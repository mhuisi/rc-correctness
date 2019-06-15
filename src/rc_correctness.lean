import data.multiset

namespace rc_correctness

def var := ℕ

def const := ℕ

def ctor := ℕ

structure ctor_app := (i : ctor) (v : list var)

inductive expr : Type
| const_app_full : const → list var → expr
| const_app_part : const → list var → expr
| var_app : var → var → expr
| ctor_app : ctor_app → expr
| proj : ctor → var → expr
| reset : var → expr
| reuse : var → ctor_app → expr

inductive fn_body : Type
| return : var → fn_body 
| «let» : var → expr → fn_body → fn_body
| case : var → list fn_body → fn_body
| inc : var → fn_body → fn_body
| dec : var → fn_body → fn_body

-- is there a better way? i couldn't find a coercion in the stdlib.
universe u
def list_to_set {α : Type u} : list α → set α
| [] := {}
| (x :: xs) := (list_to_set xs).insert x

-- :(
def set_to_list {α : Type u} : set α → list α := sorry

def FV_expr : expr → set var
| (expr.const_app_full _ xs) := list_to_set xs
| (expr.const_app_part c xs) := list_to_set xs
| (expr.var_app x y) := {x, y}
| (expr.ctor_app ⟨i, xs⟩) := list_to_set xs
| (expr.proj c x) := {x}
| (expr.reset x) := {x}
| (expr.reuse x ⟨i, xs⟩) := list_to_set (xs.insert x)

def FV : fn_body → set var
| (fn_body.return x) := {x}
| (fn_body.let x e F) := FV_expr e ∪ (FV F \ {x})
| (fn_body.case x Fs) := (Fs.map (λ F, FV F)).foldr (∪) {} -- how do we tell lean that this terminates?
| (fn_body.inc x F) := {x} ∪ FV F
| (fn_body.dec x F) := {x} ∪ FV F

structure fn := (yc : list var) (F : fn_body)

inductive rc : Type
| var : var → rc
| const : const → rc
| expr : expr → rc
| fn_body : fn_body → rc
| fn : fn → rc

instance var_to_rc : has_coe var rc := ⟨rc.var⟩ 

instance const_to_rc : has_coe var rc := ⟨rc.const⟩ 

instance expr_to_rc : has_coe expr rc := ⟨rc.expr⟩ 

instance fn_body_to_rc : has_coe fn_body rc := ⟨rc.fn_body⟩

instance fn_to_rc : has_coe fn rc := ⟨rc.fn⟩ 

def erase_rc_fn_body : fn_body → fn_body
| (fn_body.let _ (expr.reset _) F) := erase_rc_fn_body F
| (fn_body.let z (expr.reuse x cta) F) := fn_body.let z (expr.ctor_app cta) (erase_rc_fn_body F)
| (fn_body.let x e F) := fn_body.let x e (erase_rc_fn_body F)
| (fn_body.inc _ F) := erase_rc_fn_body F
| (fn_body.dec _ F) := erase_rc_fn_body F
| (fn_body.case x cases) := fn_body.case x (cases.map (λ c, erase_rc_fn_body c)) -- how do we tell lean that this terminates?
| (fn_body.return x) := fn_body.return x 

def erase_rc_fn (f : fn) : fn := ⟨f.yc, erase_rc_fn_body f.F⟩ 

@[derive decidable_eq]
inductive lin_type : Type 
    | 𝕆 | 𝔹 | ℝ

@[derive decidable_eq]
inductive ob_lin_type : Type
    | 𝕆 | 𝔹

instance ob_lin_type_to_lin_type : has_coe ob_lin_type lin_type := ⟨λ oblt, 
    match oblt with
    | ob_lin_type.𝕆 := lin_type.𝕆
    | ob_lin_type.𝔹 := lin_type.𝔹
    end⟩ 

open lin_type

structure typed_rc := (c : rc) (ty : lin_type)

structure typed_var := (x : var) (ty : lin_type)

instance typed_var_eq : decidable_eq typed_var := by tactic.mk_dec_eq_instance

notation x ` ∶ `:2 τ := typed_var.mk x τ
notation xs ` [∶] `:2 τ := xs.map (∶ τ)
notation c ` ∷ `:2 τ := typed_rc.mk c τ 

abbreviation type_context := multiset typed_var

notation Γ ` ⊪ `:1 xs := ↑xs ≤ Γ

structure param_typing := (Γ : type_context) (x : var) (β : ob_lin_type)

inductive linear : type_context → typed_rc → Prop
notation Γ ` ⊩ `:1 t := linear Γ t
| var (x : var) (τ : lin_type) : 
    [x ∶ τ] ⊩ x ∷ τ
| weaken (Γ : type_context) (t : typed_rc) (x : var) : 
    (Γ ⊩ t) 
    → (Γ + [x ∶ 𝔹] ⊩ t)
| contract (Γ : type_context) (x : var) (t : typed_rc) :
    (Γ ⊪ [x ∶ 𝔹, x ∶ 𝔹]) → (Γ ⊩ t)
    → (Γ - [x ∶ 𝔹] ⊩ t)
| inc_o (Γ : type_context) (x : var) (F : fn_body) :
    (Γ ⊪ [x ∶ 𝕆, x ∶ 𝕆]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [x ∶ 𝕆] ⊩ fn_body.inc x F ∷ 𝕆)
| inc_b (Γ : type_context) (x : var) (F : fn_body) :
    (Γ ⊪ [x ∶ 𝔹, x ∶ 𝕆]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [x ∶ 𝕆] ⊩ fn_body.inc x F ∷ 𝕆)
| dec_o (Γ : type_context) (x : var) (F : fn_body) :
    (Γ ⊩ F ∷ 𝕆)
    → (Γ + [x ∶ 𝕆] ⊩ fn_body.dec x F ∷ 𝕆)
| dec_r (Γ : type_context) (x : var) (F : fn_body) :
    (Γ ⊩ F ∷ 𝕆)
    → (Γ + [x ∶ ℝ] ⊩ fn_body.dec x F ∷ 𝕆)
| return (Γ : type_context) (x : var) :
    (Γ ⊩ x ∷ 𝕆)
    → (Γ ⊩ fn_body.return x ∷ 𝕆)
| case_o (Γ : type_context) (x : var) (Fs : list fn_body) :
    (Γ ⊪ [x ∶ 𝕆]) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
    → (Γ ⊩ fn_body.case x Fs ∷ 𝕆)
| case_b (Γ : type_context) (x : var) (Fs : list fn_body) :
    (Γ ⊪ [x ∶ 𝔹]) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
    → (Γ ⊩ fn_body.case x Fs ∷ 𝕆)
-- the app rules may need to get revamped down the road 
-- (properly modelling β may prove to be difficult, and right now there are no restrictions on β).
-- the current app rules are merely placeholders, for now. 
-- maybe the correct design decision will be obvious once we start working with these rules!
| const_app_full (pts : list param_typing) (c : const) :
    (∀ pt ∈ pts, (pt : param_typing).Γ ⊩ pt.x ∷ pt.β)
    → (multiset.join (pts.map (param_typing.Γ)) ⊩ expr.const_app_full c (pts.map (param_typing.x)) ∷ 𝕆)
| const_app_part (ys : list var) (c : const) :
    ys [∶] 𝕆 ⊩ expr.const_app_part c ys ∷ 𝕆
| var_app (x y : var) :
    [x ∶ 𝕆, y ∶ 𝕆] ⊩ expr.var_app x y ∷ 𝕆
| cnstr_app (ys : list var) (i : ctor) :
    ys [∶] 𝕆 ⊩ expr.ctor_app ⟨i, ys⟩ ∷ 𝕆
| reset (x : var) :
    [x ∶ 𝕆] ⊩ expr.reset x ∷ ℝ
| reuse (x : var) (ys : list var) (i : ctor) :
    [x ∶ ℝ] + (ys [∶] 𝕆) ⊩ expr.reuse x ⟨i, ys⟩ ∷ 𝕆
| let_o (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
    (Γ ⊪ xs [∶] 𝔹) → (Γ ⊩ e ∷ 𝕆) → (Δ ⊪ (xs [∶] 𝕆) ++ [z ∶ 𝕆]) → (Δ ⊩ F ∷ 𝕆)
    → (Γ - (xs [∶] 𝔹) + Δ - [z ∶ 𝕆] ⊩ fn_body.let z e F ∷ 𝕆)
| let_r (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
    (Γ ⊪ xs [∶] 𝔹) → (Γ ⊩ e ∷ 𝕆) → (Δ ⊪ (xs [∶] 𝕆) ++ [z ∶ ℝ]) → (Δ ⊩ F ∷ 𝕆)
    → (Γ - (xs [∶] 𝔹) + Δ - [z ∶ ℝ] ⊩ fn_body.let z e F ∷ 𝕆)
| proj_bor (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
    (Γ ⊪ [x ∶ 𝔹, y ∶ 𝔹]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [y ∶ 𝔹] ⊩ fn_body.let y (expr.proj i x) F ∷ 𝕆)
| proj_own (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
    (Γ ⊪ [x ∶ 𝕆, y ∶ 𝕆]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [y ∶ 𝕆] ⊩ fn_body.let y (expr.proj i x) (fn_body.inc y F) ∷ 𝕆)

inductive linear_const : (const → fn) → const → Prop
| const (δ : const → fn) (c : const) (βs : list ob_lin_type) :
    (linear ((δ c).yc.zip_with (∶) ↑βs) ((δ c).F ∷ 𝕆))
    → (linear_const δ c)

inductive linear_program : (const → fn) → Prop
| program (δᵣ : const → fn) (δ : const → fn) :
    (∀ c : const, δᵣ c = erase_rc_fn (δ c) ∧ linear_const δᵣ c)
    → (linear_program δᵣ)

def 𝕆plus (x : var) (V : set var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = ob_lin_type.𝕆 ∧ x ∉ V then F else fn_body.inc x F -- no decidable mem for set :(

def 𝕆minus_var (x : var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = ob_lin_type.𝕆 ∧ x ∉ FV F then fn_body.dec x F else F -- no decidable mem for set :(

def 𝕆minus : list var → fn_body → (var → ob_lin_type) → fn_body
| [] F βₗ := F
| (x :: xs) F βₗ := 𝕆minus xs (𝕆minus_var x F βₗ) βₗ

def fn_update {α : Type u} {β : Type u} [decidable_eq α] (f : α → β) (a : α) (b : β) : α → β :=
    λ x, if x = a then b else f x

notation f `[` a `↦` b `]` := fn_update f a b 

def Capp : list (var × ob_lin_type) → fn_body → (var → ob_lin_type) → fn_body
| [] (fn_body.let z e F) βₗ := fn_body.let z e F
| ((y, ob_lin_type.𝕆)::xs) (fn_body.let z e F) βₗ := 
    let ys := xs.map (λ ⟨x, b⟩, x) in 
    𝕆plus y (list_to_set ys ∪ FV F) (Capp xs (fn_body.let z e F) βₗ) βₗ -- typo in the paper!
| ((y, ob_lin_type.𝔹)::xs) (fn_body.let z e F) βₗ :=
    Capp xs (fn_body.let z e (𝕆minus_var y F βₗ)) βₗ
| xs F βₗ := F

def C (β : const → list ob_lin_type) : fn_body → (var → ob_lin_type) → fn_body
| (fn_body.return x) βₗ := 𝕆plus x {} (fn_body.return x) βₗ
| (fn_body.case x Fs) βₗ := let ys := FV (fn_body.case x Fs) in 
    fn_body.case x (Fs.map (λ F, 𝕆minus (set_to_list ys) (C F βₗ) βₗ)) -- how do we tell lean that this terminates?
| (fn_body.let y (expr.proj i x) F) βₗ := 
    if βₗ x = ob_lin_type.𝕆 then
        fn_body.let y (expr.proj i x) (fn_body.inc y (𝕆minus_var x (C F βₗ) βₗ))
    else
        fn_body.let y (expr.proj i x) (C F (βₗ[y ↦ ob_lin_type.𝔹]))
| (fn_body.let y (expr.reset x) F) βₗ := fn_body.let y (expr.reset x) (C F βₗ)
| (fn_body.let z (expr.const_app_full c ys) F) βₗ := Capp (ys.zip (β c)) (fn_body.let z (expr.const_app_full c ys) (C F βₗ)) βₗ
| (fn_body.let z (expr.const_app_part c ys) F) βₗ := 
    Capp (ys.map (λ y, ⟨y, ob_lin_type.𝕆⟩)) (fn_body.let z (expr.const_app_part c ys) (C F βₗ)) βₗ
    -- here we ignore the first case to avoid proving non-termination. so far this should be equivalent, it may however cause issues down the road!
| (fn_body.let z (expr.var_app x y) F) βₗ := 
    Capp ([⟨x, ob_lin_type.𝕆⟩, ⟨y, ob_lin_type.𝕆⟩]) (fn_body.let z (expr.var_app x y) (C F βₗ)) βₗ   
| (fn_body.let z (expr.ctor_app ⟨i, ys⟩) F) βₗ :=
    Capp (ys.map (λ y, ⟨y, ob_lin_type.𝕆⟩)) (fn_body.let z (expr.ctor_app ⟨i, ys⟩) (C F βₗ)) βₗ
| (fn_body.let z (expr.reuse x ⟨i, ys⟩) F) βₗ :=
    Capp (ys.map (λ y, ⟨y, ob_lin_type.𝕆⟩)) (fn_body.let z (expr.reuse x ⟨i, ys⟩) (C F βₗ)) βₗ
| F βₗ := F

inductive expr_wf : set var → expr → Prop
notation Γ ` ⊩ `:1 e := expr_wf Γ e
| const_app_full (δ : const → fn) (Γ : set var) (ys : list var) (c : const) :
    (list_to_set ys ⊂ Γ) → (ys.length = (δ c).yc.length)
    → (Γ ⊩ expr.const_app_full c ys)
| const_app_part (Γ : set var) (c : const) (ys : list var) :
    (list_to_set ys ⊂ Γ)
    → (Γ ⊩ expr.const_app_part c ys)
| var_app (Γ : set var) (x y : var) :
    ({x, y} ⊂ Γ)
    → (Γ ⊩ expr.var_app x y)
| ctor_app (Γ : set var) (c : ctor_app) : 
    (list_to_set c.v ⊂ Γ)
    → (Γ ⊩ expr.ctor_app c)
| proj (Γ : set var) (x : var) (i : ctor) : 
    ({x} ⊂ Γ)
    → (Γ ⊩ expr.proj i x)
| reset (Γ : set var) (x : var) :
    ({x} ⊂ Γ)
    → (Γ ⊩ expr.reset x)
| reuse (Γ : set var) (x : var) (c : ctor_app) :
    ({x} ∪ list_to_set c.v ⊂ Γ)
    → (Γ ⊩ expr.reuse x c)

inductive fn_body_wf : set var → fn_body → Prop
notation Γ ` ⊩ `:1 f := fn_body_wf Γ f
| return (Γ : set var) (x : var) : (Γ ⊩ fn_body.return x) -- error in the paper: what is well-formedness of variables?
| «let» (Γ : set var) (z : var) (e : expr) (F : fn_body) (xs : list var) :
    (expr_wf Γ e) → (z ∈ FV F) → (z ∉ Γ) → (Γ ∪ {z} ⊩ F)
    → (Γ ∪ list_to_set xs ⊩ fn_body.let z e F) -- what is xs? how do i use the expr_wf notation?
| case (Γ : set var) (x : var) (Fs : list fn_body):
    ({x} ⊂ Γ) → (∀ F ∈ Fs, Γ ⊩ F)
    → (Γ ⊩ fn_body.case x Fs)

inductive fn_wf : fn → Prop
| fn (f : fn) : (fn_body_wf (list_to_set f.yc) f.F) → fn_wf f

inductive const_wf : (const → fn) → const → Prop
| const (δ : const → fn) (c : const) : (fn_wf (δ c)) → const_wf δ c

end rc_correctness
