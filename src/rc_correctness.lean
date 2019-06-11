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

inductive linear : type_context → typed_rc → Type
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
    → (Γ - (xs [∶] 𝔹) + Δ - [z ∶ 𝕆] ⊩ fn_body.«let» z e F ∷ 𝕆)
| let_r (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
    (Γ ⊪ xs [∶] 𝔹) → (Γ ⊩ e ∷ 𝕆) → (Δ ⊪ (xs [∶] 𝕆) ++ [z ∶ ℝ]) → (Δ ⊩ F ∷ 𝕆)
    → (Γ - (xs [∶] 𝔹) + Δ - [z ∶ ℝ] ⊩ fn_body.«let» z e F ∷ 𝕆)
| proj_bor (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
    (Γ ⊪ [x ∶ 𝔹, y ∶ 𝔹]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [y ∶ 𝔹] ⊩ fn_body.«let» y (expr.proj i x) F ∷ 𝕆)
| proj_own (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
    (Γ ⊪ [x ∶ 𝕆, y ∶ 𝕆]) → (Γ ⊩ F ∷ 𝕆)
    → (Γ - [y ∶ 𝕆] ⊩ fn_body.«let» y (expr.proj i x) (fn_body.inc y F) ∷ 𝕆)

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

def erase_rc : fn_body → fn_body
| (fn_body.let _ (expr.reset _) F) := erase_rc F
| (fn_body.let z (expr.reuse x cta) F) := fn_body.let z (expr.ctor_app cta) (erase_rc F)
| (fn_body.let x e F) := fn_body.let x e (erase_rc F)
| (fn_body.inc _ F) := erase_rc F
| (fn_body.dec _ F) := erase_rc F
| (fn_body.case x cases) := fn_body.case x (cases.map (λ c, erase_rc c)) -- how do we tell lean that this terminates?
| (fn_body.return x) := fn_body.return x 


end rc_correctness
