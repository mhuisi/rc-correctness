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

end rc_correctness
