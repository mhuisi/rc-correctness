import data.multiset
import tactic.interactive
import logic.function

namespace list
open well_founded_tactics

-- sizeof_lt_sizeof_of_mem, map_wf, map_wf_eq_map & fn_body.rec_wf courtesy of Sebastian Ullrich
lemma sizeof_lt_sizeof_of_mem {α} [has_sizeof α] {a : α} : ∀ {l : list α}, a ∈ l → sizeof a < sizeof l
| []      h := absurd h (not_mem_nil _)
| (b::bs) h :=
  begin
    cases eq_or_mem_of_mem_cons h with h_1 h_2,
    subst h_1,
    {unfold_sizeof, cancel_nat_add_lt, trivial_nat_lt},
    {have aux₁ := sizeof_lt_sizeof_of_mem h_2,
     unfold_sizeof,
     exact nat.lt_add_left _ _ _ (nat.lt_add_left _ _ _ aux₁)}
  end

def map_wf {α β : Type*} [has_sizeof α] (xs : list α) (f : Π (a : α), (sizeof a < 1 + sizeof xs) → β) : list β :=
xs.attach.map (λ p,
  have sizeof p.val < 1 + sizeof xs, from nat.lt_add_left _ _ _ (list.sizeof_lt_sizeof_of_mem p.property),
  f p.val this)

lemma map_wf_eq_map {α β : Type*} [has_sizeof α] {xs : list α} {f : α → β} :
  map_wf xs (λ a _, f a) = map f xs :=
by simp [map_wf, attach, map_pmap, pmap_eq_map]
end list

namespace rc_correctness

def var := ℕ
local attribute [reducible] var
instance var_has_repr : has_repr var := ⟨repr⟩
local attribute [semireducible] var

def const := ℕ
local attribute [reducible] const
instance const_has_repr : has_repr const := ⟨repr⟩
local attribute [semireducible] const

def cnstr := ℕ

inductive expr : Type
| const_app_full (c : const) (ys : list var) : expr
| const_app_part (c : const) (ys : list var) : expr
| var_app (x : var) (y : var) : expr
| ctor (i : cnstr) (ys : list var) : expr
| proj (i : cnstr) (x : var) : expr
| reset (x : var) : expr
| reuse (x : var) (i : cnstr) (ys : list var) : expr

open rc_correctness.expr

notation c `⟦` ys `…` `⟧` := const_app_full c ys
notation c `⟦` ys `…` `, ` `_` `⟧` := const_app_part c ys
notation x `⟦` y `⟧` := var_app x y
notation `⟪` ys `⟫` i := ctor i ys
notation x `[` i `]` := proj i x
notation `reuse ` x ` in ` `⟪` ys `⟫` i := reuse x i ys

def expr_repr : expr → string
| (c⟦ys…⟧) := c.repr ++ "⟦" ++ ys.repr ++ "…⟧"
| (c⟦ys…, _⟧) := c.repr ++ "⟦" ++ ys.repr ++ "…, _⟧"
| (x⟦y⟧) := x.repr ++ "⟦" ++ y.repr ++ "⟧"
| (⟪ys⟫i) := "⟪" ++ ys.repr ++ "⟫" ++ i.repr 
| (x[i]) := x.repr ++ "[" ++ i.repr ++ "]"
| (reset x) := "reset " ++ x.repr
| (reuse x in ⟪ys⟫i) := "reuse " ++ x.repr ++ " in " ++ "⟪" ++ ys.repr ++ "⟫" ++ i.repr

instance expr_has_repr : has_repr expr := ⟨expr_repr⟩ 

inductive fn_body : Type
| ret (x : var) : fn_body 
| «let» (x : var) (e : expr) (F : fn_body) : fn_body
| case (x : var) (Fs : list fn_body) : fn_body
| inc (x : var) (F : fn_body) : fn_body
| dec (x : var) (F : fn_body) : fn_body

open fn_body

notation x ` ≔ ` e `; ` F := fn_body.let x e F
notation `case ` x ` of ` Fs := fn_body.case x Fs
notation `inc ` x `; ` F := fn_body.inc x F
notation `dec ` x `; ` F := fn_body.dec x F

def fn_body_repr : fn_body → string
| (ret x) := "ret " ++ x.repr
| (x ≔ e; F) := x.repr ++ " ≔ " ++ repr e ++ "; " ++ fn_body_repr F
| (case x of Fs) := "case " ++ x.repr ++ " of " ++ (Fs.map_wf (λ F h, fn_body_repr F)).repr
| (inc x; F) := "inc " ++ x.repr ++ "; " ++ fn_body_repr F
| (dec x; F) := "dec " ++ x.repr ++ "; " ++ fn_body_repr F

instance fn_body_has_repr : has_repr fn_body := ⟨fn_body_repr⟩ 

def {l} fn_body.rec_wf (C : fn_body → Sort l)
  («ret» : Π (x : var), C (ret x))
  («let» : Π (x : var) (e : expr) (F : fn_body) (F_ih : C F), C (x ≔ e; F))
  («case» : Π (x : var) (Fs : list fn_body) (Fs_ih : ∀ F ∈ Fs, C F), C (case x of Fs))
  («inc» : Π (x : var) (F : fn_body) (F_ih : C F), C (inc x; F))
  («dec» : Π (x : var) (F : fn_body) (F_ih : C F), C (dec x; F)) : Π (x : fn_body), C x
| (fn_body.ret a) := «ret» a
| (x ≔ a; a_1) := «let» x a a_1 (fn_body.rec_wf a_1)
| (case a of a_1) := «case» a a_1 (λ a h,
  have sizeof a < 1 + sizeof a_1, from nat.lt_add_left _ _ _ (list.sizeof_lt_sizeof_of_mem h),
  fn_body.rec_wf a)
| (inc a; a_1) := «inc» a a_1 (fn_body.rec_wf a_1)
| (dec a; a_1) := «dec» a a_1 (fn_body.rec_wf a_1)

@[simp] def FV_expr : expr → list var
| (c⟦xs…⟧) := xs
| (c⟦xs…, _⟧) := xs
| (x⟦y⟧) := [x, y]
| (⟪xs⟫i) := xs
| (x[i]) := [x]
| (reset x) := [x]
| (reuse x in ⟪xs⟫i) := xs.insert x

@[simp] def FV : fn_body → list var
| (ret x) := [x]
| (x ≔ e; F) := FV_expr e ∪ ((FV F).filter (≠ x))
| (case x of Fs) := (Fs.map_wf (λ F h, FV F)).join.erase_dup.insert x
| (inc x; F) := (FV F).insert x
| (dec x; F) := (FV F).insert x

structure fn := (ys : list var) (F : fn_body)

inductive rc : Type
| var (x : var) : rc
| const (c : const) : rc
| expr (e : expr) : rc
| fn_body (F : fn_body) : rc
| fn (f : fn) : rc

instance var_to_rc : has_coe var rc := ⟨rc.var⟩ 
instance const_to_rc : has_coe var rc := ⟨rc.const⟩ 
instance expr_to_rc : has_coe expr rc := ⟨rc.expr⟩ 
instance fn_body_to_rc : has_coe fn_body rc := ⟨rc.fn_body⟩
instance fn_to_rc : has_coe fn rc := ⟨rc.fn⟩ 

@[derive decidable_eq]
inductive ob_lin_type : Type 
  | 𝕆 | 𝔹

@[derive decidable_eq]
inductive lin_type : Type
  | ob : ob_lin_type → lin_type
  | ℝ : lin_type

instance ob_lin_type_to_lin_type : has_coe ob_lin_type lin_type := ⟨lin_type.ob⟩

structure typed_rc := (c : rc) (ty : lin_type)

@[derive decidable_eq]
structure typed_var := (x : var) (ty : lin_type)

notation x ` ∶ `:2 τ := typed_var.mk x τ
notation xs ` [∶] `:2 τ := (xs.map (∶ τ) : multiset typed_var)
notation c ` ∷ `:2 τ := typed_rc.mk c τ 

abbreviation type_context := multiset typed_var

open ob_lin_type
open lin_type

inductive expr_wf (δ : const → fn) : multiset var → expr → Prop
notation Γ ` ⊢ `:1 e := expr_wf Γ e
| const_app_full (Γ : multiset var) (ys : list var) (c : const) :
  (↑ys ⊆ Γ) → (ys.length = (δ c).ys.length)
  → (Γ ⊢ c⟦ys…⟧)
| const_app_part (Γ : multiset var) (c : const) (ys : list var) :
  (↑ys ⊆ Γ)
  → (Γ ⊢ c⟦ys…, _⟧)
| var_app (Γ : multiset var) (x y : var) :
  (x ∈ Γ) → (y ∈ Γ)
  → (Γ ⊢ x⟦y⟧)
| ctor (Γ : multiset var) (i : cnstr) (ys : list var) : 
  (↑ys ⊆ Γ)
  → (Γ ⊢ ⟪ys⟫i)
| proj (Γ : multiset var) (x : var) (i : cnstr) : 
  (x ∈ Γ)
  → (Γ ⊢ x[i])
| reset (Γ : multiset var) (x : var) :
  (x ∈ Γ)
  → (Γ ⊢ reset x)
| «reuse» (Γ : multiset var) (x : var) (i : cnstr) (ys : list var) :
  (↑ys ⊆ Γ) → (x ∈ Γ)
  → (Γ ⊢ reuse x in ⟪ys⟫i)

notation δ `; ` Γ ` ⊢ `:1 e := expr_wf δ Γ e

inductive fn_body_wf (δ : const → fn) : multiset var → fn_body → Prop
notation Γ ` ⊢ `:1 F := fn_body_wf Γ F
| ret (Γ : multiset var) (x : var) : 
  (x ∈ Γ)
  → (Γ ⊢ ret x)
| «let» (Γ : multiset var) (z : var) (e : expr) (F : fn_body) :
  (δ; Γ ⊢ e) → (z ∈ FV F) → (z ∉ Γ) → (z :: Γ ⊢ F)
  → (Γ ⊢ (z ≔ e; F))
| «case» (Γ : multiset var) (x : var) (Fs : list fn_body) :
  (x ∈ Γ) → (∀ F ∈ Fs, Γ ⊢ F)
  → (Γ ⊢ (case x of Fs))
| «inc» (Γ : multiset var) (x : var) (F : fn_body) :
  (x ∈ Γ) → (Γ ⊢ F)
  → (Γ ⊢ inc x; F)
| «dec» (Γ : multiset var) (x : var) (F : fn_body) :
  (x ∈ Γ) → (Γ ⊢ F)
  → (Γ ⊢ dec x; F)

notation δ `; ` Γ ` ⊢ `:1 F := fn_body_wf δ Γ F

inductive const_wf (δ : const → fn) : const → Prop
notation `⊢ `:1 c := const_wf c
| const (c : const) : (δ; (δ c).ys ⊢ (δ c).F) → (⊢ c)

notation δ ` ⊢ `:1 c := const_wf δ c

inductive program_wf : (const → fn) → Prop
notation `⊢ `:1 δ := program_wf δ
| program (δ : const → fn) :
  (∀ c : const, δ ⊢ c)
  → (⊢ δ)

notation `⊢ `:1 δ := program_wf δ

inductive reuse_fn_body_wf : multiset var → fn_body → Prop
notation Γ ` ⊢ᵣ `:1 F := reuse_fn_body_wf Γ F
| ret (Γ : multiset var) (x : var) : Γ ⊢ᵣ ret x
| let_reset (Γ : multiset var) (z x : var) (F : fn_body) :
  (z :: Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ reset x; F))
| let_reuse (Γ : multiset var) (z x : var) (F : fn_body) (i : cnstr) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (x :: Γ ⊢ᵣ (z ≔ reuse x in ⟪ys⟫i; F))
| let_const_app_full (Γ : multiset var) (F : fn_body) (z : var) (c : const) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ c⟦ys…⟧; F))
| let_const_app_part (Γ : multiset var) (F : fn_body) (z : var) (c : const) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ c⟦ys…, _⟧; F))
| let_var_app (Γ : multiset var) (F : fn_body) (z x y : var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ x⟦y⟧; F))
| let_ctor_app (Γ : multiset var) (F : fn_body) (z : var) (i : cnstr) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ ⟪ys⟫i; F))
| let_proj (Γ : multiset var) (F : fn_body) (z x : var) (i : cnstr) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ (z ≔ x[i]; F))
| «case» (Γ : multiset var) (x : var) (Fs : list fn_body) :
  (∀ F ∈ Fs, Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ case x of Fs)
| «inc» (Γ : multiset var) (x : var) (F : fn_body) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ inc x; F)
| «dec» (Γ : multiset var) (x : var) (F : fn_body) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ dec x; F)

notation Γ ` ⊢ᵣ `:1 F := reuse_fn_body_wf Γ F

inductive reuse_const_wf (δ : const → fn) : const → Prop
notation `⊢ᵣ `:1 c := reuse_const_wf c
| const (c : const) :
  (δ; ∅ ⊢ (δ c).F)
  → (⊢ᵣ c)

notation δ ` ⊢ᵣ `:1 c := reuse_const_wf δ c

inductive reuse_program_wf : (const → fn) → Prop
notation `⊢ᵣ `:1 δ := reuse_program_wf δ
| program (δ : const → fn) : 
  (⊢ δ) → (∀ c : const, δ ⊢ᵣ c)
  → (⊢ᵣ δ)

notation `⊢ᵣ `:1 δ := reuse_program_wf δ

inductive borrow_fn_body_wf (β : const → var → ob_lin_type) : fn_body → Prop
notation ` ⊢ᴮ `:1 F := borrow_fn_body_wf F
| ret (x : var) : ⊢ᴮ ret x
| let_reset (z x : var) (F : fn_body) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ reset x; F))
| let_reuse (z x : var) (F : fn_body) (i : cnstr) (ys : list var) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ reuse x in ⟪ys⟫i; F))
| let_const_app_full (F : fn_body) (z : var) (c : const) (ys : list var) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ c⟦ys…⟧; F))
| let_const_app_part (F : fn_body) (z : var) (c : const) (ys : list var) :
  (∀ x : var, β c x ≠ 𝔹) → (⊢ᴮ F)
  → (⊢ᴮ (z ≔ c⟦ys…, _⟧; F))
| let_var_app (F : fn_body) (z x y : var) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ x⟦y⟧; F))
| let_ctor_app (F : fn_body) (z : var) (i : cnstr) (ys : list var) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ ⟪ys⟫i; F))
| let_proj (F : fn_body) (z x : var) (i : cnstr) :
  (⊢ᴮ F)
  → (⊢ᴮ (z ≔ x[i]; F))
| «case» (x : var) (Fs : list fn_body) :
  (∀ F ∈ Fs, ⊢ᴮ F)
  → (⊢ᴮ case x of Fs)
| «inc» (x : var) (F : fn_body) :
  (⊢ᴮ F)
  → (⊢ᴮ inc x; F)
| «dec» (x : var) (F : fn_body) :
  (⊢ᴮ F)
  → (⊢ᴮ dec x; F)

notation β ` ⊢ᴮ `:1 F := borrow_fn_body_wf β F

inductive borrow_const_wf (β : const → var → ob_lin_type) (δ : const → fn) : const → Prop
notation `⊢ᴮ ` c := borrow_const_wf c
| const (c : const) :
  (β ⊢ᴮ (δ c).F) -- arity not important here?
  → (⊢ᴮ c)

notation β `; ` δ ` ⊢ᴮ ` c := borrow_const_wf β δ c

inductive borrow_program_wf (β : const → var → ob_lin_type) : (const → fn) → Prop
notation `⊢ᴮ ` δ := borrow_program_wf δ
| program (δ : const → fn) : 
  (⊢ᵣ δ) → (∀ c : const, β; δ ⊢ᴮ c)
  → (⊢ᴮ δ)

notation β ` ⊢ᴮ ` δ := borrow_program_wf β δ

inductive linear (β : const → var → ob_lin_type) : type_context → typed_rc → Prop
notation Γ ` ⊩ `:1 t := linear Γ t
| var (x : var) (τ : lin_type) : 
  (x ∶ τ)::0 ⊩ x ∷ τ
| weaken (Γ : type_context) (t : typed_rc) (x : var) : 
  (Γ ⊩ t) 
  → ((x ∶ 𝔹) :: Γ ⊩ t)
| contract (Γ : type_context) (x : var) (t : typed_rc) :
  ((x ∶ 𝔹) ∈ Γ) → ((x ∶ 𝔹) :: Γ ⊩ t)
  → (Γ ⊩ t)
| inc_o (Γ : type_context) (x : var) (F : fn_body) :
  ((x ∶ 𝕆) ∈ Γ) → ((x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ (inc x; F) ∷ 𝕆)
| inc_b (Γ : type_context) (x : var) (F : fn_body) :
  ((x ∶ 𝔹) ∈ Γ) → ((x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ (inc x; F) ∷ 𝕆)
| dec_o (Γ : type_context) (x : var) (F : fn_body) :
  (Γ ⊩ F ∷ 𝕆)
  → ((x ∶ 𝕆) :: Γ ⊩ (dec x; F) ∷ 𝕆)
| dec_r (Γ : type_context) (x : var) (F : fn_body) :
  (Γ ⊩ F ∷ 𝕆)
  → ((x ∶ ℝ) :: Γ ⊩ (dec x; F) ∷ 𝕆)
| ret (Γ : type_context) (x : var) :
  (Γ ⊩ x ∷ 𝕆)
  → (Γ ⊩ (ret x) ∷ 𝕆)
| case_o (Γ : type_context) (x : var) (Fs : list fn_body) :
  ((x ∶ 𝕆) ∈ Γ) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
  → (Γ ⊩ (case x of Fs) ∷ 𝕆)
| case_b (Γ : type_context) (x : var) (Fs : list fn_body) :
  ((x ∶ 𝔹) ∈ Γ) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
  → (Γ ⊩ (case x of Fs) ∷ 𝕆)
| const_app_full (Γys : list (type_context × var)) (c : const) :
  (∀ Γy ∈ Γys, (Γy : type_context × var).1 ⊩ Γy.2 ∷ β c Γy.2)
  → (multiset.join (Γys.map prod.fst) ⊩ c⟦Γys.map prod.snd…⟧ ∷ 𝕆)
| const_app_part (ys : list var) (c : const) :
  ys [∶] 𝕆 ⊩ c⟦ys…, _⟧ ∷ 𝕆
| var_app (x y : var) :
  (x ∶ 𝕆) :: (y ∶ 𝕆) :: 0 ⊩ x⟦y⟧ ∷ 𝕆
| cnstr_app (ys : list var) (i : cnstr) :
  ys [∶] 𝕆 ⊩ (⟪ys⟫i) ∷ 𝕆
| reset (x : var) :
  (x ∶ 𝕆) :: 0 ⊩ (reset x) ∷ ℝ
| «reuse» (x : var) (ys : list var) (i : cnstr) :
  (x ∶ ℝ) :: (ys [∶] 𝕆) ⊩ (reuse x in ⟪ys⟫i) ∷ 𝕆
| let_o (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
  ((xs [∶] 𝕆) ⊆ Δ) → (Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) → ((z ∶ 𝕆) :: Δ ⊩ F ∷ 𝕆)
  → (Γ + Δ ⊩ (z ≔ e; F) ∷ 𝕆)
| let_r (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
  ((xs [∶] 𝕆) ⊆ Δ) → (Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) → ((z ∶ ℝ) :: Δ ⊩ F ∷ 𝕆)
  → (Γ + Δ ⊩ (z ≔ e; F) ∷ 𝕆)
| proj_bor (Γ : type_context) (x y : var) (F : fn_body) (i : cnstr) :
  ((x ∶ 𝔹) ∈ Γ) → ((y ∶ 𝔹) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ (y ≔ x[i]; F) ∷ 𝕆)
| proj_own (Γ : type_context) (x y : var) (F : fn_body) (i : cnstr) :
  ((x ∶ 𝕆) ∈ Γ) → ((y ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ (y ≔ x[i]; inc y; F) ∷ 𝕆)

notation β `; ` Γ ` ⊩ `:1 t := linear β Γ t

inductive linear_const (β : const → var → ob_lin_type) (δ : const → fn) : const → Prop
notation ` ⊩ `:1 c := linear_const c
| const (c : const) :
  (β; (δ c).ys.map (λ y, y ∶ β c y) ⊩ (δ c).F ∷ 𝕆)
  → (⊩ c)

notation β `; ` δ ` ⊩ `:1 c := linear_const β δ c

inductive linear_program (β : const → var → ob_lin_type) : (const → fn) → Prop
notation ` ⊩ `:1 δ := linear_program δ
| program (δ : const → fn) :
  (β ⊢ᴮ δ) → (∀ c : const, (β; δ ⊩ c))
  → (⊩ δ)

notation β `; ` δ ` ⊩ `:1 δᵣ := linear_program β δ δᵣ

@[simp] def 𝕆plus (x : var) (V : list var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ V then F else inc x; F

@[simp] def 𝕆minus_var (x : var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ FV F then dec x; F else F

@[simp] def 𝕆minus : list var → fn_body → (var → ob_lin_type) → fn_body 
| [] F βₗ := F
| (x :: xs) F βₗ := 𝕆minus xs (𝕆minus_var x F βₗ) βₗ

notation f `[` a `↦` b `]` := function.update f a b 

@[simp] def Capp : list (var × ob_lin_type) → fn_body → (var → ob_lin_type) → fn_body
| [] (z ≔ e; F) βₗ := z ≔ e; F
| ((y, t)::xs) (z ≔ e; F) βₗ := 
  if t = 𝕆 then
    let ys := xs.map (λ ⟨x, b⟩, x) in 
      𝕆plus y (ys ∪ FV F) (Capp xs (z ≔ e; F) βₗ) βₗ
  else
    Capp xs (z ≔ e; 𝕆minus_var y F βₗ) βₗ
| xs F βₗ := F

@[simp] def C (β : const → var → ob_lin_type) : fn_body → (var → ob_lin_type) → fn_body
| (ret x) βₗ := 𝕆plus x ∅ (ret x) βₗ
| (case x of Fs) βₗ :=
  case x of Fs.map_wf (λ F h, 𝕆minus (FV (case x of Fs)) (C F βₗ) βₗ)
| (y ≔ x[i]; F) βₗ := 
  if βₗ x = 𝕆 then
    y ≔ x[i]; inc y; 𝕆minus_var x (C F βₗ) βₗ
  else
    y ≔ x[i]; C F (βₗ[y ↦ 𝔹])
| (y ≔ reset x; F) βₗ := y ≔ 
  reset x; C F βₗ
| (z ≔ c⟦ys…⟧; F) βₗ := 
  Capp (ys.map (λ y, ⟨y, β c y⟩)) (z ≔ c⟦ys…⟧; C F βₗ) βₗ
| (z ≔ c⟦ys…, _⟧; F) βₗ := 
  Capp (ys.map (λ y, ⟨y, β c y⟩)) (z ≔ c⟦ys…, _⟧; C F βₗ) βₗ
| (z ≔ x⟦y⟧; F) βₗ := 
  Capp ([⟨x, 𝕆⟩, ⟨y, 𝕆⟩]) (z ≔ x⟦y⟧; C F βₗ) βₗ   
| (z ≔ ⟪ys⟫i; F) βₗ :=
  Capp (ys.map (λ y, ⟨y, 𝕆⟩)) (z ≔ ⟪ys⟫i; C F βₗ) βₗ
| (z ≔ reuse x in ⟪ys⟫i; F) βₗ :=
  Capp (ys.map (λ y, ⟨y, 𝕆⟩)) (z ≔ reuse x in ⟪ys⟫i; C F βₗ) βₗ
| F βₗ := F

constant δ : const → fn

section FV

open multiset
open list

theorem FV_e {Γ : multiset var} {e : expr} (h : δ; Γ ⊢ e) :
  ↑(FV_expr e) ⊆ Γ :=
begin
  induction e;
  apply subset_iff.mpr; 
  intros x h₁;
  simp at h₁;
  cases h,
  { replace h_a := subset_iff.mp h_a,
    exact h_a h₁ },
  { replace h_a := subset_iff.mp h_a,
    exact h_a h₁ },
  { cases h₁; rw h₁; assumption },
  { replace h_a := subset_iff.mp h_a,
    exact h_a h₁ },
  { rw h₁, assumption },
  { rw h₁, assumption },
  { replace h₁ := eq_or_mem_of_mem_insert h₁,
    cases h₁,
    { rw h₁, assumption },
    { replace h_a := subset_iff.mp h_a,
      exact h_a h₁ } }
end

theorem FV_F {Γ : multiset var} {F : fn_body} (h : δ; Γ ⊢ F) : 
  ↑(FV F) ⊆ Γ :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing Γ },
  case ret : x {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    rw h₁,
    cases h,
    assumption
  },
  case «let» : x e F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    cases h₁,
    case or.inl { 
      have h₂ : ↑(FV_expr e) ⊆ Γ, from FV_e h_a,
      replace h₂ := subset_iff.mp h₂,
      exact h₂ h₁ 
    },
    case or.inr { 
      have h₂ : ↑(FV F) ⊆ x :: Γ, from ih h_a_3,
      replace h₂ := subset_iff.mp h₂,
      cases h₁,
      have h₃ : y ∈ x :: Γ, from h₂ h₁_left,
      replace h₃ := mem_cons.mp h₃,
      cases h₃,
      { contradiction },
      { assumption }
    }
  },
  case «case» : x Fs ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    replace h₁ := mem_insert_iff.mp h₁,
    cases h₁,
    case or.inl {
      rw h₁,
      assumption
    },
    case or.inr {
      rw map_wf_eq_map at h₁,
      simp at ih,
      simp at h₁,
      rcases h₁ with ⟨l, ⟨⟨a, ⟨a_in_Fs, FV_a_eq_l⟩⟩, y_in_l⟩⟩,
      rw ←FV_a_eq_l at y_in_l,
      have a_typed : (δ; Γ ⊢ a), from h_a_1 a a_in_Fs,
      have FV_a_sub_Γ : ↑(FV a) ⊆ Γ, from ih a a_in_Fs a_typed,
      replace FV_a_sub_Γ := subset_iff.mp FV_a_sub_Γ,
      exact FV_a_sub_Γ y_in_l
    },
  },
  case «inc» : x F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    replace h₁ := mem_insert_iff.mp h₁,
    cases h₁,
    { rw h₁,
      assumption },
    { have h₂ : ↑(FV F) ⊆ Γ, from ih h_a_1,
      replace h₂ := subset_iff.mp h₂,
      exact h₂ h₁ }
  },
  case «dec» : x F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    replace h₁ := mem_insert_iff.mp h₁,
    cases h₁,
    { rw h₁,
      assumption },
    { have h₂ : ↑(FV F) ⊆ Γ, from ih h_a_1,
      replace h₂ := subset_iff.mp h₂,
      exact h₂ h₁ }
  }
end

end FV

constant β : const → var → ob_lin_type
constant βₗ : var → ob_lin_type -- chosen arbitrarily so far, will have to adjust later

open list

theorem insert_singleton {x y : var} : x ∈ insert y (list.cons y nil) ↔ x = y :=
begin
  apply iff.intro;
  intro h,
  { have h₁ : y ∈ [y], from list.mem_singleton_self y, 
    rw list.insert_of_mem h₁ at h,
    exact eq_of_mem_singleton h },
  { rw h,
    have h₁ : y ∈ [y], from list.mem_singleton_self y,
    rw list.insert_of_mem h₁,
    assumption }
end

theorem C_no_new_vars (F : fn_body) : ∀ x : var, x ∈ FV (C β F βₗ) ↔ x ∈ FV F :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf },
  case ret : x y {
    simp,
    split_ifs;
    simp,
    apply iff.intro;
    intro h₁,
    { exact insert_singleton.mp h₁ }, 
    { exact insert_singleton.mpr h₁ }
  },
  case «let» : x e F ih y {
    simp, 
    induction e,
    case rc_correctness.expr.const_app_full {
      sorry
    },
    case rc_correctness.expr.const_app_part {
      sorry
    },
    case rc_correctness.expr.var_app {
      simp, 
      split_ifs;
      simp at *;
      rw ih at *,
      { simp [or.assoc] },
      { apply iff.intro;
        intro h_2,
        { replace h_2 := eq_or_mem_of_mem_insert h_2,
          cases h_2,
          { exact or.inl (or.inr h_2) },
          replace h_2 := eq_or_mem_of_mem_insert h_2,
          cases h_2,
          { exact or.inl (or.inl h_2) },
          replace h_2 := eq_or_mem_of_mem_insert h_2,
          cases h_2, 
          { exact or.inl (or.inr h_2) },
          simp [ih, mem_filter] at h_2, 
          exact or.inr h_2 },
        sorry }, -- cases timeout?
      sorry
    },
    case rc_correctness.expr.ctor {
      apply iff.intro;
      intro h;
      simp at *,
      sorry -- map?
    },
    case rc_correctness.expr.proj {
      simp at *, 
      split_ifs; 
      simp,
      sorry
    }, 
    sorry
    
  },
  case «case» {
    sorry
  },
  case «inc» {
    simp
  },
  case «dec» {
    simp
  }
end

end rc_correctness
