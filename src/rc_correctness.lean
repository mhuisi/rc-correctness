import data.multiset
import data.finset
import tactic.interactive tactic.fin_cases
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
abbreviation var_le : var → var → Prop := nat.le
instance var_le_is_trans : is_trans var var_le := ⟨@nat.le_trans⟩
instance var_le_is_antisymm : is_antisymm var var_le := ⟨@nat.le_antisymm⟩
instance var_le_is_total : is_total var var_le := ⟨@nat.le_total⟩
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

@[simp] def FV_expr : expr → finset var
| (c⟦xs…⟧) := xs.to_finset
| (c⟦xs…, _⟧) := xs.to_finset
| (x⟦y⟧) := {x, y}
| (⟪xs⟫i) := xs.to_finset
| (x[i]) := {x}
| (reset x) := {x}
| (reuse x in ⟪xs⟫i) := insert x xs.to_finset

def join_finset {α : Type*} [decidable_eq α] (xs : list (finset α)) : finset α := xs.foldr (∪) ∅ 

@[simp] theorem f {α : Type*} [decidable_eq α] {x : α} {xs : list (finset α)} : x ∈ join_finset xs ↔ ∃ S ∈ xs, x ∈ S :=
begin
apply iff.intro,
{ intro h, 
  induction xs; 
  simp [join_finset] at *,
  { assumption },
  { cases h, 
    { exact ⟨xs_hd, ⟨or.inl rfl, h⟩⟩ },
    { have h₁, from xs_ih h,
      cases h₁, 
      cases h₁_h,
      exact ⟨h₁_w, ⟨or.inr h₁_h_left, h₁_h_right⟩ ⟩ } } },
{ intro h,
  induction xs;
  simp [join_finset] at *,
  { assumption },
  { cases h,
    cases h_h,
    cases h_h_left,
    { rw h_h_left at h_h_right, 
      exact or.inl h_h_right },
    { exact or.inr (xs_ih h_w h_h_left h_h_right)} } }
end

@[simp] def FV : fn_body → finset var
| (ret x) := {x}
| (x ≔ e; F) := FV_expr e ∪ ((FV F).erase x)
| (case x of Fs) := insert x (join_finset (Fs.map_wf (λ F h, FV F)))
| (inc x; F) := insert x (FV F)
| (dec x; F) := insert x (FV F)

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

inductive fn_body_wf (β : const → var → ob_lin_type) (δ : const → fn) : finset var → finset var → fn_body → Prop
notation Γ `; ` Δ ` ⊢ `:1 F := fn_body_wf Γ Δ F
| ret (Γ Δ : finset var) (x : var) 
  (x_def : x ∈ Γ) :
  Γ; Δ ⊢ ret x
| let_const_app_full (Γ Δ : finset var) (z : var) (c : const) (ys : list var) (F : fn_body)
  (ys_def : ys.to_finset ⊆ Γ) (arity_eq : ys.length = (δ c).ys.length)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) :
  Γ; Δ ⊢ (z ≔ c⟦ys…⟧; F)
| let_const_app_part (Γ Δ : finset var) (z : var) (c : const) (ys : list var) (F : fn_body)
  (ys_def : ys.to_finset ⊆ Γ) 
  (no_𝔹_var : ∀ x : var, β c x ≠ 𝔹) 
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) :
  Γ; Δ ⊢ (z ≔ c⟦ys…, _⟧; F)
| let_var_app (Γ Δ : finset var) (z : var) (x y : var) (F : fn_body) 
  (x_def : x ∈ Γ) (y_in_Γ : y ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) :
  Γ; Δ ⊢ (z ≔ x⟦y⟧; F)
| let_ctor (Γ Δ : finset var) (z : var) (i : cnstr) (ys : list var) (F : fn_body)
  (ys_def : ys.to_finset ⊆ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) :
  Γ; Δ ⊢ (z ≔ ⟪ys⟫i; F)
| let_proj (Γ Δ : finset var) (z : var) (x : var) (i : cnstr) (F : fn_body)
  (x_def : x ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) : 
  Γ; Δ ⊢ (z ≔ x[i]; F)
| let_reset (Γ Δ : finset var) (z : var) (x : var) (F : fn_body)
  (x_def : x ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; insert z Δ ⊢ F) :
  Γ; Δ ⊢ (z ≔ reset x; F)
| let_reuse (Γ Δ : finset var) (z : var) (x : var) (i : cnstr) (ys : list var) (F : fn_body)
  (ys_def : ys.to_finset ⊆ Γ) (x_def : x ∈ Γ)
  (z_used : z ∈ FV F) (z_undef : z ∉ Γ) (F_wf : insert z Γ; Δ ⊢ F) :
  Γ; insert x Δ ⊢ (z ≔ reuse x in ⟪ys⟫i; F)
| «case» (Γ Δ : finset var) (x : var) (Fs : list fn_body)
  (x_def : x ∈ Γ) (Fs_wf : ∀ F ∈ Fs, Γ; Δ ⊢ F) :
  Γ; Δ ⊢ (case x of Fs)
| «inc» (Γ Δ : finset var) (x : var) (F : fn_body)
  (x_def : x ∈ Γ) (F_wf : Γ; Δ ⊢ F) :
  Γ; Δ ⊢ inc x; F
| «dec» (Γ Δ : finset var) (x : var) (F : fn_body)
  (x_def : x ∈ Γ) (F_wf : Γ; Δ ⊢ F) :
  Γ; Δ ⊢ dec x; F

notation β `; ` δ `; ` Γ `; ` Δ ` ⊢ `:1 F := fn_body_wf β δ Γ Δ F

inductive const_wf (β : const → var → ob_lin_type) (δ : const → fn) : const → Prop
notation `⊢ `:1 c := const_wf c
| const (c : const) 
  (F_wf : β; δ; (δ c).ys.to_finset; ∅ ⊢ (δ c).F) : 
  ⊢ c

notation β `; ` δ ` ⊢ `:1 c := const_wf β δ c

inductive program_wf (β : const → var → ob_lin_type) : (const → fn) → Prop
notation `⊢ `:1 δ := program_wf δ
| program (δ : const → fn)
  (const_wf : ∀ c : const, β; δ ⊢ c) :
  ⊢ δ

notation β ` ⊢ `:1 δ := program_wf β δ

inductive linear (β : const → var → ob_lin_type) : type_context → typed_rc → Prop
notation Γ ` ⊩ `:1 t := linear Γ t
| var (x : var) (τ : lin_type) : 
  (x ∶ τ)::0 ⊩ x ∷ τ
| weaken (Γ : type_context) (t : typed_rc) (x : var) 
  (t_typed : Γ ⊩ t) :
  (x ∶ 𝔹) :: Γ ⊩ t
| contract (Γ : type_context) (x : var) (t : typed_rc)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (t_typed : (x ∶ 𝔹) :: Γ ⊩ t) :
  Γ ⊩ t
| inc_o (Γ : type_context) (x : var) (F : fn_body)
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (inc x; F) ∷ 𝕆
| inc_b (Γ : type_context) (x : var) (F : fn_body)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (inc x; F) ∷ 𝕆
| dec_o (Γ : type_context) (x : var) (F : fn_body)
  (F_𝕆 : Γ ⊩ F ∷ 𝕆) :
  (x ∶ 𝕆) :: Γ ⊩ (dec x; F) ∷ 𝕆
| dec_r (Γ : type_context) (x : var) (F : fn_body)
  (F_𝕆 : Γ ⊩ F ∷ 𝕆) :
  (x ∶ ℝ) :: Γ ⊩ (dec x; F) ∷ 𝕆
| ret (Γ : type_context) (x : var)
  (x_𝕆 : Γ ⊩ x ∷ 𝕆) :
  Γ ⊩ (ret x) ∷ 𝕆
| case_o (Γ : type_context) (x : var) (Fs : list fn_body)
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (case x of Fs) ∷ 𝕆
| case_b (Γ : type_context) (x : var) (Fs : list fn_body)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (Fs_𝕆 : ∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆) :
  Γ ⊩ (case x of Fs) ∷ 𝕆
| const_app_full (Γys : list (type_context × var)) (c : const)
  (ys_β_c : ∀ Γy ∈ Γys, (Γy : type_context × var).1 ⊩ Γy.2 ∷ β c Γy.2) :
  multiset.join (Γys.map prod.fst) ⊩ c⟦Γys.map prod.snd…⟧ ∷ 𝕆
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
| let_o (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body)
  (xs_𝕆 : (xs [∶] 𝕆) ⊆ Δ) (e_𝕆 : Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) (F_𝕆 : (z ∶ 𝕆) :: Δ ⊩ F ∷ 𝕆) :
  Γ + Δ ⊩ (z ≔ e; F) ∷ 𝕆
| let_r (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body)
  (xs_𝕆 : (xs [∶] 𝕆) ⊆ Δ) (e_𝕆 : Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) (F_𝕆 : (z ∶ ℝ) :: Δ ⊩ F ∷ 𝕆) :
  Γ + Δ ⊩ (z ≔ e; F) ∷ 𝕆
| proj_bor (Γ : type_context) (x y : var) (F : fn_body) (i : cnstr)
  (x_𝔹 : (x ∶ 𝔹) ∈ Γ) (F_𝕆 : (y ∶ 𝔹) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ x[i]; F) ∷ 𝕆
| proj_own (Γ : type_context) (x y : var) (F : fn_body) (i : cnstr)
  (x_𝕆 : (x ∶ 𝕆) ∈ Γ) (F_𝕆 : (y ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆) :
  Γ ⊩ (y ≔ x[i]; inc y; F) ∷ 𝕆

notation β `; ` Γ ` ⊩ `:1 t := linear β Γ t

inductive linear_const (β : const → var → ob_lin_type) (δ : const → fn) : const → Prop
notation ` ⊩ `:1 c := linear_const c
| const (c : const)
  (F_𝕆 : β; (δ c).ys.map (λ y, y ∶ β c y) ⊩ (δ c).F ∷ 𝕆) :
  ⊩ c

notation β `; ` δ ` ⊩ `:1 c := linear_const β δ c

inductive linear_program (β : const → var → ob_lin_type) : (const → fn) → Prop
notation ` ⊩ `:1 δ := linear_program δ
| program (δ : const → fn)
  (δ_wf : β ⊢ δ) (const_typed : ∀ c : const, (β; δ ⊩ c)) :
  ⊩ δ

notation β `; ` δ ` ⊩ `:1 δᵣ := linear_program β δ δᵣ

@[simp] def 𝕆plus (x : var) (V : finset var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ V then F else inc x; F

@[simp] def 𝕆minus_var (x : var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ FV F then dec x; F else F

@[simp] def 𝕆minus (xs : list var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body := 
xs.foldr (λ x acc, 𝕆minus_var x acc βₗ) F

notation f `[` a `↦` b `]` := function.update f a b 

@[simp] def Capp : list (var × ob_lin_type) → fn_body → (var → ob_lin_type) → fn_body
| [] (z ≔ e; F) βₗ := z ≔ e; F
| ((y, t)::xs) (z ≔ e; F) βₗ := 
  if t = 𝕆 then
    let ys := xs.map (λ ⟨x, b⟩, x) in 
      𝕆plus y (ys.to_finset ∪ FV F) (Capp xs (z ≔ e; F) βₗ) βₗ
  else
    Capp xs (z ≔ e; 𝕆minus_var y F βₗ) βₗ
| xs F βₗ := F

@[simp] def C (β : const → var → ob_lin_type) : fn_body → (var → ob_lin_type) → fn_body
| (ret x) βₗ := 𝕆plus x ∅ (ret x) βₗ
| (case x of Fs) βₗ :=
  case x of Fs.map_wf (λ F h, 𝕆minus ((FV (case x of Fs)).sort var_le) (C F βₗ) βₗ)
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

constant β : const → var → ob_lin_type

section FV

open finset
open list

theorem FV_subset_finset_var {Γ Δ : finset var} {F : fn_body} (h : β; δ; Γ; Δ ⊢ F) : 
  FV F ⊆ Γ :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing Γ Δ },
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
    cases h₁,
    case or.inl { 
      cases h;
      simp at h₁,
      { simp [subset_iff] at h_ys_def ,
        exact h_ys_def h₁ },
      { simp [subset_iff] at h_ys_def,
        exact h_ys_def h₁ },
      { cases h₁; rw h₁; assumption },
      { simp [subset_iff] at h_ys_def,
        exact h_ys_def h₁ },
      { rw h₁, assumption },
      { rw h₁, assumption },
      { simp [subset_iff] at h_ys_def,
        cases h₁,
        { rw h₁, assumption },
        { exact h_ys_def h₁ } }
    },
    case or.inr { 
      cases h;
      cases h₁;
      { replace ih := subset_iff.mp (ih h_F_wf) h₁_right,
       rw mem_insert at ih,
       cases ih,
       { contradiction },
       { assumption } } 
    }
  },
  case «case» : x Fs ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
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
      have a_wf : (β; δ; Γ; Δ ⊢ a), from h_Fs_wf a a_in_Fs,
      have FV_a_sub_Γ : FV a ⊆ Γ, from ih a a_in_Fs a_wf,
      replace FV_a_sub_Γ := subset_iff.mp FV_a_sub_Γ,
      exact FV_a_sub_Γ y_in_l
    },
  },
  case «inc» : x F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    cases h₁,
    { rw h₁,
      assumption },
    { have h₂ : FV F ⊆ Γ, from ih h_F_wf,
      replace h₂ := subset_iff.mp h₂,
      exact h₂ h₁ }
  },
  case «dec» : x F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp at h₁,
    cases h,
    cases h₁,
    { rw h₁,
      assumption },
    { have h₂ : FV F ⊆ Γ, from ih h_F_wf,
      replace h₂ := subset_iff.mp h₂,
      exact h₂ h₁ }
  }
end

end FV

open finset

@[simp] lemma erase_insert_eq_erase {α : Type*} [decidable_eq α] (s : finset α) (a : α) : 
  erase (insert a s) a = erase s a :=
begin
  ext, 
  simp, 
  rw and_or_distrib_left,
  simp
end

lemma erase_insert_eq_insert_erase {α : Type*} [decidable_eq α] {a b : α} (s : finset α) (h : a ≠ b) :
  erase (insert a s) b = insert a (erase s b) :=
begin
  ext,
  simp,
  rw and_or_distrib_left,
  apply iff.intro;
  intro h₁;
  cases h₁,
  { exact or.inl h₁.right },
  { exact or.inr h₁ },
  { rw h₁, exact or.inl ⟨h, rfl⟩ },
  { exact or.inr h₁ }
end

theorem C_no_new_vars (F : fn_body) (βₗ : var → ob_lin_type) : FV (C β F βₗ) = FV F :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing βₗ },
  case ret : x {
    unfold C FV 𝕆plus, 
    split_ifs;
    simp
  },
  case «let» : x e F ih {
    unfold FV, 
    induction e,
    case rc_correctness.expr.const_app_full {
      simp, 
      have h : ∀ e_gys, e_ys ⊆ e_gys → FV (Capp (list.map (λ (y : var), (y, β e_c y)) e_ys) (x ≔ e_c⟦e_gys…⟧; C β F βₗ) βₗ) =
        list.to_finset e_gys ∪ erase (FV F) x, 
      { intros e_gys e_ys_sub_e_gys,
        induction e_ys;
        simp,
        { rw ih },
        { split_ifs;
          simp at *;
          cases e_ys_sub_e_gys,
          { exact e_ys_ih e_ys_sub_e_gys_right},
          { rw e_ys_ih e_ys_sub_e_gys_right, 
            apply insert_eq_of_mem, 
            apply mem_union_left, 
            simp, 
            assumption },
          { sorry -- pain
           }, sorry } }, sorry
    },
    case rc_correctness.expr.const_app_part {
      sorry
    },
    case rc_correctness.expr.var_app { 
      simp, 
      split_ifs; 
      simp at *; 
      rw ih at *
    },
    case rc_correctness.expr.ctor {
      simp, 
      have h : ∀ e_gys, e_ys ⊆ e_gys → FV (Capp (list.map (λ (y : var), (y, 𝕆)) e_ys) (x ≔ ⟪e_gys⟫e_i; C β F βₗ) βₗ) =
        list.to_finset e_gys ∪ erase (FV F) x, 
      { intros e_gys e_ys_sub_e_gys,
        induction e_ys;
        simp,
        { rw ih },
        { split_ifs;
          simp at *;
          cases e_ys_sub_e_gys,
          { exact e_ys_ih e_ys_sub_e_gys_right },
          { rw e_ys_ih e_ys_sub_e_gys_right, 
            apply insert_eq_of_mem, 
            apply mem_union_left, 
            simp, 
            assumption } } },
      exact h e_ys (list.subset_def.mpr (λ a, id))
    },
    case rc_correctness.expr.proj {
      simp, 
      split_ifs;
      simp at *;
      rw ih at *,
      have h : e_x = x ∨ e_x ≠ x, from dec_em (e_x = x),
      cases h,
      { rw h_2, simp },
      { rw erase_insert_eq_insert_erase (FV F) h_2, 
        simp }
    }, 
    case rc_correctness.expr.reset {
      simp, rw ih
    },
    case rc_correctness.expr.reuse {
      simp, 
      have h : ∀ e_gys, e_ys ⊆ e_gys → FV (Capp (list.map (λ (y : var), (y, 𝕆)) e_ys) (x ≔ reuse e_x in ⟪e_gys⟫e_i; C β F βₗ) βₗ) =
        insert e_x (list.to_finset e_gys ∪ erase (FV F) x), 
      { intros e_gys e_ys_sub_e_gys,
        induction e_ys;
        simp,
        { rw ih },
        { split_ifs;
          simp at *;
          cases e_ys_sub_e_gys,
          { exact e_ys_ih e_ys_sub_e_gys_right },
          { rw e_ys_ih e_ys_sub_e_gys_right, 
            apply insert_eq_of_mem, 
            apply mem_insert_of_mem,
            apply mem_union_left, 
            simp, 
            assumption } } },
      exact h e_ys (list.subset_def.mpr (λ a, id))
    }
  },
  case «case» {
    simp,
    sorry
    -- pain
  },
  case «inc» {
    simp
  },
  case «dec» {
    simp
  }
end

end rc_correctness
