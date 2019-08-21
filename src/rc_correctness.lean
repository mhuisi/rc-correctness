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

@[simp] theorem mem_join_finset {α : Type*} [decidable_eq α] {x : α} {xs : list (finset α)} : x ∈ join_finset xs ↔ ∃ S ∈ xs, x ∈ S :=
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
| (y ≔ reset x; F) βₗ := 
  y ≔ reset x; C F βₗ
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

theorem FV_subset_finset_var {Γ Δ : finset var} {F : fn_body} 
  (h : β; δ; Γ; Δ ⊢ F) : 
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

lemma erase_insert_eq_insert_erase {α : Type*} [decidable_eq α] {a b : α} (s : finset α) 
  (h : a ≠ b) :
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

lemma FV_𝕆plus_eq_FV {x : var} {F : fn_body} (V : finset var) (βₗ : var → ob_lin_type) 
  (h : x ∈ FV F) :
  FV (𝕆plus x V F βₗ) = FV F :=
begin
  unfold 𝕆plus,
  split_ifs,
  { refl },
  unfold FV,
  exact insert_eq_of_mem h
end

-- cool sort lemmas that i didn't need in the end that are useful for
-- induction over a finset in a sort
lemma sort_empty {α : Type*} (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r] :
  sort r ∅ = [] :=
begin
  apply (multiset.coe_eq_zero (sort r ∅)).mp,
  simp only [sort_eq, empty_val]
end

lemma sort_split {α : Type*} [decidable_eq α] (p : α → α → Prop) [decidable_rel p]
  [is_trans α p] [is_antisymm α p] [is_total α p]
  (a : α) (s : finset α) :
  ∃ l r : list α, sort p (insert a s) = l ++ a :: r :=
list.mem_split ((mem_sort p).mpr (mem_insert_self a s))

lemma FV_𝕆minus_sub_vars_FV (vars : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
  : FV (𝕆minus vars F βₗ) ⊆ vars.to_finset ∪ FV F :=
begin
  apply subset_iff.mpr,
  intros x h,
  unfold 𝕆minus 𝕆minus_var at h,
  induction vars,
  { rw list.foldr_nil _ F at h, 
    simpa only [list.to_finset_nil, empty_union] },
  { simp only [mem_union, mem_insert, insert_union, list.mem_to_finset, list.to_finset_cons],
    rw list.foldr_cons _ F _ at h, 
    split_ifs at h,
    { cases h_1 with vars_hd_𝕆 h2,
      simp only [FV, mem_insert] at h,
      cases h, 
      { exact or.inl h },
      have x_tl_or_FV_F, from vars_ih h,
      simp only [mem_union, list.mem_to_finset] at x_tl_or_FV_F, 
      exact or.inr x_tl_or_FV_F },
    { have x_tl_or_FV_F, from vars_ih h,
      simp only [mem_union, list.mem_to_finset] at x_tl_or_FV_F, 
      exact or.inr x_tl_or_FV_F } }
end

lemma FV_sub_FV_𝕆minus (vars : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
  : FV F ⊆ FV (𝕆minus vars F βₗ) :=
begin
  apply subset_iff.mpr,
  intros x h,
  simp,
  induction vars,
  { simpa only [list.foldr_nil] },
  simp only [list.foldr_cons],
  split_ifs,
  { simp only [FV, mem_insert],
    exact or.inr vars_ih },
  { exact vars_ih }
end

lemma FV_dec_eq_FV {e : expr} {x z : var} {F : fn_body} 
  (h : x ∈ FV_expr e ∪ erase (FV F) z) : 
  FV_expr e ∪ erase (FV (dec x; F)) z = FV_expr e ∪ erase (FV F) z :=
begin
  unfold FV, 
  have hem : x = z ∨ x ≠ z, from dec_em (x = z),
  cases hem,
  { rw hem,
    rw erase_insert_eq_erase },
  { rw erase_insert_eq_insert_erase _ hem,
    simp only [union_insert],
    exact insert_eq_of_mem h }
end

lemma FV_Capp_eq_FV {xs : list (var × ob_lin_type)} {z : var} {e : expr} {F1 F2 : fn_body} (βₗ : var → ob_lin_type)
  (heq : FV F1 = FV F2) (h : ∀ xτ ∈ xs, (xτ : var × ob_lin_type).1 ∈ FV (z ≔ e; F1)) : 
  FV (Capp xs (z ≔ e; F1) βₗ) = FV (z ≔ e; F2) :=
begin
  induction xs generalizing F1 F2,
  { simp only [FV, Capp],
    rw heq },
  cases xs_hd with x τ,
  simp only [list.mem_cons_iff, list.forall_mem_cons'] at h,
  cases h with x_in_FV h,
  simp only [Capp, FV] at *, 
  cases τ,
  { rw if_pos rfl, -- trivial works for if_false, but not for if_true?
    unfold 𝕆plus, 
    split_ifs, -- need to be careful with simplifying. simplification can lead to undecidable props!
    { exact xs_ih heq h },
    unfold FV,
    rw xs_ih heq h,
    rw heq at x_in_FV,
    exact insert_eq_of_mem x_in_FV }, 
  { simp only [𝕆minus_var, if_false], 
    split_ifs,
    { suffices h2 : ∀ (xτ : var × ob_lin_type), xτ ∈ xs_tl → xτ.fst ∈ FV_expr e ∪ erase (FV (dec x; F1)) z,
      { have h3 : FV (dec x; F1) = FV (dec x; F2), from by
        { unfold FV, rw heq },
        rw xs_ih h3 h2, 
        rw heq at x_in_FV,
        exact FV_dec_eq_FV x_in_FV },
      { intros yτ yτ_in_tl,
        have y_in_FV, from h yτ yτ_in_tl,
        rwa FV_dec_eq_FV x_in_FV } },
    { exact xs_ih heq h } }
end

theorem C_no_new_vars (F : fn_body) (βₗ : var → ob_lin_type) : FV (C β F βₗ) = FV F :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing βₗ },
  case ret : x {
    unfold FV C 𝕆plus, 
    split_ifs;
    simp only [FV, insert_eq_of_mem, insert_empty_eq_singleton, mem_singleton]
  },
  case «case» : x Fs ih {
    unfold C FV, 
    repeat { rw list.map_wf_eq_map },
    simp only [list.map_map],
    ext,
    apply iff.intro,
    { intro h, 
      apply mem_insert.mpr, 
      replace h := mem_insert.mp h,
      cases h,
      { exact or.inl h },
      { rw mem_join_finset at h, 
        rcases h with ⟨S, h, a_in_S⟩, 
        simp only [list.mem_map, function.comp_app] at h,
        rcases h with ⟨b, b_in_Fs, h⟩, 
        rw ←h at a_in_S,
        have h2, from FV_𝕆minus_sub_vars_FV (sort var_le (insert x (join_finset (list.map FV Fs)))) (C β b βₗ) βₗ,
        rw sort_to_finset _ at h2,
        have h3, from mem_of_subset h2 a_in_S,
        simp only [mem_union, mem_insert] at h3, 
        rcases h3 with ⟨l, m, r⟩,
        { exact or.inl h3 },
        { exact or.inr h3 },
        rw ih b b_in_Fs βₗ at h3,
        simp only [exists_prop, list.mem_map, mem_join_finset],
        exact or.inr ⟨FV b, ⟨⟨b, ⟨b_in_Fs, rfl⟩⟩, h3⟩⟩ } },
    { intro h,
      apply mem_insert.mpr, 
      replace h := mem_insert.mp h,
      cases h,
      { exact or.inl h },
      { rw mem_join_finset at h, 
        rcases h with ⟨S, h, a_in_S⟩, 
        rw list.mem_map at h,
        rcases h with ⟨b, ⟨b_in_Fs, FV_b_eq_S⟩⟩,
        apply or.inr,
        simp only [mem_join_finset, exists_prop, list.mem_map, function.comp_app],
        apply exists.intro (FV (𝕆minus (sort var_le (insert x (join_finset (list.map FV Fs)))) (C β b βₗ) βₗ)),
        apply and.intro,
        { exact ⟨b, ⟨b_in_Fs, rfl⟩⟩ },
        rw ←ih b b_in_Fs βₗ at FV_b_eq_S,
        rw ←FV_b_eq_S at a_in_S,
        have h, from FV_sub_FV_𝕆minus (sort var_le (insert x (join_finset (list.map FV Fs)))) (C β b βₗ) βₗ,
        exact mem_of_subset h a_in_S } }
  },
  case «let» : x e F ih {
    induction e;
    unfold C;
    try {
      apply FV_Capp_eq_FV βₗ (ih βₗ),
      intros xτ h
    };
    try {
      rw list.mem_map at h,
      rcases h with ⟨x, ⟨x_in_ys, xτ_def⟩⟩, -- this rcases is super slow :(
      cases xτ,
      rw ←xτ_def,
      simp
    },
    { exact or.inl x_in_ys },
    { exact or.inl x_in_ys },
    { simp only [list.mem_cons_iff, list.mem_singleton] at h,
      simp,
      cases h;
      rw h,
      { exact or.inr (or.inl rfl) },
      { exact or.inl (rfl) } },
    { exact or.inl x_in_ys }, 
    { simp only [FV, C, 𝕆minus_var, FV_expr, insert_empty_eq_singleton], 
      split_ifs; 
      simp only [FV, erase_insert_eq_erase, FV_expr, insert_empty_eq_singleton],
      { rw ih βₗ at *,
        have hem : e_x = x ∨ e_x ≠ x, from dec_em (e_x = x),
        cases hem,
        { rw hem at *,
          rw erase_insert_eq_erase },
        { rw erase_insert_eq_insert_erase _ hem,
          simp } },
      { rw ih βₗ },
      { rw ih (βₗ[x↦𝔹]) }},
    { unfold FV,
      rw ih βₗ },
    { exact or.inr (or.inl x_in_ys) }
  },
  case «inc» {
    simp only [FV, C]
  },
  case «dec» {
    simp only [FV, C]
  }
end

end rc_correctness
