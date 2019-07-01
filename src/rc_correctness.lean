import data.multiset

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

def const := ℕ

def ctor := ℕ

inductive expr : Type
| const_app_full (c : const) (ys : list var) : expr
| const_app_part (c : const) (ys : list var) : expr
| var_app (x : var) (y : var) : expr
| ctor_app (i : ctor) (ys : list var) : expr
| proj (i : ctor) (x : var) : expr
| reset (x : var) : expr
| reuse (x : var) (i : ctor) (ys : list var) : expr

inductive fn_body : Type
| return (x : var) : fn_body 
| «let» (x : var) (e : expr) (F : fn_body) : fn_body
| case (x : var) (Fs : list fn_body) : fn_body
| inc (x : var) (F : fn_body) : fn_body
| dec (x : var) (F : fn_body) : fn_body

def {l} fn_body.rec_wf (C : fn_body → Sort l)
  (return : Π (x : var), C (fn_body.return x))
  («let» : Π (x : var) (e : expr) (F : fn_body) (F_ih : C F), C (fn_body.let x e F))
  (case : Π (x : var) (Fs : list fn_body) (Fs_ih : ∀ F ∈ Fs, C F), C (fn_body.case x Fs))
  (inc : Π (x : var) (F : fn_body) (F_ih : C F), C (fn_body.inc x F))
  (dec : Π (x : var) (F : fn_body) (F_ih : C F), C (fn_body.dec x F)) : Π (x : fn_body), C x
| (fn_body.return a) := return a
| (fn_body.let x a a_1) := «let» x a a_1 (fn_body.rec_wf a_1)
| (fn_body.case a a_1) := case a a_1 (λ a h,
  have sizeof a < 1 + sizeof a_1, from nat.lt_add_left _ _ _ (list.sizeof_lt_sizeof_of_mem h),
  fn_body.rec_wf a)
| (fn_body.inc a a_1) := inc a a_1 (fn_body.rec_wf a_1)
| (fn_body.dec a a_1) := dec a a_1 (fn_body.rec_wf a_1)

def FV_expr : expr → list var
| (expr.const_app_full _ xs) := xs
| (expr.const_app_part c xs) := xs
| (expr.var_app x y) := [x, y]
| (expr.ctor_app i xs) := xs
| (expr.proj c x) := [x]
| (expr.reset x) := [x]
| (expr.reuse x i xs) := xs.insert x

def FV : fn_body → list var
| (fn_body.return x) := [x]
| (fn_body.let x e F) := FV_expr e ∪ ((FV F).filter (≠ x))
| (fn_body.case x Fs) := (Fs.map_wf (λ F h, FV F)).join.erase_dup.insert x
| (fn_body.inc x F) := (FV F).insert x
| (fn_body.dec x F) := (FV F).insert x

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

def erase_rc_fn_body : fn_body → fn_body
| (fn_body.let _ (expr.reset _) F) := erase_rc_fn_body F
| (fn_body.let z (expr.reuse x i ys) F) := fn_body.let z (expr.ctor_app i ys) (erase_rc_fn_body F)
| (fn_body.let x e F) := fn_body.let x e (erase_rc_fn_body F)
| (fn_body.inc _ F) := erase_rc_fn_body F
| (fn_body.dec _ F) := erase_rc_fn_body F
| (fn_body.case x cases) := fn_body.case x (cases.map_wf (λ c h, erase_rc_fn_body c))
| (fn_body.return x) := fn_body.return x 

def erase_rc_fn (f : fn) : fn := ⟨f.ys, erase_rc_fn_body f.F⟩ 

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
  → (Γ ⊩ fn_body.inc x F ∷ 𝕆)
| inc_b (Γ : type_context) (x : var) (F : fn_body) :
  ((x ∶ 𝔹) ∈ Γ) → ((x ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ fn_body.inc x F ∷ 𝕆)
| dec_o (Γ : type_context) (x : var) (F : fn_body) :
  (Γ ⊩ F ∷ 𝕆)
  → ((x ∶ 𝕆) :: Γ ⊩ fn_body.dec x F ∷ 𝕆)
| dec_r (Γ : type_context) (x : var) (F : fn_body) :
  (Γ ⊩ F ∷ 𝕆)
  → ((x ∶ ℝ) :: Γ ⊩ fn_body.dec x F ∷ 𝕆)
| return (Γ : type_context) (x : var) :
  (Γ ⊩ x ∷ 𝕆)
  → (Γ ⊩ fn_body.return x ∷ 𝕆)
| case_o (Γ : type_context) (x : var) (Fs : list fn_body) :
  ((x ∶ 𝕆) ∈ Γ) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
  → (Γ ⊩ fn_body.case x Fs ∷ 𝕆)
| case_b (Γ : type_context) (x : var) (Fs : list fn_body) :
  ((x ∶ 𝔹) ∈ Γ) → (∀ F ∈ Fs, Γ ⊩ ↑F ∷ 𝕆)
  → (Γ ⊩ fn_body.case x Fs ∷ 𝕆)
| const_app_full (Γys : list (type_context × var)) (c : const) :
  (∀ Γy ∈ Γys, (Γy : type_context × var).1 ⊩ Γy.2 ∷ β c Γy.2)
  → (multiset.join (Γys.map prod.fst) ⊩ expr.const_app_full c (Γys.map prod.snd) ∷ 𝕆)
| const_app_part (ys : list var) (c : const) :
  ys [∶] 𝕆 ⊩ expr.const_app_part c ys ∷ 𝕆
| var_app (x y : var) :
  (x ∶ 𝕆) :: (y ∶ 𝕆) :: 0 ⊩ expr.var_app x y ∷ 𝕆
| cnstr_app (ys : list var) (i : ctor) :
  ys [∶] 𝕆 ⊩ expr.ctor_app i ys ∷ 𝕆
| reset (x : var) :
  (x ∶ 𝕆) :: 0 ⊩ expr.reset x ∷ ℝ
| reuse (x : var) (ys : list var) (i : ctor) :
  (x ∶ ℝ) :: (ys [∶] 𝕆) ⊩ expr.reuse x i ys ∷ 𝕆
| let_o (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
  ((xs [∶] 𝕆) ⊆ Δ) → (Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) → ((z ∶ 𝕆) :: Δ ⊩ F ∷ 𝕆)
  → (Γ + Δ ⊩ fn_body.let z e F ∷ 𝕆)
| let_r (Γ : type_context) (xs : list var) (e : expr) (Δ : type_context) (z : var) (F : fn_body) :
  ((xs [∶] 𝕆) ⊆ Δ) → (Γ + (xs [∶] 𝔹) ⊩ e ∷ 𝕆) → ((z ∶ ℝ) :: Δ ⊩ F ∷ 𝕆)
  → (Γ + Δ ⊩ fn_body.let z e F ∷ 𝕆)
| proj_bor (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
  ((x ∶ 𝔹) ∈ Γ) → ((y ∶ 𝔹) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ fn_body.let y (expr.proj i x) F ∷ 𝕆)
| proj_own (Γ : type_context) (x y : var) (F : fn_body) (i : ctor) :
  ((x ∶ 𝕆) ∈ Γ) → ((y ∶ 𝕆) :: Γ ⊩ F ∷ 𝕆)
  → (Γ ⊩ fn_body.let y (expr.proj i x) (fn_body.inc y F) ∷ 𝕆)

notation β `; ` Γ ` ⊩ `:1 t := linear β Γ t

inductive linear_const (β : const → var → ob_lin_type) (δ : const → fn) : const → Prop
notation ` ⊩ `:1 c := linear_const c
| const (c : const) :
  (β; (δ c).ys.map (λ y, y ∶ β c y) ⊩ (δ c).F ∷ 𝕆)
  → (⊩ c)

notation β `; ` δ ` ⊩ `:1 c := linear_const β δ c

inductive linear_program (β : const → var → ob_lin_type) (δ : const → fn) : (const → fn) → Prop
notation ` ⊩ `:1 δ := linear_program δ
| program (δᵣ : const → fn) :
  (∀ c : const, δᵣ c = erase_rc_fn (δ c) ∧ (β; δᵣ ⊩ c))
  → (⊩ δᵣ)

notation β `; ` δ ` ⊩ `:1 δᵣ := linear_program β δ δᵣ

def 𝕆plus (x : var) (V : list var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ V then F else fn_body.inc x F

def 𝕆minus_var (x : var) (F : fn_body) (βₗ : var → ob_lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ FV F then fn_body.dec x F else F

def 𝕆minus : list var → fn_body → (var → ob_lin_type) → fn_body 
| [] F βₗ := F
| (x :: xs) F βₗ := 𝕆minus xs (𝕆minus_var x F βₗ) βₗ

def fn_update {α : Type} {β : Type} [decidable_eq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ x, if x = a then b else f x

notation f `[` a `↦` b `]` := fn_update f a b 

def Capp : list (var × ob_lin_type) → fn_body → (var → ob_lin_type) → fn_body
| [] (fn_body.let z e F) βₗ := fn_body.let z e F
| ((y, t)::xs) (fn_body.let z e F) βₗ := 
  if t = 𝕆 then
    let ys := xs.map (λ ⟨x, b⟩, x) in 
      𝕆plus y (ys ∪ FV F) (Capp xs (fn_body.let z e F) βₗ) βₗ
  else
    Capp xs (fn_body.let z e (𝕆minus_var y F βₗ)) βₗ
| xs F βₗ := F

def C (β : const → var → ob_lin_type) : fn_body → (var → ob_lin_type) → fn_body
| (fn_body.return x) βₗ := 𝕆plus x ∅ (fn_body.return x) βₗ
| (fn_body.case x Fs) βₗ := let ys := FV (fn_body.case x Fs) in 
  fn_body.case x (Fs.map_wf (λ F h, 𝕆minus ys (C F βₗ) βₗ))
| (fn_body.let y (expr.proj i x) F) βₗ := 
  if βₗ x = 𝕆 then
    fn_body.let y (expr.proj i x) (fn_body.inc y (𝕆minus_var x (C F βₗ) βₗ))
  else
    fn_body.let y (expr.proj i x) (C F (βₗ[y ↦ 𝔹]))
| (fn_body.let y (expr.reset x) F) βₗ := fn_body.let y (expr.reset x) (C F βₗ)
| (fn_body.let z (expr.const_app_full c ys) F) βₗ := Capp (ys.map (λ y, ⟨y, β c y⟩)) (fn_body.let z (expr.const_app_full c ys) (C F βₗ)) βₗ
| (fn_body.let z (expr.const_app_part c ys) F) βₗ := 
  Capp (ys.map (λ y, ⟨y, β c y⟩)) (fn_body.let z (expr.const_app_part c ys) (C F βₗ)) βₗ
| (fn_body.let z (expr.var_app x y) F) βₗ := 
  Capp ([⟨x, 𝕆⟩, ⟨y, 𝕆⟩]) (fn_body.let z (expr.var_app x y) (C F βₗ)) βₗ   
| (fn_body.let z (expr.ctor_app i ys) F) βₗ :=
  Capp (ys.map (λ y, ⟨y, 𝕆⟩)) (fn_body.let z (expr.ctor_app i ys) (C F βₗ)) βₗ
| (fn_body.let z (expr.reuse x i ys) F) βₗ :=
  Capp (ys.map (λ y, ⟨y, 𝕆⟩)) (fn_body.let z (expr.reuse x i ys) (C F βₗ)) βₗ
| F βₗ := F

inductive expr_wf (δ : const → fn) : multiset var → expr → Prop
notation Γ ` ⊢ `:1 e := expr_wf Γ e
| const_app_full (Γ : multiset var) (ys : list var) (c : const) :
  (↑ys ⊆ Γ) → (ys.length = (δ c).ys.length)
  → (Γ ⊢ expr.const_app_full c ys)
| const_app_part (Γ : multiset var) (c : const) (ys : list var) :
  (↑ys ⊆ Γ)
  → (Γ ⊢ expr.const_app_part c ys)
| var_app (Γ : multiset var) (x y : var) :
  (x ∈ Γ) → (y ∈ Γ)
  → (Γ ⊢ expr.var_app x y)
| ctor_app (Γ : multiset var) (i : ctor) (ys : list var) : 
  (↑ys ⊆ Γ)
  → (Γ ⊢ expr.ctor_app i ys)
| proj (Γ : multiset var) (x : var) (i : ctor) : 
  (x ∈ Γ)
  → (Γ ⊢ expr.proj i x)
| reset (Γ : multiset var) (x : var) :
  (x ∈ Γ)
  → (Γ ⊢ expr.reset x)
| reuse (Γ : multiset var) (x : var) (i : ctor) (ys : list var) :
  (↑ys ⊆ Γ) → (x ∈ Γ)
  → (Γ ⊢ expr.reuse x i ys)

notation δ `; ` Γ ` ⊢ `:1 e := expr_wf δ Γ e

inductive fn_body_wf (δ : const → fn) : multiset var → fn_body → Prop
notation Γ ` ⊢ `:1 f := fn_body_wf Γ f
| return (Γ : multiset var) (x : var) : 
  (x ∈ Γ)
  → (Γ ⊢ fn_body.return x)
| «let» (Γ : multiset var) (z : var) (e : expr) (F : fn_body) :
  (δ; Γ ⊢ e) → (z ∈ FV F) → (z ∉ Γ) → (z :: Γ ⊢ F)
  → (Γ ⊢ fn_body.let z e F)
| case (Γ : multiset var) (x : var) (Fs : list fn_body):
  (x ∈ Γ) → (∀ F ∈ Fs, Γ ⊢ F)
  → (Γ ⊢ fn_body.case x Fs)


notation δ `; ` Γ ` ⊢ `:1 f := fn_body_wf δ Γ f

inductive fn_wf (δ : const → fn) : fn → Prop
notation ` ⊢ `:1 f := fn_wf f
| fn (f : fn) : (δ; f.ys ⊢ f.F) → (⊢ f)

notation δ ` ⊢ `:1 f := fn_wf δ f

inductive const_wf (δ : const → fn) : const → Prop
notation ` ⊢ `:1 c := const_wf c
| const (c : const) : (δ ⊢ δ c) → (⊢ c)

notation δ ` ⊢ `:1 c := const_wf δ c

inductive reuse_fn_body_wf : multiset var → fn_body → Prop
notation Γ ` ⊢ᵣ `:1 f := reuse_fn_body_wf Γ f
| return (Γ : multiset var) (x : var) : Γ ⊢ᵣ fn_body.return x
| let_reset (Γ : multiset var) (z x : var) (F : fn_body) :
  (z :: Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.reset x) F)
| let_reuse (Γ : multiset var) (z x : var) (F : fn_body) (i : ctor) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (x :: Γ ⊢ᵣ fn_body.let z (expr.reuse x i ys) F)
| let_const_app_full (Γ : multiset var) (F : fn_body) (z : var) (c : const) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.const_app_full c ys) F)
| let_const_app_part (Γ : multiset var) (F : fn_body) (z : var) (c : const) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.const_app_part c ys) F)
| let_var_app (Γ : multiset var) (F : fn_body) (z x y : var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.var_app x y) F)
| let_ctor_app (Γ : multiset var) (F : fn_body) (z : var) (i : ctor) (ys : list var) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.ctor_app i ys) F)
| let_proj (Γ : multiset var) (F : fn_body) (z x : var) (i : ctor) :
  (Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.let z (expr.proj i x) F)
| case (Γ : multiset var) (x : var) (Fs : list fn_body) :
  (∀ F ∈ Fs, Γ ⊢ᵣ F)
  → (Γ ⊢ᵣ fn_body.case x Fs)

notation Γ ` ⊢ᵣ `:1 f := reuse_fn_body_wf Γ f

inductive reuse_const_wf (δ : const → fn) : const → Prop
notation ` ⊢ᵣ `:1 c := reuse_const_wf c
| const (c : const) :
  (δ; ∅ ⊢ (δ c).F) → (∅ ⊢ᵣ (δ c).F)
  → (⊢ᵣ c)

notation δ ` ⊢ᵣ `:1 c := reuse_const_wf δ c

constant δ : const → fn

open multiset
open list

theorem FV_e {Γ : multiset var} {e : expr} (h : δ; Γ ⊢ e) :
  ↑(FV_expr e) ⊆ Γ :=
begin
  induction e; 
  apply subset_iff.mpr; 
  intros x h₁;
  simp [FV_expr] at h₁;
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
  case return : x {
    apply subset_iff.mpr,
    intros y h₁, 
    simp [FV] at h₁,
    rw h₁,
    cases h,
    assumption
  },
  case «let» : x e F ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp [FV] at h₁,
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
  case case : x Fs ih {
    apply subset_iff.mpr,
    intros y h₁, 
    simp [FV] at h₁,
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
  case inc : x F ih {
    cases h
  },
  case dec : x F ih {
    cases h
  }
end

end rc_correctness
