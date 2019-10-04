import type_system

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.lin_type

def inc_𝕆 (x : var) (V : finset var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ V then F else inc x; F

def dec_𝕆_var (x : var) (F : fn_body) (βₗ : var → lin_type) : fn_body :=
if βₗ x = 𝕆 ∧ x ∉ FV F then dec x; F else F

def dec_𝕆 (xs : list var) (F : fn_body) (βₗ : var → lin_type) : fn_body := 
xs.foldr (λ x acc, dec_𝕆_var x acc βₗ) F

def dec_𝕆' (xs : list var) (F : fn_body) (βₗ : var → lin_type) : fn_body := 
xs.foldr (λ x acc, if βₗ x = 𝕆 ∧ x ∉ FV F then dec x; acc else acc) F

def C_app : list (var × lin_type) → fn_body → (var → lin_type) → fn_body
| [] (z ≔ e; F) βₗ := z ≔ e; F
| ((y, t)::xs) (z ≔ e; F) βₗ := 
  if t = 𝕆 then
    inc_𝕆 y ((xs.map prod.fst).to_finset ∪ FV F) (C_app xs (z ≔ e; F) βₗ) βₗ
  else
    C_app xs (z ≔ e; dec_𝕆_var y F βₗ) βₗ
| xs F βₗ := F

def C (β : const → var → lin_type) : fn_body → (var → lin_type) → fn_body
| (ret x) βₗ := inc_𝕆 x finset.empty (ret x) βₗ
| (case x of Fs) βₗ :=
  case x of Fs.map_wf (λ F h, dec_𝕆 ((FV (case x of Fs)).sort var_le) (C F βₗ) βₗ)
| (y ≔ x[i]; F) βₗ := 
  if βₗ x = 𝕆 then
    y ≔ x[i]; inc y; dec_𝕆_var x (C F (βₗ[y ↦ 𝕆])) βₗ
  else
    y ≔ x[i]; C F (βₗ[y ↦ 𝔹])
| (z ≔ c⟦ys…⟧; F) βₗ := 
  C_app (ys.map (λ y, ⟨y, β c y⟩)) (z ≔ c⟦ys…⟧; C F (βₗ[z ↦ 𝕆])) βₗ
| (z ≔ c⟦ys…, _⟧; F) βₗ := 
  C_app (ys.map (λ y, ⟨y, β c y⟩)) (z ≔ c⟦ys…, _⟧; C F (βₗ[z ↦ 𝕆])) βₗ
| (z ≔ x⟦y⟧; F) βₗ := 
  C_app ([⟨x, 𝕆⟩, ⟨y, 𝕆⟩]) (z ≔ x⟦y⟧; C F (βₗ[z ↦ 𝕆])) βₗ   
| (z ≔ ⟪ys⟫i; F) βₗ :=
  C_app (ys.map (λ y, ⟨y, 𝕆⟩)) (z ≔ ⟪ys⟫i; C F (βₗ[z ↦ 𝕆])) βₗ
| F βₗ := F

def C_prog (β : const → var → lin_type) (δ : program) (c : const) : fn := 
  let (βₗ, f) := (β c, δ c) in ⟨f.ys, dec_𝕆 f.ys (C β f.F βₗ) βₗ⟩

end rc_correctness