import type_system

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.ob_lin_type

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

end rc_correctness