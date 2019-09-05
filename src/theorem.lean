import compiler
import well_foundedness

namespace rc_correctness

open finset
open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.ob_lin_type
open rc_correctness.lin_type

section FV

open list

theorem FV_subset_finset_var {δ : const → fn} {β : const → var → ob_lin_type} {Γ Δ : finset var} {F : fn_body} 
  (h : β; δ; Γ; Δ ⊢ F) : 
  FV F ⊆ Γ :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing Γ Δ };
  simp only [subset_iff],
  case ret : x {
    intros y h₁, 
    simp only [FV, finset.mem_singleton, insert_empty_eq_singleton] at h₁,
    cases h,
    rwa h₁
  },
  case «let» : x e F ih {
    intros y h₁, 
    simp only [FV, mem_erase, finset.mem_union] at h₁,
    cases h₁,
    { cases h;
      simp only [FV_expr, mem_to_finset, mem_insert, 
                 finset.mem_singleton, has_insert_eq_insert, insert_empty_eq_singleton] at h₁;
      try { simp only [subset_iff, mem_to_finset] at h_ys_def };
      try { exact h_ys_def h₁ };
      try { rwa h₁ },
      { cases h₁; rwa h₁ },
      { cases h₁,
        { rwa h₁ },
        { exact h_ys_def h₁ } } },
    { cases h₁,
      cases h; 
      { replace ih := subset_iff.mp (ih h_F_wf) h₁_right,
        rw mem_insert at ih,
        cases ih,
        { contradiction },
        { assumption } } }
  },
  case «case» : x Fs ih {
    intros y h₁, 
    simp only [FV, mem_insert, finset.mem_join] at h₁,
    cases h,
    cases h₁, 
    { rwa h₁ },
    rw map_wf_eq_map at h₁,
    simp only [exists_prop, list.mem_map] at h₁,
    rcases h₁ with ⟨l, ⟨⟨a, ⟨a_in_Fs, FV_a_eq_l⟩⟩, y_in_l⟩⟩,
    rw ←FV_a_eq_l at y_in_l,
    have a_wf : (β; δ; Γ; Δ ⊢ a), from h_Fs_wf a a_in_Fs,
    have FV_a_sub_Γ : FV a ⊆ Γ, from ih a a_in_Fs a_wf,
    exact subset_iff.mp FV_a_sub_Γ y_in_l
  },
  all_goals {
    intros x F ih Γ Δ h y h₁,
    simp only [FV, mem_insert] at h₁,
    cases h,
    cases h₁,
    rwa h₁,
    have h₂ : FV F ⊆ Γ, from ih h_F_wf,
    exact subset_iff.mp h₂ h₁
  }
end

end FV

lemma FV_𝕆plus_eq_FV {x : var} {F : fn_body} (V : finset var) (βₗ : var → ob_lin_type) 
  (h : x ∈ FV F) :
  FV (inc_𝕆 x V F βₗ) = FV F :=
begin
  unfold inc_𝕆,
  split_ifs,
  { refl },
  unfold FV,
  exact insert_eq_of_mem h
end

lemma FV_dec_𝕆_sub_vars_FV (vars : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
  : FV (dec_𝕆 vars F βₗ) ⊆ vars.to_finset ∪ FV F :=
begin
  apply subset_iff.mpr,
  intros x h,
  unfold dec_𝕆 dec_𝕆_var at h,
  induction vars,
  { rw list.foldr_nil _ F at h, 
    simpa only [list.to_finset_nil, empty_union] },
  { simp only [mem_union, mem_insert, insert_union, list.mem_to_finset, list.to_finset_cons],
    rw list.foldr_cons _ F _ at h, 
    split_ifs at h,
    { cases h_1 with vars_hd_𝕆 h_2,
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

lemma FV_sub_FV_dec_𝕆 (vars : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
  : FV F ⊆ FV (dec_𝕆 vars F βₗ) :=
begin
  apply subset_iff.mpr,
  intros x h,
  unfold dec_𝕆 dec_𝕆_var,
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
  FV (C_app xs (z ≔ e; F1) βₗ) = FV (z ≔ e; F2) :=
begin
  induction xs generalizing F1 F2,
  { simp only [FV, C_app],
    rw heq },
  cases xs_hd with x τ,
  simp only [list.mem_cons_iff, list.forall_mem_cons'] at h,
  cases h with x_in_FV h,
  simp only [C_app, FV] at *, 
  cases τ,
  { rw if_pos rfl,
    unfold inc_𝕆, 
    split_ifs,
    { exact xs_ih heq h },
    unfold FV,
    rw xs_ih heq h,
    rw heq at x_in_FV,
    exact insert_eq_of_mem x_in_FV }, 
  { simp only [dec_𝕆_var, if_false], 
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

theorem C_no_new_vars (β : const → var → ob_lin_type) (F : fn_body) (βₗ : var → ob_lin_type) : FV (C β F βₗ) = FV F :=
begin
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing βₗ },
  case ret : x {
    unfold FV C inc_𝕆, 
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
      { rw mem_join at h, 
        rcases h with ⟨S, h, a_in_S⟩, 
        simp only [list.mem_map, function.comp_app] at h,
        rcases h with ⟨b, b_in_Fs, h⟩, 
        rw ←h at a_in_S,
        have h2, from FV_dec_𝕆_sub_vars_FV (sort var_le (insert x (join (list.map FV Fs)))) (C β b βₗ) βₗ,
        rw sort_to_finset _ at h2,
        have h3, from mem_of_subset h2 a_in_S,
        simp only [mem_union, mem_insert] at h3, 
        rcases h3 with ⟨l, m, r⟩,
        { exact or.inl h3 },
        { exact or.inr h3 },
        rw ih b b_in_Fs βₗ at h3,
        simp only [exists_prop, list.mem_map, mem_join],
        exact or.inr ⟨FV b, ⟨⟨b, ⟨b_in_Fs, rfl⟩⟩, h3⟩⟩ } },
    { intro h,
      apply mem_insert.mpr, 
      replace h := mem_insert.mp h,
      cases h,
      { exact or.inl h },
      { rw mem_join at h, 
        rcases h with ⟨S, h, a_in_S⟩, 
        rw list.mem_map at h,
        rcases h with ⟨b, ⟨b_in_Fs, FV_b_eq_S⟩⟩,
        apply or.inr,
        simp only [mem_join, exists_prop, list.mem_map, function.comp_app],
        apply exists.intro (FV (dec_𝕆 (sort var_le (insert x (join (list.map FV Fs)))) (C β b βₗ) βₗ)),
        apply and.intro,
        { exact ⟨b, ⟨b_in_Fs, rfl⟩⟩ },
        rw ←ih b b_in_Fs βₗ at FV_b_eq_S,
        rw ←FV_b_eq_S at a_in_S,
        have h, from FV_sub_FV_dec_𝕆 (sort var_le (insert x (join (list.map FV Fs)))) (C β b βₗ) βₗ,
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
      apply Exists.rec_on h,
      intros x h_h,
      apply and.rec_on h_h, 
      intros x_in_ys xτ_def, 
      cases xτ,
      rw ←xτ_def,
      simp only [FV, FV_expr, mem_union, mem_insert, insert_union, list.mem_to_finset, mem_erase]
    },
    { exact or.inl x_in_ys },
    { exact or.inl x_in_ys },
    { simp only [list.mem_cons_iff, list.mem_singleton] at h,
      simp only [FV, FV_expr, mem_union, mem_insert, insert_union, 
                 has_insert_eq_insert, insert_empty_eq_singleton, mem_singleton], 
      cases h;
      rw h,
      { exact or.inr (or.inl rfl) },
      { exact or.inl (rfl) } },
    { exact or.inl x_in_ys }, 
    { simp only [FV, C, dec_𝕆_var, FV_expr, insert_empty_eq_singleton], 
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
  all_goals { intros x F ih βₗ, simp only [FV, C] }
end

theorem rc_insertion_correctness (β : const → var → ob_lin_type) (δ : const → fn) (wf : β ⊢ δ) : β ⊩ C_prog β δ :=
begin
  cases wf,
  split,
  intro c,
  replace wf_const_wf := wf_const_wf c,
  cases wf_const_wf,
  rename wf_const_wf_F_wf wf,
  split,
  simp only [C_prog],
  set ys := (δ c).ys with ys_def,
  set F := (δ c).F with F_def,
  set F' := C β F (β c) with F'_def,
  sorry
end

end rc_correctness
