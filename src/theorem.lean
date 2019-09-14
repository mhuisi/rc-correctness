import compiler
import well_foundedness

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.ob_lin_type
open rc_correctness.lin_type

section FV_wf
  open finset
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
end FV_wf

section FV_C
  open finset

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

  lemma FV_dec_𝕆_filter (ys : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
    : FV (dec_𝕆 ys F βₗ) = ys.to_finset.filter (λ y, βₗ y = 𝕆 ∧ y ∉ FV F) ∪ FV F :=
  begin
    induction ys,
    { simp only [dec_𝕆, filter_empty, finset.empty_union, list.to_finset_nil, list.foldr_nil] },
    simp only [dec_𝕆, dec_𝕆_var, filter_insert, list.foldr_cons, list.to_finset_cons] at *,
    split_ifs;
    try { simp only [FV, insert_union] }, 
    { rw ys_ih },
    { simp only [not_and, not_not] at h_1,
      have ys_hd_in_FV, from h_1 h.left,
      have : 
        FV (list.foldr (λ (x : var) (acc : fn_body), 
          ite (βₗ x = 𝕆 ∧ x ∉ FV acc) (dec x; acc) acc) 
          F ys_tl) = FV (dec_𝕆 ys_tl F βₗ), from rfl,
      rw this at h,
      exact absurd (subset_iff.mp (FV_sub_FV_dec_𝕆 ys_tl F βₗ) ys_hd_in_FV) h.right },
    { simp only [not_and, not_not] at h,
      have ys_hd_in_FV, from h h_1.left,
      rw ys_ih at *,
      rw insert_eq_of_mem ys_hd_in_FV },
    { rw ys_ih }
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
end FV_C

lemma vars_sub_FV_dec_𝕆 (ys : list var) (F : fn_body) (βₗ : var → ob_lin_type) 
  : ∀ y ∈ ys, βₗ y = 𝕆 → y ∈ FV (dec_𝕆 ys F βₗ) :=
begin
  intros y y_in_ys y𝕆,
  rw FV_dec_𝕆_filter,
  simp only [list.mem_to_finset, finset.mem_union, finset.mem_filter],
  by_cases y ∈ FV F,
  { exact or.inr h },
  { exact or.inl ⟨y_in_ys, y𝕆, h⟩ }
end

open multiset (hiding coe_sort)

axiom nodup_params (δ : const → fn) (c : const) : list.nodup (δ c).ys

lemma nodup_type_context_params (β : const → var → ob_lin_type) (δ : const → fn) (c : const) 
  : nodup (map (λ t, (t : typed_var).x) ↑(list.map (λ (y : var), y ∶ ↑(β c y)) (δ c).ys)) :=
begin
  simp only [coe_nodup, coe_map, list.map_map], 
  apply @nodup_map _ _ _ (δ c).ys,
  { unfold function.injective,
    intros a b h,
    simp only [function.comp_app] at h,
    assumption },
  simp only [coe_nodup],
  exact nodup_params δ c
end

lemma foo {β : const → var → ob_lin_type} {Γ : type_context} {ys : list var} {F : fn_body} {βₗ : var → ob_lin_type}
  (h : β; Γ ⊩ dec_𝕆 ys F βₗ ∷ 𝕆) : 
  β; Γ + (filter (λ y : var, βₗ y = 𝕆) ↑ys {∶} 𝕆) ⊩ F ∷ 𝕆 :=
begin
  induction ys,
  { simp only [coe_nil_eq_zero, add_zero, filter_zero, map_zero],
    simp only [dec_𝕆, list.foldr_nil] at h,
    assumption },
  simp only [dec_𝕆, dec_𝕆_var, list.foldr_cons] at h,
  split_ifs at h,
  sorry, sorry
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
  let ys := (δ c).ys,
  let Γ := (↑(list.map (λ (y : var), y ∶ ↑(β c y)) ys) : multiset typed_var),
  let y𝕆 := filter (λ y, β c y = 𝕆) ys,
  let y𝔹 := filter (λ y, β c y = 𝔹) ys,
  let yℝ := filter (λ y, ↑(β c y) = ℝ) ys,
  obtain ⟨y𝕆_𝕆, y𝔹_𝔹, yℝ_ℝ⟩ 
    : (∀ y ∈ y𝕆, ↑(β c y) = ↑𝕆) ∧ (∀ y ∈ y𝔹, ↑(β c y) = ↑𝔹) ∧ (∀ y ∈ yℝ, ↑(β c y) = ℝ),
  { repeat { split }; { intros y h, rw (mem_filter.mp h).right } },
  obtain ⟨y𝕆_sub_ys, y𝔹_sub_ys, yℝ_sub_ys⟩ 
    : (y𝕆 ⊆ ys ∧ y𝔹 ⊆ ys ∧ yℝ ⊆ ys),
  { repeat { split }; simp only [filter_subset] },
  obtain ⟨ys_𝕆_sub_y𝕆, ys_𝔹_sub_y𝔹, ys_ℝ_sub_yℝ⟩
    : (∀ y ∈ ys, ↑(β c y) = ↑𝕆 → y ∈ y𝕆) 
    ∧ (∀ y ∈ ys, ↑(β c y) = ↑𝔹 → y ∈ y𝔹) 
    ∧ (∀ y ∈ ys, ↑(β c y) = ℝ → y ∈ yℝ),
  { repeat { split };
    { intros y y_in_ys y_ty, 
      simp only [mem_filter, mem_coe], try { rw ←coe_eq_coe }, exact ⟨y_in_ys, y_ty⟩ } },
  obtain ⟨dj_y𝕆_y𝔹, dj_y𝕆_yℝ, dj_y𝔹_yℝ⟩ 
    : multiset.disjoint y𝕆 y𝔹 ∧ multiset.disjoint y𝕆 yℝ ∧ multiset.disjoint y𝔹 yℝ,
  { repeat { split };
    { rw disjoint_filter_filter,
      intros x x_in_ys x_ty,
      rw x_ty,
      try { unfold_coes },
      simp only [not_false_iff] } },
  have ys_subdiv : ↑ys = y𝕆 + y𝔹 + yℝ,
  { rw filter_add_filter,
    have : ∀ y ∈ ↑ys, β c y = 𝕆 ∧ β c y = 𝔹 ↔ false,
    { simp only [not_and, iff_false],
      intros y y_in_ys h,
      rw h, 
      simp only [not_false_iff] }, 
    simp only [@filter_congr _ _ _ _ _ ↑ys this, coe_nil_eq_zero, add_zero, filter_false],
    rw filter_add_filter,
    have : ∀ y ∈ ↑ys, (β c y = 𝕆 ∨ β c y = 𝔹) ∧ ↑(β c y) = ℝ ↔ false,
    { simp only [or_and_distrib_right, iff_false],
      intros y y_in_ys h,
      cases h;
      { unfold_coes at h,
        simp only [and_false] at h,
        contradiction } },
    simp only [@filter_congr _ _ _ _ _ ↑ys this, coe_nil_eq_zero, add_zero, filter_false],
    have : ∀ y ∈ ↑ys, (β c y = 𝕆 ∨ β c y = 𝔹) ∨ ↑(β c y) = ℝ ↔ true,
    { simp only [iff_true],
      intros y y_in_ys,
      unfold_coes,
      cases β c y; 
      simp only [true_or, false_or, or_false] },
    simp only [@filter_congr _ _ _ _ _ ↑ys this, filter_true] },
  have Γ_subdiv : ↑(list.map (λ (y : var), y ∶ ↑(β c y)) ys) = (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) + (yℝ {∶} ℝ),
  { have : ↑(list.map (λ (y : var), y ∶ ↑(β c y)) ys) = map (λ (y : var), y ∶ ↑(β c y)) ↑ys, 
      from rfl,
    rw this,
    rw ys_subdiv,
    simp only [map_add],  
    have : ∀ (τ : lin_type) (yτ : multiset var), (∀ y ∈ yτ, ↑(β c y) = τ) →
      ∀ y ∈ yτ, (y ∶ ↑(β c y)) = (y ∶ τ), 
    { intros τ yτ h y y_in_yτ, 
      rw h y y_in_yτ },
    simp only [map_congr (this 𝕆 y𝕆 y𝕆_𝕆), map_congr (this 𝔹 y𝔹 y𝔹_𝔹), map_congr (this ℝ yℝ yℝ_ℝ)] },
  have y𝕆_sub_FV : y𝕆.to_finset ⊆ FV (dec_𝕆 ((δ c).ys) (C β ((δ c).F) (β c)) (β c)), 
  { rw finset.subset_iff,
    intros y y_in_y𝕆,
    simp only [mem_filter, mem_coe, mem_to_finset] at y_in_y𝕆,
    exact vars_sub_FV_dec_𝕆 ys (C β ((δ c).F) (β c)) (β c) y y_in_y𝕆.left y_in_y𝕆.right },
  sorry
end

end rc_correctness