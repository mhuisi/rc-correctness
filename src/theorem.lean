import compiler
import well_formedness

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.lin_type

lemma not_𝔹_iff_𝕆 {τ : lin_type} : τ ≠ 𝔹 ↔ τ = 𝕆 :=
begin
  cases τ; 
  split; intro h; contradiction <|> refl
end

lemma not_𝕆_iff_𝔹 {τ : lin_type} : τ ≠ 𝕆 ↔ τ = 𝔹 :=
begin
  cases τ; 
  split; intro h; contradiction <|> refl
end

section FV_wf
  open finset
  open list

  theorem FV_sub_wf_context {δ : program} {β : const → var → lin_type} {Γ : finset var} {F : fn_body} 
    (h : β; δ; Γ ⊢ F) : 
    FV F ⊆ Γ :=
  begin
    with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing Γ };
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
        cases h₁; rwa h₁ },
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
      have a_wf : (β; δ; Γ ⊢ a), from h_Fs_wf a a_in_Fs,
      have FV_a_sub_Γ : FV a ⊆ Γ, from ih a a_in_Fs a_wf,
      exact subset_iff.mp FV_a_sub_Γ y_in_l
    },
    all_goals {
      intros x F ih Γ h y h₁,
      cases h
    }
  end
end FV_wf

section FV_C
  open finset

  lemma FV_inc_𝕆_var_eq_FV {x : var} {F : fn_body} (V : finset var) (βₗ : var → lin_type) 
    (h : x ∈ FV F) :
    FV (inc_𝕆_var x V F βₗ) = FV F :=
  begin
    unfold inc_𝕆_var,
    split_ifs,
    { refl },
    unfold FV,
    exact insert_eq_of_mem h
  end

  lemma FV_sub_FV_dec_𝕆 (ys : list var) (F : fn_body) (βₗ : var → lin_type) 
    : FV F ⊆ FV (dec_𝕆 ys F βₗ) :=
  begin
    apply subset_iff.mpr,
    intros x h,
    unfold dec_𝕆 dec_𝕆_var,
    induction ys,
    { simpa only [list.foldr_nil] },
    simp only [list.foldr_cons],
    split_ifs,
    { simp only [FV, mem_insert],
      exact or.inr ys_ih },
    { exact ys_ih }
  end

  lemma FV_dec_𝕆_filter (ys : list var) (F : fn_body) (βₗ : var → lin_type) 
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

  lemma FV_dec_𝕆_sub_vars_FV (vars : list var) (F : fn_body) (βₗ : var → lin_type) 
  : FV (dec_𝕆 vars F βₗ) ⊆ vars.to_finset ∪ FV F :=
  begin
    simp only [FV_dec_𝕆_filter, subset_iff, mem_union, mem_filter, list.mem_to_finset], 
    intros x h,
    cases h,
    { exact or.inl h.left },
    { exact or.inr h }
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

  lemma FV_Capp_eq_FV {xs : list (var × lin_type)} {z : var} {e : expr} {F1 F2 : fn_body} (βₗ : var → lin_type)
    (heq : FV F1 = FV F2) (h : ∀ xτ ∈ xs, (xτ : var × lin_type).1 ∈ FV (z ≔ e; F1)) : 
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
      unfold inc_𝕆_var, 
      split_ifs,
      { exact xs_ih heq h },
      unfold FV,
      rw xs_ih heq h,
      rw heq at x_in_FV,
      exact insert_eq_of_mem x_in_FV }, 
    { simp only [dec_𝕆_var, if_false], 
      split_ifs,
      { suffices h2 : ∀ (xτ : var × lin_type), xτ ∈ xs_tl → xτ.fst ∈ FV_expr e ∪ erase (FV (dec x; F1)) z,
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

  theorem FV_C_eq_FV (β : const → var → lin_type) (F : fn_body) (βₗ : var → lin_type) : FV (C β F βₗ) = FV F :=
  begin
    with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing βₗ },
    case ret : x {
      unfold FV C inc_𝕆_var, 
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
        apply FV_Capp_eq_FV βₗ (ih (βₗ[x↦𝕆])),
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
        { rw ih (βₗ[x↦𝕆]) at *,
          have hem : e_x = x ∨ e_x ≠ x, from dec_em (e_x = x),
          cases hem,
          { rw hem at *,
            rw erase_insert_eq_erase, },
          { rw erase_insert_eq_insert_erase _ hem,
            simp } },
        { rw ih (βₗ[x↦𝕆]) },
        { rw ih (βₗ[x↦𝔹]) } },
    },
    all_goals { intros x F ih βₗ, simp only [FV, C] }
  end
end FV_C

section sandwich
  open finset

  lemma wf_sandwich {β : const → var → lin_type} {δ : program} {Γ Γ' Γ'' : finset var} {F : fn_body} 
    (Γ_sub_Γ' : Γ ⊆ Γ') (Γ'_sub_Γ'' : Γ' ⊆ Γ'') (hΓ : β; δ; Γ ⊢ F) (hΓ'' : β; δ; Γ'' ⊢ F)
    : β; δ; Γ' ⊢ F :=
  begin
    with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing Γ Γ' Γ'' },
    case ret : x {
      apply fn_body_wf.ret,
      cases hΓ,
      exact subset_iff.mp Γ_sub_Γ' hΓ_x_def
    },
    case «let» : x e F ih {
      cases e;
      cases hΓ;
      cases hΓ'';
      let h1 := insert_subset_insert x Γ_sub_Γ';
      let h2 := insert_subset_insert x Γ'_sub_Γ'',
      any_goals { 
        apply fn_body_wf.let_const_app_full 
        <|> apply fn_body_wf.let_const_app_part
        <|> apply fn_body_wf.let_var_app
        <|> apply fn_body_wf.let_ctor
        <|> apply fn_body_wf.let_proj },
      any_goals { assumption },
      any_goals {
        transitivity,
        { exact hΓ_ys_def },
        { assumption }
      },
      any_goals {
        intro h,
        have h', from subset_iff.mp Γ'_sub_Γ'' h,
        contradiction
      },
      any_goals { exact ih h1 h2 hΓ_F_wf hΓ''_F_wf },
      any_goals { exact subset_iff.mp Γ_sub_Γ' hΓ_x_def },
      any_goals { exact subset_iff.mp Γ_sub_Γ' hΓ_y_in_Γ }
    },
    case «case» : x Fs ih {
      cases hΓ,
      cases hΓ'',
      apply fn_body_wf.case,
      { exact subset_iff.mp Γ_sub_Γ' hΓ_x_def },
      intros F F_in_Fs,
      exact ih F F_in_Fs Γ_sub_Γ' Γ'_sub_Γ'' (hΓ_Fs_wf F F_in_Fs) (hΓ''_Fs_wf F F_in_Fs)
    },
    case «inc» : x F ih {
      cases hΓ
    },
    case «dec» : x F ih {
      cases hΓ
    }
  end

  lemma FV_wf {β : const → var → lin_type} {δ : program} {Γ : finset var} {F : fn_body} (h : β; δ; Γ ⊢ F)
    : β; δ; FV F ⊢ F :=
  begin
    induction h,
    { apply fn_body_wf.ret,
      simp only [FV, insert_empty_eq_singleton, mem_singleton] },
    any_goals {
      apply fn_body_wf.let_const_app_full
      <|> apply fn_body_wf.let_const_app_part
      <|> apply fn_body_wf.let_var_app
      <|> apply fn_body_wf.let_ctor
      <|> apply fn_body_wf.let_proj
    },
    any_goals { simp [FV, FV_expr, subset_union_left, not_or_distrib] },
    any_goals { 
      intro h,
      simp only [subset_iff, list.mem_to_finset] at h_ys_def,
      have : h_z ∈ h_Γ, from h_ys_def h,
      contradiction 
    },
    any_goals { split },
    any_goals { 
      intro h,
      rw h at h_z_undef,
      contradiction 
    },
    any_goals { apply wf_sandwich _ _ h_ih h_F_wf },
    any_goals { 
      simp only [subset_iff, mem_union, mem_insert, mem_erase],
      intros x x_in_FV,
      by_cases eq : x = h_z,
      { exact or.inl eq },
      { repeat { apply or.inr },
        exact ⟨eq, x_in_FV⟩ } 
    },
    any_goals { 
      apply insert_subset_insert,
      simp only [subset_iff, mem_union, list.mem_to_finset, mem_erase, mem_insert, mem_singleton],
      intros x h,
      repeat { cases h }
    },
    any_goals { 
      simp only [subset_iff, list.mem_to_finset] at h_ys_def,
      exact h_ys_def h 
    },
    any_goals { 
      cases mem_insert.mp (subset_iff.mp (FV_sub_wf_context h_F_wf) h_right), 
      { contradiction },
      { assumption } 
    }, 
    any_goals { assumption },
    { apply fn_body_wf.case,
      { exact mem_insert_self h_x _ },
      intros F F_in_Fs,
      apply wf_sandwich _ _ (h_ih F F_in_Fs) (h_Fs_wf F F_in_Fs);
      simp only [subset_iff, list.map_wf_eq_map, exists_prop, mem_join, mem_insert, list.mem_map], 
      { intros x x_in_FV, 
        apply or.inr,
        use FV F, 
        use F,
        { exact ⟨F_in_Fs, rfl⟩ },
        { assumption } },
      { intros x h,
        cases h,
        { rwa h },
        rcases h with ⟨S, ⟨⟨a, ⟨a_in_Fs, a_def⟩⟩, x_in_S⟩⟩,
        rw ←a_def at x_in_S,
        exact subset_iff.mp (FV_sub_wf_context (h_Fs_wf a a_in_Fs)) x_in_S } }
  end

  lemma wf_FV_sandwich {β : const → var → lin_type} {δ : program} {Γ Γ' : finset var} {F : fn_body} 
    (Γ'_low : FV F ⊆ Γ') (Γ'_high : Γ' ⊆ Γ) (h : β; δ; Γ ⊢ F)
    : β; δ; Γ' ⊢ F := wf_sandwich Γ'_low Γ'_high (FV_wf h) h
end sandwich

lemma vars_sub_FV_dec_𝕆 (ys : list var) (F : fn_body) (βₗ : var → lin_type) 
  : ∀ y ∈ ys, βₗ y = 𝕆 → y ∈ FV (dec_𝕆 ys F βₗ) :=
begin
  intros y y_in_ys y𝕆,
  rw FV_dec_𝕆_filter,
  simp only [list.mem_to_finset, finset.mem_union, finset.mem_filter],
  by_cases y ∈ FV F,
  { exact or.inr h },
  { exact or.inl ⟨y_in_ys, y𝕆, h⟩ }
end

lemma dec_𝕆_eq_dec_𝕆'_of_nodup {ys : list var} (F : fn_body) (βₗ : var → lin_type)
  (d : list.nodup ys) : dec_𝕆 ys F βₗ = dec_𝕆' ys F βₗ :=
begin
  unfold dec_𝕆 dec_𝕆_var dec_𝕆',
  induction ys,
  { simp only [list.foldr_nil] },
  cases list.nodup_cons.mp d with ys_hd_not_in_ys_tl nodup_ys_tl,
  simp only [list.foldr_cons],
  split_ifs,
  { exact ⟨rfl, ys_ih nodup_ys_tl⟩ },
  { simp only [not_and, not_not] at h_1,
    have g1, from h.right,
    have g2, from finset.subset_iff.mp (FV_sub_FV_dec_𝕆 ys_tl F βₗ) (h_1 h.left),
    contradiction },
  { simp only [not_and, not_not] at h,
    have g1, from h_1.right,
    have g2, from finset.subset_iff.mp (FV_dec_𝕆_sub_vars_FV ys_tl F βₗ) (h h_1.left),
    simp only [list.mem_to_finset, finset.mem_union] at g2,
    cases g2; contradiction },
  { exact ys_ih nodup_ys_tl }
end

open multiset (hiding coe_sort)

lemma inductive_dec' {β : const → var → lin_type} {ys : list var} {y𝕆 y𝔹 : multiset var} {F : fn_body} {βₗ : var → lin_type}
  (ys_sub_vars : ↑ys ⊆ y𝕆 + y𝔹) (d : list.nodup ys)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹) (nd_y𝕆 : nodup y𝕆) (nd_y𝔹 : nodup y𝔹)
  (h : β; (filter (λ y, y ∉ ys ∨ y ∈ FV F) y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ F ∷ 𝕆)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 ys F βₗ ∷ 𝕆 :=
begin
  have h_congr : ∀ {ys_hd : var} {ys_tl : list var} {ys' : multiset var} 
    (f : ∀ y ∈ ys', y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ FV F), 
    ∀ y ∈ ys', y ∉ (ys_hd :: ys_tl : list var) ∨ y ∈ FV F ↔ y ∉ ys_tl ∨ y ∈ FV F,
  { intros ys_hd ys_tl ys' f y y_in_ys',
    rw [list.mem_cons_iff, not_or_distrib],
    exact ⟨λ h', h'.elim (λ h'', or.inl h''.right) (λ h'', or.inr h''), 
           λ h', h'.elim (λ h'', f y y_in_ys' h'') (λ h'', or.inr h'')⟩ },
  rw dec_𝕆_eq_dec_𝕆'_of_nodup F βₗ d,
  induction ys generalizing y𝕆 y𝔹,
  { rw [dec_𝕆', list.foldr_nil], 
    simp only [list.not_mem_nil, true_or, not_false_iff, filter_true] at h, 
    assumption },
  cases list.nodup_cons.mp d with ys_hd_not_in_ys_tl nodup_ys_tl, 
  rw ←cons_coe at ys_sub_vars,
  simp only [cons_subset, mem_add] at ys_sub_vars,
  cases ys_sub_vars with ys_hd_def ys_tl_sub_vars,
  rw [dec_𝕆', list.foldr_cons], 
  split_ifs,
  { cases ys_hd_def, swap,
    { rw y𝔹_𝔹 ys_hd ys_hd_def at h_1,
      simp only [false_and] at h_1,
      contradiction },
    cases exists_cons_of_mem ys_hd_def with y𝕆' y𝕆_def,
    rw [y𝕆_def, map_cons, cons_add],
    apply linear.dec,
    apply ys_ih,
    { assumption },
    { rw y𝕆_def at ys_tl_sub_vars,
      rw subset_iff at ys_tl_sub_vars ⊢,
      intros x x_in_tl,
      let := ys_tl_sub_vars x_in_tl,
      simp only [mem_add, mem_cons] at this,
      repeat { cases this },
      { contradiction },
      { exact mem_add.mpr (or.inl this) },
      { exact mem_add.mpr (or.inr this) } },
    { simp only [y𝕆_def, mem_cons] at y𝕆_𝕆,
      intros y y_in_y𝕆',
      exact y𝕆_𝕆 y (or.inr y_in_y𝕆') },
    { assumption }, 
    { simp only [y𝕆_def, nodup_cons] at nd_y𝕆,
      exact nd_y𝕆.right },
    { assumption },
    { rw y𝕆_def at h nd_y𝕆,
      rw filter_cons_of_neg at h, swap,
      { simp, exact h_1.right },
      rw nodup_cons at nd_y𝕆,
      have : ∀ y ∈ y𝕆', y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ FV F,
      { intros y y_in_y𝕆' h',
        apply or.inl (and.intro _ h'),
        intro h',
        rw h' at y_in_y𝕆',
        exact absurd y_in_y𝕆' nd_y𝕆.left },
      rwa filter_congr (h_congr this) at h } },
  apply ys_ih,
  any_goals { assumption },
  rw not_and_distrib at h_1,
  cases h_1,
  { rw [←ne.def, not_𝕆_iff_𝔹] at h_1,
    cases ys_hd_def,
    { rw y𝕆_𝕆 ys_hd ys_hd_def at h_1,
      contradiction },
    have : ∀ y ∈ y𝕆, y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ FV F,
    { intros y y_in_y𝕆 h',
      apply or.inl (and.intro _ h'),
      intro h'',
      rw h'' at y_in_y𝕆,
      rw y𝕆_𝕆 ys_hd y_in_y𝕆 at h_1,
      contradiction },
    rwa filter_congr (h_congr this) at h },
  { have : ∀ y ∈ y𝕆, y ∉ ys_tl → ¬y = ys_hd ∧ y ∉ ys_tl ∨ y ∈ FV F,
    { intros y y_in_y𝕆 h',
      rw not_not at h_1,
      by_cases h'' : y = ys_hd,
      { rw h'',
        exact or.inr h_1 },
      { exact or.inl ⟨h'', h'⟩ } },
    rwa filter_congr (h_congr this) at h }
end

lemma inductive_dec {β : const → var → lin_type} {ys : list var} {y𝕆 y𝔹 : multiset var} {F : fn_body} {βₗ : var → lin_type}
  (y𝕆_sub_ys : y𝕆 ⊆ ↑ys) (ys_sub_vars : ↑ys ⊆ y𝕆 + y𝔹) (d : list.nodup ys)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, βₗ y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, βₗ y = 𝔹) (nd_y𝕆 : nodup y𝕆) (nd_y𝔹 : nodup y𝔹)
  (h : β; (filter (λ y, y ∈ FV F) y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ F ∷ 𝕆)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ dec_𝕆 ys F βₗ ∷ 𝕆 :=
begin
  have : ∀ y ∈ y𝕆, y ∈ FV F ↔ y ∉ ys ∨ y ∈ FV F,
  { intros y y_in_y𝕆,
    split; intro h',
    { exact or.inr h' },
    { cases h', 
      { exact absurd (y𝕆_sub_ys y_in_y𝕆) h' },
      { assumption } } },
  rw filter_congr this at h,
  exact inductive_dec' ys_sub_vars d y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹 h
end

lemma inductive_weakening {β : const → var → lin_type} {ys : multiset typed_var} {y𝔹 : multiset var} 
  {r : rc} {τ : lin_type} 
  (h : β; ys ⊩ r ∷ τ)
  : β; ys + (y𝔹 {∶} 𝔹) ⊩ r ∷ τ :=
begin
  apply multiset.induction_on y𝔹,
  { simp only [map_zero, add_zero], 
    assumption },
  intros a s ih,
  simp only [map_cons, add_cons],
  apply linear.weaken,
  assumption
end

theorem C_app_rc_insertion_correctness {β : const → var → lin_type} {βₗ : var → lin_type} {δ : program}
  {y : var} {e : expr} {F : fn_body} {y𝕆 y𝔹 : multiset var} {Γ : list (var × lin_type)}
  (ih : ∀ (βₗ : var → lin_type),
    nodup y𝕆 →
    nodup y𝔹 →
    (∀ (y : var), y ∈ y𝕆 → βₗ y = 𝕆) →
    (∀ (y : var), y ∈ y𝔹 → βₗ y = 𝔹) →
    (β; δ; to_finset y𝕆 ∪ to_finset y𝔹 ⊢ F) →
    (∀ ⦃x : var⦄, x ∈ y𝕆 → x ∈ FV F) →
    (β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ ↑(C β F βₗ) ∷ 𝕆))
  (nd_y𝕆 : nodup y𝕆) (nd_y𝔹 : nodup y𝔹)
  (y𝕆_𝕆 : ∀ (y : var), y ∈ y𝕆 → βₗ y = 𝕆)
  (y𝔹_𝔹 : ∀ (y : var), y ∈ y𝔹 → βₗ y = 𝔹)
  (wf : β; δ; to_finset y𝕆 ∪ to_finset y𝔹 ⊢ (y ≔ e; F))
  (y𝕆_free : ∀ ⦃x : var⦄, x ∈ y𝕆 → x ∈ FV (y ≔ e; F))
  (ty : β; (Γ.map (λ (yτ : var × lin_type), yτ.1 ∶ yτ.2)) ⊩ e ∷ 𝕆)
  : (β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ ↑(C_app Γ (y ≔ e; C β F (βₗ[y↦𝕆])) βₗ) ∷ 𝕆) :=
begin
  sorry
end

theorem rc_insertion_correctness' {β : const → var → lin_type} {δ : program} {c : const}
  {y𝕆 y𝔹 : multiset var}
  (nd_y𝕆 : nodup y𝕆) (nd_y𝔹 : nodup y𝔹)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, β c y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, β c y = 𝔹)
  (y𝕆_sub_FV : y𝕆.to_finset ⊆ FV (δ c).F) (wf : β; δ; y𝕆.to_finset ∪ y𝔹.to_finset ⊢ (δ c).F)
  : β; (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹) ⊩ C β ((δ c).F) (β c) ∷ 𝕆 :=
begin
  generalize h : β c = βₗ, 
  rw h at *,
  clear h,
  simp only [finset.subset_iff, mem_to_finset] at y𝕆_sub_FV,
  generalize h : (δ c).F = F,
  rw h at *,
  clear h,
  with_cases { induction F using rc_correctness.fn_body.rec_wf generalizing y𝕆 y𝔹 βₗ },
  case ret : x {
    unfold C,
    unfold FV at y𝕆_sub_FV,
    cases wf,
    simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, mem_erase_dup, finset.mem_mk] at wf_x_def,
    unfold inc_𝕆_var,
    cases wf_x_def,
    { have : βₗ x = 𝕆 ∧ x ∉ finset.empty, from ⟨y𝕆_𝕆 x wf_x_def, finset.not_mem_empty x⟩,
      rw if_pos this,
      have : y𝕆 = x :: 0,
      { rw nodup_ext nd_y𝕆 (nodup_singleton x),
        intro a,
        split;
        intro h,
        { exact y𝕆_sub_FV h },
        { rw mem_singleton at h,
          rwa h } },
      rw this,
      simp only [finset.singleton_val, finset.insert_empty_eq_singleton, zero_add, map_cons, cons_add, map_zero],
      rw ←singleton_add,
      apply inductive_weakening,
      apply linear.ret },
    { have : ¬(βₗ x = 𝕆 ∧ x ∉ finset.empty),
      { simp only [not_and], 
        intro h,
        rw y𝔹_𝔹 x wf_x_def at h, 
        simp only [] at h, 
        contradiction },
      rw if_neg this,
      apply linear.inc_𝔹,
      { apply mem_add.mpr,
        apply or.inr,
        exact mem_map_of_mem _ wf_x_def },
      have : y𝕆 = ∅,
      { apply eq_zero_of_forall_not_mem,
        simp only [finset.insert_empty_eq_singleton, finset.mem_singleton] at y𝕆_sub_FV,
        intros y y_in_y𝕆, 
        have x_in_y𝕆, from (y𝕆_sub_FV y_in_y𝕆).subst y_in_y𝕆,
        have dj : multiset.disjoint y𝕆 y𝔹,
        { rw disjoint_iff_ne,
          intros a a_in_y𝕆 b b_in_y𝔹 h,
          rw h at a_in_y𝕆,
          let := y𝕆_𝕆 b a_in_y𝕆,
          rw y𝔹_𝔹 b b_in_y𝔹 at this,
          contradiction },
        let := disjoint_right.mp dj wf_x_def,
        contradiction }, 
      simp only [this, empty_eq_zero, zero_add, map_zero],
      rw ←singleton_add,
      apply inductive_weakening,
      apply linear.ret } 
  },
  case «let» : y e F ih {
    with_cases { cases e },
    case rc_correctness.expr.proj : i x wf {
      unfold C,
      split_ifs,
      { have x_in_y𝕆 : x ∈ y𝕆,
        { let := subset_iff.mp (FV_sub_wf_context wf),
          simp only [FV, FV_expr, mem_union, finset.singleton_val, to_finset_val,
            finset.insert_empty_eq_singleton, mem_erase_dup, finset.erase_val,
            finset.union_val, mem_singleton] at this, 
          have h : x ∈ y𝕆 ∨ x ∈ y𝔹, from this (or.inl rfl),
          cases h,
          { assumption },
          { rw y𝔹_𝔹 x h_1 at h,
            contradiction } },
        apply linear.proj_𝕆,
        { simpa },
        unfold dec_𝕆_var,
        split_ifs,
        { rcases exists_cons_of_mem x_in_y𝕆 with ⟨y𝕆', y𝕆_def⟩,
          rw y𝕆_def at *,
          simp only [map_cons, cons_add],
          rw cons_swap,
          apply linear.dec,
          rw ←cons_add,
          rw ←map_cons (∶ 𝕆),
          apply ih,
          any_goals { assumption },
          { cases wf,
            simp only [not_or_distrib, mem_ndinsert, mem_ndunion, to_finset_val,
              mem_erase_dup, to_finset_cons, finset.insert_val, finset.mem_mk] at wf_z_undef,
            simp only [nodup_cons] at ⊢ nd_y𝕆,
            exact ⟨wf_z_undef.left.right, nd_y𝕆.right⟩ },
          { simp only [mem_cons],
            intros z z_in_y𝕆',
            cases z_in_y𝕆',
            { rw z_in_y𝕆',
              rw function.update_same },
            { by_cases z = y,
              { rw [h, function.update_same] },
              { rw function.update_noteq,
                { exact y𝕆_𝕆 z (mem_cons_of_mem z_in_y𝕆') },
                { assumption } } } },
          { intros z z_in_y𝔹,
            by_cases z = y,
            { cases wf,
              simp [not_or_distrib] at wf_z_undef,
              rw h at z_in_y𝔹,
              exact absurd z_in_y𝔹 wf_z_undef.right },
            { rw function.update_noteq,
              { exact y𝔹_𝔹 z z_in_y𝔹 },
              { assumption } } },
          { cases wf,
            apply wf_FV_sandwich _ _ wf_F_wf,
            { let := FV_sub_wf_context wf_F_wf,
              rw finset.subset_iff at ⊢ this,
              simp only [mem_ndinsert, mem_ndunion, to_finset_val, finset.insert_union, finset.mem_union,
                finset.mem_insert, mem_erase_dup, to_finset_cons, finset.insert_val, finset.mem_mk, mem_to_finset] at ⊢ this,
              intros z z_in_FV,
              have h', from this z_in_FV,
              repeat { cases h' },
              { exact or.inl rfl },
              { rw FV_C_eq_FV at h_1,
                exact absurd z_in_FV h_1.right },
              { exact or.inr (or.inl h') },
              { exact or.inr (or.inr h') } },
            { rw finset.subset_iff,
              simp only [mem_ndinsert, mem_ndunion, to_finset_val, finset.insert_union, finset.mem_union, finset.mem_insert,
                mem_erase_dup, to_finset_cons, finset.insert_val, finset.mem_mk, mem_to_finset],
              intros y h',
              repeat { cases h' },
              { exact or.inl rfl },
              { exact or.inr (or.inl (or.inr h')) },
              { exact or.inr (or.inr h') } } },
          { cases wf,
            simp only [FV, FV_expr, mem_cons, finset.insert_empty_eq_singleton, finset.mem_union, 
              finset.mem_singleton, finset.mem_erase] at ⊢ y𝕆_sub_FV,
            intros z h',
            cases h',
            { rwa h' },
            have h'', from y𝕆_sub_FV (or.inr h'),
            cases h'',
            { rw h'' at h',
              rw nodup_cons at nd_y𝕆,
              exact absurd h' nd_y𝕆.left },
            { exact h''.right } } },
        simp only [not_and_distrib, not_not] at h_1, 
        rw [←ne.def, not_𝕆_iff_𝔹] at h_1,
        cases h_1,
        { rw h at h_1, contradiction },
        rw ←cons_add,
        rw ←map_cons (∶ 𝕆), 
        apply ih,
        any_goals { assumption },
        { cases wf,
          simp only [nodup_cons],
          simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val,
            nodup_erase_dup, mem_erase_dup, finset.mem_mk] at wf_z_undef,
          exact ⟨wf_z_undef.left, nd_y𝕆⟩ },
        { simp only [mem_cons],
          intros z h',
          cases h',
          { rw h', rw function.update_same },
          { by_cases eq : y = z,
            { rw eq, rw function.update_same },
            rw function.update_noteq,
            { exact y𝕆_𝕆 z h' },
            symmetry,
            assumption } },
        { intros z z_in_y𝔹,
          by_cases z = y,
          { cases wf,
            simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup,
              mem_erase_dup, finset.mem_mk] at wf_z_undef,
            rw h at z_in_y𝔹,
            exact absurd z_in_y𝔹 wf_z_undef.right },
          { rw function.update_noteq,
            { exact y𝔹_𝔹 z z_in_y𝔹 },
            { assumption } } },
        { cases wf,
          apply wf_FV_sandwich _ _ wf_F_wf,
          { let := FV_sub_wf_context wf_F_wf,
            rw finset.subset_iff at ⊢ this,
            simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, finset.insert_union,
              finset.mem_union, finset.mem_insert, mem_erase_dup, to_finset_cons, finset.mem_mk, mem_to_finset] at ⊢ this,
            assumption },
          { rw finset.subset_iff,
            simp only [multiset.mem_erase_dup, multiset.mem_union, multiset.nodup_erase_dup, imp_self,
              multiset.to_finset_val, multiset.mem_to_finset, multiset.to_finset_cons, finset.insert_union,
              finset.mem_union, finset.mem_insert, finset.mem_mk, multiset.ndunion_eq_union, forall_true_iff] } },
        { cases wf,
          simp only [mem_cons],
          simp only [FV, FV_expr, finset.insert_empty_eq_singleton, finset.mem_union,
            finset.mem_singleton, finset.mem_erase] at y𝕆_sub_FV,
          intros z h',
          cases h',
          { rwa h' },
          have h'', from y𝕆_sub_FV h',
          cases h'',
          { rw h'',
            rwa FV_C_eq_FV at h_1 },
          { exact h''.right } } },
      rw [←ne.def, not_𝕆_iff_𝔹] at h,
      have x_in_y𝔹 : x ∈ y𝔹,
      { let := subset_iff.mp (FV_sub_wf_context wf),
        simp only [FV, FV_expr, mem_union, finset.singleton_val, to_finset_val,
          finset.insert_empty_eq_singleton, mem_erase_dup, finset.erase_val,
          finset.union_val, mem_singleton] at this, 
        have h : x ∈ y𝕆 ∨ x ∈ y𝔹, from this (or.inl rfl),
        cases h,
        { rw y𝕆_𝕆 x h_1 at h,
          contradiction },
        { assumption } },
      apply linear.proj_𝔹,
      { simpa },
      rw [add_comm, ←cons_add, add_comm, ←map_cons (∶ 𝔹)],
      apply ih,
      any_goals { assumption },
      { cases wf,
        simp only [nodup_cons],
        simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val,
          nodup_erase_dup, mem_erase_dup, finset.mem_mk] at wf_z_undef,
        exact ⟨wf_z_undef.right, nd_y𝔹⟩ },
      { intros z z_in_y𝕆,
        by_cases z = y,
        { cases wf,
          simp only [not_or_distrib, mem_union, ndunion_eq_union, to_finset_val,
            nodup_erase_dup, mem_erase_dup, finset.mem_mk] at wf_z_undef,
          rw h at z_in_y𝕆,
          exact absurd z_in_y𝕆 wf_z_undef.left },
        { rw function.update_noteq,
          { exact y𝕆_𝕆 z z_in_y𝕆 },
          { assumption } } },
      { simp only [mem_cons],
        intros z h',
        cases h',
        { rw h', rw function.update_same },
        { by_cases eq : y = z,
          { rw eq, rw function.update_same },
          rw function.update_noteq,
          { exact y𝔹_𝔹 z h' },
          symmetry,
          assumption } },
      { cases wf,
        apply wf_FV_sandwich _ _ wf_F_wf,
        { let := FV_sub_wf_context wf_F_wf,
          rw finset.subset_iff at ⊢ this,
          simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, finset.mem_union, finset.union_insert,
            finset.mem_insert, mem_erase_dup, to_finset_cons, finset.mem_mk, mem_to_finset] at ⊢ this,
          assumption },
        { rw finset.subset_iff,
          simp only [mem_erase_dup,mem_union, nodup_erase_dup, imp_self, to_finset_val, mem_to_finset, to_finset_cons,
            finset.mem_union, finset.union_insert, finset.mem_insert, finset.mem_mk, ndunion_eq_union, forall_true_iff] } },
      { simp only [FV, FV_expr, finset.insert_empty_eq_singleton, finset.mem_union, finset.mem_singleton, finset.mem_erase] at y𝕆_sub_FV,
        intros z z_in_y𝕆,
        have h', from y𝕆_sub_FV z_in_y𝕆,
        cases h',
        { rw h' at z_in_y𝕆,
          rw y𝕆_𝕆 x z_in_y𝕆 at h,
          contradiction },
        { exact h'.right } } 
    }, 
    case rc_correctness.expr.const_app_full : c' ys {
      unfold C,
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV,
      simp only [list.map_map],
      have : ∀ y ∈ ys, ((λ (yτ : var × lin_type), yτ.fst ∶ yτ.snd) ∘ (λ (y : var), (y, β c' y))) y = (λ (y : var), y ∶ β c' y) y,
      { intros y' y'_in_ys, 
        refl },
      rw list.map_congr this,
      exact linear.const_app_full β ys c'
    },
    case rc_correctness.expr.const_app_part : c' ys {
      unfold C,
      have : ∀ y ∈ ys, (y, β c' y) = (y, 𝕆),
      { cases wf,
        intros y' y'_in_ys,
        have not_𝔹, from wf_no_𝔹_var y',
        rw not_𝔹_iff_𝕆 at not_𝔹,
        rw not_𝔹 },
      rw list.map_congr this,
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV,
      rw list.map_map,
      have : ∀ y ∈ ys, ((λ (yτ : var × lin_type), yτ.fst ∶ yτ.snd) ∘ (λ (y : var), (y, 𝕆))) y = (λ (y : var), y ∶ 𝕆) y,
      { intros y' y'_in_ys, 
        refl },
      rw list.map_congr this,
      exact linear.const_app_part β ys c'
    },
    case rc_correctness.expr.var_app : x z {
      unfold C,
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV,
      simp only [list.map],
      exact linear.var_app β x z
    },
    case rc_correctness.expr.ctor : i ys {
      unfold C,
      apply C_app_rc_insertion_correctness ih nd_y𝕆 nd_y𝔹 y𝕆_𝕆 y𝔹_𝔹 wf y𝕆_sub_FV,
      rw list.map_map,
      have : ∀ y ∈ ys, ((λ (yτ : var × lin_type), yτ.fst ∶ yτ.snd) ∘ (λ (y : var), (y, 𝕆))) y = (λ (y : var), y ∶ 𝕆) y,
      { intros y' y'_in_ys, 
        refl },
      rw list.map_congr this,
      exact linear.ctor_app β ys i
    }
  },
  case «case» : x Fs ih {
    unfold C,
    have FV_sub_y𝕆_y𝔹 : (FV (case x of Fs)).val ⊆ y𝕆 + y𝔹,
    { let := FV_sub_wf_context wf,
      rw finset.subset_def at this,
      rw subset_iff at ⊢ this,
      simp only [mem_union, to_finset_val, mem_add, mem_erase_dup, finset.union_val] at ⊢ this,
      assumption },
    cases wf,
    simp only [mem_union, ndunion_eq_union, to_finset_val, nodup_erase_dup, mem_erase_dup, finset.mem_mk] at wf_x_def,
    cases wf_x_def,
    apply linear.case_𝕆, 
    { simpa },
    swap,
    apply linear.case_𝔹,
    { simpa },
    all_goals { 
      intros F' h,
      rw list.map_wf_eq_map at h, 
      rw list.mem_map at h,
      rcases h with ⟨F, ⟨F_in_Fs, F'_def⟩⟩, 
      rw ←F'_def,
      apply inductive_dec,
      any_goals { assumption },
      { rw subset_iff,
        rw finset.sort_eq,
        intros y y_in_y𝕆,
        exact y𝕆_sub_FV y_in_y𝕆 },
      { simp only [finset.sort_eq],
        assumption },
      { exact finset.sort_nodup var_le (FV (case x of Fs)) },
      apply ih,
      any_goals { assumption },
      { apply nodup_filter, 
        assumption },
      { simp only [and_imp, mem_filter, finset.mem_sort],
        intros y y_in_y𝕆 h,
        exact y𝕆_𝕆 y y_in_y𝕆 },
      { have wf, from wf_Fs_wf F F_in_Fs,
        apply wf_FV_sandwich _ _ wf,
        { rw finset.subset_iff,
          rw subset_iff at FV_sub_y𝕆_y𝔹,
          simp only [FV, list.map_wf_eq_map, mem_ndinsert, mem_add, finset.insert_val] at FV_sub_y𝕆_y𝔹, 
          simp [FV, list.map_wf_eq_map, not_or_distrib],
          intros y y_in_FV,
          replace FV_sub_y𝕆_y𝔹 := @FV_sub_y𝕆_y𝔹 y,
          rw ←finset.mem_def at FV_sub_y𝕆_y𝔹,
          simp only [exists_prop, list.mem_map, finset.mem_join] at FV_sub_y𝕆_y𝔹,
          rw FV_C_eq_FV,
          have : ∃ (S : finset var), (∃ (a : fn_body), a ∈ Fs ∧ FV a = S) ∧ y ∈ S,
          { use FV F, apply and.intro _ y_in_FV, use F, exact ⟨F_in_Fs, rfl⟩ },
          have : y ∈ y𝕆 ∨ y ∈ y𝔹, from FV_sub_y𝕆_y𝔹 (or.inr this),
          cases this,
          { exact or.inr ⟨this_1, y_in_FV⟩ },
          { exact or.inl this_1 } },
        { rw finset.subset_iff,
          simp only [mem_union, ndunion_eq_union, mem_filter, to_finset_val,
            nodup_erase_dup, finset.mem_union, mem_erase_dup, finset.mem_mk, mem_to_finset],
          intros y h,
          cases h,
          { exact or.inl (h.left) },
          { exact or.inr h } } },
      { simp only [and_imp, mem_filter, FV_C_eq_FV, imp_self, forall_true_iff] } 
    }
  },
  case «inc» : x F ih {
    cases wf
  },
  case «dec» : x F ih {
    cases wf
  }
end

theorem rc_insertion_correctness (β : const → var → lin_type) (δ : program) (wf : β ⊢ δ) : β ⊩ C_prog β δ :=
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
  let Γ := (↑(list.map (λ (y : var), y ∶ β c y) ys) : multiset typed_var),
  let y𝕆 := filter (λ y, β c y = 𝕆) ys,
  let y𝔹 := filter (λ y, β c y = 𝔹) ys,
  obtain ⟨y𝕆_𝕆, y𝔹_𝔹⟩ 
    : (∀ y ∈ y𝕆, β c y = 𝕆) ∧ (∀ y ∈ y𝔹, β c y = 𝔹),
  { repeat { split }; { intros y h, rw (mem_filter.mp h).right } },
  obtain ⟨y𝕆_sub_ys, y𝔹_sub_ys⟩ : (y𝕆 ⊆ ys ∧ y𝔹 ⊆ ys),
  { repeat { split }; simp only [filter_subset] },
  obtain ⟨ys_𝕆_sub_y𝕆, ys_𝔹_sub_y𝔹⟩
    : (∀ y ∈ ys, β c y = 𝕆 → y ∈ y𝕆) ∧ (∀ y ∈ ys, β c y = 𝔹 → y ∈ y𝔹),
  { repeat { split };
    { intros y y_in_ys y_ty, 
      simp only [mem_filter, mem_coe], try { rw ←coe_eq_coe }, exact ⟨y_in_ys, y_ty⟩ } },
  obtain ⟨nd_y𝕆, nd_y𝔹⟩ : multiset.nodup y𝕆 ∧ multiset.nodup y𝔹,
  { split; exact nodup_filter _ (coe_nodup.mpr wf_const_wf_nd_ys) },
  have ys_subdiv : ↑ys = y𝕆 + y𝔹,
  { have : ∀ y ∈ (↑ys : multiset var), β c y = 𝔹 ↔ β c y ≠ 𝕆, 
    { intros y y_in_ys,
      split; intro h; cases β c y; simp at h ⊢; assumption },
    simp only [y𝕆, y𝔹],
    rw filter_congr this,
    exact (filter_add_not ↑ys).symm },
  have Γ_subdiv : ↑(list.map (λ (y : var), y ∶ β c y) ys) = (y𝕆 {∶} 𝕆) + (y𝔹 {∶} 𝔹),
  { have : ↑(list.map (λ (y : var), y ∶ β c y) ys) = map (λ (y : var), y ∶ β c y) ↑ys, 
      from rfl,
    rw this,
    rw ys_subdiv,
    simp only [map_add],  
    have : ∀ (τ : lin_type) (yτ : multiset var), (∀ y ∈ yτ, β c y = τ) →
      ∀ y ∈ yτ, (y ∶ β c y) = (y ∶ τ), 
    { intros τ yτ h y y_in_yτ, 
      rw h y y_in_yτ },
    simp only [map_congr (this 𝕆 y𝕆 y𝕆_𝕆), map_congr (this 𝔹 y𝔹 y𝔹_𝔹)] },
  have y𝕆_sub_FV : y𝕆.to_finset ⊆ FV (dec_𝕆 ((δ c).ys) (C β ((δ c).F) (β c)) (β c)), 
  { rw finset.subset_iff,
    intros y y_in_y𝕆,
    simp only [mem_filter, mem_coe, mem_to_finset] at y_in_y𝕆,
    exact vars_sub_FV_dec_𝕆 ys (C β ((δ c).F) (β c)) (β c) y y_in_y𝕆.left y_in_y𝕆.right },
  rw Γ_subdiv,
  unfold list.to_finset at wf,
  rw ys_subdiv at wf,
  have : ↑ys ⊆ y𝕆 + y𝔹, { rw ys_subdiv, exact subset.refl _ },
  apply inductive_dec y𝕆_sub_ys this wf_const_wf_nd_ys y𝕆_𝕆 y𝔹_𝔹 nd_y𝕆 nd_y𝔹, 
  let y𝕆' := filter (λ (y : var), y ∈ FV (C β ((δ c).F) (β c))) y𝕆,
  have y𝕆'_𝕆 : ∀ y ∈ y𝕆', β c y = 𝕆,
  { simp only [and_imp, mem_filter, mem_coe], 
    intros y y_in_ys y_𝕆 y_in_FV,
    assumption },
  have nd_y𝕆' : nodup y𝕆', from nodup_filter _ nd_y𝕆,
  have y𝕆'_sub_y𝕆 : y𝕆' ⊆ y𝕆, from filter_subset y𝕆,
  have y𝕆'_sub_FV : y𝕆'.to_finset ⊆ FV (δ c).F,
  { rw finset.subset_iff, rw finset.subset_iff at y𝕆_sub_FV, rw subset_iff at y𝕆'_sub_y𝕆,
    simp only [mem_to_finset], simp only [mem_to_finset] at y𝕆_sub_FV,
    rw FV_dec_𝕆_filter at y𝕆_sub_FV, 
    intros x x_in_y𝕆',
    have h, from y𝕆_sub_FV (y𝕆'_sub_y𝕆 x_in_y𝕆'),
    simp only [mem_filter, mem_coe] at x_in_y𝕆',
    simp only [list.mem_to_finset, finset.mem_union, finset.mem_filter] at h,
    cases h,
    { exact absurd x_in_y𝕆'.right h.right.right },
    rwa FV_C_eq_FV at h },
  have wf' : (β; δ; to_finset y𝕆' ∪ to_finset y𝔹 ⊢ (δ c).F),
  { rw to_finset_add at wf,
    have h1 : FV (δ c).F ⊆ to_finset y𝕆' ∪ to_finset y𝔹,
    { have : FV (δ c).F ⊆ to_finset y𝕆 ∪ to_finset y𝔹, from FV_sub_wf_context wf,
      rw finset.subset_iff at this,
      rw finset.subset_iff,
      intros x x_in_FV,
      let := this x_in_FV,
      simp only [mem_filter, mem_coe, finset.mem_union, mem_to_finset] at this ⊢, 
      cases this,
      { rw FV_C_eq_FV,
        exact or.inl ⟨this_1, x_in_FV ⟩ },
      { exact or.inr this_1 } },
    have h2 : to_finset y𝕆' ∪ to_finset y𝔹 ⊆ to_finset y𝕆 ∪ to_finset y𝔹,
    { rw subset_iff at y𝕆'_sub_y𝕆,
      simp only [finset.subset_iff, finset.mem_union, mem_to_finset], 
      intros x h,
      cases h,
      { exact or.inl (y𝕆'_sub_y𝕆 h) },
      { exact or.inr h } },
    exact wf_FV_sandwich h1 h2 wf },
  exact rc_insertion_correctness' nd_y𝕆' nd_y𝔹 y𝕆'_𝕆 y𝔹_𝔹 y𝕆'_sub_FV wf'
end

end rc_correctness
