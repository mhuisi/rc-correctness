import compiler
import well_foundedness

namespace rc_correctness

open rc_correctness.expr
open rc_correctness.fn_body
open rc_correctness.lin_type

section FV_wf
  open finset
  open list

  theorem FV_subset_finset_var {δ : const → fn} {β : const → var → lin_type} {Γ : finset var} {F : fn_body} 
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
        { cases h₁; rwa h₁ } },
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

  lemma FV_𝕆plus_eq_FV {x : var} {F : fn_body} (V : finset var) (βₗ : var → lin_type) 
    (h : x ∈ FV F) :
    FV (inc_𝕆 x V F βₗ) = FV F :=
  begin
    unfold inc_𝕆,
    split_ifs,
    { refl },
    unfold FV,
    exact insert_eq_of_mem h
  end

  lemma FV_sub_FV_dec_𝕆 (vars : list var) (F : fn_body) (βₗ : var → lin_type) 
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
      unfold inc_𝕆, 
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
        { rw ih (βₗ[x↦𝔹]) } },
    },
    all_goals { intros x F ih βₗ, simp only [FV, C] }
  end
end FV_C

section sandwich
  open finset

  lemma wf_sandwich {β : const → var → lin_type} {δ : const → fn} {Γ Γ' Γ'' : finset var} {F : fn_body} 
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
      cases hΓ,
      cases hΓ'',
      apply fn_body_wf.inc,
      { exact subset_iff.mp Γ_sub_Γ' hΓ_x_def },
      exact ih Γ_sub_Γ' Γ'_sub_Γ'' hΓ_F_wf hΓ''_F_wf
    },
    case «dec» : x F ih {
      cases hΓ,
      cases hΓ'',
      apply fn_body_wf.dec,
      { exact subset_iff.mp Γ_sub_Γ' hΓ_x_def },
      exact ih Γ_sub_Γ' Γ'_sub_Γ'' hΓ_F_wf hΓ''_F_wf
    }
  end

  lemma FV_wf {β : const → var → lin_type} {δ : const → fn} {Γ : finset var} {F : fn_body} (h : β; δ; Γ ⊢ F)
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
      cases mem_insert.mp (subset_iff.mp (FV_subset_finset_var h_F_wf) h_right), 
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
        exact subset_iff.mp (FV_subset_finset_var (h_Fs_wf a a_in_Fs)) x_in_S } },
    any_goals { apply fn_body_wf.dec <|> apply fn_body_wf.inc },
    any_goals { exact mem_insert_self h_x (FV h_F) },
    all_goals {
      apply wf_sandwich _ _ h_ih h_F_wf,
      { exact subset_insert h_x (FV h_F) },
      simp only [subset_iff, mem_insert],
      intros x h,
      cases h,
      { rwa h },
      exact subset_iff.mp (FV_subset_finset_var h_F_wf) h
    }
  end

  lemma wf_FV_sandwich {β : const → var → lin_type} {δ : const → fn} {Γ Γ' : finset var} {F : fn_body} 
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

axiom nodup_params (δ : const → fn) (c : const) : list.nodup (δ c).ys

lemma linear_dec_o_vars {β : const → var → lin_type} {Γ : type_context} {ys : list var} {F : fn_body} {βₗ : var → lin_type}
  (h : β; Γ ⊩ F ∷ 𝕆) (d : nodup ys)
  : β; (filter (λ y : var, βₗ y = 𝕆 ∧ y ∉ FV F) ↑ys {∶} 𝕆) + Γ ⊩ dec_𝕆 ys F βₗ ∷ 𝕆 :=
begin
  rw add_comm,
  rw dec_𝕆_eq_dec_𝕆'_of_nodup F βₗ d,
  induction ys,
  { simp only [coe_nil_eq_zero, add_zero, filter_zero, map_zero, list.foldr_nil],
    assumption },
  cases list.nodup_cons.mp d with ys_hd_not_in_ys_tl nodup_ys_tl,
  replace ys_ih := ys_ih nodup_ys_tl,
  simp only [dec_𝕆', list.foldr_cons, coe_filter, coe_map] at *,
  split_ifs,
  { rw @list.filter_cons_of_pos _ (λ (y : var), βₗ y = 𝕆 ∧ y ∉ FV F) _ _ ys_tl h_1,
    simp only [list.map],
    have : ∀ xs : list typed_var, (↑((ys_hd ∶ 𝕆) :: xs) : multiset typed_var) = (ys_hd ∶ 𝕆) :: ↑xs, from λ xs, rfl, 
    simp only [this, add_cons],
    apply linear.dec,
    assumption },
  { simp only [not_and, not_not] at h_1, 
    by_cases ys_hd_ty : βₗ ys_hd = 𝕆,
    { rwa @list.filter_cons_of_neg _ (λ (y : var), βₗ y = 𝕆 ∧ y ∉ FV F) _ _ ys_tl (λ h, absurd (h_1 ys_hd_ty) h.right) },
    { rwa @list.filter_cons_of_neg _ (λ (y : var), βₗ y = 𝕆 ∧ y ∉ FV F) _ _ ys_tl (λ h, absurd h.left ys_hd_ty) } }
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

theorem rc_insertion_correctness' (β : const → var → lin_type) (δ : const → fn) (c : const) 
  (y𝕆 y𝔹 yℝ : finset var)
  (y𝕆_𝕆 : ∀ y ∈ y𝕆, β c y = 𝕆) (y𝔹_𝔹 : ∀ y ∈ y𝔹, β c y = 𝔹)
  (y𝕆_sub_FV : y𝕆 ⊆ FV (δ c).F) (wf : β; δ; y𝕆 ∪ y𝔹 ⊢ (δ c).F)
  : β; (y𝕆.val {∶} 𝕆) + (y𝔹.val {∶} 𝔹) ⊩ C β ((δ c).F) (β c) ∷ 𝕆 :=
begin
  rw finset.subset_iff at y𝕆_sub_FV,
  with_cases { induction idef : (δ c).F using rc_correctness.fn_body.rec_wf },
  case ret : x {
    rw idef at *,
    unfold C,
    unfold FV at y𝕆_sub_FV,
    cases wf,
    simp only [mem_ndunion, finset.mem_mk] at wf_x_def,
    unfold inc_𝕆,
    cases wf_x_def,
    { have : β c x = 𝕆 ∧ x ∉ ∅, from ⟨y𝕆_𝕆 x wf_x_def, finset.not_mem_empty x⟩,
      rw if_pos this,
      have : y𝕆 = {x},
      { ext, 
        split;
        intro h,
        { exact y𝕆_sub_FV h },
        { rwa ←finset.mem_def at wf_x_def,
          simp only [finset.insert_empty_eq_singleton, finset.mem_singleton] at h,
          rwa h } },
      rw this,
      simp only [finset.singleton_val, finset.insert_empty_eq_singleton, zero_add, map_cons, cons_add, map_zero],
      apply linear.ret,
      rw ←singleton_add,
      apply inductive_weakening,
      apply linear.var }
  }
end

theorem rc_insertion_correctness (β : const → var → lin_type) (δ : const → fn) (wf : β ⊢ δ) : β ⊩ C_prog β δ :=
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
  { split; exact nodup_filter _ (coe_nodup.mpr (nodup_params δ c)) },
  have ys_subdiv : ↑ys = y𝕆 + y𝔹,
  { rw filter_add_filter,
    have : ∀ y ∈ ↑ys, β c y = 𝕆 ∧ β c y = 𝔹 ↔ false,
    { simp only [not_and, iff_false],
      intros y y_in_ys h,
      rw h, 
      simp only [not_false_iff] }, 
    simp only [@filter_congr _ _ _ _ _ ↑ys this, coe_nil_eq_zero, add_zero, filter_false],
    have : ∀ y ∈ ↑ys, β c y = 𝕆 ∨ β c y = 𝔹 ↔ true,
    { simp only [iff_true],
      intros y y_in_ys,
      cases β c y; 
      simp only [or_false, false_or] },
    simp only [@filter_congr _ _ _ _ _ ↑ys this, filter_true] },
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
  have y𝕆_subdiv : y𝕆 = filter (λ y, y ∉ FV (C β ((δ c).F) (β c))) y𝕆
                       + filter (λ y, y ∈ FV (C β ((δ c).F) (β c))) y𝕆,            
  { rw filter_add_filter, 
    simp only [coe_nil_eq_zero, add_zero, filter_false, not_and_self],
    have : ∀ a ∈ y𝕆, a ∉ FV (C β ((δ c).F) (β c)) ∨ a ∈ FV (C β ((δ c).F) (β c)) ↔ true,
    { simp only [or.symm, dec_em, iff_self, forall_true_iff] },
    simp only [filter_congr this, filter_true] },
  rw y𝕆_subdiv,
  rw map_add,
  rw filter_filter,
  have : ∀ a ∈ ↑ys, a ∉ FV (C β ((δ c).F) (β c)) ∧ β c a = 𝕆 ↔ β c a = 𝕆 ∧ a ∉ FV (C β ((δ c).F) (β c)),
  { intros a a_in_ys, split; intro h; exact and.symm h },
  rw @filter_congr _ _ _ _ _ ↑ys this,
  simp only [add_assoc],
  apply linear_dec_o_vars _ (nodup_params δ c), 
  let y𝕆' := filter (λ (y : var), y ∈ FV (C β ((δ c).F) (β c))) y𝕆,
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
    { have : FV (δ c).F ⊆ to_finset y𝕆 ∪ to_finset y𝔹, from FV_subset_finset_var wf,
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
    exact wf_FV_sandwich h1 h2 wf }
end

end rc_correctness
