import tactic.fin_cases
import logic.function
import data.nat.basic

namespace list
  open well_founded_tactics

  -- sizeof_lt_sizeof_of_mem, map_wf, map_wf_eq_map courtesy of Sebastian Ullrich
  lemma sizeof_lt_sizeof_of_mem {α} [has_sizeof α] {a : α} : ∀ {l : list α}, a ∈ l → sizeof a < sizeof l
  | []      h := absurd h (not_mem_nil _)
  | (b::bs) h :=
  begin
    cases eq_or_mem_of_mem_cons h with h_1 h_2,
    subst h_1,
    { unfold_sizeof, cancel_nat_add_lt, trivial_nat_lt },
    { have aux₁ := sizeof_lt_sizeof_of_mem h_2,
      unfold_sizeof,
      exact nat.lt_add_left _ _ _ (nat.lt_add_left _ _ _ aux₁) }
  end

  def map_wf {α β : Type*} [has_sizeof α] (xs : list α) (f : Π (a : α), (sizeof a < 1 + sizeof xs) → β) : list β :=
  xs.attach.map (λ p, have sizeof p.val < 1 + sizeof xs, 
                        from nat.lt_add_left _ _ _ (list.sizeof_lt_sizeof_of_mem p.property),
                      f p.val this)

  lemma map_wf_eq_map {α β : Type*} [has_sizeof α] {xs : list α} {f : α → β} : map_wf xs (λ a _, f a) = map f xs :=
  by simp only [map_wf, attach, map_pmap, pmap_eq_map]

  lemma filter_cons {α : Type*} (p : α → Prop) [decidable_pred p] (a : α) (l : list α)
    : filter p (a :: l) = a :: filter p l ∨ filter p (a :: l) = filter p l :=
  by { by_cases p a, { exact or.inl (filter_cons_of_pos l h) }, { exact or.inr (filter_cons_of_neg l h) } }

  lemma sizeof_filter_le_sizeof {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) : list.sizeof (filter p xs) <= list.sizeof xs :=
  begin
    induction xs,
    { rw list.filter_nil },
    cases filter_cons p xs_hd xs_tl; rw h; unfold_sizeof,
    { assumption },
    { exact le_add_left xs_ih }
  end

  lemma all_map_iff_all {α : Type*} (p : α → bool) (xs : list α) : list.all (list.map p xs) id ↔ list.all xs p :=
  begin
    simp only [all_iff_forall, and_imp, mem_map, exists_imp_distrib],
    split;
    intro h,
    { intros a a_in_xs,
      cases h' : p a;
      exact h _ a a_in_xs h' },
    intros b a a_in_xs h',
    exact h'.subst (h a a_in_xs)
  end
  
  structure context (α : Type*) := (pre : list α) (x : α) (post : list α)

  instance context_to_list {α : Type*} : has_coe (context α) (list α) := 
  ⟨λ c, c.pre ++ c.x :: c.post⟩

  def contexts_aux {α : Type*} : list α → list α → list (context α)
  | pre [] := []
  | pre (x :: xs) := ⟨pre, x, xs⟩ :: contexts_aux (pre.concat x) xs

  def contexts {α : Type*} (xs : list α) : list (context α) := contexts_aux [] xs

  lemma contexts_aux_pre_cons_elim {α : Type*} (p : α) (pre xs : list α)
    : contexts_aux (p :: pre) xs = map (λ c : context α, ⟨p :: c.pre, c.x, c.post⟩) (contexts_aux pre xs) :=
  begin
    induction xs generalizing pre, 
    { simp only [contexts_aux, map] },
    simp [contexts_aux, xs_ih _]
  end

  lemma contexts_aux_pre_elim {α : Type*} (pre xs : list α)
    : contexts_aux pre xs = map (λ c : context α, ⟨pre ++ c.pre, c.x, c.post⟩) (contexts_aux [] xs) :=
  begin
    induction pre,
    { simp only [nil_append],
      have : (λ (c : context α), (⟨c.pre, c.x, c.post⟩ : context α)) = id,
      { ext, cases x, refl },
      rw [this, map_id] },
    simp only [contexts_aux_pre_cons_elim _ _, pre_ih, cons_append, map_map]
  end

  lemma contexts_nil (α : Type*) : contexts ([] : list α) = [] := rfl

  lemma contexts_cons {α : Type*} (x : α) (xs : list α) 
    : contexts (x :: xs) = ⟨[], x, xs⟩ :: contexts_aux [x] xs := rfl

  lemma of_mem_contexts_aux {α : Type*} {pre xs : list α} {c : context α} 
    : c ∈ contexts_aux pre xs → pre ++ xs = ↑c :=
  begin
    intro c_context,
    induction xs generalizing pre;
    simp only [contexts_aux, not_mem_nil, mem_cons_iff] at c_context,
    { contradiction },
    cases c_context,
    { rw c_context, refl },
    rw ←xs_ih c_context,
    simp only [cons_append, nil_append, append_assoc, concat_eq_append]
  end

  lemma of_mem_contexts {α : Type*} {pre xs : list α} {c : context α} 
    : c ∈ contexts xs → xs = ↑c := of_mem_contexts_aux

  lemma mem_contexts_self {α : Type*} (c : context α) : c ∈ contexts (↑c : list α) :=
  begin
    cases c,
    induction c_pre;
    unfold_coes,
    { simp only [nil_append, contexts_cons, mem_cons_self] },
    simp only [contexts, contexts_aux, mem_cons_iff, cons_append, concat_eq_append, false_or, nil_append, false_and],
    unfold_coes at c_pre_ih,
    rw [contexts_aux_pre_elim, mem_map],
    use ⟨c_pre_tl, c_x, c_post⟩,
    simpa
  end

  def group {α : Type*} [p : setoid α] [decidable_rel p.r] : list α → list (list α) 
  | []        := []
  | (x :: xs) := have list.sizeof (filter (not ∘ (≈ x)) xs) < 1 + list.sizeof xs, from 
    by { rw [nat.add_comm, ←nat.succ_eq_add_one, nat.lt_succ_iff], exact sizeof_filter_le_sizeof _ xs },
    (x :: filter (≈ x) xs) :: group (filter (not ∘ (≈ x)) xs)

  lemma sizeof_lt_of_length_lt {α : Type*} {xs ys : list α} (h : length xs < length ys) : list.sizeof xs < list.sizeof ys :=
  begin
    induction xs generalizing ys,
    { induction ys;
      unfold_sizeof,
      { exact absurd h (lt_irrefl (length nil)) },
      induction ys_tl;
      unfold_sizeof,
      { exact zero_lt_one },
      exact nat.zero_lt_one_add (list.sizeof ys_tl_tl) },
    induction ys;
    unfold_sizeof,
    { simp only [add_comm, length] at h, 
      exact false.elim (nat.not_succ_le_zero (1 + length xs_tl) h) },
    simp only [add_comm, length, add_lt_add_iff_left] at h,
    exact xs_ih h
  end

  @[elab_as_eliminator] def strong_induction_on {α : Type*} {p : list α → Sort*} :
    ∀ xs : list α, (∀ xs, (∀ ys, length ys < length xs → p ys) → p xs) → p xs
  | xs := λ ih, ih xs (λ ys h1, 
    have list.sizeof ys < list.sizeof xs, from sizeof_lt_of_length_lt h1,
    strong_induction_on ys ih)

  lemma length_filter_le_length {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) : 
    length (filter p xs) <= length xs := 
  length_le_of_sublist (filter_sublist xs)

  lemma filter_append_not_filter_perm {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) : 
    filter p xs ++ filter (not ∘ p) xs ~ xs :=
  begin
    letI := classical.dec_eq α,
    rw perm_iff_count,
    intro a,
    induction xs,
    { simp only [filter_nil, append_nil] },
    by_cases p xs_hd,
    { rw filter_cons_of_pos xs_tl h,
      rw @filter_cons_of_neg _ (not ∘ p) _ _ xs_tl (non_contradictory_intro h),
      simpa only [cons_append, count_cons', add_right_inj] },
    { rw @filter_cons_of_pos _ (not ∘ p) _ _ xs_tl h,
      rw filter_cons_of_neg xs_tl h, 
      simp only [count_append, count_cons'],
      rwa [←add_assoc, add_right_inj, ←count_append] }
  end

  lemma length_filter_lt_length_cons {α : Type*} (p : α → Prop) [decidable_pred p] (x : α) (xs : list α) : 
    length (filter p xs) < length (x :: xs) :=
  calc length (filter p xs) 
        ≤ length xs        : length_filter_le_length _ xs
    ... < length (x :: xs) : by simp only [lt_add_iff_pos_left, add_comm, length, nat.zero_lt_one]

  lemma join_group_perm {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α) : join (group xs) ~ xs :=
  begin
    letI := classical.dec_eq α,
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { refl },
    have perm := ih (filter (not ∘ (≈ xs_hd)) xs_tl) (length_filter_lt_length_cons _ xs_hd xs_tl),
    rw perm_iff_count at ⊢ perm,
    intro a,
    simp only [group, cons_append, join, count_cons', add_right_inj, count_append, perm a] at ⊢ ih,
    rw ←count_append,
    revert a,
    rw ←perm_iff_count,
    exact filter_append_not_filter_perm (≈ xs_hd) xs_tl
  end

  lemma group_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs g : list α} {x y : α}: 
    g ∈ group xs → x ∈ g → y ∈ g → x ≈ y :=
  begin
    intros g_group x_in_g y_in_g,
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [group, not_mem_nil] at g_group,
      contradiction },
    simp only [group, mem_cons_iff] at g_group,
    cases g_group,
    { rw g_group at *,
      simp only [mem_cons_iff, mem_filter] at x_in_g y_in_g,
      cases x_in_g,
      { rw x_in_g,
        cases y_in_g,
        { rw y_in_g },
        { symmetry,
          exact y_in_g.right } },
      { cases y_in_g,
        { rw ←y_in_g at x_in_g,
          exact x_in_g.right },
        { transitivity,
          { exact x_in_g.right },
          { symmetry, 
            exact y_in_g.right } } } },
    exact ih _ (length_filter_lt_length_cons _ xs_hd xs_tl) g_group
  end

  lemma nil_not_mem_group {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α)
    : [] ∉ group xs :=
  begin
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [group], exact not_mem_nil nil },
    simp only [group, mem_cons_iff],
    rw not_or_distrib,
    simp only [true_and, not_false_iff],
    exact ih (filter (not ∘ λ (_x : α), _x ≈ xs_hd) xs_tl) (length_filter_lt_length_cons _ xs_hd xs_tl)
  end

  lemma group_equiv_disjoint' {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α) : 
    ∀ g1 g2 ∈ group xs, (∀ x1 ∈ g1, ∀ x2 ∈ g2, x1 ≈ x2) → g1 = g2 :=
  begin
    intros g1 g2 g1_group g2_group h,
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [group, not_mem_nil] at g1_group,
      contradiction },
    simp only [group, mem_cons_iff] at g1_group g2_group,
    cases g1_group,
    { rw g1_group at *,
      cases g2_group,
      { rw g2_group at * },
      { cases g2,
        { exact absurd g2_group (nil_not_mem_group _) },
        have h3 : ∃ l, l ∈ group (filter (not ∘ λ (_x : α), _x ≈ xs_hd) xs_tl) ∧ g2_hd ∈ l, 
        from ⟨g2_hd :: g2_tl, ⟨g2_group, mem_cons_self g2_hd g2_tl⟩⟩,
        replace h3 := mem_join.mpr h3,
        rw mem_of_perm (join_group_perm _) at h3,
        replace h3 := of_mem_filter h3,
        simp only [function.comp_app] at h3,
        have h4 : g2_hd ≈ xs_hd, 
        { symmetry,
          exact h xs_hd (mem_cons_self xs_hd _) g2_hd (mem_cons_self g2_hd g2_tl) },
        contradiction } },
    cases g2_group,
    rw g2_group at *,
    { cases g1,
      { exact absurd g1_group (nil_not_mem_group _) },
      have h3 : ∃ l, l ∈ group (filter (not ∘ λ (_x : α), _x ≈ xs_hd) xs_tl) ∧ g1_hd ∈ l, 
      from ⟨g1_hd :: g1_tl, ⟨g1_group, mem_cons_self g1_hd g1_tl⟩⟩,
      replace h3 := mem_join.mpr h3,
      rw mem_of_perm (join_group_perm _) at h3,
      replace h3 := of_mem_filter h3,
      simp only [function.comp_app] at h3,
      have h4 : g1_hd ≈ xs_hd, from h g1_hd (mem_cons_self g1_hd g1_tl) xs_hd (mem_cons_self xs_hd _),
      contradiction },
    exact ih _ (length_filter_lt_length_cons _ xs_hd xs_tl) g1_group g2_group
  end

  section group_equiv_disjoint 
    local attribute [instance] classical.prop_decidable
    lemma group_equiv_disjoint {α : Type*} [p : setoid α] [d : decidable_rel p.r] (xs : list α) : 
      ∀ g1 g2 ∈ group xs, g1 ≠ g2 → ∀ x1 ∈ g1, ∀ x2 ∈ g2, ¬(x1 ≈ x2) :=
    begin
      intros g1 g2 g1_group g2_group,
      contrapose,
      simp only [and_imp, not_imp, not_not, exists_imp_distrib, not_forall],
      intros x1 x1_in_g1 x2 x2_in_g2 h,
      suffices g : ∀ x1 ∈ g1, ∀ x2 ∈ g2, x1 ≈ x2,
      { exact group_equiv_disjoint' xs g1 g2 g1_group g2_group g },
      intros y1 y1_in_g1 y2 y2_in_g2,
      calc y1 ≈ x1 : group_equiv g1_group y1_in_g1 x1_in_g1
          ... ≈ x2 : h
          ... ≈ y2 : group_equiv g2_group x2_in_g2 y2_in_g2
    end
  end group_equiv_disjoint

  lemma nodup_perm_group {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : list α) : 
    pairwise (λ a b, ¬(a ~ b)) (group xs) :=
  begin
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [group],
      exact pairwise.nil },
    simp only [group, pairwise_cons],
    split,
    { intros a h h',
      have h2 : ∃ l, l ∈ group (filter (not ∘ λ (_x : α), _x ≈ xs_hd) xs_tl) ∧ xs_hd ∈ l, 
      { use a,
        split,
        { assumption },
        rw mem_of_perm h'.symm, 
        exact mem_cons_self xs_hd _ },
      replace h2 := mem_join.mpr h2,
      rw mem_of_perm (join_group_perm _) at h2,
      replace h2 := of_mem_filter h2,
      simp only [function.comp_app] at h2,
      exact absurd (setoid.refl xs_hd) h2 },
    exact ih _ (length_filter_lt_length_cons _ xs_hd xs_tl)
  end

  lemma nodup_group {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : list α) :
    nodup (group xs) :=
  begin
    have h, from nodup_perm_group xs,
    unfold nodup,
    have h' : ∀ a b, (λ (a b : list α), ¬a ~ b) a b → ne a b,
    { intros a b h' a_eq_b,
      rw a_eq_b at h',
      exact h' (setoid.refl b) },
    exact pairwise.imp h' h
  end

  lemma pairwise_equiv_disjoint_group {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : list α) :
    pairwise (λ g1 g2 : list α, ∀ x1 ∈ g1, ∀ x2 ∈ g2, ¬(x1 ≈ x2)) (group xs) :=
  begin
    have h, from nodup_perm_group xs,
    suffices h' : ∀ g1 g2, g1 ∈ group xs → g2 ∈ group xs → ¬(g1 ~ g2) → ∀ x1 ∈ g1, ∀ x2 ∈ g2, ¬(x1 ≈ x2),
    { exact pairwise.imp_of_mem h' h },
    intros g1 g2 g1_group g2_group g1_not_perm_g2,
    have g1_neq_g2 : g1 ≠ g2,
    { intro h',
      rw h' at g1_not_perm_g2,
      exact absurd (setoid.refl g2) g1_not_perm_g2 },
    exact group_equiv_disjoint xs g1 g2 g1_group g2_group g1_neq_g2
  end

  lemma pairwise_disjoint_group {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : list α) :
    pairwise disjoint (group xs) :=
  begin
    have h, from pairwise_equiv_disjoint_group xs,
    suffices h' : ∀ g1 g2 : list α, (∀ (x1 : α), x1 ∈ g1 → ∀ (x2 : α), x2 ∈ g2 → ¬x1 ≈ x2) → disjoint g1 g2,
    { exact pairwise.imp h' h },
    intros g1 g2 h',
    unfold disjoint,
    intros a a_in_g1 a_in_g2,
    exact absurd (setoid.refl a) (h' a a_in_g1 a a_in_g2)
  end

  lemma group_perm_iff_group_sub {α : Type*} [p : setoid α] [decidable_rel p.r] (xs ys : list α) : 
    group xs ~ group ys ↔ group xs ⊆ group ys ∧ group ys ⊆ group xs :=
  begin
    letI := classical.dec_eq α,
    split,
    { intro h,
      exact ⟨perm_subset h, perm_subset h.symm⟩ },
    rintro ⟨xs_sub_ys, ys_sub_xs⟩,
    rw perm_iff_count,
    intro g,
    have h1, from nat.of_le_succ (nodup_iff_count_le_one.mp (nodup_group xs) g),
    have h2, from nat.of_le_succ (nodup_iff_count_le_one.mp (nodup_group ys) g),
    rw le_zero_iff_eq at h1 h2, 
    cases h1,
    { cases h2,
      { rw h1, rw h2 },
      { replace h1 := not_mem_of_count_eq_zero h1,
        replace h2 := count_pos.mp (h2.symm.subst nat.zero_lt_one),
        rw subset_def at ys_sub_xs,
        exact absurd (ys_sub_xs h2) h1 } },
    { cases h2,
      { replace h1 := count_pos.mp (h1.symm.subst nat.zero_lt_one),
        replace h2 := not_mem_of_count_eq_zero h2,
        rw subset_def at ys_sub_xs,
        exact absurd (xs_sub_ys h1) h2 },
      { rw h1, rw h2 } }
  end

  lemma filter_equiv_mem_group {α : Type*} [p : setoid α] [decidable_rel p.r] {x : α} {xs : list α} (h : x ∈ xs) : 
    filter (≈ x) xs ∈ group xs :=
  begin
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [not_mem_nil] at h, contradiction },
    simp only [group, mem_cons_iff],
    by_cases h_equiv : xs_hd ≈ x,
    { apply or.inl,
      have g : ∀ y ∈ xs_tl, y ≈ xs_hd ↔ y ≈ x,
      { intros y y_in_tl,
        split;
        intro g,
        { transitivity, exact g, exact h_equiv },
        { transitivity, exact g, exact (setoid.symm h_equiv) } },
      rw filter_congr g,
      apply filter_cons_of_pos,
      assumption },
    apply or.inr,
    rw @filter_cons_of_neg _ (λ y, y ≈ x) _ xs_hd xs_tl h_equiv,
    simp only [mem_cons_iff] at h,
    cases h,
    { rw h at h_equiv,
      exact absurd (setoid.refl xs_hd) h_equiv },
    have h' : x ∈ filter (not ∘ λ (_x : α), _x ≈ xs_hd) xs_tl,
    { apply mem_filter_of_mem h,
      simp only [function.comp_app],
      intro h',
      exact absurd (setoid.symm h') h_equiv },
    have g, from ih _ (length_filter_lt_length_cons _ xs_hd xs_tl) h', 
    rw filter_filter at g,
    simp only [function.comp_app] at g,
    have g' : ∀ y ∈ xs_tl, (y ≈ x ∧ ¬y ≈ xs_hd) ↔ y ≈ x,
    { intros y y_in_tl,
      split,
      { intro h'',
        exact h''.left },
      intro y_eq_x,
      split,
      { assumption },
      intro h'',
      exact absurd (setoid.trans (setoid.symm h'') y_eq_x) h_equiv },
    rwa filter_congr g' at g
  end

  lemma cons_eq_filter_of_group {α : Type*} [p : setoid α] [decidable_rel p.r] {g_hd : α} {xs g_tl : list α} 
    (h : (g_hd :: g_tl : list α) ∈ group xs) : 
    (g_hd :: g_tl : list α) = filter (≈ g_hd) xs :=
  begin
    induction xs using list.strong_induction_on with xs ih,
    cases xs,
    { simp only [group, not_mem_nil] at h, contradiction },
    simp only [group, mem_cons_iff] at h, 
    rcases h with ⟨hd_eq, h⟩,
    { rw hd_eq at *,
      rw h at *,
      exact (@filter_cons_of_pos _ (≈ xs_hd) _ _ xs_tl (setoid.refl xs_hd)).symm },
    have g : (g_hd :: g_tl : list α) = _, from ih _ (length_filter_lt_length_cons _ xs_hd xs_tl) h,
    rw g,
    simp only [filter_filter, function.comp_app] at *,
    by_cases g' : xs_hd ≈ g_hd,
    { have eqv : ∀ y ∈ xs_tl, (y ≈ g_hd ∧ ¬y ≈ xs_hd) ↔ false,
      { intros y y_in_tl,
        split,
        { rintros ⟨a, b⟩,
          exact absurd (setoid.trans a (setoid.symm g')) b },
        { intro f, contradiction } },
       rw filter_congr eqv at g, 
       simp only [filter_false] at g,
       contradiction },
    rw @filter_cons_of_neg _ (λ y, y ≈ g_hd) _ xs_hd xs_tl g',
    have eqv : ∀ y ∈ xs_tl, (y ≈ g_hd ∧ ¬y ≈ xs_hd) ↔ y ≈ g_hd,
    { intros y y_in_tl,
      split,
      { intro x, exact x.left },
      { intro y_eq_g_hd, 
        split,
        { assumption },
        { intro y_eq_xs_hd,
          exact absurd (setoid.trans (setoid.symm y_eq_xs_hd) y_eq_g_hd) g' } } },
    rw filter_congr eqv
  end

  lemma group_eq_of_mem_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs g1 g2 : list α}
    (h1 : g1 ∈ group xs) (h2 : g2 ∈ group xs) (h : ∃ x ∈ g1, ∃ y ∈ g2, x ≈ y) :
    g1 = g2 :=
  begin
    cases g1,
    { exact absurd h1 (nil_not_mem_group xs) },
    cases g2,
    { exact absurd h2 (nil_not_mem_group xs) },
    rw cons_eq_filter_of_group h1 at *,
    rw cons_eq_filter_of_group h2 at *,
    rcases h with ⟨x, x_in_g1, y, y_in_g2, h⟩,
    simp only [mem_filter] at *,
    apply filter_congr,
    intros z z_in_xs,
    split;
    intro h_eq,
    { calc z ≈ g1_hd : h_eq
         ... ≈ x : setoid.symm x_in_g1.right
         ... ≈ y : h
         ... ≈ g2_hd : y_in_g2.right },
    { calc z ≈ g2_hd : h_eq
         ... ≈ y : setoid.symm y_in_g2.right
         ... ≈ x : setoid.symm h
         ... ≈ g1_hd : x_in_g1.right }
  end

  lemma group_perm_of_perm {α : Type*} [p : setoid α] [decidable_rel p.r] {xs ys : list α} (h : xs ~ ys) :
    ∀ gx ∈ group xs, ∃ gy ∈ group ys, gx ~ gy :=
  begin
    intros gx gx_group,
    cases gx,
    { exact absurd gx_group (nil_not_mem_group xs) },
    set gy := filter (≈ gx_hd) ys with gy_def,
    use gy,
    have g : gx_hd ∈ ys,
    from (mem_of_perm h).mp 
      ((mem_of_perm (join_group_perm xs)).mp 
        (mem_join_of_mem gx_group (mem_cons_self gx_hd gx_tl))),
    use filter_equiv_mem_group g,
    rw gy_def,
    rw cons_eq_filter_of_group gx_group,
    apply perm_filter,
    assumption
  end

  section map_on_of_nodup
    local attribute [instance] classical.prop_decidable
    lemma inj_on_of_nodup_map {α β : Type*} {f : α → β} {s : list α} (nd : nodup (map f s)) 
      {x : α} (x_in_s : x ∈ s) {y : α} (y_in_s : y ∈ s) (f_eq : f x = f y) : x = y := 
    begin
      unfold nodup at nd,
      rw pairwise_map at nd, 
      have s : symmetric (λ (a b : α), f a ≠ f b),
      { unfold symmetric,
        intros x y,
        exact ne.symm },
      have h, from forall_of_pairwise s nd x x_in_s y y_in_s,
      by_contradiction,
      exact absurd f_eq (h a)
    end
  end map_on_of_nodup

end list

namespace multiset
  def group' {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α) : multiset (multiset α) :=
  ↑(list.map (λ g, (↑g : multiset α)) (list.group xs))

  lemma nodup_map_coe_of_perm_nodup {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list (list α)) (h : list.pairwise (λ a b, ¬(a ~ b)) xs) : 
    list.nodup (list.map coe xs : list (multiset α)) :=
  begin
    letI := classical.dec_eq α,
    rw list.nodup_iff_count_le_one,
    intro s,
    induction xs,
    { simp only [list.not_mem_nil, list.count_eq_zero_of_not_mem, zero_le, not_false_iff, list.map, zero_le_one] },
    simp only [list.map],
    rw list.count_cons,
    split_ifs,
    { apply nat.succ_le_succ,
      simp only [le_zero_iff_eq],
      rw list.count_eq_zero_of_not_mem,
      rw h_1 at *,
      simp only [not_exists, coe_eq_coe, list.mem_map, not_and],
      intros a a_in_tl,
      replace h := list.rel_of_pairwise_cons h a_in_tl,
      intro h',
      exact absurd (h'.symm) h },
    { exact xs_ih (list.pairwise_of_pairwise_cons h) }
  end

  lemma group'_eq_of_perm {α : Type*} [p : setoid α] [decidable_rel p.r] {xs ys : list α} (h : xs ~ ys) : group' xs = group' ys :=
  begin
    letI := classical.dec_eq α,
    unfold group',
    simp only [coe_eq_coe],
    rw list.perm_ext (nodup_map_coe_of_perm_nodup _ (list.nodup_perm_group xs)) 
      (nodup_map_coe_of_perm_nodup _ (list.nodup_perm_group ys)),
    simp only [list.mem_map], 
    intro s,
    split,
    { rintro ⟨ax, ax_group, ax_eq_s⟩,
      rcases list.group_perm_of_perm h ax ax_group with ⟨ay, ⟨ay_group, ax_eq_ay⟩⟩,
      use [ay, ay_group],
      rw ←coe_eq_coe at ax_eq_ay,
      rw ←ax_eq_ay,
      assumption },
    { rintro ⟨ay, ay_group, ay_eq_s⟩,
      rcases list.group_perm_of_perm h.symm ay ay_group with ⟨ax, ⟨ax_group, ay_eq_ax⟩⟩,
      use [ax, ax_group],
      rw ←coe_eq_coe at ay_eq_ax,
      rw ←ay_eq_ax,
      assumption }
  end

  lemma join_group'_eq {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α) : join (group' xs) = xs :=
  begin
    simp only [group', coe_join, coe_eq_coe],
    exact list.join_group_perm xs
  end

  lemma nil_not_mem_group' {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α)
    : ∅ ∉ group' xs :=
  begin
    simp [group'],
    intros x x_in_group h,
    rw coe_eq_zero at h,
    rw h at x_in_group,
    have g, from list.nil_not_mem_group xs,
    contradiction
  end

  lemma group'_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs : list α} {g : multiset α} {x y : α} : 
    g ∈ group' xs → x ∈ g → y ∈ g → x ≈ y :=
  begin
    simp only [group', and_imp, list.mem_map, mem_coe, exists_imp_distrib],
    intros g' g'_group heq,
    rw ←heq,
    simp only [mem_coe],
    exact list.group_equiv g'_group
  end

  lemma pairwise_equiv_disjoint_group' {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : list α) :
    pairwise (λ g1 g2 : multiset α, ∀ x1 ∈ g1, ∀ x2 ∈ g2, ¬(x1 ≈ x2)) (group' xs) :=
  begin
    simp only [group'],
    rw pairwise_coe_iff_pairwise,
    have h, from list.pairwise_equiv_disjoint_group xs,
    { rw list.pairwise_map,
      simpa only [mem_coe] },
    unfold symmetric,
    intros x y h x1 x1_in_y x2 x2_in_x h',
    exact absurd (setoid.symm h') (h x2 x2_in_x x1 x1_in_y)
  end

  lemma filter_equiv_mem_group' {α : Type*} [p : setoid α] [decidable_rel p.r] {x : α} {xs : list α} (h : x ∈ xs) : 
    filter (≈ x) xs ∈ group' xs :=
  begin
    simp only [group', coe_filter, coe_eq_coe, list.mem_map, mem_coe],
    have h, from list.filter_equiv_mem_group h,
    use list.filter (λ (_x : α), _x ≈ x) xs,
    split,
    { assumption },
    refl
  end

  lemma subset_of_eq {α : Type*} {xs ys : multiset α} (h : xs = ys) : xs ⊆ ys ∧ ys ⊆ xs :=
  begin
    rw h,
    exact ⟨subset.refl ys, subset.refl ys⟩
  end 

  lemma cons_eq_filter_of_group' {α : Type*} [p : setoid α] [decidable_rel p.r] {g_hd : α} {g_tl : multiset α} {xs : list α}
    (h : g_hd :: g_tl ∈ group' xs) : 
    g_hd :: g_tl = filter (≈ g_hd) xs :=
  begin
    letI := classical.dec_eq α,
    simp only [group', list.mem_map, mem_coe, list.map] at h,
    simp only [coe_filter],
    rcases h with ⟨a, a_group, a_eq_g⟩,
    cases a,
    { simp only [coe_nil_eq_zero, zero_ne_cons] at a_eq_g,
      contradiction },
    have g : (a_hd :: a_tl : list α) = list.filter (λ (_x : α), _x ≈ a_hd) xs, from list.cons_eq_filter_of_group a_group,
    rw ←a_eq_g,
    rw g,
    simp only [coe_eq_coe],
    have g_hd_mem_a, from (subset_of_eq a_eq_g).right (mem_cons_self g_hd g_tl),
    simp only [mem_coe] at g_hd_mem_a,
    have g_hd_equiv_a_hd, from list.group_equiv a_group (list.mem_cons_self a_hd a_tl) g_hd_mem_a,
    have equiv : (∀ x ∈ xs, x ≈ a_hd ↔ x ≈ g_hd),
    { intros x x_in_xs,
      split;
      intro h_eq,
      { exact setoid.trans h_eq g_hd_equiv_a_hd },
      { exact setoid.trans h_eq (setoid.symm g_hd_equiv_a_hd) } },
    rw list.filter_congr equiv
  end

  lemma group'_eq_of_mem_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs : list α} {g1 g2 : multiset α}
    (h1 : g1 ∈ group' xs) (h2 : g2 ∈ group' xs) (h : ∃ x ∈ g1, ∃ y ∈ g2, x ≈ y) :
    g1 = g2 :=
  begin
    simp only [group', list.mem_map, mem_coe] at h1 h2,
    rcases h1 with ⟨g1a, g1a_group, g1a_def⟩,
    rcases h2 with ⟨g2a, g2a_group, g2a_def⟩,
    rw ←g1a_def at *,
    rw ←g2a_def at *,
    simp only [coe_eq_coe],
    simp only [exists_prop, mem_coe] at h,
    rcases h with ⟨x, x_in_g1a, y, y_in_g2a, h⟩,
    rw list.group_eq_of_mem_equiv g1a_group g2a_group ⟨x, x_in_g1a, y, y_in_g2a, h⟩
  end

  def group {α : Type*} [p : setoid α] [decidable_rel p.r] (s : multiset α) : multiset (multiset α) :=
  quot.lift_on s group' (@group'_eq_of_perm _ _ _)

  lemma join_group_eq {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : multiset α) : join (group xs) = xs :=
  quot.induction_on xs join_group'_eq

  lemma nil_not_mem_group {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : multiset α) : ∅ ∉ group xs :=
  quot.induction_on xs nil_not_mem_group'

  lemma group_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs g : multiset α} {x y : α} : 
    g ∈ group xs → x ∈ g → y ∈ g → x ≈ y :=
  quot.induction_on xs (λ l, group'_equiv)

  lemma pairwise_equiv_disjoint_group {α : Type*} [decidable_eq α] [p : setoid α] [decidable_rel p.r] (xs : multiset α) :
    pairwise (λ g1 g2 : multiset α, ∀ x1 ∈ g1, ∀ x2 ∈ g2, ¬(x1 ≈ x2)) (group xs) :=
  quot.induction_on xs pairwise_equiv_disjoint_group'

  lemma filter_equiv_mem_group {α : Type*} [p : setoid α] [decidable_rel p.r] {x : α} {xs : multiset α} : 
    x ∈ xs → filter (≈ x) xs ∈ group xs :=
  quot.induction_on xs (λ l, filter_equiv_mem_group')

  lemma cons_eq_filter_of_group {α : Type*} [p : setoid α] [decidable_rel p.r] {g_hd : α} {g_tl : multiset α} {xs : multiset α} :
    g_hd :: g_tl ∈ group xs → g_hd :: g_tl = filter (≈ g_hd) xs :=
  quot.induction_on xs (λ l, cons_eq_filter_of_group')

  lemma group_eq_of_mem_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] {xs g1 g2 : multiset α} :
    g1 ∈ group xs → g2 ∈ group xs → (∃ x ∈ g1, ∃ y ∈ g2, x ≈ y) → g1 = g2 :=
  quot.induction_on xs (λ l, @group'_eq_of_mem_equiv _ _ _ l _ _)

  @[simp] lemma filter_true {α : Type*} {h : decidable_pred (λ a : α, true)} (s : multiset α) : 
    @filter α (λ _, true) h s = s :=
  quot.induction_on s (λ l, congr_arg coe (list.filter_true l))

  @[simp] lemma filter_false {α : Type*} {h : decidable_pred (λ a : α, false)} (s : multiset α) : 
    @filter α (λ _, false) h s = [] :=
  quot.induction_on s (λ l, congr_arg coe (list.filter_false l))

  lemma disjoint_filter_filter {α : Type*} {p1 p2 : α → Prop} [decidable_pred p1] [decidable_pred p2] {s : multiset α} :
    disjoint (s.filter p1) (s.filter p2) ↔ ∀ x ∈ s, p1 x → ¬p2 x :=
  begin
    simp only [disjoint, and_imp, mem_filter],
    split;
    intro h,
    { intros x x_in_s p1_x,
      exact h x_in_s p1_x x_in_s },
    intros x x_in_s p1_x x_in_s,
    exact h x x_in_s p1_x
  end

  lemma inj_on_of_nodup_map {α β : Type*} {f : α → β} {s : multiset α} : 
    nodup (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y := 
  quot.induction_on s (λ l, @list.inj_on_of_nodup_map α β f l)

  lemma map_add_of_disjoint {α β : Type*} [decidable_eq α] (f1 f2 : α → β) {s1 s2 : multiset α} (h : disjoint s1 s2) : 
    map f1 s1 + map f2 s2 = map (λ x, if x ∈ s1 then f1 x else f2 x) (s1 + s2) :=
  begin
    simp only [map_add],
    have h1 : map f1 s1 = map (λ (x : α), ite (x ∈ s1) (f1 x) (f2 x)) s1,
    { have h1' : ∀ x ∈ s1, f1 x = ite (x ∈ s1) (f1 x) (f2 x),
      { intros x x_in_s1,
        rw if_pos x_in_s1 },
      rw map_congr h1' },
    have h2 : map f2 s2 = map (λ (x : α), ite (x ∈ s1) (f1 x) (f2 x)) s2,
    { have h2' : ∀ x ∈ s2, f2 x = ite (x ∈ s1) (f1 x) (f2 x),
      { intros x x_in_s2,
        rw if_neg,
        exact h.symm x_in_s2 },
      rw map_congr h2' },
    rw h1, rw h2
  end 
end multiset

namespace finset
  def join {α : Type*} [decidable_eq α] (xs : list (finset α)) : finset α := xs.foldr (∪) ∅ 

  @[simp] theorem mem_join {α : Type*} [decidable_eq α] {x : α} {xs : list (finset α)} : x ∈ join xs ↔ ∃ S ∈ xs, x ∈ S :=
  begin
    apply iff.intro,
    { intro h, 
      induction xs;
      unfold join at *,
      { simp only [list.foldr_nil, not_mem_empty] at h,
        contradiction },
      { simp only [mem_union, list.foldr_cons] at h,
        cases h, 
        { exact ⟨xs_hd, ⟨or.inl rfl, h⟩⟩ },
        { rcases xs_ih h with ⟨S, S_in_tl, x_in_S⟩,
          exact ⟨S, ⟨or.inr S_in_tl, x_in_S⟩⟩ } } },
    { intro h,
      induction xs,
      { simp only [list.not_mem_nil, exists_false, not_false_iff, exists_prop_of_false] at h,
        contradiction },
      { unfold join at *,
        rcases h with ⟨S, S_in_hd_or_tl, x_in_S⟩,
        simp only [mem_union, list.foldr_cons, list.mem_cons_iff] at *, 
        cases S_in_hd_or_tl,
        { rw S_in_hd_or_tl at x_in_S, 
          exact or.inl x_in_S },
        { exact or.inr (xs_ih ⟨S, S_in_hd_or_tl, x_in_S⟩) } } }
    end

  @[simp] lemma erase_insert_eq_erase {α : Type*} [decidable_eq α] (s : finset α) (a : α) : 
    erase (insert a s) a = erase s a :=
  begin
    ext, 
    simp only [mem_insert, mem_erase, and_or_distrib_left, not_and_self, false_or]
  end

  lemma erase_insert_eq_insert_erase {α : Type*} [decidable_eq α] {a b : α} (s : finset α) 
    (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  begin
    ext,
    simp only [mem_insert, mem_erase, and_or_distrib_left],
    apply iff.intro;
    intro h₁;
    cases h₁,
    { exact or.inl h₁.right },
    { exact or.inr h₁ },
    { rw h₁, exact or.inl ⟨h, rfl⟩ },
    { exact or.inr h₁ }
  end

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

  lemma map_congr {α β : Type*} (f g : α ↪ β) {s : finset α} : (∀ x ∈ s, f.1 x = g.1 x) → map f s = map g s :=
  λ h, eq_of_veq (multiset.map_congr h)
end finset


namespace function
  notation f `[` a `↦` b `]` := function.update f a b 
end function