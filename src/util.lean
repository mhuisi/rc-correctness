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


  lemma sizeof_filter_le_sizeof {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) : list.sizeof (filter p xs) <= list.sizeof xs :=
  begin
    induction xs,
    { rw list.filter_nil },
    by_cases p xs_hd,
    { rw filter_cons_of_pos xs_tl h, 
      unfold_sizeof,
      assumption },
    { rw filter_cons_of_neg xs_tl h,
      unfold_sizeof,
      exact le_add_left xs_ih }
  end
  
  def group {α : Type*} [p : setoid α] [decidable_rel p.r] : list α → list (list α) 
  | []        := []
  | (x :: xs) := have list.sizeof (filter (not ∘ (≈ x)) xs) < 1 + list.sizeof xs, from 
    begin 
      have h : list.sizeof (filter (not ∘ (≈ x)) xs) ≤ list.sizeof xs, from sizeof_filter_le_sizeof _ xs,
      rw nat.add_comm,
      rw ←nat.succ_eq_add_one,
      rwa nat.lt_succ_iff
    end, (x :: filter (≈ x) xs) :: group (filter (not ∘ (≈ x)) xs)

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
      simp only [cons_append, count_cons'],
      apply congr_arg (+ ite (a = xs_hd) 1 0),
      assumption },
    { rw @filter_cons_of_pos _ (not ∘ p) _ _ xs_tl h,
      rw filter_cons_of_neg xs_tl h, 
      simp only [count_append, count_cons'],
      rw ←add_assoc,
      apply congr_arg (+ ite (a = xs_hd) 1 0),
      rwa ←count_append }
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
    { simp only [group, join] },
    rw perm_iff_count,
    intro a,
    simp only [group, cons_append, join, count_cons'],
    apply congr_arg (+ ite (a = xs_hd) 1 0),
    simp only [count_append],
    simp only [] at ih, -- surely there's a better way to eta-reduce
    replace ih := ih (filter (not ∘ (≈ xs_hd)) xs_tl),
    have h : length (filter (not ∘ (≈ xs_hd)) xs_tl) < length (xs_hd :: xs_tl),
    { exact length_filter_lt_length_cons _ xs_hd xs_tl },
    have perm, from ih h,
    rw perm_iff_count at perm,
    rw perm a,
    rw ←count_append,
    revert a,
    rw ←perm_iff_count,
    exact filter_append_not_filter_perm (≈ xs_hd) xs_tl
  end

  lemma group_equiv {α : Type*} [p : setoid α] [decidable_rel p.r] (xs : list α) : 
    ∀ g ∈ group xs, ∀ x y ∈ g, x ≈ y :=
  begin
    intros g g_group x y x_in_g y_in_g,
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
end list


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
end finset


namespace function
  notation f `[` a `↦` b `]` := function.update f a b 
end function