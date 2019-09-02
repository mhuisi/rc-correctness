import tactic.fin_cases
import logic.function

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