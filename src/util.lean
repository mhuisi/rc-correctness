import tactic
import data.multiset
import data.finset
import logic.function
import data.nat.basic

namespace list
  open well_founded_tactics

  -- map_wf
  -- provides a map function that maintains a sizeof-lemma
  -- so that recursing in a map body is possible.
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

  -- filter
  lemma filter_cons {α : Type*} (p : α → Prop) [decidable_pred p] (a : α) (l : list α)
    : filter p (a :: l) = a :: filter p l ∨ filter p (a :: l) = filter p l :=
  by { by_cases p a, { exact or.inl (filter_cons_of_pos l h) }, { exact or.inr (filter_cons_of_neg l h) } }

  lemma filter_filter_swap {α : Type*} (p q : α → Prop) [decidable_pred p] [decidable_pred q] (xs : list α)
    : filter p (filter q xs) = filter q (filter p xs) :=
  by simp only [filter_filter, @filter_congr _ (λ a, p a ∧ q a) (λ a, q a ∧ p a) _ _ _ (λ x x_in_xs, ⟨and.symm, and.symm⟩)]

  lemma filter_filter_comp {α : Type*} (p q : α → Prop) [decidable_pred p] [decidable_pred q]
    : filter p ∘ filter q = filter (λ a, p a ∧ q a) := by { funext, rw [function.comp_app, list.filter_filter] }

  -- zip
  lemma map_fst_zip {α β : Type*} : ∀ (xs : list α) (ys : list β), length xs <= length ys → map prod.fst (zip xs ys) = xs
  | [] ys h := rfl
  | xs [] h := by simp only [zip_nil_right, map, length_eq_zero.mp (le_zero_iff_eq.mp h)]
  | (x :: xs) (y :: ys) h := by simp [zip_cons_cons, map, map_fst_zip xs ys (nat.lt_succ_iff.mp h)]

  lemma map_snd_zip {α β : Type*} : ∀ (xs : list α) (ys : list β), length ys <= length xs → map prod.snd (zip xs ys) = ys
  | xs [] h := by { rw zip_nil_right, refl }
  | [] ys h := by simp only [zip_nil_right, map, length_eq_zero.mp (le_zero_iff_eq.mp h)]
  | (x :: xs) (y :: ys) h := by simp [zip_cons_cons, map, map_snd_zip xs ys (nat.lt_succ_iff.mp h)]

  -- contexts
  -- for a list xs, generates a list that contains the elements of xs paired with the
  -- values before each element and the values after each element.
  structure context (α : Type*) := (pre : list α) (x : α) (post : list α)

  instance context_to_list {α : Type*} : has_coe (context α) (list α) := 
  ⟨λ c, c.pre ++ c.x :: c.post⟩

  def contexts_aux {α : Type*} : list α → list α → list (context α)
  | pre [] := []
  | pre (x :: xs) := ⟨pre, x, xs⟩ :: contexts_aux (pre.concat x) xs

  def contexts {α : Type*} (xs : list α) : list (context α) := contexts_aux [] xs

  @[simp] lemma contexts_aux_pre_cons_elim {α : Type*} (p : α) (pre xs : list α)
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
    { have : (λ (c : context α), (⟨c.pre, c.x, c.post⟩ : context α)) = id, { ext, cases x, refl },
      simp only [nil_append, this, map_id] },
    simp only [contexts_aux_pre_cons_elim _ _, pre_ih, cons_append, map_map]
  end

  @[simp] lemma contexts_nil (α : Type*) : contexts ([] : list α) = [] := rfl

  @[simp] lemma contexts_cons {α : Type*} (x : α) (xs : list α) 
    : contexts (x :: xs) = ⟨[], x, xs⟩ :: contexts_aux [x] xs := rfl

  lemma contexts_append {α : Type*} (xs ys : list α) 
    : contexts (xs ++ ys) = (contexts xs).map (λ c, ⟨c.pre, c.x, c.post ++ ys⟩) 
        ++ (contexts ys).map (λ c, ⟨xs ++ c.pre, c.x, c.post⟩) :=
  begin
    induction xs,
    { simp only [contexts, contexts_aux, map, nil_append],
      rw map_id', intro x, cases x, refl },
    have : ∀ xs : list α, contexts_aux nil xs = contexts xs, from λ xs, rfl,
    simp [this, xs_ih]
  end

  lemma contexts_concat {α : Type*} (xs : list α) (x : α)
    : contexts (xs.concat x) 
      = ((contexts xs).map (λ c : context α, (⟨c.pre, c.x, c.post.concat x⟩ : context α))).concat ⟨xs, x, []⟩ :=
  by simp only [contexts_append, contexts_aux, list.append_nil, list.contexts_cons, list.map, list.concat_eq_append]

  lemma of_mem_contexts_aux {α : Type*} {pre xs : list α} {c : context α} 
    : c ∈ contexts_aux pre xs → pre ++ xs = ↑c :=
  begin
    intro c_context,
    induction xs generalizing pre;
    simp only [contexts_aux, not_mem_nil, mem_cons_iff] at c_context,
    { contradiction },
    cases c_context,
    { rw c_context, refl },
    rw [←xs_ih c_context, concat_append]
  end

  lemma of_mem_contexts {α : Type*} {xs : list α} {c : context α} 
    : c ∈ contexts xs → xs = ↑c := of_mem_contexts_aux

  lemma mem_of_mem_contexts {α : Type*} {c : context α} {xs : list α}
    : c ∈ contexts xs → c.x ∈ xs := λ h, by { rw of_mem_contexts h, unfold_coes, simp }

  lemma mem_contexts_self {α : Type*} (c : context α) : c ∈ contexts (↑c : list α) :=
  begin
    cases c,
    induction c_pre;
    unfold_coes,
    { simp only [nil_append, contexts_cons, mem_cons_self] },
    simp only [contexts, contexts_aux, mem_cons_iff, cons_append, concat_nil, false_or, false_and],
    rw [contexts_aux_pre_elim, mem_map],
    tauto
  end
end list

namespace multiset
  @[simp] lemma filter_true {α : Type*} {h : decidable_pred (λ a : α, true)} (s : multiset α) : 
    @filter α (λ _, true) h s = s :=
  quot.induction_on s (λ l, congr_arg coe (list.filter_true l))

  @[simp] lemma filter_false {α : Type*} {h : decidable_pred (λ a : α, false)} (s : multiset α) : 
    @filter α (λ _, false) h s = [] :=
  quot.induction_on s (λ l, congr_arg coe (list.filter_false l))

  @[simp] lemma zero_union {α : Type*} [decidable_eq α] (s : multiset α) : 0 ∪ s = s := lattice.bot_sup_eq

  @[simp] lemma union_zero {α : Type*} [decidable_eq α] (s : multiset α) : s ∪ 0 = s := lattice.sup_bot_eq
end multiset

namespace finset
  def join {α : Type*} [decidable_eq α] (xs : finset (finset α)) : finset α := (xs.1.map val).join.to_finset

  @[simp] theorem mem_join {α : Type*} [decidable_eq α] {x : α} {xs : finset (finset α)} : x ∈ join xs ↔ ∃ S ∈ xs, x ∈ S :=
  begin
    unfold join,
    simp only [multiset.mem_to_finset, multiset.mem_join, mem_def.symm, exists_prop, multiset.mem_map],
    split; intro h,
    { rcases h with ⟨s, ⟨⟨S, S_in_xs, s_def⟩, x_in_s⟩⟩, 
      rw [←s_def, ←mem_def] at x_in_s,
      exact ⟨S, S_in_xs, x_in_s⟩ },
    { tauto }
  end

  @[simp] lemma erase_insert_eq_erase {α : Type*} [decidable_eq α] (s : finset α) (a : α) : 
    erase (insert a s) a = erase s a :=
  by { ext, simp only [mem_insert, mem_erase, and_or_distrib_left, not_and_self, false_or] }

  lemma erase_insert_eq_insert_erase {α : Type*} [decidable_eq α] {a b : α} (s : finset α) 
    (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  begin
    ext, simp only [mem_insert, mem_erase, and_or_distrib_left], 
    split; intro h'; cases h'; cc
  end
end finset


namespace function
  notation f `[` a `↦` b `]` := function.update f a b 
end function