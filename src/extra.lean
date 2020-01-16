import tactic
import data.multiset

namespace list
  section inj_of_nodup_map_on
    local attribute [instance] classical.prop_decidable
    lemma inj_of_nodup_map_on {α β : Type*} {f : α → β} {xs : list α} {x y : α} :
      nodup (map f xs) → x ∈ xs → y ∈ xs → f x = f y → x = y := 
    λ nd x_in_xs y_in_xs f_eq, by_contradiction (λ x_neq_y, 
      absurd f_eq (forall_of_pairwise 
        (λ x y, ne.symm : symmetric (λ (a b : α), f a ≠ f b)) 
        ((pairwise_map _).mp nd) _ x_in_xs _ y_in_xs x_neq_y))
  end inj_of_nodup_map_on

  lemma disjoint_map_left {α β : Type*} {f : α → β} {s : list α} {t : list β} :
    disjoint (s.map f) t ↔ (∀ {a : α}, a ∈ s → f a ∉ t) :=
  by { simp only [disjoint, and_imp, mem_map, exists_imp_distrib],
    exact ⟨λ h a a_in_s, h a a_in_s rfl, λ h b a a_in_s fa_eq_b, fa_eq_b ▸ h a_in_s⟩ }

  lemma disjoint_map_right {α β : Type*} {f : α → β} {s : list α} {t : list β} :
    disjoint t (s.map f) ↔ (∀ {a : α}, a ∈ s → f a ∉ t) :=
  by { rw disjoint_comm, exact disjoint_map_left }

  lemma disjoint_filter_filter {α : Type*} {p1 p2 : α → Prop} [decidable_pred p1] [decidable_pred p2] {s : list α} :
    disjoint (s.filter p1) (s.filter p2) ↔ ∀ {x : α}, x ∈ s → p1 x → ¬p2 x :=
  by { simp only [disjoint, and_imp, mem_filter], 
    exact ⟨λ h x x_in_s p1_x, h x_in_s p1_x x_in_s, λ h x x_in_s p1_x _, h x_in_s p1_x⟩ }
end list

namespace multiset
  lemma inj_on_of_nodup_map {α β : Type*} {f : α → β} {s : multiset α} {x y : α} : 
    nodup (map f s) → x ∈ s → y ∈ s → f x = f y → x = y := 
  quot.induction_on s (λ xs, @list.inj_of_nodup_map_on _ _ _ xs _ _)

  lemma disjoint_map_left {α β : Type*} {f : α → β} {s : multiset α} {t : multiset β} :
    disjoint (s.map f) t ↔ (∀ {a : α}, a ∈ s → f a ∉ t) :=
  quotient.induction_on₂ s t (@list.disjoint_map_left _ _ _)

  lemma disjoint_map_right {α β : Type*} {f : α → β} {s : multiset α} {t : multiset β} :
    disjoint t (s.map f) ↔ (∀ {a : α}, a ∈ s → f a ∉ t) :=
  quotient.induction_on₂ s t (@list.disjoint_map_right _ _ _)

  lemma disjoint_filter_filter {α : Type*} {p1 p2 : α → Prop} [decidable_pred p1] [decidable_pred p2] {s : multiset α} :
    disjoint (s.filter p1) (s.filter p2) ↔ ∀ {x : α}, x ∈ s → p1 x → ¬p2 x :=
  quotient.induction_on s (@list.disjoint_filter_filter _ _ _ _ _)
end multiset