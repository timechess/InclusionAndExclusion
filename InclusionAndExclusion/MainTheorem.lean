import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype
import InclusionAndExclusion.Auxiliary
import InclusionAndExclusion.FinInter
import InclusionAndExclusion.FinUnion
import InclusionAndExclusion.ToInt
-- Thank 王镜廷 of PKU for providing the proof of this theorem

open BigOperators

/-- Here we introduce a way to calculate the number of elements in B which is a subset of A -/
lemma card_eq_sum_char_fun {α : Type*} [DecidableEq α] {A B : Finset α} (h : B ⊆ A) : Fintype.card B = Finset.sum A (char_fun B) := by
  sorry

/-- We derive it from eq_FinInter₀ and card_eq -/
lemma card_eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Fintype.card (⋂ (i : β), (A i : Set α)) = Fintype.card (FinInter₀ A) := card_eq _ _ (eq_FinInter₀ A)

/-- We derive it from eq_FinUnion₀ and card_eq -/
lemma card_eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Fintype.card (⋃ (i : β), (A i : Set α)) = Fintype.card (FinUnion₀ A) := card_eq _ _ (eq_FinUnion₀ A)

/-- We claim that x in the intersection of the family sets {A i} is equal to forall i, x in (A i) holds -/
lemma char_fun_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) (x : α) : char_fun (FinInter₀ A) x = ∏ (i : β), (char_fun (A i) x) := by
  sorry

/-- We claim that x in the union of the family sets {A i} is equal to at least one of (i of type β, x in (A i)) holds -/
lemma char_fun_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (x : α) : char_fun (FinUnion₀ A) x = 1 - ∏ (i : β), (1 - char_fun (A i) x) := by
  sorry

/-- Here we formalize the polynomial expansion of (1 - ∏ i (1 - g i)) in the view of (fun (Fin n) ↦ ℕ) -/
lemma mul_expand₀ (n : ℕ) (g : (Fin n) → ℤ) : 1 - ∏ (i : Fin n), (1 - g i) = ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
  sorry

/-- Finally, we can start to formalize the main theorem -/
theorem Principle_of_Inclusion_Exclusion {α : Type*} [DecidableEq α] (n : ℕ) (A : (Fin n) → Finset α) : (Fintype.card (⋃ (i : Fin n), ((A i) : Set α))) = Finset.sum (Finset.univ (α := (Finset.powerset₀ (Finset.univ (α := Fin n))))) (fun S ↦ (-1 : ℤ) ^ (Fintype.card S + 1) * Fintype.card (⋂ (i : S.1), ((A i) : Set α))) := sorry
