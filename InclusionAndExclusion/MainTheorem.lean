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
  simp only [Fintype.card_coe]
  unfold char_fun toInt
  simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  have h1: A ∩ B = B := by
    exact Finset.inter_eq_right.mpr h
  exact congrArg Finset.card (id (Eq.symm h1))


/-- We derive it from eq_FinInter₀ and card_eq -/
lemma card_eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Fintype.card (⋂ (i : β), (A i : Set α)) = Fintype.card (FinInter₀ A) := card_eq _ _ (eq_FinInter₀ A)

/-- We derive it from eq_FinUnion₀ and card_eq -/
lemma card_eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Fintype.card (⋃ (i : β), (A i : Set α)) = Fintype.card (FinUnion₀ A) := card_eq _ _ (eq_FinUnion₀ A)

/-- We claim that x in the intersection of the family sets {A i} is equal to forall i, x in (A i) holds -/
lemma char_fun_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) (x : α) : char_fun (FinInter₀ A) x = ∏ (i : β), (char_fun (A i) x) := by
  unfold char_fun toInt
  have h_1 (h1 : x ∈ FinInter₀ A): (1 : ℤ) = ∏ i : β, if x ∈ A i then 1 else 0 := by
    have ha : x ∈ ⋂ (i : β), (A i : Set α) := by
      rw [← eq_FinInter₀]
      exact h1
    have hb : ∀ i : β, x ∈ A i := by
      simp only [Set.mem_iInter, Finset.mem_coe] at ha
      exact ha
    simp only [hb, ↓reduceIte, Finset.prod_const_one]
  split
  rename x ∈ FinInter₀ A => h1
  exact h_1 h1
  rename x ∉ FinInter₀ A => h2
  have hc: ∃ i : β, x ∉ A i := by
    contrapose! h2
    change x ∈ (FinInter₀ A :Set α)
    simp_rw [eq_FinInter₀ A]
    simp only [Set.mem_iInter, Finset.mem_coe]
    exact h2
  symm
  apply Finset.prod_eq_zero_iff.mpr
  simp only [Finset.mem_univ, ite_eq_right_iff, one_ne_zero, imp_false, true_and]
  exact hc

/-- We claim that x in the union of the family sets {A i} is equal to at least one of (i of type β, x in (A i)) holds -/
lemma char_fun_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (x : α) : char_fun (FinUnion₀ A) x = 1 - ∏ (i : β), (1 - char_fun (A i) x) := by
  by_cases h : ∃ (i : β), char_fun (A i) x = 1
  · trans 1
    · unfold char_fun toInt at *
      simp at *
      apply Finset.mem_coe.mp
      rw [eq_FinUnion₀]
      apply Set.mem_iUnion.mpr h
    · have : ∏ i : β, (1 - char_fun (A i) x) = 0 := by
        rcases h with ⟨j,hj⟩
        apply Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
      rw [this]
      norm_num
  · unfold char_fun toInt at *
    simp at *
    simp [h]
    by_contra h'
    have h' := Finset.mem_coe.mpr h'
    simp_rw [eq_FinUnion₀] at h'
    have h' := Set.mem_iUnion.mp h'
    rcases h' with ⟨j,hj⟩
    exact h j hj

/-- Here we formalize the polynomial expansion of (1 - ∏ i (1 - g i)) in the view of (fun (Fin n) ↦ ℕ) -/
lemma mul_expand₀ (n : ℕ) (g : (Fin n) → ℤ) : 1 - ∏ (i : Fin n), (1 - g i) = ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
  let g' : ℕ → ℤ := fun x ↦ if h: x < n then g ⟨x,h⟩ else 0
  have (x : Fin n) : g x = g' x := by
    unfold_let g'
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
  simp_rw[this]
  exact mul_expand₁ n g'

/-- Finally, we can start to formalize the main theorem -/
theorem Principle_of_Inclusion_Exclusion {α : Type*} [DecidableEq α] (n : ℕ) (A : (Fin n) → Finset α) : (Fintype.card (⋃ (i : Fin n), ((A i) : Set α))) = Finset.sum (Finset.univ (α := (Finset.powerset₀ (Finset.univ (α := Fin n))))) (fun S ↦ (-1 : ℤ) ^ (Fintype.card S + 1) * Fintype.card (⋂ (i : S.1), ((A i) : Set α))) := by
  rw[card_eq_FinUnion]
  rw[card_eq_sum_char_fun (by rfl)]
  simp_rw[char_fun_FinUnion]
  simp_rw[mul_expand₀]
  rw[Finset.sum_comm]
  apply Finset.sum_congr (by rfl)
  simp_rw[← Finset.mul_sum]
  simp_rw[← char_fun_FinInter]
  simp_rw[card_eq_FinInter]
  intro x0 h0
  rw[card_eq_sum_char_fun]
  rw[← Finset.coe_subset,eq_FinInter₀,eq_FinUnion₀]
  intro x h
  simp at *
  have x1: x0.1 := Classical.choice (by exact powerset₀_nonempty x0)
  use x1.1
  exact h x1.1 x1.2
