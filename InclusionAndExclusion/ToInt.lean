import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype

-- Thank 王镜廷 of PKU for providing the proof of this theorem
open BigOperators

/-- We assign a value to a proposition. If the proposition holds, we assign a value of 1; otherwise, we assign a value of 0 -/
def toInt (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

/-- The value of P and Q both holds is equal to the value of P times the value of Q -/
lemma toInt_and {P Q : Prop} [Decidable P] [Decidable Q] : toInt (P ∧ Q) = toInt P * toInt Q := by
  unfold toInt
  simp only [mul_ite , mul_one , mul_zero]
  by_cases h : P
  · simp [h]
  · simp only [h, false_and , ↓ reduceIte, ite_self]


/-- The value of not P is equal to one sub the value of P -/
lemma toInt_not (P : Prop) [Decidable P] : toInt (¬ P) = 1 - toInt P := by
  unfold toInt
  simp only [ite_not]
  by_cases h : P
  · simp [h]
  · simp only [h , false_and , ↓ reduceIte, ite_self, sub_zero]


/-- We define a function that if x in A then returns 1, else returns 0 -/
def char_fun {α : Type*} [DecidableEq α] (A : Finset α) (x : α) : ℤ := toInt (x ∈ A)

/-- We claim that x in the intersection of A and B is equal to x in A and x in B both holds -/
lemma char_fun_inter {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) : char_fun (A ∩ B) x = (char_fun A x) * (char_fun B x) := by
    repeat unfold char_fun
    repeat unfold toInt
    simp only [Finset.mem_inter, mul_ite, mul_one, mul_zero]
    by_cases h: x ∈ A
    · simp [h]
    · simp only [h, false_and, ↓reduceIte, ite_self]

/-- We claim that x in the union of A and B is equal to at least one of x in A and x in B holds  -/
lemma char_fun_union {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) : char_fun (A ∪ B) x = 1 - (1 - char_fun A x) * (1 - char_fun B x) := by
    repeat unfold char_fun
    repeat unfold toInt
    simp only [Finset.mem_union]
    by_cases h : x ∈ A
    · by_cases i : x ∈ B
      · simp[h,i]
      · simp[h,i]
    · by_cases i : x ∈ B
      · simp[h,i]
      · simp[h,i]
