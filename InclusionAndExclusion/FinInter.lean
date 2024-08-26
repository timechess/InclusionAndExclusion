import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype

-- Thank 王镜廷 of PKU for providing the proof of this theorem

open BigOperators
/-- Given finite number of finite sets, List.FinInter returns their intersection using an inductive way -/
def List.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: [] => A x
  | x1 :: x2 :: xs => A x1 ∩ List.FinInter A (x2 :: xs)

/-- Forall x of type α, x in (List.FinInter A L) if and only if forall i in L, x in (A i) -/
lemma List.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) (h : L ≠ []) : ∀ x : α, x ∈ L.FinInter A ↔ ∀ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by absurd h; rfl)
  | x :: [] => (by unfold List.FinInter; simp)
  | x1 :: x2 :: xs => (by
    unfold List.FinInter
    simp only [Finset.mem_inter, mem_cons, forall_eq_or_imp, and_congr_right_iff]
    intro x a
    have := List.eq_FinInter A (x2 :: xs) (cons_ne_nil x2 _)
    simp only [this, mem_cons, forall_eq_or_imp]

  )

/-- We say the intersection of several finite sets does not depend on the order in which who and who intersect first. Therefore, we introduce the definition of multiset. Given a function A, we define a new function from a multiset to the intersection of finite sets whose index is in the multiset -/
def Multiset.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (β := Finset α) (List.FinInter A) (by
    sorry
    )

/-- We prove the lemma 'List.eq_FinInter' to be still true in the multiset case -/
lemma Multiset.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) (h : M ≠ ∅) : ∀ x : α, x ∈ M.FinInter A ↔ ∀ m ∈ M, x ∈ A m := by
  sorry

/-- Given a finite index set (@Finset.univ β _), we define FinInter₀ to be the intersection of all finite sets whose index's type is β -/
def FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Finset α := Multiset.FinInter A (Finset.univ).1

/-- Same as above, we prove the lemma 'List.eq_FinInter' to be still true in the whole case -/
lemma eq_FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [h : Nonempty β] (A : β → Finset α) :
  FinInter₀ A = ⋂ (i : β), (A i : Set α) := by
  sorry

/-- We show that the intersection of finite number of finite sets is still a finite set -/
instance FinInter_Fin {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype (⋂ (i : β), (A i : Set α)) := by
  sorry
