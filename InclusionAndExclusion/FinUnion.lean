import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype
import InclusionAndExclusion.Auxiliary
-- Thank 王镜廷 of PKU for providing the proof of this theorem

open BigOperators

/-- Given finite number of finite sets, List.FinInter returns their union using an inductive way -/
def List.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: xs => A x ∪ (xs.FinUnion A)

/-- Forall x of type α, x in (List.FinUnion A L) if and only if there exists an i in L, such that x in (A i) -/
lemma List.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : ∀ x : α, x ∈ L.FinUnion A ↔ ∃ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by unfold List.FinUnion; simp)
  | x :: [] => (by unfold List.FinUnion; unfold List.FinUnion; simp)
  | x1 :: x2 :: xs => (by
    sorry
  )

/-- We define a new function from a multiset to the union of finite sets whose index is in the multiset -/
def Multiset.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (List.FinUnion A) (by
    sorry
  )

/-- We prove the lemma 'List.eq_FinUnion' to be still true in the multiset case -/
lemma Multiset.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) : ∀ x : α, x ∈ M.FinUnion A ↔ ∃ m ∈ M, x ∈ A m := by
  sorry

/-- Given a finite index set (@Finset.univ β _), we define FinUnion₀ to be the union of all finite sets whose index's type is β -/
def FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Finset α := Multiset.FinUnion A (Finset.univ).1

/-- Same as above, we prove the lemma 'List.eq_FinUnion' to be still true in the whole case -/
lemma eq_FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  FinUnion₀ A = ⋃ (i : β), (A i : Set α) := by
  sorry

/-- We show that the union of finite number of finite sets is still a finite set -/
instance FinUnion_Fin {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype (⋃ (i : β), (A i : Set α)) := by
  sorry
