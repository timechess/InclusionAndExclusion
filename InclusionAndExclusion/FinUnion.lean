import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype

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
    unfold List.FinUnion
    simp only [Finset.mem_union, mem_cons, exists_eq_or_imp]
    intro h
    have := List.eq_FinUnion A (x2 :: xs) h
    simp only [this, mem_cons, exists_eq_or_imp]
  )

/-- We define a new function from a multiset to the union of finite sets whose index is in the multiset -/
def Multiset.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (List.FinUnion A) (by
  intro a b h
  simp [Setoid.r] at h
  ext x
  repeat rw [List.eq_FinUnion]
  constructor
  · intro h'
    rcases h' with ⟨i, ia, iA⟩
    use i
    constructor
    · exact (List.Perm.mem_iff h).mp ia
    · exact iA
  · intro h'
    rcases h' with ⟨i, ia, iA ⟩
    use i
    constructor
    · exact (List.Perm.mem_iff (id (List.Perm.symm h))).mp ia
    · exact iA
  )

/-- We prove the lemma 'List.eq_FinUnion' to be still true in the multiset case -/
lemma Multiset.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) :
∀ x : α, x ∈ M.FinUnion A ↔ ∃ m ∈ M, x ∈ A m := by
  intro h
  have : M = M.toList :=by simp
  have : M.FinUnion A = M.toList.FinUnion A := by
    unfold FinUnion
    nth_rw 1 [this]
    exact rfl
  rw [this]
  rw [List.eq_FinUnion]
  simp only [mem_toList]

/-- Given a finite index set (@Finset.univ β _), we define FinUnion₀ to be the union of all finite sets whose index's type is β -/
def FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Finset α := Multiset.FinUnion A (Finset.univ).1

/-- Same as above, we prove the lemma 'List.eq_FinUnion' to be still true in the whole case -/
lemma eq_FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : FinUnion₀ A = ⋃ (i : β), (A i : Set α) := by
  unfold FinUnion₀
  ext x
  simp
  rw [Multiset.eq_FinUnion]
  simp

/-- We show that the union of finite number of finite sets is still a finite set -/
instance FinUnion_Fin {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype (⋃ (i : β), (A i : Set α)) := by
  rw [← eq_FinUnion₀]
  exact FinsetCoe.fintype (FinUnion₀ fun i ↦ A i)
