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
    intro x
    have := List.eq_FinInter A (x2 :: xs) (cons_ne_nil x2 _)
    simp only [this, mem_cons, forall_eq_or_imp]
    simp only [implies_true]
  )

/-- We say the intersection of several finite sets does not depend on the order in which who and who intersect first. Therefore, we introduce the definition of multiset. Given a function A, we define a new function from a multiset to the intersection of finite sets whose index is in the multiset -/
def Multiset.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (β := Finset α) (List.FinInter A) (by
    intro a b hab
    simp [Setoid.r] at hab
    ext x
    by_cases ept:a≠ []
    have :b≠ []:=by
      contrapose! ept
      rw[ept] at hab
      exact Eq.symm (List.Perm.nil_eq (id (List.Perm.symm hab)))
    rw[List.eq_FinInter _ _ this]
    rw[List.eq_FinInter _ _ ept]
    constructor
    · intro ha aa bb
      have hyp: aa ∈ a := by exact (List.Perm.mem_iff (id (List.Perm.symm hab))).mp bb
      have hyp' : x ∈ A aa := by exact ha aa hyp
      exact hyp'
    · intro ha aa bb
      have hyp: aa ∈ b := by exact (List.Perm.mem_iff hab).mp bb
      exact ha aa hyp
    simp only [ne_eq, not_not] at ept
    rw[ept]
    have : b = [] := by rw[ept] at hab;exact Eq.symm (List.Perm.nil_eq hab)
    rw[this]
  )

/-- We prove the lemma 'List.eq_FinInter' to be still true in the multiset case -/
lemma Multiset.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) (h : M ≠ ∅) : ∀ x : α, x ∈ M.FinInter A ↔ ∀ m ∈ M, x ∈ A m := by
  intro x
  have : M.FinInter A = M.toList.FinInter A := by
    unfold Multiset.FinInter
    have : M.toList = M := by simp
    nth_rw 1 [← this]
    rfl
  rw [this]
  rw [List.eq_FinInter]
  simp
  simpa
/-- Given a finite index set (@Finset.univ β _), we define FinInter₀ to be the intersection of all finite sets whose index's type is β -/
def FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Finset α := Multiset.FinInter A (Finset.univ).1

/-- Same as above, we prove the lemma 'List.eq_FinInter' to be still true in the whole case -/
lemma eq_FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [h : Nonempty β] (A : β → Finset α) :
  FinInter₀ A = ⋂ (i : β), (A i : Set α) := by
  unfold FinInter₀
  ext x
  simp
  rw[Multiset.eq_FinInter]
  · simp
  · have h1:∀ t:β,t∈ Finset.univ.val :=by exact fun t => Finset.mem_univ_val t
    intro h2
    rw[h2]at h1
    simp only [Multiset.empty_eq_zero, Multiset.not_mem_zero, forall_const] at h1

/-- We show that the intersection of finite number of finite sets is still a finite set -/
instance FinInter_Fin {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype (⋂ (i : β), (A i : Set α)) := by
  rw [← eq_FinInter₀]
  simp only [Finset.coe_sort_coe]
  exact FinsetCoe.fintype (FinInter₀ A)
