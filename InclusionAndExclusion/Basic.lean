import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype

-- Thank 王镜廷 of PKU for providing the proof of this theorem
open BigOperators
/-- given finite number of finite sets, List.FinInter returns their intersection using an inductive way -/
def List.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: [] => A x
  | x1 :: x2 :: xs => A x1 ∩ List.FinInter A (x2 :: xs)

/-- given finite number of finite sets, List.FinInter returns their union using an inductive way -/
def List.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : Finset α :=
  match L with
  | [] => ∅
  | x :: xs => A x ∪ (xs.FinUnion A)
/-- forall x : α, show that x ∈ (List.FinInter A L) ↔ forall i in L, x ∈ (A i) -/
lemma List.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) (h : L ≠ []) : ∀ x : α, x ∈ L.FinInter A ↔ ∀ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by absurd h; rfl)
  | x :: [] => (by unfold List.FinInter; simp)
  | x1 :: x2 :: xs => (by
    unfold List.FinInter
    simp
    intro x _
    have := List.eq_FinInter A (x2 :: xs) (by exact cons_ne_nil x2 xs) x
    rw [this]
    simp
  )
/-- forall x : α, show that x ∈ (List.FinUnion A L) ↔ there exists an i in L, such that x ∈ (A i) -/
lemma List.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α)(L : List β) : ∀ x : α, x ∈ L.FinUnion A ↔ ∃ i ∈ L, x ∈ A i :=
  match L with
  | [] => (by unfold List.FinUnion; simp)
  | x :: [] => (by unfold List.FinUnion; unfold List.FinUnion; simp)
  | x1 :: x2 :: xs => (by
    unfold List.FinUnion
    simp
    intro x
    have := List.eq_FinUnion A (x2 :: xs) x
    rw [this]
    simp
  )
/-- we say the intersection of several finite sets does not depend on the order in which who and who intersect first. Therefore, we introduce the definition of multiset. Given a function A, we define a new function from a multiset to the intersection of finite sets whose index is in the multiset -/
def Multiset.FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (β := Finset α) (List.FinInter A) (by
    intro a b hab
    unfold Setoid.r at hab
    unfold List.isSetoid at hab
    change a.Perm b at hab
    by_cases h : a = []
    · simp [h]
      simp [h] at hab
      simp [hab]
    · have : ¬ b = [] := by
        by_contra h'
        simp [h'] at hab
        contradiction
      ext x
      rw [List.eq_FinInter _ _ h]
      rw [List.eq_FinInter _ _ this]
      simp_rw [List.Perm.mem_iff hab]
    )
/-- Same as above, we define a new function from a multiset to the union of finite sets whose index is in the multiset -/
def Multiset.FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Multiset β → Finset α :=
  Quot.lift (α := List β) (List.FinUnion A) (by
    intro a b hab
    unfold Setoid.r List.isSetoid at hab
    ext x
    rw [List.eq_FinUnion, List.eq_FinUnion]
    change a.Perm b at hab
    simp_rw [List.Perm.mem_iff hab]
  )
/-- We prove the lemma 'List.eq_FinInter' to be still true in the multiset case -/
lemma Multiset.eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) (h : M ≠ ∅) : ∀ x : α, x ∈ M.FinInter A ↔ ∀ m ∈ M, x ∈ A m := by
  intro x
  have : M.FinInter A = M.toList.FinInter A := by
    unfold Multiset.FinInter
    have : M.toList = M := by simp
    nth_rw 1 [← this]
    apply lift_coe
    intro a b hab
    change a.Perm b at hab
    by_cases h : a = []
    · simp [h]
      simp [h] at hab
      simp [hab]
    · have : ¬ b = [] := by
        by_contra h'
        simp [h'] at hab
        contradiction
      ext x
      rw [List.eq_FinInter _ _ h]
      rw [List.eq_FinInter _ _ this]
      simp_rw [List.Perm.mem_iff hab]
  rw [this]
  rw [List.eq_FinInter]
  · simp
  · simp
    exact h
/-- We prove the lemma 'List.eq_FinUnion' to be still true in the multiset case -/
lemma Multiset.eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (M : Multiset β) : ∀ x : α, x ∈ M.FinUnion A ↔ ∃ m ∈ M, x ∈ A m := by
  intro x
  have : M.FinUnion A = M.toList.FinUnion A := by
    unfold Multiset.FinUnion
    have : M.toList = M := by simp
    nth_rw 1 [← this]
    apply lift_coe
    intro a b hab
    change a.Perm b at hab
    ext x
    rw [List.eq_FinUnion, List.eq_FinUnion]
    simp_rw [List.Perm.mem_iff hab]
  rw [this]
  rw [List.eq_FinUnion]
  simp
/-- Given a finite index set (@Finset.univ β _), we define FinInter₀ to be the intersection of all finite sets whose index's type is β -/
def FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) : Finset α := Multiset.FinInter A (Finset.univ).1
/-- Given a finite index set (@Finset.univ β _), we define FinUnion₀ to be the union of all finite sets whose index's type is β -/
def FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) : Finset α := Multiset.FinUnion A (Finset.univ).1
/-- Same as above, we prove the lemma 'List.eq_FinInter' to be still true in the whole case -/
lemma eq_FinInter₀ {α β : Type*} [DecidableEq α] [Fintype β] [h : Nonempty β] (A : β → Finset α) :
  FinInter₀ A = ⋂ (i : β), (A i : Set α) := by
  unfold FinInter₀
  ext x
  simp
  rw [Multiset.eq_FinInter]
  · simp
  · simp
    apply Finset.nonempty_iff_ne_empty.mp
    exact Finset.univ_nonempty_iff.mpr h
/-- Same as above, we prove the lemma 'List.eq_FinUnion' to be still true in the whole case -/
lemma eq_FinUnion₀ {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  FinUnion₀ A = ⋃ (i : β), (A i : Set α) := by
  unfold FinUnion₀
  ext x
  simp
  rw [Multiset.eq_FinUnion]
  simp
/-- We show that the intersection of finite number of finite sets is still a finite set -/
instance FinInter_Fin {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype (⋂ (i : β), (A i : Set α)) := by
  rw [← eq_FinInter₀]
  exact FinsetCoe.fintype (FinInter₀ fun i ↦ A i)
/-- We show that the union of finite number of finite sets is still a finite set -/
instance FinUnion_Fin {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype (⋃ (i : β), (A i : Set α)) := by
  rw [← eq_FinUnion₀]
  exact FinsetCoe.fintype (FinUnion₀ fun i ↦ A i)
/-- We define all the nonempty subsets of A to be A.powerset₀ -/
def Finset.powerset₀ {α : Type*} (A : Finset α) : Finset (Finset α) :=
  Finset.filter (fun S ↦ (Fintype.card S ≠ 0)) A.powerset
/-- We show that every element whose type is A.powerset₀ is nonempty -/
instance powerset₀_nonempty {α : Type*} {A : Finset α} (S : A.powerset₀) : Nonempty S := by
  apply Finset.Nonempty.coe_sort
  apply Finset.nonempty_iff_ne_empty.mpr
  unfold Finset.powerset₀ at S
  have := S.2
  simp at this
  exact this.2
/-- We assign a value to a proposition. If the proposition holds, we assign a value of 1; otherwise, we assign a value of 0 -/
def toInt (P : Prop) [Decidable P] : ℤ := if P then 1 else 0
/-- The value of P and Q both holds is equal to the value of P times the value of Q -/
lemma toInt_and {P Q : Prop} [Decidable P] [Decidable Q] : toInt (P ∧ Q) = toInt P * toInt Q := by
  unfold toInt
  by_cases h : P
  · by_cases h' : Q
    · simp only [h, h', and_self]
      rfl
    · simp only [h, h', and_false]
      rfl
  · by_cases h' : Q
    · simp only [h, h', and_true]
      rfl
    · simp only [h, h', and_self]
      rfl
/-- The value of ¬ P is equal to one sub the value of P -/
lemma toInt_not (P : Prop) [Decidable P] : toInt (¬ P) = 1 - toInt P := by
  unfold toInt
  by_cases h : P
  · simp only [h, not_true_eq_false]
    rfl
  · simp only [h, not_false_eq_true]
    rfl
/-- We define a function that if x ∈ A then returns 1, else returns 0 -/
def char_fun {α : Type*} [DecidableEq α] (A : Finset α) (x : α) : ℤ := toInt (x ∈ A)
/-- Here we introduce a way to calculate the number of elements in B which is a subset of A -/
lemma card_eq_sum_char_fun {α : Type*} [DecidableEq α] {A B : Finset α} (h : B ⊆ A) : Fintype.card B = Finset.sum A (char_fun B) := by
  trans ∑ _ : B, (1 : ℕ)
  · simp
  · unfold char_fun
    unfold toInt
    simp
    rw [Finset.inter_eq_right.mpr h]
/-- We claim that x ∈ (A ∩ B) is equal to x ∈ A and x ∈ B both holds -/
lemma char_fun_inter {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) : char_fun (A ∩ B) x = (char_fun A x) * (char_fun B x) := by
    unfold char_fun
    rw [← toInt_and]
    simp
/-- We claim that x ∈ (A ∪ B) is equal to at least one of x ∈ A and x ∈ B holds  -/
lemma char_fun_union {α : Type*} [DecidableEq α] (A B : Finset α) (x : α) : char_fun (A ∪ B) x = 1 - (1 - char_fun A x) * (1 - char_fun B x) := by
    unfold char_fun
    rw [← toInt_not]
    rw [← toInt_not]
    rw [← toInt_and]
    rw [← toInt_not]
    simp
    simp_rw [Decidable.or_iff_not_imp_left]
/-- We claim that x ∈ (∩ i (A i)) is equal to forall i, x ∈ (A i) holds -/
lemma char_fun_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) (x : α) : char_fun (FinInter₀ A) x = ∏ (i : β), (char_fun (A i) x) := by
  by_cases h : ∃ (i : β), char_fun (A i) x = 0
  · obtain ⟨y, hy⟩ := h
    have : ∏ i : β, char_fun (A i) x = 0 := by
      apply Finset.prod_eq_zero
      · exact Finset.mem_univ y
      · rw [hy]
    rw [this]
    unfold char_fun toInt
    simp
    rw [← Finset.mem_coe, eq_FinInter₀]
    simp
    unfold char_fun toInt at hy
    simp at hy
    exact ⟨y, hy⟩
  · unfold char_fun toInt at h
    simp at h
    have h' : ∀ (y : β), char_fun (A y) x = 1 := by
      unfold char_fun toInt
      intro y
      simp [h y]
    simp_rw [h']
    simp
    unfold char_fun toInt
    simp
    rw [← Finset.mem_coe, eq_FinInter₀]
    simp
    exact h

lemma char_fun_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) (x : α) :
  char_fun (FinUnion₀ A) x = 1 - ∏ (i : β), (1 - char_fun (A i) x) := by
  by_cases h : ∃ (i : β), char_fun (A i) x = 1
  · obtain ⟨y, hy⟩ := h
    have : ∏ i : β, (1 - char_fun (A i) x) = 0 := by
      apply Finset.prod_eq_zero
      · exact Finset.mem_univ y
      · rw [hy, sub_self]
    rw [this, sub_zero]
    unfold char_fun toInt
    simp? says simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [← Finset.mem_coe, eq_FinUnion₀]
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe]
    unfold char_fun toInt at hy
    simp? at hy says simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at hy
    exact ⟨y, hy⟩
  · unfold char_fun toInt at h
    simp? at h says
      simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not, not_exists] at h
    have h' : ∀ (y : β), char_fun (A y) x = 0 := by
      unfold char_fun toInt
      intro y
      simp? [h y] says simp only [h y, ↓reduceIte]
    simp_rw [h']
    simp? says simp only [sub_zero, Finset.prod_const_one, sub_self]
    unfold char_fun toInt
    simp? says simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Finset.mem_coe, eq_FinUnion₀]
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe, not_exists]
    exact h

lemma card_eq {α : Type*} (A : Finset α) (B : Set α) [Fintype B] (h : A = B) :
  Fintype.card B = Fintype.card A := by
  simp_rw [← h]
  simp only [Finset.coe_sort_coe, Fintype.card_coe]

lemma card_eq_FinInter {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] (A : β → Finset α) :
  Fintype.card (⋂ (i : β), (A i : Set α)) = Fintype.card (FinInter₀ A) := by
    exact card_eq _ _ (eq_FinInter₀ A)

lemma card_eq_FinUnion {α β : Type*} [DecidableEq α] [Fintype β] (A : β → Finset α) :
  Fintype.card (⋃ (i : β), (A i : Set α)) = Fintype.card (FinUnion₀ A) := by
    exact card_eq _ _ (eq_FinUnion₀ A)

lemma mul_expand₃ (n : ℕ) (g : ℕ → ℤ) : ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j := by
  induction' n with n ih
  · simp? says
      simp only [Finset.range_zero, Finset.prod_empty, Finset.powerset_empty, Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, Finset.sum_singleton, Finset.card_empty, pow_zero, Finset.attach_empty, mul_one]
  · rw [Finset.prod_range_succ]
    have (n : ℕ) : (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j) = Multiset.sum (Multiset.map (fun (S : Multiset ℕ) ↦ (-1) ^ (Fintype.card S) * Multiset.prod (Multiset.map g S)) (Multiset.range n).powerset) := by
      unfold Finset.powerset
      unfold Finset.sum
      simp
      congr 1
      apply Multiset.map_eq_map_of_bij_of_nodup
      · apply Multiset.Nodup.pmap
        · intro a b b1 hb1 heq
          show (@Finset.mk ℕ a b).val = (@Finset.mk ℕ b1 hb1).val
          rw [heq]
        · apply Multiset.Nodup.powerset
          exact Multiset.nodup_range n
      · apply Multiset.Nodup.powerset
        exact Multiset.nodup_range n
      pick_goal 5
      · use fun x _ ↦ x.1
      · intro a ha
        simp at ha
        obtain ⟨a1, ha1, heq⟩ := ha
        apply Multiset.mem_powerset.mpr
        rw [← heq]
        exact ha1
      · intro _ _ _ _ heq
        exact Finset.val_inj.mp heq
      · intro b hb
        simp at hb
        have : b.Nodup := by
          exact Multiset.nodup_of_le hb (Multiset.nodup_range n)
        use Finset.mk b this
        simp
        exact hb
      · intro a ha
        simp at ha
        obtain ⟨a1, ha1, heq⟩ := ha
        simp
        rw [← heq]
        apply Finset.prod_attach
    rw [this] at *
    simp only [Multiset.range_succ, Multiset.powerset_cons, Int.reduceNeg, Multiset.card_coe,
      Multiset.map_add, Multiset.map_map, Function.comp_apply, Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_add]
    simp only [Int.reduceNeg, Multiset.card_coe] at ih
    conv => {
    rhs
    congr
    · skip
    · congr
      · congr
        ext x
        · rw [← mul_assoc, pow_succ, mul_assoc _ (-1) _, mul_comm _ (-1 * g n), ← Int.neg_eq_neg_one_mul, mul_assoc]}
    conv => {
    rhs
    congr
    · skip
    · rw [Multiset.sum_map_mul_left]}
    rw [← ih, mul_sub, mul_one, neg_mul, sub_eq_add_neg, mul_comm]

lemma mul_expand₂ (n : ℕ) (g : ℕ → ℤ) : 1 - ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j := by
  have : ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j = (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) + 1 := by
    have : (fun (S : Finset ℕ) ↦ (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) = (fun (S : Finset ℕ) ↦ if S = ∅ then (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j else (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) := by
      simp? says
        simp only [Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, ite_self]
    nth_rw 2 [this]
    rw [Finset.sum_ite]
    unfold Finset.powerset₀
    simp? says
      simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Int.reduceNeg, Finset.univ_eq_attach]
    set u := ∑ x ∈ Finset.filter (fun S ↦ ¬S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g ↑j
    set v := ∑ x ∈ Finset.filter (fun S ↦ S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g ↑j with hv
    rw [add_comm v u, add_assoc]
    nth_rw 1 [← add_zero u]
    congr 1
    rw [hv]
    have : Finset.filter (fun S ↦ S = ∅) (Finset.range n).powerset = ({∅} : Finset (Finset ℕ)) := by
      ext S
      simp? says
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, and_iff_right_iff_imp]
      intro h
      rw [h]
      exact Finset.empty_subset (Finset.range n)
    rw [this]
    simp? says
      simp only [Int.reduceNeg, Finset.sum_singleton, Finset.card_empty, zero_add, pow_one, Finset.attach_empty, Finset.prod_empty, mul_one, add_left_neg]
  rw [this, sub_eq_add_neg, Int.neg_eq_neg_one_mul, mul_expand₃ n g, Finset.mul_sum, add_comm 1 _]
  congr 2
  ext S
  rw [← mul_assoc, pow_succ']

lemma mul_expand₁ (n : ℕ) (g : ℕ → ℤ) :
  1 - ∏ (i : Fin n), (1 - g i) =
    ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))),
      (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
  have hl : ∏ (i : Fin n), (1 - g i) = ∏ i in Finset.range n, (1 - g i) := by
    exact (Finset.prod_range fun i ↦ 1 - g i).symm
  have hr : ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    apply Finset.sum_bij
    pick_goal 5
    · intro a _
      use Finset.map ⟨fun (x : Fin n) ↦ x.1, by exact Fin.val_injective⟩ a.1
      unfold Finset.powerset₀ at *
      obtain ⟨a1, ha1⟩ := a
      simp? at ha1 says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and] at ha1
      simp? [ha1] says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.mem_filter,Finset.mem_powerset, Finset.map_eq_empty, ha1, not_false_eq_true, and_true]
      intro x hx
      simp at hx
      obtain ⟨a2, ⟨_, ha2⟩⟩ := hx
      rw [← ha2]
      simp? says simp only [Finset.mem_range, Fin.is_lt]
    · simp? says simp only [Finset.univ_eq_attach, Finset.mem_attach, imp_self, implies_true]
    · intro _ _ _ _ heq
      simp? at heq says
        simp only [Subtype.mk.injEq, Finset.map_inj] at heq
      exact SetCoe.ext heq
    · simp? says
        simp only [Finset.univ_eq_attach, Finset.mem_attach, exists_true_left, Subtype.exists, true_implies, Subtype.forall, Subtype.mk.injEq, exists_prop]
      unfold Finset.powerset₀
      simp? says
        simp only [Fintype.card_coe, ne_eq, Finset.card_eq_zero, Finset.mem_filter, Finset.mem_powerset, Finset.powerset_univ, Finset.mem_univ, true_and, and_imp]
      intro a ha hnempa
      have : ∀ (x : ℕ), x ∈ a → x < n := by
        intro x hx
        have := ha hx
        simp? at this says simp only [Finset.mem_range] at this
        exact this
      let a' : Finset (Fin n) := a.attachFin (fun n' hn' ↦ this n' hn')
      use a'
      constructor
      · have : a'.card ≠ 0 := by
          unfold_let a'
          rw [Finset.card_attachFin]
          simp? says simp only [ne_eq, Finset.card_eq_zero]
          exact hnempa
        exact ne_of_apply_ne Finset.card this
      · ext x
        simp? says simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
        unfold_let a'
        constructor
        · rintro ⟨a1, ha1, heq⟩
          rw [← heq]
          simp?  at ha1 says simp only [Finset.mem_attachFin] at ha1
          exact ha1
        · intro hx
          use ⟨x, this x hx⟩
          simp? says simp only [Finset.mem_attachFin, and_true]
          exact hx
    · intro a ha
      simp? says
        simp only [Int.reduceNeg, Fintype.card_coe, Finset.univ_eq_attach, Finset.mem_map, Function.Embedding.coeFn_mk, ne_eq, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast, Finset.card_map, mul_eq_mul_left_iff, add_eq_zero, Finset.card_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff, neg_eq_zero, or_false]
      rw [Finset.prod_attach]
      simp? says simp only [Finset.prod_map, Function.Embedding.coeFn_mk]
      rw [Finset.prod_attach a.1 (fun (x : Fin n) ↦ g x.val)]
  have hr' : ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S ∈ Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    symm
    apply Finset.sum_subtype
    simp? says simp only [implies_true]
  rw [hl, hr, hr']
  exact mul_expand₂ n g

lemma mul_expand (n : ℕ) (g : (Fin n) → ℤ) :
  1 - ∏ (i : Fin n), (1 - g i) =
    ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))),
      (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
        set g' : ℕ → ℤ := fun x ↦ if h : x < n then g ⟨x, h⟩ else 0
        have (x : Fin n) : g' x = g x := by
          show (fun x ↦ if h : x < n then g ⟨x, h⟩ else 0) x = g x
          simp
        simp_rw [← this]
        exact mul_expand₁ n g'

theorem Principle_of_Inclusion_Exclusion {α : Type*} [DecidableEq α] (n : ℕ) (A : (Fin n) → Finset α) :
  (Fintype.card (⋃ (i : Fin n), ((A i) : Set α)))
    = Finset.sum
      (Finset.univ (α := (Finset.powerset₀ (Finset.univ (α := Fin n)))))
        (fun S ↦ (-1 : ℤ) ^ (Fintype.card S + 1) * Fintype.card (⋂ (i : S.1), ((A i) : Set α))) := by
  set U : Finset α := FinUnion₀ A
  rw [card_eq_FinUnion]
  simp_rw [card_eq_FinInter]
  have hU1 : FinUnion₀ A ⊆ U := by rfl
  have hU2 (S : (Finset.powerset₀ (Finset.univ (α := Fin n)))) :
    @FinInter₀ α S _ _ _ (fun i ↦ A i) ⊆ U := by
    rw [← Finset.coe_subset, eq_FinInter₀, eq_FinUnion₀]
    intro x hx
    let s : S.1 := Classical.choice (by infer_instance)
    simp? says simp only [Set.mem_iInter, Finset.mem_coe, Subtype.forall] at hx
    simp? says simp only [Set.mem_iUnion, Finset.mem_coe]
    exact ⟨s.1, hx s.1 s.2⟩
  rw [card_eq_sum_char_fun hU1]
  conv => {
    rhs
    congr
    · skip
    · ext S
      rw [card_eq_sum_char_fun (hU2 S)]
      rw [Finset.mul_sum]}
  rw [Finset.sum_comm]
  congr 1
  ext x
  set g := fun (i : Fin n) ↦ char_fun (A i) x
  have hg (i : Fin n) : g i = char_fun (A i) x := rfl
  conv => {
    congr
    · rw [char_fun_FinUnion]
      congr
      · skip
      · congr
        · skip
        · ext i
          · rw [← hg i]
    · congr
      · skip
      · ext S
        rw [char_fun_FinInter]
        congr
        · skip
        · congr
          · skip
          · ext i
            · rw [← hg i]}
  apply mul_expand
