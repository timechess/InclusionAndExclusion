import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Int.Star
import Mathlib.Data.Multiset.Fintype


-- Thank 王镜廷 of PKU for providing the proof of this theorem
open BigOperators

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

/-- It's obvious that if a Finset A equals to a Set B in the view of Set, then they have the same number of elements. Since we use this lemma a lot in below proof, we put it here to be an independent lemma -/
lemma card_eq {α : Type*} (A : Finset α) (B : Set α) [Fintype B] (h : A = B) : Fintype.card B = Fintype.card A := by
  simp_rw [← h]
  rfl
/-- Here we formalize the polynomial expansion of (∏ i (1 - g i)) -/
lemma mul_expand₃ (n : ℕ) (g : ℕ → ℤ) : ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j := by
  induction' n with n ih
  · simp
  · rw [Finset.prod_range_succ]
    have (n : ℕ) : (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S) * ∏ j : S, g j) = Multiset.sum (Multiset.map (fun (S : Multiset ℕ) ↦ (-1) ^ (Fintype.card S) * Multiset.prod (Multiset.map g S)) (Multiset.range n).powerset) := by
      unfold Finset.powerset Finset.sum
      simp
      congr 1
      apply Multiset.map_eq_map_of_bij_of_nodup
      · apply (Multiset.Nodup.pmap (by intro a ha b hb h; show (@Finset.mk ℕ a ha).val = (@Finset.mk ℕ b hb).val; rw [h]) (Multiset.Nodup.powerset (Multiset.nodup_range n)))
      · apply Multiset.Nodup.powerset (Multiset.nodup_range n)
      pick_goal 5
      · use fun a _ ↦ a.1
      · intro a ha
        simp at ha
        rcases ha with ⟨a₁,h,ha₁⟩
        simp
        exact le_of_eq_of_le (congrArg Finset.val (id (Eq.symm ha₁))) h
      · intro a₁ _ a₂ _ h
        apply Finset.val_inj.mp h
      · intro b h
        have hb := Multiset.nodup_of_le (Multiset.mem_powerset.mp h) (Multiset.nodup_range n)
        use (@Finset.mk ℕ b hb)
        simp
        exact Multiset.mem_powerset.mp h
      · intro a ha
        simp
        exact Finset.prod_attach a g
    rw [this] at *
    simp at *
    conv =>
      enter [2, 2, 1, 1]
      ext x
      rw [← mul_assoc, pow_succ, mul_assoc _ (-1), mul_comm _ (-1 * g n), ← Int.neg_eq_neg_one_mul, mul_assoc]
    conv =>
      enter [2, 2]
      rw [Multiset.sum_map_mul_left]
    rw [← ih]
    conv =>
      enter [2, 1]
      rw [← one_mul (∏ i ∈ Finset.range n, (1 - g i))]
    rw [← add_mul]
    rw [sub_eq_add_neg]
    rw [mul_comm]
/-- Same as above, here we formalize the polynomial expansion of (1 - ∏ i (1 - g i)) -/
lemma mul_expand₂ (n : ℕ) (g : ℕ → ℤ) : 1 - ∏ i ∈ Finset.range n, (1 - g i) = ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j := by
  have : ∑ S ∈ (Finset.range n).powerset₀, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j = (∑ S ∈ (Finset.range n).powerset, (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) + 1 := by
    have : (fun (S : Finset ℕ) ↦ (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) = (fun (S : Finset ℕ) ↦ if S = ∅ then (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j else (-1) ^ (Fintype.card S + 1) * ∏ j : S, g j) := by
      simp
    nth_rw 2 [this]
    rw [Finset.sum_ite]
    unfold Finset.powerset₀
    simp
    set u := ∑ x ∈ Finset.filter (fun S ↦ ¬S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g j.val
    set v := ∑ x ∈ Finset.filter (fun S ↦ S = ∅) (Finset.range n).powerset, (-1) ^ (x.card + 1) * ∏ j ∈ x.attach, g j.val with hv
    rw [add_comm v u]
    rw [add_assoc]
    nth_rw 1 [← add_zero u]
    congr 1
    rw [hv]
    have : Finset.filter (fun S => S = ∅) (Finset.range n).powerset = ({∅} : Finset (Finset ℕ)) := by
      ext x
      simp
      intro h
      rw [h]
      exact Finset.empty_subset (Finset.range n)
    rw [this]
    simp
  rw [this]
  rw [mul_expand₃]
  conv =>
    enter [2, 1]
    congr
    · skip
    ext s
    rw [pow_succ]
    rw [mul_comm _ (-1)]
  simp
  rw [add_comm]
  rw [sub_eq_add_neg]
/-- Here we formalize the polynomial expansion of (1 - ∏ i (1 - g i)) in the view of (Finset (Fin n)) -/
lemma mul_expand₁ (n : ℕ) (g : ℕ → ℤ) : 1 - ∏ (i : Fin n), (1 - g i) = ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
  conv =>
    enter [1, 2]
    rw [(Finset.prod_range fun i ↦ 1 - g i).symm]
  have hr : ∑ (S : Finset.powerset₀ (Finset.univ (α := Fin n))), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    apply Finset.sum_bij
    pick_goal 5
    · intro a ha
      use Finset.map ⟨fun (x : Fin n) ↦ x.val, (by exact Fin.val_injective)⟩ a.val
      unfold Finset.powerset₀ at *
      rcases a with ⟨a₁, ha₁⟩
      simp at ha₁
      simp [ha₁]
      intro x hx
      simp at hx
      rcases hx with ⟨ax,⟨_,hax₂⟩⟩
      simp
      rw [← hax₂]
      exact ax.isLt
    · intro a ha
      simp
    · intro a₁ ha₁ a₂ ha₂ h
      simp at h
      exact SetCoe.ext h
    · simp
      unfold Finset.powerset₀
      simp
      intro a ha₁ ha₂
      have : ∀ x ∈ a, x < n := by
        intro x hx
        exact List.mem_range.mp (ha₁ hx)
      use a.attachFin this
      constructor
      · have : (a.attachFin this).card ≠ 0 := by
          rw [Finset.card_attachFin]
          simp [ha₂]
        exact ne_of_apply_ne Finset.card this
      ext x
      simp
      constructor
      · intro hx
        rcases hx with ⟨a₁,⟨ha₁,ha₂⟩⟩
        rw [← ha₂]
        exact ha₁
      · intro hx
        use ⟨x, this x hx⟩
    · intro a ha
      simp
      rw [Finset.prod_attach]
      simp
      rw [Finset.prod_attach a.val (fun (x : Fin n) ↦ g x.val)]
  rw [hr]
  rw [mul_expand₂]
  have hr' : ∑ (S : Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) = ∑ (S ∈ Finset.powerset₀ (Finset.range n)), (-1) ^ (Fintype.card S + 1) * (∏ (j : S), g j) := by
    symm
    apply Finset.sum_subtype
    simp
  rw [hr']
