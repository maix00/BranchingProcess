/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.MovingInterior
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.TransitionFactorization

/-!
# Lower-edge prefix and meander-suffix geometry

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.prefixPositiveWindow_and_transition_subset_movingTransitionEvent`:
  for $x\in[0,\Delta/12]$, a fixed prefix of increments in
  $[a,b]\subset(0,\infty)$ followed by the independent event
  $D_{N,\Delta}$ is contained in the moving corridor event
  $\mathcal A_\Delta(x)$ at time $m+N$.

This is the lower-edge event inclusion in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The positive fixed prefix and independent transition suffix produce
the exact moving entrance event from the lower edge. -/
theorem prefixPositiveWindow_and_transition_subset_movingTransitionEvent
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc 0 (width / 12))
    (hprefixHeight : drift ≤ (m : ℝ) * a)
    (hprefixUpper : 12 * (m : ℝ) * b ≤ width)
    (hstep : drift ≤ a * width ^ 2)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2) :
    {increment : ℕ → ℝ |
      (∀ k < m, increment k ∈ Set.Icc a b) ∧
      (fun k => increment (m + k)) ∈
        FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} ⊆
      movingTransitionEvent (m + N) width drift start := by
  intro increment hinc
  let tail : ℕ → ℝ := fun k => increment (m + k)
  have hprefixSum (j : ℕ) (hj : j ≤ m) :
      (j : ℝ) * a ≤ AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤ (j : ℝ) * b := by
    have hlow : (∑ i ∈ Finset.range j, a) ≤
        ∑ i ∈ Finset.range j, increment i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i ((Finset.mem_range.mp hi).trans_le hj)).1
    have hhigh : (∑ i ∈ Finset.range j, increment i) ≤
        ∑ i ∈ Finset.range j, b := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i ((Finset.mem_range.mp hi).trans_le hj)).2
    simpa [AdditivePath.displacement, mul_comm] using And.intro hlow hhigh
  have hwidthSq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hshiftNonneg (j : ℕ) :
      0 ≤ drift * (j : ℝ) / width ^ 2 :=
    div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hwidthSq.le
  have hshiftLe (j : ℕ) (hj : j ≤ m + N) :
      drift * (j : ℝ) / width ^ 2 ≤ drift := by
    apply (div_le_iff₀ hwidthSq).2
    exact mul_le_mul_of_nonneg_left
      ((Nat.cast_le.mpr hj).trans htotal) hdrift
  have hsplit (j : ℕ) (hj : m ≤ j) :
      AdditivePath.displacement j increment =
        AdditivePath.displacement m increment +
          AdditivePath.displacement (j - m) tail := by
    conv_lhs => rw [← Nat.add_sub_of_le hj,
      AdditivePath.displacement_add]
  have hprefixAtM := hprefixSum m le_rfl
  unfold movingTransitionEvent
  constructor
  · intro k
    let j := k.val + 1
    have hj : j ≤ m + N := Nat.succ_le_of_lt k.isLt
    by_cases hjPrefix : j ≤ m
    · have hp := hprefixSum j hjPrefix
      have hjNonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      have hstepJ : drift * (j : ℝ) ≤
          a * width ^ 2 * (j : ℝ) :=
        mul_le_mul_of_nonneg_right hstep hjNonneg
      have hmoveLower : drift * (j : ℝ) / width ^ 2 ≤ (j : ℝ) * a := by
        apply (div_le_iff₀ hwidthSq).2
        nlinarith [hstepJ]
      have hpos : 0 ≤ (j : ℝ) * a := mul_nonneg hjNonneg ha.le
      have hupper : start + AdditivePath.displacement j increment ≤ width := by
        have hjCast : (j : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hjPrefix
        nlinarith [hp.2, hstart.2, hprefixUpper,
          mul_le_mul_of_nonneg_right hjCast (le_trans ha.le hab)]
      exact ⟨by nlinarith [hp.1, hstart.1],
        hupper.trans (le_add_of_nonneg_right (hshiftNonneg j))⟩
    · have hmj : m < j := Nat.lt_of_not_ge hjPrefix
      let r := j - m
      have hrpos : 0 < r := Nat.sub_pos_iff_lt.mpr hmj
      have hrle : r ≤ N := by omega
      have htail := hinc.2.1 ⟨r - 1, by omega⟩
      have hrSucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
      rw [hrSucc] at htail
      have hposition := hsplit j hmj.le
      have hupper : start + AdditivePath.displacement j increment ≤ width := by
        rw [hposition]
        nlinarith [hprefixAtM.2, htail.2, hstart.2, hprefixUpper]
      have hlower : drift * (j : ℝ) / width ^ 2 ≤
          start + AdditivePath.displacement j increment := by
        rw [hposition]
        nlinarith [hprefixAtM.1, htail.1, hstart.1,
          hprefixHeight, hshiftLe j hj]
      exact ⟨hlower,
        hupper.trans (le_add_of_nonneg_right (hshiftNonneg j))⟩
  · have hposition := hsplit (m + N) (Nat.le_add_right m N)
    have hsub : m + N - m = N := Nat.add_sub_cancel_left m N
    rw [hsub] at hposition
    have hend := hinc.2.2
    constructor
    · rw [hposition]
      nlinarith [hprefixAtM.1, hend.1, hstart.1,
        hshiftLe (m + N) le_rfl, hprefixHeight]
    · rw [hposition]
      nlinarith [hprefixAtM.2, hend.2, hstart.2,
        hprefixUpper, hshiftNonneg (m + N)]

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
