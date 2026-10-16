/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Edge.LowerGeometry
/-!
# Upper-edge reflected prefix and meander-suffix geometry

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.prefixNegativeWindow_and_reflectedTransition_subset_movingTransitionEvent`:
  for $x\in[11\Delta/12,\Delta]$, a fixed prefix with reflected
  increments in $[a,b]\subset(0,\infty)$ followed by
  $D_{N,\Delta}$ for the reflected walk is contained in
  $\mathcal A_\Delta(x)$ at time $m+N$.

This is the upper-edge reflection in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7, used in the proof of Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- A fixed negative prefix followed by the reflected transition event
enters the exact moving corridor from the upper edge. -/
theorem prefixNegativeWindow_and_reflectedTransition_subset_movingTransitionEvent
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc (11 / 12 * width) width)
    (hprefixUpper : 24 * (m : ℝ) * b ≤ width)
    (hsmallDrift : 24 * drift ≤ width)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2) :
    {increment : ℕ → ℝ |
      (∀ k < m, -increment k ∈ Set.Icc a b) ∧
      (fun k => -increment (m + k)) ∈
        FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} ⊆
      movingTransitionEvent (m + N) width drift start := by
  intro increment hinc
  let reflected : ℕ → ℝ := fun k => -increment k
  let tail : ℕ → ℝ := fun k => reflected (m + k)
  let reflectedStart : ℝ := width - start
  have hstartR : reflectedStart ∈ Set.Icc 0 (width / 12) := by
    constructor <;> dsimp [reflectedStart] <;> linarith [hstart.1, hstart.2]
  have hprefixSum (j : ℕ) (hj : j ≤ m) :
      (j : ℝ) * a ≤ AdditivePath.displacement j reflected ∧
      AdditivePath.displacement j reflected ≤ (j : ℝ) * b := by
    have hlow : (∑ i ∈ Finset.range j, a) ≤
        ∑ i ∈ Finset.range j, reflected i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i ((Finset.mem_range.mp hi).trans_le hj)).1
    have hhigh : (∑ i ∈ Finset.range j, reflected i) ≤
        ∑ i ∈ Finset.range j, b := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i ((Finset.mem_range.mp hi).trans_le hj)).2
    simpa [AdditivePath.displacement, mul_comm, reflected] using
      And.intro hlow hhigh
  have hprefixAtM := hprefixSum m le_rfl
  have hsplit (j : ℕ) (hj : m ≤ j) :
      AdditivePath.displacement j reflected =
        AdditivePath.displacement m reflected +
          AdditivePath.displacement (j - m) tail := by
    conv_lhs => rw [← Nat.add_sub_of_le hj,
      AdditivePath.displacement_add]
  have hwidthSq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hshiftNonneg (j : ℕ) :
      0 ≤ drift * (j : ℝ) / width ^ 2 :=
    div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hwidthSq.le
  have hshiftLe (j : ℕ) (hj : j ≤ m + N) :
      drift * (j : ℝ) / width ^ 2 ≤ drift := by
    apply (div_le_iff₀ hwidthSq).2
    exact mul_le_mul_of_nonneg_left
      ((Nat.cast_le.mpr hj).trans htotal) hdrift
  have hrelate (j : ℕ) :
      start + AdditivePath.displacement j increment =
        width - (reflectedStart + AdditivePath.displacement j reflected) := by
    simp [reflectedStart, reflected, AdditivePath.displacement_neg]
    ring
  have hreflectedBounds (j : ℕ) (hj : j ≤ m + N) :
      0 ≤ reflectedStart + AdditivePath.displacement j reflected ∧
      reflectedStart + AdditivePath.displacement j reflected ≤ width - drift := by
    by_cases hjPrefix : j ≤ m
    · have hp := hprefixSum j hjPrefix
      have hjCast : (j : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hjPrefix
      have hjNonneg : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      constructor
      · nlinarith [hp.1, hstartR.1, ha.le, hjNonneg]
      · nlinarith [hp.2, hstartR.2, hprefixUpper,
          hsmallDrift, mul_le_mul_of_nonneg_right hjCast (le_trans ha.le hab)]
    · have hmj : m < j := Nat.lt_of_not_ge hjPrefix
      let r := j - m
      have hrpos : 0 < r := Nat.sub_pos_iff_lt.mpr hmj
      have hrle : r ≤ N := by omega
      have htail := hinc.2.1 ⟨r - 1, by omega⟩
      have hrSucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
      rw [hrSucc] at htail
      rw [hsplit j hmj.le]
      have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      constructor
      · nlinarith [hprefixAtM.1, htail.1, hstartR.1,
          ha.le, hmNonneg]
      · nlinarith [hprefixAtM.2, htail.2, hstartR.2,
          hprefixUpper, hsmallDrift]
  unfold movingTransitionEvent
  constructor
  · intro k
    let j := k.val + 1
    have hj : j ≤ m + N := Nat.succ_le_of_lt k.isLt
    have hr := hreflectedBounds j hj
    have hp := hrelate j
    constructor
    · nlinarith [hr.2, hp, hshiftLe j hj]
    · nlinarith [hr.1, hp, hshiftNonneg j]
  · have hposition := hsplit (m + N) (Nat.le_add_right m N)
    have hsub : m + N - m = N := Nat.add_sub_cancel_left m N
    rw [hsub] at hposition
    have hend := hinc.2.2
    have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hRlower : 5 / 12 * width ≤
        reflectedStart + AdditivePath.displacement (m + N) reflected := by
      rw [hposition]
      nlinarith [hprefixAtM.1, hend.1, hstartR.1,
        ha.le, hmNonneg]
    have hRupper :
        reflectedStart + AdditivePath.displacement (m + N) reflected ≤
          7 / 12 * width := by
      rw [hposition]
      nlinarith [hprefixAtM.2, hend.2, hstartR.2, hprefixUpper]
    have hp := hrelate (m + N)
    constructor
    · nlinarith [hRupper, hp, hshiftLe (m + N) le_rfl,
        hsmallDrift]
    · nlinarith [hRlower, hp, hshiftNonneg (m + N)]

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
