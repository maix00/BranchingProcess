/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Basic
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.Edge.LowerMovingTube
import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Lemmas.Edge.UpperMovingTube
/-!
# Robust terminal geometry at the two edges

The module-visible supporting lemmas in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.prefixPositiveWindow_and_transition_subset_robustMovingTransitionEvent`:
  the lower-edge fixed prefix and nonnegative meander suffix imply the
  moving corridor with endpoint in $[h_n+2\Delta/5,h_n+3\Delta/5]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.prefixNegativeWindow_and_reflectedTransition_subset_robustMovingTransitionEvent`:
  the reflected upper-edge construction gives the same terminal interval.

These are the two fixed-prefix constructions of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7. Their printed
terminal bounds are strengthened to the displayed robust interval by
increasing the width threshold, with each prefix length fixed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The lower-edge prefix and conditioned suffix end in the narrower
entrance window at a sufficiently large width. -/
lemma prefixPositiveWindow_and_transition_subset_robustMovingTransitionEvent
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc 0 (width / 12))
    (hprefixHeight : drift ≤ (m : ℝ) * a)
    (hprefixUpper : 12 * (m : ℝ) * b ≤ width)
    (hstep : drift ≤ a * width ^ 2)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2)
    (hsmallPrefix : 120 * (m : ℝ) * b ≤ 7 * width) :
    {increment : ℕ → ℝ |
      (∀ k < m, increment k ∈ Set.Icc a b) ∧
      (fun k => increment (m + k)) ∈
        FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} ⊆
      robustMovingTransitionEvent (m + N) width drift start := by
  intro increment hinc
  have hmove :=
    prefixPositiveWindow_and_transition_subset_movingCorridorEvent
      hwidth hdrift ha hab hstart hprefixHeight hprefixUpper
      hstep htotal hinc
  have hprefixLower : (m : ℝ) * a ≤
      AdditivePath.displacement m increment := by
    have hsum : (∑ i ∈ Finset.range m, a) ≤
        ∑ i ∈ Finset.range m, increment i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i (Finset.mem_range.mp hi)).1
    simpa [AdditivePath.displacement, mul_comm] using hsum
  have hprefixHigh : AdditivePath.displacement m increment ≤
      (m : ℝ) * b := by
    have hsum : (∑ i ∈ Finset.range m, increment i) ≤
        ∑ i ∈ Finset.range m, b := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i (Finset.mem_range.mp hi)).2
    simpa [AdditivePath.displacement, mul_comm] using hsum
  have hsplit : AdditivePath.displacement (m + N) increment =
      AdditivePath.displacement m increment +
        AdditivePath.displacement N (fun k => increment (m + k)) := by
    exact AdditivePath.displacement_add m N increment
  have hend := hinc.2.2
  have hshift : drift * ((m + N : ℕ) : ℝ) / width ^ 2 ≤ drift := by
    apply (div_le_iff₀ (sq_pos_of_pos hwidth)).2
    exact mul_le_mul_of_nonneg_left htotal hdrift
  have hshiftNonneg :
      0 ≤ drift * ((m + N : ℕ) : ℝ) / width ^ 2 := by positivity
  refine ⟨hmove, ?_⟩
  constructor
  · rw [hsplit]
    nlinarith [hprefixLower, hend.1, hstart.1, hshift, hprefixHeight,
      hwidth]
  · rw [hsplit]
    nlinarith [hprefixHigh, hend.2, hstart.2, hshiftNonneg,
      hsmallPrefix]

/-- The upper-edge reflected prefix and conditioned suffix end in the
narrower entrance window at a sufficiently large width. -/
lemma prefixNegativeWindow_and_reflectedTransition_subset_robustMovingTransitionEvent
    {m N : ℕ} {width drift start a b : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (ha : 0 < a) (hab : a ≤ b)
    (hstart : start ∈ Set.Icc (11 / 12 * width) width)
    (hprefixUpper : 24 * (m : ℝ) * b ≤ width)
    (hsmallDrift : 24 * drift ≤ width)
    (htotal : ((m + N : ℕ) : ℝ) ≤ width ^ 2)
    (hsmallSum : 120 * ((m : ℝ) * b + drift) ≤ 5 * width) :
    {increment : ℕ → ℝ |
      (∀ k < m, -increment k ∈ Set.Icc a b) ∧
      (fun k => -increment (m + k)) ∈
        FunctionalLimit.Conditioned.nonnegativeTransitionEvent N width} ⊆
      robustMovingTransitionEvent (m + N) width drift start := by
  intro increment hinc
  have hmove :=
    prefixNegativeWindow_and_reflectedTransition_subset_movingCorridorEvent
      hwidth hdrift ha hab hstart hprefixUpper hsmallDrift htotal hinc
  let reflected : ℕ → ℝ := fun k => -increment k
  have hprefixLower : (m : ℝ) * a ≤
      AdditivePath.displacement m reflected := by
    have hsum : (∑ i ∈ Finset.range m, a) ≤
        ∑ i ∈ Finset.range m, reflected i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i (Finset.mem_range.mp hi)).1
    simpa [AdditivePath.displacement, reflected, mul_comm] using hsum
  have hprefixHigh : AdditivePath.displacement m reflected ≤
      (m : ℝ) * b := by
    have hsum : (∑ i ∈ Finset.range m, reflected i) ≤
        ∑ i ∈ Finset.range m, b := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hinc.1 i (Finset.mem_range.mp hi)).2
    simpa [AdditivePath.displacement, reflected, mul_comm] using hsum
  have hsplit : AdditivePath.displacement (m + N) reflected =
      AdditivePath.displacement m reflected +
        AdditivePath.displacement N (fun k => reflected (m + k)) := by
    exact AdditivePath.displacement_add m N reflected
  have hposition : start + AdditivePath.displacement (m + N) increment =
      width - ((width - start) +
        AdditivePath.displacement (m + N) reflected) := by
    simp [reflected, AdditivePath.displacement_neg]
    ring
  have hend := hinc.2.2
  have hshift : drift * ((m + N : ℕ) : ℝ) / width ^ 2 ≤ drift := by
    apply (div_le_iff₀ (sq_pos_of_pos hwidth)).2
    exact mul_le_mul_of_nonneg_left htotal hdrift
  have hshiftNonneg :
      0 ≤ drift * ((m + N : ℕ) : ℝ) / width ^ 2 := by positivity
  refine ⟨hmove, ?_⟩
  constructor
  · rw [hposition, hsplit]
    nlinarith [hprefixHigh, hend.2, hstart.1, hshift,
      hsmallSum]
  · rw [hposition, hsplit]
    nlinarith [hprefixLower, hend.1, hstart.2,
      hshiftNonneg, hwidth, ha]

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
