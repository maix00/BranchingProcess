/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Corridor
public import Probability.BranchingRandomWalk.Walk.Path.Corridor.Horizontal

/-!
# Corridor events for random walks

This file connects deterministic corridor membership to measurable events of
an increment path and to horizontal-tube probabilities.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- The finite horizontal-tube event is exactly closed corridor membership on
the positive time grid after spatial normalization. -/
theorem inHorizontalTube_iff_inClosedCorridorOnGrid
    {a width : ℝ} (hwidth : 0 < width) (n : ℕ)
    (increment : ℕ → ℝ) :
    InHorizontalTube a width n increment ↔
      InClosedCorridorOnGrid (fun _ => width) n
        (fun _ => -a) (fun _ => 1 - a) increment := by
  constructor
  · intro h
    rw [InClosedCorridorOnGrid]
    intro k
    dsimp only
    have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
    have hpath :
        normalizedStepPath (fun _ => width) n increment
            (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) =
          width⁻¹ * partialSum (k.val + 1) increment := by
      exact normalizedStepPath_grid (fun _ => width) hn increment
    rw [hpath]
    exact ⟨by
      simpa [div_eq_inv_mul] using (le_div_iff₀ hwidth).2 (h k).1,
      by simpa [div_eq_inv_mul] using (div_le_iff₀ hwidth).2 (h k).2⟩
  · intro h k
    have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
    have hk := h k
    dsimp [InClosedCorridorOnGrid] at hk
    have hpath :
        normalizedStepPath (fun _ => width) n increment
            (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) =
          width⁻¹ * partialSum (k.val + 1) increment := by
      exact normalizedStepPath_grid (fun _ => width) hn increment
    rw [hpath] at hk
    exact ⟨by
      apply (le_div_iff₀ hwidth).1
      simpa [div_eq_inv_mul] using hk.1,
      by
      apply (div_le_iff₀ hwidth).1
      simpa [div_eq_inv_mul] using hk.2⟩

/-- The finite horizontal-tube predicate is exactly the whole-time closed
corridor event for the associated step path. -/
theorem inHorizontalTube_iff_inClosedCorridor
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hwidth : 0 < width) {n : ℕ} (hn : 0 < n)
    (increment : ℕ → ℝ) :
    InHorizontalTube a width n increment ↔
      InClosedCorridor (fun _ => -a) (fun _ => 1 - a)
        (normalizedStepPath (fun _ => width) n increment) := by
  rw [inHorizontalTube_iff_inClosedCorridorOnGrid hwidth]
  symm
  exact inClosedCorridor_const_iff_grid (fun _ => width) hn
    (neg_nonpos.2 ha0) (sub_nonneg.2 ha1) increment

/-- The whole-time constant-corridor event of the normalized step path is
measurable as an event of the increment path. -/
theorem measurableSet_inClosedCorridor_const_normalizedStepPath
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hwidth : 0 < width) {n : ℕ} (hn : 0 < n) :
    MeasurableSet {increment : ℕ → ℝ |
      InClosedCorridor (fun _ => -a) (fun _ => 1 - a)
        (normalizedStepPath (fun _ => width) n increment)} := by
  rw [show {increment : ℕ → ℝ |
      InClosedCorridor (fun _ => -a) (fun _ => 1 - a)
        (normalizedStepPath (fun _ => width) n increment)} =
      {increment | InHorizontalTube a width n increment} by
    ext increment
    exact (inHorizontalTube_iff_inClosedCorridor
      ha0 ha1 hwidth hn increment).symm]
  exact measurableSet_inHorizontalTube a width n


end ProbabilityTheory.RandomWalk
