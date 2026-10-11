/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Speed.InitialPopulation

/-!
# Speed after a finite time shift

If a trajectory agrees after a fixed finite time with a trajectory of known
asymptotic speed, then the original trajectory has the same speed. The proof
accounts for the change from the local generation denominator to the absolute
generation denominator.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching.Selection.NSelection

/-- A finite initial segment and the absolute-time denominator do not change
the asymptotic speed of a trajectory. -/
theorem hasAsymptoticSpeed_of_eq_after_time
    (trajectory localTrajectory : ℕ → ℝ) (time : ℕ) (speed : ℝ)
    (htrajectory : ∀ n, trajectory (time + n) = localTrajectory n)
    (hlocal : HasAsymptoticSpeed (𝕜 := ℝ) localTrajectory speed) :
    HasAsymptoticSpeed (𝕜 := ℝ) trajectory speed := by
  rw [hasAsymptoticSpeed_iff_nat_add]
  have hlocal' : Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹) * localTrajectory n) atTop (𝓝 speed) := hlocal
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) + (time : ℝ))) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (time : ℝ)
  have hproduct := hratio.mul hlocal'
  have hshift : (fun n : ℕ => (((n + time : ℕ) : ℝ)⁻¹) *
      trajectory (n + time)) =ᶠ[atTop]
      (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + (time : ℝ))) *
        (((n : ℝ)⁻¹) * localTrajectory n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hcast : ((n + time : ℕ) : ℝ) = (n : ℝ) + (time : ℝ) := by
      exact Nat.cast_add n time
    have htrajectory' : trajectory (n + time) = localTrajectory n := by
      simpa [Nat.add_comm] using htrajectory n
    rw [htrajectory', hcast]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  exact Tendsto.congr' hshift.symm (by simpa using hproduct)

/-- Almost surely, a trajectory inherits a deterministic asymptotic speed
from a local trajectory when they agree after an almost surely finite time. -/
theorem ae_hasAsymptoticSpeed_of_eq_after_time
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (trajectory localTrajectory : Ω → ℕ → ℝ) (time : Ω → ℕ) (speed : ℝ)
    (htrajectory : ∀ᵐ ω ∂P, ∀ n,
      trajectory ω (time ω + n) = localTrajectory ω n)
    (hlocal : ∀ᵐ ω ∂P,
      HasAsymptoticSpeed (𝕜 := ℝ) (localTrajectory ω) speed) :
    ∀ᵐ ω ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (trajectory ω) speed := by
  filter_upwards [htrajectory, hlocal] with ω htrajectoryω hlocalω
  exact hasAsymptoticSpeed_of_eq_after_time (trajectory ω)
    (localTrajectory ω) (time ω) speed htrajectoryω hlocalω

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
