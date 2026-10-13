/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointLowerTail

/-!
# `L²` assembly for the logarithmic endpoint trajectory

Combine the proved lower-tail estimate with the existing fourth-moment
closure and a separately supplied upper-tail estimate on the same countable
root environment. The upper-tail input is the remaining theorem-specific
obligation; this assembly does not assert it.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

set_option maxHeartbeats 500000

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Assemble the lower endpoint tail with the existing fourth-moment
estimate and a polynomial upper-tail bound on the common countable-root
space. The lower-tail bound is derived from the paper's centered finite
variance spine assumptions. The upper-tail input is stated on that exact
space and remains to be supplied by the long-corridor argument.

The spine hypotheses in this intermediate interface are written for the
ordered potential-image law, which is the law used by the common-root
construction. They express the corresponding left-side assumptions for this
canonical law presentation. -/
theorem normalizedCountableRootEndpointMinimum_tendsto_eLpNorm_two_of_upperTail
    {L : ProbabilityTheory.BranchingRandomWalk.StepLaw ℕ ℕ ℝ}
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : ProbabilityTheory.BranchingRandomWalk.HasLeftmostFourthMoment L)
    (hsupercritical :
      ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
        (⟨L.sortedPotentialImage, inferInstance⟩ :
          ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
      (L.sortedPotentialImage : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential (-1)
        (L.sortedPotentialImage : Measure (Step ℕ ℝ))))
    {horizon : ℕ → ℕ} {a t : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n : ℕ => (horizon n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t))
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
        ∀ᶠ n : ℕ in atTop,
          (RootIndexed.stepFieldLaw (Root := ℕ)
            L.sortedPotentialImage).real
            {field | ε ≤ normalizedCountableRootEndpointMinimum
              (Nat.floor ((n : ℝ) ^ a)) n (horizon n)
              (-a + (Real.pi ^ 2 / 2) *
                (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
                  (L.sortedPotentialImage : Measure (Step ℕ ℝ))) * t)
              field} ≤ C / (n : ℝ) ^ p) :
    Tendsto
      (fun n : ℕ => eLpNorm
        (fun field => if 1 < n then
          normalizedCountableRootEndpointMinimum
            (Nat.floor ((n : ℝ) ^ a)) n (horizon n)
            (-a + (Real.pi ^ 2 / 2) *
              (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
                (L.sortedPotentialImage : Measure (Step ℕ ℝ))) * t)
            field
          else 0)
        (2 : ℝ≥0∞)
        (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage))
      atTop (nhds 0) := by
  let μ := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
  have hboundaryImage : HasBoundaryNormalization realPotential
      (L.sortedPotentialImage : Measure (Step ℕ ℝ)) :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyImage : L.sortedPotentialImage nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  let M : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ :=
    ⟨L.sortedPotentialImage, inferInstance⟩
  have hnonemptyLaw : M.HasAtLeastOneChild := by
    simpa [HasAtLeastOneChild, M] using hnonemptyImage
  have hlower :=
    normalizedCountableRootEndpointMinimum_lowerTail_le_polynomial_of_logarithmic_scales
      (L := M) hboundaryImage hnonemptyLaw hsupercritical hspineMean hspineFiniteVariance
      (horizon := horizon) (a := a) (t := t)
      ha_zero ha_one ht hhorizon
  have hm : ∀ n : ℕ, 1 < n → 0 < Nat.floor ((n : ℝ) ^ a) := by
    intro n hn
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hn)
    have hpow := Real.rpow_le_rpow_of_exponent_le hnreal ha_zero
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ a := by simpa using hpow
    have hfloor : 1 ≤ Nat.floor ((n : ℝ) ^ a) :=
      Nat.le_floor (by exact_mod_cast hone)
    omega
  have hm_le : ∀ n : ℕ, 1 < n → Nat.floor ((n : ℝ) ^ a) ≤ n := by
    intro n hn
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hn)
    have hpow : (n : ℝ) ^ a ≤ (n : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hnreal ha_one
    have hfloor : (Nat.floor ((n : ℝ) ^ a) : ℝ) ≤ (n : ℝ) := by
      calc
        (Nat.floor ((n : ℝ) ^ a) : ℝ) ≤ (n : ℝ) ^ a :=
          Nat.floor_le (by positivity)
        _ ≤ (n : ℝ) := hpow
    exact_mod_cast hfloor
  exact normalizedCountableRootEndpointMinimum_tendsto_eLpNorm_two
    (m := fun n => Nat.floor ((n : ℝ) ^ a)) hm hm_le ht hhorizon
    L hboundary hnonempty hfour hupper hlower

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
