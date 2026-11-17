/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.SpeedLowerBound
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.SpeedUpperBound
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.LowerBound

/-!
# The asymptotic speed of the N-branching random walk

## Public declarations

* `exists_speed_with_logSq_limit`: from each deterministic nonempty
  initial population of size at most $N$, the minimum divided by time
  converges almost surely and in $L^1$ to the common speed $v_N$.
  Under boundary normalization and the stated first-moment assumptions,
  $v_N(\log N)^2\to\pi^2\sigma^2/2$.

This is the first-moment speed formula of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4.
-/

open Asymptotics MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

/-- Common speed and its logarithmic asymptotic, from the two block comparisons. -/
theorem exists_speed_with_logSq_limit
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2)) :
    ∃ speed : ℕ → ℝ,
      (∀ N m : ℕ, 0 < m → m ≤ N → ∀ initial : Fin m → ℝ,
        let P := finiteRootStepFieldLaw L.sortedPotentialImage m
        let endpoint := fun field n =>
          RootIndexed.selectedPopulationEndpointWithParameter m N n (initial, field)
        (∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (endpoint field) (speed N)) ∧
        Tendsto (fun n : ℕ => eLpNorm (fun field =>
          (n : ℝ)⁻¹ * endpoint field n - speed N) 1 P) atTop (𝓝 0)) ∧
      Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 * speed N) atTop
        (𝓝 ((Real.pi ^ 2 / 2) * sigma ^ 2)) := by
  obtain ⟨speed, hspeed, _⟩ := exists_speed_with_logSq_lowerBound_of_firstMoment L
    hsuper hnonempty hboundary hfirst hsigma hspine
  have hL1 (N : ℕ) (hN : 0 < N) := (hspeed N N hN le_rfl (fun _ => 0)).2
  refine ⟨speed, hspeed, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro r hr
    exact eventually_lt_logSq_mul_speed_of_firstMoment L hnonempty hboundary hfirst
      hsigma hspine speed hL1 hr
  · intro r hr
    exact eventually_logSq_mul_speed_lt_of_firstMoment L hsuper hnonempty hboundary hcross hfirst
      hsigma hspine speed hL1 hr

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
