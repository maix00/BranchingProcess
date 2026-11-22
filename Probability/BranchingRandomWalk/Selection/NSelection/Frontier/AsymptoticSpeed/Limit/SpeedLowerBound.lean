/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Speed.CapacityHit
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.LowerBound

/-!
# Lower asymptotic bound for the speed of N-selection

## Public declarations

* `exists_speed_with_logSq_lowerBound`: for every nonempty initial cloud of
  size at most $N$, $M_k/k\to v_N$ almost surely and in $L^1$. Under the
  boundary, finite-variance, cross-weight and fourth-moment assumptions,
  $\liminf_{N\to\infty}(\log N)^2 v_N\ge\pi^2\sigma^2/2$.

* `exists_speed_with_logSq_lowerBound_of_firstMoment`: the common speed
  has $\liminf_{N\to\infty}(\log N)^2 v_N\ge\pi^2\sigma^2/2$ under a
  leftmost first moment, boundary normalization and centered finite variance.

This includes the two lower bounds in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.2 and the one-sided first-moment speed estimate
following Lemma 4.1.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance speedLowerAddressOrder (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

private lemma exists_common_speed
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L) :
    ∃ speed : ℕ → ℝ,
      (∀ N m : ℕ, 0 < m → m ≤ N → ∀ initial : Fin m → ℝ,
        let P := finiteRootStepFieldLaw L.sortedPotentialImage m
        let endpoint := fun field n =>
          RootIndexed.selectedPopulationEndpointWithParameter m N n (initial, field)
        (∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (endpoint field) (speed N)) ∧
        Tendsto (fun n : ℕ => eLpNorm (fun field =>
          (n : ℝ)⁻¹ * endpoint field n - speed N) 1 P) atTop (𝓝 0)) := by
  classical
  have hsplit : (1 : ℝ≥0∞) < ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂L.raw := by
    have h := hsuper
    unfold ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.expectedChildCount at h
    have hcast : Measurable (fun j : ℕ∞ => (j : ℝ≥0∞)) := by fun_prop
    change (1 : ℝ≥0∞) < ∫⁻ j : ℕ∞, (j : ℝ≥0∞) ∂L.raw.map Step.childCount at h
    rw [lintegral_map hcast Step.childCount_measurable] at h
    exact h
  have hcapacity (N : ℕ) (hN : 0 < N) :=
    smallInitialPopulation_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
      N hN L hboundary hnonempty hfirst hsplit
  let speed (N : ℕ) := if hN : 0 < N then Classical.choose (hcapacity N hN) else 0
  have hsmall (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) (initial : Fin m → ℝ) :=
    (Classical.choose_spec (hcapacity N (hm.trans_le hmN))).2 m initial hm hmN
  refine ⟨speed, ?_⟩
  intro N m hm hmN initial
  have hN := hm.trans_le hmN
  have h := hsmall N m hm hmN initial
  simpa [speed, dite_eq_left hN] using And.intro h.1 h.2.2

/-- The common speed from nonempty initial populations exists and satisfies
the lower bound of Wang Yiyang, Theorem 1.2. -/
theorem exists_speed_with_logSq_lowerBound
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
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
      ∀ r < (Real.pi ^ 2 / 2) * sigma ^ 2,
        ∀ᶠ N : ℕ in atTop, r < Real.log (N : ℝ) ^ 2 * speed N := by
  obtain ⟨speed, hspeed⟩ :=
    exists_common_speed L hsuper hnonempty hboundary (fourthMoment_implies_firstMoment L hfour)
  refine ⟨speed, hspeed, fun r hr => ?_⟩
  apply eventually_lt_logSq_mul_speed L hsuper hnonempty hboundary
    hcross hfour hsigma hspine speed _ hr
  intro N hN
  simpa only [selectedPopulationEndpointTrajectoryWithParameter] using
    (hspeed N N hN le_rfl (fun _ => 0)).2

/-- The first-moment speed lower bound of Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 4, obtained by applying Lemma 4.1 in the block comparison. -/
theorem exists_speed_with_logSq_lowerBound_of_firstMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
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
      (((Real.pi ^ 2 / 2) * sigma ^ 2 : ℝ) : EReal) ≤
        atTop.liminf (fun N : ℕ => ((Real.log (N : ℝ) ^ 2 * speed N : ℝ) : EReal)) := by
  obtain ⟨speed, hspeed⟩ := exists_common_speed L hsuper hnonempty hboundary hfirst
  refine ⟨speed, hspeed, ?_⟩
  by_contra! hlt
  obtain ⟨r, hliminf, hr⟩ := EReal.exists_between_coe_real hlt
  have hL1 (N : ℕ) (hN : 0 < N) :=
    (hspeed N N hN le_rfl (fun _ => 0)).2
  have hevent := eventually_lt_logSq_mul_speed_of_firstMoment L hnonempty hboundary hfirst
    hsigma hspine speed hL1 (EReal.coe_lt_coe_iff.mp hr)
  have hle : ∀ᶠ N : ℕ in atTop, (r : EReal) ≤ (Real.log (N : ℝ) ^ 2 * speed N : ℝ) :=
    hevent.mono fun _ hn => EReal.coe_le_coe hn.le
  have hconst := Filter.liminf_le_liminf hle
  exact (not_le_of_gt hliminf) (by simpa using hconst)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
