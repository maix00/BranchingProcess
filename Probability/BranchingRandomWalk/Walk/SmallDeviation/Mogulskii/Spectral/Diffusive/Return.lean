/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return.Horizontal
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Diffusive.Endpoint

/-!
# Diffusive killed-block estimates

The Brownian corridor estimate is transferred to a killed random-walk block
whose terminal interval is wider than its starting core.  These estimates
are useful one-block comparisons, but the uniform bound below is not a
self-map row bound on the terminal interval and therefore cannot be iterated
by itself.  Sharp Mogulskii blocking still needs a uniform core-to-core
transition estimate.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory.RandomWalk.Mogulskii

open Combinatorics.Branching.Walk

/-- The sharp Brownian unit-corridor constant bounds the `liminf` mass of a
diffusive killed block started at zero, provided its return interval is
strictly wider than the unit corridor and is contained in the outer interval.
-/
theorem ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredReturnKernel
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {innerWidth outerWidth : ℝ} (hinner : 1 < innerWidth)
    (hwidth : innerWidth ≤ outerWidth) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        returnKernel ν
          (Set.Icc (-(outerWidth * Real.sqrt n / 2))
            (outerWidth * Real.sqrt n / 2)) measurableSet_Icc
          (Set.Icc (-(innerWidth * Real.sqrt n / 2))
            (innerWidth * Real.sqrt n / 2)) measurableSet_Icc
          n ⟨0, by
            have hsqrt := Real.sqrt_nonneg (n : ℝ)
            have hinnerNonneg : 0 ≤ innerWidth := le_trans (by norm_num) hinner.le
            constructor <;> nlinarith [mul_nonneg hinnerNonneg hsqrt]⟩
          Set.univ) := by
  have houter : 1 < outerWidth := hinner.trans_le hwidth
  refine (ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTubeEndsIn
    ν hν hB hcontinuous hmeasurable houter
      (by linarith : -(innerWidth / 2) < -(1 / 2 : ℝ))
      (by linarith : (1 / 2 : ℝ) < innerWidth / 2)).trans ?_
  apply Filter.liminf_le_liminf _
    (Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le))
    (Filter.isCoboundedUnder_ge_of_le atTop (fun (n : ℕ) =>
      IsSubMarkovKernel.measure_univ_le_one (κ :=
        returnKernel ν
          (Set.Icc (-(outerWidth * Real.sqrt n / 2))
            (outerWidth * Real.sqrt n / 2)) measurableSet_Icc
          (Set.Icc (-(innerWidth * Real.sqrt n / 2))
            (innerWidth * Real.sqrt n / 2)) measurableSet_Icc n)
        ⟨0, by
          have hsqrt := Real.sqrt_nonneg (n : ℝ)
          have hinnerNonneg : 0 ≤ innerWidth := le_trans (by norm_num) hinner.le
          constructor <;> nlinarith [mul_nonneg hinnerNonneg hsqrt]⟩))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hinnerNonneg : 0 ≤ innerWidth := le_trans (by norm_num) hinner.le
  simpa only using
    strictTubeNormalizedEndsInProbability_le_returnKernel_centeredIcc
      ν hn (Real.sqrt_pos.2 (by exact_mod_cast hn)) le_rfl hinnerNonneg

/-- Every constant strictly below the principal Brownian corridor mass is an
eventual one-block lower bound, uniformly over a centered interval of
starting points.  A single centered increment-tube event works for every
start, so no finite discretization of the initial interval is needed.  The
terminal return interval must contain that whole increment tube; hence this
statement alone does not give a uniform row bound for every point in the
terminal interval. -/
theorem eventually_uniform_centeredReturnKernel_of_lt_exp_neg_pi_sq_div_two
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {pathWidth initialWidth outerWidth returnWidth : ℝ}
    (hpathWidth : 1 < pathWidth)
    (houter : initialWidth + pathWidth ≤ outerWidth)
    (hreturn : initialWidth + pathWidth ≤ returnWidth)
    {lowerBound : ENNReal}
    (hlowerBound : lowerBound <
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : Set.Icc (-(initialWidth / 2)) (initialWidth / 2),
        lowerBound ≤ returnKernel ν
          (Set.Icc (-(outerWidth * Real.sqrt n / 2))
            (outerWidth * Real.sqrt n / 2)) measurableSet_Icc
          (Set.Icc (-(returnWidth * Real.sqrt n / 2))
            (returnWidth * Real.sqrt n / 2)) measurableSet_Icc
          n ⟨Real.sqrt n * x, by
            have hsqrt := Real.sqrt_nonneg (n : ℝ)
            have _hreturnWidth : initialWidth ≤ returnWidth := by linarith
            constructor <;> nlinarith [x.property.1, x.property.2]⟩
          Set.univ := by
  have hliminf := ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTube
    ν hν hB hcontinuous hmeasurable hpathWidth
  have hstrict : lowerBound < atTop.liminf (fun n : ℕ =>
      independentIncrementLaw ν
        {increment | InOpenHorizontalTube (1 / 2)
          (pathWidth * Real.sqrt n) n increment}) :=
    hlowerBound.trans_le hliminf
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ =>
      independentIncrementLaw ν
        {increment | InOpenHorizontalTube (1 / 2)
          (pathWidth * Real.sqrt n) n increment}) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_lt_of_lt_liminf hstrict hbounded,
      eventually_gt_atTop 0] with n hnLower hn
  intro x
  refine hnLower.le.trans ?_
  exact strictTubeProbability_le_returnKernel_centeredIcc_from_normalized
    ν hn (Real.sqrt_pos.2 (by exact_mod_cast hn)) (by linarith)
      x.property houter hreturn

end ProbabilityTheory.RandomWalk.Mogulskii
