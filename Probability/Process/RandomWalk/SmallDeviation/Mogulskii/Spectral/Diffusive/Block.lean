/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Diffusive.Return

/-!
# Uniform return estimates at a Mogulskii block scale

The diffusive return estimate is sampled at the integer block length
`⌊c * scale n ^ 2⌋`.  Its square-root normalization converges to `sqrt c`,
which transfers a common centered increment event to fixed normalized outer,
return, and initial intervals.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open Combinatorics.Branching.Walk

/-- A constant strictly below the spectral lower bound for an inner Brownian
corridor gives a uniform return-row lower bound at every sufficiently large
Mogulskii block.  The inner corridor width and spectral fraction remain
explicit so they can be sent to the outer tube width and one, respectively.
Strict geometric margins absorb integer rounding in the block length. -/
theorem eventually_uniform_centeredReturnKernel_diffusiveBlockLength
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {rho innerWidth : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hinnerWidth : 0 < innerWidth)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {pathWidth initialWidth outerWidth returnWidth : ℝ}
    (hpathWidth : innerWidth < pathWidth)
    (houter : initialWidth + pathWidth * Real.sqrt constant < outerWidth)
    (hreturn : initialWidth + pathWidth * Real.sqrt constant < returnWidth)
    {lowerBound : ENNReal}
    (hlowerBound : lowerBound <
      ENNReal.ofReal (Real.exp
        (-(Real.pi ^ 2) / (2 * rho ^ 2 * innerWidth ^ 2)))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : Set.Icc (-(initialWidth / 2)) (initialWidth / 2),
        lowerBound ≤ returnKernel ν
          (Set.Icc (-(outerWidth * scale n / 2))
            (outerWidth * scale n / 2)) measurableSet_Icc
          (Set.Icc (-(returnWidth * scale n / 2))
            (returnWidth * scale n / 2)) measurableSet_Icc
          (diffusiveBlockLength constant scale n)
          ⟨scale n * x, by
            have hreturnWidth : initialWidth < returnWidth := by
              nlinarith [Real.sqrt_nonneg constant]
            constructor <;> nlinarith [x.property.1, x.property.2,
              hscalePos n]⟩ Set.univ := by
  let length := diffusiveBlockLength constant scale
  let ratio : ℕ → ℝ := fun n => Real.sqrt (length n) / scale n
  let probability : ℕ → ENNReal := fun m =>
    independentIncrementLaw ν {increment |
      InOpenHorizontalTube (1 / 2) (pathWidth * Real.sqrt m) m increment}
  have hliminf : ENNReal.ofReal (Real.exp
      (-(Real.pi ^ 2) / (2 * rho ^ 2 * innerWidth ^ 2))) ≤
      atTop.liminf probability := by
    simpa [probability] using
      ofReal_exp_neg_pi_sq_div_two_rho_sq_innerWidth_sq_le_liminf_centeredStrictTube
        ν hν hrho hrho_one hinnerWidth hpathWidth hB hcontinuous hmeasurable
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop probability :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  have hprobability : ∀ᶠ m in atTop, lowerBound < probability m :=
    eventually_lt_of_lt_liminf (hlowerBound.trans_le hliminf) hbounded
  have hlengthTop : Tendsto length atTop atTop := by
    simpa [length] using hscale.tendsto_diffusiveBlockLength_atTop hconstant
  have hprobabilityBlock : ∀ᶠ n in atTop,
      lowerBound < probability (length n) :=
    hlengthTop.eventually hprobability
  have hratio : Tendsto ratio atTop (nhds (Real.sqrt constant)) := by
    simpa [ratio, length] using
      hscale.tendsto_sqrt_diffusiveBlockLength_div hconstant
  have hnormalizedWidth : Tendsto
      (fun n => initialWidth + pathWidth * ratio n) atTop
      (nhds (initialWidth + pathWidth * Real.sqrt constant)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hratio)
  have houterEventually : ∀ᶠ n in atTop,
      initialWidth + pathWidth * ratio n ≤ outerWidth :=
    (hnormalizedWidth.eventually (eventually_lt_nhds houter)).mono
      fun _ h => h.le
  have hreturnEventually : ∀ᶠ n in atTop,
      initialWidth + pathWidth * ratio n ≤ returnWidth :=
    (hnormalizedWidth.eventually (eventually_lt_nhds hreturn)).mono
      fun _ h => h.le
  filter_upwards [hprobabilityBlock, houterEventually, hreturnEventually,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
    with n hnProbability hnOuter hnReturn hnLength
  intro x
  refine hnProbability.le.trans ?_
  have houterScaled : initialWidth * scale n +
      pathWidth * Real.sqrt (length n) ≤ outerWidth * scale n := by
    calc
      initialWidth * scale n + pathWidth * Real.sqrt (length n) =
          (initialWidth + pathWidth * ratio n) * scale n := by
        dsimp [ratio]
        field_simp [(hscalePos n).ne']
      _ ≤ outerWidth * scale n :=
        mul_le_mul_of_nonneg_right hnOuter (hscalePos n).le
  have hreturnScaled : initialWidth * scale n +
      pathWidth * Real.sqrt (length n) ≤ returnWidth * scale n := by
    calc
      initialWidth * scale n + pathWidth * Real.sqrt (length n) =
          (initialWidth + pathWidth * ratio n) * scale n := by
        dsimp [ratio]
        field_simp [(hscalePos n).ne']
      _ ≤ returnWidth * scale n :=
        mul_le_mul_of_nonneg_right hnReturn (hscalePos n).le
  simpa only [probability, length, mul_assoc] using
    strictTubeProbability_le_returnKernel_centeredIcc_from
      ν hnLength
      (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      (initial := scale n * (x : ℝ))
      (pathWidth := pathWidth * Real.sqrt (length n))
      (initialWidth := initialWidth * scale n)
      (outerWidth := outerWidth * scale n)
      (returnWidth := returnWidth * scale n)
      (by constructor <;> nlinarith [x.property.1, x.property.2,
        hscalePos n]) houterScaled hreturnScaled

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
