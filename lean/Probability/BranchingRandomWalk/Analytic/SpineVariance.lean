/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.PointMeasure
public import Probability.BranchingProcess.Offspring.Count
public import Probability.Distributions.Moments.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic

/-!
# Non-degeneracy of the one-step spine law

Boundary normalization makes the exponentially tilted point-process law a
probability measure. If its second moment vanished, it would be concentrated
at zero. The cancellation identity for the tilted law would then identify the
expected offspring count with the boundary weight, contradicting
supercriticality.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.PointProcess
open Combinatorics.Branching

/-- A nonnegative integrable second moment that is positive as an extended
integral is positive as a real Bochner integral. The integrability premise is
explicit because a Bochner integral is defined to be zero for a
nonintegrable function. -/
theorem positive_realSecondMoment_of_positive_lintegral
    {ν : Measure ℝ} {variance : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hpositive : 0 < ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂ν) :
    0 < variance := by
  have hreal : 0 < ENNReal.ofReal (∫ x, x ^ 2 ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hsquare
      (ae_of_all ν fun x => sq_nonneg x)]
    exact hpositive
  have hreal' : 0 < ∫ x, x ^ 2 ∂ν := ENNReal.ofReal_pos.mp hreal
  exact hcentered.2 ▸ hreal'

/-- A tilted law with zero second moment is concentrated at zero. -/
theorem ae_eq_zero_of_lintegral_sq_eq_zero
    {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂ν = 0) :
    ∀ᵐ x ∂ν, x = 0 := by
  have hfun : (fun x : ℝ => ENNReal.ofReal (x ^ 2)) =ᵐ[ν] 0 :=
    (lintegral_eq_zero_iff' (by fun_prop)).mp hν
  filter_upwards [hfun] with x hx
  have hx2 : x ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  nlinarith [sq_nonneg x]

/-- If a point-process law has boundary normalization and its tilted law has
zero second moment, then the expected total point mass is exactly one. -/
theorem expectedPointMass_eq_one_of_zero_tiltedSecondMoment
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalized : PointProcess.HasNormalization potential (-1) law)
    (hsecond : ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂
      PointProcess.tiltedLaw potential (-1) law = 0) :
    ∫⁻ ν, ν Set.univ ∂law = 1 := by
  let Q := PointProcess.tiltedLaw potential (-1) law
  have hQae : ∀ᵐ y ∂Q, y = 0 := by
    exact ae_eq_zero_of_lintegral_sq_eq_zero (by simpa [Q] using hsecond)
  have hQprob : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalized
  have hexp : ∫⁻ y, ENNReal.ofReal (Real.exp y) ∂Q = 1 := by
    calc
      (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂Q) =
          ∫⁻ y, (1 : ℝ≥0∞) ∂Q := by
            apply lintegral_congr_ae
            filter_upwards [hQae] with y hy
            simp [hy]
      _ = 1 := by rw [lintegral_one, hQprob.measure_univ]
  have hcancel := PointProcess.lintegral_tiltedLaw_cancel
    hpotential (-1) law (f := fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const
  have hmass :
      (∫⁻ ν, ∫⁻ x, (1 : ℝ≥0∞) ∂ν ∂law) = 1 := by
    calc
      (∫⁻ ν, ∫⁻ x, (1 : ℝ≥0∞) ∂ν ∂law) =
          ∫⁻ y, ENNReal.ofReal (Real.exp y) ∂Q := by
            simpa [Q] using hcancel.symm
      _ = 1 := hexp
  have hmassEq :
      (∫⁻ ν, ∫⁻ x, (1 : ℝ≥0∞) ∂ν ∂law) =
        ∫⁻ ν, ν Set.univ ∂law := by
    apply lintegral_congr
    intro ν
    exact lintegral_one
  rw [← hmassEq]
  exact hmass

/-- For a real-mark offspring law, zero second moment of the one-step spine
law forces the expected offspring count to equal the boundary weight. -/
theorem expectedChildCount_eq_one_of_zero_spineSecondMoment
    {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι ℝ)
    (hnormalized : HasBoundaryNormalization realPotential
      (μ : Measure (Step ι ℝ)))
    (hsecond : ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂
      tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ)) = 0) :
    μ.expectedChildCount = 1 := by
  have hpointNormalized := pointMeasure_hasNormalization realPotential
    (μ : Measure (Step ι ℝ)) hnormalized
  have hpointNormalized' : PointProcess.HasNormalization realPotential (-1)
      (μ.pointMeasureLaw : Measure (Measure ℝ)) := by
    rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.pointMeasureLaw_toMeasure]
    exact hpointNormalized
  have hlaw := pointMeasure_tiltedLaw_eq_tiltedPotentialLaw realPotential (-1)
    (μ : Measure (Step ι ℝ))
  have hlaw' :
      PointProcess.tiltedLaw realPotential (-1)
          (μ.pointMeasureLaw : Measure (Measure ℝ)) =
        tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ)) := by
    rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.pointMeasureLaw_toMeasure]
    exact hlaw
  have hsecondPoint :
      ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂
        PointProcess.tiltedLaw realPotential (-1)
          (μ.pointMeasureLaw : Measure (Measure ℝ)) = 0 := by
    rw [hlaw']
    exact hsecond
  have hmass := expectedPointMass_eq_one_of_zero_tiltedSecondMoment
    realPotential.measurable_toFun
    (μ.pointMeasureLaw : Measure (Measure ℝ)) hpointNormalized' hsecondPoint
  rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.expectedChildCount_eq_lintegral_pointMeasureLaw_totalMass]
  exact hmass

/-- Boundary normalization and supercriticality rule out a degenerate spine
increment law. This is the extended second-moment positivity needed before
choosing its finite variance parameter. -/
theorem spine_lintegral_secondMoment_pos_of_normalized_supercritical
    {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι ℝ)
    (hnormalized : HasBoundaryNormalization realPotential
      (μ : Measure (Step ι ℝ)))
    (hsupercritical : μ.IsSupercritical) :
    0 < ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂
      tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ)) := by
  by_contra hnot
  have hzero :
      ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂
        tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ)) = 0 :=
    le_antisymm (le_of_not_gt hnot) zero_le
  have hcount := expectedChildCount_eq_one_of_zero_spineSecondMoment
    μ hnormalized hzero
  change 1 < μ.expectedChildCount at hsupercritical
  rw [hcount] at hsupercritical
  exact (lt_irrefl 1 hsupercritical)

/-- Under the usual finite-second-moment premise, the spine's real second
moment is strictly positive. This packages the extended-moment
non-degeneracy with the integrability needed to identify it with the Bochner
integral in `IsCenteredSecondMoment`. -/
theorem spine_secondMoment_pos_of_normalized_supercritical
    {ι : Type*} [Countable ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι ℝ)
    (hnormalized : HasBoundaryNormalization realPotential
      (μ : Measure (Step ι ℝ)))
    (hsupercritical : μ.IsSupercritical)
    {variance : ℝ}
    (hspineMoment : ProbabilityTheory.IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ))) variance)
    (hsquare : Integrable
      (fun y : ℝ => y ^ 2)
      (tiltedPotentialLaw realPotential (-1) (μ : Measure (Step ι ℝ)))) :
    0 < variance :=
  positive_realSecondMoment_of_positive_lintegral hspineMoment hsquare
    (spine_lintegral_secondMoment_pos_of_normalized_supercritical
      μ hnormalized hsupercritical)

end ProbabilityTheory.BranchingRandomWalk.Analytic

end
