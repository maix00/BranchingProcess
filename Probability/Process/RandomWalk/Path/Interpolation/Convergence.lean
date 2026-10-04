/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.Path.Interpolation.MaximalJump
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Probability.ConvergenceInDistribution.AsymptoticEquivalence

/-!
# Distributional transfer between random-walk path realizations

At diffusive scale and under a finite second moment, convergence in
distribution of the polygonal interpolation implies the same convergence for
the right-continuous step realization in Skorokhod space.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A functional limit theorem for the polygonal interpolation in continuous
path space remains valid after viewing both the approximating paths and the
limit as càdlàg paths.  This is the continuous mapping theorem for the
canonical continuous inclusion into Skorokhod space. -/
theorem tendstoInDistribution_normalizedLinearCadlagPath_of_continuous
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (limit : Omega → C(unitInterval, ℝ))
    (hlinear : TendstoInDistribution
      (fun n => normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P) :
    TendstoInDistribution
      (fun n => normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop (Skorokhod.ofContinuousMap ∘ limit)
      (fun _ => independentIncrementLaw nu) P := by
  apply TendstoInDistribution.congr
    (h := hlinear.continuous_comp Skorokhod.continuous_ofContinuousMap)
  · intro n
    filter_upwards [] with increment
    rfl
  · filter_upwards [] with omega
    rfl

/-- Transfer a functional limit theorem from polygonal interpolation to the
canonical right-continuous step path. -/
theorem tendstoInDistribution_normalizedStepPath_of_linear
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    (limit : Omega → CadlagPath unitInterval ℝ)
    (hlinear : TendstoInDistribution
      (fun n => normalizedLinearCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P) :
    TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P := by
  let error : ℕ → (ℕ → ℝ) → ℝ := fun n increment =>
    (Real.sqrt n)⁻¹ * maxAbsUpTo n increment
  apply tendstoInDistribution_of_error_tendstoInMeasure
    (error := error) hlinear
  · intro n
    exact (measurable_const.mul (measurable_maxAbsUpTo n)).aemeasurable
  · intro n increment
    have hsqrt : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg n)
    have herror : 0 ≤ error n increment :=
      mul_nonneg hsqrt (maxAbsUpTo_nonneg n increment)
    apply (ENNReal.ofReal_le_ofReal_iff herror).mp
    rw [← edist_dist, Skorokhod.edist_cadlagPath_eq_j1EDist]
    simpa only [error, abs_inv, abs_of_nonneg (Real.sqrt_nonneg n)] using
      (j1EDist_normalizedStepPath_linear_le
        (fun n => Real.sqrt n) n increment)
  · intro epsilon hepsilon
    have h := (tendstoInMeasure_iff_measureReal_dist.mp
      (tendstoInMeasure_invSqrt_mul_maxAbsUpTo_zero nu hsq))
      epsilon hepsilon
    apply h.congr'
    filter_upwards [] with n
    congr 1
    ext increment
    have hnonneg : 0 ≤ error n increment :=
      mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg n))
        (maxAbsUpTo_nonneg n increment)
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero]
    change epsilon ≤ |error n increment| ↔ epsilon ≤ error n increment
    rw [abs_of_nonneg hnonneg]
  · intro n
    exact (measurable_normalizedStepCadlagPathIcc
      (fun n => Real.sqrt n) n).aemeasurable

/-- Donsker transfer in the standard formulation: convergence of the
polygonal interpolation in continuous path space, together with a finite
second moment, implies convergence of the right-continuous random-walk path
in Skorokhod space. -/
theorem tendstoInDistribution_normalizedStepPath_of_continuousLinear
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsq : Integrable (fun x : ℝ => x ^ 2) nu)
    (limit : Omega → C(unitInterval, ℝ))
    (hlinear : TendstoInDistribution
      (fun n => normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n)
      atTop limit (fun _ => independentIncrementLaw nu) P) :
    TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc (fun n => Real.sqrt n) n)
      atTop (Skorokhod.ofContinuousMap ∘ limit)
      (fun _ => independentIncrementLaw nu) P :=
  tendstoInDistribution_normalizedStepPath_of_linear P nu hsq _
    (tendstoInDistribution_normalizedLinearCadlagPath_of_continuous
      P nu limit hlinear)

end ProbabilityTheory.RandomWalk
