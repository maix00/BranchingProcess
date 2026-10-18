/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Probability.Distributions.Stable.Gaussian.Basic
public import Probability.Process.Stable.Levy

/-!
# Brownian motion as a stable Lévy process

The public theorems in this file are:

- `IsPreBrownianReal.hasStableClockIncrements`: Brownian increments satisfy
  $B_t-B_s\sim N(0,t-s)$, hence the exponent-two stable clock law.
- `IsBrownianReal.isStableLevyProcess`: an almost-surely continuous process
  with $B_t-B_s\sim N(0,t-s)$ is a Gaussian stable Lévy process.
- `IsStableLevyProcess.isPreBrownianReal_of_standardGaussian`: a càdlàg
  exponent-two stable Lévy process with $B_t-B_s\sim N(0,t-s)$ has Brownian
  finite-dimensional laws and independent increments.

The converse identifies the Gaussian process used in the proof of corridor
positivity in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Brownian motion has the stable independent-increment specification with
index `2`, standard Gaussian reference law, and the usual real clock. -/
theorem IsPreBrownianReal.hasStableClockIncrements
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) :
    HasStableClockIncrements 2 (gaussianReal 0 (1 : ℝ≥0))
      (fun t : ℝ≥0 => (t : ℝ)) B P := by
  refine ⟨isStrictlyAlphaStable_gaussianReal_zero (by norm_num),
    (fun _ _ h => NNReal.coe_le_coe.mpr h), by simp,
    hB.eval_zero_ae_eq_zero, hB.hasIndepIncrements, ?_⟩
  intro s t hst
  let d : ℝ := (t : ℝ) - (s : ℝ)
  let c : ℝ := d ^ (1 / (2 : ℝ))
  have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
  have hdist : nndist (t : ℝ) (s : ℝ) = (t - s : ℝ≥0) := by
    apply NNReal.eq
    rw [Real.nndist_eq, Real.coe_nnabs, abs_of_nonneg hd, NNReal.coe_sub hst]
  have hc2 : c ^ 2 = d := by
    dsimp [c]
    convert Real.rpow_inv_natCast_pow hd (by norm_num : (2 : ℕ) ≠ 0) using 1
    norm_num
  have hscale :
      (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
        gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
    rw [hc2, mul_one, hdist, NNReal.coe_sub hst]
  have hLaw : HasLaw (fun ω => B t ω - B s ω)
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) P := hB.hasLaw_sub t s
  change HasLaw (fun ω => B t ω - B s ω)
    ((gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x)) P
  rw [hscale]
  exact hLaw

/-- Mathlib's almost-surely continuous Brownian motion is an exponent-two
stable Lévy process in the càdlàg sense. -/
theorem IsBrownianReal.isStableLevyProcess
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B P := by
  refine ⟨hB.toIsPreBrownianReal.hasStableClockIncrements, ?_⟩
  filter_upwards [hB.cont] with ω hω
  exact hω.isCadlag

/-- A standard Gaussian exponent-two stable Lévy process has Brownian
finite-dimensional distributions and independent increments. -/
theorem IsStableLevyProcess.isPreBrownianReal_of_standardGaussian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ}
    (hB : IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B P) :
    IsPreBrownianReal B P := by
  let hInc := hB.increments
  have hLaw : ∀ t, HasLaw (B t) (gaussianReal 0 t) P := by
    intro t
    let c : ℝ := (t : ℝ) ^ (1 / (2 : ℝ))
    have hc2 : c ^ 2 = (t : ℝ) := by
      dsimp [c]
      convert Real.rpow_inv_natCast_pow (NNReal.coe_nonneg t)
        (by norm_num : (2 : ℕ) ≠ 0) using 1 <;> norm_num
    have hscale :
        (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
          gaussianReal 0 t := by
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
      simpa using hc2
    have hdiff : HasLaw (fun ω => B t ω - B 0 ω)
        ((gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x)) P := by
      simpa [c] using hInc.increment_hasLaw (0 : ℝ≥0) t (by simp)
    have hzero : B 0 =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hInc.ae_start_eq_zero] with ω hω
      exact hω
    have hfun : (fun ω => B t ω - B 0 ω) =ᵐ[P] fun ω => B t ω := by
      filter_upwards [hzero] with ω hω
      simp [hω]
    rw [hscale] at hdiff
    exact hdiff.congr hfun.symm
  exact HasIndepIncrements.isPreBrownianReal_of_hasLaw hLaw hInc.indepIncrements

end ProbabilityTheory
