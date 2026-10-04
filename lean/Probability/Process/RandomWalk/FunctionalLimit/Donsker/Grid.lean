/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Grid
public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Brownian
public import Probability.Process.RandomWalk.Path.Interpolation.MaximalJump
public import Probability.ConvergenceInDistribution.AsymptoticEquivalence

/-!
# Uniform-grid limits for polygonal random-walk paths

The equal-block endpoint limit is transferred to the values of polygonal
interpolation at the corresponding fixed uniform grid.  The deterministic
error is bounded by finitely many maximal jumps and hence vanishes in
probability under a finite second moment.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- For a positive number of blocks, a block of proportion `1 / blocks`
has exactly the quotient length `n / blocks`. -/
theorem proportionalBlockLength_one_div
    (blocks n : ℕ) :
    proportionalBlockLength (1 / (blocks : ℝ)) n = n / blocks := by
  unfold proportionalBlockLength
  rw [show (1 / (blocks : ℝ)) * n = (n : ℝ) / blocks by ring,
    Nat.floor_div_eq_div]

/-- Polygonal interpolation at a fixed uniform grid converges jointly to
Brownian motion on that grid. -/
theorem tendstoInDistribution_normalizedLinearPath_uniformGrid_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    TendstoInDistribution
      (fun n increment (j : Fin (blocks + 1)) =>
        normalizedLinearPath (fun n => Real.sqrt n) n increment
          ((j : ℝ) / blocks))
      atTop
      (fun ω => fun j : Fin (blocks + 1) =>
        B (uniformGridTime ⟨1 / blocks, by positivity⟩ j) ω)
      (fun _ => independentIncrementLaw nu) P := by
  let fraction : ℝ := 1 / blocks
  let endpoint : ℕ → (ℕ → ℝ) → Fin (blocks + 1) → ℝ :=
    fun n increment j =>
      AdditivePath.displacement (j * (n / blocks)) increment / Real.sqrt n
  let polygonal : ℕ → (ℕ → ℝ) → Fin (blocks + 1) → ℝ :=
    fun n increment j =>
      normalizedLinearPath (fun n => Real.sqrt n) n increment
        ((j : ℝ) / blocks)
  have hfraction : 0 < fraction := by
    dsimp only [fraction]
    positivity
  have hendpoint : TendstoInDistribution endpoint atTop
      (fun ω => fun j : Fin (blocks + 1) =>
        B (uniformGridTime ⟨1 / blocks, by positivity⟩ j) ω)
      (fun _ => independentIncrementLaw nu) P := by
    have h := tendstoInDistribution_proportionalBlockEndpoints_brownian
      nu hcentered hsecondMoment hB hfraction blocks
    apply h.congr_eventually
    · filter_upwards [] with n
      filter_upwards [] with increment
      funext j
      simp only [endpoint, fraction, proportionalBlockLength_one_div]
    · intro n
      exact (Measurable.of_eval fun j =>
        (displacement_measurable _).div_const _).aemeasurable
  have hsq : Integrable (fun x : ℝ => x ^ 2) nu :=
    .of_integral_ne_zero (by rw [hsecondMoment]; norm_num)
  let error : ℕ → (ℕ → ℝ) → ℝ := fun n increment =>
    (blocks + 1) * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment)
  apply tendstoInDistribution_of_error_tendstoInMeasure hendpoint
      (error := error)
  · intro n
    exact (measurable_const.mul
      (measurable_const.mul (measurable_maxAbsUpTo n))).aemeasurable
  · intro n increment
    have herr : 0 ≤ error n increment := by
      exact mul_nonneg (by positivity)
        (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
          (maxAbsUpTo_nonneg n increment))
    apply (dist_pi_le_iff herr).2
    intro j
    rw [Real.dist_eq]
    exact abs_normalizedLinearPath_uniformGrid_sub_endpoint_le
      hblocks j.is_le increment
  · intro epsilon hepsilon
    have hmax := tendstoInMeasure_invSqrt_mul_maxAbsUpTo_zero nu hsq
    rw [tendstoInMeasure_iff_measureReal_dist] at hmax
    have hthreshold := hmax (epsilon / (blocks + 1)) (by positivity)
    apply hthreshold.congr'
    filter_upwards [] with n
    congr 1
    ext increment
    have hnorm : 0 ≤ (Real.sqrt n)⁻¹ * maxAbsUpTo n increment :=
      mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
        (maxAbsUpTo_nonneg n increment)
    simp only [Set.mem_ofPred_eq, error, Real.dist_eq, sub_zero,
      abs_of_nonneg hnorm]
    rw [div_le_iff₀ (by positivity)]
    simp only [mul_comm]
  · intro n
    apply (Measurable.of_eval fun j => ?_).aemeasurable
    let t : unitInterval :=
      ⟨(j : ℝ) / blocks, by
        constructor
        · positivity
        · rw [div_le_one (by exact_mod_cast hblocks)]
          exact_mod_cast j.is_le⟩
    exact (ContinuousMap.measurable_eval t).comp
      (measurable_normalizedLinearContinuousPathIcc
        (fun n => Real.sqrt n) n)

end ProbabilityTheory.RandomWalk
