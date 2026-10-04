/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Centered

/-!
# Centered lattice discretization of a spatial scale

This file rounds a positive real spatial scale to a centered lattice interval.
The added unit keeps the radius positive at every index; it is negligible on
every scale tending to infinity.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A positive integer radius obtained by rounding half of a real spatial
scale down and adding one. -/
noncomputable def centeredLatticeRadius (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊scale n / 2⌋₊ + 1

@[simp] theorem centeredLatticeRadius_pos (scale : ℕ → ℝ) (n : ℕ) :
    0 < centeredLatticeRadius scale n := by
  simp [centeredLatticeRadius]

private theorem tendsto_half_scale_atTop {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => scale n / 2) atTop atTop := by
  simpa [div_eq_mul_inv, mul_comm] using
    hscale.const_mul_atTop (by norm_num : (0 : ℝ) < 2⁻¹)

/-- The actual centered lattice width is asymptotic to the requested real
scale. -/
theorem tendsto_centeredLatticeWidth_div
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n =>
      (((2 * centeredLatticeRadius scale n : ℕ) : ℝ) / scale n))
      atTop (nhds 1) := by
  have hhalf := tendsto_half_scale_atTop hscale
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hhalf
  have hinv := tendsto_inv_atTop_zero.comp hscale
  have herror : Tendsto (fun n => 2 / scale n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (2 : ℝ) * (scale n)⁻¹) atTop (nhds (2 * 0)))
  have hsum := hfloor.add herror
  convert hsum using 1
  · funext n
    simp only [centeredLatticeRadius, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring
  · norm_num

/-- The effective Dirichlet width, with its two killing sites, is also
asymptotic to the requested real scale. -/
theorem tendsto_centeredDirichletWidth_div
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n =>
      (((2 * (centeredLatticeRadius scale n + 1) : ℕ) : ℝ) / scale n))
      atTop (nhds 1) := by
  have hmain := tendsto_centeredLatticeWidth_div hscale
  have hinv := tendsto_inv_atTop_zero.comp hscale
  have herror : Tendsto (fun n => 2 / scale n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (2 : ℝ) * (scale n)⁻¹) atTop (nhds (2 * 0)))
  have hsum := hmain.add herror
  convert hsum using 1
  · funext n
    push_cast
    ring
  · norm_num

/-- The rounded radius tends to infinity with the real scale. -/
theorem tendsto_centeredLatticeRadius_atTop
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => (centeredLatticeRadius scale n : ℝ))
      atTop atTop := by
  have hfloor : Tendsto (fun n => ⌊scale n / 2⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_half_scale_atTop hscale)
  have hcast : Tendsto (fun n => (⌊scale n / 2⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloor
  simpa [centeredLatticeRadius] using
    tendsto_atTop_add_const_right atTop 1 hcast

/-- The centered Rademacher tube at the canonical rounded lattice width has
the sharp Gaussian small-deviation rate for every real scale tending to
infinity and negligible relative to elapsed diffusive time. -/
theorem tendsto_scaledLog_centeredHorizontalTubeProbability_of_scale
    (scale : ℕ → ℝ) (time : ℕ → ℕ)
    (hscaleTop : Tendsto scale atTop atTop)
    (htime : ∀ n, 0 < time n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      scale n ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw rademacherMeasure) (1 / 2)
          (2 * centeredLatticeRadius scale n) (time n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let radius := centeredLatticeRadius scale
  have hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop :=
    tendsto_centeredLatticeRadius_atTop hscaleTop
  have hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop := by
    have hadd := tendsto_atTop_add_const_right atTop 1 hradiusTop
    simpa [radius] using hadd.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hwidthRatio := tendsto_centeredDirichletWidth_div hscaleTop
  have hratioProduct := (hwidthRatio.pow 2).mul hsmall
  have hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0) := by
    have heq : ∀ᶠ n in atTop,
        (((2 * (centeredLatticeRadius scale n + 1) : ℕ) : ℝ) /
              scale n) ^ 2 * (scale n ^ 2 / (time n : ℝ)) =
          ((2 * (centeredLatticeRadius scale n + 1) : ℕ) : ℝ) ^ 2 /
            (time n : ℝ) := by
      filter_upwards [hscaleTop.eventually (eventually_gt_atTop 0)]
          with n hn
      field_simp [hn.ne']
    have h := hratioProduct.congr' heq
    simpa [radius] using h
  have hactualRatio := tendsto_centeredLatticeWidth_div hscaleTop
  have hasymptotic : Tendsto (fun n =>
      scale n / ((2 * radius n : ℕ) : ℝ)) atTop (nhds 1) := by
    have hinv := hactualRatio.inv₀ one_ne_zero
    simpa [one_div, inv_div, radius] using hinv
  exact tendsto_scaledLog_centeredHorizontalTubeProbability_of_asymptoticWidth
    radius time scale (fun n => centeredLatticeRadius_pos scale n) htime
    hradiusTop hwidth hratio hasymptotic


/-- Canonical centered-lattice spectral asymptotics along a Mogulskii scale.
The successor reindexing removes the irrelevant zero-time index while keeping
the statement entirely under the standard `IsMogulskiiScale` hypothesis. -/
theorem IsMogulskiiScale.tendsto_scaledLog_centeredHorizontalTubeProbability_succ
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    Tendsto (fun n =>
      scale (n + 1) ^ 2 / ((n + 1 : ℕ) : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw rademacherMeasure) (1 / 2)
          (2 * centeredLatticeRadius (fun k => scale (k + 1)) n)
          (n + 1)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let shift : ℕ → ℕ := fun n => n + 1
  have hshift : Tendsto shift atTop atTop := tendsto_add_atTop_nat 1
  exact tendsto_scaledLog_centeredHorizontalTubeProbability_of_scale
    (fun n => scale (shift n)) shift
    ((Asymptotics.IsSmallDeviationScale.tendsto_atTop
      hscale).comp hshift)
    (fun n => by dsimp [shift]; omega)
    (hscale.tendsto_sq_div_natCast_zero.comp hshift)


/-- Sharp centered Rademacher small-deviation asymptotics at the original
integer time index.  The value at time zero is irrelevant to convergence and
is removed internally by the successor equivalence for `atTop`. -/
theorem IsMogulskiiScale.tendsto_scaledLog_centeredHorizontalTubeProbability
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    Tendsto (fun n =>
      scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw rademacherMeasure) (1 / 2)
          (2 * centeredLatticeRadius scale n) n).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert IsMogulskiiScale.tendsto_scaledLog_centeredHorizontalTubeProbability_succ
      hscale using 1
  funext n
  simp only [centeredLatticeRadius]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
