/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Bessel.ThreeDimensional
import Probability.Process.Brownian.Support.LinearTube
public import Topology.Cadlag.Skorokhod.Path.Linear
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Linear paths in the support of a three-dimensional Bessel law

The public theorem in this file is:

- `BrownianBessel3.linearPath_mem_support`: for a Brownian process and
  every $a\ge0$, the path $t\mapsto at$ belongs to the support of the
  law of the radius of three independent copies.

This is a reusable support theorem for the radial path of three independent
Brownian motions. It supplies the path-space support input for Bessel-based
Brownian-meander arguments in this library.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace BrownianBessel3

private lemma radial_path_close
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    (hB : ∀ ω, Continuous (B · ω))
    {a δ r : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (hsmall : 5 * δ * (1 + |a|) < r)
    {ω : Triple Ω}
    (h₁ : dist (cadlagunitIntervalPath B hB ω.1)
      (Skorokhod.linearPath a) < δ)
    (h₂ : dist (cadlagunitIntervalPath B hB ω.2.1)
      (Skorokhod.linearPath 0) < δ)
    (h₃ : dist (cadlagunitIntervalPath B hB ω.2.2)
      (Skorokhod.linearPath 0) < δ) :
    dist (path B hB ω) (Skorokhod.linearPath a) < r := by
  have he₁ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₁
  have he₂ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₂
  have he₃ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₃
  have hpoint (t : unitInterval) :
      |path B hB ω t - a * (t : ℝ)| ≤ 5 * δ * (1 + |a|) := by
    have h₁t := he₁ t
    have h₂t := he₂ t
    have h₃t := he₃ t
    simp only [cadlagunitIntervalPath_apply, zero_mul, sub_zero,
      add_zero, abs_zero] at h₁t h₂t h₃t
    have hat : 0 ≤ a * (t : ℝ) :=
      mul_nonneg ha t.property.1
    have hrad := abs_radius_sub_abs_le
      (B (UnitInterval.toNNReal t) ω.1)
      (B (UnitInterval.toNNReal t) ω.2.1)
      (B (UnitInterval.toNNReal t) ω.2.2) (a * (t : ℝ))
    simp only [path, cadlagunitIntervalPath_apply, radius,
      abs_of_nonneg hat] at hrad ⊢
    have hδle : δ ≤ δ * (1 + |a|) := by
      nlinarith [abs_nonneg a]
    linarith
  have huniform : Skorokhod.uniformEDist (path B hB ω)
      (Skorokhod.linearPath a) ≤ ENNReal.ofReal (5 * δ * (1 + |a|)) := by
    rw [Skorokhod.uniformEDist_eq_edist, UniformFun.edist_def]
    refine iSup_le fun t => ?_
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (hpoint t)
  have hj1 := (Skorokhod.j1EDist_le_uniformEDist
    (path B hB ω) (Skorokhod.linearPath a)).trans huniform
  rw [← Skorokhod.edist_cadlagPath_eq_j1EDist, edist_dist] at hj1
  have hdist : dist (path B hB ω) (Skorokhod.linearPath a) ≤
      5 * δ * (1 + |a|) := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hj1
  exact hdist.trans_lt hsmall

/-- Every nonnegative linear path lies in the support of the radial law
formed from three independent copies of a Brownian process. -/
theorem linearPath_mem_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hBrownian : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 ≤ a) :
    Skorokhod.linearPath a ∈
      (pathLaw P B hcontinuous).support := by
  apply (Measure.mem_support_iff_forall _).2
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let δ : ℝ := r / (10 * (1 + |a|))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsmall : 5 * δ * (1 + |a|) < r := by
    dsimp [δ]
    have hden : 0 < 1 + |a| := by positivity
    field_simp
    linarith
  let E₁ : Set Ω := (cadlagunitIntervalPath B hcontinuous) ⁻¹'
    Metric.ball (Skorokhod.linearPath a) δ
  let E₀ : Set Ω := (cadlagunitIntervalPath B hcontinuous) ⁻¹'
    Metric.ball (Skorokhod.linearPath 0) δ
  have hpos₁ : 0 < P E₁ := by
    have h := hBrownian.measure_cadlagunitIntervalPathLaw_linearBall_pos
      hcontinuous hmeasurable a δ hδ
    simpa [cadlagunitIntervalPathLaw, E₁,
      Measure.map_apply (measurable_cadlagunitIntervalPath
        B hcontinuous hmeasurable) Metric.isOpen_ball.measurableSet] using h
  have hpos₀ : 0 < P E₀ := by
    have h := hBrownian.measure_cadlagunitIntervalPathLaw_linearBall_pos
      hcontinuous hmeasurable 0 δ hδ
    simpa [cadlagunitIntervalPathLaw, E₀,
      Measure.map_apply (measurable_cadlagunitIntervalPath
        B hcontinuous hmeasurable) Metric.isOpen_ball.measurableSet] using h
  have hprod : 0 < productLaw P (E₁ ×ˢ (E₀ ×ˢ E₀)) := by
    change 0 < (P.prod (P.prod P)) (E₁ ×ˢ (E₀ ×ˢ E₀))
    rw [Measure.prod_prod, Measure.prod_prod]
    exact ENNReal.mul_pos hpos₁.ne' (ENNReal.mul_pos hpos₀.ne' hpos₀.ne').ne'
  have hsubset : E₁ ×ˢ (E₀ ×ˢ E₀) ⊆
      (path B hcontinuous) ⁻¹' Metric.ball (Skorokhod.linearPath a) r := by
    intro ω hω
    exact radial_path_close hcontinuous ha hδ hsmall
      hω.1 hω.2.1 hω.2.2
  have hballPos : 0 < pathLaw P B hcontinuous
      (Metric.ball (Skorokhod.linearPath a) r) := by
    rw [pathLaw, Measure.map_apply (measurable_path hcontinuous hmeasurable)
      Metric.isOpen_ball.measurableSet]
    exact hprod.trans_le (measure_mono hsubset)
  exact hballPos.trans_le (measure_mono hball)

end BrownianBessel3

end
