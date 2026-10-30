/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Bessel.ThreeDimensional
import all Probability.Process.Brownian.Bessel.Lemmas.Support
import Probability.Process.Brownian.Support.LinearTube
public import Topology.Cadlag.Skorokhod.Path.Linear
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Linear paths in the support of a three-dimensional Bessel law

## Public declarations

- `ProbabilityTheory.BrownianBessel3.linearPath_mem_support`: for three
  independent Brownian coordinates and every $a\ge0$, the path $t\mapsto at$
  belongs to the support of the radial path law, where
  $R_t=\sqrt{(B_t^{(1)})^2+(B_t^{(2)})^2+(B_t^{(3)})^2}$.

This is a reusable support theorem for the radial path of three independent
Brownian motions. It supplies the path-space support input for Bessel-based
Brownian-meander arguments in this library.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.BrownianBessel3

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

end ProbabilityTheory.BrownianBessel3

end
