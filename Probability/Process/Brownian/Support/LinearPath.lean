/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Support.LinearTube
public import Probability.Process.Brownian.PathLaw.ContinuousModification
public import Probability.Process.Path.Scaling.FiniteHorizon
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Linear paths in the support of Brownian continuous-path laws

The public definition and theorem in this file are:

- `ProbabilityTheory.brownianLinearPath`: the path $t\mapsto at$ on $[0,1]$.
- `ProbabilityTheory.IsBrownianReal.brownianLinearPath_mem_support`:
  every such path belongs to the support of the Brownian law on
  $C([0,1],\mathbb R)$.

The proof uses the positive-probability Brownian linear-tube estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A deterministic linear continuous path on the unit interval. -/
def brownianLinearPath (a : ℝ) : C(unitInterval, ℝ) :=
  ⟨fun t => a * (t : ℝ), by fun_prop⟩

/-- Brownian motion assigns positive mass to every neighborhood of a
linear path on the unit interval. -/
theorem IsBrownianReal.brownianLinearPath_mem_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) (a : ℝ) :
    brownianLinearPath a ∈
      (P.map (fun ω => restrictPathToUnitInterval
        (hB.continuousPathMap hmeasurable ω))).support := by
  let path : Ω → C(unitInterval, ℝ) := fun ω =>
    restrictPathToUnitInterval (hB.continuousPathMap hmeasurable ω)
  have hpath : Measurable path :=
    continuous_restrictPathToUnitInterval.measurable.comp
      (hB.measurable_continuousPathMap hmeasurable)
  apply (Measure.mem_support_iff_forall _).2
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let E := fullSegmentCorridorEvent
    (fun t ω => B t ω - a * (t : ℝ)) 0 1 (-r) r
  have hE : 0 < P E := hB.measure_linearTube_pos a r hr
  let T : Set Ω := {ω | B 0 ω = 0 ∧
    ∀ t, hB.continuousPathMap hmeasurable ω t = B t ω}
  have hT : ∀ᵐ ω ∂P, ω ∈ T := by
    filter_upwards [hB.eval_zero_ae_eq_zero,
      hB.continuousPathMap_ae_eq hmeasurable] with ω hz hmodify
    exact ⟨hz, hmodify⟩
  have hsubset : T ∩ E ⊆ path ⁻¹'
      Metric.ball (brownianLinearPath a) r := by
    intro ω hω
    obtain ⟨⟨hzero, hmodify⟩, ⟨margin, hmargin, hbound⟩⟩ := hω
    change dist (path ω) (brownianLinearPath a) < r
    rw [ContinuousMap.dist_lt_iff_of_nonempty]
    intro t
    have ht := hbound t
    simp only [segmentIncrement, zero_add, one_mul, hzero] at ht
    simp only [path, restrictPathToUnitInterval, brownianLinearPath,
      hmodify]
    rw [Real.dist_eq, abs_lt]
    have hcoe : ((UnitInterval.toNNReal t : ℝ≥0) : ℝ) = (t : ℝ) := rfl
    have ht' : -r + margin ≤ B (UnitInterval.toNNReal t) ω - a * (t : ℝ) ∧
        B (UnitInterval.toNNReal t) ω - a * (t : ℝ) ≤ r - margin := by
      simpa [hcoe] using ht
    constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith [ht'.1, ht'.2]
  have hballPos : 0 < P.map path (Metric.ball (brownianLinearPath a) r) := by
    rw [Measure.map_apply hpath Metric.isOpen_ball.measurableSet]
    calc
      0 < P E := hE
      _ = P (T ∩ E) := (Measure.measure_inter_eq_of_ae hT).symm
      _ ≤ P (path ⁻¹' Metric.ball (brownianLinearPath a) r) :=
        measure_mono hsubset
  exact hballPos.trans_le (measure_mono hball)

end ProbabilityTheory

end
