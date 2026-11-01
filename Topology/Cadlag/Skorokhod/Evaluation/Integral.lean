/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Topology.Cadlag.Measurability
public import Topology.Cadlag.Skorokhod.Evaluation.Basic

/-!
# Integral functionals on Skorokhod path space

Integrating a bounded continuous transform of a càdlàg path along an injective
continuous time parametrization gives a continuous functional for the `J₁`
topology. The proof uses pointwise convergence at the continuity times of the
limit path and dominated convergence.

## Public declarations

- `integralAlongTimeChange φ ψ path` is
  `∫ u ∈ [0,1], φ (path (ψ u)) du`.
- `continuousAt_integralAlongTimeChange`: this integral functional is
  continuous at `path` when `φ` is continuous and bounded and `ψ` is
  continuous and injective on `[0,1]`.

The functional is
\(F(f)=\int_0^1\varphi(f(\psi(u)))\,du\).
Under the stated bounded-continuity and injectivity assumptions on
\(\varphi\) and \(\psi\), \(F\) is continuous at every càdlàg path.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Skorokhod

/-- Integrate a continuous state transform of a path along a time
parametrization, using Lebesgue measure on the unit interval. -/
noncomputable def integralAlongTimeChange
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φ : E → ℝ) (ψ : ℝ → unitInterval) (path : CadlagPath unitInterval E) : ℝ :=
  ∫ u, φ (path (ψ u)) ∂(volume.restrict (Icc 0 1))

theorem continuousAt_integralAlongTimeChange
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φ : E → ℝ) (hφ : Continuous φ) (bound : ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ bound)
    (ψ : ℝ → unitInterval) (hψ : Continuous ψ)
    (hψ_inj : Set.InjOn ψ (Icc 0 1))
    (path : CadlagPath unitInterval E) :
    ContinuousAt (integralAlongTimeChange φ ψ) path := by
  let bad : Set unitInterval := {s | ¬ ContinuousAt path s}
  have hbad : bad.Countable := by
    simpa [bad] using path.isCadlag_toFun.countable_discontinuitySet
  let badParam : Set ℝ := Icc 0 1 ∩ ψ ⁻¹' bad
  have hbadParam : badParam.Countable := by
    apply Set.MapsTo.countable_of_injOn (f := ψ) (s := badParam) (t := bad)
    · intro u hu
      exact hu.2
    · intro u hu v hv huv
      exact hψ_inj hu.1 hv.1 huv
    · exact hbad
  have hgood : ∀ᵐ u ∂(volume.restrict (Icc 0 1)), ContinuousAt path (ψ u) := by
    filter_upwards [hbadParam.ae_notMem (volume.restrict (Icc 0 1)),
      ae_restrict_mem measurableSet_Icc] with u hu hmem
    change u ∉ badParam at hu
    by_contra hnot
    exact hu ⟨hmem, hnot⟩
  have hmeas (g : CadlagPath unitInterval E) :
      AEStronglyMeasurable (fun u : ℝ => φ (g (ψ u)))
        (volume.restrict (Icc 0 1)) := by
    apply (hφ.measurable.comp ((g.isCadlag_toFun.measurable).comp hψ.measurable))
      |>.aestronglyMeasurable
  have hbound_integrable :
      Integrable (fun _ : ℝ => bound) (volume.restrict (Icc 0 1)) :=
    integrable_const bound
  have hlim : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
      Tendsto (fun g : CadlagPath unitInterval E => φ (g (ψ u))) (𝓝 path)
        (𝓝 (φ (path (ψ u)))) := by
    filter_upwards [hgood] with u hu
    exact hφ.continuousAt.tendsto.comp
      (continuousAt_apply_of_continuousAt path (ψ u) hu)
  have h_int := tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => bound)
    (hF_meas := Filter.Eventually.of_forall hmeas)
    (h_bound := Filter.Eventually.of_forall fun g =>
      Filter.Eventually.of_forall fun u => hbound (g (ψ u)))
    hbound_integrable hlim
  change Tendsto (fun g : CadlagPath unitInterval E =>
      ∫ u, φ (g (ψ u)) ∂(volume.restrict (Icc 0 1)))
    (𝓝 path) (𝓝 (∫ u, φ (path (ψ u)) ∂(volume.restrict (Icc 0 1))))
  simpa [integralAlongTimeChange] using h_int


end Skorokhod

end
