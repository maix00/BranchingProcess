/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Invariance under pointwise limits

The public theorems in this file are:

- `MeasureTheory.Measure.map_eq_of_ae_pointwise_limit`: if a finite Borel
  measure $\mu$ satisfies $(F_n)_*\mu=\mu$ for every $n$ and
  $F_n(x)\to F(x)$ for $\mu$-almost every $x$, then $F_*\mu=\mu$.

- `MeasureTheory.Measure.map_eq_of_pointwise_limit`: if a finite Borel
  measure $\mu$ satisfies $(F_n)_*\mu=\mu$ for every $n$, if $F_n(x)$
  converges to $F(x)$ for every $x$, and if all maps are measurable,
  then $F_*\mu=\mu$.

The proof applies bounded convergence to nonnegative bounded continuous
test functions, then uses their measure-determining property.
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal

namespace MeasureTheory

/-- A finite Borel measure remains invariant under a measurable
almost-everywhere pointwise limit of measurable measure-preserving maps. -/
theorem Measure.map_eq_of_ae_pointwise_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [HasOuterApproxClosed X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → X) (Fₙ : ℕ → X → X)
    (hF : Measurable F) (hFₙ : ∀ n, Measurable (Fₙ n))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => Fₙ n x) atTop (nhds (F x)))
    (hinv : ∀ n, μ.map (Fₙ n) = μ) :
    μ.map F = μ := by
  symm
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro g
  let φ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞)
  have hφcont : Continuous φ := by fun_prop
  have hφm : Measurable φ := hφcont.measurable
  let C : ℝ≥0 := sSup (Set.range g)
  have hC (x : X) : g x ≤ C :=
    le_csSup g.isBounded_range.bddAbove ⟨x, rfl⟩
  have hfin : ∫⁻ _ : X, (C : ℝ≥0∞) ∂μ ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top μ Set.univ)
  have hmeas (n : ℕ) : Measurable (fun x => φ (Fₙ n x)) :=
    hφm.comp (hFₙ n)
  have hbound (n : ℕ) :
      (fun x => φ (Fₙ n x)) ≤ᵐ[μ] fun _ => (C : ℝ≥0∞) := by
    exact Filter.Eventually.of_forall (fun x => ENNReal.coe_le_coe.mpr (hC (Fₙ n x)))
  have hlimφ : ∀ᵐ x ∂μ,
      Tendsto (fun n => φ (Fₙ n x)) atTop (nhds (φ (F x))) :=
    hlim.mono (fun x hx => hφcont.continuousAt.tendsto.comp hx)
  have hDCT := tendsto_lintegral_of_dominated_convergence
    (μ := μ) (fun _ : X => (C : ℝ≥0∞)) hmeas hbound hfin hlimφ
  have hintegral (n : ℕ) :
      ∫⁻ x, φ (Fₙ n x) ∂μ = ∫⁻ x, φ x ∂μ := by
    rw [← lintegral_map hφm (hFₙ n), hinv n]
  have hconst : Tendsto (fun n => ∫⁻ x, φ (Fₙ n x) ∂μ)
      atTop (nhds (∫⁻ x, φ x ∂μ)) := by
    simpa only [hintegral] using
      (tendsto_const_nhds (x := ∫⁻ x, φ x ∂μ))
  have heq := tendsto_nhds_unique hconst hDCT
  rw [lintegral_map hφm hF]
  exact heq

/-- The everywhere pointwise version of invariance under limits. -/
theorem Measure.map_eq_of_pointwise_limit
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [HasOuterApproxClosed X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → X) (Fₙ : ℕ → X → X)
    (hF : Measurable F) (hFₙ : ∀ n, Measurable (Fₙ n))
    (hlim : ∀ x, Tendsto (fun n => Fₙ n x) atTop (nhds (F x)))
    (hinv : ∀ n, μ.map (Fₙ n) = μ) :
    μ.map F = μ :=
  μ.map_eq_of_ae_pointwise_limit F Fₙ hF hFₙ
    (ae_of_all _ hlim) hinv

end MeasureTheory

end
