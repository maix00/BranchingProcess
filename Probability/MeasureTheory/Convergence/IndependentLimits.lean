/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Independence under almost-sure path limits

The public theorems in this file are:

- `MeasureTheory.ProbabilityMeasure.tendsto_map_of_ae_pointwise_limit`:
  if measurable random variables $F_n$ converge almost surely to $F$,
  their image probability measures converge weakly to the law of $F$.
- `ProbabilityTheory.indepFun_of_ae_pointwise_limits`:
  almost-sure limits of pairs of independent random variables are independent.

The first result uses bounded continuous test functions and dominated
convergence. The second combines this with continuity of products of
probability measures.
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal

namespace MeasureTheory

/-- Almost-sure convergence of measurable random variables implies weak
convergence of their laws. -/
theorem ProbabilityMeasure.tendsto_map_of_ae_pointwise_limit
    {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (ν : ProbabilityMeasure Ω) (F : Ω → X) (Fₙ : ℕ → Ω → X)
    (hF : Measurable F) (hFₙ : ∀ n, Measurable (Fₙ n))
    (hlim : ∀ᵐ ω ∂(ν : Measure Ω),
      Tendsto (fun n => Fₙ n ω) atTop (nhds (F ω))) :
    Tendsto (fun n => ν.map (Fₙ n)) atTop (nhds (ν.map F)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro g
  let φ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞)
  have hφcont : Continuous φ := by fun_prop
  have hφm : Measurable φ := hφcont.measurable
  let C : ℝ≥0 := sSup (Set.range g)
  have hC (x : X) : g x ≤ C :=
    le_csSup g.isBounded_range.bddAbove ⟨x, rfl⟩
  have hfin : ∫⁻ _ : Ω, (C : ℝ≥0∞) ∂(ν : Measure Ω) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (measure_ne_top (ν : Measure Ω) Set.univ)
  have hmeas (n : ℕ) : Measurable (fun ω => φ (Fₙ n ω)) :=
    hφm.comp (hFₙ n)
  have hbound (n : ℕ) :
      (fun ω => φ (Fₙ n ω)) ≤ᵐ[(ν : Measure Ω)]
        fun _ => (C : ℝ≥0∞) :=
    Filter.Eventually.of_forall
      (fun ω => ENNReal.coe_le_coe.mpr (hC (Fₙ n ω)))
  have hlimφ : ∀ᵐ ω ∂(ν : Measure Ω),
      Tendsto (fun n => φ (Fₙ n ω)) atTop (nhds (φ (F ω))) :=
    hlim.mono (fun ω hω => hφcont.continuousAt.tendsto.comp hω)
  have hDCT := tendsto_lintegral_of_dominated_convergence
    (μ := (ν : Measure Ω)) (fun _ : Ω => (C : ℝ≥0∞))
    hmeas hbound hfin hlimφ
  have heq (n : ℕ) :
      (∫⁻ x, φ x ∂(ν.map (Fₙ n) : Measure X)) =
        ∫⁻ ω, φ (Fₙ n ω) ∂(ν : Measure Ω) :=
    lintegral_map hφm (hFₙ n)
  have heqF :
      (∫⁻ x, φ x ∂(ν.map F : Measure X)) =
        ∫⁻ ω, φ (F ω) ∂(ν : Measure Ω) :=
    lintegral_map hφm hF
  change Tendsto
    (fun n => ∫⁻ x, φ x ∂(ν.map (Fₙ n) : Measure X))
    atTop (nhds (∫⁻ x, φ x ∂(ν.map F : Measure X)))
  simpa only [heq, heqF] using hDCT

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory
open TopologicalSpace

/-- Almost-sure limits of pairs of independent random variables with
separable pseudometrizable Borel targets remain independent. -/
theorem indepFun_of_ae_pointwise_limits
    {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [PseudoMetrizableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [PseudoMetrizableSpace Y]
    (ν : ProbabilityMeasure Ω)
    (F : Ω → X) (G : Ω → Y)
    (Fₙ : ℕ → Ω → X) (Gₙ : ℕ → Ω → Y)
    (hF : Measurable F) (hG : Measurable G)
    (hFₙ : ∀ n, Measurable (Fₙ n))
    (hGₙ : ∀ n, Measurable (Gₙ n))
    (hFlim : ∀ᵐ ω ∂(ν : Measure Ω),
      Tendsto (fun n => Fₙ n ω) atTop (nhds (F ω)))
    (hGlim : ∀ᵐ ω ∂(ν : Measure Ω),
      Tendsto (fun n => Gₙ n ω) atTop (nhds (G ω)))
    (hind : ∀ n, Fₙ n ⟂ᵢ[(ν : Measure Ω)] Gₙ n) :
    F ⟂ᵢ[(ν : Measure Ω)] G := by
  have hpairlim : ∀ᵐ ω ∂(ν : Measure Ω),
      Tendsto (fun n => (Fₙ n ω, Gₙ n ω)) atTop (nhds (F ω, G ω)) :=
    (hFlim.and hGlim).mono (fun _ hω => hω.1.prodMk_nhds hω.2)
  have hpair := ν.tendsto_map_of_ae_pointwise_limit
    (fun ω => (F ω, G ω)) (fun n ω => (Fₙ n ω, Gₙ n ω))
    (hF.prodMk hG) (fun n => (hFₙ n).prodMk (hGₙ n)) hpairlim
  have hFmap := ν.tendsto_map_of_ae_pointwise_limit F Fₙ hF hFₙ hFlim
  have hGmap := ν.tendsto_map_of_ae_pointwise_limit G Gₙ hG hGₙ hGlim
  have hprod : Tendsto
      (fun n => (ν.map (Fₙ n)).prod (ν.map (Gₙ n))) atTop
      (nhds ((ν.map F).prod (ν.map G))) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hFmap.prodMk_nhds hGmap)
  have heq (n : ℕ) :
      ν.map (fun ω => (Fₙ n ω, Gₙ n ω)) =
        (ν.map (Fₙ n)).prod (ν.map (Gₙ n)) := by
    apply Subtype.ext
    exact (indepFun_iff_map_prod_eq_prod_map_map
      (hFₙ n).aemeasurable (hGₙ n).aemeasurable).mp (hind n)
  have hlimitEq : ν.map (fun ω => (F ω, G ω)) =
      (ν.map F).prod (ν.map G) := by
    apply tendsto_nhds_unique hpair
    simpa only [heq] using hprod
  apply (indepFun_iff_map_prod_eq_prod_map_map
    hF.aemeasurable hG.aemeasurable).mpr
  exact congrArg ProbabilityMeasure.toMeasure hlimitEq

end ProbabilityTheory

end
