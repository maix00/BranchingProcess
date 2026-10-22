/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional integration for independent random variables

The public results in this file are:

- `ProbabilityTheory.IndepFun.condDistrib_ae_eq_const`: for measurable
  $X,Y$ into measurable value spaces, a probability measure $P$, and
  $X\perp Y$, the conditional law of a standard-Borel-valued $Y$ given $X$
  equals the marginal law of $Y$ almost everywhere.
- `ProbabilityTheory.IndepFun.condExp_prod_ae_eq_integral_map`:
  for the same measurable independent pair and strongly measurable $f$ with
  $f(X,Y)\in L^1(P)$,
  $\mathbb E[f(X,Y)\mid X]=\int f(X,y)\,d(P\circ Y^{-1})(y)$ almost surely.
- `ProbabilityTheory.IndepFun.condExp_indicator_pairEvent_ae_eq_sectionProbability`:
  for measurable $E\subseteq A\times B$,
  $\mathbb E[\mathbf1_E(X,Y)\mid X](\omega)
   =(P\circ Y^{-1})\{y:(X(\omega),y)\in E\}$ almost surely.

The last identity supplies the conditional probability of a measurable
section and applies to any independent pair whose future value space is
standard Borel.
-/

open Filter MeasureTheory
open scoped MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory

variable {Sample Past Future Value : Type*}
  [MeasurableSpace Sample] [MeasurableSpace Past]
  [MeasurableSpace Future] [StandardBorelSpace Future] [Nonempty Future]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
  {P : Measure Sample} [IsProbabilityMeasure P]
  {X : Sample → Past} {Y : Sample → Future}

/-- The conditional distribution of an independent random variable is its
unconditional law. -/
theorem IndepFun.condDistrib_ae_eq_const (h : IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib Y X P =ᵐ[P.map X] Kernel.const Past (P.map Y) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd
    hX.aemeasurable hY.aemeasurable
  rw [h.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.compProd_const]

/-- Condition on `X` and integrate an independent input `Y` against its
unconditional law. -/
theorem IndepFun.condExp_prod_ae_eq_integral_map
    (h : IndepFun X Y P) (hX : Measurable X) (hY : Measurable Y)
    {f : Past × Future → Value} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun sample ↦ f (X sample, Y sample)) P) :
    condExp (MeasurableSpace.comap X inferInstance) P
        (fun sample ↦ f (X sample, Y sample)) =ᵐ[P]
      fun sample ↦ ∫ y, f (X sample, y) ∂P.map Y := by
  have hbase := condExp_prod_ae_eq_integral_condDistrib
    hX hY.aemeasurable hf hf_int
  have hcond := MeasureTheory.ae_of_ae_map hX.aemeasurable
    (h.condDistrib_ae_eq_const hX hY)
  filter_upwards [hbase, hcond] with sample hbase_sample hcond_sample
  rw [hbase_sample, hcond_sample, Kernel.const_apply]

/-- For independent random variables, the conditional expectation of the
indicator of a measurable pair event is the probability of its section under
the second marginal law. -/
theorem IndepFun.condExp_indicator_pairEvent_ae_eq_sectionProbability
    (h : IndepFun X Y P) (hX : Measurable X) (hY : Measurable Y)
    (E : Set (Past × Future)) (hE : MeasurableSet E) :
    condExp (MeasurableSpace.comap X inferInstance) P
        (fun sample => E.indicator (fun _ => (1 : ℝ)) (X sample, Y sample))
      =ᵐ[P] fun sample => (P.map Y).real {y | (X sample, y) ∈ E} := by
  let pair : Sample → Past × Future := fun sample => (X sample, Y sample)
  let f : Past × Future → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hpair : Measurable pair := hX.prodMk hY
  have hpreimage : MeasurableSet (pair ⁻¹' E) := hE.preimage hpair
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hE
  have hfi : Integrable (fun sample => f (pair sample)) P :=
    (integrable_const (c := (1 : ℝ))).indicator hpreimage
  have hcond := h.condExp_prod_ae_eq_integral_map hX hY hf hfi
  have hsectionIntegral (x : Past) :
      (∫ y, f (x, y) ∂P.map Y) = (P.map Y).real {y | (x, y) ∈ E} := by
    let sectionEvent : Set Future := {y | (x, y) ∈ E}
    have hsection : MeasurableSet sectionEvent :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hfunction : (fun y => f (x, y)) =
        sectionEvent.indicator (fun _ => (1 : ℝ)) := by
      funext y
      simp [f, sectionEvent, Set.indicator]
    rw [hfunction]
    change (∫ y, sectionEvent.indicator (fun _ => (1 : ℝ)) y ∂P.map Y) =
      (P.map Y).real sectionEvent
    rw [integral_indicator_const (e := (1 : ℝ)) hsection,
      smul_eq_mul, mul_one]
  filter_upwards [hcond] with sample hsample
  rw [hsample, hsectionIntegral]

end ProbabilityTheory
