module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional integration of an independent random variable

This file connects mathlib's independence and regular conditional
distribution APIs.  It is useful when a future random input is independent
of the variable generating the current domain.
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

end ProbabilityTheory
