import Probability.Measure.ConvolutionPower

open MeasureTheory

#check MeasureTheory.Measure.convPower
#check MeasureTheory.Measure.convPower_zero
#check MeasureTheory.Measure.convPower_succ
#check MeasureTheory.Measure.convPow
#check MeasureTheory.Measure.convPow_zero
#check MeasureTheory.Measure.convPow_succ
#check MeasureTheory.Measure.convPow_eq_convPower

example {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ : Measure E) [SFinite μ] (n : ℕ) :
    μ.convPow n = μ.convPower n :=
  MeasureTheory.Measure.convPow_eq_convPower μ n

example {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (n : ℕ) :
    SFinite (μ.convPower n) := inferInstance

example {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ : Measure E) [SFinite μ] (n : ℕ) :
    SFinite (μ.convPow n) := inferInstance

example {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (μ.convPower n) :=
  MeasureTheory.Measure.isProbabilityMeasure_convPower μ n

example {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [MeasurableSingletonClass E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (μ.convPow n) := inferInstance
