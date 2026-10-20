import MeasureTheory.Measure.Convolution.Power

open MeasureTheory

#check MeasureTheory.Measure.convPower
#check MeasureTheory.Measure.convPower_zero
#check MeasureTheory.Measure.convPower_succ
example {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (n : ℕ) :
    SFinite (μ.convPower n) := inferInstance

example {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (μ.convPower n) :=
  MeasureTheory.Measure.isProbabilityMeasure_convPower μ n
