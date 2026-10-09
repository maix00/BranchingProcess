import Probability.Sequence.IID.Law

open MeasureTheory ProbabilityTheory

example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} {coordinate : ℕ → Ω → E}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ n, Measurable (coordinate n))
    (hlaw : ∀ n, HasLaw (coordinate n) ν P) :
    HasLaw (fun ω n => coordinate n ω) (iidSequenceLaw ν) P :=
  hindep.hasLaw_iidSequenceLaw hmeasurable hlaw

example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} {coordinate : ℕ → Ω → E}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ n, Measurable (coordinate n))
    (hlaw : ∀ n, HasLaw (coordinate n) ν P)
    (s : Set (ℕ → E)) (hs : MeasurableSet s) :
    P {ω | (fun n => coordinate n ω) ∈ s} = iidSequenceLaw ν s := by
  exact (hindep.hasLaw_iidSequenceLaw hmeasurable hlaw).measure_eq hs

#print axioms ProbabilityTheory.iIndepFun.hasLaw_iidSequenceLaw
