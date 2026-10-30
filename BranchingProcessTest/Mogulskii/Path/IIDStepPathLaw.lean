import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℝ}
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw
      (fun ω => terminalLeftNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω))
      ((iidSequenceLaw ν).map (terminalLeftNormalizedStepCadlagPathIcc scale n)) P :=
  hasLaw_terminalLeftNormalizedStepCadlagPathIcc_of_iid
    hindep hmeasurable hlaw scale n

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure ℝ}
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : MeasurableSet G) :
    P {ω | terminalLeftNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ G} =
      iidSequenceLaw ν {increment |
        terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ G} :=
  measure_terminalLeftNormalizedStepCadlagPathIcc_preimage_eq_of_iid
    hindep hmeasurable hlaw scale n hG

#print axioms ProbabilityTheory.RandomWalk.hasLaw_terminalLeftNormalizedStepCadlagPathIcc_of_iid
#print axioms ProbabilityTheory.RandomWalk.measure_terminalLeftNormalizedStepCadlagPathIcc_preimage_eq_of_iid
