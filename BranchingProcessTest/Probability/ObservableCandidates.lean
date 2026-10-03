import Probability.Process.HittingTime.ObservableCandidates
import Probability.Process.Adapted.Recursion

open MeasureTheory

#check ProbabilityTheory.CandidateObservable
#check ProbabilityTheory.successAtCompletion_observable
#check ProbabilityTheory.successfulCandidateWithin_measurable
#check ProbabilityTheory.causal_recursion_adapted

example {Ω ι : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    ProbabilityTheory.CandidateObservable F completion
      (fun i => ProbabilityTheory.successAtCompletion (completion i) (test i)) :=
  ProbabilityTheory.successAtCompletion_observable F completion test
    hcompletion htest

example {Ω ι : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (success : ι → Set Ω) (h : ProbabilityTheory.CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (T : ℕ) :
    MeasurableSet[F T]
      (ProbabilityTheory.successfulCandidateWithin completion success candidates T) :=
  ProbabilityTheory.successfulCandidateWithin_measurable F completion success h
    candidates hcandidates T
