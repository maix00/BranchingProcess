import Probability.Process.HittingTime.ObservableCandidates
import Probability.Process.Adapted.Recursion

open MeasureTheory

#check ProbabilityTheory.Trial.CandidateObservable
#check ProbabilityTheory.Trial.successAtCompletion_observable
#check ProbabilityTheory.Trial.successfulCandidateWithin_measurable
#check ProbabilityTheory.causal_recursion_adapted

example {Ω ι : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    ProbabilityTheory.Trial.CandidateObservable F completion
      (fun i => ProbabilityTheory.Trial.successAtCompletion (completion i) (test i)) :=
  ProbabilityTheory.Trial.successAtCompletion_observable F completion test
    hcompletion htest

example {Ω ι : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (completion : ι → Ω → WithTop ℕ)
    (success : ι → Set Ω) (h : ProbabilityTheory.Trial.CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (T : ℕ) :
    MeasurableSet[F T]
      (ProbabilityTheory.Trial.successfulCandidateWithin completion success candidates T) :=
  ProbabilityTheory.Trial.successfulCandidateWithin_measurable F completion success h
    candidates hcandidates T
