import Probability.Process.HittingTime.Declarations
import Probability.BranchingRandomWalk.Timing.Stopping

open MeasureTheory

#check ProbabilityTheory.firstDeclaredSuccess
#check ProbabilityTheory.firstDeclaredSuccess_le_iff
#check ProbabilityTheory.firstDeclaredSuccess_isStoppingTime
#check ProbabilityTheory.BranchingRandomWalk.firstDeclaredSuccess

example {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (success : ℕ → Set Ω)
    (h : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F (ProbabilityTheory.firstDeclaredSuccess success) :=
  ProbabilityTheory.firstDeclaredSuccess_isStoppingTime F success h

example {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (success : ℕ → Set Ω)
    (h : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F
      (ProbabilityTheory.BranchingRandomWalk.firstDeclaredSuccess success) :=
  ProbabilityTheory.BranchingRandomWalk.firstDeclaredSuccess_isStoppingTime
    F success h
