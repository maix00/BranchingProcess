import Probability.Process.HittingTime.Declarations

open MeasureTheory

#check ProbabilityTheory.firstDeclaredSuccess
#check ProbabilityTheory.firstDeclaredSuccess_le_iff
#check ProbabilityTheory.firstDeclaredSuccess_isStoppingTime

example {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℕ m) (success : ℕ → Set Ω)
    (h : ∀ n, MeasurableSet[F n] (success n)) :
    IsStoppingTime F (ProbabilityTheory.firstDeclaredSuccess success) :=
  ProbabilityTheory.firstDeclaredSuccess_isStoppingTime F success h
