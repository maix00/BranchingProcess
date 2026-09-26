import Probability.BranchingRandomWalk.Step.Law

/-!
# Branching random walks

`BranchingRandomWalk α X` is the random version of `BranchingWalk α X`: a law
on the deterministic branching walks, that is a probability measure on
`BranchingWalk α X`. The canonical instance `iid μ` is the independent,
identically distributed walk in which every address carries an independent
branching step with law `μ`.
-/

namespace ProbabilityTheory

namespace BranchingRandomWalk

open MeasureTheory MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory

/-- A branching random walk: a probability measure on `BranchingWalk α X`. -/
structure BranchingRandomWalk (α X : Type*) [MeasurableSpace X] where
  /-- The law of the walk. -/
  law : Measure (BranchingWalk α X)
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law

instance (α X : Type*) [MeasurableSpace X] :
    CoeFun (BranchingRandomWalk α X) (fun _ => Measure (BranchingWalk α X)) :=
  ⟨BranchingRandomWalk.law⟩

/-- The i.i.d. branching random walk: every address carries an independent
branching step with law `μ`. -/
noncomputable def iid {α X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] : BranchingRandomWalk α X :=
  ⟨stepFieldLaw μ, stepFieldLaw.isProbabilityMeasure μ⟩

end BranchingRandomWalk

end ProbabilityTheory
