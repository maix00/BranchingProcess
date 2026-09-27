import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Root-indexed branching step fields

An arbitrary type `Root` indexes the initial ancestors. Each label owns its own
step field over the Ulam--Harris addresses, and reindexing along a map
`f : NewRoot → Root` relabels the roots. The `Fin m` and `ℕ` instances are the
finite and countable cases used by the population arguments.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



namespace RootIndexed

abbrev StepField (Root α X : Type*) :=
  Root → Combinatorics.Branching.StepField α X

end RootIndexed

abbrev FiniteRootStepField (m : ℕ) (α X : Type*) :=
  RootIndexed.StepField (Fin m) α X

abbrev CountableRootStepField (α X : Type*) :=
  RootIndexed.StepField ℕ α X

namespace RootIndexed.StepField

def reindex {Root NewRoot α X : Type*} (f : NewRoot → Root)
    (step : RootIndexed.StepField Root α X) :
    RootIndexed.StepField NewRoot α X :=
  fun r => step (f r)

def first {α X : Type*} (m : ℕ) (step : CountableRootStepField α X) :
    FiniteRootStepField m α X :=
  step.reindex Fin.val

end RootIndexed.StepField

def FiniteRootStepField.first
    {α X : Type*} {m n : ℕ} (h : m ≤ n)
    (step : FiniteRootStepField n α X) :
    FiniteRootStepField m α X :=
  step.reindex (Fin.castLE h)

end ProbabilityTheory.BranchingRandomWalk
