import Combinatorics.BranchingStep.Field

/-!
# Root-indexed branching step fields

An arbitrary type `Root` indexes the initial ancestors. Each label owns its own
step field over the Ulam--Harris addresses, and reindexing along a map
`f : NewRoot → Root` relabels the roots. The `Fin m` and `ℕ` instances are the
finite and countable cases used by the population arguments.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



abbrev RootIndexedBranchingStepField (Root : Type*) (X : Type*) :=
  Root → BranchingStepField ℕ X

abbrev FiniteRootBranchingStepField (m : ℕ) (X : Type*) :=
  RootIndexedBranchingStepField (Fin m) X

abbrev CountableRootBranchingStepField (X : Type*) :=
  RootIndexedBranchingStepField ℕ X

def RootIndexedBranchingStepField.reindex
    {Root NewRoot X : Type*} (f : NewRoot → Root)
    (step : RootIndexedBranchingStepField Root X) :
    RootIndexedBranchingStepField NewRoot X :=
  fun r => step (f r)

def RootIndexedBranchingStepField.first
    {X : Type*} (m : ℕ) (step : CountableRootBranchingStepField X) :
    FiniteRootBranchingStepField m X :=
  step.reindex Fin.val

def FiniteRootBranchingStepField.first
    {X : Type*} {m n : ℕ} (h : m ≤ n)
    (step : FiniteRootBranchingStepField n X) :
    FiniteRootBranchingStepField m X :=
  step.reindex (Fin.castLE h)

end ProbabilityTheory.BranchingRandomWalk
