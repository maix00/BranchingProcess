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



abbrev RootIndexed.StepField (Root : Type*) (X : Type*) :=
  Root → Combinatorics.Branching.StepField ℕ X

abbrev FiniteRootStepField (m : ℕ) (X : Type*) :=
  RootIndexed.StepField (Fin m) X

abbrev CountableRootStepField (X : Type*) :=
  RootIndexed.StepField ℕ X

def RootIndexed.StepField.reindex
    {Root NewRoot X : Type*} (f : NewRoot → Root)
    (step : RootIndexed.StepField Root X) :
    RootIndexed.StepField NewRoot X :=
  fun r => step (f r)

def RootIndexed.StepField.first
    {X : Type*} (m : ℕ) (step : CountableRootStepField X) :
    FiniteRootStepField m X :=
  step.reindex Fin.val

def FiniteRootStepField.first
    {X : Type*} {m n : ℕ} (h : m ≤ n)
    (step : FiniteRootStepField n X) :
    FiniteRootStepField m X :=
  step.reindex (Fin.castLE h)

end ProbabilityTheory.BranchingRandomWalk
