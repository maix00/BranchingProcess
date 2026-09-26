import Probability.BranchingRandomWalk.Basic
import Combinatorics.BranchingWalk.Selection.NSelection.BranchingWalk

/-!
# Random `N`-branching walks

`NBranchingRandomWalk N α X` is the random version of `NBranchingWalk N α X`:
a probability measure on the `N`-branching walks. A random `N`-selection is a
measurable map between branching random walks whose image consists of
`N`-branching walks; it is not developed here, only the law of the resulting
walk.
-/

namespace ProbabilityTheory

namespace BranchingRandomWalk

namespace Selection

namespace NSelection

open MeasureTheory Combinatorics.UlamHarris Combinatorics.Branching

universe u v

/-- A random `N`-branching walk: a probability measure on
`NBranchingWalk N α X`. -/
structure NBranchingRandomWalk (N : ℕ) (α : Type u) (X : Type v)
    [MeasurableSpace X] where
  /-- The law of the walk. -/
  law : Measure (NBranchingWalk N α X)
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law

end NSelection

end Selection

end BranchingRandomWalk

end ProbabilityTheory
