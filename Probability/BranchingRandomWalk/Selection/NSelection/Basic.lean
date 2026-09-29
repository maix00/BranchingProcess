module

public import Probability.BranchingRandomWalk.Basic
public import Combinatorics.BranchingWalk.Selection.NSelection.BranchingWalk

/-!
# Random `N`-branching walks

`NBranchingRandomWalk N α Mark Position` is the random version of
`NBranchingWalk N α Mark Position`:
a probability measure on the `N`-branching walks. A random `N`-selection is a
measurable map between branching random walks whose image consists of
`N`-branching walks; it is not developed here, only the law of the resulting
walk.
-/

@[expose] public section

namespace ProbabilityTheory

namespace BranchingRandomWalk

namespace Selection

namespace NSelection open MeasureTheory Combinatorics.UlamHarris Combinatorics.Branching

universe u v

/-- A random `N`-branching walk: a probability measure on
`NBranchingWalk N α Mark Position`. -/
structure NBranchingRandomWalk (N : ℕ) (α : Type u)
    (Mark Position : Type v)
    [MeasurableSpace Mark] [MeasurableSpace Position] where
  /-- The law of the walk. -/
  law : Measure (NBranchingWalk N α Mark Position)
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law

end NSelection end Selection

end BranchingRandomWalk

end ProbabilityTheory
