/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Laws on branching-walk sample spaces

`WalkLaw` is an arbitrary probability law on the space of branching walks.
It records no independence or homogeneity property; those belong to specific
constructions such as `iid`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

/-- An arbitrary probability law on branching-walk realizations.  This is an
alias for mathlib's probability-measure subtype and carries no branching
property by itself. -/
abbrev WalkLaw (α Mark Position : Type*)
    [MeasurableSpace Mark] [MeasurableSpace Position] :=
  MeasureTheory.ProbabilityMeasure
    (Combinatorics.Branching.BranchingWalk α Mark Position)

end ProbabilityTheory.BranchingRandomWalk

end
