/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Finite

/-!
# Splits of a selected branching step

## Public declarations

For a finite selection rule `R`, `splitBy R` is the set of branching steps
whose selected family has at least two children:

\[
\operatorname{splitBy}(R)=\{\xi:2\leq |R(\xi)|\}.
\]
-/

@[expose] public section

namespace Combinatorics.Branching.Step.FiniteSelection

/-- A step is a split when the finite selection retains at least two children.
-/
def splitBy {α X : Type*} (R : Step.FiniteSelection α X) : Set (Step α X) :=
  {ξ | 2 ≤ (R ξ).card}

end Combinatorics.Branching.Step.FiniteSelection

end
