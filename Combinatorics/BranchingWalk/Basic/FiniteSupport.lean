/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.BranchingWalk
public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.StepField

/-!
# Finite support of branching-walk fields

Finite support means that only finitely many child slots are present at each
address, for every root:

\[
\forall u,\quad\operatorname{support}(\beta(u))\text{ is finite},
\qquad
\forall r\ \forall u,\quad
\operatorname{support}((\beta.\operatorname{step}(r))(u))\text{ is finite}.
\]

## Public declarations

- `StepField.IsFinitelySupported β` means every local step has finite support:
  `∀ u, Step.IsFinitelySupported (β u)`.
- `RootIndexed.BranchingWalk.IsFinitelySupported β` means every root's step
  field has finite support:
  `∀ r, StepField.IsFinitelySupported (β.step r)`.

These pointwise predicates belong to the branching-walk data layer. The
consequence that finite support implies orderability on natural-number slots
is proved in `Basic/Ordering/Orderable.lean`.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- A step field is finitely supported when all of its steps are. -/
class StepField.IsFinitelySupported {α X : Type*} (β : StepField α X) : Prop where
  pointwise : ∀ u, Step.IsFinitelySupported (β u)

/-- A root-indexed walk is finitely supported when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsFinitelySupported
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop where
  pointwise : ∀ r, StepField.IsFinitelySupported (β.step r)

end Combinatorics.Branching

end
