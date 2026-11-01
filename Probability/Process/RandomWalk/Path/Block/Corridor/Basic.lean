/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Algebra.BigOperators.PartialSum

/-!
# Finite increment-block corridor predicates

Defines strict partial-sum corridor events and their endpoint-constrained
form. Deterministic estimates used to assemble block corridor bounds are in
`Corridor/Geometry.lean`.

## Public declarations

* `InOpenPartialSumCorridor lower upper block` is
  `∀ k : Fin (length + 1), lower < Fin.partialSum block k ∧
  Fin.partialSum block k < upper`.
* `inOpenPartialSumCorridor_iff_succ` identifies this predicate with
  `∀ k : Fin length, lower < Fin.partialSum block k.succ ∧
  Fin.partialSum block k.succ < upper` when `lower < 0 < upper`.
* `InOpenPartialSumCorridorEndsIn lower upper endLower endUpper block` is the
  conjunction of the corridor predicate and
  `Fin.partialSum block (Fin.last length) ∈ Set.Ioo endLower endUpper`.

For `\(S_k=\sum_{i<k}x_i\)`, the corridor event is
`\(\{x\in\mathbb R^L\mid\forall k\le L,\ a<S_k<b\}\)`; its endpoint
version additionally requires `\(c<S_L<d\)`.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Every partial sum of a finite increment block, including the initial
zero, lies strictly inside a fixed open interval. -/
def InOpenPartialSumCorridor {length : ℕ} (lower upper : ℝ)
    (block : Fin length → ℝ) : Prop :=
  ∀ k : Fin (length + 1),
    lower < Fin.partialSum block k ∧ Fin.partialSum block k < upper

/-- If the interval contains the initial position, a strict partial-sum
corridor is equivalent to checking its positive-time positions. -/
theorem inOpenPartialSumCorridor_iff_succ
    {length : ℕ} {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (block : Fin length → ℝ) :
    InOpenPartialSumCorridor lower upper block ↔
      ∀ k : Fin length,
        lower < Fin.partialSum block k.succ ∧
          Fin.partialSum block k.succ < upper := by
  constructor
  · intro h k
    exact h k.succ
  · intro h k
    refine Fin.induction ?_ ?_ k
    · simp [hlower, hupper]
    · intro k ih
      exact h k

/-- A finite increment block stays in an open corridor and ends in a given
open interval. -/
def InOpenPartialSumCorridorEndsIn {length : ℕ}
    (lower upper endLower endUpper : ℝ) (block : Fin length → ℝ) : Prop :=
  InOpenPartialSumCorridor lower upper block ∧
    Fin.partialSum block (Fin.last length) ∈ Set.Ioo endLower endUpper


end ProbabilityTheory.RandomWalk
