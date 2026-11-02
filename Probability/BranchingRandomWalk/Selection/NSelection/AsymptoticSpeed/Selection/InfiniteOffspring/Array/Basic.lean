/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Run

/-!
# Definitions for the infinite-offspring block array

## Public declarations

`infiniteSelectionBlockMinimum` is the left endpoint after evolving N
particles from the common origin for a finite block. Its negative,
`infiniteSelectionSubadditiveArray`, records the corresponding displacement
with the sign used in Kingman's subadditive ergodic theorem.
`infiniteSelectionEndpointArray` is the same array indexed by ordered time
endpoints, with truncated subtraction defining it on all endpoint pairs.

For a fixed good offspring environment b, the defining quantities are
\[
  B_b(s,n)=\texttt{infiniteSelectionBlockMinimum}(s,n),
  \qquad A_b(s,n)=-B_b(s,n),
  \qquad A_b(s,t)=A_b(s,t-s)\quad(s\le t).
\]
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

/-- The leftmost position after a block of the fixed optional-offspring
environment, started from N particles at the common origin. -/
noncomputable def infiniteSelectionBlockMinimum
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start length : ℕ) : ℝ :=
  infiniteOffspringRun (fun t => offspring (start + t))
    (fun t => hgood (start + t)) (fun _ => 0) length ⟨0, hN⟩

/-- Negative block minima form a subadditive array indexed by a start time
and a block length. -/
noncomputable def infiniteSelectionSubadditiveArray
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start length : ℕ) : ℝ :=
  - infiniteSelectionBlockMinimum hN offspring hgood start length

/-- Endpoint-indexed version of the block array, defined for all pairs by
using truncated subtraction. The subadditive statements below use ordered
endpoints. -/
noncomputable def infiniteSelectionEndpointArray
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start endpoint : ℕ) : ℝ :=
  infiniteSelectionSubadditiveArray hN offspring hgood start (endpoint - start)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
