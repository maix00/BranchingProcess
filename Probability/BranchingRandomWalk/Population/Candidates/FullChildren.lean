/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs
public import Probability.BranchingRandomWalk.Population.Candidates.MultiRoot
public import Probability.BranchingRandomWalk.Population.Candidates.Ordering
public import Probability.BranchingRandomWalk.Population.Candidates.Prefix

/-!
# Full offspring candidates and strict-rank membership

This module exposes the full child population and its strict-rank predicate.
The latter is phrased using finite predecessor subsets, so it also describes
selection when the predecessor set has not been separately shown finite.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.allMultiRootChildren` is the set
  $\{q:\exists p\in s,\ \exists j\in\mathbb N,\ \operatorname{survive}(\omega(p),j)
  \land q=\operatorname{RootIndexed.childAddress}(p,j)\}$ of all realized children of
  a finite labelled parent set, without a slot cutoff.
- `ProbabilityTheory.BranchingRandomWalk.fullRankBelow N x ω C q` means that
  there is no $N$-element finite subset $t\subseteq C$ whose members all
  precede $q$ under
  `ProbabilityTheory.BranchingRandomWalk.candidateEarlier`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- All realized children of a finite labelled parent set, without a slot
cutoff. -/
def allMultiRootChildren {m : ℕ}
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ) :
    Set (RootAddress m ℕ) :=
  {q | ∃ p ∈ s, ∃ j : ℕ,
    survive (ω p.1 p.2) j ∧ q = RootIndexed.childAddress p j}

/-- A particle is among the first `N` of a possibly infinite set when there
is no finite set of `N` distinct candidates strictly ahead of it. -/
def fullRankBelow {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (ω : FiniteRootStepField m ℕ ℝ) (s : Set (RootAddress m ℕ))
    (q : RootAddress m ℕ) : Prop :=
  ¬∃ t : Finset (RootAddress m ℕ), t.card = N ∧
    ∀ r ∈ t, r ∈ s ∧ candidateEarlier x ω r q

end ProbabilityTheory.BranchingRandomWalk
