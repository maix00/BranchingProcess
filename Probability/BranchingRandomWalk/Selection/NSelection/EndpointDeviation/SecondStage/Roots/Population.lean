/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
/-!
# Population threshold for the second-stage roots

## Public declarations

The declarations are in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`.

- `RestartedField m` is the field space
  \(\Omega_m=\operatorname{StepField}(\operatorname{Fin}(m),\mathbb N,\mathbb R)\).
- `RestartedPopulation m` is the causal population on \(\Omega_m\), rooted at
  \(\operatorname{Fin}(m)\) and observed through `stepFiltration`.
- `secondStageEnoughRoots P hP generation n` defines the event
  \(A_n=\{\omega:K\le ((hP\,n).toFinset(\mathrm{generation}(n),\omega)).card\}\).
- `measurableSet_secondStageEnoughRoots` proves that `Aₙ` is
  measurable with respect to the field revealed through `generation n`, when
  every slice of `P` is finite.

This module owns the restarted field and population types together with the
finite-slice threshold event and its measurability. The predictable root
constructor and its measurable, injective-family interface are in
`Roots/Selection.lean`. The selected-root all-avoid estimate is a proof-chain
specialization in `Roots/Lemmas/AllAvoid.lean`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

@[expose] public section

/-- The root-indexed real step-field space used by the restarted
second-stage population. -/
abbrev RestartedField (m : ℕ) := RootIndexed.StepField (Fin m) ℕ ℝ

/-- The causal population process on `RestartedField m` with initial root set
`Fin m` and the natural-generation filtration. -/
abbrev RestartedPopulation (m : ℕ) :=
  RootIndexed.CausalPopulation (RestartedField m) (Fin m) ℕ ℝ
    (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)) id

/-- The event that the actual finite killed slice contains at least `K`
particles. -/
def secondStageEnoughRoots
    {m K : ℕ} (P : ℕ → RestartedPopulation m)
    (hP : ∀ n, (P n).FiniteSlices) (generation : ℕ → ℕ) (n : ℕ) :
    Set (RestartedField m) :=
  {field | K ≤ ((hP n).toFinset (generation n) field).card}

theorem measurableSet_secondStageEnoughRoots
    {m K : ℕ} (P : ℕ → RestartedPopulation m)
    (hP : ∀ n, (P n).FiniteSlices) (generation : ℕ → ℕ) (n : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) (generation n)]
      (secondStageEnoughRoots (K := K) P hP generation n) := by
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  let candidates : RestartedField m → Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
    fun field => (hP n).toFinset (generation n) field
  have hcandidates : Measurable[F (generation n)] candidates := by
    dsimp [candidates]
    exact (hP n).measurable_toFinset (generation n)
  have hcard : Measurable[F (generation n)]
      (fun field => (candidates field).card) :=
    (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode (Fin m) ℕ) => s.card)).comp
        hcandidates
  have hlarge : Measurable[F (generation n)]
      (fun field => K ≤ (candidates field).card) :=
    (measurable_of_countable (fun k : ℕ => K ≤ k)).comp hcard
  change MeasurableSet[F (generation n)]
    {field | K ≤ (candidates field).card}
  simpa using hlarge (measurableSet_singleton True)

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
