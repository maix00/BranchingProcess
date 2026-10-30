/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Candidates.Generation
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability

/-!
# Measurability of generation candidate sets

For a measurable generation-$n$ parent set $P_n(\omega)$, the set of
surviving children `Combinatorics.Branching.Population.childrenAtGeneration n (P_n ω) ω` is measurable with
respect to the generation-$(n+1)$ domain flow. This result uses the generic
combinatorial candidate construction from
`Combinatorics.BranchingWalk.Population.Candidates.Generation`.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.childrenAtGeneration_measurable`
  proves the generation-flow measurability of the full surviving child set
  when the parent-set map is measurable at generation $n$.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

namespace RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Population

/-- The full child-candidate set is observable one generation after its
parents. No finiteness or countability condition is imposed on offspring
slots. -/
theorem childrenAtGeneration_measurable
    {Root α X : Type*} [MeasurableSpace X]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (hparents : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] parents) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (n + 1)]
      (fun ω => Combinatorics.Branching.Population.childrenAtGeneration n (parents ω) ω) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)
  rw [measurable_set_iff]
  intro q
  by_cases hdepth : q.2.length = n + 1
  · have hnonempty : q.2 ≠ [] := by
      intro h
      simp [h] at hdepth
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hparentDepth : (RootIndexed.parent q).2.length = n := by
      simp only [RootIndexed.parent]
      rw [List.length_dropLast, hdepth]
      omega
    have hparents' : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)] parents :=
      hparents.mono
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) |>.mono
          (Nat.le_succ n)) le_rfl
    have hparentMem : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)]
        (fun ω => RootIndexed.parent q ∈ parents ω) :=
      (measurable_finset_mem (RootIndexed.parent q)).comp hparents'
    have hsurvive : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)]
        (fun ω => survive (ω (RootIndexed.parent q).1 (RootIndexed.parent q).2) i) := by
      apply measurableSet_setOfPred.mp
      exact (RootIndexed.step_measurable (X := X)
        (RootIndexed.parent q).1 (RootIndexed.parent q).2 (by omega))
          (survive_measurableSet (X := X) i)
    simpa [Combinatorics.Branching.Population.childrenAtGeneration, hdepth, hi] using hparentMem.and hsurvive
  · simp [Combinatorics.Branching.Population.childrenAtGeneration, hdepth]
end RootIndexed

end ProbabilityTheory.BranchingRandomWalk

end
