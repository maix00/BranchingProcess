module

public import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed
public import Probability.BranchingRandomWalk.Step.GenerationUpdate

/-!
# Generation candidates under local field updates

Changing the steps owned by generation `m` cannot change the offspring
candidates exposed by an earlier generation.  This is the set-valued bridge
needed for recursive rank-installed couplings.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching

/-- An update at a later parent generation leaves the current generation's
child-candidate set unchanged. -/
theorem childrenAtGeneration_updateGeneration_of_lt
    {Root α X : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    (n m : ℕ) (hnm : n < m)
    (parents : Finset (RootIndexed.TreeNode Root α))
    (replacement fallback : RootIndexed.StepField Root α X) :
    childrenAtGeneration n parents
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          m replacement fallback) =
      childrenAtGeneration n parents fallback := by
  ext q
  rw [mem_childrenAtGeneration_iff, mem_childrenAtGeneration_iff]
  constructor
  · rintro ⟨p, hp, hpdepth, i, hi, rfl⟩
    refine ⟨p, hp, hpdepth, i, ?_, rfl⟩
    have hstep :
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration
            m replacement fallback p.1 p.2 = fallback p.1 p.2 := by
      apply Combinatorics.Branching.StepField.updateGeneration_of_lt
      simpa [hpdepth] using hnm
    rw [hstep] at hi
    exact hi
  · rintro ⟨p, hp, hpdepth, i, hi, rfl⟩
    refine ⟨p, hp, hpdepth, i, ?_, rfl⟩
    have hstep :
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration
            m replacement fallback p.1 p.2 = fallback p.1 p.2 := by
      apply Combinatorics.Branching.StepField.updateGeneration_of_lt
      simpa [hpdepth] using hnm
    rw [hstep]
    exact hi

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
