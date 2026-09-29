module

public import Combinatorics.BranchingWalk.Basic.Descendant
public import Combinatorics.BranchingWalk.Step.Map

/-!
# Generation size of a branching walk

The population at a generation is already represented by
`survivingParticlesAt`. Its cardinality is therefore an observation of every
root-indexed branching walk. The unmarked branching specialization inherits
this definition, and forgetting marks leaves it unchanged.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- The possibly infinite number of surviving particles at generation `n`,
across all labelled initial roots. -/
noncomputable def RootIndexed.BranchingWalk.generationSize
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position)
    (n : ℕ) : ℕ∞ :=
  (survivingParticlesAt β n).encard

/-- Forgetting marks does not change the surviving population at any
generation. -/
@[simp] theorem RootIndexed.BranchingWalk.survivingParticlesAt_toBranching
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ) :
    survivingParticlesAt β.toBranching n = survivingParticlesAt β n := by
  ext p
  rw [mem_survivingParticlesAt_iff, mem_survivingParticlesAt_iff]
  apply and_congr
  · rw [mem_survivingParticles_iff_surviveAlong,
      mem_survivingParticles_iff_surviveAlong]
    exact RootIndexed.BranchingWalk.surviveAlong_toBranching_iff
      β p.1 [] p.2
  · rfl

/-- Forgetting marks does not alter generation sizes. -/
@[simp] theorem RootIndexed.BranchingWalk.generationSize_toBranching
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ) :
    β.toBranching.generationSize n = β.generationSize n := by
  simp [RootIndexed.BranchingWalk.generationSize]

end Combinatorics.Branching

end
