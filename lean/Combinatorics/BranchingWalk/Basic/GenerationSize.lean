module

public import Combinatorics.BranchingWalk.Basic.Survival
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

/- Once a generation is empty, its children are absent, so all later
generations are empty as well. -/
theorem RootIndexed.BranchingWalk.generationSize_succ_eq_zero_of_eq_zero
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ)
    (hzero : β.generationSize n = 0) :
    β.generationSize (n + 1) = 0 := by
  change (survivingParticlesAt β n).encard = 0 at hzero
  have hempty : survivingParticlesAt β n = ∅ :=
    Set.encard_eq_zero.mp hzero
  change (survivingParticlesAt β (n + 1)).encard = 0
  apply Set.encard_eq_zero.mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rcases p with ⟨r, u⟩
  rw [mem_survivingParticlesAt_iff,
    mem_survivingParticles_iff_surviveAlong] at hp
  have hu : u.length = n + 1 := by
    simpa [Combinatorics.UlamHarris.generation] using hp.2
  have hprefixLength : (u.take n).length = n := by
    rw [List.length_take, hu, Nat.min_eq_left]
    omega
  have hsurvive : surviveAlong (β.step r) [] u := hp.1
  have hprefixSurvives : surviveAlong (β.step r) [] (u.take n) := by
    apply surviveAlong_prefix (β.step r) (u.take n) (u.drop n)
    rw [List.take_append_drop]
    exact hsurvive
  have hparent : (r, u.take n) ∈ survivingParticlesAt β n := by
    rw [mem_survivingParticlesAt_iff,
      mem_survivingParticles_iff_surviveAlong]
    refine ⟨hprefixSurvives, ?_⟩
    change (u.take n).length = n
    exact hprefixLength
  rw [hempty] at hparent
  exact hparent

/-- An empty generation forces every later generation to be empty. -/
theorem RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) {n m : ℕ}
    (hnm : n ≤ m) (hzero : β.generationSize n = 0) :
    β.generationSize m = 0 := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      simpa using hzero
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · have hmid : β.generationSize m = 0 := ih hnm' hzero
        simpa using
          RootIndexed.BranchingWalk.generationSize_succ_eq_zero_of_eq_zero
            β m hmid
      · have hn : n = m + 1 := by omega
        subst n
        exact hzero

end Combinatorics.Branching

end
