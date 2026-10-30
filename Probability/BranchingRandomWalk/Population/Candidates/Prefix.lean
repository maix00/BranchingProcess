/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Basic
public import Combinatorics.BranchingWalk.Step.Ordering.SlotOrder
public import Combinatorics.UlamHarris.Relation

/-!
# Finite prefixes of children from several roots

Candidate generation is defined for an abstract ordered child-slot type.
The first $N$ inspected slots are `firstSlots α N`; this finite prefix has
cardinality $N$ and exhausts the slot type. Candidate generation is applied
to a step field already transported through the chosen measurable ordering.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootAddress` is the root-indexed
  address type. `ProbabilityTheory.BranchingRandomWalk.initialRootAddresses`
  is the set of $m$ empty addresses $(i,[])$, and
  `ProbabilityTheory.BranchingRandomWalk.initialRootAddresses_card` gives its
  cardinality $m$.
- `Combinatorics.UlamHarris.RootIndexed.childAddress` supplies the structural
  address extension used here. `ProbabilityTheory.BranchingRandomWalk.oneChildCandidate`
  is the resulting singleton when that slot survives, and is empty otherwise;
  `ProbabilityTheory.BranchingRandomWalk.mem_oneChildCandidate_iff` gives its
  membership characterization.
- `ProbabilityTheory.BranchingRandomWalk.prefixCandidates N s ω` is the set
  of surviving children of parents in $s$ at slots in `firstSlots α N`.
  `ProbabilityTheory.BranchingRandomWalk.oneChildCandidate_depth` and
  `ProbabilityTheory.BranchingRandomWalk.prefixCandidates_depth` state that
  each resulting address has length one greater than its parent.
- `ProbabilityTheory.BranchingRandomWalk.child_mem_prefixCandidates_eventually`
  states that every surviving child of a parent in a finite parent set occurs
  in `prefixCandidates N s ω` for some finite $N$.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

variable {α X : Type*}

abbrev RootAddress (m : ℕ) (α : Type*) :=
  RootIndexed.TreeNode (Fin m) α

instance (m : ℕ) (α : Type*) : MeasurableSpace (Finset (RootAddress m α)) := ⊤

def initialRootAddresses (m : ℕ) {α : Type*} :
    Finset (RootAddress m α) :=
  Finset.univ.map
    ⟨fun i : Fin m => (i, []), fun _ _ h => congrArg Prod.fst h⟩

noncomputable def oneChildCandidate {m : ℕ}
    (ω : FiniteRootStepField m α X) (p : RootAddress m α) (j : α) :
    Finset (RootAddress m α) := by
  classical
  exact if survive (ω p.1 p.2) j then
    {RootIndexed.childAddress p j} else ∅

theorem mem_oneChildCandidate_iff {m : ℕ}
    (ω : FiniteRootStepField m α X) (p q : RootAddress m α) (j : α) :
    q ∈ oneChildCandidate ω p j ↔
      survive (ω p.1 p.2) j ∧ q = RootIndexed.childAddress p j := by
  classical
  unfold oneChildCandidate
  split_ifs with h
  · simp [h]
  · simp [h]

noncomputable def prefixCandidates {m : ℕ}
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (N : ℕ) (s : Finset (RootAddress m α))
    (ω : FiniteRootStepField m α X) : Finset (RootAddress m α) := by
  classical
  exact s.biUnion (fun p =>
    (firstSlots α N).biUnion (oneChildCandidate ω p))

@[simp] theorem initialRootAddresses_card (m : ℕ) (α : Type*) :
    (initialRootAddresses (α := α) m).card = m := by
  simp [initialRootAddresses]

theorem oneChildCandidate_depth {m n : ℕ}
    (ω : FiniteRootStepField m α X) (p q : RootAddress m α) (j : α)
    (hp : p.2.length = n) (hq : q ∈ oneChildCandidate ω p j) :
    q.2.length = n + 1 := by
  rw [mem_oneChildCandidate_iff] at hq
  rcases hq with ⟨_, rfl⟩
  simp [RootIndexed.childAddress, hp]

theorem prefixCandidates_depth {m n : ℕ}
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (N : ℕ) (s : Finset (RootAddress m α))
    (ω : FiniteRootStepField m α X)
    (hs : ∀ p ∈ s, p.2.length = n)
    (q : RootAddress m α) (hq : q ∈ prefixCandidates N s ω) :
    q.2.length = n + 1 := by
  classical
  unfold prefixCandidates at hq
  obtain ⟨p, hp, j, _, hqj⟩ := by
    simpa only [Finset.mem_biUnion] using hq
  exact oneChildCandidate_depth ω p q j (hs p hp) hqj

/-- Every ordered slot is inspected at some finite population cutoff. -/
theorem child_mem_prefixCandidates_eventually {m : ℕ}
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (s : Finset (RootAddress m α)) (ω : FiniteRootStepField m α X)
    (p : RootAddress m α) (hp : p ∈ s) (j : α)
    (hj : survive (ω p.1 p.2) j) :
    ∃ N : ℕ, RootIndexed.childAddress p j ∈ prefixCandidates N s ω := by
  classical
  obtain ⟨N, hN⟩ := exists_mem_firstSlots j
  refine ⟨N, ?_⟩
  unfold prefixCandidates
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, Finset.mem_biUnion.mpr ?_⟩
  exact ⟨j, hN,
    (mem_oneChildCandidate_iff ω p (RootIndexed.childAddress p j) j).2
      ⟨hj, rfl⟩⟩

end ProbabilityTheory.BranchingRandomWalk
