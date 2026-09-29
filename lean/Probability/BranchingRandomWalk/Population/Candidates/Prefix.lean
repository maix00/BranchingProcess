module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
public import Combinatorics.BranchingWalk.Step.SlotOrder

/-!
# Finite prefixes of children from several roots

Candidate generation is defined for an abstract ordered child-slot type.
The first `N` inspected slots are `firstSlots α N`; these finite prefixes
have cardinality `N` and exhaust `α`.  No randomness or ordering assumption
is built into the definition: it is applied to a step field that has already
been transported through the chosen measurable ordering.
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

def childAddress {m : ℕ} {α : Type*} (p : RootAddress m α) (j : α) :
    RootAddress m α :=
  (p.1, p.2 ++ [j])

noncomputable def oneChildCandidate {m : ℕ}
    (ω : FiniteRootStepField m α X) (p : RootAddress m α) (j : α) :
    Finset (RootAddress m α) := by
  classical
  exact if survive (ω p.1 p.2) j then {childAddress p j} else ∅

theorem mem_oneChildCandidate_iff {m : ℕ}
    (ω : FiniteRootStepField m α X) (p q : RootAddress m α) (j : α) :
    q ∈ oneChildCandidate ω p j ↔
      survive (ω p.1 p.2) j ∧ q = childAddress p j := by
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
  simp [childAddress, hp]

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
    childAddress p j ∈
      prefixCandidates (slotOrderIsoNat α j + 1) s ω := by
  classical
  unfold prefixCandidates
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, Finset.mem_biUnion.mpr ?_⟩
  exact ⟨j, mem_firstSlots_succ_rank j,
    (mem_oneChildCandidate_iff ω p (childAddress p j) j).2 ⟨hj, rfl⟩⟩

end ProbabilityTheory.BranchingRandomWalk
