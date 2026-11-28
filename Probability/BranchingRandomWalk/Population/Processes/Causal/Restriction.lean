/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Mathlib.Data.Finset.Image

/-!
# Finite ancestral restrictions of causal populations

## Public declarations

* `RootIndexed.CausalPopulation.restrictAncestors` retains
  $P_n^s=\{(r,u)\in P_n:(r,u_{\le j})\in s\ (0\le j\le|u|)\}$ for a finite $s$.
* `RootIndexed.CausalPopulation.mem_restrictAncestors` gives its membership
  equivalence; the construction preserves adaptedness and parent closure.
* `RootIndexed.CausalPopulation.restrictAncestors_finiteSlices` gives
  $P_n^s\subseteq s$, hence every restricted generation is finite.
* `RootIndexed.CausalPopulation.restrictAncestors_subset` and
  `RootIndexed.CausalPopulation.restrictAncestors_mono` give $P_n^s\subseteq P_n$
  and $P_n^s\subseteq P_n^t$ when $s\subseteq t$.
* `RootIndexed.CausalPopulation.exists_mem_restrictAncestors` says every
  particle of $P_n$ belongs to $P_n^s$ for some finite $s$.

No offspring-law, state-space, or ordering condition is used.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}

/-- Retain particles whose finite ancestral paths lie in `s`. -/
def restrictAncestors (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (s : Finset (RootIndexed.TreeNode Root α)) :
    RootIndexed.CausalPopulation Ω Root α X ℱ stepField where
  toPopulation ω :=
    { particles := fun n => {p | p ∈ P n ω ∧ ∀ j ≤ p.2.length, (p.1, p.2.take j) ∈ s}
      depth := fun n p hp => P.depth n ω p hp.1
      successor := by
        intro n q hq
        obtain ⟨p, hp, i, hi, heq⟩ :=
          Population.mem_offspringAddressSet.mp (P.successor n ω hq.1)
        subst q
        apply Population.mem_offspringAddressSet.mpr
        refine ⟨p, ⟨hp, ?_⟩, i, hi, rfl⟩
        intro j hj
        have h := hq.2 j (by simpa [RootIndexed.childAddress] using (Nat.le_succ_of_le hj))
        simpa [RootIndexed.childAddress, List.take_append_of_le_length hj] using h }
  adapted p n := by
    have h := P.adapted p n
    letI : MeasurableSpace Ω := ℱ n
    exact h.and measurable_const

@[simp] theorem mem_restrictAncestors
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (s : Finset (RootIndexed.TreeNode Root α)) (n : ℕ) (ω : Ω)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ P.restrictAncestors s n ω ↔
      p ∈ P n ω ∧ ∀ j ≤ p.2.length, (p.1, p.2.take j) ∈ s := Iff.rfl

theorem restrictAncestors_subset
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (s : Finset (RootIndexed.TreeNode Root α)) (n : ℕ) (ω : Ω) :
    P.restrictAncestors s n ω ⊆ P n ω := fun _ hp => hp.1

theorem restrictAncestors_mono
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {s t : Finset (RootIndexed.TreeNode Root α)} (hst : s ⊆ t) (n : ℕ) (ω : Ω) :
    P.restrictAncestors s n ω ⊆ P.restrictAncestors t n ω :=
  fun _ hp => ⟨hp.1, fun j hj => hst (hp.2 j hj)⟩

theorem restrictAncestors_finiteSlices
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (s : Finset (RootIndexed.TreeNode Root α)) : (P.restrictAncestors s).FiniteSlices := by
  intro n ω
  apply s.finite_toSet.subset
  intro p hp
  simpa using hp.2 p.2.length le_rfl

theorem exists_mem_restrictAncestors
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    ∃ s : Finset (RootIndexed.TreeNode Root α), p ∈ P.restrictAncestors s n ω := by
  classical
  refine ⟨(Finset.range (p.2.length + 1)).image (fun j => (p.1, p.2.take j)), hp, ?_⟩
  intro j hj
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

end ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation
