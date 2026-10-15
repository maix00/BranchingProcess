/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law

/-!
# Product law for a finite vector of variable-length blocks

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measure_pi_forall_variableConsecutiveBlockEvent`:
  for lengths $\ell_0,\ldots,\ell_{q-1}$, with
  $N=\sum_{j<q}\ell_j$, and measurable events $E_j$ on the corresponding
  blocks, the product law on $N$ increments satisfies
  $\mathbb P(\forall j<q,\ X_{[a_j,a_j+\ell_j)}\in E_j)
   =\prod_{j<q}\mathbb P(X_{[0,\ell_j)}\in E_j)$, where
  $a_j=\sum_{i<j}\ell_i$.
- `ProbabilityTheory.RandomWalk.measure_pi_forall_variableConsecutiveBlockEvent_of_sum`:
  the same identity when the total block length is supplied by an
  equality $\sum_{j<q}\ell_j=N$.

This finite-coordinate form transports the existing independent-block
identity for the canonical IID sequence law to a finite product measure.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- A finite product measure factors over a consecutive partition into
variable-length measurable coordinate-block events. -/
theorem measure_pi_forall_variableConsecutiveBlockEvent
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    let total := AdditivePath.blockStart length blocks
    Measure.pi (fun _ : Fin total => ν)
      {x : Fin total → E | ∀ j : Fin blocks,
        (fun k : Fin (length j.val) =>
          x ⟨AdditivePath.blockStart length j.val + k.val, by
            have hmono := AdditivePath.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [AdditivePath.blockStart_succ] at hmono
            omega⟩) ∈ event j} =
      ∏ j : Fin blocks,
        Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
  let total := AdditivePath.blockStart length blocks
  let finiteEvent : Set (Fin total → E) :=
    {x | ∀ j : Fin blocks,
      (fun k : Fin (length j.val) =>
        x ⟨AdditivePath.blockStart length j.val + k.val, by
          have hmono := AdditivePath.blockStart_mono length
            (Nat.succ_le_of_lt j.isLt)
          rw [AdditivePath.blockStart_succ] at hmono
          omega⟩) ∈ event j}
  have hfinite : MeasurableSet finiteEvent := by
    have h : MeasurableSet (⋂ j : Fin blocks,
      {x : Fin total → E |
        (fun k : Fin (length j.val) =>
          x ⟨AdditivePath.blockStart length j.val + k.val, by
            have hmono := AdditivePath.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [AdditivePath.blockStart_succ] at hmono
            omega⟩) ∈ event j}) := by
      apply MeasurableSet.iInter
      intro j
      apply (hmeas j).preimage
      exact measurable_pi_iff.mpr fun k => measurable_pi_apply _
    simpa only [finiteEvent, Set.iInter_ofPred] using h
  let firstCoordinates : (ℕ → E) → Fin total → E := fun x i => x i.val
  have hprefix : Measurable firstCoordinates :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  have hpreimage :
      firstCoordinates ⁻¹' finiteEvent =
        {x : ℕ → E | ∀ j : Fin blocks,
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) x ∈ event j} := by
    ext x
    simp only [Set.mem_preimage, finiteEvent, Set.mem_ofPred_eq]
    apply forall_congr'
    intro j
    have heq :
        (fun k : Fin (length j.val) =>
          firstCoordinates x ⟨AdditivePath.blockStart length j.val + k.val, by
            have hmono := AdditivePath.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [AdditivePath.blockStart_succ] at hmono
            omega⟩) =
          Combinatorics.Sequence.blockCoordinates
            (AdditivePath.blockStart length j.val) (length j.val) x := by
      funext k
      rfl
    rw [heq]
  dsimp only
  rw [← iidSequenceLaw_map_finPrefix ν total]
  rw [Measure.map_apply hprefix hfinite, hpreimage]
  rw [iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent ν length blocks event hmeas]
  apply Finset.prod_congr rfl
  intro j _
  rw [← iidSequenceLaw_map_finPrefix ν (length j.val)]
  rw [Measure.map_apply (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)
    (hmeas j)]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  have heq :
      Combinatorics.Sequence.blockCoordinates 0 (length j.val) x =
        (fun i : Fin (length j.val) => x i.val) := by
    funext k
    simp [Combinatorics.Sequence.blockCoordinates]
  rw [heq]

/-- The finite product block factorization with an explicit total length. -/
theorem measure_pi_forall_variableConsecutiveBlockEvent_of_sum
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks n : ℕ)
    (htotal : AdditivePath.blockStart length blocks = n)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    Measure.pi (fun _ : Fin n => ν)
      {x : Fin n → E | ∀ j : Fin blocks,
        (fun k : Fin (length j.val) =>
          x ⟨AdditivePath.blockStart length j.val + k.val, by
            have hmono := AdditivePath.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [AdditivePath.blockStart_succ] at hmono
            omega⟩) ∈ event j} =
      ∏ j : Fin blocks,
        Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
  subst n
  exact measure_pi_forall_variableConsecutiveBlockEvent
    ν length blocks event hmeas

end ProbabilityTheory.RandomWalk

end
