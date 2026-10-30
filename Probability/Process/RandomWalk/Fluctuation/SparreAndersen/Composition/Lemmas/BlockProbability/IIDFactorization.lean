/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.Defs.LinearOrder
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Basic
import Combinatorics.Sequence.CyclicGap.Basic
import Probability.Process.RandomWalk.Path.Survival.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic.Abel
import Probability.Sequence.IID.Blocks.Consecutive

import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Lemmas.BlockProbability.Event
import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Lemmas.BlockProbability.Measure

/-!
# IID factorization over cyclic gaps

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.measure_pi_cyclicBlockEvent_eq_prod`:
  under the finite IID product law, the probability of $B_u$ is the product of
  the nonnegative-survival probabilities on the consecutive cyclic gaps
  determined by $u$.

This is equation (A.6) in Appendix A of M. Bauer, C. Godrèche, and
J.-M. Luck, “Statistics of persistent events in the binomial random walk:
Will the drunken sailor hit the sober man?”, *Journal of Statistical
Physics* 96 (1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252.
-/

section

open MeasureTheory

open Combinatorics.Sequence

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- A finite product measure factors over a consecutive partition into
variable-length measurable coordinate-block events. -/
private lemma measure_pi_cyclicGapBlocks_eq_prod
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    let total := Combinatorics.Sequence.blockStart length blocks
    Measure.pi (fun _ : Fin total => ν)
      {x : Fin total → E | ∀ j : Fin blocks,
        (fun k : Fin (length j.val) =>
          x ⟨Combinatorics.Sequence.blockStart length j.val + k.val, by
            have hmono := Combinatorics.Sequence.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [Combinatorics.Sequence.blockStart_succ] at hmono
            omega⟩) ∈ event j} =
      ∏ j : Fin blocks,
        Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
  let total := Combinatorics.Sequence.blockStart length blocks
  let finiteEvent : Set (Fin total → E) :=
    {x | ∀ j : Fin blocks,
      (fun k : Fin (length j.val) =>
        x ⟨Combinatorics.Sequence.blockStart length j.val + k.val, by
          have hmono := Combinatorics.Sequence.blockStart_mono length
            (Nat.succ_le_of_lt j.isLt)
          rw [Combinatorics.Sequence.blockStart_succ] at hmono
          omega⟩) ∈ event j}
  have hfinite : MeasurableSet finiteEvent := by
    have h : MeasurableSet (⋂ j : Fin blocks,
      {x : Fin total → E |
        (fun k : Fin (length j.val) =>
          x ⟨Combinatorics.Sequence.blockStart length j.val + k.val, by
            have hmono := Combinatorics.Sequence.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [Combinatorics.Sequence.blockStart_succ] at hmono
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
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) x ∈ event j} := by
    ext x
    simp only [Set.mem_preimage, finiteEvent, Set.mem_ofPred_eq]
    apply forall_congr'
    intro j
    have heq :
        (fun k : Fin (length j.val) =>
          firstCoordinates x ⟨Combinatorics.Sequence.blockStart length j.val + k.val, by
            have hmono := Combinatorics.Sequence.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [Combinatorics.Sequence.blockStart_succ] at hmono
            omega⟩) =
          Combinatorics.Sequence.blockCoordinates
            (Combinatorics.Sequence.blockStart length j.val) (length j.val) x := by
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
private lemma measure_pi_cyclicGapBlocks_eq_prod_of_total
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks n : ℕ)
    (htotal : Combinatorics.Sequence.blockStart length blocks = n)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    Measure.pi (fun _ : Fin n => ν)
      {x : Fin n → E | ∀ j : Fin blocks,
        (fun k : Fin (length j.val) =>
          x ⟨Combinatorics.Sequence.blockStart length j.val + k.val, by
            have hmono := Combinatorics.Sequence.blockStart_mono length
              (Nat.succ_le_of_lt j.isLt)
            rw [Combinatorics.Sequence.blockStart_succ] at hmono
            omega⟩) ∈ event j} =
      ∏ j : Fin blocks,
        Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
  subst n
  exact measure_pi_cyclicGapBlocks_eq_prod
    ν length blocks event hmeas


/-- Bauer--Godrèche--Luck, Appendix A, equation (A.6): the selected cyclic
survival intersection factors into the survival probabilities of its
disjoint cyclic blocks under an IID finite product law. -/
lemma measure_pi_cyclicBlockEvent_eq_prod
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    (ν : Measure G) [IsProbabilityMeasure ν]
    {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    Measure.pi (fun _ : Fin n => ν) (cyclicBlockEvent u hu) =
      ∏ j : Fin u.card,
        Measure.pi (fun _ : Fin (cyclicGapLength u hu j) => ν)
          {z : Fin (cyclicGapLength u hu j) → G |
            ∀ t : Fin (cyclicGapLength u hu j + 1),
              0 ≤ Fin.partialSum z t} := by
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  let event : ∀ j : Fin u.card, Set (Fin (length j.val) → G) :=
    fun j => {z | ∀ t : Fin (length j.val + 1), 0 ≤ Fin.partialSum z t}
  have hmeas (j : Fin u.card) : MeasurableSet (event j) :=
    measurableSet_nonnegativePartialSum (n := length j.val) hIci
  have htotal : Combinatorics.Sequence.blockStart length u.card = n :=
    blockStart_cyclicGapLength_card u hu
  have hproduct := measure_pi_cyclicGapBlocks_eq_prod_of_total
    ν length u.card n htotal event hmeas
  let e := finCycle
    (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
  let T : (Fin n → G) ≃ᵐ (Fin n → G) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => G) e.symm
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map T =
      Measure.pi (fun _ : Fin n => ν) := by
    simpa [T] using Measure.pi_map_piCongrLeft e.symm
      (fun _ : Fin n => ν)
  have hT (x : Fin n → G) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => G)
        e.symm x (e i))
  let blockEvent : Set (Fin n → G) :=
    {y | ∀ j : Fin u.card,
      (fun i : Fin (length j.val) =>
        y ⟨Combinatorics.Sequence.blockStart length j.val + i.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          have hi : i.val < cyclicGapLength u hu j := by
            exact i.isLt
          change Combinatorics.Sequence.blockStart length j.val +
            cyclicGapLength u hu j ≤ n at hbound
          omega⟩) ∈ event j}
  have hevent : cyclicBlockEvent u hu = T ⁻¹' blockEvent := by
    rw [cyclicBlockEvent_eq_gapSurvival u hu]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, blockEvent]
    apply forall_congr'
    intro j
    have hvec :
        cyclicGapCoordinates u hu x j =
          (fun i : Fin (cyclicGapLength u hu j) =>
            T x ⟨Combinatorics.Sequence.blockStart length j.val + i.val, by
              have hbound := blockStart_add_cyclicGapLength_le u hu j
              change Combinatorics.Sequence.blockStart length j.val +
                cyclicGapLength u hu j ≤ n at hbound
              omega⟩) := by
      funext i
      exact (hT x _).symm
    rcases j with ⟨j, hj⟩
    simp only [event, length, hvec]
    rfl
  have hblockMeas : MeasurableSet blockEvent := by
    have heq : blockEvent = T.symm ⁻¹' cyclicBlockEvent u hu := by
      rw [hevent]
      ext y
      simp
    rw [heq]
    exact (measurableSet_cyclicBlockEvent hIci u hu).preimage T.symm.measurable
  rw [hevent, ← Measure.map_apply T.measurable hblockMeas, hmap]
  change (Measure.pi (fun _ : Fin n => ν)) blockEvent = _
  calc
    (Measure.pi (fun _ : Fin n => ν)) blockEvent =
        ∏ j : Fin u.card,
          Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
      simpa only [blockEvent] using hproduct
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rfl

end ProbabilityTheory.RandomWalk

end
