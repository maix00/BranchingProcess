/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Coordinates
public import Probability.Independence.Finite
public import Probability.Sequence.IID
public import Mathlib.Probability.Independence.Basic

/-!
# Laws of block sums

Finite sums of consecutive IID coordinates inherit their distribution and
independence from the coordinate-block API.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- Under an IID increment law, the probability that every one of finitely
many consecutive equal-length coordinate blocks belongs to the same
measurable set is the corresponding power of the one-block probability.

The statement is phrased for any measurable finite-block event; applications
such as block oscillation can then use it without reproving the product-law
calculation. -/
theorem iidSequenceLaw_measure_forall_consecutiveBlockEvent
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) (event : Set (Fin length → E))
    (hmeas : MeasurableSet event) :
    iidSequenceLaw ν {increment : ℕ → E | ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates (j * length) length increment ∈ event} =
      (iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈ event}) ^ blocks := by
  let blockMap : Fin blocks → (ℕ → E) → (Fin length → E) := fun j =>
    Combinatorics.Sequence.blockCoordinates (j * length) length
  let allBlocks : (ℕ → E) → (Fin blocks → Fin length → E) := fun increment j =>
    blockMap j increment
  let productSet : Set (Fin blocks → Fin length → E) :=
    Set.univ.pi fun _ : Fin blocks => event
  have hblockMeasurable (j : Fin blocks) : Measurable (blockMap j) :=
    measurable_blockCoordinates (j * length) length
  have hallBlocksMeasurable : Measurable allBlocks := by
    rw [measurable_pi_iff]
    exact fun j => (hblockMeasurable j).comp measurable_id
  have hindep := iIndepFun_consecutiveBlockCoordinates ν blocks length
  have hmap : (iidSequenceLaw ν).map allBlocks =
      Measure.pi fun j : Fin blocks => (iidSequenceLaw ν).map (blockMap j) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun j => (hblockMeasurable j).aemeasurable)).mp hindep
  have hproductSet : MeasurableSet productSet :=
    MeasurableSet.pi Set.countable_univ fun _ _ => hmeas
  have hevent :
      {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event} =
        allBlocks ⁻¹' productSet := by
    ext increment
    simp [productSet, allBlocks, blockMap, Set.mem_pi]
  have hshift (j : Fin blocks) :
      (iidSequenceLaw ν).map (blockMap j) event =
        (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event := by
    exact congrArg (fun measure : Measure (Fin length → E) => measure event)
      (iidSequenceLaw_map_blockCoordinates ν (j * length) length)
  calc
    _ = (iidSequenceLaw ν).map allBlocks productSet := by
      change (iidSequenceLaw ν)
          {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event} = _
      rw [hevent]
      exact (Measure.map_apply hallBlocksMeasurable hproductSet).symm
    _ = (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j)) productSet := by rw [hmap]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map (blockMap j) event := by
      change (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j))
        (Set.univ.pi fun _ : Fin blocks => event) = _
      rw [Measure.pi_pi]
    _ = ∏ _j : Fin blocks, (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hshift j
    _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length) event) ^ blocks := by
      simp
    _ = _ := by
      rw [Measure.map_apply (measurable_blockCoordinates 0 length) hmeas]
      rfl

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- Under an IID increment law, a finite family of consecutive blocks may
have different lengths and different measurable block events. The joint
probability is the product of the corresponding one-block probabilities.

This is the finite-partition form of block independence used when a
piecewise-constant corridor is cut at its finitely many jump times. -/
theorem iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    (ν : Measure E) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (event : ∀ j : Fin blocks, Set (Fin (length j.val) → E))
    (hmeas : ∀ j, MeasurableSet (event j)) :
    iidSequenceLaw ν {increment : ℕ → E | ∀ j : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart length j.val) (length j.val) increment ∈ event j} =
      ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈ event j} := by
  let blockMap : (j : Fin blocks) → (ℕ → E) → (Fin (length j.val) → E) :=
    fun j => Combinatorics.Sequence.blockCoordinates
      (AdditivePath.blockStart length j.val) (length j.val)
  let allBlocks : (ℕ → E) → ∀ j : Fin blocks, Fin (length j.val) → E :=
    fun increment j => blockMap j increment
  let productSet : Set (∀ j : Fin blocks, Fin (length j.val) → E) :=
    Set.univ.pi event
  have hblockMeasurable (j : Fin blocks) : Measurable (blockMap j) :=
    measurable_blockCoordinates _ _
  have hallBlocksMeasurable : Measurable allBlocks := by
    rw [measurable_pi_iff]
    exact fun j => (hblockMeasurable j).comp measurable_id
  have hindep := iIndepFun_variableConsecutiveBlockCoordinates ν length blocks
  have hmap : (iidSequenceLaw ν).map allBlocks =
      Measure.pi fun j : Fin blocks => (iidSequenceLaw ν).map (blockMap j) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (fun j => (hblockMeasurable j).aemeasurable)).mp hindep
  have hproductSet : MeasurableSet productSet :=
    MeasurableSet.pi Set.countable_univ fun j _ => hmeas j
  have hevent :
      {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event j} =
        allBlocks ⁻¹' productSet := by
    ext increment
    simp [productSet, allBlocks, Set.mem_pi]
  have hshift (j : Fin blocks) :
      (iidSequenceLaw ν).map (blockMap j) (event j) =
        (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 (length j.val)) (event j) := by
    exact congrArg (fun μ : Measure (Fin (length j.val) → E) => μ (event j))
      (iidSequenceLaw_map_blockCoordinates ν (AdditivePath.blockStart length j.val)
        (length j.val))
  calc
    _ = (iidSequenceLaw ν).map allBlocks productSet := by
      change iidSequenceLaw ν
          {increment : ℕ → E | ∀ j : Fin blocks, blockMap j increment ∈ event j} = _
      rw [hevent]
      exact (Measure.map_apply hallBlocksMeasurable hproductSet).symm
    _ = (Measure.pi fun j : Fin blocks =>
          (iidSequenceLaw ν).map (blockMap j)) productSet := by rw [hmap]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map (blockMap j) (event j) := by
      change (Measure.pi fun j : Fin blocks =>
        (iidSequenceLaw ν).map (blockMap j)) (Set.univ.pi event) = _
      rw [Measure.pi_pi]
    _ = ∏ j : Fin blocks, (iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 (length j.val)) (event j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hshift j
    _ = ∏ j : Fin blocks, iidSequenceLaw ν {increment : ℕ → E |
          Combinatorics.Sequence.blockCoordinates 0 (length j.val) increment ∈ event j} := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Measure.map_apply (measurable_blockCoordinates 0 (length j.val)) (hmeas j)]
      rfl
    _ = _ := rfl

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- Events determined by two consecutive, disjoint IID coordinate blocks
factor into the prefix probability and the one-block probability.  This is
the two-block form used when a corridor path is followed by an endpoint
entrance block. -/
theorem iidSequenceLaw_measure_inter_prefix_nextBlock
    (ν : Measure E) [IsProbabilityMeasure ν]
    (prefixLength length : ℕ)
    (prefixEvent : Set (Fin prefixLength → E))
    (nextEvent : Set (Fin length → E))
    (hprefix : MeasurableSet prefixEvent)
    (hnext : MeasurableSet nextEvent) :
    iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ prefixEvent ∧
        Combinatorics.Sequence.blockCoordinates prefixLength length increment ∈ nextEvent} =
      iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ prefixEvent} *
      iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈ nextEvent} := by
  let first : (ℕ → E) → (Fin prefixLength → E) :=
    Combinatorics.Sequence.blockCoordinates 0 prefixLength
  let next : (ℕ → E) → (Fin length → E) :=
    Combinatorics.Sequence.blockCoordinates prefixLength length
  have hindep : IndepFun first next (iidSequenceLaw ν) := by
    simpa [first, next] using
      (indepFun_blockCoordinates_blockCoordinates ν 0 prefixLength length)
  have hfactor := hindep.measure_inter_preimage_eq_mul
    prefixEvent nextEvent hprefix hnext
  have hshift :
      iidSequenceLaw ν {increment : ℕ → E | next increment ∈ nextEvent} =
        iidSequenceLaw ν {increment : ℕ → E |
          Combinatorics.Sequence.blockCoordinates 0 length increment ∈ nextEvent} := by
    have hmap := congrArg (fun measure : Measure (Fin length → E) => measure nextEvent)
      (iidSequenceLaw_map_blockCoordinates ν prefixLength length)
    rw [Measure.map_apply (measurable_blockCoordinates prefixLength length) hnext,
      Measure.map_apply (measurable_blockCoordinates 0 length) hnext] at hmap
    exact hmap
  change (iidSequenceLaw ν) (next ⁻¹' nextEvent) = _ at hshift
  change iidSequenceLaw ν (first ⁻¹' prefixEvent ∩ next ⁻¹' nextEvent) = _
  rw [hfactor, hshift]
  rfl

/-- Every deterministic shift of a block sum has the same law as the
corresponding initial partial sum. -/
theorem iidSequenceLaw_map_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) :
    (iidSequenceLaw ν).map (AdditivePath.blockSum start length) =
      (iidSequenceLaw ν).map (AdditivePath.displacement length) := by
  rw [show AdditivePath.blockSum (E := E) start length =
      AdditivePath.displacement length ∘ fun increment => fun k => increment (start + k) by
    funext increment
    exact AdditivePath.blockSum_eq_displacement_natAdd start length increment]
  rw [← Measure.map_map (displacement_measurable length) (measurable_natAdd start)]
  rw [iidSequenceLaw_map_natAdd]

/-- Sums over two consecutive deterministic blocks are independent; this
follows by applying the finite-sum maps to their independent coordinate paths. -/
theorem indepFun_blockSum_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (AdditivePath.blockSum (E := E) start m)
      (AdditivePath.blockSum (start + m) n) (iidSequenceLaw ν) := by
  have hcoords := indepFun_blockCoordinates_blockCoordinates ν start m n
  have hsum (k : ℕ) : Measurable (fun x : Fin k → E => ∑ i, x i) :=
    Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i
  have h := hcoords.comp (hsum m) (hsum n)
  have hleft :
      (fun increment : ℕ → E => ∑ k : Fin m,
        Combinatorics.Sequence.blockCoordinates start m increment k) =
        AdditivePath.blockSum (E := E) start m := by
    funext increment
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    simp only [Combinatorics.Sequence.blockCoordinates]
    exact Fin.sum_univ_eq_sum_range (fun k => increment (start + k)) m
  have hright :
      (fun increment : ℕ → E => ∑ k : Fin n,
        Combinatorics.Sequence.blockCoordinates (start + m) n increment k) =
        AdditivePath.blockSum (E := E) (start + m) n := by
    funext increment
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    simp only [Combinatorics.Sequence.blockCoordinates]
    exact Fin.sum_univ_eq_sum_range
      (fun k => increment (start + m + k)) n
  change IndepFun
    (fun increment => ∑ k : Fin m,
      Combinatorics.Sequence.blockCoordinates start m increment k)
    (fun increment => ∑ k : Fin n,
      Combinatorics.Sequence.blockCoordinates (start + m) n increment k)
    (iidSequenceLaw ν) at h
  rw [hleft, hright] at h
  exact h

/-- The vector of the first variable-length block sums is independent of the
next block sum, by applying the finite-sum map to coordinate-block independence. -/
theorem indepFun_variableConsecutiveBlockSums_next
    (ν : Measure E) [IsProbabilityMeasure ν] (length : ℕ → ℕ) (blocks : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart length j.val)
          (length j.val) increment)
      (AdditivePath.blockSum (AdditivePath.blockStart length blocks) (length blocks))
      (iidSequenceLaw ν) := by
  let left : (∀ j : Fin blocks, Fin (length j.val) → E) → Fin blocks → E :=
    fun x j => ∑ k, x j k
  let right : (Fin (length blocks) → E) → E := fun x => ∑ k, x k
  have h := indepFun_variableConsecutiveBlockCoordinates_next ν length blocks
  have hleftMeasurable : Measurable left := by
    fun_prop
  have hrightMeasurable : Measurable right :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_pi_apply k
  have h := h.comp hleftMeasurable hrightMeasurable
  have hleft : left ∘ (fun increment (j : Fin blocks) =>
      Combinatorics.Sequence.blockCoordinates (AdditivePath.blockStart length j.val)
        (length j.val) increment) =
      (fun increment (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart length j.val)
          (length j.val) increment) := by
    funext increment j
    simp only [Function.comp_apply, left, Combinatorics.Sequence.blockCoordinates]
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    exact Fin.sum_univ_eq_sum_range
      (fun k => increment (AdditivePath.blockStart length j.val + k))
      (length j.val)
  have hright : right ∘ Combinatorics.Sequence.blockCoordinates
      (AdditivePath.blockStart length blocks) (length blocks) =
      AdditivePath.blockSum (AdditivePath.blockStart length blocks) (length blocks) := by
    funext increment
    simp only [Function.comp_apply, right, Combinatorics.Sequence.blockCoordinates]
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    exact Fin.sum_univ_eq_sum_range
      (fun k => increment (AdditivePath.blockStart length blocks + k))
      (length blocks)
  simpa only [hleft, hright, Function.comp_apply] using h

/-- Any finite family of variable-length block sums is mutually independent,
by applying the finite-sum map to the independent coordinate blocks. -/
theorem iIndepFun_variableConsecutiveBlockSums
    (ν : Measure E) [IsProbabilityMeasure ν] (length : ℕ → ℕ) (blocks : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      AdditivePath.blockSum (AdditivePath.blockStart length j.val)
        (length j.val) increment) (iidSequenceLaw ν) := by
  let sumBlock : ∀ j : Fin blocks, (Fin (length j.val) → E) → E :=
    fun _ x => ∑ k, x k
  have hcoords := iIndepFun_variableConsecutiveBlockCoordinates ν length blocks
  have hsumMeasurable (j : Fin blocks) : Measurable (sumBlock j) :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_pi_apply k
  have h := hcoords.comp sumBlock hsumMeasurable
  have hsum : (fun (j : Fin blocks) (increment : ℕ → E) =>
      sumBlock j (Combinatorics.Sequence.blockCoordinates
        (AdditivePath.blockStart length j.val) (length j.val) increment)) =
      (fun (j : Fin blocks) (increment : ℕ → E) =>
        AdditivePath.blockSum (AdditivePath.blockStart length j.val)
          (length j.val) increment) := by
    funext j increment
    simp only [sumBlock, Combinatorics.Sequence.blockCoordinates]
    rw [AdditivePath.blockSum_eq_displacement_natAdd]
    exact Fin.sum_univ_eq_sum_range
      (fun k => increment (AdditivePath.blockStart length j.val + k))
      (length j.val)
  rw [← hsum]
  exact h

/-- Equal-length next-block sums specialize from variable-length block-sum
independence. -/
theorem indepFun_consecutiveBlockSums_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        AdditivePath.blockSum (j * length) length increment)
      (AdditivePath.blockSum (blocks * length) length)
      (iidSequenceLaw ν) := by
  simpa only [AdditivePath.blockStart_const] using
    indepFun_variableConsecutiveBlockSums_next ν (fun _ => length) blocks

/-- Any finite family of equal-length block sums specializes from the
variable-length block-sum theorem. -/
theorem iIndepFun_consecutiveBlockSums
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      AdditivePath.blockSum (j * length) length increment) (iidSequenceLaw ν) := by
  simpa only [AdditivePath.blockStart_const] using
    iIndepFun_variableConsecutiveBlockSums ν (fun _ => length) blocks

end ProbabilityTheory.RandomWalk

end
