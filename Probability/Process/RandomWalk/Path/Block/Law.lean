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
