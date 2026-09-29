import Combinatorics.BranchingWalk.Walk.Path.Block.Basic
import Probability.Independence.Finite
import Probability.Sequence.IID
import Mathlib.Probability.Independence.Basic

/-!
# Laws and independence of increment blocks

Probability statements for consecutive blocks under the canonical i.i.d.
increment law.
-/

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Every deterministic shift of a block sum has the same law as the
corresponding initial partial sum. -/
theorem iidSequenceLaw_map_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) :
    (iidSequenceLaw ν).map (blockSum start length) =
      (iidSequenceLaw ν).map (partialSum length) := by
  rw [show blockSum (E := E) start length =
      partialSum length ∘ fun increment => fun k => increment (start + k) by
    funext increment
    exact blockSum_eq_partialSum_natAdd start length increment]
  rw [← Measure.map_map (partialSum_measurable length) (measurable_natAdd start)]
  rw [iidSequenceLaw_map_natAdd]

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- A finite coordinate block of an IID sequence has the same law after any
deterministic time shift. -/
theorem iidSequenceLaw_map_blockCoordinates (ν : Measure E)
    [IsProbabilityMeasure ν] (start length : ℕ) :
    (iidSequenceLaw ν).map (blockCoordinates start length) =
      (iidSequenceLaw ν).map (blockCoordinates 0 length) := by
  rw [show blockCoordinates (E := E) start length =
      blockCoordinates 0 length ∘ (fun increment => fun k => increment (start + k)) by
    funext increment k
    simp [blockCoordinates]]
  rw [← Measure.map_map (blockCoordinates_measurable 0 length)
    (measurable_natAdd start)]
  rw [iidSequenceLaw_map_natAdd]

/-- Sums over two consecutive deterministic blocks of an i.i.d. increment
path are independent. -/
theorem indepFun_blockSum_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (blockSum (E := E) start m)
      (blockSum (start + m) n) (iidSequenceLaw ν) := by
  let S := Finset.Ico start (start + m)
  let T := Finset.Ico (start + m) (start + m + n)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  have hsumS : Measurable (fun x : S → E => ∑ k : S, x k) := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_pi_apply k)
  have hsumT : Measurable (fun x : T → E => ∑ k : T, x k) := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_pi_apply k)
  have h := htuple.comp hsumS hsumT
  have hleft : (fun x : ℕ → E => ∑ k : S, x k) = blockSum start m := by
    funext x
    simpa [S, blockSum] using
      (Finset.sum_attach (Finset.Ico start (start + m)) x)
  have hright : (fun x : ℕ → E => ∑ k : T, x k) =
      blockSum (start + m) n := by
    funext x
    simpa [T, blockSum, Nat.add_assoc] using
      (Finset.sum_attach (Finset.Ico (start + m) (start + m + n)) x)
  simpa only [Function.comp_def, hleft, hright] using h

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- Two consecutive finite coordinate blocks of a canonical IID sequence are
independent.  This retains every coordinate, rather than only each block
sum, and therefore applies to arbitrary measurable finite-path events. -/
theorem indepFun_blockCoordinates_blockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (blockCoordinates (E := E) start m)
      (blockCoordinates (start + m) n) (iidSequenceLaw ν) := by
  let S := Finset.Ico start (start + m)
  let T := Finset.Ico (start + m) (start + m + n)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → (Fin m → E) := fun x k =>
    x ⟨start + k, by simp [S, k.isLt]⟩
  let right : (T → E) → (Fin n → E) := fun x k =>
    x ⟨start + m + k, by simp [T, k.isLt]⟩
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have hrightMeasurable : Measurable right := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have h := htuple.comp hleftMeasurable hrightMeasurable
  convert h using 1 <;> funext increment k <;>
    simp [left, right, blockCoordinates, Nat.add_assoc]

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- The vector of the first `blocks` consecutive coordinate blocks is
independent of the next block.  Unlike a statement about block sums, this
retains the full finite path in each block. -/
theorem indepFun_consecutiveBlockCoordinates_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        blockCoordinates (j * length) length increment)
      (blockCoordinates (blocks * length) length)
      (iidSequenceLaw ν) := by
  classical
  let S := Finset.range (blocks * length)
  let T := Finset.Ico (blocks * length) ((blocks + 1) * length)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_range, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → Fin blocks → Fin length → E := fun x j k =>
    x ⟨j * length + k, by
      simp only [S, Finset.mem_range]
      calc
        j * length + k < j * length + length :=
          Nat.add_lt_add_left k.isLt _
        _ = (j + 1) * length := by
          simp only [Nat.succ_mul]
        _ ≤ blocks * length := Nat.mul_le_mul_right length
          (Nat.succ_le_iff.mpr j.isLt)
    ⟩
  let right : (T → E) → Fin length → E := fun x k =>
    x ⟨blocks * length + k, by
      simp only [T, Finset.mem_Ico]
      constructor
      · exact Nat.le_add_right _ _
      · calc
          blocks * length + k < blocks * length + length :=
            Nat.add_lt_add_left k.isLt _
          _ = (blocks + 1) * length := by
            simp only [Nat.succ_mul]
    ⟩
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro j
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have hrightMeasurable : Measurable right := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have h := htuple.comp hleftMeasurable hrightMeasurable
  have hleft : left ∘ (fun increment (k : S) => increment k) =
      (fun increment (j : Fin blocks) =>
        blockCoordinates (j * length) length increment) := by
    funext increment j k
    simp only [left, Function.comp_apply, blockCoordinates]
  have hright : right ∘ (fun increment (k : T) => increment k) =
      blockCoordinates (blocks * length) length := by
    funext increment k
    simp only [right, Function.comp_apply, blockCoordinates]
  simpa only [hleft, hright] using h

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- Any finite family of consecutive coordinate blocks of an IID sequence is
mutually independent.  Each coordinate block is retained as a finite path,
so measurable events depending on the whole block can be factored. -/
theorem iIndepFun_consecutiveBlockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      blockCoordinates (j * length) length increment) (iidSequenceLaw ν) := by
  induction blocks with
  | zero => exact iIndepFun.of_subsingleton
  | succ blocks ih =>
      apply iIndepFun.finSucc
      · intro j
        exact (blockCoordinates_measurable (j * length) length).aemeasurable
      · simpa using ih
      · simpa using indepFun_consecutiveBlockCoordinates_next ν blocks length

/-- The vector of the first `blocks` consecutive block sums is independent
of the following block sum. This form supports induction over a finite time
partition without imposing finiteness on the full increment path. -/
theorem indepFun_consecutiveBlockSums_next
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    IndepFun
      (fun increment (j : Fin blocks) =>
        blockSum (j * length) length increment)
      (blockSum (blocks * length) length)
      (iidSequenceLaw ν) := by
  classical
  let S := Finset.range (blocks * length)
  let T := Finset.Ico (blocks * length) ((blocks + 1) * length)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_range, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → (Fin blocks → E) := fun x j =>
    ∑ k : S, if j * length ≤ (k : ℕ) ∧ (k : ℕ) < (j + 1) * length
      then x k else 0
  let right : (T → E) → E := fun x => ∑ k : T, x k
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro j
    exact Finset.measurable_sum Finset.univ fun k _ => by
      split_ifs <;> fun_prop
  have hrightMeasurable : Measurable right := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_pi_apply k)
  have h := htuple.comp hleftMeasurable hrightMeasurable
  have hleft :
      left ∘ (fun increment (k : S) => increment k) =
        fun increment (j : Fin blocks) =>
          blockSum (j * length) length increment := by
    funext increment j
    simp only [left, Function.comp_apply, blockSum]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp only [Finset.mem_Ico]
      simpa [Nat.add_mul] using hk
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      have hj : (j : ℕ) < blocks := j.isLt
      refine ⟨⟨k, ?_⟩, ?_, rfl⟩
      · simp only [Finset.mem_Ico] at hk
        simp only [S, Finset.mem_range]
        exact lt_of_lt_of_le (by simpa [Nat.add_mul] using hk.2)
          (Nat.mul_le_mul_right length (Nat.succ_le_iff.2 hj))
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [Finset.mem_Ico] at hk
        simpa [Nat.add_mul] using hk
    · intro k hk
      rfl
  have hright :
      right ∘ (fun increment (k : T) => increment k) =
        blockSum (blocks * length) length := by
    funext increment
    simp only [right, Function.comp_apply, blockSum]
    simpa [T, Nat.add_mul] using
      (Finset.sum_attach
        (Finset.Ico (blocks * length) ((blocks + 1) * length)) increment)
  simpa only [hleft, hright] using h

/-- Any finite family of consecutive equal-length block sums is mutually
independent under the canonical IID increment law. -/
theorem iIndepFun_consecutiveBlockSums
    (ν : Measure E) [IsProbabilityMeasure ν]
    (blocks length : ℕ) :
    iIndepFun (fun (j : Fin blocks) increment =>
      blockSum (j * length) length increment) (iidSequenceLaw ν) := by
  induction blocks with
  | zero => exact iIndepFun.of_subsingleton
  | succ blocks ih =>
      apply iIndepFun.finSucc
      · intro j
        exact (blockSum_measurable (j * length) length).aemeasurable
      · simpa using ih
      · simpa using indepFun_consecutiveBlockSums_next ν blocks length

end ProbabilityTheory.RandomWalk
