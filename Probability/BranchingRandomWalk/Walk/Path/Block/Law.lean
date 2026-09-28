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

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
