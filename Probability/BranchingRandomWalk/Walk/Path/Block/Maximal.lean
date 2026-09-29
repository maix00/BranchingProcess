import Probability.BranchingRandomWalk.Walk.Path.Block.Law
import Probability.BranchingRandomWalk.Walk.Path.Martingale

/-!
# Maximal inequalities on increment blocks

The IID maximal bound is invariant under every deterministic shift of the
increment coordinates.  This file states the resulting estimate directly in
terms of `blockSum`, the deterministic block operation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Doob's squared maximal inequality on a block beginning at an arbitrary
deterministic increment coordinate. -/
theorem maximal_ineq_sq_blockSum_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν)
    (hcentered : ∫ x, x ∂ν = 0)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal ((n + 1 : ℕ) * variance id ν) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ :=
    fun k path => path (start + k)
  have hstrong : ∀ k, StronglyMeasurable (increment k) :=
    fun k => measurable_pi_apply (start + k) |>.stronglyMeasurable
  have hcoordLaw (k : ℕ) : HasLaw (increment k) ν (iidSequenceLaw ν) :=
    ⟨(measurable_pi_apply (start + k)).aemeasurable,
      iidSequenceLaw_map_apply ν (start + k)⟩
  have hcoordMem : ∀ k, MemLp (increment k) 2 (iidSequenceLaw ν) :=
    fun k => (hcoordLaw k).memLp hmem
  have hcoordMean : ∀ k,
      ∫ path, increment k path ∂iidSequenceLaw ν = 0 := by
    intro k
    rw [(hcoordLaw k).integral_eq, hcentered]
  have hinjective : Function.Injective (fun k : ℕ => start + k) :=
    fun _ _ => Nat.add_left_cancel
  have hindep : iIndepFun increment (iidSequenceLaw ν) :=
    (iidSequenceLaw_independent ν).precomp hinjective
  have hmax := maximal_ineq_sq_partialSumProcess increment hstrong
    hcoordMem hcoordMean hindep ε n
  rw [integral_sq_partialSumProcess increment hcoordMem hcoordMean hindep n]
    at hmax
  simp_rw [(hcoordLaw _).variance_eq] at hmax
  simpa [increment, partialSumProcess,
    blockSum_eq_partialSum_natAdd] using hmax

end ProbabilityTheory.RandomWalk
