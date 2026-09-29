module

public import Probability.BranchingRandomWalk.Walk.Path.Block.Maximal
public import Probability.BranchingRandomWalk.Walk.Path.Moment.Fourth

/-!
# Fourth-moment maximal bounds on increment blocks

The IID fourth-power maximal inequality is invariant under deterministic
shifts of the increment coordinates, just as its second-moment counterpart.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Doob's fourth-power maximal inequality on a block beginning at an
arbitrary deterministic increment coordinate. -/
theorem maximal_ineq_pow_four_blockSum_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem4 : MemLp id 4 ν) (hcentered : ∫ x, x ∂ν = 0)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (blockSum start (k + 1) path) ^ 4} ≤
      ENNReal.ofReal
        (((n + 1 : ℕ) : ℝ) * (∫ x, x ^ 4 ∂ν) +
          3 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) *
            (∫ x, x ^ 2 ∂ν) ^ 2) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ :=
    fun k path => path (start + k)
  have hstrong : ∀ k, StronglyMeasurable (increment k) :=
    fun k => measurable_pi_apply (start + k) |>.stronglyMeasurable
  have hcoordLaw (k : ℕ) : HasLaw (increment k) ν (iidSequenceLaw ν) :=
    ⟨(measurable_pi_apply (start + k)).aemeasurable,
      iidSequenceLaw_map_apply ν (start + k)⟩
  have hcoordMem : ∀ k, MemLp (increment k) 4 (iidSequenceLaw ν) :=
    fun k => (hcoordLaw k).memLp hmem4
  have hcoordMean : ∀ k,
      ∫ path, increment k path ∂iidSequenceLaw ν = 0 := by
    intro k
    rw [(hcoordLaw k).integral_eq, hcentered]
  have hinjective : Function.Injective (fun k : ℕ => start + k) :=
    fun _ _ => Nat.add_left_cancel
  have hindep : iIndepFun increment (iidSequenceLaw ν) :=
    (iidSequenceLaw_independent ν).precomp hinjective
  have hmax := maximal_ineq_pow_four_partialSumProcess increment hstrong
    hcoordMem hcoordMean hindep ε n
  have hterminal :
      (∫ path, (partialSumProcess increment n path) ^ 4
          ∂iidSequenceLaw ν) =
        (((n + 1 : ℕ) : ℝ) * (∫ x, x ^ 4 ∂ν) +
          3 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) *
            (∫ x, x ^ 2 ∂ν) ^ 2) := by
    let shift : (ℕ → ℝ) → (ℕ → ℝ) :=
      fun path k => path (start + k)
    have hshiftMeas : Measurable shift :=
      Measurable.of_eval fun k => measurable_pi_apply (start + k)
    have hpartialMeas : Measurable (fun path : ℕ → ℝ =>
        partialSum (n + 1) path ^ 4) :=
      (Finset.measurable_sum (Finset.range (n + 1))
        (fun k _ => measurable_pi_apply k)).pow_const 4
    have hmapIntegral :
        (∫ path, partialSum (n + 1) (shift path) ^ 4
          ∂iidSequenceLaw ν) =
          ∫ path, partialSum (n + 1) path ^ 4 ∂iidSequenceLaw ν := by
      calc
        _ = ∫ path, partialSum (n + 1) path ^ 4
              ∂(iidSequenceLaw ν).map shift := by
          symm
          exact integral_map hshiftMeas.aemeasurable
            hpartialMeas.aestronglyMeasurable
        _ = _ := by rw [iidSequenceLaw_map_natAdd ν start]
    rw [integral_partialSum_pow_four_iidSequenceLaw
      ν hmem4 hcentered (n + 1)] at hmapIntegral
    simpa [increment, partialSumProcess, shift,
      blockSum_eq_partialSum_natAdd] using hmapIntegral
  simpa [increment, partialSumProcess,
    blockSum_eq_partialSum_natAdd] using hmax.trans_eq
      (congrArg ENNReal.ofReal hterminal)

end ProbabilityTheory.RandomWalk
