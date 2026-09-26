import Probability.BranchingRandomWalk.PointProcess.PointMeasure
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Finite truncations of the spine weight

The full child weight is a countable `ENNReal` sum.  This file records
the measurable finite truncations used before applying monotone convergence.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



noncomputable def truncatedChildWeight (n : ℕ) (ξ : NatRealStep) : ENNReal :=
  by
    classical
    exact ∑ i ∈ Finset.range n, if survive ξ i then
      ENNReal.ofReal (Real.exp (-value' ξ i)) else 0

theorem truncatedChildWeight_measurable (n : ℕ) :
    Measurable (truncatedChildWeight n) := by
  classical
  unfold truncatedChildWeight
  apply Finset.measurable_sum
  intro i hi
  have hval : Measurable (fun ξ : NatRealStep =>
      ENNReal.ofReal (Real.exp (-value' ξ i))) :=
    ENNReal.measurable_ofReal.comp
      ((value'_measurable i).neg.exp)
  exact hval.ite (survive_measurableSet i) measurable_const

theorem truncatedChildWeight_mono {n : ℕ} (ξ : NatRealStep) :
    truncatedChildWeight n ξ ≤ truncatedChildWeight (n + 1) ξ := by
  classical
  unfold truncatedChildWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (Nat.le_succ n)
  · intro i hi hnot
    positivity

theorem truncatedChildWeight_eq_finset_sum (n : ℕ) (ξ : NatRealStep) :
    truncatedChildWeight n ξ =
      ∑ i ∈ Finset.range n, realizedChildWeight ξ i := by
  rfl

theorem truncatedChildWeight_le_total (n : ℕ) (ξ : NatRealStep) :
    truncatedChildWeight n ξ ≤ totalChildWeight ξ := by
  rw [truncatedChildWeight_eq_finset_sum]
  exact ENNReal.sum_le_tsum (Finset.range n)

theorem truncatedChildWeight_iSup (ξ : NatRealStep) :
    ⨆ n : ℕ, truncatedChildWeight n ξ = totalChildWeight ξ := by
  apply le_antisymm
  · refine iSup_le fun n => truncatedChildWeight_le_total n ξ
  · apply ENNReal.tsum_le_of_sum_range_le
    intro n
    exact le_iSup (fun k : ℕ => truncatedChildWeight k ξ) n

end ProbabilityTheory.BranchingRandomWalk.Spine
