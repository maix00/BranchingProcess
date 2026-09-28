import Probability.BranchingRandomWalk.Walk.Path.Martingale
import Probability.Independence.Moment.Fourth

/-!
# Fourth moments of IID random-walk sums
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Exact one-step recurrence for the fourth moment of centered IID partial
sums. -/
theorem integral_partialSum_succ_pow_four_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem4 : MemLp id 4 ν) (hcentered : ∫ x, x ∂ν = 0) (n : ℕ) :
    (∫ path : ℕ → ℝ, partialSum (n + 1) path ^ 4 ∂iidSequenceLaw ν) =
      (∫ path : ℕ → ℝ, partialSum n path ^ 4 ∂iidSequenceLaw ν) +
        6 * ((n : ℝ) * ∫ x, x ^ 2 ∂ν) * (∫ x, x ^ 2 ∂ν) +
        ∫ x, x ^ 4 ∂ν := by
  let P := iidSequenceLaw ν
  let coordinate : ℕ → (ℕ → ℝ) → ℝ := fun k path => path k
  let S : (ℕ → ℝ) → ℝ := fun path => partialSum n path
  have hcoordLaw (k : ℕ) : HasLaw (coordinate k) ν P :=
    ⟨(measurable_pi_apply k).aemeasurable, iidSequenceLaw_map_apply ν k⟩
  have hcoordMem (k : ℕ) : MemLp (coordinate k) 4 P :=
    (hcoordLaw k).memLp hmem4
  have hS_eq : S = ∑ k ∈ Finset.range n, coordinate k := by
    funext path
    simp [S, coordinate, partialSum]
  have hSMem : MemLp S 4 P := by
    rw [hS_eq]
    exact memLp_finsetSum' _ fun k _ => hcoordMem k
  have hSmeas : Measurable S := by
    exact Finset.measurable_sum (Finset.range n)
      (fun k _ => measurable_pi_apply k)
  have hSne : n ∉ Finset.range n := by simp
  have hIndep : S ⟂ᵢ[P] coordinate n := by
    rw [hS_eq]
    exact (iidSequenceLaw_independent ν).indepFun_finsetSum_of_notMem
      (fun k => measurable_pi_apply k) hSne
  have hcoordMean (k : ℕ) : ∫ path, coordinate k path ∂P = 0 := by
    rw [(hcoordLaw k).integral_eq, hcentered]
  have hSMean : ∫ path, S path ∂P = 0 := by
    change ∫ path, ∑ k ∈ Finset.range n, coordinate k path ∂P = 0
    rw [integral_finsetSum]
    · simp [hcoordMean]
    · intro k hk
      exact (hcoordMem k).integrable (by norm_num)
  have hcoord2 :
      (∫ path, coordinate n path ^ 2 ∂P) = ∫ x, x ^ 2 ∂ν := by
    simpa [Function.comp_def] using
      (hcoordLaw n).integral_comp
        (measurable_id.pow_const 2).aestronglyMeasurable
  have hcoord4 :
      (∫ path, coordinate n path ^ 4 ∂P) = ∫ x, x ^ 4 ∂ν := by
    simpa [Function.comp_def] using
      (hcoordLaw n).integral_comp
        (measurable_id.pow_const 4).aestronglyMeasurable
  have hmem2 : MemLp id 2 ν := hmem4.mono_exponent (by norm_num)
  have hS2 : (∫ path, S path ^ 2 ∂P) =
      (n : ℝ) * ∫ x, x ^ 2 ∂ν := by
    cases n with
    | zero => simp [S, partialSum]
    | succ k =>
        have h := integral_sq_partialSumProcess_iidSequenceLaw
          ν hmem2 hcentered k
        rw [variance_of_integral_eq_zero measurable_id.aemeasurable hcentered] at h
        simpa [S, P, partialSumProcess, Nat.cast_add, Nat.cast_one] using h
  have hfourth := hIndep.integral_add_pow_four_of_centered
    hSmeas (measurable_pi_apply n) hSMem (hcoordMem n) hSMean (hcoordMean n)
  rw [show (fun path : ℕ → ℝ => partialSum (n + 1) path ^ 4) =
      fun path => (S path + coordinate n path) ^ 4 by
    funext path
    rw [partialSum_succ]]
  change (∫ path, (S path + coordinate n path) ^ 4 ∂P) = _
  rw [hfourth, hS2, hcoord2, hcoord4]

/-- Exact fourth moment of a centered IID partial sum. -/
theorem integral_partialSum_pow_four_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem4 : MemLp id 4 ν) (hcentered : ∫ x, x ∂ν = 0) (n : ℕ) :
    (∫ path : ℕ → ℝ, partialSum n path ^ 4 ∂iidSequenceLaw ν) =
      (n : ℝ) * (∫ x, x ^ 4 ∂ν) +
        3 * (n : ℝ) * ((n : ℝ) - 1) * (∫ x, x ^ 2 ∂ν) ^ 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [integral_partialSum_succ_pow_four_iidSequenceLaw
        ν hmem4 hcentered n, ih]
      push_cast
      ring

/-- A convenient upper bound obtained from the exact fourth-moment formula. -/
theorem integral_partialSum_pow_four_iidSequenceLaw_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem4 : MemLp id 4 ν) (hcentered : ∫ x, x ∂ν = 0) (n : ℕ) :
    (∫ path : ℕ → ℝ, partialSum n path ^ 4 ∂iidSequenceLaw ν) ≤
      (n : ℝ) * (∫ x, x ^ 4 ∂ν) +
        3 * (n : ℝ) ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2 := by
  rw [integral_partialSum_pow_four_iidSequenceLaw ν hmem4 hcentered n]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hm : 0 ≤ (∫ x, x ^ 2 ∂ν) ^ 2 := sq_nonneg _
  nlinarith

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
