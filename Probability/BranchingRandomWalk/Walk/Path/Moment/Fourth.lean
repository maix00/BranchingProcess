import Probability.BranchingRandomWalk.Walk.Path.Martingale
import Probability.Independence.Moment.Fourth

/-!
# Fourth moments of IID random-walk sums
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Fourth powers of partial sums of centered independent `L⁴` increments
form a nonnegative submartingale. -/
theorem submartingale_pow_four_partialSumProcess
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (increment : ℕ → Ω → ℝ)
    (hstrong : ∀ n, StronglyMeasurable (increment n))
    (hmem : ∀ n, MemLp (increment n) 4 μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) :
    Submartingale (fun n ω => (partialSumProcess increment n ω) ^ 4)
      (Filtration.natural increment hstrong) μ := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hmartingale := martingale_partialSumProcess increment hstrong
    (fun n => (hmem n).integrable (by norm_num)) hcentered hindep
  refine hmartingale.submartingale_convex_comp
    (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4) from
      (show Even (4 : ℕ) by decide).convexOn_pow)
    (by fun_prop) ?_
  intro n
  have hsum : MemLp (partialSumProcess increment n) 4 μ := by
    rw [show partialSumProcess increment n =
        ∑ k ∈ Finset.range (n + 1), increment k by
      funext ω
      simp [partialSumProcess, partialSum]]
    exact memLp_finsetSum' _ fun k _ => hmem k
  refine (hsum.integrable_norm_pow (by norm_num)).congr ?_
  filter_upwards [] with ω
  change |partialSumProcess increment n ω| ^ 4 =
    partialSumProcess increment n ω ^ 4
  calc
    |partialSumProcess increment n ω| ^ 4 =
        (|partialSumProcess increment n ω| ^ 2) ^ 2 := by ring
    _ = (partialSumProcess increment n ω ^ 2) ^ 2 := by rw [sq_abs]
    _ = partialSumProcess increment n ω ^ 4 := by ring

/-- Doob's maximal inequality for fourth powers of centered independent
partial sums. -/
theorem maximal_ineq_pow_four_partialSumProcess
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (increment : ℕ → Ω → ℝ)
    (hstrong : ∀ n, StronglyMeasurable (increment n))
    (hmem : ∀ n, MemLp (increment n) 4 μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) (ε : ℝ≥0) (n : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (partialSumProcess increment k ω) ^ 4} ≤
      ENNReal.ofReal
        (∫ ω, (partialSumProcess increment n ω) ^ 4 ∂μ) := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hsub := submartingale_pow_four_partialSumProcess increment hstrong
    hmem hcentered hindep
  calc
    _ ≤ ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              fun k => (partialSumProcess increment k ω) ^ 4},
          (partialSumProcess increment n ω) ^ 4 ∂μ) :=
      MeasureTheory.maximal_ineq hsub
        (fun _ _ => by positivity) n
    _ ≤ ENNReal.ofReal
        (∫ ω, (partialSumProcess increment n ω) ^ 4 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral (hsub.integrable n)
        (Filter.Eventually.of_forall fun _ => by positivity)

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

/-- IID specialization of the fourth-power maximal inequality, with its
terminal fourth moment evaluated explicitly. -/
theorem maximal_ineq_pow_four_partialSumProcess_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem4 : MemLp id 4 ν) (hcentered : ∫ x, x ∂ν = 0)
    (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (partialSumProcess (fun j path => path j) k path) ^ 4} ≤
      ENNReal.ofReal
        (((n + 1 : ℕ) : ℝ) * (∫ x, x ^ 4 ∂ν) +
          3 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) *
            (∫ x, x ^ 2 ∂ν) ^ 2) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ := fun k path => path k
  have hstrong : ∀ k, StronglyMeasurable (increment k) :=
    fun k => measurable_pi_apply k |>.stronglyMeasurable
  have hcoordLaw (k : ℕ) : HasLaw (increment k) ν (iidSequenceLaw ν) :=
    ⟨(measurable_pi_apply k).aemeasurable,
      iidSequenceLaw_map_apply ν k⟩
  have hcoordMem : ∀ k, MemLp (increment k) 4 (iidSequenceLaw ν) :=
    fun k => (hcoordLaw k).memLp hmem4
  have hcoordMean : ∀ k,
      ∫ path, increment k path ∂iidSequenceLaw ν = 0 := by
    intro k
    rw [(hcoordLaw k).integral_eq, hcentered]
  have hmax := maximal_ineq_pow_four_partialSumProcess increment hstrong
    hcoordMem hcoordMean (iidSequenceLaw_independent ν) ε n
  have hterminal := integral_partialSum_pow_four_iidSequenceLaw
    ν hmem4 hcentered (n + 1)
  simpa [increment, partialSumProcess] using hmax.trans_eq
    (congrArg ENNReal.ofReal hterminal)


end ProbabilityTheory.BranchingRandomWalk.RandomWalk
