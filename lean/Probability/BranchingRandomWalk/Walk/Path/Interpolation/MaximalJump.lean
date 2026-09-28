import Probability.BranchingRandomWalk.Walk.Path.Interpolation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real

/-!
# Maximal increments of an IID walk

This file contains the probability estimates needed to compare the step and
polygonal realizations of a random walk.  The estimates concern only the
increment process; the deterministic interpolation bound remains in the
combinatorial layer.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- The probability that one of the first `n + 1` IID increments exceeds a
threshold is at most `(n + 1)` times the corresponding one-step tail
probability. -/
theorem independentIncrementLaw_maxAbsUpTo_ge_le
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (threshold : ℝ) :
    (independentIncrementLaw nu).real
        {increment | threshold ≤ maxAbsUpTo n increment} ≤
      (n + 1 : ℝ) * nu.real {x | threshold ≤ |x|} := by
  let event : ℕ → Set (ℕ → ℝ) :=
    fun k => {increment | threshold ≤ |increment k|}
  have hevent :
      {increment | threshold ≤ maxAbsUpTo n increment} =
        ⋃ k ∈ Finset.range (n + 1), event k := by
    ext increment
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, event]
    unfold maxAbsUpTo
    rw [Finset.le_sup'_iff]
    simp only [Finset.mem_range]
    aesop
  rw [hevent]
  refine (measureReal_biUnion_finset_le (Finset.range (n + 1)) event).trans ?_
  have hcoordinate (k : ℕ) :
      (independentIncrementLaw nu).real (event k) =
        nu.real {x | threshold ≤ |x|} := by
    have hset : MeasurableSet {x : ℝ | threshold ≤ |x|} :=
      measurableSet_Ici.preimage measurable_abs
    change (independentIncrementLaw nu).real
        ((fun increment : ℕ → ℝ => increment k) ⁻¹' {x | threshold ≤ |x|}) = _
    apply congrArg ENNReal.toReal
    calc
      independentIncrementLaw nu
          ((fun increment : ℕ → ℝ => increment k) ⁻¹' {x | threshold ≤ |x|}) =
          (independentIncrementLaw nu).map
            (fun increment => increment k) {x | threshold ≤ |x|} :=
        (Measure.map_apply (measurable_pi_apply k) hset).symm
      _ = nu {x | threshold ≤ |x|} := by
        rw [independentIncrementLaw_coordinate nu k]
  simp_rw [hcoordinate]
  simp [Nat.cast_add, Nat.cast_one]

/-- The part of an integrable nonnegative function above a threshold tending
to infinity has integral tending to zero. -/
theorem tendsto_integral_indicator_threshold_le_zero
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : Integrable f mu) (hf_nonneg : 0 ≤ f)
    (threshold : ℕ → ℝ) (hthreshold : Tendsto threshold atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x, {x | threshold n ≤ f x}.indicator f x ∂mu)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) :
      AEStronglyMeasurable ({x | threshold n ≤ f x}.indicator f) mu := by
    exact hf.aestronglyMeasurable.indicator₀
      (hf.aemeasurable.nullMeasurable measurableSet_Ici)
  have hbound (n : ℕ) : ∀ᵐ x ∂mu,
      ‖{x | threshold n ≤ f x}.indicator f x‖ ≤ f x := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    by_cases hx : threshold n ≤ f x
    · rw [Set.indicator_of_mem (show x ∈ {y | threshold n ≤ f y} from hx),
        abs_of_nonneg (hf_nonneg x)]
    · rw [Set.indicator_of_notMem
          (show x ∉ {y | threshold n ≤ f y} from hx), abs_zero]
      exact hf_nonneg x
  have hlim : ∀ᵐ x ∂mu,
      Tendsto (fun n : ℕ => {x | threshold n ≤ f x}.indicator f x)
        atTop (nhds 0) := by
    filter_upwards [] with x
    have heventually' : ∀ᶠ n in atTop, f x + 1 ≤ threshold n :=
      tendsto_atTop.1 hthreshold (f x + 1)
    have heventually : ∀ᶠ n in atTop, f x < threshold n := by
      filter_upwards [heventually'] with n hn
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards [heventually] with n hn
    rw [Set.indicator_of_notMem]
    exact not_le_of_gt hn
  simpa using (tendsto_integral_of_dominated_convergence
    (f := fun _ : X => 0) f hmeas hf hbound hlim)

/-- Natural-number thresholds are a useful special case of the preceding
tail-integral lemma. -/
theorem tendsto_integral_indicator_nat_le_zero
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {f : X → ℝ} (hf : Integrable f mu) (hf_nonneg : 0 ≤ f) :
    Tendsto (fun n : ℕ => ∫ x, {x | (n : ℝ) ≤ f x}.indicator f x ∂mu)
      atTop (nhds 0) :=
  tendsto_integral_indicator_threshold_le_zero hf hf_nonneg
    (fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
