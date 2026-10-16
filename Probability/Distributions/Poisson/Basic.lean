/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Poisson Distribution: Expectation and Variance

This file collects moment and integral identities for the Poisson distribution with rate `r`,
along with the degenerate zero-rate case. Mathlib already provides the characteristic function
and convolution identities for Poisson measures.

## Main results

* `ProbabilityTheory.poissonExpectation_hasSum` — E[X] = r
* `ProbabilityTheory.poissonVariance` — Var[X] = r
* `ProbabilityTheory.integrable_id_poissonMeasure` — the identity `n ↦ n` is integrable against
  `poissonMeasure r`
* `ProbabilityTheory.integral_id_poissonMeasure`, `ProbabilityTheory.integral_factorialMoment_poissonMeasure`
  — the mean and second factorial moment as Bochner integrals against `poissonMeasure r`
* `ProbabilityTheory.poissonMeasure_zero` — the zero-rate law is the Dirac mass at `0`

## Implementation notes

All three proofs follow the same pattern: strip off the first few zero terms via
`hasSum_nat_add_iff'`, simplify the shifted summand using `Nat.factorial_succ`, and
reduce to `hasSum_poissonMeasure_real` (the normalization identity
`∑ (poissonMeasure r).real {n} = 1`), obtained via mathlib's `poissonMeasure`/`.real {n}` atoms.

-/

@[expose] public section

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset

namespace ProbabilityTheory

/-! ## PMF bridge lemmas -/

/-- The real-valued Poisson point masses `n ↦ Po(r).real {n}` are summable to `1`. -/
lemma hasSum_poissonMeasure_real (r : ℝ≥0) :
    HasSum (fun n ↦ (poissonMeasure r).real {n}) 1 := by
  simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r

/-- The real-valued Poisson point masses are summable. -/
lemma summable_poissonMeasure_real (r : ℝ≥0) :
    Summable (fun n ↦ (poissonMeasure r).real {n}) :=
  (hasSum_poissonMeasure_real r).summable

/-! ## Expectation: E[X] = r -/

/-- The key algebraic identity: `(n+1) * Po(r).real {n+1} = r * Po(r).real {n}`. -/
private lemma expectation_shift (r : ℝ≥0) (n : ℕ) :
    ↑(n + 1) * (poissonMeasure r).real {n + 1} = (r : ℝ) * (poissonMeasure r).real {n} := by
  simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  field_simp

/-- **Poisson expectation (HasSum form):** `∑ n * P(X = n) = r`. -/
theorem poissonExpectation_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ↑n * (poissonMeasure r).real {n}) (r : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  simp_rw [expectation_shift]
  simpa [mul_one] using (hasSum_poissonMeasure_real r).mul_left (r : ℝ)

/-! ## Variance: Var[X] = r -/

/-- Algebraic identity for the factorial moment shift:
`(n+2)(n+1) * (poissonMeasure r).real {n+2} = r² * (poissonMeasure r).real {n}`. -/
private lemma factorial_moment_shift (r : ℝ≥0) (n : ℕ) :
    (↑(n + 2) : ℝ) * ↑(n + 1) * (poissonMeasure r).real {n + 2} =
    (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
  simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h3 : (↑(n + 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Second factorial moment:** `∑ n(n-1) * P(X = n) = r²`. -/
theorem poissonFactorialMoment2_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) * (↑n - 1)) * (poissonMeasure r).real {n}) ((r : ℝ) ^ 2) := by
  apply (hasSum_nat_add_iff' 2).mp
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, zero_add, sub_self, mul_zero, sub_zero]
  have key : ∀ n : ℕ, ((↑(n + 2) : ℝ) * (↑(n + 2) - 1)) * (poissonMeasure r).real {n + 2} =
      (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    intro n
    have : (↑(n + 2) : ℝ) - 1 = ↑(n + 1) := by push_cast; ring
    rw [this]
    exact factorial_moment_shift r n
  simp_rw [key]
  simpa [mul_one] using (hasSum_poissonMeasure_real r).mul_left ((r : ℝ) ^ 2)

/-- **Second moment:** `∑ n² * P(X = n) = r² + r`. -/
theorem poissonSecondMoment_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ (↑n : ℝ) ^ 2 * (poissonMeasure r).real {n}) ((r : ℝ) ^ 2 + r) := by
  have h1 := poissonFactorialMoment2_hasSum r
  have h2 := poissonExpectation_hasSum r
  -- n² = n(n-1) + n, so E[X²] = E[X(X-1)] + E[X]
  convert h1.add h2 using 1
  ext n; ring

/-- **Poisson variance:** `∑ (n - r)² * P(X = n) = r`. -/
theorem poissonVariance (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) - ↑r) ^ 2 * (poissonMeasure r).real {n}) (r : ℝ) := by
  have h1 := poissonSecondMoment_hasSum r
  have h2 := poissonExpectation_hasSum r
  have h3 := hasSum_poissonMeasure_real r
  -- (n - r)² = n² - 2rn + r², so Var = E[X²] - 2r·E[X] + r²·1
  have key := (h1.sub (h2.mul_left (2 * (r : ℝ)))).add (h3.mul_left ((r : ℝ) ^ 2))
  have hval : (((r : ℝ) ^ 2 + r) - 2 * (r : ℝ) * (r : ℝ)) + (r : ℝ) ^ 2 * 1 = (r : ℝ) := by
    ring
  rw [hval] at key
  have hfun : (fun n : ℕ ↦ ((↑n : ℝ) - ↑r) ^ 2 * (poissonMeasure r).real {n}) =
      fun n : ℕ ↦ ((↑n : ℝ) ^ 2 * (poissonMeasure r).real {n} -
        2 * (r : ℝ) * ((↑n : ℝ) * (poissonMeasure r).real {n})) +
        (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    funext n; ring
  rw [hfun]
  exact key

/-! ## Moment integrals against `poissonMeasure` -/

/-- A real function on `ℕ` is integrable against `poissonMeasure r` whenever its norm,
weighted by the PMF, is summable. This is the bridge from the `HasSum` moment identities
(which give summability) to `Integrable`, unlocking `PMF.integral_eq_tsum`. -/
private lemma integrable_poissonMeasure_of_summable {r : ℝ≥0} {f : ℕ → ℝ}
    (hf : Summable fun n ↦ ‖f n‖ * (poissonMeasure r).real {n}) :
    Integrable f (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  refine hf.congr fun n ↦ ?_
  rw [poissonMeasure_real_singleton, mul_comm]

/-- **Integrability of the identity against a Poisson law:** `n ↦ n` is integrable against
`poissonMeasure r`, its first absolute moment being the mean `r` supplied by
`poissonExpectation_hasSum`. -/
theorem integrable_id_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) :=
  integrable_poissonMeasure_of_summable <|
    (poissonExpectation_hasSum r).summable.congr fun n ↦ by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]

/-- **Mean of the Poisson distribution (integral form):**
`∫ n, n ∂(poissonMeasure r) = r`. -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  refine (tsum_congr fun n ↦ ?_).trans (poissonExpectation_hasSum r).tsum_eq
  rw [poissonMeasure_real_singleton]; ring

/-- **ENNReal mean of the Poisson distribution:** the lintegral of the identity is its rate. -/
theorem lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = (r : ℝ≥0∞) := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_id_poissonMeasure r)
    (Filter.Eventually.of_forall fun n : ℕ => Nat.cast_nonneg n)
  rw [integral_id_poissonMeasure r] at h
  simpa using h.symm

/-- **Second factorial moment of the Poisson distribution (integral form):**
`∫ n, n(n - 1) ∂(poissonMeasure r) = r²`. -/
theorem integral_factorialMoment_poissonMeasure (r : ℝ≥0) :
    ∫ n, ((n : ℝ) * ((n : ℝ) - 1)) ∂(poissonMeasure r) = (r : ℝ) ^ 2 := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  refine (tsum_congr fun n ↦ ?_).trans (poissonFactorialMoment2_hasSum r).tsum_eq
  rw [poissonMeasure_real_singleton]; ring

/-! ## Degenerate rate -/

/-- At rate `0` the Poisson distribution is a point mass at `0`. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  rw [poissonMeasure_singleton, Measure.dirac_apply' 0 (measurableSet_singleton n)]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, NNReal.coe_zero]
    rw [ite_eq_right (fun h ↦ hn h.symm)]
    simp [zero_pow hn]

/-! ## Poisson convolution -/

/-- Singleton-level Poisson convolution: the convolution sum at a single point. -/
theorem poissonMeasure_conv_singleton (a b : ℝ≥0) (m : ℕ) :
    (∑' n : ℕ, if n ≤ m then poissonMeasure a {n} * poissonMeasure b {m - n} else 0) =
    poissonMeasure (a + b) {m} := by
  have hpc := poissonMeasure_conv_poissonMeasure a b
  -- Evaluate both sides at {m}
  have hpc' : ((poissonMeasure a).prod (poissonMeasure b)).map
      (fun p : ℕ × ℕ => p.1 + p.2) {m} = poissonMeasure (a + b) {m} := by
    change (poissonMeasure a ∗ poissonMeasure b) {m} = _
    rw [poissonMeasure_conv_poissonMeasure]
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton m)] at hpc'
  rw [← hpc']
  -- Express preimage as disjoint union of singletons {(n, m-n)}
  have hfib : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {m} =
      ⋃ n : ℕ, if n ≤ m then {⟨n, m - n⟩} else ∅ := by
    ext ⟨a', b'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hab; exact ⟨a', by rw [ite_eq_left (by omega)]; ext <;> simp; omega⟩
    · rintro ⟨n, hn⟩
      by_cases hle : n ≤ m
      · rw [ite_eq_left hle] at hn; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hn; omega
      · rw [ite_eq_right hle] at hn; exact absurd hn (by simp)
  rw [hfib, measure_iUnion₀
    (by intro i j hij; simp only [Function.onFun, AEDisjoint]
        by_cases hi : i ≤ m
        · by_cases hj : j ≤ m
          · rw [ite_eq_left hi, ite_eq_left hj]
            exact (Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).1)).aedisjoint
          · rw [ite_eq_right hj]; simp
        · rw [ite_eq_right hi]; simp)
    (by intro n; by_cases hn : n ≤ m
        · rw [ite_eq_left hn]; exact (measurableSet_singleton _).nullMeasurableSet
        · rw [ite_eq_right hn]; exact MeasurableSet.empty.nullMeasurableSet)]
  congr 1; ext n
  by_cases hn : n ≤ m
  · rw [ite_eq_left hn, ite_eq_left hn,
      show ({⟨n, m - n⟩} : Set (ℕ × ℕ)) = {n} ×ˢ {m - n} from (Set.singleton_prod_singleton).symm,
      Measure.prod_prod]
  · rw [ite_eq_right hn, ite_eq_right hn, measure_empty]

end ProbabilityTheory
