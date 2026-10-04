/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Sequence.IID
public import BrownianMotion.Auxiliary.Martingale
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Moments.Variance

/-!
# Partial-sum martingales

Centered independent real increments generate a martingale of partial sums
with respect to their natural filtration. The underlying partial-sum operation
remains in the deterministic walk layer.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The partial-sum process aligned with the natural filtration: at time `n`
it contains increments `0, ..., n`. -/
def partialSumProcess (increment : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  AdditivePath.displacement (n + 1) (fun k => increment k ω)

/-- Partial sums of centered mutually independent integrable increments form
a martingale with respect to the increments' natural filtration. -/
theorem martingale_partialSumProcess
    (increment : ℕ → Ω → ℝ)
    (hstrong : ∀ n, StronglyMeasurable (increment n))
    (hint : ∀ n, Integrable (increment n) μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) :
    Martingale (partialSumProcess increment)
      (Filtration.natural increment hstrong) μ := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  let ℱ := Filtration.natural increment hstrong
  have hadapt : StronglyAdapted ℱ (partialSumProcess increment) := by
    intro n
    rw [show partialSumProcess increment n =
        ∑ k ∈ Finset.range (n + 1), increment k by
      funext ω
      simp [partialSumProcess, AdditivePath.displacement]]
    exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun k hk =>
      (Filtration.stronglyAdapted_natural hstrong k).mono
        (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  refine ⟨hadapt, fun i j hij => ?_⟩
  rw [show partialSumProcess increment j =
      ∑ k ∈ Finset.range (j + 1), increment k by
    funext ω
    simp [partialSumProcess, AdditivePath.displacement]]
  refine (condExp_finsetSum (fun k _ => hint k) _).trans ?_
  rw [show partialSumProcess increment i =
      ∑ k ∈ Finset.range (i + 1), increment k by
    funext ω
    simp [partialSumProcess, AdditivePath.displacement]]
  have hcoord (k : ℕ) :
      μ[increment k | ℱ i] =ᵐ[μ]
        if k ≤ i then increment k else 0 := by
    by_cases hki : k ≤ i
    · simp only [hki, ↓reduceIte]
      have hmeas : StronglyMeasurable[ℱ i] (increment k) :=
        (Filtration.stronglyAdapted_natural hstrong k).mono (ℱ.mono hki)
      rw [condExp_of_stronglyMeasurable (ℱ.le i) hmeas (hint k)]
    · simp only [hki, ↓reduceIte]
      have hik : i < k := Nat.lt_of_not_ge hki
      exact (hindep.condExp_natural_ae_eq_of_lt hstrong hik).trans
        (Filter.Eventually.of_forall fun _ => by simp [hcentered k])
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range (j + 1),
      μ[increment k | Filtration.natural increment hstrong i] ω) =
    ∑ k ∈ Finset.range (i + 1), increment k ω
  rw [Finset.sum_congr rfl fun k _ => hω k]
  simp only [ite_apply, Pi.zero_apply]
  rw [show (∑ k ∈ Finset.range (j + 1),
      if k ≤ i then increment k ω else 0) =
      ∑ k ∈ Finset.range (i + 1), increment k ω by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega]

/-- Under the canonical i.i.d. path law, integrability and centering need only
be checked for the common one-step law. -/
theorem martingale_partialSumProcess_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hintegrable : Integrable id ν)
    (hcentered : ∫ x, x ∂ν = 0) :
    Martingale
      (partialSumProcess (fun n (increment : ℕ → ℝ) => increment n))
      (Filtration.natural (fun n (increment : ℕ → ℝ) => increment n)
        (fun _ => measurable_pi_apply _ |>.stronglyMeasurable))
      (iidSequenceLaw ν) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ := fun n path => path n
  have hstrong : ∀ n, StronglyMeasurable (increment n) :=
    fun n => measurable_pi_apply n |>.stronglyMeasurable
  have hint : ∀ n, Integrable (increment n) (iidSequenceLaw ν) := by
    intro n
    let eval : (ℕ → ℝ) → ℝ := fun increment => increment n
    have hp : MeasurePreserving eval (iidSequenceLaw ν) ν :=
      ⟨measurable_pi_apply n, iidSequenceLaw_map_apply ν n⟩
    simpa [eval, Function.comp_def] using
      hp.integrable_comp_of_integrable hintegrable
  have hmean : ∀ n, ∫ path, increment n path ∂iidSequenceLaw ν = 0 := by
    intro n
    calc
      (∫ path : ℕ → ℝ, path n ∂iidSequenceLaw ν) =
          ∫ x, x ∂(iidSequenceLaw ν).map (fun path => path n) :=
        (integral_map_of_stronglyMeasurable
          (μ := iidSequenceLaw ν) (φ := fun path : ℕ → ℝ => path n)
          (f := id) (measurable_pi_apply n) stronglyMeasurable_id).symm
      _ = ∫ x, x ∂ν := by rw [iidSequenceLaw_map_apply ν n]
      _ = 0 := hcentered
  simpa only [increment] using martingale_partialSumProcess
    increment hstrong hint hmean (iidSequenceLaw_independent ν)

/-- Squared partial sums form a nonnegative submartingale whenever the
increments are square integrable.  This is the form needed by Doob's maximal
inequality; it is derived from the partial-sum martingale rather than being
encoded as a separate random-walk object. -/
theorem submartingale_sq_partialSumProcess
    (increment : ℕ → Ω → ℝ)
    (hstrong : ∀ n, StronglyMeasurable (increment n))
    (hmem : ∀ n, MemLp (increment n) 2 μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) :
    Submartingale (fun n ω => (partialSumProcess increment n ω) ^ 2)
      (Filtration.natural increment hstrong) μ := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hmartingale := martingale_partialSumProcess increment hstrong
    (fun n => (hmem n).integrable (by norm_num)) hcentered hindep
  refine hmartingale.submartingale_convex_comp
    (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
      (show Even (2 : ℕ) by decide).convexOn_pow)
    (by fun_prop) ?_
  intro n
  have hsum : MemLp (partialSumProcess increment n) 2 μ := by
    rw [show partialSumProcess increment n =
        ∑ k ∈ Finset.range (n + 1), increment k by
      funext ω
      simp [partialSumProcess, AdditivePath.displacement]]
    exact memLp_finsetSum' _ fun k _ => hmem k
  simpa [Real.norm_eq_abs] using hsum.integrable_norm_pow (by norm_num)

/-- The square-submartingale specialization for the canonical IID path law.
Only the common one-step second moment and centering are assumed. -/
theorem submartingale_sq_partialSumProcess_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν)
    (hcentered : ∫ x, x ∂ν = 0) :
    Submartingale
      (fun n (increment : ℕ → ℝ) =>
        (partialSumProcess (fun k path => path k) n increment) ^ 2)
      (Filtration.natural (fun k (increment : ℕ → ℝ) => increment k)
        (fun _ => measurable_pi_apply _ |>.stronglyMeasurable))
      (iidSequenceLaw ν) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ := fun n path => path n
  have hstrong : ∀ n, StronglyMeasurable (increment n) :=
    fun n => measurable_pi_apply n |>.stronglyMeasurable
  have hcoord : ∀ n, MemLp (increment n) 2 (iidSequenceLaw ν) := by
    intro n
    exact (show HasLaw (increment n) ν (iidSequenceLaw ν) from
      ⟨(measurable_pi_apply n).aemeasurable,
        iidSequenceLaw_map_apply ν n⟩).memLp hmem
  have hmean : ∀ n, ∫ path, increment n path ∂iidSequenceLaw ν = 0 := by
    intro n
    calc
      (∫ path : ℕ → ℝ, path n ∂iidSequenceLaw ν) =
          ∫ x, x ∂(iidSequenceLaw ν).map (fun path => path n) :=
        (integral_map_of_stronglyMeasurable
          (μ := iidSequenceLaw ν) (φ := fun path : ℕ → ℝ => path n)
          (f := id) (measurable_pi_apply n) stronglyMeasurable_id).symm
      _ = ∫ x, x ∂ν := by rw [iidSequenceLaw_map_apply ν n]
      _ = 0 := hcentered
  simpa only [increment] using submartingale_sq_partialSumProcess
    increment hstrong hcoord hmean (iidSequenceLaw_independent ν)

/-- Doob's maximal inequality applied to squared partial sums.  The right-hand
side is deliberately the unrestricted terminal second moment, which is the
form subsequently evaluated from independence and the one-step variance. -/
theorem maximal_ineq_sq_partialSumProcess
    (increment : ℕ → Ω → ℝ)
    (hstrong : ∀ n, StronglyMeasurable (increment n))
    (hmem : ∀ n, MemLp (increment n) 2 μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) (ε : ℝ≥0) (n : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (partialSumProcess increment k ω) ^ 2} ≤
      ENNReal.ofReal
        (∫ ω, (partialSumProcess increment n ω) ^ 2 ∂μ) := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hsub := submartingale_sq_partialSumProcess increment hstrong hmem
    hcentered hindep
  calc
    _ ≤ ENNReal.ofReal
        (∫ ω in {ω | (ε : ℝ) ≤
            (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              fun k => (partialSumProcess increment k ω) ^ 2},
          (partialSumProcess increment n ω) ^ 2 ∂μ) :=
      MeasureTheory.maximal_ineq hsub
        (fun _ _ => sq_nonneg _) n
    _ ≤ ENNReal.ofReal
        (∫ ω, (partialSumProcess increment n ω) ^ 2 ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact setIntegral_le_integral (hsub.integrable n)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- The terminal second moment of centered independent partial sums is the
sum of the increment variances. -/
theorem integral_sq_partialSumProcess
    (increment : ℕ → Ω → ℝ)
    (hmem : ∀ n, MemLp (increment n) 2 μ)
    (hcentered : ∀ n, ∫ ω, increment n ω ∂μ = 0)
    (hindep : iIndepFun increment μ) (n : ℕ) :
    (∫ ω, (partialSumProcess increment n ω) ^ 2 ∂μ) =
      ∑ k ∈ Finset.range (n + 1), variance (increment k) μ := by
  let _ : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hsum : partialSumProcess increment n =
      ∑ k ∈ Finset.range (n + 1), increment k := by
    funext ω
    simp [partialSumProcess, AdditivePath.displacement]
  have hsumMem : MemLp (partialSumProcess increment n) 2 μ := by
    rw [hsum]
    exact memLp_finsetSum' _ fun k _ => hmem k
  have hsumMean : ∫ ω, partialSumProcess increment n ω ∂μ = 0 := by
    rw [hsum]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum]
    · simp [hcentered]
    · exact fun k _ => (hmem k).integrable (by norm_num)
  rw [← variance_of_integral_eq_zero hsumMem.aemeasurable hsumMean,
    hsum]
  exact IndepFun.variance_sum (fun k hk => hmem k)
    (fun i _ j _ hij => hindep.indepFun hij)

/-- For IID centered increments, the terminal second moment grows linearly
with the number of increments. -/
theorem integral_sq_partialSumProcess_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν)
    (hcentered : ∫ x, x ∂ν = 0) (n : ℕ) :
    (∫ increment : ℕ → ℝ,
        (partialSumProcess (fun k path => path k) n increment) ^ 2
      ∂iidSequenceLaw ν) =
      (n + 1 : ℕ) * variance id ν := by
  let increment : ℕ → (ℕ → ℝ) → ℝ := fun k path => path k
  have hcoordLaw (k : ℕ) : HasLaw (increment k) ν (iidSequenceLaw ν) :=
    ⟨(measurable_pi_apply k).aemeasurable,
      iidSequenceLaw_map_apply ν k⟩
  have hcoordMem : ∀ k, MemLp (increment k) 2 (iidSequenceLaw ν) :=
    fun k => (hcoordLaw k).memLp hmem
  have hcoordMean : ∀ k,
      ∫ path, increment k path ∂iidSequenceLaw ν = 0 := by
    intro k
    rw [(hcoordLaw k).integral_eq, hcentered]
  rw [integral_sq_partialSumProcess increment hcoordMem hcoordMean
    (iidSequenceLaw_independent ν) n]
  simp_rw [(hcoordLaw _).variance_eq]
  simp

/-- The IID form of the squared maximal inequality, with the terminal moment
evaluated as the number of exposed increments times the one-step variance. -/
theorem maximal_ineq_sq_partialSumProcess_iidSequenceLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν)
    (hcentered : ∫ x, x ∂ν = 0)
    (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {increment | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k =>
            (partialSumProcess (fun j path => path j) k increment) ^ 2} ≤
      ENNReal.ofReal ((n + 1 : ℕ) * variance id ν) := by
  let increment : ℕ → (ℕ → ℝ) → ℝ := fun k path => path k
  have hstrong : ∀ k, StronglyMeasurable (increment k) :=
    fun k => measurable_pi_apply k |>.stronglyMeasurable
  have hcoordLaw (k : ℕ) : HasLaw (increment k) ν (iidSequenceLaw ν) :=
    ⟨(measurable_pi_apply k).aemeasurable,
      iidSequenceLaw_map_apply ν k⟩
  have hcoordMem : ∀ k, MemLp (increment k) 2 (iidSequenceLaw ν) :=
    fun k => (hcoordLaw k).memLp hmem
  have hcoordMean : ∀ k,
      ∫ path, increment k path ∂iidSequenceLaw ν = 0 := by
    intro k
    rw [(hcoordLaw k).integral_eq, hcentered]
  calc
    _ ≤ ENNReal.ofReal
        (∫ path, (partialSumProcess increment n path) ^ 2
          ∂iidSequenceLaw ν) :=
      maximal_ineq_sq_partialSumProcess increment hstrong hcoordMem
        hcoordMean (iidSequenceLaw_independent ν) ε n
    _ = ENNReal.ofReal ((n + 1 : ℕ) * variance id ν) := by
      congr 1
      exact integral_sq_partialSumProcess_iidSequenceLaw ν hmem hcentered n

end ProbabilityTheory.RandomWalk
