import Combinatorics.BranchingWalk.Walk.Path.Basic
import Probability.Sequence.IID
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Basic

/-!
# Partial-sum martingales

Centered independent real increments generate a martingale of partial sums
with respect to their natural filtration. The underlying partial-sum operation
remains in the deterministic walk layer.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The partial-sum process aligned with the natural filtration: at time `n`
it contains increments `0, ..., n`. -/
def partialSumProcess (increment : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  partialSum (n + 1) (fun k => increment k ω)

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
      simp [partialSumProcess, partialSum]]
    exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun k hk =>
      (Filtration.stronglyAdapted_natural hstrong k).mono
        (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  refine ⟨hadapt, fun i j hij => ?_⟩
  rw [show partialSumProcess increment j =
      ∑ k ∈ Finset.range (j + 1), increment k by
    funext ω
    simp [partialSumProcess, partialSum]]
  refine (condExp_finsetSum (fun k _ => hint k) _).trans ?_
  rw [show partialSumProcess increment i =
      ∑ k ∈ Finset.range (i + 1), increment k by
    funext ω
    simp [partialSumProcess, partialSum]]
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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
