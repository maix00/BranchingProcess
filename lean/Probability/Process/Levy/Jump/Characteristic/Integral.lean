import Probability.Process.Levy.Jump.Characteristic.Finite
import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Poisson jump integrals as absolutely convergent piece sums

The realized Bochner integral is the sum over the canonical partition
whenever the integrand is integrable for that realized random measure.
This is the deterministic identity needed before taking characteristic
functions of the infinite Poisson jump sum.
-/

namespace ProbabilityTheory

open MeasureTheory Filter

theorem hasSum_pieceSum_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {f : E → ℝ} (hmeas : Measurable f)
    (hf : Integrable f (poissonRandomMeasure K X ω)) :
    HasSum (fun k => pieceSum K X f k ω)
      (∫ x, f x ∂(poissonRandomMeasure K X ω)) := by
  change Integrable f (Measure.sum fun k =>
    Measure.sum fun n => if n < K k ω then Measure.dirac (X k n ω) else 0) at hf
  have h := hasSum_integral_measure hf
  convert h using 1
  ext k
  have hk : Integrable f
      (Measure.sum fun n => if n < K k ω then Measure.dirac (X k n ω) else 0) :=
    hf.mono_measure (Measure.le_sum
      (fun j => Measure.sum fun n =>
        if n < K j ω then Measure.dirac (X j n ω) else 0) k)
  rw [integral_sum_measure hk]
  have hterm : ∀ n,
      (∫ x, f x ∂(if n < K k ω then Measure.dirac (X k n ω) else 0)) =
        if n < K k ω then f (X k n ω) else 0 := by
    intro n
    by_cases h : n < K k ω
    · simpa only [if_pos h] using
        (integral_dirac' f (X k n ω) hmeas.stronglyMeasurable)
    · simp [h]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω))
    fun n hn => if_neg (by simpa [Finset.mem_range] using hn)]
  exact Finset.sum_congr rfl fun j hj =>
    (if_pos (Finset.mem_range.mp hj)).symm
  rfl

theorem integral_poissonRandomMeasure_eq_tsum_pieceSum
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {f : E → ℝ} (hmeas : Measurable f)
    (hf : Integrable f (poissonRandomMeasure K X ω)) :
    (∫ x, f x ∂(poissonRandomMeasure K X ω)) =
      ∑' k, pieceSum K X f k ω :=
  (hasSum_pieceSum_poissonRandomMeasure K X ω hmeas hf).tsum_eq.symm

/-- The Poisson jump integral is an almost-everywhere measurable random
variable whenever it is almost surely integrable. -/
theorem IsPoissonPointFamily.aemeasurable_integral_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hrealized : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω)) :
    AEMeasurable (fun ω => ∫ x, f x ∂(poissonRandomMeasure K X ω)) P := by
  open scoped Topology in
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (f := fun n ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
  · intro n
    exact (Finset.measurable_sum _ fun k _ =>
      measurable_pieceSum (hd.measurable_count k)
        (hd.measurable_point k) hf).aemeasurable
  · filter_upwards [hrealized] with ω hω
    have hs := (hasSum_pieceSum_poissonRandomMeasure K X ω hf hω).tendsto_sum_nat
    simpa only [Function.comp_def] using hs.comp (tendsto_add_atTop_nat 1)

end ProbabilityTheory
