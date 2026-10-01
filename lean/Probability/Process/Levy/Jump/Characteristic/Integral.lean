import Probability.Process.Levy.Jump.Characteristic.Finite
import LeanLevy.RandomMeasure.PoissonRandomMeasure

/-!
# Poisson jump integrals as absolutely convergent piece sums

The realized Bochner integral is the sum over the canonical partition
whenever the integrand is integrable for that realized random measure.
This is the deterministic identity needed before taking characteristic
functions of the infinite Poisson jump sum.
-/

namespace ProbabilityTheory

open MeasureTheory

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

end ProbabilityTheory
