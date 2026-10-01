module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Indicator
public import Probability.Process.Levy.Jump.SmallVariation

/-!
# Vanishing variation on shrinking jump bands

The finite-variation condition gives an integrable upper bound.  If each
nonzero mark eventually leaves a shrinking band, dominated convergence shows
that the expected total variation contributed by that band tends to zero.
This argument does not require an explicit stable Lévy density.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped Topology

/-- The weighted mass of a shrinking measurable family tends to zero when
the weight has finite integral and almost every mark eventually leaves it. -/
theorem tendsto_lintegral_restrict_of_eventually_not_mem
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n) :
    Tendsto (fun n => ∫⁻ x in band n, weight x ∂ν) atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂ν,
      Tendsto (fun n => (band n).indicator weight x) atTop (𝓝 0) := by
    filter_upwards [haway] with x hx
    have heq : (fun n => (band n).indicator weight x) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [hx] with n hn
      exact Set.indicator_of_notMem hn _
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hbound : ∀ n, (band n).indicator weight ≤ᵐ[ν] weight := by
    intro n
    filter_upwards [] with x
    by_cases hx : x ∈ band n
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have ht := tendsto_lintegral_of_dominated_convergence weight
    (fun n => (hweight.indicator (hband n))) hbound hfinite hlim
  simpa only [lintegral_indicator (hband _), lintegral_zero] using ht

/-- A sufficiently small truncation band has expected absolute-jump mass
below any prescribed positive threshold. -/
theorem exists_lintegral_restrict_lt_of_eventually_not_mem
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, (∫⁻ x in band n, weight x ∂ν) < ENNReal.ofReal ρ := by
  have ht := tendsto_lintegral_restrict_of_eventually_not_mem ν weight band
    hweight hband hfinite haway
  have hpos : (0 : ENNReal) < ENNReal.ofReal ρ := ENNReal.ofReal_pos.mpr hρ
  exact ((tendsto_order.1 ht).2 _ hpos).exists

/-- Campbell's expectation identity turns finite-variation truncation into a
positive-probability small-residual event at some deterministic cutoff. -/
theorem exists_smallVariation_pos_of_campbell
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (ν : Measure E) (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : E → ENNReal) (band : ℕ → Set E) (V : ℕ → Ω → ENNReal)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n)
    (hV : ∀ n, Measurable (V n))
    (hcampbell : ∀ n, (∫⁻ ω, V n ω ∂P) =
      ∫⁻ x in band n, weight x ∂ν)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < P {ω | V n ω < ENNReal.ofReal ρ} := by
  obtain ⟨n, hn⟩ := exists_lintegral_restrict_lt_of_eventually_not_mem
    ν weight band hweight hband hfinite haway ρ hρ
  exact ⟨n, measure_smallVariation_pos P (V n) (hV n)
    (ENNReal.ofReal ρ) (by simpa [hcampbell n] using hn)⟩

end ProbabilityTheory

end
