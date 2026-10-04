/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under MIT license; see LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.RandomMeasure.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section

/-!
# Measurability of integrals against Poisson random measures

An almost-surely integrable measurable observable has an almost-everywhere
measurable Poisson integral. This is part of the general random-measure API,
independent of a particular Lévy or stable-process model.
-/

namespace ProbabilityTheory

open MeasureTheory Filter

/-- For an integrable function, its realized Poisson integral is the sum of
its contributions over the canonical countable partition. -/
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

/-- The integral against a realized Poisson random measure equals the sum of
the contributions over its canonical partition. -/
theorem integral_poissonRandomMeasure_eq_tsum_pieceSum
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {f : E → ℝ} (hmeas : Measurable f)
    (hf : Integrable f (poissonRandomMeasure K X ω)) :
    (∫ x, f x ∂(poissonRandomMeasure K X ω)) =
      ∑' k, pieceSum K X f k ω :=
  (hasSum_pieceSum_poissonRandomMeasure K X ω hmeas hf).tsum_eq.symm

/-- The realized random-measure integral is almost-everywhere measurable when its integrand is
measurable and almost surely integrable. This conclusion only uses measurability of the count and
point coordinates, not the Poisson laws or independence assumptions. -/
theorem aemeasurable_integral_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {P : Measure Ω}
    (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    {f : E → ℝ} (hf : Measurable f)
    (hrealized : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω)) :
    AEMeasurable (fun ω => ∫ x, f x ∂(poissonRandomMeasure K X ω)) P := by
  let positivePartIntegral (ω : Ω) : ℝ :=
    (∫⁻ x, ENNReal.ofReal (f x) ∂(poissonRandomMeasure K X ω)).toReal
  let negativePartIntegral (ω : Ω) : ℝ :=
    (∫⁻ x, ENNReal.ofReal (-f x) ∂(poissonRandomMeasure K X ω)).toReal
  have hpositive : Measurable positivePartIntegral :=
    (measurable_lintegral_poissonRandomMeasure hK hX
      (ENNReal.measurable_ofReal.comp hf)).ennreal_toReal
  have hnegative : Measurable negativePartIntegral :=
    (measurable_lintegral_poissonRandomMeasure hK hX
      (ENNReal.measurable_ofReal.comp hf.neg)).ennreal_toReal
  have hdecomp :
      (fun ω => ∫ x, f x ∂(poissonRandomMeasure K X ω)) =ᵐ[P]
        fun ω => positivePartIntegral ω - negativePartIntegral ω := by
    filter_upwards [hrealized] with ω hω
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω
  exact (hpositive.sub hnegative).aemeasurable.congr hdecomp.symm

/-- For a Poisson point family, the realized integral is almost-everywhere measurable whenever it
is almost surely integrable. The Poisson assumptions supply the coordinate measurability required by
the more general configuration theorem. -/
theorem IsPoissonPointFamily.aemeasurable_integral_poissonRandomMeasure
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hrealized : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω)) :
    AEMeasurable (fun ω => ∫ x, f x ∂(poissonRandomMeasure K X ω)) P :=
  ProbabilityTheory.aemeasurable_integral_poissonRandomMeasure
    hd.measurable_count hd.measurable_point hf hrealized

end ProbabilityTheory
