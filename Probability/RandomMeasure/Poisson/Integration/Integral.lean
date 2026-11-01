/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under MIT license; see LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.RandomMeasure.Poisson.PointFamily.PieceSum
public import Probability.RandomMeasure.Poisson.RandomMeasure.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Pathwise integrals against Poisson random measures

This module represents realized Poisson integrals by sums over the canonical pieces and proves
measurability of the nonnegative and real-valued integral maps.

For $N_\omega=\operatorname{poissonRandomMeasure}(K,X,\omega)$, measurable
$g:E\to[0,\infty]$ and measurable integrable $f:E\to\mathbb R$ satisfy
$$
\int^- g(x)\,N_\omega(dx)
  =\sum_{k=0}^\infty\sum_{n<K_k(\omega)}g(X_{k,n}(\omega)),
\qquad
\int f(x)\,N_\omega(dx)
  =\sum_{k=0}^\infty\sum_{n<K_k(\omega)}f(X_{k,n}(\omega)).
$$
The real-valued identity uses integrability with respect to $N_\omega$; its
series is grouped by the canonical countable intensity partition.

## Public declarations

- `lintegral_poissonRandomMeasure` expresses the nonnegative integral as the sum over realized points.
- `measurable_lintegral_poissonRandomMeasure` proves measurability of the nonnegative integral map.
- `hasSum_pieceSum_poissonRandomMeasure` and `integral_poissonRandomMeasure_eq_tsum_pieceSum`
  represent integrable real-valued integrals by the sum of piece sums.
- `aemeasurable_integral_poissonRandomMeasure` gives almost-everywhere measurability under almost-sure
  integrability.
- `IsPoissonPointFamily.aemeasurable_integral_poissonRandomMeasure` applies the same result using the
  coordinate measurability supplied by a Poisson point family.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped ENNReal

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
    · simpa only [ite_eq_left h] using
        (integral_dirac' f (X k n ω) hmeas.stronglyMeasurable)
    · simp [h]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω))
    fun n hn => ite_eq_right (by simpa [Finset.mem_range] using hn)]
  exact Finset.sum_congr rfl fun j hj =>
    (ite_eq_left (Finset.mem_range.mp hj)).symm
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

section PoissonRandomMeasureLIntegral

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E]

omit [SigmaFinite m] [Nonempty E] [MeasurableSpace Ω] in
/-- **Lebesgue integral against the random measure.** The integral of a measurable `g` against the
Poisson random measure is the sum of `g` over the realized points `X k n ω` (for `n < K k ω`). -/
theorem lintegral_poissonRandomMeasure {g : E → ℝ≥0∞} (hg : Measurable g) (ω : Ω) :
    ∫⁻ x, g x ∂(poissonRandomMeasure K X ω)
      = ∑' k, ∑ n ∈ Finset.range (K k ω), g (X k n ω) := by
  rw [poissonRandomMeasure, lintegral_sum_measure]
  refine tsum_congr fun k => ?_
  rw [lintegral_sum_measure]
  have hterm : ∀ n, ∫⁻ x, g x ∂(if n < K k ω then Measure.dirac (X k n ω) else 0)
      = if n < K k ω then g (X k n ω) else 0 := fun n => by
    by_cases h : n < K k ω
    · rw [ite_eq_left h, ite_eq_left h, lintegral_dirac' _ hg]
    · rw [ite_eq_right h, ite_eq_right h, lintegral_zero_measure]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω))
    fun n hn => ite_eq_right (by simpa [Finset.mem_range] using hn)]
  exact Finset.sum_congr rfl fun n hn => ite_eq_left (by simpa [Finset.mem_range] using hn)

omit [SigmaFinite m] [Nonempty E] in
/-- Integrating a measurable nonnegative function against the realized
Poisson random measure is measurable in the sample. -/
theorem measurable_lintegral_poissonRandomMeasure
    (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun ω => ∫⁻ x, g x ∂(poissonRandomMeasure K X ω) := by
  exact (Measure.measurable_lintegral hg).comp
    (measurable_poissonRandomMeasure hK hX)


end PoissonRandomMeasureLIntegral

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
