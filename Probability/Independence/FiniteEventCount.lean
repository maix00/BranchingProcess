/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lower tails for finite independent event counts

For a finite family of independent, identically distributed observations and
a measurable event of probability $q$, the number of observations in the
event has lower-tail bound

$$
  \mathbb P\!\left(\sum_{i\in A}1_E(X_i)\le \frac{|A|q}{4}\right)
  \le \exp\!\left(-\frac{|A|q}{4}\right).
$$

The result applies to any measurable probability space and observation type.
It uses Mathlib's moment-generating-function factorization for independent
random variables and its Chernoff bound.

## Public declarations

- `measure_iidEventCount_le_quarter_mean` gives the displayed lower-tail
  estimate for a finite subfamily of independent, identically distributed
  observations.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

private lemma mgf_eventIndicator
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) :
    mgf (E.indicator (fun _ => (1 : ℝ))) μ (-1) =
      1 - μ.real E * (1 - Real.exp (-1)) := by
  classical
  have hdecomp :
      (fun ω => Real.exp (-1 * E.indicator (fun _ => (1 : ℝ)) ω)) =
        E.indicator (fun _ => Real.exp (-1)) +
          Eᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have hleft : Integrable (E.indicator (fun _ => Real.exp (-1))) μ := by
    refine Integrable.of_bound (measurable_const.indicator hE).aestronglyMeasurable
      (Real.exp (-1)) (ae_of_all μ fun ω => ?_)
    by_cases hω : ω ∈ E <;> simp [hω, Real.exp_nonneg]
  have hEcompl : MeasurableSet Eᶜ := MeasurableSet.compl hE
  have hright : Integrable (Eᶜ.indicator (fun _ => (1 : ℝ))) μ := by
    refine Integrable.of_bound (measurable_const.indicator hEcompl).aestronglyMeasurable
      1 (ae_of_all μ fun ω => ?_)
    by_cases hω : ω ∈ E <;> simp [hω]
  calc
    mgf (E.indicator (fun _ => (1 : ℝ))) μ (-1) =
        ∫ ω, Real.exp (-1 * E.indicator (fun _ => (1 : ℝ)) ω) ∂μ := by
          simp [mgf]
    _ = ∫ ω, E.indicator (fun _ => Real.exp (-1)) ω +
          Eᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
            exact integral_congr_ae
              (ae_of_all μ fun ω => congrFun hdecomp ω)
    _ = (∫ ω, E.indicator (fun _ => Real.exp (-1)) ω ∂μ) +
          ∫ ω, Eᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
            exact integral_add' hleft hright
    _ = 1 - μ.real E * (1 - Real.exp (-1)) := by
          rw [integral_indicator_const _ hE,
            integral_indicator_const _ hEcompl,
            smul_eq_mul, smul_eq_mul, measureReal_compl hE, probReal_univ]
          ring

/-- For independent, identically distributed observations, the probability
that at most one quarter of the expected number lies in a measurable event is
at most the exponential of minus one quarter of that expected number. -/
theorem measure_iidEventCount_le_quarter_mean
    {Ω ι α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → α) (A : Finset ι) (j : ι) (hj : j ∈ A)
    (E : Set α) (hE : MeasurableSet E)
    (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i ∈ A, IdentDistrib (X i) (X j) μ μ) :
    let q : ℝ := (μ (X j ⁻¹' E)).toReal
    μ {ω | (∑ i ∈ A, E.indicator (fun _ => (1 : ℝ)) (X i ω)) ≤
        (A.card : ℝ) * q / 4} ≤
      ENNReal.ofReal (Real.exp (-((A.card : ℝ) * q / 4))) := by
  classical
  let q : ℝ := (μ (X j ⁻¹' E)).toReal
  let Xi : ι → Ω → ℝ := fun i => E.indicator (fun _ => (1 : ℝ)) ∘ X i
  let total : Ω → ℝ := fun ω => ∑ i ∈ A, Xi i ω
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact ENNReal.toReal_nonneg
  have hprob : μ (X j ⁻¹' E) ≤ 1 := by
    calc
      μ (X j ⁻¹' E) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hq_le : q ≤ 1 := by
    dsimp [q]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hprob
  have hXi_meas (i : ι) : Measurable (Xi i) := by
    exact (measurable_const.indicator hE).comp (hX i)
  have hXi_indep : iIndepFun Xi μ := by
    have hg : Measurable (E.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hE
    simpa [Xi, Function.comp_def] using
      hIndep.comp (fun _ => E.indicator (fun _ => (1 : ℝ))) (fun _ => hg)
  have hXi_ident (i : ι) (hi : i ∈ A) :
      IdentDistrib (Xi i) (Xi j) μ μ := by
    have hg : Measurable (E.indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hE
    simpa [Xi, Function.comp_def] using (hIdent i hi).comp hg
  have hXi_ident_all (i : ι) (hi : i ∈ A) (k : ι) (hk : k ∈ A) :
      IdentDistrib (Xi i) (Xi k) μ μ :=
    (hXi_ident i hi).trans (hXi_ident k hk).symm
  have hsingle : mgf (Xi j) μ (-1) =
      1 - q * (1 - Real.exp (-1)) := by
    have hevent : Xi j = (X j ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : X j ω ∈ E <;> simp [Xi, hω]
    rw [hevent]
    simpa [q, Measure.real] using
      mgf_eventIndicator μ (X j ⁻¹' E) ((hX j) hE)
  have hsumFun : (∑ i ∈ A, Xi i) = total := by
    funext ω
    simp [total, Finset.sum_apply]
  have hmgf_sum : mgf total μ (-1) = mgf (Xi j) μ (-1) ^ A.card := by
    rw [← hsumFun]
    exact mgf_sum_of_identDistrib (X := Xi) (s := A) (j := j)
      hXi_meas hXi_indep hXi_ident_all hj (-1)
  have hsingle_le : mgf (Xi j) μ (-1) ≤ Real.exp (-(q / 2)) := by
    rw [hsingle]
    have hexp : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num)
        Real.exp_one_gt_two.le
    calc
      1 - q * (1 - Real.exp (-1)) ≤ 1 - q / 2 := by
        nlinarith [mul_nonneg hq_nonneg (sub_nonneg.mpr hexp)]
      _ ≤ Real.exp (-(q / 2)) := by
        simpa using Real.one_sub_le_exp_neg (q / 2)
  have hmgf_sum_le :
      mgf total μ (-1) ≤ Real.exp (-((A.card : ℝ) * q / 2)) := by
    rw [hmgf_sum]
    calc
      mgf (Xi j) μ (-1) ^ A.card ≤
          (Real.exp (-(q / 2))) ^ A.card :=
        pow_le_pow_left₀ (mgf_nonneg) hsingle_le A.card
      _ = Real.exp (-((A.card : ℝ) * q / 2)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have htotal_nonneg (ω : Ω) : 0 ≤ total ω := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases hω : X i ω ∈ E <;> simp [Xi, hω]
  have htotal_meas : Measurable total := by
    dsimp [total]
    exact Finset.measurable_sum _ fun i hi => hXi_meas i
  have htotalExpIntegrable : Integrable (fun ω =>
      Real.exp (-1 * total ω)) μ := by
    refine Integrable.of_bound ((htotal_meas.const_mul (-1)).exp).aestronglyMeasurable 1
      (ae_of_all μ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [htotal_nonneg ω]
  have htail := measure_le_le_exp_mul_mgf (X := total) (μ := μ) (t := -1)
    ((A.card : ℝ) * q / 4) (by norm_num) htotalExpIntegrable
  have htailReal :
      μ.real {ω | total ω ≤ (A.card : ℝ) * q / 4} ≤
        Real.exp (-((A.card : ℝ) * q / 4)) := by
    calc
      _ ≤ Real.exp ((A.card : ℝ) * q / 4) * mgf total μ (-1) := by
        simpa [mul_comm] using htail
      _ ≤ Real.exp ((A.card : ℝ) * q / 4) *
          Real.exp (-((A.card : ℝ) * q / 2)) :=
        mul_le_mul_of_nonneg_left hmgf_sum_le (Real.exp_nonneg _)
      _ = Real.exp (-((A.card : ℝ) * q / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfinite : (μ {ω | total ω ≤ (A.card : ℝ) * q / 4}) ≠ ⊤ :=
    measure_ne_top _ _
  have htailENN : μ {ω | total ω ≤ (A.card : ℝ) * q / 4} ≤
      ENNReal.ofReal (Real.exp (-((A.card : ℝ) * q / 4))) := by
    calc
      _ = ENNReal.ofReal
          (μ {ω | total ω ≤ (A.card : ℝ) * q / 4}).toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ ENNReal.ofReal (Real.exp (-((A.card : ℝ) * q / 4))) :=
        ENNReal.ofReal_le_ofReal htailReal
  simpa [q, Xi, total] using htailENN

end ProbabilityTheory

end
