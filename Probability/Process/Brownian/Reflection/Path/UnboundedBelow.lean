/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassage.Principle

/-!
# Brownian paths descend below every level

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_continuousPath_unboundedBelow`:
  almost every continuous Brownian path satisfies
  $\forall a\in\mathbb R,\ \exists t\ge0,\ B_t<a$.

The proof combines the reflection-principle consequence
$\mathbb P(\min_{[0,1]}B<0)=1$ with Brownian scaling. This supplies the
eventual-descent path property used with the Lévy decomposition in
Lemma 2.3, equation (2.2), of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

private theorem everBelow_brownianPathScaling_iff
    (f : C(ℝ≥0, ℝ)) {c : ℝ≥0} (hc : 0 < c) (a : ℝ) :
    (∃ t : ℝ≥0, brownianPathScaling c f t < a) ↔
      ∃ t : ℝ≥0, f t < √c * a := by
  have hroot : 0 < (√c : ℝ) := by positivity
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨c * t, ?_⟩
    change (√c)⁻¹ * f (c * t) < a at ht
    exact (inv_mul_lt_iff₀ hroot).mp ht
  · rintro ⟨t, ht⟩
    refine ⟨t / c, ?_⟩
    change (√c)⁻¹ * f (c * (t / c)) < a
    rw [mul_div_cancel₀ _ hc.ne']
    exact (inv_mul_lt_iff₀ hroot).mpr ht

private theorem measurableSet_everBelow (a : ℝ) :
    MeasurableSet {f : C(ℝ≥0, ℝ) | ∃ t : ℝ≥0, f t < a} := by
  have hset : {f : C(ℝ≥0, ℝ) | ∃ t : ℝ≥0, f t < a} =
      ⋃ t : ℝ≥0, (fun f : C(ℝ≥0, ℝ) => f t) ⁻¹' Set.Iio a := by
    ext f
    simp
  rw [hset]
  exact (isOpen_iUnion (fun t =>
    isOpen_Iio.preimage (continuous_eval_const t))).measurableSet

private theorem IsBrownianReal.measure_everBelow_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | ∃ t : ℝ≥0, f t < a} = 1 := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let E : ℝ → Set C(ℝ≥0, ℝ) := fun b =>
    {f | ∃ t : ℝ≥0, f t < b}
  have hEmeas (b : ℝ) : MeasurableSet (E b) :=
    measurableSet_everBelow b
  let level : ℕ → ℝ := fun n => a / (n + 1 : ℝ)
  have hlevelNeg (n : ℕ) : level n < 0 := by
    dsimp [level]
    exact div_neg_of_neg_of_pos ha (by positivity)
  have hlevelMono : Monotone level := by
    intro n m hnm
    have hrecip : 1 / (m + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hmul := mul_le_mul_of_nonpos_left hrecip ha.le
    simpa [level, div_eq_mul_inv] using hmul
  have hEmono : Monotone (fun n => E (level n)) := by
    intro n m hnm f hf
    obtain ⟨t, ht⟩ := hf
    exact ⟨t, ht.trans_le (hlevelMono hnm)⟩
  have hEunion : (⋃ n, E (level n)) = E 0 := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, E]
    constructor
    · rintro ⟨n, t, ht⟩
      exact ⟨t, ht.trans (hlevelNeg n)⟩
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt
        (div_pos (neg_pos.mpr ht) (neg_pos.mpr ha))
      refine ⟨n, t, ?_⟩
      have hmul : (1 / (n + 1 : ℝ)) * (-a) < -f t :=
        (lt_div_iff₀ (neg_pos.mpr ha)).mp hn
      dsimp [level]
      rw [div_eq_mul_inv]
      rw [one_div] at hmul
      nlinarith
  have hscale (n : ℕ) : μ (E (level n)) = μ (E a) := by
    let c : ℝ≥0 := (n + 1 : ℝ≥0) ^ 2
    have hc : 0 < c := by positivity
    have hroot : (√c : ℝ) = (n + 1 : ℝ) := by
      simpa [c] using
        (Real.sqrt_sq (by positivity : 0 ≤ (n + 1 : ℝ)))
    have hlevel : (√c : ℝ) * level n = a := by
      rw [hroot]
      dsimp [level]
      field_simp
    let S := brownianPathScaling c
    have hpre : S ⁻¹' E (level n) = E a := by
      ext f
      change (∃ t, S f t < level n) ↔ ∃ t, f t < a
      rw [everBelow_brownianPathScaling_iff f hc, hlevel]
    have hlaw : μ.map S = μ := by
      rw [Measure.map_map (measurable_brownianPathScaling c)
        (hB.measurable_continuousPathMap hBmeasurable)]
      exact hB.measure_continuousPathMap_scale_eq hBmeasurable hc.ne'
    calc
      μ (E (level n)) = (μ.map S) (E (level n)) := by rw [hlaw]
      _ = μ (S ⁻¹' E (level n)) :=
        Measure.map_apply (measurable_brownianPathScaling c) (hEmeas _)
      _ = μ (E a) := by rw [hpre]
  letI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  have hEzero : μ (E 0) = 1 := by
    apply le_antisymm
    · calc
        μ (E 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by simp [μ]
    · have hmin : μ {f : C(ℝ≥0, ℝ) | runningMinimum f 1 < 0} = 1 :=
        hB.measure_runningMinimum_lt_zero hBmeasurable (by norm_num)
      rw [← hmin]
      apply measure_mono
      intro f hf
      obtain ⟨t, _, hvalue⟩ := exists_runningMinimum_eq f 1
      exact ⟨t, hvalue.trans_lt hf⟩
  calc
    μ (E a) = ⨆ n, μ (E (level n)) := by
      simp [hscale]
    _ = μ (⋃ n, E (level n)) := (hEmono.measure_iUnion).symm
    _ = μ (E 0) := by rw [hEunion]
    _ = 1 := hEzero

/-- Almost every Brownian path eventually visits below every real
level. This is the recurrence input for identifying the right limit
of its descending hitting-time process. -/
theorem IsBrownianReal.ae_continuousPath_unboundedBelow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ f ∂P.map (hB.continuousPathMap hBmeasurable),
      ∀ a : ℝ, ∃ t : ℝ≥0, f t < a := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  letI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  letI : IsProbabilityMeasure μ := by
    constructor
    simp [μ]
  have hfixed (n : ℕ) :
      ∀ᵐ f ∂μ, ∃ t : ℝ≥0, f t < -(n + 1 : ℝ) := by
    apply (ae_iff_prob_eq_one
      (measurableSet_setOfPred.mp
        (measurableSet_everBelow (-(n + 1 : ℝ))))).2
    exact hB.measure_everBelow_eq_one hBmeasurable (by
      have hnpos : 0 < (n + 1 : ℝ) := by positivity
      linarith)
  have hall : ∀ᵐ f ∂μ,
      ∀ n : ℕ, ∃ t : ℝ≥0, f t < -(n + 1 : ℝ) :=
    ae_all_iff.2 hfixed
  filter_upwards [hall] with f hf a
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  obtain ⟨t, ht⟩ := hf n
  refine ⟨t, ht.trans ?_⟩
  have hn' : -(n + 1 : ℝ) < a := by
    linarith
  exact hn'

end ProbabilityTheory

end
