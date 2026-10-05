/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.PowerTailIntegral
public import Analysis.Asymptotics.RegularVariation.Integral
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Truncated moments and power-tail asymptotics

This general probability layer records truncated second moments, their
layer-cake representation, and the consequence of a two-sided power-tail
asymptotic.  It does not assume a stable law or a domain-of-attraction
hypothesis.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

/-- The second moment truncated to the symmetric interval of radius `u`. -/
noncomputable def truncatedSecondMoment (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x in Set.Icc (-u) u, x ^ 2 ∂μ

/-- The truncated second moment is nondecreasing in its nonnegative cutoff.
This uses only finiteness of the measure: the integrand is bounded on every
bounded truncation interval, so no global second moment is required. -/
theorem truncatedSecondMoment_mono (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    truncatedSecondMoment μ u ≤ truncatedSecondMoment μ v := by
  let s : Set ℝ := Set.Icc (-u) u
  let t : Set ℝ := Set.Icc (-v) v
  have hsub : s ⊆ t := by
    intro x hx
    constructor
    · exact (neg_le_neg huv).trans hx.1
    · exact hx.2.trans huv
  have hbound : ∀ x ∈ t, ‖x ^ 2‖ ≤ v ^ 2 := by
    intro x hx
    have hxabs : |x| ≤ v := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hsq : x ^ 2 ≤ v ^ 2 := by
      rw [← sq_abs x]
      exact (sq_le_sq₀ (abs_nonneg x) (le_trans hu huv)).2 hxabs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    exact hsq
  have htfinite : μ t ≠ ⊤ := measure_ne_top μ t
  have hint : IntegrableOn (fun x : ℝ => x ^ 2) t μ :=
    Measure.integrableOn_of_bounded htfinite
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) μ)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hbound x hx))
  change (∫ x in s, x ^ 2 ∂μ) ≤ ∫ x in t, x ^ 2 ∂μ
  exact setIntegral_mono_set hint
    (ae_of_all _ fun x => sq_nonneg x)
    (LE.le.eventuallyLE hsub)

/-- Truncated second moments over expanding symmetric intervals converge to
the full second moment whenever it is finite. -/
theorem tendsto_truncatedSecondMoment
    (μ : Measure ℝ) (hμ : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (truncatedSecondMoment μ) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) := by
  change Tendsto (fun u : ℝ => truncatedSecondMoment μ u) atTop
    (nhds (∫ x, x ^ 2 ∂μ))
  let s : ℝ → Set ℝ := fun u => Set.Icc (-u) u
  have hsMeasurable : ∀ u, MeasurableSet (s u) := fun _ => measurableSet_Icc
  have hsMono : Monotone s := by
    intro u v huv x hx
    dsimp [s] at hx ⊢
    constructor
    · exact (neg_le_neg huv).trans hx.1
    · exact hx.2.trans huv
  have hsUnion : (⋃ u, s u) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_iUnion, s, Set.mem_Icc]
    refine ⟨|x| + 1, ?_⟩
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have h := tendsto_setIntegral_of_monotone hsMeasurable hsMono
    (hμ.integrableOn : IntegrableOn (fun x : ℝ => x ^ 2) (⋃ u, s u) μ)
  simpa only [truncatedSecondMoment, s, hsUnion, Measure.restrict_univ] using h

/-- Integer radii are a cofinal specialization of the real-radius limit. -/
theorem tendsto_truncatedSecondMoment_nat
    (μ : Measure ℝ) (hμ : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun n : ℕ => truncatedSecondMoment μ n) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) := by
  exact (tendsto_truncatedSecondMoment μ hμ).comp
    tendsto_natCast_atTop_atTop


/-- The bounded layer-cake tail integral associated with the truncation level
`u`. -/
noncomputable def truncatedSquareTailIntegral (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ t in Ioi 0, if t < u ^ 2 then μ.real {x : ℝ | t < x ^ 2} else 0

/-- Capping the absolute value at `u` splits its second moment into the
truncated second moment below `u` and the cap contributed by the tail. -/
theorem integral_sq_min_abs_eq_truncatedSecondMoment_add_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    (∫ x, (min |x| u) ^ 2 ∂μ) = truncatedSecondMoment μ u +
      u ^ 2 * (μ.real {x : ℝ | u < |x|}) := by
  let s : Set ℝ := Icc (-u) u
  let f : ℝ → ℝ := fun x => (min |x| u) ^ 2
  have hs : MeasurableSet s := measurableSet_Icc
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (by fun_prop : Measurable f).aestronglyMeasurable
  have hfbdd : ∀ᵐ x ∂μ, ‖f x‖ ≤ u ^ 2 := by
    filter_upwards with x
    have hmin : 0 ≤ min |x| u := by
      by_cases hx : |x| ≤ u
      · rw [min_eq_left hx]
        exact abs_nonneg x
      · rw [min_eq_right (le_of_not_ge hx)]
        exact hu
    have hle : min |x| u ≤ u := min_le_right _ _
    have hsq : (min |x| u) ^ 2 ≤ u ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hle hmin,
        mul_le_mul_of_nonneg_right hmin hu]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq
  have hf : Integrable f μ := ⟨hfmeas, HasFiniteIntegral.of_bounded hfbdd⟩
  have hsplit := integral_add_compl hs hf
  have hleft : (∫ x in s, f x ∂μ) = truncatedSecondMoment μ u := by
    rw [truncatedSecondMoment]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change -u ≤ x ∧ x ≤ u at hx
    have hx' : |x| ≤ u := abs_le.mpr hx
    simp [f, min_eq_left hx', sq_abs]
  have hsComplement : sᶜ = {x : ℝ | u < |x|} := by
    ext x
    change ¬ (-u ≤ x ∧ x ≤ u) ↔ u < |x|
    constructor
    · intro hx
      by_contra h
      exact hx (abs_le.mp (le_of_not_gt h))
    · intro hx h
      exact (not_lt_of_ge (abs_le.mpr h)) hx
  have hright : (∫ x in sᶜ, f x ∂μ) = u ^ 2 * μ.real {x : ℝ | u < |x|} := by
    calc
      (∫ x in sᶜ, f x ∂μ) = ∫ x in sᶜ, (fun _ : ℝ => u ^ 2) x ∂μ := by
        apply setIntegral_congr_fun hs.compl
        intro x hx
        have hx' : u < |x| := by
          have hnot : ¬ (-u ≤ x ∧ x ≤ u) := by simpa [s, Set.mem_Icc] using hx
          by_contra h
          exact hnot (abs_le.mp (le_of_not_gt h))
        simp [f, min_eq_right (le_of_lt hx')]
      _ = μ.real (sᶜ) * u ^ 2 := by rw [setIntegral_const, smul_eq_mul]
      _ = u ^ 2 * μ.real {x : ℝ | u < |x|} := by rw [hsComplement]; ring
  rw [hleft, hright] at hsplit
  exact hsplit.symm

/-- Mathlib's layer-cake formula applied to the capped square. -/
theorem integral_sq_min_abs_eq_layercake
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    (∫ x, (min |x| u) ^ 2 ∂μ) =
      ∫ t in Ioi 0, μ.real {x : ℝ | t < (min |x| u) ^ 2} := by
  let f : ℝ → ℝ := fun x => (min |x| u) ^ 2
  have hfmeas : Measurable f := by fun_prop
  have hfbdd : ∀ᵐ x ∂μ, ‖f x‖ ≤ u ^ 2 := by
    filter_upwards with x
    have hmin : 0 ≤ min |x| u := by
      by_cases hx : |x| ≤ u
      · rw [min_eq_left hx]
        exact abs_nonneg x
      · rw [min_eq_right (le_of_not_ge hx)]
        exact hu
    have hle : min |x| u ≤ u := min_le_right _ _
    have hsq : (min |x| u) ^ 2 ≤ u ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hle hmin,
        mul_le_mul_of_nonneg_right hmin hu]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq
  have hf : Integrable f μ := ⟨hfmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hfbdd⟩
  apply hf.integral_eq_integral_meas_lt
  exact Filter.Eventually.of_forall fun x => sq_nonneg (min |x| u)

/-- The capped layer-cake integrand vanishes above `u²`; below that level it
is the two-sided tail of the original law. -/
theorem integral_sq_min_abs_eq_layercake_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    (∫ x, (min |x| u) ^ 2 ∂μ) =
      ∫ t in Ioi 0, if t < u ^ 2 then μ.real {x : ℝ | t < x ^ 2} else 0 := by
  rw [integral_sq_min_abs_eq_layercake μ hu]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change μ.real {x : ℝ | t < (min |x| u) ^ 2} = _
  have hcap : {x : ℝ | t < (min |x| u) ^ 2} =
      {x : ℝ | t < u ^ 2 ∧ t < x ^ 2} := by
    ext x
    change t < (min |x| u) ^ 2 ↔ t < u ^ 2 ∧ t < x ^ 2
    by_cases hxu : |x| ≤ u
    · rw [min_eq_left hxu, sq_abs]
      have hsq : x ^ 2 ≤ u ^ 2 := by
        rw [← sq_abs x]
        exact (sq_le_sq₀ (abs_nonneg x) hu).2 hxu
      constructor
      · intro hx
        exact ⟨lt_of_lt_of_le hx hsq, hx⟩
      · rintro ⟨_, hx⟩
        exact hx
    · have hux : u < |x| := lt_of_not_ge hxu
      rw [min_eq_right (le_of_lt hux)]
      have hsq : u ^ 2 < x ^ 2 := by
        rw [← sq_abs x]
        exact (sq_lt_sq₀ hu (abs_nonneg x)).2 hux
      constructor
      · intro hx
        exact ⟨hx, lt_trans hx hsq⟩
      · rintro ⟨hx, _⟩
        exact hx
  have hset : {x : ℝ | t < u ^ 2 ∧ t < x ^ 2} =
      if t < u ^ 2 then {x : ℝ | t < x ^ 2} else ∅ := by
    ext x
    by_cases ht' : t < u ^ 2 <;> simp [ht']
  rw [hcap, hset]
  by_cases ht' : t < u ^ 2 <;> simp [ht']

/-- The first-moment analogue of the truncated-square layer-cake identity.
The expected absolute value capped at `u` is the integral of the two-sided
tail over `[0,u]`. -/
theorem integral_min_abs_eq_intervalIntegral_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    (∫ x, min |x| u ∂μ) =
      ∫ t in (0 : ℝ)..u, μ.real {x : ℝ | t < |x|} := by
  let f : ℝ → ℝ := fun x => min |x| u
  have hfmeas : Measurable f := by fun_prop
  have hfbdd : ∀ᵐ x ∂μ, ‖f x‖ ≤ u := by
    filter_upwards with x
    have hfnonneg : 0 ≤ f x := by
      dsimp [f]
      exact le_min (abs_nonneg x) hu
    have hfle : f x ≤ u := min_le_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg]
    exact hfle
  have hfi : Integrable f μ :=
    ⟨hfmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hfbdd⟩
  have hfnn : 0 ≤ᵐ[μ] f := Eventually.of_forall fun x => by
    dsimp [f]
    exact le_min (abs_nonneg x) hu
  have hlayer := hfi.integral_eq_integral_meas_lt hfnn
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < |x|}
  have hset : ∫ t in Ioi (0 : ℝ), μ.real {x : ℝ | t < f x} =
      ∫ t in Ioo (0 : ℝ) u, g t := by
    calc
      ∫ t in Ioi (0 : ℝ), μ.real {x : ℝ | t < f x} =
          ∫ t in Ioi (0 : ℝ), (Ioo (0 : ℝ) u).indicator g t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            have htail : {x : ℝ | t < f x} =
                if t < u then {x : ℝ | t < |x|} else ∅ := by
              ext x
              simp only [Set.mem_ofPred_eq]
              dsimp [f]
              rw [lt_min_iff]
              by_cases htu : t < u <;> simp [htu]
            change μ.real {x : ℝ | t < f x} = _
            rw [htail]
            by_cases htu : t < u
            · have htmem : t ∈ Ioo (0 : ℝ) u := ⟨ht, htu⟩
              simp [Set.indicator, htmem, g, htu]
            · have htmem : t ∉ Ioo (0 : ℝ) u := fun hm => htu hm.2
              simp [Set.indicator, htmem, g, htu]
      _ = ∫ t in Ioi (0 : ℝ) ∩ Ioo (0 : ℝ) u, g t :=
          setIntegral_indicator measurableSet_Ioo
      _ = ∫ t in Ioo (0 : ℝ) u, g t := by
          have hinter : Ioi (0 : ℝ) ∩ Ioo (0 : ℝ) u = Ioo (0 : ℝ) u := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
            constructor
            · exact fun ⟨_, h⟩ => h
            · exact fun h => ⟨h.1, h⟩
          rw [hinter]
  rw [hlayer, hset]
  rw [← integral_Icc_eq_integral_Ioo]
  rw [intervalIntegral.integral_of_le hu]
  exact integral_Icc_eq_integral_Ioc

/-- Exact tail-integral representation of the truncated second moment. The
endpoint correction is the mass strictly outside `[-u,u]`. -/
theorem truncatedSecondMoment_eq_layercake_sub_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 ≤ u) :
    truncatedSecondMoment μ u = truncatedSquareTailIntegral μ u -
      u ^ 2 * μ.real {x : ℝ | u < |x|} := by
  have hsplit := integral_sq_min_abs_eq_truncatedSecondMoment_add_tail μ hu
  have hlayer := integral_sq_min_abs_eq_layercake_tail μ hu
  change (∫ x, (min |x| u) ^ 2 ∂μ) =
    truncatedSecondMoment μ u + u ^ 2 * μ.real {x : ℝ | u < |x|} at hsplit
  rw [hlayer] at hsplit
  dsimp [truncatedSquareTailIntegral]
  linarith

/-- The cutoff layer-cake integral is the usual interval integral of the
two-sided square tail. -/
theorem truncatedSquareTailIntegral_eq_intervalIntegral
    (μ : Measure ℝ) {u : ℝ} (_hu : 0 ≤ u) :
    truncatedSquareTailIntegral μ u =
      ∫ t in (0:ℝ)..u ^ 2, μ.real {x : ℝ | t < x ^ 2} := by
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < x ^ 2}
  have hset : ∫ t in Ioi (0:ℝ), (if t < u ^ 2 then g t else 0) =
      ∫ t in Ioo (0:ℝ) (u ^ 2), g t := by
    calc
      ∫ t in Ioi (0:ℝ), (if t < u ^ 2 then g t else 0) =
          ∫ t in Ioi (0:ℝ), (Ioo (0:ℝ) (u ^ 2)).indicator g t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            by_cases htu : t < u ^ 2
            · have hmem : t ∈ Ioo (0:ℝ) (u ^ 2) := ⟨ht, htu⟩
              simp [Set.indicator, htu, hmem]
            · have hnot : t ∉ Ioo (0:ℝ) (u ^ 2) := fun hm => htu hm.2
              simp [Set.indicator, htu, hnot]
      _ = ∫ t in Ioi (0:ℝ) ∩ Ioo (0:ℝ) (u ^ 2), g t :=
          setIntegral_indicator measurableSet_Ioo
      _ = ∫ t in Ioo (0:ℝ) (u ^ 2), g t := by
          have hinter : Ioi (0:ℝ) ∩ Ioo (0:ℝ) (u ^ 2) = Ioo (0:ℝ) (u ^ 2) := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
            tauto
          rw [hinter]
  change (∫ t in Ioi (0:ℝ), (if t < u ^ 2 then μ.real {x : ℝ | t < x ^ 2} else 0)) = _
  rw [hset]
  rw [← integral_Icc_eq_integral_Ioo]
  rw [intervalIntegral.integral_of_le (sq_nonneg u)]
  exact integral_Icc_eq_integral_Ioc

/-- A finite limit for the normalized layer-cake integral and for
`u^α` times the two-sided tail gives the corresponding normalized truncated
second-moment limit. -/
theorem tendsto_truncatedSecondMoment_scale_of_layercake_and_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment μ u) atTop (nhds (A - B)) := by
  have hsub : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|}) atTop (nhds (A - B)) :=
    hA.sub hB
  have heq : (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment μ u) =ᶠ[atTop]
      fun u => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|} := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [truncatedSecondMoment_eq_layercake_sub_tail μ hu.le,
      truncatedSquareTailIntegral]
    rw [mul_sub]
    have hpow : u ^ (α - 2) * u ^ 2 = u ^ α := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu]
      congr 1
      ring
    rw [← mul_assoc, hpow]
  exact hsub.congr' heq.symm

/-- A two-sided power-tail asymptotic determines the normalized truncated
second-moment constant. If `u^α μ(|x| > u) → B` with `0 < α < 2`, then
`u^(α-2) ∫_{|x|≤u} x^2 μ(dx) → α B / (2-α)`. -/
theorem tendsto_truncatedSecondMoment_scale_of_twoSidedTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α B : ℝ}
    (_hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment μ u) atTop
      (nhds (α * B / (2 - α))) := by
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < x ^ 2}
  let β : ℝ := α / 2
  have hβ₁ : β < 1 := by dsimp [β]; linarith
  have hg_anti : Antitone g := by
    intro s t hst
    apply measureReal_mono (μ := μ) (s₁ := {x : ℝ | t < x ^ 2})
      (s₂ := {x : ℝ | s < x ^ 2}) (by
        intro x hx
        exact lt_of_le_of_lt hst hx) (by finiteness)
  have hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    exact measureReal_nonneg
  have hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1 := by
    intro t ht
    exact measureReal_le_one
  have hTailSqrt : Tendsto
      (fun t : ℝ => (Real.sqrt t) ^ α *
        μ.real {x : ℝ | Real.sqrt t < |x|}) atTop (nhds B) := by
    exact hTail.comp Real.tendsto_sqrt_atTop
  have hlimSquare : Tendsto (fun t : ℝ => t ^ β * g t) atTop (nhds B) := by
    apply hTailSqrt.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hpow : t ^ β = (Real.sqrt t) ^ α := by
      dsimp [β]
      exact Real.rpow_div_two_eq_sqrt α ht.le
    have hset : {x : ℝ | t < x ^ 2} = {x : ℝ | Real.sqrt t < |x|} := by
      ext x
      constructor
      · intro hx
        apply (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).1
        simpa [Real.sq_sqrt ht.le] using hx
      · intro hx
        have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).2 hx
        simpa [Real.sq_sqrt ht.le] using hsq
    simp only [hpow, g, hset]
  have hKaramata :=
    _root_.Asymptotics.tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul
      (g := g) (β := β) (C := B) hβ₁ hB hg_anti hg_nonneg hg_le_one hlimSquare
  have hsquare : Tendsto
      (fun u : ℝ => (u ^ 2) ^ (β - 1) *
        ∫ t in (0:ℝ)..u ^ 2, g t) atTop (nhds (B / (1 - β))) := by
    apply hKaramata.comp
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max (1:ℝ) b)] with u hu
    have h1u : 1 ≤ u := le_trans (le_max_left 1 b) hu
    have hbu : b ≤ u := le_trans (le_max_right 1 b) hu
    have huu : u ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    exact hbu.trans huu
  have hmain : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u)
      atTop (nhds (B / (1 - β))) := by
    apply hsquare.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    rw [truncatedSquareTailIntegral_eq_intervalIntegral μ hu.le]
    have hpow : (u ^ (2:ℕ)) ^ (β - 1) = u ^ (α - 2) := by
      rw [← Real.rpow_natCast u 2]
      calc
        (u ^ (2:ℝ)) ^ (β - 1) = u ^ ((2:ℝ) * (β - 1)) :=
          (Real.rpow_mul hu.le 2 (β - 1)).symm
        _ = u ^ (α - 2) := by
          congr 1
          dsimp [β]
          ring
    rw [hpow]
  have hmoment := tendsto_truncatedSecondMoment_scale_of_layercake_and_tail μ hmain hTail
  have hconst : B / (1 - β) - B = α * B / (2 - α) := by
    dsimp [β]
    field_simp [ne_of_gt (by linarith : 0 < (2:ℝ) - α)]
    ring
  rw [hconst] at hmoment
  exact hmoment

/-- Regular variation of the two-sided tail determines the truncated second
moment without requiring the slowly varying factor to converge. If
`T(u) = μ(|x| > u)` is regularly varying with index `-α`, where
`0 < α < 2`, then
`∫_{|x|≤u} x² μ(dx) / (u² T(u)) → α / (2-α)`. -/
theorem tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hTail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => μ.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun u : ℝ =>
      truncatedSecondMoment μ u /
        (u ^ 2 * μ.real {x : ℝ | u < |x|})) atTop
      (nhds (α / (2 - α))) := by
  let T : ℝ → ℝ := fun u => μ.real {x : ℝ | u < |x|}
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < x ^ 2}
  let β : ℝ := α / 2
  have hβ₀ : 0 < β := by dsimp [β]; linarith
  have hβ₁ : β < 1 := by dsimp [β]; linarith
  have hsetSqrt (t : ℝ) (ht : 0 ≤ t) :
      {x : ℝ | t < x ^ 2} = {x : ℝ | Real.sqrt t < |x|} := by
    ext x
    constructor
    · intro hx
      apply (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).1
      simpa [Real.sq_sqrt ht] using hx
    · intro hx
      have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).2 hx
      simpa [Real.sq_sqrt ht] using hsq
  have hg_anti : Antitone g := by
    intro s t hst
    dsimp [g]
    apply measureReal_mono (μ := μ) (s₁ := {x : ℝ | t < x ^ 2})
      (s₂ := {x : ℝ | s < x ^ 2}) (by
        intro x hx
        exact lt_of_le_of_lt hst hx) (by finiteness)
  have hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    exact measureReal_nonneg
  have hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1 := by
    intro t ht
    exact measureReal_le_one
  have hposT : ∀ᶠ u : ℝ in atTop, 0 < T u := by
    simpa [T] using hTail.eventually_pos
  have hposG : ∀ᶠ t : ℝ in atTop, 0 < g t := by
    have hsqrt := Real.tendsto_sqrt_atTop.eventually hposT
    filter_upwards [hsqrt, eventually_gt_atTop (0:ℝ)] with t htT ht
    rw [show g t = T (Real.sqrt t) by
      dsimp [g, T]
      rw [hsetSqrt t ht.le]]
    exact htT
  have hregG : Asymptotics.IsRegularlyVaryingAtTop g (-β) := by
    refine ⟨hposG, ?_⟩
    intro c hc
    let d : ℝ := Real.sqrt c
    have hd : 0 < d := Real.sqrt_pos.2 hc
    have hratioT := hTail.ratio_tendsto (c := d) hd
    have hratio := hratioT.comp Real.tendsto_sqrt_atTop
    have hratioEq : (fun t : ℝ => g (c * t) / g t) =ᶠ[atTop]
        fun t => T (d * Real.sqrt t) / T (Real.sqrt t) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      have hct : 0 ≤ c * t := mul_nonneg hc.le ht.le
      have hgct : g (c * t) = T (Real.sqrt (c * t)) := by
        dsimp [g, T]
        rw [hsetSqrt (c * t) hct]
      have hgt : g t = T (Real.sqrt t) := by
        dsimp [g, T]
        rw [hsetSqrt t ht.le]
      rw [hgct, hgt, show Real.sqrt (c * t) = d * Real.sqrt t by
        dsimp [d]
        exact Real.sqrt_mul (le_of_lt hc) t]
    have hpow : d ^ (-α) = c ^ (-β) := by
      convert (Real.rpow_div_two_eq_sqrt (-α) hc.le).symm using 1
      · congr 1
        ring
    have hratio' : Tendsto
        (fun t : ℝ => T (d * Real.sqrt t) / T (Real.sqrt t)) atTop
        (nhds (c ^ (-β))) := by
      rw [← hpow]
      exact hratio
    exact hratio'.congr' hratioEq.symm
  have hKaramata := hregG.tendsto_intervalIntegral_div_mul_of_antitone
    (by linarith : 0 ≤ β) hβ₁ hg_anti hg_nonneg hg_le_one
  have hu2 : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with u hu
    have h1u : 1 ≤ u := le_trans (le_max_left 1 b) hu
    have hbu : b ≤ u := le_trans (le_max_right 1 b) hu
    have huu : u ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    exact hbu.trans huu
  have hscaled := hKaramata.comp hu2
  have hsetSquare (u : ℝ) (hu : 0 ≤ u) :
      {x : ℝ | u ^ 2 < x ^ 2} = {x : ℝ | u < |x|} := by
    ext x
    constructor
    · intro hx
      exact (sq_lt_sq₀ hu (abs_nonneg x)).1 (by simpa [sq_abs] using hx)
    · intro hx
      have hsq := (sq_lt_sq₀ hu (abs_nonneg x)).2 hx
      simpa [sq_abs] using hsq
  have hdenEq : (fun u : ℝ => u ^ 2 * g (u ^ 2)) =ᶠ[atTop]
      fun u => u ^ 2 * T u := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    congr 1
    dsimp [g, T]
    rw [hsetSquare u hu]
  have hscale' : Tendsto (fun u : ℝ =>
      (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u)) atTop
      (nhds (1 / (1 - β))) := by
    have heq : (fun u : ℝ =>
        (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u)) =ᶠ[atTop]
        fun u => (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * g (u ^ 2)) := by
      filter_upwards [hdenEq] with u hu
      rw [hu]
    exact hscaled.congr' heq.symm
  have hlayer : Tendsto (fun u : ℝ =>
      truncatedSquareTailIntegral μ u / (u ^ 2 * T u)) atTop
      (nhds (1 / (1 - β))) := by
    have heq : (fun u : ℝ =>
        truncatedSquareTailIntegral μ u / (u ^ 2 * T u)) =ᶠ[atTop]
        fun u => (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
      rw [truncatedSquareTailIntegral_eq_intervalIntegral μ hu]
    exact hscale'.congr' heq.symm
  have hsub : Tendsto (fun u : ℝ =>
      truncatedSquareTailIntegral μ u / (u ^ 2 * T u) - 1) atTop
      (nhds (1 / (1 - β) - 1)) := by
    simpa using hlayer.sub tendsto_const_nhds
  have hmomentEq : (fun u : ℝ =>
      truncatedSecondMoment μ u / (u ^ 2 * T u)) =ᶠ[atTop]
      fun u => truncatedSquareTailIntegral μ u / (u ^ 2 * T u) - 1 := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hposT] with u hu hTu
    rw [truncatedSecondMoment_eq_layercake_sub_tail μ hu.le]
    dsimp [T]
    have hden : u ^ 2 * μ.real {x : ℝ | u < |x|} ≠ 0 :=
      ne_of_gt (mul_pos (sq_pos_of_pos hu) hTu)
    have htailNe : μ.real {x : ℝ | u < |x|} ≠ 0 := by
      simpa [T] using hTu.ne'
    field_simp [hden, htailNe]
  have hconst : 1 / (1 - β) - 1 = α / (2 - α) := by
    dsimp [β]
    field_simp [ne_of_gt (by linarith : 0 < 2 - α)]
    ring
  rw [hconst] at hsub
  exact hsub.congr' hmomentEq.symm

end ProbabilityTheory
