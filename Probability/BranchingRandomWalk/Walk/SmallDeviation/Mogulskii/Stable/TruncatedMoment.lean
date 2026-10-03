module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Normalization
public import Analysis.Asymptotics.PowerTailIntegral
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Layer-cake representation of truncated moments

This file connects the truncated second moment in Mogulskii's normalization to
bounded layer-cake integrals.  It uses Mathlib's general layer-cake theorem;
it also proves the exact implication from a two-sided power-tail asymptotic to
the limiting truncated second moment.  Establishing the stable law's tail
asymptotic remains a separate distributional result.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

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
`u^α` times the two-sided tail gives the corresponding limit of Mogulskii's
`L*`. -/
theorem tendsto_stableSlowVariation_of_layercake_and_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α μ) atTop (nhds (A - B)) := by
  have hsub : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|}) atTop (nhds (A - B)) :=
    hA.sub hB
  have heq : (fun u : ℝ => stableSlowVariation α μ u) =ᶠ[atTop]
      fun u => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|} := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [stableSlowVariation, truncatedSecondMoment_eq_layercake_sub_tail μ hu.le,
      truncatedSquareTailIntegral]
    rw [mul_sub]
    have hpow : u ^ (α - 2) * u ^ 2 = u ^ α := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu]
      congr 1
      ring
    rw [← mul_assoc, hpow]
  exact hsub.congr' heq.symm

/-- A two-sided power-tail asymptotic determines the stable truncated-second-
moment constant. If `u^α μ(|x| > u) → B` with `0 < α < 2`, then
`u^(α-2) E[min(|X|,u)^2] → α B / (2-α)`. -/
theorem tendsto_stableSlowVariation_of_twoSidedTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α B : ℝ}
    (_hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α μ) atTop
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
  have hstable := tendsto_stableSlowVariation_of_layercake_and_tail μ hmain hTail
  have hconst : B / (1 - β) - B = α * B / (2 - α) := by
    dsimp [β]
    field_simp [ne_of_gt (by linarith : 0 < (2:ℝ) - α)]
    ring
  rw [hconst] at hstable
  exact hstable

end ProbabilityTheory
