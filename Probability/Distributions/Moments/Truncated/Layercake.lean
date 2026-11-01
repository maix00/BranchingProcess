/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Layercake
public import Probability.Distributions.Moments.Truncated.Basic

/-!
# Layer-cake identities for truncated second moments

These identities express truncated and capped moments through the two-sided
square-tail function. They provide the bridge between moment truncation and
integrated-tail asymptotics.

## Public declarations

- `truncatedSquareTailIntegral μ u` is the layer-cake integral over levels
  `0 < t < u²` of `μ(|x| > √t)`.
- The capped second moment satisfies
  `∫ min(|x|,u)² dμ = Vμ(u) + u² μ(|x|>u)` for probability measures and `u≥0`.
- The capped-moment layer-cake identities give exact integral formulas for
  `truncatedSquareTailIntegral` and `truncatedSecondMoment`.
- `truncatedSquareTailIntegral μ u = ∫₀^{u²} μ(x²>t) dt` for `u≥0`.

For a probability measure `\mu` and `u\ge0`, capping and layer-cake give

\[\begin{aligned}
\int_{\mathbb R}\min(|x|,u)^2\,d\mu(x)
&=V_\mu(u)+u^2\mu\{|x|>u\},\\
\int_0^{u^2}\mu\{x^2>t\}\,dt
&=V_\mu(u)+u^2\mu\{|x|>u\}.
\end{aligned}\]
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

end ProbabilityTheory

end
