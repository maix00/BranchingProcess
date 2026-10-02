module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Normalization
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Layer-cake representation of truncated moments

This file connects the truncated second moment in Mogulskii's normalization to
bounded layer-cake integrals.  It uses Mathlib's general layer-cake theorem;
the stable-law tail asymptotics are developed separately.
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

/-- A finite limit for the normalized layer-cake integral and for
`u^α` times the two-sided tail gives the corresponding limit of Mogulskii's
`L*`. This is the analytic bridge; proving these two limits for a stable law
is a separate tail-asymptotic theorem. -/
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

end ProbabilityTheory
