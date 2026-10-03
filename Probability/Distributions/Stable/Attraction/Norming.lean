module

public import Probability.Distributions.Moments.Truncated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Norming and scales in a stable domain of attraction

These deterministic quantities are defined from the one-step increment law `ν`.
Under attraction to a nondegenerate `α`-stable law, the normalized truncated
second moment is slowly varying; the definition alone does not assert that
property. The limiting stable law and the functional limit theorem remain
separate data.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

/-- The truncated-moment factor `L*` associated with the input increment law
`ν`. This definition makes no regularity assertion; proving slow variation
from a stable domain-of-attraction hypothesis is a separate theorem. -/
noncomputable def stableSlowVariation
    (α : ℝ) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ (α - 2) * truncatedSecondMoment ν u

/-- A normalization satisfies the asymptotic inverse-norming condition for a
stable domain of attraction. The ratio tends to one rather than requiring an
exact identity. Positivity and divergence are recorded separately because
the asymptotic relation alone does not constrain finitely many initial terms. -/
def IsStableNorming (α : ℝ) (ν : Measure ℝ) (normalization : ℕ → ℝ) : Prop :=
  (∀ n, 0 < n → 0 < normalization n) ∧
    Tendsto normalization atTop atTop ∧
      Tendsto (fun n =>
        normalization n ^ α / stableSlowVariation α ν (normalization n) /
          (n : ℝ)) atTop (nhds 1)

/-- The logarithmic normalization in Mogulskii's `α`-stable
small-deviation theorem. -/
noncomputable def stableSmallDeviationRate
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  scale n ^ α / ((n : ℝ) * stableSlowVariation α ν (scale n))

@[simp] theorem stableSlowVariation_two (ν : Measure ℝ) (u : ℝ) :
    stableSlowVariation 2 ν u = truncatedSecondMoment ν u := by
  simp [stableSlowVariation]

@[simp] theorem stableSmallDeviationRate_two
    (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableSmallDeviationRate 2 ν scale n =
      scale n ^ 2 / ((n : ℝ) * truncatedSecondMoment ν (scale n)) := by
  simp [stableSmallDeviationRate]

/-- The rate normalization associated to a stable small-deviation scale. It is
the reciprocal of `stableSmallDeviationRate`; its value is
`n * L*ν (x n) / (x n)^α`. -/
noncomputable def stableRateNormalization
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  (stableSmallDeviationRate α ν scale n)⁻¹

/-- The rate normalization written out: `n * L* (x n) / x n ^ α`. -/
@[simp] theorem stableRateNormalization_eq
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α ν scale n =
      (n : ℝ) * stableSlowVariation α ν (scale n) / scale n ^ α := by
  rw [stableRateNormalization, stableSmallDeviationRate, inv_div]

/-! ## Positivity of `L*` -/

/-- Mogulskii's slowly varying function is positive at a positive scale as soon
as the truncated second moment is. -/
theorem stableSlowVariation_pos {α : ℝ} {ν : Measure ℝ} {u : ℝ}
    (hu : 0 < u) (hmoment : 0 < truncatedSecondMoment ν u) :
    0 < stableSlowVariation α ν u :=
  mul_pos (Real.rpow_pos_of_pos hu _) hmoment

/-- A nonvanishing second moment makes the truncated second moment eventually
positive. -/
theorem eventually_truncatedSecondMoment_pos (ν : Measure ℝ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ u in atTop, 0 < truncatedSecondMoment ν u :=
  (tendsto_truncatedSecondMoment ν hν).eventually (isOpen_Ioi.mem_nhds hpos)

/-- Consequently `L*` is eventually positive. -/
theorem eventually_stableSlowVariation_pos (α : ℝ) (ν : Measure ℝ)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ u in atTop, 0 < stableSlowVariation α ν u := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_truncatedSecondMoment_pos ν hν hpos] with u hu hmoment
  exact stableSlowVariation_pos hu hmoment

/-! ## The inverse norming function -/

/-- The characteristic step time at spatial scale `u` for increment law `ν`:
`κν(u) = u ^ α / L*ν(u)`. Under the corresponding regular-variation
hypotheses, this is asymptotically inverse to the stable normalization.

At `α = 2` it is `u ^ 2 / truncatedSecondMoment ν u`, the diffusive time scale. -/
noncomputable def stableScaleTime (α : ℝ) (ν : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ α / stableSlowVariation α ν u

@[simp] theorem stableScaleTime_two (ν : Measure ℝ) (u : ℝ) :
    stableScaleTime 2 ν u = u ^ 2 / truncatedSecondMoment ν u := by
  simp [stableScaleTime]

/-- Under the paper's asymptotic norming condition, the quadratic norming has
the expected variance scale. The exact identity `B*(B(n)) = n` is not needed:
the defining asymptotic `B*(B(n))/n → 1` and convergence of truncated second
moments suffice. -/
theorem IsStableNorming.tendsto_sq_div_nat
    {ν : Measure ℝ} (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℕ → ℝ} (h : IsStableNorming 2 ν b) :
    Tendsto (fun n : ℕ => b n ^ 2 / (n : ℝ)) atTop
      (nhds (∫ x, x ^ 2 ∂ν)) := by
  have hnat : Tendsto (fun n : ℕ => truncatedSecondMoment ν (b n)) atTop
      (nhds (∫ x, x ^ 2 ∂ν)) :=
    (tendsto_truncatedSecondMoment ν hν).comp h.2.1
  have hratio : Tendsto
      (fun n : ℕ => stableScaleTime 2 ν (b n) / (n : ℝ)) atTop (nhds 1) := by
    simpa [stableScaleTime, stableSlowVariation_two] using h.2.2
  have hproduct : Tendsto
      (fun n : ℕ => stableScaleTime 2 ν (b n) / (n : ℝ) *
        truncatedSecondMoment ν (b n)) atTop
      (nhds (1 * (∫ x, x ^ 2 ∂ν))) := hratio.mul hnat
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime 2 ν (b n) / (n : ℝ) := by
    simpa only [Set.mem_Ioi] using
      hratio.eventually (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq : (fun n : ℕ => b n ^ 2 / (n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime 2 ν (b n) / (n : ℝ) *
        truncatedSecondMoment ν (b n) := by
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hr hn
    have hLne : truncatedSecondMoment ν (b n) ≠ 0 := by
      intro hzero
      have hpos := hr
      rw [stableScaleTime_two, hzero] at hpos
      simp at hpos
    rw [stableScaleTime_two]
    field_simp [hLne, show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  simpa using hproduct.congr' heq.symm

/-- The rate normalization is the number of steps divided by the scale time: `λ n = n / B* (x n)`,
the number of blocks of `B* (x n)` steps that fit into the `n` steps of the walk. -/
theorem stableRateNormalization_eq_natCast_div_stableScaleTime
    (α : ℝ) (ν : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α ν scale n = (n : ℝ) / stableScaleTime α ν (scale n) := by
  simp only [stableRateNormalization_eq, stableScaleTime, div_eq_mul_inv]
  rw [mul_inv_rev, inv_inv]
  ring

end ProbabilityTheory
