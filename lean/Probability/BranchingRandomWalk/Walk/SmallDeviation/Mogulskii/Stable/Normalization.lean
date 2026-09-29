module

public import Probability.Distributions.Stable.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Small-deviation scales associated with a stable law

These are the deterministic quantities in Mogulskii's stable small-deviation
theorem.  For an `α`-stable limit law `μ`, the slowly varying function is

`u ↦ u ^ (α - 2) * ∫ x in [-u, u], x ^ 2 ∂μ`.

The functional limit theorem and the stable-process small-ball constant are
kept separate from these definitions.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

/-- The second moment truncated to the symmetric interval of radius `u`. -/
noncomputable def truncatedSecondMoment (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x in Set.Icc (-u) u, x ^ 2 ∂μ

/-- Mogulskii's slowly varying function `L*` associated with an `α`-stable
limit law. -/
noncomputable def stableSlowVariation
    (α : ℝ) (μ : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ (α - 2) * truncatedSecondMoment μ u

/-- A normalization satisfies the asymptotic inverse-norming condition used
in the stable Mogulskii theorem.  The paper requires `B^*(B(n)) ∼ n`, not an
exact identity. Positivity and divergence are recorded separately because
the asymptotic relation alone does not constrain finitely many initial terms. -/
def IsStableNorming (α : ℝ) (μ : Measure ℝ) (normalization : ℕ → ℝ) : Prop :=
  (∀ n, 0 < n → 0 < normalization n) ∧
    Tendsto normalization atTop atTop ∧
      Tendsto (fun n =>
        normalization n ^ α / stableSlowVariation α μ (normalization n) /
          (n : ℝ)) atTop (nhds 1)

/-- The logarithmic normalization in Mogulskii's `α`-stable
small-deviation theorem. -/
noncomputable def stableSmallDeviationRate
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  scale n ^ α / ((n : ℝ) * stableSlowVariation α μ (scale n))

@[simp] theorem stableSlowVariation_two (μ : Measure ℝ) (u : ℝ) :
    stableSlowVariation 2 μ u = truncatedSecondMoment μ u := by
  simp [stableSlowVariation]

@[simp] theorem stableSmallDeviationRate_two
    (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableSmallDeviationRate 2 μ scale n =
      scale n ^ 2 / ((n : ℝ) * truncatedSecondMoment μ (scale n)) := by
  simp [stableSmallDeviationRate]

/-- Mogulskii's normalization `λ n = n * L* (x n) / x n ^ α` in the stable small-deviation theorem: the
reciprocal of `stableSmallDeviationRate`. The theorem states `ln P (s n (·) ∈ G) ~ C * H (G) * λ n` with
`H` the energy functional of the corridor, so `λ n` is the factor scaling the rate, while
`stableSmallDeviationRate` is the reciprocal factor scaling the small-deviation scale itself. -/
noncomputable def stableRateNormalization
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  (stableSmallDeviationRate α μ scale n)⁻¹

/-- The rate normalization written out: `n * L* (x n) / x n ^ α`. -/
@[simp] theorem stableRateNormalization_eq
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α μ scale n =
      (n : ℝ) * stableSlowVariation α μ (scale n) / scale n ^ α := by
  rw [stableRateNormalization, stableSmallDeviationRate, inv_div]

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

/-! ## Positivity of `L*` -/

/-- Mogulskii's slowly varying function is positive at a positive scale as soon
as the truncated second moment is. -/
theorem stableSlowVariation_pos {α : ℝ} {μ : Measure ℝ} {u : ℝ}
    (hu : 0 < u) (hmoment : 0 < truncatedSecondMoment μ u) :
    0 < stableSlowVariation α μ u :=
  mul_pos (Real.rpow_pos_of_pos hu _) hmoment

/-- A nonvanishing second moment makes the truncated second moment eventually
positive. -/
theorem eventually_truncatedSecondMoment_pos (μ : Measure ℝ)
    (hμ : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < ∫ x, x ^ 2 ∂μ) :
    ∀ᶠ u in atTop, 0 < truncatedSecondMoment μ u :=
  (tendsto_truncatedSecondMoment μ hμ).eventually (isOpen_Ioi.mem_nhds hpos)

/-- Consequently `L*` is eventually positive. -/
theorem eventually_stableSlowVariation_pos (α : ℝ) (μ : Measure ℝ)
    (hμ : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < ∫ x, x ^ 2 ∂μ) :
    ∀ᶠ u in atTop, 0 < stableSlowVariation α μ u := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_truncatedSecondMoment_pos μ hμ hpos] with u hu hmoment
  exact stableSlowVariation_pos hu hmoment

/-! ## The inverse norming function -/

/-- The number of steps in which a walk whose increments have law `μ` travels a distance of order
`u`: the function `B* (u) = u ^ α / L* (u)` of the original paper's (4), whose inverse is the norming
`B` of (2), so that `B* (B n) ↝ n` there. Its regular variation, `B* (a * u) ~ a ^ α * B* u`, is what
carries the walk estimate over to the stable process in (43).

At `α = 2` it is `u ^ 2 / truncatedSecondMoment μ u`, the diffusive time scale. -/
noncomputable def stableScaleTime (α : ℝ) (μ : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ α / stableSlowVariation α μ u

@[simp] theorem stableScaleTime_two (μ : Measure ℝ) (u : ℝ) :
    stableScaleTime 2 μ u = u ^ 2 / truncatedSecondMoment μ u := by
  simp [stableScaleTime]

/-- Under the paper's asymptotic norming condition, the quadratic norming has
the expected variance scale. The exact identity `B*(B(n)) = n` is not needed:
the defining asymptotic `B*(B(n))/n → 1` and convergence of truncated second
moments suffice. -/
theorem IsStableNorming.tendsto_sq_div_nat
    {μ : Measure ℝ} (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    {b : ℕ → ℝ} (h : IsStableNorming 2 μ b) :
    Tendsto (fun n : ℕ => b n ^ 2 / (n : ℝ)) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) := by
  have hnat : Tendsto (fun n : ℕ => truncatedSecondMoment μ (b n)) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) :=
    (tendsto_truncatedSecondMoment μ hμ).comp h.2.1
  have hratio : Tendsto
      (fun n : ℕ => stableScaleTime 2 μ (b n) / (n : ℝ)) atTop (nhds 1) := by
    simpa [stableScaleTime, stableSlowVariation_two] using h.2.2
  have hproduct : Tendsto
      (fun n : ℕ => stableScaleTime 2 μ (b n) / (n : ℝ) *
        truncatedSecondMoment μ (b n)) atTop
      (nhds (1 * (∫ x, x ^ 2 ∂μ))) := hratio.mul hnat
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime 2 μ (b n) / (n : ℝ) := by
    simpa only [Set.mem_Ioi] using
      hratio.eventually (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))
  have heq : (fun n : ℕ => b n ^ 2 / (n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime 2 μ (b n) / (n : ℝ) *
        truncatedSecondMoment μ (b n) := by
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hr hn
    have hLne : truncatedSecondMoment μ (b n) ≠ 0 := by
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
    (α : ℝ) (μ : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableRateNormalization α μ scale n = (n : ℝ) / stableScaleTime α μ (scale n) := by
  simp only [stableRateNormalization_eq, stableScaleTime, div_eq_mul_inv]
  rw [mul_inv_rev, inv_inv]
  ring

end ProbabilityTheory
