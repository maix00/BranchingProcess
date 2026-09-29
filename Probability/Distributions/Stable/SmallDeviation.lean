import Probability.Distributions.Stable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Small-deviation scales associated with a stable law

These are the deterministic quantities in Mogulskii's stable small-deviation
theorem.  For an `α`-stable limit law `μ`, the slowly varying function is

`u ↦ u ^ (α - 2) * ∫ x in [-u, u], x ^ 2 ∂μ`.

The functional limit theorem and the stable-process small-ball constant are
kept separate from these definitions.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory

/-- The second moment truncated to the symmetric interval of radius `u`. -/
noncomputable def truncatedSecondMoment (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x in Set.Icc (-u) u, x ^ 2 ∂μ

/-- Mogulskii's slowly varying function `L*` associated with an `α`-stable
limit law. -/
noncomputable def stableSlowVariation
    (α : ℝ) (μ : Measure ℝ) (u : ℝ) : ℝ :=
  u ^ (α - 2) * truncatedSecondMoment μ u

/-- A normalization satisfies the equation used in the stable Mogulskii
theorem.  Positivity and divergence are stated explicitly because the
equation alone does not constrain the value at time zero. -/
def IsStableNorming (α : ℝ) (μ : Measure ℝ) (normalization : ℕ → ℝ) : Prop :=
  (∀ n, 0 < n → 0 < normalization n) ∧
    Tendsto normalization atTop atTop ∧
      ∀ n, 0 < n →
        normalization n ^ α / stableSlowVariation α μ (normalization n) = n

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

end ProbabilityTheory
