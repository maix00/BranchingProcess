import Probability.BranchingRandomWalk.Walk.Law
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Scale
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Assumptions for the variance-one Mogulskii theorem

These predicates record the hypotheses of the `α = 2` theorem without
bundling a new random-walk type.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- A one-step law has mean zero and the specified second moment.  For a
centered law this parameter is its variance. -/
def IsCenteredSecondMoment (ν : Measure ℝ) (variance : ℝ) : Prop :=
  (∫ x, x ∂ν) = 0 ∧ (∫ x, x ^ 2 ∂ν) = variance

/-- A one-step law has mean zero and second moment one. -/
def IsCenteredUnitSecondMoment (ν : Measure ℝ) : Prop :=
  IsCenteredSecondMoment ν 1

/-- A probability law with second moment one has a square-integrable identity
random variable. -/
theorem IsCenteredUnitSecondMoment.memLp_two
    {ν : Measure ℝ} (hν : IsCenteredUnitSecondMoment ν) :
    MemLp id 2 ν := by
  apply (memLp_two_iff_integrable_sq
    stronglyMeasurable_id.aestronglyMeasurable).2
  exact Integrable.of_integral_ne_zero (by
    rw [show (∫ x, id x ^ 2 ∂ν) = 1 by simpa [id] using hν.2]
    norm_num)

/-- Dividing centered increments with second moment `sigma²` by a positive
standard deviation `sigma` produces centered unit-second-moment increments. -/
theorem IsCenteredSecondMoment.map_div
    {ν : Measure ℝ} {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    IsCenteredUnitSecondMoment (ν.map fun x => x / sigma) := by
  constructor
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => x / sigma)
      (f := fun x : ℝ => x) (measurable_id.div_const sigma).aemeasurable
      measurable_id.aestronglyMeasurable]
    rw [integral_div, hν.1, zero_div]
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => x / sigma)
      (f := fun x : ℝ => x ^ 2) (measurable_id.div_const sigma).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simp_rw [div_pow]
    rw [integral_div, hν.2]
    exact div_self (pow_ne_zero 2 hsigma.ne')

/-- Reflection preserves a centered second-moment hypothesis. -/
theorem IsCenteredSecondMoment.map_neg
    {ν : Measure ℝ} {variance : ℝ}
    (hν : IsCenteredSecondMoment ν variance) :
    IsCenteredSecondMoment (ν.map fun x => -x) variance := by
  constructor
  · calc
      (∫ x, x ∂ν.map fun x => -x) = ∫ x, -x ∂ν := by
        simpa using integral_map (μ := ν) (φ := fun x : ℝ => -x)
          measurable_neg.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := by rw [integral_neg, hν.1, neg_zero]
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => -x)
      (f := fun x : ℝ => x ^ 2)
      measurable_neg.aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simpa using hν.2

/-- Reflection preserves the centered unit-second-moment hypothesis. -/
theorem IsCenteredUnitSecondMoment.map_neg
    {ν : Measure ℝ} (hν : IsCenteredUnitSecondMoment ν) :
    IsCenteredUnitSecondMoment (ν.map fun x => -x) :=
  IsCenteredSecondMoment.map_neg hν

/-- A spatial scale diverges while remaining negligible compared with the
diffusive scale. -/
def IsMogulskiiScale (scale : ℕ → ℝ) : Prop :=
  IsSmallDeviationScale scale (fun n => Real.sqrt n)

theorem isMogulskiiScale_iff {scale : ℕ → ℝ} :
    IsMogulskiiScale scale ↔
      IsSmallDeviationScale scale (fun n => Real.sqrt n) := Iff.rfl

theorem IsMogulskiiScale.eventually_pos {scale : ℕ → ℝ}
    (hscale : IsMogulskiiScale scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
  IsSmallDeviationScale.eventually_pos hscale

/-- The squared spatial scale is negligible compared with elapsed time. -/
theorem IsMogulskiiScale.tendsto_sq_div_natCast_zero
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    Tendsto (fun n => scale n ^ 2 / (n : ℝ)) atTop (nhds 0) := by
  have h := hscale.2.pow 2
  convert h using 1
  · funext n
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  · norm_num

/-- Equivalently, the number of diffusive-scale blocks available by time
`n` diverges. -/
theorem IsMogulskiiScale.tendsto_natCast_div_sq_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale) :
    Tendsto (fun n : ℕ => (n : ℝ) / scale n ^ 2) atTop atTop := by
  have hzero := hscale.tendsto_sq_div_natCast_zero
  have hpos : ∀ᶠ n in atTop, 0 < scale n ^ 2 / (n : ℝ) := by
    filter_upwards [hscale.eventually_pos, eventually_gt_atTop 0] with n hs hn
    positivity
  have hwithin : Tendsto (fun n : ℕ => scale n ^ 2 / (n : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  apply hinv.congr'
  filter_upwards [hscale.eventually_pos, eventually_gt_atTop 0] with n hs hn
  dsimp
  field_simp [ne_of_gt hs, Nat.cast_ne_zero.mpr hn.ne']

end ProbabilityTheory.RandomWalk
