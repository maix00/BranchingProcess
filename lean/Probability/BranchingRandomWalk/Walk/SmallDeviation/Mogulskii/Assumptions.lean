import Probability.BranchingRandomWalk.Walk.Law
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Scale
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Assumptions for the variance-one Mogulskii theorem

These predicates record the hypotheses of the `α = 2` theorem without
bundling a new random-walk type.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- A one-step law has mean zero and second moment one. -/
def IsCenteredUnitSecondMoment (ν : Measure ℝ) : Prop :=
  (∫ x, x ∂ν) = 0 ∧ (∫ x, x ^ 2 ∂ν) = 1

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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
