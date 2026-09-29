import Probability.Distributions.Stable.Attraction
import Probability.Distributions.Stable.SmallDeviation

/-!
# Scales for the stable Mogulskii route

This file records the deterministic scale interface used by Mogulskii's
stable-domain-of-attraction proof.  The finite-variance files use
`IsMogulskiiScale`, which is based on the diffusive scale `sqrt n`.  The
stable proof has two visible scales instead: a stable normalization `b n` and
a smaller corridor scale `a n`.

The stable law, the domain-of-attraction statement, and the one-block
corridor estimate remain separate hypotheses.  This module only contains
the scale predicate and its elementary rounding lemmas.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory

/-! ## Stable scales -/

/-- The two-scale hypothesis used in the stable version of Mogulskii's
theorem.  `normalization` is the stable norming `bₙ`; `scale` is the smaller
corridor scale `aₙ`.  The stable law and the domain-of-attraction statement
are deliberately separate hypotheses and are not bundled into this
deterministic predicate.
-/
def IsStableMogulskiiScale
    (α : ℝ) (μ : Measure ℝ)
    (normalization scale : ℕ → ℝ) : Prop :=
  IsStableNorming α μ normalization ∧
    Tendsto scale atTop atTop ∧
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0)

namespace IsStableMogulskiiScale

theorem stableNorming
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    IsStableNorming α μ normalization := h.1

theorem scale_tendsto_atTop
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto scale atTop atTop := h.2.1

theorem scale_div_normalization_tendsto_zero
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2.2

theorem eventually_normalization_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < normalization n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact h.1.1 n hn

theorem eventually_scale_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
  h.2.1.eventually (eventually_gt_atTop 0)

/-- The corridor scale is eventually strictly below the norming. This is the only
consequence of `a n / b n → 0` that the block argument uses. -/
theorem eventually_scale_lt_normalization
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, scale n < normalization n := by
  have hlt : ∀ᶠ n in atTop, scale n / normalization n < 1 :=
    (tendsto_order.1 h.scale_div_normalization_tendsto_zero).2 1 zero_lt_one
  filter_upwards [h.eventually_normalization_pos, hlt] with n hn hlt
  exact (div_lt_one hn).mp hlt

/-- The two scale facts the block argument uses together. -/
theorem eventually_scale_pos_and_lt_normalization
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n ∧ scale n < normalization n :=
  h.eventually_scale_pos.and h.eventually_scale_lt_normalization

/-- `L*` is eventually positive along the corridor scale, so that the rate
`a n ^ α / (n * L* (a n))` has a nonvanishing denominator. -/
theorem eventually_slowVariation_pos
    {α : ℝ} {μ : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α μ normalization scale)
    (hμ : Integrable (fun x : ℝ => x ^ 2) μ) (hpos : 0 < ∫ x, x ^ 2 ∂μ) :
    ∀ᶠ n in atTop, 0 < stableSlowVariation α μ (scale n) :=
  h.scale_tendsto_atTop.eventually (eventually_stableSlowVariation_pos α μ hμ hpos)

end IsStableMogulskiiScale

/-! ## Stable block lengths -/

/-- The integer length of a block whose time scale is a constant multiple of
`a_n ^ α`.  For `α = 2` this specializes to the diffusive block length used
by the Gaussian route.
-/
noncomputable def stableBlockLength
    (α constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊constant * scale n ^ α⌋₊

theorem tendsto_stableBlockArgument_atTop
    {α constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => constant * scale n ^ α) atTop atTop := by
  exact (tendsto_rpow_atTop hα).comp hscale |>.const_mul_atTop hconstant

theorem tendsto_stableBlockLength_atTop
    {α constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (stableBlockLength α constant scale) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (tendsto_stableBlockArgument_atTop hα hconstant hscale)

theorem eventually_stableBlockLength_pos
    {α constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α constant scale n :=
  (tendsto_stableBlockLength_atTop hα hconstant hscale).eventually
    (eventually_gt_atTop 0)

/-- Rounding the stable block length does not change its ratio to `a_n ^ α`.
This is the deterministic rounding lemma used before the probabilistic
one-block estimate is iterated.
-/
theorem tendsto_stableBlockLength_div_rpow
    {α constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant)
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n =>
        (stableBlockLength α constant scale n : ℝ) / scale n ^ α)
      atTop (nhds constant) := by
  have harg := tendsto_stableBlockArgument_atTop hα hconstant hscale
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp harg
  have hmul := hratio.mul_const constant
  convert hmul.congr' ?_ using 1 <;> simp
  filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
  dsimp [stableBlockLength]
  have hpow : 0 < scale n ^ α := Real.rpow_pos_of_pos hn _
  have harg_ne : constant * scale n ^ α ≠ 0 :=
    mul_ne_zero hconstant.ne' hpow.ne'
  field_simp [harg_ne, hpow.ne']

end ProbabilityTheory.RandomWalk
