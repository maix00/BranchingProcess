/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand
import MeasureTheory.Measure.Levy.JumpRegions
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.ScaledBounds
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.SmallJumpMoment
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.Lemmas.AtomFreeRadii
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Large-jump identification in the Lévy–Khintchine proof

## Internal proof declarations

Smooth cutoff functions approximate the indicator of `{x | r ≤ |x|}`. The resulting
`scaled_largeJumpSet_charFun_tendsto` identifies the limit of
`t⁻¹ ∫_{r≤|x|} exp(iξx) dμ_t` with the corresponding integral against the extracted Lévy
measure. The band and small-ball second-moment estimates control the truncation boundaries.
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-! ### Smooth cutoff BCFs for the LK assembly

To identify the small- and large-jump limit pieces in `psi_eq_levyKhintchine_formula`,
we need to approximate the indicator `1_{|x| ≥ 1}` (and the related annulus indicator
near `|x| = 1`) by bounded continuous functions, then apply `h_jump`. -/

/-- Bounded continuous "upper" cutoff approximating `1_{|x| ≥ ρ}` from above.

* `largeUpperBCF ρ n x = 1` for `|x| ≥ ρ`
* `largeUpperBCF ρ n x = 0` for `|x| ≤ ρ - ρ/(n+1) = ρ(1 - 1/(n+1))`
* linear ramp from `0` to `1` on `[ρ(1 - 1/(n+1)), ρ]`. -/
private noncomputable def largeUpperBCF (ρ : ℝ) (_hρ : 0 < ρ) (n : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)),
      Continuous.min continuous_const
        (Continuous.max continuous_const
          (((continuous_abs.sub continuous_const).mul continuous_const).add continuous_const))⟩
    1
    (fun x y => by
      have hbnd : ∀ z : ℝ,
          0 ≤ min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ∧
          min 1 (max 0 ((|z| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 := fun z =>
        ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      have hx := hbnd x; have hy := hbnd y
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)

private lemma largeUpperBCF_apply (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeUpperBCF ρ hρ n x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) := rfl

private lemma largeUpperBCF_nonneg (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    0 ≤ largeUpperBCF ρ hρ n x := by
  rw [largeUpperBCF_apply]; exact le_min zero_le_one (le_max_left _ _)

private lemma largeUpperBCF_le_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeUpperBCF ρ hρ n x ≤ 1 := by
  rw [largeUpperBCF_apply]; exact min_le_left _ _

private lemma largeUpperBCF_eq_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) {x : ℝ} (hx : ρ ≤ |x|) :
    largeUpperBCF ρ hρ n x = 1 := by
  rw [largeUpperBCF_apply]
  have hnn : (0 : ℝ) ≤ (n + 1 : ℝ) / ρ := by positivity
  have h1 : 0 ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) := mul_nonneg (by linarith) hnn
  have h2 : 1 ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 := by linarith
  rw [show max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1) = (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 from
      max_eq_right (by linarith)]
  exact min_eq_left h2

private lemma largeUpperBCF_eq_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) {x : ℝ}
    (hx : |x| ≤ ρ - ρ/(n + 1 : ℝ)) : largeUpperBCF ρ hρ n x = 0 := by
  rw [largeUpperBCF_apply]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hslope : (0 : ℝ) < (n + 1 : ℝ) / ρ := by positivity
  have hbnd : (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 ≤ 0 := by
    have h1 : |x| - ρ ≤ -(ρ/(n + 1 : ℝ)) := by linarith
    have h2 : (|x| - ρ) * ((n + 1 : ℝ) / ρ) ≤ -(ρ/(n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) :=
      mul_le_mul_of_nonneg_right h1 hslope.le
    rw [show -(ρ/(n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) = -1 from by field_simp] at h2
    linarith
  rw [show max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1) = 0 from max_eq_left hbnd]
  exact min_eq_right zero_le_one

/-- `largeUpperBCF ρ n` vanishes on a neighborhood of `0` for `n ≥ 1`, hence it
lies in the test class of `h_jump`. -/
private lemma largeUpperBCF_vanishes_near_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → largeUpperBCF ρ hρ n x = 0 := by
  refine ⟨ρ/(n + 2 : ℝ), by positivity, fun x hx => ?_⟩
  apply largeUpperBCF_eq_zero
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  have hn_cast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h_ineq : ρ/(n + 2 : ℝ) ≤ ρ - ρ/(n + 1 : ℝ) := by
    rw [sub_eq_add_neg, ← sub_eq_add_neg, le_sub_iff_add_le, div_add_div _ _ hn2.ne' hn1.ne',
        div_le_iff₀ (by positivity)]
    have hn_poly : (n+1:ℝ) + (n+2) ≤ (n+2)*(n+1) := by nlinarith [hn_cast]
    calc ρ*(n+1) + (n+2)*ρ = ρ*((n+1)+(n+2)) := by ring
      _ ≤ ρ*((n+2)*(n+1)) := mul_le_mul_of_nonneg_left hn_poly hρ.le
  linarith [le_of_lt hx]

/-- As `n → ∞`, `largeUpperBCF ρ n x → 1_{|x| ≥ ρ}` pointwise. -/
private lemma largeUpperBCF_tendsto_indicator (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => largeUpperBCF ρ hρ n x) atTop
      (𝓝 (Set.indicator {y : ℝ | ρ ≤ |y|} (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : ρ ≤ |x|
  · rw [Set.indicator_of_mem (show x ∈ {y | ρ ≤ |y|} from hx)]
    refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun n _ => ?_)
    exact largeUpperBCF_eq_one ρ hρ n hx
  · push Not at hx
    rw [Set.indicator_of_notMem (show x ∉ {y | ρ ≤ |y|} from not_le.mpr hx)]
    have h_pos : 0 < ρ - |x| := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (ρ/(ρ - |x|))
    rw [div_lt_iff₀ h_pos] at hN  -- hN : ρ < ↑N * (ρ - |x|)
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
    apply largeUpperBCF_eq_zero
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hN_le : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : ρ ≤ (ρ - |x|) * (n + 1 : ℝ) := by
      calc ρ ≤ (N : ℝ) * (ρ - |x|) := le_of_lt hN
        _ ≤ (n : ℝ) * (ρ - |x|) := mul_le_mul_of_nonneg_right hN_le h_pos.le
        _ ≤ (n + 1 : ℝ) * (ρ - |x|) :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos.le
        _ = (ρ - |x|) * (n + 1 : ℝ) := by ring
    rw [← div_le_iff₀ hn1_pos] at h1
    linarith

/-- Bounded continuous "annulus" cutoff centered at `|x| = ρ`.

* `largeAnnulusBCF ρ n x = 1` for `||x| - ρ| ≤ ρ/(n+1)` (plateau on the annulus)
* `largeAnnulusBCF ρ n x = 0` for `||x| - ρ| ≥ 2ρ/(n+1)` (outside a slightly wider annulus)
* linear ramp on the transition bands. -/
private noncomputable def largeAnnulusBCF (ρ : ℝ) (_hρ : 0 < ρ) (n : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))),
      Continuous.max continuous_const
        (continuous_const.sub (continuous_const.mul
          (Continuous.max continuous_const
            ((continuous_abs.comp (continuous_abs.sub continuous_const)).sub continuous_const))))⟩
    1
    (fun x y => by
      have hbnd : ∀ z : ℝ,
          0 ≤ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ∧
          max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ))) ≤ 1 := fun z => by
        refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
        have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|z| - ρ)| - ρ/(n + 1 : ℝ)) := by positivity
        linarith
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      have hx := hbnd x; have hy := hbnd y
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)

private lemma largeAnnulusBCF_apply (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeAnnulusBCF ρ hρ n x =
      max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) := rfl

private lemma largeAnnulusBCF_nonneg (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    0 ≤ largeAnnulusBCF ρ hρ n x := by
  rw [largeAnnulusBCF_apply]; exact le_max_left _ _

private lemma largeAnnulusBCF_le_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    largeAnnulusBCF ρ hρ n x ≤ 1 := by
  rw [largeAnnulusBCF_apply]
  refine max_le zero_le_one ?_
  have h1 : 0 ≤ ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ)) := by positivity
  linarith

private lemma largeAnnulusBCF_eq_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) {x : ℝ}
    (hx : |(|x| - ρ)| ≤ ρ/(n + 1 : ℝ)) : largeAnnulusBCF ρ hρ n x = 1 := by
  rw [largeAnnulusBCF_apply]
  have hsub : |(|x| - ρ)| - ρ/(n + 1 : ℝ) ≤ 0 := by linarith
  rw [show max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ)) = 0 from max_eq_left hsub,
      mul_zero, sub_zero, max_eq_right zero_le_one]

private lemma largeAnnulusBCF_eq_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) {x : ℝ}
    (hx : 2 * ρ/(n + 1 : ℝ) ≤ |(|x| - ρ)|) : largeAnnulusBCF ρ hρ n x = 0 := by
  rw [largeAnnulusBCF_apply]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have h_diff : ρ/(n + 1 : ℝ) ≤ |(|x| - ρ)| - ρ/(n + 1 : ℝ) := by
    have : 2 * ρ/(n + 1 : ℝ) = ρ/(n + 1 : ℝ) + ρ/(n + 1 : ℝ) := by ring
    linarith [this ▸ hx]
  have h_nn : 0 ≤ |(|x| - ρ)| - ρ/(n + 1 : ℝ) := le_trans (by positivity) h_diff
  rw [max_eq_right h_nn]
  have h_prod : 1 ≤ ((n + 1 : ℝ) / ρ) * (|(|x| - ρ)| - ρ/(n + 1 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left h_diff (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) / ρ)
    rw [show ((n + 1 : ℝ) / ρ) * (ρ/(n + 1 : ℝ)) = 1 from by field_simp] at this
    exact this
  have : 1 - ((n + 1 : ℝ) / ρ) * (|(|x| - ρ)| - ρ/(n + 1 : ℝ)) ≤ 0 := by linarith
  exact max_eq_left this

/-- `largeAnnulusBCF ρ n` vanishes on a neighborhood of `0` for `n ≥ 2`. -/
private lemma largeAnnulusBCF_vanishes_near_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → largeAnnulusBCF ρ hρ n x = 0 := by
  refine ⟨ρ/(n + 1 : ℝ), by positivity, fun x hx => ?_⟩
  apply largeAnnulusBCF_eq_zero
  -- |x| < ρ/(n+1), so |x| - ρ < ρ/(n+1) - ρ ≤ 0 (since n+1 ≥ 3), hence
  -- ||x| - ρ| = ρ - |x| ≥ ρ - ρ/(n+1) ≥ 2ρ/(n+1) when n ≥ 2.
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hx_nn : 0 ≤ |x| := abs_nonneg _
  have hx_lt : |x| < ρ/(n + 1 : ℝ) := hx
  have h_ratio : ρ/(n + 1 : ℝ) ≤ ρ/3 := by
    rw [div_le_div_iff₀ hn1 (by norm_num : (0 : ℝ) < 3)]
    have h3 : (3 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    exact mul_le_mul_of_nonneg_left h3 hρ.le
  have hx_lt_1 : |x| < ρ := by
    have : ρ/3 < ρ := by linarith [div_lt_self hρ (by norm_num : (1 : ℝ) < 3)]
    linarith
  have h_neg : |x| - ρ < 0 := by linarith
  rw [abs_of_neg h_neg, neg_sub]
  -- goal: 2ρ/(n+1) ≤ ρ - |x|
  have h_bound : 2 * ρ/(n + 1 : ℝ) + ρ/(n + 1 : ℝ) ≤ ρ := by
    rw [← add_div, show (2 : ℝ) * ρ + ρ = 3 * ρ from by ring, div_le_iff₀ hn1]
    have h3 : (3 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    calc 3*ρ = ρ*3 := by ring
      _ ≤ ρ*(n+1) := mul_le_mul_of_nonneg_left h3 hρ.le
  linarith

/-- As `n → ∞`, `largeAnnulusBCF ρ n x → 1_{|x| = ρ}` pointwise. -/
private lemma largeAnnulusBCF_tendsto_indicator (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => largeAnnulusBCF ρ hρ n x) atTop
      (𝓝 (Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : |x| = ρ
  · -- At |x| = ρ, χ_n x = 1 always.
    rw [Set.indicator_of_mem (show x ∈ {y | |y| = ρ} from hx)]
    refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun n _ => ?_)
    apply largeAnnulusBCF_eq_one
    rw [hx]
    rw [show ρ - ρ = 0 from sub_self ρ, abs_zero]
    positivity
  · -- |x| ≠ ρ: eventually χ_n x = 0.
    rw [Set.indicator_of_notMem (show x ∉ {y | |y| = ρ} from hx)]
    have h_pos : 0 < |(|x| - ρ)| := abs_pos.mpr (sub_ne_zero.mpr hx)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * ρ/|(|x| - ρ)|)
    rw [div_lt_iff₀ h_pos] at hN  -- hN : 2ρ < ↑N * |(|x| - ρ)|
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
    apply largeAnnulusBCF_eq_zero
    -- Goal: 2ρ/(n+1) ≤ |(|x| - ρ)|
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hN_le : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : 2 * ρ ≤ (n + 1 : ℝ) * |(|x| - ρ)| :=
      calc (2 : ℝ) * ρ ≤ (N : ℝ) * |(|x| - ρ)| := le_of_lt hN
        _ ≤ (n : ℝ) * |(|x| - ρ)| := mul_le_mul_of_nonneg_right hN_le h_pos.le
        _ ≤ (n + 1 : ℝ) * |(|x| - ρ)| :=
            mul_le_mul_of_nonneg_right (by linarith) h_pos.le
    rw [div_le_iff₀ hn1_pos]; linarith

/-- BCF representing `largeUpperBCF ρ n · g` for a bounded continuous `g`. -/
private noncomputable def largeUpperMulBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (M : ℝ) (hg_bnd : ∀ x, |g x| ≤ M) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => largeUpperBCF ρ hρ n x * g x,
      (largeUpperBCF ρ hρ n).continuous.mul hg_cont⟩
    (2 * M)
    (fun x y => by
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq]
      have hbnd : ∀ z, |largeUpperBCF ρ hρ n z * g z| ≤ M := fun z => by
        rw [abs_mul, abs_of_nonneg (largeUpperBCF_nonneg ρ hρ n z)]
        calc largeUpperBCF ρ hρ n z * |g z|
            ≤ 1 * |g z| :=
              mul_le_mul_of_nonneg_right (largeUpperBCF_le_one ρ hρ n z) (abs_nonneg _)
          _ ≤ 1 * M := mul_le_mul_of_nonneg_left (hg_bnd z) zero_le_one
          _ = M := one_mul _
      have hx := hbnd x; have hy := hbnd y
      rw [abs_le] at hx hy
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)

@[simp]
private lemma largeUpperMulBCF_apply (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (g : ℝ → ℝ)
    (hg_cont : Continuous g) (M : ℝ) (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd x = largeUpperBCF ρ hρ n x * g x := rfl

private lemma largeUpperMulBCF_abs_le (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (g : ℝ → ℝ)
    (hg_cont : Continuous g) (M : ℝ) (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    |largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd x| ≤ M := by
  rw [largeUpperMulBCF_apply, abs_mul, abs_of_nonneg (largeUpperBCF_nonneg ρ hρ n x)]
  calc largeUpperBCF ρ hρ n x * |g x|
      ≤ 1 * M :=
        mul_le_mul (largeUpperBCF_le_one ρ hρ n x) (hg_bnd x) (abs_nonneg _) zero_le_one
    _ = M := one_mul _

private lemma largeUpperMulBCF_vanishes_near_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ) (hg_bnd : ∀ x, |g x| ≤ M) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd x = 0 := by
  obtain ⟨r, hr_pos, hr_zero⟩ := largeUpperBCF_vanishes_near_zero ρ hρ n hn
  refine ⟨r, hr_pos, fun x hx => ?_⟩
  rw [largeUpperMulBCF_apply, hr_zero x hx, zero_mul]

private lemma largeUpperMulBCF_tendsto_indicator
    (ρ : ℝ) (hρ : 0 < ρ) (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    Tendsto (fun n => largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd x) atTop
      (𝓝 (Set.indicator (largeJumpSet ρ) g x)) := by
  have h1 := (largeUpperBCF_tendsto_indicator ρ hρ x).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)))
  have h_eq :
      Set.indicator {y : ℝ | ρ ≤ |y|} (fun _ => (1 : ℝ)) x * g x =
        Set.indicator (largeJumpSet ρ) g x := by
    by_cases hx : ρ ≤ |x|
    · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | ρ ≤ |y|} from hx),
          Set.indicator_of_mem (show x ∈ largeJumpSet ρ from hx), one_mul]
    · push Not at hx
      rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | ρ ≤ |y|} from not_le.mpr hx),
          Set.indicator_of_notMem (show x ∉ largeJumpSet ρ from not_le.mpr hx), zero_mul]
  rw [← h_eq]
  exact h1.congr (fun n => (largeUpperMulBCF_apply ρ hρ n g hg_cont M hg_bnd x).symm)

/-- Pointwise bound `|largeUpperMulBCF ρ n g x − Set.indicator (largeJumpSet ρ) g x| ≤
M · largeAnnulusBCF ρ n x`, the key inequality controlling the discrepancy between
the smooth cutoff product and the true indicator product. -/
private lemma largeUpperMulBCF_sub_indicator_abs_le
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ) (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M) (x : ℝ) :
    |largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd x - Set.indicator (largeJumpSet ρ) g x| ≤
      M * largeAnnulusBCF ρ hρ n x := by
  rw [largeUpperMulBCF_apply]
  by_cases hx : ρ ≤ |x|
  · -- |x| ≥ ρ: both = g(x), difference 0.
    rw [Set.indicator_of_mem (show x ∈ largeJumpSet ρ from hx),
        largeUpperBCF_eq_one ρ hρ n hx, one_mul]
    rw [show g x - g x = 0 from sub_self (g x), abs_zero]
    exact mul_nonneg hM_nn (largeAnnulusBCF_nonneg ρ hρ n x)
  · push Not at hx
    rw [Set.indicator_of_notMem (show x ∉ largeJumpSet ρ from not_le.mpr hx), sub_zero,
        abs_mul, abs_of_nonneg (largeUpperBCF_nonneg ρ hρ n x)]
    by_cases hx' : |x| ≤ ρ - ρ/(n + 1 : ℝ)
    · rw [largeUpperBCF_eq_zero ρ hρ n hx', zero_mul]
      exact mul_nonneg hM_nn (largeAnnulusBCF_nonneg ρ hρ n x)
    · push Not at hx'
      have h_in_annulus : |(|x| - ρ)| ≤ ρ/(n + 1 : ℝ) := by
        rw [abs_of_nonpos (by linarith : |x| - ρ ≤ 0), neg_sub]; linarith
      rw [largeAnnulusBCF_eq_one ρ hρ n h_in_annulus, mul_one]
      calc largeUpperBCF ρ hρ n x * |g x|
          ≤ 1 * M :=
            mul_le_mul (largeUpperBCF_le_one ρ hρ n x) (hg_bnd x) (abs_nonneg _) zero_le_one
        _ = M := one_mul _

/-- **Scalar large-jump limit identification.** For any continuous bounded `g : ℝ → ℝ`,
under the hypothesis that `ν` has no atom at `|x| = ρ`, the scaled set integral over
`largeJumpSet ρ` of `g` against `μ_t` converges to the corresponding ν-integral.

The proof is an ε/3 sandwich: approximate `1_{|x| ≥ ρ}` from above by the smooth cutoff
`largeUpperBCF ρ n`, bound the discrepancy by `largeAnnulusBCF ρ n` (whose ν-integral
vanishes as `n → ∞` by `hν_atom`), and apply `h_jump` for each fixed `n`. -/
lemma scaled_largeJumpSet_integral_tendsto
    {ρ : ℝ} (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ} (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k =>
      (t_seq k).val⁻¹ * ∫ x in largeJumpSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ))
    atTop (𝓝 (∫ x in largeJumpSet ρ, g x ∂ν)) := by
  -- Composite BCFs `largeUpperBCF ρ n · g` for each n.
  set φg : ℕ → BoundedContinuousFunction ℝ ℝ :=
    fun n => largeUpperMulBCF ρ hρ n g hg_cont M hg_bnd with hφg_def
  -- DCT on ν for the BCFs: ∫ φg n dν → ∫_{largeJumpSet ρ} g dν. For a (possibly σ-finite) Lévy
  -- measure the constant bound `M` is not integrable, so we dominate the tail `n ≥ 1` (where
  -- `φg n` vanishes on `{|x| < ρ/2}`) by `M · 1_{largeJumpSet (ρ/2)}` and transfer via a shift.
  have h_dct_φg : Tendsto (fun n => ∫ x, φg n x ∂ν) atTop
      (𝓝 (∫ x in largeJumpSet ρ, g x ∂ν)) := by
    have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
    have h_bound_int : Integrable (Set.indicator (largeJumpSet (ρ / 2)) (fun _ => M)) ν := by
      have hfinite := hν.isFiniteMeasure_restrict_abs_ge hρ2
      exact (integrable_indicator_iff (measurableSet_largeJumpSet (ρ / 2))).mpr
        (integrable_const_iff.mpr (Or.inr hfinite))
    have h_shift : Tendsto (fun n => ∫ x, φg (n + 1) x ∂ν) atTop
        (𝓝 (∫ x, Set.indicator (largeJumpSet ρ) g x ∂ν)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := Set.indicator (largeJumpSet (ρ / 2)) (fun _ => M))
        (fun n => (φg (n + 1)).continuous.aestronglyMeasurable)
        h_bound_int
        (fun n => Filter.Eventually.of_forall (fun x => ?_))
        (Filter.Eventually.of_forall (fun x =>
          (tendsto_add_atTop_iff_nat 1).mpr
            (largeUpperMulBCF_tendsto_indicator ρ hρ g hg_cont M hg_bnd x)))
      rw [Real.norm_eq_abs]
      by_cases hx : x ∈ largeJumpSet (ρ / 2)
      · rw [Set.indicator_of_mem hx]
        exact largeUpperMulBCF_abs_le ρ hρ (n + 1) g hg_cont M hg_bnd x
      · rw [Set.indicator_of_notMem hx]
        rw [mem_largeJumpSet, not_le] at hx
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hxle : |x| ≤ ρ - ρ / ((↑(n + 1) : ℝ) + 1) := by
          have hcast : (↑(n + 1) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
          rw [hcast]
          have hden : (0 : ℝ) < (n : ℝ) + 2 := by linarith
          have h1 : ρ / ((n : ℝ) + 2) ≤ ρ / 2 :=
            (div_le_div_iff_of_pos_left hρ hden (by norm_num)).mpr (by linarith)
          linarith
        simp only [hφg_def, largeUpperMulBCF_apply,
          largeUpperBCF_eq_zero ρ hρ (n + 1) hxle, zero_mul, abs_zero, le_refl]
    have h_lim := (tendsto_add_atTop_iff_nat (f := fun m => ∫ x, φg m x ∂ν) 1).mp h_shift
    rwa [integral_indicator (measurableSet_largeJumpSet ρ)] at h_lim
  -- DCT on ν for χ_n: ∫ χ_n dν → 0, using hν_atom. The tail `n ≥ 2` is supported in
  -- `largeJumpSet (ρ/3)` (bump around `|x| = ρ`), dominated by `1_{largeJumpSet (ρ/3)}`.
  have h_dct_χ : Tendsto (fun n => ∫ x, largeAnnulusBCF ρ hρ n x ∂ν) atTop (𝓝 0) := by
    have hρ3 : (0 : ℝ) < ρ / 3 := by positivity
    have h_bound_int : Integrable (Set.indicator (largeJumpSet (ρ / 3)) (fun _ => (1 : ℝ))) ν := by
      have hfinite := hν.isFiniteMeasure_restrict_abs_ge hρ3
      exact (integrable_indicator_iff (measurableSet_largeJumpSet (ρ / 3))).mpr
        (integrable_const_iff.mpr (Or.inr hfinite))
    have h_shift : Tendsto (fun n => ∫ x, largeAnnulusBCF ρ hρ (n + 2) x ∂ν) atTop
        (𝓝 (∫ x, Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ)) x ∂ν)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := Set.indicator (largeJumpSet (ρ / 3)) (fun _ => (1 : ℝ)))
        (fun n => (largeAnnulusBCF ρ hρ (n + 2)).continuous.aestronglyMeasurable)
        h_bound_int
        (fun n => Filter.Eventually.of_forall (fun x => ?_))
        (Filter.Eventually.of_forall (fun x =>
          (tendsto_add_atTop_iff_nat 2).mpr (largeAnnulusBCF_tendsto_indicator ρ hρ x)))
      rw [Real.norm_eq_abs, abs_of_nonneg (largeAnnulusBCF_nonneg ρ hρ (n + 2) x)]
      by_cases hx : x ∈ largeJumpSet (ρ / 3)
      · rw [Set.indicator_of_mem hx]; exact largeAnnulusBCF_le_one ρ hρ (n + 2) x
      · rw [Set.indicator_of_notMem hx]
        rw [mem_largeJumpSet, not_le] at hx
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        refine le_of_eq (largeAnnulusBCF_eq_zero ρ hρ (n + 2) ?_)
        have habs : |(|x| - ρ)| = ρ - |x| := by
          rw [abs_of_nonpos (by linarith : |x| - ρ ≤ 0)]; ring
        rw [habs]
        have hcast : (↑(n + 2) : ℝ) + 1 = (n : ℝ) + 3 := by push_cast; ring
        rw [hcast]
        have hden : (0 : ℝ) < (n : ℝ) + 3 := by linarith
        have h1 : 2 * ρ / ((n : ℝ) + 3) ≤ 2 * ρ / 3 :=
          (div_le_div_iff_of_pos_left (by positivity) hden (by norm_num)).mpr (by linarith)
        linarith
    have h_meas_singleton : MeasurableSet {y : ℝ | |y| = ρ} :=
      (isClosed_singleton.preimage continuous_abs).measurableSet
    rw [integral_indicator h_meas_singleton] at h_shift
    have h_zero : ∫ _ in {y : ℝ | |y| = ρ}, (1 : ℝ) ∂ν = 0 := by
      have : (ν.restrict {y : ℝ | |y| = ρ}) = 0 := by
        rw [Measure.restrict_eq_zero]; exact hν_atom
      rw [show (∫ _ in {y : ℝ | |y| = ρ}, (1 : ℝ) ∂ν) =
            ∫ _, (1 : ℝ) ∂(ν.restrict {y : ℝ | |y| = ρ}) from rfl, this,
          integral_zero_measure]
    rw [h_zero] at h_shift
    exact (tendsto_add_atTop_iff_nat
      (f := fun m => ∫ x, largeAnnulusBCF ρ hρ m x ∂ν) 2).mp h_shift
  -- ε/3 argument.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hMplus : (0 : ℝ) < M + 1 := by linarith
  have hpos_3 : (0 : ℝ) < ε / 3 := by positivity
  have hpos_6Mplus : (0 : ℝ) < ε / (6 * (M + 1)) := by positivity
  -- Choose n₀ ≥ 2 such that |∫ φg n₀ dν - target| < ε/3 AND ∫ χ_{n₀} dν < ε/(6(M+1)).
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h_dct_φg) (ε / 3) hpos_3
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h_dct_χ) (ε / (6 * (M + 1))) hpos_6Mplus
  set n₀ : ℕ := max (max N₁ N₂) 2 with hn₀_def
  have hn₀_N₁ : N₁ ≤ n₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn₀_N₂ : N₂ ≤ n₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn₀_2 : 2 ≤ n₀ := le_max_right _ _
  have hn₀_1 : 1 ≤ n₀ := le_trans (by norm_num) hn₀_2
  have h_bnd_φg_int : |∫ x, φg n₀ x ∂ν - ∫ x in largeJumpSet ρ, g x ∂ν| < ε / 3 := by
    have := hN₁ n₀ hn₀_N₁; rwa [Real.dist_eq] at this
  have h_χ_int_nn : 0 ≤ ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂ν :=
    integral_nonneg (fun x => largeAnnulusBCF_nonneg ρ hρ n₀ x)
  have h_bnd_χ_int : ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂ν < ε / (6 * (M + 1)) := by
    have := hN₂ n₀ hn₀_N₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_χ_int_nn] at this
    exact this
  -- Apply h_jump to φg n₀ and χ_{n₀}.
  have h_φg_kjump : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x, φg n₀ x ∂ν)) :=
    h_jump (φg n₀) (largeUpperMulBCF_vanishes_near_zero ρ hρ n₀ hn₀_1 g hg_cont M hg_bnd)
  have h_χ_kjump : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x, largeAnnulusBCF ρ hρ n₀ x ∂ν)) :=
    h_jump (largeAnnulusBCF ρ hρ n₀) (largeAnnulusBCF_vanishes_near_zero ρ hρ n₀ hn₀_2)
  obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.mp h_φg_kjump) (ε / 3) hpos_3
  obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_atTop.mp h_χ_kjump) (ε / (6 * (M + 1))) hpos_6Mplus
  refine ⟨max K₁ K₂, fun k hk => ?_⟩
  have hk_K₁ : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk_K₂ : K₂ ≤ k := le_trans (le_max_right _ _) hk
  -- Bound on |t_k⁻¹ · ∫ φg n₀ dμ_k - ∫ φg n₀ dν|.
  have h_bnd_φg_k : |(t_seq k).val⁻¹ *
      ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ) - ∫ x, φg n₀ x ∂ν| < ε / 3 := by
    have := hK₁ k hk_K₁; rwa [Real.dist_eq] at this
  -- Bound on t_k⁻¹ · ∫ χ_{n₀} dμ_k via the limit of ∫ χ dν.
  have h_bnd_χ_k : (t_seq k).val⁻¹ *
      ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂(S.measure (t_seq k) : Measure ℝ) ≤
      2 * (ε / (6 * (M + 1))) := by
    have h_diff := hK₂ k hk_K₂
    rw [Real.dist_eq] at h_diff
    have h_abs_sub := abs_sub_lt_iff.mp h_diff
    linarith [h_bnd_χ_int, h_abs_sub.1]
  -- Pointwise bound: |φg n₀ x - indicator g x| ≤ M · χ_{n₀} x.
  -- Integrate against μ_k: |t_k⁻¹ · ∫ (φg n₀ - indicator g) dμ_k| ≤ M · t_k⁻¹ · ∫ χ_{n₀} dμ_k.
  have h_int_diff_bnd :
      |(t_seq k).val⁻¹ * ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ) -
        (t_seq k).val⁻¹ * ∫ x in largeJumpSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ)| ≤
      M * ((t_seq k).val⁻¹ *
        ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂(S.measure (t_seq k) : Measure ℝ)) := by
    set μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ) with hμk_def
    have h_indicator_int :
        ∫ x in largeJumpSet ρ, g x ∂μk = ∫ x, Set.indicator (largeJumpSet ρ) g x ∂μk :=
      (integral_indicator (measurableSet_largeJumpSet ρ)).symm
    rw [h_indicator_int, ← mul_sub, abs_mul]
    have h_tinv_nn : (0 : ℝ) ≤ (t_seq k).val⁻¹ :=
      inv_nonneg.mpr (le_of_lt (t_seq k).prop)
    rw [abs_of_nonneg h_tinv_nn,
        show M * ((t_seq k).val⁻¹ * ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂μk) =
            (t_seq k).val⁻¹ * (M * ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂μk) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ h_tinv_nn
    -- |∫ (φg - indicator g) dμk| ≤ M · ∫ χ dμk
    have h_φg_int : Integrable (φg n₀) μk := (φg n₀).integrable _
    have h_ind_int : Integrable (Set.indicator (largeJumpSet ρ) g) μk := by
      have hg_int : Integrable g μk :=
        Integrable.mono' (integrable_const M)
          hg_cont.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs]; exact hg_bnd x))
      exact hg_int.indicator (measurableSet_largeJumpSet ρ)
    rw [← integral_sub h_φg_int h_ind_int]
    have h_ptwise : ∀ x, |φg n₀ x - Set.indicator (largeJumpSet ρ) g x| ≤
        M * largeAnnulusBCF ρ hρ n₀ x := fun x =>
      largeUpperMulBCF_sub_indicator_abs_le ρ hρ n₀ g hg_cont M hM_nn hg_bnd x
    calc |∫ x, (φg n₀ x - Set.indicator (largeJumpSet ρ) g x) ∂μk|
        ≤ ∫ x, M * largeAnnulusBCF ρ hρ n₀ x ∂μk := by
          have h_bnd_int :=
            MeasureTheory.norm_integral_le_of_norm_le
              (((largeAnnulusBCF ρ hρ n₀).integrable μk).const_mul M)
              (Filter.Eventually.of_forall (fun x => by
                rw [Real.norm_eq_abs]; exact h_ptwise x))
          rwa [Real.norm_eq_abs] at h_bnd_int
      _ = M * ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂μk := integral_const_mul _ _
  -- Triangle inequality assembly.
  rw [Real.dist_eq]
  have h_split :
      (t_seq k).val⁻¹ * ∫ x in largeJumpSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ) -
        ∫ x in largeJumpSet ρ, g x ∂ν =
      ((t_seq k).val⁻¹ * ∫ x in largeJumpSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ) -
          (t_seq k).val⁻¹ * ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ)) +
        ((t_seq k).val⁻¹ * ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ) -
          ∫ x, φg n₀ x ∂ν) +
        (∫ x, φg n₀ x ∂ν - ∫ x in largeJumpSet ρ, g x ∂ν) := by ring
  rw [h_split]
  have h_tri : ∀ a b c : ℝ, |a + b + c| ≤ |a| + |b| + |c| := fun a b c => by
    have h1 : |a + b + c| ≤ |a + b| + |c| := by
      have := norm_add_le (a + b) c
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this; exact this
    have h2 : |a + b| ≤ |a| + |b| := by
      have := norm_add_le a b
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this; exact this
    linarith
  refine lt_of_le_of_lt (h_tri _ _ _) ?_
  have h_step1 :
      |(t_seq k).val⁻¹ * ∫ x in largeJumpSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ) -
        (t_seq k).val⁻¹ * ∫ x, φg n₀ x ∂(S.measure (t_seq k) : Measure ℝ)| ≤
      M * ((t_seq k).val⁻¹ *
        ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂(S.measure (t_seq k) : Measure ℝ)) := by
    rw [abs_sub_comm]; exact h_int_diff_bnd
  have h_main_bnd :
      M * ((t_seq k).val⁻¹ *
        ∫ x, largeAnnulusBCF ρ hρ n₀ x ∂(S.measure (t_seq k) : Measure ℝ)) ≤
        M * (2 * (ε / (6 * (M + 1)))) :=
    mul_le_mul_of_nonneg_left h_bnd_χ_k hM_nn
  have h_alg : M * (2 * (ε / (6 * (M + 1)))) ≤ ε / 3 := by
    have hM1 : 0 < M + 1 := by linarith
    have h_ratio : M / (M + 1) ≤ 1 := by
      rw [div_le_one hM1]; linarith
    calc M * (2 * (ε / (6 * (M + 1))))
        = (M / (M + 1)) * (ε / 3) := by field_simp; ring
      _ ≤ 1 * (ε / 3) :=
          mul_le_mul_of_nonneg_right h_ratio (by linarith [hε.le])
      _ = ε / 3 := one_mul _
  linarith [h_step1, h_main_bnd, h_alg, h_bnd_φg_k, h_bnd_φg_int]

/-- **Large-jump identification (complex), at split radius `ρ`.** The scaled set integral
over `largeJumpSet ρ` of the characteristic integrand `exp(ix·ξ) − 1` against `μ_t` converges
to the corresponding ν-integral, obtained from the scalar identification via the Re/Im
split. -/
lemma scaled_largeJumpSet_charFun_tendsto
    {ρ : ℝ} (hρ : 0 < ρ) (ξ : ℝ)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in largeJumpSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeJumpSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)) := by
  -- Real and imaginary parts of the complex integrand.
  set gRe : ℝ → ℝ := fun x => Real.cos (x * ξ) - 1 with hgRe_def
  set gIm : ℝ → ℝ := fun x => Real.sin (x * ξ) with hgIm_def
  -- Continuity.
  have hgRe_cont : Continuous gRe :=
    (Real.continuous_cos.comp (continuous_id.mul continuous_const)).sub continuous_const
  have hgIm_cont : Continuous gIm :=
    Real.continuous_sin.comp (continuous_id.mul continuous_const)
  -- Bounds: |gRe| ≤ 2, |gIm| ≤ 1.
  have hgRe_bnd : ∀ x, |gRe x| ≤ 2 := fun x =>
    abs_le.mpr ⟨by simp only [hgRe_def]; linarith [Real.neg_one_le_cos (x * ξ)],
                by simp only [hgRe_def]; linarith [Real.cos_le_one (x * ξ)]⟩
  have hgIm_bnd : ∀ x, |gIm x| ≤ 1 := fun x =>
    abs_le.mpr ⟨Real.neg_one_le_sin (x * ξ), Real.sin_le_one (x * ξ)⟩
  -- Pointwise Re/Im of the complex integrand.
  have hExp_arg : ∀ x : ℝ, (↑x : ℂ) * ↑ξ * I = (↑(x * ξ) : ℂ) * I := fun x => by
    push_cast; ring
  have hRe_eq : ∀ x : ℝ, RCLike.re (exp ((↑x : ℂ) * ↑ξ * I) - 1) = gRe x := fun x => by
    simp only [hgRe_def, RCLike.re_to_complex, Complex.sub_re, Complex.one_re, hExp_arg,
      Complex.exp_ofReal_mul_I_re]
  have hIm_eq : ∀ x : ℝ, RCLike.im (exp ((↑x : ℂ) * ↑ξ * I) - 1) = gIm x := fun x => by
    simp only [hgIm_def, RCLike.im_to_complex, Complex.sub_im, Complex.one_im, hExp_arg,
      Complex.exp_ofReal_mul_I_im, sub_zero]
  -- Decomposition of the complex set integral over any measure finite on `largeJumpSet ρ`.
  have h_decomp : ∀ (m : Measure ℝ), m (largeJumpSet ρ) < ⊤ →
      ∫ x in largeJumpSet ρ, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂m =
        (↑(∫ x in largeJumpSet ρ, gRe x ∂m) : ℂ) + (↑(∫ x in largeJumpSet ρ, gIm x ∂m) : ℂ) * I := by
    intro m hm
    have h_int : IntegrableOn (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) (largeJumpSet ρ) m := by
      refine Measure.integrableOn_of_bounded hm.ne
        (((Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.mul continuous_const).mul continuous_const))).sub
          continuous_const)).aestronglyMeasurable (M := 2)
        (Filter.Eventually.of_forall (fun x => ?_))
      rw [show exp ((↑x : ℂ) * ↑ξ * I) - 1 = exp ((↑(x * ξ) : ℂ) * I) - 1 from by
            rw [hExp_arg]]
      calc ‖exp ((↑(x * ξ) : ℂ) * I) - 1‖
          ≤ ‖exp ((↑(x * ξ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
            rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
    have h := setIntegral_re_add_im h_int
    simp only [RCLike.I_to_complex] at h
    have hRe_int : ∫ x in largeJumpSet ρ, RCLike.re (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂m =
        ∫ x in largeJumpSet ρ, gRe x ∂m :=
      setIntegral_congr_fun (measurableSet_largeJumpSet ρ) (fun x _ => hRe_eq x)
    have hIm_int : ∫ x in largeJumpSet ρ, RCLike.im (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂m =
        ∫ x in largeJumpSet ρ, gIm x ∂m :=
      setIntegral_congr_fun (measurableSet_largeJumpSet ρ) (fun x _ => hIm_eq x)
    rw [hRe_int, hIm_int] at h
    exact h.symm
  -- Scalar limits for gRe and gIm.
  have h_re_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeJumpSet ρ, gRe x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeJumpSet ρ, gRe x ∂ν)) :=
    S.scaled_largeJumpSet_integral_tendsto hρ gRe hgRe_cont (by norm_num) hgRe_bnd hν hν_atom h_jump
  have h_im_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeJumpSet ρ, gIm x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeJumpSet ρ, gIm x ∂ν)) :=
    S.scaled_largeJumpSet_integral_tendsto hρ gIm hgIm_cont (by norm_num) hgIm_bnd hν hν_atom h_jump
  -- Recombine into the complex limit.
  have h_re_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in largeJumpSet ρ, gRe x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 (↑(∫ x in largeJumpSet ρ, gRe x ∂ν) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_re_lim
  have h_im_lim_C : Tendsto (fun k => (↑((t_seq k).val⁻¹ *
      ∫ x in largeJumpSet ρ, gIm x ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) * I)
      atTop (𝓝 ((↑(∫ x in largeJumpSet ρ, gIm x ∂ν) : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h_im_lim).mul_const I
  have h_sum := h_re_lim_C.add h_im_lim_C
  rw [← h_decomp ν (hν.measure_setOf_abs_ge_lt_top hρ)] at h_sum
  refine h_sum.congr (fun k => ?_)
  rw [h_decomp (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _)]
  push_cast
  ring

/-- **Band convergence.** For atom-free radii `0 < δ < ρ`, the scaled band integral of a
bounded continuous function converges to the `ν`-band integral. Proof: clamp `g` to
`[-ρ, ρ]` and subtract two `largeJumpSet` limits (`largeJumpSet ρ ⊆ largeJumpSet δ`). -/
lemma scaled_band_integral_tendsto
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ} (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_δ : ν {x | |x| = δ} = 0) (hν_ρ : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂ν)) := by
  have hρ : 0 < ρ := hδ.trans hδρ
  -- Clamp `g` to `[-ρ, ρ]`: `g_tilde := g ∘ clamp`, continuous and globally bounded by `M`.
  set clamp : ℝ → ℝ := fun x => max (-ρ) (min x ρ)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_id.min continuous_const)
  set g' : ℝ → ℝ := fun x => g (clamp x)
  have hg'_cont : Continuous g' := hg_cont.comp hclamp_cont
  have hg'_bnd : ∀ x, |g' x| ≤ M := fun x => hg_bnd (clamp x)
  -- The band is `largeJumpSet δ \ largeJumpSet ρ`, with `largeJumpSet ρ ⊆ largeJumpSet δ`.
  have h_sub : largeJumpSet ρ ⊆ largeJumpSet δ := largeJumpSet_antitone (le_of_lt hδρ)
  have h_band_eq : {x | δ ≤ |x| ∧ |x| < ρ} = largeJumpSet δ \ largeJumpSet ρ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, mem_largeJumpSet, not_le]
  -- On the band, `clamp x = x`, hence `g' = g`.
  have h_clamp_eq : ∀ x ∈ {x | δ ≤ |x| ∧ |x| < ρ}, clamp x = x := by
    intro x hx
    have hxρ : |x| < ρ := hx.2
    obtain ⟨hxl, hxr⟩ := abs_lt.mp hxρ
    show max (-ρ) (min x ρ) = x
    rw [min_eq_left (le_of_lt hxr), max_eq_right (le_of_lt hxl)]
  -- For any measure finite on `largeJumpSet δ`, the band integral of `g` equals the difference of
  -- the two `largeJumpSet` integrals of `g'`.
  have h_split : ∀ (m : Measure ℝ), m (largeJumpSet δ) < ⊤ →
      ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂m =
        (∫ x in largeJumpSet δ, g' x ∂m) - ∫ x in largeJumpSet ρ, g' x ∂m := by
    intro m hm
    have hg'_intOn : IntegrableOn g' (largeJumpSet δ) m :=
      Measure.integrableOn_of_bounded hm.ne hg'_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => by
          simpa [Real.norm_eq_abs] using hg'_bnd x))
    have h_diff : ∫ x in largeJumpSet δ \ largeJumpSet ρ, g' x ∂m =
        (∫ x in largeJumpSet δ, g' x ∂m) - ∫ x in largeJumpSet ρ, g' x ∂m :=
      setIntegral_sdiff (measurableSet_largeJumpSet ρ) hg'_intOn h_sub
    have h_congr : ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂m =
        ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g' x ∂m := by
      refine (setIntegral_congr_fun ?_ (fun x hx => ?_)).symm
      · rw [h_band_eq]
        exact (measurableSet_largeJumpSet δ).diff (measurableSet_largeJumpSet ρ)
      · show g (clamp x) = g x
        rw [h_clamp_eq x hx]
    rw [h_congr, h_band_eq, h_diff]
  -- Two `largeJumpSet` limits for `g'`, then subtract.
  have h_δ_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeJumpSet δ, g' x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeJumpSet δ, g' x ∂ν)) :=
    S.scaled_largeJumpSet_integral_tendsto hδ g' hg'_cont hM_nn hg'_bnd hν hν_δ h_jump
  have h_ρ_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
      ∫ x in largeJumpSet ρ, g' x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeJumpSet ρ, g' x ∂ν)) :=
    S.scaled_largeJumpSet_integral_tendsto hρ g' hg'_cont hM_nn hg'_bnd hν hν_ρ h_jump
  have h_sub_lim := h_δ_lim.sub h_ρ_lim
  rw [← h_split ν (hν.measure_setOf_abs_ge_lt_top hδ)] at h_sub_lim
  refine h_sub_lim.congr (fun k => ?_)
  rw [h_split (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _), mul_sub]

/-- `x²` is integrable on the ball `{|x| < r}` under any Lévy measure. On the ball the bound
`x² ≤ max 1 (r²) · min 1 (x²)` holds pointwise (case on `x² ≤ 1`), so the ν-integral is
controlled by `∫⁻ min(1, x²) dν < ⊤`. -/
lemma sq_integrableOn_ball_levy
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} ν := by
  set K : ℝ := max 1 (r ^ 2) with hK_def
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hK_nn : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound : ∫⁻ x in {x : ℝ | |x| < r}, ‖x ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
    calc ∫⁻ x in {x : ℝ | |x| < r}, ‖x ^ 2‖ₑ ∂ν
        ≤ ∫⁻ x in {x : ℝ | |x| < r}, ENNReal.ofReal (K * min 1 (x ^ 2)) ∂ν := by
          refine setLIntegral_mono ?_ (fun x hx => ?_)
          · exact ENNReal.measurable_ofReal.comp
              (measurable_const.mul (measurable_const.min (measurable_id'.pow_const 2)))
          · rw [Real.enorm_eq_ofReal (sq_nonneg x)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hxr : |x| < r := hx
            by_cases hle : x ^ 2 ≤ 1
            · rw [min_eq_right hle]
              exact le_mul_of_one_le_left (sq_nonneg x) hK1
            · rw [min_eq_left (not_le.mp hle).le, mul_one]
              have hx2 : x ^ 2 < r ^ 2 := by
                have h := abs_lt.mp hxr
                nlinarith [h.1, h.2]
              exact le_trans (le_of_lt hx2) (le_max_right _ _)
      _ = ∫⁻ x in {x : ℝ | |x| < r}, ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
          refine lintegral_congr (fun x => ?_)
          rw [ENNReal.ofReal_mul hK_nn]
      _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2)

/-- The cubic Taylor remainder is integrable on the ball `{|x| < r}` (for `r ≤ 1`) under any
Lévy measure: on the ball it equals `levyCompensatedIntegrand ξ x + (xξ)²/2`, and both summands
are ν-integrable (the compensated integrand globally, the quadratic term by
`sq_integrableOn_ball_levy`). -/
lemma remainder_integrableOn_ball_levy
    {r : ℝ} (hr1 : r ≤ 1) (ξ : ℝ) {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} ν := by
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hcomp : IntegrableOn (levyCompensatedIntegrand ξ) {x : ℝ | |x| < r} ν :=
    (integrable_levyCompensatedIntegrand hν ξ).integrableOn
  have hquad : IntegrableOn (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) {x : ℝ | |x| < r} ν := by
    have hrw : (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) =
        fun x : ℝ => (↑((x ^ 2 * (ξ ^ 2 / 2) : ℝ)) : ℂ) := by
      funext x; push_cast; ring
    rw [hrw]
    exact ((sq_integrableOn_ball_levy hν r).mul_const (ξ ^ 2 / 2)).ofReal
  have hsum : IntegrableOn
      (levyCompensatedIntegrand ξ + fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} ν := hcomp.add hquad
  refine hsum.congr_fun (fun x hx => ?_) hmeas
  have hx1 : |x| < 1 := lt_of_lt_of_le hx hr1
  simp only [Pi.add_apply, levyCompensatedIntegrand_def, ite_eq_left hx1]
  ring

/-- The `ν`-small-ball second moment is dominated by the scaled-second-moment limit:
`∫_{|x|<r} x² dν ≤ σ_sq_r`. This makes the Gaussian variance
`σ_G² = σ_sq_r − ∫_{|x|<r} x² dν` nonnegative. -/
lemma smallBall_second_moment_nu_le
    {r : ℝ} (hr : 0 < r)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    ∫ x in {x | |x| < r}, x ^ 2 ∂ν ≤ σ_sq_r := by
  -- Clamp `x²` to `[0, r²]`: globally bounded, continuous, and equal to `x²` on `{|x|<r}`.
  set g : ℝ → ℝ := fun x => min (x ^ 2) (r ^ 2) with hg_def
  have hg_cont : Continuous g := (continuous_pow 2).min continuous_const
  have hr2_nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hg_nn : ∀ x, 0 ≤ g x := fun x => le_min (sq_nonneg x) hr2_nn
  have hg_bnd : ∀ x, |g x| ≤ r ^ 2 := fun x =>
    abs_le.mpr ⟨le_trans (by linarith [hr2_nn]) (hg_nn x), min_le_right _ _⟩
  -- On the ball `{|x| < r}`, the clamp is inactive: `g x = x²`.
  have hg_eq_ball : ∀ x ∈ {x : ℝ | |x| < r}, g x = x ^ 2 := by
    intro x hx
    have hx' : |x| < r := hx
    have : x ^ 2 ≤ r ^ 2 := by
      have := sq_le_sq' (by linarith [abs_lt.mp hx']) (le_of_lt (abs_lt.mp hx').2)
      simpa using this
    exact min_eq_left this
  have h_meas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  -- Atom-free shrinking sequence `δ m ↓ 0` inside `(0, r)`.
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_null, hδ_tendsto⟩ := hν.exists_atomFree_seq_tendsto_zero hr
  -- Per-`m` ν-band second moment, bounded by `σ_sq_r`.
  have h_band_le : ∀ m, ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν ≤ σ_sq_r := by
    intro m
    -- The band is measurable and contained in the ball.
    have h_meas_band : MeasurableSet {x : ℝ | δ m ≤ |x| ∧ |x| < r} :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_lt continuous_abs.measurable measurable_const)
    have h_band_sub : {x : ℝ | δ m ≤ |x| ∧ |x| < r} ⊆ {x : ℝ | |x| < r} :=
      fun x hx => hx.2
    -- Step 1: band limit for the clamped `g`, then rewrite to `x²` on both sides.
    have h_band_lim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν)) := by
      have h := S.scaled_band_integral_tendsto (hδ := hδ_pos m) (hδρ := hδ_lt m)
        g hg_cont hr2_nn hg_bnd hν (hδ_null m) hν_r h_jump
      -- Swap `g` for `x²` on the band (it lies in the ball where `g = x²`).
      have hswap : ∀ (μ : Measure ℝ),
          ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, g x ∂μ =
            ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂μ :=
        fun μ => setIntegral_congr_fun h_meas_band
          (fun x hx => hg_eq_ball x (h_band_sub hx))
      simpa only [hswap ν, hswap (S.measure (t_seq _) : Measure ℝ)] using h
    -- Step 2: per-`k` comparison band ⊆ ball, using the clamped `g` for integrability.
    have h_compare : ∀ k, (t_seq k).val⁻¹ *
        ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤
        (t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr (t_seq k).2))
      set μ := (S.measure (t_seq k) : Measure ℝ)
      -- Compare via the clamped `g`, which is integrable on the ball (bounded, finite measure).
      have hg_int_ball : IntegrableOn g {x : ℝ | |x| < r} μ :=
        Measure.integrableOn_of_bounded (measure_ne_top _ _)
          hg_cont.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => by
            simpa [Real.norm_eq_abs] using hg_bnd x))
      have h_band : ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂μ =
          ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, g x ∂μ :=
        (setIntegral_congr_fun h_meas_band
          (fun x hx => hg_eq_ball x (h_band_sub hx))).symm
      have h_ball : ∫ x in {x | |x| < r}, x ^ 2 ∂μ =
          ∫ x in {x | |x| < r}, g x ∂μ :=
        (setIntegral_congr_fun h_meas_ball hg_eq_ball).symm
      rw [h_band, h_ball]
      exact setIntegral_mono_set hg_int_ball
        (ae_restrict_of_forall_mem h_meas_ball (fun x _ => hg_nn x))
        (LE.le.eventuallyLE h_band_sub)
    exact le_of_tendsto_of_tendsto' h_band_lim hσ h_compare
  -- Step 3: `m → ∞`. The bands exhaust the punctured ball; `x²·1_{band m} → x²·1_{ball∖{0}}`
  -- pointwise off `{0}`, dominated by `r²`, so the band integrals tend to the ball integral.
  set f : ℕ → ℝ → ℝ := fun m x =>
    Set.indicator {x : ℝ | δ m ≤ |x| ∧ |x| < r} (fun x => x ^ 2) x with hf_def
  have h_meas_band' : ∀ m, MeasurableSet {x : ℝ | δ m ≤ |x| ∧ |x| < r} := fun m =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  -- Rewrite band/ball integrals as integrals of indicators on all of ℝ.
  have h_band_int : ∀ m, ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν = ∫ x, f m x ∂ν :=
    fun m => (integral_indicator (h_meas_band' m)).symm
  have h_ball_int : ∫ x in {x | |x| < r}, x ^ 2 ∂ν =
      ∫ x, Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x ∂ν :=
    (integral_indicator h_meas_ball).symm
  have h_lim : Tendsto (fun m => ∫ x, f m x ∂ν) atTop
      (𝓝 (∫ x, Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun x => Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x)
      (fun m => ((continuous_pow 2).aestronglyMeasurable.indicator (h_meas_band' m)))
      ?_ ?_ ?_
    · -- the dominating function `x²·1_ball` is ν-integrable (Lévy small-ball second moment).
      exact (integrable_indicator_iff h_meas_ball).mpr (sq_integrableOn_ball_levy hν r)
    · -- domination `|f m x| ≤ x²·1_ball x`.
      intro m
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [Real.norm_eq_abs, hf_def, Set.indicator_apply]
      by_cases hx : x ∈ {x : ℝ | δ m ≤ |x| ∧ |x| < r}
      · have hxr : x ∈ {x : ℝ | |x| < r} := hx.2
        rw [ite_eq_left hx, ite_eq_left hxr]
        exact le_of_eq (abs_of_nonneg (sq_nonneg x))
      · rw [ite_eq_right hx]
        simp only [abs_zero]
        split <;> [exact sq_nonneg x; exact le_refl 0]
    · -- pointwise convergence ν-a.e. (off the ν-null point `0`).
      have h_ae : ∀ᵐ x ∂ν, x ≠ 0 := by
        rw [ae_iff]
        simpa using hν.1
      filter_upwards [h_ae] with x hx0
      by_cases hxr : x ∈ {x : ℝ | |x| < r}
      · rw [Set.indicator_of_mem hxr]
        -- eventually `δ m < |x|`, so `x` enters the band and stays.
        have hx_pos : 0 < |x| := abs_pos.mpr hx0
        have h_ev : ∀ᶠ m in atTop, δ m < |x| :=
          (hδ_tendsto.eventually_lt_const hx_pos)
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [h_ev] with m hm
        have hmem : x ∈ {x : ℝ | δ m ≤ |x| ∧ |x| < r} := ⟨le_of_lt hm, hxr⟩
        simp only [hf_def, Set.indicator_apply, ite_eq_left hmem]
      · rw [Set.indicator_of_notMem hxr]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.Eventually.of_forall (fun m => ?_)
        have hnmem : x ∉ {x : ℝ | δ m ≤ |x| ∧ |x| < r} := fun h => hxr h.2
        simp only [hf_def, Set.indicator_apply, ite_eq_right hnmem]
  rw [h_ball_int]
  exact le_of_tendsto' (h_lim.congr (fun m => (h_band_int m).symm)) h_band_le

end ConvolutionSemigroup

end ProbabilityTheory
