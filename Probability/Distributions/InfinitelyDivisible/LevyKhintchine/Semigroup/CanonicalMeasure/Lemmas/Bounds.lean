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
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.CanonicalMeasure.Basic
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
import MeasureTheory.Measure.Levy.JumpRegions
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.ScaledBounds
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.SmallJumpMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds for tilted scaled measures

This proof-support module establishes the integral identity and uniform mass
bounds used to extract a finite limit of the tilted scaled measures.

## Internal proof declarations

* `tiltedScaledMeasure_integral_eq` identifies an integral against the tilted
  measure with the corresponding `min(1,x²)`-weighted integral against the
  scaled convolution-semigroup member.
* `tiltedScaledMeasure_mass_eventually_le` gives an eventual uniform total-mass
  bound as `t → 0⁺`.
* `tiltedScaledMeasure_largeJumpSet_le` gives a uniform tail bound outside a
  sufficiently large radius.

For the tilted scaled measure $\widetilde\mu_t$, its defining integral and
the resulting bounds are
\[
 \int f(x)\,d\widetilde\mu_t(x)
   =\frac1t\int f(x)\min(1,x^2)\,d\mu_t(x),
 \qquad \sup_{0<t<t_0}\widetilde\mu_t(\mathbb R)<\infty.
\]
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory
namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- A real bound on the scaled mass `t⁻¹ · μ_t(A)` lifts to an `ℝ≥0∞` bound on
`scaledMeasure t A`. -/
private lemma scaledMeasure_apply_le_ofReal (t : {t : ℝ // 0 < t}) (A : Set ℝ) (c : ℝ)
    (h : t.val⁻¹ * ((S.measure t : Measure ℝ) A).toReal ≤ c) :
    S.scaledMeasure t A ≤ ENNReal.ofReal c := by
  rw [S.scaledMeasure_apply,
    show (S.measure t : Measure ℝ) A = ENNReal.ofReal ((S.measure t : Measure ℝ) A).toReal from
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr t.prop))]
  exact ENNReal.ofReal_le_ofReal h

/-- Integrals against the tilted measure are tilt-weighted integrals against `μ_t`. -/
lemma tiltedScaledMeasure_integral_eq (t : {t : ℝ // 0 < t}) (g : ℝ → ℝ) :
    ∫ x, g x ∂(S.tiltedScaledMeasure t) =
      t.val⁻¹ * ∫ x, g x * min 1 (x ^ 2) ∂(S.measure t : Measure ℝ) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (continuous_pow 2).measurable)
  have hpt : ∀ x : ℝ,
      (ENNReal.ofReal (min 1 (x ^ 2))).toReal • g x = g x * min 1 (x ^ 2) := by
    intro x
    rw [ENNReal.toReal_ofReal (le_min zero_le_one (sq_nonneg x)), smul_eq_mul, mul_comm]
  rw [show S.tiltedScaledMeasure t = (S.scaledMeasure t).withDensity
        (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_congr_ae (Eventually.of_forall hpt),
    S.integral_scaledMeasure, smul_eq_mul]

/-- Eventual uniform total-mass bound on the tilted measures as `t → 0⁺`. -/
lemma tiltedScaledMeasure_mass_eventually_le :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      S.tiltedScaledMeasure t Set.univ ≤ (C : ℝ≥0∞) := by
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := S.scaledMeasure_small_second_moment_bounded
  obtain ⟨C_large, hC_large⟩ := S.scaled_mass_bound_real 1 one_pos
  refine ⟨C₂.toNNReal + C_large + 1, zero_lt_one.trans_le le_add_self, ?_⟩
  filter_upwards [hC₂] with t ht
  -- Bound on the small-jump part: tilt = x², controlled by the second moment.
  have hA : ∫⁻ x in smallJumpSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal C₂ := by
    have hfg : Set.EqOn (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)))
        (fun x => ENNReal.ofReal (x ^ 2)) smallJumpSet := by
      intro x hx
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, mem_smallJumpSet.mp hx]
      simp [min_eq_right hx2]
    rw [setLIntegral_congr_fun measurableSet_smallJumpSet hfg]
    simp only [scaledMeasure]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
        ← ofReal_integral_eq_lintegral_ofReal (integrableOn_sq_smallJumpSet (S.measure t : Measure ℝ))
          (ae_of_all _ fun x => sq_nonneg x),
        ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr t.prop))]
    exact ENNReal.ofReal_le_ofReal ht
  -- Bound on the large-jump part: tilt ≤ 1, controlled by the large-jump mass bound.
  have hB : ∫⁻ x in smallJumpSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal (C_large : ℝ) := by
    have hle1 : ∫⁻ x in smallJumpSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        ≤ S.scaledMeasure t smallJumpSetᶜ := by
      calc ∫⁻ x in smallJumpSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
          ≤ ∫⁻ _ in smallJumpSetᶜ, 1 ∂(S.scaledMeasure t) :=
            lintegral_mono (fun x => ENNReal.ofReal_le_one.mpr (min_le_left _ _))
        _ = S.scaledMeasure t smallJumpSetᶜ := setLIntegral_one _
    refine hle1.trans ?_
    rw [smallJumpSet_eq_compl_largeJumpSet_one, compl_compl]
    exact S.scaledMeasure_apply_le_ofReal t (largeJumpSet 1) (C_large : ℝ) (hC_large t)
  -- Assemble: total mass = small + large parts.
  have hmass : S.tiltedScaledMeasure t Set.univ
      = ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t) := by
    rw [show S.tiltedScaledMeasure t = (S.scaledMeasure t).withDensity
          (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
      withDensity_apply _ MeasurableSet.univ]
    exact setLIntegral_univ _
  have hsplit : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      = ∫⁻ x in smallJumpSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        + ∫⁻ x in smallJumpSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t) :=
    (lintegral_add_compl _ measurableSet_smallJumpSet).symm
  rw [hmass, hsplit]
  calc ∫⁻ x in smallJumpSet, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
        + ∫⁻ x in smallJumpSetᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂(S.scaledMeasure t)
      ≤ ENNReal.ofReal C₂ + ENNReal.ofReal (C_large : ℝ) := add_le_add hA hB
    _ ≤ ((C₂.toNNReal + C_large + 1 : ℝ≥0) : ℝ≥0∞) := by
        have e1 : ENNReal.ofReal C₂ = (↑C₂.toNNReal : ℝ≥0∞) := rfl
        have e2 : ENNReal.ofReal (C_large : ℝ) = (↑C_large : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
        rw [e1, e2, ENNReal.coe_add, ENNReal.coe_add, ENNReal.coe_one]
        exact le_self_add

/-- Uniform tail bound: for every `ε > 0` some radius `R ≥ 1` has
`tiltedScaledMeasure t (largeJumpSet R) ≤ ε` for all `t`. -/
lemma tiltedScaledMeasure_largeJumpSet_le (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : {t : ℝ // 0 < t},
      S.tiltedScaledMeasure t (largeJumpSet R) ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR1, hR⟩ := S.scaled_largeJumpSet_mass_le_of_large_radius ε hε
  refine ⟨R, hR1, fun t => ?_⟩
  -- On `largeJumpSet R` the tilt equals `1`, so the tilted mass is the plain scaled mass.
  have hfg : Set.EqOn (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)))
      (fun _ => (1 : ℝ≥0∞)) (largeJumpSet R) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x ^ 2 := by
      nlinarith [sq_abs x, abs_nonneg x, hR1, mem_largeJumpSet.mp hx]
    simp [min_eq_left hx1]
  have heq : S.tiltedScaledMeasure t (largeJumpSet R) = S.scaledMeasure t (largeJumpSet R) := by
    rw [show S.tiltedScaledMeasure t = (S.scaledMeasure t).withDensity
          (fun x => ENNReal.ofReal (min 1 (x ^ 2))) from rfl,
      withDensity_apply _ (measurableSet_largeJumpSet R),
      setLIntegral_congr_fun (measurableSet_largeJumpSet R) hfg, setLIntegral_one]
  rw [heq]
  exact S.scaledMeasure_apply_le_ofReal t (largeJumpSet R) ε (hR t)



end ConvolutionSemigroup
end ProbabilityTheory

end
