/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Finite fourth moment of the standard Gaussian law

The public theorem in this file is:

- `gaussianReal_zero_one_lintegral_enorm_four_lt_top`:
  $\int |x|^4\,N(0,1)(dx)<\infty$.
- `gaussianReal_zero_lintegral_enorm_four_eq`:
  $\int |x|^4\,N(0,v)(dx)=v^2\int |x|^4\,N(0,1)(dx)$.

This moment input is used in the Kolmogorov--Chentsov continuity argument
for Brownian motion in Rémy Degenne et al., *Brownian Motion in Lean*,
arXiv:2511.20118, `BrownianMotion.Gaussian.BrownianMotion`, theorem
`IsPreBrownianReal.isAEKolmogorovProcess`. The finite-moment theorem itself comes from Mathlib's
Gaussian Fernique theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The standard Gaussian law has a finite fourth absolute moment. -/
theorem gaussianReal_zero_one_lintegral_enorm_four_lt_top :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂gaussianReal 0 1) < ⊤ := by
  have hLp : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    IsGaussian.memLp_id (gaussianReal 0 1) 4 (by norm_num)
  have hFinite := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hLp.eLpNorm_lt_top
  simpa using hFinite

/-- The fourth absolute moment of a centered Gaussian law scales as the
square of its variance. -/
theorem gaussianReal_zero_lintegral_enorm_four_eq (v : ℝ≥0) :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 v) =
      (v : ℝ≥0∞) ^ (2 : ℕ) *
        (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt (v : ℝ)
  have hc : c ^ 2 = (v : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg v)
  have hmap : (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
    simpa using hc
  rw [← hmap]
  have hchange :
      (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 (1 : ℝ≥0)).map
        (fun x : ℝ => c * x)) =
        ∫⁻ x : ℝ, ‖c * x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1 := by
    exact lintegral_map (measurable_id.enorm.pow_const (4 : ℕ))
      (by fun_prop : Measurable fun x : ℝ => c * x)
  rw [hchange]
  simp only [enorm_mul, mul_pow]
  have hcNonnegative : 0 ≤ c := Real.sqrt_nonneg _
  have hcoefficient : ‖c‖ₑ ^ (4 : ℕ) = (v : ℝ≥0∞) ^ (2 : ℕ) := calc
    ‖c‖ₑ ^ (4 : ℕ) = (ENNReal.ofReal c ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [Real.enorm_eq_ofReal hcNonnegative]
      norm_num [← pow_mul]
    _ = (ENNReal.ofReal (c ^ 2)) ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_pow hcNonnegative]
    _ = (v : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [hc, ENNReal.ofReal_coe_nnreal]
  calc
    (∫⁻ x : ℝ, ‖c‖ₑ ^ (4 : ℕ) * ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1) =
        ‖c‖ₑ ^ (4 : ℕ) *
          (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1) := by
      exact lintegral_const_mul (‖c‖ₑ ^ (4 : ℕ))
        (measurable_id.enorm.pow_const (4 : ℕ))
    _ = _ := by rw [hcoefficient]

end ProbabilityTheory

end
