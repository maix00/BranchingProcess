/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Kolmogorov

/-!
# Fourth-moment Kolmogorov bound for Brownian finite-dimensional laws

## Internal proof declarations

- `gaussianReal_zero_one_lintegral_enorm_four_lt_top` proves
  $\int |x|^4\,N(0,1)(dx)<\infty$, and
  `gaussianReal_zero_lintegral_enorm_four_eq` gives
  $\int |x|^4\,N(0,v)(dx)=v^2\int |x|^4\,N(0,1)(dx)$. These are private
  moment inputs derived from Mathlib's Gaussian $L^p$ theorem and scaling law.
- `IsPreBrownianReal.isAEKolmogorovProcess_four`: a pre-Brownian process
  has a measurable modification $Y$ satisfying
  $\mathbb E|Y_t-Y_s|^4\le M|t-s|^2$ for one finite constant $M$.

This one-use fourth-moment specialization supplies the Kolmogorov input for
`Construction/PreBrownianModification.lean`. The more general BrownianMotion
source theorem is cited below; its module currently requires upstream
compatibility repairs against the pinned Mathlib revision.

This is the $n=2$ case of the moment step in Rémy Degenne et al.,
*Brownian Motion in Lean*, arXiv:2511.20118,
`BrownianMotion.Gaussian.BrownianMotion`, theorem
`IsPreBrownianReal.isAEKolmogorovProcess`. It is the continuity input for
the Brownian motion used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5.
-/

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The standard Gaussian law has a finite fourth absolute moment. -/
private lemma gaussianReal_zero_one_lintegral_enorm_four_lt_top :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂gaussianReal 0 1) < ⊤ := by
  have hLp : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    IsGaussian.memLp_id (gaussianReal 0 1) 4 (by norm_num)
  have hFinite := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hLp.eLpNorm_lt_top
  simpa using hFinite

/-- The fourth absolute moment of a centered Gaussian law scales as the
square of its variance. -/
private lemma gaussianReal_zero_lintegral_enorm_four_eq (v : ℝ≥0) :
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

/-- The Gaussian fourth-moment scaling gives the Kolmogorov condition with
exponents four and two, after making all time coordinates measurable. -/
lemma IsPreBrownianReal.isAEKolmogorovProcess_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsAEKolmogorovProcess B P 4 2
      ((∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1).toNNReal) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t)
  have hBY (t : ℝ≥0) : B t =ᵐ[P] Y t :=
    (hB.aemeasurable t).ae_eq_mk
  have hY : IsPreBrownianReal Y P := hB.congr hBY
  have hYmeasurable (t : ℝ≥0) : Measurable (Y t) :=
    (hB.aemeasurable t).measurable_mk
  let m : ℝ≥0∞ := ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1
  have hmFinite : m ≠ ⊤ := by
    exact ne_of_lt (by simpa [m] using
      gaussianReal_zero_one_lintegral_enorm_four_lt_top)
  have hmCoeff : ((m.toNNReal : ℝ≥0) : ℝ≥0∞) = m :=
    ENNReal.coe_toNNReal hmFinite
  refine ⟨Y, ?_, hBY⟩
  apply IsKolmogorovProcess.mk_of_secondCountableTopology hYmeasurable
  · intro s t
    have hLaw := hY.hasLaw_sub s t
    have hPointwise (ω : Ω) : (Y s - Y t) ω = Y s ω - Y t ω := by
      exact Pi.sub_apply _ _ _
    have hIntegral :
        (∫⁻ ω, edist (Y s ω) (Y t ω) ^ (4 : ℕ) ∂P) =
          ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 (nndist (s : ℝ) t) := by
      have hInt := hLaw.lintegral_comp
        (measurable_id.enorm.pow_const (4 : ℕ)).aemeasurable
      simp only [id_eq, hPointwise, ← edist_eq_enorm_sub] at hInt
      exact hInt
    calc
      _ = ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂gaussianReal 0 (nndist (s : ℝ) t) := by
        simpa only [← ENNReal.rpow_natCast, Nat.cast_ofNat] using hIntegral
      _ = (↑(nndist (s : ℝ) t) : ℝ≥0∞) ^ (2 : ℕ) * m := by
        simpa only [m, ← ENNReal.rpow_natCast, Nat.cast_ofNat] using gaussianReal_zero_lintegral_enorm_four_eq
          (nndist (s : ℝ) t)
      _ ≤ _ := by
        rw [hmCoeff]
        simp only [← ENNReal.rpow_natCast, Nat.cast_ofNat]
        rw [edist_nndist]
        have hdist : nndist (s : ℝ) (t : ℝ) = nndist s t := by
          apply NNReal.eq
          simp only [coe_nndist]
          rfl
        rw [hdist]
        simpa only [← ENNReal.rpow_natCast, Nat.cast_ofNat] using
          (mul_comm ((nndist s t : ℝ≥0∞) ^ (2 : ℕ)) m).le
  · norm_num
  · norm_num

end ProbabilityTheory

end
