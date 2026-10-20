/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Gaussian.FourthMoment
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Kolmogorov

/-!
# Fourth-moment Kolmogorov bound for Brownian finite-dimensional laws

The public theorem in this file is:

- `IsPreBrownianReal.isAEKolmogorovProcess_four`: a pre-Brownian process
  has a measurable modification $Y$ satisfying
  $\mathbb E|Y_t-Y_s|^4\le M|t-s|^2$ for one finite constant $M$.

This is the $n=2$ case of the moment step in Rémy Degenne et al.,
*Brownian Motion in Lean*, arXiv:2511.20118,
`BrownianMotion.Gaussian.BrownianMotion`, theorem
`IsPreBrownianReal.isAEKolmogorovProcess`. It is the continuity input for
the Brownian motion used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The Gaussian fourth-moment scaling gives the Kolmogorov condition with
exponents four and two, after making all time coordinates measurable. -/
theorem IsPreBrownianReal.isAEKolmogorovProcess_four
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
