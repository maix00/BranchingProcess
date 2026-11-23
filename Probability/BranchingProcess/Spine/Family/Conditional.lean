/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Family.Marginals

/-!
# Conditional selection of a spine child given its offspring family

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `lintegral_biasedFamilyChild_eq_conditional` identifies conditional child
  probabilities under the joint bias with `h(ξ_i)/∑_j h(ξ_j)`:
  `E_joint[g(ξ,i)] = E_family[∑_i h(ξ_i)/T(ξ) g(ξ,i)]`.
  The assumptions are measurable weights, `h(s) < ∞`, and the
  mean-harmonic identity `E_Q(s)[T] = h(s)`. The integral identity extends
  to zero-weight parents; positive weight makes the two laws probabilities.

This is the family-then-child description following (4.8) in Zhan Shi,
*Branching Random Walks* (2015), Chapter 4, §4.4,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
It is proved from the single joint kernel and its family marginal. A family
with zero or infinite total weight is handled by almost-everywhere identities;
no extra probability law or arbitrary default child is introduced.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

/-- Conditional child selection is the normalized weight within the realized family. -/
theorem lintegral_biasedFamilyChild_eq_conditional
    {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) (s : S)
    (htop : h s ≠ ∞)
    (harmonic : (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    {g : Step ι S × ι → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ p, g p ∂biasedFamilyChild Q h s) =
      ∫⁻ ξ, ∑' i, ((ξ i).elim 0 h / ∑' j, (ξ j).elim 0 h) * g (ξ, i)
        ∂biasedFamily Q h s := by
  let T : Step ι S → ℝ≥0∞ := fun ξ => ∑' i, (ξ i).elim 0 h
  have hw : ∀ i : ι, Measurable (fun ξ : Step ι S => (ξ i).elim 0 h) :=
    fun i => (measurable_option_elim 0 hh).comp (measurable_pi_apply i)
  have hT : Measurable T := Measurable.tsum hw
  have hfinite : ∀ᵐ ξ ∂Q s, T ξ ≠ ∞ := by
    filter_upwards [ae_lt_top hT (harmonic.trans_ne htop)] with ξ hξ
    exact hξ.ne
  have hG : Measurable (fun ξ : Step ι S =>
      ∑' i, ((ξ i).elim 0 h / T ξ) * g (ξ, i)) :=
    Measurable.tsum fun i => ((hw i).div hT).mul (by fun_prop)
  rw [lintegral_biasedFamilyChild Q hh hg s, biasedFamily_eq_withDensity Q hh,
    Kernel.lintegral_withDensity Q (f := fun s ξ => T ξ / h s) (by fun_prop) s hG]
  rw [← lintegral_tsum (f := fun i (ξ : Step ι S) =>
    ((ξ i).elim 0 h / h s) * g (ξ, i)) (fun i =>
      (((hw i).div_const (h s)).mul
        (show Measurable (fun ξ => g (ξ, i)) from by fun_prop)).aemeasurable)]
  apply lintegral_congr_ae
  filter_upwards [hfinite] with ξ hξ
  by_cases hTzero : T ξ = 0
  · have hwzero : ∀ i, (ξ i).elim 0 h = 0 := by
      intro i
      exact le_antisymm (hTzero ▸ le_tsum (fun j => (ξ j).elim 0 h) i) bot_le
    simp only [hwzero, ENNReal.zero_div, zero_mul, tsum_zero, mul_zero]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro i
    simp only [div_eq_mul_inv]
    calc
      _ = ((T ξ) * (T ξ)⁻¹) * ((ξ i).elim 0 h * (h s)⁻¹ * g (ξ, i)) := by
        rw [ENNReal.mul_inv_cancel hTzero hξ, one_mul]
      _ = _ := by ac_rfl

end ProbabilityTheory.BranchingProcess.Spine

end
