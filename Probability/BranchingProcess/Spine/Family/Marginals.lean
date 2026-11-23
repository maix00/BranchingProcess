/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Family.Joint
public import Probability.BranchingProcess.Offspring.Mean

/-!
# Family and selected-state marginals of the joint spine bias

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `biasedFamily Q h` is the family marginal of `biasedFamilyChild Q h`.
* `biasedFamily_eq_withDensity` identifies its density with
  `(∑_i h(ξ_i))/h(s)` relative to the original family law.
* `ae_biasedFamily_totalWeight` proves `0 < ∑_i h(ξ_i) < ∞` almost surely
  under the biased family, making the conditional selection weights meaningful.
* `spineChildKernel Q h` is the selected-state marginal, discarding absent slots.
* `spineChildKernel_eq_doobTransform` states that it equals the Doob transform
  of `meanChildKernel Q`.
* `ae_biasedFamilyChild_eligible` proves that the chosen child is present and
  has finite positive weight, under the mean-harmonic identity at an eligible parent.

These are the two marginals of one joint construction, rather than independent
biased laws. They give the general-state form of Zhan Shi, *Branching Random
Walks* (2015), Chapter 4, §4.4, (4.8) and Theorem 4.4(ii),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
The full tree/path assertions in that theorem require the subsequent process
construction; the results here identify its one-generation ingredients.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]

/-- The family marginal of the joint family/child bias. -/
noncomputable def biasedFamily (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (h : S → ℝ≥0∞) : Kernel S (Step ι S) :=
  (biasedFamilyChild Q h).map Prod.fst

/-- The family bias is the sum of its child weights, divided by the parent's weight. -/
theorem biasedFamily_eq_withDensity (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) :
    biasedFamily Q h = Q.withDensity (fun s ξ => (∑' i, (ξ i).elim 0 h) / h s) := by
  have hw : ∀ i : ι, Measurable (fun ξ : Step ι S => (ξ i).elim 0 h) :=
    fun i => (measurable_option_elim 0 hh).comp (measurable_pi_apply i)
  apply Kernel.ext_fun
  intro s g hg
  rw [biasedFamily, Kernel.lintegral_map _ measurable_fst s hg,
    lintegral_biasedFamilyChild Q hh (g := fun p => g p.1) (by fun_prop) s]
  have hd : Measurable (Function.uncurry
      (fun s (ξ : Step ι S) => (∑' i, (ξ i).elim 0 h) / h s)) := by
    exact ((Measurable.tsum (fun i => (hw i).comp measurable_snd)).div
      (hh.comp measurable_fst))
  rw [Kernel.lintegral_withDensity Q hd s hg]
  symm
  calc
    _ = ∫⁻ ξ, ∑' i : ι, ((ξ i).elim 0 h / h s) * g ξ ∂Q s := by
      apply lintegral_congr
      intro ξ
      simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
    _ = _ := lintegral_tsum (fun i => ((hw i).div_const _ |>.mul hg).aemeasurable)

/-- Normalized conditional child weights have finite nonzero total, almost surely. -/
theorem ae_biasedFamily_totalWeight (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) (s : S) (htop : h s ≠ ∞)
    (harmonic : (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    ∀ᵐ ξ ∂biasedFamily Q h s,
      (∑' i, (ξ i).elim 0 h) ≠ 0 ∧ (∑' i, (ξ i).elim 0 h) ≠ ∞ := by
  let T (ξ : Step ι S) := ∑' i, (ξ i).elim 0 h
  have hT : Measurable T := Measurable.tsum (fun i =>
    (measurable_option_elim 0 hh).comp (measurable_pi_apply i))
  rw [biasedFamily_eq_withDensity Q hh]
  have hd : Measurable (Function.uncurry (fun s (ξ : Step ι S) => T ξ / h s)) :=
    (hT.comp measurable_snd).div (hh.comp measurable_fst)
  rw [Kernel.withDensity_apply Q hd]
  have hfinite : ∀ᵐ ξ ∂Q s, T ξ ≠ ∞ := by
    filter_upwards [ae_lt_top hT (harmonic.trans_ne htop)] with ξ hξ
    exact hξ.ne
  apply (ae_withDensity_iff (hT.div_const (h s))).mpr
  filter_upwards [hfinite] with ξ hξ hdensity
  refine ⟨?_, hξ⟩
  intro hz
  change T ξ = 0 at hz
  exact hdensity (by rw [hz]; exact ENNReal.zero_div)

/-- The selected state is read from the joint family and index; absence has zero mass. -/
noncomputable def spineChildKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (h : S → ℝ≥0∞) : Kernel S S :=
  ((biasedFamilyChild Q h).map (fun p => p.1 p.2)).comapRight
    measurableEmbedding_option_some

/-- The distinguished child's state follows the Doob transform of the mean offspring kernel. -/
theorem spineChildKernel_eq_doobTransform [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) :
    spineChildKernel Q h = (meanChildKernel Q).doobTransform h := by
  have heval : Measurable (fun p : Step ι S × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  apply Kernel.ext_fun
  intro s g hg
  have ho : Measurable (fun o : Option S => o.elim 0 g) := measurable_option_elim 0 hg
  calc
    _ = ∫⁻ o, o.elim 0 g ∂(spineChildKernel Q h s).map some := by
      rw [measurableEmbedding_option_some.lintegral_map]
      rfl
    _ = ∫⁻ p, (p.1 p.2).elim 0 g ∂biasedFamilyChild Q h s := by
      rw [spineChildKernel, Kernel.comapRight_apply,
        measurableEmbedding_option_some.map_comap,
        ← lintegral_indicator measurableEmbedding_option_some.measurableSet_range]
      have hzero : (Set.range some).indicator (fun o : Option S => o.elim 0 g) =
          (fun o : Option S => o.elim 0 g) := by
        funext o
        cases o <;> simp
      rw [hzero, Kernel.lintegral_map _ heval s ho]
    _ = ∑' i, ∫⁻ ξ, ((ξ i).elim 0 h / h s) * (ξ i).elim 0 g ∂Q s := by
      exact lintegral_biasedFamilyChild Q hh (g := fun p => (p.1 p.2).elim 0 g)
        (ho.comp heval) s
    _ = (∫⁻ ξ, ∑' i, (ξ i).elim 0 (fun t => h t * g t) ∂Q s) / h s := by
      simp only [div_eq_mul_inv]
      have hterm : ∀ ξ : Step ι S, ∀ i, (ξ i).elim 0 h * (h s)⁻¹ * (ξ i).elim 0 g =
          (ξ i).elim 0 (fun t => h t * g t) * (h s)⁻¹ := by
        intro ξ i
        cases ξ i with
        | none => simp
        | some t => dsimp; ac_rfl
      simp_rw [hterm]
      have hw : ∀ i : ι, Measurable (fun ξ : Step ι S =>
          (ξ i).elim 0 (fun t => h t * g t)) := fun i =>
        (measurable_option_elim 0 (hh.mul hg)).comp (measurable_pi_apply i)
      simp_rw [lintegral_mul_const _ (hw _)]
      rw [ENNReal.tsum_mul_right, lintegral_tsum (fun i => (hw i).aemeasurable)]
    _ = _ := by
      rw [Kernel.lintegral_doobTransform _ hh hg s]
      congr 1
      exact (lintegral_meanChildKernel Q (f := fun t => h t * g t) (by fun_prop) s).symm

/-- The distinguished child exists and remains in the finite positive-weight domain. -/
theorem ae_biasedFamilyChild_eligible [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) (s : S)
    (hzero : h s ≠ 0) (htop : h s ≠ ∞)
    (harmonic : (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    ∀ᵐ p ∂biasedFamilyChild Q h s,
      ∃ t, p.1 p.2 = some t ∧ h t ≠ 0 ∧ h t ≠ ∞ := by
  let C : Set S := {t | h t ≠ 0 ∧ h t ≠ ∞}
  have hC : MeasurableSet C :=
    (hh (MeasurableSet.singleton 0).compl).inter (hh (MeasurableSet.singleton ∞).compl)
  have hmean : (∫⁻ t, h t ∂meanChildKernel Q s) = h s :=
    (lintegral_meanChildKernel Q hh s).trans harmonic
  let : IsProbabilityMeasure (biasedFamilyChild Q h s) :=
    biasedFamilyChild_isProbabilityMeasure Q hh s hzero htop harmonic
  let : IsProbabilityMeasure ((meanChildKernel Q).doobTransform h s) :=
    Kernel.doobTransform_isProbabilityMeasure _ hh s hzero htop hmean
  have hgood : (meanChildKernel Q).doobTransform h s C = 1 := by
    apply (mem_ae_iff_prob_eq_one hC).mp
    exact (Kernel.ae_doobTransform_weight_ne_zero _ hh s).and
      (Kernel.ae_doobTransform_weight_ne_top _ hh s (hmean.trans_ne htop))
  have heval : Measurable (fun p : Step ι S × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hsC := measurableSet_option_some_image hC
  have hmass : (biasedFamilyChild Q h s) ((fun p => p.1 p.2) ⁻¹' (some '' C)) = 1 := by
    rw [← Kernel.map_apply' _ heval s hsC,
      ← Kernel.comapRight_apply' _ measurableEmbedding_option_some s hC]
    change spineChildKernel Q h s C = 1
    rw [spineChildKernel_eq_doobTransform Q hh]
    exact hgood
  have hA := (mem_ae_iff_prob_eq_one (hsC.preimage heval)).mpr hmass
  filter_upwards [hA] with p hp
  obtain ⟨t, ht, he⟩ := hp
  exact ⟨t, he.symm, ht⟩

end ProbabilityTheory.BranchingProcess.Spine

end
