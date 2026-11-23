/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.FieldLaw
public import Probability.BranchingRandomWalk.Spine.Tilted.Law
public import Probability.BranchingProcess.Spine.StateChain
public import Probability.Process.RandomWalk.Kernel.Basic

/-!
# The additive branching realization of the general state kernel

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine.Additive`:

* `weight` is `h(x)=exp(-x)`; `measurable_weight`, `weight_ne_zero` and
  `weight_ne_top` give its measurable finite positive values.
* `offspringKernel φ μ` specializes the existing state update to
  `F(x,e)=x+φ(e)`, retaining absent children and the raw mark law.
* `offspringKernel.isMarkovKernel` follows when `μ` is a probability law.
* `map_stateTree_law` identifies the complete independent-field realization
  with the existing canonical state-tree law for this kernel.
* `spineChildKernel_eq_incrementKernel` identifies the general spine-state
  transition with translation by the existing tilted increment law.
* `harmonic_weight` derives `E_x[∑ h(child)] = h(x)` from boundary
  normalization, without ordering, moment, or nonextinction assumptions.

These are realization and hypothesis adapters for Zhan Shi,
*Branching Random Walks* (2015), Chapter 4, (4.1)–(4.4) and Theorem 4.4,
DOI 10.1007/978-3-319-25372-5. No second tree law is defined.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.Additive

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def weight (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-x))

@[fun_prop] theorem measurable_weight : Measurable weight := by fun_prop [weight]

@[simp] theorem weight_ne_zero (x : ℝ) : weight x ≠ 0 := by
  simp [weight, Real.exp_pos]

@[simp] theorem weight_ne_top (x : ℝ) : weight x ≠ ∞ := ENNReal.ofReal_ne_top

noncomputable def offspringKernel {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) : Kernel ℝ (Step ι ℝ) :=
  BranchingProcess.offspringStateKernel (fun x e => x + φ e)
    (measurable_fst.add (φ.measurable_toFun.comp measurable_snd)) (Kernel.const ℝ μ)

instance offspringKernel.isMarkovKernel {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (offspringKernel φ μ) := by
  unfold offspringKernel
  infer_instance

/-- Complete-tree law transport; the raw mark space remains arbitrary. -/
theorem map_stateTree_law {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) [IsProbabilityMeasure μ] (x : ℝ) :
    (BranchingProcess.offspringFieldLaw μ).map (stateTree (fun x e => x + φ e) x) =
      BranchingProcess.State.treeKernel (offspringKernel φ μ) (some x) :=
  BranchingProcess.State.map_stateTree_offspringFieldLaw μ
    (fun (y : ℝ) (e : Mark) => y + φ e)
    (measurable_fst.add (φ.measurable_toFun.comp measurable_snd)) x

private lemma child_weight {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (x : ℝ) (ξ : Step ι Mark) (i : ι) :
    ((ξ.map (fun e => x + φ e)) i).elim 0 weight =
      weight x * realizedPotentialWeight φ (-1) ξ i := by
  classical
  cases hi : ξ i with
  | none => simp [Step.map, hi, realizedPotentialWeight, survive]
  | some e =>
    simp [Step.map, hi, realizedPotentialWeight, survive, Step.potentialValue', Step.potentialAt?, weight,
      Real.exp_add, mul_comm]
    exact ENNReal.ofReal_mul (Real.exp_pos _).le

/-- Boundary normalization is exactly the harmonicity needed by the general
spine construction, after the existing additive state update. -/
theorem harmonic_weight {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (x : ℝ) :
    (∫⁻ ξ, ∑' i, (ξ i).elim 0 weight ∂offspringKernel φ μ x) = weight x := by
  rw [offspringKernel, BranchingProcess.offspringStateKernel_apply, Kernel.const_apply]
  have hm : Measurable (fun ξ : Step ι ℝ => ∑' i, (ξ i).elim 0 weight) :=
    Measurable.tsum fun i =>
      (measurable_option_elim 0 measurable_weight).comp (measurable_pi_apply i)
  have hmap : Measurable (Step.map (fun e : Mark => x + φ e) :
      Step ι Mark → Step ι ℝ) :=
    Step.map_measurable (measurable_const.add φ.measurable_toFun)
  rw [lintegral_map hm hmap]
  simp_rw [child_weight, ENNReal.tsum_mul_left]
  change (∫⁻ a, weight x * totalPotentialWeight φ (-1) a ∂μ) = weight x
  rw [lintegral_const_mul (weight x) (totalPotentialWeight_measurable φ (-1))]
  exact (congrArg (weight x * ·) hboundary).trans (mul_one _)

private lemma child_weight_test {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (x : ℝ) (ξ : Step ι Mark) (i : ι) (g : ℝ → ℝ≥0∞) :
    ((ξ.map (fun e => x + φ e)) i).elim 0 (fun y => weight y * g y) =
      weight x * (realizedPotentialWeight φ (-1) ξ i * g (x + ξ.potentialValue' φ i)) := by
  cases hi : ξ i with
  | none => simp [Step.map, hi, realizedPotentialWeight, survive]
  | some e =>
    have hw := child_weight φ x ξ i
    simp only [Step.map, hi, Option.map_some, Option.elim_some] at hw ⊢
    rw [hw]
    simp [Step.potentialValue', Step.potentialAt?, hi, mul_assoc]

/-- The canonical spine sees the old tilted increment law, translated by its
current state. This is a transition-law identification, not a second walk. -/
theorem spineChildKernel_eq_incrementKernel {ι Mark : Type*}
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) :
    letI := tiltedPotentialLaw_isProbability φ μ hboundary
    BranchingProcess.Spine.spineChildKernel (offspringKernel φ μ) weight =
      RandomWalk.incrementKernel (tiltedPotentialLaw φ (-1) μ) := by
  let := tiltedPotentialLaw_isProbability φ μ hboundary
  rw [BranchingProcess.Spine.spineChildKernel_eq_doobTransform _ measurable_weight]
  apply Kernel.ext_fun
  intro x g hg
  rw [Kernel.lintegral_doobTransform _ measurable_weight hg]
  have hwg : Measurable (fun y => weight y * g y) := measurable_weight.mul hg
  rw [BranchingProcess.lintegral_meanChildKernel _ hwg]
  have hm : Measurable (fun ξ : Step ι ℝ => ∑' i, (ξ i).elim 0 (fun y => weight y * g y)) :=
    Measurable.tsum fun i =>
      (measurable_option_elim 0 (measurable_weight.mul hg)).comp (measurable_pi_apply i)
  have hmap : Measurable (Step.map (fun e : Mark => x + φ e) : Step ι Mark → Step ι ℝ) :=
    Step.map_measurable (measurable_const.add φ.measurable_toFun)
  rw [offspringKernel, BranchingProcess.offspringStateKernel_apply, Kernel.const_apply,
    lintegral_map hm hmap]
  simp_rw [child_weight_test, ENNReal.tsum_mul_left]
  have ht : Measurable (fun ξ : Step ι Mark =>
      ∑' i, realizedPotentialWeight φ (-1) ξ i * g (x + ξ.potentialValue' φ i)) :=
    Measurable.tsum fun i => (realizedPotentialWeight_measurable φ (-1) i).mul
      (hg.comp (measurable_const.add (Step.potentialValue'_measurable φ i)))
  rw [lintegral_const_mul (weight x) ht]
  have hcancel (v : ℝ≥0∞) : weight x * v / weight x = v := by
    simp only [div_eq_mul_inv, mul_assoc]
    rw [mul_comm v (weight x)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel (weight_ne_zero x) (weight_ne_top x), one_mul]
  rw [hcancel]
  have hx : Measurable (fun y : ℝ => x + y) := measurable_const.add measurable_id
  rw [RandomWalk.incrementKernel_apply, lintegral_map hg hx]
  exact (lintegral_tiltedPotentialLaw φ (-1) μ (fun y => g (x + y))
    (hg.comp (measurable_const.add measurable_id))).symm

end ProbabilityTheory.BranchingRandomWalk.Spine.Additive
