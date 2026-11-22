/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Offspring configurations locally finite on the left

## Public declarations

- `Step.IsLeftLocallyFinite` means that $\#\{i:\xi_i\le x\}<\infty$ for every
  real $x$, counting surviving child slots.
- `Step.measurableSet_isLeftLocallyFinite` makes this a measurable event on
  the space of steps with countable child slots.
- `Step.isLeftLocallyFinite_of_totalPotentialWeight_ne_top` proves that
  $\sum_i e^{-\beta\xi_i}<\infty$ for $\beta>0$ implies left local finiteness.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Combinatorics.Branching

/-- Every left half-line contains only finitely many surviving child slots. -/
def Step.IsLeftLocallyFinite {ι : Type*} (ξ : Step ι ℝ) : Prop :=
  ∀ x : ℝ, {i : ι | survive ξ i ∧ value' ξ i ≤ x}.Finite

theorem Step.measurableSet_isLeftLocallyFinite {ι : Type*} [Countable ι] :
    MeasurableSet {ξ : Step ι ℝ | ξ.IsLeftLocallyFinite} := by
  let lower : ℕ → Step ι ℝ → Set ι :=
    fun n ξ => {i | survive ξ i ∧ value' ξ i ≤ (n : ℝ)}
  have hset : {ξ : Step ι ℝ | ξ.IsLeftLocallyFinite} =
      ⋂ n : ℕ, {ξ | (lower n ξ).encard ≠ ⊤} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.encard_ne_top_iff]
    constructor
    · exact fun h n => h n
    · intro h x
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact (h n).subset fun i hi => ⟨hi.1, hi.2.trans hn⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro n
  have h_lower : Measurable (lower n) := by
    rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp ((survive_measurableSet i).inter
      (measurableSet_le (value'_measurable i) measurable_const))
  exact ((measurable_encard.comp h_lower) (measurableSet_singleton ⊤).compl)

theorem Step.isLeftLocallyFinite_of_totalPotentialWeight_ne_top
    {ι : Type*} (ξ : Step ι ℝ) {β : ℝ} (hβ : 0 < β)
    (hweight : totalPotentialWeight realPotential (-β) ξ ≠ ∞) :
    ξ.IsLeftLocallyFinite := by
  intro x
  have hlarge : {i | ENNReal.ofReal (Real.exp (-β * x)) ≤
      realizedPotentialWeight realPotential (-β) ξ i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hweight
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  apply hlarge.subset
  intro i hi
  have hvalue : ξ.potentialValue' realPotential i = value' ξ i := by
    cases h : ξ i <;> simp [Step.potentialValue', Step.potentialAt?, realPotential, value', h]
  have hle := ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hi.2 (neg_nonpos.mpr hβ.le)))
  simpa [realizedPotentialWeight, hi.1, hvalue] using hle

end Combinatorics.Branching

end
