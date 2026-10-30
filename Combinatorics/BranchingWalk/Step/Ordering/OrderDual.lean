/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Map
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight
public import Mathlib.Order.OrderDual

/-!
# Order duality of real-marked branching steps

For an optional-child step $\xi : \iota \to \mathrm{Option}(\mathbb R)$,
`stepOrderDual` keeps the surviving slots and reads each mark in the reversed
order. Its potential is the negative of the original mark, so the dual
negative-tilt exponential weights equal the original positive-tilt weights.
These deterministic identities require no law, moment, or countability
assumptions; only the support and finite-sum definitions of total weights are
inherited from their existing interfaces.

## Public declarations

- `Combinatorics.Branching.orderDualPotential`: $\phi^*(x)=-x$ on
  $\mathrm{OrderDual}(\mathbb R)$.
- `Combinatorics.Branching.stepOrderDual`: maps a real-marked step by
  $\mathrm{OrderDual.toDual}$ while preserving absent slots.
- `Combinatorics.Branching.measurable_stepOrderDual`: the step map is measurable.
- `Combinatorics.Branching.survive_stepOrderDual_iff`: slot survival is preserved.
- `Combinatorics.Branching.orderDualPotentialValue_stepOrderDual`:
  $\phi^*(\xi^*,i)=-\mathrm{value}'(\xi,i)$.
- `Combinatorics.Branching.realizedPotentialWeight_orderDual_stepOrderDual` and
  `Combinatorics.Branching.totalPotentialWeight_orderDual_stepOrderDual`:
  the dual $-1$ weight equals the original $+1$ weight, slotwise and in total.
- `Combinatorics.Branching.orderDualPotentialValue_stepMap`:
  mapping a dual-marked step by $\phi^*$ preserves its potential value as a real mark.
- `Combinatorics.Branching.realizedPotentialWeight_real_stepMapOrderDualPotential` and
  `Combinatorics.Branching.totalPotentialWeight_real_stepMapOrderDualPotential`:
  real $-1$ weights after this map equal the dual $-1$ weights.
- `Combinatorics.Branching.mem_nonemptySupport_stepOrderDual_iff`:
  the mapped step has nonempty support exactly when the original does.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace Combinatorics.Branching

variable {ι : Type*}

/-- The real-valued potential that is increasing in the order-dual order. -/
def orderDualPotential : Potential (OrderDual ℝ) where
  toFun := fun x => -(OrderDual.ofDual x)
  measurable_toFun := by
    exact measurable_neg.comp measurable_id

/-- Observe a real displacement in the reversed order without changing its
underlying value. -/
def stepOrderDual (ξ : Step ι ℝ) : Step ι (OrderDual ℝ) :=
  ξ.map OrderDual.toDual

theorem measurable_stepOrderDual {ι : Type*} :
    Measurable (stepOrderDual (ι := ι)) := by
  have hf : Measurable (OrderDual.toDual : ℝ → OrderDual ℝ) := measurable_id
  exact Step.map_measurable hf

@[simp] theorem survive_stepOrderDual_iff (ξ : Step ι ℝ) (i : ι) :
    survive (stepOrderDual ξ) i ↔ survive ξ i := by
  exact survive_map_iff OrderDual.toDual ξ i

theorem orderDualPotentialValue_stepOrderDual (ξ : Step ι ℝ) (i : ι) :
    (stepOrderDual ξ).potentialValue' orderDualPotential i =
      -(value' ξ i) := by
  cases h : ξ i <;>
    simp [stepOrderDual, orderDualPotential, Step.map,
      Step.potentialValue', Step.potentialAt?, value', h]

@[simp] theorem realizedPotentialWeight_orderDual_stepOrderDual
    (ξ : Step ι ℝ) (i : ι) :
    realizedPotentialWeight orderDualPotential (-1) (stepOrderDual ξ) i =
      realizedPotentialWeight realPotential 1 ξ i := by
  cases h : ξ i <;>
    simp [realizedPotentialWeight, stepOrderDual, Step.map, survive,
      orderDualPotential, Step.potentialValue', Step.potentialAt?,
      realPotential, h]

@[simp] theorem totalPotentialWeight_orderDual_stepOrderDual
    (ξ : Step ι ℝ) :
    totalPotentialWeight orderDualPotential (-1) (stepOrderDual ξ) =
      totalPotentialWeight realPotential 1 ξ := by
  unfold totalPotentialWeight
  apply tsum_congr
  intro i
  have hsurv := survive_stepOrderDual_iff ξ i
  by_cases hs : survive ξ i
  · have hs' : survive (stepOrderDual ξ) i := hsurv.mpr hs
    simp only [realizedPotentialWeight, hs, hs', ite_true]
    rw [orderDualPotentialValue_stepOrderDual]
    have hreal : Step.potentialValue' realPotential ξ i = value' ξ i := by
      simp [Step.potentialValue', Step.potentialAt?, realPotential, value']
    rw [hreal]
    change ENNReal.ofReal (Real.exp ((-1 : ℝ) * -(value' ξ i))) =
      ENNReal.ofReal (Real.exp ((1 : ℝ) * value' ξ i))
    exact congrArg (fun x : ℝ => ENNReal.ofReal (Real.exp x)) (by ring)
  · have hs' : ¬ survive (stepOrderDual ξ) i := fun h => hs (hsurv.mp h)
    simp [realizedPotentialWeight, hs, hs']

@[simp] theorem orderDualPotentialValue_stepMap
    (ξ : Step ι (OrderDual ℝ)) (i : ι) :
    (ξ.map orderDualPotential).potentialValue' realPotential i =
      ξ.potentialValue' orderDualPotential i := by
  cases h : ξ i <;>
    simp [Step.map, Step.potentialValue', Step.potentialAt?, realPotential,
      orderDualPotential, h]

@[simp] theorem realizedPotentialWeight_real_stepMapOrderDualPotential
    (ξ : Step ι (OrderDual ℝ)) (i : ι) :
    realizedPotentialWeight realPotential (-1)
        (ξ.map orderDualPotential) i =
      realizedPotentialWeight orderDualPotential (-1) ξ i := by
  cases h : ξ i <;>
    simp [realizedPotentialWeight, Step.map, survive,
      Step.potentialValue', Step.potentialAt?, realPotential,
      orderDualPotential, h]

@[simp] theorem totalPotentialWeight_real_stepMapOrderDualPotential
    (ξ : Step ι (OrderDual ℝ)) :
    totalPotentialWeight realPotential (-1)
        (ξ.map orderDualPotential) =
      totalPotentialWeight orderDualPotential (-1) ξ := by
  unfold totalPotentialWeight
  apply tsum_congr
  intro i
  exact realizedPotentialWeight_real_stepMapOrderDualPotential ξ i

theorem mem_nonemptySupport_stepOrderDual_iff (ξ : Step ι ℝ) :
    stepOrderDual ξ ∈ nonemptySupport ↔ ξ ∈ nonemptySupport := by
  simp [nonemptySupport, stepOrderDual]

end Combinatorics.Branching

end
