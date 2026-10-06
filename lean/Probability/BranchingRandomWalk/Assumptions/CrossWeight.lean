/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Cross-child exponential weight

The cross term is a permutation-invariant observable of the raw optional-slot
step. It is kept separate from one-slot moment assumptions because it is a
pair-weight integrability condition and remains meaningful before any ordered
enumeration is chosen.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory

/-- The cross term `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`, with absent slots contributing
zero. The value is allowed to be infinite before imposing the assumption. -/
noncomputable def crossChildWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Combinatorics.Branching.Step ι X) : ENNReal := by
  classical
  exact ∑' i : ι, ∑' j : ι,
    if i ≠ j ∧ survive ξ i ∧ survive ξ j then
      ENNReal.ofReal
        (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
    else 0

theorem crossChildWeight_measurable {ι X : Type*} [Countable ι]
    [MeasurableSpace X] (φ : Potential X) :
    Measurable (crossChildWeight (ι := ι) φ :
      Combinatorics.Branching.Step ι X → ENNReal) := by
  classical
  unfold crossChildWeight
  apply Measurable.tsum
  intro i
  apply Measurable.tsum
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hset : MeasurableSet
        ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) :=
      (survive_measurableSet (X := X) i).inter
        (survive_measurableSet (X := X) j)
    have hvalue : Measurable (fun ξ : Combinatorics.Branching.Step ι X =>
        ENNReal.ofReal
          (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))) :=
      ENNReal.measurable_ofReal.comp
        (((Step.potentialValue'_measurable φ i).add
          (Step.potentialValue'_measurable φ j)).neg.exp)
    simp only [hij, ne_eq, not_false_eq_true, true_and]
    change Measurable (fun ξ : Combinatorics.Branching.Step ι X =>
      if ξ ∈ ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) then
        ENNReal.ofReal
          (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
      else 0)
    exact hvalue.ite hset measurable_const

/-- The raw law has finite cross-child exponential weight. -/
def HasFiniteCrossWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) : Prop :=
  (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≠ ∞

end ProbabilityTheory.BranchingRandomWalk

end
