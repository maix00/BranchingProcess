/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Finite
public import Combinatorics.BranchingWalk.Step.Selection.Potential
import MeasureTheory.Selection.NSelection.FromSet
import MeasureTheory.Selection.NSelection.ByValue

/-!
# Measurable finite selections from a branching step

The intrinsic first-`N` selection of an unordered branching step is measurable
when the slot labels are countable and its comparison keys are measurable.
These are measurable adapters for the combinatorial `Step.FiniteSelection`
constructors.

## Public declarations

- `Combinatorics.Branching.Step.FiniteSelection.firstNBy_measurable` proves
  `\(\operatorname{Measurable}(\xi \mapsto
  \operatorname{firstNBy}(N,\operatorname{value})(\xi).select)\)` under
  admissibility and measurable pairwise comparison keys.
- `Combinatorics.Branching.Step.FiniteSelection.firstNByPotential_measurable`
  gives the same measurability conclusion when candidates are ordered by a
  real-valued potential.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching.Step.FiniteSelection

open _root_.Combinatorics.Selection.NSelection

theorem firstNBy_measurable
    {α X Value : Type*} [Countable α]
    [MeasurableSpace X] [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ))
    (hkey : ∀ p q : α, Measurable fun ξ : Step α X =>
      valueKey (value ξ) q < valueKey (value ξ) p) :
    Measurable (Step.FiniteSelection.firstNBy N value hadmits).select := by
  apply Combinatorics.Selection.NSelection.measurable_selectFirstNFromSet
    N value (fun ξ : Step α X => support ξ) hadmits
  · rw [measurable_set_iff]
    intro i
    exact measurableSet_setOfPred.mp (survive_measurableSet i)
  · exact hkey

theorem firstNByPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X)
    (hadmits : ∀ ξ : Step α X, AdmitsFirstNBy N
      (fun i => ξ.potentialValue' φ i) (support ξ)) :
    Measurable
      (Step.FiniteSelection.firstNByPotential N φ hadmits).select := by
  apply firstNBy_measurable N
    (fun (ξ : Step α X) i => ξ.potentialValue' φ i) hadmits
  intro p q
  exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
    (fun (ξ : Step α X) i => ξ.potentialValue' φ i)
    (fun i => Step.potentialValue'_measurable φ i) p q

end Combinatorics.Branching.Step.FiniteSelection

end
