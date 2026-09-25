import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued offspring encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  It is kept separate from the legacy weighted
slot implementation so that the latter can be migrated without changing the
pre-sampled-tree API in one step.
-/

open MeasureTheory

namespace ThesisSpeed

abbrev OptionOffspringConfig := ℕ → Option ℝ

def optionChildPresent (ξ : OptionOffspringConfig) (i : ℕ) : Prop :=
  ∃ x, ξ i = some x

def optionPrefixOrdered (ξ : OptionOffspringConfig) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → x ≤ y

def optionPresencePrefix (ξ : OptionOffspringConfig) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

def OrderedOptionOffspring (ξ : OptionOffspringConfig) : Prop :=
  optionPresencePrefix ξ ∧ optionPrefixOrdered ξ

noncomputable def optionChildAtomMeasure (ξ : OptionOffspringConfig) (i : ℕ) :
    Measure ℝ := by
  classical
  exact match ξ i with
  | some x => Measure.dirac x
  | none => 0

noncomputable def optionOffspringPointMeasure (ξ : OptionOffspringConfig) :
    Measure ℝ := Measure.sum (optionChildAtomMeasure ξ)

end ThesisSpeed
