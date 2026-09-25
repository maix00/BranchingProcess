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
open Classical

namespace ThesisSpeed

abbrev OffspringConfig (ι X : Type*) := ι → Option X

def offspringConfigPresent {ι X : Type*}
    (ξ : OffspringConfig ι X) (i : ι) : Prop := ∃ x, ξ i = some x

def offspringConfigPrefixOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : OffspringConfig ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → x ≤ y

def offspringConfigPresencePrefix {ι X : Type*} [LT ι]
    (ξ : OffspringConfig ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

theorem offspringConfig_present_of_later
    {ι X : Type*} [LT ι]
    (ξ : OffspringConfig ι X)
    (hprefix : offspringConfigPresencePrefix ξ)
    {i j : ι} (hij : i < j) (h : offspringConfigPresent ξ j) :
    offspringConfigPresent ξ i := by
  classical
  by_contra hi
  simp only [offspringConfigPresent, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simpa [hxi]
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hprefix i j hij hnone
  rw [hy] at hjnone
  cases hjnone

abbrev NatRealOffspringConfig := OffspringConfig ℕ ℝ

def optionChildPresent (ξ : NatRealOffspringConfig) (i : ℕ) : Prop :=
  offspringConfigPresent ξ i

def optionPrefixOrdered (ξ : NatRealOffspringConfig) : Prop :=
  offspringConfigPrefixOrdered ξ

def optionPresencePrefix (ξ : NatRealOffspringConfig) : Prop :=
  offspringConfigPresencePrefix ξ

def OrderedNatRealOffspring (ξ : NatRealOffspringConfig) : Prop :=
  optionPresencePrefix ξ ∧ optionPrefixOrdered ξ

noncomputable def optionChildAtomMeasure (ξ : NatRealOffspringConfig) (i : ℕ) :
    Measure ℝ := by
  classical
  exact match ξ i with
  | some x => Measure.dirac x
  | none => 0

noncomputable def optionOffspringPointMeasure (ξ : NatRealOffspringConfig) :
    Measure ℝ := Measure.sum (optionChildAtomMeasure ξ)

theorem optionChildAtomMeasure_apply (ξ : NatRealOffspringConfig) (i : ℕ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    optionChildAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  classical
  cases h : ξ i with
  | none => simp [optionChildAtomMeasure, h]
  | some x =>
      by_cases hx : x ∈ s <;>
        simp [optionChildAtomMeasure, h, Measure.dirac_apply' _ hs, hx]

theorem optionOffspringPointMeasure_apply (ξ : NatRealOffspringConfig)
    (s : Set ℝ) (hs : MeasurableSet s) :
    optionOffspringPointMeasure ξ s =
      ∑' i : ℕ, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [optionOffspringPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => optionChildAtomMeasure_apply ξ i s hs)

end ThesisSpeed
