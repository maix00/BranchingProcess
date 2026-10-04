/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Product law for fixed coordinate matching

A target field can take a coordinate from a source field when that target has
a matched preimage, and otherwise retain an independent fallback coordinate.
Both fields are represented by the two summands of one root-indexed product
field.  The resulting field again has the original product law whenever a
source coordinate is used at most once.

This is the deterministic cell used in the law of an adaptively matched
field.  It makes no countability assumption on roots or offspring slots.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The coordinate in a two-copy field used by a target coordinate.  A
matched target reads from the left (source) copy; an unmatched target reads
its own coordinate from the right (fallback) copy. -/
def RootIndexed.StepField.pasteCoordinate
    {Root α : Type*}
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (q : RootIndexed.TreeNode Root α) :
    (Root ⊕ Root) × TreeNode α :=
  match preimage q with
  | some p => (Sum.inl p.1, p.2)
  | none => (Sum.inr q.1, q.2)

/-- Paste matched source coordinates into an independent fallback field. -/
def RootIndexed.StepField.paste
    {Root α X : Type*}
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindexCoordinates
    (RootIndexed.StepField.pasteCoordinate preimage)

@[simp] theorem RootIndexed.StepField.paste_apply_some
    {Root α X : Type*}
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q p : RootIndexed.TreeNode Root α) (h : preimage q = some p) :
    RootIndexed.StepField.paste preimage field q.1 q.2 =
      field (Sum.inl p.1) p.2 := by
  simp [RootIndexed.StepField.paste,
    RootIndexed.StepField.pasteCoordinate, h]

@[simp] theorem RootIndexed.StepField.paste_apply_none
    {Root α X : Type*}
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.TreeNode Root α) (h : preimage q = none) :
    RootIndexed.StepField.paste preimage field q.1 q.2 =
      field (Sum.inr q.1) q.2 := by
  simp [RootIndexed.StepField.paste,
    RootIndexed.StepField.pasteCoordinate, h]

/-- The pasted coordinate map is injective precisely under the property
needed by matching: no source coordinate is assigned to two targets. -/
theorem RootIndexed.StepField.pasteCoordinate_injective
    {Root α : Type*}
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (hunique : ∀ q₁ q₂ p, preimage q₁ = some p →
      preimage q₂ = some p → q₁ = q₂) :
    Function.Injective
      (RootIndexed.StepField.pasteCoordinate preimage) := by
  intro q₁ q₂ h
  cases h₁ : preimage q₁ with
  | none =>
      cases h₂ : preimage q₂ with
      | none =>
          simp only [RootIndexed.StepField.pasteCoordinate, h₁, h₂,
            Sum.inr.injEq, Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2
      | some p₂ =>
          simp [RootIndexed.StepField.pasteCoordinate, h₁, h₂] at h
  | some p₁ =>
      cases h₂ : preimage q₂ with
      | none =>
          simp [RootIndexed.StepField.pasteCoordinate, h₁, h₂] at h
      | some p₂ =>
          have hp : p₁ = p₂ := by
            simp only [RootIndexed.StepField.pasteCoordinate, h₁, h₂,
              Sum.inl.injEq, Prod.mk.injEq] at h
            exact Prod.ext h.1 h.2
          subst p₂
          exact hunique q₁ q₂ p₁ h₁ h₂

/-- Pasting along a fixed matching preserves the complete root-indexed
product law.  The two input copies are supplied by the sum-root product
field, so source and fallback coordinates are independent by construction. -/
theorem RootIndexed.stepFieldLaw_paste
    {Root α X : Type*} [MeasurableSpace X]
    (mu : Measure (Step α X)) [IsProbabilityMeasure mu]
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (hunique : ∀ q₁ q₂ p, preimage q₁ = some p →
      preimage q₂ = some p → q₁ = q₂) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) mu).map
        (RootIndexed.StepField.paste preimage) =
      RootIndexed.stepFieldLaw (Root := Root) mu := by
  exact RootIndexed.stepFieldLaw_reindexCoordinates mu
    (RootIndexed.StepField.pasteCoordinate preimage)
    (RootIndexed.StepField.pasteCoordinate_injective preimage hunique)

end ProbabilityTheory.BranchingRandomWalk
