/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

/-!
# Product law for fixed coordinate matching

A partner field can take a coordinate from an object field when that partner
has a matched object preimage, and otherwise retain an independent fallback
coordinate.  Both fields are represented by the two summands of one
root-indexed product field.  The resulting field again has the original
product law whenever each matched object coordinate is used at most once.

This is the deterministic cell used in the law of an adaptively matched
field.  It makes no countability assumption on roots or offspring slots.

## Public declarations

The fixed paste reads a matched object coordinate and uses the partner's
fallback coordinate when no match exists; injective matching preserves the
root-indexed product law.

Here `q` indexes a partner coordinate, and `p(q)` is its optional object
preimage.

\[\begin{aligned}
\operatorname{paste}(p,F)(q)
&=\begin{cases}
F(\operatorname{inl}(r),u),&p(q)=\operatorname{some}(r,u),\\
F(\operatorname{inr}(q.1),q.2),&p(q)=\operatorname{none},
\end{cases}\\
\operatorname{paste}(p)_{\#}\,
\operatorname{stepFieldLaw}_{R\oplus R}^{\mu}
&=\operatorname{stepFieldLaw}_{R}^{\mu}.
\end{aligned}\]

* `RootIndexed.StepField.pasteCoordinate` reads a partner coordinate from the
  object summand when its guarded object preimage exists and otherwise from the
  fallback summand.
* `RootIndexed.StepField.paste` applies that coordinate rule to the complete
  root-indexed field.
* `RootIndexed.StepField.pasteCoordinate_injective` proves injectivity of
  the two-copy coordinate map when each object coordinate is used at most
  once.
* `RootIndexed.stepFieldLaw_paste` states that this fixed injective paste
  preserves the root-indexed product law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The coordinate in a two-copy field used by a partner coordinate.  A
matched partner reads from the left (object) copy; an unmatched partner reads
its own coordinate from the right (fallback) copy. -/
def RootIndexed.StepField.pasteCoordinate
    {Root α : Type*}
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (q : RootIndexed.TreeNode Root α) :
    (Root ⊕ Root) × TreeNode α :=
  match objectPreimageAtPartner q with
  | some p => (Sum.inl p.1, p.2)
  | none => (Sum.inr q.1, q.2)

/-- Paste matched object coordinates into an independent fallback field. -/
def RootIndexed.StepField.paste
    {Root α X : Type*}
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindexCoordinates
    (RootIndexed.StepField.pasteCoordinate objectPreimageAtPartner)

@[simp] theorem RootIndexed.StepField.paste_apply_some
    {Root α X : Type*}
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (partner object : RootIndexed.TreeNode Root α)
    (h : objectPreimageAtPartner partner = some object) :
    RootIndexed.StepField.paste objectPreimageAtPartner field
      partner.1 partner.2 = field (Sum.inl object.1) object.2 := by
  simp [RootIndexed.StepField.paste,
    RootIndexed.StepField.pasteCoordinate, h]

@[simp] theorem RootIndexed.StepField.paste_apply_none
    {Root α X : Type*}
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (partner : RootIndexed.TreeNode Root α)
    (h : objectPreimageAtPartner partner = none) :
    RootIndexed.StepField.paste objectPreimageAtPartner field
      partner.1 partner.2 = field (Sum.inr partner.1) partner.2 := by
  simp [RootIndexed.StepField.paste,
    RootIndexed.StepField.pasteCoordinate, h]

/-- The pasted coordinate map is injective when each object coordinate is
assigned to at most one partner coordinate. -/
theorem RootIndexed.StepField.pasteCoordinate_injective
    {Root α : Type*}
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (hobjectPreimage_uniquePartner : ∀ partner₁ partner₂ object,
      objectPreimageAtPartner partner₁ = some object →
      objectPreimageAtPartner partner₂ = some object → partner₁ = partner₂) :
    Function.Injective
      (RootIndexed.StepField.pasteCoordinate objectPreimageAtPartner) := by
  intro partner₁ partner₂ h
  cases h₁ : objectPreimageAtPartner partner₁ with
  | none =>
      cases h₂ : objectPreimageAtPartner partner₂ with
      | none =>
          simp only [RootIndexed.StepField.pasteCoordinate, h₁, h₂,
            Sum.inr.injEq, Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2
      | some p₂ =>
          simp [RootIndexed.StepField.pasteCoordinate, h₁, h₂] at h
  | some p₁ =>
      cases h₂ : objectPreimageAtPartner partner₂ with
      | none =>
          simp [RootIndexed.StepField.pasteCoordinate, h₁, h₂] at h
      | some p₂ =>
          have hp : p₁ = p₂ := by
            simp only [RootIndexed.StepField.pasteCoordinate, h₁, h₂,
              Sum.inl.injEq, Prod.mk.injEq] at h
            exact Prod.ext h.1 h.2
          subst p₂
          exact hobjectPreimage_uniquePartner partner₁ partner₂ p₁ h₁ h₂

/-- Pasting along a fixed matching preserves the complete root-indexed
product law.  The two input copies are supplied by the sum-root product
field, so object and fallback coordinates are independent by construction. -/
theorem RootIndexed.stepFieldLaw_paste
    {Root α X : Type*} [MeasurableSpace X]
    (mu : Measure (Step α X)) [IsProbabilityMeasure mu]
    (objectPreimageAtPartner : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α))
    (hobjectPreimage_uniquePartner : ∀ partner₁ partner₂ object,
      objectPreimageAtPartner partner₁ = some object →
      objectPreimageAtPartner partner₂ = some object → partner₁ = partner₂) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) mu).map
        (RootIndexed.StepField.paste objectPreimageAtPartner) =
      RootIndexed.stepFieldLaw (Root := Root) mu := by
  exact RootIndexed.stepFieldLaw_reindexCoordinates mu
    (RootIndexed.StepField.pasteCoordinate objectPreimageAtPartner)
    (RootIndexed.StepField.pasteCoordinate_injective objectPreimageAtPartner
      hobjectPreimage_uniquePartner)

end ProbabilityTheory.BranchingRandomWalk
