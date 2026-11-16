/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Basic

/-!
# Order-dominating maps between finite populations

The labels and their ordered observations are separate. No finiteness,
countability, time, or branching assumption is built into this definition.

## Public declarations

- `Order.DominatingMap objectsToMatch availablePartners objectOrderKey
  partnerOrderKey` consists of an injection from `objectsToMatch` into
  `availablePartners`, with `partnerOrderKey (f a) ≤ objectOrderKey a`.
- `Order.DominatingMap.refl` gives the identity map, and `trans` composes two
  such maps while preserving their membership, injectivity, and order
  properties.
- `Order.DominatingMap.card_filter_le` bounds the number of objects whose
  order key is below a value by the number of available partners whose key is
  below that value whenever both sets are finite.

Concretely, `f : DominatingMap P Q κ₁ κ₂` packages
\[
  f(P)\subseteq Q,\qquad \operatorname{InjOn}(f,P),\qquad
  \kappa_2(f(a))\le\kappa_1(a)\quad(a\in P).
\]
For finite `P` and `Q`, the induced cardinality comparison is
\[
  \#\{a\in P:\kappa_1(a)\le r\}
    \le \#\{b\in Q:\kappa_2(b)\le r\}\quad(r\in\mathrm{Value}).
\]
-/

@[expose] public section

namespace Order

variable {A B C Value : Type*}

/-- An injective map from `objectsToMatch` to `availablePartners` whose
partner order key is no larger than the corresponding object order key. -/
structure DominatingMap [Preorder Value]
    (objectsToMatch : Set A) (availablePartners : Set B)
    (objectOrderKey : A → Value) (partnerOrderKey : B → Value) where
  toFun : A → B
  mapsTo : Set.MapsTo toFun objectsToMatch availablePartners
  injOn : Set.InjOn toFun objectsToMatch
  dominates : ∀ a ∈ objectsToMatch,
    partnerOrderKey (toFun a) ≤ objectOrderKey a

namespace DominatingMap

variable [Preorder Value]

instance (objectsToMatch : Set A) (availablePartners : Set B)
    (objectOrderKey : A → Value) (partnerOrderKey : B → Value) :
    CoeFun (DominatingMap objectsToMatch availablePartners
      objectOrderKey partnerOrderKey) (fun _ => A → B) :=
  ⟨DominatingMap.toFun⟩

def refl (objectsToMatch : Set A) (orderKey : A → Value) :
    DominatingMap objectsToMatch objectsToMatch orderKey orderKey where
  toFun := id
  mapsTo := fun _ ha => ha
  injOn := fun _ _ _ _ h => h
  dominates := fun _ _ => le_rfl

def trans {objectsToMatch : Set A} {middlePartners : Set B}
    {availablePartners : Set C}
    {objectOrderKey : A → Value} {middleOrderKey : B → Value}
    {partnerOrderKey : C → Value}
    (f : DominatingMap objectsToMatch middlePartners
      objectOrderKey middleOrderKey)
    (g : DominatingMap middlePartners availablePartners
      middleOrderKey partnerOrderKey) :
    DominatingMap objectsToMatch availablePartners
      objectOrderKey partnerOrderKey where
  toFun := g ∘ f
  mapsTo := fun _ ha => g.mapsTo (f.mapsTo ha)
  injOn := by
    intro a ha a' ha' h
    exact f.injOn ha ha' (g.injOn (f.mapsTo ha) (f.mapsTo ha') h)
  dominates := fun a ha =>
    (g.dominates (f a) (f.mapsTo ha)).trans (f.dominates a ha)

/-- An order-dominating injection maps every finite lower level set of
`objectsToMatch` into the corresponding lower level set of `availablePartners`.
-/
theorem card_filter_le [DecidableRel (· ≤ · : Value → Value → Prop)]
    {objectsToMatch : Set A} {availablePartners : Set B}
    {objectOrderKey : A → Value} {partnerOrderKey : B → Value}
    (f : DominatingMap objectsToMatch availablePartners
      objectOrderKey partnerOrderKey)
    (hobjectsToMatchFinite : objectsToMatch.Finite)
    (havailablePartnersFinite : availablePartners.Finite) (a : Value) :
    (hobjectsToMatchFinite.toFinset.filter fun x => objectOrderKey x ≤ a).card ≤
      (havailablePartnersFinite.toFinset.filter fun y => partnerOrderKey y ≤ a).card := by
  classical
  apply Finset.card_le_card_of_injOn f.toFun
  · intro x hx
    obtain ⟨hx, hxa⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨havailablePartnersFinite.mem_toFinset.mpr
      (f.mapsTo (hobjectsToMatchFinite.mem_toFinset.mp hx)), ?_⟩
    exact (f.dominates x (hobjectsToMatchFinite.mem_toFinset.mp hx)).trans hxa
  · intro x hx y hy hxy
    exact f.injOn
      (hobjectsToMatchFinite.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
      (hobjectsToMatchFinite.mem_toFinset.mp (Finset.mem_filter.mp hy).1) hxy

end DominatingMap

end Order

end
