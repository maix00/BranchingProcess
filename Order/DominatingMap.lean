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
# Order-dominating maps between sets

The labels and their ordered observations are separate.  No finiteness,
countability, time, or branching assumption is built into this definition.

## Public declarations

- `Order.DominatingMap source target sourceValue targetValue` consists of an
  map `f` with `f '' source ⊆ target`, injective on `source`, and
  `targetValue (f a) ≤ sourceValue a` for every `a ∈ source`.
- `Order.DominatingMap.refl` gives the identity map, and `trans` composes two
  such maps while preserving their membership, injectivity, and order
  properties.
- `Order.DominatingMap.card_filter_le` bounds the number of source points
  below a value by the number of target points below that value whenever both
  domains are finite.
-/

@[expose] public section

namespace Order

variable {A B C Value : Type*}

/-- An injective map from `source` to `target` whose target observation is no
larger than the corresponding source observation. -/
structure DominatingMap [Preorder Value]
    (source : Set A) (target : Set B)
    (sourceValue : A → Value) (targetValue : B → Value) where
  toFun : A → B
  mapsTo : Set.MapsTo toFun source target
  injOn : Set.InjOn toFun source
  dominates : ∀ a ∈ source, targetValue (toFun a) ≤ sourceValue a

namespace DominatingMap

variable [Preorder Value]

instance (source : Set A) (target : Set B)
    (sourceValue : A → Value) (targetValue : B → Value) :
    CoeFun (DominatingMap source target sourceValue targetValue) (fun _ => A → B) :=
  ⟨DominatingMap.toFun⟩

def refl (source : Set A) (value : A → Value) :
    DominatingMap source source value value where
  toFun := id
  mapsTo := fun _ ha => ha
  injOn := fun _ _ _ _ h => h
  dominates := fun _ _ => le_rfl

def trans {source : Set A} {middle : Set B} {target : Set C}
    {sourceValue : A → Value} {middleValue : B → Value} {targetValue : C → Value}
    (f : DominatingMap source middle sourceValue middleValue)
    (g : DominatingMap middle target middleValue targetValue) :
    DominatingMap source target sourceValue targetValue where
  toFun := g ∘ f
  mapsTo := fun _ ha => g.mapsTo (f.mapsTo ha)
  injOn := by
    intro a ha a' ha' h
    exact f.injOn ha ha' (g.injOn (f.mapsTo ha) (f.mapsTo ha') h)
  dominates := fun a ha =>
    (g.dominates (f a) (f.mapsTo ha)).trans (f.dominates a ha)

/-- An order-dominating injection maps every finite lower level set of the
source into the corresponding lower level set of the target. -/
theorem card_filter_le [DecidableRel (· ≤ · : Value → Value → Prop)]
    {source : Set A} {target : Set B}
    {sourceValue : A → Value} {targetValue : B → Value}
    (f : DominatingMap source target sourceValue targetValue)
    (hsource : source.Finite) (htarget : target.Finite) (a : Value) :
    (hsource.toFinset.filter fun x => sourceValue x ≤ a).card ≤
      (htarget.toFinset.filter fun y => targetValue y ≤ a).card := by
  classical
  apply Finset.card_le_card_of_injOn f.toFun
  · intro x hx
    obtain ⟨hx, hxa⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨htarget.mem_toFinset.mpr
      (f.mapsTo (hsource.mem_toFinset.mp hx)), ?_⟩
    exact (f.dominates x (hsource.mem_toFinset.mp hx)).trans hxa
  · intro x hx y hy hxy
    exact f.injOn
      (hsource.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
      (hsource.mem_toFinset.mp (Finset.mem_filter.mp hy).1) hxy

end DominatingMap

end Order

end
