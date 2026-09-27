import Mathlib.Data.Set.Basic

/-!
# Order-dominating maps between labelled sets

The labels and their ordered observations are separate.  No finiteness,
countability, time, or branching assumption is built into this definition.
-/

namespace Combinatorics

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

end DominatingMap

end Combinatorics
