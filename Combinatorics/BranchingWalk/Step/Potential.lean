import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Map

/-!
# Real-valued potentials on abstract child marks

A branching step may carry marks in an arbitrary measurable space `X`.
A measurable potential `φ : X → ℝ` supplies the scalar displacement used
for ordering, exponential weights, fronts, and speeds.  Mapping a step by
`φ` preserves the child slots and their absence, so multiplicities remain
visible even when distinct marks have the same potential.
-/

open MeasureTheory

namespace Combinatorics.Branching

structure Potential (X : Type*) [MeasurableSpace X] where
  toFun : X → ℝ
  measurable_toFun : Measurable toFun

instance {X : Type*} [MeasurableSpace X] : CoeFun (Potential X) (fun _ => X → ℝ) :=
  ⟨Potential.toFun⟩

/-- Slot order after projecting abstract marks to their real potentials. -/
def Step.IsOrderedBy {ι X : Type*} [LT ι] [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X) : Prop :=
  (ξ.map φ).IsOrdered

/-- The scalar optional displacement at a slot; absence remains explicit. -/
def Step.potentialAt? {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X) (i : ι) : Option ℝ :=
  (ξ i).map φ

theorem Step.potentialAt?_measurable {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (i : ι) :
    Measurable (fun ξ : Step ι X => ξ.potentialAt? φ i) :=
  (measurable_option_map φ.measurable_toFun).comp (measurable_pi_apply i)

/-- Zero-defaulted scalar potential.  Presence must still be checked when a
zero potential and an absent slot have to be distinguished. -/
def Step.potentialValue' {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X) (i : ι) : ℝ :=
  (ξ.potentialAt? φ i).getD 0

theorem Step.potentialValue'_measurable {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (i : ι) :
    Measurable (fun ξ : Step ι X => ξ.potentialValue' φ i) :=
  (measurable_optionGetD 0).comp (Step.potentialAt?_measurable φ i)

/-- Sum of projected edge marks along a finite lineage.  It needs no additive
structure on the original mark space. -/
def pathPotential {X : Type*} [MeasurableSpace X]
    (φ : Potential X) : List X → ℝ :=
  List.sum ∘ List.map φ

@[simp] theorem pathPotential_nil {X : Type*} [MeasurableSpace X]
    (φ : Potential X) : pathPotential φ [] = 0 := rfl

@[simp] theorem pathPotential_cons {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (x : X) (xs : List X) :
    pathPotential φ (x :: xs) = φ x + pathPotential φ xs := by
  simp [pathPotential]

/-- The original real-valued model is the identity-potential specialization. -/
def realPotential : Potential ℝ where
  toFun := id
  measurable_toFun := measurable_id

@[simp] theorem realPotential_apply (x : ℝ) : realPotential x = x := rfl

/-- A measurable additive potential for displacement marks.  This is the
structure used when path positions are first added in `X` and then projected
to the real line. -/
structure AdditivePotential (X : Type*) [MeasurableSpace X]
    [AddMonoid X] where
  toAddMonoidHom : X →+ ℝ
  measurable_toFun : Measurable toAddMonoidHom

instance {X : Type*} [MeasurableSpace X] [AddMonoid X] :
    CoeFun (AdditivePotential X) (fun _ => X → ℝ) :=
  ⟨fun φ => φ.toAddMonoidHom⟩

def AdditivePotential.toPotential {X : Type*} [MeasurableSpace X]
    [AddMonoid X] (φ : AdditivePotential X) : Potential X where
  toFun := φ
  measurable_toFun := φ.measurable_toFun

@[simp] theorem AdditivePotential.toPotential_apply
    {X : Type*} [MeasurableSpace X] [AddMonoid X]
    (φ : AdditivePotential X) (x : X) : φ.toPotential x = φ x := rfl

@[simp] theorem AdditivePotential.map_zero {X : Type*} [MeasurableSpace X]
    [AddMonoid X] (φ : AdditivePotential X) : φ 0 = 0 :=
  φ.toAddMonoidHom.map_zero

@[simp] theorem AdditivePotential.map_add {X : Type*} [MeasurableSpace X]
    [AddMonoid X] (φ : AdditivePotential X) (x y : X) :
    φ (x + y) = φ x + φ y :=
  φ.toAddMonoidHom.map_add x y

/-- Additivity makes the two path conventions coincide. -/
theorem AdditivePotential.map_list_sum {X : Type*} [MeasurableSpace X]
    [AddMonoid X] (φ : AdditivePotential X) (xs : List X) :
    φ xs.sum = pathPotential φ.toPotential xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Identity projection for the one-dimensional displacement model. -/
def realAdditivePotential : AdditivePotential ℝ where
  toAddMonoidHom := AddMonoidHom.id ℝ
  measurable_toFun := measurable_id

@[simp] theorem realAdditivePotential_apply (x : ℝ) :
    realAdditivePotential x = x := rfl

end Combinatorics.Branching
