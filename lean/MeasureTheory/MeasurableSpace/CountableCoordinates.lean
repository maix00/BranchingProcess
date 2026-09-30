module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurable functionals determined by coordinates

A path functional that factors through a measurable coordinate restriction is
measurable. The index set need not be countable for this elementary statement;
countability matters when constructing the measurable factor from coordinate
conditions.
-/

@[expose] public section

namespace MeasureTheory

/-- A functional is determined by its values on a chosen set of coordinates. -/
def DeterminedBy {T E Y : Type*} (D : Set T)
    (F : (T → E) → Y) : Prop :=
  ∀ f g, (∀ t ∈ D, f t = g t) → F f = F g

/-- A measurable representation of a functional through selected coordinates. -/
def HasMeasurableCoordinateRepresentation
    {T E Y : Type*} [MeasurableSpace E] [MeasurableSpace Y]
    (D : Set T) (F : (T → E) → Y) : Prop :=
  ∃ G : (D → E) → Y, Measurable G ∧
    ∀ f, F f = G (fun t => f t)

theorem HasMeasurableCoordinateRepresentation.determinedBy
    {T E Y : Type*} [MeasurableSpace E] [MeasurableSpace Y]
    {D : Set T} {F : (T → E) → Y}
    (h : HasMeasurableCoordinateRepresentation D F) :
    DeterminedBy D F := by
  obtain ⟨G, _, hG⟩ := h
  intro f g hfg
  rw [hG f, hG g]
  congr 1
  funext t
  exact hfg t t.property

theorem HasMeasurableCoordinateRepresentation.measurable
    {T E Y : Type*} [MeasurableSpace E] [MeasurableSpace Y]
    {D : Set T} {F : (T → E) → Y}
    (h : HasMeasurableCoordinateRepresentation D F) :
    Measurable F := by
  obtain ⟨G, hG, hfactor⟩ := h
  have hrestrict : Measurable (fun f : T → E => fun t : D => f t) :=
    Measurable.of_eval fun t : D => (measurable_pi_apply (t : T))
  have hcomp := hG.comp hrestrict
  convert hcomp using 1
  funext f
  exact hfactor f

end MeasureTheory

end
