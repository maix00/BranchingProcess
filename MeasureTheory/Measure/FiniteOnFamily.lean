import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Bornology

/-!
# Finiteness of a measure on a family of sets

The single condition behind both the abstract point-process axiom and the
thesis's left-half-line hypothesis is: a measure is finite on every member of a
family `𝒜` of sets. There is one definition, `IsFiniteOnFamily`, and three
instances of the family:

* `compactFamily` recovers mathlib's `IsFiniteMeasureOnCompacts`, the standard
  locally-finite counting-measure axiom;
* `leftRayFamily` gives the paper's "locally finite on the left";
* `rightRayFamily` is its mirror image, obtained by the same definition.

Nothing in the definition is specific to an order, a topology, or the real
line. In particular the left and right versions are the *same* statement for
mirrored families, so no theorem has to be reproved for the right side. What
is genuinely asymmetric is only the direction of the enumeration chosen later,
not this finiteness condition.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

/-- A measure is finite on every member of a family of sets. -/
def IsFiniteOnFamily {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (𝒜 : Set (Set E)) : Prop :=
  ∀ s ∈ 𝒜, ν s ≠ ∞

theorem IsFiniteOnFamily.mono {E : Type*} [MeasurableSpace E]
    {ν : Measure E} {𝒜 ℬ : Set (Set E)}
    (h : IsFiniteOnFamily ν ℬ) (hsub : 𝒜 ⊆ ℬ) : IsFiniteOnFamily ν 𝒜 :=
  fun s hs => h s (hsub hs)

/-- A finite measure is finite on every family of sets. This is the measure
level form of the paper's derivation: a finite total mass forces finiteness on
each left ray. -/
theorem IsFiniteOnFamily.of_finiteMeasure {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] {𝒜 : Set (Set E)} :
    IsFiniteOnFamily ν 𝒜 :=
  fun s _ => ne_top_of_le_ne_top (measure_ne_top ν Set.univ) (measure_mono (Set.subset_univ s))

/-- The family of compact subsets. -/
def compactFamily (E : Type*) [TopologicalSpace E] : Set (Set E) :=
  {s | IsCompact s}

/-- The family of left rays `(-∞, a]`, written in mathlib's canonical spelling
`Set.range Set.Iic` (the spelling used by `isPiSystem_Iic` and
`borel_eq_generateFrom_Iic`). -/
def leftRayFamily (E : Type*) [Preorder E] : Set (Set E) :=
  Set.range (Set.Iic : E → Set E)

/-- The family of right rays `[a, ∞)`, the mirror family `Set.range Set.Ici`. -/
def rightRayFamily (E : Type*) [Preorder E] : Set (Set E) :=
  Set.range (Set.Ici : E → Set E)

/-- Finiteness on every left ray: the paper's "locally finite on the left". -/
abbrev IsLeftLocallyFinite {E : Type*} [MeasurableSpace E] [Preorder E]
    (ν : Measure E) : Prop :=
  IsFiniteOnFamily ν (leftRayFamily E)

/-- Finiteness on every right ray. It is the same condition with the order
reversed, which is why a dedicated left-only theory is not needed. -/
abbrev IsRightLocallyFinite {E : Type*} [MeasurableSpace E] [Preorder E]
    (ν : Measure E) : Prop :=
  IsFiniteOnFamily ν (rightRayFamily E)

/-- The unfolded form of left-ray finiteness: each ray alone is finite. -/
theorem IsLeftLocallyFinite.apply {E : Type*} [MeasurableSpace E] [Preorder E]
    {ν : Measure E} (h : IsLeftLocallyFinite ν) (a : E) : ν (Set.Iic a) ≠ ∞ :=
  h (Set.Iic a) ⟨a, rfl⟩

/-- The unfolded form of right-ray finiteness. -/
theorem IsRightLocallyFinite.apply {E : Type*} [MeasurableSpace E] [Preorder E]
    {ν : Measure E} (h : IsRightLocallyFinite ν) (a : E) : ν (Set.Ici a) ≠ ∞ :=
  h (Set.Ici a) ⟨a, rfl⟩

/-- Right rays are exactly left rays in the dual order, so the left/right
difference is purely the choice of orientation. -/
theorem mem_rightRayFamily_iff_orderDual (E : Type*) [Preorder E] (s : Set E) :
    s ∈ rightRayFamily E ↔ s ∈ leftRayFamily (OrderDual E) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨OrderDual.toDual a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨OrderDual.ofDual b, rfl⟩

/-- Left rays form a π-system. This is mathlib's `isPiSystem_Iic` transported
to the local name of the family. -/
theorem isPiSystem_leftRayFamily (E : Type*) [LinearOrder E] :
    IsPiSystem (leftRayFamily E) :=
  isPiSystem_Iic

/-- Right rays form a π-system, the mirror of `isPiSystem_leftRayFamily`. -/
theorem isPiSystem_rightRayFamily (E : Type*) [LinearOrder E] :
    IsPiSystem (rightRayFamily E) :=
  isPiSystem_Ici

/-- Finiteness on the compact family is exactly mathlib's
`IsFiniteMeasureOnCompacts`. -/
theorem isFiniteOnFamily_compactFamily_iff {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] (ν : Measure E) :
    IsFiniteOnFamily ν (compactFamily E) ↔ IsFiniteMeasureOnCompacts ν := by
  constructor
  · intro h
    exact ⟨fun K hK => lt_top_iff_ne_top.mpr (h K hK)⟩
  · intro h
    have h' := h
    exact fun K hK => hK.measure_ne_top

/-- A finite total mass gives finiteness on the left rays, mirroring the
paper's sufficient condition. -/
theorem isLeftLocallyFinite_of_finiteMeasure {ν : Measure ℝ} [IsFiniteMeasure ν] :
    IsLeftLocallyFinite ν :=
  IsFiniteOnFamily.of_finiteMeasure

/-- Left-ray finiteness implies compact finiteness on `ℝ`, because every
compact subset is bounded above: the left-ray condition is strictly stronger
than the point-process axiom. -/
theorem IsLeftLocallyFinite.isFiniteMeasureOnCompacts {ν : Measure ℝ}
    (hν : IsLeftLocallyFinite ν) : IsFiniteMeasureOnCompacts ν where
  lt_top_of_isCompact := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.bddAbove
    exact lt_of_le_of_lt (measure_mono fun _x hx => hR hx)
      (lt_top_iff_ne_top.mpr (hν (Set.Iic R) ⟨R, rfl⟩))

end MeasureTheory
