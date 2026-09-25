import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Count

/-!
# Abstract offspring point processes

The mathematical input is a measurable random counting measure on `ℝ`,
locally finite on every left half-line. In particular the zero measure is
allowed. Countable slot marks are a later measurable representation used to
attach independent copies to an Ulam--Harris tree.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed

/-- A measure takes values in `ℕ ∪ {∞}` on measurable sets. -/
def IsCountingMeasure (ν : Measure ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s →
    ν s = ∞ ∨ ∃ n : ℕ, ν s = n

/-- The local finiteness relevant for ordering offspring from the left. -/
def IsLeftLocallyFinite (ν : Measure ℝ) : Prop :=
  ∀ R : ℝ, ν (Set.Iic R) ≠ ∞

/-- A point process is a measurable random measure together with the
counting and left-local-finiteness properties used in the thesis. -/
structure OffspringPointProcess (Ω : Type*) [MeasurableSpace Ω] where
  toMeasure : Ω → Measure ℝ
  measurable_toMeasure : Measurable toMeasure
  counting : ∀ ω, IsCountingMeasure (toMeasure ω)
  leftLocallyFinite : ∀ ω, IsLeftLocallyFinite (toMeasure ω)

instance {Ω : Type*} [MeasurableSpace Ω] :
    CoeFun (OffspringPointProcess Ω) (fun _ => Ω → Measure ℝ) :=
  ⟨OffspringPointProcess.toMeasure⟩

/-- The empty offspring point process is valid at the foundational level. -/
def emptyOffspringPointProcess (Ω : Type*) [MeasurableSpace Ω] :
    OffspringPointProcess Ω where
  toMeasure := fun _ => 0
  measurable_toMeasure := measurable_const
  counting := by
    intro ω s hs
    right
    exact ⟨0, by simp⟩
  leftLocallyFinite := by simp [IsLeftLocallyFinite]

end ThesisSpeed
