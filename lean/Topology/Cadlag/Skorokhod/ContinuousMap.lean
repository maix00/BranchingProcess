import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.Topology

/-!
# Continuous paths inside Skorokhod space

Continuous paths embed continuously into the Skorokhod `J₁` space.  The
identity time change bounds the `J₁` distance by the uniform distance.
-/

open Filter
open scoped ENNReal Topology

namespace Skorokhod

/-- Regard a continuous path as a càdlàg path. -/
def ofContinuousMap {E : Type*} [MetricSpace E]
    (f : C(unitInterval, E)) : CadlagPath unitInterval E :=
  ⟨f, f.continuous.isCadlag⟩

@[simp]
theorem ofContinuousMap_apply {E : Type*} [MetricSpace E]
    (f : C(unitInterval, E)) (t : unitInterval) :
    ofContinuousMap f t = f t := rfl

theorem edist_ofContinuousMap_le {E : Type*} [MetricSpace E]
    (f g : C(unitInterval, E)) :
    edist (ofContinuousMap f) (ofContinuousMap g) ≤ edist f g := by
  rw [edist_cadlagPath_eq_j1EDist]
  refine (j1EDist_le_uniformEDist _ _).trans_eq ?_
  rw [ContinuousMap.edist_eq_iSup]
  rfl

theorem continuous_ofContinuousMap {E : Type*} [MetricSpace E] :
    Continuous (ofContinuousMap : C(unitInterval, E) →
      CadlagPath unitInterval E) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hupper : Tendsto (fun g : C(unitInterval, E) ↦ edist g f)
      (nhds f) (nhds 0) :=
    tendsto_iff_edist_tendsto_0.1 continuousAt_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ ↦ bot_le
  · exact Eventually.of_forall fun g ↦ edist_ofContinuousMap_le g f

theorem measurable_ofContinuousMap {E : Type*} [MetricSpace E]
    [SecondCountableTopology E] :
    Measurable (ofContinuousMap : C(unitInterval, E) →
      CadlagPath unitInterval E) :=
  continuous_ofContinuousMap.measurable

end Skorokhod
