import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Topology.Cadlag.Skorokhod.Separation

/-!
# The Skorokhod emetric topology

The verified metric axioms for `j1EDist` define the Skorokhod `J₁` extended
metric topology on càdlàg paths.  The Borel measurable space below is generated
by this topology.
-/

namespace Skorokhod

noncomputable instance instEMetricSpaceCadlagPath
    {E : Type*} [MetricSpace E] :
    EMetricSpace (CadlagPath UnitInterval E) where
  edist := j1EDist
  edist_self := j1EDist_self
  edist_comm := j1EDist_comm
  edist_triangle := j1EDist_triangle
  eq_of_edist_eq_zero := j1EDist_eq_zero_imp

noncomputable instance instMetricSpaceCadlagPath
    {E : Type*} [MetricSpace E] :
    MetricSpace (CadlagPath UnitInterval E) :=
  EMetricSpace.toMetricSpace j1EDist_ne_top

@[simp]
theorem edist_cadlagPath_eq_j1EDist {E : Type*} [MetricSpace E]
    (f g : CadlagPath UnitInterval E) : edist f g = j1EDist f g :=
  rfl

noncomputable instance instMeasurableSpaceCadlagPath
    {E : Type*} [MetricSpace E] :
    MeasurableSpace (CadlagPath UnitInterval E) :=
  borel _

instance instBorelSpaceCadlagPath {E : Type*} [MetricSpace E] :
    BorelSpace (CadlagPath UnitInterval E) :=
  ⟨rfl⟩

end Skorokhod
