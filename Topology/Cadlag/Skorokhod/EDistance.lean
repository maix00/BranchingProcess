import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Extended distance underlying the Skorokhod `J₁` topology

The definitions in this file do not install an `EMetricSpace` instance.  That
instance is available only after symmetry, separation, and the triangle
inequality have been proved.  This prevents downstream code from using an
unverified path-space topology.
-/

open scoped ENNReal

namespace Skorokhod

/-- Uniform extended distance between two paths with a common time domain. -/
noncomputable def uniformEDist {T E : Type*} [EMetricSpace E]
    (f g : T → E) : ℝ≥0∞ :=
  ⨆ t, edist (f t) (g t)

theorem edist_apply_le_uniformEDist {T E : Type*} [EMetricSpace E]
    (f g : T → E) (t : T) :
    edist (f t) (g t) ≤ uniformEDist f g :=
  le_iSup (fun s ↦ edist (f s) (g s)) t

@[simp]
theorem uniformEDist_self {T E : Type*} [EMetricSpace E] (f : T → E) :
    uniformEDist f f = 0 := by
  simp [uniformEDist]

theorem uniformEDist_comm {T E : Type*} [EMetricSpace E] (f g : T → E) :
    uniformEDist f g = uniformEDist g f := by
  simp only [uniformEDist, edist_comm]

theorem uniformEDist_comp_equiv {S T E : Type*} [EMetricSpace E]
    (f g : T → E) (e : S ≃ T) :
    uniformEDist (f ∘ e) (g ∘ e) = uniformEDist f g := by
  simpa only [uniformEDist, Function.comp_apply] using
    (e.iSup_comp (g := fun t : T ↦ edist (f t) (g t)))

theorem uniformEDist_triangle {T E : Type*} [EMetricSpace E] (f g h : T → E) :
    uniformEDist f h ≤ uniformEDist f g + uniformEDist g h := by
  refine iSup_le fun t ↦ ?_
  exact (edist_triangle (f t) (g t) (h t)).trans <|
    add_le_add (edist_apply_le_uniformEDist f g t)
      (edist_apply_le_uniformEDist g h t)

/-- The extended Skorokhod `J₁` cost associated with a specified time
change. -/
noncomputable def j1Cost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) (change : TimeChange) : ℝ≥0∞ :=
  max (ENNReal.ofReal change.distortion) (uniformEDist (change.act f) g)

theorem j1Cost_nonneg {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) (change : TimeChange) :
    0 ≤ j1Cost f g change :=
  bot_le

theorem uniformEDist_act_symm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) (change : TimeChange) :
    uniformEDist (change.act f) g =
      uniformEDist (change.symm.act g) f := by
  simp only [uniformEDist, TimeChange.act_apply]
  rw [← change.toHomeomorph.symm.toEquiv.iSup_comp]
  simp [TimeChange.symm, edist_comm]

theorem j1Cost_symm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) (change : TimeChange) :
    j1Cost f g change = j1Cost g f change.symm := by
  simp only [j1Cost, TimeChange.distortion_symm]
  rw [uniformEDist_act_symm]

/-- The extended distance formula underlying the Skorokhod `J₁` topology.

No `EMetricSpace` instance is installed at this point; its metric axioms are
proved separately. -/
noncomputable def j1EDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) : ℝ≥0∞ :=
  ⨅ change : TimeChange, j1Cost f g change

theorem j1EDist_le_cost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) (change : TimeChange) :
    j1EDist f g ≤ j1Cost f g change :=
  iInf_le _ change

theorem j1EDist_le_uniformEDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) :
    j1EDist f g ≤ uniformEDist f g := by
  refine (j1EDist_le_cost f g TimeChange.refl).trans_eq ?_
  simp [j1Cost]

theorem j1EDist_comm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath UnitInterval E) : j1EDist f g = j1EDist g f := by
  apply le_antisymm
  · refine le_iInf fun change ↦ ?_
    calc
      j1EDist f g ≤ j1Cost f g change.symm := j1EDist_le_cost f g change.symm
      _ = j1Cost g f change := by
        rw [j1Cost_symm, TimeChange.symm_symm]
  · refine le_iInf fun change ↦ ?_
    calc
      j1EDist g f ≤ j1Cost g f change.symm := j1EDist_le_cost g f change.symm
      _ = j1Cost f g change := by
        rw [j1Cost_symm, TimeChange.symm_symm]

@[simp]
theorem j1EDist_self {E : Type*} [EMetricSpace E]
    (f : CadlagPath UnitInterval E) : j1EDist f f = 0 := by
  apply le_antisymm
  · simpa using j1EDist_le_uniformEDist f f
  · exact bot_le

end Skorokhod
