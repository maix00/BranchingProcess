module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.TimeChange

@[expose] public section

/-!
# Extended distance underlying the Skorokhod `J₁` topology

The definitions in this file do not install a topology.  After the
pseudo-emetric axioms are proved, `Skorokhod.Topology` installs the associated
pseudo-emetric topology.  A genuine `EMetricSpace` instance additionally
requires the separate càdlàg separation theorem.
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

theorem uniformEDist_ne_top {E : Type*} [MetricSpace E]
    (f g : CadlagPath unitInterval E) : uniformEDist f g ≠ ∞ := by
  have hbf : Bornology.IsBounded (Set.range f) := by
    simpa only [Set.image_univ] using
      isBounded_image_of_isCadlag_of_isCompact f.isCadlag_toFun
        (isCompact_univ : IsCompact (Set.univ : Set unitInterval))
  have hbg : Bornology.IsBounded (Set.range g) := by
    simpa only [Set.image_univ] using
      isBounded_image_of_isCadlag_of_isCompact g.isCadlag_toFun
        (isCompact_univ : IsCompact (Set.univ : Set unitInterval))
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hbf.union hbg)
  have hle : uniformEDist f g ≤ ENNReal.ofReal C := by
    refine iSup_le fun t ↦ ?_
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal <| hC
      (Set.mem_union_left _ ⟨t, rfl⟩) (Set.mem_union_right _ ⟨t, rfl⟩)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

theorem uniformEDist_act {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    uniformEDist (change.act f) (change.act g) = uniformEDist f g := by
  simp only [uniformEDist, TimeChange.act_apply]
  exact change.toHomeomorph.toEquiv.iSup_comp
    (g := fun t : unitInterval ↦ edist (f t) (g t))

theorem uniformEDist_trans_act_le {E : Type*} [EMetricSpace E]
    (f g h : CadlagPath unitInterval E) (first second : TimeChange) :
    uniformEDist ((first.trans second).act f) h ≤
      uniformEDist (second.act f) g + uniformEDist (first.act g) h := by
  calc
    uniformEDist ((first.trans second).act f) h =
        uniformEDist (first.act (second.act f)) h := by
          rw [TimeChange.trans_act]
    _ ≤ uniformEDist (first.act (second.act f)) (first.act g) +
        uniformEDist (first.act g) h := uniformEDist_triangle _ _ _
    _ = uniformEDist (second.act f) g + uniformEDist (first.act g) h := by
      rw [uniformEDist_act]

/-- The extended Skorokhod `J₁` cost associated with a specified time
change. -/
noncomputable def j1Cost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) : ℝ≥0∞ :=
  max (ENNReal.ofReal change.distortion) (uniformEDist (change.act f) g)

theorem j1Cost_nonneg {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    0 ≤ j1Cost f g change :=
  bot_le

theorem uniformEDist_act_symm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    uniformEDist (change.act f) g =
      uniformEDist (change.symm.act g) f := by
  simp only [uniformEDist, TimeChange.act_apply]
  rw [← change.toHomeomorph.symm.toEquiv.iSup_comp]
  simp [TimeChange.symm, edist_comm]

theorem j1Cost_symm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    j1Cost f g change = j1Cost g f change.symm := by
  simp only [j1Cost, TimeChange.distortion_symm]
  rw [uniformEDist_act_symm]

theorem j1Cost_trans_le {E : Type*} [EMetricSpace E]
    (f g h : CadlagPath unitInterval E) (first second : TimeChange) :
    j1Cost f h (first.trans second) ≤
      j1Cost f g second + j1Cost g h first := by
  apply max_le
  · calc
      ENNReal.ofReal (first.trans second).distortion ≤
          ENNReal.ofReal (first.distortion + second.distortion) :=
        ENNReal.ofReal_le_ofReal (TimeChange.distortion_trans_le first second)
      _ = ENNReal.ofReal first.distortion + ENNReal.ofReal second.distortion := by
        rw [ENNReal.ofReal_add first.distortion_nonneg second.distortion_nonneg]
      _ = ENNReal.ofReal second.distortion + ENNReal.ofReal first.distortion :=
        add_comm _ _
      _ ≤ j1Cost f g second + j1Cost g h first :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact (uniformEDist_trans_act_le f g h first second).trans <|
      add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The extended distance formula underlying the Skorokhod `J₁` topology.

Its pseudo-emetric axioms are proved below. -/
noncomputable def j1EDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) : ℝ≥0∞ :=
  ⨅ change : TimeChange, j1Cost f g change

theorem j1EDist_le_cost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    j1EDist f g ≤ j1Cost f g change :=
  iInf_le _ change

theorem j1EDist_le_uniformEDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) :
    j1EDist f g ≤ uniformEDist f g := by
  refine (j1EDist_le_cost f g TimeChange.refl).trans_eq ?_
  simp [j1Cost]

theorem j1EDist_ne_top {E : Type*} [MetricSpace E]
    (f g : CadlagPath unitInterval E) : j1EDist f g ≠ ∞ :=
  ne_top_of_le_ne_top (uniformEDist_ne_top f g)
    (j1EDist_le_uniformEDist f g)

theorem j1EDist_comm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) : j1EDist f g = j1EDist g f := by
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

theorem j1EDist_triangle {E : Type*} [EMetricSpace E]
    (f g h : CadlagPath unitInterval E) :
    j1EDist f h ≤ j1EDist f g + j1EDist g h := by
  calc
    j1EDist f h ≤
        ⨅ second : TimeChange, ⨅ first : TimeChange,
          j1Cost f g second + j1Cost g h first := by
      refine le_iInf fun second ↦ le_iInf fun first ↦ ?_
      exact (j1EDist_le_cost f h (first.trans second)).trans
        (j1Cost_trans_le f g h first second)
    _ = (⨅ second : TimeChange, j1Cost f g second) +
        ⨅ first : TimeChange, j1Cost g h first := by
      simp_rw [← ENNReal.add_iInf]
      rw [← ENNReal.iInf_add]
    _ = j1EDist f g + j1EDist g h := rfl

@[simp]
theorem j1EDist_self {E : Type*} [EMetricSpace E]
    (f : CadlagPath unitInterval E) : j1EDist f f = 0 := by
  apply le_antisymm
  · simpa using j1EDist_le_uniformEDist f f
  · exact bot_le

end Skorokhod
