module

public import Topology.Cadlag.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Path sets for small deviations

These deterministic operations describe spatial scaling, a range tube, a
spatial corridor, an observation at one time, and agreement on a time
interval. They do not depend on a process law.
-/

@[expose] public section

namespace Skorokhod

open Set

/-- Paths starting at zero whose range has diameter strictly less than
`2 * halfWidth`. -/
def rangeTubeStartingAtZero (halfWidth : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0} ∩ oscillationInOpenTube (2 * halfWidth)

/-- Paths starting at zero and lying uniformly inside a spatial corridor. -/
def corridorStartingAtZero (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0} ∩ rangeInOpenInterval lower upper

/-- Spatial scaling of a set of càdlàg paths, expressed by pointwise
equality so it does not require a scalar-action instance on path space. -/
def scaleSet (scale : ℝ) (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ g ∈ G, ∀ t, f t = scale * g t}

/-- Restrict a path set by the path value at a specified time. -/
def endpointWindow (time : unitInterval) (lower upper : ℝ)
    (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  G ∩ {f | f time ∈ Set.Ioo lower upper}

/-- All càdlàg paths agreeing on a closed time interval with some member of
`G`. Values outside that interval are unconstrained. -/
def segmentExtension (start finish : unitInterval)
    (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ g ∈ G, ∀ t, start ≤ t → t ≤ finish → f t = g t}

@[simp]
theorem mem_scaleSet_iff {scale : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {f : CadlagPath unitInterval ℝ} :
    f ∈ scaleSet scale G ↔ ∃ g ∈ G, ∀ t, f t = scale * g t := Iff.rfl

@[simp]
theorem mem_endpointWindow_iff {time : unitInterval} {lower upper : ℝ}
    {G : Set (CadlagPath unitInterval ℝ)} {f : CadlagPath unitInterval ℝ} :
    f ∈ endpointWindow time lower upper G ↔
      f ∈ G ∧ lower < f time ∧ f time < upper := Iff.rfl

@[simp]
theorem mem_segmentExtension_iff {start finish : unitInterval}
    {G : Set (CadlagPath unitInterval ℝ)} {f : CadlagPath unitInterval ℝ} :
    f ∈ segmentExtension start finish G ↔
      ∃ g ∈ G, ∀ t, start ≤ t → t ≤ finish → f t = g t := Iff.rfl

theorem measurableSet_rangeTubeStartingAtZero (halfWidth : ℝ) :
    MeasurableSet (rangeTubeStartingAtZero halfWidth) :=
  (measurableSet_singleton 0).preimage continuous_apply_bot.measurable |>.inter
    (measurableSet_oscillationInOpenTube (2 * halfWidth))

theorem measurableSet_corridorStartingAtZero (lower upper : ℝ) :
    MeasurableSet (corridorStartingAtZero lower upper) :=
  (measurableSet_singleton 0).preimage continuous_apply_bot.measurable |>.inter
    (measurableSet_rangeInOpenInterval lower upper)

/-- The centered corridor is contained in the range tube of the same
half-width. This is the event inclusion used on the left of Lemma 2(b). -/
theorem centeredCorridor_subset_rangeTube (halfWidth : ℝ) :
    corridorStartingAtZero (-halfWidth) halfWidth ⊆
      rangeTubeStartingAtZero halfWidth := by
  intro f hf
  rcases hf with ⟨hzero, margin, hmargin, hrange⟩
  refine ⟨hzero, margin, hmargin, ?_⟩
  intro s t
  have hs := hrange s
  have ht := hrange t
  have hsub : -(2 * halfWidth - 2 * margin) ≤ f s - f t ∧
      f s - f t ≤ 2 * halfWidth - 2 * margin := by
    constructor <;> linarith
  have habs : |f s - f t| ≤ 2 * halfWidth - 2 * margin :=
    abs_le.mpr hsub
  linarith

end Skorokhod

end
