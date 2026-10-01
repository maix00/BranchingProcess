module

public import Topology.Cadlag.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Path sets for small deviations

These deterministic operations describe spatial scaling, a range tube, a
spatial corridor, an observation at one time, and agreement on a time
interval. They do not depend on a process law.
-/

@[expose] public section

namespace Skorokhod

open Set

/-- Spatial scaling of a càdlàg path. -/
def scalePath (scale : ℝ) (f : CadlagPath unitInterval ℝ) :
    CadlagPath unitInterval ℝ :=
  ⟨fun t => scale * f t, f.isCadlag_toFun.const_smul scale⟩

@[simp] theorem scalePath_apply (scale : ℝ)
    (f : CadlagPath unitInterval ℝ) (t : unitInterval) :
    scalePath scale f t = scale * f t := rfl

/-- Paths starting at zero whose range has diameter strictly less than
`2 * halfWidth`. -/
def rangeTubeStartingAtZero (halfWidth : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0} ∩ oscillationInOpenTube (2 * halfWidth)

/-- Paths starting at zero and lying uniformly inside a spatial corridor. -/
def corridorStartingAtZero (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0} ∩ rangeInOpenInterval lower upper

/-- Spatial scaling of a set of càdlàg paths. -/
def scaleSet (scale : ℝ) (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  scalePath scale '' G

/-- Restrict a path set by `lower < f(time) ≤ upper`, the endpoint
condition `Y_lower^upper(time) G` in the source. -/
def endpointWindow (time : unitInterval) (lower upper : ℝ)
    (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  G ∩ {f | f time ∈ Set.Ioc lower upper}

/-- All càdlàg paths agreeing on a closed time interval with some member of
`G`. Values outside that interval are unconstrained. -/
def segmentExtension (start finish : unitInterval)
    (G : Set (CadlagPath unitInterval ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ g ∈ G, ∀ t, start ≤ t → t ≤ finish → f t = g t}

@[simp]
theorem mem_scaleSet_iff {scale : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {f : CadlagPath unitInterval ℝ} :
    f ∈ scaleSet scale G ↔ ∃ g ∈ G, ∀ t, f t = scale * g t := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun _ => rfl⟩
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, hg, (CadlagPath.ext fun t => (hfg t).symm)⟩

@[simp]
theorem mem_endpointWindow_iff {time : unitInterval} {lower upper : ℝ}
    {G : Set (CadlagPath unitInterval ℝ)} {f : CadlagPath unitInterval ℝ} :
    f ∈ endpointWindow time lower upper G ↔
      f ∈ G ∧ lower < f time ∧ f time ≤ upper := Iff.rfl

/-- The strict endpoint event used for open-set support arguments is a
subset of the source's left-open, right-closed endpoint event. -/
theorem rangeInOpenIntervalEndsIn_subset_endpointWindow
    (lower upper endpointLower endpointUpper : ℝ) :
    rangeInOpenIntervalEndsIn lower upper endpointLower endpointUpper ⊆
      endpointWindow ⊤ endpointLower endpointUpper
        (rangeInOpenInterval lower upper) := by
  rintro f ⟨hpath, hendpoint⟩
  exact ⟨hpath, hendpoint.1, hendpoint.2.le⟩

theorem measurableSet_endpointWindow_top
    (lower upper : ℝ) {G : Set (CadlagPath unitInterval ℝ)}
    (hG : MeasurableSet G) :
    MeasurableSet (endpointWindow ⊤ lower upper G) := by
  exact hG.inter (MeasurableSet.preimage measurableSet_Ioc
    continuous_apply_top.measurable)

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
