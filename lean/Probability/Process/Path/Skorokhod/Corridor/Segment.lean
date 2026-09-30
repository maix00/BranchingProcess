module

public import Probability.Process.Path.Skorokhod.RationalTime
public import Topology.Cadlag.Skorokhod.Corridor.Dense
public import Probability.Process.Path.UnitInterval

/-!
# Full-path corridor events on a time segment

The statement of a corridor event quantifies over the complete càdlàg
segment. A countable-coordinate description is used only to establish its
measurability and independence consequences.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- A segment of a process, translated to start at zero. -/
def segmentIncrement {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (ω : Ω) (t : unitInterval) : ℝ :=
  X (start + length * unitIntervalToNNReal t) ω - X start ω

/-- The complete segment remains a positive uniform distance inside a
spatial corridor. -/
def fullSegmentCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) : Set Ω :=
  {ω | ∃ margin > 0, ∀ t : unitInterval,
    lower + margin ≤ segmentIncrement X start length ω t ∧
      segmentIncrement X start length ω t ≤ upper - margin}

/-- A complete-segment corridor constrains its terminal increment to the
corresponding closed interval. -/
theorem fullSegmentCorridorEvent_subset_endpoint_Icc
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) :
    fullSegmentCorridorEvent X start length lower upper ⊆
      {ω | segmentIncrement X start length ω ⊤ ∈ Set.Icc lower upper} := by
  rintro ω ⟨margin, hmargin, hpath⟩
  have hend := hpath ⊤
  exact ⟨by linarith, by linarith⟩

/-- The endpoint-constrained complete segment corridor. -/
def fullSegmentCorridorReturnEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) : Set Ω :=
  fullSegmentCorridorEvent X start length lower upper ∩
    {ω | segmentIncrement X start length ω ⊤ ∈
      Set.Ioo coreLower coreUpper}

/-- Enlarging the spatial corridor and endpoint window preserves a
complete-path entrance event. -/
theorem fullSegmentCorridorReturnEvent_mono_bounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    fullSegmentCorridorReturnEvent X start length
        lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      fullSegmentCorridorReturnEvent X start length
        lower₂ upper₂ coreLower₂ coreUpper₂ := by
  rintro ω ⟨⟨margin, hmargin, hpath⟩, hend⟩
  refine ⟨⟨margin, hmargin, ?_⟩, ?_⟩
  · intro t
    obtain ⟨hlo, hhi⟩ := hpath t
    exact ⟨by linarith, by linarith⟩
  · exact ⟨lt_of_le_of_lt hcoreLower hend.1,
      lt_of_lt_of_le hend.2 hcoreUpper⟩

theorem isCadlag_segmentIncrement {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    IsCadlag (segmentIncrement X start length ω) := by
  let clock : unitInterval → ℝ≥0 :=
    fun t => start + length * unitIntervalToNNReal t
  have hclockMono : Monotone clock := by
    intro s t hst
    have hst' : unitIntervalToNNReal s ≤ unitIntervalToNNReal t := by
      exact hst
    simpa [clock, add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left hst' length.property) start
  have hclockCont : Continuous clock := by
    dsimp [clock]
    exact continuous_const.add
      (continuous_const.mul continuous_unitIntervalToNNReal)
  have hcomp := hω.comp_monotone_continuous hclockMono hclockCont
  have htranslated : IsCadlag (fun t : unitInterval =>
      X (clock t) ω - X start ω) :=
    hcomp.continuous_comp (g := fun x : ℝ => x - X start ω) (by fun_prop)
  change IsCadlag (fun t : unitInterval =>
    X (start + length * unitIntervalToNNReal t) ω - X start ω)
  simpa [clock] using htranslated

/-- At a càdlàg sample, the full-path event agrees exactly with its
countable-coordinate positive-margin description. -/
theorem mem_fullSegmentCorridorEvent_iff_rational
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    ω ∈ fullSegmentCorridorEvent X start length lower upper ↔
      (fun q => X (start + length * rationalUnitTime q) ω - X start ω) ∈
        Skorokhod.rationalCoordinateCorridorWithMargin lower upper := by
  let f : CadlagPath unitInterval ℝ :=
    ⟨segmentIncrement X start length ω,
      isCadlag_segmentIncrement X start length ω hω⟩
  have hbridge := Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff
    f lower upper
  simpa only [fullSegmentCorridorEvent, Set.mem_ofPred_eq,
    Skorokhod.rangeInOpenInterval, f,
    segmentIncrement, rationalUnitTime, unitIntervalToNNReal]
    using hbridge.symm

/-- Full-segment corridor events are measurable up to a null set when the
sample paths are càdlàg almost surely. -/
theorem nullMeasurableSet_fullSegmentCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper : ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    NullMeasurableSet
      (fullSegmentCorridorEvent X start length lower upper) P := by
  let rationalEvent : Set Ω :=
    (fun ω q => X (start + length * rationalUnitTime q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  have hmap : AEMeasurable
      (fun ω q => X (start + length * rationalUnitTime q) ω - X start ω) P := by
    exact AEMeasurable.of_eval fun q => (hX _).sub (hX start)
  have hrational : NullMeasurableSet rationalEvent P :=
    hmap.nullMeasurableSet_preimage
      (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin lower upper)
  have heq : rationalEvent =ᵐ[P]
      fullSegmentCorridorEvent X start length lower upper := by
    filter_upwards [hcadlag] with ω hω
    exact propext ((mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).symm)
  exact hrational.congr heq

theorem mem_fullSegmentCorridorReturnEvent_iff_rational
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    ω ∈ fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper ↔
      (fun q => X (start + length * rationalUnitTime q) ω - X start ω) ∈
        Skorokhod.rationalCoordinateCorridorReturnWithMargin
          lower upper coreLower coreUpper := by
  rw [fullSegmentCorridorReturnEvent,
    Skorokhod.rationalCoordinateCorridorReturnWithMargin]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_Ioo]
  have htop : unitIntervalToNNReal ⊤ = 1 := by
    apply NNReal.coe_injective
    rfl
  constructor
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mp hcorridor, by simpa [segmentIncrement,
        rationalUnitTime_top, htop] using hend⟩
  · rintro ⟨hcorridor, hend⟩
    exact ⟨(mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).mpr hcorridor, by simpa [segmentIncrement,
        rationalUnitTime_top, htop] using hend⟩

theorem nullMeasurableSet_fullSegmentCorridorReturnEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    NullMeasurableSet (fullSegmentCorridorReturnEvent X start length
      lower upper coreLower coreUpper) P := by
  let rationalEvent : Set Ω :=
    (fun ω q => X (start + length * rationalUnitTime q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  have hmap : AEMeasurable
      (fun ω q => X (start + length * rationalUnitTime q) ω - X start ω) P := by
    exact AEMeasurable.of_eval fun q => (hX _).sub (hX start)
  have hrational : NullMeasurableSet rationalEvent P :=
    hmap.nullMeasurableSet_preimage
      (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper)
  have heq : rationalEvent =ᵐ[P]
      fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper := by
    filter_upwards [hcadlag] with ω hω
    exact propext ((mem_fullSegmentCorridorReturnEvent_iff_rational
      X start length lower upper coreLower coreUpper ω hω).symm)
  exact hrational.congr heq

/-- A constrained first segment and a translated continuation lie in the
same complete-path corridor. This is the pathwise inclusion behind the
fixed-cut probability lower bound. -/
theorem fullEntrance_inter_continuation_subset_fullCorridor
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper endpointLower endpointUpper : ℝ) :
    fullSegmentCorridorReturnEvent X 0 cut
        lower upper endpointLower endpointUpper ∩
      fullSegmentCorridorEvent X cut remaining
        (lower - endpointLower) (upper - endpointUpper) ⊆
      fullSegmentCorridorEvent X 0 (cut + remaining) lower upper := by
  intro ω hω
  rcases hω with ⟨⟨⟨margin₁, hmargin₁, hfirst⟩, hend⟩,
    margin₂, hmargin₂, hsecond⟩
  have hendpoint : endpointLower < X cut ω - X 0 ω ∧
      X cut ω - X 0 ω < endpointUpper := by
    simpa [segmentIncrement] using hend
  let margin := min margin₁ (min margin₂
    (min (X cut ω - X 0 ω - endpointLower)
      (endpointUpper - (X cut ω - X 0 ω))))
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min hmargin₁ (lt_min hmargin₂
      (lt_min (sub_pos.mpr hendpoint.1) (sub_pos.mpr hendpoint.2)))
  refine ⟨margin, hmargin, ?_⟩
  intro t
  let absoluteTime := (cut + remaining) * unitIntervalToNNReal t
  by_cases hbefore : absoluteTime ≤ cut
  · obtain ⟨u, hu⟩ := exists_unitInterval_mul_eq cut absoluteTime hcut hbefore
    have hu' := hfirst u
    have hm : margin ≤ margin₁ := min_le_left _ _
    dsimp [segmentIncrement] at hu' ⊢
    simp only [zero_add] at hu' ⊢
    change cut * unitIntervalToNNReal u = absoluteTime at hu
    rw [hu] at hu'
    constructor <;> linarith

  · have hafter : cut ≤ absoluteTime := le_of_not_ge hbefore
    have htotal : absoluteTime ≤ cut + remaining := by
      simpa [absoluteTime] using mul_le_mul_of_nonneg_left
        (unitIntervalToNNReal_le_one t) (cut + remaining).property
    obtain ⟨u, hu⟩ := exists_unitInterval_add_mul_eq
      cut remaining absoluteTime hremaining hafter htotal
    have hu' := hsecond u
    have hmLow : margin ≤ X cut ω - X 0 ω - endpointLower := by
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hmUp : margin ≤ endpointUpper - (X cut ω - X 0 ω) := by
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    dsimp [segmentIncrement] at hu' ⊢
    simp only [zero_add] at hu' ⊢
    change cut + remaining * unitIntervalToNNReal u = absoluteTime at hu
    rw [hu] at hu'
    constructor <;> linarith

/-- Restricting a complete corridor path to a shorter initial horizon
preserves its positive uniform spatial margin. -/
theorem fullSegmentCorridorEvent_mono_length
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start short long : ℝ≥0) (hlong : 0 < long)
    (hshort : short ≤ long) (lower upper : ℝ) :
    fullSegmentCorridorEvent X start long lower upper ⊆
      fullSegmentCorridorEvent X start short lower upper := by
  intro ω hω
  rcases hω with ⟨margin, hmargin, hpath⟩
  refine ⟨margin, hmargin, ?_⟩
  intro t
  have htime : short * unitIntervalToNNReal t ≤ long := by
    calc
      short * unitIntervalToNNReal t ≤ short * 1 :=
        mul_le_mul_of_nonneg_left (unitIntervalToNNReal_le_one t) short.property
      _ = short := mul_one _
      _ ≤ long := hshort
  obtain ⟨u, hu⟩ := exists_unitInterval_mul_eq long
    (short * unitIntervalToNNReal t) hlong htime
  have hb := hpath u
  dsimp [segmentIncrement] at hb ⊢
  rw [hu] at hb
  exact hb

end ProbabilityTheory

end
