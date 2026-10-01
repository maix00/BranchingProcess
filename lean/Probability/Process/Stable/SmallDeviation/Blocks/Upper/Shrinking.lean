module

public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Strict
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover

/-!
# Vanishing probability of a shrinking full-path corridor

The finite-block tube upper bound already supplies a strictly subunit
probability at one fixed width. A shrinking spatial corridor fits inside the
corresponding scaled tube for each fixed block count, so its probability
vanishes without an atomlessness assumption on the increment law.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

/-- A full-segment corridor controls the range of all rational coordinates.
The extra width makes the range tube strict even if the corridor has only a
closed bound at an individual coordinate. -/
theorem fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (lower upper extra : ℝ) (hextra : 0 < extra) :
    fullSegmentCorridorEvent X 0 1 lower upper ⊆
      rationalHorizonTubeEvent X 1 (upper - lower + extra) := by
  intro ω hω
  have hcoord :
      (fun q => X (rationalUnitTime q) ω - X 0 ω) ∈
        rationalCoordinateCorridor lower upper := by
    simp only [rationalCoordinateCorridor, Set.mem_iInter, Set.mem_ofPred_eq,
      Set.mem_Ioo] 
    intro q
    obtain ⟨margin, hmargin, hpath⟩ := hω
    have hq := hpath (RationalGrid.unitCoe q)
    change lower + margin ≤
        X (0 + 1 * unitIntervalToNNReal (RationalGrid.unitCoe q)) ω - X 0 ω ∧
      X (0 + 1 * unitIntervalToNNReal (RationalGrid.unitCoe q)) ω - X 0 ω ≤
        upper - margin at hq
    have htime : unitIntervalToNNReal (RationalGrid.unitCoe q) =
        rationalUnitTime q := rfl
    rw [htime] at hq
    simp only [zero_add, one_mul] at hq
    exact ⟨by linarith, by linarith⟩
  have htube := rationalCoordinateCorridor_subset_oscillationTube
    lower upper extra hextra hcoord
  have hraw := (Skorokhod.mem_rationalCoordinateOscillationTube_sub_const_iff
    (upper - lower + extra) (X 0 ω)
    (fun q => X (rationalUnitTime q) ω)).mp htube
  change rationalHorizonProcess X 1 ω ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower + extra)
  change (fun q => X (1 * rationalUnitTime q) ω) ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower + extra)
  simpa using hraw

/-- The probability of any fixed-shape full-path corridor vanishes under
positive scaling towards zero as soon as the stable law charges the positive
half-line. This uses the established finite-block upper bound. -/
theorem IsStableLevyProcess.tendsto_measure_scaledFullCorridor_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) (lower upper : ℝ) :
    Tendsto (fun a : ℝ =>
      P (fullSegmentCorridorEvent X 0 1 (a * lower) (a * upper)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨width, c, hwidth, hc, hbound⟩ :=
    h.exists_strict_exponential_tube_upper_bound hpos
  have hα : 0 < α := h.increments.strictlyStable.1
  let C : ℝ := |upper - lower| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine tendsto_order.2 ⟨fun ε hε => (ENNReal.not_lt_zero hε).elim,
    fun ε (hε : 0 < ε) => ?_⟩
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc
  obtain ⟨n, hn'⟩ := Filter.eventually_atTop.1
    (hpow.eventually (gt_mem_nhds hε))
  have hn : c ^ n < ε := hn' n le_rfl
  let blocks : ℕ := n + 1
  have hblocks : 0 < blocks := Nat.succ_pos n
  let scale : ℝ :=
    (((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α)))
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _
  have htarget : 0 < width / scale := div_pos hwidth hscale
  have ha : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a * C < width / scale := by
    have hlim0 : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun a : ℝ => a * C) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hlim0.mul_const C
    exact hlim.eventually (gt_mem_nhds htarget)
  filter_upwards [ha, self_mem_nhdsWithin] with a ha ha0
  have hwidth' : a * upper - a * lower + a ≤ width / scale := by
    have hmul : a * (upper - lower + 1) ≤ a * C := by
      apply mul_le_mul_of_nonneg_left _ ha0.le
      dsimp [C]
      linarith [le_abs_self (upper - lower)]
    nlinarith
  have hsubset :
      fullSegmentCorridorEvent X 0 1 (a * lower) (a * upper) ⊆
        rationalHorizonTubeEvent X 1 (width / scale) := by
    intro ω hω
    have hmem := fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent
      X (a * lower) (a * upper) a ha0 hω
    have hmono : Skorokhod.rationalCoordinateOscillationTube
        (a * upper - a * lower + a) ⊆
        Skorokhod.rationalCoordinateOscillationTube (width / scale) := by
      rintro x ⟨margin, hmargin, hbound'⟩
      refine ⟨margin, hmargin, ?_⟩
      intro s t
      exact (hbound' s t).trans (sub_le_sub_right hwidth' _)
    exact hmono hmem
  calc
    P (fullSegmentCorridorEvent X 0 1 (a * lower) (a * upper)) ≤
        P (rationalHorizonTubeEvent X 1 (width / scale)) :=
      measure_mono hsubset
    _ ≤ c ^ blocks := by simpa [scale] using hbound blocks hblocks
    _ ≤ c ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (le_of_lt hc)
    _ < ε := hn

end ProbabilityTheory

end
