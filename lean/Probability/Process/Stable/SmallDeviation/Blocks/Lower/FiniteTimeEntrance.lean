/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.ShortTime
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FullCorridor
public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Support

/-!
# Stable entrance in a fixed finite time

For the shifted-corridor comparison, an entrance block may have any fixed
finite duration. The construction below uses a positive-probability bounded
block, rescales it, and repeats it a finite number of times.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

private def rationalUniformBlockEndpointSet (δ d r R : ℝ) :
    Set (↑RationalCoordinate.UnitInterval → ℝ) :=
  Skorokhod.rationalCoordinateCorridorWithMargin (-δ) δ ∩
    {f | f ⊤ - d ∈ Set.Ioo r R}

private theorem measurableSet_rationalUniformBlockEndpointSet
    (δ d r R : ℝ) :
    MeasurableSet (rationalUniformBlockEndpointSet δ d r R) := by
  exact (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin
    (-δ) δ).inter
      (measurableSet_Ioo.preimage
        ((measurable_pi_apply ⊤).sub measurable_const))

private theorem measure_firstUniformBlockEndpoint_eq_full
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (n : ℕ) (δ d r R : ℝ) :
    P ((fun ω s => rationalUniformBlockProcessFromTime X
      (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
        rationalUniformBlockEndpointSet δ d r R) =
      P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) - d ∈
          Set.Ioo r R}) := by
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  have hfirst := rationalUniformBlockProcess_zero_eq_initial X
    (Nat.succ_pos n)
  rw [rationalUniformBlockBoundary_succ_one] at hfirst
  have heq :
      ((fun ω s => rationalUniformBlockProcessFromTime X
        (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
          rationalUniformBlockEndpointSet δ d r R) =ᵐ[P]
        (fullSegmentCorridorEvent X 0 t (-δ) δ ∩
          {ω | (X t ω - X 0 ω) - d ∈ Set.Ioo r R}) := by
    filter_upwards [h.ae_cadlag] with ω hω
    have hcorr := mem_fullSegmentCorridorEvent_iff_rational
      X 0 t (-δ) δ ω hω
    simp only [rationalUniformBlockEndpointSet, Set.mem_preimage,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hfirstω := congrFun hfirst ω
    have hend : rationalUniformBlockProcessFromTime X
        (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ ⊤ ω = X t ω - X 0 ω := by
      simpa [t, rationalUnitTime_top] using congrFun hfirstω ⊤
    rw [hfirstω, hend]
    simp only [zero_add] at *
    exact propext (and_congr hcorr.symm Iff.rfl)
  exact measure_congr heq

private theorem rationalUniformPrefixBlockBounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (d R B : ℝ) (hR : 0 ≤ R) (_hB : 0 ≤ B)
    (hendpoint : ∀ j : Fin blocks,
      |rationalTubeBlockIncrement hblocks j
        (fun q => X (rationalUnitTime q) ω - X 0 ω) ⊤ - d| ≤ R)
    (hlocal : ∀ j : Fin blocks, ∀ q : ↑RationalCoordinate.UnitInterval,
      |rationalTubeBlockIncrement hblocks j
        (fun q => X (rationalUnitTime q) ω - X 0 ω) q| ≤ B) :
    (∀ q : ↑RationalCoordinate.UnitInterval,
      min 0 ((blocks : ℝ) * d) - ((blocks : ℝ) * R + B) ≤
          X (rationalUnitTime q) ω - X 0 ω ∧
        X (rationalUnitTime q) ω - X 0 ω ≤
          max 0 ((blocks : ℝ) * d) + ((blocks : ℝ) * R + B)) ∧
      |X 1 ω - X 0 ω - (blocks : ℝ) * d| ≤ (blocks : ℝ) * R := by
  let f : ↑RationalCoordinate.UnitInterval → ℝ :=
    fun q => X (rationalUnitTime q) ω - X 0 ω
  let e : ℕ → ℝ := fun k =>
    f (rationalUniformBlockBoundaryTime hblocks k) - (k : ℝ) * d
  have hf0 : f ⊥ = 0 := by simp [f, rationalUnitTime_bot]
  have he0 : e 0 = 0 := by
    simp [e, rationalUniformBlockBoundaryTime_zero hblocks, hf0]
  have hdiff (k : ℕ) (hk : k < blocks) :
      e (k + 1) - e k =
        rationalTubeBlockIncrement hblocks ⟨k, hk⟩ f ⊤ - d := by
    dsimp [e, rationalTubeBlockIncrement]
    rw [rationalUniformBlockBoundaryTime_eq_blockStart hblocks ⟨k, hk⟩,
      rationalUniformBlockBoundaryTime_succ_eq_blockEnd hblocks ⟨k, hk⟩]
    push_cast
    ring
  have herr : ∀ k ≤ blocks, |e k| ≤ (k : ℝ) * R := by
    intro k hk
    induction k with
    | zero => simp [he0]
    | succ k ih =>
      have hklt : k < blocks := by omega
      have hstep := hendpoint ⟨k, hklt⟩
      have hprev := ih (by omega)
      have hrec : e (k + 1) = e k +
          (rationalTubeBlockIncrement hblocks ⟨k, hklt⟩ f ⊤ - d) := by
        linarith [hdiff k hklt]
      rw [hrec]
      calc
        |e k + (rationalTubeBlockIncrement hblocks ⟨k, hklt⟩ f ⊤ - d)|
            ≤ |e k| +
              |rationalTubeBlockIncrement hblocks ⟨k, hklt⟩ f ⊤ - d| :=
                abs_add_le _ _
        _ ≤ (k : ℝ) * R + R := add_le_add hprev hstep
        _ = ((k + 1 : ℕ) : ℝ) * R := by push_cast; ring
  constructor
  · intro q
    obtain ⟨j, s, hjs⟩ := exists_rationalUniformBlockTime hblocks q
    have hjerr := herr j.val j.isLt.le
    have hstart : f (rationalUniformBlockTime hblocks j ⊥) =
        (j.val : ℝ) * d + e j.val := by
      have hboundary := rationalUniformBlockBoundaryTime_eq_blockStart hblocks j
      dsimp [e]
      rw [← hboundary]
      ring
    have hblock := hlocal j s
    have hdecomp : f (rationalUniformBlockTime hblocks j s) =
        f (rationalUniformBlockTime hblocks j ⊥) +
          rationalTubeBlockIncrement hblocks j f s := by
      have h := rationalUniformBlock_displacement_eq_endpoint_add_increment
        hblocks j f s
      simpa [f, hf0] using h
    have hvalue : f q = (j.val : ℝ) * d + e j.val +
        rationalTubeBlockIncrement hblocks j f s := by
      rw [← hjs, hdecomp, hstart]
    have hjlo : min 0 ((blocks : ℝ) * d) ≤ (j.val : ℝ) * d := by
      by_cases hd : 0 ≤ d
      · exact le_trans (min_le_left _ _)
          (mul_nonneg (show 0 ≤ (j.val : ℝ) by positivity) hd)
      · have hd' : d ≤ 0 := le_of_not_ge hd
        have hle : (blocks : ℝ) * d ≤ (j.val : ℝ) * d := by
          exact mul_le_mul_of_nonpos_right (by exact_mod_cast j.isLt.le) hd'
        exact le_trans (min_le_right _ _) hle
    have hjhi : (j.val : ℝ) * d ≤ max 0 ((blocks : ℝ) * d) := by
      by_cases hd : 0 ≤ d
      · exact le_trans
          (mul_le_mul_of_nonneg_right
            (show (j.val : ℝ) ≤ (blocks : ℝ) by exact_mod_cast j.isLt.le) hd)
          (le_max_right _ _)
      · have hd' : d ≤ 0 := le_of_not_ge hd
        exact le_trans
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hd')
          (le_max_left _ _)
    have hjN : (j.val : ℝ) ≤ (blocks : ℝ) := by
      exact_mod_cast (Nat.le_of_lt j.isLt)
    have hJRle : (j.val : ℝ) * R ≤ (blocks : ℝ) * R :=
      mul_le_mul_of_nonneg_right hjN hR
    have hJRnonneg : 0 ≤ (j.val : ℝ) * R := mul_nonneg (by positivity) hR
    have herrlo : -((blocks : ℝ) * R) ≤ e j.val := by
      have := abs_le.mp hjerr
      nlinarith
    have herrhi : e j.val ≤ (blocks : ℝ) * R := by
      have := abs_le.mp hjerr
      nlinarith
    have hblock := hlocal j s
    have hblocklo : -B ≤
        rationalTubeBlockIncrement hblocks j f s := (abs_le.mp hblock).1
    have hblockhi :
        rationalTubeBlockIncrement hblocks j f s ≤ B := (abs_le.mp hblock).2
    change min 0 ((blocks : ℝ) * d) - ((blocks : ℝ) * R + B) ≤ f q ∧
      f q ≤ max 0 ((blocks : ℝ) * d) + ((blocks : ℝ) * R + B)
    rw [hvalue]
    constructor <;> linarith
  · have htop : f ⊤ = f (rationalUniformBlockBoundaryTime hblocks blocks) := by
      congr 1
      apply Subtype.ext
      simp [rationalUniformBlockBoundaryTime]
      field_simp [Nat.ne_of_gt hblocks]
    have htopX : f ⊤ = X 1 ω - X 0 ω := by
      simp [f, rationalUnitTime_top]
    have hendpoint : f ⊤ - (blocks : ℝ) * d = e blocks := by
      dsimp [e]
      rw [htop]
    rw [← htopX, hendpoint]
    have hlast := herr blocks le_rfl
    exact hlast

private theorem measure_fullSegmentCorridorReturn_timeSpaceScale_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent
        (fun t ω => (horizon : ℝ) ^ (-(1 / α)) * X (horizon * t) ω)
        0 1 lower upper coreLower coreUpper) =
      P (fullSegmentCorridorReturnEvent X 0 1
        lower upper coreLower coreUpper) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    (horizon : ℝ) ^ (-(1 / α)) * X (horizon * t) ω
  have hY : IsStableLevyProcess α μ Y P := h.timeSpaceScale horizon hhorizon
  let C := Skorokhod.rationalCoordinateCorridorReturnWithMargin
    lower upper coreLower coreUpper
  let fX : Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => X (rationalUnitTime q) ω - X 0 ω
  let fY : Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => Y (rationalUnitTime q) ω - Y 0 ω
  have hC : MeasurableSet C := by
    exact Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
      lower upper coreLower coreUpper
  have hrat : P (fY ⁻¹' C) = P (fX ⁻¹' C) := by
    have hlaw := h.centeredRationalRestriction_identDistrib horizon hhorizon
    have hprob := hlaw.measure_mem_eq hC
    let g : Ω → ↑RationalCoordinate.UnitInterval → ℝ := fun ω q =>
      (horizon : ℝ) ^ (-(1 / α)) *
        (X (horizon * rationalUnitTime q) ω - X 0 ω)
    have hg : g = fY := by
      funext ω q
      simp [g, fY, Y]
      ring
    change P (fX ⁻¹' C) = P (g ⁻¹' C) at hprob
    rw [hg] at hprob
    exact hprob.symm
  have hfullX : fullSegmentCorridorReturnEvent X 0 1
      lower upper coreLower coreUpper =ᵐ[P] fX ⁻¹' C := by
    filter_upwards [h.ae_cadlag] with ω hω
    apply propext
    change (ω ∈ fullSegmentCorridorReturnEvent X 0 1
      lower upper coreLower coreUpper) ↔ fX ω ∈ C
    simpa [fX] using
      (mem_fullSegmentCorridorReturnEvent_iff_rational X 0 1
        lower upper coreLower coreUpper ω hω)
  have hfullY : fullSegmentCorridorReturnEvent Y 0 1
      lower upper coreLower coreUpper =ᵐ[P] fY ⁻¹' C := by
    filter_upwards [hY.ae_cadlag] with ω hω
    apply propext
    change (ω ∈ fullSegmentCorridorReturnEvent Y 0 1
      lower upper coreLower coreUpper) ↔ fY ω ∈ C
    simpa [fY] using
      (mem_fullSegmentCorridorReturnEvent_iff_rational Y 0 1
        lower upper coreLower coreUpper ω hω)
  calc
    P (fullSegmentCorridorReturnEvent Y 0 1
        lower upper coreLower coreUpper) = P (fY ⁻¹' C) := measure_congr hfullY
    _ = P (fX ⁻¹' C) := hrat
    _ = P (fullSegmentCorridorReturnEvent X 0 1
        lower upper coreLower coreUpper) := (measure_congr hfullX).symm

private theorem exists_bounded_unit_endpoint_block
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (z w : ℝ)
    (hJpos : 0 < μ (Set.Ioo (z - w) (z + w))) :
    ∃ K : ℝ, 0 < K ∧
      0 < P (fullSegmentCorridorReturnEvent X 0 1
        (-K) K (z - w) (z + w)) := by
  have heventually := h.eventually_fullShortCorridor_scaledIncrement_pos
    1 (by norm_num) (Set.Ioo (z - w) (z + w)) measurableSet_Ioo hJpos
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp heventually
  have hshort := hn n le_rfl
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hα : 0 < α := h.increments.strictlyStable.1
  let a : ℝ := (t : ℝ) ^ (1 / α)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _
  have haPow : a ^ α = (t : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul (NNReal.coe_pos.mpr ht).le]
    have hexp : (1 / α) * α = 1 := by field_simp [ne_of_gt hα]
    rw [hexp, Real.rpow_one]
  have htime : stableEntranceHorizon α a = t := by
    apply NNReal.coe_injective
    simp [stableEntranceHorizon, haPow]
  let shortEvent : Set Ω :=
    fullSegmentCorridorEvent X 0 t (-1) 1 ∩
      {ω | (X t ω - X 0 ω) / a ∈ Set.Ioo (z - w) (z + w)}
  have hshort' : 0 < P shortEvent := by
    simpa [shortEvent, t, a] using hshort
  let shortReturn : Set Ω :=
    fullSegmentCorridorReturnEvent X 0 t (-1) 1
      (a * (z - w)) (a * (z + w))
  have hsubset : shortEvent ⊆ shortReturn := by
    rintro ω ⟨hcorr, hend⟩
    refine ⟨hcorr, ?_⟩
    have ha0 : a ≠ 0 := ha.ne'
    have hseg : segmentIncrement X 0 t ω ⊤ = X t ω - X 0 ω := by
      simp [segmentIncrement]
    have hcancel : a * ((X t ω - X 0 ω) / a) = X t ω - X 0 ω := by
      field_simp
    have hend' : z - w < (X t ω - X 0 ω) / a ∧
        (X t ω - X 0 ω) / a < z + w := hend
    change segmentIncrement X 0 t ω ⊤ ∈
      Set.Ioo (a * (z - w)) (a * (z + w))
    rw [hseg]
    simp only [Set.mem_Ioo]
    constructor
    · have := mul_lt_mul_of_pos_left hend'.1 ha
      nlinarith [hcancel]
    · have := mul_lt_mul_of_pos_left hend'.2 ha
      nlinarith [hcancel]
  have hshortReturn : 0 < P shortReturn :=
    hshort'.trans_le (measure_mono hsubset)
  let K : ℝ := a⁻¹
  have hK : 0 < K := inv_pos.mpr ha
  have hscale := h.shortEntrance_fullCorridorReturn_probability a ha
    (-K) K (z - w) (z + w)
  rw [htime] at hscale
  have hcancelPos : a * K = 1 := by
    dsimp [K]
    field_simp
  have hcancelNeg : a * (-K) = -1 := by rw [mul_neg, hcancelPos]
  rw [hcancelNeg, hcancelPos] at hscale
  refine ⟨K, hK, ?_⟩
  rw [← hscale]
  exact hshortReturn

/-- A stable process can enter any open corridor at any interior endpoint
with positive probability in some fixed finite time. The time may depend on
the corridor and endpoint, but is fixed independently of later scalings. -/
theorem IsStableLevyProcess.exists_pos_time_measure_fullSegmentCorridorReturnEvent_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper y ε : ℝ)
    (hlower : lower < 0) (hupper : 0 < upper)
    (hlowerY : lower < y) (hyUpper : y < upper) (hε : 0 < ε)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ T : ℝ≥0, 0 < T ∧
      0 < P (fullSegmentCorridorReturnEvent X 0 T
        lower upper (y - ε) (y + ε)) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  by_cases hy0 : y = 0
  · refine ⟨1, by norm_num, ?_⟩
    have hcoreLower : y - ε < 0 := by rw [hy0]; linarith
    have hcoreUpper : 0 < y + ε := by rw [hy0]; linarith
    simpa [hy0] using h.measure_fullSegmentCorridorReturn_pos_of_zero_mem
      lower upper (y - ε) (y + ε) hlower hupper hcoreLower hcoreUpper hpos hneg
  · let m : ℝ := min (min (-lower) (y - lower))
      (min upper (min (upper - y) ε))
    have hm : 0 < m := by
      dsimp [m]
      exact lt_min (lt_min (by linarith) (sub_pos.mpr hlowerY))
        (lt_min hupper (lt_min (sub_pos.mpr hyUpper) hε))
    have hmLower : m ≤ -lower :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hmLowerY : m ≤ y - lower :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hmUpper : m ≤ upper :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hmUpperY : m ≤ upper - y :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hmEps : m ≤ ε :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hyne : y ≠ 0 := hy0
    have hposPick : ∃ z : ℝ, 0 < z ∧ z ∈ μ.support := by
      obtain ⟨z, hz, hzs⟩ := μ.nonempty_inter_support_of_pos hpos
      exact ⟨z, hz, hzs⟩
    have hnegPick : ∃ z : ℝ, z < 0 ∧ z ∈ μ.support := by
      obtain ⟨z, hz, hzs⟩ := μ.nonempty_inter_support_of_pos hneg
      exact ⟨z, hz, hzs⟩
    let z : ℝ := if 0 < y then Classical.choose hposPick else Classical.choose hnegPick
    have hzsign : (0 < y ∧ 0 < z) ∨ (y < 0 ∧ z < 0) := by
      by_cases hypos : 0 < y
      · left
        refine ⟨hypos, ?_⟩
        simpa [z, hypos] using (Classical.choose_spec hposPick).1
      · right
        have hyneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hyne
        refine ⟨hyneg, ?_⟩
        simpa [z, hypos] using (Classical.choose_spec hnegPick).1
    have hzSupport : z ∈ μ.support := by
      by_cases hypos : 0 < y
      · simpa [z, hypos] using (Classical.choose_spec hposPick).2
      · simpa [z, hypos] using (Classical.choose_spec hnegPick).2
    have hyAbs : 0 < |y| := abs_pos.mpr hyne
    have hzAbs : 0 < |z| := abs_pos.mpr (by
      rcases hzsign with ⟨_, hzpos⟩ | ⟨_, hzneg⟩
      · exact ne_of_gt hzpos
      · exact ne_of_lt hzneg)
    have hyz : 0 < y / z := by
      rcases hzsign with ⟨hypos, hzpos⟩ | ⟨hyneg, hzneg⟩
      · exact div_pos hypos hzpos
      · exact div_pos_of_neg_of_neg hyneg hzneg
    have hyzAbs : y / z = |y| / |z| := by
      calc
        y / z = |y / z| := (abs_of_pos hyz).symm
        _ = |y| / |z| := abs_div y z
    let w : ℝ := min (|z| / 4) (m * |z| / (16 * |y|))
    have hw : 0 < w := by
      dsimp [w]
      apply lt_min
      · positivity
      · positivity
    have hwAbs : w ≤ m * |z| / (16 * |y|) := min_le_right _ _
    have hwz : w ≤ |z| / 4 := min_le_left _ _
    have hzJ : z ∈ Set.Ioo (z - w) (z + w) := by
      constructor <;> linarith
    have hJpos : 0 < μ (Set.Ioo (z - w) (z + w)) := by
      exact (Measure.mem_support_iff_forall z).mp hzSupport _
        (isOpen_Ioo.mem_nhds hzJ)
    obtain ⟨K, hK, hq⟩ := exists_bounded_unit_endpoint_block h z w hJpos
    let threshold : ℝ := 32 * K * |y| / (m * |z|)
    have hthreshold : 0 < threshold := by
      dsimp [threshold]
      positivity
    obtain ⟨M, hM⟩ := exists_nat_gt threshold
    let N : ℕ := M + 1
    have hN : 0 < N := by dsimp [N]; omega
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hNlarger : threshold < (N : ℝ) := by
      dsimp [N]
      exact lt_trans hM (by norm_num)
    have hNcross : 32 * K * |y| < (N : ℝ) * (m * |z|) := by
      have h := mul_lt_mul_of_pos_right hNlarger (mul_pos hm hzAbs)
      dsimp [threshold] at h
      have hmz : m * |z| ≠ 0 := (mul_pos hm hzAbs).ne'
      field_simp [hmz] at h
      nlinarith
    have hKcost : (K * |y|) / ((N : ℝ) * |z|) < m / 16 := by
      apply (div_lt_iff₀ (mul_pos hNreal hzAbs)).2
      nlinarith [hNcross]
    let blockTime : ℝ≥0 := 1 / (N : ℝ≥0)
    have hblockTime : 0 < blockTime := by
      dsimp [blockTime]
      positivity
    let cN : ℝ := (blockTime : ℝ) ^ (1 / α)
    let cNInv : ℝ := (blockTime : ℝ) ^ (-(1 / α))
    have hcN : 0 < cN := by
      dsimp [cN]
      exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hblockTime) _
    have hcNInv : 0 < cNInv := by
      dsimp [cNInv]
      exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hblockTime) _
    have hcNmul : cN * cNInv = 1 := by
      have hpowne : (blockTime : ℝ) ^ (1 / α) ≠ 0 := hcN.ne'
      dsimp [cN, cNInv]
      rw [Real.rpow_neg (NNReal.coe_pos.mpr hblockTime).le]
      exact mul_inv_cancel₀ hpowne
    let d : ℝ := z * cN
    let R : ℝ := w * cN
    let B : ℝ := K * cN
    let Troot : ℝ := y / ((N : ℝ) * z * cN)
    have hTroot : 0 < Troot := by
      have hTrootEq : Troot = (y / z) / ((N : ℝ) * cN) := by
        dsimp [Troot]
        field_simp [ne_of_gt hzAbs, hcN.ne', hNreal.ne']
      rw [hTrootEq]
      exact div_pos hyz (mul_pos hNreal hcN)
    have htarget : y / Troot = (N : ℝ) * d := by
      dsimp [Troot, d]
      field_simp [ne_of_gt hzAbs, hcN.ne', hNreal.ne']
    have hratioWindow : (y / z) * w ≤ m / 16 := by
      rw [hyzAbs]
      calc
        (|y| / |z|) * w ≤ (|y| / |z|) * (m * |z| / (16 * |y|)) :=
          mul_le_mul_of_nonneg_left hwAbs (div_nonneg (abs_nonneg y) (abs_nonneg z))
        _ = m / 16 := by field_simp [ne_of_gt hyAbs, ne_of_gt hzAbs]
    have hBcost : Troot * B < m / 16 := by
      have hidentity : Troot * B = K * (y / z) / (N : ℝ) := by
        dsimp [Troot, B]
        field_simp [ne_of_gt hzAbs, hcN.ne', hNreal.ne']
      have hcost' : K * (y / z) / (N : ℝ) =
          (K * |y|) / ((N : ℝ) * |z|) := by
        rw [hyzAbs]
        field_simp [ne_of_gt hzAbs, hNreal.ne']
      rw [hidentity, hcost']
      exact hKcost
    have hRcost : Troot * ((N : ℝ) * R) ≤ m / 16 := by
      have hidentity : Troot * ((N : ℝ) * R) = (y / z) * w := by
        dsimp [Troot, R]
        field_simp [ne_of_gt hzAbs, hcN.ne', hNreal.ne']
      rw [hidentity]
      exact hratioWindow
    have htotalCost : Troot * ((N : ℝ) * R + B) < m / 8 := by
      rw [mul_add]
      linarith [hRcost, hBcost]
    have herror : (N : ℝ) * R + B < m / (4 * Troot) := by
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith [htotalCost]
    have hendpointError : (N : ℝ) * R < ε / Troot := by
      apply (lt_div_iff₀ hTroot).2
      have hcost : ((N : ℝ) * R) * Troot ≤ m / 16 := by
        nlinarith [hRcost]
      have hm16 : m / 16 < ε := by
        exact (div_lt_self hm (by norm_num : (1 : ℝ) < 16)).trans_le hmEps
      exact lt_of_le_of_lt hcost hm16
    have hα : 0 < α := h.increments.strictlyStable.1
    let T : ℝ≥0 := ⟨Troot ^ α, (Real.rpow_pos_of_pos hTroot α).le⟩
    have hT : 0 < T := by
      apply NNReal.coe_pos.mp
      exact Real.rpow_pos_of_pos hTroot α
    have hTscale : (T : ℝ) ^ (-(1 / α)) = Troot⁻¹ := by
      change (Troot ^ α) ^ (-(1 / α)) = Troot⁻¹
      rw [← Real.rpow_mul hTroot.le]
      have hexp : α * (-(1 / α)) = -1 := by
        field_simp [ne_of_gt hα]
      rw [hexp, Real.rpow_neg_one]
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      (T : ℝ) ^ (-(1 / α)) * X (T * t) ω
    have hY : IsStableLevyProcess α μ Y P := by
      exact h.timeSpaceScale T hT
    have hqY : 0 < P (fullSegmentCorridorReturnEvent Y 0 1
        (-K) K (z - w) (z + w)) := by
      rw [measure_fullSegmentCorridorReturn_timeSpaceScale_eq h T hT
        (-K) K (z - w) (z + w)]
      exact hq
    have hBpos : 0 ≤ B := le_of_lt (mul_pos hK hcN)
    have hRpos : 0 ≤ R := le_of_lt (mul_pos hw hcN)
    have hscaleBlock := hY.measure_fullSegmentCorridorReturn_scale
      blockTime hblockTime (-B) B (d - R) (d + R)
    have hBscale : (-B) * cNInv = -K := by
      dsimp [B]
      rw [← neg_mul, mul_assoc, hcNmul]
      ring
    have hUscale : B * cNInv = K := by
      dsimp [B]
      calc
        K * cN * cNInv = K * (cN * cNInv) := by ring
        _ = K := by rw [hcNmul]; ring
    have hCoreLo : (d - R) * cNInv = z - w := by
      dsimp [d, R]
      calc
        (z * cN - w * cN) * cNInv = (z - w) * (cN * cNInv) := by ring
        _ = z - w := by rw [hcNmul]; ring
    have hCoreHi : (d + R) * cNInv = z + w := by
      dsimp [d, R]
      calc
        (z * cN + w * cN) * cNInv = (z + w) * (cN * cNInv) := by ring
        _ = z + w := by rw [hcNmul]; ring
    rw [hBscale, hUscale, hCoreLo, hCoreHi] at hscaleBlock
    have hblockPos : 0 < P (fullSegmentCorridorReturnEvent Y 0 blockTime
        (-B) B (d - R) (d + R)) := by
      rw [hscaleBlock]
      exact hqY
    have hblockSubset :
        fullSegmentCorridorReturnEvent Y 0 blockTime
            (-B) B (d - R) (d + R) ⊆
          fullSegmentCorridorEvent Y 0 blockTime (-B) B ∩
            {ω | (Y blockTime ω - Y 0 ω) - d ∈ Set.Ioo (-R) R} := by
      rintro ω ⟨hcorr, hend⟩
      refine ⟨hcorr, ?_⟩
      change (Y blockTime ω - Y 0 ω) - d ∈ Set.Ioo (-R) R
      change segmentIncrement Y 0 blockTime ω ⊤ ∈
        Set.Ioo (d - R) (d + R) at hend
      have hseg : segmentIncrement Y 0 blockTime ω ⊤ =
          Y blockTime ω - Y 0 ω := by
        simp [segmentIncrement]
      rw [hseg] at hend
      simp only [Set.mem_Ioo] at hend ⊢
      constructor <;> linarith
    have hblockTimeEq : blockTime = 1 / ((M : ℝ≥0) + 1) := by
      dsimp [blockTime, N]
      simp
    have hblockFullPos : 0 < P
        (fullSegmentCorridorEvent Y 0
          (1 / ((M : ℝ≥0) + 1)) (-B) B ∩
          {ω | (Y (1 / ((M : ℝ≥0) + 1)) ω - Y 0 ω) - d ∈
            Set.Ioo (-R) R}) := by
      have hpos := hblockPos.trans_le (measure_mono hblockSubset)
      rw [← hblockTimeEq]
      exact hpos
    let V := rationalUniformBlockEndpointSet B d (-R) R
    have hV : MeasurableSet V :=
      measurableSet_rationalUniformBlockEndpointSet B d (-R) R
    have hfirstPos : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime Y
        (Nat.succ_pos M) ⟨0, Nat.succ_pos M⟩ s ω) ⁻¹' V) := by
      rw [measure_firstUniformBlockEndpoint_eq_full hY M B d (-R) R]
      exact hblockFullPos
    let q : ENNReal := P ((fun ω s => rationalUniformBlockProcessFromTime Y
      (Nat.succ_pos M) ⟨0, Nat.succ_pos M⟩ s ω) ⁻¹' V)
    have hq : 0 < q := hfirstPos
    have hsuccess : 0 < P
        (rationalUniformPrefixBlockEvent Y V (Nat.succ_pos M) (M + 1)) := by
      exact (ENNReal.pow_pos hq (M + 1)).trans_le
        (hY.pow_le_measure_rationalUniformPrefixBlockEvent (M + 1)
          (Nat.succ_pos M) V hV q le_rfl)
    let Nreal : ℝ := (N : ℝ)
    let lowerY : ℝ := lower / Troot
    let upperY : ℝ := upper / Troot
    let coreLowerY : ℝ := (y - ε) / Troot
    let coreUpperY : ℝ := (y + ε) / Troot
    let entranceY : Set Ω := fullSegmentCorridorReturnEvent Y 0 1
      lowerY upperY coreLowerY coreUpperY
    have hNrealEq : Nreal = (N : ℝ) := rfl
    have hmarginLower : lowerY + m / Troot ≤ min 0 (y / Troot) := by
      have h0 : lower + m ≤ 0 := by linarith
      have hy : lower + m ≤ y := by linarith
      have h0' : lower / Troot + m / Troot ≤ 0 := by
        rw [← add_div]
        exact (div_le_iff₀ hTroot).2 (by simpa using h0)
      have hy' : lower / Troot + m / Troot ≤ y / Troot := by
        rw [← add_div]
        apply (div_le_iff₀ hTroot).2
        calc
          lower + m ≤ y := hy
          _ = y / Troot * Troot := (div_mul_cancel₀ y hTroot.ne').symm
      exact le_min h0' hy'
    have hmarginUpper : max 0 (y / Troot) ≤ upperY - m / Troot := by
      have h0 : 0 ≤ upper - m := by linarith
      have hy : y ≤ upper - m := by linarith
      have h0' : 0 ≤ upper / Troot - m / Troot := by
        rw [← sub_div]
        exact (le_div_iff₀ hTroot).2 (by simpa using h0)
      have hy' : y / Troot ≤ upper / Troot - m / Troot := by
        rw [← sub_div]
        apply (div_le_iff₀ hTroot).2
        calc
          y ≤ upper - m := hy
          _ = (upper - m) / Troot * Troot :=
            (div_mul_cancel₀ (upper - m) hTroot.ne').symm
      exact max_le h0' hy'
    have hmarginSplit : m / Troot = 4 * (m / (4 * Troot)) := by
      field_simp
    have hNtarget : (N : ℝ) * d = y / Troot := htarget.symm
    have hNRE : (N : ℝ) * R + B < m / (4 * Troot) := herror
    let successSet : Set Ω :=
      rationalUniformPrefixBlockEvent Y V (Nat.succ_pos M) (M + 1)
    have hentrancePos : 0 < P entranceY := by
      apply hsuccess.trans_le
      apply measure_mono_ae
      filter_upwards [hY.ae_cadlag] with ω hcad hω
      let f : ↑RationalCoordinate.UnitInterval → ℝ := fun q =>
        Y (rationalUnitTime q) ω - Y 0 ω
      have hboundary : rationalUniformBlockBoundary (M + 1) (M + 1)
          (Nat.succ_pos M) = 1 := by
        apply NNReal.coe_injective
        change ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) = 1
        exact div_self (by positivity)
      have hprefixEq : rationalUniformPrefixPath Y (M + 1) (M + 1)
          (Nat.succ_pos M) ω = f := by
        funext q
        simp [f, rationalUniformPrefixPath, hboundary,
          min_eq_left (rationalUnitTime_le_one q)]
      have hmem : f ∈ rationalUniformPrefixBlockSet (Nat.succ_pos M)
          (M + 1) V := by
        have hω' : ω ∈ rationalUniformPrefixBlockEvent Y V
            (Nat.succ_pos M) (M + 1) := by
          simpa only [successSet] using hω
        rw [rationalUniformPrefixBlockEvent_eq_preimage Y V
          (Nat.succ_pos M) (M + 1)] at hω'
        simpa [hprefixEq] using hω'
      have hmem' : ∀ j : Fin (M + 1),
          rationalTubeBlockIncrement (Nat.succ_pos M) j f ∈ V := by
        simp only [rationalUniformPrefixBlockSet, Set.mem_iInter] at hmem
        intro j
        have hj := hmem j
        simpa [j.isLt] using hj
      have hdata : ∀ j : Fin (M + 1),
          |rationalTubeBlockIncrement (Nat.succ_pos M) j f ⊤ - d| ≤ R ∧
          ∀ q : ↑RationalCoordinate.UnitInterval,
            |rationalTubeBlockIncrement (Nat.succ_pos M) j f q| ≤ B := by
        intro j
        have hj := hmem' j
        change rationalTubeBlockIncrement (Nat.succ_pos M) j f ∈
          rationalUniformBlockEndpointSet B d (-R) R at hj
        rcases hj with ⟨hcorr, hend⟩
        rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real] at hcorr
        obtain ⟨margin, hmargin, hbound⟩ := hcorr
        have hend' : -R < rationalTubeBlockIncrement (Nat.succ_pos M) j f ⊤ - d ∧
            rationalTubeBlockIncrement (Nat.succ_pos M) j f ⊤ - d < R := by
          simpa using hend
        have he : |rationalTubeBlockIncrement (Nat.succ_pos M) j f ⊤ - d| ≤ R := by
          exact abs_le.mpr ⟨by linarith [hend'.1], by linarith [hend'.2]⟩
        have hloc : ∀ q : ↑RationalCoordinate.UnitInterval,
            |rationalTubeBlockIncrement (Nat.succ_pos M) j f q| ≤ B := by
          intro q
          have hq := hbound q
          apply abs_le.mpr
          constructor <;> linarith
        exact ⟨he, hloc⟩
      have hpathBounds := rationalUniformPrefixBlockBounds Y ω
        (M + 1) (Nat.succ_pos M) d R B hRpos hBpos
        (fun j => (hdata j).1) (fun j q => (hdata j).2 q)
      have hrat : f ∈ Skorokhod.rationalCoordinateCorridorWithMargin
          lowerY upperY := by
        rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real]
        refine ⟨m / (4 * Troot), by positivity, fun q => ?_⟩
        rcases hpathBounds.1 q with ⟨hqlo, hqhi⟩
        have hmarginSmall : 0 < m / (4 * Troot) := by positivity
        have herrorGap : m / (4 * Troot) ≤ m / Troot - ((N : ℝ) * R + B) := by
          rw [hmarginSplit]
          linarith only [hNRE, hmarginSmall]
        have hlowerStart : lowerY + m / Troot ≤ min 0 ((N : ℝ) * d) := by
          rw [hNtarget]
          exact hmarginLower
        have hupperStart : max 0 ((N : ℝ) * d) ≤ upperY - m / Troot := by
          rw [hNtarget]
          exact hmarginUpper
        have hlow : lowerY + m / (4 * Troot) ≤
            min 0 ((N : ℝ) * d) - ((N : ℝ) * R + B) := by
          calc
            lowerY + m / (4 * Troot) ≤
                lowerY + (m / Troot - ((N : ℝ) * R + B)) := by linarith
            _ = lowerY + m / Troot - ((N : ℝ) * R + B) := by ring
            _ ≤ min 0 ((N : ℝ) * d) - ((N : ℝ) * R + B) :=
              sub_le_sub_right hlowerStart _
        have hhigh : max 0 ((N : ℝ) * d) + ((N : ℝ) * R + B) ≤
            upperY - m / (4 * Troot) := by
          calc
            max 0 ((N : ℝ) * d) + ((N : ℝ) * R + B) ≤
                max 0 ((N : ℝ) * d) + (m / Troot - m / (4 * Troot)) := by
                  rw [hmarginSplit]
                  linarith only [hNRE, hmarginSmall]
            _ = (m / Troot - m / (4 * Troot)) + max 0 ((N : ℝ) * d) := by ring
            _ ≤ (m / Troot - m / (4 * Troot)) + (upperY - m / Troot) :=
              add_le_add_right hupperStart _
            _ = upperY - m / (4 * Troot) := by ring
        constructor
        · exact le_trans hlow hqlo
        · exact le_trans hqhi hhigh
      have hEndAbs : |Y 1 ω - Y 0 ω - y / Troot| ≤ (N : ℝ) * R := by
        have hend0 := hpathBounds.2
        change |Y 1 ω - Y 0 ω - (N : ℝ) * d| ≤ (N : ℝ) * R at hend0
        rw [hNtarget] at hend0
        exact hend0
      have hcore : f ⊤ ∈ Set.Ioo coreLowerY coreUpperY := by
        change f ⊤ ∈ Set.Ioo ((y - ε) / Troot) ((y + ε) / Troot)
        have hleft : (y - ε) / Troot = y / Troot - ε / Troot := by
          rw [sub_div]
        have hright : (y + ε) / Troot = y / Troot + ε / Troot := by
          rw [add_div]
        rw [hleft, hright]
        have hEndAbs' : |f ⊤ - y / Troot| ≤ (N : ℝ) * R := by
          simpa only [f, rationalUnitTime_top] using hEndAbs
        have hEps : (N : ℝ) * R < ε / Troot := hendpointError
        rcases abs_le.mp hEndAbs' with ⟨hlo, hhi⟩
        exact ⟨by linarith, by linarith⟩
      have hratReturn : f ∈
          Skorokhod.rationalCoordinateCorridorReturnWithMargin
            lowerY upperY coreLowerY coreUpperY := by
        exact ⟨hrat, hcore⟩
      exact (mem_fullSegmentCorridorReturnEvent_iff_rational Y 0 1
        lowerY upperY coreLowerY coreUpperY ω hcad).2 (by
          simpa [f] using hratReturn)
    have hunitPos : 0 < P (fullSegmentCorridorReturnEvent X 0 1
        lowerY upperY coreLowerY coreUpperY) := by
      rw [← measure_fullSegmentCorridorReturn_timeSpaceScale_eq h T hT
        lowerY upperY coreLowerY coreUpperY]
      exact hentrancePos
    have hscaleBack := h.measure_fullSegmentCorridorReturn_scale T hT
      lower upper (y - ε) (y + ε)
    rw [hTscale] at hscaleBack
    have hscaleBack' : P (fullSegmentCorridorReturnEvent X 0 T
        lower upper (y - ε) (y + ε)) =
      P (fullSegmentCorridorReturnEvent X 0 1
        lowerY upperY coreLowerY coreUpperY) := by
      simpa [lowerY, upperY, coreLowerY, coreUpperY,
        div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaleBack
    refine ⟨T, hT, ?_⟩
    rw [hscaleBack']
    exact hunitPos

end ProbabilityTheory

end
