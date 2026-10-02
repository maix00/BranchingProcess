module

public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Return
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover
public import Probability.Process.Path.Skorokhod.Corridor.Segment
import Mathlib.Order.CompleteLattice.Lemmas

/-!
# Stable-process block bounds

Finite endpoint bins give the lower block estimate while preserving the
left-open, right-closed endpoint convention. The same construction provides
the finite-horizon return bound used in the small-deviation comparison.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The integer shift represented by one of seven endpoint windows. -/
def blockEndpointShift (i : Fin 7) : ℝ := 3 - (i.val : ℝ)

/-- A full rational block path confined to `(-a,a)` and ending in the
source's left-open, right-closed window. -/
def rationalBlockEndpointEvent (a ε : ℝ) (i : Fin 7) :
    Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
  Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
    (-a) a ((blockEndpointShift i - 1) * ε * a)
      ((blockEndpointShift i + 1) * ε * a)

/-- Probability of one prescribed endpoint window on the first block of a
uniform partition. Keeping this abbreviation separate avoids unfolding the
path event while selecting a term from the finite infimum. -/
private def rationalBlockEndpointProbability
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (blocks : ℕ) (hblocks : 0 < blocks) (a ε : ℝ) (i : Fin 7) : ENNReal :=
  P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks
    ⟨0, hblocks⟩ s ω) ⁻¹' rationalBlockEndpointEvent a ε i)

/-- Five disjoint endpoint bins cover the invariant core `(-2d,2d)`. -/
def blockEndpointBin (d : ℝ) (i : Fin 5) : Set ℝ :=
  Set.Ioo (-2 * d) (2 * d) ∩
    Set.Ioc (((i.val : ℝ) - 5 / 2) * d) (((i.val : ℝ) - 3 / 2) * d)

private theorem mem_blockEndpointBin_iff {d x : ℝ} (i : Fin 5) :
    x ∈ blockEndpointBin d i ↔
      -2 * d < x ∧ x < 2 * d ∧
        (((i.val : ℝ) - 5 / 2) * d < x ∧
          x ≤ ((i.val : ℝ) - 3 / 2) * d) := by
  change x ∈ Set.Ioo (-2 * d) (2 * d) ∩
    Set.Ioc (((i.val : ℝ) - 5 / 2) * d) (((i.val : ℝ) - 3 / 2) * d) ↔ _
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hwindow⟩
    exact ⟨hlo, hhi, hwindow⟩
  · rintro ⟨hlo, hhi, hwindow⟩
    exact ⟨⟨hlo, hhi⟩, hwindow⟩

private theorem blockEndpointBin_measurable (d : ℝ) (i : Fin 5) :
    MeasurableSet (blockEndpointBin d i) := by
  exact measurableSet_Ioo.inter measurableSet_Ioc

private theorem blockEndpointBin_disjoint (d : ℝ) :
    Pairwise (fun i j : Fin 5 => Disjoint (blockEndpointBin d i)
      (blockEndpointBin d j)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hxi' := (mem_blockEndpointBin_iff i).mp hxi
  have hxj' := (mem_blockEndpointBin_iff j).mp hxj
  have hd : 0 < d := by nlinarith [hxi'.1, hxi'.2.1]
  have hij' : i.val < j.val ∨ j.val < i.val := by omega
  rcases hij' with hlt | hlt
  · have hindex : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    have hstep : ((i.val : ℝ) - 3 / 2) * d ≤
        ((j.val : ℝ) - 5 / 2) * d := by
      nlinarith
    have hcontr : ((i.val : ℝ) - 3 / 2) * d < x :=
      lt_of_le_of_lt hstep hxj'.2.2.1
    exact (not_lt_of_ge hxi'.2.2.2) hcontr
  · have hindex : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    have hstep : ((j.val : ℝ) - 3 / 2) * d ≤
        ((i.val : ℝ) - 5 / 2) * d := by
      nlinarith
    have hcontr : ((j.val : ℝ) - 3 / 2) * d < x :=
      lt_of_le_of_lt hstep hxi'.2.2.1
    exact (not_lt_of_ge hxj'.2.2.2) hcontr

private theorem blockEndpointBin_cover {d : ℝ} (hd : 0 < d) :
    Set.Ioo (-2 * d) (2 * d) ⊆ ⋃ i : Fin 5, blockEndpointBin d i := by
  intro x hx
  by_cases h₀ : x ≤ -(3 / 2) * d
  · refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
    apply (mem_blockEndpointBin_iff ⟨0, by omega⟩).2
    constructor
    · exact hx.1
    constructor
    · exact hx.2
    constructor
    · nlinarith [hx.1, hd]
    · simpa using h₀
  · by_cases h₁ : x ≤ -(1 / 2) * d
    · refine Set.mem_iUnion.mpr ⟨⟨1, by omega⟩, ?_⟩
      apply (mem_blockEndpointBin_iff ⟨1, by omega⟩).2
      constructor
      · exact hx.1
      constructor
      · exact hx.2
      constructor <;> norm_num at * <;> nlinarith [hd]
    · by_cases h₂ : x ≤ (1 / 2) * d
      · refine Set.mem_iUnion.mpr ⟨⟨2, by omega⟩, ?_⟩
        apply (mem_blockEndpointBin_iff ⟨2, by omega⟩).2
        constructor
        · exact hx.1
        constructor
        · exact hx.2
        constructor <;> norm_num at * <;> nlinarith [hd]
      · by_cases h₃ : x ≤ (3 / 2) * d
        · refine Set.mem_iUnion.mpr ⟨⟨3, by omega⟩, ?_⟩
          apply (mem_blockEndpointBin_iff ⟨3, by omega⟩).2
          constructor
          · exact hx.1
          constructor
          · exact hx.2
          constructor <;> norm_num at * <;> nlinarith [hd]
        · refine Set.mem_iUnion.mpr ⟨⟨4, by omega⟩, ?_⟩
          apply (mem_blockEndpointBin_iff ⟨4, by omega⟩).2
          constructor
          · exact hx.1
          constructor
          · exact hx.2
          constructor <;> norm_num at * <;> nlinarith [hd]

set_option maxHeartbeats 1000000 in
/-- Seven endpoint windows produce a lower bound for a whole unit-time
corridor. The proof uses five endpoint bins, with no positivity assumption on
the minimum block probability. -/
theorem IsStableLevyProcess.iInf_sevenBlockEndpointProbability_pow_le_corridor
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    (⨅ i : Fin 7, P ((fun ω q => rationalUniformBlockProcessFromTime X
        hblocks ⟨0, hblocks⟩ q ω) ⁻¹' rationalBlockEndpointEvent a ε i)) ^ blocks ≤
      P (fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := by
  let d : ℝ := ε * a
  let coreLower : ℝ := -2 * d
  let coreUpper : ℝ := 2 * d
  let innerLower : ℝ := -(a * (1 + 2 * ε))
  let innerUpper : ℝ := a * (1 + 2 * ε)
  let V : Fin 5 → Set (↑RationalGrid.RationalUnitInterval → ℝ) :=
    fun i => rationalBlockEndpointEvent a ε ⟨i.val + 1, by omega⟩
  let blockProbability : Fin 7 → ENNReal :=
    rationalBlockEndpointProbability (X := X) (P := P) blocks hblocks a ε
  let q : ENNReal := ⨅ i : Fin 7, blockProbability i
  have hd : 0 < d := mul_pos hε ha
  have hcore : coreLower < 0 ∧ 0 < coreUpper := by
    constructor <;> dsimp [coreLower, coreUpper] <;> nlinarith
  have hzero : 1 ≤ P (rationalUniformPrefixCorridorReturnEvent X
      innerLower innerUpper coreLower coreUpper hblocks 0) := by
    simp [rationalUniformPrefixCorridorReturnEvent_zero, hcore]
  have hprefix : q ^ blocks ≤ P (rationalUniformPrefixCorridorReturnEvent X
      innerLower innerUpper coreLower coreUpper hblocks blocks) := by
    apply ProbabilityTheory.pow_le_measure_prefixCorridorReturn_of_steps
      (P := P) (X := X) blocks hblocks innerLower innerUpper coreLower coreUpper q
      hzero ?_
    intro j
    apply h.measure_prefixCorridorReturn_succ_ge_mul_of_glue
      blocks hblocks j innerLower innerUpper coreLower coreUpper
      (blockEndpointBin d) V q
    · exact blockEndpointBin_measurable d
    · intro i
      exact Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
        (-a) a
          ((blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * ε * a)
          ((blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * ε * a)
    · exact blockEndpointBin_disjoint d
    · intro ω hω
      exact Set.mem_iUnion.mp (blockEndpointBin_cover hd hω.2)
    · intro i
      have hlaw := h.rationalUniformBlockProcess_identDistrib blocks hblocks j
        ⟨0, hblocks⟩
      have hprob := hlaw.measure_mem_eq
        (Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
          (-a) a
          ((blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * ε * a)
          ((blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * ε * a))
      have hprob' : P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
          rationalBlockEndpointEvent a ε ⟨i.val + 1, by omega⟩) =
          blockProbability ⟨i.val + 1, by omega⟩ := by
        change P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
            rationalBlockEndpointEvent a ε ⟨i.val + 1, by omega⟩) =
          P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks
            ⟨0, hblocks⟩ s ω) ⁻¹'
              rationalBlockEndpointEvent a ε ⟨i.val + 1, by omega⟩)
        exact hprob
      have hle : q ≤ blockProbability ⟨i.val + 1, by omega⟩ := by
        exact iInf_le (fun k : Fin 7 => blockProbability k) ⟨i.val + 1, by omega⟩
      calc
        q ≤ blockProbability ⟨i.val + 1, by omega⟩ := hle
        _ = P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks
            j s ω) ⁻¹' rationalBlockEndpointEvent a ε ⟨i.val + 1, by omega⟩) := hprob'.symm
    · intro ω i hpast hbin hnext
      have hxcore : rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈
          Set.Ioo coreLower coreUpper := hpast.2
      have hxbin := (mem_blockEndpointBin_iff i).mp hbin
      have hlocal : (fun s => rationalUniformBlockProcessFromTime X hblocks j s ω) ∈
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (-a) a
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * ε * a)
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * ε * a) := by
        simpa [V, rationalBlockEndpointEvent] using hnext
      rcases hlocal with ⟨⟨margin, hmargin, hpath⟩, hend⟩
      have hblock : ∀ s : ↑RationalGrid.RationalUnitInterval,
          innerLower - coreLower <
              rationalTubeBlockIncrement hblocks j
                (fun t => X (rationalUnitTime t) ω) s ∧
            rationalTubeBlockIncrement hblocks j
                (fun t => X (rationalUnitTime t) ω) s < innerUpper - coreUpper := by
        intro s
        have hlocal' := hpath s
        constructor
        · have heq : innerLower - coreLower = -a := by
            simp [innerLower, coreLower, d]
            ring
          rw [heq]
          have hproc := hlocal'.1
          simpa [rationalUniformBlockProcessFromTime, rationalTubeBlockIncrement,
            rationalUniformBlockAbsoluteTime, rationalUnitTime_bot] using
              (show -a < rationalUniformBlockProcessFromTime X hblocks j s ω by
                linarith [hlocal'.1, hmargin])
        · have heq : innerUpper - coreUpper = a := by
            simp [innerUpper, coreUpper, d]
            ring
          rw [heq]
          have hproc := hlocal'.2
          simpa [rationalUniformBlockProcessFromTime, rationalTubeBlockIncrement,
            rationalUniformBlockAbsoluteTime, rationalUnitTime_bot] using
              (show rationalUniformBlockProcessFromTime X hblocks j s ω < a by
                linarith [hlocal'.2, hmargin])
      have hnew := rationalUniformBlockProcess_corridor_of_prefix_bin X hblocks j ω
        innerLower innerUpper coreLower coreUpper
        (le_of_lt hxcore.1) (le_of_lt hxcore.2) hblock
      have hreturn : rationalUniformPrefixPath X blocks (j.val + 1)
          hblocks ω ⊤ ∈ Set.Ioo coreLower coreUpper := by
        have hxwindow : rationalUniformBlockProcessFromTime X hblocks j ⊤ ω ∈
            Set.Ioc
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * ε * a)
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * ε * a) := hend
        have hshiftLo :
            ((i.val : ℝ) - 5 / 2) * d +
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * d) =
                -(3 / 2) * d := by
          rw [show blockEndpointShift ⟨i.val + 1, by omega⟩ =
              2 - (i.val : ℝ) by
                change 3 - ((i.val + 1 : ℕ) : ℝ) = _
                push_cast
                ring]
          ring
        have hshiftHi :
            ((i.val : ℝ) - 3 / 2) * d +
              ((blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * d) =
                (3 / 2) * d := by
          rw [show blockEndpointShift ⟨i.val + 1, by omega⟩ =
              2 - (i.val : ℝ) by
                change 3 - ((i.val + 1 : ℕ) : ℝ) = _
                push_cast
                ring]
          ring
        rw [rationalUniformPrefixPath_top_succ]
        have hendEq : rationalTubeBlockIncrement hblocks j
            (fun t => X (rationalUnitTime t) ω) ⊤ =
            rationalUniformBlockProcessFromTime X hblocks j ⊤ ω := rfl
        rw [hendEq]
        constructor
        · have hlo := hxbin.2.2.1
          have hwin :
              (blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * d <
                rationalUniformBlockProcessFromTime X hblocks j ⊤ ω := by
            rw [show (blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * ε * a =
              (blockEndpointShift ⟨i.val + 1, by omega⟩ - 1) * d by ring] at hxwindow
            exact hxwindow.1
          change -2 * d < _
          nlinarith [hwin, hxbin.2.2.1, hshiftLo, hd]
        · have hhi := hxbin.2.2.2
          have hwin :
              rationalUniformBlockProcessFromTime X hblocks j ⊤ ω ≤
                (blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * d := by
            rw [show (blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * ε * a =
              (blockEndpointShift ⟨i.val + 1, by omega⟩ + 1) * d by ring] at hxwindow
            exact hxwindow.2
          change _ < 2 * d
          nlinarith [hwin, hxbin.2.2.2, hshiftHi, hd]
      change ω ∈ rationalUniformPrefixCorridorEvent X innerLower innerUpper
          hblocks (j.val + 1) ∧
        rationalUniformPrefixPath X blocks (j.val + 1) hblocks ω ⊤ ∈
          Set.Ioo coreLower coreUpper
      rw [rationalUniformPrefixCorridorEvent_succ X innerLower innerUpper hblocks j]
      exact ⟨⟨hpast.1, hnew⟩, hreturn⟩
  have hmargin : 0 < 2 * ε * a := by positivity
  have htarget :
      P (rationalUniformPrefixCorridorReturnEvent X innerLower innerUpper
        coreLower coreUpper hblocks blocks) ≤
      P (fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := by
    apply measure_mono_ae
    filter_upwards [h.ae_cadlag] with ω hcadlag hω
    have hcoords := rationalUniformPrefixCorridorEvent_full_positions X hblocks
      innerLower innerUpper ω hω.1
    obtain ⟨m, hmpos, hm⟩ := exists_rat_btwn hmargin
    have hrat :
        (fun q => X (rationalUnitTime q) ω - X 0 ω) ∈
          Skorokhod.rationalCoordinateCorridorWithMargin
            (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) := by
      refine ⟨m, hmpos, ?_⟩
      intro q
      have hq := Set.mem_iInter.mp hcoords q
      rcases hq with ⟨hlo, hhi⟩
      constructor
      · dsimp [innerLower] at hlo
        nlinarith [hm, hlo]
      · dsimp [innerUpper] at hhi
        nlinarith [hm, hhi]
    have hrat' :
        (fun q => X (0 + 1 * rationalUnitTime q) ω - X 0 ω) ∈
          Skorokhod.rationalCoordinateCorridorWithMargin
            (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) := by
      simpa using hrat
    have hfull := (mem_fullSegmentCorridorEvent_iff_rational X 0 1
      (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) ω hcadlag).2 hrat'
    simpa [segmentIncrement, rationalUnitTime_bot, one_mul, zero_add] using hfull
  calc
    _ = q ^ blocks := rfl
    _ ≤ P (rationalUniformPrefixCorridorReturnEvent X
        innerLower innerUpper coreLower coreUpper hblocks blocks) := hprefix
    _ ≤ P (fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := htarget

set_option maxHeartbeats 2000000 in
/-- The seven endpoint windows give the return bound at an arbitrary
horizon `c`, with the source exponent `⌊c⁻¹⌋₊ + 1`. We run exactly that
many `c`-length blocks, then restrict the longer corridor to `[0,1]`. -/
theorem IsStableLevyProcess.iInf_sevenBlockEndpointProbability_pow_le_corridor_of_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a ε c : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (⨅ i : Fin 7, P (fullSegmentCorridorIocReturnEvent X 0
      ⟨c, hc.le⟩ (-a) a
      ((blockEndpointShift i - 1) * ε * a)
      ((blockEndpointShift i + 1) * ε * a))) ^
        (⌊c⁻¹⌋₊ + 1) ≤
      P (fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := by
  let blocks : ℕ := ⌊c⁻¹⌋₊ + 1
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc1
  have hblocks : 0 < blocks := by
    dsimp [blocks]
    omega
  have hblocksReal : 0 < (blocks : ℝ) := Nat.cast_pos.mpr hblocks
  have hfloorLt : c⁻¹ < (blocks : ℝ) := by
    dsimp [blocks]
    exact_mod_cast Nat.lt_floor_add_one (c⁻¹)
  have hlongReal : 1 < c * (blocks : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hfloorLt hc
    have hinv : c⁻¹ * c = 1 := by field_simp
    nlinarith
  let long : ℝ≥0 := ⟨c * (blocks : ℝ), by positivity⟩
  have hlongPos : 0 < long := by
    apply NNReal.coe_pos.mp
    change 0 < c * (blocks : ℝ)
    positivity
  have hlong : 1 ≤ long := by
    apply NNReal.coe_le_coe.mp
    change (1 : ℝ) ≤ c * (blocks : ℝ)
    exact le_of_lt hlongReal
  have hboundary :
      (rationalUniformBlockBoundary blocks 1 hblocks : ℝ) =
        1 / (blocks : ℝ) := by
    simp [rationalUniformBlockBoundary]
    rfl
  have htimeReal :
      (long : ℝ) * (rationalUniformBlockBoundary blocks 1 hblocks : ℝ) = c := by
    rw [show (long : ℝ) = c * (blocks : ℝ) by rfl, hboundary]
    field_simp [ne_of_gt hblocksReal]
  have htime : long * rationalUniformBlockBoundary blocks 1 hblocks =
      (⟨c, hc.le⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    exact htimeReal
  have hα : 0 < α := h.increments.strictlyStable.1
  let scale : ℝ := (long : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hlongPos) _
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    scale * X (long * t) ω
  have hY : IsStableLevyProcess α μ Y P := h.timeSpaceScale long hlongPos
  have hascale : 0 < scale * a := mul_pos hscale ha
  have hmain := hY.iInf_sevenBlockEndpointProbability_pow_le_corridor
    blocks hblocks (scale * a) ε hascale hε
  let τ : ℝ≥0 := ⟨c, hc.le⟩
  let core (i : Fin 7) : ℝ × ℝ :=
    (((blockEndpointShift i - 1) * ε * a),
      ((blockEndpointShift i + 1) * ε * a))
  let pLong : Fin 7 → ENNReal := fun i =>
    P ((fun ω q => rationalUniformBlockProcessFromTime Y hblocks
      ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalBlockEndpointEvent (scale * a) ε i)
  let pShort : Fin 7 → ENNReal := fun i =>
    P (fullSegmentCorridorIocReturnEvent X 0 τ (-a) a
      (core i).1 (core i).2)
  have hfirst := rationalUniformBlockProcess_zero_eq_initial Y hblocks
  have hprocess :
      (fun ω q => rationalUniformBlockProcessFromTime Y hblocks
        ⟨0, hblocks⟩ q ω) =
      (fun ω q => scale *
        (X (τ * rationalUnitTime q) ω - X 0 ω)) := by
    rw [hfirst]
    funext ω q
    simp only [Y]
    have htimeQ : long * (rationalUniformBlockBoundary blocks 1 hblocks *
        rationalUnitTime q) =
          τ * rationalUnitTime q := by
      rw [← mul_assoc, htime]
    rw [htimeQ]
    simp
    ring
  have hprob : ∀ i : Fin 7, pLong i = pShort i := by
    intro i
    have hset :
        (fun ω q => rationalUniformBlockProcessFromTime Y hblocks
          ⟨0, hblocks⟩ q ω) ⁻¹'
          rationalBlockEndpointEvent (scale * a) ε i =
        (fun ω q => X (τ * rationalUnitTime q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (-a) a
            ((blockEndpointShift i - 1) * ε * a)
            ((blockEndpointShift i + 1) * ε * a) := by
      ext ω
      rw [hprocess]
      have hm :=
        Skorokhod.mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff
          scale hscale
          (fun q => X (τ * rationalUnitTime q) ω - X 0 ω)
          (-(scale * a)) (scale * a)
          ((blockEndpointShift i - 1) * ε * (scale * a))
          ((blockEndpointShift i + 1) * ε * (scale * a))
      simpa [rationalBlockEndpointEvent, mul_assoc, mul_left_comm, mul_comm,
        div_eq_mul_inv, hscale.ne'] using hm
    have hmeas := measure_fullSegmentCorridorIocReturnEvent_eq_rational
      P X 0 τ (-a) a (core i).1 (core i).2 h.ae_cadlag
    have hmeas' :
        P ((fun ω q => X (τ * rationalUnitTime q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (-a) a (core i).1 (core i).2) = pShort i := by
      simpa [pShort, τ, core, zero_add, mul_comm] using hmeas
    change P ((fun ω q => rationalUniformBlockProcessFromTime Y hblocks
      ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalBlockEndpointEvent (scale * a) ε i) = pShort i
    rw [hset, hmeas']
  have hInf : (⨅ i : Fin 7, pLong i) = (⨅ i : Fin 7, pShort i) :=
    iInf_congr hprob
  have hmain' : (⨅ i : Fin 7, pShort i) ^ blocks ≤
      P (fullSegmentCorridorEvent Y 0 1
        (-(scale * a * (1 + 4 * ε)))
        (scale * a * (1 + 4 * ε))) := by
    rw [← hInf]
    simpa [pLong, core] using hmain
  have hscaledSubset :
      fullSegmentCorridorEvent Y 0 1
        (-(scale * a * (1 + 4 * ε)))
        (scale * a * (1 + 4 * ε)) ⊆
      fullSegmentCorridorEvent X 0 long
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) := by
    intro ω hω
    rcases hω with ⟨margin, hmargin, hpath⟩
    refine ⟨margin / scale, div_pos hmargin hscale, ?_⟩
    intro t
    have hpathEq : segmentIncrement Y 0 1 ω t =
        scale * segmentIncrement X 0 long ω t := by
      simp [segmentIncrement, Y]
      ring
    have hp := hpath t
    rw [hpathEq] at hp
    have hmarginEq : scale * (margin / scale) = margin :=
      mul_div_cancel₀ margin hscale.ne'
    constructor
    · apply le_of_mul_le_mul_left ?_ hscale
      have hscaled : scale * (-(a * (1 + 4 * ε)) + margin / scale) ≤
          scale * segmentIncrement X 0 long ω t := by
        rw [mul_add, hmarginEq]
        convert hp.1 using 1
        ring
      exact hscaled
    · apply le_of_mul_le_mul_left ?_ hscale
      have hscaled : scale * segmentIncrement X 0 long ω t ≤
          scale * (a * (1 + 4 * ε) - margin / scale) := by
        rw [mul_sub, hmarginEq]
        convert hp.2 using 1
        ring
      exact hscaled
  have hshortSubset :
      fullSegmentCorridorEvent X 0 long
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) ⊆
      fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε)) :=
    fullSegmentCorridorEvent_mono_length X 0 1 long hlongPos hlong _ _
  calc
    _ = (⨅ i : Fin 7, pShort i) ^ blocks := by
      simp [blocks, pShort, core, τ]
    _ ≤ P (fullSegmentCorridorEvent Y 0 1
        (-(scale * a * (1 + 4 * ε)))
        (scale * a * (1 + 4 * ε))) := hmain'
    _ ≤ P (fullSegmentCorridorEvent X 0 long
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := measure_mono hscaledSubset
    _ ≤ P (fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) := measure_mono hshortSubset

end ProbabilityTheory

end
