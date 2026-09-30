module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Global
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.ShortTime
public import Probability.Process.Stable.SmallDeviation.Blocks.ReturnScale
import Mathlib.Order.CompleteLattice.Lemmas

/-!
# A concrete finite partition for returning corridor blocks

The two bins split the return core at zero. Unlike the abstract binning
theorem, endpoint coverage and all bin bounds are discharged here. A narrow
return core makes both translated block corridors contain the zero starting
point.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private def returnBin (coreLower coreUpper : ℝ) : Bool → Set ℝ
  | false => Set.Ioo coreLower 0
  | true => Set.Ico 0 coreUpper

private def returnBinLower (coreLower : ℝ) : Bool → ℝ
  | false => coreLower
  | true => 0

private def returnBinUpper (coreUpper : ℝ) : Bool → ℝ
  | false => 0
  | true => coreUpper

private theorem returnBin_measurable (coreLower coreUpper : ℝ) (i : Bool) :
    MeasurableSet (returnBin coreLower coreUpper i) := by
  cases i <;> simp [returnBin, measurableSet_Ioo, measurableSet_Ico]

private theorem returnBin_disjoint (coreLower coreUpper : ℝ) :
    Pairwise (fun i k => Disjoint (returnBin coreLower coreUpper i)
      (returnBin coreLower coreUpper k)) := by
  intro i k hik
  cases i <;> cases k
  · exact (hik rfl).elim
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy.1) hx.2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.1) hy.2
  · exact (hik rfl).elim

private theorem returnBin_bounds (coreLower coreUpper : ℝ) (i : Bool)
    (b : ℝ) (hb : b ∈ returnBin coreLower coreUpper i) :
    returnBinLower coreLower i ≤ b ∧ b ≤ returnBinUpper coreUpper i := by
  cases i with
  | false =>
      simp only [returnBin, Set.mem_Ioo, returnBinLower, returnBinUpper] at *
      exact ⟨le_of_lt hb.1, le_of_lt hb.2⟩
  | true =>
      simp only [returnBin, Set.mem_Ico, returnBinLower, returnBinUpper] at *
      exact ⟨hb.1, le_of_lt hb.2⟩

private theorem returnBin_cover (coreLower coreUpper : ℝ) :
    Set.Ioo coreLower coreUpper ⊆ ⋃ i : Bool, returnBin coreLower coreUpper i := by
  intro b hb
  by_cases h : b < 0
  · exact Set.mem_iUnion.mpr ⟨false, by simpa [returnBin] using And.intro hb.1 h⟩
  · exact Set.mem_iUnion.mpr ⟨true, by
      simpa [returnBin] using And.intro (le_of_not_gt h) hb.2⟩

/-- A concrete two-bin version of the stable block lower estimate. The two
block probabilities correspond to endpoints in the negative and nonnegative
halves of the return core. -/
theorem IsStableLevyProcess.min_two_blockProbabilities_pow_le_rationalHorizonTube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper) :
    (P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - coreLower) upper 0 coreUpper) ⊓
      P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          lower (upper - coreUpper) coreLower 0)) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  have hbound := h.iInf_blockProbability_pow_le_rationalHorizonTube_of_coreCover
    blocks hblocks lower upper extra hextra coreLower coreUpper hcore
    (returnBin coreLower coreUpper)
    (returnBinLower coreLower) (returnBinUpper coreUpper)
    (returnBin_measurable coreLower coreUpper)
    (returnBin_disjoint coreLower coreUpper)
    (returnBin_bounds coreLower coreUpper)
    (returnBin_cover coreLower coreUpper)
  simpa [iInf_bool_eq, inf_comm, returnBinLower, returnBinUpper] using hbound

/-- An interior margin turns both bin-specific next-block corridors into the
same centered path corridor. Only the sign of the return endpoint differs.
This reduces the analytic input for the block lower bound to two directional
short-block events. -/
theorem IsStableLevyProcess.min_directional_blockProbabilities_pow_le_rationalHorizonTube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper δ : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (hleft : lower ≤ coreLower - δ)
    (hright : coreUpper + δ ≤ upper) :
    (P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ⊓
      P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ coreLower 0)) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  have hplus : rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper ⊆
      rationalCoordinateCorridorReturn (lower - coreLower) upper 0 coreUpper := by
    apply rationalCoordinateCorridorReturn_mono <;> linarith [hcore.2]
  have hminus : rationalCoordinateCorridorReturn (-δ) δ coreLower 0 ⊆
      rationalCoordinateCorridorReturn lower (upper - coreUpper) coreLower 0 := by
    apply rationalCoordinateCorridorReturn_mono <;> linarith [hcore.1]
  have hmin :
      (P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
          ⟨0, hblocks⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ⊓
        P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
          ⟨0, hblocks⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ coreLower 0)) ≤
        (P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
          ⟨0, hblocks⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn (lower - coreLower) upper 0 coreUpper) ⊓
        P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
          ⟨0, hblocks⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn lower (upper - coreUpper) coreLower 0)) := by
    exact inf_le_inf (measure_mono (Set.preimage_mono hplus))
      (measure_mono (Set.preimage_mono hminus))
  exact (pow_le_pow_left₀ (by positivity) hmin blocks).trans
    (h.min_two_blockProbabilities_pow_le_rationalHorizonTube
      blocks hblocks lower upper extra hextra coreLower coreUpper hcore)

/-- The two directional probabilities in the block lower estimate are
unit-time stable-process probabilities in corridors scaled by the block
duration. This is the quantitative bridge between the finite-block gluing
argument and the stable time-space scaling law. -/
theorem IsStableLevyProcess.min_scaled_directional_probabilities_pow_le_rationalHorizonTube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper δ : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (hleft : lower ≤ coreLower - δ)
    (hright : coreUpper + δ ≤ upper) :
    let scale : ℝ :=
      ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
    (P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (-δ * scale) (δ * scale) 0 (coreUpper * scale)) ⊓
      P ((fun ω q => X (rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (-δ * scale) (δ * scale) (coreLower * scale) 0)) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  dsimp only
  have hbound := h.min_directional_blockProbabilities_pow_le_rationalHorizonTube
    blocks hblocks lower upper extra hextra coreLower coreUpper δ
    hcore hleft hright
  rw [h.firstBlock_corridorReturn_scale_inv blocks hblocks
      (-δ) δ 0 coreUpper,
    h.firstBlock_corridorReturn_scale_inv blocks hblocks
      (-δ) δ coreLower 0] at hbound
  simpa using hbound

/-- Two-sided stable increment mass and càdlàg paths imply positive mass for
every unit-time tube that admits an interior return core and spatial margin.
The proof uses a sufficiently fine finite block partition. -/
theorem IsStableLevyProcess.measure_rationalHorizonTube_pos_of_returnCore
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (lower upper extra coreLower coreUpper δ : ℝ)
    (hextra : 0 < extra) (hδ : 0 < δ)
    (hcoreLower : coreLower ≤ -δ) (hcoreUpper : δ ≤ coreUpper)
    (hleft : lower ≤ coreLower - δ)
    (hright : coreUpper + δ ≤ upper)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    0 < P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  obtain ⟨n, hn⟩ := (h.eventually_firstBlock_directionalReturn_probabilities_pos
    δ coreLower coreUpper hδ hcoreLower hcoreUpper hpos hneg).exists
  have hcore : coreLower < 0 ∧ 0 < coreUpper := by
    constructor <;> linarith
  have hmin :
      0 < (P ((fun ω q => rationalUniformBlockProcessFromTime X
          (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ⊓
        P ((fun ω q => rationalUniformBlockProcessFromTime X
          (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) ⁻¹'
          rationalCoordinateCorridorReturn (-δ) δ coreLower 0)) :=
    lt_min hn.1 hn.2
  exact (ENNReal.pow_pos hmin _).trans_le
    (h.min_directional_blockProbabilities_pow_le_rationalHorizonTube
      (n + 1) (Nat.succ_pos n) lower upper extra hextra
      coreLower coreUpper δ hcore hleft hright)

/-- Every positive-width unit-time rational range tube has positive
probability for a càdlàg stable process whose reference increment law has
positive mass on both sides of zero. -/
theorem IsStableLevyProcess.measure_rationalHorizonTube_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (width : ℝ) (hwidth : 0 < width)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    0 < P (rationalHorizonTubeEvent X 1 width) := by
  let a : ℝ := width / 3
  let δ : ℝ := a / 4
  have ha : 0 < a := by dsimp [a]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbound := h.measure_rationalHorizonTube_pos_of_returnCore
    (-a) a a (-δ) δ δ ha hδ le_rfl le_rfl
    (by dsimp [δ]; linarith)
    (by dsimp [δ]; linarith) hpos hneg
  convert hbound using 1
  dsimp [a]
  ring_nf

theorem IsStableLevyProcess.measure_rationalHorizonTube_pos_of_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (width : ℝ) (hwidth : 0 < width)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    0 < P (rationalHorizonTubeEvent X horizon width) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hunit := h.measure_rationalHorizonTube_pos
    (width * scale) (mul_pos hwidth hscale) hpos hneg
  have hscaleLaw := h.rationalTube_timeSpaceScale horizon hhorizon
    (width * scale)
  have hnormalize : width * scale / scale = width := by
    field_simp
  rw [hnormalize] at hscaleLaw
  simpa only [scale] using hscaleLaw ▸ hunit

end ProbabilityTheory
