module

public import Probability.Process.Corridor.Range
public import Probability.Process.Stable.SmallDeviation.ShiftedCorridor
public import Analysis.Asymptotics.LogSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Comparison of range and centered-corridor probabilities

This module proves the two logarithmic comparisons in Mogulskii's range
comparison. The range event is the rational-coordinate event of the original
process; almost-sure càdlàg paths connect it to full-segment corridors.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Probability of the centered full-segment corridor with half-width `a`. -/
def centeredCorridorProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1 (-a) a)

/-- Probability that the full path range has diameter strictly less than
`2 * a`, expressed through the rational coordinates of the original process. -/
def rationalRangeProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) : ℝ≥0∞ :=
  P (rationalHorizonTubeEvent X 1 (2 * a))

/-- Probability of the centered full-segment corridor enlarged by the factor
`1 + ε`. -/
def expandedCenteredCorridorProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (ε a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1 (-(1 + ε) * a) ((1 + ε) * a))

/-- The `j`th translated corridor in the finite range cover. -/
def rangeCoverCorridorProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (k j : ℕ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1
    (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
    (a * (((j : ℝ) / k - 1) + (1 + 2 / k))))

/-- The centered corridor of half-width `a` is contained in the range event
of total width `2a`. -/
theorem centeredCorridorProbability_le_rationalRangeProbability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) :
    centeredCorridorProbability P X a ≤ rationalRangeProbability P X a := by
  change P (fullSegmentCorridorEvent X 0 1 (-a) a) ≤
    P (rationalHorizonTubeEvent X 1 (2 * a))
  apply measure_mono
  simpa [two_mul] using
    fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent_exact X (-a) a

/-- A rational range event of width `2a` is contained almost surely in the
centered corridor of half-width `2a`. -/
theorem rationalRangeProbability_le_centeredCorridorProbability_double
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    rationalRangeProbability P X a ≤ centeredCorridorProbability P X (2 * a) := by
  change P (rationalHorizonTubeEvent X 1 (2 * a)) ≤
    P (fullSegmentCorridorEvent X 0 1 (-(2 * a)) (2 * a))
  apply measure_mono_ae
  filter_upwards [hcadlag] with ω hω
  exact mem_rationalHorizonTubeEvent_imp_fullSegmentCorridorEvent
    X (2 * a) ω hω

/-- The left range comparison in Lemma 2(b): its logarithmic ratio is
eventually at least one. -/
theorem IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ Real.log ((centeredCorridorProbability P X a).toReal) /
        Real.log ((rationalRangeProbability P X a).toReal) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let q : ℝ → ℝ≥0∞ := centeredCorridorProbability P X
  let r : ℝ → ℝ≥0∞ := rationalRangeProbability P X
  obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have hqpos : ∀ᶠ a : ℝ in l, 0 < q a := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    dsimp [q, centeredCorridorProbability]
    exact h.measure_fullSegmentCorridor_pos (-a) a (by linarith) ha' hpos hneg
  have hqr : ∀ a, q a ≤ r a := by
    intro a
    exact centeredCorridorProbability_le_rationalRangeProbability P X a
  have hrpos : ∀ᶠ a : ℝ in l, 0 < r a := by
    filter_upwards [hqpos] with a ha
    exact ha.trans_le (hqr a)
  have hrle : ∀ a, r a ≤ q (2 * a) := by
    intro a
    exact rationalRangeProbability_le_centeredCorridorProbability_double
      P X a h.ae_cadlag
  have hq2zero : Tendsto (fun a : ℝ => q (2 * a)) l (𝓝 0) := by
    simpa [q, centeredCorridorProbability, mul_assoc, mul_comm, mul_left_comm] using
      h.tendsto_measure_scaledFullCorridor_zero hpos (-2) 2
  have hq2realZero : Tendsto (fun a : ℝ => (q (2 * a)).toReal) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hq2zero
  have hrrealZero : Tendsto (fun a : ℝ => (r a).toReal) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hq2realZero
    · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
    · exact Eventually.of_forall fun a =>
        by
          have hbound := hrle a
          dsimp [r, q, rationalRangeProbability, centeredCorridorProbability] at hbound
          exact (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
            (measure_lt_top P _).ne).mpr hbound
  have hrrealPos : ∀ᶠ a : ℝ in l, 0 < (r a).toReal := by
    filter_upwards [hrpos] with a ha
    dsimp [r, rationalRangeProbability] at ha ⊢
    exact ENNReal.toReal_pos_iff.mpr ⟨ha, measure_lt_top P _⟩
  have hrrealGT : Tendsto (fun a : ℝ => (r a).toReal)
      l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrrealZero, hrrealPos⟩
  have hlogr : Tendsto (fun a : ℝ => Real.log ((r a).toReal)) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hrrealGT
  have hlogrNeg : ∀ᶠ a : ℝ in l, Real.log ((r a).toReal) < 0 :=
    hlogr.eventually (eventually_lt_atBot 0)
  have hqrealPos : ∀ᶠ a : ℝ in l, 0 < (q a).toReal := by
    filter_upwards [hqpos] with a ha
    dsimp [q, centeredCorridorProbability] at ha ⊢
    exact ENNReal.toReal_pos_iff.mpr ⟨ha, measure_lt_top P _⟩
  have hqrealLe : ∀ᶠ a : ℝ in l, (q a).toReal ≤ (r a).toReal := by
    filter_upwards [self_mem_nhdsWithin] with a _
    have hbound := hqr a
    dsimp [q, r, centeredCorridorProbability, rationalRangeProbability] at hbound
    exact (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
      (measure_lt_top P _).ne).mpr hbound
  filter_upwards [hlogrNeg, hqrealPos, hrrealPos, hqrealLe] with a hlogneg hqpos' hrpos' hqle
  have hlogle := Real.log_le_log hqpos' (by exact_mod_cast hqle : (q a).toReal ≤ (r a).toReal)
  exact (le_div_iff_of_neg hlogneg).2 (by simpa using hlogle)

/-- The right range comparison in Lemma 2(b). The finite translated cover is
normalized to the half-width-one form required by relation (21), then the
fixed finite-sum cost is absorbed at the diverging logarithmic scale. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤ Real.log ((rationalRangeProbability P X a).toReal) /
        Real.log ((expandedCenteredCorridorProbability P X ε a).toReal) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  obtain ⟨k, hkLarge⟩ := exists_nat_gt (2 / ε)
  have hkPosReal : 0 < (k : ℝ) := by
    exact lt_trans (by positivity) hkLarge
  have hkPos : 0 < k := Nat.cast_pos.mp hkPosReal
  have hProduct : 2 < ε * (k : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hkLarge
    nlinarith [h]
  have hGrid : 2 / (k : ℝ) < ε :=
    (div_lt_iff₀ hkPosReal).2 hProduct
  let scaleFactor : ℝ := 1 + 2 / k
  have hscaleFactor : 1 < scaleFactor := by
    dsimp [scaleFactor]
    have hdiv : 0 < 2 / (k : ℝ) := div_pos (by norm_num) hkPosReal
    linarith
  have hscaleFactorUpper : scaleFactor < 1 + ε := by
    dsimp [scaleFactor]
    linarith
  let ε' : ℝ := (1 + ε) / scaleFactor - 1
  have hε' : 0 < ε' := by
    dsimp [ε']
    rw [sub_pos]
    exact (lt_div_iff₀ (by linarith : 0 < scaleFactor)).2 (by nlinarith [hscaleFactorUpper])
  let F : Finset ℕ := Finset.range (2 * k + 1)
  have hF : 0 < F.card := by
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    simp [F]
  let center : ℕ → ℝ := fun j => (j : ℝ) / k - 1
  let b : ℕ → ℝ := fun j => center j / scaleFactor
  let η : ℝ := δ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let q : ℝ → ℝ := fun a => (rationalRangeProbability P X a).toReal
  let w : ℝ → ℝ := fun a =>
    Real.log ((expandedCenteredCorridorProbability P X ε a).toReal)
  let p : ℝ → ℕ → ℝ := fun a j =>
    (rangeCoverCorridorProbability P X a k j).toReal
  have hscale : Tendsto (fun a : ℝ => scaleFactor * a) l l := by
    have hzero : Tendsto (fun a : ℝ => scaleFactor * a) l (𝓝 0) := by
      have hid : Tendsto (fun a : ℝ => a) l (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hid)
    have hpositive : ∀ᶠ a : ℝ in l, 0 < scaleFactor * a := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact mul_pos (by linarith) ha
    exact tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hcenterBounds (j : ℕ) (hj : j ∈ F) :
      -1 ≤ center j ∧ center j ≤ 1 := by
    have hjNat : j ≤ 2 * k := by
      apply Nat.le_of_lt_succ
      simpa [F] using Finset.mem_range.mp hj
    have hjReal : (j : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hjNat
    have hdivNonneg : 0 ≤ (j : ℝ) / k :=
      div_nonneg (Nat.cast_nonneg _) hkPosReal.le
    have hdivUpper : (j : ℝ) / k ≤ 2 :=
      (div_le_iff₀ hkPosReal).2 (by nlinarith [hjReal])
    constructor <;> dsimp [center] <;> linarith
  have hb (j : ℕ) (hj : j ∈ F) : -1 < b j ∧ b j < 1 := by
    obtain ⟨hcenterLo, hcenterHi⟩ := hcenterBounds j hj
    constructor
    · dsimp [b]
      rw [lt_div_iff₀ (by linarith : 0 < scaleFactor)]
      have hnegscaleFactor : -scaleFactor < -1 := by linarith
      linarith
    · dsimp [b]
      rw [div_lt_iff₀ (by linarith : 0 < scaleFactor)]
      linarith
  have hwZero : Tendsto
      (fun a : ℝ => (expandedCenteredCorridorProbability P X ε a).toReal)
      l (𝓝 0) := by
    have hmeasure : Tendsto (fun a : ℝ =>
        expandedCenteredCorridorProbability P X ε a) l (𝓝 0) := by
      obtain ⟨_, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
      simpa [expandedCenteredCorridorProbability, mul_assoc, mul_comm,
        mul_left_comm] using
        h.tendsto_measure_scaledFullCorridor_zero hpos (-(1 + ε)) (1 + ε)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure
  have hwPositive : ∀ᶠ a : ℝ in l,
      0 < (expandedCenteredCorridorProbability P X ε a).toReal := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hprob : 0 < expandedCenteredCorridorProbability P X ε a := by
      dsimp [expandedCenteredCorridorProbability]
      apply h.measure_fullSegmentCorridor_pos_of_cdfAtZero
      · nlinarith
      · nlinarith
      · exact hcdf
    exact ENNReal.toReal_pos_iff.mpr ⟨hprob, measure_lt_top P _⟩
  have hwPositiveReal : ∀ᶠ a : ℝ in l, 0 <
      (expandedCenteredCorridorProbability P X ε a).toReal := hwPositive
  have hwWithin : Tendsto
      (fun a : ℝ => (expandedCenteredCorridorProbability P X ε a).toReal)
      l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hwZero, hwPositiveReal⟩
  have hwLog : Tendsto w l atBot := by
    change Tendsto (fun a : ℝ =>
      Real.log ((expandedCenteredCorridorProbability P X ε a).toReal)) l atBot
    exact Real.tendsto_log_nhdsGT_zero.comp hwWithin
  have hqPositive : ∀ᶠ a : ℝ in l, 0 < q a := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hprob : 0 < centeredCorridorProbability P X a := by
      dsimp [centeredCorridorProbability]
      obtain ⟨hneg, hpos⟩ :=
        h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
      exact h.measure_fullSegmentCorridor_pos (-a) a (by linarith) ha' hpos hneg
    dsimp [q]
    exact ENNReal.toReal_pos_iff.mpr ⟨
      hprob.trans_le (centeredCorridorProbability_le_rationalRangeProbability P X a),
      measure_lt_top P _⟩
  have hsum : ∀ᶠ a : ℝ in l, q a ≤ ∑ j ∈ F, p a j := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hcover := measure_rationalHorizonTube_le_sum_scaledFullSegmentCorridors
      P X a ha' k hkPos h.ae_cadlag
    have hsumNeTop : (∑ j ∈ F,
        P (fullSegmentCorridorEvent X 0 1
          (a * (((j : ℝ) / k - 1) - (1 + 2 / k)))
          (a * (((j : ℝ) / k - 1) + (1 + 2 / k))))) ≠ ∞ := by
      apply ENNReal.sum_ne_top.mpr
      intro j hj
      exact (measure_lt_top P _).ne
    have hcoverReal := (ENNReal.toReal_le_toReal
      (measure_lt_top P _).ne hsumNeTop).mpr hcover
    rw [ENNReal.toReal_sum (by
      intro j hj
      exact (measure_lt_top P _).ne)] at hcoverReal
    simpa only [q, p, rationalRangeProbability, rangeCoverCorridorProbability, F] using
      hcoverReal
  have hp : ∀ j ∈ F, ∀ᶠ a : ℝ in l, 0 < p a j := by
    intro j hj
    have ⟨hcenterLo, hcenterHi⟩ := hcenterBounds j hj
    have hlower : center j - scaleFactor < 0 := by linarith [hscaleFactor]
    have hupper : 0 < center j + scaleFactor := by linarith [hscaleFactor]
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hprob : 0 < rangeCoverCorridorProbability P X a k j := by
      dsimp [rangeCoverCorridorProbability]
      apply h.measure_fullSegmentCorridor_pos_of_cdfAtZero
      · dsimp [center] at hlower ⊢
        nlinarith
      · dsimp [center] at hupper ⊢
        nlinarith
      · exact hcdf
    dsimp [p]
    exact ENNReal.toReal_pos_iff.mpr ⟨hprob, measure_lt_top P _⟩
  have hlog : ∀ j ∈ F, ∀ᶠ a : ℝ in l,
      1 - η ≤ Real.log (p a j) / w a := by
    intro j hj
    let bj : ℝ := b j
    have hb' : -1 < bj ∧ bj < 1 := by simpa [bj] using hb j hj
    have h21 := h.eventually_one_sub_le_log_corridor_ratio_of_cdf hcdf
      bj 0 ε' hb' (by norm_num) hε' η hη
    have h21scaled := hscale.eventually h21
    filter_upwards [h21scaled] with a h21a
    have hleft : (scaleFactor * a) * (bj - 1) =
        a * (((j : ℝ) / k - 1) - scaleFactor) := by
      dsimp [bj, b, center, scaleFactor]
      field_simp [hkPosReal.ne']
    have hright : (scaleFactor * a) * (bj + 1) =
        a * (((j : ℝ) / k - 1) + scaleFactor) := by
      dsimp [bj, b, center, scaleFactor]
      field_simp [hkPosReal.ne']
    have hwideLower : (scaleFactor * a) * (0 - (1 + ε')) =
        -(1 + ε) * a := by
      dsimp [ε', scaleFactor]
      field_simp [hkPosReal.ne']
      ring
    have hwideUpper : (scaleFactor * a) * (0 + 1 + ε') =
        (1 + ε) * a := by
      dsimp [ε', scaleFactor]
      field_simp [hkPosReal.ne']
      ring
    have htermEq : rangeCoverCorridorProbability P X a k j =
        P (fullSegmentCorridorEvent X 0 1
          ((scaleFactor * a) * (bj - 1)) ((scaleFactor * a) * (bj + 1))) := by
      rw [rangeCoverCorridorProbability, hleft, hright]
    have hwideEq : expandedCenteredCorridorProbability P X ε a =
        P (fullSegmentCorridorEvent X 0 1
          ((scaleFactor * a) * (0 - (1 + ε'))) ((scaleFactor * a) * (0 + 1 + ε'))) := by
      rw [expandedCenteredCorridorProbability, hwideLower, hwideUpper]
    rw [← htermEq, ← hwideEq] at h21a
    simpa [p, w, η] using h21a
  have hresult :=
    Asymptotics.eventually_one_sub_eta_sub_delta_le_log_sum_ratio
      F hF w q p η (δ / 2) (by positivity) hwLog hqPositive hsum hp hlog
  filter_upwards [hresult] with a ha
  have ha' : 1 - δ ≤ Real.log (q a) / w a := by
    dsimp [η] at ha
    linarith
  simpa [q, w] using ha'

/-- The source's strict left-half-line mass condition is an equivalent public
entry for the right range comparison. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_range_div_log_corridor_of_measure_Iio_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤ Real.log ((rationalRangeProbability P X a).toReal) /
        Real.log ((expandedCenteredCorridorProbability P X ε a).toReal) := by
  exact h.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
    (h.increments.strictlyStable.cdfAtZero_condition_of_strictLeftMass hleft)
    ε hε δ hδ

/-- The left comparison also accepts the source's strict left-half-line mass
condition directly. -/
theorem IsStableLevyProcess.eventually_one_le_log_corridor_div_log_range_of_measure_Iio_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 ≤ Real.log ((centeredCorridorProbability P X a).toReal) /
        Real.log ((rationalRangeProbability P X a).toReal) := by
  exact h.eventually_one_le_log_corridor_div_log_range_of_cdf
    (h.increments.strictlyStable.cdfAtZero_condition_of_strictLeftMass hleft)

end ProbabilityTheory

end
