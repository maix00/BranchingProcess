import Probability.Process.Stable.SmallDeviation.BlockBounds
import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Strict
import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.AllIndices
import Probability.Process.Stable.SmallDeviation.RangeComparison
import Probability.Process.Stable.SmallDeviation.RationalTube
import Probability.Process.Corridor.Range

/-!
# Stable-process escape rates

The escape rate is derived from the finite-window lower bound and the
arbitrary-horizon range inequality. The centered corridor and range tube are
kept as distinct events throughout.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

/-- The normalized logarithmic probability of the full range tube. -/
noncomputable def stableRangeLogRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (α a : ℝ) : ℝ :=
  a ^ α * Real.log ((rationalRangeProbability P X a).toReal)

/-- The rational range event has positive probability at every positive width
under the source's two-sided stable-law condition. -/
theorem IsStableLevyProcess.rationalRangeProbability_pos_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) {a : ℝ} (ha : 0 < a) :
    0 < rationalRangeProbability P X a := by
  obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have hcenter : 0 < centeredCorridorProbability P X a := by
    dsimp [centeredCorridorProbability]
    exact h.measure_fullSegmentCorridor_pos (-a) a (by linarith) ha hpos hneg
  exact hcenter.trans_le (centeredCorridorProbability_le_rationalRangeProbability P X a)

private theorem rationalRangeProbability_le_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (a : ℝ) :
    rationalRangeProbability P X a ≤ 1 := by
  unfold rationalRangeProbability
  calc
    P (rationalHorizonTubeEvent X 1 (2 * a)) ≤ P Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

private theorem stableRangeLogRate_nonpos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) {α a : ℝ}
    (_hα : 0 ≤ α) (ha : 0 ≤ a) :
    stableRangeLogRate P X α a ≤ 0 := by
  have hprob := rationalRangeProbability_le_one P X a
  have hreal : (rationalRangeProbability P X a).toReal ≤ 1 := by
    have h := (ENNReal.toReal_le_toReal (measure_lt_top P _).ne ENNReal.one_ne_top).mpr hprob
    simpa [rationalRangeProbability] using h
  unfold stableRangeLogRate
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ha α)
    (Real.log_nonpos (ENNReal.toReal_nonneg) hreal)

private theorem tendsto_of_fixed_reference_scale
    {g : ℝ → ℝ} {S : Set ℝ} {l : Filter ℝ} {scale : ℝ → ℝ → ℝ}
    (hne : (g '' S).Nonempty) (hbounded : BddBelow (g '' S))
    (hdomain : ∀ᶠ a in l, a ∈ S)
    (hscale : ∀ b ∈ S, Tendsto (scale b) l (𝓝 1))
    (hcompare : ∀ b ∈ S, ∀ᶠ a in l, g a ≤ scale b a * g b) :
    Tendsto g l (𝓝 (sInf (g '' S))) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro x hx
    have hle : ∀ᶠ a in l, sInf (g '' S) ≤ g a := by
      filter_upwards [hdomain] with a ha
      exact csInf_le hbounded ⟨a, ha, rfl⟩
    filter_upwards [hle] with a ha
    exact lt_of_lt_of_le hx ha
  · intro x hx
    have hmem : ∃ y ∈ g '' S, y < x :=
      exists_lt_of_csInf_lt hne hx
    rcases hmem with ⟨y, ⟨b, hb, rfl⟩, hbx⟩
    have hproduct : Tendsto (fun a => scale b a * g b) l (𝓝 (g b)) := by
      simpa using (hscale b hb).mul_const (g b)
    filter_upwards [hcompare b hb, hproduct.eventually_lt_const hbx] with a hga hlt
    exact lt_of_le_of_lt hga hlt

private noncomputable def rangeScaleFactor (α b a : ℝ) : ℝ :=
  a ^ α * (⌊(b / a) ^ α⌋₊ : ℝ) / b ^ α

/-- The normalized logarithmic probability of the centered full-path
corridor. -/
noncomputable def stableCenteredLogRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (α a : ℝ) : ℝ :=
  a ^ α * Real.log ((centeredCorridorProbability P X a).toReal)

/-- Probability of the full-segment corridor translated by `d * a`. -/
def shiftedCorridorProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (d a : ℝ) : ℝ≥0∞ :=
  P (fullSegmentCorridorEvent X 0 1 (a * (d - 1)) (a * (d + 1)))

/-- The normalized logarithmic probability of a translated corridor. -/
noncomputable def stableShiftedCorridorLogRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (α d a : ℝ) : ℝ :=
  a ^ α * Real.log ((shiftedCorridorProbability P X d a).toReal)

private theorem tendsto_rangeScaleFactor
    {α b : ℝ} (hα : 0 < α) (hb : 0 < b) :
    Tendsto (rangeScaleFactor α b) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let l := 𝓝[>] (0 : ℝ)
  have hsmall : Tendsto (fun a : ℝ => a ^ (-α)) l atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hα)
  have hproduct : Tendsto (fun a : ℝ => b ^ α * a ^ (-α)) l atTop :=
    hsmall.const_mul_atTop (Real.rpow_pos_of_pos hb α)
  have hargument : Tendsto (fun a : ℝ => (b / a) ^ α) l atTop := by
    apply hproduct.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    rw [div_eq_mul_inv, Real.mul_rpow hb.le (inv_nonneg.mpr ha'.le),
      Real.inv_rpow ha'.le, ← Real.rpow_neg ha'.le α]
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument
  have hfactorEq : ∀ᶠ a : ℝ in l,
      rangeScaleFactor α b a =
        (⌊(b / a) ^ α⌋₊ : ℝ) / ((b / a) ^ α) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hp : 0 < a ^ α := Real.rpow_pos_of_pos ha' α
    have hx : 0 < (b / a) ^ α := Real.rpow_pos_of_pos (div_pos hb ha') α
    have hmulBase : a * (b / a) = b := by
      field_simp [ha'.ne']
    have hmul : a ^ α * (b / a) ^ α = b ^ α := by
      rw [← Real.mul_rpow ha'.le (div_nonneg hb.le ha'.le), hmulBase]
    dsimp [rangeScaleFactor]
    rw [← hmul]
    field_simp [hp.ne', hx.ne']
  apply hfloor.congr'
  filter_upwards [hfactorEq] with a ha
  exact ha.symm

private def referenceEndpointProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (i : Fin 7) : ℝ≥0∞ :=
  P (fullSegmentCorridorIocReturnEvent X 0 1 (-1) 1
    ((blockEndpointShift i - 1) * (1 / 16))
    ((blockEndpointShift i + 1) * (1 / 16)))

private theorem referenceEndpointProbability_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) (i : Fin 7) :
    0 < referenceEndpointProbability P X i := by
  have hi : |blockEndpointShift i| ≤ 3 := by
    fin_cases i <;> norm_num [blockEndpointShift]
  have hb : -1 < -(blockEndpointShift i * (1 / 16)) ∧
      -(blockEndpointShift i * (1 / 16)) < 1 := by
    have hi' : -3 ≤ blockEndpointShift i ∧ blockEndpointShift i ≤ 3 :=
      abs_le.mp hi
    constructor <;> nlinarith [hi'.1, hi'.2]
  have hε : 0 < (1 / 16 : ℝ) := by norm_num
  have hp := h.measure_sourceEntrance_pos_of_cdfAtZero_allIndices
    hcdf (-(blockEndpointShift i * (1 / 16))) 0 (1 / 16) hb
    (by norm_num) hε
  have hlower : (blockEndpointShift i - 1) * (1 / 16) =
      0 - -(blockEndpointShift i * (1 / 16)) - (1 / 16) := by ring_nf
  have hupper : (blockEndpointShift i + 1) * (1 / 16) =
      0 - -(blockEndpointShift i * (1 / 16)) + (1 / 16) := by ring_nf
  have heq :
      fullSegmentCorridorIocReturnEvent X 0 1 (-1) 1
        ((blockEndpointShift i - 1) * (1 / 16))
        ((blockEndpointShift i + 1) * (1 / 16)) =
      fullSegmentCorridorEvent X 0 1 (-1) 1 ∩
        {ω | 0 - -(blockEndpointShift i * (1 / 16)) - (1 / 16) <
            segmentIncrement X 0 1 ω ⊤ ∧
          segmentIncrement X 0 1 ω ⊤ ≤
            0 - -(blockEndpointShift i * (1 / 16)) + (1 / 16)} := by
    ext ω
    simp only [fullSegmentCorridorIocReturnEvent,
      segmentCorridorEndpointEvent, Set.mem_inter_iff,
      Set.mem_Ioc, Set.mem_ofPred_eq]
    rw [hlower, hupper]
  unfold referenceEndpointProbability
  rw [heq]
  simpa using hp

private theorem referenceEndpointProbability_lt_one
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (_h : IsStableLevyProcess α μ X P)
    (_hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) (i : Fin 7) :
    referenceEndpointProbability P X i ≤ 1 := by
  exact le_trans (measure_mono (Set.subset_univ _)) (by simp)

/-- The seven endpoint windows in relation (24) have a common positive
reference probability. -/
private noncomputable def stableEndpointBase
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  (referenceEndpointProbability P X ⟨0, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨1, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨2, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨3, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨4, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨5, by omega⟩ ⊓
   referenceEndpointProbability P X ⟨6, by omega⟩) ⊓ (1 / 2 : ℝ≥0∞)

private theorem stableEndpointBase_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < stableEndpointBase P X := by
  have hp : ∀ i : Fin 7, 0 < referenceEndpointProbability P X i :=
    fun i => referenceEndpointProbability_pos h hcdf i
  have h0 := hp ⟨0, by omega⟩
  have h1 := hp ⟨1, by omega⟩
  have h2 := hp ⟨2, by omega⟩
  have h3 := hp ⟨3, by omega⟩
  have h4 := hp ⟨4, by omega⟩
  have h5 := hp ⟨5, by omega⟩
  have h6 := hp ⟨6, by omega⟩
  have h01 := lt_min h0 h1
  have h012 := lt_min h01 h2
  have h0123 := lt_min h012 h3
  have h01234 := lt_min h0123 h4
  have h012345 := lt_min h01234 h5
  have h0123456 := lt_min h012345 h6
  have hhalf : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) := by norm_num
  unfold stableEndpointBase
  simpa only [min_assoc] using lt_min h0123456 hhalf

/-- The completed seven-window return estimate and stable scaling give a
uniform exponential lower bound for every sufficiently small centered
corridor width. -/
theorem IsStableLevyProcess.exists_centeredCorridor_exponential_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ M : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 →
      M ≤ a ^ α * Real.log
        ((centeredCorridorProbability P X a).toReal) := by
  let ε : ℝ := 1 / 16
  let A : ℝ := 1 + 4 * ε
  let q : ℝ≥0∞ := stableEndpointBase P X
  have hα : 0 < α := h.increments.strictlyStable.1
  have hε : 0 < ε := by norm_num [ε]
  have hA : A = 5 / 4 := by norm_num [A, ε]
  have hApos : 0 < A := by rw [hA]; norm_num
  have hqpos : 0 < q := by
    exact stableEndpointBase_pos h hcdf
  have hqlehalf : q ≤ (1 / 2 : ℝ≥0∞) := by
    simp [q, stableEndpointBase]
  have hq_lt_top : q < ∞ := lt_of_le_of_lt hqlehalf (by simp)
  have hqfinite : q ≠ ∞ := hq_lt_top.ne
  have hqrealpos : 0 < q.toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hqpos, hq_lt_top⟩
  have hqrealle : q.toReal ≤ (1 / 2 : ℝ) := by
    have hle := (ENNReal.toReal_le_toReal hqfinite (by norm_num)).mpr hqlehalf
    simpa using hle
  have hqlog : Real.log q.toReal < 0 :=
    Real.log_neg hqrealpos (lt_of_le_of_lt hqrealle (by norm_num))
  refine ⟨(A ^ α + 1) * Real.log q.toReal, ?_⟩
  intro a ha ha1
  let u : ℝ := a / A
  let c : ℝ := u ^ α
  let cNN : ℝ≥0 := ⟨c, (Real.rpow_pos_of_pos (div_pos ha hApos) α).le⟩
  let blocks : ℕ := ⌊c⁻¹⌋₊ + 1
  have hu : 0 < u := by dsimp [u]; exact div_pos ha hApos
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_iff₀ hApos]
    nlinarith
  have hcpos : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hu α
  have hcNN : 0 < cNN := by
    exact NNReal.coe_pos.mp (by dsimp [cNN]; exact hcpos)
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact Real.rpow_le_one hu.le hu1 hα.le
  have hscale : c ^ (-(1 / α)) = u⁻¹ := by
    dsimp [c]
    rw [← Real.rpow_mul hu.le]
    have hexp : α * (-(1 / α)) = -1 := by field_simp [hα.ne']
    rw [hexp, Real.rpow_neg_one]
  have hscaleNN : (cNN : ℝ) ^ (-(1 / α)) = u⁻¹ := by
    change c ^ (-(1 / α)) = u⁻¹
    exact hscale
  let shortProbability : Fin 7 → ℝ≥0∞ := fun i =>
    P (fullSegmentCorridorIocReturnEvent X 0 cNN (-u) u
      ((blockEndpointShift i - 1) * ε * u)
      ((blockEndpointShift i + 1) * ε * u))
  have hshortEq : ∀ i : Fin 7,
      shortProbability i = referenceEndpointProbability P X i := by
    intro i
    have hs := h.measure_fullSegmentCorridorIocReturn_scale cNN hcNN
      (-u) u ((blockEndpointShift i - 1) * ε * u)
      ((blockEndpointShift i + 1) * ε * u)
    rw [hscaleNN] at hs
    have hcancel (x : ℝ) : x * u * u⁻¹ = x := by
      field_simp [hu.ne']
    have hlower : -u * u⁻¹ = -1 := by
      rw [neg_mul, mul_inv_cancel₀ hu.ne']
    have hupper : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
    have hcoreLower : ((blockEndpointShift i - 1) * ε * u) * u⁻¹ =
        (blockEndpointShift i - 1) * ε := hcancel _
    have hcoreUpper : ((blockEndpointShift i + 1) * ε * u) * u⁻¹ =
        (blockEndpointShift i + 1) * ε := hcancel _
    rw [hlower, hupper, hcoreLower, hcoreUpper] at hs
    simpa [shortProbability, referenceEndpointProbability, ε] using hs
  have hInf : (⨅ i : Fin 7, shortProbability i) =
      (⨅ i : Fin 7, referenceEndpointProbability P X i) :=
    iInf_congr hshortEq
  have hbase_le (i : Fin 7) : q ≤ referenceEndpointProbability P X i := by
    change stableEndpointBase P X ≤ referenceEndpointProbability P X i
    fin_cases i <;> simp [stableEndpointBase]
  have hqinf : q ≤ ⨅ i : Fin 7, referenceEndpointProbability P X i :=
    le_iInf hbase_le
  have hblocksPos : 0 < blocks := by
    dsimp [blocks]
    omega
  have hpowerBound : a ^ α * (blocks : ℝ) ≤ A ^ α + 1 := by
    have hfloor : (blocks : ℝ) ≤ c⁻¹ + 1 := by
      dsimp [blocks]
      push_cast
      have hf := Nat.floor_le (show 0 ≤ c⁻¹ by positivity)
      linarith
    have haPow : 0 < a ^ α := Real.rpow_pos_of_pos ha α
    have haPowLe : a ^ α ≤ 1 := Real.rpow_le_one ha.le ha1 hα.le
    have hac : a ^ α * c⁻¹ = A ^ α := by
      have hau : A * u = a := by
        dsimp [u]
        field_simp [hApos.ne']
      rw [← hau, Real.mul_rpow hApos.le hu.le]
      dsimp [c]
      calc
        A ^ α * u ^ α * (u ^ α)⁻¹ = A ^ α * (u ^ α * (u ^ α)⁻¹) := by ring
        _ = A ^ α := by rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hu α).ne', mul_one]
    calc
      a ^ α * (blocks : ℝ) ≤ a ^ α * (c⁻¹ + 1) :=
        mul_le_mul_of_nonneg_left hfloor haPow.le
      _ = A ^ α + a ^ α := by rw [mul_add, hac]; ring
      _ ≤ A ^ α + 1 := by nlinarith [haPowLe]
  have hmain := h.iInf_sevenBlockEndpointProbability_pow_le_corridor_of_horizon
    u ε c hu hε hcpos hc1
  have hmainShort : (⨅ i : Fin 7, shortProbability i) ^ blocks ≤
      P (fullSegmentCorridorEvent X 0 1
        (-(u * (1 + 4 * ε))) (u * (1 + 4 * ε))) := by
    simpa [shortProbability, blocks] using hmain
  have hmain' : (⨅ i : Fin 7, shortProbability i) ^ blocks ≤
      centeredCorridorProbability P X a := by
    change (⨅ i : Fin 7, shortProbability i) ^ blocks ≤
      P (fullSegmentCorridorEvent X 0 1 (-a) a)
    have hwidth : u * (1 + 4 * ε) = a := by
      calc
        u * (1 + 4 * ε) = u * A := by simp [A]
        _ = a := by dsimp [u]; field_simp [hApos.ne']
    rw [← hwidth]
    exact hmainShort
  have hqshort : q ≤ ⨅ i : Fin 7, shortProbability i := by
    rw [hInf]
    exact hqinf
  have hprob : q ^ blocks ≤ centeredCorridorProbability P X a :=
    le_trans (pow_le_pow_left' hqshort blocks) hmain'
  have hreal : q.toReal ^ blocks ≤
      (centeredCorridorProbability P X a).toReal := by
    rw [← ENNReal.toReal_pow]
    exact (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hqfinite)
      (measure_lt_top P _).ne).mpr hprob
  have hlog : (blocks : ℝ) * Real.log q.toReal ≤
      Real.log ((centeredCorridorProbability P X a).toReal) := by
    have hpos : 0 < q.toReal ^ blocks := by positivity
    have hlog' := Real.log_le_log hpos hreal
    rw [Real.log_pow] at hlog'
    exact hlog'
  have hscaled := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le α)
  calc
    (A ^ α + 1) * Real.log q.toReal ≤
        (a ^ α * (blocks : ℝ)) * Real.log q.toReal := by
          exact mul_le_mul_of_nonpos_right hpowerBound hqlog.le
    _ ≤ a ^ α * Real.log ((centeredCorridorProbability P X a).toReal) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled

private theorem stableRangeLogRate_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ M : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 →
      M ≤ stableRangeLogRate P X α a := by
  obtain ⟨M, hM⟩ := h.exists_centeredCorridor_exponential_lower_bound hcdf
  refine ⟨M, fun a ha ha1 => ?_⟩
  obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have hcenterpos : 0 < centeredCorridorProbability P X a := by
    dsimp [centeredCorridorProbability]
    exact h.measure_fullSegmentCorridor_pos (-a) a (by linarith) ha hpos hneg
  have hmono := centeredCorridorProbability_le_rationalRangeProbability P X a
  have hreal : (centeredCorridorProbability P X a).toReal ≤
      (rationalRangeProbability P X a).toReal := by
    exact (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
      (measure_lt_top P _).ne).mpr hmono
  have hlog := Real.log_le_log
    (ENNReal.toReal_pos_iff.mpr ⟨hcenterpos, measure_lt_top P _⟩) hreal
  have hM' := hM a ha ha1
  unfold stableRangeLogRate
  change M ≤ a ^ α * Real.log
    ((centeredCorridorProbability P X a).toReal) at hM'
  exact hM'.trans (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le α))

/-- The range-tube form of relation (23), expressed directly in terms of its
half-width. -/
theorem IsStableLevyProcess.measure_rationalRangeProbability_le_pow_of_le
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    rationalRangeProbability P X a ≤
      (rationalRangeProbability P X b) ^ ⌊(b / a) ^ α⌋₊ := by
  have hα : 0 < α := h.increments.strictlyStable.1
  let ratio : ℝ := a / b
  let c : ℝ := ratio ^ α
  let cNN : ℝ≥0 := ⟨c, (Real.rpow_pos_of_pos (div_pos ha hb) α).le⟩
  have hratioPos : 0 < ratio := by dsimp [ratio]; exact div_pos ha hb
  have hratioLe : ratio ≤ 1 := by
    dsimp [ratio]
    rw [div_le_one hb]
    exact hab
  have hcPos : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hratioPos α
  have hcNN : 0 < cNN := by
    exact NNReal.coe_pos.mp (by dsimp [cNN]; exact hcPos)
  have hcLe : c ≤ 1 := by
    dsimp [c]
    exact Real.rpow_le_one hratioPos.le hratioLe hα.le
  have hratioInv : (a / b)⁻¹ = b / a := by
    field_simp [ha.ne', hb.ne']
  have hscale : c ^ (-(1 / α)) = b / a := by
    dsimp [c, ratio]
    rw [← Real.rpow_mul hratioPos.le]
    have hexp : α * (-(1 / α)) = -1 := by field_simp [hα.ne']
    rw [hexp, Real.rpow_neg_one]
    exact hratioInv
  have hscaleNN : (cNN : ℝ) ^ (-(1 / α)) = b / a := by
    change c ^ (-(1 / α)) = b / a
    exact hscale
  have hcinv : c⁻¹ = (b / a) ^ α := by
    have hmul : c * (b / a) ^ α = 1 := by
      dsimp [c, ratio]
      rw [← Real.mul_rpow hratioPos.le (div_nonneg hb.le ha.le)]
      have hratio : a / b * (b / a) = 1 := by
        field_simp [ha.ne', hb.ne']
      rw [hratio, Real.one_rpow]
    calc
      c⁻¹ = c⁻¹ * 1 := by rw [mul_one]
      _ = c⁻¹ * (c * (b / a) ^ α) := by rw [hmul]
      _ = (b / a) ^ α := by field_simp [hcPos.ne']
  have h23 := h.measure_rationalTube_le_pow_floor_inv_horizon
    a c ha hcPos hcLe
  have hscaleProb := h.rationalTube_timeSpaceScale_inv cNN hcNN (2 * a)
  rw [hscaleProb, hscaleNN, hcinv] at h23
  have hwidth : 2 * a * (b / a) = 2 * b := by
    field_simp [ha.ne']
  rw [hwidth] at h23
  simpa [rationalRangeProbability] using h23

private theorem stableRangeLogRate_le_scale_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    stableRangeLogRate P X α a ≤
      rangeScaleFactor α b a * stableRangeLogRate P X α b := by
  let n : ℕ := ⌊(b / a) ^ α⌋₊
  have hprob := h.measure_rationalRangeProbability_le_pow_of_le a b ha hb hab
  have hRaPos := h.rationalRangeProbability_pos_of_cdf hcdf ha
  have hRbPos := h.rationalRangeProbability_pos_of_cdf hcdf hb
  have hreal : (rationalRangeProbability P X a).toReal ≤
      (rationalRangeProbability P X b).toReal ^ n := by
    have hprob' : rationalRangeProbability P X a ≤
        (rationalRangeProbability P X b) ^ n := by simpa [n] using hprob
    have hreal' := (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
      (ENNReal.pow_ne_top (measure_lt_top P _).ne)).mpr hprob'
    simpa [rationalRangeProbability] using hreal'
  have hlog := Real.log_le_log
    (ENNReal.toReal_pos_iff.mpr ⟨hRaPos, measure_lt_top P _⟩) hreal
  rw [Real.log_pow] at hlog
  have haPow : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have hbPow : 0 < b ^ α := Real.rpow_pos_of_pos hb α
  have hmain := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le α)
  have hfactor : rangeScaleFactor α b a *
        (b ^ α * Real.log ((rationalRangeProbability P X b).toReal)) =
      a ^ α * (n : ℝ) * Real.log ((rationalRangeProbability P X b).toReal) := by
    dsimp [rangeScaleFactor, n]
    field_simp [hbPow.ne']
  unfold stableRangeLogRate
  calc
    a ^ α * Real.log ((rationalRangeProbability P X a).toReal) ≤
        a ^ α * ((n : ℝ) * Real.log ((rationalRangeProbability P X b).toReal)) := hmain
    _ = rangeScaleFactor α b a *
        (b ^ α * Real.log ((rationalRangeProbability P X b).toReal)) := by
          simpa [mul_assoc] using hfactor.symm

/-- Lemma 1(I) for the full range tube: the normalized log probability has a
finite strictly negative limit. -/
theorem IsStableLevyProcess.exists_rationalRange_escape_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  let g : ℝ → ℝ := stableRangeLogRate P X α
  let S : Set ℝ := Set.Ioc 0 1
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  obtain ⟨M, hM⟩ := stableRangeLogRate_lower_bound h hcdf
  have hnonempty : (g '' S).Nonempty := by
    refine ⟨g (1 / 2), ?_⟩
    exact ⟨1 / 2, by norm_num [S], rfl⟩
  have hbounded : BddBelow (g '' S) := by
    refine ⟨M, ?_⟩
    rintro y ⟨a, ha, rfl⟩
    exact hM a ha.1 ha.2
  have hdomain : ∀ᶠ a : ℝ in l, a ∈ S := by
    have hid : Tendsto id l (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hlt := hid.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with a ha hlt
    exact ⟨ha, le_of_lt hlt⟩
  have hscale : ∀ b ∈ S, Tendsto (rangeScaleFactor α b) l (𝓝 1) := by
    intro b hb
    exact tendsto_rangeScaleFactor h.increments.strictlyStable.1 hb.1
  have hcompare : ∀ b ∈ S, ∀ᶠ a : ℝ in l, g a ≤ rangeScaleFactor α b a * g b := by
    intro b hb
    have hid : Tendsto id l (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hlt := hid.eventually (Iio_mem_nhds hb.1)
    filter_upwards [self_mem_nhdsWithin, hlt] with a ha hlt
    exact stableRangeLogRate_le_scale_mul h hcdf ha hb.1 (le_of_lt hlt)
  let C : ℝ := sInf (g '' S)
  have hlim : Tendsto g l (𝓝 C) := by
    dsimp [C]
    exact tendsto_of_fixed_reference_scale hnonempty hbounded hdomain hscale hcompare
  obtain ⟨tail, htailPos, htail⟩ :=
    MeasureTheory.exists_positive_tail_threshold μ
      (h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf).2
  let b : ℝ := min (tail / 4) (1 / 2)
  have hbpos : 0 < b := by
    dsimp [b]
    exact lt_min (div_pos htailPos (by norm_num)) (by norm_num)
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact (min_le_right _ _).trans (by norm_num)
  have h2b : 2 * b ≤ tail := by
    dsimp [b]
    have hmin : min (tail / 4) (1 / 2) ≤ tail / 4 := min_le_left _ _
    nlinarith
  have htail2 : 0 < μ (Set.Ioi (2 * b)) := by
    apply lt_of_lt_of_le htail
    exact measure_mono (by intro x hx; exact lt_of_le_of_lt h2b hx)
  have hRlt : rationalRangeProbability P X b < 1 := by
    exact h.measure_rationalHorizonTube_lt_one_of_positive_tail (2 * b) htail2
  have hRpos := h.rationalRangeProbability_pos_of_cdf hcdf hbpos
  have hRrealpos : 0 < (rationalRangeProbability P X b).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hRpos, measure_lt_top P _⟩
  have hRreallt : (rationalRangeProbability P X b).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal (measure_lt_top P _).ne ENNReal.one_ne_top).mpr hRlt
  have hgb : g b < 0 := by
    dsimp [g, stableRangeLogRate]
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hbpos _)
      (Real.log_neg hRrealpos hRreallt)
  have hbmem : b ∈ S := ⟨hbpos, hb1⟩
  have hC_le : C ≤ g b := by
    exact csInf_le hbounded ⟨b, hbmem, rfl⟩
  refine ⟨C, lt_of_le_of_lt hC_le hgb, ?_⟩
  simpa [g, l] using hlim


end ProbabilityTheory

end
