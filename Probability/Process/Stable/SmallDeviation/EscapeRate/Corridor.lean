import Probability.Process.Stable.SmallDeviation.EscapeRate
import Probability.Process.Stable.SmallDeviation.RangeComparison
import Probability.Process.Stable.SmallDeviation.ShiftedCorridor

/-!
# Centered and translated stable corridor escape rates

The centered and shifted corridor limits follow from the range escape rate and
Mogulskii's stable-process comparison inequalities.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

private theorem centeredCorridorProbability_pos_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) {a : ℝ} (ha : 0 < a) :
    0 < centeredCorridorProbability P X a := by
  obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  dsimp [centeredCorridorProbability]
  exact h.measure_fullSegmentCorridor_pos (-a) a (by linarith) ha hpos hneg

private theorem stableCenteredLogRate_le_range
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) {a : ℝ} (ha : 0 < a) :
    stableCenteredLogRate P X α a ≤ stableRangeLogRate P X α a := by
  have hqpos := centeredCorridorProbability_pos_of_cdf h hcdf ha
  have hrpos := h.rationalRangeProbability_pos_of_cdf hcdf ha
  have hprob := centeredCorridorProbability_le_rationalRangeProbability P X a
  have hreal : (centeredCorridorProbability P X a).toReal ≤
      (rationalRangeProbability P X a).toReal :=
    (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
      (measure_lt_top P _).ne).mpr hprob
  have hlog := Real.log_le_log
    (ENNReal.toReal_pos_iff.mpr ⟨hqpos, measure_lt_top P _⟩) hreal
  unfold stableCenteredLogRate stableRangeLogRate
  exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le _)

/-- The centered corridor has the same finite negative escape rate as the
range tube. This is the squeeze from relation (22), after the range limit has
been established from relation (23). -/
theorem IsStableLevyProcess.exists_centeredCorridor_escape_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableCenteredLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, hRange⟩ := h.exists_rationalRange_escape_rate hcdf
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hlim : Tendsto (stableCenteredLogRate P X α) l (𝓝 C) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro x hx
      have htarget : 1 < x / C := by
        exact (lt_div_iff_of_neg hC).2 (by linarith)
      have hpowLimit : Tendsto (fun e : ℝ => (1 + e) ^ α)
          (𝓝 (0 : ℝ)) (𝓝 1) := by
        have hbase : Tendsto (fun e : ℝ => 1 + e)
            (𝓝 (0 : ℝ)) (𝓝 1) := by
          simpa using (tendsto_const_nhds.add tendsto_id :
            Tendsto (fun e : ℝ => (1 : ℝ) + e) (𝓝 0) (𝓝 (1 + 0)))
        simpa only [Function.comp_def, Real.one_rpow] using
          (Real.continuousAt_rpow_const 1 α
            (Or.inl (by norm_num : (1 : ℝ) ≠ 0))).tendsto.comp hbase
      have hpowEvent : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) ^ α < x / C :=
        hpowLimit.eventually (Iio_mem_nhds htarget)
      obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hpowEvent
      let ε : ℝ := r / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hεball : ε ∈ Metric.ball (0 : ℝ) r := by
        change dist ε 0 < r
        rw [Real.dist_eq]
        simp only [sub_zero, abs_of_pos hε]
        dsimp [ε]
        linarith
      have hpow : (1 + ε) ^ α < x / C := hrsub hεball
      let scl : ℝ := 1 + ε
      have hscl : 0 < scl := by dsimp [scl]; linarith
      have hsclpow : 0 < scl ^ α := Real.rpow_pos_of_pos hscl α
      have hδval : 0 < (x / C - scl ^ α) / (2 * (x / C)) := by
        apply div_pos
        · dsimp [scl]
          linarith
        · positivity
      let δ : ℝ := (x / C - scl ^ α) / (2 * (x / C))
      have hδ : 0 < δ := by dsimp [δ]; exact hδval
      have htargetpos : 0 < x / C := by linarith
      have hxne : x ≠ 0 := by
        intro hxzero
        simp [hxzero] at htargetpos
      have hCne : C ≠ 0 := ne_of_lt hC
      have hdenForm : 1 - δ = (x / C + scl ^ α) / (2 * (x / C)) := by
        dsimp [δ]
        field_simp [hxne, hCne]
        ring
      have hden : 0 < 1 - δ := by rw [hdenForm]; positivity
      have hδlt : δ < 1 := by linarith
      have hfactor : scl ^ α / (1 - δ) < x / C := by
        rw [div_lt_iff₀ hden]
        rw [hdenForm]
        have hproduct : (x / C) * ((x / C + scl ^ α) / (2 * (x / C))) =
            (x / C + scl ^ α) / 2 := by
          field_simp [hxne, hCne]
        rw [hproduct]
        have hpow' : scl ^ α < x / C := by simpa [scl] using hpow
        linarith
      have hfactorC : x < (scl ^ α / (1 - δ)) * C := by
        have := mul_lt_mul_of_neg_right hfactor hC
        have hcancel : (x / C) * C = x := div_mul_cancel₀ x hC.ne
        linarith
      have hrel := h.eventually_one_sub_le_log_range_div_log_corridor_of_cdf
        hcdf ε hε δ hδ
      have hscale : Tendsto (fun a : ℝ => a / scl) l l := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have hid : Tendsto id l (𝓝 (0 : ℝ)) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          simpa [div_eq_mul_inv] using hid.mul_const scl⁻¹
        · filter_upwards [self_mem_nhdsWithin] with a ha
          exact div_pos ha hscl
      have hrelScaled := hscale.eventually hrel
      have hqzeroMeasure : Tendsto
          (centeredCorridorProbability P X) l (𝓝 0) := by
        obtain ⟨_, hpos⟩ :=
          h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
        change Tendsto (fun a : ℝ =>
          P (fullSegmentCorridorEvent X 0 1 (-a) a)) l (𝓝 0)
        convert h.tendsto_measure_scaledFullCorridor_zero hpos (-1) 1 using 1
        ext a
        congr 1
        ring_nf
      have hqzero : Tendsto (fun a : ℝ =>
          (centeredCorridorProbability P X a).toReal) l (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hqzeroMeasure
      have hqLt : ∀ᶠ a : ℝ in l,
          (centeredCorridorProbability P X a).toReal < 1 :=
        hqzero.eventually (Iio_mem_nhds (by norm_num))
      have hqneg : ∀ᶠ a : ℝ in l,
          Real.log ((centeredCorridorProbability P X a).toReal) < 0 := by
        filter_upwards [self_mem_nhdsWithin, hqLt] with a ha hlt
        have hqpos := centeredCorridorProbability_pos_of_cdf h hcdf ha
        exact Real.log_neg
          (ENNReal.toReal_pos_iff.mpr ⟨hqpos, measure_lt_top P _⟩) hlt
      have hscaledRange : Tendsto
          (fun a : ℝ => stableRangeLogRate P X α (a / scl)) l (𝓝 C) :=
        hRange.comp hscale
      have hproduct : Tendsto (fun a : ℝ =>
          (scl ^ α / (1 - δ)) * stableRangeLogRate P X α (a / scl))
          l (𝓝 ((scl ^ α / (1 - δ)) * C)) := by
        simpa using tendsto_const_nhds.mul hscaledRange
      have hproductEvent := hproduct.eventually (Ioi_mem_nhds hfactorC)
      have hratebound : ∀ᶠ a : ℝ in l,
          (scl ^ α / (1 - δ)) * stableRangeLogRate P X α (a / scl) ≤
            stableCenteredLogRate P X α a := by
        have hwidth (a : ℝ) : (1 + ε) * (a / scl) = a := by
          dsimp [scl]
          field_simp [hscl.ne']
        filter_upwards [self_mem_nhdsWithin, hrelScaled, hqneg] with a ha hratio hlogneg
        have hlogratio :
            Real.log ((rationalRangeProbability P X (a / scl)).toReal) ≤
              (1 - δ) * Real.log ((centeredCorridorProbability P X a).toReal) := by
          have heq : expandedCenteredCorridorProbability P X ε (a / scl) =
              centeredCorridorProbability P X a := by
            unfold expandedCenteredCorridorProbability centeredCorridorProbability
            have hwidthNeg : (-(1 + ε)) * (a / scl) = -a := by
              calc
                (-(1 + ε)) * (a / scl) = -((1 + ε) * (a / scl)) := by ring
                _ = -a := by rw [hwidth a]
            rw [hwidthNeg, hwidth a]
          rw [heq] at hratio
          exact (le_div_iff_of_neg hlogneg).mp hratio
        have hloglower :
                Real.log ((rationalRangeProbability P X (a / scl)).toReal) /
                (1 - δ) ≤ Real.log ((centeredCorridorProbability P X a).toReal) :=
          (div_le_iff₀ hden).2 (by simpa [mul_comm] using hlogratio)
        have haPos : 0 < a := ha
        have hscalePow : a ^ α = scl ^ α * (a / scl) ^ α := by
          have hmul : scl * (a / scl) = a := by field_simp [hscl.ne']
          calc
            a ^ α = (scl * (a / scl)) ^ α := by rw [hmul]
            _ = scl ^ α * (a / scl) ^ α :=
              Real.mul_rpow hscl.le (div_nonneg haPos.le hscl.le)
        have hmul := mul_le_mul_of_nonneg_left hloglower
          (Real.rpow_nonneg haPos.le α)
        have hfactorEq :
            a ^ α * (Real.log ((rationalRangeProbability P X (a / scl)).toReal) /
              (1 - δ)) =
              (scl ^ α / (1 - δ)) *
              stableRangeLogRate P X α (a / scl) := by
          rw [hscalePow]
          unfold stableRangeLogRate
          ring
        unfold stableCenteredLogRate
        rw [← hfactorEq]
        exact hmul
      filter_upwards [hproductEvent, hratebound] with a hproduct' hbound
      exact lt_of_lt_of_le hproduct' hbound
    · intro x hx
      have hrangeEventually : ∀ᶠ a : ℝ in l,
          stableRangeLogRate P X α a < x := hRange.eventually (Iio_mem_nhds hx)
      have hupper : ∀ᶠ a : ℝ in l,
          stableCenteredLogRate P X α a ≤ stableRangeLogRate P X α a := by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact stableCenteredLogRate_le_range h hcdf ha
      filter_upwards [hupper, hrangeEventually] with a hq hr
      exact lt_of_le_of_lt hq hr
  exact ⟨C, hC, by simpa [l] using hRange, by simpa [l] using hlim⟩

private theorem shiftedCorridorProbability_pos_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α d a : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) (ha : 0 < a) :
    0 < shiftedCorridorProbability P X d a := by
  obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have hlo : a * (d - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
  have hhi : 0 < a * (d + 1) := mul_pos ha (by linarith)
  dsimp [shiftedCorridorProbability]
  exact h.measure_fullSegmentCorridor_pos _ _ hlo hhi hpos hneg

private theorem stableShiftedCorridorLogRate_le_range
    {Ω : Type*} [MeasurableSpace Ω]
    {α d a : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) (ha : 0 < a) :
    stableShiftedCorridorLogRate P X α d a ≤ stableRangeLogRate P X α a := by
  have hqpos := shiftedCorridorProbability_pos_of_cdf h hcdf hd ha
  have hrpos := h.rationalRangeProbability_pos_of_cdf hcdf ha
  have hsubset : shiftedCorridorProbability P X d a ≤
      rationalRangeProbability P X a := by
    change P (fullSegmentCorridorEvent X 0 1
      (a * (d - 1)) (a * (d + 1))) ≤ _
    apply measure_mono
    have htube := fullSegmentCorridorEvent_subset_rationalHorizonTubeEvent_exact
      X (a * (d - 1)) (a * (d + 1))
    have hwidth : a * (d + 1) - a * (d - 1) = 2 * a := by ring
    rw [hwidth] at htube
    simpa [rationalRangeProbability] using htube
  have hreal : (shiftedCorridorProbability P X d a).toReal ≤
      (rationalRangeProbability P X a).toReal :=
    (ENNReal.toReal_le_toReal (measure_lt_top P _).ne
      (measure_lt_top P _).ne).mpr hsubset
  have hlog := Real.log_le_log
    (ENNReal.toReal_pos_iff.mpr ⟨hqpos, measure_lt_top P _⟩) hreal
  unfold stableShiftedCorridorLogRate stableRangeLogRate
  exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg ha.le _)

/-- Every translated corridor whose interior contains the starting point has
the same finite negative escape rate as the range tube. This is the direct
application of relation (21) after the centered rate has been proved. -/
theorem IsStableLevyProcess.exists_shiftedCorridor_escape_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {α d : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableCenteredLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (stableShiftedCorridorLogRate P X α d)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, hRange, hcenter⟩ := h.exists_centeredCorridor_escape_rate hcdf
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hlim : Tendsto (stableShiftedCorridorLogRate P X α d) l (𝓝 C) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro x hx
      have htarget : 1 < x / C := (lt_div_iff_of_neg hC).2 (by linarith)
      have hpowLimit : Tendsto (fun e : ℝ => (1 + e) ^ α)
          (𝓝 (0 : ℝ)) (𝓝 1) := by
        have hbase : Tendsto (fun e : ℝ => 1 + e)
            (𝓝 (0 : ℝ)) (𝓝 1) := by
          simpa using (tendsto_const_nhds.add tendsto_id :
            Tendsto (fun e : ℝ => (1 : ℝ) + e) (𝓝 0) (𝓝 (1 + 0)))
        simpa only [Function.comp_def, Real.one_rpow] using
          (Real.continuousAt_rpow_const 1 α
            (Or.inl (by norm_num : (1 : ℝ) ≠ 0))).tendsto.comp hbase
      have hpowEvent : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) ^ α < x / C :=
        hpowLimit.eventually (Iio_mem_nhds htarget)
      obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hpowEvent
      have habs : |d| < 1 := abs_lt.mpr hd
      let ε : ℝ := min (r / 2) ((1 - |d|) / 2)
      have hε : 0 < ε := by
        dsimp [ε]
        exact lt_min (half_pos hrpos) (half_pos (sub_pos.mpr habs))
      have hεle : ε ≤ (1 - |d|) / 2 := min_le_right _ _
      have hεltR : ε < r := by
        have : ε ≤ r / 2 := min_le_left _ _
        dsimp [ε] at this ⊢
        linarith
      have hεball : ε ∈ Metric.ball (0 : ℝ) r := by
        change dist ε 0 < r
        rw [Real.dist_eq]
        simp only [sub_zero, abs_of_pos hε]
        exact hεltR
      have hpow : (1 + ε) ^ α < x / C := hrsub hεball
      let scl : ℝ := 1 + ε
      have hscl : 0 < scl := by dsimp [scl]; linarith
      have hsclpow : 0 < scl ^ α := Real.rpow_pos_of_pos hscl α
      have habsMul : |scl * d| = scl * |d| := by
        rw [abs_mul, abs_of_pos hscl]
      have hscld : |scl * d| < 1 := by
        rw [habsMul]
        have hεd : ε * |d| ≤ ε := by
          calc
            ε * |d| ≤ ε * 1 := mul_le_mul_of_nonneg_left habs.le hε.le
            _ = ε := mul_one _
        dsimp [scl]
        nlinarith [hεle]
      have hc : -1 < scl * d ∧ scl * d < 1 := abs_lt.mp hscld
      have hδval : 0 < (x / C - scl ^ α) / (2 * (x / C)) := by
        apply div_pos
        · have hpow' : scl ^ α < x / C := by simpa [scl] using hpow
          linarith
        · positivity
      let δ : ℝ := (x / C - scl ^ α) / (2 * (x / C))
      have hδ : 0 < δ := by dsimp [δ]; exact hδval
      have htargetpos : 0 < x / C := by linarith
      have hxne : x ≠ 0 := by
        intro hxzero
        simp [hxzero] at htargetpos
      have hCne : C ≠ 0 := ne_of_lt hC
      have hdenForm : 1 - δ = (x / C + scl ^ α) / (2 * (x / C)) := by
        dsimp [δ]
        field_simp [hxne, hCne]
        ring_nf
      have hden : 0 < 1 - δ := by rw [hdenForm]; positivity
      have hfactor : scl ^ α / (1 - δ) < x / C := by
        rw [div_lt_iff₀ hden, hdenForm]
        have hproduct : (x / C) * ((x / C + scl ^ α) / (2 * (x / C))) =
            (x / C + scl ^ α) / 2 := by
          field_simp [hxne, hCne]
        rw [hproduct]
        have hpow' : scl ^ α < x / C := by simpa [scl] using hpow
        linarith
      have hfactorC : x < (scl ^ α / (1 - δ)) * C := by
        have hmul := mul_lt_mul_of_neg_right hfactor hC
        have hcancel : (x / C) * C = x := div_mul_cancel₀ x hCne
        linarith
      have hrel := h.eventually_one_sub_le_log_corridor_ratio_of_cdf
        hcdf 0 (scl * d) ε (by norm_num) hc hε δ hδ
      have hscale : Tendsto (fun a : ℝ => a / scl) l l := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have hid : Tendsto id l (𝓝 (0 : ℝ)) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          simpa [div_eq_mul_inv] using hid.mul_const scl⁻¹
        · filter_upwards [self_mem_nhdsWithin] with a ha
          exact div_pos ha hscl
      have hrelScaled := hscale.eventually hrel
      have hqzeroMeasure : Tendsto (shiftedCorridorProbability P X d)
          l (𝓝 0) := by
        obtain ⟨_, hpos⟩ :=
          h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
        have hlower : d - 1 < 0 := by linarith [hd.1]
        have hupper : 0 < d + 1 := by linarith [hd.2]
        change Tendsto (fun a : ℝ => P (fullSegmentCorridorEvent X 0 1
          (a * (d - 1)) (a * (d + 1)))) l (𝓝 0)
        exact h.tendsto_measure_scaledFullCorridor_zero hpos (d - 1) (d + 1)
      have hqzero : Tendsto (fun a : ℝ =>
          (shiftedCorridorProbability P X d a).toReal) l (𝓝 0) := by
        simpa only [Function.comp_def, ENNReal.toReal_zero] using
          (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hqzeroMeasure
      have hqLt : ∀ᶠ a : ℝ in l,
          (shiftedCorridorProbability P X d a).toReal < 1 :=
        hqzero.eventually (Iio_mem_nhds (by norm_num))
      have hqneg : ∀ᶠ a : ℝ in l,
          Real.log ((shiftedCorridorProbability P X d a).toReal) < 0 := by
        filter_upwards [self_mem_nhdsWithin, hqLt] with a ha hlt
        have hqpos := shiftedCorridorProbability_pos_of_cdf h hcdf hd ha
        exact Real.log_neg
          (ENNReal.toReal_pos_iff.mpr ⟨hqpos, measure_lt_top P _⟩) hlt
      have hscaledCenter : Tendsto
          (fun a : ℝ => stableCenteredLogRate P X α (a / scl)) l (𝓝 C) :=
        hcenter.comp hscale
      have hproduct : Tendsto (fun a : ℝ =>
          (scl ^ α / (1 - δ)) * stableCenteredLogRate P X α (a / scl))
          l (𝓝 ((scl ^ α / (1 - δ)) * C)) := by
        simpa using tendsto_const_nhds.mul hscaledCenter
      have hproductEvent := hproduct.eventually (Ioi_mem_nhds hfactorC)
      have hratebound : ∀ᶠ a : ℝ in l,
          (scl ^ α / (1 - δ)) * stableCenteredLogRate P X α (a / scl) ≤
            stableShiftedCorridorLogRate P X α d a := by
        have hleft (a : ℝ) :
            (a / scl) * (scl * d - (1 + ε)) = a * (d - 1) := by
          dsimp [scl]
          field_simp [hscl.ne']
        have hright (a : ℝ) :
            (a / scl) * (scl * d + 1 + ε) = a * (d + 1) := by
          dsimp [scl]
          field_simp [hscl.ne']
          ring
        filter_upwards [self_mem_nhdsWithin, hrelScaled, hqneg] with a ha hratio hlogneg
        have heq : P (fullSegmentCorridorEvent X 0 1
            ((a / scl) * (scl * d - (1 + ε)))
            ((a / scl) * (scl * d + 1 + ε))) =
            shiftedCorridorProbability P X d a := by
          rw [hleft a, hright a]
          rfl
        rw [heq] at hratio
        have hcenterEq :
            P (fullSegmentCorridorEvent X 0 1
              ((a / scl) * (0 - 1)) ((a / scl) * (0 + 1))) =
            centeredCorridorProbability P X (a / scl) := by
          simp [centeredCorridorProbability]
        rw [hcenterEq] at hratio
        have hlogratio :
            Real.log ((centeredCorridorProbability P X (a / scl)).toReal) ≤
              (1 - δ) * Real.log ((shiftedCorridorProbability P X d a).toReal) :=
          (le_div_iff_of_neg hlogneg).mp hratio
        have hloglower :
            Real.log ((centeredCorridorProbability P X (a / scl)).toReal) /
                (1 - δ) ≤
              Real.log ((shiftedCorridorProbability P X d a).toReal) :=
          (div_le_iff₀ hden).2 (by simpa [mul_comm] using hlogratio)
        have haPos : 0 < a := ha
        have hscalePow : a ^ α = scl ^ α * (a / scl) ^ α := by
          have hmul : scl * (a / scl) = a := by field_simp [hscl.ne']
          calc
            a ^ α = (scl * (a / scl)) ^ α := by rw [hmul]
            _ = scl ^ α * (a / scl) ^ α :=
              Real.mul_rpow hscl.le (div_nonneg haPos.le hscl.le)
        have hmul := mul_le_mul_of_nonneg_left hloglower
          (Real.rpow_nonneg haPos.le α)
        have hfactorEq :
            a ^ α * (Real.log ((centeredCorridorProbability P X (a / scl)).toReal) /
              (1 - δ)) =
            (scl ^ α / (1 - δ)) *
              stableCenteredLogRate P X α (a / scl) := by
          rw [hscalePow]
          unfold stableCenteredLogRate
          ring
        unfold stableShiftedCorridorLogRate
        rw [← hfactorEq]
        exact hmul
      filter_upwards [hproductEvent, hratebound] with a hproduct' hbound
      exact lt_of_lt_of_le hproduct' hbound
    · intro x hx
      have hrangeEventually : ∀ᶠ a : ℝ in l,
          stableRangeLogRate P X α a < x := hRange.eventually (Iio_mem_nhds hx)
      have hupper : ∀ᶠ a : ℝ in l,
          stableShiftedCorridorLogRate P X α d a ≤ stableRangeLogRate P X α a := by
        filter_upwards [self_mem_nhdsWithin] with a ha
        exact stableShiftedCorridorLogRate_le_range h hcdf hd ha
      filter_upwards [hupper, hrangeEventually] with a hq hr
      exact lt_of_le_of_lt hq hr
  exact ⟨C, hC, by simpa [l] using hRange,
    by simpa [l] using hcenter, by simpa [l] using hlim⟩

/-- The logarithmic probability of a translated corridor is asymptotic to
that of the range tube. This is relation (19), obtained by cancelling the
common positive normalization factor from their escape rates. -/
theorem IsStableLevyProcess.tendsto_log_shiftedCorridor_div_log_range
    {Ω : Type*} [MeasurableSpace Ω]
    {α d : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) :
    Tendsto
      (fun a : ℝ =>
        Real.log ((shiftedCorridorProbability P X d a).toReal) /
          Real.log ((rationalRangeProbability P X a).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨C, hC, hRange, _, hshift⟩ :=
    h.exists_shiftedCorridor_escape_rate hcdf hd
  have hratio := hshift.div hRange (ne_of_lt hC)
  have hcancel :
      (fun a : ℝ => stableShiftedCorridorLogRate P X α d a /
        stableRangeLogRate P X α a) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun a : ℝ =>
        Real.log ((shiftedCorridorProbability P X d a).toReal) /
          Real.log ((rationalRangeProbability P X a).toReal)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have haPow : a ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha α)
    simpa [stableShiftedCorridorLogRate, stableRangeLogRate] using
      (mul_div_mul_left
        (Real.log ((shiftedCorridorProbability P X d a).toReal))
        (Real.log ((rationalRangeProbability P X a).toReal)) haPow)
  simpa [div_self (ne_of_lt hC)] using hratio.congr' hcancel

end ProbabilityTheory

end
