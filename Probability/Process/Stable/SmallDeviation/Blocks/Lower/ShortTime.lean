module

public import Probability.Process.Path.Cadlag.ShortTime
public import Probability.Process.Stable.FiniteDimensional
public import Probability.Distributions.Stable.Sign
public import Probability.Process.Path.Skorokhod.Corridor.Enlargement
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Short stable blocks remain in a fixed centered corridor

This is the topological probability input for the directional return events
in the stable-process block lower bound. Endpoint sign probabilities are
handled separately through the stable increment law.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

theorem IsStableLevyProcess.tendsto_measure_shortCorridor
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ => P (rationalInitialCorridorEvent X
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ))
      atTop (𝓝 1) := by
  exact tendsto_measure_rationalInitialCorridorEvent P X
    (fun t => h.increments.aemeasurable_eval t) h.ae_cadlag
    (horizon := fun n : ℕ => 1 / ((n : ℝ≥0) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat δ hδ

/-- Every positive-mass window of the reference stable law can occur at the
end of a sufficiently short block while the whole block stays in a fixed
centered corridor. The endpoint is normalized by the stable time scale. -/
theorem IsStableLevyProcess.eventually_shortCorridor_scaledIncrement_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ : ℝ) (hδ : 0 < δ)
    (J : Set ℝ) (hJ : MeasurableSet J) (hJpos : 0 < μ J) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (rationalInitialCorridorEvent X
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
          (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈ J}) := by
  let t : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  let A : ℕ → Set Ω := fun n => rationalInitialCorridorEvent X (t n) (-δ) δ
  let B : ℕ → Set Ω := fun n =>
    {ω | (X (t n) ω - X 0 ω) / ((t n : ℝ) ^ (1 / α)) ∈ J}
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    exact nullMeasurableSet_rationalInitialCorridorEvent P X
      (fun s => h.increments.aemeasurable_eval s) _ _ _
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 1) :=
    h.tendsto_measure_shortCorridor δ hδ
  have hB : ∀ n, μ J ≤ P (B n) := by
    intro n
    let scale : ℝ := (t n : ℝ) ^ (1 / α)
    have hscale : scale ≠ 0 :=
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (by positivity : 0 < t n)) _).ne'
    have hset : MeasurableSet {z : ℝ | z / scale ∈ J} :=
      hJ.preimage (measurable_id.div_const scale)
    have hlaw := h.increments.increment_hasLaw 0 (t n) (by exact bot_le)
    have hp : P (B n) =
        (μ.map (fun x : ℝ => scale * x)) {z : ℝ | z / scale ∈ J} := by
      simpa [B, scale] using
        (hlaw.measure_eq (p := fun z : ℝ => z / scale ∈ J) hset)
    rw [Measure.map_apply (by fun_prop) hset] at hp
    have hpre : (fun x : ℝ => scale * x) ⁻¹' {z : ℝ | z / scale ∈ J} = J := by
      ext x
      simp [Set.mem_preimage, mul_div_cancel_left₀ x hscale]
    rw [hpre] at hp
    exact hp.symm.le
  simpa [A, B, t] using
    (eventually_measure_inter_pos_of_tendsto_one P A B hA hlim hJpos hB)

/-- The same short-block statement for the complete càdlàg path. A smaller
rational corridor supplies a uniform margin in the displayed corridor. -/
theorem IsStableLevyProcess.eventually_fullShortCorridor_scaledIncrement_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ : ℝ) (hδ : 0 < δ)
    (J : Set ℝ) (hJ : MeasurableSet J) (hJpos : 0 < μ J) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
          (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈ J}) := by
  have hsmall := h.eventually_shortCorridor_scaledIncrement_pos
    (δ / 2) (by positivity) J hJ hJpos
  filter_upwards [hsmall] with n hn
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  have hle :
      P (rationalInitialCorridorEvent X t (-(δ / 2)) (δ / 2) ∩
          {ω | (X t ω - X 0 ω) / ((t : ℝ) ^ (1 / α)) ∈ J}) ≤
        P (fullSegmentCorridorEvent X 0 t (-δ) δ ∩
          {ω | (X t ω - X 0 ω) / ((t : ℝ) ^ (1 / α)) ∈ J}) := by
    apply measure_mono_ae
    filter_upwards [h.ae_cadlag] with ω hω
    rintro ⟨hsmallω, hendω⟩
    refine ⟨?_, hendω⟩
    apply (mem_fullSegmentCorridorEvent_iff_rational X 0 t (-δ) δ ω hω).2
    rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real]
    refine ⟨δ / 2, by positivity, fun q => ?_⟩
    have hq := Set.mem_iInter.mp hsmallω q
    change -(δ / 2) < X (t * rationalUnitTime q) ω - X 0 ω ∧
      X (t * rationalUnitTime q) ω - X 0 ω < δ / 2 at hq
    simpa only [zero_add] using And.intro (le_of_lt (by linarith :
      -δ + δ / 2 < X (t * rationalUnitTime q) ω - X 0 ω))
      (le_of_lt (by linarith :
        X (t * rationalUnitTime q) ω - X 0 ω < δ - δ / 2))
  have hn' : 0 < P (rationalInitialCorridorEvent X t (-(δ / 2)) (δ / 2) ∩
      {ω | (X t ω - X 0 ω) / ((t : ℝ) ^ (1 / α)) ∈ J}) := by
    simpa [t] using hn
  exact hn'.trans_le (by simpa [t] using hle)

/-- Strict stability preserves the probability that an increment is positive
at every positive time. -/
theorem IsStableLevyProcess.measure_positive_increment_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (t : ℝ≥0) (ht : 0 < t) :
    P {ω | 0 < X t ω - X 0 ω} = μ (Set.Ioi 0) := by
  have hlaw := h.increments.increment_hasLaw 0 t (by exact bot_le)
  have hfactor : 0 < (t : ℝ) ^ (1 / α) :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _
  have hprob : P {ω | 0 < X t ω - X 0 ω} =
      (μ.map fun x : ℝ => (t : ℝ) ^ (1 / α) * x) (Set.Ioi 0) := by
    simpa only [NNReal.coe_zero, sub_zero, Set.Ioi, one_div] using
      (hlaw.measure_eq (p := fun x : ℝ => 0 < x) measurableSet_Ioi)
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at hprob
  rw [hprob]
  congr 1
  ext x
  change (0 < (t : ℝ) ^ (1 / α) * x) ↔ 0 < x
  exact (mul_pos_iff_of_pos_left hfactor)

/-- The negative-side increment probability is likewise independent of the
positive time horizon. -/
theorem IsStableLevyProcess.measure_negative_increment_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (t : ℝ≥0) (ht : 0 < t) :
    P {ω | X t ω - X 0 ω < 0} = μ (Set.Iio 0) := by
  have hlaw := h.increments.increment_hasLaw 0 t (by exact bot_le)
  have hfactor : 0 < (t : ℝ) ^ (1 / α) :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _
  have hprob : P {ω | X t ω - X 0 ω < 0} =
      (μ.map fun x : ℝ => (t : ℝ) ^ (1 / α) * x) (Set.Iio 0) := by
    simpa only [NNReal.coe_zero, sub_zero, Set.Iio, one_div] using
      (hlaw.measure_eq (p := fun x : ℝ => x < 0) measurableSet_Iio)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio] at hprob
  rw [hprob]
  congr 1
  ext x
  change ((t : ℝ) ^ (1 / α) * x < 0) ↔ x < 0
  have hfpos : 0 < (t : ℝ) ^ α⁻¹ := by simpa only [one_div] using hfactor
  simp [mul_neg_iff, hfpos, not_lt_of_ge hfpos.le]

theorem IsStableLevyProcess.eventually_measure_shortCorridor_positiveIncrement_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ : ℝ) (hδ : 0 < δ) (hpos : 0 < μ (Set.Ioi 0)) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (rationalInitialCorridorEvent X
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | 0 < X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω}) := by
  let t : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  let A : ℕ → Set Ω := fun n => rationalInitialCorridorEvent X (t n) (-δ) δ
  let B : ℕ → Set Ω := fun n => {ω | 0 < X (t n) ω - X 0 ω}
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    exact nullMeasurableSet_rationalInitialCorridorEvent P X
      (fun s => h.increments.aemeasurable_eval s) _ _ _
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 1) :=
    h.tendsto_measure_shortCorridor δ hδ
  have hB : ∀ n, μ (Set.Ioi 0) ≤ P (B n) := by
    intro n
    exact le_of_eq (h.measure_positive_increment_eq (t n) (by positivity)).symm
  exact eventually_measure_inter_pos_of_tendsto_one P A B hA hlim hpos hB

theorem IsStableLevyProcess.eventually_measure_shortCorridor_negativeIncrement_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ : ℝ) (hδ : 0 < δ) (hneg : 0 < μ (Set.Iio 0)) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (rationalInitialCorridorEvent X
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω < 0}) := by
  let t : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  let A : ℕ → Set Ω := fun n => rationalInitialCorridorEvent X (t n) (-δ) δ
  let B : ℕ → Set Ω := fun n => {ω | X (t n) ω - X 0 ω < 0}
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    exact nullMeasurableSet_rationalInitialCorridorEvent P X
      (fun s => h.increments.aemeasurable_eval s) _ _ _
  have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 1) :=
    h.tendsto_measure_shortCorridor δ hδ
  have hB : ∀ n, μ (Set.Iio 0) ≤ P (B n) := by
    intro n
    exact le_of_eq (h.measure_negative_increment_eq (t n) (by positivity)).symm
  exact eventually_measure_inter_pos_of_tendsto_one P A B hA hlim hneg hB

/-- Both directional return blocks have positive probability once the block
duration is sufficiently small. This is the nondegeneracy input for the
two-bin lower block iteration. -/
theorem IsStableLevyProcess.eventually_directionalReturn_probabilities_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ coreLower coreUpper : ℝ) (hδ : 0 < δ)
    (hcoreLower : coreLower ≤ -δ) (hcoreUpper : δ ≤ coreUpper)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    ∀ᶠ n : ℕ in atTop,
      0 < P ((fun ω q => X ((1 / ((n : ℝ≥0) + 1)) * rationalUnitTime q) ω -
          X 0 ω) ⁻¹' rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ∧
      0 < P ((fun ω q => X ((1 / ((n : ℝ≥0) + 1)) * rationalUnitTime q) ω -
          X 0 ω) ⁻¹' rationalCoordinateCorridorReturn (-δ) δ coreLower 0) := by
  filter_upwards
    [h.eventually_measure_shortCorridor_positiveIncrement_pos δ hδ hpos,
      h.eventually_measure_shortCorridor_negativeIncrement_pos δ hδ hneg]
    with n hnpos hnneg
  constructor
  · exact hnpos.trans_le (measure_mono
      (rationalInitialCorridorEvent_inter_positive_subset_return X
        (1 / ((n : ℝ≥0) + 1)) δ coreUpper hcoreUpper))
  · exact hnneg.trans_le (measure_mono
      (rationalInitialCorridorEvent_inter_negative_subset_return X
        (1 / ((n : ℝ≥0) + 1)) δ coreLower hcoreLower))

/-- The short directional blocks are positive under the original condition
`0 < F_α(0) < 1`, with atomlessness stated through Mathlib's class. -/
theorem IsStableLevyProcess.eventually_directionalReturn_probabilities_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ coreLower coreUpper : ℝ) (hδ : 0 < δ)
    (hcoreLower : coreLower ≤ -δ) (hcoreUpper : δ ≤ coreUpper)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∀ᶠ n : ℕ in atTop,
      0 < P ((fun ω q => X ((1 / ((n : ℝ≥0) + 1)) * rationalUnitTime q) ω -
          X 0 ω) ⁻¹' rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ∧
      0 < P ((fun ω q => X ((1 / ((n : ℝ≥0) + 1)) * rationalUnitTime q) ω -
          X 0 ω) ⁻¹' rationalCoordinateCorridorReturn (-δ) δ coreLower 0) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  exact h.eventually_directionalReturn_probabilities_pos
    δ coreLower coreUpper hδ hcoreLower hcoreUpper hpos hneg

/-- The original CDF hypothesis yields positive probabilities for complete
càdlàg short blocks. The proof first uses a smaller rational corridor, then
enlarges it to recover a genuine uniform margin on every time coordinate. -/
theorem IsStableLevyProcess.eventually_fullDirectionalReturn_probabilities_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ coreLower coreUpper : ℝ) (hδ : 0 < δ)
    (hcoreLower : coreLower ≤ -δ) (hcoreUpper : δ ≤ coreUpper)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (fullSegmentCorridorReturnEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ 0 coreUpper) ∧
      0 < P (fullSegmentCorridorReturnEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ coreLower 0) := by
  have hsmall := h.eventually_directionalReturn_probabilities_pos_of_cdfAtZero
    (δ / 2) coreLower coreUpper (by positivity)
    (by linarith) (by linarith) hcdf
  filter_upwards [hsmall] with n hn
  have hplus := measure_rationalCorridorReturn_le_fullSegmentCorridorReturn_enlarged
    P X (1 / ((n : ℝ≥0) + 1)) (-(δ / 2)) (δ / 2) 0 coreUpper
      (δ / 2) (by positivity) h.ae_cadlag
  have hminus := measure_rationalCorridorReturn_le_fullSegmentCorridorReturn_enlarged
    P X (1 / ((n : ℝ≥0) + 1)) (-(δ / 2)) (δ / 2) coreLower 0
      (δ / 2) (by positivity) h.ae_cadlag
  constructor
  · convert hn.1.trans_le hplus using 1 <;> ring
  · convert hn.2.trans_le hminus using 1 <;> ring

theorem IsStableLevyProcess.eventually_firstBlock_directionalReturn_probabilities_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (δ coreLower coreUpper : ℝ) (hδ : 0 < δ)
    (hcoreLower : coreLower ≤ -δ) (hcoreUpper : δ ≤ coreUpper)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0)) :
    ∀ᶠ n : ℕ in atTop,
      0 < P ((fun ω q => rationalUniformBlockProcessFromTime X
          (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper) ∧
      0 < P ((fun ω q => rationalUniformBlockProcessFromTime X
          (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ coreLower 0) := by
  filter_upwards [h.eventually_directionalReturn_probabilities_pos δ coreLower
    coreUpper hδ hcoreLower hcoreUpper hpos hneg] with n hn
  have hmap : (fun ω q => rationalUniformBlockProcessFromTime X
      (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) =
      (fun ω q => X ((1 / ((n : ℝ≥0) + 1)) * rationalUnitTime q) ω -
        X 0 ω) := by
    rw [rationalUniformBlockProcess_zero_eq_initial,
      rationalUniformBlockBoundary_succ_one]
  simpa only [hmap] using hn

end ProbabilityTheory
