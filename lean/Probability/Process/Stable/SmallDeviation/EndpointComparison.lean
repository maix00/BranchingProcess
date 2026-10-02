module

public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceFactorization
public import Probability.Process.Stable.SmallDeviation.Blocks.EntranceScaling
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FiniteTimeEntrance
public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Shrinking
public import Probability.Process.Corridor.Range
public import Analysis.Asymptotics.NegativeRatio
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Endpoint-constrained small-corridor comparison

Finite covers of possible prefixH endpoints reduce the endpoint-constrained
comparison to fixed-time entrance probabilities and independent increments.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

private theorem exists_finset_open_cover_Icc
    {r : ℝ} (hr : 0 < r) :
    ∃ F : Finset {x : ℝ // x ∈ Set.Icc (-1) 1},
      ∀ z ∈ Set.Icc (-1) 1,
        ∃ x ∈ F, z ∈ Set.Ioo (x.1 - r) (x.1 + r) := by
  let Center := {x : ℝ // x ∈ Set.Icc (-1) 1}
  let W : Center → Set ℝ := fun x => Set.Ioo (x.1 - r) (x.1 + r)
  have hopen : ∀ x : Center, IsOpen (W x) := fun _ => isOpen_Ioo
  have hcover : Set.Icc (-1 : ℝ) 1 ⊆ ⋃ x : Center, W x := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    change z - r < z ∧ z < z + r
    constructor <;> linarith
  obtain ⟨F, hscover⟩ :=
    isCompact_Icc.elim_finite_subcover W hopen hcover
  refine ⟨F, ?_⟩
  intro z hz
  obtain ⟨x, hxs⟩ := Set.mem_iUnion.mp (hscover hz)
  obtain ⟨hxin, hxW⟩ := Set.mem_iUnion.mp hxs
  exact ⟨x, hxin, by simpa [W] using hxW⟩

private def endpointBinEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a r x : ℝ) : Set Ω :=
  fullSegmentCorridorReturnEvent X 0 1 (-a) a
    (a * (x - r)) (a * (x + r))

private def endpointTargetEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (a ε c b : ℝ) : Set Ω :=
  fullSegmentCorridorIocReturnEvent X 0 1
    (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b)

/-- Scaling both time and space by the stable scale preserves a complete
corridor-return probability, including its open endpoint convention. -/
theorem IsStableLevyProcess.measure_scaled_time_fullReturn
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0
      (T * stableEntranceHorizon α a)
      (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) =
    P (fullSegmentCorridorReturnEvent X 0 T
      lower upper coreLower coreUpper) := by
  let smallHorizon : ℝ≥0 := stableEntranceHorizon α a
  let horizon : ℝ≥0 := T * smallHorizon
  have hα : 0 < α := h.increments.strictlyStable.1
  have hsmall : (smallHorizon : ℝ) = a ^ α := by
    simp [smallHorizon, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
  have hsmallPos : 0 < smallHorizon := by
    apply NNReal.coe_pos.mp
    rw [hsmall]
    exact Real.rpow_pos_of_pos ha α
  have hhorizon : 0 < horizon := mul_pos hT hsmallPos
  have hscale : (horizon : ℝ) ^ (-(1 / α)) =
      (T : ℝ) ^ (-(1 / α)) * a⁻¹ := by
    change (((T * smallHorizon : ℝ≥0) : ℝ) ^ (-(1 / α))) = _
    rw [NNReal.coe_mul, hsmall]
    rw [Real.mul_rpow (NNReal.coe_nonneg T)
      (Real.rpow_nonneg ha.le α)]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by field_simp [hα.ne']
    rw [hexp, Real.rpow_neg_one]
  have hscaled := h.measure_fullSegmentCorridorReturn_scale horizon hhorizon
    (a * lower) (a * upper) (a * coreLower) (a * coreUpper)
  have hbase := h.measure_fullSegmentCorridorReturn_scale T hT
    lower upper coreLower coreUpper
  have hcancel (x : ℝ) :
      a * x * ((T : ℝ) ^ (-(1 / α)) * a⁻¹) =
        x * (T : ℝ) ^ (-(1 / α)) := by
    field_simp [ha.ne']
  rw [hscale, hcancel lower, hcancel upper,
    hcancel coreLower, hcancel coreUpper] at hscaled
  exact hscaled.trans hbase.symm


private theorem eventually_fixed_endpoint_bin_le_target
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (b c ε y r : ℝ)
    (x : {z : ℝ // z ∈ Set.Icc (-1) 1})
    (hr : 0 < r) (h4rε : 4 * r < ε)
    (h4rc : 4 * r < y - c) (h4rb : 4 * r < b - y)
    (T : ℝ≥0) (hT : 0 < T)
    :
    ∀ᶠ a' : ℝ in nhdsWithin 0 (Set.Ioi 0),
      P (fullSegmentCorridorReturnEvent X 0 T
        (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
        (y - x.1 - r) (y - x.1 + r)) *
        P (endpointBinEvent X a' r x.1) ≤
      P (endpointTargetEvent X a' ε c b) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hα : 0 < α := h.increments.strictlyStable.1
  have hpow : Tendsto (fun a' : ℝ => a' ^ α) l (nhds 0) := by
    have hcont := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using
      (hcont.mono_left (nhdsWithin_le_nhds : l ≤ nhds 0))
  have hcutTendsto : Tendsto (fun a' : ℝ => (T : ℝ) * a' ^ α)
      l (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hpow :
        Tendsto (fun a' : ℝ => (T : ℝ) * a' ^ α) l
          (nhds ((T : ℝ) * 0)))
  have hcutSmall : ∀ᶠ a' : ℝ in l, (T : ℝ) * a' ^ α < 1 := by
    filter_upwards [hcutTendsto.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a' ha'
    exact ha'
  have hprefixTendsto : Tendsto
      (fun a' : ℝ => 1 - (T : ℝ) * a' ^ α) l (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hcutTendsto)
  have hscaleTendsto : Tendsto
      (fun a' : ℝ => (1 - (T : ℝ) * a' ^ α) ^ (1 / α))
      l (nhds 1) := by
    have hcont := (Real.continuousAt_rpow_const 1 (1 / α)
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0))).tendsto
    simpa only [Function.comp_def, Real.one_rpow] using hcont.comp hprefixTendsto
  have hdeltaSmall : ∀ᶠ a' : ℝ in l,
      1 - (1 - (T : ℝ) * a' ^ α) ^ (1 / α) < r := by
    have hdeltaTendsto : Tendsto
        (fun a' : ℝ => 1 - (1 - (T : ℝ) * a' ^ α) ^ (1 / α))
        l (nhds 0) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) :=
        tendsto_const_nhds
      simpa only [Function.comp_def, Real.one_rpow, sub_self] using
        hconst.sub hscaleTendsto
    exact hdeltaTendsto.eventually (Iio_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hcutSmall, hdeltaSmall]
    with a' ha' hcut hdelta
  have hhor : (stableEntranceHorizon α a' : ℝ) = a' ^ α := by
    simp [stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha' α).le]
  let tail : ℝ≥0 := T * stableEntranceHorizon α a'
  have htail : 0 < tail := by
    apply NNReal.coe_pos.mp
    change 0 < (T : ℝ) * (stableEntranceHorizon α a' : ℝ)
    rw [hhor]
    exact mul_pos (NNReal.coe_pos.mpr hT) (Real.rpow_pos_of_pos ha' α)
  have htailCo : (tail : ℝ) = (T : ℝ) * a' ^ α := by
    simp [tail, hhor]
  have htailLt : tail < 1 := by
    apply NNReal.coe_lt_one.mp
    rw [htailCo]
    exact hcut
  let prefixH : ℝ≥0 := 1 - tail
  have hprefix : 0 < prefixH := by
    dsimp [prefixH]
    exact tsub_pos_iff_lt.mpr htailLt
  have hprefixLt : prefixH < 1 := by
    dsimp [prefixH]
    exact tsub_lt_self (by norm_num : (0 : ℝ≥0) < 1) htail
  have hprefixCo : (prefixH : ℝ) = 1 - (tail : ℝ) := by
    simp [prefixH, NNReal.coe_sub htailLt.le]
  have hs : 0 < (prefixH : ℝ) ^ (1 / α) :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hprefix) _
  have hsle : (prefixH : ℝ) ^ (1 / α) ≤ 1 := by
    exact Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast hprefixLt.le)
      (by positivity)
  have hsp : 0 < prefixH := hprefix
  have hpowprod : (prefixH : ℝ) ^ (1 / α) *
      (prefixH : ℝ) ^ (-(1 / α)) = 1 := by
    rw [Real.rpow_neg (NNReal.coe_pos.mpr hsp).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos
      (NNReal.coe_pos.mpr hsp) (1 / α)).ne'
  let scale : ℝ := (prefixH : ℝ) ^ (1 / α)
  let invScale : ℝ := (prefixH : ℝ) ^ (-(1 / α))
  let outerLower : ℝ := -(1 + ε)
  let outerUpper : ℝ := 1 + ε
  let firstLower : ℝ := scale * a' * (x.1 - 2 * r)
  let firstUpper : ℝ := scale * a' * (x.1 + 2 * r)
  let secondLower : ℝ := a' * (y - x.1 - r)
  let secondUpper : ℝ := a' * (y - x.1 + r)
  have hinvScale : 1 ≤ invScale := by
    have hinvNonneg : 0 ≤ invScale := Real.rpow_nonneg
      (NNReal.coe_nonneg _) _
    calc
      1 = scale * invScale := by simpa [scale, invScale] using hpowprod.symm
      _ ≤ 1 * invScale := mul_le_mul_of_nonneg_right hsle hinvNonneg
      _ = invScale := one_mul _
  have hfirstScale := h.measure_fullSegmentCorridorReturn_scale prefixH hprefix
    (a' * outerLower) (a' * outerUpper) firstLower firstUpper
  have hprefixProb :
      P (fullSegmentCorridorReturnEvent X 0 prefixH
        (a' * outerLower) (a' * outerUpper) firstLower firstUpper) =
      P (fullSegmentCorridorReturnEvent X 0 1
        (a' * outerLower * invScale) (a' * outerUpper * invScale)
        (a' * (x.1 - 2 * r)) (a' * (x.1 + 2 * r))) := by
    rw [hfirstScale]
    have hcancel (z : ℝ) : (scale * z) * invScale = z := by
      calc
        (scale * z) * invScale = z * (scale * invScale) := by ring
        _ = z := by simpa [scale, invScale] using congrArg (fun w : ℝ => z * w) hpowprod
    have hcancelL : firstLower * invScale = a' * (x.1 - 2 * r) := by
      dsimp [firstLower]
      convert hcancel (a' * (x.1 - 2 * r)) using 1
      ring
    have hcancelU : firstUpper * invScale = a' * (x.1 + 2 * r) := by
      dsimp [firstUpper]
      convert hcancel (a' * (x.1 + 2 * r)) using 1
      ring
    rw [hcancelL, hcancelU]
  have hbinSubset : endpointBinEvent X a' r x.1 ⊆
      fullSegmentCorridorReturnEvent X 0 1
        (a' * outerLower * invScale) (a' * outerUpper * invScale)
        (a' * (x.1 - 2 * r)) (a' * (x.1 + 2 * r)) := by
    have hε : 0 < ε := by linarith
    have hinvNonneg : 0 ≤ invScale := Real.rpow_nonneg (NNReal.coe_nonneg _) _
    have hfactor : 1 + ε ≤ (1 + ε) * invScale := by
      calc
        1 + ε = (1 + ε) * 1 := by ring
        _ ≤ (1 + ε) * invScale :=
          mul_le_mul_of_nonneg_left hinvScale (by linarith)
    have hfactorA : a' * (1 + ε) ≤ a' * ((1 + ε) * invScale) :=
      mul_le_mul_of_nonneg_left hfactor ha'.le
    apply fullSegmentCorridorReturnEvent_mono_bounds X 0 1
    · dsimp [outerLower]
      calc
        a' * (-(1 + ε)) * invScale = -(a' * ((1 + ε) * invScale)) := by ring
        _ ≤ -(a' * (1 + ε)) := by linarith
        _ ≤ -a' := by nlinarith [mul_nonneg ha'.le (le_of_lt hε)]
    · dsimp [outerUpper]
      calc
        a' ≤ a' * (1 + ε) := by nlinarith [mul_nonneg ha'.le (le_of_lt hε)]
        _ ≤ a' * ((1 + ε) * invScale) := hfactorA
        _ = a' * (1 + ε) * invScale := by ring
    · nlinarith [mul_pos ha' hr]
    · nlinarith [mul_pos ha' hr]
  have hprefixLE : P (endpointBinEvent X a' r x.1) ≤
      P (fullSegmentCorridorReturnEvent X 0 prefixH
        (a' * outerLower) (a' * outerUpper) firstLower firstUpper) := by
    rw [hprefixProb]
    exact measure_mono hbinSubset
  have hbufferLower :
      0 < (((prefixH : ℝ) ^ (1 / α)) - 1) * x.1 +
        3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r := by
    have hδ : 0 ≤ 1 - (prefixH : ℝ) ^ (1 / α) := sub_nonneg.mpr hsle
    have hδsmall : 1 - (prefixH : ℝ) ^ (1 / α) < r := by
      have hbase : (prefixH : ℝ) = 1 - (T : ℝ) * a' ^ α := by
        calc
          (prefixH : ℝ) = 1 - (tail : ℝ) := hprefixCo
          _ = 1 - (T : ℝ) * a' ^ α := by rw [htailCo]
      simpa only [hbase] using hdelta
    have hx1 := x.2.1
    have hx2 := x.2.2
    have hdx : (1 - (prefixH : ℝ) ^ (1 / α)) * x.1 ≤
        1 - (prefixH : ℝ) ^ (1 / α) := by
      calc
        _ = x.1 * (1 - (prefixH : ℝ) ^ (1 / α)) := by ring
        _ ≤ 1 * (1 - (prefixH : ℝ) ^ (1 / α)) :=
          mul_le_mul_of_nonneg_right hx2 hδ
        _ = _ := one_mul _
    have hsr : (prefixH : ℝ) ^ (1 / α) * r ≤ r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsle hr.le
    nlinarith
  have hbufferUpper :
      0 < (1 - (prefixH : ℝ) ^ (1 / α)) * x.1 +
        3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r := by
    have hδ : 0 ≤ 1 - (prefixH : ℝ) ^ (1 / α) := sub_nonneg.mpr hsle
    have hδsmall : 1 - (prefixH : ℝ) ^ (1 / α) < r := by
      have hbase : (prefixH : ℝ) = 1 - (T : ℝ) * a' ^ α := by
        calc
          (prefixH : ℝ) = 1 - (tail : ℝ) := hprefixCo
          _ = 1 - (T : ℝ) * a' ^ α := by rw [htailCo]
      simpa only [hbase] using hdelta
    have hx1 := x.2.1
    have hx2 := x.2.2
    have hdx : -(1 - (prefixH : ℝ) ^ (1 / α)) ≤
        (1 - (prefixH : ℝ) ^ (1 / α)) * x.1 := by
      nlinarith [mul_le_mul_of_nonneg_right hx1 hδ]
    have hsr : (prefixH : ℝ) ^ (1 / α) * r ≤ r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsle hr.le
    nlinarith
  have hcorridorLower :
      a' * outerLower - firstLower ≤ a' * (outerLower - x.1 + 3 * r) := by
    have hdiff : a' * (outerLower - x.1 + 3 * r) -
        (a' * outerLower - firstLower) =
        a' * ((((prefixH : ℝ) ^ (1 / α) - 1) * x.1) +
          3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r) := by
      dsimp [outerLower, firstLower, scale]
      ring
    have hnonneg := mul_nonneg ha'.le hbufferLower.le
    linarith [hdiff]
  have hcorridorUpper :
      a' * (outerUpper - x.1 - 3 * r) ≤ a' * outerUpper - firstUpper := by
    have hdiff : (a' * outerUpper - firstUpper) -
        a' * (outerUpper - x.1 - 3 * r) =
        a' * ((1 - (prefixH : ℝ) ^ (1 / α)) * x.1 +
          3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r) := by
      dsimp [outerUpper, firstUpper, scale]
      ring
    have hnonneg := mul_nonneg ha'.le hbufferUpper.le
    linarith [hdiff]
  let tailAtCut : Set Ω :=
    fullSegmentCorridorReturnEvent X prefixH tail
      (a' * (outerLower - x.1 + 3 * r))
      (a' * (outerUpper - x.1 - 3 * r)) secondLower secondUpper
  let exactTail : Set Ω :=
    fullSegmentCorridorReturnEvent X prefixH tail
      (a' * outerLower - firstLower)
      (a' * outerUpper - firstUpper) secondLower secondUpper
  have htailSubset : tailAtCut ⊆ exactTail := by
    apply fullSegmentCorridorReturnEvent_mono_bounds X prefixH tail
    · exact hcorridorLower
    · exact hcorridorUpper
    · rfl
    · rfl
  have htailOrigin :
      P (fullSegmentCorridorReturnEvent X 0 tail
        (a' * (outerLower - x.1 + 3 * r))
        (a' * (outerUpper - x.1 - 3 * r)) secondLower secondUpper) =
      P tailAtCut := by
    simpa [tailAtCut] using
      h.measure_fullSegmentCorridorReturn_shift prefixH tail
        (a' * (outerLower - x.1 + 3 * r))
        (a' * (outerUpper - x.1 - 3 * r)) secondLower secondUpper
  have htailScale := h.measure_scaled_time_fullReturn a' ha' T hT
    (outerLower - x.1 + 3 * r) (outerUpper - x.1 - 3 * r)
    (y - x.1 - r) (y - x.1 + r)
  have htailLE :
      P (fullSegmentCorridorReturnEvent X 0 T
        (outerLower - x.1 + 3 * r) (outerUpper - x.1 - 3 * r)
        (y - x.1 - r) (y - x.1 + r)) ≤ P exactTail := by
    calc
      _ = P (fullSegmentCorridorReturnEvent X 0 tail
          (a' * (outerLower - x.1 + 3 * r))
          (a' * (outerUpper - x.1 - 3 * r)) secondLower secondUpper) := by
        simpa [tail, stableEntranceHorizon] using htailScale.symm
      _ = P tailAtCut := htailOrigin
      _ ≤ P exactTail := measure_mono htailSubset
  have htailLE' :
      P (fullSegmentCorridorReturnEvent X 0 T
        (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
        (y - x.1 - r) (y - x.1 + r)) ≤ P exactTail := by
    have hevent :
        fullSegmentCorridorReturnEvent X 0 T
          (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
          (y - x.1 - r) (y - x.1 + r) =
        fullSegmentCorridorReturnEvent X 0 T
          (outerLower - x.1 + 3 * r) (outerUpper - x.1 - 3 * r)
          (y - x.1 - r) (y - x.1 + r) := by
      congr 1
      all_goals dsimp [outerLower, outerUpper]
      all_goals ring_nf
    rw [hevent]
    exact htailLE
  have hsum : prefixH + tail = 1 := tsub_add_cancel_of_le htailLt.le
  have hglue := h.measure_fullReturn_ge_return_mul_return
    prefixH tail hprefix htail (a' * outerLower) (a' * outerUpper)
    firstLower firstUpper secondLower secondUpper
  rw [hsum] at hglue
  have hglobalSubset :
      fullSegmentCorridorReturnEvent X 0 1
        (a' * outerLower) (a' * outerUpper)
        (firstLower + secondLower) (firstUpper + secondUpper) ⊆
      endpointTargetEvent X a' ε c b := by
    intro ω hω
    refine ⟨?_, ?_⟩
    · convert hω.1 using 1
      dsimp [outerLower, outerUpper]
      ring_nf
    · rcases hω.2 with ⟨hlo, hhi⟩
      have hloBound : a' * c < firstLower + secondLower := by
        have hbuf : 0 < ((y - c - 4 * r) +
            (((prefixH : ℝ) ^ (1 / α) - 1) * x.1 +
              3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r)) :=
          add_pos (by linarith [h4rc]) hbufferLower
        dsimp [firstLower, secondLower, scale]
        nlinarith [mul_pos ha' hbuf]
      have hhiBound : firstUpper + secondUpper < a' * b := by
        have hbuf : 0 < ((b - y - 4 * r) +
            ((1 - (prefixH : ℝ) ^ (1 / α)) * x.1 +
              3 * r - 2 * ((prefixH : ℝ) ^ (1 / α)) * r)) :=
          add_pos (by linarith [h4rb]) hbufferUpper
        dsimp [firstUpper, secondUpper, scale]
        nlinarith [mul_pos ha' hbuf]
      exact ⟨lt_trans hloBound hlo, le_of_lt (lt_trans hhi hhiBound)⟩
  have hfinalLE :
      P (fullSegmentCorridorReturnEvent X 0 1
        (a' * outerLower) (a' * outerUpper)
        (firstLower + secondLower) (firstUpper + secondUpper)) ≤
      P (endpointTargetEvent X a' ε c b) :=
    measure_mono hglobalSubset
  have hprodLE :
      P (fullSegmentCorridorReturnEvent X 0 T
        (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
        (y - x.1 - r) (y - x.1 + r)) *
        P (endpointBinEvent X a' r x.1) ≤
      P (fullSegmentCorridorReturnEvent X 0 prefixH
        (a' * outerLower) (a' * outerUpper) firstLower firstUpper) *
      P exactTail := by
    calc
      _ ≤ P (fullSegmentCorridorReturnEvent X 0 T
            (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
            (y - x.1 - r) (y - x.1 + r)) *
          P (fullSegmentCorridorReturnEvent X 0 prefixH
            (a' * outerLower) (a' * outerUpper) firstLower firstUpper) :=
        mul_le_mul_of_nonneg_left hprefixLE bot_le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        htailLE' bot_le
      _ = _ := mul_comm _ _
  calc
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 prefixH
        (a' * outerLower) (a' * outerUpper) firstLower firstUpper) *
        P exactTail := hprodLE
    _ ≤ P (fullSegmentCorridorReturnEvent X 0 1
        (a' * outerLower) (a' * outerUpper)
        (firstLower + secondLower) (firstUpper + secondUpper)) := hglue
    _ ≤ P (endpointTargetEvent X a' ε c b) := hfinalLE

/-- A probability-level form of the endpoint comparison. The finite-cover
argument gives a fixed multiplicative constant between the centered corridor
probability and the endpoint-constrained, slightly wider corridor probability.
-/
theorem IsStableLevyProcess.eventually_centeredCorridorProbability_le_endpointCorridor_mul_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c b ε : ℝ) (hc : -1 ≤ c) (hcb : c < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (centeredCorridorProbability P X a).toReal ≤
          D * (P (fullSegmentCorridorIocReturnEvent X 0 1
            (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))).toReal := by
  classical
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let Center := {x : ℝ // x ∈ Set.Icc (-1) 1}
  let y : ℝ := (b + c) / 2
  let r : ℝ := min (ε / 8) ((b - c) / 16)
  have hyc : c < y := by dsimp [y]; linarith
  have hyb : y < b := by dsimp [y]; linarith
  have hyLower : -1 < y := lt_of_le_of_lt hc hyc
  have hyUpper : y < 1 := lt_of_lt_of_le hyb hb
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by linarith)
  have h4rε : 4 * r < ε := by
    have hrε : r ≤ ε / 8 := min_le_left _ _
    dsimp [r] at hrε
    nlinarith
  have h4rc : 4 * r < y - c := by
    have hrbc : r ≤ (b - c) / 16 := min_le_right _ _
    have hyc' : y - c = (b - c) / 2 := by dsimp [y]; ring
    dsimp [r] at hrbc
    rw [hyc']
    nlinarith [hcb]
  have h4rb : 4 * r < b - y := by
    have hrbc : r ≤ (b - c) / 16 := min_le_right _ _
    have hyb' : b - y = (b - c) / 2 := by dsimp [y]; ring
    dsimp [r] at hrbc
    rw [hyb']
    nlinarith [hcb]
  obtain ⟨F, hFcover⟩ := exists_finset_open_cover_Icc hr
  have hF : 0 < F.card := by
    apply Finset.card_pos.mpr
    obtain ⟨x, hx⟩ := hFcover 0 (by constructor <;> norm_num)
    exact ⟨x, hx.1⟩

  let entranceEvent (x : Center) (T : ℝ≥0) : Set Ω :=
    fullSegmentCorridorReturnEvent X 0 T
      (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
      (y - x.1 - r) (y - x.1 + r)
  have hexists (x : Center) : ∃ T : ℝ≥0, 0 < T ∧ 0 < P (entranceEvent x T) := by
    have hxlo := x.2.1
    have hxhi := x.2.2
    have hzeroLo : -1 - ε - x.1 + 3 * r < 0 := by linarith [h4rε]
    have hzeroHi : 0 < 1 + ε - x.1 - 3 * r := by linarith [h4rε]
    have htargetLo : -1 - ε - x.1 + 3 * r < y - x.1 - r := by
      have : 0 < 1 + y + ε - 4 * r := by linarith [hyLower, h4rε]
      linarith
    have htargetHi : y - x.1 + r < 1 + ε - x.1 - 3 * r := by
      have : 0 < 1 - y + ε - 4 * r := by linarith [hyUpper, h4rε]
      linarith
    exact h.exists_pos_time_measure_fullSegmentCorridorReturnEvent_pos
      (-1 - ε - x.1 + 3 * r) (1 + ε - x.1 - 3 * r)
      (y - x.1) r hzeroLo hzeroHi (by linarith [htargetLo])
      (by linarith [htargetHi]) hr hcdf
  let entranceTime (x : Center) : ℝ≥0 := Classical.choose (hexists x)
  have hentranceTime (x : Center) : 0 < entranceTime x :=
    (Classical.choose_spec (hexists x)).1
  let entranceProb (x : Center) : ℝ≥0∞ :=
    P (entranceEvent x (entranceTime x))
  have hentrancePos (x : Center) : 0 < entranceProb x :=
    (Classical.choose_spec (hexists x)).2
  let entranceProbReal (x : Center) : ℝ := (entranceProb x).toReal
  have hentranceRealPos (x : Center) : 0 < entranceProbReal x := by
    exact ENNReal.toReal_pos_iff.mpr
      ⟨hentrancePos x, measure_lt_top P _⟩
  have hbinEventually (x : Center) (hx : x ∈ F) :
      ∀ᶠ a : ℝ in l,
        (P (endpointBinEvent X a r x.1)).toReal ≤
          (P (endpointTargetEvent X a ε c b)).toReal /
            entranceProbReal x := by
    have hraw := eventually_fixed_endpoint_bin_le_target h b c ε y r x
      hr h4rε h4rc h4rb (entranceTime x) (hentranceTime x)
    filter_upwards [hraw] with a ha
    have hreal : entranceProbReal x * (P (endpointBinEvent X a r x.1)).toReal ≤
        (P (endpointTargetEvent X a ε c b)).toReal := by
      rw [← ENNReal.toReal_mul]
      have hraw' :
          P (entranceEvent x (entranceTime x)) *
            P (endpointBinEvent X a r x.1) ≤
          P (endpointTargetEvent X a ε c b) := by
        simpa [entranceProb, entranceEvent, entranceTime] using ha
      exact (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (measure_lt_top P _).ne (measure_lt_top P _).ne)
        (measure_lt_top P _).ne).mpr hraw'
    exact (le_div_iff₀ (hentranceRealPos x)).2 (by
      simpa [div_eq_mul_inv, mul_comm] using hreal)
  have hbinEventuallyAll : ∀ᶠ a : ℝ in l,
      ∀ x ∈ F,
        (P (endpointBinEvent X a r x.1)).toReal ≤
          (P (endpointTargetEvent X a ε c b)).toReal /
            entranceProbReal x := by
    apply F.eventually_all.2
    intro x hx
    exact hbinEventually x hx

  let q : ℝ → ℝ := fun a => (centeredCorridorProbability P X a).toReal
  let e : ℝ → ℝ := fun a => (P (endpointTargetEvent X a ε c b)).toReal
  let D : ℝ := ∑ x ∈ F, (entranceProbReal x)⁻¹
  have hD : 0 < D := by
    dsimp [D]
    apply Finset.sum_pos'
    · intro x hx
      exact (inv_nonneg.mpr (le_of_lt (hentranceRealPos x)))
    · obtain ⟨x, hx⟩ := Finset.card_pos.mp hF
      exact ⟨x, hx, inv_pos.mpr (hentranceRealPos x)⟩

  have hcoverReal (a : ℝ) (ha : 0 < a) :
      q a ≤ ∑ x ∈ F, (P (endpointBinEvent X a r x.1)).toReal := by
    have hsubset : fullSegmentCorridorEvent X 0 1 (-a) a ⊆
        ⋃ x ∈ F, endpointBinEvent X a r x.1 := by
      intro ω hω
      have hvalue := fullSegmentCorridorEvent_subset_endpoint_Icc X 0 1
        (-a) a hω
      let z : ℝ := segmentIncrement X 0 1 ω ⊤ / a
      have hz : z ∈ Set.Icc (-1) 1 := by
        constructor
        · change -1 ≤ segmentIncrement X 0 1 ω ⊤ / a
          exact (le_div_iff₀ ha).2 (by nlinarith [hvalue.1])
        · change segmentIncrement X 0 1 ω ⊤ / a ≤ 1
          exact (div_le_iff₀ ha).2 (by nlinarith [hvalue.2])
      obtain ⟨x, hxF, hxz⟩ := hFcover z hz
      have hval : segmentIncrement X 0 1 ω ⊤ = a * z := by
        dsimp [z]
        field_simp [ha.ne']
      have hxbin : segmentIncrement X 0 1 ω ⊤ ∈
          Set.Ioo (a * (x.1 - r)) (a * (x.1 + r)) := by
        constructor
        · have hmul := mul_lt_mul_of_pos_left hxz.1 ha
          nlinarith [hval]
        · have hmul := mul_lt_mul_of_pos_left hxz.2 ha
          nlinarith [hval]
      refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxF, ?_⟩⟩
      change ω ∈ fullSegmentCorridorEvent X 0 1 (-a) a ∩
        {ω | segmentIncrement X 0 1 ω ⊤ ∈
          Set.Ioo (a * (x.1 - r)) (a * (x.1 + r))}
      exact ⟨hω, hxbin⟩
    have hcoverProb : centeredCorridorProbability P X a ≤
        ∑ x ∈ F, P (endpointBinEvent X a r x.1) := by
      change P (fullSegmentCorridorEvent X 0 1 (-a) a) ≤ _
      calc
        _ ≤ P (⋃ x ∈ F, endpointBinEvent X a r x.1) := measure_mono hsubset
        _ ≤ _ := measure_biUnion_finset_le _ _
    have hsumNeTop : (∑ x ∈ F, P (endpointBinEvent X a r x.1)) ≠ ∞ := by
      apply ENNReal.sum_ne_top.mpr
      intro x hx
      exact (measure_lt_top P _).ne
    have hcoverReal' := (ENNReal.toReal_le_toReal
      (measure_lt_top P _).ne hsumNeTop).mpr hcoverProb
    rw [ENNReal.toReal_sum (by
      intro x hx
      exact (measure_lt_top P _).ne)] at hcoverReal'
    exact hcoverReal'

  have hqPos : ∀ᶠ a : ℝ in l, 0 < q a := by
    obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hprob : 0 < centeredCorridorProbability P X a := by
      dsimp [centeredCorridorProbability]
      have ha' : 0 < a := ha
      exact h.measure_fullSegmentCorridor_pos (-a) a (neg_neg_of_pos ha') ha' hpos hneg
    dsimp [q]
    exact ENNReal.toReal_pos_iff.mpr ⟨hprob, measure_lt_top P _⟩

  have hbound : ∀ᶠ a : ℝ in l, q a ≤ D * e a := by
    filter_upwards [self_mem_nhdsWithin, hbinEventuallyAll] with a ha hbins
    have ha' : 0 < a := ha
    have hcover := hcoverReal a ha'
    have hsum : (∑ x ∈ F, (P (endpointBinEvent X a r x.1)).toReal) ≤
        ∑ x ∈ F, e a / entranceProbReal x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hbins x hx
    have hsumEq : (∑ x ∈ F, e a / entranceProbReal x) = e a * D := by
      dsimp [D]
      simp only [div_eq_mul_inv]
      rw [Finset.mul_sum]
    calc
      q a ≤ ∑ x ∈ F, (P (endpointBinEvent X a r x.1)).toReal := hcover
      _ ≤ ∑ x ∈ F, e a / entranceProbReal x := hsum
      _ = D * e a := by rw [hsumEq, mul_comm]

  exact ⟨D, hD, by
    simpa [q, e, endpointTargetEvent] using hbound⟩

/-- The endpoint-constrained comparison in Mogulskii's Lemma 2. For any
`-1 ≤ c < b ≤ 1`, the logarithm of the centered corridor probability is no
larger than the endpoint-constrained, slightly wider corridor logarithm up
to a fixed additive constant. The endpoint window retains the source's
left-open, right-closed convention. -/
theorem IsStableLevyProcess.eventually_one_sub_le_log_corridor_div_endpointCorridor_of_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c b ε δ : ℝ) (hc : -1 ≤ c) (hcb : c < b) (hb : b ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((centeredCorridorProbability P X a).toReal) /
          Real.log ((P (fullSegmentCorridorIocReturnEvent X 0 1
            (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))).toReal) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let q : ℝ → ℝ := fun a => (centeredCorridorProbability P X a).toReal
  let e : ℝ → ℝ := fun a => (P (endpointTargetEvent X a ε c b)).toReal
  obtain ⟨D, hD, hbound⟩ :=
    h.eventually_centeredCorridorProbability_le_endpointCorridor_mul_of_cdf
      hcdf c b ε hc hcb hb hε
  have hprobBound : ∀ᶠ a : ℝ in l, q a ≤ D * e a := by
    simpa [q, e, endpointTargetEvent] using hbound
  have hqPos : ∀ᶠ a : ℝ in l, 0 < q a := by
    obtain ⟨hneg, hpos⟩ :=
      h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hprob : 0 < centeredCorridorProbability P X a := by
      dsimp [centeredCorridorProbability]
      exact h.measure_fullSegmentCorridor_pos (-a) a
        (neg_neg_of_pos ha) ha hpos hneg
    dsimp [q]
    exact ENNReal.toReal_pos_iff.mpr ⟨hprob, measure_lt_top P _⟩
  have hePos : ∀ᶠ a : ℝ in l, 0 < e a := by
    filter_upwards [hqPos, hprobBound] with a hqa hba
    dsimp [e, endpointTargetEvent] at hba ⊢
    dsimp [q] at hqa
    by_contra hnot
    have hnonpos : (P (fullSegmentCorridorIocReturnEvent X 0 1
        (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))).toReal ≤ 0 :=
      le_of_not_gt hnot
    nlinarith [mul_pos hD hqa]

  obtain ⟨_, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have heMeasureZero : Tendsto
      (fun a : ℝ => P (endpointTargetEvent X a ε c b)) l (𝓝 0) := by
    have hwide := h.tendsto_measure_scaledFullCorridor_zero hpos
      (-(1 + ε)) (1 + ε)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwide
    · exact Eventually.of_forall fun _ => bot_le
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have hsubset : endpointTargetEvent X a ε c b ⊆
          fullSegmentCorridorEvent X 0 1
            (a * (-(1 + ε))) (a * (1 + ε)) := by
        intro ω hω
        simpa [endpointTargetEvent, fullSegmentCorridorIocReturnEvent,
          mul_comm, mul_left_comm, mul_assoc] using hω.1
      exact measure_mono hsubset
  have heZero : Tendsto e l (𝓝 0) := by
    change Tendsto (fun a : ℝ =>
      (P (endpointTargetEvent X a ε c b)).toReal) l (𝓝 0)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp heMeasureZero
  have heWithin : Tendsto e l (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨heZero, hePos⟩
  let g : ℝ → ℝ := fun a => Real.log (e a)
  have hg : Tendsto g l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp heWithin
  have hfg : (fun a => Real.log (q a)) ≤ᶠ[l]
      (fun a => g a + Real.log D) := by
    filter_upwards [hprobBound, hqPos, hePos] with a hba hqa hea
    have hlog := Real.log_le_log hqa (by
      simpa [q, e, endpointTargetEvent] using hba)
    have hlog' : Real.log (q a) ≤ Real.log (D * e a) := by
      simpa [e, endpointTargetEvent] using hlog
    rw [Real.log_mul hD.ne' hea.ne'] at hlog'
    simpa [g, add_comm] using hlog'
  have hratio := Asymptotics.eventually_one_sub_le_ratio_of_additive_bound
    (Real.log D) hfg hg δ hδ
  simpa [q, e, g, endpointTargetEvent, fullSegmentCorridorIocReturnEvent,
    mul_comm, mul_left_comm, mul_assoc] using hratio


end ProbabilityTheory

end
