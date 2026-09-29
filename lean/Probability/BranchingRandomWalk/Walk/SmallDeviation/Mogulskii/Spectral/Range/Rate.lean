module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Diffusive.Brownian
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Range.Asymptotics
public import Probability.Process.Path.Oscillation
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Small-width logarithmic bound for Brownian range events

The corrected fixed finite corridor cover gives the Brownian range event a
finite sum of full-spectrum corridor bounds.  This file extracts its
small-width exponential rate without introducing a minimum over the
approximating lattice walk.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

open ProbabilityTheory.Process.Path

/-- Principal exponential for a corridor in a fixed finite minimum cover. -/
noncomputable def finiteCoverCorridorExponential (count : ℕ) (width : ℝ) : ℝ :=
  Real.exp (-(Real.pi ^ 2) /
    (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2))

/-- Complete-spectrum finite-cover correction at a fixed width. -/
noncomputable def finiteCoverRangeBound (count : ℕ) (width : ℝ) : ℝ :=
  (count : ℝ) * (8 * finiteCoverCorridorExponential count width)

/-- At a fixed finite-cover count, the Brownian range event is bounded by the
complete-spectrum geometric correction for corridors of width
`width * (1 + 3 / count)`. -/
theorem brownianRangeOscillationMass_le_fixedSpectralSum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    rangeOscillationMass (P := P) hcontinuous width ≤
      ∑ _j : Fin count, ENNReal.ofReal (4 *
        (Real.exp (-(Real.pi ^ 2) /
            (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) /
            (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2))))) := by
  have h := brownianRangeOscillation_le_fixedSpectralCover
    hB hcontinuous hmeasurable hwidth hcount
  have hcorridor : width + 3 * (width / (count : ℝ)) =
      (1 + 3 / (count : ℝ)) * width := by
    field_simp
  rw [rangeOscillationMass]
  simpa only [hcorridor] using h

/-- Once the fixed corridor eigenvalue is below `1/2`, the full-spectrum
geometric correction is at most twice its leading exponential.  The finite
cover contributes only its fixed cardinality. -/
theorem brownianRangeOscillationMass_le_smallWidthExponential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count)
    (hsmall : Real.exp (-(Real.pi ^ 2) /
      (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)) < 1 / 2) :
    rangeOscillationMass (P := P) hcontinuous width ≤
      ENNReal.ofReal ((count : ℝ) * (8 * Real.exp (-(Real.pi ^ 2) /
        (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)))) := by
  let r : ℝ := Real.exp (-(Real.pi ^ 2) /
    (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2))
  have hrpos : 0 < r := by positivity
  have hden : 0 < 1 - r := by linarith [hsmall]
  have hratio : 4 * (r / (1 - r)) ≤ 8 * r := by
    field_simp [hden.ne']
    have hgap : 0 < 1 - 2 * r := by linarith [hsmall]
    nlinarith [mul_pos hrpos hgap]
  have hcover := brownianRangeOscillationMass_le_fixedSpectralSum
    hB hcontinuous hmeasurable hwidth hcount
  calc
    rangeOscillationMass (P := P) hcontinuous width ≤
        ∑ _j : Fin count, ENNReal.ofReal (4 * (r / (1 - r))) := by
      simpa [r] using hcover
    _ ≤ ∑ _j : Fin count, ENNReal.ofReal (8 * r) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal hratio
    _ = ENNReal.ofReal ((count : ℝ) * (8 * r)) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity)]

/-- A Brownian path confined to a centered closed corridor has range
oscillation at most its width. -/
theorem brownianRangeOscillationMass_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} (hwidth : 0 < width) :
    rangeOscillationMass (P := P) hcontinuous width ≠ 0 := by
  let pathLaw := P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
  have hclosed := ofReal_exp_neg_pi_sq_div_two_rho_sq_width_sq_le_brownian_closedCorridor
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    hwidth hB hcontinuous hmeasurable
  have hsub : (Skorokhod.ofContinuousMap) ⁻¹'
      Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2) ⊆
      ProbabilityTheory.Process.Path.rangeOscillationSet width := by
    intro path hpath
    change ∀ t, -(width / 2) ≤ Skorokhod.ofContinuousMap path t ∧
      Skorokhod.ofContinuousMap path t ≤ width / 2 at hpath
    simp only [Skorokhod.ofContinuousMap_apply] at hpath
    change path ∈ ProbabilityTheory.Process.Path.rangeOscillationSet width
    simp only [ProbabilityTheory.Process.Path.rangeOscillationSet,
      Set.mem_iInter, Set.mem_ofPred_eq]
    intro s t
    apply abs_sub_le_iff.mpr
    constructor
    · have hs := (hpath s).2
      have ht := (hpath t).1
      nlinarith
    · have hs := (hpath s).1
      have ht := (hpath t).2
      nlinarith
  have hmap : pathLaw.map Skorokhod.ofContinuousMap =
      P.map (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath B hcontinuous) := by
    dsimp [pathLaw]
    rw [Measure.map_map]
    · exact Skorokhod.measurable_ofContinuousMap
    · exact ProbabilityTheory.measurable_continuousunitIntervalPath
        B hcontinuous hmeasurable
  have hle :
      P.map (Skorokhod.ofContinuousMap ∘
        ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) ≤
        rangeOscillationMass (P := P) hcontinuous width := by
    rw [← hmap, Measure.map_apply Skorokhod.measurable_ofContinuousMap
      (Skorokhod.isClosed_rangeInClosedInterval _ _).measurableSet]
    exact measure_mono hsub
  intro hz
  have hpos : 0 < ENNReal.ofReal
      (Real.exp (-(Real.pi ^ 2) /
        (2 * (1 / 2 : ℝ) ^ 2 * width ^ 2))) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hlower := hclosed.trans hle
  rw [hz] at hlower
  exact (not_le_of_gt hpos) hlower

/-- The corridor eigenvalue exponential tends to zero as its diffusive width
shrinks to zero through positive values. -/
theorem tendsto_corridorExponential_nhdsGT_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun width : ℝ => Real.exp (-(Real.pi ^ 2) /
      (2 * (c * width) ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscaled : Tendsto (fun width : ℝ => c * width)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun width : ℝ => c * width) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    · filter_upwards [self_mem_nhdsWithin] with width hwidth
      exact mul_pos hc hwidth
  have hscaledZero : Tendsto (fun width : ℝ => c * width)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hscaled.mono_right nhdsWithin_le_nhds
  have hsquare : Tendsto (fun width : ℝ => (c * width) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using hscaledZero.pow 2, ?_⟩
    filter_upwards [hscaled.eventually self_mem_nhdsWithin] with width hwidth
    exact sq_pos_of_pos hwidth
  have hinv := tendsto_inv_nhdsGT_zero.comp hsquare
  have hcoef : 0 < Real.pi ^ 2 / 2 := by positivity
  have hlarge := hinv.const_mul_atTop hcoef
  have hnegative : Tendsto (fun width : ℝ =>
      -(Real.pi ^ 2 / 2 * ((c * width) ^ 2)⁻¹))
      (𝓝[>] (0 : ℝ)) atBot := by
    exact tendsto_neg_atTop_atBot.comp hlarge
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with width hwidth
  have hne : c * width ≠ 0 := ne_of_gt (mul_pos hc hwidth)
  apply congrArg Real.exp
  field_simp [hne]

/-- For a fixed cover size, the logarithmic Brownian range upper rate is the
spectral rate of the slightly enlarged corridors. -/
theorem eventually_scaledLog_brownianRangeOscillationMass_le_fixedCover
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℕ → ℝ}
    (hwidth : Tendsto width atTop (𝓝[>] (0 : ℝ)))
    {count : ℕ} (hcount : 0 < count) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      width n ^ 2 * Real.log
          (rangeOscillationMass (P := P) hcontinuous (width n)).toReal ≤
        -(Real.pi ^ 2) / (2 * (1 + 3 / (count : ℝ)) ^ 2) + ε := by
  let c : ℝ := 1 + 3 / (count : ℝ)
  let a : ℝ := Real.pi ^ 2 / 2
  let constant : ℝ := (count : ℝ) * 8
  let mass : ℕ → ENNReal := fun n =>
    rangeOscillationMass (P := P) hcontinuous (width n)
  let envelope : ℕ → ℝ := fun n =>
    constant * Real.exp (-a / (c * width n) ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n := by
    have h := hwidth.eventually self_mem_nhdsWithin
    simpa using h
  have hexpWidth : Tendsto (fun w : ℝ => Real.exp (-a / (c * w) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hbase := tendsto_corridorExponential_nhdsGT_zero (c := c) hc
    have hbase' : Tendsto (fun w : ℝ => Real.exp (-a / (c * w) ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      convert hbase using 1
      dsimp [a]
      ring_nf
    exact hbase'
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (-a / (c * width n) ^ 2) < 1 / 2 := by
    have hsmall' := (hexpWidth.comp hwidth).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall'] with n hn
    simpa using hn
  have hprob : ∀ᶠ n : ℕ in atTop,
      mass n ≤ ENNReal.ofReal (envelope n) := by
    filter_upwards [hwidthPos, hsmall] with n hnwidth hneigen
    have hsmallCorridor : Real.exp (-(Real.pi ^ 2) /
        (2 * ((1 + 3 / (count : ℝ)) * width n) ^ 2)) < 1 / 2 := by
      have hz : c * width n ≠ 0 := ne_of_gt (mul_pos hc hnwidth)
      convert hneigen using 1
      congr 1
      dsimp [a, c]
      field_simp [hz, Nat.cast_ne_zero.mpr hcount.ne']
    have hpoint := brownianRangeOscillationMass_le_smallWidthExponential
      hB hcontinuous hmeasurable hnwidth hcount hsmallCorridor
    have htarget : Real.exp (-(Real.pi ^ 2) /
          (2 * ((1 + 3 / (count : ℝ)) * width n) ^ 2)) =
        Real.exp (-a / (c * width n) ^ 2) := by
      apply congrArg Real.exp
      have hz : c * width n ≠ 0 := ne_of_gt (mul_pos hc hnwidth)
      dsimp [a, c]
      field_simp [hz, Nat.cast_ne_zero.mpr hcount.ne']
    rw [htarget] at hpoint
    have henv : envelope n =
        (count : ℝ) * (8 * Real.exp (-a / (c * width n) ^ 2)) := by
      dsimp [envelope, constant]
      ring
    rw [← henv] at hpoint
    simpa [mass] using hpoint
  have hmassPos : ∀ᶠ n : ℕ in atTop, mass n ≠ 0 := by
    filter_upwards [hwidthPos] with n hn
    exact brownianRangeOscillationMass_ne_zero hB hcontinuous hmeasurable hn
  have hmassOne : ∀ n, mass n ≤ 1 := by
    intro n
    dsimp [mass, rangeOscillationMass]
    calc
      P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
          (ProbabilityTheory.Process.Path.rangeOscillationSet (width n)) ≤
        P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous) Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := by
        rw [Measure.map_apply
          (ProbabilityTheory.measurable_continuousunitIntervalPath
            B hcontinuous hmeasurable) MeasurableSet.univ]
        exact measure_univ
  have hlog : ∀ᶠ n : ℕ in atTop,
      width n ^ 2 * Real.log (mass n).toReal ≤
        width n ^ 2 * Real.log (envelope n) := by
    filter_upwards [hprob, hwidthPos, hmassPos] with n hp hnwidth hpmass
    have hmassTop : mass n ≠ ⊤ := by
      exact ne_of_lt ((hmassOne n).trans_lt ENNReal.one_lt_top)
    have henvelopePos : 0 < envelope n := by
      dsimp [envelope]
      positivity
    have hreal : (mass n).toReal ≤ envelope n := by
      have h := (ENNReal.toReal_le_toReal hmassTop ENNReal.ofReal_ne_top).2 hp
      simpa [ENNReal.toReal_ofReal henvelopePos.le] using h
    have hmassRealPos : 0 < (mass n).toReal :=
      ENNReal.toReal_pos hpmass hmassTop
    have hlog := Real.log_le_log hmassRealPos hreal
    exact mul_le_mul_of_nonneg_left hlog (sq_nonneg (width n))
  have henvelopeLog : Tendsto (fun n : ℕ =>
      width n ^ 2 * Real.log (envelope n)) atTop
      (nhds (-(Real.pi ^ 2) / (2 * c ^ 2))) := by
    let widthReal : ℕ → ℝ := width
    have hwidthZero : Tendsto widthReal atTop (nhds 0) :=
      hwidth.mono_right nhdsWithin_le_nhds
    have hwidthSq : Tendsto (fun n => width n ^ 2) atTop (nhds 0) := by
      simpa using hwidthZero.pow 2
    have hlogEq : ∀ᶠ n : ℕ in atTop,
        width n ^ 2 * Real.log (envelope n) =
          width n ^ 2 * Real.log constant - a / c ^ 2 := by
      filter_upwards [hwidthPos] with n hn
      have hconst : constant ≠ 0 := ne_of_gt hconstant
      have hexp : Real.exp (-a / (c * width n) ^ 2) ≠ 0 := Real.exp_ne_zero _
      simp only [envelope]
      rw [Real.log_mul hconst hexp, Real.log_exp]
      have hcn : c * width n ≠ 0 := ne_of_gt (mul_pos hc hn)
      field_simp [hcn]
      ring
    have hlimit : Tendsto (fun n : ℕ =>
        width n ^ 2 * Real.log constant - a / c ^ 2) atTop
        (nhds (-(Real.pi ^ 2) / (2 * c ^ 2))) := by
      have h := hwidthSq.mul_const (Real.log constant)
      have h' := h.sub_const (a / c ^ 2)
      convert h' using 1
      dsimp [a]
      ring_nf
    exact hlimit.congr' (hlogEq.mono fun _ h => h.symm)
  have heventual : ∀ᶠ n : ℕ in atTop,
      width n ^ 2 * Real.log (envelope n) ≤
        -(Real.pi ^ 2) / (2 * c ^ 2) + ε :=
    (henvelopeLog.eventually (Iio_mem_nhds (by linarith :
      -(Real.pi ^ 2) / (2 * c ^ 2) <
        -(Real.pi ^ 2) / (2 * c ^ 2) + ε))).mono fun _ h => le_of_lt h
  filter_upwards [hlog, heventual] with n hn henv
  have hresult := hn.trans henv
  simpa [c] using hresult

/-- Letting the fixed cover mesh tend to zero recovers the sharp Brownian
small-range logarithmic upper rate.  The mesh index is chosen only after the
small-width limit for each fixed cover has been taken. -/
theorem eventually_scaledLog_brownianRangeOscillationMass_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℕ → ℝ}
    (hwidth : Tendsto width atTop (𝓝[>] (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      width n ^ 2 * Real.log
          (rangeOscillationMass (P := P) hcontinuous (width n)).toReal ≤
        -(Real.pi ^ 2) / 2 + ε := by
  let coverCount : ℕ → ℕ := fun k => k + 1
  let coverFactor : ℕ → ℝ := fun k => 1 + 3 / (coverCount k : ℝ)
  have hinv : Tendsto (fun k : ℕ => 3 / ((k + 1 : ℕ) : ℝ)) atTop
      (nhds 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    · funext k
      simp [Nat.cast_add]
  have hfactor : Tendsto coverFactor atTop (nhds 1) := by
    simpa [coverFactor, coverCount] using tendsto_const_nhds.add hinv
  have hdenom : Tendsto (fun k : ℕ => 2 * coverFactor k ^ 2) atTop
      (nhds 2) := by
    simpa using tendsto_const_nhds.mul (hfactor.pow 2)
  have hrate : Tendsto (fun k : ℕ =>
      -(Real.pi ^ 2) / (2 * coverFactor k ^ 2)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    convert (tendsto_const_nhds.div hdenom
      (by norm_num : (2 : ℝ) ≠ 0)) using 1
  have hrateEvent := hrate.eventually
    (Iio_mem_nhds (by linarith : -(Real.pi ^ 2) / 2 <
      -(Real.pi ^ 2) / 2 + ε / 2))
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hrateEvent
  let count := coverCount k
  have hcount : 0 < count := by dsimp [count, coverCount]; omega
  have hrateCount : -(Real.pi ^ 2) /
      (2 * (1 + 3 / (count : ℝ)) ^ 2) <
        -(Real.pi ^ 2) / 2 + ε / 2 := by
    have hk' := hk k le_rfl
    simpa [count, coverFactor, coverCount] using hk'
  have hfixed := eventually_scaledLog_brownianRangeOscillationMass_le_fixedCover
    hB hcontinuous hmeasurable hwidth hcount (ε := ε / 2) (by linarith)
  have hcombine : -(Real.pi ^ 2) /
      (2 * (1 + 3 / (count : ℝ)) ^ 2) + ε / 2 ≤
        -(Real.pi ^ 2) / 2 + ε := by
    linarith
  filter_upwards [hfixed] with n hn
  exact hn.trans hcombine

end ProbabilityTheory.RandomWalk.Mogulskii

end
