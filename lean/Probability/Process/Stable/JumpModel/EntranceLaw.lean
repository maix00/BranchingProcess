import Probability.Process.Stable.JumpModel.IndependentIncrements
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FullCorridor
import Probability.Process.Path.Skorokhod.Corridor.Segment
import Probability.Process.Path.Skorokhod.RationalTime
import Probability.Distributions.Stable.LevyMeasure.EntranceWindows
import Probability.Distributions.Stable.LevyMeasure.SignOfJumps
import Probability.Process.Levy.Jump.Intensity.Entrance.Canonical

/-!
# Transfer of a Poisson entrance event to a stable process

For stable index below one, a finite-variation Poisson jump model provides a
positive entrance event. Its rational-coordinate law identifies the event
for the given stable process, and càdlàg paths recover the full corridor.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private theorem monotone_rationalUnitCoe :
    Monotone (RationalGrid.unitCoe : RationalGrid.RationalUnitInterval → unitInterval) := by
  intro p q hpq
  change ((p : ℚ) : ℝ) ≤ ((q : ℚ) : ℝ)
  exact_mod_cast hpq

private theorem rationalUnitCoe_bot :
    RationalGrid.unitCoe ⊥ = (⊥ : unitInterval) := by
  apply Subtype.ext
  norm_num [RationalGrid.unitCoe]

private theorem rationalUnitCoe_top :
    RationalGrid.unitCoe ⊤ = (⊤ : unitInterval) := by
  apply Subtype.ext
  norm_num [RationalGrid.unitCoe]

/-- For 0 < α < 1, the CDF sign condition gives positive probability to a
complete fixed-corridor event with a prescribed endpoint window. A nonzero
endpoint uses the finite-variation Poisson jump model; the zero endpoint is
covered by the centered-corridor theorem. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero_of_poissonModel
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  let y : ℝ := c - b
  by_cases hy0 : y = 0
  · have hy0' : c - b = 0 := by simpa [y] using hy0
    obtain ⟨hneg, hpos⟩ := h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
    simpa [hy0'] using h.measure_fullSegmentCorridorReturn_pos_of_zero_mem
      (c - 1) (c + 1) (-ε) ε
      (by linarith [hc.2]) (by linarith [hc.1])
      (by linarith) hε hpos hneg
  · let margin : ℝ := min (min (1 - b) (1 + b)) (min (1 + c) (1 - c))
    have hmargin : 0 < margin := by
      dsimp [margin]
      apply lt_min
      · exact lt_min (by linarith [hb.2]) (by linarith [hb.1])
      · exact lt_min (by linarith [hc.1]) (by linarith [hc.2])
    let ρ : ℝ := min (margin / 4) (min (ε / 4) (|y| / 4))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      apply lt_min
      · positivity
      · apply lt_min
        · positivity
        · exact div_pos (abs_pos.mpr hy0) (by norm_num)
    have hρm : ρ ≤ margin / 4 := min_le_left _ _
    have hρε : ρ ≤ ε / 4 := (min_le_right _ _).trans (min_le_left _ _)
    have hρy : ρ ≤ |y| / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmargin_blo : margin ≤ 1 - b :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hmargin_bhi : margin ≤ 1 + b :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hmargin_clo : margin ≤ 1 + c :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hmargin_chi : margin ≤ 1 - c :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hγ : 0 < margin - 2 * ρ := by linarith
    have htwoρ : 2 * ρ < ε := by linarith
    let δ : ℝ := |y| / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let J : Set ℝ := Set.Ioo (y - ρ) (y + ρ)
    have hJ : MeasurableSet J := measurableSet_Ioo
    have hrad : 0 < |y| - ρ := by linarith [hρy]
    have hradR : |y| - ρ < |y| + ρ := by linarith [hρ]
    have hwindows := h.increments.strictlyStable.twoSidedLevyWindows_of_cdfAtZero
      T hT hα hcdf (r := |y| - ρ) (R := |y| + ρ) hrad hradR
    have hJpos : 0 < T.levyMeasure J := by
      by_cases hy : 0 < y
      · have habs : |y| = y := abs_of_pos hy
        have hset : Set.Ioo (|y| - ρ) (|y| + ρ) = J := by
          ext x
          simp only [Set.mem_Ioo, J]
          rw [habs]
        rw [← hset]
        exact hwindows.2
      · have hy' : y < 0 := lt_of_le_of_ne (le_of_not_gt hy) hy0
        have habs : |y| = -y := abs_of_neg hy'
        have hset : Set.Ioo (-(|y| + ρ)) (-(|y| - ρ)) = J := by
          ext x
          simp only [Set.mem_Ioo, J]
          rw [habs]
          constructor
          · rintro ⟨hx₁, hx₂⟩
            exact ⟨by linarith, by linarith⟩
          · rintro ⟨hx₁, hx₂⟩
            exact ⟨by linarith, by linarith⟩
        rw [← hset]
        exact hwindows.1
    have hJwindow : ∀ x ∈ J, |x - y| < ρ := by
      intro x hx
      change y - ρ < x ∧ x < y + ρ at hx
      rw [abs_lt]
      constructor <;> linarith
    have hJaway : ∀ x ∈ J, δ ≤ |x| := by
      intro x hx
      by_cases hy : 0 < y
      · have hxpos : 0 < x := by
          have habs : |y| = y := abs_of_pos hy
          have hρy' : ρ ≤ y / 4 := by simpa [habs] using hρy
          linarith [hx.1]
        have habs : |y| = y := abs_of_pos hy
        dsimp [δ]
        rw [abs_of_pos hxpos]
        have hρy' : ρ ≤ y / 4 := by simpa [habs] using hρy
        linarith [hx.1]
      · have hy' : y < 0 := lt_of_le_of_ne (le_of_not_gt hy) hy0
        have hxneg : x < 0 := by
          have habs : |y| = -y := abs_of_neg hy'
          have hρy' : ρ ≤ -y / 4 := by simpa [habs] using hρy
          linarith [hx.2]
        have habs : |y| = -y := abs_of_neg hy'
        dsimp [δ]
        rw [abs_of_neg hxneg]
        have hρy' : ρ ≤ -y / 4 := by simpa [habs] using hρy
        linarith [hx.2]
    let lower : ℝ := c - 1
    let upper : ℝ := c + 1
    have hl0 : lower + margin ≤ 0 := by dsimp [lower]; linarith
    have hu0 : 0 ≤ upper - margin := by dsimp [upper]; linarith
    have hly : lower + margin ≤ y := by dsimp [lower, y]; linarith
    have huy : y ≤ upper - margin := by dsimp [upper, y]; linarith
    obtain ⟨n, Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
        hPs, hPb, hds, hdb, hentrance⟩ :=
      exists_poissonEntrancePath_model_of_finiteVariation T.levyMeasure
        (h.increments.strictlyStable.levyMeasure_smallJumpMoment_lt_top
          T hT hα).ne
        (fun n => T.levyMeasure_largeJumpBand_lt_top n)
        hJ hJpos lower upper y ρ ε margin δ hρ hδ htwoρ
        hl0 hu0 hly huy hJwindow hJaway
    letI : MeasurableSpace Ωs := mΩs
    letI : MeasurableSpace Ωb := mΩb
    letI : IsProbabilityMeasure Ps := hPs
    letI : IsProbabilityMeasure Pb := hPb
    let Q : Measure (Ωs × Ωb) := Ps.prod Pb
    let Y : unitInterval → Ωs × Ωb → ℝ := fun t ω =>
      poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) t ω
    have hmodel : HasStableClockIncrements α μ (fun t : unitInterval => (t : ℝ))
        Y Q := by
      simpa [Y, Q] using
        h.increments.strictlyStable.hasStableClockIncrements_poissonEntrancePath
          T hT hα n hds hdb
    have hstart : ∀ᵐ ω ∂Q, Y ⊥ ω = 0 := hmodel.ae_start_eq_zero
    let modelEvent : Set (Ωs × Ωb) := {ω |
      (∀ t : unitInterval,
        lower + (margin - 2 * ρ) ≤ Y t ω ∧
          Y t ω ≤ upper - (margin - 2 * ρ)) ∧
      y - ε < Y ⊤ ω ∧ Y ⊤ ω < y + ε}
    have hmodelEvent : 0 < Q modelEvent := by
      simpa [modelEvent, Y, lower, upper] using hentrance
    let origR : RationalGrid.RationalUnitInterval → Ω → ℝ :=
      fun q ω => X (rationalUnitTime q) ω
    let modelR : RationalGrid.RationalUnitInterval → Ωs × Ωb → ℝ :=
      fun q ω => Y (RationalGrid.unitCoe q) ω
    have horigR : HasStableClockIncrements α μ
        (fun q : RationalGrid.RationalUnitInterval =>
          (RationalGrid.unitCoe q : ℝ)) origR P := by
      simpa only [origR, rationalUnitTime_coe] using
        h.increments.comp_time rationalUnitTime monotone_rationalUnitTime
          rationalUnitTime_bot
    have hmodelR : HasStableClockIncrements α μ
        (fun q : RationalGrid.RationalUnitInterval =>
          (RationalGrid.unitCoe q : ℝ)) modelR Q := by
      simpa only [modelR] using
        hmodel.comp_time RationalGrid.unitCoe monotone_rationalUnitCoe
          rationalUnitCoe_bot
    have horigMeas : AEMeasurable (fun ω q => origR q ω) P :=
      AEMeasurable.of_eval fun q => horigR.aemeasurable_eval q
    have hmodelMeas : AEMeasurable (fun ω q => modelR q ω) Q :=
      AEMeasurable.of_eval fun q => hmodelR.aemeasurable_eval q
    have hlaw := horigR.process_identDistrib_of_aemeasurable hmodelR
      horigMeas hmodelMeas
    have hcenterLaw := hlaw.comp measurable_centerRationalPath
    let targetSet := Skorokhod.rationalCoordinateCorridorReturnWithMargin
      (c - 1) (c + 1) (y - ε) (y + ε)
    let targetRationalEvent : Set Ω :=
      {ω | centerRationalPath (fun q => origR q ω) ∈ targetSet}
    let modelRationalEvent : Set (Ωs × Ωb) :=
      {ω | centerRationalPath (fun q => modelR q ω) ∈ targetSet}
    have hprobEq : P targetRationalEvent = Q modelRationalEvent := by
      change P ((fun ω => centerRationalPath (fun q => origR q ω)) ⁻¹' targetSet) =
        Q ((fun ω => centerRationalPath (fun q => modelR q ω)) ⁻¹' targetSet)
      exact hcenterLaw.measure_mem_eq
        (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
          (c - 1) (c + 1) (y - ε) (y + ε))
    have hgood : 0 < Q (modelEvent ∩ {ω | Y ⊥ ω = 0}) := by
      have hae : modelEvent =ᵐ[Q] modelEvent ∩ {ω | Y ⊥ ω = 0} := by
        filter_upwards [hstart] with ω hω
        simp [hω]
      rw [measure_congr hae.symm]
      exact hmodelEvent
    have hmodelSubset :
        modelEvent ∩ {ω | Y ⊥ ω = 0} ⊆ modelRationalEvent := by
      intro ω hω
      rcases hω with ⟨⟨hpath, hlow, hupp⟩, hzero⟩
      change Y ⊥ ω = 0 at hzero
      have hcenter (q : RationalGrid.RationalUnitInterval) :
          centerRationalPath (fun r => modelR r ω) q = Y (RationalGrid.unitCoe q) ω := by
        simp [centerRationalPath, modelR, rationalUnitCoe_bot, hzero]
      change centerRationalPath (fun q => modelR q ω) ∈ targetSet
      change
        centerRationalPath (fun q => modelR q ω) ∈
            Skorokhod.rationalCoordinateCorridorWithMargin (c - 1) (c + 1) ∧
          centerRationalPath (fun q => modelR q ω) ⊤ ∈ Set.Ioo (y - ε) (y + ε)
      rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real]
      constructor
      · refine ⟨margin - 2 * ρ, hγ, ?_⟩
        intro q
        rw [hcenter q]
        exact hpath (RationalGrid.unitCoe q)
      · have htop := hcenter ⊤
        rw [htop, rationalUnitCoe_top]
        exact ⟨hlow, hupp⟩
    have hmodelRationalPos : 0 < Q modelRationalEvent :=
      hgood.trans_le (measure_mono hmodelSubset)
    have htargetRationalPos : 0 < P targetRationalEvent := by
      rw [hprobEq]
      exact hmodelRationalPos
    have htargetEq : targetRationalEvent =ᵐ[P]
        fullSegmentCorridorReturnEvent X 0 1
          (c - 1) (c + 1) (y - ε) (y + ε) := by
      filter_upwards [h.ae_cadlag] with ω hcadlag
      have hpath :
          (fun q : RationalGrid.RationalUnitInterval =>
            X (0 + 1 * rationalUnitTime q) ω - X 0 ω) =
          centerRationalPath (fun q => origR q ω) := by
        funext q
        simp [centerRationalPath, origR, rationalUnitTime_bot]
      apply propext
      change centerRationalPath (fun q => origR q ω) ∈
          Skorokhod.rationalCoordinateCorridorReturnWithMargin
            (c - 1) (c + 1) (y - ε) (y + ε) ↔ _
      rw [← hpath]
      exact (mem_fullSegmentCorridorReturnEvent_iff_rational X 0 1
        (c - 1) (c + 1) (y - ε) (y + ε) ω hcadlag).symm
    have htargetMeasure := measure_congr htargetEq
    rw [htargetMeasure] at htargetRationalPos
    exact htargetRationalPos

/-- The positive open endpoint interval implies the source theorem's
left-open, right-closed endpoint convention. -/
theorem IsStableLevyProcess.measure_sourceEntrance_pos_of_cdfAtZero_of_poissonModel
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorEvent X 0 1 (c - 1) (c + 1) ∩
      {ω | c - b - ε < segmentIncrement X 0 1 ω ⊤ ∧
        segmentIncrement X 0 1 ω ⊤ ≤ c - b + ε}) := by
  have hp := h.measure_fullEntrance_pos_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε
  apply hp.trans_le
  apply measure_mono
  rintro ω ⟨hcorridor, hend⟩
  exact ⟨hcorridor, hend.1, hend.2.le⟩

end ProbabilityTheory

end
