/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.RelativeApproximation
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.ContinuousBoundary
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Energy of continuous-boundary corridors

The reciprocal-width energy of a strictly separated continuous corridor is
finite and agrees with the ordinary real Lebesgue integral of its density.
The interval is the source unit interval, on which the path-space and corridor
energy APIs are currently defined.
-/

open MeasureTheory
open Filter

open scoped ENNReal

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- The reciprocal-power density associated to a pair of continuous
boundaries. -/
noncomputable def continuousBoundaryDensity (α : ℝ)
    (lower upper : C(unitInterval, ℝ)) (t : unitInterval) : ℝ :=
  (upper t - lower t) ^ (-α)

/-- The extended-real energy of a continuous-boundary corridor. -/
noncomputable def continuousBoundaryEnergy (α : ℝ)
    (lower upper : C(unitInterval, ℝ)) : ℝ≥0∞ :=
  ∫⁻ t : unitInterval,
    ENNReal.ofReal (continuousBoundaryDensity α lower upper t) ∂volume

/-- The corresponding ordinary real Lebesgue integral. -/
noncomputable def continuousBoundaryRealEnergy (α : ℝ)
    (lower upper : C(unitInterval, ℝ)) : ℝ :=
  ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume

private theorem exists_rpow_uniform_width_modulus (α m M η : ℝ)
    (hm : 0 < m) (hη : 0 < η) :
    ∃ δ > 0, ∀ x y : ℝ, m ≤ x → x ≤ M → m / 2 ≤ y → y ≤ M + m →
      |x - y| < δ → |x ^ (-α) - y ^ (-α)| < η := by
  let S : Set ℝ := Set.Icc (m / 2) (M + m)
  have hpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    exact lt_of_lt_of_le (by linarith) hx.1
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-α)) S := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-α)
      (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  have huc : UniformContinuousOn (fun x : ℝ => x ^ (-α)) S :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hxM hxU hyL hyU hxy
  have hxS : x ∈ S := ⟨by linarith, by linarith⟩
  have hyS : y ∈ S := ⟨hyL, hyU⟩
  have h := hmod x hxS y hyS (by simpa [Real.dist_eq] using hxy)
  simpa [Real.dist_eq] using h

theorem continuous_continuousBoundaryDensity (α : ℝ)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    Continuous (continuousBoundaryDensity α lower upper) := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold continuousBoundaryDensity
  have hbase : ContinuousAt (fun s : unitInterval => upper s - lower s) t :=
    (upper.continuous.sub lower.continuous).continuousAt
  convert
    (Real.continuousAt_rpow_const (upper t - lower t) (-α)
      (Or.inl (ne_of_gt (hwidth t)))).comp
      (f := fun s : unitInterval => upper s - lower s) hbase using 1
  ext s
  rfl

theorem continuousBoundaryDensity_nonneg (α : ℝ)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) (t : unitInterval) :
    0 ≤ continuousBoundaryDensity α lower upper t := by
  unfold continuousBoundaryDensity
  exact le_of_lt (Real.rpow_pos_of_pos (hwidth t) _)

theorem integrable_continuousBoundaryDensity (α : ℝ)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    Integrable (continuousBoundaryDensity α lower upper) volume := by
  have hcont := continuous_continuousBoundaryDensity α lower upper hwidth
  have hI : IntegrableOn (continuousBoundaryDensity α lower upper)
      (Set.univ : Set unitInterval) volume := by
    exact hcont.continuousOn.integrableOn_compact isCompact_univ
  simpa [IntegrableOn, Measure.restrict_univ] using hI

/-- The continuous-boundary energy is exactly the `ofReal` of the usual
Lebesgue integral. This puts the path-class energy in the same normalization
as the integral functional in the source theorem. -/
theorem continuousBoundaryEnergy_eq_ofReal_realEnergy (α : ℝ)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    continuousBoundaryEnergy α lower upper =
      ENNReal.ofReal (continuousBoundaryRealEnergy α lower upper) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_continuousBoundaryDensity α lower upper hwidth)
    (Filter.Eventually.of_forall
      (continuousBoundaryDensity_nonneg α lower upper hwidth))

theorem continuousBoundaryEnergy_lt_top (α : ℝ)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    continuousBoundaryEnergy α lower upper < ⊤ := by
  rw [continuousBoundaryEnergy_eq_ofReal_realEnergy α lower upper hwidth]
  exact ENNReal.ofReal_lt_top

/-- The real-valued density of a finite-step corridor. -/
noncomputable def stepCorridorRealDensity (α : ℝ)
    (c : ContinuousAdmissibleStepCorridor) (t : unitInterval) : ℝ :=
  (widthCost α (c.upper.eval t) (c.lower.eval t)).toReal

private theorem stepCorridorRealDensity_eq_rpow_of_values
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor) (t : unitInterval)
    (u l : ℝ) (hu : c.upper.eval t = (u : EReal))
    (hl : c.lower.eval t = (l : EReal)) (hwidth : 0 < u - l) :
    stepCorridorRealDensity α c t = (u - l) ^ (-α) := by
  simp [stepCorridorRealDensity, hu, hl,
    widthCost_coe_sub α u l hwidth,
    le_of_lt (Real.rpow_pos_of_pos hwidth _)]

private theorem abs_sample_add_offset_sub_le {s t offset ε : ℝ}
    (hsample : |t - s| < ε) :
    |s + offset - t| ≤ |offset| + ε := by
  have htri := abs_sub_le (s + offset) s t
  have hoff : (s + offset) - s = offset := by ring
  rw [hoff] at htri
  have hsample' : |s - t| ≤ ε := by
    have := le_of_lt hsample
    simpa [abs_sub_comm] using this
  exact htri.trans (add_le_add_right hsample' _)

private theorem abs_step_width_error_le {uS lS u l ε : ℝ}
    (hu : |uS - u| ≤ 3 * ε) (hl : |lS - l| ≤ 3 * ε) :
    |(uS - lS) - (u - l)| ≤ 6 * ε := by
  have htri := abs_sub_le (uS - u) 0 (lS - l)
  have htri' : |(uS - u) - (lS - l)| ≤ |uS - u| + |lS - l| := by
    have hcomm : |l - lS| = |lS - l| := by rw [abs_sub_comm]
    calc
      |(uS - u) - (lS - l)| ≤ |uS - u| + |l - lS| := by simpa using htri
      _ = |uS - u| + |lS - l| := by rw [hcomm]
  have heq : (uS - lS) - (u - l) = (uS - u) - (lS - l) := by ring
  calc
    |(uS - lS) - (u - l)| = |(uS - u) - (lS - l)| := by rw [heq]
    _ ≤ |uS - u| + |lS - l| := htri'
    _ ≤ 3 * ε + 3 * ε := add_le_add hu hl
    _ = 6 * ε := by ring

private theorem exists_continuous_width_bounds
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ t, m ≤ upper t - lower t ∧ upper t - lower t ≤ M := by
  let width : unitInterval → ℝ := fun t => upper t - lower t
  have hcont : Continuous width := upper.continuous.sub lower.continuous
  obtain ⟨tmin, -, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set unitInterval).Nonempty from ⟨⊥, Set.mem_univ _⟩)
    hcont.continuousOn
  obtain ⟨tmax, -, hmax⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set unitInterval).Nonempty from ⟨⊥, Set.mem_univ _⟩)
    hcont.continuousOn
  refine ⟨width tmin, width tmax, hwidth tmin, ?_, ?_⟩
  · exact hmin (Set.mem_univ tmax)
  · intro t
    exact ⟨hmin (Set.mem_univ t), hmax (Set.mem_univ t)⟩

private theorem exists_continuous_density_lower_bound
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) :
    ∃ d : ℝ, 0 < d ∧ ∀ t, d ≤ continuousBoundaryDensity α lower upper t := by
  have hcont := continuous_continuousBoundaryDensity α lower upper hwidth
  obtain ⟨tmin, -, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set unitInterval).Nonempty from ⟨⊥, Set.mem_univ _⟩)
    hcont.continuousOn
  have hdpos : 0 < continuousBoundaryDensity α lower upper tmin := by
    exact Real.rpow_pos_of_pos (hwidth tmin) _
  refine ⟨continuousBoundaryDensity α lower upper tmin, hdpos, ?_⟩
  · intro t
    exact hmin (Set.mem_univ t)

private theorem stepCorridor_density_close_of_width_error
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor)
    (lower upper : C(unitInterval, ℝ)) (t : unitInterval)
    (u l m M ε δ η : ℝ)
    (hu : c.upper.eval t = (u : EReal))
    (hl : c.lower.eval t = (l : EReal))
    (hm : 0 < m)
    (hbound : m ≤ upper t - lower t ∧ upper t - lower t ≤ M)
    (herror : |(u - l) - (upper t - lower t)| ≤ 6 * ε)
    (hε : ε ≤ m / 24) (hδ : 6 * ε < δ)
    (hmod : ∀ x y : ℝ, m ≤ x → x ≤ M → m / 2 ≤ y → y ≤ M + m →
      |x - y| < δ → |x ^ (-α) - y ^ (-α)| < η) :
    |stepCorridorRealDensity α c t - continuousBoundaryDensity α lower upper t| < η := by
  have hwidthLower : m / 2 ≤ u - l := by
    have hle := (abs_le.mp herror).1
    nlinarith [hbound.1, hε, hm]
  have hwidthUpper : u - l ≤ M + m := by
    have hle := (abs_le.mp herror).2
    nlinarith [hbound.2, hε, hm]
  have hwidthStep : 0 < u - l := lt_of_lt_of_le (by linarith [hm]) hwidthLower
  have herror' : |(upper t - lower t) - (u - l)| ≤ 6 * ε := by
    simpa [abs_sub_comm] using herror
  have hpow := hmod (upper t - lower t) (u - l) hbound.1 hbound.2
    hwidthLower hwidthUpper (lt_of_le_of_lt herror' hδ)
  rw [stepCorridorRealDensity_eq_rpow_of_values α c t u l hu hl hwidthStep]
  simpa [continuousBoundaryDensity, abs_sub_comm] using hpow

theorem ContinuousAdmissibleStepCorridor.measurable_widthCost (α : ℝ)
    (c : ContinuousAdmissibleStepCorridor) :
    Measurable (fun t : unitInterval =>
      widthCost α (c.upper.eval t) (c.lower.eval t)) := by
  let cost : Fin (c.upper.knots.card + 1) × Fin (c.lower.knots.card + 1) → ℝ≥0∞ :=
    fun p => widthCost α (c.upper.levels p.1) (c.lower.levels p.2)
  have hcost : Measurable cost := measurable_of_finite cost
  change Measurable (cost ∘ c.levelPairIndex)
  exact hcost.comp c.levelPairIndex_measurable

theorem ContinuousAdmissibleStepCorridor.energy_toReal_eq_integral_stepCorridorRealDensity
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor) :
    (c.energy α).toReal = ∫ t : unitInterval, stepCorridorRealDensity α c t ∂volume := by
  symm
  unfold stepCorridorRealDensity ContinuousAdmissibleStepCorridor.energy
  exact integral_toReal (c.measurable_widthCost α).aemeasurable
    (Filter.Eventually.of_forall fun t => widthCost_lt_top α (c.upper.eval t) (c.lower.eval t))

theorem ContinuousAdmissibleStepCorridor.energy_pos_of_realDensity_pos
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor)
    (hpos : ∀ t, 0 < stepCorridorRealDensity α c t) :
    0 < c.energy α := by
  have hnonneg : ∀ t, 0 ≤ stepCorridorRealDensity α c t :=
    fun t => le_of_lt (hpos t)
  have hint : Integrable (stepCorridorRealDensity α c) volume := by
    apply integrable_toReal_of_lintegral_ne_top (c.measurable_widthCost α).aemeasurable
    exact ne_of_lt (c.energy_lt_top α)
  have hsupport : Function.support (stepCorridorRealDensity α c) = Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (ne_of_gt (hpos t))
  have hreal : 0 < ∫ t : unitInterval, stepCorridorRealDensity α c t ∂volume := by
    apply (integral_pos_iff_support_of_nonneg hnonneg hint).2
    rw [hsupport]
    simp
  rw [← c.energy_toReal_eq_integral_stepCorridorRealDensity α] at hreal
  exact (ENNReal.toReal_pos_iff.mp hreal).1

/-- A uniform pointwise bound on the step-corridor density error bounds the
difference between its real `Hα` energy and the continuous-boundary energy.
This separates the geometric approximation estimate from integration. -/
theorem ContinuousAdmissibleStepCorridor.abs_energy_toReal_sub_continuousBoundaryRealEnergy_le
    (α : ℝ) (c : ContinuousAdmissibleStepCorridor)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) (ε : ℝ)
    (hbound : ∀ t, |stepCorridorRealDensity α c t -
      continuousBoundaryDensity α lower upper t| ≤ ε) :
    |(c.energy α).toReal - continuousBoundaryRealEnergy α lower upper| ≤ ε := by
  let stepDensity := stepCorridorRealDensity α c
  let targetDensity := continuousBoundaryDensity α lower upper
  have hstepIntegrable : Integrable stepDensity volume := by
    apply integrable_toReal_of_lintegral_ne_top (c.measurable_widthCost α).aemeasurable
    exact ne_of_lt (c.energy_lt_top α)
  have htargetIntegrable : Integrable targetDensity volume :=
    integrable_continuousBoundaryDensity α lower upper hwidth
  have hdiffIntegrable : Integrable (fun t => stepDensity t - targetDensity t) volume :=
    hstepIntegrable.sub htargetIntegrable
  have hnorm : ∀ᵐ t : unitInterval ∂volume,
      ‖stepDensity t - targetDensity t‖ ≤ ε := by
    filter_upwards with t
    rw [Real.norm_eq_abs]
    exact hbound t
  calc
    |(c.energy α).toReal - continuousBoundaryRealEnergy α lower upper| =
        |∫ t : unitInterval, stepDensity t - targetDensity t ∂volume| := by
      rw [c.energy_toReal_eq_integral_stepCorridorRealDensity, continuousBoundaryRealEnergy]
      rw [integral_sub hstepIntegrable htargetIntegrable]
    _ ≤ ∫ t : unitInterval, |stepDensity t - targetDensity t| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t : unitInterval, ε ∂volume := by
      apply integral_mono_ae hdiffIntegrable.abs (integrable_const ε)
      filter_upwards [hnorm] with t ht
      simpa [Real.norm_eq_abs] using ht
    _ = ε := by simp

/-- If the inner and outer step-corridor densities are both uniformly close
to the same continuous-boundary density, their real energies have a vanishing
gap as soon as the common error tends to zero. -/
theorem abs_stepCorridor_energy_gap_le_of_density_errors
    (α : ℝ) (inner outer : ContinuousAdmissibleStepCorridor)
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, 0 < upper t - lower t) (ε : ℝ)
    (hinner : ∀ t, |stepCorridorRealDensity α inner t -
      continuousBoundaryDensity α lower upper t| ≤ ε)
    (houter : ∀ t, |stepCorridorRealDensity α outer t -
      continuousBoundaryDensity α lower upper t| ≤ ε) :
    |(inner.energy α).toReal - (outer.energy α).toReal| ≤ 2 * ε := by
  have hi := inner.abs_energy_toReal_sub_continuousBoundaryRealEnergy_le
    α lower upper hwidth ε hinner
  have ho := outer.abs_energy_toReal_sub_continuousBoundaryRealEnergy_le
    α lower upper hwidth ε houter
  have htri := abs_sub_le ((inner.energy α).toReal)
    (continuousBoundaryRealEnergy α lower upper) ((outer.energy α).toReal)
  apply le_trans htri
  calc
    |(inner.energy α).toReal - continuousBoundaryRealEnergy α lower upper| +
        |continuousBoundaryRealEnergy α lower upper - (outer.energy α).toReal|
      ≤ ε + ε := add_le_add hi (by simpa [abs_sub_comm] using ho)
    _ = 2 * ε := by ring

/-- For every requested density tolerance, sufficiently fine sampled inner
and outer step corridors have densities uniformly close to the continuous
boundary density. The shared offset tends to zero with the tolerance, while
the mesh is chosen fine enough to control both sampled boundary errors. This
is the quantitative input for a vanishing-energy-gap approximation. -/
theorem exists_fine_uniformGrid_relativeCorridor_density_approximation
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (blocks : ℕ) (hblocks : 0 < blocks),
        1 / (blocks : ℝ) < δ →
        ∃ inner outer : ContinuousAdmissibleStepCorridor,
          inner.upper = uniformGridStepBoundary blocks hblocks upper (-2 * ε) ∧
          inner.lower = uniformGridStepBoundary blocks hblocks lower (2 * ε) ∧
          outer.upper = uniformGridStepBoundary blocks hblocks upper (2 * ε) ∧
          outer.lower = uniformGridStepBoundary blocks hblocks lower (-2 * ε) ∧
          Skorokhod.terminalLeftPathSpace ∩ inner.toSet ⊆
            relativeContinuousBoundaryCorridorSet lower upper ∧
          relativeContinuousBoundaryCorridorSet lower upper ⊆
            Skorokhod.terminalLeftPathSpace ∩ outer.toSet ∧
          (∀ t, |stepCorridorRealDensity α inner t -
            continuousBoundaryDensity α lower upper t| < η) ∧
          (∀ t, |stepCorridorRealDensity α outer t -
            continuousBoundaryDensity α lower upper t| < η) ∧
          0 < inner.energy α ∧ 0 < outer.energy α ∧
          |(inner.energy α).toReal - (outer.energy α).toReal| ≤ 2 * η := by
  have hwidthReal : ∀ t, 0 < upper t - lower t := fun t => sub_pos.mpr (hwidth t)
  obtain ⟨center, margin, hmargin, hcenterZero, hcenter, hsand⟩ :=
    exists_fine_uniformGrid_relativeCorridor_sandwich lower upper hwidth
      hstartLower hstartUpper
  obtain ⟨m, M, hm, hMm, hbounds⟩ :=
    exists_continuous_width_bounds lower upper hwidthReal
  obtain ⟨d, hd, hdensity⟩ :=
    exists_continuous_density_lower_bound α lower upper hwidthReal
  let η₀ : ℝ := min η (d / 2)
  have hη₀ : 0 < η₀ := by
    dsimp [η₀]
    exact lt_min hη (half_pos hd)
  have hη₀le : η₀ ≤ d / 2 := min_le_right _ _
  obtain ⟨δpow, hδpow, hmod⟩ :=
    exists_rpow_uniform_width_modulus α m M η₀ hm hη₀
  let ε : ℝ := min (margin / 4) (min (m / 24) (δpow / 12))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεMargin : ε ≤ margin / 4 := by
    dsimp [ε]
    exact min_le_left _ _
  have hεWidth : ε ≤ m / 24 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεPow : ε ≤ δpow / 12 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall : 3 * ε < margin := by nlinarith [hmargin, hεMargin]
  have h6epsPow : 6 * ε < δpow := by nlinarith [hδpow, hεPow]
  obtain ⟨δSand, hδSand, hSand⟩ := hsand ε hε hsmall
  obtain ⟨δLower, hδLower, hsampleLower⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error lower ε hε
  obtain ⟨δUpper, hδUpper, hsampleUpper⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error upper ε hε
  let δ : ℝ := min δSand (min δLower δUpper)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδSand (lt_min hδLower hδUpper)
  refine ⟨ε, δ, hε, hδ, ?_⟩
  intro blocks hblocks hmesh
  have hmeshSand : 1 / (blocks : ℝ) < δSand :=
    hmesh.trans_le (min_le_left _ _)
  have hleLower : δ ≤ δLower :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hmeshLower : 1 / (blocks : ℝ) < δLower := hmesh.trans_le hleLower
  have hmeshUpper : 1 / (blocks : ℝ) < δUpper := by
    have hle : δ ≤ δUpper := le_trans (min_le_right _ _) (min_le_right _ _)
    exact hmesh.trans_le hle
  let innerLower := uniformGridStepBoundary blocks hblocks lower (2 * ε)
  let innerUpper := uniformGridStepBoundary blocks hblocks upper (-2 * ε)
  let outerLower := uniformGridStepBoundary blocks hblocks lower (-2 * ε)
  let outerUpper := uniformGridStepBoundary blocks hblocks upper (2 * ε)
  rcases hSand blocks hblocks hmeshSand with
    ⟨hinward, houtward, hadmissible, hadmissibleOuter, hinnerSubset, houterSubset⟩
  let inner : ContinuousAdmissibleStepCorridor :=
    ⟨⟨innerUpper, innerLower⟩, hadmissible⟩
  let outer : ContinuousAdmissibleStepCorridor :=
    ⟨⟨outerUpper, outerLower⟩, hadmissibleOuter⟩
  have hsampleIL : ∀ t : unitInterval,
      |lower t - lower (uniformGridTime blocks hblocks
        (Fin.cast (by simpa [innerLower, uniformGridStepBoundary] using
          uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)))| < ε := by
    intro t
    simpa [innerLower] using hsampleLower blocks hblocks hmeshLower (2 * ε) t
  have hsampleIU : ∀ t : unitInterval,
      |upper t - upper (uniformGridTime blocks hblocks
        (Fin.cast (by simpa [innerUpper, uniformGridStepBoundary] using
          uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)))| < ε := by
    intro t
    simpa [innerUpper] using hsampleUpper blocks hblocks hmeshUpper (-2 * ε) t
  have hsampleOL : ∀ t : unitInterval,
      |lower t - lower (uniformGridTime blocks hblocks
        (Fin.cast (by simpa [outerLower, uniformGridStepBoundary] using
          uniformCorridorKnots_card blocks hblocks) (outerLower.levelIndex t)))| < ε := by
    intro t
    simpa [outerLower] using hsampleLower blocks hblocks hmeshLower (-2 * ε) t
  have hsampleOU : ∀ t : unitInterval,
      |upper t - upper (uniformGridTime blocks hblocks
        (Fin.cast (by simpa [outerUpper, uniformGridStepBoundary] using
          uniformCorridorKnots_card blocks hblocks) (outerUpper.levelIndex t)))| < ε := by
    intro t
    simpa [outerUpper] using hsampleUpper blocks hblocks hmeshUpper (2 * ε) t
  have h2epsAbsPos : |(2 : ℝ) * ε| = 2 * ε := by
    rw [abs_of_nonneg (by positivity)]
  have h2epsAbsNeg : |(-2 : ℝ) * ε| = 2 * ε := by
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hε.le)]
    ring
  have hinnerDensity₀ : ∀ t, |stepCorridorRealDensity α inner t -
      continuousBoundaryDensity α lower upper t| < η₀ := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [innerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [innerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)
    let lS := lower (uniformGridTime blocks hblocks iL) + 2 * ε
    let uS := upper (uniformGridTime blocks hblocks iU) - 2 * ε
    have hlEval : inner.lower.eval t = (lS : EReal) := by
      simpa [inner, innerLower, iL, lS, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (2 * ε) t
    have huEval : inner.upper.eval t = (uS : EReal) := by
      simpa [inner, innerUpper, iU, uS, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (-2 * ε) t
    have hlErr : |lS - lower t| ≤ 3 * ε := by
      have hs := hsampleIL t
      change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hs
      have hbase := abs_sample_add_offset_sub_le
        (s := lower (uniformGridTime blocks hblocks iL)) (t := lower t)
        (offset := 2 * ε) (ε := ε) hs
      have heq : lS = lower (uniformGridTime blocks hblocks iL) + 2 * ε := by
        dsimp [lS]
      rw [heq]
      calc
        _ ≤ |2 * ε| + ε := hbase
        _ = 3 * ε := by rw [h2epsAbsPos]; ring
    have huErr : |uS - upper t| ≤ 3 * ε := by
      have hs := hsampleIU t
      change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hs
      have hbase := abs_sample_add_offset_sub_le
        (s := upper (uniformGridTime blocks hblocks iU)) (t := upper t)
        (offset := -2 * ε) (ε := ε) hs
      have heq : uS = upper (uniformGridTime blocks hblocks iU) + (-2 * ε) := by
        dsimp [uS]
        ring
      rw [heq]
      calc
        _ ≤ |-2 * ε| + ε := hbase
        _ = 3 * ε := by rw [h2epsAbsNeg]; ring
    have hwidthErr := abs_step_width_error_le huErr hlErr
    exact stepCorridor_density_close_of_width_error α inner lower upper t uS lS m M ε δpow η₀
      huEval hlEval hm (hbounds t) hwidthErr hεWidth h6epsPow hmod
  have houterDensity₀ : ∀ t, |stepCorridorRealDensity α outer t -
      continuousBoundaryDensity α lower upper t| < η₀ := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [outerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [outerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerUpper.levelIndex t)
    let lS := lower (uniformGridTime blocks hblocks iL) - 2 * ε
    let uS := upper (uniformGridTime blocks hblocks iU) + 2 * ε
    have hlEval : outer.lower.eval t = (lS : EReal) := by
      simpa [outer, outerLower, iL, lS, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (-2 * ε) t
    have huEval : outer.upper.eval t = (uS : EReal) := by
      simpa [outer, outerUpper, iU, uS, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (2 * ε) t
    have hlErr : |lS - lower t| ≤ 3 * ε := by
      have hs := hsampleOL t
      change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hs
      have hbase := abs_sample_add_offset_sub_le
        (s := lower (uniformGridTime blocks hblocks iL)) (t := lower t)
        (offset := -2 * ε) (ε := ε) hs
      have heq : lS = lower (uniformGridTime blocks hblocks iL) + (-2 * ε) := by
        dsimp [lS]
        ring
      rw [heq]
      calc
        _ ≤ |-2 * ε| + ε := hbase
        _ = 3 * ε := by rw [h2epsAbsNeg]; ring
    have huErr : |uS - upper t| ≤ 3 * ε := by
      have hs := hsampleOU t
      change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hs
      have hbase := abs_sample_add_offset_sub_le
        (s := upper (uniformGridTime blocks hblocks iU)) (t := upper t)
        (offset := 2 * ε) (ε := ε) hs
      have heq : uS = upper (uniformGridTime blocks hblocks iU) + 2 * ε := by
        dsimp [uS]
      rw [heq]
      calc
        _ ≤ |2 * ε| + ε := hbase
        _ = 3 * ε := by rw [h2epsAbsPos]; ring
    have hwidthErr := abs_step_width_error_le huErr hlErr
    exact stepCorridor_density_close_of_width_error α outer lower upper t uS lS m M ε δpow η₀
      huEval hlEval hm (hbounds t) hwidthErr hεWidth h6epsPow hmod
  have hinnerDensity : ∀ t, |stepCorridorRealDensity α inner t -
      continuousBoundaryDensity α lower upper t| < η := by
    intro t
    exact lt_of_lt_of_le (hinnerDensity₀ t) (min_le_left _ _)
  have houterDensity : ∀ t, |stepCorridorRealDensity α outer t -
      continuousBoundaryDensity α lower upper t| < η := by
    intro t
    exact lt_of_lt_of_le (houterDensity₀ t) (min_le_left _ _)
  have hinnerPos : 0 < inner.energy α := by
    apply inner.energy_pos_of_realDensity_pos α
    intro t
    have htarget := hdensity t
    have hbelow := (abs_lt.mp (hinnerDensity₀ t)).1
    nlinarith [hη₀, hη₀le, hd]
  have houterPos : 0 < outer.energy α := by
    apply outer.energy_pos_of_realDensity_pos α
    intro t
    have htarget := hdensity t
    have hbelow := (abs_lt.mp (houterDensity₀ t)).1
    nlinarith [hη₀, hη₀le, hd]
  have hgap := abs_stepCorridor_energy_gap_le_of_density_errors α inner outer lower upper
    hwidthReal η (fun t => le_of_lt (hinnerDensity t))
    (fun t => le_of_lt (houterDensity t))
  refine ⟨inner, outer, rfl, rfl, rfl, rfl, ?_, ?_, hinnerDensity, houterDensity,
    hinnerPos, houterPos, hgap⟩
  · change Skorokhod.terminalLeftPathSpace ∩ corridorSet innerUpper innerLower ⊆
      relativeContinuousBoundaryCorridorSet lower upper
    exact hinnerSubset
  · change relativeContinuousBoundaryCorridorSet lower upper ⊆
      Skorokhod.terminalLeftPathSpace ∩ corridorSet outerUpper outerLower
    exact houterSubset

private noncomputable def singletonFiniteCorridorUnion (α : ℝ)
    (c : ContinuousAdmissibleStepCorridor) (hpos : 0 < c.energy α) :
    FiniteCorridorUnion α := by
  have henergy : finiteMinimumEnergy α 1 (by norm_num) (fun _ : Fin 1 => c) =
      c.energy α := by
    simp [finiteMinimumEnergy]
  refine ⟨1, by norm_num, fun _ => c, ?_⟩
  rw [henergy]
  exact hpos

private theorem singletonFiniteCorridorUnion_toSet (α : ℝ)
    (c : ContinuousAdmissibleStepCorridor) (hpos : 0 < c.energy α) :
    FiniteCorridorUnion.toSet (singletonFiniteCorridorUnion α c hpos) = c.toSet := by
  ext path
  simp [singletonFiniteCorridorUnion, FiniteCorridorUnion.toSet]

private theorem singletonFiniteCorridorUnion_realEnergy (α : ℝ)
    (c : ContinuousAdmissibleStepCorridor) (hpos : 0 < c.energy α) :
    (singletonFiniteCorridorUnion α c hpos).realEnergy = (c.energy α).toReal := by
  change (finiteMinimumEnergy α 1 (by norm_num) (fun _ : Fin 1 => c)).toReal = _
  have henergy : finiteMinimumEnergy α 1 (by norm_num) (fun _ : Fin 1 => c) =
      c.energy α := by
    simp [finiteMinimumEnergy]
  rw [henergy]

/-- Every strictly separated continuous corridor with the source's pinned
start condition admits a relative `M₃` approximation whose inner and outer
energies both converge to the continuous-boundary integral. Each approximant
is a single uniform-grid step corridor; the diagonal chooses the mesh after
choosing a density tolerance tending to zero. -/
theorem exists_continuousBoundary_relativeApproximation_energy_tendsto
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ A : RelativeFiniteCorridorUnionApproximation α
        Skorokhod.terminalLeftPathSpace
        (relativeContinuousBoundaryCorridorSet lower upper),
      Tendsto (fun n => (A.inner n).realEnergy) atTop
        (nhds (continuousBoundaryRealEnergy α lower upper)) ∧
      Tendsto (fun n => (A.outer n).realEnergy) atTop
        (nhds (continuousBoundaryRealEnergy α lower upper)) := by
  classical
  let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hη : ∀ n, 0 < η n := by
    intro n
    dsimp [η]
    positivity
  have hquant : ∀ n, ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (blocks : ℕ) (hblocks : 0 < blocks),
        1 / (blocks : ℝ) < δ →
        ∃ inner outer : ContinuousAdmissibleStepCorridor,
          inner.upper = uniformGridStepBoundary blocks hblocks upper (-2 * ε) ∧
          inner.lower = uniformGridStepBoundary blocks hblocks lower (2 * ε) ∧
          outer.upper = uniformGridStepBoundary blocks hblocks upper (2 * ε) ∧
          outer.lower = uniformGridStepBoundary blocks hblocks lower (-2 * ε) ∧
          Skorokhod.terminalLeftPathSpace ∩ inner.toSet ⊆
            relativeContinuousBoundaryCorridorSet lower upper ∧
          relativeContinuousBoundaryCorridorSet lower upper ⊆
            Skorokhod.terminalLeftPathSpace ∩ outer.toSet ∧
          (∀ t, |stepCorridorRealDensity α inner t -
            continuousBoundaryDensity α lower upper t| < η n) ∧
          (∀ t, |stepCorridorRealDensity α outer t -
            continuousBoundaryDensity α lower upper t| < η n) ∧
          0 < inner.energy α ∧ 0 < outer.energy α ∧
          |(inner.energy α).toReal - (outer.energy α).toReal| ≤ 2 * η n := by
    intro n
    exact exists_fine_uniformGrid_relativeCorridor_density_approximation α lower upper
      hwidth hstartLower hstartUpper (η n) (hη n)
  choose ε δ hε hδ hgrid using hquant
  let blocks : ℕ → ℕ := fun n => Classical.choose (exists_nat_one_div_lt (hδ n)) + 1
  have hblocks : ∀ n, 0 < blocks n := by
    intro n
    dsimp [blocks]
    omega
  have hmesh : ∀ n, 1 / (blocks n : ℝ) < δ n := by
    intro n
    have hn := Classical.choose_spec (exists_nat_one_div_lt (hδ n))
    dsimp [blocks]
    simpa [Nat.cast_add, Nat.cast_one] using hn
  have hselected : ∀ n, ∃ inner outer : ContinuousAdmissibleStepCorridor,
      0 < inner.energy α ∧ 0 < outer.energy α ∧
      (∀ t, |stepCorridorRealDensity α inner t -
        continuousBoundaryDensity α lower upper t| < η n) ∧
      (∀ t, |stepCorridorRealDensity α outer t -
        continuousBoundaryDensity α lower upper t| < η n) ∧
      Skorokhod.terminalLeftPathSpace ∩ inner.toSet ⊆
        relativeContinuousBoundaryCorridorSet lower upper ∧
      relativeContinuousBoundaryCorridorSet lower upper ⊆
        Skorokhod.terminalLeftPathSpace ∩ outer.toSet := by
    intro n
    obtain ⟨inner, outer, _, _, _, _, hinnerSubset, houterSubset,
      hinnerDensity, houterDensity, hinnerPos, houterPos, _⟩ :=
        hgrid n (blocks n) (hblocks n) (hmesh n)
    exact ⟨inner, outer, hinnerPos, houterPos,
      hinnerDensity, houterDensity, hinnerSubset, houterSubset⟩
  choose inner outer hinnerPos houterPos hinnerDensity houterDensity
    hinnerSubset houterSubset using hselected
  let innerUnion : ℕ → FiniteCorridorUnion α := fun n =>
    singletonFiniteCorridorUnion α (inner n) (hinnerPos n)
  let outerUnion : ℕ → FiniteCorridorUnion α := fun n =>
    singletonFiniteCorridorUnion α (outer n) (houterPos n)
  have hwidthReal : ∀ t, 0 < upper t - lower t :=
    fun t => sub_pos.mpr (hwidth t)
  have hinnerEnergyError : ∀ n,
      |(innerUnion n).realEnergy - continuousBoundaryRealEnergy α lower upper| ≤ η n := by
    intro n
    have h := (inner n).abs_energy_toReal_sub_continuousBoundaryRealEnergy_le
      α lower upper hwidthReal (η n) (fun t => le_of_lt (hinnerDensity n t))
    simpa [innerUnion, singletonFiniteCorridorUnion_realEnergy] using h
  have houterEnergyError : ∀ n,
      |(outerUnion n).realEnergy - continuousBoundaryRealEnergy α lower upper| ≤ η n := by
    intro n
    have h := (outer n).abs_energy_toReal_sub_continuousBoundaryRealEnergy_le
      α lower upper hwidthReal (η n) (fun t => le_of_lt (houterDensity n t))
    simpa [outerUnion, singletonFiniteCorridorUnion_realEnergy] using h
  have hηT : Tendsto η atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [η] using hbase
  have hinnerEnergyT : Tendsto (fun n => (innerUnion n).realEnergy) atTop
      (nhds (continuousBoundaryRealEnergy α lower upper)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε' hε'
    have hsmall : ∀ᶠ n : ℕ in atTop, η n < ε' :=
      hηT.eventually (Iio_mem_nhds hε')
    filter_upwards [hsmall] with n hn
    simpa [Real.dist_eq] using lt_of_le_of_lt (hinnerEnergyError n) hn
  have houterEnergyT : Tendsto (fun n => (outerUnion n).realEnergy) atTop
      (nhds (continuousBoundaryRealEnergy α lower upper)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε' hε'
    have hsmall : ∀ᶠ n : ℕ in atTop, η n < ε' :=
      hηT.eventually (Iio_mem_nhds hε')
    filter_upwards [hsmall] with n hn
    simpa [Real.dist_eq] using lt_of_le_of_lt (houterEnergyError n) hn
  have henergyGapT : Tendsto
      (fun n => (innerUnion n).realEnergy - (outerUnion n).realEnergy)
      atTop (nhds 0) := by
    have h := hinnerEnergyT.sub houterEnergyT
    simpa using h
  refine ⟨⟨innerUnion, outerUnion, ?_, ?_, henergyGapT⟩,
    hinnerEnergyT, houterEnergyT⟩
  · intro n
    rw [singletonFiniteCorridorUnion_toSet]
    exact hinnerSubset n
  · intro n
    rw [singletonFiniteCorridorUnion_toSet]
    exact houterSubset n

/-- The continuous-boundary energy convergence theorem supplies the source's
relative vanishing-energy-gap witness. -/
theorem continuousBoundary_hasRelativeVanishingEnergyGapApproximation
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    HasRelativeVanishingEnergyGapApproximation α
      Skorokhod.terminalLeftPathSpace
      (relativeContinuousBoundaryCorridorSet lower upper) := by
  obtain ⟨A, _, _⟩ := exists_continuousBoundary_relativeApproximation_energy_tendsto
    α lower upper hwidth hstartLower hstartUpper
  exact ⟨A⟩

/-- For the continuous-boundary approximation, the common limit carried by
`RelativeFiniteCorridorUnionEnergyLimits` is exactly the boundary energy. -/
theorem exists_continuousBoundary_relativeApproximation_energyLimits
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ A : RelativeFiniteCorridorUnionApproximation α
        Skorokhod.terminalLeftPathSpace
        (relativeContinuousBoundaryCorridorSet lower upper),
      ∃ L : RelativeFiniteCorridorUnionEnergyLimits A,
        L.commonEnergy = continuousBoundaryRealEnergy α lower upper := by
  obtain ⟨A, hinner, houter⟩ :=
    exists_continuousBoundary_relativeApproximation_energy_tendsto
      α lower upper hwidth hstartLower hstartUpper
  let L : RelativeFiniteCorridorUnionEnergyLimits A :=
    ⟨continuousBoundaryRealEnergy α lower upper,
      continuousBoundaryRealEnergy α lower upper, hinner, houter⟩
  exact ⟨A, L, rfl⟩

/-- The common limiting energy in the previous result is the ordinary real
Lebesgue integral of the reciprocal corridor width to the power `-α`. -/
theorem exists_continuousBoundary_relativeApproximation_commonEnergy_eq_integral
    (α : ℝ) (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ A : RelativeFiniteCorridorUnionApproximation α
        Skorokhod.terminalLeftPathSpace
        (relativeContinuousBoundaryCorridorSet lower upper),
      ∃ L : RelativeFiniteCorridorUnionEnergyLimits A,
        L.commonEnergy =
          ∫ t : unitInterval, continuousBoundaryDensity α lower upper t ∂volume := by
  obtain ⟨A, L, hL⟩ := exists_continuousBoundary_relativeApproximation_energyLimits
    α lower upper hwidth hstartLower hstartUpper
  exact ⟨A, L, by simpa [continuousBoundaryRealEnergy] using hL⟩

end Skorokhod.PathClass.StepCorridor

end
