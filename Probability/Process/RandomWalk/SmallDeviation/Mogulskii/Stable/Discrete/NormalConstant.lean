/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PathClassRegimes
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.EndpointWindowSelection
import Probability.Distributions.Rademacher
import Probability.Process.Path.PathClass.StepCorridor.Probability.StableRate
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy

/-!
# The Gaussian escape constant in the normal-domain path-class theorem

The source path-class theorem gives the exponent-two rate in terms of the
Brownian escape constant. This module calibrates that constant against the
sharp horizontal-tube asymptotic, using a constant corridor as a member of
class `M`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open Skorokhod.PathClass.StepCorridor

theorem truncatedSecondMoment_rademacher_eq_one_of_one_le {u : ℝ}
    (hu : 1 ≤ u) :
    truncatedSecondMoment rademacherMeasure u = 1 := by
  rw [truncatedSecondMoment]
  have hset : MeasurableSet (Set.Icc (-u) u) := measurableSet_Icc
  have hmass : rademacherMeasure (Set.Icc (-u) u) = 1 := by
    simpa [rademacherMeasure] using
      (bernoulliMeasure_apply_of_mem_of_mem
        (x := (-1 : ℝ)) (y := (1 : ℝ))
        (p := (⟨1 / 2, by norm_num⟩ : unitInterval))
        (s := Set.Icc (-u) u) hset
        (by constructor <;> linarith)
        (by constructor <;> linarith))
  have hae : ∀ᵐ x ∂rademacherMeasure, x ∈ Set.Icc (-u) u :=
    (mem_ae_iff_prob_eq_one hset).2 hmass
  have hzero : ∀ᵐ x ∂rademacherMeasure,
      x ∉ Set.Icc (-u) u → x ^ 2 = 0 := by
    filter_upwards [hae] with x hx hnot
    exact (hnot hx).elim
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hzero,
    integral_rademacherMeasure]
  norm_num

theorem stableSmallDeviationRate_rademacher_eq_of_scale_ge_one
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 rademacherMeasure normalization scale) :
    stableSmallDeviationRate 2 rademacherMeasure scale =ᶠ[atTop]
      fun n => scale n ^ 2 / (n : ℝ) := by
  filter_upwards [hscale.scale_tendsto_atTop.eventually
    (eventually_ge_atTop (1 : ℝ))] with n hn
  rw [stableSmallDeviationRate_two,
    truncatedSecondMoment_rademacher_eq_one_of_one_le hn]
  simp

/-- The centered unit-width corridor around zero, represented as an `M₂`
corridor. -/
noncomputable def centeredUnitCorridor : ContinuousAdmissibleStepCorridor :=
  ContinuousAdmissibleStepCorridor.constantBounds (lower := -1 / 2) (upper := 1 / 2)
    (by norm_num) (by norm_num)

theorem centeredUnitCorridor_energy :
    ContinuousAdmissibleStepCorridor.energy 2 centeredUnitCorridor = 1 := by
  rw [ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values 2
    centeredUnitCorridor (1 / 2 : ℝ) (-1 / 2 : ℝ)]
  · norm_num [centeredUnitCorridor, ContinuousAdmissibleStepCorridor.constantBounds,
      StepBoundary.eval_constant, widthCost]
  · intro t
    simp [centeredUnitCorridor, ContinuousAdmissibleStepCorridor.constantBounds,
      StepBoundary.eval_constant]
  · intro t
    simp [centeredUnitCorridor, ContinuousAdmissibleStepCorridor.constantBounds,
      StepBoundary.eval_constant]

/-- The one-piece `M₃` set given by the centered unit-width corridor. -/
noncomputable def centeredUnitCorridorFiniteUnion : FiniteCorridorUnion 2 where
  count := 1
  count_pos := by norm_num
  pieces := fun _ => centeredUnitCorridor
  minimum_energy_pos := by
    simp [finiteMinimumEnergy, centeredUnitCorridor_energy]

theorem centeredUnitCorridorFiniteUnion_realEnergy :
    centeredUnitCorridorFiniteUnion.realEnergy = 1 := by
  simp [FiniteCorridorUnion.realEnergy, FiniteCorridorUnion.energy, centeredUnitCorridorFiniteUnion,
    finiteMinimumEnergy, centeredUnitCorridor_energy]

theorem centeredUnitCorridorFiniteUnion_toSet :
    centeredUnitCorridorFiniteUnion.toSet = centeredUnitCorridor.toSet := by
  ext f
  simp [centeredUnitCorridorFiniteUnion, FiniteCorridorUnion.toSet]

/-- Constant inner and outer approximations witness membership of the
centered corridor in the source class `M`. -/
noncomputable def centeredUnitCorridorApproximation :
    FiniteCorridorUnionApproximation 2 centeredUnitCorridorFiniteUnion.toSet := {
    inner := fun _ => centeredUnitCorridorFiniteUnion
    outer := fun _ => centeredUnitCorridorFiniteUnion
    inner_subset := by intro n; exact Set.Subset.rfl
    subset_outer := by intro n; exact Set.Subset.rfl
    energy_gap_tendsto_zero := by simp
  }

theorem hasVanishingEnergyGapApproximation_centeredUnitCorridor :
    HasVanishingEnergyGapApproximation 2 centeredUnitCorridorFiniteUnion.toSet :=
  ⟨centeredUnitCorridorApproximation⟩

noncomputable def centeredUnitCorridorEnergyLimits :
    FiniteCorridorUnionEnergyLimits centeredUnitCorridorApproximation := by
  have hinner : Tendsto
      (fun n : ℕ => FiniteCorridorUnion.realEnergy (centeredUnitCorridorApproximation.inner n))
      atTop (𝓝 1) := by
    simp [centeredUnitCorridorApproximation, centeredUnitCorridorFiniteUnion_realEnergy]
  exact FiniteCorridorUnionEnergyLimits.ofInnerTendsto
    (A := centeredUnitCorridorApproximation) (L := 1) hinner

@[simp] theorem centeredUnitCorridorEnergyLimits_commonEnergy :
    centeredUnitCorridorEnergyLimits.commonEnergy = 1 := by
  simp [centeredUnitCorridorEnergyLimits, FiniteCorridorUnionEnergyLimits.commonEnergy,
    FiniteCorridorUnionEnergyLimits.ofInnerTendsto]

theorem nullMeasurableSet_centeredUnitCorridorFiniteUnion_preimage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → CadlagPath unitInterval ℝ) (hX : AEMeasurable X P) :
    NullMeasurableSet (X ⁻¹' centeredUnitCorridorFiniteUnion.toSet) P := by
  rw [centeredUnitCorridorFiniteUnion_toSet]
  exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
    centeredUnitCorridor P X hX

/-- Membership of a normalized right-continuous step path in the centered
unit-width corridor is exactly the strict horizontal-tube event. -/
theorem normalizedStepCadlagPathIcc_mem_centeredUnitCorridorFiniteUnion_iff_openTube
    {scale : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hs : 0 < scale n)
    (increment : ℕ → ℝ) :
    RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        centeredUnitCorridorFiniteUnion.toSet ↔
      RandomWalk.InOpenHorizontalTube (1 / 2) (scale n) n increment := by
  rw [centeredUnitCorridorFiniteUnion_toSet]
  change RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
    (ContinuousAdmissibleStepCorridor.constantBounds (lower := -1 / 2) (upper := 1 / 2)
      (by norm_num) (by norm_num)).toSet ↔ _
  rw [ContinuousAdmissibleStepCorridor.constantBounds_toSet (by norm_num) (by norm_num)]
  change (RandomWalk.normalizedStepCadlagPathIcc scale n increment ⊥ = 0 ∧
    ∀ t, (-1 / 2 : ℝ) < RandomWalk.normalizedStepCadlagPathIcc
        scale n increment t ∧
      RandomWalk.normalizedStepCadlagPathIcc scale n increment t < 1 / 2) ↔ _
  constructor
  · rintro ⟨_, hpath⟩
    intro k
    let t : unitInterval := ⟨((k.val + 1 : ℕ) : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hn)]
        exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have hk := hpath t
    rw [RandomWalk.normalizedStepCadlagPathIcc_apply,
      RandomWalk.normalizedStepPath_grid scale hn] at hk
    have hmul : scale n * ((scale n)⁻¹ *
        AdditivePath.displacement (k.val + 1) increment) =
        AdditivePath.displacement (k.val + 1) increment := by
      field_simp
    constructor
    · have hscaled := mul_lt_mul_of_pos_left hk.1 hs
      rw [hmul] at hscaled
      nlinarith [hscaled]
    · have hscaled := mul_lt_mul_of_pos_left hk.2 hs
      rw [hmul] at hscaled
      nlinarith [hscaled]
  · intro htube
    have hvertex (j : ℕ) (hj : j ≤ n) :
        (-1 / 2 : ℝ) < (scale n)⁻¹ * AdditivePath.displacement j increment ∧
          (scale n)⁻¹ * AdditivePath.displacement j increment < 1 / 2 := by
      cases j with
      | zero =>
        norm_num [AdditivePath.displacement_zero]
      | succ j =>
        have h := htube ⟨j, by omega⟩
        change -(1 / 2 : ℝ) * scale n <
            AdditivePath.displacement (j + 1) increment ∧
          AdditivePath.displacement (j + 1) increment <
            (1 - 1 / 2 : ℝ) * scale n at h
        constructor
        · have hscaled := mul_lt_mul_of_pos_left h.1 (inv_pos.mpr hs)
          have hcancel : (scale n)⁻¹ * ((-1 / 2 : ℝ) * scale n) = -1 / 2 := by
            field_simp
          nlinarith [hscaled, hcancel]
        · have hscaled := mul_lt_mul_of_pos_left h.2 (inv_pos.mpr hs)
          have hcancel : (scale n)⁻¹ * ((1 - 1 / 2 : ℝ) * scale n) = 1 / 2 := by
            field_simp
            norm_num
          nlinarith [hscaled, hcancel]
    refine ⟨?_, ?_⟩
    · simp [RandomWalk.normalizedStepCadlagPathIcc_apply,
        RandomWalk.normalizedStepPath, AdditivePath.displacement_zero]
    · intro t
      let j := ⌊(n : ℝ) * (t : ℝ)⌋₊
      have hj : j ≤ n := by
        apply Nat.floor_le_of_le
        calc
          (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
          _ = n := by norm_num
      have h := hvertex j hj
      simpa [j, RandomWalk.normalizedStepCadlagPathIcc_apply,
        RandomWalk.normalizedStepPath] using h

/-- The discrete finite-partition theorem specializes on the centered
unit-width corridor to the strict horizontal-tube probability. -/
theorem tendsto_stableRate_openHorizontalTube_eq_escapeRate
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 rademacherMeasure normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation 2 rademacherMeasure))
    {C : ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 (gaussianReal 0 1) P C)
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStableLevyProcess 2 (gaussianReal 0 1) X Q)
    (hcdf : 0 < cdf (gaussianReal 0 1) 0 ∧
      cdf (gaussianReal 0 1) 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong rademacherMeasure
      (gaussianReal 0 1) normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw
        rademacherMeasure normalization n)) :
    (∀ᶠ n : ℕ in atTop, 0 <
      openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
        (1 / 2) (scale n) n) ∧
    Tendsto (fun n : ℕ => stableSmallDeviationRate 2
      rademacherMeasure scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
          (1 / 2) (scale n) n).toReal)
      atTop (𝓝 (C * 2 ^ (2 : ℝ))) := by
  let corridor : ContinuousAdmissibleStepCorridor := centeredUnitCorridor
  have hcorridorSet : centeredUnitCorridorFiniteUnion.toSet =
      corridorSet corridor.upper corridor.lower := by
    dsimp [corridor]
    rw [centeredUnitCorridorFiniteUnion_toSet]
    rfl
  have hrate := tendsto_scaledLog_normalizedStepCorridor_eq_energyRate
    hscale (by norm_num) (by norm_num) hslow hEscape hX hcdf hDOA
    htightBase corridor
  have hprobabilityEq (n : ℕ) (hn : 0 < n) (hs : 0 < scale n) :
      iidSequenceLaw rademacherMeasure
          {increment : ℕ → ℝ |
            RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
              corridorSet corridor.upper corridor.lower} =
        openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
          (1 / 2) (scale n) n := by
    unfold openHorizontalTubeProbability
    congr 1
    ext increment
    change RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
      corridorSet corridor.upper corridor.lower ↔ _
    rw [← hcorridorSet]
    exact normalizedStepCadlagPathIcc_mem_centeredUnitCorridorFiniteUnion_iff_openTube
      (scale := scale) (n := n) hn hs increment
  have hscaled := hrate.2
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
        (1 / 2) (scale n) n := by
    filter_upwards [hrate.1, eventually_gt_atTop (0 : ℕ),
      hscale.eventually_scale_pos] with n hcorridor hn hs
    rw [← hprobabilityEq n hn hs]
    exact hcorridor
  have hlogEq : (fun n : ℕ => stableSmallDeviationRate 2
      rademacherMeasure scale n * Real.log
        (openHorizontalTubeProbability (iidSequenceLaw rademacherMeasure)
          (1 / 2) (scale n) n).toReal) =ᶠ[atTop]
      (fun n => stableSmallDeviationRate 2 rademacherMeasure scale n *
        Real.log
          (iidSequenceLaw rademacherMeasure
            {increment : ℕ → ℝ |
              RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
                corridorSet corridor.upper corridor.lower}).toReal) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hscale.eventually_scale_pos] with n hn hs
    rw [hprobabilityEq n hn hs]
  have henergy : (corridor.energy 2).toReal = 1 := by
    simp [corridor, centeredUnitCorridor_energy]
  have htarget : C * 2 ^ (2 : ℝ) * (corridor.energy 2).toReal =
      C * 2 ^ (2 : ℝ) := by rw [henergy]; ring
  rw [← htarget]
  exact ⟨hpositive, hscaled.congr' hlogEq.symm⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
