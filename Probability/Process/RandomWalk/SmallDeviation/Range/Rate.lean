/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Range.GaussianCover
public import Probability.Process.RandomWalk.SmallDeviation.Range.BlockOscillation

/-!
# Sharp range bounds from finite corridor rates

The public definitions and theorems are:

- `rangeCoverTarget`, `rangeCoverRelativeApproximation`, and
  `rangeCoverRelativeEnergyLimits`: the finite translated-corridor cover
  of the source-path range event and its constant energy approximation.
- `sourceRangeCoverProbabilityRate_of_centeredUnitVariance`:
  $\Delta_n^2/n\,\log\mathbb P(R_{k,n})\to
  -\pi^2\mathcal E_k/2$, where $\mathcal E_k$ is the cover energy.
- `blockOscillationEvent_subset_sourceRangeTube`:
  an increment block of oscillation at most $w$ lies in the normalized
  source-path range tube at spatial scale greater than $w/2$.
- `eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_centeredUnitVariance_rangeCover`:
  for a rate $d<\pi^2\mathcal E_k/2$, the block oscillation probability
  is eventually at most $\exp(-dn/\Delta_n^2)$.

Finite translated corridors cover paths whose range diameter is bounded.
Combining that cover with the raw increment-law Mogul'skii rate yields the
sharp finite-variance exponential rate for block oscillation.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Range

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- The range-cover target, restricted to the source path domain. -/
def rangeCoverTarget (k : ℕ) (hk : 0 < k) :
    Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.terminalLeftPathSpace ∩ (rangeCoverUnion k hk).toSet

/-- The constant relative corridor approximation of a finite range cover. -/
noncomputable def rangeCoverRelativeApproximation (k : ℕ) (hk : 0 < k) :
    RelativeFiniteCorridorUnionApproximation 2
      Skorokhod.terminalLeftPathSpace (rangeCoverTarget k hk) where
  inner := fun _ => rangeCoverUnion k hk
  outer := fun _ => rangeCoverUnion k hk
  inner_subset := by intro n f hf; exact hf
  subset_outer := by intro n f hf; exact hf
  energy_gap_tendsto_zero := by
    convert (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (rangeCoverUnion k hk).realEnergy -
        (rangeCoverUnion k hk).realEnergy)
      atTop (𝓝 ((rangeCoverUnion k hk).realEnergy -
        (rangeCoverUnion k hk).realEnergy))) using 1 <;> simp

/-- Energy limits for the constant approximation of a finite range cover. -/
noncomputable def rangeCoverRelativeEnergyLimits (k : ℕ) (hk : 0 < k) :
    RelativeFiniteCorridorUnionEnergyLimits (rangeCoverRelativeApproximation k hk) where
  innerLimit := (rangeCoverUnion k hk).realEnergy
  outerLimit := (rangeCoverUnion k hk).realEnergy
  inner_tendsto := by
    simpa [rangeCoverRelativeApproximation] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (rangeCoverUnion k hk).realEnergy) atTop
        (𝓝 ((rangeCoverUnion k hk).realEnergy)))
  outer_tendsto := by
    simpa [rangeCoverRelativeApproximation] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (rangeCoverUnion k hk).realEnergy) atTop
        (𝓝 ((rangeCoverUnion k hk).realEnergy)))

/-- The raw finite-variance Mogul'skii rate for the finite translated
corridor cover of a path range. -/
theorem sourceRangeCoverProbabilityRate_of_centeredUnitVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun n : ℕ => scale n ^ 2 / (n : ℝ) * Real.log
        ((iidSequenceLaw ν {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈
            rangeCoverTarget k hk}).toReal))
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (rangeCoverUnion k hk).realEnergy)) := by
  let data := rawNormalSourceRateData_of_centered_unitVariance
    hscale hcentered hsquare hvariance
  let rates := sourceScaledInnerOuterLogRate_of_centered_unitVariance
    hscale hcentered hsquare hvariance
    (show HasRelativeVanishingEnergyGapApproximation 2
      Skorokhod.terminalLeftPathSpace (rangeCoverTarget k hk) from
      ⟨rangeCoverRelativeApproximation k hk⟩)
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    sourceNormalizedStepCadlagPathIcc scale n increment
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (normalizedStepCadlagPathIcc scale n increment)
  have hnegative : data.timeFactor * data.sourceEscapeConstant < 0 := by
    rw [data.normalizedEscape_eq]
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hκ : 0 < rateCoefficient 2
      (data.timeFactor * data.sourceEscapeConstant) := rateCoefficient_pos hnegative
  have hFiniteUnionRate : ∀ C : FiniteCorridorUnion 2,
      (∀ n : ℕ, NullMeasurableSet {increment : ℕ → ℝ |
        paths n increment ∈ C.toSet} (iidSequenceLaw ν)) ∧
      (∀ᶠ n : ℕ in atTop,
        0 < (iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log
        ((iidSequenceLaw ν
          {increment : ℕ → ℝ | paths n increment ∈ C.toSet}).toReal) /
          probabilityRateDenominator 2 ν scale n)
        atTop (𝓝 (rateCoefficient 2
          (data.timeFactor * data.sourceEscapeConstant) * C.realEnergy)) := by
    intro C
    simpa [paths] using data.finiteCorridorUnionRate C
  have hcommon :=
    RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation
      (iidSequenceLaw ν) paths Skorokhod.terminalLeftPathSpace hpaths
      (probabilityRateDenominator 2 ν scale) data.denominator_tendsto_atBot hκ
      rates.approximation (rangeCoverRelativeApproximation k hk)
      rates.energyLimits (rangeCoverRelativeEnergyLimits k hk) hFiniteUnionRate
  have henergy : rates.energy = (rangeCoverUnion k hk).realEnergy := by
    calc
      rates.energy = rates.energyLimits.commonEnergy := rates.energy_eq
      _ = (rangeCoverRelativeEnergyLimits k hk).commonEnergy := hcommon
      _ = (rangeCoverUnion k hk).realEnergy := rfl
  have hrate := rates.outerRate
  rw [henergy] at hrate
  simpa [paths, rangeCoverTarget] using hrate

/-- Pairwise oscillation of the block partial sums is the range diameter of
the source-convention step path. -/
theorem blockOscillationEvent_subset_sourceRangeTube
    {n : ℕ} (hn : 0 < n) {width factor : ℝ}
    (hwidth : 0 < width) (hfactor : 1 < factor)
    (scale : ℕ → ℝ) (hscale : scale n = factor * width / 2)
    (increment : ℕ → ℝ)
    (hosc : blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)) :
    sourceNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.rangeTubeStartingAtZero 1 := by
  have hscalePos : 0 < scale n := by rw [hscale]; positivity
  have hoscBlock : OscillationBounded
      (fun i : Fin ((n - 1) + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) i)
      width := by
    change OscillationBounded _ width at hosc
    exact hosc
  have hdisplacement (i j : Fin n) :
      |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| ≤ width := by
    have h := hoscBlock
      (Fin.cast (by omega : n = (n - 1) + 1) i)
      (Fin.cast (by omega : n = (n - 1) + 1) j)
    change |Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) i) -
      Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) j)| ≤ width at h
    rw [partialSum_blockCoordinates (start := 0) (increment := increment)
          (Fin.cast (by omega : n = (n - 1) + 1) i),
      partialSum_blockCoordinates (start := 0) (increment := increment)
          (Fin.cast (by omega : n = (n - 1) + 1) j)] at h
    simpa [Fin.cast] using h
  have hrange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  let path := sourceNormalizedStepCadlagPathIcc scale n increment
  have hpathStart : path ⊥ = 0 := by
    change sourceNormalizedStepCadlagPathIcc scale n increment ⊥ = 0
    rw [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top
      scale n increment (t := ⊥) (by norm_num [unitInterval])]
    simp [normalizedStepPath, AdditivePath.displacement]
  have hRange : Set.range path =
      Set.range (fun k : Fin n => (scale n)⁻¹ *
        AdditivePath.displacement (k : ℕ) increment) := by
    simpa [path] using hrange
  have hpathOsc : Skorokhod.OscillationBounded path (width / scale n) := by
    intro s t
    have hs : path s ∈ Set.range path := ⟨s, rfl⟩
    have ht : path t ∈ Set.range path := ⟨t, rfl⟩
    rw [hRange] at hs ht
    rcases hs with ⟨i, hi⟩
    rcases ht with ⟨j, hj⟩
    rw [← hi, ← hj]
    have hdiff := hdisplacement i j
    change |(scale n)⁻¹ * AdditivePath.displacement (i : ℕ) increment -
        (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment| ≤ width / scale n
    rw [show (scale n)⁻¹ * AdditivePath.displacement (i : ℕ) increment -
        (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment =
          (scale n)⁻¹ * (AdditivePath.displacement (i : ℕ) increment -
            AdditivePath.displacement (j : ℕ) increment) by ring,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hscalePos.le)]
    calc
      (scale n)⁻¹ * |AdditivePath.displacement (i : ℕ) increment -
          AdditivePath.displacement (j : ℕ) increment| ≤ (scale n)⁻¹ * width :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hscalePos.le)
      _ = width / scale n := by rw [div_eq_mul_inv]; ring
  have hwidthScale : width / scale n = 2 / factor := by
    rw [hscale]
    field_simp [ne_of_gt hfactor, ne_of_gt hwidth]
  have hstrict : width / scale n < 2 := by
    rw [hwidthScale]
    exact (div_lt_iff₀ (by linarith : 0 < factor)).2 (by nlinarith)
  change path ⊥ = 0 ∧ path ∈ Skorokhod.oscillationInOpenTube (2 * 1)
  refine ⟨hpathStart, ?_⟩
  refine ⟨2 - width / scale n, sub_pos.mpr hstrict, ?_⟩
  simpa using hpathOsc

/-- The raw finite-variance path rate gives the sharp block oscillation
exponent. The factor `factor` is the spatial enlargement of the range tube;
the finite translated cover approaches the Gaussian range energy as `k` grows. -/
theorem eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_centeredUnitVariance_rangeCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {factor rate : ℝ} (hfactor : 1 < factor) (hrate : 0 < rate)
    (k : ℕ) (hk : 0 < k)
    (hrate_lt : rate < (Real.pi ^ 2 / 2) * (rangeCoverUnion k hk).realEnergy) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (2 * scale n / factor) (n - 1)
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)} ≤
        ENNReal.ofReal (Real.exp (-rate * ((n : ℝ) / scale n ^ 2))) := by
  let paths : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ := fun n increment =>
    sourceNormalizedStepCadlagPathIcc scale n increment
  let target : Set (CadlagPath unitInterval ℝ) := rangeCoverTarget k hk
  let targetEvent (n : ℕ) : Set (ℕ → ℝ) :=
    {increment | paths n increment ∈ target}
  have hpaths : ∀ n increment, paths n increment ∈
      Skorokhod.terminalLeftPathSpace := by
    intro n increment
    exact Skorokhod.terminalLeftPath_mem_space
      (normalizedStepCadlagPathIcc scale n increment)
  have hlimit := sourceRangeCoverProbabilityRate_of_centeredUnitVariance
    ν hcentered hsquare hvariance hscale k hk
  have hratePath : ∀ᶠ n : ℕ in atTop,
      (scale n ^ 2 / (n : ℝ)) * Real.log
        ((iidSequenceLaw ν (targetEvent n)).toReal) < -rate := by
    have htarget : -(Real.pi ^ 2) / 2 * (rangeCoverUnion k hk).realEnergy < -rate := by
      nlinarith [hrate_lt]
    filter_upwards [hlimit.eventually (eventually_lt_nhds htarget)] with n hn
    exact hn
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    (Asymptotics.IsSmallDeviationScale.tendsto_atTop hscale).eventually
      (eventually_gt_atTop 0)
  have htargetPos : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν (targetEvent n)).toReal := by
    let data := rawNormalSourceRateData_of_centered_unitVariance
      hscale hcentered hsquare hvariance
    let coverEvent (n : ℕ) : Set (ℕ → ℝ) :=
      {increment | paths n increment ∈ (rangeCoverUnion k hk).toSet}
    have hcoverPos := (data.finiteCorridorUnionRate (rangeCoverUnion k hk)).2.1
    have heventEq (n : ℕ) : targetEvent n = coverEvent n := by
      ext increment
      simp [targetEvent, coverEvent, target, rangeCoverTarget, hpaths n increment]
    filter_upwards [hcoverPos] with n hn
    simpa [heventEq n] using hn
  filter_upwards [hratePath, hscalePos, htargetPos,
      eventually_gt_atTop (0 : ℕ)] with n hratePath hscalePos htargetPos hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaleSq : 0 < scale n ^ 2 := sq_pos_of_pos hscalePos
  have hden : 0 < scale n ^ 2 / (n : ℝ) := div_pos hscaleSq hnReal
  let q : ℝ≥0∞ := iidSequenceLaw ν (targetEvent n)
  have hlog : Real.log q.toReal < -rate * ((n : ℝ) / scale n ^ 2) := by
    have hdiv : Real.log q.toReal < (-rate) / (scale n ^ 2 / (n : ℝ)) :=
      (lt_div_iff₀ hden).2 (by simpa [q, mul_comm] using hratePath)
    have heq : (-rate) / (scale n ^ 2 / (n : ℝ)) =
        -rate * ((n : ℝ) / scale n ^ 2) := by
      field_simp [ne_of_gt hscaleSq, ne_of_gt hnReal]
    rw [heq] at hdiv
    exact hdiv
  have hqle : q ≤ 1 := by
    calc
      q ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hqtop : q ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hqle ENNReal.one_lt_top)
  have hqpos : 0 < q.toReal := by simpa [q] using htargetPos
  have hreal : Real.exp (Real.log q.toReal) <
      Real.exp (-rate * ((n : ℝ) / scale n ^ 2)) := Real.exp_strictMono hlog
  have hprobReal : q.toReal < Real.exp (-rate * ((n : ℝ) / scale n ^ 2)) := by
    rwa [Real.exp_log hqpos] at hreal
  have htargetBound : q ≤ ENNReal.ofReal
      (Real.exp (-rate * ((n : ℝ) / scale n ^ 2))) := by
    rw [← ENNReal.ofReal_toReal hqtop]
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hprobReal.le
  have hwidth : 0 < 2 * scale n / factor := by positivity
  have hscaleIdentity : factor * (2 * scale n / factor) / 2 = scale n := by
    field_simp [ne_of_gt (by linarith : 0 < factor)]
  have hsubset :
      {increment : ℕ → ℝ | blockOscillationEvent (2 * scale n / factor)
        (n - 1) (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)} ⊆
      targetEvent n := by
    intro increment hosc
    have hTube := blockOscillationEvent_subset_sourceRangeTube hn hwidth
      hfactor scale hscaleIdentity.symm increment hosc
    have hcover := rangeTubeStartingAtZero_subset_rangeCoverUnion k hk hTube
    exact ⟨hpaths n increment, hcover⟩
  exact (measure_mono hsubset).trans htargetBound

end ProbabilityTheory.RandomWalk.SmallDeviation.Range

end
