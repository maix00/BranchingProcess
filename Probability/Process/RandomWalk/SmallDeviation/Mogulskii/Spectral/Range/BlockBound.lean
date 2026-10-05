/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.BlockDonsker
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate
import Probability.Process.Path.Oscillation

/-!
# Fixed-cover upper bound for diffusive blocks

For a fixed finite Brownian corridor cover, Donsker bounds the probability of
one discrete oscillation block. This is the one-block input for the later
independent-block product estimate; all cover and enlargement parameters are
fixed before the small-deviation index tends to infinity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


open ProbabilityTheory.Process.Path

/-- For a fixed block constant, finite cover count, and small relative
enlargement, the oscillation probability of one diffusive block is
eventually bounded by twice the explicit Brownian finite-cover spectral
bound. -/
theorem eventually_diffusiveBlockOscillationProbability_le_of_fixedCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant enlargement : ℝ} {count : ℕ}
    (hconstant : 0 < constant) (henlargement : 0 < enlargement)
    (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (scale n)
          (diffusiveBlockLength constant scale n)
          (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)} ≤
      ENNReal.ofReal (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt constant)) := by
  let blockWidth : ℝ := (1 + enlargement) / Real.sqrt constant
  let coverFactor : ℝ := 1 + 3 / (count : ℝ)
  let spectralBound : ℝ := finiteCoverRangeBound count blockWidth
  let upperBound : ℝ := 2 * spectralBound
  have hcountPos : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hspectralPos : 0 < spectralBound := by
    dsimp [spectralBound, finiteCoverRangeBound,
      finiteCoverCorridorExponential, blockWidth]
    positivity
  have hupperPos : 0 < upperBound := by
    dsimp [upperBound]
    positivity
  have hroot : Tendsto
      (fun n => Real.sqrt (diffusiveBlockLength constant scale n) / scale n)
      atTop (nhds (Real.sqrt constant)) :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div hscale hconstant
  have hrootPos : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have henlargeTarget : Real.sqrt constant / (1 + enlargement) <
      Real.sqrt constant := by
    rw [div_lt_iff₀ (by positivity : 0 < 1 + enlargement)]
    nlinarith
  have hrootLower : ∀ᶠ n : ℕ in atTop,
      Real.sqrt constant / (1 + enlargement) <
        Real.sqrt (diffusiveBlockLength constant scale n) / scale n :=
    hroot.eventually (eventually_gt_nhds henlargeTarget)
  have hscaleRatio : ∀ᶠ n : ℕ in atTop,
      scale n / Real.sqrt (diffusiveBlockLength constant scale n) ≤ blockWidth := by
    filter_upwards [hrootLower, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant] with n hlow hscalePos hlenPos
    have hsqrtPos : 0 < Real.sqrt (diffusiveBlockLength constant scale n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hlenPos)
    have hratioPos : 0 < Real.sqrt (diffusiveBlockLength constant scale n) / scale n :=
      div_pos hsqrtPos hscalePos
    have hlowerPos : 0 < Real.sqrt constant / (1 + enlargement) := by
      exact div_pos hrootPos (by positivity)
    have hinv : (Real.sqrt (diffusiveBlockLength constant scale n) / scale n)⁻¹ <
        (Real.sqrt constant / (1 + enlargement))⁻¹ :=
      by simpa only [one_div] using one_div_lt_one_div_of_lt hlowerPos hlow
    have heq : scale n / Real.sqrt (diffusiveBlockLength constant scale n) =
        (Real.sqrt (diffusiveBlockLength constant scale n) / scale n)⁻¹ := by
      field_simp [hsqrtPos.ne', hscalePos.ne']
    have htarget : (Real.sqrt constant / (1 + enlargement))⁻¹ = blockWidth := by
      dsimp [blockWidth]
      field_simp [hrootPos.ne']
    exact (heq ▸ hinv.le).trans_eq htarget
  have hblockTop : Tendsto (diffusiveBlockLength constant scale) atTop atTop :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop hscale hconstant
  have hfixedLimsup :=
    limsup_iidSequenceLaw_blockOscillation_le_brownianRangeOscillationMass
      ν hcentered hsecondMoment hB hcontinuous hmeasurable
      (length := fun n => n) tendsto_id
      (blockWidth := fun n => blockWidth * Real.sqrt n)
      (width := blockWidth) (by
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hsqrtPos : 0 < Real.sqrt (n : ℝ) :=
          Real.sqrt_pos.2 (by exact_mod_cast hn)
        simpa using (le_of_eq (mul_div_cancel_right₀ blockWidth hsqrtPos.ne')))
  have hfixedProbabilityBound : ∀ᶠ m : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (blockWidth * Real.sqrt m) m
          (AdditivePath.blockCoordinates 0 m increment)} < ENNReal.ofReal upperBound := by
    have hmassBound := brownianRangeOscillationMass_le_smallWidthExponential
      hB hcontinuous hmeasurable (width := blockWidth) (count := count)
      (div_pos (by positivity) (Real.sqrt_pos.2 hconstant)) hcount
      (by simpa [finiteCoverCorridorExponential, blockWidth] using hspectral)
    have hmassStrict :
        rangeOscillationMass (P := P) hcontinuous blockWidth <
          ENNReal.ofReal upperBound := by
      have hmassBound' :
          rangeOscillationMass (P := P) hcontinuous blockWidth ≤
            ENNReal.ofReal spectralBound := by
        simpa [spectralBound, finiteCoverRangeBound,
          finiteCoverCorridorExponential, coverFactor, blockWidth] using hmassBound
      have hlt : ENNReal.ofReal spectralBound < ENNReal.ofReal upperBound := by
        apply (ENNReal.ofReal_lt_ofReal_iff hupperPos).2
        dsimp [upperBound]
        nlinarith
      exact hmassBound'.trans_lt hlt
    have hlimsup := hfixedLimsup.trans_lt hmassStrict
    have hprobBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => iidSequenceLaw ν {increment : ℕ → ℝ |
          blockOscillationEvent (blockWidth * Real.sqrt m) m
            (AdditivePath.blockCoordinates 0 m increment)}) := by
      apply Filter.isBoundedUnder_of_eventually_le (a := 1)
      exact Eventually.of_forall fun m : ℕ => by
        calc
          _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
    exact eventually_lt_of_limsup_lt hlimsup hprobBounded
  have hfixedAtBlocks := hblockTop.eventually hfixedProbabilityBound
  filter_upwards [hfixedAtBlocks, hscaleRatio,
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant] with n hfixed hratio hlenPos
  have hsqrtPos : 0 < Real.sqrt (diffusiveBlockLength constant scale n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hlenPos)
  have hwidth : scale n ≤ blockWidth *
      Real.sqrt (diffusiveBlockLength constant scale n) :=
    (div_le_iff₀ hsqrtPos).mp hratio
  have hsubset :
      {increment : ℕ → ℝ | blockOscillationEvent (scale n)
        (diffusiveBlockLength constant scale n)
        (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)} ⊆
      {increment : ℕ → ℝ | blockOscillationEvent
        (blockWidth * Real.sqrt (diffusiveBlockLength constant scale n))
        (diffusiveBlockLength constant scale n)
        (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)} := by
    intro increment hosc
    exact OscillationBounded.mono hwidth hosc
  calc
    iidSequenceLaw ν {increment : ℕ → ℝ | blockOscillationEvent (scale n)
        (diffusiveBlockLength constant scale n)
        (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)} ≤
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (blockWidth *
          Real.sqrt (diffusiveBlockLength constant scale n))
          (diffusiveBlockLength constant scale n)
          (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal upperBound := hfixed.le
    _ = ENNReal.ofReal (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt constant)) := by
      congr 1

/-- The discrete horizontal block comparison iterates the preceding
one-block estimate over every complete diffusive block. The last incomplete
block is ignored, as in the original horizontal blocking argument. -/
theorem eventually_horizontalTubeProbability_le_pow_fixedCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant enlargement : ℝ} {count : ℕ}
    (hconstant : 0 < constant) (henlargement : 0 < enlargement)
    (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (scale n) n ≤
      ENNReal.ofReal (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt constant)) ^
        (n / diffusiveBlockLength constant scale n) := by
  have hblock := eventually_diffusiveBlockOscillationProbability_le_of_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hconstant henlargement hcount hspectral
  filter_upwards [hblock, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant] with n hblock hscalePos hlengthPos
  have hhorizontal := horizontalTubeProbability_le_pow_blockOscillation
    ν (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hscalePos.le
    (diffusiveBlockLength constant scale n) n
  have hpow :
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (scale n) (diffusiveBlockLength constant scale n)
          (AdditivePath.blockCoordinates 0 (diffusiveBlockLength constant scale n) increment)}) ^
          (n / diffusiveBlockLength constant scale n) ≤
        ENNReal.ofReal (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) ^
            (n / diffusiveBlockLength constant scale n) := by
    gcongr
  exact hhorizontal.trans (hpow.trans_eq (by rfl))

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
