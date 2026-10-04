/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.BlockBound
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Logarithmic transfer from finite-cover block bounds

The block estimate is converted to the Mogulskii normalization with the
complete-block count. A lower coboundedness hypothesis is kept explicit here;
the matching lower-bound argument is responsible for discharging it in the
two-sided theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open Combinatorics.Branching.Walk

/-- A fixed finite-cover block bound gives the corresponding normalized
logarithmic `limsup`, provided the tube probabilities are eventually
positive. The separate lower-bound route supplies the lower coboundedness
needed for a real-valued `limsup`. -/
theorem limsup_scaledLog_horizontalTubeProbability_le_of_fixedCover
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
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2)
    (hbound : finiteCoverRangeBound count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (independentIncrementLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => scale n ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (scale n) n).toReal) ≤
      (1 / constant) * Real.log
        (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) := by
  let blockLength : ℕ → ℕ := diffusiveBlockLength constant scale
  let blockCount : ℕ → ℕ := fun n => n / blockLength n
  let q : ℝ := 2 * finiteCoverRangeBound count
    ((1 + enlargement) / Real.sqrt constant)
  let probability : ℕ → ENNReal := fun n =>
    horizontalTubeProbability (independentIncrementLaw ν) (1 / 2) (scale n) n
  let coefficient : ℕ → ℝ := fun n =>
    (blockCount n : ℝ) * scale n ^ 2 / (n : ℝ)
  have hqPos : 0 < q := by
    dsimp [q, finiteCoverRangeBound, finiteCoverCorridorExponential]
    positivity
  have hqOne : q < 1 := by
    dsimp [q]
    linarith [hbound]
  have hblock := eventually_horizontalTubeProbability_le_pow_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hconstant henlargement hcount hspectral
  have hlog : ∀ᶠ n : ℕ in atTop,
      scale n ^ 2 / (n : ℝ) * Real.log (probability n).toReal ≤
        coefficient n * Real.log q := by
    filter_upwards [hblock, hpositive, hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant,
      (hscale.tendsto_nat_div_diffusiveBlockLength_atTop hconstant).eventually_gt_atTop 0]
      with n hblockN hpositiveN hscalePos hlengthPos hcountPos
    have hcountNat : 0 < blockCount n := by
      dsimp [blockCount, blockLength]
      exact hcountPos
    have hTubeOne : probability n ≤ 1 := by
      dsimp [probability, horizontalTubeProbability]
      calc
        independentIncrementLaw ν
            {increment | InHorizontalTube (1 / 2) (scale n) n increment} ≤
            independentIncrementLaw ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hTubeTop : probability n ≠ ⊤ :=
      ne_of_lt (hTubeOne.trans_lt ENNReal.one_lt_top)
    have hqENNTop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
    have hreal : (probability n).toReal ≤ q ^ blockCount n := by
      have hrealENN : (probability n).toReal ≤
          ((ENNReal.ofReal q) ^ blockCount n).toReal :=
        (ENNReal.toReal_le_toReal hTubeTop
          (ENNReal.pow_ne_top hqENNTop)).2 hblockN
      simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hqPos.le] using hrealENN
    have hrealPos : 0 < (probability n).toReal :=
      ENNReal.toReal_pos hpositiveN.ne' hTubeTop
    have hlogReal := Real.log_le_log hrealPos hreal
    rw [Real.log_pow] at hlogReal
    have hratioNonneg : 0 ≤ scale n ^ 2 / (n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlogReal hratioNonneg
    calc
      scale n ^ 2 / (n : ℝ) * Real.log (probability n).toReal ≤
          scale n ^ 2 / (n : ℝ) *
            ((blockCount n : ℝ) * Real.log q) := hmul
      _ = coefficient n * Real.log q := by
        dsimp [coefficient]
        ring
  have hcoefficient : Tendsto coefficient atTop (nhds (1 / constant)) := by
    simpa [coefficient, blockCount, blockLength] using
      hscale.tendsto_completeBlockCount_mul_sq_div hconstant
  have hright : Tendsto (fun n => coefficient n * Real.log q) atTop
      (nhds ((1 / constant) * Real.log q)) := hcoefficient.mul_const _
  calc
    atTop.limsup (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (probability n).toReal) ≤
      atTop.limsup (fun n => coefficient n * Real.log q) :=
        Filter.limsup_le_limsup hlog hlowerCobounded hright.isBoundedUnder_le
    _ = (1 / constant) * Real.log
        (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) := by
      simpa [q] using hright.limsup_eq

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
