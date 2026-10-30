/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Block.Oscillation
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Analysis.Asymptotics.Scale.Block.Diffusive
import Probability.Process.RandomWalk.SmallDeviation.Range.FiniteCoverUpper
import Probability.Sequence.Block

/-!
# Diffusive finite-cover block estimate for Mogulskii's upper rate

This module specializes the reusable arbitrary-block estimate in
`Probability.Process.RandomWalk.SmallDeviation.Range.FiniteCoverUpper` to
Mogulskii's diffusive block lengths $L_n=\lfloor c s_n^2\rfloor$. For a fixed
cover count and enlargement, the block oscillation probability is eventually
bounded by twice the Brownian finite-cover spectral bound.

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_diffusiveBlockOscillationProbability_le_of_fixedCover`:
  the diffusive-block specialization used by the horizontal-tube power bound
  in `Rate/Bounds/Upper.lean`.

The fixed-cover argument is part of A. A. Mogul'skii, Theorem 3, Section 4,
p. 764, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.Process.Brownian.SmallDeviation.Range


open ProbabilityTheory.Process.Path
open ProbabilityTheory.RandomWalk.SmallDeviation.Range

/-- For a fixed block constant, finite cover count, and small relative
enlargement, the oscillation probability of one diffusive block is
eventually bounded by twice the explicit Brownian finite-cover spectral
bound. -/
lemma eventually_diffusiveBlockOscillationProbability_le_of_fixedCover
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
          (Asymptotics.diffusiveBlockLength constant scale n)
          (Combinatorics.Sequence.blockCoordinates 0 (Asymptotics.diffusiveBlockLength constant scale n) increment)} ≤
      ENNReal.ofReal (2 * finiteCoverRangeBound count
        ((1 + enlargement) / Real.sqrt constant)) := by
  let blockWidth : ℝ := (1 + enlargement) / Real.sqrt constant
  have hroot : Tendsto
      (fun n => Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n)
      atTop (nhds (Real.sqrt constant)) :=
    _root_.Asymptotics.IsSmallDeviationScale.tendsto_sqrt_diffusiveBlockLength_div
      hscale hconstant
  have hrootPos : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have henlargeTarget : Real.sqrt constant / (1 + enlargement) <
      Real.sqrt constant := by
    rw [div_lt_iff₀ (by positivity : 0 < 1 + enlargement)]
    nlinarith
  have hrootLower : ∀ᶠ n : ℕ in atTop,
      Real.sqrt constant / (1 + enlargement) <
        Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n :=
    hroot.eventually (eventually_gt_nhds henlargeTarget)
  have hscaleRatio : ∀ᶠ n : ℕ in atTop,
      scale n / Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) ≤ blockWidth := by
    filter_upwards [hrootLower,
      _root_.Asymptotics.IsSmallDeviationScale.eventually_pos hscale,
      _root_.Asymptotics.IsSmallDeviationScale.eventually_diffusiveBlockLength_pos hscale hconstant]
      with n hlow hscalePos hlenPos
    have hsqrtPos : 0 < Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hlenPos)
    have hratioPos : 0 < Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n :=
      div_pos hsqrtPos hscalePos
    have hlowerPos : 0 < Real.sqrt constant / (1 + enlargement) :=
      div_pos hrootPos (by positivity)
    have hinv : (Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n)⁻¹ <
        (Real.sqrt constant / (1 + enlargement))⁻¹ := by
      simpa only [one_div] using one_div_lt_one_div_of_lt hlowerPos hlow
    have heq : scale n / Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) =
        (Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n)⁻¹ := by
      field_simp [hsqrtPos.ne', hscalePos.ne']
    have htarget : (Real.sqrt constant / (1 + enlargement))⁻¹ = blockWidth := by
      dsimp [blockWidth]
      field_simp [hrootPos.ne']
    exact (heq ▸ hinv.le).trans_eq htarget
  have hblockTop : Tendsto (Asymptotics.diffusiveBlockLength constant scale) atTop atTop :=
    _root_.Asymptotics.IsSmallDeviationScale.tendsto_diffusiveBlockLength_atTop
      hscale hconstant
  exact eventually_iidSequenceLaw_blockOscillationProbability_le_of_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hblockTop hscaleRatio
    (div_pos (by positivity) hrootPos) hcount (by
      simpa [finiteCoverCorridorExponential, blockWidth] using hspectral)


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
