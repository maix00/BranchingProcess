/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Setup.Numeric
/-!
# Ordinary and final staircase endpoint margins

The public theorem in this file is:

- `staircaseEndpointMarginConditions`:
  with $b=1-1/(3m)$ and $D_*=2c\ell/\Delta^2<\Delta$, four
  inequalities at the global scales $\Delta$ and $\Delta-D_*$ imply the
  endpoint-window margin inequalities for every horizontal block.
  Ordinary blocks use an interior interval $(u_{\rm int},v_{\rm int})$;
  the final block uses a separate interval $(u_{\rm fin},v_{\rm fin})$.

This is the two-case endpoint comparison in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5, immediately before the common-threshold
contradiction argument.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Global margin inequalities imply the corresponding margin inequalities
for every ordinary and final horizontal block. -/
theorem staircaseEndpointMarginConditions
    {entrance horizon blockLength m : ℕ}
    {globalWidth drift endpointFraction margin
      uInterior vInterior uFinal vFinal : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hm : 2 ≤ m)
    (hwidth : 0 < globalWidth) (hdrift : 0 ≤ drift)
    (hendpoint : 0 ≤ endpointFraction)
    (hcost : 2 * drift * (blockLength : ℝ) < globalWidth ^ 3)
    (hinteriorLower :
      ((globalWidth / 3 +
          (2 / 3 : ℝ) *
            (2 * drift * (blockLength : ℝ) / globalWidth ^ 2)) /
          (globalWidth -
            2 * drift * (blockLength : ℝ) / globalWidth ^ 2)) /
        staircaseBinWidth m + margin ≤ uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hfinalLower : margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    let q := staircaseBlockCount entrance horizon blockLength
    let length := staircaseBlockLength entrance horizon blockLength
    let v₁ := staircaseEndpointLowerFraction q globalWidth drift length j
    let v₂ := staircaseEndpointUpperFraction q globalWidth drift
      endpointFraction length j
    (j + 1 < q →
      staircaseBinEndpointLowerFraction m v₁ + margin ≤ uInterior ∧
      vInterior + margin ≤ staircaseBinEndpointUpperFraction m v₂) ∧
    (¬j + 1 < q →
      staircaseBinEndpointLowerFraction m v₁ + margin ≤ uFinal ∧
      vFinal + margin ≤ staircaseBinEndpointUpperFraction m v₂) := by
  let q := staircaseBlockCount entrance horizon blockLength
  let length := staircaseBlockLength entrance horizon blockLength
  let actualWidth := staircaseTubeWidth globalWidth drift length j
  let loss := 2 * drift * (blockLength : ℝ) / globalWidth ^ 2
  have hsq : 0 < globalWidth ^ 2 := sq_pos_of_pos hwidth
  have hlossNonneg : 0 ≤ loss := by dsimp [loss]; positivity
  have hlossSmall : loss < globalWidth := by
    dsimp [loss]
    exact (div_lt_iff₀ hsq).2 (by nlinarith [hcost])
  have hminWidth : 0 < globalWidth - loss := by linarith
  have hactualPositive : 0 < actualWidth :=
    staircaseTubeWidth_pos_of_schedule_bound hentrance
      hblockLength hwidth hdrift hcost hj
  have hactualLow : globalWidth - loss ≤ actualWidth :=
    staircaseTubeWidth_ge_commonLossBound hentrance
      hblockLength hwidth hdrift hj
  have hactualHigh : actualWidth ≤ globalWidth :=
    staircaseTubeWidth_le_globalWidth hdrift
  have hβ : 0 < staircaseBinWidth m := staircaseBinWidth_pos hm
  constructor
  · intro hbefore
    have hnext : j + 1 < q := hbefore
    have hnextWidth : globalWidth - loss ≤
        staircaseTubeWidth globalWidth drift length (j + 1) :=
      staircaseTubeWidth_ge_commonLossBound hentrance
        hblockLength hwidth hdrift hnext
    have hnextLoss :
        drift * (length (j + 1) : ℝ) / globalWidth ^ 2 ≤ loss := by
      dsimp [loss] at hnextWidth ⊢
      unfold staircaseTubeWidth at hnextWidth
      linarith
    have hnextLossNonneg :
        0 ≤ drift * (length (j + 1) : ℝ) / globalWidth ^ 2 := by
      positivity
    have hnumNonneg :
        0 ≤ globalWidth / 3 + (2 / 3 : ℝ) * drift *
          (length (j + 1) : ℝ) / globalWidth ^ 2 := by positivity
    have hnumBound :
        globalWidth / 3 + (2 / 3 : ℝ) * drift *
            (length (j + 1) : ℝ) / globalWidth ^ 2 ≤
          globalWidth / 3 + (2 / 3 : ℝ) * loss := by
      have hscale :
          (2 / 3 : ℝ) * drift * (length (j + 1) : ℝ) /
              globalWidth ^ 2 =
            (2 / 3 : ℝ) *
              (drift * (length (j + 1) : ℝ) / globalWidth ^ 2) := by
        ring
      rw [hscale]
      linarith
    have hv₁Bound :
        staircaseEndpointLowerFraction q globalWidth drift length j ≤
          (globalWidth / 3 + (2 / 3 : ℝ) * loss) /
            (globalWidth - loss) := by
      rw [staircaseEndpointLowerFraction, ite_eq_left hbefore]
      calc
        (globalWidth / 3 + (2 / 3 : ℝ) * drift *
            (length (j + 1) : ℝ) / globalWidth ^ 2) / actualWidth ≤
          (globalWidth / 3 + (2 / 3 : ℝ) * drift *
            (length (j + 1) : ℝ) / globalWidth ^ 2) /
              (globalWidth - loss) :=
          div_le_div_of_nonneg_left hnumNonneg hminWidth hactualLow
        _ ≤ (globalWidth / 3 + (2 / 3 : ℝ) * loss) /
              (globalWidth - loss) :=
          div_le_div_of_nonneg_right hnumBound hminWidth.le
    have hv₂Bound : (2 / 3 : ℝ) ≤
        staircaseEndpointUpperFraction q globalWidth drift
          endpointFraction length j := by
      rw [staircaseEndpointUpperFraction, ite_eq_left hbefore]
      apply (le_div_iff₀ hactualPositive).2
      have hnextTerm :
          0 ≤ (1 / 3 : ℝ) * drift *
            (length (j + 1) : ℝ) / globalWidth ^ 2 := by
        positivity
      linarith [mul_le_mul_of_nonneg_left hactualHigh
        (show (0 : ℝ) ≤ 2 / 3 by norm_num)]
    constructor
    · unfold staircaseBinEndpointLowerFraction
      have hquot := div_le_div_of_nonneg_right hv₁Bound hβ.le
      calc
        staircaseEndpointLowerFraction q globalWidth drift length j /
            staircaseBinWidth m + margin ≤
          (globalWidth / 3 + (2 / 3 : ℝ) * loss) /
              (globalWidth - loss) / staircaseBinWidth m + margin :=
          by simpa only [add_comm margin] using add_le_add_right hquot margin
        _ ≤ uInterior := by simpa only [loss] using hinteriorLower
    · unfold staircaseBinEndpointUpperFraction
      have hquot := div_le_div_of_nonneg_right
        (sub_le_sub_right hv₂Bound (1 / (3 * (m : ℝ)))) hβ.le
      exact hinteriorUpper.trans hquot
  · intro hlast
    have hv₁ : staircaseEndpointLowerFraction q globalWidth drift length j = 0 := by
      rw [staircaseEndpointLowerFraction, ite_eq_right hlast]
    have hv₂Bound : endpointFraction ≤
        staircaseEndpointUpperFraction q globalWidth drift
          endpointFraction length j := by
      rw [staircaseEndpointUpperFraction, ite_eq_right hlast]
      apply (le_div_iff₀ hactualPositive).2
      exact mul_le_mul_of_nonneg_left hactualHigh hendpoint
    constructor
    · change staircaseBinEndpointLowerFraction m
          (staircaseEndpointLowerFraction q globalWidth drift length j) +
          margin ≤ uFinal
      rw [staircaseBinEndpointLowerFraction, hv₁]
      simpa using hfinalLower
    · unfold staircaseBinEndpointUpperFraction
      have hquot := div_le_div_of_nonneg_right
        (sub_le_sub_right hv₂Bound (1 / (3 * (m : ℝ)))) hβ.le
      exact hfinalUpper.trans hquot

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
