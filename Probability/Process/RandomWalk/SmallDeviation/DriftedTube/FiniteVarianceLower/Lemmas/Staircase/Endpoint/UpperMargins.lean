/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Endpoint.Margins

/-!
# Endpoint margins for the upper-window staircase

The public theorem in this file is:

- `staircaseUpperEndpointMarginConditions`:
  the ordinary blocks retain the margins of the lower-window
  staircase; the final block uses the normalized window
  $[\max(1-v,0)\Delta/\Delta(q),1]$.

This is the symmetric final-window choice in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Uniform ordinary and final margins for a staircase ending next to
the upper edge of the target tube. -/
lemma staircaseUpperEndpointMarginConditions
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
    (hfinalLower :
      (max (1 - endpointFraction) 0 * globalWidth /
          (globalWidth -
            2 * drift * (blockLength : ℝ) / globalWidth ^ 2)) /
        staircaseBinWidth m + margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (1 - 1 / (3 * (m : ℝ))) / staircaseBinWidth m)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    let q := staircaseBlockCount entrance horizon blockLength
    let length := staircaseBlockLength entrance horizon blockLength
    let v₁ := staircaseUpperEndpointLowerFraction q globalWidth drift
      endpointFraction length j
    let v₂ := staircaseUpperEndpointUpperFraction q globalWidth drift
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
  have hβ : 0 < staircaseBinWidth m := staircaseBinWidth_pos hm
  have hsq : 0 < globalWidth ^ 2 := sq_pos_of_pos hwidth
  have hlossSmall : loss < globalWidth := by
    dsimp [loss]
    exact (div_lt_iff₀ hsq).2 (by nlinarith [hcost])
  have hminWidth : 0 < globalWidth - loss := by linarith
  have hactualLow : globalWidth - loss ≤ actualWidth :=
    staircaseTubeWidth_ge_commonLossBound hentrance
      hblockLength hwidth hdrift hj
  have hordinary := staircaseEndpointMarginConditions
    (uFinal := margin)
    (vFinal :=
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m - margin)
    hentrance hblockLength hm hwidth hdrift hendpoint hcost
    hinteriorLower hinteriorUpper (le_refl margin)
    (by simp) hj
  constructor
  · intro hbefore
    have hOrd := hordinary.1 hbefore
    simpa only [staircaseUpperEndpointLowerFraction,
      staircaseUpperEndpointUpperFraction, ite_eq_left hbefore]
      using hOrd
  · intro hlast
    have hnumNonneg :
        0 ≤ max (1 - endpointFraction) 0 * globalWidth :=
      mul_nonneg (le_max_right _ _) hwidth.le
    have hv₁Bound :
        staircaseUpperEndpointLowerFraction q globalWidth drift
            endpointFraction length j ≤
          max (1 - endpointFraction) 0 * globalWidth /
            (globalWidth - loss) := by
      rw [staircaseUpperEndpointLowerFraction,
        ite_eq_right hlast]
      exact div_le_div_of_nonneg_left hnumNonneg hminWidth hactualLow
    constructor
    · unfold staircaseBinEndpointLowerFraction
      have hquot := div_le_div_of_nonneg_right hv₁Bound hβ.le
      have hbound :
          (max (1 - endpointFraction) 0 * globalWidth /
              (globalWidth - loss)) /
            staircaseBinWidth m + margin ≤ uFinal := by
        simpa only [loss] using hfinalLower
      linarith
    · rw [staircaseUpperEndpointUpperFraction,
        ite_eq_right hlast]
      simpa only [staircaseBinEndpointUpperFraction] using hfinalUpper

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
