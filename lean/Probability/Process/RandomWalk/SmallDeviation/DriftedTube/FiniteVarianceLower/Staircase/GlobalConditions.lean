/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Endpoint.Margins
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Endpoint.UpperMargins
/-!
# Common global conditions for the staircase blocks

The public theorem in this file is:

- `staircaseBlockConditions_of_global`:
  if $10c\ell<\Delta^3$, the four global width, time, and rate
  inequalities together with four ordinary/final endpoint inequalities
  imply all six requirements for every staircase block. The endpoint
  interval for the final block is allowed to differ from that for the
  ordinary blocks.
- `staircaseUpperEndpointBlockConditions_of_global`:
  the same numeric conditions and ordinary-block margins, with the
  final endpoint margin placed near the upper tube boundary.

This is the common-threshold step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Global inequalities imply the numeric and endpoint conditions for every
scheduled horizontal block. -/
theorem staircaseBlockConditions_of_global
    {entrance horizon blockLength m width₀ ratio₀ : ℕ}
    {globalWidth drift endpointFraction margin narrowedRate blockRate
      uInterior vInterior uFinal vFinal : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hm : 2 ≤ m)
    (hwidth : 0 < globalWidth) (hdrift : 0 ≤ drift)
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (hcost : 10 * drift * (blockLength : ℝ) < globalWidth ^ 3)
    (hfloorThreshold : width₀ ≤
      ⌊staircaseBinWidth m * (globalWidth / 2)⌋₊)
    (hmarginWidth : 1 / margin ≤
      staircaseBinWidth m * (globalWidth / 2))
    (htime : ratio₀ *
      ⌊staircaseBinWidth m * globalWidth⌋₊ ^ 2 ≤ blockLength)
    (hrate : narrowedRate * globalWidth ^ 2 ≤
      blockRate *
        (⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ : ℝ) ^ 2)
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
        staircaseBinWidth m) :
    ∀ j, j < staircaseBlockCount entrance horizon blockLength →
      let width := staircaseTubeWidth globalWidth drift
        (staircaseBlockLength entrance horizon blockLength) j
      let v₁ := staircaseEndpointLowerFraction
        (staircaseBlockCount entrance horizon blockLength)
        globalWidth drift
        (staircaseBlockLength entrance horizon blockLength) j
      let v₂ := staircaseEndpointUpperFraction
        (staircaseBlockCount entrance horizon blockLength)
        globalWidth drift endpointFraction
        (staircaseBlockLength entrance horizon blockLength) j
      let narrowedWidth := staircaseBinWidth m * width
      width₀ ≤ ⌊narrowedWidth⌋₊ ∧
      1 / margin ≤ narrowedWidth ∧
      ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤
        staircaseBlockLength entrance horizon blockLength j ∧
      narrowedRate * globalWidth ^ 2 ≤
        blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
      (j + 1 < staircaseBlockCount entrance horizon blockLength →
        staircaseBinEndpointLowerFraction m v₁ + margin ≤
          uInterior ∧
        vInterior + margin ≤
          staircaseBinEndpointUpperFraction m v₂) ∧
      (¬j + 1 < staircaseBlockCount entrance horizon blockLength →
        staircaseBinEndpointLowerFraction m v₁ + margin ≤
          uFinal ∧
        vFinal + margin ≤
          staircaseBinEndpointUpperFraction m v₂) := by
  intro j hj
  have hnonneg : 0 ≤ drift * (blockLength : ℝ) := by positivity
  have hcostFour :
      4 * drift * (blockLength : ℝ) ≤ globalWidth ^ 3 := by
    nlinarith [hcost]
  have hcostTwo :
      2 * drift * (blockLength : ℝ) < globalWidth ^ 3 := by
    nlinarith [hcost]
  obtain ⟨hfloor, hmargin, hratio, hexponent⟩ :=
    staircaseBlockNumericConditions hentrance hblockLength hm
      hwidth hdrift hblockRate hcostFour hfloorThreshold
      hmarginWidth htime hrate hj
  obtain ⟨hinterior, hfinal⟩ :=
    staircaseEndpointMarginConditions hentrance hblockLength hm
      hwidth hdrift hendpoint hcostTwo hinteriorLower
      hinteriorUpper hfinalLower hfinalUpper hj
  exact ⟨hfloor, hmargin, hratio, hexponent, hinterior, hfinal⟩

/-- The same global block estimates with the terminal window next to the
upper boundary of the target tube. -/
theorem staircaseUpperEndpointBlockConditions_of_global
    {entrance horizon blockLength m width₀ ratio₀ : ℕ}
    {globalWidth drift endpointFraction margin narrowedRate blockRate
      uInterior vInterior uFinal vFinal : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hm : 2 ≤ m)
    (hwidth : 0 < globalWidth) (hdrift : 0 ≤ drift)
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (hcost : 10 * drift * (blockLength : ℝ) < globalWidth ^ 3)
    (hfloorThreshold : width₀ ≤
      ⌊staircaseBinWidth m * (globalWidth / 2)⌋₊)
    (hmarginWidth : 1 / margin ≤
      staircaseBinWidth m * (globalWidth / 2))
    (htime : ratio₀ *
      ⌊staircaseBinWidth m * globalWidth⌋₊ ^ 2 ≤ blockLength)
    (hrate : narrowedRate * globalWidth ^ 2 ≤
      blockRate *
        (⌊staircaseBinWidth m *
          (globalWidth - 2 * drift * (blockLength : ℝ) /
            globalWidth ^ 2)⌋₊ : ℝ) ^ 2)
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
      (1 - 1 / (3 * (m : ℝ))) / staircaseBinWidth m) :
    ∀ j, j < staircaseBlockCount entrance horizon blockLength →
      let width := staircaseTubeWidth globalWidth drift
        (staircaseBlockLength entrance horizon blockLength) j
      let v₁ := staircaseUpperEndpointLowerFraction
        (staircaseBlockCount entrance horizon blockLength)
        globalWidth drift endpointFraction
        (staircaseBlockLength entrance horizon blockLength) j
      let v₂ := staircaseUpperEndpointUpperFraction
        (staircaseBlockCount entrance horizon blockLength)
        globalWidth drift endpointFraction
        (staircaseBlockLength entrance horizon blockLength) j
      let narrowedWidth := staircaseBinWidth m * width
      width₀ ≤ ⌊narrowedWidth⌋₊ ∧
      1 / margin ≤ narrowedWidth ∧
      ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤
        staircaseBlockLength entrance horizon blockLength j ∧
      narrowedRate * globalWidth ^ 2 ≤
        blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
      (j + 1 < staircaseBlockCount entrance horizon blockLength →
        staircaseBinEndpointLowerFraction m v₁ + margin ≤
          uInterior ∧
        vInterior + margin ≤
          staircaseBinEndpointUpperFraction m v₂) ∧
      (¬j + 1 < staircaseBlockCount entrance horizon blockLength →
        staircaseBinEndpointLowerFraction m v₁ + margin ≤
          uFinal ∧
        vFinal + margin ≤
          staircaseBinEndpointUpperFraction m v₂) := by
  intro j hj
  have hcostFour :
      4 * drift * (blockLength : ℝ) ≤ globalWidth ^ 3 := by
    nlinarith [hcost]
  have hcostTwo :
      2 * drift * (blockLength : ℝ) < globalWidth ^ 3 := by
    nlinarith [hcost]
  obtain ⟨hfloor, hmargin, hratio, hexponent⟩ :=
    staircaseBlockNumericConditions hentrance hblockLength hm
      hwidth hdrift hblockRate hcostFour hfloorThreshold
      hmarginWidth htime hrate hj
  obtain ⟨hinterior, hfinal⟩ :=
    staircaseUpperEndpointMarginConditions hentrance hblockLength hm
      hwidth hdrift hendpoint hcostTwo hinteriorLower
      hinteriorUpper hfinalLower hfinalUpper hj
  exact ⟨hfloor, hmargin, hratio, hexponent, hinterior, hfinal⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
