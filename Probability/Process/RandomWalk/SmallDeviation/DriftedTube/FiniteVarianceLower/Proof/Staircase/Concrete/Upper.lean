/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.FiniteUpper
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Endpoint.Windows
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Concrete.Lower.Entrance

/-!
# Upper-endpoint bound for Wang Yiyang's Lemma 3.5 staircase schedule

The public theorem in this file is:

- `exists_concreteStaircaseUpperEndpointLowerBound`:
  the same block schedule and interior windows as in the first part of
  Wang Yiyang's Lemma 3.5, with the last endpoint window placed near
  $s_L$, give $\mathbb P(E_{\rm upper})\ge\exp(-d'L/\Delta^2)$ once
  the explicit block inequalities and entrance bound hold.

This is the symmetric construction in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The Markov multiplication is the same
`exists_uniform_staircaseProbability_ge_product` theorem as for the
lower endpoint.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The rising staircase with a final upper-edge window gives a uniform
finite-width lower probability bound. -/
theorem exists_concreteStaircaseUpperEndpointLowerBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma narrowedRate uInterior vInterior uFinal vFinal : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huFinal : 0 < uFinal)
    (huvFinal : uFinal < vFinal)
    (hvFinal : vFinal < 1)
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ (entrance horizon blockLength : ℕ)
        (initial : Set (ℕ → ℝ))
        (margin globalWidth drift base endpointFraction
          blockRate totalRate : ℝ),
        entrance ≤ horizon → 0 < blockLength →
        entrance + blockLength ≤ horizon →
        MeasurableSet[sequencePrefixFiltration (E := ℝ) entrance] initial →
        0 < globalWidth → 0 < margin → 0 ≤ drift → 0 ≤ blockRate →
        2 * drift * (blockLength : ℝ) < globalWidth ^ 3 →
        (∀ increment ∈ initial,
          AdditivePath.displacement entrance increment ∈
            Set.Icc
              (staircaseLowerEdge base drift globalWidth
                (staircaseBlockStart entrance horizon blockLength) 0 +
                staircaseTubeWidth globalWidth drift
                  (staircaseBlockLength entrance horizon blockLength) 0 / 3)
              (staircaseLowerEdge base drift globalWidth
                (staircaseBlockStart entrance horizon blockLength) 0 +
                2 * staircaseTubeWidth globalWidth drift
                  (staircaseBlockLength entrance horizon blockLength) 0 / 3)) →
        (∀ j, j < staircaseBlockCount entrance horizon blockLength →
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
              staircaseBinEndpointUpperFraction m v₂)) →
        (∀ increment ∈ initial, ∀ time : ℕ,
          1 ≤ time → time ≤ entrance →
            base + drift * (time : ℝ) / globalWidth ^ 2 ≤
              AdditivePath.displacement time increment ∧
            AdditivePath.displacement time increment ≤
              base + drift * (time : ℝ) / globalWidth ^ 2 +
                globalWidth) →
        Real.exp (-(totalRate - blockRate) * (horizon : ℝ) /
          globalWidth ^ 2) ≤ (iidSequenceLaw ν).real initial →
        Real.exp (-totalRate * (horizon : ℝ) / globalWidth ^ 2) ≤
          (iidSequenceLaw ν).real
            (driftedTubeUpperEndpointWindowEvent horizon globalWidth
              drift base endpointFraction) := by
  obtain ⟨width₀, ratio₀, hfinite⟩ :=
    exists_uniform_finiteStaircaseUpperEndpointLowerBound
      hν hsigma m hm huInterior huvInterior hvInterior
        huFinal huvFinal hvFinal hrate
  refine ⟨width₀, ratio₀, ?_⟩
  intro entrance horizon blockLength initial margin globalWidth drift base
    endpointFraction blockRate totalRate hentrance hblockLength hremaining
    hinitial hglobalWidth hmargin hdrift hblockRate hcost hfirst
    hparameters hentranceTube hentranceProbability
  let start := staircaseBlockStart entrance horizon blockLength
  let length := staircaseBlockLength entrance horizon blockLength
  let q := staircaseBlockCount entrance horizon blockLength
  let lower := staircaseLowerEdge base drift globalWidth start
  let width := staircaseTubeWidth globalWidth drift length
  let v₁ := staircaseUpperEndpointLowerFraction q globalWidth drift
    endpointFraction length
  let v₂ := staircaseUpperEndpointUpperFraction q globalWidth drift
    endpointFraction length
  have hq : 0 < q :=
    staircaseBlockCount_pos_of_entrance_add_blockLength_le
      hblockLength hremaining
  have hnext : ∀ j, start (j + 1) = start j + length j :=
    staircaseBlockStart_next_eq_add_length hentrance
  have hstart : start 0 = entrance := staircaseBlockStart_zero hq
  have hfinish : start q = horizon :=
    staircaseBlockStart_count entrance horizon blockLength
  have hwidth : ∀ j, j < q → 0 < width j := by
    intro j hj
    exact staircaseTubeWidth_pos_of_schedule_bound hentrance
      hblockLength hglobalWidth hdrift hcost hj
  have hwindow : ∀ j, j + 1 < q →
      Set.Icc (lower j + v₁ j * width j)
        (lower j + v₂ j * width j) ⊆
      Set.Icc (lower (j + 1) + width (j + 1) / 3)
        (lower (j + 1) + 2 * width (j + 1) / 3) := by
    intro j hj
    rw [staircaseUpperEndpointWindow_interior base globalWidth drift
      endpointFraction start length hnext q j hj
      (ne_of_gt (hwidth j (by omega)))]
  have hparameters' : ∀ j, j < q →
      let narrowedWidth := staircaseBinWidth m * width j
      width₀ ≤ ⌊narrowedWidth⌋₊ ∧
      1 / margin ≤ narrowedWidth ∧
      ratio₀ * (⌊narrowedWidth⌋₊) ^ 2 ≤ length j ∧
      narrowedRate * globalWidth ^ 2 ≤
        blockRate * (⌊narrowedWidth⌋₊ : ℝ) ^ 2 ∧
      (j + 1 < q →
        staircaseBinEndpointLowerFraction m (v₁ j) + margin ≤
          uInterior ∧
        vInterior + margin ≤
          staircaseBinEndpointUpperFraction m (v₂ j)) ∧
      (¬j + 1 < q →
        staircaseBinEndpointLowerFraction m (v₁ j) + margin ≤
          uFinal ∧
        vFinal + margin ≤
          staircaseBinEndpointUpperFraction m (v₂ j)) := by
    intro j hj
    exact hparameters j hj
  have hfinal : Set.Icc (lower (q - 1) +
        v₁ (q - 1) * width (q - 1))
        (lower (q - 1) + v₂ (q - 1) * width (q - 1)) ⊆
      Set.Icc (base + drift * (horizon : ℝ) / globalWidth ^ 2)
          (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
            globalWidth) ∩
        Set.Icc
          (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
            globalWidth - endpointFraction * globalWidth)
          (base + drift * (horizon : ℝ) / globalWidth ^ 2 +
            globalWidth) :=
    staircaseUpperEndpointWindow_last_subset base globalWidth drift
      endpointFraction start length q horizon hq hnext hfinish
      hglobalWidth hdrift (ne_of_gt (hwidth (q - 1) (by omega)))
  have hmono (j : ℕ) :
      drift * (start j : ℝ) / globalWidth ^ 2 ≤
        drift * ((start j + length j : ℕ) : ℝ) / globalWidth ^ 2 := by
    have htime : (start j : ℝ) ≤
        ((start j + length j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right (start j) (length j))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htime hdrift)
      (sq_nonneg globalWidth)
  apply hfinite start length hnext q horizon hq hfinish initial
    (by rw [hstart]; exact hinitial)
    lower width v₁ v₂ margin globalWidth drift base endpointFraction
    blockRate totalRate hglobalWidth hmargin hblockRate hwidth
  · simpa only [hstart] using hfirst
  · exact hwindow
  · exact hparameters'
  · intro j hj
    simpa only [max_eq_right (hmono j)] using
      staircaseLowerEdge_eq_endBoundary base drift globalWidth
        start length hnext j
  · intro j hj
    simpa only [min_eq_left (hmono j)] using
      staircaseLowerEdge_add_staircaseTubeWidth_eq_startUpperBoundary
        base drift globalWidth start length hnext j
  · intro increment hin time ht htime
    exact hentranceTube increment hin time ht
      (by simpa only [hstart] using htime)
  · exact fun y hy => (hfinal hy).1
  · exact fun y hy => (hfinal hy).2
  · exact hentranceProbability

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
