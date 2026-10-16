/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Geometry
/-!
# Common narrowed tubes give uniform block probabilities

The module-visible lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.relativeHorizontalTubeProbability_ge_of_staircaseBinBounds`:
  lower probability bounds for the finitely many fixed narrowed tubes
  give one lower bound for every starting point in the central window.

This is the finite spatial-bin selection and probability monotonicity in
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5. Its fixed-bin estimates are
provided by that work's Lemma 3.1(ii), based on Mogul'skii,
"Small Deviations in a Space of Trajectories," Theorem 3, Section 4,
p. 764 of the 1974 Russian original (DOI 10.1137/1119081).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The lower bound for every fixed narrowed sub-tube transfers to the
target tube at every point of its central entrance window. -/
lemma relativeHorizontalTubeProbability_ge_of_staircaseBinBounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {m horizon : ℕ} {width v₁ v₂ lowerEdge bound : ℝ}
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hbins : ∀ l : ℕ, l < m →
      bound ≤ (iidSequenceLaw ν).real
        (horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width) horizon
          (staircaseBinEndpointLowerFraction m v₁)
          (staircaseBinEndpointUpperFraction m v₂)))
    (position : ℝ)
    (hposition : position ∈
      Set.Icc (lowerEdge + width / 3)
        (lowerEdge + 2 * width / 3)) :
    bound ≤ (iidSequenceLaw ν).real
      (relativeHorizontalTubeEndpointWindowEvent
        (lowerEdge - position) width horizon v₁ v₂) := by
  obtain ⟨l, hl, hsubset⟩ :=
    exists_staircaseBin_commonEvent_subset_centerWindow
      hm hwidth hposition
  exact (hbins l hl).trans
    (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono hsubset))

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
