/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Filtration.ConditionalBlocks
import Probability.Sequence.IID.Basic
import all Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
import all Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Geometry
/-!
# Common narrowed tubes give uniform block probabilities

## Internal proof declarations

For each bin $l<m$, suppose the narrowed endpoint-window event has probability at least $b$. Then the translated target event has the same lower bound for every entrance position in the central window:

$$
\left(\forall l<m,\ b\leq (\operatorname{iidSequenceLaw}\nu)(H_l)\right)
\Longrightarrow
\forall y\in[r+\Delta/3,r+2\Delta/3],\quad
b\leq (\operatorname{iidSequenceLaw}\nu)(T_y).
$$

Here $H_l$ is the fixed narrowed tube for bin $l$, and $T_y$ is the target tube translated by $r-y$.
The supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.relativeHorizontalTubeProbability_ge_of_staircaseBinBounds`:
  lower probability bounds for the finitely many fixed narrowed tubes
  give one lower bound for every starting point in the central window.

This is the finite spatial-bin selection and probability monotonicity in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. Its fixed-bin estimates are
provided by Chapter 3, Lemma 3.1(ii), based on Theorem 3, Section 4, p. 764
of A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube


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
