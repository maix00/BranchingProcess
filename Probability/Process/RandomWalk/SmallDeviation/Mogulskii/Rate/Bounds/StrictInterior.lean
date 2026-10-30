/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.LiminfLimsup
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Sequence.IID.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Bounds.Lemmas.ThreePointReferences

/-!
# Mogulskii lower rate for a strict interior horizontal tube

The proof uses a three-point return cover and compares the maximal-inequality
error with finite Gaussian return products. The public strict-interior rate
theorem assumes only the eventual positivity contained in `IsMogulskiiScale`;
the cover construction and Gaussian estimates are discharged internally.

This is the strict horizontal-tube lower-rate construction in A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.

The three-point return-margin choice is local to the proof.

## Public declarations

The declaration is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.exists_lowerRate_horizontalTubeProbability_of_strictInterior`:
  every fixed horizontal tube with $0<a<1$ has such a finite logarithmic
  lower rate, with the return parameters chosen internally.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Every horizontal tube containing the starting point in its strict
interior has a finite logarithmic lower rate.  The return radius and its
quadratically scaled block constant are chosen internally, so no numerical
Gaussian-product condition remains in the public statement. -/
theorem exists_lowerRate_horizontalTubeProbability_of_strictInterior
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
        (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
          atTop.liminf (fun n =>
            scale n ^ 2 / (n : ℝ) *
              Real.log (horizontalTubeProbability
                (iidSequenceLaw ν) a (scale n) n).toReal) := by
  let interior : ℝ := min a (1 - a)
  have hinterior : 0 < interior := by
    rw [show interior = min a (1 - a) by rfl, lt_min_iff]
    exact ⟨ha, sub_pos.mpr haOne⟩
  let endpointMargin : ℝ := interior / 2
  have hendpointMargin : 0 < endpointMargin := by
    exact div_pos hinterior (by norm_num)
  obtain ⟨returnMargin, hreturnMargin, hreturnUpper, hprincipal⟩ :=
    exists_returnMargin_principal_gaussianProduct
      (endpointMargin := endpointMargin)
      (show 0 < interior / 16 by positivity) hblocks
  have hinteriorLeft : interior ≤ a := min_le_left _ _
  have hinteriorRight : interior ≤ 1 - a := min_le_right _ _
  have hleft : endpointMargin + 4 * returnMargin < a := by
    dsimp [endpointMargin]
    nlinarith
  have hright : endpointMargin + 4 * returnMargin < 1 - a := by
    dsimp [endpointMargin]
    nlinarith
  refine ⟨returnMargin ^ 2, sq_pos_of_pos hreturnMargin, ?_⟩
  exact
    exists_lowerRate_horizontalTubeProbability_of_threePointReferences
      ν hν hscale (sq_pos_of_pos hreturnMargin) hblocks
      hreturnMargin hendpointMargin hleft hright hprincipal

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
