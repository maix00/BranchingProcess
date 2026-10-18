/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Levy
public import Probability.Process.Path.Skorokhod.RationalTime
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
import Probability.Process.Stable.SmallDeviation.Blocks.ReturnScale

/-!
# First-block return scaling for lower-bound proofs

This file contains the lower-bound proof helper that specializes stable
time-space scaling to the first interval of a finite uniform partition. For
the first-block path \(B_N(q)=X_{q/N}-X_0\), where
\(\mathcal C(l,u,c_-,c_+)\) is the set of rational paths staying in
\((l,u)\) and ending in \((c_-,c_+)\),
\[\mathbb P(B_N\in C_{l,u,c_-,c_+})=
  \mathbb P(X_{[0,1]}\in C_{N^{1/\alpha}l,N^{1/\alpha}u,
    N^{1/\alpha}c_-,N^{1/\alpha}c_+}).\]
The helper is used by the lower block estimates; the arbitrary-horizon
scaling theorem remains in `Blocks/ReturnScale.lean`.

The sole lemma is
`IsStableLevyProcess.firstBlock_corridorReturn_scale_inv`, which states the
displayed probability identity for a positive number of uniform blocks.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The first uniform block's return-corridor probability is the unit-time
probability with all spatial bounds multiplied by the stable scale of its
duration. -/
lemma IsStableLevyProcess.firstBlock_corridorReturn_scale_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) =
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (lower * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (upper * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (coreLower * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (coreUpper * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))) := by
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hscale := h.corridorReturn_timeSpaceScale_inv
    (rationalUniformBlockBoundary blocks 1 hblocks) ht
    lower upper coreLower coreUpper
  rw [rationalUniformBlockProcess_zero_eq_initial]
  exact hscale

end ProbabilityTheory

end
