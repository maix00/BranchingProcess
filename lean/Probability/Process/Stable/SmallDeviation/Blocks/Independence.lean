module

public import Probability.Process.Stable.SmallDeviation.Blocks
public import Probability.Process.IndepIncrements.DisjointPaths

/-!
# Independence of neighboring stable-process blocks

The translated rational-coordinate paths on consecutive uniform blocks are
independent. The proof uses full process independence of adjacent increment
paths, not merely pairwise independence of individual increments.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The complete translated paths on two neighboring blocks of a stable
Lévy process are independent in the rational-coordinate product space. -/
theorem IsStableLevyProcess.indepFun_adjacentRationalUniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) (hnext : j.val + 1 = j'.val) :
    (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω) ⟂ᵢ[P]
    (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j' q ω) := by
  let a := rationalUniformBlockAbsoluteTime hblocks j ⊥
  let b := rationalUniformBlockAbsoluteTime hblocks j ⊤
  let c := rationalUniformBlockAbsoluteTime hblocks j' ⊤
  have hleft (q : ↑Skorokhod.RationalunitInterval) :
      a ≤ rationalUniformBlockAbsoluteTime hblocks j q ∧
        rationalUniformBlockAbsoluteTime hblocks j q ≤ b := by
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j le_top⟩
  have hright (q : ↑Skorokhod.RationalunitInterval) :
      b ≤ rationalUniformBlockAbsoluteTime hblocks j' q ∧
        rationalUniformBlockAbsoluteTime hblocks j' q ≤ c := by
    dsimp [b, c]
    rw [rationalUniformBlockAbsoluteTime_top_eq_bot_of_succ hblocks j j' hnext]
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j' bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j' le_top⟩
  have hindep := h.increments.indepIncrements.indepFun_adjacentPaths
    (fun t => h.increments.aemeasurable_eval t) a b c
    (rationalUniformBlockAbsoluteTime hblocks j)
    (rationalUniformBlockAbsoluteTime hblocks j') hleft hright
  dsimp [b] at hindep
  rw [rationalUniformBlockAbsoluteTime_top_eq_bot_of_succ hblocks j j' hnext]
    at hindep
  simpa [a, b, c, rationalUniformBlockProcessFromLevy] using hindep

/-- The tube events of two neighboring stable-process blocks factor exactly.
This is the two-block probability identity underlying the upper block bound. -/
theorem IsStableLevyProcess.measure_inter_adjacentRationalUniformBlockTubes
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) (hnext : j.val + 1 = j'.val) (width : ℝ) :
    P (((fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ∩
      ((fun ω q => rationalUniformBlockProcessFromLevy X hblocks j' q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) =
      P ((fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) *
      P ((fun ω q => rationalUniformBlockProcessFromLevy X hblocks j' q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) := by
  exact (h.indepFun_adjacentRationalUniformBlocks blocks hblocks j j' hnext).measure_inter_preimage_eq_mul
    _ _ (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)

end ProbabilityTheory
