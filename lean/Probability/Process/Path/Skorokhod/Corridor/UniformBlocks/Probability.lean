module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Events
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# Probability bounds for uniform block restrictions

This module contains the measure-theoretic consequences of the generic
uniform-block construction.  It assumes only a measure on the sample space,
independence of the block paths, and equality of their laws; stable-process
instances are supplied by the Stable small-deviation adapters.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- For any measure on rational-coordinate paths, the global tube probability
is bounded by the probability of the intersection of its block restrictions.
This theorem is purely pathwise; independent increments are needed for the
product formula below. -/
theorem measure_rationalTube_le_uniformBlockInter
    (P : Measure (↑RationalGrid.RationalUnitInterval → ℝ)) (width : ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    P (Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks, rationalTubeBlockEvent width hblocks j) :=
  measure_mono
    (rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
      width hblocks)

/-- Independent block paths factor the probability of the intersection of
their tube events. This uses Mathlib's finite-family independence theorem. -/
theorem measure_iInter_rationalTubeBlock_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {blocks : ℕ}
    (X : Fin blocks → Ω → ↑RationalGrid.RationalUnitInterval → ℝ)
    (hblocks : iIndepFun X P) (width : ℝ) :
    P (⋂ j : Fin blocks,
        X j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
      ∏ j : Fin blocks,
        P (X j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) := by
  have hfactor := hblocks.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin blocks))
    (sets := fun _ => Skorokhod.rationalCoordinateOscillationTube width)
    (by
      intro j hj
      exact Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  simpa using hfactor

/-- The upper block inequality for a uniform rational partition, conditional
only on independence of the block paths and equality of their path laws. -/
theorem measure_rationalTube_le_pow_of_iIndep_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ↑RationalGrid.RationalUnitInterval → Ω → ℝ)
    {blocks : ℕ} (hblocksPos : 0 < blocks) (width : ℝ)
    (hindep : iIndepFun (rationalUniformBlockProcess X hblocksPos) P)
    (hsameLaw : ∀ j : Fin blocks,
      IdentDistrib (rationalUniformBlockProcess X hblocksPos j)
        (rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) P P) :
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P ((rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
  let blockProcess := rationalUniformBlockProcess X hblocksPos
  have hsubset :
      (fun ω q => X q ω) ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width ⊆
        ⋂ j : Fin blocks,
          blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width := by
    intro ω hω
    simp only [Set.mem_iInter]
    intro j
    have hglobal : (fun q => X q ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width := hω
    have hlocal :=
      rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
        width hblocksPos hglobal
    have hlocalj := Set.mem_iInter.mp hlocal j
    simpa [blockProcess, rationalUniformBlockProcess, rationalTubeBlockEvent,
      Set.mem_preimage] using hlocalj
  have hfactor := measure_iInter_rationalTubeBlock_eq_prod P blockProcess
    hindep width
  have hsame (j : Fin blocks) :
      P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
        P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width) := by
    exact (hsameLaw j).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  calc
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks,
        blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      measure_mono hsubset
    _ = ∏ j : Fin blocks,
        P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      hfactor
    _ = (P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
      simp_rw [hsame]
      simp

/-- Probability of a translated block tube, extended by `1` outside the
finite partition so that it can be indexed by all natural numbers. -/
def rationalUniformBlockTubeProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) (m : ℕ) : ENNReal :=
  if hm : m < blocks then
    P (rationalUniformBlockTubeEvent X width hblocks ⟨m, hm⟩)
  else 1

end ProbabilityTheory

end
