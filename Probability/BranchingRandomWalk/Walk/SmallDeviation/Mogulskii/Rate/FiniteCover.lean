import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Rate.FinitePartition
import Combinatorics.BranchingWalk.Walk.Path.Corridor.FiniteCover

/-!
# Mogulskii lower rate from an interval cover

The finite reference family used by the return-kernel comparison is an
internal compactness device.  This file constructs it from the return
interval, so public rate statements need only geometric conditions on that
interval and a Gaussian-product inequality throughout its shrunken interior.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Construct the finite reference cover internally and derive a nontrivial
horizontal-tube lower rate.  Each reference point follows the linear skeleton
back to zero during the return block. -/
theorem exists_lowerRate_horizontalTubeProbability_of_IccCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnLower returnUpper coverMargin : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hreturnZero : (0 : ℝ) ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius : ℝ}
    (hcoverMargin : 0 < coverMargin)
    (hinside : returnLower + coverMargin ≤ returnUpper - coverMargin)
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    (houterInterior :
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < returnLower + coverMargin ∧
        returnUpper - coverMargin <
          1 - a - coverMargin - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (houterZero :
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < 0 ∧
        0 < 1 - a - coverMargin - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hreturnFinal :
      returnLower + coverMargin + (blocks : ℝ) * blockRadius < 0 ∧
        0 < returnUpper - coverMargin -
          (blocks : ℝ) * blockRadius)
    (hprincipal : ∀ y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin),
      ENNReal.ofReal (blocks * (constant / endpointMargin ^ 2)) <
        ∏ _j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              (((-y / (blocks : ℝ)) - blockRadius) /
                Real.sqrt constant)
              (((-y / (blocks : ℝ)) + blockRadius) /
                Real.sqrt constant))) :
    ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
        (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
          atTop.liminf (fun n =>
            scale n ^ 2 / (n : ℝ) *
              Real.log (horizontalTubeProbability
                (independentIncrementLaw ν) a (scale n) n).toReal) := by
  obtain ⟨references, hreference, hcover⟩ :=
    exists_finset_Icc_cover_inside hcoverMargin hinside
  have hlowerUpper : returnLower ≤ returnUpper := by
    linarith
  obtain ⟨y, hy, _⟩ := hcover returnLower ⟨le_rfl, hlowerUpper⟩
  have hreferences : references.Nonempty := ⟨y, hy⟩
  apply exists_lowerRate_horizontalTubeProbability_of_linearReturn
    ν hν hscale hscalePos hconstant hblocks ha0 ha1 hreturnZero
    hendpointMargin hblockRadius references hreferences hcover hreference
  · intro z hz
    have hzInterior := hreference z hz
    exact ⟨houterInterior.1.trans_le hzInterior.1,
      hzInterior.2.trans_lt houterInterior.2⟩
  · exact houterZero
  · exact hreturnFinal
  · intro z hz
    exact hprincipal z (hreference z hz)

/-- The Gaussian numerical condition can be discharged uniformly when the
return interval is narrow enough that every linear-return block shift is at
most half the block radius.  The diffusive block constant is then selected
internally and is shared by the whole finite reference cover. -/
theorem exists_constant_lowerRate_horizontalTubeProbability_of_IccCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnLower returnUpper coverMargin : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hreturnZero : (0 : ℝ) ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius : ℝ}
    (hcoverMargin : 0 < coverMargin)
    (hinside : returnLower + coverMargin ≤ returnUpper - coverMargin)
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    (houterInterior :
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < returnLower + coverMargin ∧
        returnUpper - coverMargin <
          1 - a - coverMargin - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (houterZero :
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < 0 ∧
        0 < 1 - a - coverMargin - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hreturnFinal :
      returnLower + coverMargin + (blocks : ℝ) * blockRadius < 0 ∧
        0 < returnUpper - coverMargin -
          (blocks : ℝ) * blockRadius)
    (hshift : ∀ y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin),
      |y / (blocks : ℝ)| ≤ blockRadius / 2) :
    ∃ constant > 0, constant ≤ 1 ∧
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
        (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
          atTop.liminf (fun n =>
            scale n ^ 2 / (n : ℝ) *
              Real.log (horizontalTubeProbability
                (independentIncrementLaw ν) a (scale n) n).toReal) := by
  obtain ⟨constant, hconstant, hconstantOne, error, herror,
      auxiliaryBound, hauxiliaryBound, hgap⟩ :=
    exists_constant_error_lowerBound_lt_linearReturn
      hendpointMargin hblockRadius hblocks
  have hprincipal : ∀ y ∈ Set.Icc (returnLower + coverMargin)
      (returnUpper - coverMargin),
      ENNReal.ofReal (blocks * (constant / endpointMargin ^ 2)) <
        ∏ _j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              (((-y / (blocks : ℝ)) - blockRadius) /
                Real.sqrt constant)
              (((-y / (blocks : ℝ)) + blockRadius) /
                Real.sqrt constant)) := by
    intro y hy
    have hreal : (blocks : ℝ) * (constant / endpointMargin ^ 2) ≤
        (blocks : ℝ) * (constant / endpointMargin ^ 2 + error) := by
      gcongr
      exact le_add_of_nonneg_right herror.le
    exact (ENNReal.ofReal_le_ofReal hreal).trans_lt
      ((le_add_left le_rfl).trans_lt (hgap y (hshift y hy)))
  obtain ⟨lowerBound, hlowerBound, hlowerBoundOne, hrate⟩ :=
    exists_lowerRate_horizontalTubeProbability_of_IccCover
      ν hν hscale hscalePos hconstant hblocks ha0 ha1 hreturnZero
      hcoverMargin hinside hendpointMargin hblockRadius houterInterior
      houterZero hreturnFinal hprincipal
  exact ⟨constant, hconstant, hconstantOne, lowerBound, hlowerBound,
    hlowerBoundOne, hrate⟩

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
