module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Rate.Lower
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.GaussianProduct

@[expose] public section

/-!
# Mogulskii lower rate from a finite Gaussian partition

This file closes the interface between the finite-dimensional Gaussian
partition argument and the arbitrary-duration logarithmic rate.  Its
hypotheses are purely geometric and numerical; the intermediate uniform
return-block estimate is constructed internally.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Finite Gaussian return estimates with a strict common gap give a
horizontal-tube logarithmic lower rate.  The return interval contains zero,
so the iterated return construction starts from the zero-started walk. -/
theorem mul_log_toReal_le_liminf_horizontalTubeProbability_of_finset_gaussianProduct
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnLower returnUpper coverMargin : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hreturnZero : (0 : ℝ) ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius error : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (herror : 0 < error)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin))
    (houter : ∀ y ∈ references,
      y ∈ Set.Icc (-a + coverMargin)
        (1 - a - coverMargin))
    (hstartMargin : ∀ y ∈ references, ∀ k < blocks,
      -a + coverMargin - y + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          1 - a - coverMargin - y - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hfinalMargin : ∀ y ∈ references,
      returnLower + coverMargin - y + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range blocks, target y j ∧
        ∑ j ∈ Finset.range blocks, target y j <
          returnUpper - coverMargin - y -
            (blocks : ℝ) * blockRadius)
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hgap : ∀ y ∈ references,
      lowerBound + ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) <
        ∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) :
    (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n =>
        scale n ^ 2 / (n : ℝ) *
          Real.log (horizontalTubeProbability
            (independentIncrementLaw ν) a (scale n) n).toReal) := by
  have hblock := eventually_uniform_returnKernel_of_finset_gaussianProduct
    ν hν hscale (fun n => (hscalePos n).le) hconstant hblocks
    hendpointMargin hblockRadius herror references target hcover hreference
    houter hstartMargin hfinalMargin lowerBound hgap
  exact
    mul_log_toReal_le_liminf_normalizedLog_horizontalTubeProbability_of_return
      ν hscale hscalePos hconstant hblocks ha0 ha1 hreturnZero
      lowerBound hlowerBound hlowerBoundOne hblock

/-- A convenient specialization in which every reference point follows the
linear deterministic skeleton back to zero.  The hypotheses only say that
the reference points, the zero endpoint, and the return endpoint have the
required common safety margins. -/
theorem mul_log_toReal_le_liminf_horizontalTubeProbability_of_linearReturn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnLower returnUpper coverMargin : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hreturnZero : (0 : ℝ) ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius error : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (herror : 0 < error)
    (references : Finset ℝ)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin))
    (houterReference : ∀ y ∈ references,
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < y ∧
        y < 1 - a - coverMargin - endpointMargin -
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
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hgap : ∀ y ∈ references,
      lowerBound + ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) <
        ∏ _j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              (((-y / (blocks : ℝ)) - blockRadius) /
                Real.sqrt constant)
              (((-y / (blocks : ℝ)) + blockRadius) /
                Real.sqrt constant))) :
    (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n =>
        scale n ^ 2 / (n : ℝ) *
          Real.log (horizontalTubeProbability
            (independentIncrementLaw ν) a (scale n) n).toReal) := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  refine
    mul_log_toReal_le_liminf_horizontalTubeProbability_of_finset_gaussianProduct
      ν hν hscale hscalePos hconstant hblocks ha0 ha1 hreturnZero
      hendpointMargin hblockRadius herror references
      (fun y _ => -y / (blocks : ℝ)) hcover hreference ?_ ?_ ?_
      lowerBound hlowerBound hlowerBoundOne ?_
  · intro y hy
    have hs := houterReference y hy
    have hbr : 0 ≤ (blocks : ℝ) * blockRadius := by positivity
    constructor <;> linarith
  · intro y hy k hk
    have hkNonneg : 0 ≤ (k : ℝ) := by positivity
    have hkLt : (k : ℝ) < (blocks : ℝ) := by exact_mod_cast hk
    let q : ℝ := 1 - (k : ℝ) / (blocks : ℝ)
    have hqPos : 0 < q := by
      dsimp [q]
      exact sub_pos.mpr ((div_lt_one hblocksReal).2 hkLt)
    have hqOne : q ≤ 1 := by
      dsimp [q]
      exact sub_le_self _ (div_nonneg hkNonneg hblocksReal.le)
    have hsum : ∑ _j ∈ Finset.range k, -y / (blocks : ℝ) =
        (k : ℝ) * (-y / (blocks : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hposition : y + ∑ _j ∈ Finset.range k,
        -y / (blocks : ℝ) = q * y := by
      rw [hsum]
      dsimp [q]
      field_simp [hblocksReal.ne']
      ring
    have hs := houterReference y hy
    have hlower : -a + coverMargin + endpointMargin +
        (blocks : ℝ) * blockRadius < q * y := by
      rcases le_total y 0 with hy0 | hy0
      · have hqy : y ≤ q * y := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hqOne)
            (neg_nonneg.mpr hy0)]
        exact hs.1.trans_le hqy
      · have hqy : 0 ≤ q * y := mul_nonneg hqPos.le hy0
        exact houterZero.1.trans_le hqy
    have hupper : q * y < 1 - a - coverMargin - endpointMargin -
        (blocks : ℝ) * blockRadius := by
      rcases le_total y 0 with hy0 | hy0
      · have hqy : q * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqPos.le hy0
        exact hqy.trans_lt houterZero.2
      · have hqy : q * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hqOne) hy0]
        exact hqy.trans_lt hs.2
    rw [← hposition] at hlower hupper
    constructor <;> linarith
  · intro y hy
    have hsum : ∑ _j ∈ Finset.range blocks, -y / (blocks : ℝ) = -y := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hblocksReal.ne']
    rw [hsum]
    constructor <;> linarith [hreturnFinal.1, hreturnFinal.2]
  · exact hgap

/-- The linear-return rate with the auxiliary error tolerance and survival
bound chosen automatically.  Only the principal maximal-inequality error has
to be compared with the finite Gaussian products. -/
theorem exists_lowerRate_horizontalTubeProbability_of_linearReturn
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
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    (references : Finset ℝ) (hreferences : references.Nonempty)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin))
    (houterReference : ∀ y ∈ references,
      -a + coverMargin + endpointMargin +
            (blocks : ℝ) * blockRadius < y ∧
        y < 1 - a - coverMargin - endpointMargin -
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
    (hprincipal : ∀ y ∈ references,
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
  obtain ⟨error, herror, lowerBound, hlowerBound, hlowerBoundOne, hgap⟩ :=
    exists_error_lowerBound_gap_finset_gaussianProduct
      hconstant hendpointMargin hblocks references hreferences
      (fun y _ => -y / (blocks : ℝ)) hprincipal
  refine ⟨lowerBound, hlowerBound, hlowerBoundOne, ?_⟩
  exact mul_log_toReal_le_liminf_horizontalTubeProbability_of_linearReturn
    ν hν hscale hscalePos hconstant hblocks ha0 ha1 hreturnZero
    hendpointMargin hblockRadius herror references hcover hreference
    houterReference houterZero hreturnFinal lowerBound hlowerBound
    hlowerBoundOne hgap

end ProbabilityTheory.RandomWalk
