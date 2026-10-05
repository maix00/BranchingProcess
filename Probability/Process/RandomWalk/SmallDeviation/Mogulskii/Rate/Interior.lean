/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.FinitePartition
public import Probability.Distributions.Gaussian.Interval
public import Analysis.Asymptotics.Tolerance

/-!
# Mogulskii lower rate for a strict interior horizontal tube

This file chooses a three-point return cover and discharges the geometric
hypotheses of the finite-partition lower bound.  The remaining hypothesis is
the genuinely analytic comparison between the maximal-inequality error and
the finite Gaussian products.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- With the block constant scaled quadratically in the return radius, the
three standardized Gaussian products are fixed.  Hence the quadratic
maximal-inequality error can be made strictly smaller than all three. -/
theorem exists_returnMargin_principal_gaussianProduct
    {endpointMargin upper : ℝ} (_hendpointMargin : 0 < endpointMargin)
    (hupper : 0 < upper) {blocks : ℕ} (hblocks : 0 < blocks) :
    ∃ returnMargin : ℝ, 0 < returnMargin ∧ returnMargin < upper ∧
      ∀ y ∈ ({-2 * returnMargin, 0, 2 * returnMargin} : Finset ℝ),
        ENNReal.ofReal
            (blocks * (returnMargin ^ 2 / endpointMargin ^ 2)) <
          ∏ _j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                (((-y / (blocks : ℝ)) -
                    returnMargin / (blocks : ℝ)) /
                  Real.sqrt (returnMargin ^ 2))
                (((-y / (blocks : ℝ)) +
                    returnMargin / (blocks : ℝ)) /
                  Real.sqrt (returnMargin ^ 2))) := by
  let product : ℝ → ENNReal := fun center =>
    ∏ _j : Fin blocks,
      gaussianReal 0 1
        (Set.Ioo
          ((-center / (blocks : ℝ)) - 1 / (blocks : ℝ))
          ((-center / (blocks : ℝ)) + 1 / (blocks : ℝ)))
  let probability : ENNReal :=
    min (product (-2)) (min (product 0) (product 2))
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hproductPos : ∀ center : ℝ, 0 < product center := by
    intro center
    dsimp [product]
    rw [pos_iff_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact (gaussianReal_Ioo_pos (μ := 0) (v := 1) (by norm_num) (by
      have : 0 < 1 / (blocks : ℝ) := one_div_pos.mpr hblocksReal
      linarith)).ne'
  have hprobability : 0 < probability := by
    simp only [probability, lt_min_iff]
    exact ⟨hproductPos (-2), hproductPos 0, hproductPos 2⟩
  obtain ⟨returnMargin, hreturnMargin, hreturnUpper, herror⟩ :=
    _root_.Asymptotics.exists_pos_lt_ofReal_mul_sq_div_lt
      (coefficient := blocks) (denominator := endpointMargin)
      hprobability hupper
  refine ⟨returnMargin, hreturnMargin, hreturnUpper, ?_⟩
  intro y hy
  have hsqrt : Real.sqrt (returnMargin ^ 2) = returnMargin := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hreturnMargin]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · convert herror.trans_le (min_le_left _ _) using 1
    dsimp [product]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2 <;> rw [hsqrt] <;>
      field_simp [hreturnMargin.ne', hblocksReal.ne']
  · convert herror.trans_le
      ((min_le_right _ _).trans (min_le_left _ _)) using 1
    dsimp [product]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2 <;> rw [hsqrt] <;>
      field_simp [hreturnMargin.ne', hblocksReal.ne'] <;> ring
  · convert herror.trans_le
      ((min_le_right _ _).trans (min_le_right _ _)) using 1
    dsimp [product]
    apply Finset.prod_congr rfl
    intro j hj
    congr 2 <;> rw [hsqrt] <;>
      field_simp [hreturnMargin.ne', hblocksReal.ne']

/-- For a horizontal tube whose zero starting point lies strictly inside,
three reference points suffice to implement the return-block geometry. -/
theorem exists_lowerRate_horizontalTubeProbability_of_strictInterior_parameters
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnMargin endpointMargin : ℝ}
    (hreturnMargin : 0 < returnMargin)
    (hendpointMargin : 0 < endpointMargin)
    (hleft : endpointMargin + 4 * returnMargin < a)
    (hright : endpointMargin + 4 * returnMargin < 1 - a)
    (hprincipal : ∀ y ∈
        ({-2 * returnMargin, 0, 2 * returnMargin} : Finset ℝ),
      ENNReal.ofReal (blocks * (constant / endpointMargin ^ 2)) <
        ∏ _j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              (((-y / (blocks : ℝ)) - returnMargin / (blocks : ℝ)) /
                Real.sqrt constant)
              (((-y / (blocks : ℝ)) + returnMargin / (blocks : ℝ)) /
                Real.sqrt constant))) :
    ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
      (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
        atTop.liminf (fun n =>
          scale n ^ 2 / (n : ℝ) *
            Real.log (horizontalTubeProbability
              (independentIncrementLaw ν) a (scale n) n).toReal) := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  let references : Finset ℝ :=
    {-2 * returnMargin, 0, 2 * returnMargin}
  apply exists_lowerRate_horizontalTubeProbability_of_linearReturn
    ν hν hscale hscalePos hconstant hblocks ha0 ha1
    (returnLower := -3 * returnMargin)
    (returnUpper := 3 * returnMargin)
    (coverMargin := returnMargin) (endpointMargin := endpointMargin)
    (blockRadius := returnMargin / (blocks : ℝ))
    (references := references)
  · constructor <;> linarith
  · exact hendpointMargin
  · exact div_pos hreturnMargin hblocksReal
  · simp [references]
  · intro x hx
    rcases le_total x (-returnMargin) with hxLeft | hxLeft
    · refine ⟨-2 * returnMargin, by simp [references], ?_⟩
      rw [abs_le]
      constructor <;> linarith [hx.1]
    · rcases le_total returnMargin x with hxRight | hxRight
      · refine ⟨2 * returnMargin, by simp [references], ?_⟩
        rw [abs_le]
        constructor <;> linarith [hx.2]
      · refine ⟨0, by simp [references], ?_⟩
        rw [abs_le]
        constructor <;> linarith
  · intro y hy
    simp only [references, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> constructor <;> linarith
  · intro y hy
    simp only [references, Finset.mem_insert, Finset.mem_singleton] at hy
    have hradius : (blocks : ℝ) *
        (returnMargin / (blocks : ℝ)) = returnMargin := by
      field_simp [hblocksReal.ne']
    rcases hy with rfl | rfl | rfl <;> rw [hradius] <;>
      constructor <;> linarith
  · have hradius : (blocks : ℝ) *
        (returnMargin / (blocks : ℝ)) = returnMargin := by
      field_simp [hblocksReal.ne']
    rw [hradius]
    constructor <;> linarith
  · have hradius : (blocks : ℝ) *
        (returnMargin / (blocks : ℝ)) = returnMargin := by
      field_simp [hblocksReal.ne']
    rw [hradius]
    constructor <;> linarith
  · simpa [references] using hprincipal

/-- Every horizontal tube containing the starting point in its strict
interior has a finite logarithmic lower rate.  The return radius and its
quadratically scaled block constant are chosen internally, so no numerical
Gaussian-product condition remains in the public statement. -/
theorem exists_lowerRate_horizontalTubeProbability_of_strictInterior
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧ lowerBound ≤ 1 ∧
        (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
          atTop.liminf (fun n =>
            scale n ^ 2 / (n : ℝ) *
              Real.log (horizontalTubeProbability
                (independentIncrementLaw ν) a (scale n) n).toReal) := by
  let interior : ℝ := min a (1 - a)
  have hinterior : 0 < interior := by
    rw [show interior = min a (1 - a) by rfl, lt_min_iff]
    exact ⟨ha, sub_pos.mpr haOne⟩
  let endpointMargin : ℝ := interior / 2
  have hendpointMargin : 0 < endpointMargin := by
    exact div_pos hinterior (by norm_num)
  obtain ⟨returnMargin, hreturnMargin, hreturnUpper, hprincipal⟩ :=
    exists_returnMargin_principal_gaussianProduct
      hendpointMargin (show 0 < interior / 16 by positivity) hblocks
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
    exists_lowerRate_horizontalTubeProbability_of_strictInterior_parameters
      ν hν hscale hscalePos (sq_pos_of_pos hreturnMargin) hblocks
      hreturnMargin hendpointMargin hleft hright hprincipal

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
