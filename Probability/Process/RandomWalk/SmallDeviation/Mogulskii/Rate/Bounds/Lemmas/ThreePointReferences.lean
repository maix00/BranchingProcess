/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Order.LiminfLimsup
import Probability.Distributions.Moments.Real
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Probability.Distributions.Gaussian.Interval
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Partition.Finite
/-!
# Strict-interior return-margin construction

## Internal proof declarations

- `exists_pos_lt_ofReal_quadratic_error`: a positive finite-measure mass admits a small radius whose quadratic error is below that mass.
- `exists_returnMargin_principal_gaussianProduct`: choose one positive return radius so the maximal-inequality error is below each of the three Gaussian return products.
- `exists_lowerRate_horizontalTubeProbability_of_threePointReferences`: assemble the three-point return cover into a strict-interior horizontal-tube logarithmic lower rate.


These declarations form a one-use proof stage for `StrictInterior.lean` in
the strict horizontal-tube lower-rate argument of A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

lemma exists_pos_lt_ofReal_quadratic_error
    {coefficient denominator : ℝ} {probability : ENNReal}
    (hprobability : 0 < probability) {upper : ℝ} (hupper : 0 < upper) :
    ∃ radius : ℝ, 0 < radius ∧ radius < upper ∧
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability := by
  have hreal : Tendsto
      (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto
        (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
        (𝓝 0) (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => coefficient)
          (𝓝 0) (𝓝 coefficient)).mul
          (((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2).div_const
            (denominator ^ 2))
    exact hfull.mono_left inf_le_left
  have hennreal : Tendsto
      (fun radius : ℝ =>
        ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hsmall : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability :=
    (tendsto_order.1 hennreal).2 _ hprobability
  have hinterval : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      radius ∈ Ioo 0 upper := Ioo_mem_nhdsGT hupper
  obtain ⟨radius, hradius, herror⟩ := (hinterval.and hsmall).exists
  exact ⟨radius, hradius.1, hradius.2, herror⟩


/-- With the block constant scaled quadratically in the return radius, the
three standardized Gaussian products are fixed.  Hence the quadratic
maximal-inequality error can be made strictly smaller than all three. -/
lemma exists_returnMargin_principal_gaussianProduct
    {endpointMargin upper : ℝ} (hupper : 0 < upper)
    {blocks : ℕ} (hblocks : 0 < blocks) :
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
    exists_pos_lt_ofReal_quadratic_error
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
lemma exists_lowerRate_horizontalTubeProbability_of_threePointReferences
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
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
              (iidSequenceLaw ν) a (scale n) n).toReal) := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 := by linarith
  let references : Finset ℝ :=
    {-2 * returnMargin, 0, 2 * returnMargin}
  apply exists_lowerRate_horizontalTubeProbability_of_linearReturn
    ν hν hscale hconstant hblocks ha0 ha1
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
