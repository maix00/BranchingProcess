/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointMoments
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointPositiveMomentClosure
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.CountableRoots

/-!
# Two-sided endpoint fourth moments on the common root forest

The positive and negative endpoint parts have separate estimates under the
paper's assumptions. This module combines them on the common countable-root
environment, which is the probability space used for the varying-
initial-population trajectory.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

private theorem fourth_eq_positive_fourth_add_negative_fourth (x : ℝ) :
    x ^ 4 = (max x 0) ^ 4 + (max (-x) 0) ^ 4 := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hneg : 0 ≤ -x := le_of_lt (neg_pos.mpr hx')
    calc
      x ^ 4 = (-x) ^ 4 := by ring
      _ = (max x 0) ^ 4 + (max (-x) 0) ^ 4 := by
        rw [max_eq_right hx'.le, max_eq_left hneg]
        simp

private theorem fourth_sub_le_eight_add_fourths (x c : ℝ) :
    (x - c) ^ 4 ≤ 8 * (x ^ 4 + c ^ 4) := by
  have habs (y : ℝ) : |y| ^ 4 = y ^ 4 := by
    rw [pow_abs]
    exact abs_of_nonneg (by positivity)
  have htriangle : |x - c| ≤ |x| + |c| := by
    apply abs_le.mpr
    constructor
    · calc
        -(|x| + |c|) = -|x| + -|c| := by ring
        _ ≤ x + -c := add_le_add
          (by simpa using neg_le_neg (neg_le_abs x))
          (by simpa using neg_le_neg (le_abs_self c))
        _ = x - c := by ring
    · calc
        x - c = x + -c := by ring
        _ ≤ |x| + |c| := add_le_add (le_abs_self x) (neg_le_abs c)
  calc
    (x - c) ^ 4 = |x - c| ^ 4 := by rw [habs]
    _ ≤ (|x| + |c|) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) htriangle 4
    _ ≤ 2 ^ (4 - 1) * (|x| ^ 4 + |c| ^ 4) :=
      add_pow_le (abs_nonneg x) (abs_nonneg c) 4
    _ = 8 * (x ^ 4 + c ^ 4) := by rw [habs x, habs c]; norm_num

/-- On the finite-root forest, the full endpoint fourth moment is the sum of
the separately controlled positive and negative fourth moments. -/
theorem finiteRootStepFieldLaw_integrable_pow_four_firstNSelectedEndpointMinimum
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L) :
    Integrable
      (fun field => (firstNSelectedEndpointMinimum m N H field) ^ 4)
      (finiteRootStepFieldLaw L.sortedPotentialImage m) ∧
    (∫ field, (firstNSelectedEndpointMinimum m N H field) ^ 4
      ∂finiteRootStepFieldLaw L.sortedPotentialImage m) ≤
        (H : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
            2048 * (1 + Real.log (m : ℝ) ^ 4) := by
  let P := finiteRootStepFieldLaw L.sortedPotentialImage m
  let endpoint : FiniteRootStepField m ℕ ℝ → ℝ :=
    firstNSelectedEndpointMinimum m N H
  have hboundarySorted := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptySorted : L.sortedPotentialImage nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hpos :=
    finiteRootStepFieldLaw_integrable_pow_four_max_firstNSelectedEndpointMinimum_pos
      m N H hm hN L hboundary hnonempty hfour
  have hneg :=
    finiteRootStepFieldLaw_integrable_pow_four_max_neg_firstNSelectedEndpointMinimum
      m N H hm hN L.sortedPotentialImage hboundarySorted hnonemptySorted
  have hdecomp (field : FiniteRootStepField m ℕ ℝ) :
      (endpoint field) ^ 4 = (max (endpoint field) 0) ^ 4 +
        (max (-(endpoint field)) 0) ^ 4 :=
    fourth_eq_positive_fourth_add_negative_fourth (endpoint field)
  have hint : Integrable (fun field => (endpoint field) ^ 4) P := by
    apply (hpos.1.add hneg.1).congr
    exact ae_of_all P fun field => (hdecomp field).symm
  have hintegral :
      (∫ field, (endpoint field) ^ 4 ∂P) =
        (∫ field, (max (endpoint field) 0) ^ 4 ∂P) +
          ∫ field, (max (-(endpoint field)) 0) ^ 4 ∂P := by
    calc
      (∫ field, (endpoint field) ^ 4 ∂P) =
          ∫ field, (max (endpoint field) 0) ^ 4 +
            (max (-(endpoint field)) 0) ^ 4 ∂P :=
        integral_congr_ae (ae_of_all P hdecomp)
      _ = (∫ field, (max (endpoint field) 0) ^ 4 ∂P) +
            ∫ field, (max (-(endpoint field)) 0) ^ 4 ∂P :=
        integral_add hpos.1 hneg.1
  refine ⟨?_, ?_⟩
  · simpa [P, endpoint] using hint
  · calc
      (∫ field, (endpoint field) ^ 4 ∂P) =
          (∫ field, (max (endpoint field) 0) ^ 4 ∂P) +
            ∫ field, (max (-(endpoint field)) 0) ^ 4 ∂P := hintegral
      _ ≤ (H : ℝ) ^ 4 *
            ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
              2048 * (1 + Real.log (m : ℝ) ^ 4) := add_le_add hpos.2 hneg.2

/-- The two-sided endpoint fourth-moment estimate on the common countable-root
environment. In addition to the moment bound it gives `MemLp` at exponent
four, so centered versions can be passed to the polynomial-tail `L²` closure. -/
theorem countableRootEndpointMinimum_memLp_four_and_integral_bound
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L) :
    MemLp (countableRootEndpointMinimum m N H)
        (4 : ℝ≥0∞) (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ∧
    (∫ field, (countableRootEndpointMinimum m N H field) ^ 4
      ∂RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ≤
        (H : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
            2048 * (1 + Real.log (m : ℝ) ^ 4) := by
  let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
  let Q := finiteRootStepFieldLaw L.sortedPotentialImage m
  let endpoint : FiniteRootStepField m ℕ ℝ → ℝ :=
    firstNSelectedEndpointMinimum m N H
  let countableEndpoint : CountableRootStepField ℕ ℝ → ℝ :=
    countableRootEndpointMinimum m N H
  have hfinite :=
    finiteRootStepFieldLaw_integrable_pow_four_firstNSelectedEndpointMinimum
      m N H hm hN L hboundary hnonempty hfour
  have hpreserving :=
    RootIndexed.StepField.measurePreserving_first L.sortedPotentialImage m
  have hintCountable : Integrable (fun field => (countableEndpoint field) ^ 4) P := by
    have hcomp := hpreserving.integrable_comp_of_integrable hfinite.1
    change Integrable
      (fun field => endpoint (RootIndexed.StepField.first m field) ^ 4) P at hcomp
    simpa [P, countableEndpoint, countableRootEndpointMinimum, endpoint] using hcomp
  have hmeas : Measurable countableEndpoint := by
    simpa [countableEndpoint, countableRootEndpointMinimum] using
      measurable_countableRootEndpointMinimum m N H
  have hnormInt : Integrable
      (fun field => ‖countableEndpoint field‖ ^ 4) P := by
    apply hintCountable.congr
    exact ae_of_all P fun field => by
      have hpow : |countableEndpoint field| ^ 4 =
          (countableEndpoint field) ^ 4 := by
        rw [pow_abs]
        exact abs_of_nonneg (by positivity)
      simpa [Real.norm_eq_abs] using hpow.symm
  have hnormInt' : Integrable
      (fun field => ‖countableEndpoint field‖ ^
        ENNReal.toReal (4 : ℝ≥0∞)) P := by
    simpa using hnormInt
  have hmem : MemLp countableEndpoint (4 : ℝ≥0∞) P :=
    (integrable_norm_rpow_iff hmeas.aestronglyMeasurable
      (by norm_num) (by norm_num)).1 hnormInt'
  have hintegral :=
    countableRootEndpointMinimum_integral_map_eq L.sortedPotentialImage m N H
      (fun x : ℝ => x ^ 4) (measurable_id.pow_const 4)
  have hbound :
      (∫ field, (countableEndpoint field) ^ 4 ∂P) ≤
        (H : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
            2048 * (1 + Real.log (m : ℝ) ^ 4) := by
    rw [show countableEndpoint = countableRootEndpointMinimum m N H by rfl]
    rw [hintegral]
    simpa [Q, endpoint] using hfinite.2
  exact ⟨by simpa [P, countableEndpoint] using hmem, hbound⟩

/-- Centering the endpoint by any fixed real constant preserves fourth
integrability. Its fourth moment is controlled by the uncentered endpoint
bound and the fourth power of the center. -/
theorem countableRootEndpointMinimum_sub_memLp_four_and_integral_bound
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L) (c : ℝ) :
    MemLp (fun field => countableRootEndpointMinimum m N H field - c)
        (4 : ℝ≥0∞) (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ∧
    (∫ field,
      (countableRootEndpointMinimum m N H field - c) ^ 4
        ∂RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ≤
      8 * ((H : ℝ) ^ 4 *
        ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
        2048 * (1 + Real.log (m : ℝ) ^ 4) + c ^ 4) := by
  let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
  let endpoint : CountableRootStepField ℕ ℝ → ℝ :=
    countableRootEndpointMinimum m N H
  have hraw := countableRootEndpointMinimum_memLp_four_and_integral_bound
    m N H hm hN L hboundary hnonempty hfour
  have hcenter : MemLp (fun field => endpoint field - c) (4 : ℝ≥0∞) P := by
    exact hraw.1.sub (memLp_const c)
  have hint : Integrable (fun field => (endpoint field - c) ^ 4) P := by
    have hnorm := hcenter.integrable_norm_pow (by norm_num : 4 ≠ 0)
    apply hnorm.congr
    exact ae_of_all P fun field => by
      have hpow : ‖endpoint field - c‖ ^ 4 = (endpoint field - c) ^ 4 := by
        rw [Real.norm_eq_abs, pow_abs]
        exact abs_of_nonneg (by positivity)
      exact hpow
  have hendpointInt : Integrable (fun field => endpoint field ^ 4) P := by
    have hnorm := hraw.1.integrable_norm_pow (by norm_num : 4 ≠ 0)
    apply hnorm.congr
    exact ae_of_all P fun field => by
      have hpow : ‖endpoint field‖ ^ 4 = endpoint field ^ 4 := by
        rw [Real.norm_eq_abs, pow_abs]
        exact abs_of_nonneg (by positivity)
      exact hpow
  have hdomInt : Integrable
      (fun field => 8 * (endpoint field ^ 4 + c ^ 4)) P := by
    exact (hendpointInt.add (integrable_const (c ^ 4 : ℝ))).const_mul 8
  have hpoint (field : CountableRootStepField ℕ ℝ) :
      (endpoint field - c) ^ 4 ≤ 8 * (endpoint field ^ 4 + c ^ 4) :=
    fourth_sub_le_eight_add_fourths (endpoint field) c
  have hcompare := integral_mono_ae hint hdomInt (ae_of_all P hpoint)
  have hbound := hraw.2
  refine ⟨by simpa [P, endpoint] using hcenter, ?_⟩
  calc
    (∫ field, (endpoint field - c) ^ 4 ∂P) ≤
        ∫ field, 8 * (endpoint field ^ 4 + c ^ 4) ∂P := hcompare
    _ = 8 * ((∫ field, endpoint field ^ 4 ∂P) + c ^ 4) := by
      rw [integral_const_mul, integral_add hendpointInt
        (integrable_const (c ^ 4 : ℝ))]
      simp
    _ ≤ 8 * ((H : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw +
          2048 * (1 + Real.log (m : ℝ) ^ 4) + c ^ 4) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
      linarith

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
