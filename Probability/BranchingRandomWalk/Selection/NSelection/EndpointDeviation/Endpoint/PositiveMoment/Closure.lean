/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Lineage
/-!
# Positive fourth moment of the selected endpoint

The endpoint-minimizing address has a predictable fresh slot-zero increment.
Its one-step comparison and the zero initial endpoint imply that the positive
endpoint is bounded by the sum of these nonnegative increments. The existing
fourth-moment estimate for predictable increments then gives the endpoint
fourth-moment bound.
-/


open MeasureTheory

set_option maxHeartbeats 1000000

section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

/-- A scalar sequence with zero initial value and nonnegative one-step
increments is bounded above, after taking positive part, by the cumulative
sum of those increments. -/
private theorem max_iterate_le_range_sum
    (f y : ℕ → ℝ)
    (hzero : f 0 = 0)
    (hstep : ∀ k, f (k + 1) ≤ f k + y k)
    (hy : ∀ k, 0 ≤ y k) :
    ∀ n, max (f n) 0 ≤ ∑ k ∈ Finset.range n, y k := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      have hsumNonneg : 0 ≤ ∑ k ∈ Finset.range n, y k := by
        apply Finset.sum_nonneg
        intro k hk
        exact hy k
      have hnext :
          f (n + 1) ≤ (∑ k ∈ Finset.range n, y k) + y n := by
        calc
          f (n + 1) ≤ f n + y n := hstep n
          _ ≤ (∑ k ∈ Finset.range n, y k) + y n := by
            linarith [le_trans (le_max_left (f n) 0) ih]
      calc
        max (f (n + 1)) 0 ≤
            (∑ k ∈ Finset.range n, y k) + y n :=
          max_le hnext (add_nonneg hsumNonneg (hy n))
        _ = ∑ k ∈ Finset.range (n + 1), y k := by
          rw [Finset.sum_range_succ]

/-- The selected population starts at the roots, all at position zero, so
its endpoint minimum at generation zero is exactly zero. -/
theorem firstNSelectedEndpointMinimum_zero_eq
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    firstNSelectedEndpointMinimum m N 0 field = 0 := by
  classical
  let roots : Finset (Fin m) := Finset.univ
  have hpopulation : firstNSelectedPopulation m N 0 field =
      RootIndexed.initialPopulation roots := by
    simp [firstNSelectedPopulation, roots,
      RootIndexed.selectedPopulationTotalized]
  have hnonempty : (firstNSelectedPopulation m N 0 field).Nonempty := by
    rw [hpopulation]
    apply Finset.card_pos.mp
    rw [RootIndexed.initialPopulation_card]
    simpa [roots] using hm
  rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
    m N 0 field hnonempty]
  apply le_antisymm
  · rw [Finset.inf'_le_iff]
    refine ⟨((⟨0, hm⟩ : Fin m), []), ?_, ?_⟩
    · rw [hpopulation]
      exact RootIndexed.mem_initialPopulation_iff.mpr
        ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩
    · simp [RootIndexed.position]
  · rw [Finset.le_inf'_iff]
    intro p hp
    rw [hpopulation] at hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, hr, rfl⟩
    simp [RootIndexed.position]

/-- The positive part of the selected endpoint has a finite-root fourth
moment bounded by `n^4` times the leftmost positive-step fourth
moment. The only probabilistic assumptions are the left boundary
normalization, nonempty offspring, and leftmost fourth moment. -/
theorem finiteRootStepFieldLaw_integrable_pow_four_max_firstNSelectedEndpointMinimum_pos
    (m N n : ℕ) (hm : 0 < m) (hN : 0 < N)
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L) :
    Integrable (fun field =>
      (max (firstNSelectedEndpointMinimum m N n field) 0) ^ 4)
        (finiteRootStepFieldLaw L.sortedPotentialImage m) ∧
      (∫ field,
        (max (firstNSelectedEndpointMinimum m N n field) 0) ^ 4
        ∂finiteRootStepFieldLaw L.sortedPotentialImage m) ≤
        (n : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw := by
  classical
  let P := finiteRootStepFieldLaw L.sortedPotentialImage m
  let increment : ℕ → FiniteRootStepField m ℕ ℝ → ℝ := fun k field =>
    max (value' (field
      (firstNSelectedEndpointMinAddressAtDepth m N k hm field).1
      (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2) 0) 0
  let endpoint : ℕ → FiniteRootStepField m ℕ ℝ → ℝ := fun k field =>
    firstNSelectedEndpointMinimum m N k field

  have hsum :=
    finiteRootStepFieldLaw_integral_pow_four_sum_endpointMinAddressPositiveSlotZero_le
      m n N hm L hfour
  have hstep :=
    finiteRootStepFieldLaw_endpointMinimum_succ_le_predictablePositiveSlotZero_ae
      m N hm hN L hboundary hnonempty
  have hzero : ∀ field, endpoint 0 field = 0 := by
    intro field
    exact firstNSelectedEndpointMinimum_zero_eq m N hm field
  have hstep' : ∀ᵐ field ∂P, ∀ k,
      endpoint (k + 1) field ≤ endpoint k field + increment k field := by
    simpa [P, endpoint, increment] using hstep
  have hincrementNonneg (field : FiniteRootStepField m ℕ ℝ) (k : ℕ) :
      0 ≤ increment k field := by
    exact le_max_right _ _
  have hdom : ∀ᵐ field ∂P, ∀ k,
      max (endpoint k field) 0 ≤
        ∑ j ∈ Finset.range k, increment j field := by
    filter_upwards [hstep'] with field hstep'
    intro k
    exact max_iterate_le_range_sum
      (fun k => endpoint k field) (fun k => increment k field)
      (hzero field) hstep' (hincrementNonneg field) k

  have hpoint : ∀ᵐ field ∂P,
      (max (endpoint n field) 0) ^ 4 ≤
        (∑ k ∈ Finset.range n, increment k field) ^ 4 := by
    filter_upwards [hdom] with field hdom
    exact pow_le_pow_left₀ (le_max_right _ _) (hdom n) 4

  have hendpointMeas : Measurable
      (fun field => max (endpoint n field) 0) := by
    exact (measurable_firstNSelectedEndpointMinimum m N n).max
      measurable_const
  have hendpointIntegrable : Integrable
      (fun field => (max (endpoint n field) 0) ^ 4) P := by
    apply hsum.1.mono' (hendpointMeas.pow_const 4).aestronglyMeasurable
    filter_upwards [hpoint] with field hfield
    calc
      ‖(max (endpoint n field) 0) ^ 4‖ =
          (max (endpoint n field) 0) ^ 4 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (∑ k ∈ Finset.range n, increment k field) ^ 4 := hfield
      _ ≤ (∑ k ∈ Finset.range n,
          max (value' (field
            (firstNSelectedEndpointMinAddressAtDepth m N k hm field).1
            (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2) 0) 0) ^ 4 := by
            simp [increment]

  have hIntegralCompare :
      (∫ field, (max (endpoint n field) 0) ^ 4 ∂P) ≤
        ∫ field, (∑ k ∈ Finset.range n, increment k field) ^ 4 ∂P :=
    integral_mono_ae hendpointIntegrable hsum.1 hpoint
  refine ⟨?_, ?_⟩
  · simpa [P, endpoint] using hendpointIntegrable
  · calc
      (∫ field, (max (endpoint n field) 0) ^ 4 ∂P) ≤
          ∫ field, (∑ k ∈ Finset.range n, increment k field) ^ 4 ∂P :=
        hIntegralCompare
      _ ≤ (n : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw := by
        simpa [P, increment] using hsum.2

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
