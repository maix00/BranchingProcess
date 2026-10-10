/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.Tail.Endpoint
import Probability.BranchingRandomWalk.Selection.Tail.Nonempty

/-!
# Measurable endpoint minimum

The minimum endpoint of the totalized first-`N` selected population is
defined to be zero when that population is empty. Under the branching
assumptions used for the speed theorem, emptiness has probability zero, so
this totalization agrees almost surely with the ordinary finite-population
minimum.
-/

open MeasureTheory

section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

/-- The minimum endpoint among the generation-`H` first-`N` selected
population. The value on an empty population is set to zero. -/
noncomputable def firstNSelectedEndpointMinimum (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) : ℝ := by
  classical
  let population := firstNSelectedPopulation m N H field
  exact if h : population.Nonempty then
    population.inf' h (fun p =>
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2)
  else 0

theorem firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
    (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hpopulation : (firstNSelectedPopulation m N H field).Nonempty) :
    firstNSelectedEndpointMinimum m N H field =
      (firstNSelectedPopulation m N H field).inf' hpopulation
        (fun p => RootIndexed.position (fun _ : Fin m => (0 : ℝ))
          id field p.1 p.2) := by
  classical
  simp [firstNSelectedEndpointMinimum, hpopulation]

theorem firstNSelectedEndpointMinimum_le_iff
    (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) (x : ℝ) :
    firstNSelectedEndpointMinimum m N H field ≤ x ↔
      field ∈ firstNSelectedEndpointBelow m N H x ∨
        (¬ (firstNSelectedPopulation m N H field).Nonempty ∧ 0 ≤ x) := by
  classical
  unfold firstNSelectedEndpointMinimum
  dsimp only
  by_cases h : (firstNSelectedPopulation m N H field).Nonempty
  · rw [dif_pos h, Finset.inf'_le_iff]
    constructor
    · intro hmin
      exact Or.inl (by simpa [firstNSelectedEndpointBelow] using hmin)
    · intro hbelow
      rcases hbelow with hbelow | ⟨hfalse, _⟩
      · simpa [firstNSelectedEndpointBelow] using hbelow
      · exact False.elim (hfalse h)
  · rw [dif_neg h]
    constructor
    · intro hx
      exact Or.inr ⟨h, hx⟩
    · intro hx
      rcases hx with hbelow | ⟨_, hx⟩
      · simp only [firstNSelectedEndpointBelow] at hbelow
        rcases hbelow with ⟨p, hp, _⟩
        exact (h ⟨p, hp⟩).elim
      · exact hx

theorem measurable_firstNSelectedEndpointMinimum
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable (firstNSelectedEndpointMinimum m N H) := by
  classical
  apply measurable_of_Iic
  intro x
  rw [show (firstNSelectedEndpointMinimum m N H) ⁻¹' Set.Iic x =
      firstNSelectedEndpointBelow m N H x ∪
        (if 0 ≤ x then
          {field : FiniteRootStepField m ℕ ℝ |
            ¬ (firstNSelectedPopulation m N H field).Nonempty}
        else ∅) by
    ext field
    rw [Set.mem_preimage, Set.mem_Iic]
    have hiff := firstNSelectedEndpointMinimum_le_iff m N H field x
    rw [hiff]
    by_cases hx : 0 ≤ x <;> simp [hx]]
  have hbelow : MeasurableSet (firstNSelectedEndpointBelow m N H x) :=
    measurableSet_firstNSelectedEndpointBelow m N H x
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    apply hbelow.union
    have hpopulation : Measurable (firstNSelectedPopulation m N H) :=
      firstNSelectedPopulation_measurable m N H
    have hempty : MeasurableSet
        {field : FiniteRootStepField m ℕ ℝ |
          ¬ (firstNSelectedPopulation m N H field).Nonempty} := by
      rw [show {field : FiniteRootStepField m ℕ ℝ |
          ¬ (firstNSelectedPopulation m N H field).Nonempty} =
          {field | firstNSelectedPopulation m N H field = ∅} by
        ext field
        simp [Finset.not_nonempty_iff_eq_empty]]
      exact hpopulation (measurableSet_singleton (∅ : Finset
        (RootIndexed.TreeNode (Fin m) ℕ)))
    exact hempty
  · rw [if_neg hx]
    exact hbelow.union MeasurableSet.empty

theorem firstNSelectedEndpointMinimum_eq_population_inf'_ae
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∃ hpopulation : (firstNSelectedPopulation m N H field).Nonempty,
        firstNSelectedEndpointMinimum m N H field =
          (firstNSelectedPopulation m N H field).inf' hpopulation
            (fun p => RootIndexed.position (fun _ : Fin m => (0 : ℝ))
              id field p.1 p.2) := by
  letI : DecidableEq (RootIndexed.TreeNode (Fin m) ℕ) := instDecidableEqProd
  filter_upwards [finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    m N hm hN μ hboundary hnonempty] with field hpopulation
  have hpopulation' : (firstNSelectedPopulation m N H field).Nonempty := by
    simpa [firstNSelectedPopulation] using hpopulation H
  exact ⟨hpopulation',
    firstNSelectedEndpointMinimum_eq_inf'_of_nonempty m N H field
      hpopulation'⟩

theorem firstNSelectedEndpointMinimum_le_iff_endpointBelow_ae
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) (x : ℝ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      (field ∈ firstNSelectedEndpointBelow m N H x ↔
        firstNSelectedEndpointMinimum m N H field ≤ x) := by
  letI : DecidableEq (RootIndexed.TreeNode (Fin m) ℕ) := instDecidableEqProd
  filter_upwards [finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    m N hm hN μ hboundary hnonempty] with field hpopulation
  have hpopulation' : (firstNSelectedPopulation m N H field).Nonempty := by
    simpa [firstNSelectedPopulation] using hpopulation H
  rw [firstNSelectedEndpointMinimum_le_iff]
  simp [hpopulation']

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail

end
