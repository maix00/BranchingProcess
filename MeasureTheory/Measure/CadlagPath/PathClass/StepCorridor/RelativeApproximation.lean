/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Approximation

/-!
# Relative corridor approximations

An inner and outer corridor approximation may be valid only on a specified
subset of path space. The containment and energy-limit statements are
deterministic measure-theoretic data; probability-rate arguments consuming
them live in the probability layer.
-/

open Filter
open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- An `M₃` approximation of `G` relative to a path domain `D`. The inner and
outer set inclusions are required only after intersecting with `D`. -/
structure RelativeFiniteCorridorUnionApproximation (α : ℝ)
    (D G : Set (CadlagPath unitInterval ℝ)) where
  inner : ℕ → FiniteCorridorUnion α
  outer : ℕ → FiniteCorridorUnion α
  inner_subset : ∀ n, D ∩ (FiniteCorridorUnion.toSet (inner n)) ⊆ G
  subset_outer : ∀ n, G ⊆ D ∩ (FiniteCorridorUnion.toSet (outer n))
  energy_gap_tendsto_zero :
    Tendsto (fun n => FiniteCorridorUnion.realEnergy (inner n) -
      FiniteCorridorUnion.realEnergy (outer n)) atTop (nhds 0)

/-- Membership in the relative version of the source's class `M`. -/
def HasRelativeVanishingEnergyGapApproximation (α : ℝ)
    (D G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  Nonempty (RelativeFiniteCorridorUnionApproximation α D G)

/-- Convergent inner and outer energies for a relative approximation. -/
structure RelativeFiniteCorridorUnionEnergyLimits {α : ℝ}
    {D G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α D G) where
  innerLimit : ℝ
  outerLimit : ℝ
  inner_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.inner n))
    atTop (nhds innerLimit)
  outer_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.outer n))
    atTop (nhds outerLimit)

theorem RelativeFiniteCorridorUnionEnergyLimits.innerLimit_eq_outerLimit
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : h.innerLimit = h.outerLimit := by
  have hdiff : Tendsto
      (fun n => FiniteCorridorUnion.realEnergy (A.inner n) -
        FiniteCorridorUnion.realEnergy (A.outer n))
      atTop (nhds (h.innerLimit - h.outerLimit)) :=
    h.inner_tendsto.sub h.outer_tendsto
  have hzero := tendsto_nhds_unique hdiff A.energy_gap_tendsto_zero
  linarith

/-- The common energy limit of a relative approximation. -/
def RelativeFiniteCorridorUnionEnergyLimits.commonEnergy
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : ℝ := h.innerLimit

theorem RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_outerLimit
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : h.commonEnergy = h.outerLimit :=
  h.innerLimit_eq_outerLimit

/-- Cross-order of relative inner and outer energies, together with the
vanishing energy gap, gives a common energy limit. -/
noncomputable def RelativeFiniteCorridorUnionApproximation.energyLimits_of_crossOrder
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α D G)
    (hcross : ∀ n m, FiniteCorridorUnion.realEnergy (A.outer m) ≤
      FiniteCorridorUnion.realEnergy (A.inner n)) :
    RelativeFiniteCorridorUnionEnergyLimits A := by
  let innerCost : ℕ → ℝ := fun n => FiniteCorridorUnion.realEnergy (A.inner n)
  let outerCost : ℕ → ℝ := fun n => FiniteCorridorUnion.realEnergy (A.outer n)
  have hCauchy : CauchySeq innerCost := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (A.energy_gap_tendsto_zero.eventually (Iio_mem_nhds hε))
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hgap := hN n hn
      have hcrossnm : outerCost n ≤ innerCost m := hcross m n
      dsimp [innerCost, outerCost] at hgap hcrossnm
      linarith
    · have hgap := hN m hm
      have hcrossmn : outerCost m ≤ innerCost n := hcross n m
      dsimp [innerCost, outerCost] at hgap hcrossmn
      linarith
  classical
  let hExists : ∃ L, Tendsto innerCost atTop (nhds L) :=
    cauchySeq_tendsto_of_complete hCauchy
  refine ⟨hExists.choose, hExists.choose, ?_, ?_⟩
  · simpa [innerCost] using hExists.choose_spec
  · have houter := hExists.choose_spec.sub A.energy_gap_tendsto_zero
    have heq :
        (fun n => FiniteCorridorUnion.realEnergy (A.inner n) -
          (FiniteCorridorUnion.realEnergy (A.inner n) -
            FiniteCorridorUnion.realEnergy (A.outer n))) =
        fun n => FiniteCorridorUnion.realEnergy (A.outer n) := by
      funext n
      ring
    rw [heq] at houter
    simpa [outerCost] using houter

end Skorokhod.PathClass.StepCorridor

end
