/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy

/-!
# Vanishing-energy-gap approximation of path sets

This file defines path sets that admit inner and outer approximations by finite
unions of step corridors, with the energy gap tending to zero. In §1 of A. A.
Mogul'skii, "Small deviations in the space of trajectories" (1974), this is
the class `M`; its energy is denoted `Hα`. The library names the approximation
property and the common energy limit by their roles. Convergence and
independence of the resulting limit are theorem obligations, not fields
silently added to the approximation property.
-/

open Filter

open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- An inner/outer finite-union corridor approximation with vanishing energy
gap. This is the approximation property denoted `M` in Mogul'skii's §1. -/
structure FiniteCorridorUnionApproximation (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) where
  /-- Inner finite-union corridors, one at each approximation scale. -/
  inner : ℕ → FiniteCorridorUnion α
  /-- Outer finite-union corridors, one at each approximation scale. -/
  outer : ℕ → FiniteCorridorUnion α
  /-- Each inner corridor is contained in the target path set. -/
  inner_subset : ∀ n, (FiniteCorridorUnion.toSet (inner n)) ⊆ G
  /-- The target path set is contained in each outer corridor. -/
  subset_outer : ∀ n, G ⊆ (FiniteCorridorUnion.toSet (outer n))
  /-- The gap between the inner and outer energies vanishes. -/
  energy_gap_tendsto_zero :
    Tendsto (fun n => (FiniteCorridorUnion.realEnergy (inner n)) - (FiniteCorridorUnion.realEnergy (outer n)))
      atTop (nhds 0)

/-- A path set admits a vanishing-energy-gap approximation. -/
def HasVanishingEnergyGapApproximation (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  Nonempty (FiniteCorridorUnionApproximation α G)

/-- A witness that the inner and outer energies converge. Their equality is
proved below from the vanishing energy gap. -/
structure FiniteCorridorUnionEnergyLimits {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    (A : FiniteCorridorUnionApproximation α G) where
  /-- Limit of the inner corridor energies. -/
  innerLimit : ℝ
  /-- Limit of the outer corridor energies. -/
  outerLimit : ℝ
  /-- Convergence of the inner corridor energies. -/
  inner_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.inner n)) atTop (nhds innerLimit)
  /-- Convergence of the outer corridor energies. -/
  outer_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.outer n)) atTop (nhds outerLimit)

theorem FiniteCorridorUnionEnergyLimits.innerLimit_eq_outerLimit
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : FiniteCorridorUnionApproximation α G} (h : FiniteCorridorUnionEnergyLimits A) :
    h.innerLimit = h.outerLimit := by
  have hdiff : Tendsto
      (fun n => FiniteCorridorUnion.realEnergy (A.inner n) - FiniteCorridorUnion.realEnergy (A.outer n))
      atTop (nhds (h.innerLimit - h.outerLimit)) :=
    h.inner_tendsto.sub h.outer_tendsto
  have hzero := tendsto_nhds_unique hdiff A.energy_gap_tendsto_zero
  linarith

/-- If the inner `M₃` energies converge, the source's vanishing energy-gap
condition forces the outer energies to converge to the same value. -/
def FiniteCorridorUnionEnergyLimits.ofInnerTendsto
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : FiniteCorridorUnionApproximation α G} {L : ℝ}
    (hinner : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.inner n)) atTop (nhds L)) :
    FiniteCorridorUnionEnergyLimits A := by
  refine ⟨L, L, hinner, ?_⟩
  have houter := hinner.sub A.energy_gap_tendsto_zero
  have heq :
      (fun n => FiniteCorridorUnion.realEnergy (A.inner n) -
        (FiniteCorridorUnion.realEnergy (A.inner n) - FiniteCorridorUnion.realEnergy (A.outer n))) =
      fun n => FiniteCorridorUnion.realEnergy (A.outer n) := by
    funext n
    ring
  rw [heq] at houter
  simpa using houter

/-- If the outer `M₃` energies converge, the source's vanishing energy-gap
condition forces the inner energies to converge to the same value. -/
def FiniteCorridorUnionEnergyLimits.ofOuterTendsto
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : FiniteCorridorUnionApproximation α G} {L : ℝ}
    (houter : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.outer n)) atTop (nhds L)) :
    FiniteCorridorUnionEnergyLimits A := by
  refine ⟨L, L, ?_, houter⟩
  have hinner := houter.add A.energy_gap_tendsto_zero
  have heq :
      (fun n => FiniteCorridorUnion.realEnergy (A.outer n) +
        (FiniteCorridorUnion.realEnergy (A.inner n) - FiniteCorridorUnion.realEnergy (A.outer n))) =
      fun n => FiniteCorridorUnion.realEnergy (A.inner n) := by
    funext n
    ring
  rw [heq] at hinner
  simpa using hinner

/-- The candidate value of `Hα` supplied by a convergent inner/outer
approximation. Independence from the chosen approximation is established by
`existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation` in the path-class rate layer. -/
def FiniteCorridorUnionEnergyLimits.commonEnergy
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : FiniteCorridorUnionApproximation α G} (h : FiniteCorridorUnionEnergyLimits A) : ℝ :=
  h.innerLimit

theorem FiniteCorridorUnionEnergyLimits.commonEnergy_eq_outerLimit
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : FiniteCorridorUnionApproximation α G} (h : FiniteCorridorUnionEnergyLimits A) :
    h.commonEnergy = h.outerLimit := by
  exact h.innerLimit_eq_outerLimit

end Skorokhod.PathClass.StepCorridor
