/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Energy

/-!
# The `M` approximation class

The source defines `M` by inner and outer sequences from `M₃`, with the path
set sandwiched between them and the difference of their energies tending to
zero.  This file formalizes that definition separately from the additional
claim that the two energy sequences have limits.  Existence and independence
of the resulting `Hα` limit are theorem obligations, not fields silently
added to membership in `M`.
-/

open Filter

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- An inner/outer `M₃` approximation of a path set, with the vanishing energy
gap required in the source's definition of class `M`. -/
structure M3Approximation (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) where
  inner : ℕ → M3 α
  outer : ℕ → M3 α
  inner_subset : ∀ n, (M3.toSet (inner n)) ⊆ G
  subset_outer : ∀ n, G ⊆ (M3.toSet (outer n))
  energy_gap_tendsto_zero :
    Tendsto (fun n => (M3.hAlpha (inner n)) - (M3.hAlpha (outer n)))
      atTop (nhds 0)

/-- Membership in the source's approximation class `M`. -/
def IsM (α : ℝ) (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  Nonempty (M3Approximation α G)

/-- A witness that the inner and outer `M₃` energies of a fixed approximation
have limits.  The source's theorem states these limits agree; that equality is
proved below from the vanishing energy gap. -/
structure M3EnergyLimits {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    (A : M3Approximation α G) where
  innerLimit : ℝ
  outerLimit : ℝ
  inner_tendsto : Tendsto (fun n => M3.hAlpha (A.inner n)) atTop (nhds innerLimit)
  outer_tendsto : Tendsto (fun n => M3.hAlpha (A.outer n)) atTop (nhds outerLimit)

theorem M3EnergyLimits.innerLimit_eq_outerLimit
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : M3Approximation α G} (h : M3EnergyLimits A) :
    h.innerLimit = h.outerLimit := by
  have hdiff : Tendsto
      (fun n => M3.hAlpha (A.inner n) - M3.hAlpha (A.outer n))
      atTop (nhds (h.innerLimit - h.outerLimit)) :=
    h.inner_tendsto.sub h.outer_tendsto
  have hzero := tendsto_nhds_unique hdiff A.energy_gap_tendsto_zero
  linarith

/-- If the inner `M₃` energies converge, the source's vanishing energy-gap
condition forces the outer energies to converge to the same value. -/
def M3EnergyLimits.ofInnerTendsto
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : M3Approximation α G} {L : ℝ}
    (hinner : Tendsto (fun n => M3.hAlpha (A.inner n)) atTop (nhds L)) :
    M3EnergyLimits A := by
  refine ⟨L, L, hinner, ?_⟩
  have houter := hinner.sub A.energy_gap_tendsto_zero
  have heq :
      (fun n => M3.hAlpha (A.inner n) -
        (M3.hAlpha (A.inner n) - M3.hAlpha (A.outer n))) =
      fun n => M3.hAlpha (A.outer n) := by
    funext n
    ring
  rw [heq] at houter
  simpa using houter

/-- If the outer `M₃` energies converge, the source's vanishing energy-gap
condition forces the inner energies to converge to the same value. -/
def M3EnergyLimits.ofOuterTendsto
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : M3Approximation α G} {L : ℝ}
    (houter : Tendsto (fun n => M3.hAlpha (A.outer n)) atTop (nhds L)) :
    M3EnergyLimits A := by
  refine ⟨L, L, ?_, houter⟩
  have hinner := houter.add A.energy_gap_tendsto_zero
  have heq :
      (fun n => M3.hAlpha (A.outer n) +
        (M3.hAlpha (A.inner n) - M3.hAlpha (A.outer n))) =
      fun n => M3.hAlpha (A.inner n) := by
    funext n
    ring
  rw [heq] at hinner
  simpa using hinner

/-- The candidate value of `Hα` supplied by a convergent inner/outer
approximation.  Independence from the chosen approximation is a separate
well-definedness theorem still required for the full statement. -/
def M3EnergyLimits.hAlpha
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : M3Approximation α G} (h : M3EnergyLimits A) : ℝ :=
  h.innerLimit

theorem M3EnergyLimits.hAlpha_eq_outerLimit
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    {A : M3Approximation α G} (h : M3EnergyLimits A) :
    h.hAlpha = h.outerLimit := by
  exact h.innerLimit_eq_outerLimit

end ProbabilityTheory.RandomWalk.Mogulskii
