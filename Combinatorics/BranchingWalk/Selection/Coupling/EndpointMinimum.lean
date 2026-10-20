/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Combinatorics.BranchingWalk.Selection.Coupling.PopulationCloud
import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap

/-!
# Endpoint minima under spatial domination

A particle injection that sends every source particle to a particle no higher
in the target gives the corresponding order between the two finite endpoint
minima.  This is the pathwise order step used when comparing selected
populations through a coupling.
-/

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Mark Position Value : Type*}

/-- A spatially dominated finite target cloud has minimum observed value no
larger than the source minimum. -/
theorem populationCloud_inf'_le_of_sliceDominatingMap
    [AddCommMonoid Position] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (hmap : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ())
    (hsource : source.Nonempty) :
    target.inf' (by
      obtain ⟨p, hp⟩ := hsource
      refine ⟨hmap p, ?_⟩
      have hp' : p ∈ (populationCloud d sourceWalk source).particles () := by
        simpa [populationCloud] using hp
      have htarget := hmap.mapsTo hp'
      simpa [populationCloud] using htarget)
        (fun q => φ (targetWalk.position d q.1 q.2)) ≤
      source.inf' hsource (fun p => φ (sourceWalk.position d p.1 p.2)) := by
  classical
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image source
    (fun p => φ (sourceWalk.position d p.1 p.2)) hsource
  have hp' : p ∈ (populationCloud d sourceWalk source).particles () := by
    simpa [populationCloud] using hp
  have htgt : hmap p ∈ target := by
    have h := hmap.mapsTo hp'
    simpa [populationCloud] using h
  have hdom : φ (targetWalk.position d (hmap p).1 (hmap p).2) ≤
      φ (sourceWalk.position d p.1 p.2) := by
    simpa [populationCloud] using hmap.dominates p hp'
  have hpEq : source.inf' hsource
      (fun q => φ (sourceWalk.position d q.1 q.2)) =
      φ (sourceWalk.position d p.1 p.2) := by
    apply le_antisymm
    · rw [Finset.inf'_le_iff]
      exact ⟨p, hp, le_rfl⟩
    · rw [Finset.le_inf'_iff]
      intro q hq
      exact hpmin q hq
  rw [Finset.inf'_le_iff]
  refine ⟨hmap p, htgt, ?_⟩
  rw [hpEq]
  exact hdom

/-- Right-tail events are ordered in the same direction as the endpoint
minima: if the target minimum is at most the source minimum, a target value
above a threshold forces the source value above that threshold. -/
theorem source_ge_of_target_ge_of_minima_le
    {sourceMinimum targetMinimum threshold : Value}
    [Preorder Value]
    (hminimum : targetMinimum ≤ sourceMinimum)
    (htarget : threshold ≤ targetMinimum) :
    threshold ≤ sourceMinimum :=
  htarget.trans hminimum

/-- A right-tail event for the target endpoint minimum implies the same
right-tail event for the source endpoint minimum under spatial domination. -/
theorem populationCloud_source_ge_of_target_ge_of_sliceDominatingMap
    [AddCommMonoid Position] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (hmap : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ())
    (hsource : source.Nonempty) (threshold : Value) :
    threshold ≤ target.inf' (by
      obtain ⟨p, hp⟩ := hsource
      refine ⟨hmap p, ?_⟩
      have hp' : p ∈ (populationCloud d sourceWalk source).particles () := by
        simpa [populationCloud] using hp
      have htarget := hmap.mapsTo hp'
      simpa [populationCloud] using htarget)
        (fun q => φ (targetWalk.position d q.1 q.2)) →
      threshold ≤ source.inf' hsource
        (fun p => φ (sourceWalk.position d p.1 p.2)) := by
  exact source_ge_of_target_ge_of_minima_le
    (populationCloud_inf'_le_of_sliceDominatingMap φ d sourceWalk targetWalk
      source target hmap hsource)

end Combinatorics.Branching.Selection.Coupling
