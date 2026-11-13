/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.Coupling.PopulationCloud
public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap

/-!
# Endpoint minima under spatial domination

## Public declarations

The declarations below are in namespace
`Combinatorics.Branching.Selection.Coupling`.

- `populationCloud_inf'_le_of_sliceDominatingMap`:
  if `hmap` injectively maps every object particle to a partner particle whose
  observed value is no larger, and `objectsToMatch.Nonempty`, then
  \[
  \min_{q\in availablePartners}\phi(\mathrm{partnerWalk.position}(d,q_1,q_2))
  \le \min_{p\in objectsToMatch}\phi(\mathrm{objectWalk.position}(d,p_1,p_2)).
  \]
- `populationCloud_object_ge_of_partner_ge_of_sliceDominatingMap`:
  under the same assumptions, for each `threshold : Value`,
  \[
  threshold\le\min_{q\in availablePartners}\phi(\mathrm{partnerWalk.position}(d,q_1,q_2))
  \;\Longrightarrow\;
  threshold\le\min_{p\in objectsToMatch}\phi(\mathrm{objectWalk.position}(d,p_1,p_2)).
  \]

A particle injection that sends every object particle to a particle no higher
in the partner population gives the corresponding order between the two finite endpoint
minima.  This is the pathwise order step used when comparing selected
populations through a coupling.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Mark Position Value : Type*}

/-- A spatially dominated finite availablePartners cloud has minimum observed value no
larger than the object minimum. -/
theorem populationCloud_inf'_le_of_sliceDominatingMap
    [AddCommMonoid Position] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (objectWalk partnerWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (objectsToMatch availablePartners : Finset (RootIndexed.TreeNode Root α))
    (hmap : Cloud.SliceDominatingMap φ
      (populationCloud d objectWalk objectsToMatch)
      (populationCloud d partnerWalk availablePartners) ())
    (hobjectsToMatch : objectsToMatch.Nonempty) :
    availablePartners.inf' (by
      obtain ⟨p, hp⟩ := hobjectsToMatch
      refine ⟨hmap p, ?_⟩
      have hp' : p ∈ (populationCloud d objectWalk objectsToMatch).particles () := by
        simpa [populationCloud] using hp
      have havailablePartners := hmap.mapsTo hp'
      simpa [populationCloud] using havailablePartners)
        (fun q => φ (partnerWalk.position d q.1 q.2)) ≤
      objectsToMatch.inf' hobjectsToMatch (fun p => φ (objectWalk.position d p.1 p.2)) := by
  classical
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image objectsToMatch
    (fun p => φ (objectWalk.position d p.1 p.2)) hobjectsToMatch
  have hp' : p ∈ (populationCloud d objectWalk objectsToMatch).particles () := by
    simpa [populationCloud] using hp
  have hpartnerMembership : hmap p ∈ availablePartners := by
    have h := hmap.mapsTo hp'
    simpa [populationCloud] using h
  have horderBound : φ (partnerWalk.position d (hmap p).1 (hmap p).2) ≤
      φ (objectWalk.position d p.1 p.2) := by
    simpa [populationCloud] using hmap.dominates p hp'
  have hpEq : objectsToMatch.inf' hobjectsToMatch
      (fun q => φ (objectWalk.position d q.1 q.2)) =
      φ (objectWalk.position d p.1 p.2) := by
    apply le_antisymm
    · rw [Finset.inf'_le_iff]
      exact ⟨p, hp, le_rfl⟩
    · rw [Finset.le_inf'_iff]
      intro q hq
      exact hpmin q hq
  rw [Finset.inf'_le_iff]
  refine ⟨hmap p, hpartnerMembership, ?_⟩
  rw [hpEq]
  exact horderBound

/-- A right-tail event for the availablePartners endpoint minimum implies the same
right-tail event for the objectsToMatch endpoint minimum under spatial domination. -/
theorem populationCloud_object_ge_of_partner_ge_of_sliceDominatingMap
    [AddCommMonoid Position] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (objectWalk partnerWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (objectsToMatch availablePartners : Finset (RootIndexed.TreeNode Root α))
    (hmap : Cloud.SliceDominatingMap φ
      (populationCloud d objectWalk objectsToMatch)
      (populationCloud d partnerWalk availablePartners) ())
    (hobjectsToMatch : objectsToMatch.Nonempty) (threshold : Value) :
    threshold ≤ availablePartners.inf' (by
      obtain ⟨p, hp⟩ := hobjectsToMatch
      refine ⟨hmap p, ?_⟩
      have hp' : p ∈ (populationCloud d objectWalk objectsToMatch).particles () := by
        simpa [populationCloud] using hp
      have havailablePartners := hmap.mapsTo hp'
      simpa [populationCloud] using havailablePartners)
        (fun q => φ (partnerWalk.position d q.1 q.2)) →
      threshold ≤ objectsToMatch.inf' hobjectsToMatch
        (fun p => φ (objectWalk.position d p.1 p.2)) := by
  intro havailablePartners
  exact havailablePartners.trans
    (populationCloud_inf'_le_of_sliceDominatingMap φ d objectWalk partnerWalk
      objectsToMatch availablePartners hmap hobjectsToMatch)

end Combinatorics.Branching.Selection.Coupling

end
