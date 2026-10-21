/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Cloud.Order.DynamicSelection
public import Combinatorics.BranchingWalk.Selection.Coupling.PopulationCloud
public import Combinatorics.BranchingWalk.Selection.NSelection.Mechanism.Matching

/-!
# Population clouds for the multi-root spatial coupling

This file turns finite populations in root-indexed branching walks into
constant-time clouds and chooses the canonical equal-rank injection.

The public API consists of `population_card_le_of_injection`, which gives
`source.card ≤ target.card` from a spatially dominating injection of the
population clouds; `canonicalInjection`, which replaces any such witness by
the injection matching equal dynamic ranks; and `canonicalInjection_apply`,
which identifies that map pointwise with `matchByRankOrSelf`.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open Selection.NSelection

variable {Root α Mark Position Value : Type*}

theorem population_card_le_of_injection
    [AddCommMonoid Position]
    [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ()) :
    source.card ≤ target.card := by
  apply Finset.card_le_card_of_injOn prior
  · intro p hp
    simpa [populationCloud] using
      prior.mapsTo (by simpa [populationCloud] using hp)
  · intro p hp q hq hpq
    exact prior.injOn (by simpa [populationCloud] using hp)
      (by simpa [populationCloud] using hq) hpq

/-- Replace any finite spatial domination witness by the canonical
equal-dynamic-rank injection. -/
noncomputable def canonicalInjection
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ()) :
    Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) () := by
  classical
  have hcard := population_card_le_of_injection φ d sourceWalk targetWalk
    source target prior
  let sourceValue : RootIndexed.TreeNode Root α → Value :=
    fun p => φ (sourceWalk.position d p.1 p.2)
  let targetValue : RootIndexed.TreeNode Root α → Value :=
    fun q => φ (targetWalk.position d q.1 q.2)
  have hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card := by
    intro a
    simpa [sourceValue, targetValue, populationCloud] using
      Cloud.filter_card_le_of_injectivelyDominatesBy φ ()
        source.finite_toSet target.finite_toSet
        prior.injectivelyDominatesBy a
  let matchParticle : RootIndexed.TreeNode Root α →
      RootIndexed.TreeNode Root α :=
    matchByRankOrSelf sourceValue targetValue source target hcard
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ source := by simpa [populationCloud] using hp
    change matchParticle p ∈ target
    exact matchByRankOrSelf_mem sourceValue targetValue source target hcard hpr
  · intro p hp q hq hpq
    apply matchByRankOrSelf_injOn sourceValue targetValue source target hcard
    · simpa [populationCloud] using hp
    · simpa [populationCloud] using hq
    · exact hpq
  · intro p hp
    have hpr : p ∈ source := by simpa [populationCloud] using hp
    exact matchByRankOrSelf_value_le sourceValue targetValue source target
      hcard hthreshold hpr

@[simp] theorem canonicalInjection_apply
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (d : Mark → Position)
    (sourceWalk targetWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (source target : Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d sourceWalk source)
      (populationCloud d targetWalk target) ())
    (p : RootIndexed.TreeNode Root α) :
    canonicalInjection φ d sourceWalk targetWalk source target prior p =
      matchByRankOrSelf
        (fun q => φ (sourceWalk.position d q.1 q.2))
        (fun q => φ (targetWalk.position d q.1 q.2))
        source target
        (population_card_le_of_injection φ d sourceWalk targetWalk
          source target prior) p := by
  rfl


end Combinatorics.Branching.Selection.Coupling

end
