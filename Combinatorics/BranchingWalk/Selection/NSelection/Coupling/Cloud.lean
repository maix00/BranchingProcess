/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap
public import Combinatorics.BranchingWalk.Selection.Coupling.PopulationCloud
public import Combinatorics.Selection.NSelection.Matching.ByRank

/-!
# Population clouds for the multi-root spatial coupling

## Public declarations

An injective spatially dominating map between finite population clouds implies
the corresponding cardinality inequality. Matching equal dynamic ranks gives
a canonical witness:

\[
\iota:C\hookrightarrow D,\quad
\phi(\operatorname{position}_D(\iota(p)))
 \le\phi(\operatorname{position}_C(p))
\Longrightarrow |C|\le|D|,
\qquad
\iota_{\mathrm{rank}}(p)=\operatorname{matchByRankOrSelf}(p).
\]

This file turns finite populations in root-indexed branching walks into
constant-time clouds and chooses the canonical equal-rank injection.

The public API consists of `population_card_le_of_injection`, which gives
`selectedBranchingWalkPopulation.card ≤ nSelectedBranchingWalkPopulation.card`
from a spatially dominating injection of the corresponding population clouds;
`canonicalInjection`, which replaces any such witness by the injection
matching equal dynamic ranks; and `canonicalInjection_apply`, which identifies
that map pointwise with `matchByRankOrSelf`.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

variable {Root α Mark Position OrderKey : Type*}

theorem population_card_le_of_injection
    [AddCommMonoid Position]
    [Preorder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation :
      Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkPopulation)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkPopulation) ()) :
    selectedBranchingWalkPopulation.card ≤ nSelectedBranchingWalkPopulation.card := by
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
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation :
      Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkPopulation)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkPopulation) ()) :
    Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkPopulation)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkPopulation) () := by
  classical
  have hcard := population_card_le_of_injection φ d selectedBranchingWalk nSelectedBranchingWalk
    selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation prior
  let selectedBranchingWalkOrderKey : RootIndexed.TreeNode Root α → OrderKey :=
    fun p => φ (selectedBranchingWalk.position d p.1 p.2)
  let nSelectedBranchingWalkOrderKey : RootIndexed.TreeNode Root α → OrderKey :=
    fun q => φ (nSelectedBranchingWalk.position d q.1 q.2)
  have hthresholdCount : ∀ a : OrderKey,
      (selectedBranchingWalkPopulation.filter fun p => selectedBranchingWalkOrderKey p ≤ a).card ≤
        (nSelectedBranchingWalkPopulation.filter fun q => nSelectedBranchingWalkOrderKey q ≤ a).card := by
    intro a
    simpa [selectedBranchingWalkOrderKey, nSelectedBranchingWalkOrderKey, populationCloud] using
      prior.card_filter_le selectedBranchingWalkPopulation.finite_toSet
        nSelectedBranchingWalkPopulation.finite_toSet a
  let matchedNSelectedChildOrSelf : RootIndexed.TreeNode Root α →
      RootIndexed.TreeNode Root α :=
    matchByRankOrSelf selectedBranchingWalkOrderKey nSelectedBranchingWalkOrderKey
      selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation hcard
  refine ⟨matchedNSelectedChildOrSelf, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkPopulation := by
      simpa [populationCloud] using hp
    change matchedNSelectedChildOrSelf p ∈ nSelectedBranchingWalkPopulation
    exact matchByRankOrSelf_mem selectedBranchingWalkOrderKey
      nSelectedBranchingWalkOrderKey selectedBranchingWalkPopulation
      nSelectedBranchingWalkPopulation hcard hpr
  · intro p hp q hq hpq
    apply matchByRankOrSelf_injOn selectedBranchingWalkOrderKey
      nSelectedBranchingWalkOrderKey selectedBranchingWalkPopulation
      nSelectedBranchingWalkPopulation hcard
    · simpa [populationCloud] using hp
    · simpa [populationCloud] using hq
    · exact hpq
  · intro p hp
    have hpr : p ∈ selectedBranchingWalkPopulation := by
      simpa [populationCloud] using hp
    exact matchByRankOrSelf_partnerOrderKey_le selectedBranchingWalkOrderKey
      nSelectedBranchingWalkOrderKey selectedBranchingWalkPopulation
      nSelectedBranchingWalkPopulation hcard hthresholdCount hpr

@[simp] theorem canonicalInjection_apply
    [AddCommMonoid Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    (φ : Position → OrderKey) (d : Mark → Position)
    (selectedBranchingWalk nSelectedBranchingWalk : RootIndexed.BranchingWalk Root α Mark Position)
    (selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation :
      Finset (RootIndexed.TreeNode Root α))
    (prior : Cloud.SliceDominatingMap φ
      (populationCloud d selectedBranchingWalk selectedBranchingWalkPopulation)
      (populationCloud d nSelectedBranchingWalk nSelectedBranchingWalkPopulation) ())
    (p : RootIndexed.TreeNode Root α) :
    canonicalInjection φ d selectedBranchingWalk nSelectedBranchingWalk
      selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation prior p =
      matchByRankOrSelf
        (fun q => φ (selectedBranchingWalk.position d q.1 q.2))
        (fun q => φ (nSelectedBranchingWalk.position d q.1 q.2))
        selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation
        (population_card_le_of_injection φ d selectedBranchingWalk nSelectedBranchingWalk
          selectedBranchingWalkPopulation nSelectedBranchingWalkPopulation prior) p := by
  rfl


end Combinatorics.Branching.Selection.Coupling

end
