/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Random lines of tree addresses

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsRandomLine L` means `L : Ω → Set (RootIndexed.TreeNode Root α)` is
  measurable for Mathlib's membership-generated set space and every `L ω`
  satisfies the existing deterministic `RootIndexed.IsLine` predicate.
* `IsRandomLine.measurableSet_mem` states that `{ω | u ∈ L ω}` is measurable.
* `IsRandomLine.const` constructs a constant random line from a deterministic line.
* `IsRandomLine.inter` intersects two random lines;
  `IsRandomLine.restrict` intersects a random line with a fixed node set.
* `IsRandomLine.ite` chooses between random lines on a measurable event.
* `IsRandomLine.comp` pulls a random line back along a measurable map.

The sample space, root set, and child-index type are arbitrary. A random line
need not cover infinite paths. Membership in a particular realized random
tree is the separate condition `∀ ω, L ω ⊆ T ω`.

The ancestry condition is the definition of a line in A. E. Kyprianou,
*Martingale convergence and the stopped branching random walk* (2000), §2,
p. 408, [DOI:10.1007/s004409900036](https://doi.org/10.1007/s004409900036).
This module uses no branching law or probability measure.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

variable {Ω Ω' Root α : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- A measurable random subset which is an ancestry line at every sample point. -/
structure IsRandomLine (L : Ω → Set (RootIndexed.TreeNode Root α)) : Prop where
  measurable : Measurable L
  isLine : ∀ ω, RootIndexed.IsLine (L ω)

theorem IsRandomLine.measurableSet_mem {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (h : IsRandomLine L) (u : RootIndexed.TreeNode Root α) :
    MeasurableSet {ω | u ∈ L ω} :=
  measurableSet_setOfPred.mpr (h.measurable.mem)

theorem IsRandomLine.const {ℓ : Set (RootIndexed.TreeNode Root α)}
    (hℓ : RootIndexed.IsLine ℓ) : IsRandomLine (fun _ : Ω => ℓ) :=
  ⟨measurable_const, fun _ => hℓ⟩

theorem IsRandomLine.inter {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsRandomLine L) (hM : IsRandomLine M) :
    IsRandomLine (fun ω => L ω ∩ M ω) :=
  ⟨hL.measurable.inter hM.measurable, fun ω => (hL.isLine ω).subset Set.inter_subset_left⟩

theorem IsRandomLine.restrict {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsRandomLine L) (C : Set (RootIndexed.TreeNode Root α)) :
    IsRandomLine (fun ω => L ω ∩ C) :=
  ⟨hL.measurable.inter measurable_const, fun ω => (hL.isLine ω).subset Set.inter_subset_left⟩

theorem IsRandomLine.ite {L M : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsRandomLine L) (hM : IsRandomLine M) {A : Set Ω} (hA : MeasurableSet A) :
    IsRandomLine (fun ω => if ω ∈ A then L ω else M ω) := by
  classical
  refine ⟨hL.measurable.ite hA hM.measurable, fun ω => ?_⟩
  split <;> first | exact hL.isLine ω | exact hM.isLine ω

theorem IsRandomLine.comp {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsRandomLine L) {f : Ω' → Ω} (hf : Measurable f) : IsRandomLine (L ∘ f) :=
  ⟨hL.measurable.comp hf, fun ω => hL.isLine (f ω)⟩

end ProbabilityTheory.Tree

end
