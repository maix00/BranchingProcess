/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.FirstEntrance
public import Probability.Process.Tree.Line.Ancestral

/-!
# Observable first-entrance lines

## Public declarations

In `ProbabilityTheory.Tree`:

* `measurableSet_firstEntrance_mem` proves `{u ∈ firstEntrance (A ω)}` is
  measurable in `history u` when each target decision `{v ∈ A ω}` is
  measurable in `history v` and these histories increase along ancestry.
* `isRandomLine_firstEntrance` constructs a random line from measurable
  target decisions, with arbitrary root and child types.
* `isOptionalLine_firstEntrance` proves optionality for a countable address
  space when target decisions use strict-ancestor reproduction information.

These results formalize the first-entry construction of J. D. Biggins and
A. E. Kyprianou, *Measure change in multitype branching* (2004), §6, p. 557,
lines `I[t]` before Proposition 6.1,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
They separate construction and observability from the martingale and
mean-harmonic assumptions of that proposition. Targets may depend on the
node and its full ancestral observations; no common threshold rule is needed.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*}

/-- First entrance can be decided from finitely many ancestral target decisions. -/
theorem measurableSet_firstEntrance_mem
    (history : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    (hmono : ∀ {v u}, RootIndexed.IsAncestor v u → history v ≤ history u)
    (A : Ω → Set (RootIndexed.TreeNode Root α))
    (hA : ∀ u, MeasurableSet[history u] {ω | u ∈ A ω})
    (u : RootIndexed.TreeNode Root α) :
    MeasurableSet[history u] {ω | u ∈ RootIndexed.Line.firstEntrance (A ω)} := by
  have heq : {ω | u ∈ RootIndexed.Line.firstEntrance (A ω)} =
      {ω | u ∈ A ω} ∩ ⋂ k : ℕ, {ω | k < u.2.length → (u.1, u.2.take k) ∉ A ω} := by
    ext ω
    simp [RootIndexed.Line.mem_firstEntrance_iff]
  rw [heq]
  apply (hA u).inter
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k < u.2.length
  · have hm := hmono (show RootIndexed.IsAncestor (u.1, u.2.take k) u from
      ⟨rfl, List.take_prefix _ _⟩) _ (hA (u.1, u.2.take k))
    simpa only [hk, true_implies, Set.compl_ofPred] using hm.compl
  · simp only [hk, false_implies, Set.ofPred_true]
    exact @MeasurableSet.univ Ω (history u)

/-- Measurable target sets give measurable first-entrance lines. -/
theorem isRandomLine_firstEntrance [mΩ : MeasurableSpace Ω]
    (A : Ω → Set (RootIndexed.TreeNode Root α))
    (hA : ∀ u, MeasurableSet {ω | u ∈ A ω}) :
    IsRandomLine (fun ω => RootIndexed.Line.firstEntrance (A ω)) := by
  refine ⟨measurable_set_iff.mpr (fun u => measurableSet_setOfPred.mp ?_),
    fun ω => RootIndexed.Line.isLine_firstEntrance (A ω)⟩
  exact measurableSet_firstEntrance_mem (fun _ => mΩ) (fun _ => le_rfl) A hA u

/-- Ancestrally observable target rules yield optional first entrance. -/
theorem isOptionalLine_firstEntrance [mΩ : MeasurableSpace Ω]
    [Countable (RootIndexed.TreeNode Root α)]
    (initial : MeasurableSpace Ω)
    (coordinate : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    (hi : initial ≤ mΩ) (hc : ∀ u, coordinate u ≤ mΩ)
    (A : Ω → Set (RootIndexed.TreeNode Root α))
    (hA : ∀ u, MeasurableSet[ancestralPast initial coordinate u] {ω | u ∈ A ω}) :
    @IsOptionalLine Ω Root α mΩ (linePast initial coordinate)
      (fun ω => RootIndexed.Line.firstEntrance (A ω)) := by
  have hmem := measurableSet_firstEntrance_mem (ancestralPast initial coordinate)
    (ancestralPast_mono initial coordinate) A hA
  apply IsRandomLine.isOptionalLine_of_ancestral_mem (mΩ := mΩ)
    initial coordinate _ hmem
  exact @isRandomLine_firstEntrance Ω Root α mΩ A
    (fun u => ancestralPast_le initial coordinate hi hc u _ (hA u))

end ProbabilityTheory.Tree

end
