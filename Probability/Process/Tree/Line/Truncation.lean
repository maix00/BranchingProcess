/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.Truncation
public import Probability.Process.Tree.Line.FirstEntrance

/-!
# Observable generation truncations

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsRandomLine.truncate` proves that `ω ↦ L(ω)_n` is a random line.
* `isOptionalLine_truncate_of_ancestral_mem` proves optionality of `L_n`
  when each `{u ∈ L}` uses initial and strict-ancestor reproduction
  information. Addresses are countable only in the optionality theorem.

J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*
(2004), §14, p. 578, Lemma 14.3,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585),
prove optionality for simple optional lines. The result here handles the
ancestrally observable subclass using the existing first-entrance theorem;
it does not claim the full simple-line lemma or its martingale consequences.
General optional lines need not have optional truncations (same page).
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

variable {Ω Root α : Type*} [mΩ : MeasurableSpace Ω]

/-- A generation cut preserves randomness, without an optionality assumption. -/
theorem IsRandomLine.truncate {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (hL : IsRandomLine L) (n : ℕ) :
    IsRandomLine (fun ω => RootIndexed.Line.truncate (L ω) n) := by
  apply isRandomLine_firstEntrance
  intro u
  by_cases hu : u.2.length = n
  · simp only [Set.mem_union, Set.mem_ofPred_eq, hu, or_true, Set.ofPred_true]
    exact MeasurableSet.univ
  · simpa only [Set.mem_union, Set.mem_ofPred_eq, hu, or_false] using hL.measurableSet_mem u

/-- The same ancestral target rule decides both original and truncated stopping. -/
theorem isOptionalLine_truncate_of_ancestral_mem
    [Countable (RootIndexed.TreeNode Root α)]
    (initial : MeasurableSpace Ω)
    (coordinate : RootIndexed.TreeNode Root α → MeasurableSpace Ω)
    (hi : initial ≤ mΩ) (hc : ∀ u, coordinate u ≤ mΩ)
    (L : Ω → Set (RootIndexed.TreeNode Root α))
    (hL : ∀ u, MeasurableSet[ancestralPast initial coordinate u] {ω | u ∈ L ω})
    (n : ℕ) : @IsOptionalLine Ω Root α mΩ (linePast initial coordinate)
      (fun ω => RootIndexed.Line.truncate (L ω) n) := by
  apply isOptionalLine_firstEntrance (mΩ := mΩ) initial coordinate hi hc
  intro u
  by_cases hu : u.2.length = n
  · simp only [Set.mem_union, Set.mem_ofPred_eq, hu, or_true, Set.ofPred_true]
    exact @MeasurableSet.univ Ω (ancestralPast initial coordinate u)
  · simpa only [Set.mem_union, Set.mem_ofPred_eq, hu, or_false] using hL u

end ProbabilityTheory.Tree

end
