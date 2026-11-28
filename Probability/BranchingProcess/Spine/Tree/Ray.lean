/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Construction
import Probability.BranchingProcess.Spine.LocalBias.Ray
public import Probability.BranchingProcess.Spine.Observation
public import Probability.BranchingProcess.State.Support
public import Combinatorics.UlamHarris.Ray

/-!
# The unique realized distinguished ray

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `ae_treeKernel_unique_spine` proves
  `∃! f, IsRay C(t) f ∧ C(t) = range (lineagePrefix f)` almost surely when the root is
  distinguished, the offspring kernel is Markov, and its mean weight is
  harmonic on the finite positive-weight domain. Each prefix is an actual
  distinguished node, so the ray is realized and infinite.

This formalizes the nonextinction and unique spine in Zhan Shi,
*Branching Random Walks* (2015), Chapter 4, §4.4, the construction after
(4.8) and the paragraph before Theorem 4.3,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
It specializes `LocalBias.ae_treeKernel_unique_spine`; existence of a ray
alone does not assert the tree-density or conditional spinal decomposition.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open scoped ENNReal

/-- The canonical normal/distinguished tree has exactly one realized infinite spine. -/
theorem ae_treeKernel_unique_spine {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)),
      ∃! f, IsRay (distinguishedNodes t) f ∧
        distinguishedNodes t = Set.range (lineagePrefix f) := by
  exact LocalBias.ae_treeKernel_unique_spine Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic) s

end ProbabilityTheory.BranchingProcess.Spine

end
