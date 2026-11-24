/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.FiniteGeneration
public import Probability.BranchingProcess.State.Observation.History
import Probability.BranchingProcess.Spine.LocalBias.ManyToOne

/-!
# Many-to-one for generation-adapted node payoffs

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `lintegral_adaptedPayoff_eq` proves
  `E[∑_u W_u F_u(T)] = E_spine[∑_(u∈spine) F_u(erase(T))]`
  for arbitrary nonnegative node payoffs measurable at each node's generation.
  No line, antichain, stopping rule, bounded depth, integrability or coverage
  assumption is required. Payoffs may use the whole observed generation.

The offspring kernel is state dependent on an arbitrary measurable state space;
child slots are countable with measurable singletons. The measurable weight is
mean harmonic on its finite positive region, and the root lies there. The
existing ancestral eligibility weights are retained.

This extends the summation argument in J. D. Biggins and A. E. Kyprianou,
*Measure change in multitype branching* (2004), proof of Lemma 14.1,
pp. 577–578, DOI 10.1239/aap/1086957585: finite-history density is the only
probabilistic ingredient. The general local-bias theorem factors generation-measurable payoffs
through finite history and sums the fixed-address identities; this module
specializes that theorem without another summation proof. A line hypothesis is needed only by corollaries that identify
spinal sums with a single entrance payoff.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open Classical MeasureTheory Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- The many-to-one compensation identity for all nonnegative adapted node
payoffs, without requiring the active nodes to form a line. -/
theorem lintegral_adaptedPayoff_eq
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    (F : List ι → (List ι → Option S) → ℝ≥0∞)
    (hF : ∀ u, Measurable[State.treeFiltration u.length] (F u)) :
    (∫⁻ t, ∑' u : List ι,
      addressWeight h u.length u.get (State.treeHistory u.length t) * F u t
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, ∑' u : List ι, if (t u).any Sum.isRight = true then
      F u (fun v => (t v).map (Sum.elim id Subtype.val)) else 0
      ∂treeKernel Q hh harmonic (some (Sum.inr s)) := by
  exact LocalBias.lintegral_adaptedPayoff_eq Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic) s F hF

end ProbabilityTheory.BranchingProcess.Spine
