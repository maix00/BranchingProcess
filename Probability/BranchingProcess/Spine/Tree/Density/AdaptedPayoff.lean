/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.FiniteGeneration
public import Probability.BranchingProcess.State.Observation.History
import Mathlib.MeasureTheory.Function.FactorsThrough

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
probabilistic ingredient. Mathlib factors a generation-measurable payoff
through the actual history observation; Tonelli sums the fixed-address
identities. A line hypothesis is needed only by corollaries that identify
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
  choose g hg hge using fun u => (hF u).exists_eq_measurable_comp
  have he : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun v => (t v).map (Sum.elim id Subtype.val)) := by
    have hm := measurable_option_map (measurable_id.sumElim
      (measurable_subtype_coe : Measurable (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S)))
    fun_prop
  have hleft (u : List ι) : Measurable (fun t : List ι → Option S =>
      addressWeight h u.length u.get (State.treeHistory u.length t) * F u t) :=
    ((measurable_addressWeight hh _ _).comp (State.measurable_treeHistory _)).mul
      ((hF u).mono (State.treeFiltration.le _) le_rfl)
  have hright (u : List ι) : Measurable (fun t :
      List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      if (t u).any Sum.isRight = true then
        F u (fun v => (t v).map (Sum.elim id Subtype.val)) else 0) := by
    have htag : Measurable (fun t :
        List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) => (t u).any Sum.isRight) :=
      (show Measurable (fun o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
        o.any Sum.isRight) from
        measurable_option_elim false (measurable_const.sumElim measurable_const)).comp
          (measurable_pi_apply u)
    exact (((hF u).mono (State.treeFiltration.le _) le_rfl).comp he).ite
      ((measurableSet_singleton true).preimage htag) measurable_const
  rw [lintegral_tsum (fun u => (hleft u).aemeasurable),
    lintegral_tsum (fun u => (hright u).aemeasurable)]
  apply tsum_congr
  intro u
  have hi := lintegral_treeKernel_fixedAddress Q hh harmonic s u.length u.get (hg u)
  simp only [List.ofFn_get] at hi
  have hread (t : List ι → Option S) : F u t = g u (State.treeHistory u.length t) :=
    congrFun (hge u) t
  calc
    _ = ∫⁻ t, addressWeight h u.length u.get (State.treeHistory u.length t) *
        g u (State.treeHistory u.length t) ∂State.treeKernel Q (some s.1) :=
      lintegral_congr fun t => congrArg _ (hread t)
    _ = _ := hi.symm.trans (lintegral_congr fun t => by
      change (if (t u).any Sum.isRight = true then g u (untypedHistory u.length t) else 0) = _
      have hr := hread (fun v => (t v).map (Sum.elim id Subtype.val))
      change F u (fun v => (t v).map (Sum.elim id Subtype.val)) =
        g u (untypedHistory u.length t) at hr
      rw [hr])

end ProbabilityTheory.BranchingProcess.Spine
