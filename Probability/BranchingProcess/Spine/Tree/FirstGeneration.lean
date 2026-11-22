/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Construction

/-!
# First-generation density of the distinguished tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `treeKernel_firstFamily` identifies the root's untyped offspring-family
  marginal under the canonical distinguished tree with
  `Q(s,dξ) (∑_i h(ξ_i))/h(s)`.

This is the first-generation case of Zhan Shi, *Branching Random Walks*
(2015), Chapter 4, §4.4, Theorem 4.3 and its proof,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
The law on the left is extracted from the already constructed entire tree;
it is not a separately defined tilted family law. Here `h` is the full
reproductive weight, including Shi's exponential and region factors.
Higher-generation densities require the subsequent induction over the same law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

/-- Erasing the first generation's role tags gives exactly its total-weight density. -/
theorem treeKernel_firstFamily {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (treeKernel Q hh harmonic (some (Sum.inr s))).map
      (fun t => Step.map (Sum.elim id Subtype.val) (fun j => t [j])) =
      (Q s).withDensity (fun ξ => (∑' i, (ξ i).elim 0 h) / h s) := by
  let : IsMarkovKernel (reproductionKernel Q h) :=
    reproductionKernel_isMarkovKernel Q hh harmonic
  have herase : Measurable (Step.map (ι := ι)
      (Sum.elim id (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S))) :=
    Step.map_measurable (measurable_id.sumElim measurable_subtype_coe)
  change (State.treeKernel (reproductionKernel Q h) (some (Sum.inr s))).map
    ((Step.map (Sum.elim id Subtype.val)) ∘ (fun t => fun j => t [j])) = _
  rw [← Measure.map_map herase (by fun_prop), State.treeKernel_children,
    Kernel.optionElim_some, reproductionKernel_distinguished_map Q hh,
    biasedFamily_eq_withDensity Q hh]
  apply Kernel.withDensity_apply
  exact (Measurable.tsum (fun i => (measurable_option_elim 0 hh).comp
    ((measurable_pi_apply i).comp measurable_snd))).div (hh.comp measurable_fst)

end ProbabilityTheory.BranchingProcess.Spine

end
