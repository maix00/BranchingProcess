/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.StoppingLine.Martingale

/-!
# The ancestral density martingale

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `martingale_totalWeight` proves that `M_n = (totalWeight h n H_n).toReal`
  is a native `Martingale` in `State.treeFiltration`, under the original
  canonical state-tree law started at a finite positive-weight state.

The weight is measurable and mean harmonic at finite positive-weight states.
Child slots are countable with measurable singletons; state spaces are arbitrary.
No second moment, uniform integrability or global density at infinity is assumed.
This packages Zhan Shi, *Branching Random Walks* (2015), §4.3, Lemma 4.1,
DOI 10.1007/978-3-319-25372-5. The theorem is the empty-line specialization of the stopped-line mass
martingale, so it has no parallel conditional-expectation proof.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching StoppingLine
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- The finite-generation ancestral mass is the density martingale of the
existing changed tree law (Shi, Lemma 4.1), without uniform integrability. -/
theorem martingale_totalWeight
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    Martingale (fun n t => (totalWeight h n (State.treeHistory n t)).toReal)
      (State.treeFiltration (ι := ι)) (State.treeKernel Q (some s.1)) := by
  let L := fun _t : List ι → Option S => (∅ : Set (Unit × List ι))
  have hL : Tree.IsRandomLine L := Tree.IsRandomLine.const IsAntichain.empty
  have hs : ∀ u : Unit × List ι,
      MeasurableSet[State.treeFiltration u.2.length] {t | u ∈ L t} :=
    fun _ => MeasurableSet.const _
  have hm := martingale_truncatedMass Q hh harmonic s hL hs
  have heq : truncatedMass h L =
      (fun n t => (totalWeight h n (State.treeHistory n t)).toReal) := by
    funext n t
    exact truncatedMass_empty h n t
  rwa [heq] at hm

end ProbabilityTheory.BranchingProcess.Spine
