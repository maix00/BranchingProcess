/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Additive.StateKernel
public import Probability.BranchingProcess.Spine.Tree.PathLaw
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
public import Probability.Process.RandomWalk.Kernel.Markov.Trajectory

/-!
# The additive spine and the auxiliary tilted random walk have one path law

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine.Additive`:

* `map_spinePath_law` identifies the observed spine under the canonical
  distinguished-tree measure with the random walk under the existing IID
  tilted-increment law: `P_spine.map spinePositions = ν^ℕ.map partialSums`.
  It assumes an arbitrary probability law on indexed raw offspring marks,
  countable measurable child slots and boundary normalization only.

This is Zhan Shi, *Branching Random Walks* (2015), Theorem 4.4(ii), (4.10),
DOI 10.1007/978-3-319-25372-5. The proof transports the existing general Doob
state-chain law through its state projection, identifies its increment kernel,
and uses the canonical IID trajectory-law theorem. The original tree law,
changed distinguished-tree law and auxiliary IID law remain distinct measures.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.Additive

open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The observed spine under the changed tree measure has exactly the
auxiliary tilted walk's law; neither realization is assumed on the original space. -/
theorem map_spinePath_law {ι Mark : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Mark]
    (φ : Potential Mark) (μ : Measure (Step ι Mark)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (x : ℝ) :
    let s : {y // weight y ≠ 0 ∧ weight y ≠ ∞} :=
      ⟨x, weight_ne_zero x, weight_ne_top x⟩
    let harmonic := fun y (_ : weight y ≠ 0) (_ : weight y ≠ ∞) =>
      harmonic_weight φ μ hboundary y
    ((BranchingProcess.Spine.treeKernel (offspringKernel φ μ) measurable_weight
      harmonic (some (Sum.inr s))).map
        (fun t n => (BranchingProcess.Spine.statePath s t n).1)) =
      (tiltedIncrementFieldLaw φ μ).map (fun ξ n => RandomWalk.positionProcess x n ξ) := by
  let s : {y // weight y ≠ 0 ∧ weight y ≠ ∞} :=
    ⟨x, weight_ne_zero x, weight_ne_top x⟩
  let harmonic := fun y (_ : weight y ≠ 0) (_ : weight y ≠ ∞) =>
    harmonic_weight φ μ hboundary y
  let := tiltedPotentialLaw_isProbability φ μ hboundary
  let K := BranchingProcess.Spine.eligibleStateKernel (offspringKernel φ μ) measurable_weight
  let := BranchingProcess.Spine.eligibleStateKernel_isMarkovKernel
    (offspringKernel φ μ) measurable_weight harmonic
  let ν := tiltedPotentialLaw φ (-1) μ
  have ht := congrArg (fun m : Measure (ℕ → {y // weight y ≠ 0 ∧ weight y ≠ ∞}) =>
      m.map (fun z n => (z n).1))
    (BranchingProcess.Spine.treeKernel_statePath
      (offspringKernel φ μ) measurable_weight harmonic s s)
  rw [Measure.map_map (by fun_prop) (BranchingProcess.Spine.measurable_statePath s)] at ht
  have hstep (n : ℕ) (history : Iic n → {y // weight y ≠ 0 ∧ weight y ≠ ∞}) :
      ((Kernel.historyKernel K n) history).map Subtype.val =
        Kernel.historyKernel (RandomWalk.incrementKernel ν) n (fun k => (history k).1) := by
    change (K (history ⟨n, by simp⟩)).map Subtype.val =
      RandomWalk.incrementKernel ν (history ⟨n, by simp⟩).1
    rw [BranchingProcess.Spine.eligibleStateKernel_map
      (offspringKernel φ μ) measurable_weight harmonic]
    exact congrArg (fun k : Kernel ℝ ℝ => k (history ⟨n, by simp⟩).1)
      (spineChildKernel_eq_incrementKernel φ μ hboundary)
  have hstart : Kernel.traj (X := fun _ => {y // weight y ≠ 0 ∧ weight y ≠ ∞})
      (Kernel.historyKernel K) 0 (fun _ => s) =
      Kernel.trajMeasure (Measure.dirac s) (Kernel.historyKernel K) := by
    rw [Kernel.trajMeasure, Measure.map_dirac' (by fun_prop),
      Measure.dirac_bind (Kernel.measurable _)]
    rfl
  have hi := Kernel.map_trajMeasure
    (Kernel.historyKernel K) (Kernel.historyKernel (RandomWalk.incrementKernel ν))
    (fun (_ : ℕ) (y : {y // weight y ≠ 0 ∧ weight y ≠ ∞}) => y.1)
    (fun _ => measurable_subtype_coe) hstep (Measure.dirac s)
  rw [Measure.map_dirac' measurable_subtype_coe] at hi
  change _ = (Kernel.traj (X := fun _ => {y // weight y ≠ 0 ∧ weight y ≠ ∞})
    (Kernel.historyKernel K) 0 (fun _ => s)).map
    (fun z n => (z n).1) at ht
  rw [hstart, hi] at ht
  exact ht.trans (RandomWalk.map_positionProcess_eq_trajMeasure ν x).symm

end ProbabilityTheory.BranchingRandomWalk.Spine.Additive
