/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition
public import Probability.Process.RandomWalk.Path.Basic
public import Combinatorics.UlamHarris.Mark.Path

/-!
# Potential histories along branching paths

A history of length `n` records positions at times `0, ..., n`. The generic
increment-path history is `history`; this file relates it to paths
inside a branching realization.

## Public declarations

- `pathHistory`: the real positions at times $0,\ldots,n$ along a branching
  address, including its initial position.
- `pathHistory_last`, `pathHistory_measurable`,
  `pathHistory_joint_measurable`, and `pathHistory_cons`: identify the endpoint,
  prove measurability in the field and initial position, and give the
  one-step recursive decomposition.
- `pathHistory_eq_finitePrefix_records` identifies the scalar history with
  the partial sums of complete ancestral parent-family/child records.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.RandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Positions, including the initial position, along the first `n` edges of
an address in a pre-sampled branching field. -/
def pathHistory {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι) :
    Fin (n + 1) → ℝ :=
  fun k => x + pathPotential φ ω (u.take k)

@[simp] theorem pathHistory_zero
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι) :
    pathHistory φ n x ω u ⟨0, Nat.zero_lt_succ n⟩ = x := by
  simp [pathHistory]

theorem pathHistory_last
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (u : TreeNode ι)
    (hu : u.length = n) :
    pathHistory φ n x ω u ⟨n, Nat.lt_succ_self n⟩ =
      x + pathPotential φ ω u := by
  simp [pathHistory, ← hu]

theorem pathHistory_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (u : TreeNode ι) :
    Measurable (fun ω : Combinatorics.Branching.StepField ι X =>
      pathHistory φ n x ω u) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_const.add (pathPotential_measurable φ [] (u.take k))

theorem pathHistory_joint_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (u : TreeNode ι) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathHistory φ n p.1 p.2 u) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.add
    ((pathPotential_measurable φ [] (u.take k)).comp measurable_snd)

/-- A branching history along `i :: v` consists of its initial position and
the descendant history below the actually chosen first slot `i`. -/
theorem pathHistory_cons
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) (i : ι) (v : TreeNode ι) :
    pathHistory φ (n + 1) x ω (i :: v) =
      prependHistory x
        (pathHistory φ n (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) v) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [pathHistory]
  · simp [pathHistory, prependHistory, List.take_succ_cons,
      pathPotential_cons, add_assoc]

/-- The original scalar history is the finite partial-sum path of the
displacements read from the complete parent-family/child records. -/
theorem pathHistory_eq_finitePrefix_records {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (field : StepField ι X) (z : Fin n → ι) :
    pathHistory φ n x field (List.ofFn z) =
      AdditivePath.finitePrefix x (fun j =>
        (Mark.pathRecords field z j).1.potentialValue' φ
          (Mark.pathRecords field z j).2) := by
  funext k
  induction k using Fin.induction with
  | zero => simp [pathHistory]
  | succ k ih =>
    rw [AdditivePath.finitePrefix_succ, ← ih]
    have hk : k.val < (List.ofFn z).length := by simpa only [List.length_ofFn] using k.isLt
    have ht := List.take_concat_get hk
    simp only [List.getElem_ofFn] at ht
    simp only [pathHistory, Fin.val_succ, Fin.val_castSucc, Mark.pathRecords]
    rw [← ht]
    simp only [List.concat_eq_append, pathPotential]
    change x + displace (field.map φ) [] ((List.ofFn z).take k.val ++ [z k]) =
      x + displace (field.map φ) [] ((List.ofFn z).take k.val) +
        ((field ((List.ofFn z).take k.val)).potentialAt? φ (z k)).getD 0
    rw [displace_append_singleton]
    simp [StepField.map, Step.map, value', Step.potentialAt?, add_assoc]

end ProbabilityTheory.BranchingRandomWalk.Spine
