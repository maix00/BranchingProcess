/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition
public import Combinatorics.BranchingWalk.Walk.Path.Basic

/-!
# Potential histories along branching paths

A history of length `n` records positions at times `0, ..., n`. The generic
increment-path history is `history`; this file relates it to paths
inside a branching realization.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk

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

end ProbabilityTheory.BranchingRandomWalk.Spine
