/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Prefix

/-!
# Address expansion of an MRCA contribution

An MRCA contribution at a fixed positive depth can be expanded over the
addresses at that generation.  The path test is sliced recursively by
`prependHistory`, so the local depth-zero contribution retains the complete
original path history.  Every birth-survival test along the prefix remains
in the summand.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- Restrict a path test to the continuation below a fixed ancestral
address.  At each edge, `prependHistory` restores the previous position, so
the resulting test is the original test on the full path history. -/
noncomputable def pathGenerationPrefixTest {X : Type*} [MeasurableSpace X]
    (φ : Potential X) :
    (m n : ℕ) → ((Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞) → ℝ →
      StepField ℕ X → TreeNode ℕ → (Fin (n + 2) → ℝ) → ℝ≥0∞
  | 0, _, F, _, _, u => if u = [] then F else fun _ => 0
  | m + 1, n, F, x, ω, u =>
      match u with
      | [] => 0
      | i :: v => pathGenerationPrefixTest φ m n
          (fun tail => F (prependHistory x tail))
          (x + (ω []).potentialValue' φ i) (subtreeStepField [i] ω) v

/-- The local depth-zero contribution associated with a generation-`m`
address. -/
noncomputable def pathGenerationPrefixMRCAContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ)
    (F : (Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ω : StepField ℕ X) (u : TreeNode ℕ) : ℝ≥0∞ :=
  pathGenerationMRCAContribution φ 0 (n + 1)
    (pathGenerationPrefixTest φ m n F x ω u)
    (x + pathPotential φ ω u) (subtreeStepField u ω)

/-- The prefix contribution with its ancestral survival condition. -/
noncomputable def pathGenerationSurvivingPrefixMRCAContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ)
    (F : (Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ω : StepField ℕ X) (u : {u : TreeNode ℕ // u.length = m}) : ℝ≥0∞ := by
  classical
  exact if surviveAlong ω [] u.1 then
    pathGenerationPrefixMRCAContribution φ m n F x ω u.1 else 0

/-- Adding the first edge to a prefix contribution tests that edge and then
continues with the same local contribution in its descendant field. -/
theorem pathGenerationSurvivingPrefixMRCAContribution_cons
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ)
    (F : (Fin ((n + 1 + (m + 1)) + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) (i : ℕ)
    (v : {v : TreeNode ℕ // v.length = m}) :
    pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω
        ⟨i :: v.1, by simp [v.2]⟩ =
      survivingPotentialTest φ
        (fun y => pathGenerationSurvivingPrefixMRCAContribution φ m n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω) v)
        (ω []) i := by
  classical
  have hposition :
      x + pathPotential φ ω (i :: v.1) =
        (x + (ω []).potentialValue' φ i) +
          pathPotential φ (subtreeStepField [i] ω) v.1 := by
    rw [pathPotential_cons]
    ring
  have hsubtree : subtreeStepField (i :: v.1) ω =
      subtreeStepField v.1 (subtreeStepField [i] ω) := rfl
  have hlocal :
      pathGenerationPrefixMRCAContribution φ (m + 1) n F x ω (i :: v.1) =
        pathGenerationPrefixMRCAContribution φ m n
          (fun tail => F (prependHistory x tail))
          (x + (ω []).potentialValue' φ i) (subtreeStepField [i] ω) v.1 := by
    simp only [pathGenerationPrefixMRCAContribution, pathGenerationPrefixTest]
    rw [hposition, hsubtree]
  have hsurvive : surviveAlong ω [] (i :: v.1) ↔
      survive (ω []) i ∧
        surviveAlong (subtreeStepField [i] ω) [] v.1 := by
    rw [surviveAlong_cons]
    simp only [List.nil_append]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨hi, (surviveAlong_rebase ω [i] [] v.1).mpr h⟩
    · rintro ⟨hi, h⟩
      exact ⟨hi, (surviveAlong_rebase ω [i] [] v.1).mp h⟩
  unfold pathGenerationSurvivingPrefixMRCAContribution
  rw [hsurvive, hlocal]
  unfold survivingPotentialTest
  by_cases hi : survive (ω []) i <;> simp [hi]

/-- The recursively sliced test is exactly the original test evaluated on
the full path history obtained by joining the ancestral address and its
continuation. -/
theorem pathGenerationPrefixTest_apply_pathHistory
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ)
    (F : (Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X)
    (u v : TreeNode ℕ) (hu : u.length = m) (hv : v.length = n + 1) :
    pathGenerationPrefixTest φ m n F x ω u
      (pathHistory φ (n + 1) (x + pathPotential φ ω u)
        (subtreeStepField u ω) v) =
      F (pathHistory φ ((n + 1) + m) x ω (u ++ v)) := by
  induction m generalizing x ω u v with
  | zero =>
      have hu0 : u = [] := List.eq_nil_iff_length_eq_zero.mpr hu
      subst u
      have hnil : subtreeStepField [] ω = ω := by
        funext w
        simp [subtreeStepField]
      simp [pathGenerationPrefixTest, pathPotential, hnil]
  | succ m ih =>
      cases u with
      | nil => simp at hu
      | cons i u =>
          have hu' : u.length = m := by simpa using hu
          let tailTest : (Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞ :=
            fun tail => F (prependHistory x tail)
          have hposition :
              (x + (ω []).potentialValue' φ i) +
                  pathPotential φ (subtreeStepField [i] ω) u =
                x + pathPotential φ ω (i :: u) := by
            rw [pathPotential_cons]
            ring
          have hsubtree :
              subtreeStepField u (subtreeStepField [i] ω) =
                subtreeStepField (i :: u) ω := rfl
          have htail :
              pathHistory φ (n + 1)
                  (x + pathPotential φ ω (i :: u))
                  (subtreeStepField (i :: u) ω) v =
                pathHistory φ (n + 1)
                  ((x + (ω []).potentialValue' φ i) +
                    pathPotential φ (subtreeStepField [i] ω) u)
                  (subtreeStepField u (subtreeStepField [i] ω)) v := by
            rw [hposition, hsubtree]
          have hsplice :
              prependHistory x
                (pathHistory φ ((n + 1) + m)
                  (x + (ω []).potentialValue' φ i)
                  (subtreeStepField [i] ω) (u ++ v)) =
              pathHistory φ ((n + 1) + (m + 1)) x ω
                ((i :: u) ++ v) := by
            simpa only [Nat.add_succ, List.cons_append] using
              (pathHistory_cons φ (n + 1 + m) x ω i (u ++ v)).symm
          rw [pathGenerationPrefixTest]
          rw [htail]
          rw [ih tailTest (x + (ω []).potentialValue' φ i)
            (subtreeStepField [i] ω) u v hu' hv]
          change F (prependHistory x
            (pathHistory φ ((n + 1) + m)
              (x + (ω []).potentialValue' φ i)
              (subtreeStepField [i] ω) (u ++ v))) = _
          rw [hsplice]

/-- Expanding a fixed-depth ordered-pair contribution by its unique
generation-`m` ancestor.  The summand retains the survival of every edge in
the ancestral prefix and evaluates the depth-zero pair contribution in that
ancestor's descendant field, using the complete original path test. -/
theorem pathGenerationMRCAContribution_eq_sum_prefix
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ)
    (F : (Fin ((n + 1 + m) + 1) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ω : StepField ℕ X) :
    pathGenerationMRCAContribution φ m ((n + 1) + m) F x ω =
      ∑' u : {u : TreeNode ℕ // u.length = m},
        pathGenerationSurvivingPrefixMRCAContribution φ m n F x ω u := by
  classical
  induction m generalizing n x ω with
  | zero =>
      rw [tsum_eq_single ⟨[], by simp⟩]
      · have hnil : subtreeStepField [] ω = ω := by
          funext v
          simp [subtreeStepField]
        simp [pathGenerationPrefixMRCAContribution,
          pathGenerationSurvivingPrefixMRCAContribution,
          pathGenerationPrefixTest, pathGenerationMRCAContribution,
          pathPotential, subtreeStepField, surviveAlong, hnil]
      · intro u hu
        have hu' : u.1 ≠ [] := by
          intro hnil
          apply hu
          exact Subtype.ext hnil
        have hsurvive : ¬ surviveAlong ω [] u.1 := by
          intro hs
          exact hu' (List.eq_nil_iff_length_eq_zero.mpr u.2)
        simp [pathGenerationSurvivingPrefixMRCAContribution, hsurvive]
  | succ m ih =>
      rw [pathGenerationMRCAContribution.eq_def]
      simp only [Nat.add_succ]
      change (∑' i : ℕ,
          survivingPotentialTest φ
            (fun y => pathGenerationMRCAContribution φ m ((n + 1) + m)
              (fun tail => F (prependHistory x tail)) (x + y)
              (subtreeStepField [i] ω)) (ω []) i) = _
      have hchild (i : ℕ) :
          survivingPotentialTest φ
            (fun y => pathGenerationMRCAContribution φ m ((n + 1) + m)
              (fun tail => F (prependHistory x tail)) (x + y)
              (subtreeStepField [i] ω)) (ω []) i =
          ∑' v : {v : TreeNode ℕ // v.length = m},
            pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω
              ⟨i :: v.1, by simp [v.2]⟩ := by
        unfold survivingPotentialTest
        by_cases hi : survive (ω []) i
        · simp only [hi, ite_true]
          rw [ih n (fun tail => F (prependHistory x tail))
            (x + (ω []).potentialValue' φ i) (subtreeStepField [i] ω)]
          apply tsum_congr
          intro v
          rw [pathGenerationSurvivingPrefixMRCAContribution_cons]
          simp [survivingPotentialTest, hi]
        · simp only [hi, ite_false]
          symm
          apply ENNReal.tsum_eq_zero.mpr
          intro v
          rw [pathGenerationSurvivingPrefixMRCAContribution_cons]
          simp [survivingPotentialTest, hi]
      calc
        _ = ∑' i : ℕ, ∑' v : {v : TreeNode ℕ // v.length = m},
              pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω
                ⟨i :: v.1, by simp [v.2]⟩ := by
              apply tsum_congr
              exact hchild
        _ = ∑' p : ℕ × {v : TreeNode ℕ // v.length = m},
              pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω
                ((generationConsEquiv ℕ m p)) := ENNReal.tsum_prod.symm
        _ = ∑' u : {u : TreeNode ℕ // u.length = m + 1},
              pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω u :=
                Equiv.tsum_eq (generationConsEquiv ℕ m)
                  (pathGenerationSurvivingPrefixMRCAContribution φ (m + 1) n F x ω)

end ProbabilityTheory.BranchingRandomWalk.Spine
