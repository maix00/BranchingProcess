/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Basic

/-!
# Actual generation observables of ancestral paths

The sums range over all addresses and use the same realization event as the
endpoint observables. Empty generations contribute zero.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.RandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

noncomputable def weightedPathGenerationTerm
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ENNReal) (x : ℝ)
    (u : TreeNode ι) :
    Combinatorics.Branching.StepField ι X → ENNReal :=
  {ω | u.length = n ∧ surviveAlong ω [] u}.indicator fun ω =>
    ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
      F (pathHistory φ n x ω u)

noncomputable def pathGenerationTerm
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ENNReal) (x : ℝ)
    (u : TreeNode ι) :
    Combinatorics.Branching.StepField ι X → ENNReal :=
  {ω | u.length = n ∧ surviveAlong ω [] u}.indicator fun ω =>
    F (pathHistory φ n x ω u)

noncomputable def weightedPathGeneration
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) : ENNReal :=
  ∑' u : TreeNode ι, weightedPathGenerationTerm φ n F x u ω

noncomputable def pathGeneration
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) : ENNReal :=
  ∑' u : TreeNode ι, pathGenerationTerm φ n F x u ω

theorem weightedPathGenerationTerm_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) (u : TreeNode ι) :
    Measurable (weightedPathGenerationTerm φ n F x u) := by
  have hp := pathPotential_measurable φ [] u
  apply (hp.neg.exp.ennreal_ofReal.mul
    (hF.comp (pathHistory_measurable φ n x u))).indicator
  by_cases hu : u.length = n
  · simpa [hu] using measurableSet_surviveAlong (X := X) [] u
  · simp [hu]

theorem pathGenerationTerm_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) (u : TreeNode ι) :
    Measurable (pathGenerationTerm φ n F x u) := by
  apply (hF.comp (pathHistory_measurable φ n x u)).indicator
  by_cases hu : u.length = n
  · simpa [hu] using measurableSet_surviveAlong (X := X) [] u
  · simp [hu]

theorem weightedPathGeneration_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : ℝ) :
    Measurable (weightedPathGeneration (ι := ι) φ n F x) :=
  Measurable.tsum fun u => weightedPathGenerationTerm_measurable φ n hF x u

theorem pathGeneration_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : ℝ) :
    Measurable (pathGeneration (ι := ι) φ n F x) :=
  Measurable.tsum fun u => pathGenerationTerm_measurable φ n hF x u

theorem weightedPathGeneration_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      weightedPathGeneration φ n F p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hp : Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathPotential φ p.2 u) :=
    (pathPotential_measurable φ [] u).comp measurable_snd
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  exact (hp.neg.exp.ennreal_ofReal.mul
    (hF.comp ((pathHistory_joint_measurable φ n u).comp
      (measurable_fst.prodMk measurable_snd)))).indicator hevent

theorem pathGeneration_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathGeneration φ n F p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  exact (hF.comp ((pathHistory_joint_measurable φ n u).comp
    (measurable_fst.prodMk measurable_snd))).indicator hevent

@[simp] theorem weightedPathGeneration_zero
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (F : (Fin 1 → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    weightedPathGeneration φ 0 F x ω = F (fun _ => x) := by
  classical
  rw [weightedPathGeneration, tsum_eq_single ([] : TreeNode ι)]
  · rw [weightedPathGenerationTerm, Set.indicator_of_mem]
    · simp only [pathPotential, displaceWith, displace, neg_zero,
        Real.exp_zero, ENNReal.ofReal_one, one_mul]
      congr 1
      funext k
      have hk : k = 0 := Fin.eq_zero k
      subst k
      exact pathHistory_zero φ 0 x ω []
    · exact ⟨rfl, surviveAlong_nil ω []⟩
  · intro u hu
    simp [weightedPathGenerationTerm, Set.indicator, hu,
      List.length_eq_zero_iff]

@[simp] theorem pathGeneration_zero
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (F : (Fin 1 → ℝ) → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    pathGeneration φ 0 F x ω = F (fun _ => x) := by
  classical
  rw [pathGeneration, tsum_eq_single ([] : TreeNode ι)]
  · rw [pathGenerationTerm, Set.indicator_of_mem]
    · congr 1
      funext k
      have hk : k = 0 := Fin.eq_zero k
      subst k
      exact pathHistory_zero φ 0 x ω []
    · exact ⟨rfl, surviveAlong_nil ω []⟩
  · intro u hu
    simp [pathGenerationTerm, Set.indicator, hu,
      List.length_eq_zero_iff]

/-- Endpoint observables are path observables tested at the last coordinate. -/
theorem weightedPathGeneration_last
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    weightedPathGeneration φ n
        (fun path => f (path ⟨n, Nat.lt_succ_self n⟩)) x ω =
      weightedGenerationEndpoint φ n f x ω := by
  apply tsum_congr
  intro u
  by_cases hu : u.length = n
  · by_cases hs : surviveAlong ω [] u
    · simp [weightedPathGenerationTerm, weightedGenerationTerm, hu, hs,
        pathHistory_last]
    · simp [weightedPathGenerationTerm, weightedGenerationTerm, hu, hs]
  · simp [weightedPathGenerationTerm, weightedGenerationTerm, hu]

theorem pathGeneration_last
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    pathGeneration φ n
        (fun path => f (path ⟨n, Nat.lt_succ_self n⟩)) x ω =
      generationEndpoint φ n f x ω := by
  apply tsum_congr
  intro u
  by_cases hu : u.length = n
  · by_cases hs : surviveAlong ω [] u
    · simp [pathGenerationTerm, generationTerm, hu, hs, pathHistory_last]
    · simp [pathGenerationTerm, generationTerm, hu, hs]
  · simp [pathGenerationTerm, generationTerm, hu]

/-- The unweighted path sum is the weighted path sum after multiplying the
test by the reciprocal endpoint weight. -/
theorem pathGeneration_eq_weightedPathGeneration
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ENNReal)
    (x : ℝ) (ω : Combinatorics.Branching.StepField ι X) :
    pathGeneration φ n F x ω =
      weightedPathGeneration φ n
        (fun history => ENNReal.ofReal
          (Real.exp (history ⟨n, Nat.lt_succ_self n⟩ - x)) * F history)
        x ω := by
  apply tsum_congr
  intro u
  by_cases hu : u.length = n
  · by_cases hs : surviveAlong ω [] u
    · rw [pathGenerationTerm, weightedPathGenerationTerm,
        Set.indicator_of_mem, Set.indicator_of_mem]
      rotate_left
      · exact ⟨hu, hs⟩
      · exact ⟨hu, hs⟩
      rw [pathHistory_last φ n x ω u hu]
      rw [show x + pathPotential φ ω u - x = pathPotential φ ω u by ring]
      rw [← mul_assoc, ← ENNReal.ofReal_mul
        (le_of_lt (Real.exp_pos (-pathPotential φ ω u))), ← Real.exp_add]
      simp
    · simp [pathGenerationTerm, weightedPathGenerationTerm, hu, hs]
  · simp [pathGenerationTerm, weightedPathGenerationTerm, hu]

end ProbabilityTheory.BranchingRandomWalk.Spine
