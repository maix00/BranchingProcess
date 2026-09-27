import Probability.BranchingRandomWalk.Spine.Path.Basic

/-!
# Actual generation observables of ancestral paths

The sums range over all addresses and use the same realization event as the
endpoint observables. Empty generations contribute zero.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

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

end ProbabilityTheory.BranchingRandomWalk.Spine
