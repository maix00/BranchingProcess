/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.Family.Path
public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching

/-!
# Path-count comparison under whole-family selection

## Public declarations

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `pathGeneration_selectFamily_le` proves `Zₙ(F, selectedField) ≤ Zₙ(F, field)`
  for every nonnegative path test and whole-family acceptance rule.
* `pathHistory_selectFamily_eq_of_survive` preserves every retained
  ancestral position, `Hₙ(selectedField,u)=Hₙ(field,u)`.
* `pathGenerationTerm_selectFamily_eq` and `pathGeneration_selectFamily_eq`
  identify the actual count with the original address sum multiplied by
  acceptance at every strict ancestor, `∏_(j<|u|) 1_A(field(u|j))`.
* `offspringFieldLaw_map_selectFamily` identifies the selected original
  independent field with the independent field of the selected family law.
* `lintegral_pathGeneration_selectFamily_le` compares expected path counts
  under that selected family law with those under the original law.

The coupling preserves the actual child marks and therefore every surviving
ancestral position. No boundary normalization, moment or finiteness of the
number of children is needed. In particular the family test may be `W≤K`;
its selected reproduction law is a probability without any reweighting.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching
open BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem pathGeneration_selectFamily_le {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (accepted : Set (Step ι X)) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (x : ℝ) (field : StepField ι X) :
    pathGeneration φ n F x (fun u => Step.selectFamily accepted (field u)) ≤
      pathGeneration φ n F x field := by
  induction n generalizing x field with
  | zero => simp only [pathGeneration_zero, le_refl]
  | succ n ih =>
    rw [pathGeneration_succ, pathGeneration_succ]
    by_cases h : field [] ∈ accepted
    · simp only [Step.selectFamily_of_mem h]
      apply tsum_le_tsum
      intro i
      by_cases hi : survive (field []) i
      · simp only [survivingPotentialTest, hi, ↓reduceIte]
        exact ih _ _ _
      · simp only [survivingPotentialTest, hi, ↓reduceIte, le_refl]
    · simp [Step.selectFamily_of_notMem h, survivingPotentialTest, survive]

/-- Every retained ancestral position agrees with the original field. -/
theorem pathHistory_selectFamily_eq_of_survive {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (A : Set (Step ι X)) (n : ℕ) (x : ℝ)
    (field : StepField ι X) (u : List ι)
    (hs : surviveAlong (fun q => Step.selectFamily A (field q)) [] u) :
    pathHistory φ n x (fun q => Step.selectFamily A (field q)) u =
      pathHistory φ n x field u := by
  funext k
  have hp := surviveAlong_prefix (fun q => Step.selectFamily A (field q))
    (u.take k) (u.drop k) (by simpa only [List.take_append_drop] using hs)
  change x + displaceWith φ (fun q => Step.selectFamily A (field q)) [] (u.take k) =
    x + displaceWith φ field [] (u.take k)
  rw [displaceWith_selectFamily_eq_of_survive φ A field [] (u.take k) hp]

/-- The selected contribution is exactly the original one with acceptance
imposed at every strict ancestor. The reproducing endpoint is not tested. -/
theorem pathGenerationTerm_selectFamily_eq {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (A : Set (Step ι X)) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (x : ℝ)
    (field : StepField ι X) (u : List ι) :
    pathGenerationTerm φ n F x u (fun q => Step.selectFamily A (field q)) =
      if ∀ j : Fin u.length, field (u.take j) ∈ A then
        pathGenerationTerm φ n F x u field else 0 := by
  have hiff := surviveAlong_selectFamily_iff A field [] u
  simp only [List.nil_append] at hiff
  by_cases ha : ∀ j : Fin u.length, field (u.take j) ∈ A
  · rw [ite_eq_left ha]
    by_cases hs : surviveAlong field [] u
    · have hsel := hiff.mpr ⟨hs, ha⟩
      have hh := pathHistory_selectFamily_eq_of_survive φ A n x field u hsel
      by_cases hu : u.length = n
      · simp [pathGenerationTerm, hu, hs, hsel, hh]
      · simp [pathGenerationTerm, hu]
    · have hsel : ¬surviveAlong (fun q => Step.selectFamily A (field q)) [] u :=
        fun h => hs (hiff.mp h).1
      simp [pathGenerationTerm, hs, hsel]
  · rw [ite_eq_right ha]
    have hsel : ¬surviveAlong (fun q => Step.selectFamily A (field q)) [] u :=
      fun h => ha (hiff.mp h).2
    simp [pathGenerationTerm, hsel]

/-- The actual whole-family selected count retains the family condition on
all strict ancestors of every contributing address. -/
theorem pathGeneration_selectFamily_eq {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (A : Set (Step ι X)) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (x : ℝ) (field : StepField ι X) :
    pathGeneration φ n F x (fun q => Step.selectFamily A (field q)) =
      ∑' u : Combinatorics.UlamHarris.TreeNode ι,
        if ∀ j : Fin u.length, field (u.take j) ∈ A then
          pathGenerationTerm φ n F x u field else 0 := by
  exact tsum_congr (fun u => pathGenerationTerm_selectFamily_eq φ A n F x field u)

theorem offspringFieldLaw_map_selectFamily {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    {accepted : Set (Step ι X)} (ha : MeasurableSet accepted) :
    (offspringFieldLaw μ).map (fun field u => Step.selectFamily accepted (field u)) =
      offspringFieldLaw (μ.map (Step.selectFamily accepted)) := by
  unfold offspringFieldLaw
  rw [← Measure.infinitePi_map_pi (μ := fun _ => μ)
    (f := fun _ => Step.selectFamily accepted)
    (hf := fun _ => Step.selectFamily_measurable ha)]

theorem lintegral_pathGeneration_selectFamily_le {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    {accepted : Set (Step ι X)} (ha : MeasurableSet accepted) (n : ℕ)
    {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) :
    (∫⁻ field, pathGeneration φ n F x field
      ∂offspringFieldLaw (μ.map (Step.selectFamily accepted))) ≤
      ∫⁻ field, pathGeneration φ n F x field ∂offspringFieldLaw μ := by
  have hm : Measurable (fun field : StepField ι X =>
      fun u => Step.selectFamily accepted (field u)) :=
    measurable_pi_iff.mpr (fun _ =>
      (Step.selectFamily_measurable ha).comp (measurable_pi_apply _))
  rw [← offspringFieldLaw_map_selectFamily μ ha,
    lintegral_map (pathGeneration_measurable φ n hF x) hm]
  exact lintegral_mono (pathGeneration_selectFamily_le φ accepted n F x)

end ProbabilityTheory.BranchingRandomWalk.Spine
