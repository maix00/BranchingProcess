/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization

/-!
# Law and independence of the stopped subtree vector

The stopped subtree vector is measurable, its law is the product of independent
copies of the original field, and it is independent of the stopping-time
σ-algebra.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem selectedSubtreeStepFieldVector_measurable_of_measurable
    {κ α X : Type*} [MeasurableSpace X]
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (hroots : Measurable roots)
    (hcount : (Set.range roots).Countable) :
    Measurable (selectedSubtreeStepFieldVector roots) := by
  apply measurable_pi_iff.mpr
  intro i
  have hcoord : (Set.range (fun ω => roots ω i)).Countable := by
    apply (hcount.image (fun r => r i)).mono
    rintro _ ⟨ω, rfl⟩
    exact ⟨roots ω, Set.mem_range_self ω, rfl⟩
  exact selectedSubtreeStepField_measurable_of_countable_range
    (fun ω => roots ω i) ((measurable_pi_apply i).comp hroots) hcoord

theorem stopped_selectedSubtreeStepFieldVector_law
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    (stepFieldLaw μ).map
        (selectedSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : κ => stepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull
      hcount)
    hB]
  have hfactor := stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ τ hτ roots hcount hfiber hdepth (fun ω _ => hinj ω) Set.univ B
      (by simp) hB
  simpa [hfinite] using hfactor

theorem stopped_selectedSubtreeStepFieldVector_independent
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap
        (selectedSubtreeStepFieldVector roots) inferInstance)
      (stepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull
      hcount
  apply (indep_iff_forall_indepSet (stepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB)
    (stepFieldLaw μ)).2
  have hlaw : stepFieldLaw μ
      (selectedSubtreeStepFieldVector roots ⁻¹' B) =
      (Measure.infinitePi (fun _ : κ => stepFieldLaw μ)) B := by
    rw [← Measure.map_apply hselected hB,
      stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots
        hroots hcount hfiber hdepth hinj]
  rw [hlaw]
  have hfactor := stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ τ hτ roots hcount hfiber hdepth (fun ω _ => hinj ω) A B hA hB
  simpa [hfinite] using hfactor

end ProbabilityTheory.BranchingRandomWalk
