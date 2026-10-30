/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Factorization
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.SelectedSubtreeVector

/-!
# Law and independence of the stopped subtree vector

## Public declarations

In namespace `ProbabilityTheory.BranchingRandomWalk`, the public declarations
are:

- `stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots hroots hcount hfiber hdepth hinj`
  states that, for an everywhere-finite stopping generation and a stopped-
  measurable, countably ranged, depth-matched, injective root family,
  \[
    \nu.\operatorname{map}(\Phi)
      =\operatorname{Measure.infinitePi}
        (i:\kappa\mapsto\nu),\qquad
    \nu=\operatorname{offspringFieldLaw}(\mu),
  \]
  where $\Phi$ is the selected subtree-vector map.
- `stopped_selectedSubtreeStepFieldVector_independent μ τ hτ hfinite roots hroots hcount hfiber hdepth hinj`
  states independence of the stopping-time $\sigma$-algebra and the selected
  subtree-vector field under the original step-field law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


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
    (offspringFieldLaw μ).map
        (selectedSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : κ => offspringFieldLaw μ) := by
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
      (offspringFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull
      hcount
  apply (indep_iff_forall_indepSet (offspringFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB)
    (offspringFieldLaw μ)).2
  have hlaw : offspringFieldLaw μ
      (selectedSubtreeStepFieldVector roots ⁻¹' B) =
      (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
    rw [← Measure.map_apply hselected hB,
      stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots
        hroots hcount hfiber hdepth hinj]
  rw [hlaw]
  have hfactor := stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ τ hτ roots hcount hfiber hdepth (fun ω _ => hinj ω) A B hA hB
  simpa [hfinite] using hfactor

end ProbabilityTheory.BranchingRandomWalk

end
