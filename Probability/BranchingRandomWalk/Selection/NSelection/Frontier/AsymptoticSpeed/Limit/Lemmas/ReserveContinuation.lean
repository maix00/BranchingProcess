/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Splits

/-!
# Fresh continuation at the restart deadline

## Internal proof declarations

* `measurableSet_splitCount_at_stopped_time`: the event that fewer than
  $K$ splits precede the successful trial is measurable at its completion.
* `badRestart_reserveContinuation_factorization`: let $E$ be success
  among the first $K$ trials by time $T$ and let $W$ be the subtree rooted at
  the continuation particle at $T$. The subtree is independent of
  $\mathcal F_T$, and
  $P(E^c\cap W^{-1}(B))=P(E^c)Q(B)$ for each measurable $B$, where $Q$
  is the original one-root offspring-field law.

This checks the independence input of the first-moment speed reduction in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Lemma 4.2 and the subsequent
reserve-continuation argument.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Coupling
open SelectedPath SelectedPath.GrowthTrial

local notation "Ωf" => RootIndexed.StepField (ℕ ⊕ ℕ) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := ℕ ⊕ ℕ) (α := ℕ) (X := ℝ)

lemma measurableSet_splitCount_at_stopped_time
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    {τ : Ωf → WithTop ℕ} (hτ : IsStoppingTime 𝔽 τ) (d K : ℕ) :
    MeasurableSet[hτ.measurableSpace] {ω | splitCount R 0 ((τ ω).untopD 0 - (d + 1))
      (RootIndexed.StepField.left ω) < K} := by
  let A : Set Ωf := {ω | splitCount R 0 ((τ ω).untopD 0 - (d + 1))
    (RootIndexed.StepField.left ω) < K}
  let B (n : ℕ) : Set Ωf := {ω | splitCount R 0 (n - (d + 1))
    (RootIndexed.StepField.left ω) < K}
  have hB (n : ℕ) : MeasurableSet[𝔽 n] (B n) := by
    let k := n - (d + 1)
    have hleft := RootIndexed.StepField.reindex_filtration_measurable
      (α := ℕ) (X := ℝ) (Sum.inl : ℕ → ℕ ⊕ ℕ) k
    exact (𝔽).mono (Nat.sub_le ..) _
      (((splitCount_measurable R hR (0 : ℕ) k).comp hleft) (measurableSet_Iio (a := K)))
  have heq : A = ⋃ s : WithTop ℕ, B (s.untopD 0) ∩ {ω | τ ω = s} := by
    ext ω
    simp only [A, B, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨τ ω, h, rfl⟩, fun ⟨s, h, he⟩ => he.symm ▸ h⟩
  change MeasurableSet[hτ.measurableSpace] A
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  cases s with
  | top =>
    exact ((hτ.le_measurableSpace_of_const_le (i := 0) fun _ => bot_le) _ (hB 0)).inter
      (hτ.measurable (measurableSet_singleton _))
  | coe n =>
    have he : A ∩ {ω | τ ω = (n : WithTop ℕ)} = B n ∩ {ω | τ ω = (n : WithTop ℕ)} := by
      ext ω
      simp only [A, B, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact and_congr_left fun h => by rw [h]; rfl
    change MeasurableSet[hτ.measurableSpace] (B n ∩ {ω | τ ω = (n : WithTop ℕ)})
    rw [← he]
    apply (hτ.measurableSet_inter_eq_iff _ n).2
    exact he.symm ▸ (hB n).inter (hτ.measurableSet_eq n)

/-- The future of the selected path particle at the deadline factors from
the actual failure event on the original marked tree. -/
lemma badRestart_reserveContinuation_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration K T : ℕ)
    (B : Set (RootIndexed.StepField Unit ℕ ℝ)) (hB : MeasurableSet B) :
    let τ := Completion.time R growth hR hgrowth lower upper duration (0 : ℕ)
    let E : Set Ωf := {ω | splitCount R 0 ((τ ω).untopD 0 - (duration + 1))
      (RootIndexed.StepField.left ω) < K} ∩ {ω | τ ω ≤ (T : WithTop ℕ)}
    let chosen (ω : Ωf) (_ : Unit) : (ℕ ⊕ ℕ) × TreeNode ℕ :=
      (Sum.inl 0, selectedPath R 0 T (RootIndexed.StepField.left ω))
    let W := RootIndexed.selectedSubtreeStepFieldVector chosen
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let Q := RootIndexed.stepFieldLaw (Root := Unit) μ
    Indep ((𝔽) T) (MeasurableSpace.comap W inferInstance) P ∧
      P (Eᶜ ∩ W ⁻¹' B) = P Eᶜ * Q B := by
  intro τ E chosen W P Q
  have hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration (0 : ℕ)
  have hE : MeasurableSet[(𝔽) T] E :=
    (measurableSet_splitCount_at_stopped_time R hR hτ duration K).2 T
  have hleft :
      @Measurable Ωf (RootIndexed.StepField ℕ ℕ ℝ) ((𝔽) T)
        (RootIndexed.stepFiltration (Root := ℕ) (α := ℕ) (X := ℝ) T)
        RootIndexed.StepField.left :=
    RootIndexed.StepField.reindex_filtration_measurable Sum.inl T
  have hpath : Measurable[(𝔽) T] (fun ω : Ωf =>
      selectedPath R 0 T (RootIndexed.StepField.left ω)) :=
    (SelectedPath.adapted R hR (0 : ℕ) T).comp hleft
  have hfiber (roots : Unit → (ℕ ⊕ ℕ) × TreeNode ℕ) :
      MeasurableSet[(𝔽) T] {ω | chosen ω = roots} := by
    have heq : {ω | chosen ω = roots} = {ω | chosen ω () = roots ()} := by
      ext ω
      exact ⟨fun h => congrFun h (), fun h => funext fun u => by cases u; exact h⟩
    rw [heq]
    by_cases hroot : (roots ()).1 = Sum.inl 0
    · have hcell : {ω | chosen ω () = roots ()} =
          {ω | selectedPath R 0 T (RootIndexed.StepField.left ω) = (roots ()).2} := by
        ext ω
        simp [chosen, Prod.ext_iff, hroot]
      rw [hcell]
      exact hpath (measurableSet_singleton _)
    · have hcell : {ω | chosen ω () = roots ()} = ∅ := by
        ext ω
        simp [chosen, Prod.ext_iff, Ne.symm hroot]
      rw [hcell]
      exact @MeasurableSet.empty Ωf ((𝔽) T)
  have hdepth (ω : Ωf) (i : Unit) : (chosen ω i).2.length = T :=
    SelectedPath.depth R 0 (RootIndexed.StepField.left ω) T
  have hinj (ω : Ωf) : Function.Injective (chosen ω) :=
    fun _ _ _ => Subsingleton.elim _ _
  exact ⟨RootIndexed.selectedSubtreeStepFieldVector_independent μ chosen
      (Set.to_countable _) hfiber hdepth hinj,
    RootIndexed.selectedSubtreeStepFieldVector_event_factorization μ chosen
      (Set.to_countable _) hfiber hdepth hinj Eᶜ B hE.compl hB⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
