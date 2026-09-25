import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.Domains

/-!
# A fresh subtree selected from an exploration domain

A root chosen measurably from the exploration domain and always fresh for it
carries an independent subtree with the original field law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingStep MeasureTheory


theorem selectedSubtreeStepField_measurable_of_measurable
    {X : Type*} [MeasurableSpace X]
    (chosen : (𝕍 → Step ℕ X) → 𝕍)
    (hchosen : Measurable chosen) :
    Measurable (selectedSubtreeStepField chosen) := by
  have hjoint : Measurable
      (fun p : 𝕍 × (𝕍 → Step ℕ X) =>
        subtreeStepField p.1 p.2) :=
    measurable_from_prod_countable_right subtreeStepField_measurable
  exact hjoint.comp (hchosen.prodMk measurable_id)

theorem BranchingExplorationDomains.selected_fresh_subtree_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ)
    (chosen : (𝕍 → Step ℕ X) → 𝕍)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω)))
    (A B : Set (𝕍 → Step ℕ X))
    (hA : MeasurableSet[H.domain j] A) (hB : MeasurableSet B) :
    stepFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      stepFieldLaw μ A * stepFieldLaw μ B := by
  let P := stepFieldLaw μ
  let C := fun u => abstractSelectionCell chosen A u
  let D := fun u => C u ∩ subtreeStepField u ⁻¹' B
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (stepsOnSpace_le _)) le_rfl
  have hCdomain (u : 𝕍) : MeasurableSet[H.domain j] (C u) :=
    hA.inter (hchosen (measurableSet_singleton u))
  have hCmeas (u : 𝕍) : MeasurableSet (C u) :=
    ((H.domain_le j).trans (stepsOnSpace_le _)) _ (hCdomain u)
  have hDmeas (u : 𝕍) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeStepField_measurable u) hB)
  have hcell (u : 𝕍) : P (D u) = P (C u) * P B := by
    by_cases hu : Disjoint (H.inspected j) (branchingDescendantAddresses u)
    · have hind := H.fresh_subtree_independent μ j u hu
      have hpre : MeasurableSet[
          MeasurableSpace.comap (subtreeStepField u) inferInstance]
          (subtreeStepField u ⁻¹' B) := ⟨B, hB, rfl⟩
      have hfactor := (hind.indepSet_of_measurableSet
        (hCdomain u) hpre).measure_inter_eq_mul
      have hlaw : P (subtreeStepField u ⁻¹' B) = P B := by
        rw [← Measure.map_apply (subtreeStepField_measurable u) hB,
          subtreeStepField_law]
      rw [hlaw] at hfactor
      exact hfactor
    · have hempty : C u = ∅ := by
        ext ω
        simp only [C, abstractSelectionCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hchoose⟩
        exact hu (hchoose ▸ hfresh ω)
      simp [D, hempty]
  have hCpair : Pairwise (fun u v => Disjoint (C u) (C v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro ω hcu hcv
    exact huv (hcu.2.symm.trans hcv.2)
  have hDpair : Pairwise (fun u v => Disjoint (D u) (D v)) := by
    intro u v huv
    exact (hCpair huv).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ u, C u) = A := by
    ext ω
    simp [C, abstractSelectionCell]
  have hDunion : (⋃ u, D u) =
      A ∩ selectedSubtreeStepField chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, abstractSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedSubtreeStepField]
    constructor
    · rintro ⟨u, ⟨⟨hAω, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨chosen ω, ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' u, P (C u)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
        P (⋃ u, D u) := by rw [hDunion]
    _ = ∑' u, P (D u) := measure_iUnion hDpair hDmeas
    _ = ∑' u, P (C u) * P B := tsum_congr hcell
    _ = (∑' u, P (C u)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

theorem BranchingExplorationDomains.selected_fresh_subtree_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ)
    (chosen : (𝕍 → Step ℕ X) → 𝕍)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω))) :
    Indep (H.domain j)
      (MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance)
      (stepFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (stepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (stepsOnSpace_le _)) le_rfl
  have hselected :=
    selectedSubtreeStepField_measurable_of_measurable chosen hchosenFull
  apply (indepSet_iff_measure_inter_eq_mul
    (((H.domain_le j).trans (stepsOnSpace_le _)) _ hA)
    (hselected hB) (stepFieldLaw μ)).2
  have hlaw : stepFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = stepFieldLaw μ B := by
    have hfactor := H.selected_fresh_subtree_event_factorization μ j
      chosen hchosen hfresh Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact H.selected_fresh_subtree_event_factorization μ j chosen
    hchosen hfresh A B hA hB

end ProbabilityTheory.BranchingRandomWalk
