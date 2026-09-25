import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtree

/-!
# Exploration information and unused abstract branching subtrees

An exploration domain is bounded by the branching-step coordinates actually
inspected.  Any descendant address set disjoint from those coordinates remains
fresh under the product branching law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



@[instance_reducible] def branchingStepsOnSpace
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  ⨆ u ∈ s, branchingStepCoordinateSpace u

theorem branchingStepsOnSpace_mono
    {X : Type*} [MeasurableSpace X] {s t : Set 𝕍} (hst : s ⊆ t) :
    branchingStepsOnSpace (X := X) s ≤ branchingStepsOnSpace t := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem branchingStepsOnSpace_le
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    branchingStepsOnSpace (X := X) s ≤
      (inferInstance : MeasurableSpace (𝕍 → BranchingStep ℕ X)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  exact (measurable_pi_apply u).comap_le

theorem branchingStepsOnSpace_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (s t : Set 𝕍) (hdisj : Disjoint s t) :
    Indep (branchingStepsOnSpace s) (branchingStepsOnSpace t)
      (branchingStepFieldLaw μ) := by
  have hle : ∀ u : 𝕍, branchingStepCoordinateSpace (X := X) u ≤
      (inferInstance : MeasurableSpace (𝕍 → BranchingStep ℕ X)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle
    (branchingStep_coordinate_independent μ) hdisj

theorem branchingStepsOnSpace_descendant_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (explored : Set 𝕍) (root : 𝕍)
    (hfresh : Disjoint explored (branchingDescendantAddresses root)) :
    Indep (branchingStepsOnSpace explored)
      (branchingStepDescendantSpace root) (branchingStepFieldLaw μ) := by
  rw [branchingStepDescendantSpace_eq_iSup]
  exact branchingStepsOnSpace_independent μ explored
    (branchingDescendantAddresses root) hfresh

structure BranchingExplorationDomains
    (X : Type*) [MeasurableSpace X] where
  inspected : ℕ → Set 𝕍
  domain : ℕ → MeasurableSpace (𝕍 → BranchingStep ℕ X)
  domain_le : ∀ j, domain j ≤ branchingStepsOnSpace (inspected j)
  inspected_mono : Monotone inspected

theorem BranchingExplorationDomains.fresh_descendant_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ) (root : 𝕍)
    (hfresh : Disjoint (H.inspected j)
      (branchingDescendantAddresses root)) :
    Indep (H.domain j) (branchingStepDescendantSpace root)
      (branchingStepFieldLaw μ) := by
  apply indep_of_indep_of_le_left
    (branchingStepsOnSpace_descendant_independent μ
      (H.inspected j) root hfresh)
  exact H.domain_le j

theorem BranchingExplorationDomains.fresh_subtree_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ) (root : 𝕍)
    (hfresh : Disjoint (H.inspected j)
      (branchingDescendantAddresses root)) :
    Indep (H.domain j)
      (MeasurableSpace.comap (subtreeStepField root) inferInstance)
      (branchingStepFieldLaw μ) :=
  indep_of_indep_of_le_right
    (H.fresh_descendant_independent μ j root hfresh)
    (subtreeStepField_descendant_measurable root).comap_le

theorem selectedSubtreeStepField_measurable_of_measurable
    {X : Type*} [MeasurableSpace X]
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable chosen) :
    Measurable (selectedSubtreeStepField chosen) := by
  have hjoint : Measurable
      (fun p : 𝕍 × (𝕍 → BranchingStep ℕ X) =>
        subtreeStepField p.1 p.2) :=
    measurable_from_prod_countable_right subtreeStepField_measurable
  exact hjoint.comp (hchosen.prodMk measurable_id)

theorem BranchingExplorationDomains.selected_fresh_subtree_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω)))
    (A B : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[H.domain j] A) (hB : MeasurableSet B) :
    branchingStepFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      branchingStepFieldLaw μ A * branchingStepFieldLaw μ B := by
  let P := branchingStepFieldLaw μ
  let C := fun u => abstractSelectionCell chosen A u
  let D := fun u => C u ∩ subtreeStepField u ⁻¹' B
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (branchingStepsOnSpace_le _)) le_rfl
  have hCdomain (u : 𝕍) : MeasurableSet[H.domain j] (C u) :=
    hA.inter (hchosen (measurableSet_singleton u))
  have hCmeas (u : 𝕍) : MeasurableSet (C u) :=
    ((H.domain_le j).trans (branchingStepsOnSpace_le _)) _ (hCdomain u)
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
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains X) (j : ℕ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω))) :
    Indep (H.domain j)
      (MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance)
      (branchingStepFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (branchingStepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (branchingStepsOnSpace_le _)) le_rfl
  have hselected :=
    selectedSubtreeStepField_measurable_of_measurable chosen hchosenFull
  apply (indepSet_iff_measure_inter_eq_mul
    (((H.domain_le j).trans (branchingStepsOnSpace_le _)) _ hA)
    (hselected hB) (branchingStepFieldLaw μ)).2
  have hlaw : branchingStepFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = branchingStepFieldLaw μ B := by
    have hfactor := H.selected_fresh_subtree_event_factorization μ j
      chosen hchosen hfresh Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact H.selected_fresh_subtree_event_factorization μ j chosen
    hchosen hfresh A B hA hB

end ProbabilityTheory.BranchingRandomWalk
