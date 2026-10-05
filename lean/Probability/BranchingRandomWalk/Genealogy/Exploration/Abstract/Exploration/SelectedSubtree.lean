/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.Domains

/-!
# A fresh subtree selected from an exploration domain

A root chosen measurably from the exploration domain and always fresh for it
carries an independent subtree with the original field law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem selectedSubtreeStepField_measurable_of_measurable
    {α X : Type*} [MeasurableSpace X]
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable chosen)
    (hcount : (Set.range chosen).Countable) :
    Measurable (selectedSubtreeStepField chosen) :=
  selectedSubtreeStepField_measurable_of_countable_range chosen hchosen hcount

theorem BranchingExplorationDomains.selected_fresh_subtree_event_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[H.domain j] chosen)
    (hcount : (Set.range chosen).Countable)
    (hfresh : ∀ ω, Disjoint (H.inspected j)
      (branchingDescendantAddresses (chosen ω)))
    (A B : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[H.domain j] A) (hB : MeasurableSet B) :
    stepFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      stepFieldLaw μ A * stepFieldLaw μ B := by
  let P := stepFieldLaw μ
  let S : Set (TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun u : S => abstractSelectionCell chosen A u.1
  let D := fun u : S => C u ∩ subtreeStepField u.1 ⁻¹' B
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (stepsOnSpace_le _)) le_rfl
  have hCdomain (u : S) : MeasurableSet[H.domain j] (C u) :=
    hA.inter (hchosen (measurableSet_singleton u.1))
  have hCmeas (u : S) : MeasurableSet (C u) :=
    ((H.domain_le j).trans (stepsOnSpace_le _)) _ (hCdomain u)
  have hDmeas (u : S) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeStepField_measurable u.1) hB)
  have hcell (u : S) : P (D u) = P (C u) * P B := by
    by_cases hu : Disjoint (H.inspected j) (branchingDescendantAddresses u.1)
    · have hind := H.fresh_subtree_independent μ j u.1 hu
      have hpre : MeasurableSet[
          MeasurableSpace.comap (subtreeStepField u.1) inferInstance]
          (subtreeStepField u.1 ⁻¹' B) := ⟨B, hB, rfl⟩
      have hfactor := (hind.indepSet_of_measurableSet
        (hCdomain u) hpre).measure_inter_eq_mul
      have hlaw : P (subtreeStepField u ⁻¹' B) = P B := by
        rw [← Measure.map_apply (subtreeStepField_measurable u.1) hB,
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
    exact huv (Subtype.ext (hcu.2.symm.trans hcv.2))
  have hDpair : Pairwise (fun u v => Disjoint (D u) (D v)) := by
    intro u v huv
    exact (hCpair huv).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ u, C u) = A := by
    ext ω
    simp only [Set.mem_iUnion, C, abstractSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, hAω, _⟩; exact hAω
    · intro hAω
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, hAω, rfl⟩
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
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩,
        ⟨⟨hAω, rfl⟩, hBω⟩⟩
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
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (H : BranchingExplorationDomains α X) (j : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[H.domain j] chosen)
    (hcount : (Set.range chosen).Countable)
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
    selectedSubtreeStepField_measurable_of_measurable chosen hchosenFull hcount
  apply (indepSet_iff_measure_inter_eq_mul
    (((H.domain_le j).trans (stepsOnSpace_le _)) _ hA)
    (hselected hB) (stepFieldLaw μ)).2
  have hlaw : stepFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = stepFieldLaw μ B := by
    have hfactor := H.selected_fresh_subtree_event_factorization μ j
      chosen hchosen hcount hfresh Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact H.selected_fresh_subtree_event_factorization μ j chosen
    hchosen hcount hfresh A B hA hB

end ProbabilityTheory.BranchingRandomWalk

end
