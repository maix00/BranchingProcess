/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.Domains
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.SelectedSubtree
import MeasureTheory.Measure.Partition

/-!
# A fresh subtree selected from an exploration domain

## Public declarations

A root chosen measurably from the exploration domain, with countable range,
and whose descendant coordinates are disjoint from the inspected set for
every outcome carries an independent subtree with the original field law.

- `BranchingExplorationDomains.selected_fresh_subtree_event_factorization`
  states `P(A ∩ F⁻¹(B)) = P(A) P(B)` for a domain-measurable event `A` and
  measurable subtree event `B`, when the selector has countable range and
  every selected descendant set is disjoint from the inspected coordinates.
- `BranchingExplorationDomains.selected_fresh_subtree_independent` states
  independence of the selected subtree field from the exploration domain.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

private def abstractSelectionCell {α X : Type*}
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (A : Set (TreeNode α → Step α X)) (u : TreeNode α) :
    Set (TreeNode α → Step α X) :=
  A ∩ {ω | chosen ω = u}


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
    offspringFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      offspringFieldLaw μ A * offspringFieldLaw μ B := by
  let P := offspringFieldLaw μ
  let S : Set (TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun u : S => abstractSelectionCell chosen A u.1
  let D := fun u : S => C u ∩ subtreeStepField u.1 ⁻¹' B
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
  calc
    P (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
        P (⋃ u, D u) := by rw [hDunion]
    _ = P (⋃ u, C u) * P B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (P B)
        hCmeas hDmeas hCpair hDpair hcell
    _ = P A * P B := by rw [hCunion]

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
      (offspringFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (offspringFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (stepsOnSpace_le _)) le_rfl
  have hselected :=
    selectedSubtreeStepField_measurable_of_countable_range chosen hchosenFull hcount
  apply (indepSet_iff_measure_inter_eq_mul
    (((H.domain_le j).trans (stepsOnSpace_le _)) _ hA)
    (hselected hB) (offspringFieldLaw μ)).2
  have hlaw : offspringFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = offspringFieldLaw μ B := by
    have hfactor := H.selected_fresh_subtree_event_factorization μ j
      chosen hchosen hcount hfresh Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact H.selected_fresh_subtree_event_factorization μ j chosen
    hchosen hcount hfresh A B hA hB

end ProbabilityTheory.BranchingRandomWalk

end
