/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.AddressFiltration
public import Probability.BranchingRandomWalk.Step.Position.Measurability
import MeasureTheory.Measure.Partition

/-!
# Subtrees selected from the explored field

## Public declarations

For a measurable selector `chosen` whose range is countable and whose values
have fixed depth `n`, `selectedSubtreeStepField chosen` is independent of the
generation-`n` filtration and has the original step-field law. For measurable
`A` in that flow and measurable `B`, the factorization is
$P(A\cap F^{-1}(B))=P(A)P(B)$, where
$F=\operatorname{selectedSubtreeStepField}(chosen)$ and
$P=\operatorname{offspringFieldLaw}(\mu)$.

- `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField` defines
  the field $F(\omega)(v)=\omega(\operatorname{chosen}(\omega)\mathbin{++}v)$.
- `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField_measurable_of_countable_range`
  and `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField_measurable`
  prove measurability from a countable range, respectively from generation
  filtration measurability.
- `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField_event_factorization`
  proves the displayed identity for $A\in\mathcal F_n$ and measurable $B$,
  provided $|\operatorname{chosen}(\omega)|=n$ for every $\omega$.
- `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField_law` proves
  $P.map(F)=P$, where $P=\operatorname{offspringFieldLaw}(\mu)$.
- `ProbabilityTheory.BranchingRandomWalk.selectedSubtreeStepField_independent`
  states independence of $F$ from the generation-`n` filtration.
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



def selectedSubtreeStepField {α X : Type*}
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (ω : TreeNode α → Step α X) :
    TreeNode α → Step α X :=
  subtreeStepField (chosen ω) ω

/-- A dynamically selected subtree is measurable when the selector is
measurable and has countable range. This is the actual requirement; the whole
child-slot type need not be countable. -/
theorem selectedSubtreeStepField_measurable_of_countable_range
    {α X : Type*} [MeasurableSpace X]
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable chosen)
    (hcount : (Set.range chosen).Countable) :
    Measurable (selectedSubtreeStepField chosen) := by
  let S : Set (TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hjoint : Measurable
      (fun p : S × (TreeNode α → Step α X) =>
        subtreeStepField p.1.1 p.2) :=
    measurable_from_prod_countable_right fun u =>
      subtreeStepField_measurable u.1
  have hchosenS : Measurable (fun ω =>
      (⟨chosen ω, Set.mem_range_self ω⟩ : S)) :=
    hchosen.subtype_mk
  exact hjoint.comp (hchosenS.prodMk measurable_id)

theorem selectedSubtreeStepField_measurable
    {α X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable) :
    Measurable (selectedSubtreeStepField chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  exact selectedSubtreeStepField_measurable_of_countable_range chosen hselect
    hcount

private theorem abstractSelectionCell_measurable
    {α X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (A : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (u : TreeNode α) :
    MeasurableSet[generationFiltration (M := Step α X) n]
      (abstractSelectionCell chosen A u) :=
  hA.inter (hchosen (measurableSet_singleton u))

private theorem abstractSelectionCell_measure_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) (u : TreeNode α) :
    offspringFieldLaw μ (abstractSelectionCell chosen A u ∩
      subtreeStepField u ⁻¹' B) =
      offspringFieldLaw μ (abstractSelectionCell chosen A u) *
        offspringFieldLaw μ B := by
  by_cases hu : u.length = n
  · apply fixed_subtreeStepField_event_factorization μ u _ _ _ hB
    rw [hu]
    exact abstractSelectionCell_measurable n chosen hchosen A hA u
  · have hempty : abstractSelectionCell chosen A u = ∅ := by
      ext ω
      simp only [abstractSelectionCell, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hchosenω⟩
      exact hu (by simpa [hchosenω] using hdepth ω)
    simp [hempty]

theorem selectedSubtreeStepField_event_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) :
    offspringFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      offspringFieldLaw μ A * offspringFieldLaw μ B := by
  let P := offspringFieldLaw μ
  let S : Set (TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun u : S => abstractSelectionCell chosen A u.1
  let D := fun u : S => C u ∩ subtreeStepField u.1 ⁻¹' B
  have hCmeas (u : S) : MeasurableSet (C u) :=
    (generationFiltration (M := Step α X) |>.le n) _
      (abstractSelectionCell_measurable n chosen hchosen A hA u.1)
  have hDmeas (u : S) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeStepField_measurable u.1) hB)
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
    simp only [Set.mem_iUnion, C, abstractSelectionCell, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hAω, _⟩
      exact hAω
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
    P (A ∩ selectedSubtreeStepField chosen ⁻¹' B) = P (⋃ u, D u) := by
      rw [hDunion]
    _ = P (⋃ u, C u) * P B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (P B)
        hCmeas hDmeas hCpair hDpair (fun u =>
          abstractSelectionCell_measure_factorization μ n chosen hchosen
            hdepth A B hA hB u.1)
    _ = P A * P B := by rw [hCunion]

theorem selectedSubtreeStepField_law
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    (offspringFieldLaw μ).map (selectedSubtreeStepField chosen) =
      offspringFieldLaw μ := by
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepField_measurable n chosen hchosen hcount) hB]
  have h := selectedSubtreeStepField_event_factorization μ n chosen hchosen
    hcount hdepth Set.univ B (by simp) hB
  simpa using h

theorem selectedSubtreeStepField_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (TreeNode α → Step α X) → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance)
      (offspringFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (offspringFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (M := Step α X) |>.le n) _ hA)
    ((selectedSubtreeStepField_measurable n chosen hchosen hcount) hB)
    (offspringFieldLaw μ)).2
  have hmap : offspringFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = offspringFieldLaw μ B := by
    rw [← Measure.map_apply
      (selectedSubtreeStepField_measurable n chosen hchosen hcount) hB,
      selectedSubtreeStepField_law μ n chosen hchosen hcount hdepth]
  rw [hmap]
  exact selectedSubtreeStepField_event_factorization μ n chosen hchosen
    hcount hdepth A B hA hB

end ProbabilityTheory.BranchingRandomWalk

end
