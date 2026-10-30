/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.SelectedSubtree
import MeasureTheory.Measure.Partition

/-!
# Joint branching after a measurable frontier-family selection

## Public declarations

An arbitrarily indexed family of distinct generation-`n` addresses may be
selected from the generation filtration. The selected descendant step fields
are fresh, independent copies of the original pre-sampled field. The proof
only requires the random family itself to have countable range.

- `selectedSubtreeStepFieldVector chosen field` is the random family
  $V(\omega)(i,v)=\omega(\operatorname{chosen}(\omega)(i)\mathbin{++}v)$.
  `selectedSubtreeStepFieldVector_measurable_of_measurable` proves
  measurability when the root-family map is measurable with countable range;
  `selectedSubtreeStepFieldVector_measurable` specializes this to a family
  measurable at generation `n`.
- `selectedSubtreeStepFieldVector_event_factorization` gives, for a past
  event $A\in\mathcal F_n$ and measurable vector event $B$,
  $\mathbb P(A\cap V^{-1}(B))=\mathbb P(A)\,\mathbb P^{\otimes\kappa}(B)$,
  when the selected roots are distinct and have depth $n$.
- `selectedSubtreeStepFieldVector_law` identifies the vector law with the
  product law, $(\operatorname{offspringFieldLaw}(\mu)).\operatorname{map}(V)
  =\operatorname{Measure.infinitePi}(i\mapsto\operatorname{offspringFieldLaw}(\mu))$.
  `selectedSubtreeStepFieldVector_independent` states independence of $V$
  from the generation-`n` filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def selectedSubtreeStepFieldVector {κ α X : Type*}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (ω : TreeNode α → Step α X) :
    κ → TreeNode α → Step α X :=
  subtreeStepFieldVector (chosen ω) ω

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

theorem selectedSubtreeStepFieldVector_measurable
    {κ α X : Type*} [MeasurableSpace X] {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable) :
    Measurable (selectedSubtreeStepFieldVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  exact selectedSubtreeStepFieldVector_measurable_of_measurable
    chosen hselect hcount

private def abstractVectorSelectionCell {κ α X : Type*}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (roots : κ → TreeNode α) : Set (TreeNode α → Step α X) :=
  A ∩ {ω | chosen ω = roots}

private theorem abstractVectorSelectionCell_measurable
    {κ α X : Type*} [MeasurableSpace X] {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (A : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (roots : κ → TreeNode α)
    (hfiber : MeasurableSet[generationFiltration (M := Step α X) n]
      {ω | chosen ω = roots}) :
    MeasurableSet[generationFiltration (M := Step α X) n]
      (abstractVectorSelectionCell chosen A roots) :=
  hA.inter hfiber

private theorem abstractVectorSelectionCell_measure_factorization
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) (roots : κ → TreeNode α)
    (hfiber : MeasurableSet[generationFiltration (M := Step α X) n]
      {ω | chosen ω = roots}) :
    offspringFieldLaw μ (abstractVectorSelectionCell chosen A roots ∩
      subtreeStepFieldVector roots ⁻¹' B) =
      offspringFieldLaw μ (abstractVectorSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
  by_cases hr : ∃ ω, chosen ω = roots
  · obtain ⟨ω, hw⟩ := hr
    have hlen : ∀ i, (roots i).length = n := by
      intro i
      simpa [← hw] using hdepth ω i
    have hroots_inj : Function.Injective roots := by
      simpa [← hw] using hinj ω
    exact fixed_subtreeStepFieldVector_event_factorization μ roots hlen
      hroots_inj _ _
      (abstractVectorSelectionCell_measurable chosen A hA roots hfiber) hB
  · have hempty : abstractVectorSelectionCell chosen A roots = ∅ := by
      ext ω
      simp only [abstractVectorSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hw⟩
      exact hr ⟨ω, hw⟩
    simp [hempty]

theorem selectedSubtreeStepFieldVector_event_factorization
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[generationFiltration
      (M := Step α X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) :
    offspringFieldLaw μ
        (A ∩ selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      offspringFieldLaw μ A *
        (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
  let P := offspringFieldLaw μ
  let Q := Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)
  let S : Set (κ → TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun roots : S => abstractVectorSelectionCell chosen A roots.1
  let D := fun roots : S => C roots ∩ subtreeStepFieldVector roots.1 ⁻¹' B
  have hCmeas (roots : S) : MeasurableSet (C roots) :=
    (generationFiltration (M := Step α X) |>.le n) _
      (abstractVectorSelectionCell_measurable chosen A hA roots.1
        (hfiber roots.1))
  have hDmeas (roots : S) : MeasurableSet (D roots) :=
    (hCmeas roots).inter ((subtreeStepFieldVector_measurable roots.1) hB)
  have hCpair : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro ω hcr hcs
    exact hrs (Subtype.ext (hcr.2.symm.trans hcs.2))
  have hDpair : Pairwise (fun r s => Disjoint (D r) (D s)) := by
    intro r s hrs
    exact (hCpair hrs).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ roots, C roots) = A := by
    ext ω
    simp only [Set.mem_iUnion, C, abstractVectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨roots, hAω, _⟩
      exact hAω
    · intro hAω
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, hAω, rfl⟩
  have hDunion : (⋃ roots, D roots) =
      A ∩ selectedSubtreeStepFieldVector chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, abstractVectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedSubtreeStepFieldVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAω, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩,
        ⟨⟨hAω, rfl⟩, hBω⟩⟩
  calc
    P (A ∩ selectedSubtreeStepFieldVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = P (⋃ roots, C roots) * Q B :=
      measure_iUnion_eq_mul_of_disjoint_factor P C D (Q B)
        hCmeas hDmeas hCpair hDpair (fun roots =>
          abstractVectorSelectionCell_measure_factorization μ chosen
            hdepth hinj A B hA hB roots.1 (hfiber roots.1))
    _ = P A * Q B := by rw [hCunion]

theorem selectedSubtreeStepFieldVector_law
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[generationFiltration
      (M := Step α X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    (offspringFieldLaw μ).map (selectedSubtreeStepFieldVector chosen) =
      Measure.infinitePi (fun _ : κ => offspringFieldLaw μ) := by
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepFieldVector_measurable chosen hchosen hcount) hB]
  have h := selectedSubtreeStepFieldVector_event_factorization μ chosen
    hcount hfiber hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selectedSubtreeStepFieldVector_independent
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : (TreeNode α → Step α X) → κ → TreeNode α)
    (hchosen : Measurable[
      generationFiltration (M := Step α X) n] chosen)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[generationFiltration
      (M := Step α X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (selectedSubtreeStepFieldVector chosen)
        inferInstance) (offspringFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (offspringFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (M := Step α X) |>.le n) _ hA)
    ((selectedSubtreeStepFieldVector_measurable chosen hchosen hcount) hB)
    (offspringFieldLaw μ)).2
  have hmap : offspringFieldLaw μ
      (selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : κ => offspringFieldLaw μ)) B := by
    rw [← Measure.map_apply
      (selectedSubtreeStepFieldVector_measurable chosen hchosen hcount) hB,
      selectedSubtreeStepFieldVector_law μ chosen hchosen hcount hfiber
        hdepth hinj]
  rw [hmap]
  exact selectedSubtreeStepFieldVector_event_factorization μ chosen
    hcount hfiber hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk
