import ThesisSpeed.Probability.Genealogy.Exploration.Abstract.DomainFlow
import ThesisSpeed.Probability.Branching.Position.Measurability

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedSubtreeStepField {X : Type*}
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (ω : 𝕍 → BranchingStep ℕ X) :
    𝕍 → BranchingStep ℕ X :=
  subtreeStepField (chosen ω) ω

theorem selectedSubtreeStepField_measurable
    {X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen) :
    Measurable (selectedSubtreeStepField chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono
      (generationFiltration (M := BranchingStep ℕ X) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : 𝕍 × (𝕍 → BranchingStep ℕ X) =>
        subtreeStepField p.1 p.2) :=
    measurable_from_prod_countable_right
      (subtreeStepField_measurable (X := X))
  exact hjoint.comp (hselect.prodMk measurable_id)

def abstractSelectionCell {X : Type*}
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (A : Set (𝕍 → BranchingStep ℕ X)) (u : 𝕍) :
    Set (𝕍 → BranchingStep ℕ X) :=
  A ∩ {ω | chosen ω = u}

theorem abstractSelectionCell_measurable
    {X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen)
    (A : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (M := BranchingStep ℕ X) n] A)
    (u : 𝕍) :
    MeasurableSet[generationFiltration (M := BranchingStep ℕ X) n]
      (abstractSelectionCell chosen A u) :=
  hA.inter (hchosen (measurableSet_singleton u))

theorem abstractSelectionCell_measure_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (M := BranchingStep ℕ X) n] A)
    (hB : MeasurableSet B) (u : 𝕍) :
    branchingStepFieldLaw μ (abstractSelectionCell chosen A u ∩
      subtreeStepField u ⁻¹' B) =
      branchingStepFieldLaw μ (abstractSelectionCell chosen A u) *
        branchingStepFieldLaw μ B := by
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
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (M := BranchingStep ℕ X) n] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      branchingStepFieldLaw μ A * branchingStepFieldLaw μ B := by
  let P := branchingStepFieldLaw μ
  let C := fun u => abstractSelectionCell chosen A u
  let D := fun u => C u ∩ subtreeStepField u ⁻¹' B
  have hCmeas (u : 𝕍) : MeasurableSet (C u) :=
    (generationFiltration (M := BranchingStep ℕ X) |>.le n) _
      (abstractSelectionCell_measurable n chosen hchosen A hA u)
  have hDmeas (u : 𝕍) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeStepField_measurable u) hB)
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
    simp only [Set.mem_iUnion, C, abstractSelectionCell, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hAω, _⟩
      exact hAω
    · intro hAω
      exact ⟨chosen ω, hAω, rfl⟩
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
    P (A ∩ selectedSubtreeStepField chosen ⁻¹' B) = P (⋃ u, D u) := by
      rw [hDunion]
    _ = ∑' u, P (D u) := measure_iUnion hDpair hDmeas
    _ = ∑' u, P (C u) * P B := by
      apply tsum_congr
      intro u
      exact abstractSelectionCell_measure_factorization μ n chosen hchosen
        hdepth A B hA hB u
    _ = (∑' u, P (C u)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

theorem selectedSubtreeStepField_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    (branchingStepFieldLaw μ).map (selectedSubtreeStepField chosen) =
      branchingStepFieldLaw μ := by
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepField_measurable n chosen hchosen) hB]
  have h := selectedSubtreeStepField_event_factorization μ n chosen hchosen
    hdepth Set.univ B (by simp) hB
  simpa using h

theorem selectedSubtreeStepField_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Indep (generationFiltration (M := BranchingStep ℕ X) n)
      (MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance)
      (branchingStepFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (branchingStepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (M := BranchingStep ℕ X) |>.le n) _ hA)
    ((selectedSubtreeStepField_measurable n chosen hchosen) hB)
    (branchingStepFieldLaw μ)).2
  have hmap : branchingStepFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = branchingStepFieldLaw μ B := by
    rw [← Measure.map_apply
      (selectedSubtreeStepField_measurable n chosen hchosen) hB,
      selectedSubtreeStepField_law μ n chosen hchosen hdepth]
  rw [hmap]
  exact selectedSubtreeStepField_event_factorization μ n chosen hchosen
    hdepth A B hA hB

end ThesisSpeed
