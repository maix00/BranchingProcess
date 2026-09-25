import ThesisSpeed.Probability.Branching.AbstractJointSubtrees

/-!
# Joint branching after a measurable finite frontier selection

A finite vector of distinct generation-`n` addresses may be selected from the
generation domain flow.  The selected descendant step fields are fresh,
independent copies of the original pre-sampled field.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedSubtreeStepFieldVector {X : Type*} {k : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (ω : TreeNode → BranchingStep ℕ X) :
    Fin k → TreeNode → BranchingStep ℕ X :=
  subtreeStepFieldVector (chosen ω) ω

theorem selectedSubtreeStepFieldVector_measurable
    {X : Type*} [MeasurableSpace X] {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen) :
    Measurable (selectedSubtreeStepFieldVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono
      (generationFiltration (Mark := BranchingStep ℕ X) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : (Fin k → TreeNode) × (TreeNode → BranchingStep ℕ X) =>
        subtreeStepFieldVector p.1 p.2) :=
    measurable_from_prod_countable_right subtreeStepFieldVector_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

def abstractVectorSelectionCell {X : Type*} {k : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (A : Set (TreeNode → BranchingStep ℕ X))
    (roots : Fin k → TreeNode) : Set (TreeNode → BranchingStep ℕ X) :=
  A ∩ {ω | chosen ω = roots}

theorem abstractVectorSelectionCell_measurable
    {X : Type*} [MeasurableSpace X] {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (A : Set (TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (Mark := BranchingStep ℕ X) n] A)
    (roots : Fin k → TreeNode) :
    MeasurableSet[generationFiltration (Mark := BranchingStep ℕ X) n]
      (abstractVectorSelectionCell chosen A roots) :=
  hA.inter (hchosen (measurableSet_singleton roots))

theorem abstractVectorSelectionCell_measure_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (TreeNode → BranchingStep ℕ X))
    (B : Set (Fin k → TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (Mark := BranchingStep ℕ X) n] A)
    (hB : MeasurableSet B) (roots : Fin k → TreeNode) :
    branchingStepFieldLaw μ (abstractVectorSelectionCell chosen A roots ∩
      subtreeStepFieldVector roots ⁻¹' B) =
      branchingStepFieldLaw μ (abstractVectorSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  by_cases hr : ∃ ω, chosen ω = roots
  · obtain ⟨ω, hw⟩ := hr
    have hlen : ∀ i, (roots i).length = n := by
      intro i
      simpa [← hw] using hdepth ω i
    have hroots_inj : Function.Injective roots := by
      simpa [← hw] using hinj ω
    exact fixed_subtreeStepFieldVector_event_factorization μ roots hlen
      hroots_inj _ _
      (abstractVectorSelectionCell_measurable chosen hchosen A hA roots) hB
  · have hempty : abstractVectorSelectionCell chosen A roots = ∅ := by
      ext ω
      simp only [abstractVectorSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hw⟩
      exact hr ⟨ω, hw⟩
    simp [hempty]

theorem selectedSubtreeStepFieldVector_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (TreeNode → BranchingStep ℕ X))
    (B : Set (Fin k → TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (Mark := BranchingStep ℕ X) n] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ
        (A ∩ selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      branchingStepFieldLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  let P := branchingStepFieldLaw μ
  let Q := Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)
  let C := fun roots => abstractVectorSelectionCell chosen A roots
  let D := fun roots => C roots ∩ subtreeStepFieldVector roots ⁻¹' B
  have hCmeas (roots : Fin k → TreeNode) : MeasurableSet (C roots) :=
    (generationFiltration (Mark := BranchingStep ℕ X) |>.le n) _
      (abstractVectorSelectionCell_measurable chosen hchosen A hA roots)
  have hDmeas (roots : Fin k → TreeNode) : MeasurableSet (D roots) :=
    (hCmeas roots).inter ((subtreeStepFieldVector_measurable roots) hB)
  have hCpair : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro ω hcr hcs
    exact hrs (hcr.2.symm.trans hcs.2)
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
      exact ⟨chosen ω, hAω, rfl⟩
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
      exact ⟨chosen ω, ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeStepFieldVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := by
      apply tsum_congr
      intro roots
      exact abstractVectorSelectionCell_measure_factorization μ chosen
        hchosen hdepth hinj A B hA hB roots
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

theorem selectedSubtreeStepFieldVector_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    (branchingStepFieldLaw μ).map (selectedSubtreeStepFieldVector chosen) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepFieldVector_measurable chosen hchosen) hB]
  have h := selectedSubtreeStepFieldVector_event_factorization μ chosen
    hchosen hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selectedSubtreeStepFieldVector_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : (TreeNode → BranchingStep ℕ X) → Fin k → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    Indep (generationFiltration (Mark := BranchingStep ℕ X) n)
      (MeasurableSpace.comap (selectedSubtreeStepFieldVector chosen)
        inferInstance) (branchingStepFieldLaw μ) := by
  apply (indep_iff_forall_indepSet (branchingStepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (Mark := BranchingStep ℕ X) |>.le n) _ hA)
    ((selectedSubtreeStepFieldVector_measurable chosen hchosen) hB)
    (branchingStepFieldLaw μ)).2
  have hmap : branchingStepFieldLaw μ
      (selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
    rw [← Measure.map_apply
      (selectedSubtreeStepFieldVector_measurable chosen hchosen) hB,
      selectedSubtreeStepFieldVector_law μ chosen hchosen hdepth hinj]
  rw [hmap]
  exact selectedSubtreeStepFieldVector_event_factorization μ chosen
    hchosen hdepth hinj A B hA hB

end ThesisSpeed
