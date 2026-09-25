import ThesisSpeed.Probability.Branching.RootIndexed.DomainFlow

/-!
# Branching after a measurable frontier selection in a multi-root field

The selected nodes may belong to different initial roots.  Selection uses the
joint generation domain flow of every root, while the selected descendant
fields retain the product law of fresh independent branching-step fields.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedMultiRootSubtreeStepFieldVector
    {m k : ℕ} {X : Type*}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (step : FiniteRootBranchingStepField m X) :
    Fin k → 𝕍 → BranchingStep ℕ X :=
  multiRootSubtreeStepFieldVector (chosen step) step

theorem selectedMultiRootSubtreeStepFieldVector_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen) :
    Measurable (selectedMultiRootSubtreeStepFieldVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono (multiRootStepFiltration (m := m) (X := X) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : (Fin k → Fin m × 𝕍) × FiniteRootBranchingStepField m X =>
        multiRootSubtreeStepFieldVector p.1 p.2) :=
    measurable_from_prod_countable_right
      multiRootSubtreeStepFieldVector_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

def abstractMultiRootSelectionCell
    {m k : ℕ} {X : Type*}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (A : Set (FiniteRootBranchingStepField m X))
    (roots : Fin k → Fin m × 𝕍) :
    Set (FiniteRootBranchingStepField m X) :=
  A ∩ {step | chosen step = roots}

theorem abstractMultiRootSelectionCell_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (A : Set (FiniteRootBranchingStepField m X))
    (hA : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] A)
    (roots : Fin k → Fin m × 𝕍) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      (abstractMultiRootSelectionCell chosen A roots) :=
  hA.inter (hchosen (measurableSet_singleton roots))

theorem abstractMultiRootSelectionCell_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step))
    (A : Set (FiniteRootBranchingStepField m X))
    (B : Set (Fin k → 𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] A)
    (hB : MeasurableSet B)
    (roots : Fin k → Fin m × 𝕍) :
    finiteRootBranchingStepFieldLaw μ m
        (abstractMultiRootSelectionCell chosen A roots ∩
          multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootBranchingStepFieldLaw μ m
          (abstractMultiRootSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  by_cases hr : ∃ step, chosen step = roots
  · obtain ⟨step, hs⟩ := hr
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      simpa [← hs] using hdepth step j
    have hroots_inj : Function.Injective roots := by
      simpa [← hs] using hinj step
    exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots
      hlen hroots_inj _ _
      (abstractMultiRootSelectionCell_measurable chosen hchosen A hA roots) hB
  · have hempty : abstractMultiRootSelectionCell chosen A roots = ∅ := by
      ext step
      simp only [abstractMultiRootSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hs⟩
      exact hr ⟨step, hs⟩
    simp [hempty]

theorem selectedMultiRootSubtreeStepFieldVector_event_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step))
    (A : Set (FiniteRootBranchingStepField m X))
    (B : Set (Fin k → 𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] A)
    (hB : MeasurableSet B) :
    finiteRootBranchingStepFieldLaw μ m
        (A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
      finiteRootBranchingStepFieldLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  let P := finiteRootBranchingStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)
  let C := fun roots => abstractMultiRootSelectionCell chosen A roots
  let D := fun roots =>
    C roots ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B
  have hCmeas (roots : Fin k → Fin m × 𝕍) :
      MeasurableSet (C roots) :=
    (multiRootStepFiltration (m := m) (X := X) |>.le n) _
      (abstractMultiRootSelectionCell_measurable chosen hchosen A hA roots)
  have hDmeas (roots : Fin k → Fin m × 𝕍) :
      MeasurableSet (D roots) :=
    (hCmeas roots).inter
      ((multiRootSubtreeStepFieldVector_measurable roots) hB)
  have hCpair : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro step hcr hcs
    exact hrs (hcr.2.symm.trans hcs.2)
  have hDpair : Pairwise (fun r s => Disjoint (D r) (D s)) := by
    intro r s hrs
    exact (hCpair hrs).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ roots, C roots) = A := by
    ext step
    simp only [Set.mem_iUnion, C, abstractMultiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨roots, hAstep, _⟩
      exact hAstep
    · intro hAstep
      exact ⟨chosen step, hAstep, rfl⟩
  have hDunion : (⋃ roots, D roots) =
      A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B := by
    ext step
    simp only [Set.mem_iUnion, D, C, abstractMultiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedMultiRootSubtreeStepFieldVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAstep, hchoose⟩, hBstep⟩⟩
      exact ⟨hAstep, by simpa [hchoose] using hBstep⟩
    · rintro ⟨hAstep, hBstep⟩
      exact ⟨chosen step, ⟨⟨hAstep, rfl⟩, hBstep⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := by
      apply tsum_congr
      intro roots
      exact abstractMultiRootSelectionCell_factorization μ chosen hchosen
        hdepth hinj A B hA hB roots
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

theorem selectedMultiRootSubtreeStepFieldVector_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step)) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (selectedMultiRootSubtreeStepFieldVector chosen) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  ext B hB
  rw [Measure.map_apply
    (selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB]
  have h := selectedMultiRootSubtreeStepFieldVector_event_factorization μ
    chosen hchosen hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selectedMultiRootSubtreeStepFieldVector_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : FiniteRootBranchingStepField m X → Fin k → Fin m × 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ step j, (chosen step j).2.length = n)
    (hinj : ∀ step, Function.Injective (chosen step)) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (MeasurableSpace.comap
        (selectedMultiRootSubtreeStepFieldVector chosen) inferInstance)
      (finiteRootBranchingStepFieldLaw μ m) := by
  apply (indep_iff_forall_indepSet (finiteRootBranchingStepFieldLaw μ m)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((multiRootStepFiltration (m := m) (X := X) |>.le n) _ hA)
    ((selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB)
    (finiteRootBranchingStepFieldLaw μ m)).2
  have hmap : finiteRootBranchingStepFieldLaw μ m
      (selectedMultiRootSubtreeStepFieldVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
    rw [← Measure.map_apply
      (selectedMultiRootSubtreeStepFieldVector_measurable chosen hchosen) hB,
      selectedMultiRootSubtreeStepFieldVector_law μ chosen hchosen
        hdepth hinj]
  rw [hmap]
  exact selectedMultiRootSubtreeStepFieldVector_event_factorization μ chosen
    hchosen hdepth hinj A B hA hB

end ThesisSpeed
