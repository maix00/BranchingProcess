import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Exploration.SelectedSubtree

/-!
# Abstract branching at a finite stopping generation

The proof partitions by the stopping generation and selected address.  Every
cell reduces to the deterministic-generation branching theorem on abstract
`BranchingStep` fields.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



def abstractStoppedSelectionCell {X : Type*}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (A : Set (𝕍 → BranchingStep ℕ X))
    (p : ℕ × 𝕍) : Set (𝕍 → BranchingStep ℕ X) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | chosen ω = p.2}

theorem abstractStoppedSelectionCell_measurable
    {X : Type*} [MeasurableSpace X]
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (A : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × 𝕍) :
    MeasurableSet[generationFiltration (M := BranchingStep ℕ X) p.1]
      (abstractStoppedSelectionCell τ chosen A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hchoose : MeasurableSet[hτ.measurableSpace]
      {ω | chosen ω = p.2} := hchosen (measurableSet_singleton p.2)
  have hchooseEq := (hτ.measurableSet_inter_eq_iff
    {ω | chosen ω = p.2} p.1).1
      (hchoose.inter (hτ.measurable
        (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : abstractStoppedSelectionCell τ chosen A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | chosen ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [abstractStoppedSelectionCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hchooseEq

theorem stopped_selectedSubtreeStepField_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      (chosen ω).length = n)
    (A B : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
      branchingStepFieldLaw μ A * branchingStepFieldLaw μ B := by
  let P := branchingStepFieldLaw μ
  let C := fun p => abstractStoppedSelectionCell τ chosen A p
  let D := fun p => C p ∩ subtreeStepField p.2 ⁻¹' B
  have hCmeas (p : ℕ × 𝕍) : MeasurableSet (C p) :=
    (generationFiltration (M := BranchingStep ℕ X) |>.le p.1) _
      (abstractStoppedSelectionCell_measurable τ hτ chosen hchosen A hA p)
  have hDmeas (p : ℕ × 𝕍) : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeStepField_measurable p.2) hB)
  have hcell (p : ℕ × 𝕍) : P (D p) = P (C p) * P B := by
    by_cases hp : p.2.length = p.1
    · have hcellGen := abstractStoppedSelectionCell_measurable
        τ hτ chosen hchosen A hA p
      have hcellDepth : MeasurableSet[
          generationFiltration (M := BranchingStep ℕ X) p.2.length]
          (C p) := by
        rw [hp]
        exact hcellGen
      exact fixed_subtreeStepField_event_factorization μ p.2 (C p) B
        hcellDepth hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, abstractStoppedSelectionCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htime⟩, hchoose⟩
        exact hp (by simpa [hchoose] using hdepth ω p.1 htime)
      simp [D, hempty]
  have hCpair : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨n, u⟩ ⟨k, v⟩ hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    apply hpq
    exact Prod.ext
      (WithTop.coe_injective (hp.1.2.symm.trans hq.1.2))
      (hp.2.symm.trans hq.2)
  have hDpair : Pairwise (fun p q => Disjoint (D p) (D q)) := by
    intro p q hpq
    exact (hCpair hpq).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ p, C p) = A := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, C, abstractStoppedSelectionCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨p, ⟨hAω, _⟩, _⟩
      exact hAω
    · intro hAω
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, chosen ω), ⟨⟨hAω, htime⟩, rfl⟩⟩
  have hDunion : (⋃ p, D p) =
      A ∩ selectedSubtreeStepField chosen ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, abstractStoppedSelectionCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtreeStepField]
      rintro ⟨p, ⟨⟨⟨hAω, _⟩, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, chosen ω), ⟨⟨⟨hAω, htime⟩, rfl⟩, hBω⟩⟩
  have hCsum : (∑' p, P (C p)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeStepField chosen ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * P B := tsum_congr hcell
    _ = (∑' p, P (C p)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

theorem stopped_selectedSubtreeStepField_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (chosen : (𝕍 → BranchingStep ℕ X) → 𝕍)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      (chosen ω).length = n) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (selectedSubtreeStepField chosen) inferInstance)
      (branchingStepFieldLaw μ) := by
  have hchosenFull : Measurable chosen :=
    hchosen.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeStepField_measurable_of_measurable chosen hchosenFull
  apply (indep_iff_forall_indepSet (branchingStepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB)
    (branchingStepFieldLaw μ)).2
  have hlaw : branchingStepFieldLaw μ
      (selectedSubtreeStepField chosen ⁻¹' B) = branchingStepFieldLaw μ B := by
    have hfactor := stopped_selectedSubtreeStepField_event_factorization μ
      τ hτ hfinite chosen hchosen hdepth Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact stopped_selectedSubtreeStepField_event_factorization μ τ hτ hfinite
    chosen hchosen hdepth A B hA hB

end ProbabilityTheory.BranchingRandomWalk
