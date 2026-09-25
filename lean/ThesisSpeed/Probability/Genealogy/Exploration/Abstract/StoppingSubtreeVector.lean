import ThesisSpeed.Probability.Genealogy.Exploration.Abstract.StoppingSubtree
import ThesisSpeed.Probability.Genealogy.Exploration.Selected.AbstractSubtreeVector

/-!
# Joint abstract branching at a finite stopping generation

This is the fixed-cardinality stopping layer.  A measurable vector of distinct
nodes at the finite stopping generation has fresh descendant step fields with
the product law of independent copies of the original field.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def abstractStoppedVectorCell {X : Type*} {k : ℕ}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (A : Set (𝕍 → BranchingStep ℕ X))
    (p : ℕ × (Fin k → 𝕍)) :
    Set (𝕍 → BranchingStep ℕ X) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | roots ω = p.2}

theorem abstractStoppedVectorCell_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (A : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × (Fin k → 𝕍)) :
    MeasurableSet[generationFiltration (M := BranchingStep ℕ X) p.1]
      (abstractStoppedVectorCell τ roots A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hrootSet : MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = p.2} := hroots (measurableSet_singleton p.2)
  have hrootEq := (hτ.measurableSet_inter_eq_iff
    {ω | roots ω = p.2} p.1).1
      (hrootSet.inter (hτ.measurable
        (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : abstractStoppedVectorCell τ roots A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | roots ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [abstractStoppedVectorCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hrootEq

theorem stopped_selectedSubtreeStepFieldVector_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω))
    (A : Set (𝕍 → BranchingStep ℕ X))
    (B : Set (Fin k → 𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ
        (A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B) =
      branchingStepFieldLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  let P := branchingStepFieldLaw μ
  let Q := Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)
  let C := fun p => abstractStoppedVectorCell τ roots A p
  let D := fun p => C p ∩ subtreeStepFieldVector p.2 ⁻¹' B
  have hCmeas (p : ℕ × (Fin k → 𝕍)) : MeasurableSet (C p) :=
    (generationFiltration (M := BranchingStep ℕ X) |>.le p.1) _
      (abstractStoppedVectorCell_measurable τ hτ roots hroots A hA p)
  have hDmeas (p : ℕ × (Fin k → 𝕍)) : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeStepFieldVector_measurable p.2) hB)
  have hcell (p : ℕ × (Fin k → 𝕍)) :
      P (D p) = P (C p) * Q B := by
    by_cases hvalid : (∀ i, (p.2 i).length = p.1) ∧
        Function.Injective p.2
    · have hgen := abstractStoppedVectorCell_measurable
        τ hτ roots hroots A hA p
      exact fixed_subtreeStepFieldVector_event_factorization μ p.2
        hvalid.1 hvalid.2 (C p) B hgen hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, abstractStoppedVectorCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htime⟩, hroot⟩
        apply hvalid
        constructor
        · intro i
          simpa [← hroot] using hdepth ω p.1 htime i
        · simpa [← hroot] using hinj ω
      simp [D, hempty]
  have hCpair : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨n, r⟩ ⟨l, s⟩ hpq
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
    · simp only [Set.mem_iUnion, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨p, ⟨hAω, _⟩, _⟩
      exact hAω
    · intro hAω
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, roots ω), ⟨⟨hAω, htime⟩, rfl⟩⟩
  have hDunion : (⋃ p, D p) =
      A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtreeStepFieldVector]
      rintro ⟨p, ⟨⟨⟨hAω, _⟩, hroot⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hroot] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, roots ω), ⟨⟨⟨hAω, htime⟩, rfl⟩, hBω⟩⟩
  have hCsum : (∑' p, P (C p)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * Q B := tsum_congr hcell
    _ = (∑' p, P (C p)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

theorem selectedSubtreeStepFieldVector_measurable_of_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (hroots : Measurable roots) :
    Measurable (selectedSubtreeStepFieldVector roots) := by
  have hjoint : Measurable
      (fun p : (Fin k → 𝕍) × (𝕍 → BranchingStep ℕ X) =>
        subtreeStepFieldVector p.1 p.2) :=
    measurable_from_prod_countable_right subtreeStepFieldVector_measurable
  exact hjoint.comp (hroots.prodMk measurable_id)

theorem stopped_selectedSubtreeStepFieldVector_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    (branchingStepFieldLaw μ).map
        (selectedSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull)
    hB]
  have hfactor := stopped_selectedSubtreeStepFieldVector_event_factorization μ
    τ hτ hfinite roots hroots hdepth hinj Set.univ B (by simp) hB
  simpa using hfactor

theorem stopped_selectedSubtreeStepFieldVector_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : (𝕍 → BranchingStep ℕ X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := BranchingStep ℕ X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (𝕍 → BranchingStep ℕ X) → Fin k → 𝕍)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap
        (selectedSubtreeStepFieldVector roots) inferInstance)
      (branchingStepFieldLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeStepFieldVector_measurable_of_measurable roots hrootsFull
  apply (indep_iff_forall_indepSet (branchingStepFieldLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB)
    (branchingStepFieldLaw μ)).2
  have hlaw : branchingStepFieldLaw μ
      (selectedSubtreeStepFieldVector roots ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
    rw [← Measure.map_apply hselected hB,
      stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots
        hroots hdepth hinj]
  rw [hlaw]
  exact stopped_selectedSubtreeStepFieldVector_event_factorization μ τ hτ
    hfinite roots hroots hdepth hinj A B hA hB

end ThesisSpeed
