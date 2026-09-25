import ThesisSpeed.Probability.Branching.StoppingTime
import ThesisSpeed.Probability.Branching.RandomSubtreeVector

/-!
# Joint branching for a fixed-size vector at a stopping time

This is the fixed-cardinality layer needed before partitioning a random
finite surviving population by its cardinality.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def stoppedVectorCell {k : ℕ}
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (A : Set (MarkedTree OffspringMark))
    (p : ℕ × (Fin k → TreeNode)) : Set (MarkedTree OffspringMark) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | roots ω = p.2}

theorem stoppedVectorCell_measurable {k : ℕ}
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (A : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × (Fin k → TreeNode)) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) p.1]
      (stoppedVectorCell τ roots A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable
      (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hrootSet : MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = p.2} := hroots (measurableSet_singleton p.2)
  have hrootEq := (hτ.measurableSet_inter_eq_iff
    {ω | roots ω = p.2} p.1).1
      (hrootSet.inter (hτ.measurable
        (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : stoppedVectorCell τ roots A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | roots ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [stoppedVectorCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hrootEq

theorem stopped_selectedSubtreeVector_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω))
    (A : Set (MarkedTree OffspringMark))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ selectedSubtreeVector roots ⁻¹' B) =
      iidMarkedTreeLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  let P := iidMarkedTreeLaw μ
  let Q := Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)
  let C : ℕ × (Fin k → TreeNode) → Set (MarkedTree OffspringMark) :=
    stoppedVectorCell τ roots A
  let D : ℕ × (Fin k → TreeNode) → Set (MarkedTree OffspringMark) :=
    fun p => C p ∩ subtreeVector p.2 ⁻¹' B
  have hCmeas p : MeasurableSet (C p) :=
    (generationFiltration (Mark := OffspringMark) |>.le p.1) _
      (stoppedVectorCell_measurable τ hτ roots hroots A hA p)
  have hDmeas p : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeVector_measurable p.2) hB)
  have hcell p : P (D p) = P (C p) * Q B := by
    by_cases hvalid : (∀ i, (p.2 i).length = p.1) ∧
        Function.Injective p.2
    · have hgen := stoppedVectorCell_measurable
        τ hτ roots hroots A hA p
      exact fixed_subtreeVector_event_factorization μ p.2 hvalid.1
        hvalid.2 (C p) B hgen hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, stoppedVectorCell, Set.mem_inter_iff,
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
    · simp only [Set.mem_iUnion, C, stoppedVectorCell,
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
      A ∩ selectedSubtreeVector roots ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, stoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtreeVector]
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
    P (A ∩ selectedSubtreeVector roots ⁻¹' B) = P (⋃ p, D p) := by
      rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * Q B := tsum_congr hcell
    _ = (∑' p, P (C p)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

theorem selectedSubtreeVector_measurable_of_measurable {k : ℕ}
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (hroots : Measurable roots) :
    Measurable (selectedSubtreeVector roots) := by
  have hjoint : Measurable
      (fun p : (Fin k → TreeNode) × MarkedTree OffspringMark =>
        subtreeVector p.1 p.2) :=
    measurable_from_prod_countable_right subtreeVector_measurable
  exact hjoint.comp (hroots.prodMk measurable_id)

theorem stopped_selectedSubtreeVector_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    (iidMarkedTreeLaw μ).map (selectedSubtreeVector roots) =
      Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  ext B hB
  rw [Measure.map_apply
    (selectedSubtreeVector_measurable_of_measurable roots hrootsFull) hB]
  have hfactor := stopped_selectedSubtreeVector_event_factorization μ
    τ hτ hfinite roots hroots hdepth hinj Set.univ B (by simp) hB
  simpa using hfactor

theorem stopped_selectedSubtreeVector_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : MarkedTree OffspringMark → Fin k → TreeNode)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω)) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (selectedSubtreeVector roots) inferInstance)
      (iidMarkedTreeLaw μ) := by
  have hrootsFull : Measurable roots :=
    hroots.mono hτ.measurableSpace_le le_rfl
  have hselected :=
    selectedSubtreeVector_measurable_of_measurable roots hrootsFull
  apply (indep_iff_forall_indepSet (iidMarkedTreeLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB) (iidMarkedTreeLaw μ)).2
  have hlaw : iidMarkedTreeLaw μ
      (selectedSubtreeVector roots ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
    rw [← Measure.map_apply hselected hB,
      stopped_selectedSubtreeVector_law μ τ hτ hfinite roots
        hroots hdepth hinj]
  rw [hlaw]
  exact stopped_selectedSubtreeVector_event_factorization μ τ hτ hfinite
    roots hroots hdepth hinj A B hA hB

end ThesisSpeed
