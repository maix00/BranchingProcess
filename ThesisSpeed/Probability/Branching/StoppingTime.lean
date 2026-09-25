import ThesisSpeed.Probability.Branching.Exploration

/-!
# Branching at a finite stopping time

The proof partitions simultaneously by the stopping generation and the
selected genealogical address. On each countable cell it reduces to the
deterministic-generation branching theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def stoppedSelectionCell
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (A : Set (MarkedTree OffspringMark))
    (p : ℕ × TreeNode) : Set (MarkedTree OffspringMark) :=
  A ∩ {ω | τ ω = p.1} ∩ {ω | chosen ω = p.2}

theorem stoppedSelectionCell_measurable
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (A : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (p : ℕ × TreeNode) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) p.1]
      (stoppedSelectionCell τ chosen A p) := by
  have hAeq := (hτ.measurableSet_inter_eq_iff A p.1).1
    (hA.inter (hτ.measurable (measurableSet_singleton (p.1 : WithTop ℕ))))
  have hchoose : MeasurableSet[hτ.measurableSpace]
      {ω | chosen ω = p.2} := hchosen (measurableSet_singleton p.2)
  have hchooseEq := (hτ.measurableSet_inter_eq_iff
    {ω | chosen ω = p.2} p.1).1
      (hchoose.inter
        (hτ.measurable (measurableSet_singleton (p.1 : WithTop ℕ))))
  have heq : stoppedSelectionCell τ chosen A p =
      (A ∩ {ω | τ ω = p.1}) ∩
        ({ω | chosen ω = p.2} ∩ {ω | τ ω = p.1}) := by
    ext ω
    simp [stoppedSelectionCell, and_left_comm, and_assoc, and_comm]
  rw [heq]
  exact hAeq.inter hchooseEq

theorem stopped_selected_subtree_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      (chosen ω).length = n)
    (A B : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ A * iidMarkedTreeLaw μ B := by
  let P := iidMarkedTreeLaw μ
  let C : ℕ × TreeNode → Set (MarkedTree OffspringMark) :=
    stoppedSelectionCell τ chosen A
  let D : ℕ × TreeNode → Set (MarkedTree OffspringMark) :=
    fun p => C p ∩ subtreeMarks p.2 ⁻¹' B
  have hCmeas (p : ℕ × TreeNode) : MeasurableSet (C p) :=
    (generationFiltration (Mark := OffspringMark) |>.le p.1) _
      (stoppedSelectionCell_measurable τ hτ chosen hchosen A hA p)
  have hDmeas (p : ℕ × TreeNode) : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeMarks_measurable p.2) hB)
  have hcell (p : ℕ × TreeNode) : P (D p) = P (C p) * P B := by
    by_cases hp : p.2.length = p.1
    · have hcellGen := stoppedSelectionCell_measurable
        τ hτ chosen hchosen A hA p
      have hcellDepth : MeasurableSet[generationFiltration
          (Mark := OffspringMark) p.2.length]
          (C p) := by
        rw [hp]
        exact hcellGen
      exact fixed_subtree_event_factorization μ p.2 (C p) B
        hcellDepth hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, stoppedSelectionCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htime⟩, hchoose⟩
        exact hp (by simpa [hchoose] using hdepth ω p.1 htime)
      simp [D, hempty]
  have hCpair : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨n, u⟩ ⟨k, v⟩ hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    have hn : τ ω = n := hp.1.2
    have hk : τ ω = k := hq.1.2
    have hu : chosen ω = u := hp.2
    have hv : chosen ω = v := hq.2
    apply hpq
    exact Prod.ext (WithTop.coe_injective (hn.symm.trans hk))
      (hu.symm.trans hv)
  have hDpair : Pairwise (fun p q => Disjoint (D p) (D q)) := by
    intro p q hpq
    exact (hCpair hpq).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ p, C p) = A := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, C, stoppedSelectionCell,
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
      A ∩ selectedSubtree chosen ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, stoppedSelectionCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtree]
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
    P (A ∩ selectedSubtree chosen ⁻¹' B) = P (⋃ p, D p) := by
      rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * P B := tsum_congr hcell
    _ = (∑' p, P (C p)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

theorem stopped_selected_subtree_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (τ : MarkedTree OffspringMark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (Mark := OffspringMark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[hτ.measurableSpace] chosen)
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      (chosen ω).length = n) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (selectedSubtree chosen) inferInstance)
      (iidMarkedTreeLaw μ) := by
  have hchosenFull : Measurable chosen :=
    hchosen.mono hτ.measurableSpace_le le_rfl
  have hselected := selectedSubtree_measurable_of_measurable chosen hchosenFull
  apply (indep_iff_forall_indepSet (iidMarkedTreeLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    (hτ.measurableSpace_le _ hA) (hselected hB) (iidMarkedTreeLaw μ)).2
  have hlaw : iidMarkedTreeLaw μ (selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ B := by
    have hfactor := stopped_selected_subtree_event_factorization μ
      τ hτ hfinite chosen hchosen hdepth Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact stopped_selected_subtree_event_factorization μ τ hτ hfinite
    chosen hchosen hdepth A B hA hB

end ThesisSpeed
