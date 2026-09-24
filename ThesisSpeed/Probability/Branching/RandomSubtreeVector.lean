import ThesisSpeed.Probability.Branching.JointSubtrees

/-!
# Joint branching at a finite random generation frontier

A fixed number of distinct generation-`n` roots may be selected using only
generation-`n` information. Partitioning by the countable vector of selected
addresses reduces their joint subtree law to the fixed-root product theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedSubtreeVector {k : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (ω : MarkedTree OffspringMark) :
    Fin k → MarkedTree OffspringMark :=
  subtreeVector (chosen ω) ω

theorem selectedSubtreeVector_measurable {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen) :
    Measurable (selectedSubtreeVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono (generationFiltration (Mark := OffspringMark) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : (Fin k → TreeNode) × MarkedTree OffspringMark =>
        subtreeVector p.1 p.2) :=
    measurable_from_prod_countable_right subtreeVector_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

def vectorSelectionCell {k : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (A : Set (MarkedTree OffspringMark))
    (roots : Fin k → TreeNode) : Set (MarkedTree OffspringMark) :=
  A ∩ {ω | chosen ω = roots}

theorem vectorSelectionCell_measurable {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (A : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (roots : Fin k → TreeNode) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) n]
      (vectorSelectionCell chosen A roots) :=
  hA.inter (hchosen (measurableSet_singleton roots))

theorem vectorSelectionCell_measure_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (MarkedTree OffspringMark))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (hB : MeasurableSet B) (roots : Fin k → TreeNode) :
    iidMarkedTreeLaw μ (vectorSelectionCell chosen A roots ∩
      subtreeVector roots ⁻¹' B) =
      iidMarkedTreeLaw μ (vectorSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  by_cases hr : ∃ ω, chosen ω = roots
  · obtain ⟨ω, hw⟩ := hr
    have hlen : ∀ i, (roots i).length = n := by
      intro i
      simpa [← hw] using hdepth ω i
    have hroots_inj : Function.Injective roots := by
      simpa [← hw] using hinj ω
    exact fixed_subtreeVector_event_factorization μ roots hlen hroots_inj
      _ _ (vectorSelectionCell_measurable chosen hchosen A hA roots) hB
  · have hempty : vectorSelectionCell chosen A roots = ∅ := by
      ext ω
      simp only [vectorSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hw⟩
      exact hr ⟨ω, hw⟩
    simp [hempty]

/-- Exact branching formula for a measurable finite vector of distinct roots. -/
theorem selected_subtreeVector_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (MarkedTree OffspringMark))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ selectedSubtreeVector chosen ⁻¹' B) =
      iidMarkedTreeLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  let P := iidMarkedTreeLaw μ
  let Q := Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)
  let C : (Fin k → TreeNode) → Set (MarkedTree OffspringMark) :=
    vectorSelectionCell chosen A
  let D : (Fin k → TreeNode) → Set (MarkedTree OffspringMark) :=
    fun roots => C roots ∩ subtreeVector roots ⁻¹' B
  have hCmeas (roots : Fin k → TreeNode) : MeasurableSet (C roots) :=
    (generationFiltration (Mark := OffspringMark) |>.le n) _
      (vectorSelectionCell_measurable chosen hchosen A hA roots)
  have hDmeas (roots : Fin k → TreeNode) : MeasurableSet (D roots) :=
    (hCmeas roots).inter ((subtreeVector_measurable roots) hB)
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
    simp only [Set.mem_iUnion, C, vectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨roots, hAω, _⟩
      exact hAω
    · intro hAω
      exact ⟨chosen ω, hAω, rfl⟩
  have hDunion :
      (⋃ roots, D roots) = A ∩ selectedSubtreeVector chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, vectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedSubtreeVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAω, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨chosen ω, ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeVector chosen ⁻¹' B) = P (⋃ roots, D roots) := by
      rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := by
      apply tsum_congr
      intro roots
      exact vectorSelectionCell_measure_factorization μ chosen hchosen
        hdepth hinj A B hA hB roots
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

/-- Joint offspring subtrees selected using generation-`n` information are
independent copies of the original tree. -/
theorem selected_subtreeVector_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    (iidMarkedTreeLaw μ).map (selectedSubtreeVector chosen) =
      Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ) := by
  ext B hB
  rw [Measure.map_apply (selectedSubtreeVector_measurable chosen hchosen) hB]
  have h := selected_subtreeVector_event_factorization μ chosen hchosen
    hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selected_subtreeVector_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ}
    (chosen : MarkedTree OffspringMark → Fin k → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω i, (chosen ω i).length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    Indep (generationFiltration (Mark := OffspringMark) n)
      (MeasurableSpace.comap (selectedSubtreeVector chosen) inferInstance)
      (iidMarkedTreeLaw μ) := by
  apply (indep_iff_forall_indepSet (iidMarkedTreeLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (Mark := OffspringMark) |>.le n) _ hA)
    ((selectedSubtreeVector_measurable chosen hchosen) hB)
    (iidMarkedTreeLaw μ)).2
  have hmap : iidMarkedTreeLaw μ (selectedSubtreeVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
    rw [← Measure.map_apply (selectedSubtreeVector_measurable chosen hchosen) hB,
      selected_subtreeVector_law μ chosen hchosen hdepth hinj]
  rw [hmap]
  exact selected_subtreeVector_event_factorization μ chosen hchosen
    hdepth hinj A B hA hB

end ThesisSpeed
