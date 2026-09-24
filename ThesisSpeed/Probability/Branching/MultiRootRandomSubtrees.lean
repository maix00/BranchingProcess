import ThesisSpeed.Probability.Branching.MultiRootBranching

/-!
# Branching from a measurable frontier in a multi-root tree

The vector of labelled roots may depend on all marks exposed through
generation `n`, including marks belonging to other initial ancestors. Its
length is fixed. A random-size selected population requires an additional
partition by size.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedMultiRootSubtreeVector {m k : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (ω : MultiRootTree m) : Fin k → MarkedTree OffspringMark :=
  multiRootSubtreeVector (chosen ω) ω

theorem selectedMultiRootSubtreeVector_measurable {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen) :
    Measurable (selectedMultiRootSubtreeVector chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono (multiRootFiltration m |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : (Fin k → Fin m × TreeNode) × MultiRootTree m =>
        multiRootSubtreeVector p.1 p.2) :=
    measurable_from_prod_countable_right multiRootSubtreeVector_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

def multiRootSelectionCell {m k : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (A : Set (MultiRootTree m))
    (roots : Fin k → Fin m × TreeNode) : Set (MultiRootTree m) :=
  A ∩ {ω | chosen ω = roots}

theorem multiRootSelectionCell_measurable {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (A : Set (MultiRootTree m))
    (hA : MeasurableSet[multiRootFiltration m n] A)
    (roots : Fin k → Fin m × TreeNode) :
    MeasurableSet[multiRootFiltration m n]
      (multiRootSelectionCell chosen A roots) :=
  hA.inter (hchosen (measurableSet_singleton roots))

theorem multiRootSelectionCell_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω j, (chosen ω j).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (MultiRootTree m))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[multiRootFiltration m n] A)
    (hB : MeasurableSet B)
    (roots : Fin k → Fin m × TreeNode) :
    iidMultiRootLaw μ m (multiRootSelectionCell chosen A roots ∩
      multiRootSubtreeVector roots ⁻¹' B) =
      iidMultiRootLaw μ m (multiRootSelectionCell chosen A roots) *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  by_cases hr : ∃ ω, chosen ω = roots
  · obtain ⟨ω, hw⟩ := hr
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      simpa [← hw] using hdepth ω j
    have hroots_inj : Function.Injective roots := by
      simpa [← hw] using hinj ω
    exact fixed_multiRootSubtreeVector_event_factorization μ roots hlen
      hroots_inj _ _
      (multiRootSelectionCell_measurable chosen hchosen A hA roots) hB
  · have hempty : multiRootSelectionCell chosen A roots = ∅ := by
      ext ω
      simp only [multiRootSelectionCell, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hw⟩
      exact hr ⟨ω, hw⟩
    simp [hempty]

/-- The joint marked-tree branching formula after a measurable selection
from all `m` initial ancestors. -/
theorem selected_multiRootSubtreeVector_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω j, (chosen ω j).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (MultiRootTree m))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[multiRootFiltration m n] A)
    (hB : MeasurableSet B) :
    iidMultiRootLaw μ m
        (A ∩ selectedMultiRootSubtreeVector chosen ⁻¹' B) =
      iidMultiRootLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  let P := iidMultiRootLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)
  let C : (Fin k → Fin m × TreeNode) → Set (MultiRootTree m) :=
    multiRootSelectionCell chosen A
  let D : (Fin k → Fin m × TreeNode) → Set (MultiRootTree m) :=
    fun roots => C roots ∩ multiRootSubtreeVector roots ⁻¹' B
  have hCmeas (roots : Fin k → Fin m × TreeNode) :
      MeasurableSet (C roots) :=
    (multiRootFiltration m |>.le n) _
      (multiRootSelectionCell_measurable chosen hchosen A hA roots)
  have hDmeas (roots : Fin k → Fin m × TreeNode) :
      MeasurableSet (D roots) :=
    (hCmeas roots).inter ((multiRootSubtreeVector_measurable roots) hB)
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
    simp only [Set.mem_iUnion, C, multiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨roots, hAω, _⟩
      exact hAω
    · intro hAω
      exact ⟨chosen ω, hAω, rfl⟩
  have hDunion : (⋃ roots, D roots) =
      A ∩ selectedMultiRootSubtreeVector chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, multiRootSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedMultiRootSubtreeVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAω, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨chosen ω, ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedMultiRootSubtreeVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := by
      apply tsum_congr
      intro roots
      exact multiRootSelectionCell_factorization μ chosen hchosen
        hdepth hinj A B hA hB roots
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

theorem selected_multiRootSubtreeVector_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω j, (chosen ω j).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    (iidMultiRootLaw μ m).map (selectedMultiRootSubtreeVector chosen) =
      Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ) := by
  ext B hB
  rw [Measure.map_apply
    (selectedMultiRootSubtreeVector_measurable chosen hchosen) hB]
  have h := selected_multiRootSubtreeVector_event_factorization μ chosen
    hchosen hdepth hinj Set.univ B (by simp) hB
  simpa using h

theorem selected_multiRootSubtreeVector_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ}
    (chosen : MultiRootTree m → Fin k → Fin m × TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω j, (chosen ω j).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    Indep (multiRootFiltration m n)
      (MeasurableSpace.comap (selectedMultiRootSubtreeVector chosen)
        inferInstance) (iidMultiRootLaw μ m) := by
  apply (indep_iff_forall_indepSet (iidMultiRootLaw μ m)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((multiRootFiltration m |>.le n) _ hA)
    ((selectedMultiRootSubtreeVector_measurable chosen hchosen) hB)
    (iidMultiRootLaw μ m)).2
  have hmap : iidMultiRootLaw μ m
      (selectedMultiRootSubtreeVector chosen ⁻¹' B) =
      (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
    rw [← Measure.map_apply
      (selectedMultiRootSubtreeVector_measurable chosen hchosen) hB,
      selected_multiRootSubtreeVector_law μ chosen hchosen hdepth hinj]
  rw [hmap]
  exact selected_multiRootSubtreeVector_event_factorization μ chosen
    hchosen hdepth hinj A B hA hB

end ThesisSpeed
