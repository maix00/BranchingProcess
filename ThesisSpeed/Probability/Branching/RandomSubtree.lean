import ThesisSpeed.Probability.Branching.BranchingProperty

/-!
# A subtree chosen from current-generation information

The random root is selected before its own offspring mark is exposed. This
file turns fixed-root branching into a single randomly selected-root formula
by partitioning over the countable Ulam--Harris address space.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedSubtree (chosen : MarkedTree OffspringMark → TreeNode)
    (ω : MarkedTree OffspringMark) : MarkedTree OffspringMark :=
  subtreeMarks (chosen ω) ω

theorem selectedSubtree_measurable (n : ℕ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen) :
    Measurable (selectedSubtree chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono (generationFiltration (Mark := OffspringMark) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : TreeNode × MarkedTree OffspringMark =>
        subtreeMarks p.1 p.2) :=
    measurable_from_prod_countable_right subtreeMarks_measurable
  exact hjoint.comp (hselect.prodMk measurable_id)

/-- A past event restricted to the outcomes selecting a particular address. -/
def selectionCell (chosen : MarkedTree OffspringMark → TreeNode)
    (A : Set (MarkedTree OffspringMark)) (u : TreeNode) :
    Set (MarkedTree OffspringMark) :=
  A ∩ {ω | chosen ω = u}

theorem selectionCell_measurable (n : ℕ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (A : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (u : TreeNode) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) n]
      (selectionCell chosen A u) :=
  hA.inter (hchosen (measurableSet_singleton u))

theorem selectionCell_measure_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (hB : MeasurableSet B) (u : TreeNode) :
    iidMarkedTreeLaw μ (selectionCell chosen A u ∩
      subtreeMarks u ⁻¹' B) =
      iidMarkedTreeLaw μ (selectionCell chosen A u) * iidMarkedTreeLaw μ B := by
  by_cases hu : u.length = n
  · have hcell := selectionCell_measurable n chosen hchosen A hA u
    have hcell' :
        MeasurableSet[generationFiltration (Mark := OffspringMark) u.length]
          (selectionCell chosen A u) := by
      rw [hu]
      exact hcell
    exact fixed_subtree_event_factorization μ u _ _ hcell' hB
  · have hempty : selectionCell chosen A u = ∅ := by
      ext ω
      simp only [selectionCell, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hchosenω⟩
      exact hu (by simpa [hchosenω] using hdepth ω)
    simp [hempty]

/-- The subtree selected from generation-`n` information retains the original
marked-tree law and is independent of every generation-`n` event. -/
theorem selected_subtree_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n)
    (A B : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ A * iidMarkedTreeLaw μ B := by
  let P := iidMarkedTreeLaw μ
  let C : TreeNode → Set (MarkedTree OffspringMark) :=
    selectionCell chosen A
  let D : TreeNode → Set (MarkedTree OffspringMark) :=
    fun u => C u ∩ subtreeMarks u ⁻¹' B
  have hCmeas (u : TreeNode) : MeasurableSet (C u) :=
    (generationFiltration (Mark := OffspringMark) |>.le n) _
      (selectionCell_measurable n chosen hchosen A hA u)
  have hDmeas (u : TreeNode) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeMarks_measurable u) hB)
  have hCpair : Pairwise (fun u v => Disjoint (C u) (C v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro ω hcu hcv
    have hu : chosen ω = u := hcu.2
    have hv : chosen ω = v := hcv.2
    exact huv (hu.symm.trans hv)
  have hDpair : Pairwise (fun u v => Disjoint (D u) (D v)) := by
    intro u v huv
    exact (hCpair huv).mono (Set.inter_subset_left)
      (Set.inter_subset_left)
  have hCunion : (⋃ u, C u) = A := by
    ext ω
    simp only [Set.mem_iUnion, C, selectionCell, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hAω, _⟩
      exact hAω
    · intro hAω
      exact ⟨chosen ω, hAω, rfl⟩
  have hDunion : (⋃ u, D u) = A ∩ selectedSubtree chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, selectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      selectedSubtree]
    constructor
    · rintro ⟨u, ⟨⟨hAω, hchoose⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hchoose] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨chosen ω, ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' u, P (C u)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtree chosen ⁻¹' B) = P (⋃ u, D u) := by rw [hDunion]
    _ = ∑' u, P (D u) := measure_iUnion hDpair hDmeas
    _ = ∑' u, P (C u) * P B := by
      apply tsum_congr
      intro u
      exact selectionCell_measure_factorization μ n chosen hchosen hdepth
        A B hA hB u
    _ = (∑' u, P (C u)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

/-- A root chosen from the current generation's information has a fresh
subtree with the original i.i.d. marked-tree law. -/
theorem selected_subtree_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    (iidMarkedTreeLaw μ).map (selectedSubtree chosen) = iidMarkedTreeLaw μ := by
  ext B hB
  rw [Measure.map_apply (selectedSubtree_measurable n chosen hchosen) hB]
  have h := selected_subtree_event_factorization μ n chosen hchosen hdepth
    Set.univ B (by simp) hB
  simpa using h

/-- The selected subtree is independent of the generation domain flow. This
is the single random-root form of deterministic-time branching. -/
theorem selected_subtree_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (n : ℕ) (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := OffspringMark) n]
      chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Indep (generationFiltration (Mark := OffspringMark) n)
      (MeasurableSpace.comap (selectedSubtree chosen) inferInstance)
      (iidMarkedTreeLaw μ) := by
  apply (indep_iff_forall_indepSet (iidMarkedTreeLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((generationFiltration (Mark := OffspringMark) |>.le n) _ hA)
    ((selectedSubtree_measurable n chosen hchosen) hB)
    (iidMarkedTreeLaw μ)).2
  have hmap : iidMarkedTreeLaw μ (selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ B := by
    rw [← Measure.map_apply (selectedSubtree_measurable n chosen hchosen) hB,
      selected_subtree_law μ n chosen hchosen hdepth]
  rw [hmap]
  exact selected_subtree_event_factorization μ n chosen hchosen hdepth
    A B hA hB

end ThesisSpeed
