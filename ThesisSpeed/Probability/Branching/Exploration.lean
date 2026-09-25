import ThesisSpeed.Probability.Branching.RandomSubtree

/-!
# Exploration information and unused subtrees

An exploration domain is bounded by the coordinate marks that have actually
been inspected. A fixed reserve subtree is fresh whenever none of its
addresses belongs to that inspected coordinate set.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

@[instance_reducible] def marksOnSpace (s : Set TreeNode) :
    MeasurableSpace (MarkedTree OffspringMark) :=
  ⨆ u ∈ s, coordinateMarkSpace u

theorem marksOnSpace_mono {s t : Set TreeNode} (hst : s ⊆ t) :
    marksOnSpace s ≤ marksOnSpace t := by
  unfold marksOnSpace
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem marksOnSpace_le (s : Set TreeNode) :
    marksOnSpace s ≤
      (inferInstance : MeasurableSpace (MarkedTree OffspringMark)) := by
  unfold marksOnSpace
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact (measurable_pi_apply u).comap_le

/-- Coordinate fields on disjoint address sets are independent under the
i.i.d. pre-sampled-tree law. -/
theorem marksOnSpace_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (s t : Set TreeNode)
    (hdisj : Disjoint s t) :
    Indep (marksOnSpace s) (marksOnSpace t) (iidMarkedTreeLaw μ) := by
  unfold marksOnSpace
  have hle : ∀ u : TreeNode, coordinateMarkSpace u ≤
      (inferInstance : MeasurableSpace (MarkedTree OffspringMark)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle (iid_coordinateMarkSpaces μ) hdisj

theorem marksOnSpace_descendant_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (explored : Set TreeNode) (root : TreeNode)
    (hfresh : Disjoint explored (descendantAddresses root)) :
    Indep (marksOnSpace explored) (descendantMarkSpace root)
      (iidMarkedTreeLaw μ) := by
  rw [descendantMarkSpace_eq_iSup]
  exact marksOnSpace_independent μ explored (descendantAddresses root) hfresh

/-- A sequence of exploration domains `ℋ j`, each explicitly bounded by the
marks inspected in the first `j` exploration stages. -/
structure ExplorationDomains where
  inspected : ℕ → Set TreeNode
  domain : ℕ → MeasurableSpace (MarkedTree OffspringMark)
  domain_le : ∀ j, domain j ≤ marksOnSpace (inspected j)
  inspected_mono : Monotone inspected

theorem ExplorationDomains.fresh_descendant_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (H : ExplorationDomains) (j : ℕ) (root : TreeNode)
    (hfresh : Disjoint (H.inspected j) (descendantAddresses root)) :
    Indep (H.domain j) (descendantMarkSpace root)
      (iidMarkedTreeLaw μ) := by
  apply indep_of_indep_of_le_left
    (marksOnSpace_descendant_independent μ (H.inspected j) root hfresh)
  exact H.domain_le j

theorem ExplorationDomains.fresh_subtree_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (H : ExplorationDomains) (j : ℕ) (root : TreeNode)
    (hfresh : Disjoint (H.inspected j) (descendantAddresses root)) :
    Indep (H.domain j)
      (MeasurableSpace.comap (subtreeMarks root) inferInstance)
      (iidMarkedTreeLaw μ) :=
  indep_of_indep_of_le_right
    (H.fresh_descendant_independent μ j root hfresh)
    (subtreeMarks_descendant_measurable root).comap_le

theorem selectedSubtree_measurable_of_measurable
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable chosen) :
    Measurable (selectedSubtree chosen) := by
  have hjoint : Measurable
      (fun p : TreeNode × MarkedTree OffspringMark =>
        subtreeMarks p.1 p.2) :=
    measurable_from_prod_countable_right subtreeMarks_measurable
  exact hjoint.comp (hchosen.prodMk measurable_id)

/-- A reserve root selected using `ℋ j` has a fresh subtree when every root
that can be selected is disjoint from the coordinates inspected by `ℋ j`. -/
theorem ExplorationDomains.selected_fresh_subtree_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (H : ExplorationDomains) (j : ℕ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω,
      Disjoint (H.inspected j) (descendantAddresses (chosen ω)))
    (A B : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[H.domain j] A) (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ A * iidMarkedTreeLaw μ B := by
  let P := iidMarkedTreeLaw μ
  let C : TreeNode → Set (MarkedTree OffspringMark) :=
    selectionCell chosen A
  let D : TreeNode → Set (MarkedTree OffspringMark) :=
    fun u => C u ∩ subtreeMarks u ⁻¹' B
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (marksOnSpace_le _)) le_rfl
  have hCdomain (u : TreeNode) : MeasurableSet[H.domain j] (C u) :=
    hA.inter (hchosen (measurableSet_singleton u))
  have hCmeas (u : TreeNode) : MeasurableSet (C u) :=
    ((H.domain_le j).trans (marksOnSpace_le _)) _ (hCdomain u)
  have hDmeas (u : TreeNode) : MeasurableSet (D u) :=
    (hCmeas u).inter ((subtreeMarks_measurable u) hB)
  have hcell (u : TreeNode) : P (D u) = P (C u) * P B := by
    by_cases hu : Disjoint (H.inspected j) (descendantAddresses u)
    · have hind := H.fresh_subtree_independent μ j u hu
      have hpre : MeasurableSet[MeasurableSpace.comap
          (subtreeMarks u) inferInstance]
          (subtreeMarks u ⁻¹' B) := ⟨B, hB, rfl⟩
      have hfactor := (hind.indepSet_of_measurableSet
        (hCdomain u) hpre).measure_inter_eq_mul
      have hlaw : P (subtreeMarks u ⁻¹' B) = P B := by
        rw [← Measure.map_apply (subtreeMarks_measurable u) hB,
          subtreeMarks_law]
      rw [hlaw] at hfactor
      exact hfactor
    · have hempty : C u = ∅ := by
        ext ω
        simp only [C, selectionCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hchoose⟩
        exact hu (hchoose ▸ hfresh ω)
      simp [D, hempty]
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
    simp [C, selectionCell]
  have hDunion : (⋃ u, D u) =
      A ∩ selectedSubtree chosen ⁻¹' B := by
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
    P (A ∩ selectedSubtree chosen ⁻¹' B) = P (⋃ u, D u) := by
      rw [hDunion]
    _ = ∑' u, P (D u) := measure_iUnion hDpair hDmeas
    _ = ∑' u, P (C u) * P B := tsum_congr hcell
    _ = (∑' u, P (C u)) * P B := ENNReal.tsum_mul_right
    _ = P A * P B := by rw [hCsum]

theorem ExplorationDomains.selected_fresh_subtree_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (H : ExplorationDomains) (j : ℕ)
    (chosen : MarkedTree OffspringMark → TreeNode)
    (hchosen : Measurable[H.domain j] chosen)
    (hfresh : ∀ ω,
      Disjoint (H.inspected j) (descendantAddresses (chosen ω))) :
    Indep (H.domain j)
      (MeasurableSpace.comap (selectedSubtree chosen) inferInstance)
      (iidMarkedTreeLaw μ) := by
  apply (indep_iff_forall_indepSet (iidMarkedTreeLaw μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  have hchosenFull : Measurable chosen :=
    hchosen.mono ((H.domain_le j).trans (marksOnSpace_le _)) le_rfl
  have hselected := selectedSubtree_measurable_of_measurable chosen hchosenFull
  apply (indepSet_iff_measure_inter_eq_mul
    (((H.domain_le j).trans (marksOnSpace_le _)) _ hA)
    (hselected hB) (iidMarkedTreeLaw μ)).2
  have hlaw : iidMarkedTreeLaw μ (selectedSubtree chosen ⁻¹' B) =
      iidMarkedTreeLaw μ B := by
    have hfactor := H.selected_fresh_subtree_event_factorization μ j
      chosen hchosen hfresh Set.univ B (by simp) hB
    simpa using hfactor
  rw [hlaw]
  exact H.selected_fresh_subtree_event_factorization μ j chosen
    hchosen hfresh A B hA hB

end ThesisSpeed
