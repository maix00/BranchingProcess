import ThesisSpeed.Probability.Branching.MultiRootBranching

/-!
# Exploration domains with several initial roots

Coordinates are labelled by `(initial root, Ulam--Harris address)`. This keeps
descendant subtrees belonging to different initial particles disjoint even
when their local addresses coincide.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

@[instance_reducible] def multiMarksOnSpace {m : ℕ}
    (s : Set (Fin m × TreeNode)) : MeasurableSpace (MultiRootTree m) :=
  ⨆ p ∈ s, multiCoordinateSpace p

def multiDescendantAddresses {m : ℕ} (root : Fin m × TreeNode) :
    Set (Fin m × TreeNode) :=
  {p | ∃ tail : TreeNode, p = (root.1, root.2 ++ tail)}

@[instance_reducible] def multiDescendantMarkSpace {m : ℕ}
    (root : Fin m × TreeNode) : MeasurableSpace (MultiRootTree m) :=
  ⨆ tail : TreeNode,
    multiCoordinateSpace (root.1, root.2 ++ tail)

def multiSubtreeMarks {m : ℕ} (root : Fin m × TreeNode)
    (ω : MultiRootTree m) : MarkedTree OffspringMark :=
  fun tail => ω root.1 (root.2 ++ tail)

theorem multiDescendantMarkSpace_eq_iSup {m : ℕ}
    (root : Fin m × TreeNode) :
    multiDescendantMarkSpace root =
      multiMarksOnSpace (multiDescendantAddresses root) := by
  apply le_antisymm
  · unfold multiDescendantMarkSpace multiMarksOnSpace
    apply iSup_le
    intro tail
    exact le_iSup_of_le (root.1, root.2 ++ tail)
      (le_iSup_of_le ⟨tail, rfl⟩ le_rfl)
  · unfold multiMarksOnSpace
    apply iSup_le
    intro p
    apply iSup_le
    rintro ⟨tail, rfl⟩
    unfold multiDescendantMarkSpace
    exact le_iSup (fun v : TreeNode =>
      multiCoordinateSpace (root.1, root.2 ++ v)) tail

theorem multiMarksOnSpace_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m : ℕ} (s t : Set (Fin m × TreeNode)) (hdisj : Disjoint s t) :
    Indep (multiMarksOnSpace s) (multiMarksOnSpace t)
      (iidMultiRootLaw μ m) := by
  unfold multiMarksOnSpace
  have hle : ∀ p : Fin m × TreeNode, multiCoordinateSpace p ≤
      (inferInstance : MeasurableSpace (MultiRootTree m)) := by
    intro p
    have hmeas : Measurable (fun ω : MultiRootTree m => ω p.1 p.2) :=
      (measurable_pi_apply p.2 :
        Measurable (fun tree : MarkedTree OffspringMark => tree p.2)).comp
          (measurable_pi_apply p.1 :
            Measurable (fun ω : MultiRootTree m => ω p.1))
    exact hmeas.comap_le
  exact indep_iSup_of_disjoint hle (iid_multi_coordinates μ m) hdisj

structure MultiRootExplorationDomains (m : ℕ) where
  inspected : ℕ → Set (Fin m × TreeNode)
  domain : ℕ → MeasurableSpace (MultiRootTree m)
  domain_le : ∀ j, domain j ≤ multiMarksOnSpace (inspected j)
  inspected_mono : Monotone inspected

theorem MultiRootExplorationDomains.fresh_descendant_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m : ℕ} (H : MultiRootExplorationDomains m)
    (j : ℕ) (root : Fin m × TreeNode)
    (hfresh : Disjoint (H.inspected j) (multiDescendantAddresses root)) :
    Indep (H.domain j) (multiDescendantMarkSpace root)
      (iidMultiRootLaw μ m) := by
  rw [multiDescendantMarkSpace_eq_iSup]
  apply indep_of_indep_of_le_left
    (multiMarksOnSpace_independent μ (H.inspected j)
      (multiDescendantAddresses root) hfresh)
  exact H.domain_le j

theorem multiSubtreeMarks_descendant_measurable {m : ℕ}
    (root : Fin m × TreeNode) :
    Measurable[multiDescendantMarkSpace root] (multiSubtreeMarks root) := by
  apply (@measurable_pi_iff (MultiRootTree m) TreeNode
    (fun _ => OffspringMark) (multiDescendantMarkSpace root)
    (fun _ => inferInstance) (multiSubtreeMarks root)).2
  intro tail
  have hle : multiCoordinateSpace (root.1, root.2 ++ tail) ≤
      multiDescendantMarkSpace root := by
    unfold multiDescendantMarkSpace
    exact le_iSup (fun v : TreeNode =>
      multiCoordinateSpace (root.1, root.2 ++ v)) tail
  have hcoord : Measurable[multiCoordinateSpace
      (root.1, root.2 ++ tail)]
      (fun ω : MultiRootTree m => ω root.1 (root.2 ++ tail)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem MultiRootExplorationDomains.fresh_subtree_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m : ℕ} (H : MultiRootExplorationDomains m)
    (j : ℕ) (root : Fin m × TreeNode)
    (hfresh : Disjoint (H.inspected j) (multiDescendantAddresses root)) :
    Indep (H.domain j)
      (MeasurableSpace.comap (multiSubtreeMarks root) inferInstance)
      (iidMultiRootLaw μ m) :=
  indep_of_indep_of_le_right
    (H.fresh_descendant_independent μ j root hfresh)
    (multiSubtreeMarks_descendant_measurable root).comap_le

end ThesisSpeed
