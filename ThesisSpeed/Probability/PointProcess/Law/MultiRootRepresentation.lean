import ThesisSpeed.Probability.PointProcess.Enumeration.FromMeasure
import ThesisSpeed.Probability.Genealogy.MultiRoot

/-!
# Abstract point-process laws on several initial roots

An ordered slot representation is first pushed forward to one offspring-mark
law. The existing infinite-product construction then attaches independent
copies at every address of every labelled initial root.
-/

open MeasureTheory

namespace ThesisSpeed

theorem representedMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : OffspringPointProcess Ω)
    (r : OrderedSlotRepresentation Ξ) {m : ℕ}
    (i : Fin m) (u : TreeNode) :
    (iidMultiRootLaw (r.markLaw P) m).map
        (fun ω : MultiRootTree m => offspringPointMeasure (ω i u)) =
      P.map Ξ := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (iidMultiRootLaw (r.markLaw P) m).map
        (fun ω : MultiRootTree m => offspringPointMeasure (ω i u)) =
        ((iidMultiRootLaw (r.markLaw P) m).map
          (fun ω : MultiRootTree m => ω i u)).map
            offspringPointMeasure := by
          rw [Measure.map_map]
          · rfl
          · exact offspringPointMeasure_measurable
          · exact (measurable_pi_apply u).comp (measurable_pi_apply i)
    _ = (r.markLaw P).map offspringPointMeasure := by
      rw [iidMultiRoot_mark_marginal]

theorem representedMultiRoot_all_ordered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : OffspringPointProcess Ω)
    (r : OrderedSlotRepresentation Ξ) (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : TreeNode, ω i u ∈ orderedOffspring :=
  iidMultiRoot_all_ordered (r.markLaw P) (r.markLaw_ordered P) m

theorem representedMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : OffspringPointProcess Ω)
    (r : OrderedSlotRepresentation Ξ) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂iidMultiRootLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : TreeNode, ω i u ∈ childRealized 0 := by
  exact iidMultiRoot_all_first_child (r.markLaw P)
    (r.markLaw_ordered P) (r.markLaw_nonempty P hnonempty) m

/-- The multi-root construction for the canonical representation of the
abstract point process. No representation hypothesis remains in this API. -/
theorem canonicalMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : OffspringPointProcess Ω)
    {m : ℕ} (i : Fin m) (u : TreeNode) :
    (iidMultiRootLaw ((canonicalOrderedSlotRepresentation Ξ).markLaw P) m).map
        (fun ω : MultiRootTree m => offspringPointMeasure (ω i u)) =
      P.map Ξ :=
  representedMultiRoot_pointMeasure_marginal P Ξ
    (canonicalOrderedSlotRepresentation Ξ) i u

theorem canonicalMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : OffspringPointProcess Ω) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂iidMultiRootLaw
        ((canonicalOrderedSlotRepresentation Ξ).markLaw P) m,
      ∀ i : Fin m, ∀ u : TreeNode, ω i u ∈ childRealized 0 :=
  representedMultiRoot_all_first_child P Ξ
    (canonicalOrderedSlotRepresentation Ξ) m hnonempty

end ThesisSpeed
