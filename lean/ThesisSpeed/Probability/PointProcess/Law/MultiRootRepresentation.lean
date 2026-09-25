import ThesisSpeed.Probability.PointProcess.Representation.FromMeasure
import ThesisSpeed.Probability.PointProcess.Representation.RealLineEnumeration
import ThesisSpeed.Probability.Genealogy.RootIndexed.Law

/-!
# Abstract point-process laws on several initial roots

An ordered slot representation is first pushed forward to one child-mark
law. The existing infinite-product construction then attaches independent
copies at every address of every labelled initial root.
-/

open MeasureTheory

namespace ThesisSpeed

theorem representedMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealBranchingStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) {m : ℕ}
    (i : Fin m) (u : 𝕍) :
    (finiteRootBranchingStepFieldLaw (r.markLaw P) m).map
        (fun ω : FiniteRootBranchingStepField m ℝ => branchingStepPointMeasure (ω i u)) =
      P.map Ξ := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (finiteRootBranchingStepFieldLaw (r.markLaw P) m).map
        (fun ω : FiniteRootBranchingStepField m ℝ => branchingStepPointMeasure (ω i u)) =
        ((finiteRootBranchingStepFieldLaw (r.markLaw P) m).map
          (fun ω : FiniteRootBranchingStepField m ℝ => ω i u)).map
            branchingStepPointMeasure := by
          rw [Measure.map_map]
          · rfl
          · exact branchingStepPointMeasure_measurable
          · exact (measurable_pi_apply u).comp (measurable_pi_apply i)
    _ = (r.markLaw P).map branchingStepPointMeasure := by
      rw [finiteRootBranchingStepFieldLaw_coordinate_marginal]

theorem representedMultiRoot_all_ordered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealBranchingStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ) :
    ∀ᵐ ω ∂finiteRootBranchingStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ orderedBranchingSteps :=
  finiteRootBranchingStepFieldLaw_all_ordered (r.markLaw P) (r.markLaw_ordered P) m

theorem representedMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealBranchingStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootBranchingStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ childRealized 0 := by
  exact finiteRootBranchingStepFieldLaw_all_first_child (r.markLaw P)
    (r.markLaw_ordered P) (r.markLaw_nonempty P hnonempty) m

/-- The multi-root construction for the canonical representation of the
abstract point process. No representation hypothesis remains in this API. -/
theorem canonicalMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealBranchingStepPointProcess Ω)
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    (finiteRootBranchingStepFieldLaw ((canonicalMonotoneEnumeration Ξ).markLaw P) m).map
        (fun ω : FiniteRootBranchingStepField m ℝ => branchingStepPointMeasure (ω i u)) =
      P.map Ξ :=
  representedMultiRoot_pointMeasure_marginal P Ξ
    (canonicalMonotoneEnumeration Ξ) i u

theorem canonicalMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealBranchingStepPointProcess Ω) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootBranchingStepFieldLaw
        ((canonicalMonotoneEnumeration Ξ).markLaw P) m,
      ∀ i : Fin m, ∀ u : 𝕍, ω i u ∈ childRealized 0 :=
  representedMultiRoot_all_first_child P Ξ
    (canonicalMonotoneEnumeration Ξ) m hnonempty

end ThesisSpeed
