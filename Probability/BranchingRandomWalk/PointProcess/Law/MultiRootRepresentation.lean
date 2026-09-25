import Probability.BranchingRandomWalk.PointProcess.Representation.FromMeasure
import Probability.BranchingRandomWalk.PointProcess.Representation.RealLineEnumeration
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Abstract point-process laws on several initial roots

An ordered slot representation is first pushed forward to one child-mark
law. The existing infinite-product construction then attaches independent
copies at every address of every labelled initial root.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



theorem representedMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) {m : ℕ}
    (i : Fin m) (u : 𝕍) :
    (finiteRootStepFieldLaw (r.markLaw P) m).map
        (fun ω : FiniteRootStepField m ℝ => stepPointMeasure (ω i u)) =
      P.map Ξ := by
  rw [← r.map_pointMeasure_markLaw P]
  calc
    (finiteRootStepFieldLaw (r.markLaw P) m).map
        (fun ω : FiniteRootStepField m ℝ => stepPointMeasure (ω i u)) =
        ((finiteRootStepFieldLaw (r.markLaw P) m).map
          (fun ω : FiniteRootStepField m ℝ => ω i u)).map
            stepPointMeasure := by
          rw [Measure.map_map]
          · rfl
          · exact stepPointMeasure_measurable
          · exact (measurable_pi_apply u).comp (measurable_pi_apply i)
    _ = (r.markLaw P).map stepPointMeasure := by
      rw [finiteRootStepFieldLaw_coordinate_marginal]

theorem representedMultiRoot_all_ordered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ orderedSteps :=
  finiteRootStepFieldLaw_all_ordered (r.markLaw P) (r.markLaw_ordered P) m

theorem representedMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ childRealized 0 := by
  exact finiteRootStepFieldLaw_all_first_child (r.markLaw P)
    (r.markLaw_ordered P) (r.markLaw_nonempty P hnonempty) m

/-- The multi-root construction for the canonical representation of the
abstract point process. No representation hypothesis remains in this API. -/
theorem canonicalMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    (finiteRootStepFieldLaw ((canonicalMonotoneEnumeration Ξ).markLaw P) m).map
        (fun ω : FiniteRootStepField m ℝ => stepPointMeasure (ω i u)) =
      P.map Ξ :=
  representedMultiRoot_pointMeasure_marginal P Ξ
    (canonicalMonotoneEnumeration Ξ) i u

theorem canonicalMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw
        ((canonicalMonotoneEnumeration Ξ).markLaw P) m,
      ∀ i : Fin m, ∀ u : 𝕍, ω i u ∈ childRealized 0 :=
  representedMultiRoot_all_first_child P Ξ
    (canonicalMonotoneEnumeration Ξ) m hnonempty

end ProbabilityTheory.BranchingRandomWalk
