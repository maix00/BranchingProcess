import Probability.BranchingRandomWalk.PointProcess.Representation.FromMeasure
import Probability.BranchingRandomWalk.PointProcess.Representation.RealLineEnumeration
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Combinatorics.BranchingWalk.Step.Basic
import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Abstract point-process laws on several initial roots

An ordered slot resurviveation is first pushed forward to one child-mark
law. The existing infinite-product construction then attaches independent
copies at every address of every labelled initial root.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



theorem resurviveedMultiRoot_pointMeasure_marginal
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

theorem resurviveedMultiRoot_all_ordered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ orderedSteps :=
  finiteRootStepFieldLaw_all_ordered (r.markLaw P) (r.markLaw_ordered P) m

theorem resurviveedMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    (r : MonotoneEnumeration (X := ℝ) Ξ (· ≤ ·)) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw (r.markLaw P) m, ∀ i : Fin m,
      ∀ u : 𝕍, survive (ω i u) 0 := by
  exact finiteRootStepFieldLaw_all_first_child (r.markLaw P)
    (r.markLaw_ordered P) (r.markLaw_nonempty P hnonempty) m

/-- The multi-root construction for the canonical resurviveation of the
abstract point process. No resurviveation hypothesis remains in this API. -/
theorem canonicalMultiRoot_pointMeasure_marginal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω)
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    (finiteRootStepFieldLaw ((canonicalMonotoneEnumeration Ξ).markLaw P) m).map
        (fun ω : FiniteRootStepField m ℝ => stepPointMeasure (ω i u)) =
      P.map Ξ :=
  resurviveedMultiRoot_pointMeasure_marginal P Ξ
    (canonicalMonotoneEnumeration Ξ) i u

theorem canonicalMultiRoot_all_first_child
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Ξ : RealStepPointProcess Ω) (m : ℕ)
    (hnonempty : P {ω | Ξ ω ≠ 0} = 1) :
    ∀ᵐ ω ∂finiteRootStepFieldLaw
        ((canonicalMonotoneEnumeration Ξ).markLaw P) m,
      ∀ i : Fin m, ∀ u : 𝕍, survive (ω i u) 0 :=
  resurviveedMultiRoot_all_first_child P Ξ
    (canonicalMonotoneEnumeration Ξ) m hnonempty

end ProbabilityTheory.BranchingRandomWalk
