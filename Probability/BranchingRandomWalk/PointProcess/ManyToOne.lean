import Probability.BranchingRandomWalk.PointProcess.Representation.RealLineEnumeration

/-!
# Law-level many-to-one identities

These are the two orientations of the point-process/slot-law identity used
throughout the thesis.  The forward direction pushes the encoded slot law to
the point-measure law; the reverse direction reconstructs the point-process
law from the encoded slots.  Both directions are consequences of the
pointwise `measure_eq` field of `MonotoneEnumeration`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem manyToOne_forward
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop}
    (r : MonotoneEnumeration (X := ℝ) Ξ rel) (P : Measure Ω) :
    (r.markLaw P).map stepPointMeasure = P.map Ξ :=
  r.map_pointMeasure_markLaw P

theorem manyToOne_backward
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop}
    (r : MonotoneEnumeration (X := ℝ) Ξ rel) (P : Measure Ω) :
    P.map Ξ = (r.markLaw P).map stepPointMeasure :=
  (r.map_pointMeasure_markLaw P).symm

theorem manyToOne_integral_forward
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop}
    (r : MonotoneEnumeration (X := ℝ) Ξ rel) (P : Measure Ω)
    (F : Measure ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ η, F η ∂(P.map Ξ) =
      ∫⁻ ξ, F (stepPointMeasure (r.toStep ξ)) ∂P :=
  r.lintegral_pointMeasure_eq P F hF

theorem manyToOne_integral_backward
    {Ω : Type*} [MeasurableSpace Ω] {Ξ : RealStepPointProcess Ω}
    {rel : ℝ → ℝ → Prop}
    (r : MonotoneEnumeration (X := ℝ) Ξ rel) (P : Measure Ω)
    (F : Measure ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ ξ, F (stepPointMeasure (r.toStep ξ)) ∂P =
      ∫⁻ η, F η ∂(P.map Ξ) :=
  (r.lintegral_pointMeasure_eq P F hF).symm

end ProbabilityTheory.BranchingRandomWalk
