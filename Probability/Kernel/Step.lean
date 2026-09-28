import MeasureTheory.MeasurableSpace.Option
import Probability.Kernel.SubMarkov
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Kernels realized by random steps

The API takes the noise law and the measurable step function directly.  No
separate realization structure is introduced.  An option-valued step loses
the mass mapped to `none`, and therefore defines a sub-Markov kernel.
-/

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {α ξ β : Type*} [MeasurableSpace α] [MeasurableSpace ξ]
  [MeasurableSpace β]

/-- The Markov kernel realized by noise with law `ν` and a measurable step
`step : α → ξ → β`. -/
noncomputable def ofStep (ν : Measure ξ) [SFinite ν]
    (step : α → ξ → β) (_hstep : Measurable (Function.uncurry step)) :
    Kernel α β :=
  Kernel.map
    ((Kernel.id : Kernel α α) ⊗ₖ Kernel.const (α × α) ν)
    (Function.uncurry step)

noncomputable instance ofStep.instIsMarkovKernel
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → β) (hstep : Measurable (Function.uncurry step)) :
    IsMarkovKernel (ofStep ν step hstep) := by
  unfold ofStep
  exact IsMarkovKernel.map _ hstep

/-- The sub-Markov kernel realized by an option-valued random step.  Noise
mapped to `none` is discarded; `some b` contributes mass at `b`. -/
noncomputable def ofPartialStep (ν : Measure ξ) [SFinite ν]
    (step : α → ξ → Option β)
    (hstep : Measurable (Function.uncurry step)) : Kernel α β :=
  (ofStep ν step hstep).comapRight measurableEmbedding_option_some

noncomputable instance ofPartialStep.instIsSubMarkovKernel
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option β)
    (hstep : Measurable (Function.uncurry step)) :
    IsSubMarkovKernel (ofPartialStep ν step hstep) where
  measure_univ_le_one a := by
    rw [ofPartialStep, Kernel.comapRight_apply' _ _ _ .univ]
    let _ : IsProbabilityMeasure (ofStep ν step hstep a) :=
      IsMarkovKernel.isProbabilityMeasure a
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ

/-- Evaluation of a realized total step. -/
theorem ofStep_apply (ν : Measure ξ) [SFinite ν]
    [MeasurableSingletonClass α]
    (step : α → ξ → β) (hstep : Measurable (Function.uncurry step))
    (a : α) (s : Set β) (hs : MeasurableSet s) :
    ofStep ν step hstep a s = ν {z | step a z ∈ s} := by
  rw [ofStep, Kernel.map_apply' _ hstep _ hs,
    Kernel.compProd_apply (hstep hs) _ _ _]
  simp only [Kernel.id_apply, Kernel.const_apply]
  rw [lintegral_dirac]
  rfl

/-- Evaluation of a realized partial step. -/
theorem ofPartialStep_apply (ν : Measure ξ) [SFinite ν]
    [MeasurableSingletonClass α]
    (step : α → ξ → Option β)
    (hstep : Measurable (Function.uncurry step))
    (a : α) (s : Set β) (hs : MeasurableSet s) :
    ofPartialStep ν step hstep a s = ν {z | step a z ∈ some '' s} := by
  rw [ofPartialStep, Kernel.comapRight_apply' _ _ _ hs,
    ofStep_apply ν step hstep _ _ (measurableSet_option_some_image hs)]

end ProbabilityTheory.Kernel
