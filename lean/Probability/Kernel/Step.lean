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

/-- At a fixed source, a realized step is the pushforward of its noise law. -/
theorem ofStep_apply_eq_map (ν : Measure ξ) [SFinite ν]
    [MeasurableSingletonClass α]
    (step : α → ξ → β) (hstep : Measurable (Function.uncurry step))
    (a : α) :
    ofStep ν step hstep a = ν.map (step a) := by
  have hstepa : Measurable (step a) :=
    hstep.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [ofStep_apply ν step hstep a s hs,
    Measure.map_apply hstepa hs]
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

/-- Integrating against a partial-step kernel integrates over the noise and
assigns value zero to killed outcomes. -/
theorem lintegral_ofPartialStep (ν : Measure ξ) [SFinite ν]
    [MeasurableSingletonClass α]
    (step : α → ξ → Option β)
    (hstep : Measurable (Function.uncurry step))
    (a : α) (f : β → ENNReal) (hf : Measurable f) :
    ∫⁻ b, f b ∂ofPartialStep ν step hstep a =
      ∫⁻ z, (step a z).elim 0 f ∂ν := by
  let g : Option β → ENNReal := fun o => o.elim 0 f
  have hg : Measurable g := measurable_option_elim 0 hf
  have hstepa : Measurable (step a) :=
    hstep.comp (measurable_const.prodMk measurable_id)
  calc
    (∫⁻ b, f b ∂ofPartialStep ν step hstep a) =
        ∫⁻ o, g o ∂(ofPartialStep ν step hstep a).map some := by
      rw [measurableEmbedding_option_some.lintegral_map]
      rfl
    _ = ∫⁻ o, g o ∂(ofStep ν step hstep a).restrict (Set.range some) := by
      rw [ofPartialStep, Kernel.comapRight_apply,
        measurableEmbedding_option_some.map_comap]
    _ = ∫⁻ o, g o ∂ofStep ν step hstep a := by
      rw [← MeasureTheory.lintegral_indicator
        measurableEmbedding_option_some.measurableSet_range]
      congr 1
      funext o
      cases o <;> simp [g]
    _ = ∫⁻ z, g (step a z) ∂ν := by
      rw [ofStep_apply_eq_map ν step hstep a,
        MeasureTheory.lintegral_map hg hstepa]
    _ = _ := rfl

end ProbabilityTheory.Kernel
