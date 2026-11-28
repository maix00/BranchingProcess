/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.Endpoint

/-!
# Measurable changes of noise in partial steps

## Public declarations

In `ProbabilityTheory.Kernel`:

* `runPartialSteps_comp_noise` identifies execution with transformed noise:
  `run(step ∘ f, z) = run(step, f ∘ z)`.
* `ofPartialStep_map_noise` identifies the kernels
  `ofPartialStep (ν.map f) step = ofPartialStep ν (fun x z => step x (f z))`.

Both identities use the existing partial step and its native pushforward law.
They require no injectivity, independence, moment or countability assumptions.
-/

@[expose] public section
namespace ProbabilityTheory.Kernel
open MeasureTheory

set_option backward.isDefEq.respectTransparency false

theorem runPartialSteps_comp_noise {S E F : Type*}
    (step : S → F → Option S) (f : E → F) (n : ℕ)
    (x : S) (history : Fin n → E) :
    runPartialSteps (fun x z => step x (f z)) n x history =
      runPartialSteps step n x (fun j => f (history j)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [runPartialSteps]
    cases h : step x (f (history 0)) with
    | none => simp
    | some y =>
      simp only [Option.bind_some]
      rw [ih]
      congr 1

theorem ofPartialStep_map_noise {S E F : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure E) [SFinite ν] (f : E → F) (hf : Measurable f)
    [SFinite (ν.map f)] (step : S → F → Option S)
    (hs : Measurable (Function.uncurry step)) :
    ofPartialStep (ν.map f) step hs =
      ofPartialStep ν (fun x z => step x (f z))
        (hs.comp (measurable_fst.prodMk (hf.comp measurable_snd))) := by
  ext x target ht
  rw [ofPartialStep_apply (ν.map f) step hs x target ht,
    ofPartialStep_apply ν _ _ x target ht]
  rw [Measure.map_apply hf]
  · rfl
  · exact (measurableSet_option_some_image ht).preimage
      (hs.comp (measurable_const.prodMk measurable_id))

end ProbabilityTheory.Kernel
