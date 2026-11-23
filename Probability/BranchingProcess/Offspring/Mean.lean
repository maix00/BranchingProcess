/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Offspring.Kernel
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# The mean offspring-state kernel

## Public declarations

In `ProbabilityTheory.BranchingProcess`:

* `meanChildKernel Q` is `M(s,A) = E_Q(s)[∑_i 1_{ξ_i ∈ A}]`.
  Missing slots contribute zero; infinitely many offspring are allowed.
* `meanChildKernel.isSFiniteKernel` proves s-finiteness for countable slots
  and an s-finite offspring kernel.
* `lintegral_meanChildKernel` states `M f(s) = E_Q(s)[∑_i f(ξ_i)]`.

This mean kernel separates the offspring family law from its first moment.
It supplies the kernel whose positive harmonic functions drive a general
spine transform. Compare Zhan Shi, *Branching Random Walks* (2015), §4.2,
(4.1)–(4.4), [author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [Countable ι]

/-- The expected child counting measure, retaining only present child states. -/
noncomputable def meanChildKernel (Q : Kernel S (Step ι S)) : Kernel S S :=
  Kernel.sum fun i => (Q.map (fun ξ => ξ i)).comapRight measurableEmbedding_option_some

instance meanChildKernel.isSFiniteKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q] :
    IsSFiniteKernel (meanChildKernel Q) := by
  unfold meanChildKernel
  infer_instance

/-- A mean-kernel integral is the expected sum of a test over the offspring family. -/
theorem lintegral_meanChildKernel (Q : Kernel S (Step ι S))
    {f : S → ℝ≥0∞} (hf : Measurable f) (s : S) :
    (∫⁻ t, f t ∂meanChildKernel Q s) =
      ∫⁻ ξ, ∑' i, (ξ i).elim 0 f ∂Q s := by
  rw [meanChildKernel, Kernel.sum_apply, lintegral_sum_measure]
  have hg : Measurable (fun o : Option S => o.elim 0 f) := measurable_option_elim 0 hf
  calc
    _ = ∑' i : ι, ∫⁻ ξ, (ξ i).elim 0 f ∂Q s := by
      apply tsum_congr
      intro i
      calc
        _ = ∫⁻ o, o.elim 0 f ∂((Q.map (fun ξ => ξ i)).comapRight
            measurableEmbedding_option_some s).map some := by
          rw [measurableEmbedding_option_some.lintegral_map]
          rfl
        _ = ∫⁻ o, o.elim 0 f ∂Q.map (fun ξ => ξ i) s := by
          rw [Kernel.comapRight_apply, measurableEmbedding_option_some.map_comap,
            ← lintegral_indicator measurableEmbedding_option_some.measurableSet_range]
          apply lintegral_congr
          intro o
          cases o <;> simp
        _ = _ := Kernel.lintegral_map Q (measurable_pi_apply i) s hg
    _ = _ := (lintegral_tsum (fun i =>
      (hg.comp (measurable_pi_apply i)).aemeasurable)).symm

end ProbabilityTheory.BranchingProcess

end
