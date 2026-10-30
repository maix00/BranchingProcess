/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Combinatorics.BranchingWalk.Step.Ordering.OrderDual

/-!
# Order-dual generation environments

The order-dual map is applied coordinatewise to an i.i.d. sequence of
$N$-parent offspring batches. The resulting batch and environment laws are the
corresponding finite and infinite product laws of the mapped offspring
measure.

## Public declarations

For a probability measure \(\mu\) on offspring steps and capacity \(N\),
let the mapped one-generation law be
\[
  \mu^\dagger:=\operatorname{Measure.map}
    (\operatorname{stepOrderDual})\,\mu,
\]
the batch and environment transformations satisfy
\[
  \operatorname{Measure.map}(\operatorname{generationBatchOrderDual})
    (\operatorname{generationBatchLaw}\,\mu\,N)
      =(\mu^\dagger)^{\otimes N},
  \qquad
  \operatorname{Measure.map}(\operatorname{generationEnvironmentOrderDual})
    (\operatorname{generationEnvironmentLaw}\,\mu\,N)
      =((\mu^\dagger)^{\otimes N})^{\otimes\mathbb N}.
\]
Here \(\operatorname{generationBatchOrderDual}\) applies
\(\operatorname{stepOrderDual}\) in each of the \(N\) parent coordinates,
and \(\operatorname{generationEnvironmentOrderDual}\) applies that map at
every generation.

- `generationBatchOrderDual` maps every child step in a generation batch
  through `stepOrderDual`.
- `generationEnvironmentOrderDual` applies that map at every generation.
- `generationBatchLaw_orderDual_map` and
  `generationEnvironmentLaw_orderDual_map` identify the image laws with the
  corresponding product laws.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching

/-- A generation batch observed in the dual order. -/
abbrev OrderDualGenerationBatch (N : ℕ) :=
  Fin N → Step ℕ (OrderDual ℝ)

def generationBatchOrderDual {N : ℕ} (batch : GenerationBatch N) :
    OrderDualGenerationBatch N :=
  fun i => stepOrderDual (batch i)

theorem measurable_generationBatchOrderDual {N : ℕ} :
    Measurable (generationBatchOrderDual (N := N)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_stepOrderDual.comp (measurable_pi_apply i)

/-- The i.i.d. generation law after changing only the order observation. -/
noncomputable def orderDualGenerationBatchLaw
    (μ : Measure (Step ℕ ℝ)) (N : ℕ) :
    Measure (OrderDualGenerationBatch N) :=
  Measure.pi (fun _ : Fin N => Measure.map stepOrderDual μ)

theorem generationBatchLaw_orderDual_map
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    (generationBatchLaw μ N).map (generationBatchOrderDual (N := N)) =
      orderDualGenerationBatchLaw μ N := by
  classical
  unfold generationBatchLaw orderDualGenerationBatchLaw
  change (Measure.pi (fun _ : Fin N => μ)).map
      (fun batch i => stepOrderDual (batch i)) =
        Measure.pi (fun _ : Fin N => Measure.map stepOrderDual μ)
  rw [Measure.pi_map_pi
    (hf := fun _ => measurable_stepOrderDual.aemeasurable)]

abbrev OrderDualGenerationEnvironment (N : ℕ) :=
  ℕ → OrderDualGenerationBatch N

def generationEnvironmentOrderDual {N : ℕ}
    (ω : ℕ → GenerationBatch N) : OrderDualGenerationEnvironment N :=
  fun t => generationBatchOrderDual (ω t)

theorem measurable_generationEnvironmentOrderDual {N : ℕ} :
    Measurable (generationEnvironmentOrderDual (N := N)) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_generationBatchOrderDual.comp (measurable_pi_apply t)

noncomputable def orderDualGenerationEnvironmentLaw
    (μ : Measure (Step ℕ ℝ)) (N : ℕ) :
    Measure (OrderDualGenerationEnvironment N) :=
  Measure.infinitePi (fun _ : ℕ => orderDualGenerationBatchLaw μ N)

theorem generationEnvironmentLaw_orderDual_map
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    (generationEnvironmentLaw μ N).map
        (generationEnvironmentOrderDual (N := N)) =
      orderDualGenerationEnvironmentLaw μ N := by
  unfold generationEnvironmentLaw orderDualGenerationEnvironmentLaw
  change (Measure.infinitePi (fun _ : ℕ => generationBatchLaw μ N)).map
      (fun ω t => generationBatchOrderDual (ω t)) =
        Measure.infinitePi (fun _ : ℕ => orderDualGenerationBatchLaw μ N)
  rw [Measure.infinitePi_map_pi
    (fun _ : ℕ => generationBatchLaw μ N)
    (fun _ => measurable_generationBatchOrderDual)]
  simp_rw [generationBatchLaw_orderDual_map]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
