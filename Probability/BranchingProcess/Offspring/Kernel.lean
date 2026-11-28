/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.BranchingWalk.State
public import Probability.BranchingProcess.Offspring.PointMeasure
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# State-dependent branching laws

## Public declarations

* `ProbabilityTheory.BranchingProcess.offspringStateKernel` transforms a
  mark-valued offspring kernel $Q:S\to\mathcal P(\mathrm{Step}(ι,E))$
  into the state-valued offspring kernel induced by $F:S\times E\to S$.
* `ProbabilityTheory.BranchingProcess.offspringStateKernel_apply` states
  $K(s)=Q(s).\mathrm{map}(ξ\mapsto ξ.\mathrm{map}(F(s,\cdot)))$.
* `ProbabilityTheory.BranchingProcess.offspringStateKernel.isMarkovKernel`
  states that this is a probability kernel whenever $Q$ is.
* `ProbabilityTheory.BranchingProcess.offspringStateKernel_const_apply` identifies
  a constant offspring kernel with the existing `OffspringConfigurationLaw.mapMarks`.
* `ProbabilityTheory.BranchingProcess.branchingPointMeasureKernel` forgets
  child indices and retains their marks and multiplicities.
* `ProbabilityTheory.BranchingProcess.branchingPointMeasureKernel_apply`
  states $Q_{\mathrm{point}}(s)=Q(s).\mathrm{map}(\operatorname{stepPointMeasure})$.
* `ProbabilityTheory.BranchingProcess.branchingPointMeasureKernel.isMarkovKernel`
  preserves probability kernels for countably many child slots.

An indexed branching law depending on a parent's state is Mathlib's
`Kernel State (Step ι Mark)` with `IsMarkovKernel`; no duplicate kernel
structure is introduced. `Kernel.const State μ` is the fixed-law case.
Sibling marks may be dependent. Conditional independence between different
parents belongs to the process generated from this kernel, not its definition.

The kernel formalism follows the parent-state/offspring-family formulation
in S. Valère Bitseki Penda and J.-F. Delmas, "Central limit theorem for
bifurcating Markov chains", Definition 2.1
(binary families), https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf.
The constructions below allow arbitrary child-slot types; the countable
point-measure observation uses the existing `stepPointMeasure` interface.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching

namespace ProbabilityTheory.BranchingProcess

/-- Push a parent's offspring marks through a measurable state update. -/
noncomputable def offspringStateKernel {ι Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (Q : Kernel State (Step ι Mark)) : Kernel State (Step ι State) :=
  (Kernel.deterministic (fun p : State × Step ι Mark => p.2.map (F p.1))
    (Step.map_state_measurable F hF)) ∘ₖ (Kernel.id.prod Q)

/-- At each state this is the image of the joint offspring law, retaining indices. -/
theorem offspringStateKernel_apply {ι Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (Q : Kernel State (Step ι Mark)) [IsSFiniteKernel Q] (s : State) :
    offspringStateKernel F hF Q s = (Q s).map (Step.map (F s)) := by
  have hm := Step.map_state_measurable (α := ι) F hF
  have hfixed : Measurable (F s) := hF.comp (measurable_const.prodMk measurable_id)
  rw [offspringStateKernel, Kernel.deterministic_comp_eq_map hm, Kernel.map_apply _ hm]
  ext A hA
  rw [Measure.map_apply hm hA, Kernel.id_prod_apply' Q s (hm hA),
    Measure.map_apply (Step.map_measurable hfixed) hA]
  rfl

instance offspringStateKernel.isMarkovKernel {ι Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (Q : Kernel State (Step ι Mark)) [IsMarkovKernel Q] :
    IsMarkovKernel (offspringStateKernel F hF Q) := by
  unfold offspringStateKernel
  infer_instance

/-- A fixed branching law is the constant-kernel case of state-dependent reproduction. -/
theorem offspringStateKernel_const_apply {ι Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (μ : OffspringConfigurationLaw ι Mark) (s : State) :
    offspringStateKernel F hF (Kernel.const State (μ : Measure (Step ι Mark))) s =
      (μ.mapMarks (F s) (hF.comp (measurable_const.prodMk measurable_id)) :
        Measure (Step ι State)) := by
  rw [offspringStateKernel_apply, Kernel.const_apply]
  rfl

/-- The counting-measure branching law induced by an indexed offspring kernel. -/
noncomputable def branchingPointMeasureKernel {ι Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (Q : Kernel State (Step ι Mark)) : Kernel State (Measure Mark) :=
  Q.map stepPointMeasure

theorem branchingPointMeasureKernel_apply {ι Mark State : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace State]
    (Q : Kernel State (Step ι Mark)) (s : State) :
    branchingPointMeasureKernel Q s = (Q s).map stepPointMeasure :=
  Kernel.map_apply Q stepPointMeasure_measurable s

instance branchingPointMeasureKernel.isMarkovKernel {ι Mark State : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace State]
    (Q : Kernel State (Step ι Mark)) [IsMarkovKernel Q] :
    IsMarkovKernel (branchingPointMeasureKernel Q) :=
  Kernel.IsMarkovKernel.map Q stepPointMeasure_measurable

end ProbabilityTheory.BranchingProcess
