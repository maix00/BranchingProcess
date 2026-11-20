/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.BranchingWalk.MarkedTree
public import Probability.BranchingProcess.Offspring.FieldLaw
public import Probability.Independence.ConditionalIntegral

/-!
# Branching with arbitrary measurable state updates

## Public declarations

In namespace `ProbabilityTheory.BranchingProcess`:

* `stateTreeKernel` is the single-root state-tree law
  $P_s=\operatorname{Law}(v\mapsto V_s(v))$, where each offspring family has
  law $\mu$ independently, $V_s(\emptyset)=s$, and
  $V_s(uj)=F(V_s(u),U(uj))$. Absent nodes have value `none`.
* `stateTreeKernel_apply` identifies $P_s$ with the measurable image of the
  offspring-field law; `stateTreeKernel.isMarkovKernel` proves it is a
  probability kernel for every probability offspring law.
* `stateTreeKernel_family` identifies the image of independent offspring
  fields, started at states $s_i$, with $\bigotimes_i P_{s_i}$.
* `condExp_stateTree_family` states the branching identity
  $E[g((V_{S_i}(Y_i))_i)\mid\mathcal H]
    =\int g\,d\bigotimes_i P_{S_i}$ when $S$ is measurable in the past,
  the fresh field vector $Y$ is independent of that past, and its law is the
  independent product offspring-field law. No addition or order is assumed.

This is the independent-mark, general-state-update version of the branching
Markov property in S. Valère Bitseki Penda and J.-F. Delmas,
"Central limit theorem for bifurcating Markov chains", Definition 2.1
(binary families), https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf.
Different siblings may be dependent through their joint offspring-family law.
The complete state-dependent reproduction-kernel construction is separate;
this module starts from a fixed independent offspring-mark law.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingProcess

/-- Single-root law of the realized state tree under a fixed offspring-mark law. -/
noncomputable def stateTreeKernel {α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) :
    Kernel State (TreeNode α → Option State) :=
  (Kernel.deterministic (fun p : State × StepField α Mark ↦ stateTree F p.1 p.2)
    (stateTree_measurable F hF)) ∘ₖ
      (Kernel.id.prod (Kernel.const State (offspringFieldLaw μ)))

theorem stateTreeKernel_apply {α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) (s : State) :
    stateTreeKernel μ F hF s = (offspringFieldLaw μ).map (stateTree F s) := by
  rw [stateTreeKernel, Kernel.deterministic_comp_eq_map (stateTree_measurable F hF),
    Kernel.map_apply _ (stateTree_measurable F hF)]
  ext A hA
  rw [Measure.map_apply (stateTree_measurable F hF) hA,
    Kernel.id_prod_apply' _ _ ((stateTree_measurable F hF) hA), Kernel.const_apply]
  exact (Measure.map_apply ((stateTree_measurable (α := α) F hF).comp
    (measurable_const.prodMk measurable_id)) hA).symm

instance stateTreeKernel.isMarkovKernel {α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) :
    IsMarkovKernel (stateTreeKernel μ F hF) := by
  unfold stateTreeKernel
  infer_instance

/-- Updating independent descendant fields at their respective root states
preserves their product structure. -/
theorem stateTreeKernel_family {ι α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) (s : ι → State) :
    (Measure.infinitePi (fun _ : ι ↦ offspringFieldLaw μ)).map
        (fun fields i ↦ stateTree F (s i) (fields i)) =
      Measure.infinitePi (fun i ↦ stateTreeKernel μ F hF (s i)) := by
  calc
    _ = Measure.infinitePi (fun i ↦ (offspringFieldLaw μ).map (stateTree F (s i))) := by
      apply Measure.infinitePi_map_pi
      intro i
      exact (stateTree_measurable (α := α) F hF).comp
        ((measurable_const (a := s i)).prodMk measurable_id)
    _ = _ := by simp_rw [stateTreeKernel_apply]

/-- Conditional law of a family of state subtrees, with arbitrary past-measurable
root states. The entire realized state trees, including absence, are tested. -/
theorem condExp_stateTree_family {Ω ι α Mark State : Type*}
    (past : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Mark] [MeasurableSpace State]
    (P : Measure Ω) [IsProbabilityMeasure P] (hpast : past ≤ mΩ)
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (s : Ω → ι → State) (hs : Measurable[past] s)
    (fields : Ω → ι → StepField α Mark) (hfields : Measurable fields)
    (hind : Indep past (MeasurableSpace.comap fields inferInstance) P)
    (hlaw : P.map fields = Measure.infinitePi (fun _ : ι ↦ offspringFieldLaw μ))
    (g : (ι → TreeNode α → Option State) → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun w ↦ g (fun i ↦ stateTree F (s w i) (fields w i))) P) :
    condExp past P (fun w ↦ g (fun i ↦ stateTree F (s w i) (fields w i))) =ᵐ[P]
      fun w ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i ↦ stateTreeKernel μ F hF (s w i)) := by
  have hrealize : Measurable (fun p : (ι → State) × (ι → StepField α Mark) ↦
      fun i ↦ stateTree F (p.1 i) (p.2 i)) := by
    apply measurable_pi_iff.mpr
    intro i
    have hpair : Measurable (fun p : (ι → State) × (ι → StepField α Mark) ↦
        (p.1 i, p.2 i)) := by fun_prop
    exact (stateTree_measurable (α := α) F hF).comp hpair
  have hc := hind.condExp_prod_ae_eq_integral_map past hpast hs hfields
    (hg.comp hrealize).stronglyMeasurable hgi
  change condExp past P (fun w ↦ g (fun i ↦ stateTree F (s w i) (fields w i))) =ᵐ[P]
    (fun w ↦ ∫ ys, g (fun i ↦ stateTree F (s w i) (ys i)) ∂P.map fields) at hc
  filter_upwards [hc] with w hw
  rw [hw, hlaw, ← stateTreeKernel_family μ F hF (s w)]
  exact (integral_map ((hrealize.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    hg.aestronglyMeasurable).symm

end ProbabilityTheory.BranchingProcess
