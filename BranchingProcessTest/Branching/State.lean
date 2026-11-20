import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.State
import Combinatorics.BranchingWalk.MarkedTree.State
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.State
import Probability.BranchingProcess.Offspring.Kernel
import MeasureTheory.BranchingWalk.MarkedTree

open Combinatorics.Branching
open MeasureTheory

-- Nonadditive updates retain their chronological order.
example : stateAlong (fun (s e : Bool) => if e then !s else true)
    (fun (v : List Unit) _ => some (!v.isEmpty)) false [] [(), ()] = false := rfl

-- No mark type inhabitant is required when the field has no children.
example (s : Bool) : stateAlong (fun (_s : Bool) (e : Empty) => nomatch e)
    (fun (_ : List Unit) _ => none) s [] [()] = s := rfl

-- Random initial states may depend on the same sample as the mark field.
example {Ω α Mark State : Type*} [MeasurableSpace Ω] [MeasurableSpace Mark]
    [MeasurableSpace State]
    (β : Ω → Combinatorics.Branching.RootIndexed.BranchingWalk Unit α Mark State)
    (hβ : Measurable β) (F : State → Mark → State)
    (hF : Measurable (Function.uncurry F)) (u : List α) :
    Measurable (fun w => (β w).state F () u) :=
  (Combinatorics.Branching.RootIndexed.BranchingWalk.state_measurable F hF () u).comp hβ

-- The existing additive position is exactly the general state interpretation.
example {Root α Mark Position : Type*} [AddCommMonoid Position]
    (β : Combinatorics.Branching.RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) (r : Root) (u : List α) :
    β.state (fun s e => s + d e) r u =
      ProbabilityTheory.BranchingRandomWalk.RootIndexed.position β.initial d β.step r u :=
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.state_add_eq_position β d r u

#print axioms Combinatorics.Branching.stateAlong_add
#print axioms Combinatorics.Branching.RootIndexed.BranchingWalk.state_measurable
#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.stateAlong_filtration_measurable

-- State-dependent families use the full indexed offspring kernel, not a mixture
-- over parent states. Updating marks preserves the probability-kernel property.
example {ι Mark State : Type*} [MeasurableSpace Mark] [MeasurableSpace State]
    (Q : ProbabilityTheory.Kernel State (Step ι Mark))
    [ProbabilityTheory.IsMarkovKernel Q] (F : State → Mark → State)
    (hF : Measurable (Function.uncurry F)) :
    ProbabilityTheory.IsMarkovKernel
      (ProbabilityTheory.BranchingProcess.offspringStateKernel F hF Q) := inferInstance

#print axioms ProbabilityTheory.BranchingProcess.offspringStateKernel_apply
#print axioms ProbabilityTheory.BranchingProcess.branchingPointMeasureKernel_apply
#print axioms Combinatorics.Branching.RootIndexed.BranchingWalk.stateMarkedTree_measurable

-- The affine update is jointly measurable and induces a probability kernel
-- on complete state trees under any probability offspring-mark law.
example : Measurable (Function.uncurry (fun (s : ℝ) (e : ℝ × ℝ) ↦ e.1 * s + e.2)) := by
  fun_prop

example (μ : Measure (Step Bool (ℝ × ℝ))) [IsProbabilityMeasure μ] :
    ProbabilityTheory.IsMarkovKernel
      (ProbabilityTheory.BranchingProcess.stateTreeKernel μ
        (fun (s : ℝ) (e : ℝ × ℝ) ↦ e.1 * s + e.2) (by fun_prop)) :=
  ProbabilityTheory.BranchingProcess.stateTreeKernel.isMarkovKernel μ _ _

-- A real, nonadditive update: two affine steps multiply the root state and
-- transform the first offset before adding the second one.
example (x a₁ b₁ a₂ b₂ : ℝ) :
    stateAlong (fun (s : ℝ) (e : ℝ × ℝ) ↦ e.1 * s + e.2)
      (fun (u : List Unit) _ ↦ some (if u = [] then (a₁, b₁) else (a₂, b₂)))
      x [] [(), ()] = a₂ * a₁ * x + a₂ * b₁ + b₂ := by
  simp [stateAlong]
  ring

-- Subtracting the root state does not give a common state-tree law for this
-- update: after two steps a unit change of initial state gives a change of four.
example : stateAlong (fun (s e : ℝ) ↦ 2 * s + e)
      (fun (_ : List Unit) _ ↦ some 1) 1 [] [(), ()] -
    stateAlong (fun (s e : ℝ) ↦ 2 * s + e)
      (fun (_ : List Unit) _ ↦ some 1) 0 [] [(), ()] = 4 := by
  norm_num [stateAlong]

-- A state subtree preserves the survival domain and all descendant states.
example {α Mark State : Type*} (F : State → Mark → State)
    (s : State) (β : StepField α Mark) (u v : List α)
    (hu : surviveAlong β [] u) :
    stateTree F (stateAlong F β s [] u) (fun w ↦ β (u ++ w)) v =
      stateTree F s β (u ++ v) := stateTree_subtree F s β u v hu

#print axioms Combinatorics.Branching.stateTree_subtree
#print axioms Combinatorics.Branching.stateTree_add
#print axioms Combinatorics.Branching.stateTree_measurable
#print axioms ProbabilityTheory.Indep.condExp_prod_ae_eq_integral_map
#print axioms ProbabilityTheory.BranchingProcess.stateTreeKernel_apply
#print axioms ProbabilityTheory.BranchingProcess.stateTreeKernel_family
#print axioms ProbabilityTheory.BranchingProcess.condExp_stateTree_family
#print axioms ProbabilityTheory.BranchingRandomWalk.selected_stateTree_family_condExp
#print axioms ProbabilityTheory.BranchingRandomWalk.stopped_stateTree_family_condExp
#print axioms ProbabilityTheory.BranchingRandomWalk.stopped_stateTree_family_condExp_on_finite
