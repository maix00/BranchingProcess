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
      (ProbabilityTheory.BranchingProcess.State.treeKernel
        (ProbabilityTheory.BranchingProcess.offspringStateKernel
          (fun (s : ℝ) (e : ℝ × ℝ) ↦ e.1 * s + e.2) (by fun_prop)
          (ProbabilityTheory.Kernel.const ℝ μ))) := inferInstance

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
#print axioms ProbabilityTheory.BranchingProcess.State.map_stateTree_offspringFieldLaw
#print axioms ProbabilityTheory.BranchingRandomWalk.Exploration.State.condExp_selectedTrees
#print axioms ProbabilityTheory.BranchingRandomWalk.Exploration.State.condExp_stoppedTrees
#print axioms ProbabilityTheory.BranchingRandomWalk.Exploration.State.condExp_stoppedTrees_on_finite

-- Additive observations are definitionally instances of the common update
-- recursion; this guards the dependency direction, including noncommutative monoids.
example {α X : Type*} [AddMonoid X] (β : StepField α X) (v p : List α) :
    displace β v p = stateAlong (fun s e ↦ s + e) β 0 v p := rfl

example {α X : Type*} [AddMonoid X] (β : StepField α X) (v p : List α) :
    displace? β v p = stateAlong? (fun s e ↦ s + e) β 0 v p := rfl

-- Presence inspection requires no equality or inhabitance of either index or mark type.
example {α Mark : Type*} (β : StepField α Mark) (v p : List α) :
    Decidable (surviveAlong β v p) := surviveAlong.decidable β v p

-- A field realization is identified with the one canonical state kernel,
-- for arbitrary jointly measurable updates and probability offspring laws.
example {α Mark S : Type*} [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) :
    (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ).map (stateTree F s) =
      ProbabilityTheory.BranchingProcess.State.treeKernel
        (ProbabilityTheory.BranchingProcess.offspringStateKernel F hF
          (ProbabilityTheory.Kernel.const S μ)) (some s) :=
  ProbabilityTheory.BranchingProcess.State.map_stateTree_offspringFieldLaw μ F hF s
