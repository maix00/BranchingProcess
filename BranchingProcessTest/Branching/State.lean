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
