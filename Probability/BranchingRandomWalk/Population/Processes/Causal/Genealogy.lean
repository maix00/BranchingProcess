import Probability.BranchingRandomWalk.Population.Processes.Causal
import Combinatorics.BranchingWalk.Population.Genealogy

/-!
# Samplewise genealogy of causal populations

The genealogical theorems are proved in the deterministic combinatorial
layer.  This file only evaluates an adapted random population at a sample and
reexports the resulting consequences.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

namespace RootIndexed.CausalPopulation

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}

 theorem initial_mem_and_surviveAlong
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    (p.1, []) ∈ P 0 ω ∧ surviveAlong (stepField ω p.1) [] p.2 :=
  (P.toPopulation ω).initial_mem_and_surviveAlong hp

theorem initial_mem_of_mem
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    (p.1, []) ∈ P 0 ω :=
  (P.initial_mem_and_surviveAlong hp).1

theorem surviveAlong_of_mem
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    surviveAlong (stepField ω p.1) [] p.2 :=
  (P.initial_mem_and_surviveAlong hp).2

theorem parent_mem_of_mem_succ
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {q : RootIndexed.TreeNode Root α}
    (hq : q ∈ P (n + 1) ω) : parent q ∈ P n ω :=
  (P.toPopulation ω).parent_mem_of_mem_succ hq

theorem prefix_mem_of_mem
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α}
    (hp : p ∈ P n ω) {k : ℕ} (hk : k ≤ n) :
    (p.1, p.2.take k) ∈ P k ω :=
  (P.toPopulation ω).prefix_mem_of_mem hp k hk

end RootIndexed.CausalPopulation

end ProbabilityTheory.BranchingRandomWalk
