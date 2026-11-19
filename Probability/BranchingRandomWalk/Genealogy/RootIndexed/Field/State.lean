/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.BranchingWalk.State
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Positions

/-!
# General state updates and generation observability

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.stateAlong_filtration_measurable`:
  if $|v|+|p|\le n$, an initial state observable at generation $n$ and a
  jointly measurable update $F:S\times E\to S$ produce a terminal state
  observable at generation $n$. The state and mark spaces are arbitrary.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.state_add_eq_position`:
  for $F(s,e)=s+d(e)$, the state of a bundled walk equals its existing
  additive position $\operatorname{initial}(i)+\operatorname{displace}(d,β,i,u)$.

The measurable update changes the interpretation of child marks, not the
underlying tree, generation filtration, or branching law.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

/-- State evolution uses only the branching coordinates before the terminal
generation and the supplied initial state. -/
theorem stateAlong_filtration_measurable {Root α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (i : Root) (v p : TreeNode α) (n : ℕ) (hn : v.length + p.length ≤ n)
    (s : StepField Root α Mark → State)
    (hs : Measurable[stepFiltration (Root := Root) (α := α) (X := Mark) n] s) :
    Measurable[stepFiltration (Root := Root) (α := α) (X := Mark) n]
      (fun ω : StepField Root α Mark => stateAlong F (ω i) (s ω) v p) := by
  let : MeasurableSpace (StepField Root α Mark) :=
    stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply stateAlong_measurable F hF (fun ω => ω i) s v p hs
  intro k hk
  apply (measurable_pi_apply (p[k])).comp
  apply step_measurable
  simp only [List.length_append, List.length_take]
  omega

/-- The original additive position is the additive case of the update construction. -/
theorem state_add_eq_position {Root α Mark Position : Type*} [AddCommMonoid Position]
    (β : Combinatorics.Branching.RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) (i : Root) (u : TreeNode α) :
    β.state (fun s e => s + d e) i u = position β.initial d β.step i u := by
  exact stateAlong_add d (β.step i) (β.initial i) [] u

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
