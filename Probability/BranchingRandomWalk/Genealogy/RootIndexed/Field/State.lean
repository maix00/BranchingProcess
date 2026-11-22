/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.BranchingWalk.State
public import Probability.Process.Tree.Line.Information.Observations
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Positions

/-!
# General state updates and generation observability

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.stateAlong_filtration_measurable`:
  if $|v|+|p|\le n$, an initial state observable at generation $n$ and a
  jointly measurable update $F:S\times E\to S$ produce a terminal state
  observable at generation $n$. The state and mark spaces are arbitrary.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.state_measurable_ancestralPast`:
  the state at `(i,u)` is measurable from the initial information and the
  reproduction records of strict ancestors of `(i,u)`, for any measurable
  update `F : State × Mark → State`. The sample domain and all state spaces
  are arbitrary; no probability law, countability, or additive structure is needed.
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

/-- A node's birth state uses its strict ancestors' reproduction, not its own reproduction. -/
theorem state_measurable_ancestralPast {Ω Root α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (β : Ω → StepField Root α Mark) (x : Ω → Root → State)
    (initial : MeasurableSpace Ω)
    (hx : ∀ i, Measurable[initial] (fun ω => x ω i))
    (i : Root) (u : TreeNode α) :
    Measurable[ProbabilityTheory.Tree.ancestralPast initial
      (fun v : Root × TreeNode α =>
        MeasurableSpace.comap (fun ω => β ω v.1 v.2) inferInstance) (i, u)]
      (fun ω => stateAlong F (β ω i) (x ω i) [] u) := by
  let coordinate (v : Root × TreeNode α) : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω => β ω v.1 v.2) inferInstance
  let information := ProbabilityTheory.Tree.ancestralPast initial coordinate (i, u)
  let : MeasurableSpace Ω := information
  change Measurable (fun ω => stateAlong F (β ω i) (x ω i) [] u)
  apply stateAlong_measurable F hF (fun ω => β ω i) (fun ω => x ω i) [] u
  · exact (hx i).mono le_sup_left le_rfl
  · intro k hk
    have hparent : Combinatorics.UlamHarris.RootIndexed.IsAncestor (i, u.take k) (i, u) :=
      ⟨rfl, List.take_prefix k u⟩
    have hne : (i, u.take k) ≠ (i, u) := by
      intro heq
      have hlen := congrArg (fun v : Root × TreeNode α => v.2.length) heq
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hlen
      omega
    have hcoordinate := ProbabilityTheory.Tree.coordinate_le_ancestralPast
      initial coordinate hparent hne
    have hp : Measurable (fun ω => β ω i (u.take k)) :=
      Measurable.of_comap_le hcoordinate
    simpa only [List.nil_append, Function.comp_def] using (measurable_pi_apply (u[k])).comp hp

/-- The original additive position is the additive case of the update construction. -/
theorem state_add_eq_position {Root α Mark Position : Type*} [AddCommMonoid Position]
    (β : Combinatorics.Branching.RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) (i : Root) (u : TreeNode α) :
    β.state (fun s e => s + d e) i u = position β.initial d β.step i u := by
  exact stateAlong_add d (β.step i) (β.initial i) [] u

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
