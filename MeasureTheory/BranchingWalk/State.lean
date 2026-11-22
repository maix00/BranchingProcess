/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.State
public import Combinatorics.BranchingWalk.Step.DistinguishedChild
public import MeasureTheory.MeasurableSpace.Option

/-!
# Measurable state updates on branching trees

## Public declarations

* `Combinatorics.Branching.Step.map_state_measurable` states that
  $(s,ξ)\mapsto (j\mapsto ξ(j).\mathrm{map}(F(s,\cdot)))$ is measurable
  for jointly measurable $F:S\times E\to S$.
* `Combinatorics.Branching.stateAlong_measurable` states that along a fixed
  finite path, measurable initial states and measurable child coordinates
  give measurable terminal states for every jointly measurable update
  $F:S\times E\to S$. Only coordinates on that path are required.
* `Combinatorics.Branching.RootIndexed.BranchingWalk.state_measurable`
  states that $β\mapsto β.\operatorname{state}(F,r,u)$ is measurable on the
  bundled walk space when $F$ is jointly measurable.
* `Combinatorics.Branching.Step.distinguishChild_measurable` states that
  distinguishing an eligible selected child is jointly measurable in the
  family and selected index, for a measurable eligibility set and measurable
  index singletons.

The state and mark spaces are arbitrary measurable spaces. No additive,
topological or probability-law assumptions are used. The selected-index
operation additionally uses measurable singletons in the index space.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

open scoped Classical in
/-- A measurable eligibility predicate gives a measurable distinguished-child assignment. -/
theorem Step.distinguishChild_measurable {ι S : Type*}
    [MeasurableSpace S] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {P : S → Prop} (hP : MeasurableSet {s | P s}) :
    Measurable (fun p : Step ι S × ι => Step.distinguishChild P p.1 p.2) := by
  let tag (s : S) : S ⊕ {s // P s} :=
    if hs : P s then Sum.inr ⟨s, hs⟩ else Sum.inl s
  have htag : Measurable tag :=
    Measurable.dite measurable_inr (measurable_inl.comp measurable_subtype_coe) hP
  apply Measurable.of_eval
  intro j
  have heq : (fun p : Step ι S × ι => Step.distinguishChild P p.1 p.2 j) =
      (fun p => if p.2 = j then (p.1 j).map tag else (p.1 j).map Sum.inl) := by
    funext ⟨ξ, i⟩
    by_cases hij : i = j
    · subst i
      cases he : ξ j <;> simp [Step.distinguishChild, tag, he]
    · cases he : ξ j <;> simp [Step.distinguishChild, he, hij, Ne.symm hij]
  rw [heq]
  exact ((measurable_option_map htag).comp ((measurable_pi_apply j).comp measurable_fst)).ite
    ((MeasurableSet.singleton j).preimage measurable_snd)
    ((measurable_option_map measurable_inl).comp ((measurable_pi_apply j).comp measurable_fst))

/-- Updating every present child mark by the parent state is jointly measurable. -/
theorem Step.map_state_measurable {α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : State × Step α Mark => p.2.map (F p.1)) := by
  apply Measurable.of_eval
  intro j
  have ho : Measurable (fun p : State × Step α Mark => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hf : Measurable
      (fun p : (State × Step α Mark) × Mark => some (F p.1.1 p.2)) :=
    measurable_option_some.comp
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  convert ho.option_elim (g := fun _ => (none : Option State))
    (f := fun p e => some (F p.1 e)) measurable_const hf using 1
  funext p
  cases h : p.2 j <;> simp [Step.map, h]

/-- Observing the marks on a fixed path suffices for measurable state evolution. -/
theorem stateAlong_measurable {Ω α Mark State : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (β : Ω → StepField α Mark) (s : Ω → State) (v p : TreeNode α)
    (hs : Measurable s)
    (hβ : ∀ k (hk : k < p.length),
      Measurable (fun w => β w (v ++ p.take k) (p[k]'hk))) :
    Measurable (fun w => stateAlong F (β w) (s w) v p) := by
  induction p generalizing v s with
  | nil => exact hs
  | cons j p ih =>
      have hstep : Measurable (fun w => β w v j) := by
        have hfirst := hβ 0 (by simp)
        change Measurable (fun w => β w (v ++ []) j) at hfirst
        simpa only [List.append_nil] using hfirst
      have hnext : Measurable (fun w => (β w v j).elim (s w) (F (s w))) :=
        hstep.option_elim hs
          (hF.comp ((hs.comp measurable_fst).prodMk measurable_snd))
      apply ih (fun w => (β w v j).elim (s w) (F (s w))) (v ++ [j]) hnext
      intro k hk
      have htail := hβ (k + 1) (by simpa using Nat.succ_lt_succ hk)
      change Measurable (fun w => β w (v ++ (j :: p.take k)) (p[k])) at htail
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using htail

namespace RootIndexed.BranchingWalk

/-- State evaluation is measurable on the space of branching fields and roots. -/
theorem state_measurable {Root α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (r : Root) (u : TreeNode α) :
    Measurable (fun β : RootIndexed.BranchingWalk Root α Mark State => β.state F r u) := by
  have hcoords : Measurable
      (fun β : RootIndexed.BranchingWalk Root α Mark State => (β.step, β.initial)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact stateAlong_measurable (Ω := RootIndexed.BranchingWalk Root α Mark State)
    F hF (fun β => β.step r) (fun β => β.initial r) [] u
    ((measurable_pi_apply r).comp (measurable_snd.comp hcoords))
    (fun k _ => (measurable_pi_apply (u[k])).comp
      ((measurable_pi_apply ([] ++ u.take k)).comp
        ((measurable_pi_apply r).comp (measurable_fst.comp hcoords))))

end RootIndexed.BranchingWalk

end Combinatorics.Branching
