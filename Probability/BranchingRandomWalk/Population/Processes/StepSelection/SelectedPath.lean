/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic

/-!
# Paths retained by a finite step selection

## Public declarations

- `selectedAlong R ω v p` means that each successive child slot of the finite
  path `p`, starting at the prefix `v`, is selected by `R` at the mark of its
  parent.
- `selectedAlong_append_singleton` states that a path followed by one final
  slot is selected precisely when its prefix is selected and the final slot
  is retained at the prefix endpoint.
- `mem_population_iff_length_selectedAlong` characterizes generation
  membership: `u ∈ population R n ω` if and only if `u.length = n` and every
  child slot along `u` is selected.

Let `P_n=population(R,n,\omega)`. The path predicate checks each child slot
at its parent, and generation membership is exactly the address length
together with selection along the whole address:

\[\begin{aligned}
\operatorname{selectedAlong}(v,[])&=\mathrm{True},\\
\operatorname{selectedAlong}(v,i::p)
&\Longleftrightarrow
  i\in R(\omega(v))\ \wedge\ 
  \operatorname{selectedAlong}(v\mathbin{+\!\!+}[i],p),\\
u\in P_n&\Longleftrightarrow
  |u|=n\ \wedge\ \operatorname{selectedAlong}([],u).
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory
open Combinatorics.Branching Combinatorics.UlamHarris

namespace ProbabilityTheory.BranchingRandomWalk.StepSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite address is selected along a marked branching walk when every
child slot on the address is retained by the selector at its parent. -/
def selectedAlong {α X : Type*}
    (R : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => i ∈ R (ω v) ∧ selectedAlong R ω (v ++ [i]) p

theorem selectedAlong_append_singleton
    {α X : Type*} (R : Step.FiniteSelection α X)
    (ω : Mark α (Step α X)) :
    ∀ (v p : TreeNode α) (i : α),
      selectedAlong R ω v (p ++ [i]) ↔
        selectedAlong R ω v p ∧ i ∈ R (ω (v ++ p)) := by
  intro v p
  induction p generalizing v with
  | nil => intro i; simp [selectedAlong]
  | cons j p ih =>
      intro i
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, selectedAlong]
      rw [ih]
      simp only [hpath, and_assoc]

/-- Membership in generation `n` is equivalent to having length `n` and
being selected at every step along the address. -/
theorem mem_population_iff_length_selectedAlong
    {α X : Type*} (R : Step.FiniteSelection α X)
    (ω : Mark α (Step α X)) :
    ∀ n u, u ∈ population R n ω ↔
      u.length = n ∧ selectedAlong R ω [] u := by
  intro n
  induction n with
  | zero =>
      intro u
      rw [population_zero]
      simp only [Finset.mem_singleton]
      constructor
      · intro hu
        subst u
        simp [selectedAlong]
      · rintro ⟨hu, _⟩
        exact List.length_eq_zero_iff.mp hu
  | succ n ih =>
      intro q
      rw [population_succ, mem_grow_iff]
      constructor
      · rintro ⟨u, hu, i, hi, rfl⟩
        have hu' := (ih u).mp hu
        have hfrontier : frontierMarks n ω u = ω u := by
          simp [frontierMarks, hu'.1]
        refine ⟨by simp [hu'.1], ?_⟩
        rw [selectedAlong_append_singleton]
        exact ⟨hu'.2, hfrontier ▸ hi⟩
      · rintro ⟨hqLength, hqSelected⟩
        have hqne : q ≠ [] := by
          intro h
          simp [h] at hqLength
        let i := q.getLast hqne
        have hsplit : q.dropLast ++ [i] = q := by
          simpa [i] using List.dropLast_append_getLast hqne
        have hselected : selectedAlong R ω [] (q.dropLast ++ [i]) := by
          simpa [hsplit] using hqSelected
        have hparts := (selectedAlong_append_singleton R ω [] q.dropLast i).mp
          hselected
        have hparentLength : q.dropLast.length = n := by
          rw [List.length_dropLast]
          omega
        have hparent : q.dropLast ∈ population R n ω :=
          (ih q.dropLast).mpr ⟨hparentLength, hparts.1⟩
        have hfrontier :
            frontierMarks n ω q.dropLast = ω q.dropLast := by
          simp [frontierMarks, hparentLength]
        exact ⟨q.dropLast, hparent, i, hfrontier ▸ hparts.2, hsplit.symm⟩

end ProbabilityTheory.BranchingRandomWalk.StepSelection
