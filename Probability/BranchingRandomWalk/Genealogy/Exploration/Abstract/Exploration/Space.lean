/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.AddressFiltration

/-!
# Independence of inspected coordinates

## Public declarations

`stepsOnSpace s = ⨆ u ∈ s, stepCoordinateSpace u` is defined with the
abstract branching-step coordinate spaces. This file proves its order and
independence properties.

With `\mathscr F(S)` denoting `stepsOnSpace S` and `\nu_\mu` the product law
of the pre-sampled steps, the structural and independence statements are

\[\begin{aligned}
S\subseteq T&\Longrightarrow\mathscr F(S)\le\mathscr F(T),\\
S\cap T=\varnothing&\Longrightarrow
\operatorname{Indep}(\mathscr F(S),\mathscr F(T),\nu_\mu).
\end{aligned}\]

- `stepsOnSpace_mono` states `s ⊆ t → stepsOnSpace s ≤ stepsOnSpace t`, and
  `stepsOnSpace_le` bounds every such space by the ambient product
  measurable space.
- `stepsOnSpace_independent` states that `Disjoint s t` implies
  `Indep (stepsOnSpace s) (stepsOnSpace t) (offspringFieldLaw μ)`.
  `stepsOnSpace_descendant_independent` applies this when the inspected
  addresses are disjoint from every descendant of a fixed root.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem stepsOnSpace_mono
    {α X : Type*} [MeasurableSpace X] {s t : Set (TreeNode α)} (hst : s ⊆ t) :
    stepsOnSpace (X := X) s ≤ stepsOnSpace t := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem stepsOnSpace_le
    {α X : Type*} [MeasurableSpace X] (s : Set (TreeNode α)) :
    stepsOnSpace (X := X) s ≤
      (inferInstance : MeasurableSpace (TreeNode α → Step α X)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  exact (measurable_pi_apply u).comap_le

theorem stepsOnSpace_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (s t : Set (TreeNode α)) (hdisj : Disjoint s t) :
    Indep (stepsOnSpace s) (stepsOnSpace t)
      (offspringFieldLaw μ) := by
  have hle : ∀ u : TreeNode α, stepCoordinateSpace (X := X) u ≤
      (inferInstance : MeasurableSpace (TreeNode α → Step α X)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle
    (step_coordinate_independent μ) hdisj

theorem stepsOnSpace_descendant_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (explored : Set (TreeNode α)) (root : TreeNode α)
    (hfresh : Disjoint explored (branchingDescendantAddresses root)) :
    Indep (stepsOnSpace explored)
      (stepDescendantSpace root) (offspringFieldLaw μ) := by
  rw [stepDescendantSpace_eq_iSup]
  exact stepsOnSpace_independent μ explored
    (branchingDescendantAddresses root) hfresh

end ProbabilityTheory.BranchingRandomWalk

end
