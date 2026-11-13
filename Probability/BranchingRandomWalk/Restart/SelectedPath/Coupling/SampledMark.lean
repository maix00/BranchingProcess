/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.SelectedPath.Path
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.Independence.FiniteFamily
import Combinatorics.BranchingWalk.Step.Selection.Potential

/-!
# Laws of predictably sampled selected-path steps

At each generation, the selected-path address is selected from the previously
revealed domain flow and has the current generation's depth. The step at that
address therefore has the original one-step law and is independent of the
information revealed before that generation. Iteration shows that the
totalized sequence of sampled steps is mutually independent, even though its
addresses are chosen adaptively from earlier marks.

## Public declarations

Let \(X_n\) be the step sampled at the selected-path address of depth \(n\).
Predictable sampling preserves the one-step law and independence:

\[\operatorname{Law}(X_n)=\mu,\qquad
  (X_n)_{n\ge0}\text{ is an independent family}.\]

- `Restart.SelectedPath.Coupling.futureRoots`,
  `Restart.SelectedPath.Coupling.futureRoots_countable`,
  `Restart.SelectedPath.Coupling.futureRoots_fiber_measurable`,
  `Restart.SelectedPath.Coupling.futureRoots_depth`, and
  `Restart.SelectedPath.Coupling.futureRoots_injective`: the selected path address
  defines a measurable, countable future-root family at the correct depth.
- `Restart.SelectedPath.Coupling.step`, `Restart.SelectedPath.Coupling.step_measurable`,
  `Restart.SelectedPath.Coupling.step_law`, `Restart.SelectedPath.Coupling.step_independent`,
  `Restart.SelectedPath.Coupling.step_iIndepFun`,
  `Restart.SelectedPath.Coupling.integral_step_observable`, and
  `Restart.SelectedPath.Coupling.integral_step_firstSelectedSlotPositivePotential`:
  predictably sampled marks have the original one-step law and are mutually
  independent, with the corresponding observable expectation identities.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The selected-path vertex at generation `n`, viewed as a one-element
family of roots for the unexplored descendant field. -/
noncomputable def futureRoots
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    RootIndexed.StepField Root α X → PUnit.{1} → Root × TreeNode α :=
  fun ω _ => (r, Restart.selectedPath R r n ω)

theorem futureRoots_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    (Set.range (Restart.SelectedPath.Coupling.futureRoots R r n)).Countable := by
  have hrange : (Set.range (Restart.selectedPath R r n)).Countable :=
    Set.to_countable _
  have hEq : Set.range (Restart.SelectedPath.Coupling.futureRoots R r n) =
      (fun u : TreeNode α => fun _ : PUnit.{1} => (r, u)) ''
        Set.range (Restart.selectedPath R r n) := by
    ext roots
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨ω, rfl⟩
      exact ⟨Restart.selectedPath R r n ω, ⟨ω, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨ω, rfl⟩, rfl⟩
      exact ⟨ω, rfl⟩
  rw [hEq]
  exact hrange.image _

theorem futureRoots_fiber_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      {ω | Restart.SelectedPath.Coupling.futureRoots R r n ω = roots} := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hpath : Measurable[F n] (Restart.selectedPath R r n) :=
    Restart.SelectedPath.adapted R hR r n
  intro roots
  let u := roots PUnit.unit
  by_cases hr : u.1 = r
  · have hroots : roots = fun _ : PUnit.{1} => (r, u.2) := by
      funext q
      have hq : q = PUnit.unit := Subsingleton.elim _ _
      subst q
      exact Prod.ext hr rfl
    have hset : {ω | Restart.SelectedPath.Coupling.futureRoots R r n ω = roots} =
        {ω | Restart.selectedPath R r n ω = u.2} := by
      rw [hroots]
      ext ω
      change (fun _ : PUnit.{1} =>
        (r, Restart.selectedPath R r n ω)) =
          (fun _ : PUnit.{1} => (r, u.2)) ↔
        Restart.selectedPath R r n ω = u.2
      constructor
      · intro h
        have h' := congrFun h PUnit.unit
        exact congrArg Prod.snd h'
      · intro h
        funext q
        have hq : q = PUnit.unit := Subsingleton.elim _ _
        subst q
        exact Prod.ext rfl h
    rw [hset]
    exact hpath (measurableSet_singleton u.2)
  · have hset : {ω | Restart.SelectedPath.Coupling.futureRoots R r n ω = roots} =
        (∅ : Set (RootIndexed.StepField Root α X)) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      have heq' := congrArg (fun f => f PUnit.unit) heq
      exact hr (congrArg Prod.fst heq').symm
    rw [hset]
    exact F n |>.measurableSet_empty

theorem futureRoots_depth
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    ∀ ω i, (Restart.SelectedPath.Coupling.futureRoots R r n ω i).2.length = n := by
  intro ω i
  change (Restart.selectedPath R r n ω).length = n
  exact Restart.SelectedPath.depth R r ω n

theorem futureRoots_injective
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) (ω) :
    Function.Injective (Restart.SelectedPath.Coupling.futureRoots R r n ω) := by
  intro i j _
  exact Subsingleton.elim _ _

/-- The step observed at the selected-path vertex of generation `n`. -/
noncomputable def step
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Step α X :=
  ω r (Restart.selectedPath R r n ω)

theorem step_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable (Restart.SelectedPath.Coupling.step R r n) := by
  exact (Restart.SelectedPath.mark_adapted R hR r n).mono
    (RootIndexed.stepFiltration.le (n + 1)) le_rfl

theorem step_law
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
      (Restart.SelectedPath.Coupling.step R r n) = μ := by
  let chosen := Restart.SelectedPath.Coupling.futureRoots R r n
  have hcount : (Set.range chosen).Countable :=
    Restart.SelectedPath.Coupling.futureRoots_countable R r n
  have hfiber := Restart.SelectedPath.Coupling.futureRoots_fiber_measurable R hR r n
  have hdepth := Restart.SelectedPath.Coupling.futureRoots_depth R r n
  have hinj : ∀ ω, Function.Injective (chosen ω) :=
    Restart.SelectedPath.Coupling.futureRoots_injective R r n
  let selected := RootIndexed.selectedSubtreeStepFieldVector chosen
  have hselectedMeas : Measurable selected :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable chosen hcount hfiber
  have hselectedLaw := RootIndexed.selectedSubtreeStepFieldVector_law
    μ chosen hcount hfiber hdepth hinj
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} α X => field PUnit.unit []) := by
    exact (measurable_pi_apply ([] : TreeNode α)).comp
      (measurable_pi_apply PUnit.unit)
  have hstep : Restart.SelectedPath.Coupling.step R r n = fun ω =>
      selected ω PUnit.unit [] := by
    funext ω
    simp [Restart.SelectedPath.Coupling.step, selected, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector,
      Restart.SelectedPath.Coupling.futureRoots]
  rw [hstep]
  change (RootIndexed.stepFieldLaw (Root := Root) μ).map
      ((fun field : RootIndexed.StepField PUnit.{1} α X =>
        field PUnit.unit []) ∘ selected) = μ
  rw [← Measure.map_map heval hselectedMeas, hselectedLaw]
  exact RootIndexed.stepFieldLaw_coordinate_marginal
    (Root := PUnit.{1}) (α := α) μ PUnit.unit []

theorem step_independent
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap (Restart.SelectedPath.Coupling.step R r n) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let chosen := Restart.SelectedPath.Coupling.futureRoots R r n
  have hcount : (Set.range chosen).Countable :=
    Restart.SelectedPath.Coupling.futureRoots_countable R r n
  have hfiber := Restart.SelectedPath.Coupling.futureRoots_fiber_measurable R hR r n
  have hdepth := Restart.SelectedPath.Coupling.futureRoots_depth R r n
  have hinj : ∀ ω, Function.Injective (chosen ω) :=
    Restart.SelectedPath.Coupling.futureRoots_injective R r n
  have hind := RootIndexed.selectedSubtreeStepFieldVector_independent
    μ chosen hcount hfiber hdepth hinj
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} α X => field PUnit.unit []) := by
    exact (measurable_pi_apply ([] : TreeNode α)).comp
      (measurable_pi_apply PUnit.unit)
  have hstep : Restart.SelectedPath.Coupling.step R r n = fun ω =>
      RootIndexed.selectedSubtreeStepFieldVector chosen ω PUnit.unit [] := by
    funext ω
    simp [Restart.SelectedPath.Coupling.step, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector,
      Restart.SelectedPath.Coupling.futureRoots]
  rw [hstep]
  apply indep_of_indep_of_le_right hind
  have hevalComap : Measurable[
      MeasurableSpace.comap
        (RootIndexed.selectedSubtreeStepFieldVector chosen) inferInstance]
      (fun ω => RootIndexed.selectedSubtreeStepFieldVector chosen ω
        PUnit.unit []) :=
    heval.comp (Measurable.of_comap_le le_rfl)
  exact hevalComap.comap_le

/-- The entire sequence of marks sampled along a pre-sampled selected path is
mutually independent.  At generation `n`, the selected path address is measurable
from the preceding domain flow, while the step at that address is independent
of that flow.  Iterating this fact gives an iid sequence, despite the address
at generation `n` being chosen from earlier marks. -/
theorem step_iIndepFun
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    iIndepFun (Restart.SelectedPath.Coupling.step R r)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hprefix : ∀ n,
      iIndepFun (fun i : Fin n => Restart.SelectedPath.Coupling.step R r i.1) P := by
    intro n
    induction n with
    | zero => exact iIndepFun.of_subsingleton
    | succ n ih =>
      apply iIndepFun.finSucc
      · intro i
        exact (Restart.SelectedPath.Coupling.step_measurable R hR r i.1).aemeasurable
      · simpa using ih
      · let past : RootIndexed.StepField Root α X → Fin n → Step α X :=
          fun ω i => Restart.SelectedPath.Coupling.step R r i.1 ω
        have hpast : Measurable[F n] past := by
          apply (@measurable_pi_iff
            (RootIndexed.StepField Root α X) (Fin n) (fun _ => Step α X)
            (F n) (fun _ => inferInstance) past).2
          intro i
          have hmark := Restart.SelectedPath.mark_adapted R hR r i.1
          have hle : i.1 + 1 ≤ n := by omega
          change Measurable[F n]
            (fun ω => ω r (Restart.selectedPath R r i.1 ω))
          exact hmark.mono (F.mono hle) le_rfl
        have hind := Restart.SelectedPath.Coupling.step_independent μ R hR r n
        have hlast : IndepFun past (Restart.SelectedPath.Coupling.step R r n) P :=
          (IndepFun_iff_Indep past (Restart.SelectedPath.Coupling.step R r n) P).2
            (indep_of_indep_of_le_left hind hpast.comap_le)
        simpa [past] using hlast
  rw [iIndepFun_iff_finset]
  intro s
  let N := s.sup id + 1
  have hbound : ∀ i : s, i.1 < N := by
    intro i
    dsimp [N]
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun x : ℕ => x) i.2)
  let embed : s → Fin N := fun i => ⟨i.1, hbound i⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hind := (hprefix N).precomp hembed
  have heq : (fun i : s => Restart.SelectedPath.Coupling.step R r i.1) =
      fun i => (fun j : Fin N => Restart.SelectedPath.Coupling.step R r j.1) (embed i) := by
    funext i
    rfl
  change iIndepFun (fun i : s => Restart.SelectedPath.Coupling.step R r i.1) P
  rw [heq]
  exact hind

/-- Every real-valued integrable observable of the adaptively sampled step
has exactly its original one-step expectation. -/
theorem integral_step_observable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) (g : Step α X → ℝ) (hg : Integrable g μ) :
    (∫ ω, g (Restart.SelectedPath.Coupling.step R r n ω)
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) = ∫ ξ, g ξ ∂μ := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  have hmeas := Restart.SelectedPath.Coupling.step_measurable R hR r n
  have hlaw := Restart.SelectedPath.Coupling.step_law μ R hR r n
  calc
    (∫ ω, g (Restart.SelectedPath.Coupling.step R r n ω) ∂P) =
        ∫ ξ, g ξ ∂P.map (Restart.SelectedPath.Coupling.step R r n) := by
          symm
          have hgm : AEStronglyMeasurable g
              (P.map (Restart.SelectedPath.Coupling.step R r n)) := by
            change AEStronglyMeasurable g
              ((RootIndexed.stepFieldLaw (Root := Root) μ).map
                (Restart.SelectedPath.Coupling.step R r n))
            rw [hlaw]
            exact hg.aestronglyMeasurable
          exact integral_map hmeas.aemeasurable hgm
    _ = ∫ ξ, g ξ ∂μ := by rw [hlaw]

/-- The preceding identity applies to the positive part of the potential at
the first `R`-selected slot, provided it is integrable under the one-step
law.  This names the slot selected by `R`; it does not identify it with a
distinguished offspring mark such as `Xi₁`. -/
theorem integral_step_firstSelectedSlotPositivePotential
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) (φ : Potential X)
    (hg : Integrable (firstSelectedSlotPositivePotential R φ) μ) :
    (∫ ω, firstSelectedSlotPositivePotential R φ
        (Restart.SelectedPath.Coupling.step R r n ω)
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
    ∫ ξ, firstSelectedSlotPositivePotential R φ ξ ∂μ := by
  exact Restart.SelectedPath.Coupling.integral_step_observable μ R hR r n
    (firstSelectedSlotPositivePotential R φ) hg

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Coupling
