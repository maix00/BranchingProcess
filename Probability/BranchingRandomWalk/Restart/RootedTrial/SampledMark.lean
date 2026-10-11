/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.CapStopped
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.Independence.Finite

/-!
# Laws of predictably sampled reserve-spine steps

At each generation, the reserve-spine address is selected from the previously
revealed domain flow and has the current generation's depth. The step at that
address therefore has the original one-step law and is independent of the
information revealed before that generation. Iteration shows that the
totalized sequence of sampled steps is mutually independent, even though its
addresses are chosen adaptively from earlier marks.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The reserve-spine vertex at generation `n`, viewed as a one-element
family of roots for the unexplored descendant field. -/
noncomputable def selectedReserveSpineFutureRoots
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    RootIndexed.StepField Root α X → PUnit.{1} → Root × TreeNode α :=
  fun ω _ => (r, selectedReserveSpinePath R r n ω)

theorem selectedReserveSpineFutureRoots_countable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    (Set.range (selectedReserveSpineFutureRoots R r n)).Countable := by
  have hrange : (Set.range (selectedReserveSpinePath R r n)).Countable :=
    Set.to_countable _
  have hEq : Set.range (selectedReserveSpineFutureRoots R r n) =
      (fun u : TreeNode α => fun _ : PUnit.{1} => (r, u)) ''
        Set.range (selectedReserveSpinePath R r n) := by
    ext roots
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨ω, rfl⟩
      exact ⟨selectedReserveSpinePath R r n ω, ⟨ω, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨ω, rfl⟩, rfl⟩
      exact ⟨ω, rfl⟩
  rw [hEq]
  exact hrange.image _

theorem selectedReserveSpineFutureRoots_fiber_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      {ω | selectedReserveSpineFutureRoots R r n ω = roots} := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hpath : Measurable[F n] (selectedReserveSpinePath R r n) :=
    selectedReserveSpinePath_adapted R hR r n
  intro roots
  let u := roots PUnit.unit
  by_cases hr : u.1 = r
  · have hroots : roots = fun _ : PUnit.{1} => (r, u.2) := by
      funext q
      have hq : q = PUnit.unit := Subsingleton.elim _ _
      subst q
      exact Prod.ext hr rfl
    have hset : {ω | selectedReserveSpineFutureRoots R r n ω = roots} =
        {ω | selectedReserveSpinePath R r n ω = u.2} := by
      rw [hroots]
      ext ω
      change (fun _ : PUnit.{1} =>
        (r, selectedReserveSpinePath R r n ω)) =
          (fun _ : PUnit.{1} => (r, u.2)) ↔
        selectedReserveSpinePath R r n ω = u.2
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
  · have hset : {ω | selectedReserveSpineFutureRoots R r n ω = roots} =
        (∅ : Set (RootIndexed.StepField Root α X)) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      have heq' := congrArg (fun f => f PUnit.unit) heq
      exact hr (congrArg Prod.fst heq').symm
    rw [hset]
    exact F n |>.measurableSet_empty

theorem selectedReserveSpineFutureRoots_depth
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) :
    ∀ ω i, (selectedReserveSpineFutureRoots R r n ω i).2.length = n := by
  intro ω i
  change (selectedReserveSpinePath R r n ω).length = n
  exact selectedReserveSpinePath_depth R r ω n

theorem selectedReserveSpineFutureRoots_injective
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ) (ω) :
    Function.Injective (selectedReserveSpineFutureRoots R r n ω) := by
  intro i j _
  exact Subsingleton.elim _ _

/-- The step observed at the reserve-spine vertex of generation `n`. -/
noncomputable def selectedReserveSpineStep
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Step α X :=
  ω r (selectedReserveSpinePath R r n ω)

theorem selectedReserveSpineStep_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable (selectedReserveSpineStep R r n) := by
  exact (selectedReserveSpineMark_adapted R hR r n).mono
    (RootIndexed.stepFiltration.le (n + 1)) le_rfl

theorem selectedReserveSpineStep_law
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
      (selectedReserveSpineStep R r n) = μ := by
  let chosen := selectedReserveSpineFutureRoots R r n
  have hcount : (Set.range chosen).Countable :=
    selectedReserveSpineFutureRoots_countable R r n
  have hfiber := selectedReserveSpineFutureRoots_fiber_measurable R hR r n
  have hdepth := selectedReserveSpineFutureRoots_depth R r n
  have hinj : ∀ ω, Function.Injective (chosen ω) :=
    selectedReserveSpineFutureRoots_injective R r n
  let selected := RootIndexed.selectedSubtreeStepFieldVector chosen
  have hselectedMeas : Measurable selected :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable chosen hcount hfiber
  have hselectedLaw := RootIndexed.selectedSubtreeStepFieldVector_law
    μ chosen hcount hfiber hdepth hinj
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} α X => field PUnit.unit []) := by
    exact (measurable_pi_apply ([] : TreeNode α)).comp
      (measurable_pi_apply PUnit.unit)
  have hstep : selectedReserveSpineStep R r n = fun ω =>
      selected ω PUnit.unit [] := by
    funext ω
    simp [selectedReserveSpineStep, selected, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector,
      selectedReserveSpineFutureRoots]
  rw [hstep]
  change (RootIndexed.stepFieldLaw (Root := Root) μ).map
      ((fun field : RootIndexed.StepField PUnit.{1} α X =>
        field PUnit.unit []) ∘ selected) = μ
  rw [← Measure.map_map heval hselectedMeas, hselectedLaw]
  exact RootIndexed.stepFieldLaw_coordinate_marginal
    (Root := PUnit.{1}) (α := α) μ PUnit.unit []

theorem selectedReserveSpineStep_independent
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap (selectedReserveSpineStep R r n) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let chosen := selectedReserveSpineFutureRoots R r n
  have hcount : (Set.range chosen).Countable :=
    selectedReserveSpineFutureRoots_countable R r n
  have hfiber := selectedReserveSpineFutureRoots_fiber_measurable R hR r n
  have hdepth := selectedReserveSpineFutureRoots_depth R r n
  have hinj : ∀ ω, Function.Injective (chosen ω) :=
    selectedReserveSpineFutureRoots_injective R r n
  have hind := RootIndexed.selectedSubtreeStepFieldVector_independent
    μ chosen hcount hfiber hdepth hinj
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} α X => field PUnit.unit []) := by
    exact (measurable_pi_apply ([] : TreeNode α)).comp
      (measurable_pi_apply PUnit.unit)
  have hstep : selectedReserveSpineStep R r n = fun ω =>
      RootIndexed.selectedSubtreeStepFieldVector chosen ω PUnit.unit [] := by
    funext ω
    simp [selectedReserveSpineStep, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector,
      selectedReserveSpineFutureRoots]
  rw [hstep]
  apply indep_of_indep_of_le_right hind
  have hevalComap : Measurable[
      MeasurableSpace.comap
        (RootIndexed.selectedSubtreeStepFieldVector chosen) inferInstance]
      (fun ω => RootIndexed.selectedSubtreeStepFieldVector chosen ω
        PUnit.unit []) :=
    heval.comp (Measurable.of_comap_le le_rfl)
  exact hevalComap.comap_le

/-- The entire sequence of marks sampled along a pre-sampled reserve spine is
mutually independent.  At generation `n`, the spine address is measurable
from the preceding domain flow, while the step at that address is independent
of that flow.  Iterating this fact gives an iid sequence, despite the address
at generation `n` being chosen from earlier marks. -/
theorem selectedReserveSpineStep_iIndepFun
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    iIndepFun (selectedReserveSpineStep R r)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hprefix : ∀ n,
      iIndepFun (fun i : Fin n => selectedReserveSpineStep R r i.1) P := by
    intro n
    induction n with
    | zero => exact iIndepFun.of_subsingleton
    | succ n ih =>
      apply iIndepFun.finSucc
      · intro i
        exact (selectedReserveSpineStep_measurable R hR r i.1).aemeasurable
      · simpa using ih
      · let past : RootIndexed.StepField Root α X → Fin n → Step α X :=
          fun ω i => selectedReserveSpineStep R r i.1 ω
        have hpast : Measurable[F n] past := by
          apply (@measurable_pi_iff
            (RootIndexed.StepField Root α X) (Fin n) (fun _ => Step α X)
            (F n) (fun _ => inferInstance) past).2
          intro i
          have hmark := selectedReserveSpineMark_adapted R hR r i.1
          have hle : i.1 + 1 ≤ n := by omega
          change Measurable[F n]
            (fun ω => ω r (selectedReserveSpinePath R r i.1 ω))
          exact hmark.mono (F.mono hle) le_rfl
        have hind := selectedReserveSpineStep_independent μ R hR r n
        have hlast : IndepFun past (selectedReserveSpineStep R r n) P :=
          (IndepFun_iff_Indep past (selectedReserveSpineStep R r n) P).2
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
  have heq : (fun i : s => selectedReserveSpineStep R r i.1) =
      fun i => (fun j : Fin N => selectedReserveSpineStep R r j.1) (embed i) := by
    funext i
    rfl
  change iIndepFun (fun i : s => selectedReserveSpineStep R r i.1) P
  rw [heq]
  exact hind

/-- Every real-valued integrable observable of the adaptively sampled step
has exactly its original one-step expectation. -/
theorem integral_selectedReserveSpineStep_observable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) (g : Step α X → ℝ) (hg : Integrable g μ) :
    (∫ ω, g (selectedReserveSpineStep R r n ω)
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) = ∫ ξ, g ξ ∂μ := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  have hmeas := selectedReserveSpineStep_measurable R hR r n
  have hlaw := selectedReserveSpineStep_law μ R hR r n
  calc
    (∫ ω, g (selectedReserveSpineStep R r n ω) ∂P) =
        ∫ ξ, g ξ ∂P.map (selectedReserveSpineStep R r n) := by
          symm
          have hgm : AEStronglyMeasurable g
              (P.map (selectedReserveSpineStep R r n)) := by
            change AEStronglyMeasurable g
              ((RootIndexed.stepFieldLaw (Root := Root) μ).map
                (selectedReserveSpineStep R r n))
            rw [hlaw]
            exact hg.aestronglyMeasurable
          exact integral_map hmeas.aemeasurable hgm
    _ = ∫ ξ, g ξ ∂μ := by rw [hlaw]

/-- The preceding identity applies to the positive part of the potential at
the first `R`-selected slot, provided it is integrable under the one-step
law.  This names the slot selected by `R`; it does not identify it with a
distinguished offspring mark such as `Xi₁`. -/
theorem integral_selectedReserveSpineStep_firstRSelectedSlotPositivePotential
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) (φ : Potential X)
    (hg : Integrable
      (fun ξ : Step α X => max 0
        (ξ.potentialValue' φ (firstSelectedSlot R ξ))) μ) :
    (∫ ω, max 0 ((selectedReserveSpineStep R r n ω).potentialValue' φ
        (firstSelectedSlot R (selectedReserveSpineStep R r n ω)))
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
    ∫ ξ, max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ)) ∂μ := by
  exact integral_selectedReserveSpineStep_observable μ R hR r n
    (fun ξ => max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ))) hg

end ProbabilityTheory.BranchingRandomWalk
