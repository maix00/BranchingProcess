/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Lineage.Lineages
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration

/-!
# Reserve lineages in a root-indexed marked forest

The root, trial, child-slot, and mark types are independent parameters.  Each
root/trial pair carries a pre-sampled causal lineage in the common product
field.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

structure RootIndexed.ReserveLineages
    (Root Trial α X : Type*) [MeasurableSpace X] where
  path : Root → Trial → ℕ → RootIndexed.StepField Root α X → TreeNode α
  step : Root → Trial → TreeNode α × Step α X → TreeNode α
  measurable_step : ∀ r i, Measurable (step r i)
  measurable_root : ∀ r i,
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) 0] (path r i 0)
  depth : ∀ r i n ω, (path r i n ω).length = n
  recursion : ∀ r i n ω,
    path r i (n + 1) ω =
      step r i (path r i n ω, ω r (path r i n ω))

theorem RootIndexed.ReserveLineages.path_adapted_of_countable_range
    {Root Trial α X : Type*} [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (r : Root) (i : Trial)
    (hcount : ∀ n, (Set.range (lineages.path r i n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (lineages.path r i n) := by
  intro n
  induction n with
  | zero => exact lineages.measurable_root r i
  | succ n ih =>
      have hold : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (lineages.path r i n) :=
        ih.mono (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) |>.mono (Nat.le_succ n)) le_rfl
      let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
        fun ω => (r, lineages.path r i n ω)
      have hfiber : ∀ p, MeasurableSet[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          {ω | chosen ω = p} := by
        intro p
        by_cases hp : p.1 = r
        · have heq : {ω | chosen ω = p} =
              {ω | lineages.path r i n ω = p.2} := by
            ext ω
            simp [chosen, Prod.ext_iff, hp, eq_comm]
          rw [heq]
          exact hold (measurableSet_singleton p.2)
        · have heq : {ω | chosen ω = p} = ∅ := by
            ext ω
            simp [chosen, Prod.ext_iff, hp, eq_comm]
          rw [heq]
          exact (RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty
      have hmark : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω : RootIndexed.StepField Root α X =>
            ω r (lineages.path r i n ω)) := by
        exact RootIndexed.selectedStep_measurable chosen hfiber
          (fun ω => by
            change (lineages.path r i n ω).length < n + 1
            rw [lineages.depth r i n ω]
            omega)
          (by
            apply (hcount n).image (fun u => (r, u)) |>.mono
            rintro p ⟨ω, rfl⟩
            exact ⟨lineages.path r i n ω, ⟨ω, rfl⟩, rfl⟩)
      have hpair : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω : RootIndexed.StepField Root α X =>
            (lineages.path r i n ω, ω r (lineages.path r i n ω))) :=
        hold.prodMk hmark
      convert (lineages.measurable_step r i).comp hpair using 1
      funext ω
      exact lineages.recursion r i n ω

theorem RootIndexed.ReserveLineages.path_adapted
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (r : Root) (i : Trial) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (lineages.path r i n) :=
  lineages.path_adapted_of_countable_range r i
    (fun n => Set.to_countable (Set.range (lineages.path r i n)))

def RootIndexed.splitDeclaration
    {Root α X : Type*} [MeasurableSpace X]
    (r : Root) (path : ℕ → RootIndexed.StepField Root α X → TreeNode α)
    (splitMark : Set (Step α X)) : ℕ → Set (RootIndexed.StepField Root α X)
  | 0 => ∅
  | n + 1 => {ω | ω r (path n ω) ∈ splitMark}

noncomputable def RootIndexed.ReserveLineages.sigma
    {Root Trial α X : Type*} [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (r : Root) (i : Trial) :
    RootIndexed.StepField Root α X → WithTop ℕ :=
  firstDeclaredSuccess
    (RootIndexed.splitDeclaration r (lineages.path r i) splitMark)

theorem RootIndexed.ReserveLineages.sigma_isStoppingTime_of_countable_range
    {Root Trial α X : Type*} [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial)
    (hcount : ∀ n, (Set.range (lineages.path r i n)).Countable) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (lineages.sigma splitMark r i) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero => exact (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) 0).measurableSet_empty
  | succ n =>
      have hold :=
        (lineages.path_adapted_of_countable_range r i hcount n).mono
        (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) |>.mono (Nat.le_succ n)) le_rfl
      let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
        fun ω => (r, lineages.path r i n ω)
      have hfiber : ∀ p, MeasurableSet[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          {ω | chosen ω = p} := by
        intro p
        by_cases hp : p.1 = r
        · have heq : {ω | chosen ω = p} =
              {ω | lineages.path r i n ω = p.2} := by
            ext ω
            simp [chosen, Prod.ext_iff, hp, eq_comm]
          rw [heq]
          exact hold (measurableSet_singleton p.2)
        · have heq : {ω | chosen ω = p} = ∅ := by
            ext ω
            simp [chosen, Prod.ext_iff, hp, eq_comm]
          rw [heq]
          exact (RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty
      exact (RootIndexed.selectedStep_measurable chosen hfiber
        (fun ω => by
          change (lineages.path r i n ω).length < n + 1
          rw [lineages.depth r i n ω]
          omega)
        (by
          apply (hcount n).image (fun u => (r, u)) |>.mono
          rintro p ⟨ω, rfl⟩
          exact ⟨lineages.path r i n ω, ⟨ω, rfl⟩, rfl⟩)) hsplit

theorem RootIndexed.ReserveLineages.sigma_isStoppingTime
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (lineages.sigma splitMark r i) :=
  lineages.sigma_isStoppingTime_of_countable_range splitMark hsplit r i
    (fun n => Set.to_countable (Set.range (lineages.path r i n)))

end ProbabilityTheory.BranchingRandomWalk
