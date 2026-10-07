/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.SelectedRoot

/-!
# A reserve trial rooted at its observable split time

The pre-sampled lineage is selected at its `sigma` completion generation.
The selector is measurable in the stopped sigma-algebra, including the
infinite-time fiber, so the selected subtree's later split completion is a
stopping time in the original generation filtration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

/-- The first selected child root, chosen from a pre-sampled reserve lineage
at its observable `sigma` completion, is measurable in the stopped
sigma-algebra. The infinite-time fiber is included explicitly; the
generation-zero value is the totalized root address. -/
theorem RootIndexed.ReserveLineages.firstChildRootAt_sigma_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (p : Root × TreeNode α) :
    MeasurableSet[(lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace]
      {ω | lineages.firstChildRootAt R r i
        (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω = p} := by
  classical
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let σ := lineages.sigma splitMark r i
  have hσ : IsStoppingTime F σ :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have htimeCell (n : ℕ) (E : Set (RootIndexed.StepField Root α X))
      (hE : MeasurableSet[F n] E) :
      MeasurableSet[hσ.measurableSpace] (E ∩ {ω | σ ω = (n : WithTop ℕ)}) := by
    have htimeStop : MeasurableSet[hσ.measurableSpace]
        {ω | σ ω = (n : WithTop ℕ)} :=
      hσ.measurableSet_eq_of_countable' n
    have htime : MeasurableSet[F n] {ω | σ ω = (n : WithTop ℕ)} := by
      simpa using (hσ.measurableSet_inter_eq_iff
        {ω | σ ω = (n : WithTop ℕ)} n).1 (htimeStop.inter htimeStop)
    have hcell : MeasurableSet[F n]
        (E ∩ {ω | σ ω = (n : WithTop ℕ)}) := hE.inter htime
    have hleF : F n ≤ ⨆ k, F k := le_iSup (fun k => F k) n
    refine ⟨hleF _ hcell, fun k => ?_⟩
    have hcut :
        (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} =
          if n ≤ k then E ∩ {ω | σ ω = (n : WithTop ℕ)} else ∅ := by
      ext ω
      by_cases hnk : n ≤ k
      · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ite_eq_left hnk]
        constructor
        · rintro ⟨⟨hEω, htimeω⟩, hleω⟩
          exact ⟨hEω, htimeω⟩
        · rintro ⟨hEω, htimeω⟩
          exact ⟨⟨hEω, htimeω⟩, by rw [htimeω]; exact WithTop.coe_le_coe.mpr hnk⟩
      · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ite_eq_right hnk,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htimeω⟩, hleω⟩
        apply hnk
        rw [htimeω] at hleω
        exact WithTop.coe_le_coe.mp hleω
    by_cases hnk : n ≤ k
    · have heq :
          (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} =
            E ∩ {ω | σ ω = (n : WithTop ℕ)} := by
        simpa [hnk] using hcut
      exact heq.symm ▸ (F.mono hnk) _ hcell
    · have heq :
          (E ∩ {ω | σ ω = (n : WithTop ℕ)}) ∩ {ω | σ ω ≤ k} = ∅ := by
        simpa [hnk] using hcut
      exact heq.symm ▸ (F k).measurableSet_empty
  have htop : MeasurableSet[hσ.measurableSpace] {ω | σ ω = ⊤} := by
    have hfinite : MeasurableSet[hσ.measurableSpace]
        (⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)}) :=
      MeasurableSet.iUnion fun n : ℕ => hσ.measurableSet_eq_of_countable' n
    have heq : {ω | σ ω = ⊤} =
        (⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)})ᶜ := by
      ext ω
      cases htime : σ ω with
      | top => simp [htime]
      | coe n => simp [htime]
    rw [heq]
    exact hfinite.compl
  let chosenAt (n : ℕ) : RootIndexed.StepField Root α X → Root × TreeNode α :=
    lineages.firstChildRootAt R r i n
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => chosenAt (WithTop.untopD 0 (σ ω)) ω
  have hzero : MeasurableSet[F 0] {ω | chosenAt 0 ω = p} :=
    lineages.firstChildRootAt_fiber_measurable R hR r i 0 p
  have hzeroStopped : MeasurableSet[hσ.measurableSpace]
      {ω | chosenAt 0 ω = p} := by
    by_cases hp : (r, []) = p
    · have heq : {ω | chosenAt 0 ω = p} = Set.univ := by
        ext ω
        simp [chosenAt, RootIndexed.ReserveLineages.firstChildRootAt, hp]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {ω | chosenAt 0 ω = p} = ∅ := by
        ext ω
        simp [chosenAt, RootIndexed.ReserveLineages.firstChildRootAt, hp]
      rw [heq]
      exact hσ.measurableSpace.measurableSet_empty
  have hdecomp : {ω | chosen ω = p} =
      ({ω | σ ω = ⊤} ∩ {ω | chosenAt 0 ω = p}) ∪
        ⋃ n : ℕ, {ω | σ ω = (n : WithTop ℕ)} ∩
          {ω | chosenAt n ω = p} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion,
      Set.mem_inter_iff]
    cases htime : σ ω with
    | top => simp [chosen, htime, chosenAt, WithTop.untopD_top]
    | coe n =>
        simp [chosen, chosenAt, htime]
        rfl
  rw [hdecomp]
  apply htop.inter hzeroStopped |>.union
  apply MeasurableSet.iUnion
  intro n
  have hfiber : MeasurableSet[F n] {ω | chosenAt n ω = p} :=
    lineages.firstChildRootAt_fiber_measurable R hR r i n p
  simpa [Set.inter_comm] using htimeCell n _ hfiber

/-- A split-completion trial rooted at the first selected child of a
pre-sampled reserve lineage, started at its observable completion `sigma`,
has a stopping-time endpoint in the domain filtration. This is the concrete
stopped-root application; it does not assert independence from the explored
domain or freshness after earlier failed candidates. -/
theorem RootIndexed.ReserveLineages.sigma_firstChildSubtree_splitCompletion_isStoppingTime
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => lineages.sigma splitMark r i ω +
        selectedPopulationSplitCompletion R (fun v =>
          ω ((lineages.firstChildRootAt R r i
            (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).1)
            (((lineages.firstChildRootAt R r i
              (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).2) ++ v))) := by
  let start := lineages.sigma splitMark r i
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => lineages.firstChildRootAt R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstart : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) start :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have hcount : (Set.range chosen).Countable := by
    have hnodes : (Set.range (fun ω => (chosen ω).2)).Countable := Set.to_countable _
    apply hnodes.image (fun u => (r, u)) |>.mono
    rintro p ⟨ω, rfl⟩
    have hroot : (chosen ω).1 = r := by
      exact lineages.firstChildRootAt_root R r i
        (WithTop.untopD 0 (start ω)) ω
    have hpair : (r, (chosen ω).2) = chosen ω := by
      apply Prod.ext
      · exact hroot.symm
      · rfl
    exact ⟨(chosen ω).2, ⟨ω, rfl⟩, hpair⟩
  have hchosen : ∀ p, MeasurableSet[hstart.measurableSpace]
      {ω | chosen ω = p} := by
    intro p
    simpa [chosen, start] using
      lineages.firstChildRootAt_sigma_fiber_measurable R hR splitMark hsplit r i p
  have hdepth : ∀ ω, (chosen ω).2.length = WithTop.untopD 0 (start ω) := by
    intro ω
    exact lineages.firstChildRootAt_depth R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstopped := RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime_withTop
    R hR start hstart chosen hcount hchosen hdepth
  simpa [start, chosen] using hstopped

end ProbabilityTheory.BranchingRandomWalk

end
