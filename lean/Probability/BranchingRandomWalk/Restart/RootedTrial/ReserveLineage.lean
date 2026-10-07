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

/-- The second selected child of a pre-sampled reserve lineage at a proposed
split generation.  The selector removes the first slot from the finite
offspring set and takes the least remaining slot; it is total on every sample,
including samples with fewer than two children. -/
noncomputable def RootIndexed.ReserveLineages.secondChildRootAt
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X) : Root × TreeNode α :=
  if _h : start = 0 then (r, []) else
    let parent := lineages.path r i (start - 1) ω
    (r, parent ++ [secondSelectedSlot R (ω r parent)])

theorem RootIndexed.ReserveLineages.secondChildRootAt_root
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (lineages.secondChildRootAt R r i start ω).1 = r := by
  by_cases hs : start = 0 <;>
    simp [secondChildRootAt, hs]

theorem RootIndexed.ReserveLineages.secondChildRootAt_depth
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (lineages.secondChildRootAt R r i start ω).2.length = start := by
  by_cases hs : start = 0
  · simp [secondChildRootAt, hs]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    simp [secondChildRootAt, lineages.depth]

/-- At a marked split, the totalized second-slot selector is a genuine child.
Only the event's lower bound of two selected offspring is used; additional
offspring remain allowed. -/
theorem RootIndexed.ReserveLineages.secondChildRootAt_selected
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X)
    (hstart : 0 < start)
    (hsplit : ω r (lineages.path r i (start - 1) ω) ∈ splitBy R) :
    (lineages.secondChildRootAt R r i start ω).2 =
        lineages.path r i (start - 1) ω ++
          [secondSelectedSlot R
            (ω r (lineages.path r i (start - 1) ω))] ∧
      secondSelectedSlot R (ω r (lineages.path r i (start - 1) ω)) ∈
        R (ω r (lineages.path r i (start - 1) ω)) := by
  constructor
  · simp [secondChildRootAt, Nat.ne_of_gt hstart]
  · have hcard : 2 ≤
        (R (ω r (lineages.path r i (start - 1) ω))).card := by
      simpa [splitBy] using hsplit
    exact (secondSelectedSlot_mem_of_card R
      (ω r (lineages.path r i (start - 1) ω)) hcard).1

/-- At a fixed positive generation the second-child root selector has
measurable fibres in the corresponding field filtration. -/
theorem RootIndexed.ReserveLineages.secondChildRootAt_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (i : Trial)
    (start : ℕ) (p : Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start]
      {ω | lineages.secondChildRootAt R r i start ω = p} := by
  cases start with
  | zero =>
      by_cases hp : (r, []) = p
      · rw [show {ω | lineages.secondChildRootAt R r i 0 ω = p} =
            Set.univ by ext ω; simp [secondChildRootAt, hp]]
        exact MeasurableSet.univ
      · rw [show {ω | lineages.secondChildRootAt R r i 0 ω = p} =
            ∅ by ext ω; simp [secondChildRootAt, hp]]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) 0).measurableSet_empty
  | succ n =>
      have hpath : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (lineages.path r i n) :=
        (lineages.path_adapted r i n).mono
          (RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) |>.mono (Nat.le_succ n)) le_rfl
      have hmark : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω => ω r (lineages.path r i n ω)) := by
        let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
          fun ω => (r, lineages.path r i n ω)
        have hfiber : ∀ q, MeasurableSet[RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) (n + 1)]
            {ω | chosen ω = q} := by
          intro q
          by_cases hq : q.1 = r
          · have heq : {ω | chosen ω = q} =
                {ω | lineages.path r i n ω = q.2} := by
              ext ω
              simp [chosen, Prod.ext_iff, hq, eq_comm]
            rw [heq]
            exact hpath (measurableSet_singleton q.2)
          · have heq : {ω | chosen ω = q} = ∅ := by
              ext ω
              have hqr : r ≠ q.1 := fun h => hq h.symm
              simp [chosen, Prod.ext_iff, hqr]
            rw [heq]
            exact (RootIndexed.stepFiltration
              (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty
        have hcount : (Set.range chosen).Countable := by
          have hrange : Set.range chosen =
              (fun u => (r, u)) '' Set.range (lineages.path r i n) := by
            ext q
            simp only [Set.mem_range, Set.mem_image]
            constructor
            · rintro ⟨ω, rfl⟩
              exact ⟨lineages.path r i n ω, ⟨ω, rfl⟩, rfl⟩
            · rintro ⟨u, ⟨ω, rfl⟩, hq⟩
              exact ⟨ω, by simpa [chosen] using hq⟩
          rw [hrange]
          exact (Set.to_countable (Set.range (lineages.path r i n))).image
            (fun u => (r, u))
        exact RootIndexed.selectedStep_measurable chosen hfiber
          (fun ω => by
            change (lineages.path r i n ω).length < n + 1
            rw [lineages.depth r i n ω]
            omega)
          hcount
      have hslot : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω => secondSelectedSlot R (ω r (lineages.path r i n ω))) :=
        (secondSelectedSlot_measurable R hR).comp hmark
      have hnode : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω => lineages.path r i n ω ++
            [secondSelectedSlot R (ω r (lineages.path r i n ω))]) := by
        exact (measurable_of_countable (fun q : TreeNode α × α =>
          q.1 ++ [q.2])).comp (hpath.prodMk hslot)
      by_cases hp : p.1 = r
      · have heq : {ω | lineages.secondChildRootAt R r i (n + 1) ω = p} =
            {ω | lineages.path r i n ω ++
              [secondSelectedSlot R (ω r (lineages.path r i n ω))] = p.2} := by
          ext ω
          simp [secondChildRootAt, Prod.ext_iff, hp]
        rw [heq]
        exact hnode (measurableSet_singleton p.2)
      · have heq : {ω | lineages.secondChildRootAt R r i (n + 1) ω = p} = ∅ := by
          ext ω
          have hpr : r ≠ p.1 := fun h => hp h.symm
          simp [secondChildRootAt, Prod.ext_iff, hpr]
        rw [heq]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty

/-- The second-child root selected at the observable reserve completion
`σ_i` has measurable fibres in the stopped domain filtration. The selector
uses only the pre-sampled field at that completion time. -/
theorem RootIndexed.ReserveLineages.secondChildRootAt_sigma_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (p : Root × TreeNode α) :
    MeasurableSet[(lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace]
      {ω | lineages.secondChildRootAt R r i
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
        {ω | σ ω = (n : WithTop ℕ)} := hσ.measurableSet_eq_of_countable' n
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
        · rintro ⟨⟨hEω, htimeω⟩, _⟩
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
    lineages.secondChildRootAt R r i n
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => chosenAt (WithTop.untopD 0 (σ ω)) ω
  have hzeroStopped : MeasurableSet[hσ.measurableSpace]
      {ω | chosenAt 0 ω = p} := by
    by_cases hp : (r, []) = p
    · have heq : {ω | chosenAt 0 ω = p} = Set.univ := by
        ext ω
        simp [chosenAt, RootIndexed.ReserveLineages.secondChildRootAt, hp]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {ω | chosenAt 0 ω = p} = ∅ := by
        ext ω
        simp [chosenAt, RootIndexed.ReserveLineages.secondChildRootAt, hp]
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
    | coe n => simp [chosen, chosenAt, htime]; rfl
  rw [hdecomp]
  apply htop.inter hzeroStopped |>.union
  apply MeasurableSet.iUnion
  intro n
  have hfiber : MeasurableSet[F n] {ω | chosenAt n ω = p} :=
    lineages.secondChildRootAt_fiber_measurable R hR r i n p
  simpa [Set.inter_comm] using htimeCell n _ hfiber

/-- A split-completion trial rooted at the second selected child of a
pre-sampled reserve lineage, started at its observable completion `sigma`,
has a stopping-time endpoint in the domain filtration. The selected family
may have any finite size at least two on the split event. -/
theorem RootIndexed.ReserveLineages.sigma_secondChildSubtree_splitCompletion_isStoppingTime
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
          ω ((lineages.secondChildRootAt R r i
            (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).1)
            (((lineages.secondChildRootAt R r i
              (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).2) ++ v))) := by
  let start := lineages.sigma splitMark r i
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => lineages.secondChildRootAt R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstart : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) start :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have hcount : (Set.range chosen).Countable := by
    have hnodes : (Set.range (fun ω => (chosen ω).2)).Countable := Set.to_countable _
    apply hnodes.image (fun u => (r, u)) |>.mono
    rintro p ⟨ω, rfl⟩
    have hroot : (chosen ω).1 = r := by
      exact lineages.secondChildRootAt_root R r i
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
      lineages.secondChildRootAt_sigma_fiber_measurable R hR splitMark hsplit r i p
  have hdepth : ∀ ω, (chosen ω).2.length = WithTop.untopD 0 (start ω) := by
    intro ω
    exact lineages.secondChildRootAt_depth R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstopped := RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime_withTop
    R hR start hstart chosen hcount hchosen hdepth
  simpa [start, chosen] using hstopped

end ProbabilityTheory.BranchingRandomWalk

end
