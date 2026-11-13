/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.SelectedPath.Roots
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Growth-trial and continuation roots at a split

The pre-sampled lineage is selected at its `sigma` completion generation.
The selector is measurable in the stopped sigma-algebra, including the
infinite-time fiber, so the selected subtree's later split completion is a
stopping time in the original generation filtration.

## Public declarations

At the observable split completion \(s\), the first two selected sibling
roots are distinct and both have address depth \(s\); each sibling's next
split completion is a stopping time in the original generation domain:

\[|\rho_1|=|\rho_2|=s,\qquad \rho_1\ne\rho_2,\qquad
  \sigma_{\rho_1}^{\mathrm{split}},\ \sigma_{\rho_2}^{\mathrm{split}}
  \text{ are stopping times}.\]

- `Restart.SelectedPath.GrowthTrial.growthTrialRootAt_sigma_fiber_measurable` and
  `Restart.SelectedPath.GrowthTrial.sigma_growthTrialSubtree_splitCompletion_isStoppingTime`:
  the first sibling root selected at a sigma completion is measurable in the
  stopped domain, and its subsequent split completion is a stopping time.
- `Restart.SelectedPath.GrowthTrial.continuationChildAt`,
  `continuationChildAt_root`, `continuationChildAt_depth`,
  `continuationChildAt_selected`, `continuationChildAt_sigma_selected`,
  `continuationChildAt_ne_growthTrialRootAt`,
  `continuationChildAt_sigma_ne_growthTrialRootAt`,
  `continuationChildAt_fiber_measurable`, and
  `continuationChildAt_sigma_fiber_measurable`: define the second sibling root
  and establish its root, depth, selection, distinctness, and stopped-domain
  measurability properties.
- `Restart.SelectedPath.GrowthTrial.sigma_continuationChildSubtree_splitCompletion_isStoppingTime`,
  `Restart.SelectedPath.GrowthTrial.sigmaGrowthTrialAndContinuationRoots`, and
  `Restart.SelectedPath.GrowthTrial.siblingField_factorization_on_finite`:
  the second subtree split completion is a stopping time and the sibling
  subtree vector has product law on finite completion.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

/-- The first selected child root, chosen from a pre-sampled lineage
at its observable `sigma` completion, is measurable in the stopped
sigma-algebra. The infinite-time fiber is included explicitly; the
generation-zero value is the totalized root address. -/
theorem growthTrialRootAt_sigma_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (p : Root × TreeNode α) :
    MeasurableSet[(lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace]
      {ω | Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
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
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i n
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => chosenAt (WithTop.untopD 0 (σ ω)) ω
  have hzero : MeasurableSet[F 0] {ω | chosenAt 0 ω = p} :=
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt_fiber_measurable lineages R hR r i 0 p
  have hzeroStopped : MeasurableSet[hσ.measurableSpace]
      {ω | chosenAt 0 ω = p} := by
    by_cases hp : (r, []) = p
    · have heq : {ω | chosenAt 0 ω = p} = Set.univ := by
        ext ω
        simp [chosenAt, Restart.SelectedPath.GrowthTrial.growthTrialRootAt, hp]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {ω | chosenAt 0 ω = p} = ∅ := by
        ext ω
        simp [chosenAt, Restart.SelectedPath.GrowthTrial.growthTrialRootAt, hp]
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
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt_fiber_measurable lineages R hR r i n p
  simpa [Set.inter_comm] using htimeCell n _ hfiber

/-- A split-completion trial rooted at the first selected child of a
pre-sampled lineage, started at its observable completion `sigma`,
has a stopping-time endpoint in the domain filtration. This is the concrete
stopped-root application; it does not assert independence from the explored
domain or freshness after earlier failed candidates. -/
theorem sigma_growthTrialSubtree_splitCompletion_isStoppingTime
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => lineages.sigma splitMark r i ω +
        selectedPopulationSplitCompletion R (fun v =>
          ω ((Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
            (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).1)
            (((Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
              (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).2) ++ v))) := by
  let start := lineages.sigma splitMark r i
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstart : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) start :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have hcount : (Set.range chosen).Countable := by
    have hnodes : (Set.range (fun ω => (chosen ω).2)).Countable := Set.to_countable _
    apply hnodes.image (fun u => (r, u)) |>.mono
    rintro p ⟨ω, rfl⟩
    have hroot : (chosen ω).1 = r := by
      exact Restart.SelectedPath.GrowthTrial.growthTrialRootAt_root lineages R r i
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
      Restart.SelectedPath.GrowthTrial.growthTrialRootAt_sigma_fiber_measurable lineages R hR splitMark hsplit r i p
  have hdepth : ∀ ω, (chosen ω).2.length = WithTop.untopD 0 (start ω) := by
    intro ω
    exact Restart.SelectedPath.GrowthTrial.growthTrialRootAt_depth lineages R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstopped := RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime_withTop
    R hR start hstart chosen hcount hchosen hdepth
  simpa [start, chosen] using hstopped

/-- The second selected child of a pre-sampled lineage at a proposed
split generation.  The selector removes the first slot from the finite
offspring set and takes the least remaining slot; it is total on every sample,
including samples with fewer than two children. -/
noncomputable def continuationChildAt
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X) : Root × TreeNode α :=
  if _h : start = 0 then (r, []) else
    let parent := lineages.path r i (start - 1) ω
    (r, parent ++ [secondSelectedSlot R (ω r parent)])

theorem continuationChildAt_root
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i start ω).1 = r := by
  by_cases hs : start = 0 <;>
    simp [continuationChildAt, hs]

theorem continuationChildAt_depth
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i start ω).2.length = start := by
  by_cases hs : start = 0
  · simp [continuationChildAt, hs]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    simp [continuationChildAt, lineages.depth]

/-- At a marked split, the totalized second-slot selector is a genuine child.
Only the event's lower bound of two selected offspring is used; additional
offspring remain allowed. -/
theorem continuationChildAt_selected
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X)
    (hstart : 0 < start)
    (hsplit : ω r (lineages.path r i (start - 1) ω) ∈ splitBy R) :
    (Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i start ω).2 =
        lineages.path r i (start - 1) ω ++
          [secondSelectedSlot R
            (ω r (lineages.path r i (start - 1) ω))] ∧
      secondSelectedSlot R (ω r (lineages.path r i (start - 1) ω)) ∈
        R (ω r (lineages.path r i (start - 1) ω)) := by
  constructor
  · simp [continuationChildAt, Nat.ne_of_gt hstart]
  · have hcard : 2 ≤
        (R (ω r (lineages.path r i (start - 1) ω))).card := by
      simpa [splitBy] using hsplit
    exact (secondSelectedSlot_mem_of_card R
      (ω r (lineages.path r i (start - 1) ω)) hcard).1

/-- A finite observable selected-path split completion is declared by a split at the
preceding lineage node, so the second-child selector at `σᵢ` is a genuine
selected sibling. The offspring family may have any finite size at least two. -/
theorem continuationChildAt_sigma_selected
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (splitMark : Set (Step α X))
    (hsplitMark : splitMark ⊆ splitBy R)
    (r : Root) (i : Trial) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsigma : lineages.sigma splitMark r i ω = (n + 1 : WithTop ℕ)) :
    (Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i (n + 1) ω).2 =
        lineages.path r i n ω ++
          [secondSelectedSlot R (ω r (lineages.path r i n ω))] ∧
      secondSelectedSlot R (ω r (lineages.path r i n ω)) ∈
        R (ω r (lineages.path r i n ω)) := by
  have hsplitMark' : ω r (lineages.path r i n ω) ∈ splitMark := by
    have hdecl := (firstDeclaredSuccess_eq_iff
      (RootIndexed.splitDeclaration r (lineages.path r i) splitMark)
      ω (n + 1)).mp hsigma
    simpa [RootIndexed.splitDeclaration] using hdecl.1
  have hsplit : ω r (lineages.path r i n ω) ∈ splitBy R :=
    hsplitMark hsplitMark'
  simpa using Restart.SelectedPath.GrowthTrial.continuationChildAt_selected lineages R r i (n + 1) ω
    (by omega) hsplit

/-- At a genuine split, the second selected child root is distinct from the
first. The only cardinality assumption is that the selected family has at
least two members. -/
theorem continuationChildAt_ne_growthTrialRootAt
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X)
    (hstart : 0 < start)
    (hsplit : ω r (lineages.path r i (start - 1) ω) ∈ splitBy R) :
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i start ω ≠
      Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i start ω := by
  intro hroot
  have hcard : 2 ≤
      (R (ω r (lineages.path r i (start - 1) ω))).card := by
    simpa [splitBy] using hsplit
  have hslots := secondSelectedSlot_mem_of_card R
    (ω r (lineages.path r i (start - 1) ω)) hcard
  have hsnd := congrArg Prod.snd hroot
  have happend :
      lineages.path r i (start - 1) ω ++
          [firstSelectedSlot R (ω r (lineages.path r i (start - 1) ω))] =
        lineages.path r i (start - 1) ω ++
          [secondSelectedSlot R (ω r (lineages.path r i (start - 1) ω))] := by
    simpa [Restart.SelectedPath.GrowthTrial.growthTrialRootAt,
      Restart.SelectedPath.GrowthTrial.continuationChildAt,
      Nat.ne_of_gt hstart] using hsnd
  have hslotsEq := List.append_cancel_left happend
  have hslotEq :
      firstSelectedSlot R (ω r (lineages.path r i (start - 1) ω)) =
        secondSelectedSlot R (ω r (lineages.path r i (start - 1) ω)) := by
    simpa using hslotsEq
  exact hslots.2 hslotEq

/-- At every finite `σᵢ` declared by a subset of `splitBy R`, the first and
second selected child roots are distinct. Arbitrary finite offspring sizes
are allowed. -/
theorem continuationChildAt_sigma_ne_growthTrialRootAt
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (splitMark : Set (Step α X))
    (hsplitMark : splitMark ⊆ splitBy R)
    (r : Root) (i : Trial) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsigma : lineages.sigma splitMark r i ω = (n + 1 : WithTop ℕ)) :
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i (n + 1) ω ≠
      Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i (n + 1) ω := by
  have hsplit : ω r (lineages.path r i n ω) ∈ splitMark := by
    have hdecl := (firstDeclaredSuccess_eq_iff
      (RootIndexed.splitDeclaration r (lineages.path r i) splitMark)
      ω (n + 1)).mp hsigma
    simpa [RootIndexed.splitDeclaration] using hdecl.1
  apply Restart.SelectedPath.GrowthTrial.continuationChildAt_ne_growthTrialRootAt lineages R r i (n + 1) ω
    (by omega)
  exact hsplitMark hsplit

/-- At a fixed positive generation the second-child root selector has
measurable fibres in the corresponding field filtration. -/
theorem continuationChildAt_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (i : Trial)
    (start : ℕ) (p : Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start]
      {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i start ω = p} := by
  cases start with
  | zero =>
      by_cases hp : (r, []) = p
      · rw [show {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i 0 ω = p} =
            Set.univ by ext ω; simp [continuationChildAt, hp]]
        exact MeasurableSet.univ
      · rw [show {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i 0 ω = p} =
            ∅ by ext ω; simp [continuationChildAt, hp]]
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
      · have heq : {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i (n + 1) ω = p} =
            {ω | lineages.path r i n ω ++
              [secondSelectedSlot R (ω r (lineages.path r i n ω))] = p.2} := by
          ext ω
          simp [continuationChildAt, Prod.ext_iff, hp]
        rw [heq]
        exact hnode (measurableSet_singleton p.2)
      · have heq : {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i (n + 1) ω = p} = ∅ := by
          ext ω
          have hpr : r ≠ p.1 := fun h => hp h.symm
          simp [continuationChildAt, Prod.ext_iff, hpr]
        rw [heq]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty

/-- The second-child root selected at the observable selected-path split completion
`σ_i` has measurable fibres in the stopped domain filtration. The selector
uses only the pre-sampled field at that completion time. -/
theorem continuationChildAt_sigma_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (p : Root × TreeNode α) :
    MeasurableSet[(lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace]
      {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
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
    Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i n
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => chosenAt (WithTop.untopD 0 (σ ω)) ω
  have hzeroStopped : MeasurableSet[hσ.measurableSpace]
      {ω | chosenAt 0 ω = p} := by
    by_cases hp : (r, []) = p
    · have heq : {ω | chosenAt 0 ω = p} = Set.univ := by
        ext ω
        simp [chosenAt, Restart.SelectedPath.GrowthTrial.continuationChildAt, hp]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {ω | chosenAt 0 ω = p} = ∅ := by
        ext ω
        simp [chosenAt, Restart.SelectedPath.GrowthTrial.continuationChildAt, hp]
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
    Restart.SelectedPath.GrowthTrial.continuationChildAt_fiber_measurable lineages R hR r i n p
  simpa [Set.inter_comm] using htimeCell n _ hfiber

/-- A split-completion trial rooted at the second selected child of a
pre-sampled lineage, started at its observable completion `sigma`,
has a stopping-time endpoint in the domain filtration. The selected family
may have any finite size at least two on the split event. -/
theorem sigma_continuationChildSubtree_splitCompletion_isStoppingTime
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => lineages.sigma splitMark r i ω +
        selectedPopulationSplitCompletion R (fun v =>
          ω ((Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
            (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).1)
            (((Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
              (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).2) ++ v))) := by
  let start := lineages.sigma splitMark r i
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstart : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) start :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have hcount : (Set.range chosen).Countable := by
    have hnodes : (Set.range (fun ω => (chosen ω).2)).Countable := Set.to_countable _
    apply hnodes.image (fun u => (r, u)) |>.mono
    rintro p ⟨ω, rfl⟩
    have hroot : (chosen ω).1 = r := by
      exact Restart.SelectedPath.GrowthTrial.continuationChildAt_root lineages R r i
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
      Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_fiber_measurable lineages R hR splitMark hsplit r i p
  have hdepth : ∀ ω, (chosen ω).2.length = WithTop.untopD 0 (start ω) := by
    intro ω
    exact Restart.SelectedPath.GrowthTrial.continuationChildAt_depth lineages R r i
      (WithTop.untopD 0 (start ω)) ω
  have hstopped := RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime_withTop
    R hR start hstart chosen hcount hchosen hdepth
  simpa [start, chosen] using hstopped

/-- The first two selected child roots at the observable selected-path split
completion.  The selector is total on all samples; only on a finite split
completion are both coordinates actual, distinct children. -/
noncomputable def sigmaGrowthTrialAndContinuationRoots
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (splitMark : Set (Step α X))
    (r : Root) (i : Trial) :
    RootIndexed.StepField Root α X → Fin 2 → Root × TreeNode α :=
  fun ω j => if j = 0 then
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
      (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω
    else Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
      (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω

/-- At finite `σᵢ`, the two selected sibling subtrees have the product
branching law, independently of any event observable at `σᵢ`.  The hypothesis
only says that the declaration marks a genuine split (at least two selected
children); offspring size need not equal two. -/
theorem siblingField_factorization_on_finite
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (hsplitMark : splitMark ⊆ splitBy R)
    (r : Root) (i : Trial)
    (A : Set (RootIndexed.StepField Root α X))
    (B : Set (Fin 2 → TreeNode α → Step α X))
    (hA : MeasurableSet[
      (lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        ((A ∩ {ω | lineages.sigma splitMark r i ω ≠ ⊤}) ∩
          RootIndexed.selectedSubtreeStepFieldVector
            (sigmaGrowthTrialAndContinuationRoots lineages R splitMark r i) ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root) μ
        (A ∩ {ω | lineages.sigma splitMark r i ω ≠ ⊤}) *
        RootIndexed.stepFieldLaw (Root := Fin 2) μ B := by
  let σ := lineages.sigma splitMark r i
  let roots := sigmaGrowthTrialAndContinuationRoots lineages R splitMark r i
  have hσ : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) σ :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have hcountPath : (Set.range (fun ω => fun j : Fin 2 =>
      (roots ω j).2)).Countable := Set.to_countable _
  let encode : (Fin 2 → TreeNode α) → Fin 2 → Root × TreeNode α :=
    fun paths j => (r, paths j)
  have hcount : (Set.range roots).Countable := by
    apply (hcountPath.image encode).mono
    intro q hq
    obtain ⟨ω, rfl⟩ := hq
    refine ⟨(fun j => (roots ω j).2), Set.mem_range_self ω, ?_⟩
    funext j
    fin_cases j
    · apply Prod.ext
      · exact (Restart.SelectedPath.GrowthTrial.growthTrialRootAt_root lineages R r i
          (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).symm
      · rfl
    · apply Prod.ext
      · exact (Restart.SelectedPath.GrowthTrial.continuationChildAt_root lineages R r i
          (WithTop.untopD 0 (lineages.sigma splitMark r i ω)) ω).symm
      · rfl
  have hfiber : ∀ q, MeasurableSet[hσ.measurableSpace]
      {ω | roots ω = q} := by
    intro q
    have heq : {ω | roots ω = q} =
        {ω | Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
          (WithTop.untopD 0 (σ ω)) ω = q 0} ∩
        {ω | Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
          (WithTop.untopD 0 (σ ω)) ω = q 1} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨congrFun h 0, congrFun h 1⟩
      · rintro ⟨h0, h1⟩
        apply funext
        intro j
        fin_cases j
        · simpa [roots, sigmaGrowthTrialAndContinuationRoots, σ] using h0
        · simpa [roots, sigmaGrowthTrialAndContinuationRoots, σ] using h1
    rw [heq]
    exact (Restart.SelectedPath.GrowthTrial.growthTrialRootAt_sigma_fiber_measurable lineages
      R hR splitMark hsplit r i (q 0)).inter
      (Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_fiber_measurable lineages
        R hR splitMark hsplit r i (q 1))
  have hdepth : ∀ ω (n : ℕ), σ ω = (n : WithTop ℕ) →
      ∀ j, (roots ω j).2.length = n := by
    intro ω n htime j
    fin_cases j
    · have hlen := Restart.SelectedPath.GrowthTrial.growthTrialRootAt_depth lineages R r i
        (WithTop.untopD 0 (σ ω)) ω
      rw [htime] at hlen
      have hcast : WithTop.untopD 0 (n : WithTop ℕ) = n := rfl
      rw [hcast] at hlen
      simpa [roots, sigmaGrowthTrialAndContinuationRoots, σ, htime, hcast] using hlen
    · have hlen := Restart.SelectedPath.GrowthTrial.continuationChildAt_depth lineages R r i
        (WithTop.untopD 0 (σ ω)) ω
      rw [htime] at hlen
      have hcast : WithTop.untopD 0 (n : WithTop ℕ) = n := rfl
      rw [hcast] at hlen
      simpa [roots, sigmaGrowthTrialAndContinuationRoots, σ, htime, hcast] using hlen
  have hnonzero : ∀ ω, σ ω ≠ (0 : WithTop ℕ) := by
    intro ω hzero
    have hσeq := congrFun (lineages.sigma_eq_tau_add_one splitMark r i) ω
    have hσeq' : σ ω = lineages.tau splitMark r i ω + 1 := by
      simpa [σ] using hσeq
    rw [hσeq'] at hzero
    cases hτ : lineages.tau splitMark r i ω <;> simp [hτ] at hzero
  have hinj : ∀ ω, σ ω ≠ ⊤ → Function.Injective (roots ω) := by
    intro ω hfinite
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have htime : σ ω = (n : WithTop ℕ) := hn.symm
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hnonzero ω
      simpa [hn0] using htime
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hsigma : σ ω = (m + 1 : WithTop ℕ) := by simpa using htime
    have hseparate := Restart.SelectedPath.GrowthTrial.continuationChildAt_sigma_ne_growthTrialRootAt lineages
      R splitMark hsplitMark r i m ω hsigma
    have hne : roots ω 0 ≠ roots ω 1 := by
      have hsel : Restart.SelectedPath.GrowthTrial.growthTrialRootAt lineages R r i
          (WithTop.untopD 0 (σ ω)) ω ≠
          Restart.SelectedPath.GrowthTrial.continuationChildAt lineages R r i
            (WithTop.untopD 0 (σ ω)) ω := by
        rw [hsigma]
        have hcast : WithTop.untopD 0 ((m + 1 : WithTop ℕ)) = m + 1 := rfl
        rw [hcast]
        exact hseparate
      simpa [roots, sigmaGrowthTrialAndContinuationRoots, σ] using hsel
    intro j k hjk
    fin_cases j <;> fin_cases k
    · rfl
    · exact (hne hjk).elim
    · exact (hne hjk.symm).elim
    · rfl
  exact RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ σ hσ roots hcount hfiber hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

end
