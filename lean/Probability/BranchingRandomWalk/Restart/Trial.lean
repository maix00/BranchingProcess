/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
public import Probability.BranchingRandomWalk.Restart.ReserveLineage

/-!
# Observable first-split growth trials

This module gives the first reserve-lineage candidate the concrete event used
in the thesis: after the first split, the selected first child starts a finite
growth trial, which stays nonempty and below the cap before its endpoint and
ends in the prescribed population band.  The split-completion generation is
used as the trial start, so the trial event is measurable at its actual
completion time.

The result is an event and measurability adapter.  It does not identify a
sequence of reserve siblings after failed trials or supply the exploration
filtration needed to keep those subtrees fresh.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The first slot in a finite selected family, with a total value on the
empty-family case.  On a split mark this is the first selected child. -/
noncomputable def firstSelectedSlot {α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  if h : (R ξ).Nonempty then (R ξ).min' h else ⊥

theorem firstSelectedSlot_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [LinearOrder α]
    [OrderBot α] [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) : Measurable (firstSelectedSlot R) := by
  let f : Finset α → α := fun s => if h : s.Nonempty then s.min' h else ⊥
  have hf : Measurable f := measurable_of_countable f
  have heq : firstSelectedSlot R = f ∘ R.select := by
    funext ξ
    rfl
  rw [heq]
  exact hf.comp hR

theorem firstSelectedSlot_mem {α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) : firstSelectedSlot R ξ ∈ R ξ := by
  rw [firstSelectedSlot, dite_eq_left hne]
  exact Finset.min'_mem _ _

/-- A split is a step at which the chosen finite offspring rule retains at
least two children. -/
def splitBy {α X : Type*} (R : Step.FiniteSelection α X) : Set (Step α X) :=
  {ξ | 2 ≤ (R ξ).card}

theorem splitBy_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) : MeasurableSet (splitBy R) := by
  change MeasurableSet {ξ | 2 ≤ (R ξ).card}
  have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hR
  exact hcard measurableSet_Ici

/-- The event for a finite growth trial. The endpoint has population in
`[lower, upper]`; at every earlier positive age the process is nonempty and
has population strictly below `upper`. -/
def growthTrialSuccess {α X : Type*} (R : Step.FiniteSelection α X)
    (lower upper duration : ℕ) (ω : Mark α (Step α X)) : Prop :=
    lower ≤ (StepSelection.population R duration ω).card ∧
    (StepSelection.population R duration ω).card ≤ upper ∧
    ∀ k : Fin (duration - 1),
      0 < (StepSelection.population R (k.val + 1) ω).card ∧
        (StepSelection.population R (k.val + 1) ω).card < upper

theorem growthTrialSuccess_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) (lower upper duration : ℕ) :
    MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | growthTrialSuccess R lower upper duration ω} := by
  have hcard (k : ℕ) : Measurable[generationFiltration (M := Step α X) k]
      (fun ω => (StepSelection.population R k ω).card) := by
    exact (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
      (StepSelection.population_adapted R hR k)
  have hend := hcard duration
  have hendlo : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | lower ≤ (StepSelection.population R duration ω).card} :=
    hend measurableSet_Ici
  have hendhi : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | (StepSelection.population R duration ω).card ≤ upper} :=
    hend measurableSet_Iic
  have hinterEq :
      {ω | ∀ k : Fin (duration - 1),
        0 < (StepSelection.population R (k.val + 1) ω).card ∧
          (StepSelection.population R (k.val + 1) ω).card < upper} =
        ⋂ k : Fin (duration - 1),
          {ω | 0 < (StepSelection.population R (k.val + 1) ω).card ∧
            (StepSelection.population R (k.val + 1) ω).card < upper} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hinter : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | ∀ k : Fin (duration - 1),
        0 < (StepSelection.population R (k.val + 1) ω).card ∧
          (StepSelection.population R (k.val + 1) ω).card < upper} := by
    rw [hinterEq]
    apply MeasurableSet.iInter
    intro k
    have hlocal := hcard (k.val + 1)
    have hle : k.val + 1 ≤ duration := by omega
    have hglobal : Measurable[generationFiltration (M := Step α X) duration]
        (fun ω => (StepSelection.population R (k.val + 1) ω).card) :=
      hlocal.mono (generationFiltration (M := Step α X) |>.mono hle) le_rfl
    have hpos : MeasurableSet[generationFiltration (M := Step α X) duration]
        {ω | 0 < (StepSelection.population R (k.val + 1) ω).card} :=
      hglobal measurableSet_Ioi
    have hcap : MeasurableSet[generationFiltration (M := Step α X) duration]
        {ω | (StepSelection.population R (k.val + 1) ω).card < upper} :=
      hglobal measurableSet_Iio
    exact hpos.inter hcap
  exact hendlo.inter (hendhi.inter hinter)

/-- The subtree of a fixed labelled node, viewed only through its first
`duration` generations, is observable by the corresponding global generation
when the root has depth `start`. -/
theorem RootIndexed.fixedSubtree_measurable_at
    {Root α X : Type*} [MeasurableSpace X]
    (root : Root × TreeNode α) (start duration : ℕ)
    (hdepth : root.2.length = start) :
    @Measurable (RootIndexed.StepField Root α X)
      (Mark α (Step α X))
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
        (start + duration))
      (generationFiltration (M := Step α X) duration)
      (fun ω v => ω root.1 (root.2 ++ v)) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
      (start + duration)
  let _ : MeasurableSpace (Mark α (Step α X)) :=
    generationFiltration (M := Step α X) duration
  change Measurable[RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) (start + duration)]
    (fun ω : RootIndexed.StepField Root α X =>
      fun v : TreeNode α => ω root.1 (root.2 ++ v))
  apply measurable_generateFrom
  intro s hs
  obtain ⟨v, hv, t, ht, rfl⟩ := hs
  have hcoord : (root.2 ++ v).length < start + duration := by
    rw [List.length_append, hdepth]
    omega
  exact RootIndexed.step_measurable root.1 (root.2 ++ v) hcoord ht

/-- The address of the first selected child at a prescribed observable split
generation. Generation zero is totalized because a split completion is
always at a positive generation. -/
noncomputable def RootIndexed.ReserveLineages.firstChildRootAt
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X) : Root × TreeNode α :=
  if _h : start = 0 then (r, []) else
    let parent := lineages.path r i (start - 1) ω
    (r, parent ++ [firstSelectedSlot R (ω r parent)])

theorem RootIndexed.ReserveLineages.firstChildRootAt_root
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (lineages.firstChildRootAt R r i start ω).1 = r := by
  by_cases hs : start = 0 <;>
    simp [firstChildRootAt, hs]

theorem RootIndexed.ReserveLineages.firstChildRootAt_depth
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X) :
    (lineages.firstChildRootAt R r i start ω).2.length = start := by
  by_cases hs : start = 0
  · simp [firstChildRootAt, hs]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    simp [firstChildRootAt, lineages.depth]

/-- On a split mark, the first selected slot is an actual child of the split
parent. The parent is at generation `start - 1`, and its child is at
generation `start`. -/
theorem RootIndexed.ReserveLineages.firstChildRootAt_selected
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (r : Root) (i : Trial)
    (start : ℕ) (ω : RootIndexed.StepField Root α X)
    (hstart : 0 < start)
    (hsplit : ω r (lineages.path r i (start - 1) ω) ∈ splitBy R) :
    (lineages.firstChildRootAt R r i start ω).2 =
        lineages.path r i (start - 1) ω ++
          [firstSelectedSlot R (ω r (lineages.path r i (start - 1) ω))] ∧
      firstSelectedSlot R (ω r (lineages.path r i (start - 1) ω)) ∈
        R (ω r (lineages.path r i (start - 1) ω)) := by
  constructor
  · simp [firstChildRootAt, Nat.ne_of_gt hstart]
  · apply firstSelectedSlot_mem
    have hcard : 2 ≤
        (R (ω r (lineages.path r i (start - 1) ω))).card := by
      simpa [splitBy] using hsplit
    exact Finset.card_pos.mp (by omega)

theorem RootIndexed.ReserveLineages.firstChildRootAt_fiber_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (i : Trial)
    (start : ℕ) (p : Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start]
      {ω | lineages.firstChildRootAt R r i start ω = p} := by
  cases start with
  | zero =>
      by_cases hp : (r, []) = p
      · rw [show {ω | lineages.firstChildRootAt R r i 0 ω = p} =
            Set.univ by ext ω; simp [firstChildRootAt, hp]]
        exact MeasurableSet.univ
      · rw [show {ω | lineages.firstChildRootAt R r i 0 ω = p} =
            ∅ by ext ω; simp [firstChildRootAt, hp]]
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
          (fun ω => firstSelectedSlot R (ω r (lineages.path r i n ω))) :=
        (firstSelectedSlot_measurable R hR).comp hmark
      have hnode : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)]
          (fun ω => lineages.path r i n ω ++
            [firstSelectedSlot R (ω r (lineages.path r i n ω))]) := by
        exact (measurable_of_countable (fun q : TreeNode α × α =>
          q.1 ++ [q.2])).comp (hpath.prodMk hslot)
      by_cases hp : p.1 = r
      · have heq : {ω | lineages.firstChildRootAt R r i (n + 1) ω = p} =
            {ω | lineages.path r i n ω ++
              [firstSelectedSlot R (ω r (lineages.path r i n ω))] = p.2} := by
          ext ω
          simp [firstChildRootAt, Prod.ext_iff, hp]
        rw [heq]
        exact hnode (measurableSet_singleton p.2)
      · have heq : {ω | lineages.firstChildRootAt R r i (n + 1) ω = p} = ∅ := by
          ext ω
          have hpr : r ≠ p.1 := fun h => hp h.symm
          simp [firstChildRootAt, Prod.ext_iff, hpr]
        rw [heq]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)).measurableSet_empty

/-- A finite selected-population trial with a random, generation-observable
root has a measurable band-success event at its endpoint. -/
theorem RootIndexed.growthTrialSuccessAt_selectedRoot_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (start duration lower upper : ℕ)
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hchosen : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start] {ω | chosen ω = p})
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).2.length = start) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + duration)]
      {ω | growthTrialSuccess R lower upper duration
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))} := by
  let S : Set (Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hfixed (p : S) : MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + duration)]
      {ω | growthTrialSuccess R lower upper duration
        (fun v => ω p.1.1 (p.1.2 ++ v))} := by
    have hsub : @Measurable (RootIndexed.StepField Root α X)
        (Mark α (Step α X))
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
          (start + duration))
        (generationFiltration (M := Step α X) duration)
        (fun ω v => ω p.1.1 (p.1.2 ++ v)) :=
      RootIndexed.fixedSubtree_measurable_at p.1 start duration
        (by obtain ⟨ω, hω⟩ := p.2; simpa [← hω] using hdepth ω)
    have hlocal : MeasurableSet[generationFiltration
        (M := Step α X) duration]
        {ω | growthTrialSuccess R lower upper duration ω} :=
      growthTrialSuccess_measurable R hR lower upper duration
    exact hlocal.preimage hsub
  have heq :
      {ω | growthTrialSuccess R lower upper duration
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))} =
        ⋃ p : S, {ω | chosen ω = p.1} ∩
          {ω | growthTrialSuccess R lower upper duration
            (fun v => ω p.1.1 (p.1.2 ++ v))} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨p, hp, h⟩
      simpa [hp] using h
  rw [heq]
  apply MeasurableSet.iUnion
  intro p
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hfiber : MeasurableSet[F (start + duration)]
      {ω | chosen ω = p.1} :=
    F.mono (Nat.le_add_right start duration) _ (hchosen p.1)
  exact hfiber.inter (hfixed p)

/-- The growth test attached to a first-split candidate.  If the global
generation is too early to contain a positive split generation followed by
the requested trial duration, the test is empty. -/
noncomputable def RootIndexed.ReserveLineages.firstGrowthCandidateTest
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (r : Root) (i : Trial) (duration lower upper n : ℕ) :
    Set (RootIndexed.StepField Root α X) :=
  if 0 < n - duration then
    {ω | growthTrialSuccess growthSelection lower upper duration
      (fun v => ω ((lineages.firstChildRootAt splitSelection r i
        (n - duration) ω).1)
        ((lineages.firstChildRootAt splitSelection r i
          (n - duration) ω).2 ++ v))}
  else ∅

theorem RootIndexed.ReserveLineages.firstGrowthCandidateTest_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplitSelection : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (r : Root) (i : Trial) (duration lower upper n : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (lineages.firstGrowthCandidateTest splitSelection growthSelection
        r i duration lower upper n) := by
  unfold RootIndexed.ReserveLineages.firstGrowthCandidateTest
  by_cases hstart : 0 < n - duration
  · let start := n - duration
    have hsum : start + duration = n := by dsimp [start]; omega
    let chosen := lineages.firstChildRootAt splitSelection r i start
    have hchosen := lineages.firstChildRootAt_fiber_measurable
      splitSelection hsplitSelection r i start
    have hcount : (Set.range chosen).Countable := by
      have hnode : (Set.range (fun ω => (chosen ω).2)).Countable :=
        Set.to_countable _
      apply hnode.image (fun u => (r, u)) |>.mono
      rintro p ⟨ω, rfl⟩
      have hpair : (r, (chosen ω).2) = chosen ω := by
        have hroot := lineages.firstChildRootAt_root splitSelection r i start ω
        have hroot' : (chosen ω).1 = r := by simpa [chosen] using hroot
        apply Prod.ext
        · exact hroot'.symm
        · rfl
      exact ⟨(chosen ω).2, ⟨ω, rfl⟩,
        hpair⟩
    have hdepth : ∀ ω, (chosen ω).2.length = start := by
      intro ω
      exact lineages.firstChildRootAt_depth splitSelection r i start ω
    have hsuccess := RootIndexed.growthTrialSuccessAt_selectedRoot_measurable
      growthSelection hgrowth start duration lower upper chosen
      hchosen hcount hdepth
    simp only [hstart, ↓reduceIte]
    rw [← hsum]
    simpa [chosen, start] using hsuccess
  · simp [hstart]

/-- Completion of the first-split growth trial. -/
noncomputable def RootIndexed.ReserveLineages.firstGrowthCompletion
    {Root Trial α X : Type*} [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (r : Root) (i : Trial)
    (duration : ℕ) : RootIndexed.StepField Root α X → WithTop ℕ :=
  fun ω => lineages.sigma splitMark r i ω + duration

/-- With `duration = ℓ - 1`, the observable candidate endpoint `σ + duration`
is the thesis's `τ + ℓ`. -/
theorem RootIndexed.ReserveLineages.firstGrowthCompletion_eq_tau_add_trialLength
    {Root Trial α X : Type*} [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (r : Root) (i : Trial) (ell : ℕ)
    (hell : 1 ≤ ell) :
    lineages.firstGrowthCompletion splitMark r i (ell - 1) =
      fun ω => lineages.tau splitMark r i ω + ell := by
  funext ω
  rw [firstGrowthCompletion, lineages.sigma_eq_tau_add_one]
  have hnat : 1 + (ell - 1) = ell := by omega
  calc
    (lineages.tau splitMark r i ω + 1) + (ell - 1) =
        lineages.tau splitMark r i ω +
          ((1 : WithTop ℕ) + (ell - 1 : WithTop ℕ)) := by simp [add_assoc]
    _ = lineages.tau splitMark r i ω + ell := by rw [← hnat]; simp

theorem RootIndexed.ReserveLineages.firstGrowthCompletion_isStoppingTime
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (duration : ℕ) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (lineages.firstGrowthCompletion splitMark r i duration) := by
  exact (lineages.sigma_isStoppingTime splitMark hsplit r i).add_const' duration

/-- Candidate growth succeeds at the observable generation following the
first split by `duration` further generations. -/
noncomputable def RootIndexed.ReserveLineages.firstGrowthCandidateSuccess
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (splitMark : Set (Step α X)) (r : Root) (i : Trial)
    (duration lower upper : ℕ) :
    Set (RootIndexed.StepField Root α X) :=
  successAtCompletion
    (lineages.firstGrowthCompletion splitMark r i duration)
    (fun n => lineages.firstGrowthCandidateTest splitSelection growthSelection
      r i duration lower upper n)

theorem RootIndexed.ReserveLineages.firstGrowthCandidate_observable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplitSelection : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (r : Root) (i : Trial) (duration lower upper : ℕ) :
    CandidateObservable (ι := Unit)
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (fun _ : Unit => lineages.firstGrowthCompletion splitMark r i duration)
      (fun _ : Unit => lineages.firstGrowthCandidateSuccess splitSelection
        growthSelection splitMark r i duration lower upper) := by
  exact successAtCompletion_observable
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    (fun _ : Unit => lineages.firstGrowthCompletion splitMark r i duration)
    (fun _ n => lineages.firstGrowthCandidateTest splitSelection
      growthSelection r i duration lower upper n)
    (fun _ => lineages.firstGrowthCompletion_isStoppingTime
      splitMark hsplit r i duration)
    (fun _ n => lineages.firstGrowthCandidateTest_measurable
      splitSelection growthSelection hsplitSelection hgrowth
      r i duration lower upper n)

/-- The success event for any countable family of first-split growth
candidates is measurable by a fixed horizon. -/
theorem RootIndexed.ReserveLineages.firstGrowthCandidatesWithin_measurable
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplitSelection : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (candidates : Set (Root × Trial)) (hcandidates : candidates.Countable)
    (duration lower upper T : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T]
      (successfulCandidateWithin
        (fun p => lineages.firstGrowthCompletion
          splitMark p.1 p.2 duration)
        (fun p => lineages.firstGrowthCandidateSuccess
          splitSelection growthSelection splitMark p.1 p.2
          duration lower upper)
        candidates T) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let completion := fun p : Root × Trial =>
    lineages.firstGrowthCompletion splitMark p.1 p.2 duration
  let test := fun p : Root × Trial =>
    fun n => lineages.firstGrowthCandidateTest splitSelection growthSelection
      p.1 p.2 duration lower upper n
  have hcompletion : ∀ p, IsStoppingTime F (completion p) := by
    intro p
    exact lineages.firstGrowthCompletion_isStoppingTime
      splitMark hsplit p.1 p.2 duration
  have htest : ∀ p n, MeasurableSet[F n] (test p n) := by
    intro p n
    exact lineages.firstGrowthCandidateTest_measurable
      splitSelection growthSelection hsplitSelection hgrowth
      p.1 p.2 duration lower upper n
  have hobs := successAtCompletion_observable F completion test
    hcompletion htest
  exact successfulCandidateWithin_measurable F completion
    (fun p => successAtCompletion (completion p) (test p)) hobs
    candidates hcandidates T

/-- The paper's first-split growth event supplies the observable candidate
family consumed by the existing `L¹` restart estimate. The probability bound
for candidate failure remains an explicit input, as does freshness of the
continuation subtree family. -/
theorem RootIndexed.ReserveLineages.integral_selectedSubtree_abs_on_firstGrowthFailure_le
    {Root Trial κ α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSpace X]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplitSelection : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (candidates : Set (Root × Trial)) (hcandidates : candidates.Countable)
    (T duration lower upper : ℕ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hchosenRangeCountable : (Set.range chosen).Countable)
    (hchosenFiberMeasurable : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) T] {ω | chosen ω = roots})
    (hchosenDepth : ∀ ω i, (chosen ω i).2.length = T)
    (hchosenInjective : ∀ ω, Function.Injective (chosen ω))
    (g : (κ → TreeNode α → Step α X) → ℝ) (hg : Measurable g)
    (hint : Integrable
      (fun ω => g (RootIndexed.selectedSubtreeStepFieldVector chosen ω))
      (RootIndexed.stepFieldLaw (Root := Root) μ))
    (B p : ℝ) (hB : 0 ≤ B)
    (hmoment : (∫ ω,
        |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)|
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B)
    (hprob : (RootIndexed.stepFieldLaw (Root := Root) μ).real
      (successfulCandidateWithin
        (fun q => lineages.firstGrowthCompletion splitMark q.1 q.2 duration)
        (fun q => lineages.firstGrowthCandidateSuccess splitSelection
          growthSelection splitMark q.1 q.2 duration lower upper)
        candidates T)ᶜ ≤ p) :
    (∫ ω, |g (RootIndexed.selectedSubtreeStepFieldVector chosen ω)| *
        (successfulCandidateWithin
          (fun q => lineages.firstGrowthCompletion splitMark q.1 q.2 duration)
          (fun q => lineages.firstGrowthCandidateSuccess splitSelection
            growthSelection splitMark q.1 q.2 duration lower upper)
          candidates T)ᶜ.indicator (fun _ => (1 : ℝ)) ω
      ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤ B * p := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let completion := fun q : Root × Trial =>
    lineages.firstGrowthCompletion splitMark q.1 q.2 duration
  let test := fun q : Root × Trial =>
    fun n => lineages.firstGrowthCandidateTest splitSelection growthSelection
      q.1 q.2 duration lower upper n
  let success := fun q : Root × Trial =>
    successAtCompletion (completion q) (test q)
  have hcompletion : ∀ q, IsStoppingTime F (completion q) := by
    intro q
    exact lineages.firstGrowthCompletion_isStoppingTime
      splitMark hsplit q.1 q.2 duration
  have htest : ∀ q n, MeasurableSet[F n] (test q n) := by
    intro q n
    exact lineages.firstGrowthCandidateTest_measurable
      splitSelection growthSelection hsplitSelection hgrowth
      q.1 q.2 duration lower upper n
  have hobs := successAtCompletion_observable F completion test
    hcompletion htest
  have hprob' : (RootIndexed.stepFieldLaw (Root := Root) μ).real
      (successfulCandidateWithin completion success candidates T)ᶜ ≤ p := by
    simpa [completion, success, firstGrowthCandidateSuccess] using hprob
  have hevent :
      (successfulCandidateWithin
        (fun q => lineages.firstGrowthCompletion splitMark q.1 q.2 duration)
        (fun q => lineages.firstGrowthCandidateSuccess splitSelection
          growthSelection splitMark q.1 q.2 duration lower upper)
        candidates T)ᶜ =
      (successfulCandidateWithin completion success candidates T)ᶜ := by
    ext ω
    simp [completion, success, test, firstGrowthCandidateSuccess]
  rw [hevent]
  rw [RootIndexed.integral_reserve_abs_on_candidateFailure
    μ completion success hobs candidates hcandidates chosen
    hchosenRangeCountable hchosenFiberMeasurable hchosenDepth
    hchosenInjective g hg hint]
  exact mul_le_mul hmoment hprob' (by positivity) hB

end ProbabilityTheory.BranchingRandomWalk

end
