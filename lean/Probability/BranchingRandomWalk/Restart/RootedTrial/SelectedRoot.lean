/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial

/-!
# Split trials from an observable selected root

At a fixed generation, a root may be selected using the information already
observed by that generation.  Splitting the event by the countable range of
the selector reduces its descendant split time to the fixed-root theorem.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

private theorem nat_add_withTop_le_iff
    (start age n : ℕ) (hsum : start + age = n) (m : WithTop ℕ) :
    (start : WithTop ℕ) + m ≤ n ↔ m ≤ age := by
  cases m with
  | top => simp
  | coe k =>
      constructor
      · intro h
        have hnat : start + k ≤ n := by
          have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n := by
            convert h using 1
            exact WithTop.coe_add start k
          exact WithTop.coe_le_coe.mp h'
        have hk : k ≤ age := by omega
        exact WithTop.coe_le_coe.mpr hk
      · intro h
        have hk : k ≤ age := WithTop.coe_le_coe.mp h
        have hnat : start + k ≤ n := by omega
        have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n :=
          WithTop.coe_le_coe.mpr hnat
        convert h' using 1
        exact WithTop.coe_add start k

private theorem nat_of_withTop_add_le
    {start n : ℕ} {m : WithTop ℕ}
    (h : (start : WithTop ℕ) + m ≤ n) : start ≤ n := by
  cases m with
  | top => simp at h
  | coe k =>
      have hnat : start + k ≤ n := by
        have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n := by
          convert h using 1
          exact WithTop.coe_add start k
        exact WithTop.coe_le_coe.mp h'
      omega

/-- The split-completion time in a subtree whose root is selected measurably
at a deterministic generation.  The selected root has that generation as
its depth, so the local completion is shifted into the ambient filtration. -/
theorem RootIndexed.selectedSubtree_splitCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    (start : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hchosen : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start] {ω | chosen ω = p})
    (hdepth : ∀ ω, (chosen ω).2.length = start) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => (start : WithTop ℕ) +
        selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let subtree (p : Root × TreeNode α) :
      RootIndexed.StepField Root α X → Mark α (Step α X) :=
    fun ω v => ω p.1 (p.2 ++ v)
  intro n
  change MeasurableSet[F n]
    {ω | (start : WithTop ℕ) +
      selectedPopulationSplitCompletion R
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n}
  by_cases hstart : start ≤ n
  · let age := n - start
    have hsum : start + age = n := Nat.add_sub_of_le hstart
    rw [← hsum]
    let S : Set (Root × TreeNode α) := Set.range chosen
    let _ : Countable S := Set.countable_coe_iff.mpr hcount
    have hevent :
        {ω | (start : WithTop ℕ) +
          selectedPopulationSplitCompletion R
            (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤
              (start + age : ℕ)} =
        ⋃ p : S, {ω | chosen ω = p.1} ∩
          {ω | selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ age} := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro htime
        refine ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, ?_⟩
        have hlocal := (nat_add_withTop_le_iff start age (start + age) rfl
          (selectedPopulationSplitCompletion R
            (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)))).mp htime
        simpa [subtree] using hlocal
      · rintro ⟨p, hp, hlocal⟩
        have htime := (nat_add_withTop_le_iff start age (start + age) rfl
          (selectedPopulationSplitCompletion R ((subtree p.1) ω))).mpr hlocal
        simpa [hp, subtree] using htime
    rw [hevent]
    apply MeasurableSet.iUnion
    intro p
    have hdepthp : p.1.2.length = start := by
      obtain ⟨ω, hω⟩ := p.2
      simpa [← hω] using hdepth ω
    have hsub : @Measurable (RootIndexed.StepField Root α X)
        (Mark α (Step α X)) (F (start + age))
        (generationFiltration (M := Step α X) age) (subtree p.1) :=
      RootIndexed.fixedSubtree_measurable_at p.1 start age hdepthp
    have hlocal : MeasurableSet[F (start + age)]
        {ω | selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ age} :=
      (selectedPopulationSplitCompletion_isStoppingTime R hR age).preimage hsub
    have hfiber : MeasurableSet[F (start + age)] {ω | chosen ω = p.1} :=
      F.mono (Nat.le_add_right start age) _ (hchosen p.1)
    exact hfiber.inter hlocal
  · have hnot :
        {ω : RootIndexed.StepField Root α X | (start : WithTop ℕ) +
          selectedPopulationSplitCompletion R
            (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro htime
      cases hcompletion : selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) with
      | top => simp [hcompletion] at htime
      | coe k =>
          rw [hcompletion] at htime
          have hnatural : start + k ≤ n := by
            have h' : (↑(start + k) : WithTop ℕ) ≤ ↑n := by
              convert htime using 1
              exact WithTop.coe_add start k
            exact WithTop.coe_le_coe.mp h'
          omega
    rw [hnot]
    exact F n |>.measurableSet_empty

/-- A stopping-time root selector can start a split trial at its random
completion generation.  The selector is measurable in the stopped sigma
algebra of `start`, and every selected root has depth `start`.  The proof
decomposes by the countable range of selected roots and applies the
fixed-root stopping-time result to each descendant subtree. -/
theorem RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (start : RootIndexed.StepField Root α X → ℕ)
    (hstart : IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => (start ω : WithTop ℕ)))
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hchosen : ∀ p, MeasurableSet[hstart.measurableSpace]
      {ω | chosen ω = p})
    (hdepth : ∀ ω, (chosen ω).2.length = start ω) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => (start ω : WithTop ℕ) +
        selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let subtree (p : Root × TreeNode α) :
      RootIndexed.StepField Root α X → Mark α (Step α X) :=
    fun ω v => ω p.1 (p.2 ++ v)
  intro n
  change MeasurableSet[F n]
    {ω | (start ω : WithTop ℕ) +
      selectedPopulationSplitCompletion R
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n}
  let S : Set (Root × TreeNode α) :=
    {p | p ∈ Set.range chosen ∧ p.2.length ≤ n}
  have hScount : S.Countable :=
    hcount.mono (by intro p hp; exact hp.1)
  let _ : Countable S := Set.countable_coe_iff.mpr hScount
  have hevent :
      {ω | (start ω : WithTop ℕ) +
        selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n} =
      ⋃ p : S, {ω | chosen ω = p.1} ∩
        {ω | (p.1.2.length : WithTop ℕ) +
          selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ n} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro htime
      let p := chosen ω
      have hstartle : start ω ≤ n :=
        nat_of_withTop_add_le htime
      have hpdepth : p.2.length ≤ n := by
        rw [hdepth ω]
        exact hstartle
      refine ⟨⟨p, Set.mem_range_self ω, hpdepth⟩, rfl, ?_⟩
      have hstartEq : start ω = p.2.length := by
        rw [← hdepth ω]
      simpa [p, subtree, hstartEq] using htime
    · rintro ⟨p, hp, hfixed⟩
      have hstartEq : start ω = p.1.2.length := by
        rw [← hdepth ω, hp]
      simpa [subtree, hp, hstartEq] using hfixed
  rw [hevent]
  apply MeasurableSet.iUnion
  intro p
  let d := p.1.2.length
  have hchosenAtDepth : MeasurableSet[F d] {ω | chosen ω = p.1} := by
    have htimeEq : MeasurableSet[hstart.measurableSpace]
        {ω | (start ω : WithTop ℕ) = d} :=
      (measurableSet_singleton _).preimage hstart.measurable
    have hstoppedInter : MeasurableSet[hstart.measurableSpace]
        ({ω | chosen ω = p.1} ∩ {ω | (start ω : WithTop ℕ) = d}) :=
      (hchosen p.1).inter htimeEq
    have hstopped := (hstart.measurableSet_inter_eq_iff
      {ω | chosen ω = p.1} d).mp hstoppedInter
    have heq : {ω | chosen ω = p.1} ∩
        {ω | (start ω : WithTop ℕ) = d} = {ω | chosen ω = p.1} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · exact fun h => h.1
      · intro hp
        refine ⟨hp, ?_⟩
        rw [← hdepth ω, hp]
    rw [← heq]
    simpa [d] using hstopped
  have hchosenAtN : MeasurableSet[F n] {ω | chosen ω = p.1} :=
    F.mono p.2.2 _ hchosenAtDepth
  have hfixed : MeasurableSet[F n]
      {ω | (d : WithTop ℕ) +
        selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ n} := by
    simpa [d, subtree] using
      (RootIndexed.fixedSubtree_splitCompletion_isStoppingTime
        p.1 d rfl R hR n)
  exact hchosenAtN.inter hfixed

/-- The random start may itself be an infinite-valued stopping time, as is a
raw first-declaration completion `σ`.  On `start = ⊤` the total completion is
also `⊤`; on finite fibers the chosen root has the corresponding generation
as its depth. -/
theorem RootIndexed.stoppedSubtree_splitCompletion_isStoppingTime_withTop
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (start : RootIndexed.StepField Root α X → WithTop ℕ)
    (hstart : IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X)) start)
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hchosen : ∀ p, MeasurableSet[hstart.measurableSpace]
      {ω | chosen ω = p})
    (hdepth : ∀ ω, (chosen ω).2.length = WithTop.untopD 0 (start ω)) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (fun ω => start ω +
        selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let subtree (p : Root × TreeNode α) :
      RootIndexed.StepField Root α X → Mark α (Step α X) :=
    fun ω v => ω p.1 (p.2 ++ v)
  intro n
  change MeasurableSet[F n]
    {ω | start ω +
      selectedPopulationSplitCompletion R
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n}
  let S : Set (Root × TreeNode α) :=
    {p | p ∈ Set.range chosen ∧ p.2.length ≤ n}
  have hScount : S.Countable :=
    hcount.mono (by intro p hp; exact hp.1)
  let _ : Countable S := Set.countable_coe_iff.mpr hScount
  have hevent :
      {ω | start ω +
        selectedPopulationSplitCompletion R
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) ≤ n} =
      ⋃ p : S, {ω | chosen ω = p.1} ∩
        ({ω | start ω = (p.1.2.length : WithTop ℕ)} ∩
          {ω | (p.1.2.length : WithTop ℕ) +
            selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ n}) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro htime
      cases hs : start ω with
      | top => simp [hs] at htime
      | coe k =>
          cases hc : selectedPopulationSplitCompletion R
              (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) with
          | top => simp [hs, hc] at htime
          | coe m =>
              have h' : (↑(k + m) : WithTop ℕ) ≤ n := by
                calc
                  (↑(k + m) : WithTop ℕ) = (↑k : WithTop ℕ) + ↑m :=
                    WithTop.coe_add k m
                  _ = start ω + selectedPopulationSplitCompletion R
                      (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v)) := by
                    rw [hs, hc]
                    rfl
                  _ ≤ n := htime
              have hnat : k + m ≤ n :=
                (WithTop.coe_le_coe (a := n) (b := k + m)).mp h'
              have hdepthNat : (chosen ω).2.length = k := by
                have h := hdepth ω
                rw [hs, WithTop.untopD_coe] at h
                exact h
              have hdepthLe : (chosen ω).2.length ≤ n := by omega
              refine ⟨⟨chosen ω, Set.mem_range_self ω, hdepthLe⟩, rfl, ?_⟩
              constructor
              · change (↑k : WithTop ℕ) = ((chosen ω).2.length : WithTop ℕ)
                exact congrArg (fun j : ℕ => (j : WithTop ℕ)) hdepthNat.symm
              · simpa [subtree, hs, hdepthNat] using htime
    · rintro ⟨p, hp, ⟨hstartEq, hfixed⟩⟩
      simpa [subtree, hp, hstartEq] using hfixed
  rw [hevent]
  apply MeasurableSet.iUnion
  intro p
  let d := p.1.2.length
  have htimeEq : MeasurableSet[hstart.measurableSpace]
      {ω | start ω = (d : WithTop ℕ)} :=
    (measurableSet_singleton _).preimage hstart.measurable
  have hchosenAndTime : MeasurableSet[hstart.measurableSpace]
      ({ω | chosen ω = p.1} ∩ {ω | start ω = (d : WithTop ℕ)}) :=
    (hchosen p.1).inter htimeEq
  have hchosenAtDepth : MeasurableSet[F d]
      ({ω | chosen ω = p.1} ∩ {ω | start ω = (d : WithTop ℕ)}) := by
    simpa using (hstart.measurableSet_inter_eq_iff
      {ω | chosen ω = p.1} d).mp hchosenAndTime
  have hchosenAtN : MeasurableSet[F n]
      ({ω | chosen ω = p.1} ∩ {ω | start ω = (d : WithTop ℕ)}) :=
    F.mono p.2.2 _ hchosenAtDepth
  have hfixed : MeasurableSet[F n]
      {ω | (d : WithTop ℕ) +
        selectedPopulationSplitCompletion R ((subtree p.1) ω) ≤ n} := by
    simpa [d, subtree] using
      (RootIndexed.fixedSubtree_splitCompletion_isStoppingTime
        p.1 d rfl R hR n)
  simpa only [Set.inter_assoc] using hchosenAtN.inter hfixed

end ProbabilityTheory.BranchingRandomWalk

end
