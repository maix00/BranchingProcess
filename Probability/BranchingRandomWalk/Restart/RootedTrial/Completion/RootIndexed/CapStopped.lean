/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Combinatorics.BranchingWalk.Step.Selection.Finite
public import Combinatorics.UlamHarris.Basic
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.CapStopped
public import Probability.BranchingRandomWalk.Restart.Trial.RootIndexed
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Basic
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Lineage
public import Probability.BranchingRandomWalk.Tree.Filtration
public import Mathlib.Basic.Countable.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Root-indexed cap-stopped reserve candidates

For a reserve-lineage family, capStoppedCandidate starts the growth process
from the first selected child of the split observed at its start generation.
## Public declarations

The declarations in ProbabilityTheory.BranchingRandomWalk are
RootIndexed.ReserveLineages.capStoppedCandidate,
RootIndexed.ReserveLineages.capStoppedCandidate_zero,
RootIndexed.ReserveLineages.capStoppedCandidate_card_le_two_mul,
RootIndexed.capStoppedPopulationAt_selectedRoot_measurable,
RootIndexed.ReserveLineages.capStoppedCandidate_adapted,
RootIndexed.ReserveLineages.capStoppedCandidates_adapted,
RootIndexed.ReserveLineages.capStoppedCandidates_card_le, and
RootIndexed.ReserveLineages.serialCapStoppedReserveAndCandidatePopulation_card_le. Put
\(q_i(k,\omega)=\operatorname{firstChildRootAt}(i,k,\omega)\) and let
\(C_{i,k,a}(\omega)\) be the age-\(a\) cap-stopped descendant population
rooted at \(q_i(k,\omega)\). Then
\[
  C_{i,k,0}(\omega)=\{q_i(k,\omega)\}.
\]
If the growth selector is bounded by two and \(1\le c\), then
\[
  \#C_{i,k,a}(\omega)\le 2c.
\]
The map \(\omega\mapsto C_{i,k,a}(\omega)\) is measurable in the
generation-\((k+a)\) domain. For an enabled finite index set \(E_n(\omega)\),
the concurrent union has size at most \(\#E_n(\omega)\,2c\); if
\(\#E_n(\omega)\le1\) and the reserve has size at most one, the combined reserve-spine and candidate population has size at most \(1+2c\).
For any generation-measurable selected root $q(\omega)=(r(\omega),u(\omega))$
with $|u(\omega)|=s$, the public selected-root measurability theorem gives
measurability of the rooted cap-stopped population at generation $s+a$.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A pre-sampled reserve candidate, rooted at the first selected child of
the split completed at generation `start`.  Its definition is total for
every candidate index and every sample; earlier trial outcomes do not enter
the construction. -/
noncomputable def RootIndexed.ReserveLineages.capStoppedCandidate
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (r : Root) (i : Trial) (start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  rootedCapStoppedPopulation growthSelection cap ω
    (lineages.firstChildRootAt splitSelection r i start ω) age

@[simp] theorem RootIndexed.ReserveLineages.capStoppedCandidate_zero
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    lineages.capStoppedCandidate splitSelection growthSelection
      cap r i start 0 ω =
        {lineages.firstChildRootAt splitSelection r i start ω} := by
  simp [RootIndexed.ReserveLineages.capStoppedCandidate]

theorem RootIndexed.ReserveLineages.capStoppedCandidate_card_le_two_mul
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root) (i : Trial) (start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (lineages.capStoppedCandidate splitSelection growthSelection
      cap r i start age ω).card ≤ 2 * cap := by
  exact rootedCapStoppedPopulation_card_le_two_mul growthSelection cap hR hcap
    ω (lineages.firstChildRootAt splitSelection r i start ω) age

/-- A root chosen measurably at generation `start` gives a measurable
cap-stopped descendant population at global generation `start + age`. -/
theorem RootIndexed.capStoppedPopulationAt_selectedRoot_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap start age : ℕ)
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hchosen : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start] {ω | chosen ω = p})
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).2.length = start) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (fun ω => rootedCapStoppedPopulation R cap ω (chosen ω) age) := by
  classical
  let S : Set (Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hfixed (p : S) : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (fun ω => rootedCapStoppedPopulation R cap ω p.1 age) := by
    let subtree : RootIndexed.StepField Root α X → Mark α (Step α X) :=
      fun ω v => ω p.1.1 (p.1.2 ++ v)
    have hsubtree : @Measurable (RootIndexed.StepField Root α X)
        (Mark α (Step α X))
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
          (start + age))
        (generationFiltration (M := Step α X) age)
        subtree :=
      RootIndexed.fixedSubtree_measurable_at p.1 start age (by
        obtain ⟨ω, hω⟩ := p.2
        simpa [← hω] using hdepth ω)
    have hlocal := capStoppedPopulation_adapted R hR cap age
    let embed : Finset (TreeNode α) → Finset (RootIndexed.TreeNode Root α) :=
      fun s => s.map ⟨fun u => (p.1.1, p.1.2 ++ u), fun u v huv => by
        have htail : p.1.2 ++ u = p.1.2 ++ v := congrArg Prod.snd huv
        exact List.append_cancel_left htail⟩
    have hembed : Measurable embed := measurable_of_countable embed
    have hlocalMap : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (start + age)]
        (fun ω => capStoppedPopulation R cap age (subtree ω)) :=
      hlocal.comp hsubtree
    have hresult := hembed.comp hlocalMap
    convert hresult using 1
    funext ω
    simp [rootedCapStoppedPopulation, subtree, embed]
  intro t ht
  change MeasurableSet[RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) (start + age)]
      {ω | rootedCapStoppedPopulation R cap ω (chosen ω) age ∈ t}
  have heq : {ω | rootedCapStoppedPopulation R cap ω (chosen ω) age ∈ t} =
      ⋃ p : S, {ω | chosen ω = p.1} ∩
        {ω | rootedCapStoppedPopulation R cap ω p.1 age ∈ t} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, hω⟩
    · rintro ⟨p, hp, hω⟩
      simpa [hp] using hω
  rw [heq]
  apply MeasurableSet.iUnion
  intro p
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hfiber : MeasurableSet[F (start + age)] {ω | chosen ω = p.1} :=
    F.mono (Nat.le_add_right start age) _ (hchosen p.1)
  exact hfiber.inter ((hfixed p) ht)

/-- Every reserve candidate has an unconditional completion time `σᵢ`; the
candidate's rooted cap-stopped population is adapted at its global age.  The
look-ahead `τᵢ` is not used as a start time. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidate_adapted
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (cap : ℕ) (r : Root) :
    ∀ i k age, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (k + age)]
      (fun ω => lineages.capStoppedCandidate splitSelection growthSelection
        cap r i k age ω) := by
  intro i k age
  let chosen := lineages.firstChildRootAt splitSelection r i k
  have hchosen := lineages.firstChildRootAt_fiber_measurable
    splitSelection hsplit r i k
  have hcount : (Set.range chosen).Countable := by
    have hnode : (Set.range (fun ω => (chosen ω).2)).Countable :=
      Set.to_countable _
    apply (hnode.image fun u => (r, u)).mono
    rintro p ⟨ω, rfl⟩
    have hroot := lineages.firstChildRootAt_root
      splitSelection r i k ω
    have hp : (r, (chosen ω).2) = chosen ω := by
      apply Prod.ext
      · exact hroot.symm
      · rfl
    exact ⟨(chosen ω).2, ⟨ω, rfl⟩, hp⟩
  have hdepth : ∀ ω, (chosen ω).2.length = k := by
    intro ω
    exact lineages.firstChildRootAt_depth splitSelection r i k ω
  have hmeas := RootIndexed.capStoppedPopulationAt_selectedRoot_measurable
    growthSelection hgrowth cap k age chosen hchosen hcount hdepth
  simpa [chosen, RootIndexed.ReserveLineages.capStoppedCandidate,
    rootedCapStoppedPopulation] using hmeas

/-- The finite union of pre-sampled candidates is adapted when its enabled
index set is observable.  Candidate start times are their unconditional
stopping-time completions `σᵢ`. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidates_adapted
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root] [DecidableEq Trial]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hmark : MeasurableSet splitMark)
    (cap : ℕ) (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled
        (fun i => lineages.sigma splitMark r i)
        (fun i k age ω => lineages.capStoppedCandidate
          splitSelection growthSelection cap r i k age ω) n ω) := by
  have hcomponent : ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (ProbabilityTheory.Process.Stopping.Concurrent.Finite.component
        (fun i => lineages.sigma splitMark r i)
        (fun i k age ω => lineages.capStoppedCandidate
          splitSelection growthSelection cap r i k age ω) i n) := by
    intro i n
    exact (ProbabilityTheory.Process.Stopping.Concurrent.Finite.component_adapted
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (fun i => lineages.sigma splitMark r i)
      (fun i => lineages.sigma_isStoppingTime splitMark hmark r i)
      (fun i k age ω => lineages.capStoppedCandidate
        splitSelection growthSelection cap r i k age ω)
      (fun i k age => lineages.capStoppedCandidate_adapted
        splitSelection growthSelection hsplit hgrowth cap r i k age)
      i n)
  exact ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    enabled
    (fun i => lineages.sigma splitMark r i)
    (fun i k age ω => lineages.capStoppedCandidate
      splitSelection growthSelection cap r i k age ω)
    henabled henabledRange hcomponent

/-- The concurrent family of reserve candidates has at most twice the cap
per enabled candidate. The multiplier `2` comes from the selected rule's
two-child bound at its first crossing generation. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidates_card_le
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq Trial]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    (ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled
      (fun i => lineages.sigma (splitBy splitSelection) r i)
      (fun i k age ω => lineages.capStoppedCandidate splitSelection
        growthSelection cap r i k age ω) n ω).card ≤
      (enabled n ω).card * (2 * cap) := by
  apply ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_card_le_enabled_mul_candidateCap
    enabled
    (fun i => lineages.sigma (splitBy splitSelection) r i)
    (fun i k age ω => lineages.capStoppedCandidate splitSelection
      growthSelection cap r i k age ω)
    (2 * cap) n ω
  intro i k age
  exact lineages.capStoppedCandidate_card_le_two_mul splitSelection
    growthSelection cap hR hcap r i k age ω

/-- A serial restart schedule enables at most one capped candidate at a time.
Combining this with a one-particle reserve spine gives the reserve-and-candidate capacity
bound `1 + 2 * cap`; the theorem isolates the exact combinatorial input from
the schedule and branching arguments. -/
theorem RootIndexed.ReserveLineages.serialCapStoppedReserveAndCandidatePopulation_card_le
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq Trial]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (n : ℕ) (ω : RootIndexed.StepField Root α X)
    (reserve : Finset (RootIndexed.TreeNode Root α))
    (hreserve : reserve.card ≤ 1)
    (henabled : (enabled n ω).card ≤ 1) :
    (reserve ∪ ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled
      (fun i => lineages.sigma (splitBy splitSelection) r i)
      (fun i k age ω => lineages.capStoppedCandidate splitSelection
        growthSelection cap r i k age ω) n ω).card ≤ 1 + 2 * cap := by
  calc
    (reserve ∪ ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled
        (fun i => lineages.sigma (splitBy splitSelection) r i)
        (fun i k age ω => lineages.capStoppedCandidate splitSelection
          growthSelection cap r i k age ω) n ω).card ≤
        reserve.card + (ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled
          (fun i => lineages.sigma (splitBy splitSelection) r i)
          (fun i k age ω => lineages.capStoppedCandidate splitSelection
            growthSelection cap r i k age ω) n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (enabled n ω).card * (2 * cap) := by
      exact Nat.add_le_add hreserve
        (lineages.capStoppedCandidates_card_le splitSelection growthSelection
          cap hR hcap r enabled n ω)
    _ ≤ 1 + 1 * (2 * cap) := Nat.add_le_add_left
      (Nat.mul_le_mul_right (2 * cap) henabled) 1
    _ = 1 + 2 * cap := by simp

end ProbabilityTheory.BranchingRandomWalk

end
