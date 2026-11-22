/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Core
public import Probability.BranchingRandomWalk.Coupling.Slice
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
public import Combinatorics.BranchingWalk.Basic.BranchingWalk
public import Combinatorics.BranchingWalk.Selection.Coupling.PopulationCloud
public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step

/-!
# A recursively matched field for a selected branching walk

This file specializes the abstract rank-installed field to a coupling from a
selected branching walk to its first-`N` counterpart.  Both order keys are
computed from path positions.  At each stage, the selected population supplies
the particles and steps matched to the recursively constructed first-`N`
population.

## Public declarations

Write `F_n` for the recursively installed field at stage `n`, `P_n` for the
selected population, and `P_n^{(N)}` for the corresponding first-`N`
population. Installing the next generation preserves `P_n^{(N)}` and leaves
all positions through depth `n` unchanged:

\[\begin{aligned}
P_n^{(N)}(F_{n+1})&=P_n^{(N)}(F_n),\\
|q|\le n\quad&\Longrightarrow\quad
\operatorname{position}_{F_{n+1}}(q)=\operatorname{position}_{F_n}(q).
\end{aligned}\]

* `RootIndexed.initialPopulationSliceDominatingMap_of_subset` constructs an
  identity particle map from the initial cloud on `subsetBRWRoots` into that on
  `supersetBRWRoots` whenever `subsetBRWRoots ⊆ supersetBRWRoots`; both clouds may use
  different step fields because their particles have empty addresses.
* `RootIndexed.coupledField` recursively installs selected-population steps
  at equal-rank parents in the first-`N` population;
  `RootIndexed.coupledPopulation` reads that first-`N` population in the
  installed field.
* `RootIndexed.coupledPopulation_succ_stage` states that installation at stage
  `n+1` preserves the first-`N` population at generation `n`.
* `RootIndexed.coupledField_position_succ_of_depth_le` states that positions
  at address depth at most `n` are unchanged from stage `n` to `n+1`.
* `RootIndexed.coupledField_succ_apply_matchByRankOrSelf` identifies the
  installed step at an equal-rank first-`N` parent with the corresponding
  selected-population step.
* `RootIndexed.coupledInjection` constructs a slice-dominating injection from
  the selected population into the first-`N` population at every stage, using
  the initial injection, offspring inclusion, and capacity hypotheses.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection
open Combinatorics.Branching.Selection
open _root_.Combinatorics.Selection.NSelection

variable {Ω Root α Mark Position Value : Type*}

/-- If `subsetBRWRoots ⊆ supersetBRWRoots`, the initial subset-root BRW cloud embeds into the
superset-root BRW cloud by the identity on root particles. The superset-root and subset-root step
fields may differ because every initial particle has the empty address, so
both position maps equal the prescribed initial position there. -/
noncomputable def RootIndexed.initialPopulationSliceDominatingMap_of_subset
    {Root α Mark Position Value : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (initial : Root → Position)
    (subsetBRWRoots supersetBRWRoots : Finset Root)
    (hroots : subsetBRWRoots ⊆ supersetBRWRoots)
    (subsetBRWField supersetBRWField : RootIndexed.StepField Root α Mark) :
    Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial subsetBRWField)
        (RootIndexed.initialPopulation (α := α) subsetBRWRoots))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial supersetBRWField)
        (RootIndexed.initialPopulation (α := α) supersetBRWRoots)) () := by
  refine {
    toFun := id
    mapsTo := ?_
    injOn := Set.injOn_id _
    dominates := ?_ }
  · intro p hp
    change p ∈ RootIndexed.initialPopulation (α := α) supersetBRWRoots
    change p ∈ RootIndexed.initialPopulation (α := α) subsetBRWRoots at hp
    rw [RootIndexed.mem_initialPopulation_iff] at hp ⊢
    rcases hp with ⟨r, hr, rfl⟩
    exact ⟨r, hroots hr, rfl⟩
  · intro p hp
    change φ (RootIndexed.position initial d supersetBRWField p.1 p.2) ≤
      φ (RootIndexed.position initial d subsetBRWField p.1 p.2)
    obtain ⟨r, _, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hp
    simp [RootIndexed.position]

/-- The field obtained by installing each selected-population step at the
first-`N` particle of the same spatial rank, one generation at a time. -/
noncomputable def RootIndexed.coupledField
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α)) :
    ℕ → Ω → RootIndexed.StepField Root α Mark :=
  BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField
    (fun _ ω p => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) (selectedBRWStepField ω)).position d p.1 p.2))
    (fun _ ω β p => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) β).position d p.1 p.2))
    selectedBRWPopulation
    (fun n ω β => RootIndexed.selectedPopulation
      N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω) n β)
    selectedBRWStepField nSelectedBRWFallbackStepField

/-- The first-`N` population at a finite recursive coupling stage. -/
noncomputable def RootIndexed.coupledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) : Finset (RootIndexed.TreeNode Root α) :=
  RootIndexed.selectedPopulation N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω) n
    (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
      selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω)

/-- Installing the current matched steps leaves the current first-`N`
population unchanged. -/
theorem RootIndexed.coupledPopulation_succ_stage
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) :
    RootIndexed.selectedPopulation N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω) n
        (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
          selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation (n + 1) ω) =
      RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω := by
  exact BranchingRandomWalk.Coupling.RootIndexed.selectedPopulation_rankInstalledField_succ
    N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω) _ _ _ _ selectedBRWStepField nSelectedBRWFallbackStepField n ω

/-- The successor installation changes no spatial position through the parent
generation at which it is installed. -/
theorem RootIndexed.coupledField_position_succ_of_depth_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) (q : RootIndexed.TreeNode Root α)
    (hq : q.2.length ≤ n) :
    (RootIndexed.BranchingWalk.ofStepField (initial ω)
      (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField
        selectedBRWPopulation (n + 1) ω)).position d q.1 q.2 =
      (RootIndexed.BranchingWalk.ofStepField (initial ω)
        (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField
          selectedBRWPopulation n ω)).position d q.1 q.2 := by
  rw [RootIndexed.coupledField,
    BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_succ]
  exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
    d n (initial ω) _ _ q.1 q.2 hq

/-- At the successor stage, the step at an equal-rank first-`N` parent is the
corresponding selected-population step. -/
theorem RootIndexed.coupledField_succ_apply_matchByRankOrSelf
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω)
    (hselectedBRWPopulationCard_le_nSelectedBRWPopulation : (selectedBRWPopulation n ω).card ≤
      (RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω).card)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ selectedBRWPopulation n ω) :
    let selectedBRWPopulationOrderKey := fun q => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) (selectedBRWStepField ω)).position d q.1 q.2)
    let nSelectedBRWPopulationPriorField := RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
      selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω
    let nSelectedBRWPopulationOrderKey := fun q => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) nSelectedBRWPopulationPriorField).position d q.1 q.2)
    let q := matchByRankOrSelf selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
      (selectedBRWPopulation n ω)
      (RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω) hselectedBRWPopulationCard_le_nSelectedBRWPopulation p
    RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField
        selectedBRWPopulation (n + 1) ω q.1 q.2 =
      selectedBRWStepField ω p.1 p.2 := by
  dsimp only
  apply BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_succ_apply_matchByRankOrSelf
  · intro q hq
    exact RootIndexed.selectedPopulation_depth N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω)
      n (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω) q hq
  · exact hp

/-- The recursive equal-rank installation couples a capacity-bounded selected
population to the first-`N` population at every stage.  Child-slot sets remain
arbitrary sets; no countability of roots or slots is used. -/
noncomputable def RootIndexed.coupledInjection
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (nSelectedBRWRoots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hnSelectedBRWPopulationAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (selectedBRWStepField nSelectedBRWFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (selectedBRWPopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (selectedBRWPopulationChildSlots : ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (selectedBRWPopulationToNSelectedBRWPopulationInitialInjection : ∀ ω, Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (selectedBRWStepField ω))
        (selectedBRWPopulation 0 ω))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (nSelectedBRWFallbackStepField ω))
        (RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
          nSelectedBRWFallbackStepField selectedBRWPopulation 0 ω)) ())
    (hselectedBRWPopulationChildren_subset_offspring : ∀ n ω, ↑(selectedBRWPopulation (n + 1) ω) ⊆
      Combinatorics.Branching.Population.offspringAddressSet
        (↑(selectedBRWPopulation n ω)) (selectedBRWPopulationChildSlots n ω))
    (hselectedBRWPopulationChildSlots_subset_survival : ∀ n ω p, p ∈ selectedBRWPopulation n ω →
      selectedBRWPopulationChildSlots n ω p ⊆ {i | survive (selectedBRWStepField ω p.1 p.2) i})
    (hBRWOrderKeyTranslation_mono : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω)
    (hselectedBRWPopulationCard_le_N : ∀ k < n, (selectedBRWPopulation (k + 1) ω).card ≤ N) :
    Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (selectedBRWStepField ω))
        (selectedBRWPopulation n ω))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω)
          (RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
            nSelectedBRWFallbackStepField selectedBRWPopulation n ω))
        (RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
          nSelectedBRWFallbackStepField selectedBRWPopulation n ω)) () := by
  induction n with
  | zero =>
      simpa [RootIndexed.coupledField] using selectedBRWPopulationToNSelectedBRWPopulationInitialInjection ω
  | succ n ih =>
      have ih := ih (fun k hk => hselectedBRWPopulationCard_le_N k (Nat.lt_succ_of_lt hk))
      let selectedBRW := RootIndexed.BranchingWalk.ofStepField (initial ω)
        (selectedBRWStepField ω)
      let priorField := RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω
      let nextField := RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy
        selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation (n + 1) ω
      let nSelectedBRWPopulationParents := RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ
        hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω
      let canonical := Combinatorics.Branching.Selection.Coupling.canonicalInjection
        φ d selectedBRW (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
        (selectedBRWPopulation n ω) nSelectedBRWPopulationParents ih
      let hparents : Cloud.SliceDominatingMap φ
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            selectedBRW (selectedBRWPopulation n ω))
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            (RootIndexed.BranchingWalk.ofStepField (initial ω) nextField)
            nSelectedBRWPopulationParents) () := {
        toFun := canonical
        mapsTo := canonical.mapsTo
        injOn := canonical.injOn
        dominates := by
          intro p hp
          change φ ((RootIndexed.BranchingWalk.ofStepField (initial ω) nextField).position
              d (canonical p).1 (canonical p).2) ≤
            φ (selectedBRW.position d p.1 p.2)
          rw [RootIndexed.coupledField_position_succ_of_depth_le N nSelectedBRWRoots initial
            d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω (canonical p)]
          · exact canonical.dominates p hp
          · apply Nat.le_of_eq
            apply RootIndexed.selectedPopulation_depth N nSelectedBRWRoots (initial ω) d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω)
              n priorField (canonical p)
            simpa [nSelectedBRWPopulationParents, RootIndexed.coupledPopulation,
              Combinatorics.Branching.Selection.Coupling.populationCloud]
              using canonical.mapsTo hp }
      have hparents_apply (p : RootIndexed.TreeNode Root α) :
          hparents p = canonical p := rfl
      refine Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
          φ d N selectedBRW
          (RootIndexed.BranchingWalk.ofStepField (initial ω) nextField)
          (selectedBRWPopulation n ω) nSelectedBRWPopulationParents
          (selectedBRWPopulationChildSlots n ω)
          (fun q => {i | survive (nextField q.1 q.2) i})
          (selectedBRWPopulation (n + 1) ω)
          (RootIndexed.coupledPopulation N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
            nSelectedBRWFallbackStepField selectedBRWPopulation (n + 1) ω)
          (hselectedBRWPopulationChildren_subset_offspring n ω) (hselectedBRWPopulationCard_le_N n (Nat.lt_succ_self n))
          ?_ hparents ?_ ?_ hBRWOrderKeyTranslation_mono
      · simpa [RootIndexed.coupledPopulation, nSelectedBRWPopulationParents, nextField,
          RootIndexed.coupledPopulation_succ_stage
          N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω]
          using RootIndexed.selectedPopulation_succ_spec_position N nSelectedBRWRoots (initial ω)
            d φ (hnSelectedBRWPopulationAdmitsFirstNBy ω) n nextField
      · intro p hp i hi
        have his := hselectedBRWPopulationChildSlots_subset_survival n ω p
          (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
            using hp) hi
        have hstep : nextField (canonical p).1 (canonical p).2 =
            selectedBRWStepField ω p.1 p.2 := by
          change RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
            nSelectedBRWFallbackStepField selectedBRWPopulation (n + 1) ω
              (canonical p).1 (canonical p).2 = selectedBRWStepField ω p.1 p.2
          rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
          exact RootIndexed.coupledField_succ_apply_matchByRankOrSelf N nSelectedBRWRoots
            initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω
            (Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
                φ d selectedBRW
                (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
                (selectedBRWPopulation n ω) nSelectedBRWPopulationParents ih)
            (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
              using hp)
        have hstep' : nextField (hparents p).1 (hparents p).2 =
            selectedBRWStepField ω p.1 p.2 := by simpa [hparents_apply] using hstep
        simpa [hstep'] using his
      · intro p hp i hi
        have hstep : nextField (canonical p).1 (canonical p).2 =
            selectedBRWStepField ω p.1 p.2 := by
          change RootIndexed.coupledField N nSelectedBRWRoots initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField
              nSelectedBRWFallbackStepField selectedBRWPopulation (n + 1) ω
                (canonical p).1 (canonical p).2 = selectedBRWStepField ω p.1 p.2
          rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
          exact RootIndexed.coupledField_succ_apply_matchByRankOrSelf N nSelectedBRWRoots
            initial d φ hnSelectedBRWPopulationAdmitsFirstNBy selectedBRWStepField nSelectedBRWFallbackStepField selectedBRWPopulation n ω
            (Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
                φ d selectedBRW
                (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
                (selectedBRWPopulation n ω) nSelectedBRWPopulationParents ih)
            (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
              using hp)
        have hstep' : nextField (hparents p).1 (hparents p).2 =
            selectedBRWStepField ω p.1 p.2 := by simpa [hparents_apply] using hstep
        simp [selectedBRW, hstep']

end ProbabilityTheory.BranchingRandomWalk.Coupling
