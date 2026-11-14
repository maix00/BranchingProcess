/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.Coupling.SelectedPopulation
public import Probability.BranchingRandomWalk.Coupling.Field.Position
public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed

/-!
# Coupling `selectedBranchingWalk` to `nSelectedBranchingWalk`

The single-root process `selectedBranchingWalk` is coupled to the
multi-root process `nSelectedBranchingWalk`. They may use different step
fields on the same sample; their relation is specified by selected-slot
inclusion and equality of the corresponding mapped increments.

For a fixed root \(\texttt{selectedBranchingWalkRoot}\), let
\[
  P^{\mathrm{sel}}_{n,\omega}
    := \operatorname{labelledPopulation}
      \bigl(\texttt{selectedBranchingWalkSelectionRule},n,
        \texttt{selectedBranchingWalkStepField}(\omega),
        \texttt{selectedBranchingWalkRoot}\bigr),
  \qquad
  P^N_{n,\omega}
    := \operatorname{selectedPopulation}
      \bigl(N,\texttt{nSelectedBranchingWalkRoots},\texttt{initial},d,\varphi,
        \texttt{nSelectedBranchingWalkAdmitsFirstNBy},n,\omega\bigr).
\]
The corresponding spatial clouds are
\[
  C^{\mathrm{sel}}_{n,\omega}
    :=\operatorname{populationCloud}\,d\,
      \bigl(\operatorname{ofStepField}
        (\texttt{initial},\texttt{selectedBranchingWalkStepField}(\omega))\bigr)
      \,P^{\mathrm{sel}}_{n,\omega},
  \qquad
  C^N_{n,\omega}
    :=\operatorname{populationCloud}\,d\,
      \bigl(\operatorname{ofStepField}(\texttt{initial},\omega)\bigr)
      \,P^N_{n,\omega}.
\]
Under the selected-slot, increment, and capacity hypotheses, the coupling
gives
\[
  \forall n,\omega,\qquad
  C^{\mathrm{sel}}_{n,\omega}\preceq_{\varphi} C^N_{n,\omega},
\]
where \(C\preceq_{\varphi}D\) means
\(\texttt{Cloud.InjectivelyDominatesBy }\varphi\,C\,D\,()\).

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.RootIndexed.coupledInjection_labelledPopulation`:
  for finite `selectedBranchingWalkRoots ⊆ nSelectedBranchingWalkRoots`,
  constructs the equal-rank slice injection from the labelled
  `selectedBranchingWalk` population to `nSelectedBranchingWalk`.
- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.generationInjection_labelledPopulation`:
  constructs a canonical single-root slice injection at a fixed generation.
- `ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.injectivelyDominatesBy_labelledPopulation`:
  if each labelled `selectedBranchingWalk` population has size at most $N$,
  the parents paired by `nSelectedBranchingWalkParentMatching` share selected
  slots and mapped increments, and $φ$ preserves order under common
  translations, then its cloud is injectively dominated by the
  `nSelectedBranchingWalk` cloud at every generation.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling

variable {Root α Mark Position OrderKey : Type*}

/-- Couple `selectedBranchingWalk` particles from a finite set of roots to the
causal `nSelectedBranchingWalk` population. The latter field is built by
equal-rank step installation, which gives selected-slot inclusion and
increment agreement. Only the root sets are finite; the ambient root and slot
types need no countability assumptions. -/
noncomputable def RootIndexed.coupledInjection_labelledPopulation
    {Ω : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    [AddCommMonoid Position]
    (N : ℕ) (selectedBranchingWalkSelectionRule : Step.FiniteSelection α Mark)
    (selectedBranchingWalkRoots nSelectedBranchingWalkRoots : Finset Root) (hroots : selectedBranchingWalkRoots ⊆ nSelectedBranchingWalkRoots)
    (initial : Ω → Root → Position) (d : Mark → Position) (φ : Position → OrderKey)
    (nSelectedBranchingWalkAdmitsFirstNBy : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α)),
      Combinatorics.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n nSelectedBranchingWalkParents β))
    (selectedBranchingWalkStepField nSelectedBranchingWalkFallbackStepField : Ω → RootIndexed.StepField Root α Mark)
    (hcard : ∀ n ω,
      (RootIndexed.StepSelection.labelledPopulationOn
        selectedBranchingWalkSelectionRule selectedBranchingWalkRoots n (selectedBranchingWalkStepField ω)).card ≤ N)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (selectedBranchingWalkStepField ω))
        (RootIndexed.StepSelection.labelledPopulationOn
          selectedBranchingWalkSelectionRule selectedBranchingWalkRoots n (selectedBranchingWalkStepField ω)))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω)
          (RootIndexed.coupledField N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy selectedBranchingWalkStepField
            nSelectedBranchingWalkFallbackStepField
            (fun k sample => RootIndexed.StepSelection.labelledPopulationOn
              selectedBranchingWalkSelectionRule selectedBranchingWalkRoots k (selectedBranchingWalkStepField sample)) n ω))
        (RootIndexed.coupledPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy
          selectedBranchingWalkStepField nSelectedBranchingWalkFallbackStepField
          (fun k sample => RootIndexed.StepSelection.labelledPopulationOn
            selectedBranchingWalkSelectionRule selectedBranchingWalkRoots k (selectedBranchingWalkStepField sample)) n ω)) () := by
  apply RootIndexed.coupledInjection N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy
    selectedBranchingWalkStepField nSelectedBranchingWalkFallbackStepField
    (fun k sample => RootIndexed.StepSelection.labelledPopulationOn
      selectedBranchingWalkSelectionRule selectedBranchingWalkRoots k (selectedBranchingWalkStepField sample))
    (fun _ sample p => ↑(selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField sample p.1 p.2)))
  · intro sample
    refine ⟨id, ?_, Set.injOn_id _, ?_⟩
    · intro p hp
      obtain ⟨selectedBranchingWalkRoot, hselectedBranchingWalkRoot, hroot, hpopulation⟩ :=
        (RootIndexed.StepSelection.mem_labelledPopulationOn
          selectedBranchingWalkSelectionRule selectedBranchingWalkRoots 0 (selectedBranchingWalkStepField sample) p).mp hp
      have hp' : p = (selectedBranchingWalkRoot, []) := by
        apply Prod.ext
        · exact hroot
        · simpa using hpopulation
      subst p
      change (selectedBranchingWalkRoot, []) ∈ RootIndexed.initialPopulation (α := α) nSelectedBranchingWalkRoots
      rw [RootIndexed.initialPopulation, Finset.mem_map]
      exact ⟨selectedBranchingWalkRoot, hroots hselectedBranchingWalkRoot, rfl⟩
    · intro p hp
      obtain ⟨selectedBranchingWalkRoot, _, hroot, hpopulation⟩ :=
        (RootIndexed.StepSelection.mem_labelledPopulationOn
          selectedBranchingWalkSelectionRule selectedBranchingWalkRoots 0 (selectedBranchingWalkStepField sample) p).mp hp
      have hp' : p = (selectedBranchingWalkRoot, []) := by
        apply Prod.ext
        · exact hroot
        · simpa using hpopulation
      subst p
      simp only [id_eq]
      change φ (RootIndexed.position (initial sample) d (nSelectedBranchingWalkFallbackStepField sample) selectedBranchingWalkRoot []) ≤
        φ (RootIndexed.position (initial sample) d (selectedBranchingWalkStepField sample) selectedBranchingWalkRoot [])
      simp
  · intro k sample
    exact RootIndexed.StepSelection.labelledPopulationOn_succ_subset
      selectedBranchingWalkSelectionRule selectedBranchingWalkRoots k (selectedBranchingWalkStepField sample)
  · intro k sample p hp i hi
    exact selectedBranchingWalkSelectionRule.subset_support (selectedBranchingWalkStepField sample p.1 p.2) i hi
  · exact htranslate
  · exact fun k _ => hcard (k + 1) ω

/-- Data-valued canonical coupling of the labelled
`selectedBranchingWalk` trial to `nSelectedBranchingWalk`. At generation zero
the labelled root is included by identity; every successor map is the
canonical equal-rank map. -/
noncomputable def generationInjection_labelledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    [AddCommMonoid Position]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalkSelectionRule : Step.FiniteSelection α Mark)
    (nSelectedBranchingWalkRoots : Finset Root) (selectedBranchingWalkRoot : Root) (hselectedBranchingWalkRoot : selectedBranchingWalkRoot ∈ nSelectedBranchingWalkRoots)
    (initial : Root → Position)
    (selectedBranchingWalkStepField : RootIndexed.StepField Root α Mark →
      RootIndexed.StepField Root α Mark)
    (nSelectedBranchingWalkAdmitsFirstNBy : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α)),
      Combinatorics.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n nSelectedBranchingWalkParents ω))
    (hcard : ∀ n ω,
      (RootIndexed.StepSelection.labelledPopulation
        selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot).card ≤ N)
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
          (RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot))
        (populationCloud d (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot,
        ↑(selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField ω p.1 p.2)) ⊆
          {i | survive (ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2) i})
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
          (RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot))
        (populationCloud d (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot,
      ∀ i ∈ selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField ω p.1 p.2),
        value' ((ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' ((selectedBranchingWalkStepField ω p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark) :
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
        (RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation
          N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) () :=
  generationInjection_selectedPopulation φ d N nSelectedBranchingWalkRoots initial
    (fun sample => RootIndexed.BranchingWalk.ofStepField
      initial (selectedBranchingWalkStepField sample))
    (fun k sample => RootIndexed.StepSelection.labelledPopulation
      selectedBranchingWalkSelectionRule k (selectedBranchingWalkStepField sample) selectedBranchingWalkRoot)
    (fun _ sample p => ↑(selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField sample p.1 p.2))) nSelectedBranchingWalkAdmitsFirstNBy
    (fun sample =>
      { toFun := id
        mapsTo := by
          intro p hp
          have hp' : p = (selectedBranchingWalkRoot, []) := by simpa using hp
          subst p
          change (selectedBranchingWalkRoot, []) ∈ RootIndexed.initialPopulation (α := α) nSelectedBranchingWalkRoots
          rw [RootIndexed.initialPopulation, Finset.mem_map]
          exact ⟨selectedBranchingWalkRoot, hselectedBranchingWalkRoot, rfl⟩
        injOn := Set.injOn_id _
        dominates := by
          intro p hp
          have hp' : p = (selectedBranchingWalkRoot, []) := by simpa using hp
          subst p
          change φ (RootIndexed.position initial d sample selectedBranchingWalkRoot []) ≤
            φ (RootIndexed.position initial d (selectedBranchingWalkStepField sample) selectedBranchingWalkRoot [])
          simp })
    (fun k sample =>
      RootIndexed.StepSelection.labelledPopulation_succ_subset
        selectedBranchingWalkSelectionRule k (selectedBranchingWalkStepField sample) selectedBranchingWalkRoot)
    (fun k sample => hcard (k + 1) sample)
    hslots hsharedIncrement htranslate n ω

/-- A capacity-bounded single-root `selectedBranchingWalk` population is
dominated by `nSelectedBranchingWalk` whenever the parents paired by
`nSelectedBranchingWalkParentMatching` share every selected slot and its
displacement. No offspring law, countability, or address ordering is assumed. -/
theorem injectivelyDominatesBy_labelledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder OrderKey]
    [AddCommMonoid Position]
    (φ : Position → OrderKey) (d : Mark → Position) (N : ℕ)
    (selectedBranchingWalkSelectionRule : Step.FiniteSelection α Mark)
    (nSelectedBranchingWalkRoots : Finset Root) (selectedBranchingWalkRoot : Root) (hselectedBranchingWalkRoot : selectedBranchingWalkRoot ∈ nSelectedBranchingWalkRoots)
    (initial : Root → Position)
    (selectedBranchingWalkStepField : RootIndexed.StepField Root α Mark →
      RootIndexed.StepField Root α Mark)
    (nSelectedBranchingWalkAdmitsFirstNBy : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (nSelectedBranchingWalkParents : Finset (RootIndexed.TreeNode Root α)),
      Combinatorics.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (Combinatorics.Branching.Population.childrenAtGeneration n nSelectedBranchingWalkParents ω))
    (hcard : ∀ n ω,
      (RootIndexed.StepSelection.labelledPopulation
        selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot).card ≤ N)
    (hslots : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
          (RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot))
        (populationCloud d (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot,
        ↑(selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField ω p.1 p.2)) ⊆
          {i | survive (ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2) i})
    (hsharedIncrement : ∀ n ω (nSelectedBranchingWalkParentMatching : Cloud.SliceDominatingMap φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
          (RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot))
        (populationCloud d (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) ()),
      ∀ p ∈ RootIndexed.StepSelection.labelledPopulation selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot,
      ∀ i ∈ selectedBranchingWalkSelectionRule (selectedBranchingWalkStepField ω p.1 p.2),
        value' ((ω (nSelectedBranchingWalkParentMatching p).1 (nSelectedBranchingWalkParentMatching p).2).map d) i =
          value' ((selectedBranchingWalkStepField ω p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial (selectedBranchingWalkStepField ω))
        (RootIndexed.StepSelection.labelledPopulation
          selectedBranchingWalkSelectionRule n (selectedBranchingWalkStepField ω) selectedBranchingWalkRoot)).InjectivelyDominatesBy φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial ω)
        (RootIndexed.selectedPopulation
          N nSelectedBranchingWalkRoots initial d φ nSelectedBranchingWalkAdmitsFirstNBy n ω)) () := by
  intro n ω
  exact (generationInjection_labelledPopulation φ d N selectedBranchingWalkSelectionRule nSelectedBranchingWalkRoots selectedBranchingWalkRoot hselectedBranchingWalkRoot initial
    selectedBranchingWalkStepField nSelectedBranchingWalkAdmitsFirstNBy hcard hslots hsharedIncrement htranslate n ω).injectivelyDominatesBy

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

end
