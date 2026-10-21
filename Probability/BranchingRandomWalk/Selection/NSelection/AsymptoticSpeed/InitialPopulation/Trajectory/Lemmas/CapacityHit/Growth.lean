/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Address
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Nonempty
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Population
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Lemmas.CapacityHit.Mark

/-!
# Cardinality growth of the selected population

The proof-chain results are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialFirstN_card_ge`:
  if each particle in the generation-$n$ population has a child, then the
  next selected population has cardinality at least that of the current one.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialFirstN_card_gt_of_split`:
  while the population has fewer than $N$ particles, a split at the selected
  active address makes the next selected population strictly larger.

Both statements are specific to the root-indexed $N$-selection capacity proof.

-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.UlamHarris
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingProcess.Offspring

attribute [local instance] Classical.propDecidable Classical.decEq

private noncomputable def smallInitialOneChildSlot
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i)
    (p : {p // p ∈ parents}) : ℕ :=
  Classical.choose (hchildren p.1 p.2)

private lemma smallInitialOneChildSlot_survives
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i)
    (p : {p // p ∈ parents}) :
    survive (field p.1.1 p.1.2)
      (smallInitialOneChildSlot parents field hchildren p) := by
  exact Classical.choose_spec (hchildren p.1 p.2)

private noncomputable def smallInitialOneChildImage
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
  parents.attach.image (fun p =>
    Combinatorics.Branching.Selection.Coupling.childAddress p.1
      (smallInitialOneChildSlot parents field hchildren p))

private lemma smallInitialOneChildImage_injective
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i) :
    Function.Injective (fun p : {p // p ∈ parents} =>
      Combinatorics.Branching.Selection.Coupling.childAddress p.1
        (smallInitialOneChildSlot parents field hchildren p)) := by
  intro p q hpq
  have hpair : (p.1, smallInitialOneChildSlot parents field hchildren p) =
      (q.1, smallInitialOneChildSlot parents field hchildren q) :=
    Combinatorics.Branching.Selection.Coupling.childAddress_joint_injective
      (by simpa using hpq)
  apply Subtype.ext
  exact congrArg Prod.fst hpair

private lemma smallInitialOneChildImage_card
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i) :
    (smallInitialOneChildImage parents field hchildren).card = parents.card := by
  classical
  simp [smallInitialOneChildImage,
    Finset.card_image_of_injective _
      (smallInitialOneChildImage_injective parents field hchildren)]

private lemma smallInitialOneChildImage_subset
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hdepth : ∀ p ∈ parents, p.2.length = n)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i) :
    ↑(smallInitialOneChildImage parents field hchildren) ⊆
      RootIndexed.childrenAtGeneration n parents field := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact RootIndexed.childAddress_mem_childrenAtGeneration n parents field
    p.1 p.2 (hdepth p.1 p.2) (smallInitialOneChildSlot parents field
      hchildren p) (smallInitialOneChildSlot_survives parents field hchildren p)

lemma smallInitialFirstN_card_ge
    (N n : ℕ) (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (value : RootIndexed.TreeNode (Fin m) ℕ → ℝ)
    (selected : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hfirst : IsFirstNBy N value
      (RootIndexed.childrenAtGeneration n parents field) selected)
    (hdepth : ∀ p ∈ parents, p.2.length = n)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i)
    (hcapacity : parents.card ≤ N) :
    parents.card ≤ selected.card := by
  let base := smallInitialOneChildImage parents field hchildren
  have hbaseSubset : (base : Set (RootIndexed.TreeNode (Fin m) ℕ)) ⊆
      RootIndexed.childrenAtGeneration n parents field := by
    simpa [base] using smallInitialOneChildImage_subset n parents field
      hdepth hchildren
  rcases (RootIndexed.childrenAtGeneration n parents field).finite_or_infinite with
    hfinite | hinfinite
  · have hbaseCard : base.card ≤ hfinite.toFinset.card :=
      Finset.card_le_card (fun q hq =>
        hfinite.mem_toFinset.mpr (hbaseSubset hq))
    have hcard := smallInitialOneChildImage_card parents field hchildren
    rw [hfirst.card_finite hfinite]
    exact le_min hcapacity (by
      calc
        parents.card = base.card := hcard.symm
        _ ≤ hfinite.toFinset.card := hbaseCard)
  · rw [hfirst.card_infinite hinfinite]
    exact hcapacity

lemma smallInitialFirstN_card_gt_of_split
    (N n : ℕ) (hm : 0 < m)
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (value : RootIndexed.TreeNode (Fin m) ℕ → ℝ)
    (selected : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hfirst : IsFirstNBy N value
      (RootIndexed.childrenAtGeneration n parents field) selected)
    (hdepth : ∀ p ∈ parents, p.2.length = n)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i)
    (hchosen : smallInitialActiveAddress m N n hm field ∈ parents)
    (hsplit : 2 ≤ Step.childCount
      (field (smallInitialActiveAddress m N n hm field).1
        (smallInitialActiveAddress m N n hm field).2))
    (hcapacity : parents.card < N) :
    parents.card < selected.card := by
  classical
  let chosen := smallInitialActiveAddress m N n hm field
  have hsplitSet : field chosen.1 chosen.2 ∈ offspringSplitSet := hsplit
  rw [offspringSplitSet_eq_nontrivialSupport] at hsplitSet
  change ∃ i j, i ≠ j ∧ survive (field chosen.1 chosen.2) i ∧
    survive (field chosen.1 chosen.2) j at hsplitSet
  obtain ⟨i, j, hij, hi, hj⟩ := hsplitSet
  let hchildren' := hchildren
  let base := smallInitialOneChildImage parents field hchildren'
  let chosenAttached : {p // p ∈ parents} := ⟨chosen, hchosen⟩
  let chosenSlot := smallInitialOneChildSlot parents field hchildren' chosenAttached
  let extraSlot := if chosenSlot = i then j else i
  let extra := Combinatorics.Branching.Selection.Coupling.childAddress
    chosen extraSlot
  have hextraSurvives : survive (field chosen.1 chosen.2) extraSlot := by
    by_cases hslot : chosenSlot = i
    · simp [extraSlot, hslot]
      exact hj
    · simp [extraSlot, hslot]
      exact hi
  have hextraNe : extraSlot ≠ chosenSlot := by
    dsimp [extraSlot]
    by_cases hslot : chosenSlot = i
    · simp only [ite_eq_left hslot]
      intro heq
      exact hij (hslot.symm.trans heq.symm)
    · simp only [ite_eq_right hslot]
      intro heq
      exact hslot heq.symm
  have hbaseSubset : (base : Set (RootIndexed.TreeNode (Fin m) ℕ)) ⊆
      RootIndexed.childrenAtGeneration n parents field := by
    simpa [base] using smallInitialOneChildImage_subset n parents field
      hdepth hchildren'
  have hextraMem : extra ∈ RootIndexed.childrenAtGeneration n parents field := by
    exact RootIndexed.childAddress_mem_childrenAtGeneration n parents field
      chosen hchosen (hdepth chosen hchosen) extraSlot hextraSurvives
  have hextraNotBase : extra ∉ base := by
    intro hmem
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
    have hpair : (p.1,
        smallInitialOneChildSlot parents field hchildren' p) =
        (chosen, extraSlot) :=
      Combinatorics.Branching.Selection.Coupling.childAddress_joint_injective
        (by simpa [extra, smallInitialOneChildImage] using heq)
    have hparent : p.1 = chosen := congrArg Prod.fst hpair
    have hslot : smallInitialOneChildSlot parents field hchildren' p =
        extraSlot := congrArg Prod.snd hpair
    have hchosenSlot : smallInitialOneChildSlot parents field hchildren'
        chosenAttached = chosenSlot := rfl
    have hpEq : p = chosenAttached := Subtype.ext hparent
    subst p
    exact hextraNe (hslot.symm.trans hchosenSlot)
  let large := base ∪ {extra}
  have hlargeSubset : (large : Set (RootIndexed.TreeNode (Fin m) ℕ)) ⊆
      RootIndexed.childrenAtGeneration n parents field := by
    intro q hq
    rcases Finset.mem_union.mp hq with hbase | hextra
    · exact hbaseSubset hbase
    · have : q = extra := Finset.mem_singleton.mp hextra
      subst q
      exact hextraMem
  have hbaseCard := smallInitialOneChildImage_card parents field hchildren'
  have hdisjoint : Disjoint base ({extra} : Finset (RootIndexed.TreeNode (Fin m) ℕ)) :=
    Finset.disjoint_singleton_right.mpr hextraNotBase
  have hlargeCard : large.card = parents.card + 1 := by
    dsimp [large]
    rw [Finset.card_union_of_disjoint hdisjoint,
      Finset.card_singleton, hbaseCard]
  rcases (RootIndexed.childrenAtGeneration n parents field).finite_or_infinite with
    hfinite | hinfinite
  · have hlargeCardLe : large.card ≤ hfinite.toFinset.card :=
      Finset.card_le_card (fun q hq =>
        hfinite.mem_toFinset.mpr (hlargeSubset hq))
    have hcandidateCard : parents.card + 1 ≤ hfinite.toFinset.card := by
      rw [← hlargeCard]
      exact hlargeCardLe
    rw [hfirst.card_finite hfinite]
    omega
  · rw [hfirst.card_infinite hinfinite]
    omega


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
