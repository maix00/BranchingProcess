/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.BoundedOffspring
public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtreeVector
import Probability.Independence.ConditionalIntegral
import all Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlot.Lemmas.Coding

/-!
# Finite-slot offspring process coupled to a selected population

For a selector `S` with `|(S ξ)| ≤ 2`, let `Aₙ(ω)` be the set of surviving
binary addresses of length `n` in the coded tree, and let `Lₙ(ω)` be the row of
finite-slot offspring configurations at those addresses.

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels` defines
  `Aₙ(ω) = {u : Fin n → Fin 2 | u survives in the coded tree}`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels_card_eq_population_card`
  proves `|Aₙ(ω)| = |Zₙ(ω)|`, where `Zₙ` is the selected population.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels_measurable`
  proves that `ω ↦ Aₙ(ω)` is measurable with respect to the generation field
  `𝓕ₙ`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotLevelSteps` defines the
  offspring row `Lₙ(ω)(u)` by reading the selected offspring at the source
  vertex coded by `u`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels_card_succ_eq_sum`
  proves the population recursion
  `|Aₙ₊₁(ω)| = ∑_{u ∈ Aₙ(ω)} childCount(Lₙ(ω)(u))`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotRowCountSum` defines
  `Rₙ(A,L) = ∑_{u : Fin n → Fin 2} 1_{u ∈ A} childCount(L(u))`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotRowCountSum_measurable`
  proves measurability of `Rₙ`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotRowCountSum_eq_sum`
  rewrites `Rₙ(A,L)` as `∑_{u ∈ A} childCount(L(u))`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotLevelSteps_measurable`
  proves measurability of `ω ↦ Lₙ(ω)`.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotLevelSteps_law` identifies
  the law of `Lₙ` with the product of `2ⁿ` copies of the selected offspring
  law.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels_levelSteps_independent`
  proves `Aₙ ⫫ Lₙ` under the step-field law.
* `ProbabilityTheory.BranchingRandomWalk.finiteSlotActiveLabels_condExp_succ_card`
  gives the conditional expectation of `|Aₙ₊₁|` given `Aₙ` as the integral of
  `Rₙ(Aₙ, ·)` against the product offspring law.

The coding bijection and its measurability details are internal support in
`Lemmas/Coding.lean`; the present module owns the induced population process,
its generation law, and its first-moment recursion.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

/-- The active coded parents at generation `n`. -/
noncomputable def finiteSlotActiveLabels
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    Finset (Fin n → Fin 2) :=
  by
    classical
    exact Finset.univ.filter fun u =>
      Combinatorics.Branching.surviveAlong
        (finiteSlotCodedStepField S ω) [] (List.ofFn u)

/-- The active finite-slot labels are in bijection with the source selected
population at the same generation. -/
theorem finiteSlotActiveLabels_card_eq_population_card
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (finiteSlotActiveLabels S ω n).card =
      (StepSelection.population S n ω).card := by
  classical
  apply Finset.card_bij (fun u _ => finiteSlotLevelRoots S ω n u)
  · intro u hu
    have hactive := (Finset.mem_filter.mp hu).2
    have hlen : (List.ofFn u).length = n := by simp
    have hpop := finiteSlotDecode_mem_population_of_surviveAlong
      S ω hcapacity n hlen hactive
    simpa [finiteSlotLevelRoots] using hpop
  · intro u hu v hv huv
    apply List.ofFn_injective
    apply finiteSlotDecode_injective_level S ω (by simp)
    simpa [finiteSlotLevelRoots] using huv
  · intro p hp
    obtain ⟨u, ⟨hlen, hactive, hdecode⟩, _⟩ :=
      finiteSlotDecode_existsUnique_of_mem_population
        S ω hcapacity n hp
    let v : Fin n → Fin 2 :=
      fun i => u.get (Fin.cast hlen.symm i)
    have hvlist : List.ofFn v = u := by
      calc
        List.ofFn v = List.ofFn u.get := by
          symm
          exact List.ofFn_congr hlen u.get
        _ = u := List.ofFn_get u
    refine ⟨v, ?_, ?_⟩
    · simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hvlist]
      exact hactive
    · simpa [finiteSlotLevelRoots, hvlist] using hdecode

/-- Distinct parent addresses have disjoint child families, and the list
append map preserves the number of selected slots. Hence a growth step has
cardinality equal to the sum of its parent offspring counts. -/
private theorem grow_card_eq_sum_childCount
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (parents : Finset (TreeNode α))
    (ω : Mark α (Step α X)) :
    (StepSelection.grow S parents ω).card =
      ∑ u ∈ parents, (S (ω u)).card := by
  have hchildren (u : TreeNode α) :
      (StepSelection.children S ω u).card = (S (ω u)).card := by
    have heq : StepSelection.children S ω u =
        (S (ω u)).image (fun i => u ++ [i]) := by
      ext q
      simp [StepSelection.children]
    rw [heq]
    apply Finset.card_image_iff.mpr
    intro i hi j hj hij
    have hsingle : [i] = [j] := List.append_cancel_left hij
    simpa using hsingle
  have hdisjoint :
      (parents : Set (TreeNode α)).PairwiseDisjoint
        (StepSelection.children S ω) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro u hu v hv hne
    obtain ⟨q, hq⟩ := hne
    have hqu : q ∈ StepSelection.children S ω u :=
      (Finset.mem_inter.mp hq).1
    have hqv : q ∈ StepSelection.children S ω v :=
      (Finset.mem_inter.mp hq).2
    obtain ⟨i, hi, hqi⟩ :=
      (StepSelection.mem_children_iff S ω u q).mp hqu
    obtain ⟨j, hj, hqj⟩ :=
      (StepSelection.mem_children_iff S ω v q).mp hqv
    have happend : u ++ [i] = v ++ [j] := hqi.symm.trans hqj
    have hdrop := congrArg List.dropLast happend
    simpa using hdrop
  have hgrow : StepSelection.grow S parents ω =
      parents.biUnion (StepSelection.children S ω) := by
    ext q
    simp [StepSelection.grow]
  calc
    (StepSelection.grow S parents ω).card =
        (parents.biUnion (StepSelection.children S ω)).card :=
      congrArg Finset.card hgrow
    _ = ∑ u ∈ parents, (StepSelection.children S ω u).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ u ∈ parents, (S (ω u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hchildren u

/-- The selected population cardinality advances by summing the selected
offspring counts of the current generation. -/
private theorem population_card_succ_eq_sum_childCount
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    (StepSelection.population S (n + 1) ω).card =
      ∑ u ∈ StepSelection.population S n ω, (S (ω u)).card := by
  rw [StepSelection.population_succ,
    grow_card_eq_sum_childCount S _ (frontierMarks n ω)]
  apply Finset.sum_congr rfl
  intro u hu
  have hdepth := StepSelection.population_depth S ω n u hu
  simp [frontierMarks, hdepth]

/-- The coded active-parent set is observable from the source field through
generation `n`. Pathwise, its members are exactly the coded addresses of the
source N-selected population. -/
theorem finiteSlotActiveLabels_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    Measurable[generationFiltration (M := Step α X) n]
      (finiteSlotActiveLabels S · n) := by
  classical
  let F : MeasurableSpace (Mark α (Step α X)) :=
    generationFiltration (M := Step α X) n
  have hpopulation : Measurable[F] (StepSelection.population S n) :=
    StepSelection.population_adapted S hS n
  rw [measurable_finset_iff]
  intro u
  have hroot : Measurable[F] (fun ω : Mark α (Step α X) =>
      finiteSlotLevelRoots S ω n u) := by
    exact (measurable_pi_apply u).comp
      (finiteSlotLevelRoots_measurable S hS n)
  have hrel : Measurable (fun q :
      TreeNode α × Finset (TreeNode α) => q.1 ∈ q.2) :=
    measurable_of_countable _
  have hmem : Measurable[F] (fun ω : Mark α (Step α X) =>
      finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω) :=
    hrel.comp (hroot.prodMk hpopulation)
  have hequiv : ∀ ω : Mark α (Step α X),
      u ∈ finiteSlotActiveLabels S ω n ↔
        finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω := by
    intro ω
    simp only [finiteSlotActiveLabels, Finset.mem_filter, Finset.mem_univ,
      true_and]
    let p := finiteSlotDecode S ω (List.ofFn u)
    have hlength : p.length = n := by
      simp [p, finiteSlotLevelRoots, finiteSlotDecode_length]
    have hdecode : p = finiteSlotLevelRoots S ω n u := by
      rfl
    constructor
    · intro hactive
      change finiteSlotDecode S ω (List.ofFn u) ∈
        StepSelection.population S n ω
      exact finiteSlotDecode_mem_population_of_surviveAlong S ω hcapacity n
        (by simp) hactive
    · intro hp
      change p ∈ StepSelection.population S n ω at hp
      have hp' := (mem_population_iff_length_selectedAlong S ω n p).mp hp
      exact (finiteSlotDecode_surviveAlong_iff_selectedAlong S ω
        hcapacity (List.ofFn u)).mpr (by simpa [p] using hp'.2)
  have hfun : (fun ω : Mark α (Step α X) =>
      u ∈ finiteSlotActiveLabels S ω n) =
    (fun ω => finiteSlotLevelRoots S ω n u ∈
      StepSelection.population S n ω) := by
    funext ω
    exact propext (hequiv ω)
  rw [hfun]
  exact hmem

/-- The finite-slot offspring observations at a fixed decoded generation are
independent and each has the offspring law induced by the selector. -/
noncomputable def finiteSlotLevelSteps
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} :=
  fun u => finiteOffspringStep S (ω (finiteSlotLevelRoots S ω n u))

/-- Summing the coded offspring counts over active labels gives exactly the
sum of selected offspring counts over the source population. -/
private theorem finiteSlotActiveLabels_sum_childCount_eq_population_sum
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat =
      ∑ p ∈ StepSelection.population S n ω, (S (ω p)).card := by
  classical
  have hactivePop {u : Fin n → Fin 2} :
      u ∈ finiteSlotActiveLabels S ω n ↔
        finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω := by
    constructor
    · intro hu
      have hsurvive := (Finset.mem_filter.mp hu).2
      have hlen : (List.ofFn u).length = n := by simp
      have hp := finiteSlotDecode_mem_population_of_surviveAlong
        S ω hcapacity n hlen hsurvive
      simpa [finiteSlotLevelRoots] using hp
    · intro hp
      have hpop := (mem_population_iff_length_selectedAlong S ω n
        (finiteSlotLevelRoots S ω n u)).mp hp
      have hselected : selectedAlong S ω []
          (finiteSlotDecode S ω (List.ofFn u)) := by
        simpa [finiteSlotLevelRoots] using hpop.2
      have hsurvive :=
        (finiteSlotDecode_surviveAlong_iff_selectedAlong S ω hcapacity
          (List.ofFn u)).mpr hselected
      simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hsurvive
  apply Finset.sum_bij (fun u _ => finiteSlotLevelRoots S ω n u)
  · intro u hu
    exact hactivePop.mp hu
  · intro u hu v hv huv
    apply List.ofFn_injective
    apply finiteSlotDecode_injective_level S ω (by simp)
    simpa [finiteSlotLevelRoots] using huv
  · intro p hp
    obtain ⟨u, ⟨hlen, hsurvive, hdecode⟩, _⟩ :=
      finiteSlotDecode_existsUnique_of_mem_population
        S ω hcapacity n hp
    let v : Fin n → Fin 2 :=
      fun i => u.get (Fin.cast hlen.symm i)
    have hvlist : List.ofFn v = u := by
      calc
        List.ofFn v = List.ofFn u.get := by
          symm
          exact List.ofFn_congr hlen u.get
        _ = u := List.ofFn_get u
    refine ⟨v, ?_, ?_⟩
    · simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hvlist]
      exact hsurvive
    · simpa [finiteSlotLevelRoots, hvlist] using hdecode
  · intro u hu
    simp [finiteSlotLevelSteps, finiteOffspringStep_childCount,
      hcapacity (ω (finiteSlotLevelRoots S ω n u))]

/-- Pathwise finite-generation transition for the coded reserve population.
Each active source parent contributes its selected child count, and the
active-label cardinality agrees with the actual selected population. -/
theorem finiteSlotActiveLabels_card_succ_eq_sum
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (finiteSlotActiveLabels S ω (n + 1)).card =
      ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat := by
  calc
    (finiteSlotActiveLabels S ω (n + 1)).card =
        (StepSelection.population S (n + 1) ω).card :=
      finiteSlotActiveLabels_card_eq_population_card S ω hcapacity (n + 1)
    _ = ∑ p ∈ StepSelection.population S n ω, (S (ω p)).card :=
      population_card_succ_eq_sum_childCount S ω n
    _ = ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat :=
      (finiteSlotActiveLabels_sum_childCount_eq_population_sum
        S ω hcapacity n).symm

/-- The offspring sum generated from a fixed active-label set by a row of
finite-slot offspring configurations. -/
noncomputable def finiteSlotRowCountSum
    (n : ℕ)
    (p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1})) : ℝ :=
  ∑ u : Fin n → Fin 2,
    if u ∈ p.1 then ((p.2 u).childCount.toNat : ℝ) else 0

theorem finiteSlotRowCountSum_measurable (n : ℕ) :
    Measurable (finiteSlotRowCountSum n) := by
  classical
  unfold finiteSlotRowCountSum
  apply Finset.measurable_fun_sum Finset.univ
  intro u hu
  have hmem : Measurable (fun p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) => u ∈ p.1) :=
    (measurable_finset_mem u).comp measurable_fst
  have hset : MeasurableSet {p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) | u ∈ p.1} :=
    measurableSet_setOfPred.mpr hmem
  have hcount : Measurable (fun p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) =>
      ((p.2 u).childCount.toNat : ℝ)) := by
    have hcast : Measurable (fun z : ℕ∞ => (z.toNat : ℝ)) :=
      measurable_of_countable _
    exact hcast.comp <| Step.childCount_measurable.comp <|
      (measurable_pi_apply u).comp measurable_snd
  exact Measurable.ite hset hcount measurable_const

theorem finiteSlotRowCountSum_eq_sum
    (n : ℕ) (A : Finset (Fin n → Fin 2))
    (rows : (Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :
    finiteSlotRowCountSum n (A, rows) =
      ∑ u ∈ A, ((rows u).childCount.toNat : ℝ) := by
  classical
  simp [finiteSlotRowCountSum, Finset.sum_ite_mem_eq]

theorem finiteSlotLevelSteps_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    Measurable (finiteSlotLevelSteps S · n) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hvector : Measurable vector :=
    selectedSubtreeStepFieldVector_measurable roots
      (finiteSlotLevelRoots_measurable S hS n)
      (finiteSlotLevelRoots_range_countable S n)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hobserveVector : Measurable observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (finiteSlotLevelSteps S · n) = observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  rw [hcompose]
  exact hobserveVector.comp hvector

theorem finiteSlotLevelSteps_law
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    (stepFieldLaw μ).map (finiteSlotLevelSteps S · n) =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS :
          Measure (Step (Fin 2) PUnit.{1}))) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let ν : ProbabilityMeasure (Step α X) := ⟨μ, inferInstance⟩
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hmap : Measure.map observe (stepFieldLaw μ) =
      (finiteOffspringLaw ν S hS :
        Measure (Step (Fin 2) PUnit.{1})) := by
    change Measure.map (fun field : StepField α X =>
      finiteOffspringStep S (field ([] : TreeNode α))) (stepFieldLaw μ) = _
    rw [show (fun field : StepField α X =>
        finiteOffspringStep S (field ([] : TreeNode α))) =
        (finiteOffspringStep S) ∘ (fun field : StepField α X =>
          field ([] : TreeNode α)) by rfl]
    rw [← Measure.map_map (finiteOffspringStep_measurable S hS)
      (measurable_pi_apply ([] : TreeNode α))]
    rw [stepFieldLaw_coordinate μ []]
    rfl
  have hvector : (stepFieldLaw μ).map vector =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ) := by
    exact finiteSlotLevelSubtreeVector_law μ S hS n
  have hmapVector :
      (Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ)).map
          observeVector =
        Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
          Measure.map observe (stepFieldLaw μ)) := by
    exact Measure.infinitePi_map_pi
      (μ := fun _ : (Fin n → Fin 2) => stepFieldLaw μ)
      (f := fun _ => observe) (hf := fun _ => hobserve)
  have hvectorMeasurable : Measurable vector :=
    selectedSubtreeStepFieldVector_measurable roots
      (finiteSlotLevelRoots_measurable S hS n)
      (finiteSlotLevelRoots_range_countable S n)
  have hmapVectorMeasurable : Measurable
      observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (fun ω => finiteSlotLevelSteps S ω n) =
      observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  calc
    (stepFieldLaw μ).map (finiteSlotLevelSteps S · n) =
        (Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ)).map
          observeVector := by
      rw [hcompose, ← Measure.map_map hmapVectorMeasurable hvectorMeasurable,
        hvector]
    _ = Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        Measure.map observe (stepFieldLaw μ)) := hmapVector
    _ = Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw ν S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
      apply Measure.eq_infinitePi
      intro t A hA
      rw [Measure.infinitePi_pi _ (fun i _ => hA i)]
      apply Finset.prod_congr rfl
      intro i hi
      exact congrArg (fun ν : Measure (Step (Fin 2) PUnit.{1}) => ν (A i)) hmap

/-- The decoded offspring family at generation `n` is independent of the
source marks revealed before that generation. -/
private theorem finiteSlotLevelSteps_independent
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (finiteSlotLevelSteps S · n) inferInstance)
      (stepFieldLaw μ) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hchosen := finiteSlotLevelRoots_measurable S hS n
  have hind := selectedSubtreeStepFieldVector_independent μ roots
    hchosen (finiteSlotLevelRoots_range_countable S n)
    (finiteSlotLevelRoots_fiber_measurable S hS n)
    (fun ω u => finiteSlotLevelRoots_depth S ω n u)
    (fun ω => finiteSlotLevelRoots_injective S ω n)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hobserveVector : Measurable observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (finiteSlotLevelSteps S · n) = observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  apply indep_of_indep_of_le_right hind
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    observeVector hobserveVector hcompose

theorem finiteSlotActiveLabels_levelSteps_independent
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    IndepFun (finiteSlotActiveLabels S · n)
      (finiteSlotLevelSteps S · n) (stepFieldLaw μ) := by
  classical
  have hactive : Measurable[generationFiltration (M := Step α X) n]
      (finiteSlotActiveLabels S · n) :=
    finiteSlotActiveLabels_measurable S hS hcapacity n
  have hsteps : Measurable (finiteSlotLevelSteps S · n) :=
    finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotLevelSteps_independent μ S hS n
  have hsmall : Indep
      (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (MeasurableSpace.comap (finiteSlotLevelSteps S · n) inferInstance)
      (stepFieldLaw μ) :=
    ProbabilityTheory.indep_of_indep_of_le_left hind hactive.comap_le
  rw [IndepFun_iff_Indep]
  exact hsmall

/-- The observable active set and the fresh offspring row have a product
joint law. Thus finite-horizon moment recurrences can condition on the active
set without a stopping-time theorem. -/
private theorem finiteSlotActiveLabels_levelSteps_jointLaw
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (stepFieldLaw μ).map (fun ω =>
      (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n)) =
      ((stepFieldLaw μ).map (finiteSlotActiveLabels S · n)).prod
        (Measure.infinitePi fun _ : (Fin n → Fin 2) =>
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
            S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
  have hactive : Measurable (finiteSlotActiveLabels S · n) :=
    (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hsteps : Measurable (finiteSlotLevelSteps S · n) :=
    finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotActiveLabels_levelSteps_independent
    μ S hS hcapacity n
  rw [hind.map_prod_eq_prod_map_map hactive.aemeasurable hsteps.aemeasurable,
    finiteSlotLevelSteps_law μ S hS n]

/-- Conditional first-moment recursion at an observable generation: after
conditioning on the active labels, integrate their fresh offspring counts
against the fixed iid finite-slot row law. -/
theorem finiteSlotActiveLabels_condExp_succ_card
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)) =ᵐ[stepFieldLaw μ]
    fun ω => ∫ row, finiteSlotRowCountSum n
      (finiteSlotActiveLabels S ω n, row) ∂
        Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
            S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
  classical
  let active : Mark α (Step α X) → Finset (Fin n → Fin 2) :=
    fun ω => finiteSlotActiveLabels S ω n
  let rows : Mark α (Step α X) →
      (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} :=
    fun ω => finiteSlotLevelSteps S ω n
  let nextSize : Mark α (Step α X) → ℝ := fun ω =>
    ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)
  let rowSum : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) → ℝ :=
    finiteSlotRowCountSum n
  have hactive : Measurable active := by
    simpa [active] using
      (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
        (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hrows : Measurable rows := by
    simpa [rows] using finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotActiveLabels_levelSteps_independent
    μ S hS hcapacity n
  have hnext : Measurable nextSize := by
    change Measurable (fun ω =>
      ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ))
    exact (measurable_of_countable fun A : Finset (Fin (n + 1) → Fin 2) =>
      (A.card : ℝ)).comp <|
        (finiteSlotActiveLabels_measurable S hS hcapacity (n + 1)).mono
          (generationFiltration (M := Step α X) |>.le (n + 1)) le_rfl
  have hnextBound : ∀ ω, ‖nextSize ω‖ ≤ (2 ^ (n + 1) : ℝ) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hcard : (finiteSlotActiveLabels S ω (n + 1)).card ≤ 2 ^ (n + 1) := by
      rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity]
      exact StepSelection.population_card_le S 2 hcapacity ω (n + 1)
    have hreal :
        ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ≤
          (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast hcard
    simpa only [nextSize] using hreal
  have hnextIntegrable : Integrable nextSize (stepFieldLaw μ) :=
    Integrable.of_bound hnext.aestronglyMeasurable (2 ^ (n + 1) : ℝ)
      (ae_of_all _ hnextBound)
  have hrowMeasurable : Measurable rowSum := by
    exact finiteSlotRowCountSum_measurable n
  have hrowStrong : StronglyMeasurable rowSum := hrowMeasurable.stronglyMeasurable
  have hsample : (fun ω => rowSum (active ω, rows ω)) = nextSize := by
    funext ω
    have hsum := finiteSlotActiveLabels_card_succ_eq_sum S ω hcapacity n
    change finiteSlotRowCountSum n
      (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n) = _
    rw [finiteSlotRowCountSum_eq_sum]
    simpa only [Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) hsum.symm
  have hsampleIntegrable :
      Integrable (fun ω => rowSum (active ω, rows ω)) (stepFieldLaw μ) := by
    rw [hsample]
    exact hnextIntegrable
  letI : MeasurableSingletonClass (Option PUnit.{1}) := by
    refine ⟨fun x => ?_⟩
    cases x with
    | none => exact measurableSet_option_none
    | some x =>
      rw [show ({some x} : Set (Option PUnit.{1})) = some '' {x} by
        ext y
        simp]
      exact measurableSet_option_some_image (measurableSet_singleton x)
  letI : MeasurableSingletonClass (Step (Fin 2) PUnit.{1}) := inferInstance
  letI : StandardBorelSpace (Step (Fin 2) PUnit.{1}) := by infer_instance
  letI : StandardBorelSpace ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) := by
    infer_instance
  have hcond := hind.condExp_prod_ae_eq_integral_map
    hactive hrows hrowStrong hsampleIntegrable
  rw [hsample] at hcond
  have hrowLaw : (stepFieldLaw μ).map rows =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
    simpa [rows] using finiteSlotLevelSteps_law μ S hS n
  rw [hrowLaw] at hcond
  simpa [active, nextSize, rowSum] using hcond

end ProbabilityTheory.BranchingRandomWalk
