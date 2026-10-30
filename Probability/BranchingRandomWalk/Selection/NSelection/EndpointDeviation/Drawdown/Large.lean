/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.FirstPassage
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Lemmas.SelectedCount

/-!
# Large ancestral drawdowns for the first-`N` selected population

This file handles the exceptional large-drawdown term in Aïdékon--Hu's
polynomial endpoint sublevel estimate.  It branches at a deterministic generation
along the generation-measurable first-`N` population, and bounds each
fresh descendant tree by the one-root many-to-one estimate.  Empty offspring
remain allowed: all population and descendant events are phrased by actual
surviving addresses.

The source estimate is equation (4.16) in the proof of Proposition 3.1 of
Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the complete graph*,
arXiv:2512.23266 (2025).

## Public declarations

- `selectedFirstPassageBelowAtGeneration` is the first-`N` population event
  at a fixed generation; `measurableSet_selectedFirstPassageBelowAtGeneration`
  proves measurability, and
  `measure_selectedFirstPassageBelowAtGeneration_le` bounds its probability.
- `selectedFirstPassageBelowByHorizon` is the union over generations through
  `H`; `measure_selectedFirstPassageBelowByHorizon_le` gives its probability
  bound.
- `rawFirstNSelectedLargeDrop` is the raw large-drop event and
  `firstNSelectedLargeDrawdown` is its totalized version.
  `rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown` and
  `firstNSelectedLargeDrawdown_subset_selectedFirstPassageBelowByHorizon`
  give the event inclusions; `measure_firstNSelectedLargeDrawdown_le` and
  `measure_rawFirstNSelectedLargeDrop_le` give their probability bounds.

The totalized first-`N` population and its cardinality and filtration
properties are defined in `Drawdown/Population.lean`. The one-root event
`hasFirstPassageBelow` and its many-to-one bound are defined in
`Probability/BranchingRandomWalk/Spine/FirstPassage.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

private abbrev GenerationAddress (m j : ℕ) :=
  {p : RootIndexed.TreeNode (Fin m) ℕ // p.2.length = j}

/-- At generation `j`, a first passage below `-B` from one of the
first-`N` selected particles during the remaining finite horizon.  Each
event in the union is a root-fiber event intersected with an event depending
only on that root's fresh descendant tree. -/
def selectedFirstPassageBelowAtGeneration (m N j H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  ⋃ p : {p : RootIndexed.TreeNode (Fin m) ℕ // p.2.length = j},
    {field | p.1 ∈ firstNSelectedPopulation m N j field ∧
      RootIndexed.subtreeStepFieldVector
        (fun q => (q.1.1, q.1.2)) field p ∈
        hasFirstPassageBelow (ι := ℕ) (H - j) B}

theorem measurableSet_selectedFirstPassageBelowAtGeneration
    (m N j H : ℕ) (B : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    MeasurableSet (selectedFirstPassageBelowAtGeneration m N j H B) := by
  classical
  apply MeasurableSet.iUnion
  intro p
  have hpop : Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) j]
      (firstNSelectedPopulation m N j) :=
    firstNSelectedPopulation_adapted m N j
  have hmem : MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) j]
      {field | p.1 ∈ firstNSelectedPopulation m N j field} :=
    hpop (measurableSet_mem_finset p.1)
  have hfirst : MeasurableSet
      (hasFirstPassageBelow (ι := ℕ) (H - j) B) :=
    measurableSet_hasFirstPassageBelow (H - j) B
  have hvector : Measurable
      (RootIndexed.subtreeStepFieldVector (fun q : GenerationAddress m j => (q.1.1, q.1.2))) :=
    RootIndexed.subtreeStepFieldVector_measurable
      (X := ℝ) (fun q : GenerationAddress m j => (q.1.1, q.1.2))
  have hhit : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        RootIndexed.subtreeStepFieldVector
            (fun q : GenerationAddress m j => (q.1.1, q.1.2)) field p ∈
          hasFirstPassageBelow (ι := ℕ) (H - j) B} :=
    hfirst.preimage ((measurable_pi_apply p).comp hvector)
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p.1 ∈ firstNSelectedPopulation m N j field ∧
        RootIndexed.subtreeStepFieldVector (fun q : GenerationAddress m j => (q.1.1, q.1.2))
          field p ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B} =
      {field | p.1 ∈ firstNSelectedPopulation m N j field} ∩
        {field | RootIndexed.subtreeStepFieldVector
          (fun q : GenerationAddress m j => (q.1.1, q.1.2)) field p ∈
            hasFirstPassageBelow (ι := ℕ) (H - j) B} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact ((RootIndexed.stepFiltration
    (Root := Fin m) (α := ℕ) (X := ℝ) |>.le j) _ hmem).inter hhit

/-- At a fixed generation, branch at each first-`N` selected address before
revealing its descendants.  The sum of all possible selected roots is at
most `N`, and each fresh one-root tree contributes only the one-root
first-passage bound. -/
theorem measure_selectedFirstPassageBelowAtGeneration_le
    (m N j H : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (hj : j < H)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (B : ℝ) :
    (finiteRootStepFieldLaw μ m)
        (selectedFirstPassageBelowAtGeneration m N j H B) ≤
      (N : ℝ≥0∞) *
        (((H - j : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (-B))) := by
  classical
  let P := finiteRootStepFieldLaw μ m
  let A : GenerationAddress m j → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | p.1 ∈ firstNSelectedPopulation m N j field}
  let E : GenerationAddress m j → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | p.1 ∈ firstNSelectedPopulation m N j field ∧
      RootIndexed.subtreeStepFieldVector (fun q : GenerationAddress m j => (q.1.1, q.1.2))
        field p ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B}
  let roots (p : GenerationAddress m j) : Unit → Fin m × TreeNode ℕ :=
    fun _ => (p.1.1, p.1.2)
  let freshEvent : Set (Unit → TreeNode ℕ → Step ℕ ℝ) :=
    {v | v () ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B}
  have hA (p : GenerationAddress m j) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) j] (A p) := by
    have hpop := firstNSelectedPopulation_adapted m N j
    simpa [A] using hpop (measurableSet_mem_finset p.1)
  have hfresh : MeasurableSet
      (hasFirstPassageBelow (ι := ℕ) (H - j) B) :=
    measurableSet_hasFirstPassageBelow (H - j) B
  have hfreshEvent : MeasurableSet freshEvent := by
    exact hfresh.preimage (measurable_pi_apply ())
  have hfactor (p : GenerationAddress m j) :
      P (E p) = P (A p) *
        (offspringFieldLaw μ)
          (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
    have hlen : ∀ i : Unit, (roots p i).2.length = j := by
      intro i
      exact p.2
    have hinj : Function.Injective (roots p) := by
      intro a b _
      exact Subsingleton.elim _ _
    have hfactor := RootIndexed.subtreeStepFieldVector_event_factorization
      (Root := Fin m) (κ := Unit) (α := ℕ) (X := ℝ)
      μ (roots p) hlen hinj (A p) freshEvent (hA p) hfreshEvent
    have hBprob :
        (RootIndexed.stepFieldLaw (Root := Unit) μ) freshEvent =
          (offspringFieldLaw μ)
            (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
      change (RootIndexed.stepFieldLaw (Root := Unit) μ)
          ((fun η : RootIndexed.StepField Unit ℕ ℝ => η ()) ⁻¹'
            (hasFirstPassageBelow (ι := ℕ) (H - j) B)) = _
      rw [← Measure.map_apply (measurable_pi_apply ()) hfresh]
      rw [RootIndexed.stepFieldLaw_root_marginal μ ()]
    have hE :
        E p = A p ∩
          RootIndexed.subtreeStepFieldVector (roots p) ⁻¹' freshEvent := by
      ext field
      simp only [E, A, Set.mem_ofPred_eq, Set.mem_inter_iff,
        Set.mem_preimage]
      rfl
    change (RootIndexed.stepFieldLaw (Root := Fin m) μ) (E p) = _
    rw [hE, hfactor, hBprob]
  have hsumA :
      ∑' p : GenerationAddress m j, P (A p) ≤ N := by
    exact tsum_generationAddress_selected_le m N j hmN μ
  have hsingle :
      (offspringFieldLaw μ)
        (hasFirstPassageBelow (ι := ℕ) (H - j) B) ≤
        ((H - j : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (-B)) :=
    by
      simpa [Nat.cast_sub hj.le] using
        (measure_hasFirstPassageBelow_le μ hboundary (H - j) B)
  calc
    P (selectedFirstPassageBelowAtGeneration m N j H B) ≤
        ∑' p : GenerationAddress m j, P (E p) := by
      change P (⋃ p : GenerationAddress m j, E p) ≤ _
      exact measure_iUnion_le E
    _ = (∑' p : GenerationAddress m j, P (A p)) *
          (offspringFieldLaw μ)
            (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
      calc
        ∑' p : GenerationAddress m j, P (E p) =
            ∑' p : GenerationAddress m j,
              P (A p) * (offspringFieldLaw μ)
                (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
          apply tsum_congr
          intro p
          exact hfactor p
        _ = (∑' p : GenerationAddress m j, P (A p)) *
              (offspringFieldLaw μ)
                (hasFirstPassageBelow (ι := ℕ) (H - j) B) :=
          ENNReal.tsum_mul_right
    _ ≤ (N : ℝ≥0∞) *
          ((H - j + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-B))) := by
      gcongr

/-- The full finite-horizon large-drawdown source event: at some generation
`j < H`, a particle of the first-`N` population has a descendant whose
relative path first crosses below `-B` before generation `H`. -/
def selectedFirstPassageBelowByHorizon (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  ⋃ j : Fin H, selectedFirstPassageBelowAtGeneration m N j H B

/-- Union bound over all possible starting generations.  The intentionally
coarse `(H+1)^2` factor absorbs both the number of starting generations and
the remaining descendant horizon. -/
theorem measure_selectedFirstPassageBelowByHorizon_le
    (m N H : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (B : ℝ) :
    (finiteRootStepFieldLaw μ m)
        (selectedFirstPassageBelowByHorizon m N H B) ≤
      (N : ℝ≥0∞) *
        (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) := by
  classical
  let P := finiteRootStepFieldLaw μ m
  let C : ℝ≥0∞ :=
    (N : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp (-B)))
  have hper (j : Fin H) :
      P (selectedFirstPassageBelowAtGeneration m N j H B) ≤ C := by
    calc
      P (selectedFirstPassageBelowAtGeneration m N j H B) ≤
          (N : ℝ≥0∞) * (((H - (j : ℕ) : ℝ≥0∞) + 1) *
            ENNReal.ofReal (Real.exp (-B))) :=
        measure_selectedFirstPassageBelowAtGeneration_le
          m N j H hmN j.isLt μ hboundary B
      _ ≤ C := by
        have hjle : H - (j : ℕ) ≤ H := Nat.sub_le _ _
        have hjcast :
            ((H - (j : ℕ) : ℝ≥0∞) + 1) ≤ (H : ℝ≥0∞) + 1 := by
          exact_mod_cast (Nat.add_le_add_right hjle 1)
        dsimp [C]
        gcongr
  calc
    P (selectedFirstPassageBelowByHorizon m N H B) ≤
        ∑ j : Fin H,
          P (selectedFirstPassageBelowAtGeneration m N j H B) := by
      exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _j : Fin H, C := by
      exact Finset.sum_le_sum fun j _ => hper j
    _ = (H : ℝ≥0∞) * C := by
      simp [C, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) := by
      dsimp [C]
      calc
        (H : ℝ≥0∞) *
            ((N : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) *
              ENNReal.ofReal (Real.exp (-B)))) =
          (N : ℝ≥0∞) *
            ((H : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) *
              ENNReal.ofReal (Real.exp (-B)))) := by ac_rfl
        _ ≤ (N : ℝ≥0∞) *
              (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) := by
          have hH : (H : ℝ≥0∞) ≤ (H : ℝ≥0∞) + 1 :=
            le_add_of_nonneg_right (by norm_num)
          have hprod : (H : ℝ≥0∞) * ((H : ℝ≥0∞) + 1) ≤
              ((H : ℝ≥0∞) + 1) * ((H : ℝ≥0∞) + 1) :=
            mul_le_mul_left hH _
          have hinner :
              (H : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) *
                ENNReal.ofReal (Real.exp (-B))) ≤
              (((H : ℝ≥0∞) + 1) ^ 2) * ENNReal.ofReal (Real.exp (-B)) := by
            calc
              (H : ℝ≥0∞) * (((H : ℝ≥0∞) + 1) *
                  ENNReal.ofReal (Real.exp (-B))) =
                ((H : ℝ≥0∞) * ((H : ℝ≥0∞) + 1)) *
                  ENNReal.ofReal (Real.exp (-B)) := by ac_rfl
              _ ≤ (((H : ℝ≥0∞) + 1) * ((H : ℝ≥0∞) + 1)) *
                    ENNReal.ofReal (Real.exp (-B)) :=
                mul_le_mul_left hprod _
              _ = (((H : ℝ≥0∞) + 1) ^ 2) *
                    ENNReal.ofReal (Real.exp (-B)) := by rw [pow_two]
          exact mul_le_mul_right hinner _

private lemma take_append_drop_take_eq {α : Type*} (u : List α)
    (k j i : ℕ) (hjk : j ≤ k) (hik : i ≤ k - j) :
    (u.take k).take j ++ ((u.take k).drop j).take i = u.take (j + i) := by
  calc
    (u.take k).take j ++ ((u.take k).drop j).take i =
        u.take j ++ (u.drop j).take i := by
      have htake : (u.take k).take j = u.take j := by
        rw [List.take_take, min_eq_left hjk]
      have hdrop : ((u.take k).drop j).take i = (u.drop j).take i := by
        rw [List.drop_take, List.take_take, min_eq_left hik]
      rw [htake, hdrop]
    _ = u.take (j + i) := by rw [← List.take_add]

/-- The raw large-drop event for the first-`N` population: a selected
generation-`n` particle has an ancestor at generation `j<n` from which its
position drops by more than `B`. -/
def rawFirstNSelectedLargeDrop (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ n : Fin (H + 1), ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
      p ∈ firstNSelectedPopulation m N n.val field ∧
      ∃ j : ℕ, j < n.val ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
            (p.2.take j) -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 > B}

/-- A large drawdown along a first-`N` selected address, recorded at its
first crossing.  The intermediate-prefix clause is the first-crossing
normalization; the ancestor is recovered from the selected endpoint by
`firstNSelectedPopulation_prefix_mem`. -/
def firstNSelectedLargeDrawdown (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ n : Fin (H + 1), ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
      p ∈ firstNSelectedPopulation m N n.val field ∧
      ∃ j : ℕ, j < n.val ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
            (p.2.take j) -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 > B ∧
        ∀ i : ℕ, 0 < i → i < (p.2.drop j).length →
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
              (p.2.take j) -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
              (p.2.take j ++ (p.2.drop j).take i) ≤ B}

/-- Any raw selected large drop has a first crossing along the selected
ancestral path.  The first-crossing endpoint remains selected because the
totalized selected population is ancestor closed. -/
theorem rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown
    (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    rawFirstNSelectedLargeDrop m N H B ⊆
      firstNSelectedLargeDrawdown m N H B := by
  classical
  intro field hraw
  obtain ⟨n, p, hp, j, hjn, hdrop⟩ := hraw
  have hp' : p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n.val field := by
    simpa [firstNSelectedPopulation] using hp
  have hdepth : p.2.length = n.val :=
    RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n.val field p hp'
  let D : ℕ → ℝ := fun i =>
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
        (p.2.take j) -
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
        (p.2.take i)
  have hcross : ∃ i, j < i ∧ i ≤ n.val ∧ B < D i := by
    refine ⟨n.val, hjn, le_rfl, ?_⟩
    have htakeN : p.2.take n.val = p.2 :=
      (List.take_eq_self_iff p.2).2 (by omega)
    simpa [D, htakeN] using hdrop
  let k : ℕ := Nat.find hcross
  have hk : j < k ∧ k ≤ n.val ∧ B < D k := Nat.find_spec hcross
  have hfirst : ∀ i, j < i → i < k → D i ≤ B := by
    intro i hji hik
    by_contra hnot
    have hgt : B < D i := lt_of_not_ge hnot
    have hnotcross := Nat.find_min hcross hik
    exact hnotcross ⟨hji, by omega, hgt⟩
  have hklen : k ≤ p.2.length := by omega
  let endpoint : RootIndexed.TreeNode (Fin m) ℕ := (p.1, p.2.take k)
  have hendpointMem : endpoint ∈ firstNSelectedPopulation m N k field := by
    exact firstNSelectedPopulation_prefix_mem m N n.val field p hp k (by omega)
  have hendpointDepth : endpoint.2.length = k := by
    simp [endpoint, List.length_take, min_eq_left hklen]
  have hjk : j ≤ k := by omega
  have htakeJ : endpoint.2.take j = p.2.take j := by
    simp [endpoint, List.take_take, min_eq_left hjk]
  have hendpointBound : k ≤ H := by omega
  let endpointGeneration : Fin (H + 1) := ⟨k, by omega⟩
  refine ⟨endpointGeneration, endpoint, hendpointMem, j, hk.1, ?_, ?_⟩
  · have hD := hk.2.2
    simpa [D, endpoint, htakeJ] using hD
  · intro i hiPos hiLen
    have hsuffixLength : (endpoint.2.drop j).length = k - j := by
      simp [List.length_drop, hendpointDepth, min_eq_left hjk]
    have hiBound : i ≤ k - j := by omega
    have hji : j + i < k := by omega
    have hdi := hfirst (j + i) (by omega) hji
    have hpath :
        endpoint.2.take j ++ (endpoint.2.drop j).take i = p.2.take (j + i) := by
      change (p.2.take k).take j ++ ((p.2.take k).drop j).take i =
        p.2.take (j + i)
      exact take_append_drop_take_eq p.2 k j i hjk hiBound
    have hpath' :
        p.2.take j ++ (endpoint.2.drop j).take i = p.2.take (j + i) := by
      simpa [htakeJ] using hpath
    rw [htakeJ, hpath']
    simpa [D] using hdi

/-- Pathwise, a first-`N` selected large drawdown is a first-passage event
from the selected ancestor at its starting generation. -/
theorem firstNSelectedLargeDrawdown_subset_selectedFirstPassageBelowByHorizon
    (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hB : 0 < B) :
    firstNSelectedLargeDrawdown m N H B ⊆
      selectedFirstPassageBelowByHorizon m N H B := by
  classical
  intro field hF
  obtain ⟨n, p, hp, j, hjn, hdrop, hprefix⟩ := hF
  have hnH : n.val ≤ H := by omega
  have hp' : p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n.val field := by
    simpa [firstNSelectedPopulation] using hp
  have hdepth : p.2.length = n.val :=
    RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n.val field p hp'
  have hjdepth : j ≤ p.2.length := by omega
  have qmem :
      (p.1, p.2.take j) ∈ firstNSelectedPopulation m N j field :=
    firstNSelectedPopulation_prefix_mem m N n.val field p hp j (by omega)
  have hqdepth : (p.2.take j).length = j := by
    simp [List.length_take, min_eq_left hjdepth]
  let suffix : TreeNode ℕ := p.2.drop j
  have hsuffix : suffix.length = n.val - j := by
    simp [suffix, List.length_drop, min_eq_left hjdepth, hdepth]
  have hpos : 0 < suffix.length := by omega
  have hlen : suffix.length ≤ H - j := by omega
  have hsurvive : surviveAlong (field p.1) [] p.2 := by
    apply firstNSelectedPopulation_surviveAlong m N n.val field p
    simpa [firstNSelectedPopulation] using hp
  have hsplit :
      surviveAlong (field p.1) [] (p.2.take j ++ suffix) := by
    simpa [suffix, List.take_append_drop] using hsurvive
  have htail : surviveAlong (field p.1) (p.2.take j) suffix :=
    (surviveAlong_append (field p.1) [] (p.2.take j) suffix).mp hsplit |>.2
  have hlocalSurvive :
      surviveAlong
        (RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (p.1, p.2.take j)) field ()) [] suffix := by
    have htail' :
        surviveAlong (field p.1) (p.2.take j ++ []) suffix := by
      simpa using htail
    have hrebased :=
      (surviveAlong_rebase (field p.1) (p.2.take j) [] suffix).mpr htail'
    change surviveAlong (fun w => field p.1 (p.2.take j ++ w)) [] suffix
    exact hrebased
  have hlocalEnd :
      Spine.pathPotential realPotential
          (RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (p.1, p.2.take j)) field ()) suffix =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
            (p.2.take j) := by
    have h := pathPotential_subtreeStepFieldVector_eq_position_sub
      (φ := realPotential) field p.1 (p.2.take j) suffix
    simpa [realPotential, suffix, List.take_append_drop] using h
  have hbelow :
      Spine.pathPotential realPotential
          (RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (p.1, p.2.take j)) field ()) suffix < -B := by
    rw [hlocalEnd]
    linarith
  have hfirst : ∀ i : ℕ, i < suffix.length →
      -B ≤ Spine.pathPotential realPotential
        (RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (p.1, p.2.take j)) field ()) (suffix.take i) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [Spine.pathPotential]
      linarith
    · have hprefix' := hprefix i (Nat.pos_of_ne_zero hi0) (by simpa [suffix] using hi)
      have hlocalI :
          Spine.pathPotential realPotential
              (RootIndexed.subtreeStepFieldVector
                (fun _ : Unit => (p.1, p.2.take j)) field ())
              (suffix.take i) =
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                (p.2.take j ++ suffix.take i) -
              RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
                (p.2.take j) := by
        have h := pathPotential_subtreeStepFieldVector_eq_position_sub
          (φ := realPotential) field p.1 (p.2.take j) (suffix.take i)
        simpa [realPotential, suffix] using h
      rw [hlocalI]
      linarith
  let q : RootIndexed.TreeNode (Fin m) ℕ := (p.1, p.2.take j)
  let q' : GenerationAddress m j := ⟨q, hqdepth⟩
  have hvectorEq :
      RootIndexed.subtreeStepFieldVector
          (fun q : GenerationAddress m j => (q.1.1, q.1.2)) field q' =
        RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (p.1, p.2.take j)) field () := by
    funext w
    rfl
  have hjH : j < H := by omega
  have hlocalEvent :
      RootIndexed.subtreeStepFieldVector
          (fun q : GenerationAddress m j => (q.1.1, q.1.2)) field q' ∈
        hasFirstPassageBelow (ι := ℕ) (H - j) B := by
    refine ⟨suffix, hpos, hlen, ?_, ?_, ?_⟩
    · rw [hvectorEq]
      exact hlocalSurvive
    · have h := hbelow
      rw [hvectorEq]
      exact h
    · intro i hi
      have h := hfirst i hi
      rw [hvectorEq]
      exact h
  rw [selectedFirstPassageBelowByHorizon]
  refine Set.mem_iUnion.2 ⟨⟨j, hjH⟩, ?_⟩
  rw [selectedFirstPassageBelowAtGeneration]
  refine Set.mem_iUnion.2 ⟨q', ?_⟩
  change q ∈ firstNSelectedPopulation m N j field ∧ _
  exact ⟨by simpa [q] using qmem, hlocalEvent⟩

/-- The first-`N` large-drawdown witness is bounded by the
finite-horizon first-passage estimate.  This combines the pathwise witness
inclusion with branching at each selected ancestor. -/
theorem measure_firstNSelectedLargeDrawdown_le
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedLargeDrawdown m N H B) ≤
      (N : ℝ≥0∞) *
        (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) := by
  calc
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedLargeDrawdown m N H B) ≤
      (finiteRootStepFieldLaw μ m)
        (selectedFirstPassageBelowByHorizon m N H B) :=
      measure_mono
        (firstNSelectedLargeDrawdown_subset_selectedFirstPassageBelowByHorizon
          m N H B hB)
    _ ≤ (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) :=
      measure_selectedFirstPassageBelowByHorizon_le
        m N H hmN μ hboundary B

/-- Probability bound for the original, unnormalized first-`N` large-drop
witness.  The finite first-crossing reduction preserves selection by
ancestor-closure, so the estimate is inherited from the normalized event. -/
theorem measure_rawFirstNSelectedLargeDrop_le
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    (finiteRootStepFieldLaw μ m)
        (rawFirstNSelectedLargeDrop m N H B) ≤
      (N : ℝ≥0∞) *
        (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) := by
  calc
    (finiteRootStepFieldLaw μ m)
        (rawFirstNSelectedLargeDrop m N H B) ≤
      (finiteRootStepFieldLaw μ m)
        (firstNSelectedLargeDrawdown m N H B) :=
      measure_mono
        (rawFirstNSelectedLargeDrop_subset_firstNSelectedLargeDrawdown
          m N H B)
    _ ≤ (N : ℝ≥0∞) *
          (((H : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-B))) :=
      measure_firstNSelectedLargeDrawdown_le
        m N H hmN B hB μ hboundary

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
