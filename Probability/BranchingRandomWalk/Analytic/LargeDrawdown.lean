/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.LeftTailAtAOne
import Probability.BranchingRandomWalk.Analytic.SelectedPopulationDrawdown
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Large ancestral drawdowns for the first-`N` selected population

This file handles the exceptional large-drawdown term in Aïdékon--Hu's
polynomial left-tail estimate.  It branches at a deterministic generation
along the generation-measurable first-`N` population, and bounds each
fresh descendant tree by the one-root many-to-one estimate.  Empty offspring
remain allowed: all population and descendant events are phrased by actual
surviving addresses.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open Combinatorics.Branching
open Combinatorics.UlamHarris

private abbrev GenerationAddress (m j : ℕ) :=
  {p : RootIndexed.TreeNode (Fin m) ℕ // p.2.length = j}

/-- The fixed generation-`j` root family used to apply the branching
property before revealing the independent descendant fields. -/
private def generationAddressRoots (m j : ℕ) :
    GenerationAddress m j → Fin m × TreeNode ℕ :=
  fun p => (p.1.1, p.1.2)

/-- The totalized first-`N` population at generation `j` from `m` roots at
zero.  It is defined for every sampled forest, including fields where the
raw candidate population is not lower-finite. -/
noncomputable def largeDrawdownPopulation (m N j : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.selectedPopulationTotalized N Finset.univ (fun _ => 0)
    id id j field

theorem largeDrawdownPopulation_card_le (m N j : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N)
    (field : FiniteRootStepField m ℕ ℝ) :
    (largeDrawdownPopulation m N j field).card ≤ N := by
  classical
  cases j with
  | zero =>
      simpa [largeDrawdownPopulation, RootIndexed.selectedPopulationTotalized,
        RootIndexed.initialPopulation_card] using hmN
  | succ j =>
      let value := RootIndexed.observedPositionAtGeneration
        (α := ℕ)
        (fun _ : Fin m => (0 : ℝ)) (id : ℝ → ℝ) (id : ℝ → ℝ) (j + 1)
      let candidates := fun ω : FiniteRootStepField m ℕ ℝ =>
        RootIndexed.childrenAtGeneration j
          (RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id j ω) ω
      by_cases hgood : Combinatorics.Branching.Selection.NSelection.IsLowerFiniteBy
          (value field) (candidates field)
      · change (RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun _ : Fin m => (0 : ℝ)) id id (j + 1) field).card ≤ N
        exact (RootIndexed.selectedPopulationTotalized_succ_spec
          N Finset.univ (fun _ : Fin m => (0 : ℝ)) id id j field hgood).card_le
      · change (Selection.NSelection.selectFirstNFromSetTotalized
          N value candidates field).card ≤ N
        rw [Selection.NSelection.selectFirstNFromSetTotalized_empty_of_not_lowerFinite
          N value candidates field hgood]
        simp

/-- A first crossing below `-B` in a one-root tree within `horizon` steps.
The `first` clause records that every earlier vertex on the same surviving
lineage stays at or above the level. -/
def hasFirstPassageBelow {ι : Type*} [MeasurableSpace ι]
    [Countable ι] (horizon : ℕ) (B : ℝ) :
    Set (StepField ι ℝ) :=
  {ω | ∃ u : TreeNode ι, 0 < u.length ∧ u.length ≤ horizon ∧
      surviveAlong ω [] u ∧
      Spine.pathPotential realPotential ω u < -B ∧
      ∀ i : ℕ, i < u.length →
        -B ≤ Spine.pathPotential realPotential ω (u.take i)}

theorem measurableSet_hasFirstPassageBelow
    {ι : Type*} [MeasurableSpace ι] [Countable ι]
    (horizon : ℕ) (B : ℝ) :
    MeasurableSet (hasFirstPassageBelow (ι := ι) horizon B) := by
  classical
  rw [show hasFirstPassageBelow (ι := ι) horizon B =
      ⋃ u : TreeNode ι,
        {ω | 0 < u.length ∧ u.length ≤ horizon ∧ surviveAlong ω [] u ∧
          Spine.pathPotential realPotential ω u < -B ∧
          ∀ i : ℕ, i < u.length →
            -B ≤ Spine.pathPotential realPotential ω (u.take i)} by
    ext ω
    simp [hasFirstPassageBelow]]
  apply MeasurableSet.iUnion
  intro u
  have hsurvive : MeasurableSet {ω : StepField ι ℝ |
      surviveAlong ω [] u} := Spine.measurableSet_surviveAlong [] u
  have hend : MeasurableSet {ω : StepField ι ℝ |
      Spine.pathPotential realPotential ω u < -B} :=
    measurableSet_Iio.preimage (Spine.pathPotential_measurable realPotential [] u)
  have hprefix : MeasurableSet {ω : StepField ι ℝ |
      ∀ i : ℕ, i < u.length →
        -B ≤ Spine.pathPotential realPotential ω (u.take i)} := by
    rw [show {ω : StepField ι ℝ |
        ∀ i : ℕ, i < u.length →
          -B ≤ Spine.pathPotential realPotential ω (u.take i)} =
      ⋂ i : ℕ, {ω | i < u.length →
        -B ≤ Spine.pathPotential realPotential ω (u.take i)} by
      ext ω
      simp]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i < u.length
    · have hcoord : MeasurableSet {ω : StepField ι ℝ |
          -B ≤ Spine.pathPotential realPotential ω (u.take i)} :=
        measurableSet_Ici.preimage
          (Spine.pathPotential_measurable realPotential [] (u.take i))
      simpa [hi] using hcoord
    · simp [hi]
  have hlen : MeasurableSet {ω : StepField ι ℝ |
      0 < u.length ∧ u.length ≤ horizon} := by
    by_cases h : 0 < u.length ∧ u.length ≤ horizon <;> simp [h]
  rw [show {ω : StepField ι ℝ |
      0 < u.length ∧ u.length ≤ horizon ∧ surviveAlong ω [] u ∧
        Spine.pathPotential realPotential ω u < -B ∧
        ∀ i : ℕ, i < u.length →
          -B ≤ Spine.pathPotential realPotential ω (u.take i)} =
      {ω | 0 < u.length ∧ u.length ≤ horizon} ∩
        {ω | surviveAlong ω [] u} ∩
        {ω | Spine.pathPotential realPotential ω u < -B} ∩
        {ω | ∀ i : ℕ, i < u.length →
          -B ≤ Spine.pathPotential realPotential ω (u.take i)} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]]
  exact ((hlen.inter hsurvive).inter hend).inter hprefix

/-- A first-passage event is contained in the event that some generation
through the horizon has an endpoint below `-B`. -/
theorem hasFirstPassageBelow_subset_endpointHorizon
    {ι : Type*} [MeasurableSpace ι] [Countable ι]
    (horizon : ℕ) (B : ℝ) :
    hasFirstPassageBelow (ι := ι) horizon B ⊆
      hasEndpointBelowByHorizon realPotential horizon (-B) := by
  rintro ω ⟨u, hpos, hlen, hsurvive, hbelow, _⟩
  rw [hasEndpointBelowByHorizon]
  refine Set.mem_iUnion.2 ⟨⟨u.length, Nat.lt_succ_of_le hlen⟩, ?_⟩
  exact ⟨u, rfl, hsurvive, le_of_lt hbelow⟩

/-- The one-root probability of a first passage is bounded by summing the
one-generation many-to-one estimate over the available horizon. -/
theorem measure_hasFirstPassageBelow_le
    {ι : Type*} [MeasurableSpace ι] [Countable ι]
    (μ : Measure (Step ι ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (horizon : ℕ) (B : ℝ) :
    (stepFieldLaw μ) (hasFirstPassageBelow (ι := ι) horizon B) ≤
      (horizon + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-B)) := by
  calc
    (stepFieldLaw μ) (hasFirstPassageBelow (ι := ι) horizon B) ≤
        (stepFieldLaw μ)
          (hasEndpointBelowByHorizon realPotential horizon (-B)) :=
      measure_mono (hasFirstPassageBelow_subset_endpointHorizon horizon B)
    _ ≤ ∑ n : Fin (horizon + 1), ENNReal.ofReal (Real.exp (-B)) :=
      measure_hasEndpointBelowByHorizon_le_sum_exp realPotential μ hboundary
        horizon (-B)
    _ = (horizon + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-B)) := by
      simp [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- The random selected population is measurable in the domain filtration
revealing precisely generations below `j`. -/
theorem largeDrawdownPopulation_measurable (m N j : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable (largeDrawdownPopulation m N j) := by
  classical
  have hflow : Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) j]
      (largeDrawdownPopulation m N j) := by
    exact RootIndexed.selectedPopulationTotalized_adapted
      N Finset.univ (fun _ => (0 : ℝ)) id measurable_id id measurable_id j
  exact hflow.mono (RootIndexed.stepFiltration
    (Root := Fin m) (α := ℕ) (X := ℝ) |>.le j) le_rfl

/-- Domain-filtration measurability of the first-`N` population. -/
theorem largeDrawdownPopulation_adapted (m N j : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) j]
      (largeDrawdownPopulation m N j) := by
  classical
  exact RootIndexed.selectedPopulationTotalized_adapted
    N Finset.univ (fun _ => (0 : ℝ)) id measurable_id id measurable_id j

/-- At generation `j`, a first passage below `-B` from one of the
first-`N` selected particles during the remaining finite horizon.  Each
event in the union is a root-fiber event intersected with an event depending
only on that root's fresh descendant tree. -/
def selectedFirstPassageBelowAtGeneration (m N j H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  ⋃ p : GenerationAddress m j,
    {field | p.1 ∈ largeDrawdownPopulation m N j field ∧
      RootIndexed.subtreeStepFieldVector (generationAddressRoots m j) field p ∈
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
      (largeDrawdownPopulation m N j) :=
    largeDrawdownPopulation_adapted m N j
  have hmem : MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) j]
      {field | p.1 ∈ largeDrawdownPopulation m N j field} :=
    hpop (measurableSet_mem_finset p.1)
  have hfirst : MeasurableSet
      (hasFirstPassageBelow (ι := ℕ) (H - j) B) :=
    measurableSet_hasFirstPassageBelow (H - j) B
  have hvector : Measurable
      (RootIndexed.subtreeStepFieldVector (generationAddressRoots m j)) :=
    RootIndexed.subtreeStepFieldVector_measurable
      (X := ℝ) (generationAddressRoots m j)
  have hhit : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        RootIndexed.subtreeStepFieldVector
            (generationAddressRoots m j) field p ∈
          hasFirstPassageBelow (ι := ℕ) (H - j) B} :=
    hfirst.preimage ((measurable_pi_apply p).comp hvector)
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p.1 ∈ largeDrawdownPopulation m N j field ∧
        RootIndexed.subtreeStepFieldVector (generationAddressRoots m j)
          field p ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B} =
      {field | p.1 ∈ largeDrawdownPopulation m N j field} ∩
        {field | RootIndexed.subtreeStepFieldVector
          (generationAddressRoots m j) field p ∈
            hasFirstPassageBelow (ι := ℕ) (H - j) B} by
    ext field
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]]
  exact ((RootIndexed.stepFiltration
    (Root := Fin m) (α := ℕ) (X := ℝ) |>.le j) _ hmem).inter hhit

/-- The sum of the probabilities that each fixed generation-`j` address is
selected is at most `N`.  This is the random-finite-set decomposition: the
countable sum of membership indicators is exactly the cardinality of the
selected finset, pointwise. -/
theorem tsum_generationAddress_selected_le
    (m N j : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    ∑' p : GenerationAddress m j,
      (finiteRootStepFieldLaw μ m)
        {field | p.1 ∈ largeDrawdownPopulation m N j field} ≤ N := by
  classical
  let P := finiteRootStepFieldLaw μ m
  let A : GenerationAddress m j → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | p.1 ∈ largeDrawdownPopulation m N j field}
  let g : GenerationAddress m j → FiniteRootStepField m ℕ ℝ → ℝ≥0∞ :=
    fun p => (A p).indicator fun _ => 1
  have hA (p : GenerationAddress m j) : MeasurableSet (A p) := by
    have hpop := largeDrawdownPopulation_measurable m N j
    simpa [A] using hpop (measurableSet_mem_finset p.1)
  have hg (p : GenerationAddress m j) : Measurable (g p) :=
    measurable_const.indicator (hA p)
  have hsum (field : FiniteRootStepField m ℕ ℝ) :
      ∑' p : GenerationAddress m j, g p field =
        (largeDrawdownPopulation m N j field).card := by
    let pop := largeDrawdownPopulation m N j field
    let encode : {q : RootIndexed.TreeNode (Fin m) ℕ // q ∈ pop} ↪
        GenerationAddress m j :=
      ⟨fun q => ⟨q.1, RootIndexed.selectedPopulationTotalized_depth
          N Finset.univ (fun _ => (0 : ℝ)) id id j field q.1 q.2⟩,
        fun p q hpq => Subtype.ext
          (congrArg (fun z : GenerationAddress m j => z.1) hpq)⟩
    let selectedAddresses : Finset (GenerationAddress m j) :=
      pop.attach.map encode
    have hmem (p : GenerationAddress m j) :
        p ∈ selectedAddresses ↔ p.1 ∈ pop := by
      constructor
      · intro hp
        rcases Finset.mem_map.1 hp with ⟨q, hq, heq⟩
        have hv : q.1 = p.1 := congrArg Subtype.val heq
        rw [← hv]
        exact q.2
      · intro hp
        refine Finset.mem_map.2 ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, ?_⟩
        apply Subtype.ext
        rfl
    have htsum : ∑' p : GenerationAddress m j, g p field =
        ∑ p ∈ selectedAddresses, g p field := by
      apply tsum_eq_sum
      intro p hp
      have hnot : p.1 ∉ pop := fun h => hp (hmem p |>.2 h)
      have hnot' : p.1 ∉ largeDrawdownPopulation m N j field := by
        simpa [pop] using hnot
      simp [g, A, hnot']
    calc
      ∑' p : GenerationAddress m j, g p field =
          ∑ p ∈ selectedAddresses, g p field := htsum
      _ = selectedAddresses.card := by
        calc
          ∑ p ∈ selectedAddresses, g p field =
              ∑ p ∈ selectedAddresses, (1 : ℝ≥0∞) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hp' : p.1 ∈ pop := (hmem p).1 hp
            have hp'' : p.1 ∈ largeDrawdownPopulation m N j field := by
              simpa [pop] using hp'
            simp [g, A, hp'']
          _ = selectedAddresses.card := by simp
      _ = pop.card := by simp [selectedAddresses, encode]
  have hsumA :
      ∑' p : GenerationAddress m j, P (A p) =
        ∫⁻ field, (largeDrawdownPopulation m N j field).card ∂P := by
    calc
      ∑' p, P (A p) = ∑' p, ∫⁻ field, g p field ∂P := by
        apply tsum_congr
        intro p
        rw [lintegral_indicator_const (hA p)]
        simp [g]
      _ = ∫⁻ field, ∑' p, g p field ∂P := by
        symm
        exact lintegral_tsum (fun p => (hg p).aemeasurable)
      _ = ∫⁻ field, (largeDrawdownPopulation m N j field).card ∂P :=
        lintegral_congr hsum
  calc
    ∑' p : GenerationAddress m j, P (A p) =
        ∫⁻ field, (largeDrawdownPopulation m N j field).card ∂P := hsumA
    _ ≤ ∫⁻ _field, (N : ℝ≥0∞) ∂P := by
      apply lintegral_mono
      intro field
      change ((largeDrawdownPopulation m N j field).card : ℝ≥0∞) ≤
        (N : ℝ≥0∞)
      exact_mod_cast largeDrawdownPopulation_card_le m N j hmN field
    _ = N := by simp [P]

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
    fun p => {field | p.1 ∈ largeDrawdownPopulation m N j field}
  let E : GenerationAddress m j → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | p.1 ∈ largeDrawdownPopulation m N j field ∧
      RootIndexed.subtreeStepFieldVector (generationAddressRoots m j)
        field p ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B}
  let roots (p : GenerationAddress m j) : Unit → Fin m × TreeNode ℕ :=
    fun _ => (p.1.1, p.1.2)
  let freshEvent : Set (Unit → TreeNode ℕ → Step ℕ ℝ) :=
    {v | v () ∈ hasFirstPassageBelow (ι := ℕ) (H - j) B}
  have hA (p : GenerationAddress m j) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) j] (A p) := by
    have hpop := largeDrawdownPopulation_adapted m N j
    simpa [A] using hpop (measurableSet_mem_finset p.1)
  have hfresh : MeasurableSet
      (hasFirstPassageBelow (ι := ℕ) (H - j) B) :=
    measurableSet_hasFirstPassageBelow (H - j) B
  have hfreshEvent : MeasurableSet freshEvent := by
    exact hfresh.preimage (measurable_pi_apply ())
  have hfactor (p : GenerationAddress m j) :
      P (E p) = P (A p) *
        (stepFieldLaw μ)
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
          (stepFieldLaw μ)
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
      simp only [E, A, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_preimage]
      rfl
    change (RootIndexed.stepFieldLaw (Root := Fin m) μ) (E p) = _
    rw [hE, hfactor, hBprob]
  have hsumA :
      ∑' p : GenerationAddress m j, P (A p) ≤ N := by
    exact tsum_generationAddress_selected_le m N j hmN μ
  have hsingle :
      (stepFieldLaw μ)
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
          (stepFieldLaw μ)
            (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
      calc
        ∑' p : GenerationAddress m j, P (E p) =
            ∑' p : GenerationAddress m j,
              P (A p) * (stepFieldLaw μ)
                (hasFirstPassageBelow (ι := ℕ) (H - j) B) := by
          apply tsum_congr
          intro p
          exact hfactor p
        _ = (∑' p : GenerationAddress m j, P (A p)) *
              (stepFieldLaw μ)
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

/-- Every prefix of a selected address is selected at its own generation.
This is the ancestor-closure property needed to branch the first-`N`
population at the start of a witnessed drawdown. -/
theorem largeDrawdownPopulation_prefix_mem (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ largeDrawdownPopulation m N n field)
    (j : ℕ) (hjn : j ≤ n) :
    (p.1, p.2.take j) ∈ largeDrawdownPopulation m N j field := by
  classical
  induction n generalizing p j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      change p ∈ RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)) at hp
      change (p.1, p.2.take 0) ∈
        RootIndexed.initialPopulation (Finset.univ : Finset (Fin m))
      rw [RootIndexed.mem_initialPopulation_iff] at hp ⊢
      obtain ⟨r, hr, hpEq⟩ := hp
      subst p
      simp
  | succ n ih =>
      by_cases htop : j = n + 1
      · subst j
        have hdepth : p.2.length = n + 1 := by
          change p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field at hp
          exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field p hp
        have htake : p.2.take (n + 1) = p.2 :=
          (List.take_eq_self_iff p.2).2 (by omega)
        simpa [largeDrawdownPopulation, htake] using hp
      · have hjn' : j ≤ n := by omega
        have hchild :
            p ∈ RootIndexed.childrenAtGeneration n
              (largeDrawdownPopulation m N n field) field := by
          change p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ
            (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field at hp
          exact RootIndexed.selectedPopulationTotalized_succ_subset
            N Finset.univ (fun _ : Fin m => (0 : ℝ)) id id n field hp
        obtain ⟨q, hq, hqdepth, i, hi, rfl⟩ :=
          (RootIndexed.mem_childrenAtGeneration_iff n
            (largeDrawdownPopulation m N n field) field p).mp hchild
        have htake : (q.2 ++ [i]).take j = q.2.take j :=
          List.take_append_of_le_length (by simpa [hqdepth] using hjn')
        simpa [htake] using ih q hq j hjn'

/-- The local potential in the subtree rooted at `q` is the absolute
position difference `V(qv) - V(q)` in the original forest. -/
theorem subtreePathPotential_eq_position_sub (m : ℕ)
    (field : FiniteRootStepField m ℕ ℝ) (r : Fin m)
    (q v : TreeNode ℕ) :
    Spine.pathPotential realPotential
        (RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (r, q)) field ()) v =
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r (q ++ v) -
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r q := by
  have hpos := RootIndexed.position_subtreeStepFieldVector
    (initial := fun _ : Fin m => (0 : ℝ)) (d := id) field
    (fun _ : Unit => (r, q)) () v
  have hlocal :
      RootIndexed.position
          (RootIndexed.subtreeInitialPosition
            (fun _ : Fin m => (0 : ℝ)) id field
            (fun _ : Unit => (r, q))) id
          (RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (r, q)) field) () v =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r (q ++ v) :=
    hpos
  have hform :
      RootIndexed.position
          (RootIndexed.subtreeInitialPosition
            (fun _ : Fin m => (0 : ℝ)) id field
            (fun _ : Unit => (r, q))) id
          (RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (r, q)) field) () v =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field r q +
          Spine.pathPotential realPotential
            (RootIndexed.subtreeStepFieldVector
              (fun _ : Unit => (r, q)) field ()) v := by
    simp [RootIndexed.position, RootIndexed.subtreeInitialPosition,
      RootIndexed.displace, Spine.pathPotential,
      RootIndexed.subtreeStepFieldVector,
      Combinatorics.Branching.displaceWith, realPotential]
  rw [hform] at hlocal
  linarith

private theorem take_append_drop_take_eq {α : Type*} (u : List α)
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
      p ∈ largeDrawdownPopulation m N n.val field ∧
      ∃ j : ℕ, j < n.val ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1
            (p.2.take j) -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field p.1 p.2 > B}

/-- A large drawdown along a first-`N` selected address, recorded at its
first crossing.  The intermediate-prefix clause is the paper's first-crossing
normalization; the ancestor is recovered from the selected endpoint by
`largeDrawdownPopulation_prefix_mem`. -/
def firstNSelectedLargeDrawdown (m N H : ℕ) (B : ℝ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ n : Fin (H + 1), ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
      p ∈ largeDrawdownPopulation m N n.val field ∧
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
    simpa [largeDrawdownPopulation] using hp
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
  have hendpointMem : endpoint ∈ largeDrawdownPopulation m N k field := by
    exact largeDrawdownPopulation_prefix_mem m N n.val field p hp k (by omega)
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
    simpa [largeDrawdownPopulation] using hp
  have hdepth : p.2.length = n.val :=
    RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n.val field p hp'
  have hjdepth : j ≤ p.2.length := by omega
  have qmem :
      (p.1, p.2.take j) ∈ largeDrawdownPopulation m N j field :=
    largeDrawdownPopulation_prefix_mem m N n.val field p hp j (by omega)
  have hqdepth : (p.2.take j).length = j := by
    simp [List.length_take, min_eq_left hjdepth]
  let suffix : TreeNode ℕ := p.2.drop j
  have hsuffix : suffix.length = n.val - j := by
    simp [suffix, List.length_drop, min_eq_left hjdepth, hdepth]
  have hpos : 0 < suffix.length := by omega
  have hlen : suffix.length ≤ H - j := by omega
  have hsurvive : surviveAlong (field p.1) [] p.2 := by
    apply firstNSelectedPopulation_surviveAlong m N n.val field p
    simpa [largeDrawdownPopulation, firstNSelectedPopulation] using hp
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
    have h := subtreePathPotential_eq_position_sub m field p.1
      (p.2.take j) suffix
    simpa [suffix, List.take_append_drop] using h
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
        have h := subtreePathPotential_eq_position_sub m field p.1
          (p.2.take j) (suffix.take i)
        simpa [suffix] using h
      rw [hlocalI]
      linarith
  let q : RootIndexed.TreeNode (Fin m) ℕ := (p.1, p.2.take j)
  let q' : GenerationAddress m j := ⟨q, hqdepth⟩
  have hvectorEq :
      RootIndexed.subtreeStepFieldVector
          (generationAddressRoots m j) field q' =
        RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (p.1, p.2.take j)) field () := by
    funext w
    rfl
  have hjH : j < H := by omega
  have hlocalEvent :
      RootIndexed.subtreeStepFieldVector
          (generationAddressRoots m j) field q' ∈
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
  change q ∈ largeDrawdownPopulation m N j field ∧ _
  exact ⟨by simpa [q] using qmem, hlocalEvent⟩

/-- The thesis's first-`N` large-drawdown witness is bounded by the
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

end ProbabilityTheory.BranchingRandomWalk.Analytic
