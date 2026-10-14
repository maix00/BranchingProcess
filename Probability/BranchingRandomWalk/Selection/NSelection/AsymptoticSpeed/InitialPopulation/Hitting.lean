/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.EndpointMinimumAddress
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Nonempty
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.Independence.Finite

/-!
# Hitting the capacity from a smaller initial population

The selected address used below is chosen from the actual generation-`n`
population. Its offspring mark is therefore an adaptive, predictable sample
from the root-indexed environment. The fresh-mark law and positive split
probability combine with a pathwise cardinality argument to prove that the
actual selected population reaches capacity in finite time almost surely.
-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.UlamHarris
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

attribute [local instance] Classical.propDecidable Classical.decEq

/-- One offspring configuration splits when it has at least two children. -/
def offspringSplitSet : Set (Step ℕ ℝ) :=
  {ξ | 2 ≤ Step.childCount ξ}

private theorem offspringSplitSet_eq_nontrivialSupport :
    offspringSplitSet = nontrivialSupport := by
  ext ξ
  change 2 ≤ (support ξ).encard ↔
    ∃ i j, i ≠ j ∧ survive ξ i ∧ survive ξ j
  constructor
  · intro hcount
    have hcard : 1 < (support ξ).encard :=
      lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) hcount
    obtain ⟨i, j, hi, hj, hij⟩ := Set.one_lt_encard_iff.mp hcard
    exact ⟨i, j, hij, by simpa [support] using hi,
      by simpa [support] using hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hcard : 1 < (support ξ).encard :=
      Set.one_lt_encard_iff.mpr
        ⟨i, j, by simpa [support] using hi,
          by simpa [support] using hj, hij⟩
    cases hencard : (support ξ).encard with
    | top => simp
    | coe k =>
      have hk : 1 < k := by simpa [hencard] using hcard
      have hk' : 2 ≤ k := by omega
      simpa [hencard] using hk'

private theorem measurable_offspringSplitSet : MeasurableSet offspringSplitSet := by
  rw [offspringSplitSet_eq_nontrivialSupport]
  exact nontrivialSupport_measurable

/-- The actual root-indexed selected population from `m` initial roots,
viewed at generation `n`. -/
noncomputable def smallInitialPopulation (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin m)) (fun _ => 0) id id n field

/-- A predictable representative of the actual selected population. The
endpoint-minimizing address is used only to make the choice measurable; any
selected address would have the same fresh-mark law. -/
noncomputable def smallInitialActiveAddress (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    FiniteRootStepField m ℕ ℝ → RootIndexed.TreeNode (Fin m) ℕ := fun field =>
  if _hpop : (Tail.firstNSelectedPopulation m N n field).Nonempty then
    Tail.firstNSelectedEndpointMinAddress m N n hm field
  else
    ((⟨0, hm⟩ : Fin m), List.replicate n 0)

theorem smallInitialActiveAddress_depth (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    (smallInitialActiveAddress m N n hm field).2.length = n := by
  classical
  by_cases hpop : (Tail.firstNSelectedPopulation m N n field).Nonempty
  · have hmem := (Tail.firstNSelectedEndpointMinAddress_mem_and_min
      m N n hm field hpop).1
    have hmem' : smallInitialActiveAddress m N n hm field ∈
        Tail.firstNSelectedPopulation m N n field := by
      simpa [smallInitialActiveAddress, hpop] using hmem
    exact Tail.firstNSelectedPopulation_depth m N n field _ hmem'
  · simp [smallInitialActiveAddress, hpop]

theorem measurable_smallInitialActiveAddress (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (smallInitialActiveAddress m N n hm) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  have hpopulation : Measurable[F n]
      (Tail.firstNSelectedPopulation m N n) := by
    change Measurable[F n]
      (fun field => RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field)
    exact RootIndexed.selectedPopulationTotalized_adapted N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id measurable_id id measurable_id n
  have hnonempty : MeasurableSet[F n]
      {field | (Tail.firstNSelectedPopulation m N n field).Nonempty} := by
    rw [show {field | (Tail.firstNSelectedPopulation m N n field).Nonempty} =
      {field | Tail.firstNSelectedPopulation m N n field ≠ ∅} by
        ext field
        simp [Finset.nonempty_iff_ne_empty]]
    exact (hpopulation (measurableSet_singleton
      (∅ : Finset (RootIndexed.TreeNode (Fin m) ℕ)))).compl
  exact Measurable.ite hnonempty
    (Tail.measurable_firstNSelectedEndpointMinAddress m N n hm)
    measurable_const

private theorem smallInitialActiveAddress_fiber_measurable
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      {field | smallInitialActiveAddress m N n hm field = p} := by
  intro p
  exact measurable_smallInitialActiveAddress m N n hm
    (measurableSet_singleton p)

/-- The mark at the actual selected address in generation `n`. -/
noncomputable def smallInitialActiveMark (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) : Step ℕ ℝ :=
  field (smallInitialActiveAddress m N n hm field).1
    (smallInitialActiveAddress m N n hm field).2

private noncomputable def smallInitialFutureRoots (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    FiniteRootStepField m ℕ ℝ → PUnit.{1} → Fin m × TreeNode ℕ :=
  fun field _ => smallInitialActiveAddress m N n hm field

private theorem smallInitialFutureRoots_countable (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    (Set.range (smallInitialFutureRoots m N n hm)).Countable := by
  have haddr : (Set.range (smallInitialActiveAddress m N n hm)).Countable :=
    Set.to_countable _
  have hrange : Set.range (smallInitialFutureRoots m N n hm) =
      (fun p : Fin m × TreeNode ℕ => fun _ : PUnit.{1} => p) ''
        Set.range (smallInitialActiveAddress m N n hm) := by
    ext roots
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨field, rfl⟩
      exact ⟨smallInitialActiveAddress m N n hm field,
        ⟨field, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨field, rfl⟩, rfl⟩
      exact ⟨field, rfl⟩
  rw [hrange]
  exact haddr.image _

private theorem smallInitialFutureRoots_fiber_measurable
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      {field | smallInitialFutureRoots m N n hm field = roots} := by
  have haddr := measurable_smallInitialActiveAddress m N n hm
  intro roots
  let p := roots PUnit.unit
  have hroots : roots = fun _ : PUnit.{1} => p := by
    funext i
    have hi : i = PUnit.unit := Subsingleton.elim _ _
    subst i
    rfl
  have hset : {field |
      smallInitialFutureRoots m N n hm field = roots} =
      {field | smallInitialActiveAddress m N n hm field = p} := by
    ext field
    rw [hroots]
    change ((fun _ : PUnit.{1} =>
      smallInitialActiveAddress m N n hm field) =
        (fun _ : PUnit.{1} => p)) ↔
      smallInitialActiveAddress m N n hm field = p
    constructor
    · intro h
      exact congrArg (fun f => f PUnit.unit) h
    · intro h
      funext i
      have hi : i = PUnit.unit := Subsingleton.elim _ _
      simpa [hi] using h
  rw [hset]
  exact haddr (measurableSet_singleton p)

private theorem smallInitialFutureRoots_depth (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ field i, (smallInitialFutureRoots m N n hm field i).2.length = n := by
  intro field i
  exact smallInitialActiveAddress_depth m N n hm field

private theorem smallInitialFutureRoots_injective (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Function.Injective (smallInitialFutureRoots m N n hm field) := by
  intro i j _
  exact Subsingleton.elim _ _

/-- The actual adaptive mark is measurable when generation `n` is revealed. -/
theorem measurable_smallInitialActiveMark_at_succ
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
      (smallInitialActiveMark m N n hm) := by
  change Measurable[RootIndexed.stepFiltration
    (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
    (fun field => field
      (smallInitialActiveAddress m N n hm field).1
      (smallInitialActiveAddress m N n hm field).2)
  exact RootIndexed.selectedStep_measurable
    (smallInitialActiveAddress m N n hm)
    (fun p => (RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ)).mono (Nat.le_succ n) _
        (smallInitialActiveAddress_fiber_measurable m N n hm p))
    (fun field => by
      rw [smallInitialActiveAddress_depth]
      exact Nat.lt_succ_self n)
    (Set.to_countable _)

/-- The split event for the parent chosen from the actual selected
generation. -/
def smallInitialActiveSplitEvent (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | field ∈ offspringSplitSet.preimage
    (smallInitialActiveMark m N n hm)}

theorem measurableSet_smallInitialActiveSplitEvent
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    MeasurableSet (smallInitialActiveSplitEvent m N n hm) := by
  change MeasurableSet
    (smallInitialActiveMark m N n hm ⁻¹' offspringSplitSet)
  exact measurable_offspringSplitSet.preimage
    ((measurable_smallInitialActiveMark_at_succ m N n hm).mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1)) le_rfl)

/-- The address selected from the actual generation-`n` population has an
offspring mark with the original law, independent of the revealed past.
The fallback address is only reached if the selected population is empty;
its depth is still `n`, so the probabilistic statement is valid on the full
sample space. -/
theorem smallInitialActiveMark_independent_and_law
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    Indep (RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n)
      (MeasurableSpace.comap (smallInitialActiveMark m N n hm) inferInstance)
      (finiteRootStepFieldLaw μ m) ∧
      (finiteRootStepFieldLaw μ m).map
        (smallInitialActiveMark m N n hm) = μ := by
  let chosen := smallInitialFutureRoots m N n hm
  let fresh := RootIndexed.selectedSubtreeStepFieldVector chosen
  have hcount := smallInitialFutureRoots_countable m N n hm
  have hfiber := smallInitialFutureRoots_fiber_measurable m N n hm
  have hdepth := smallInitialFutureRoots_depth m N n hm
  have hinj := smallInitialFutureRoots_injective m N n hm
  have hind := RootIndexed.selectedSubtreeStepFieldVector_independent
    μ chosen hcount hfiber hdepth hinj
  have hselectedMeas : Measurable fresh :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable chosen hcount hfiber
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} ℕ ℝ => field PUnit.unit []) :=
    (measurable_pi_apply ([] : TreeNode ℕ)).comp
      (measurable_pi_apply PUnit.unit)
  have hmark : smallInitialActiveMark m N n hm = fun field =>
      fresh field PUnit.unit [] := by
    funext field
    simp [smallInitialActiveMark, fresh, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector, smallInitialFutureRoots]
  constructor
  · rw [hmark]
    apply indep_of_indep_of_le_right hind
    exact (heval.comp (Measurable.of_comap_le le_rfl)).comap_le
  · rw [hmark]
    change (finiteRootStepFieldLaw μ m).map
        ((fun field : RootIndexed.StepField PUnit.{1} ℕ ℝ =>
          field PUnit.unit []) ∘ fresh) = μ
    rw [← Measure.map_map heval hselectedMeas,
      RootIndexed.selectedSubtreeStepFieldVector_law μ chosen
        hcount hfiber hdepth hinj]
    exact RootIndexed.stepFieldLaw_coordinate_marginal
      (Root := PUnit.{1}) (α := ℕ) μ PUnit.unit []

/-- The adaptive offspring marks read along the actual selected population
form an i.i.d. sequence. At time `n`, the chosen address depends only on the
previous generations, so the new mark is independent of the finite vector of
earlier sampled marks. -/
theorem smallInitialActiveMark_iIndepFun
    (m N : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    iIndepFun (smallInitialActiveMark m N · hm)
      (finiteRootStepFieldLaw μ m) := by
  classical
  let P := finiteRootStepFieldLaw μ m
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  have hprefix : ∀ k,
      iIndepFun (fun i : Fin k => smallInitialActiveMark m N i.1 hm) P := by
    intro k
    induction k with
    | zero => exact iIndepFun.of_subsingleton
    | succ k ih =>
        apply (iIndepFun.finSucc (μ := P))
        · intro i
          have hmark := measurable_smallInitialActiveMark_at_succ
            m N i.1 hm
          have hmarkAmbient : Measurable
              (smallInitialActiveMark m N i.1 hm) :=
            hmark.mono (F.le (i.1 + 1)) le_rfl
          exact ⟨smallInitialActiveMark m N i.1 hm, hmarkAmbient,
            ae_eq_refl _⟩
        · simpa using ih
        · let past : FiniteRootStepField m ℕ ℝ → Fin k → Step ℕ ℝ :=
            fun field i => smallInitialActiveMark m N i.1 hm field
          have hpast : Measurable[F k] past := by
            apply (@measurable_pi_iff
              (FiniteRootStepField m ℕ ℝ) (Fin k) (fun _ => Step ℕ ℝ)
              (F k) (fun _ => inferInstance) past).2
            intro i
            have hmark := measurable_smallInitialActiveMark_at_succ
              m N i.1 hm
            have hle : i.1 + 1 ≤ k := by omega
            exact hmark.mono (F.mono hle) le_rfl
          have hind :=
            (smallInitialActiveMark_independent_and_law m N k hm μ).1
          have hlast : IndepFun past
              (smallInitialActiveMark m N k hm) P :=
            (IndepFun_iff_Indep past
              (smallInitialActiveMark m N k hm) P).2
                (indep_of_indep_of_le_left hind hpast.comap_le)
          simpa [past] using hlast
  rw [iIndepFun_iff_finset]
  intro s
  let k := s.sup id + 1
  have hbound : ∀ i : s, i.1 < k := by
    intro i
    dsimp [k]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : ℕ => x) i.2)
  let embed : s → Fin k := fun i => ⟨i.1, hbound i⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hsmall := hprefix k
  have hsmall' := hsmall.precomp hembed
  have heq : (fun i : s => smallInitialActiveMark m N i.1 hm) =
      fun i => (fun j : Fin k => smallInitialActiveMark m N j.1 hm)
        (embed i) := by
    funext i
    rfl
  change iIndepFun (fun i : s => smallInitialActiveMark m N i.1 hm) P
  rw [heq]
  exact hsmall'

/-- Under the paper's supercriticality hypothesis, the actual predictable
selected address has a strictly positive one-generation chance to split. -/
theorem smallInitialActiveMark_split_measure_pos
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    0 < finiteRootStepFieldLaw μ m
      {field | 2 ≤ Step.childCount (smallInitialActiveMark m N n hm field)} := by
  have hsplit := positive_raw_measure_childCount_ge_two μ hsupercritical
  have hmark := smallInitialActiveMark_independent_and_law m N n hm μ
  let split : Set (Step ℕ ℝ) := {ξ | 2 ≤ Step.childCount ξ}
  have hsplitEq : split = nontrivialSupport := by
    ext ξ
    change 2 ≤ (support ξ).encard ↔
      ∃ i j, i ≠ j ∧ survive ξ i ∧ survive ξ j
    constructor
    · intro hcount
      have hcard : 1 < (support ξ).encard :=
        lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) hcount
      obtain ⟨i, j, hi, hj, hij⟩ := Set.one_lt_encard_iff.mp hcard
      exact ⟨i, j, hij, by simpa [support] using hi,
        by simpa [support] using hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      have hcard : 1 < (support ξ).encard :=
        Set.one_lt_encard_iff.mpr
          ⟨i, j, by simpa [support] using hi,
            by simpa [support] using hj, hij⟩
      cases hencard : (support ξ).encard with
      | top => simp
      | coe k =>
        have hk : 1 < k := by simpa [hencard] using hcard
        have hk' : 2 ≤ k := by omega
        simpa [hencard] using hk'
  have hmeas : MeasurableSet split := by
    rw [hsplitEq]
    exact nontrivialSupport_measurable
  let chosen := smallInitialFutureRoots m N n hm
  let fresh := RootIndexed.selectedSubtreeStepFieldVector chosen
  have hselectedMeas : Measurable fresh :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable chosen
      (smallInitialFutureRoots_countable m N n hm)
      (smallInitialFutureRoots_fiber_measurable m N n hm)
  have heval : Measurable
      (fun field : RootIndexed.StepField PUnit.{1} ℕ ℝ => field PUnit.unit []) :=
    (measurable_pi_apply ([] : TreeNode ℕ)).comp
      (measurable_pi_apply PUnit.unit)
  have hmarkEq : smallInitialActiveMark m N n hm = fun field =>
      (fresh field PUnit.unit []) := by
    funext field
    simp [smallInitialActiveMark, fresh, chosen,
      RootIndexed.selectedSubtreeStepFieldVector,
      RootIndexed.subtreeStepFieldVector, smallInitialFutureRoots]
  have hmarkMeas : Measurable (smallInitialActiveMark m N n hm) := by
    rw [hmarkEq]
    exact heval.comp hselectedMeas
  have heq : finiteRootStepFieldLaw μ m
      {field | 2 ≤ Step.childCount (smallInitialActiveMark m N n hm field)} =
      μ split := by
    change finiteRootStepFieldLaw μ m
        ((smallInitialActiveMark m N n hm) ⁻¹' split) = μ split
    rw [← Measure.map_apply hmarkMeas hmeas, hmark.2]
  rw [heq]
  exact hsplit

/-- The actual selected population's predictable active address splits at
infinitely many generations almost surely under the paper's supercriticality
assumption. This uses the adaptive fresh-mark law, rather than a fixed-root
trial schedule. -/
theorem ae_frequently_smallInitialActiveSplitEvent
    (m N : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∃ᶠ n in atTop, field ∈ smallInitialActiveSplitEvent m N n hm := by
  let ν := finiteRootStepFieldLaw μ m
  let events : ℕ → Set (FiniteRootStepField m ℕ ℝ) :=
    fun n => smallInitialActiveSplitEvent m N n hm
  let coordinate : ℕ → MeasurableSpace (FiniteRootStepField m ℕ ℝ) :=
    fun n => MeasurableSpace.comap
      (smallInitialActiveMark m N n hm) inferInstance
  have hcoordinateIndep : iIndep coordinate ν := by
    apply (iIndepFun_iff_iIndep
      (fun _ : ℕ => (inferInstance : MeasurableSpace (Step ℕ ℝ)))
      (fun (n : ℕ) (field : FiniteRootStepField m ℕ ℝ) =>
        smallInitialActiveMark m N n hm field) ν).mp
    exact smallInitialActiveMark_iIndepFun m N hm μ
  have heventMeasurable : ∀ n, MeasurableSet[coordinate n] (events n) := by
    intro n
    change MeasurableSet[
      MeasurableSpace.comap (smallInitialActiveMark m N n hm) inferInstance]
      ((smallInitialActiveMark m N n hm) ⁻¹' offspringSplitSet)
    exact ⟨offspringSplitSet, measurable_offspringSplitSet, rfl⟩
  have heventsMeasurable : ∀ n, MeasurableSet (events n) := by
    intro n
    exact measurableSet_smallInitialActiveSplitEvent m N n hm
  have heventsIndep : iIndepSet events ν := by
    rw [iIndepSet_iff_iIndep]
    apply iIndep_of_iIndep_of_le hcoordinateIndep
    intro n
    exact MeasurableSpace.generateFrom_le fun s hs => by
      have hs' : s = events n := by simpa using hs
      rw [hs']
      exact heventMeasurable n
  have hsplit := positive_raw_measure_childCount_ge_two μ hsupercritical
  have hprob : ∀ n, ν (events n) = μ offspringSplitSet := by
    intro n
    have hmark := smallInitialActiveMark_independent_and_law m N n hm μ
    have hmarkMeas : Measurable (smallInitialActiveMark m N n hm) := by
      exact (measurable_smallInitialActiveMark_at_succ m N n hm).mono
        ((RootIndexed.stepFiltration
          (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1)) le_rfl
    change ν ((smallInitialActiveMark m N n hm) ⁻¹' offspringSplitSet) =
      μ offspringSplitSet
    rw [← Measure.map_apply hmarkMeas measurable_offspringSplitSet, hmark.2]
  have hsum : (∑' n : ℕ, ν (events n)) = ∞ := by
    rw [show (∑' n : ℕ, ν (events n)) =
      ∑' _n : ℕ, μ offspringSplitSet by
        exact tsum_congr fun n => hprob n]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hsplit.ne'
  have hBC := ProbabilityTheory.measure_limsup_eq_one
    heventsMeasurable heventsIndep hsum
  have hlimsupMeasurable : MeasurableSet (Filter.limsup events atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact MeasurableSet.iInter (fun n =>
      MeasurableSet.iUnion (fun k => heventsMeasurable (k + n)))
  have hae : ∀ᵐ field ∂ν, field ∈ Filter.limsup events atTop :=
    (ae_mem_iff_measure_eq hlimsupMeasurable.nullMeasurableSet).2 (by
      simpa using hBC)
  filter_upwards [hae] with field hfield
  simpa [events, Filter.mem_limsup_iff_frequently_mem] using hfield

variable {m : ℕ}

private noncomputable def smallInitialOneChildSlot
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i)
    (p : {p // p ∈ parents}) : ℕ :=
  Classical.choose (hchildren p.1 p.2)

private theorem smallInitialOneChildSlot_survives
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

private theorem smallInitialOneChildImage_injective
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

private theorem smallInitialOneChildImage_card
    (parents : Finset (RootIndexed.TreeNode (Fin m) ℕ))
    (field : FiniteRootStepField m ℕ ℝ)
    (hchildren : ∀ p ∈ parents,
      ∃ i : ℕ, survive (field p.1 p.2) i) :
    (smallInitialOneChildImage parents field hchildren).card = parents.card := by
  classical
  simp [smallInitialOneChildImage,
    Finset.card_image_of_injective _
      (smallInitialOneChildImage_injective parents field hchildren)]

private theorem smallInitialOneChildImage_subset
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

private theorem smallInitialFirstN_card_ge
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

private theorem smallInitialFirstN_card_gt_of_split
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

/-- Starting from any nonempty population of size at most N, the actual
root-indexed N-selection population reaches size N in finite time almost
surely. The only offspring assumptions are supercriticality and almost-sure
nonemptiness; boundary normalization is the existing admissibility hypothesis
for the selected process. -/
theorem finiteRootStepFieldLaw_ae_smallInitialPopulation_hits_capacity
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∃ n, (smallInitialPopulation m N n field).card = N := by
  have hN : 0 < N := lt_of_lt_of_le hm hmN
  have hgoodAE := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hboundary N Finset.univ (fun _ : Fin m => (0 : ℝ))
  have hpopulationAE := Tail.finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    m N hm hN μ hboundary hnonempty
  have hmarksAE := finiteRootStepFieldLaw_all_nonempty μ hnonempty m
  have hsplitAE := ae_frequently_smallInitialActiveSplitEvent
    m N hm μ hsupercritical
  filter_upwards [hgoodAE, hpopulationAE, hmarksAE, hsplitAE]
    with field hgood hpopulation hmarks hsplit
  let populationSize : ℕ → ℕ := fun n =>
    (smallInitialPopulation m N n field).card
  let split : ℕ → Prop := fun n =>
    field ∈ smallInitialActiveSplitEvent m N n hm
  have hinitial : 0 < populationSize 0 := by
    simp [populationSize, smallInitialPopulation,
      RootIndexed.selectedPopulationTotalized,
      RootIndexed.initialPopulation_card]
    exact hm
  have hcapacity : ∀ n, populationSize n ≤ N := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [populationSize, smallInitialPopulation,
        RootIndexed.selectedPopulationTotalized,
        RootIndexed.initialPopulation_card]
      exact hmN
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hfirst := hgood k
      change IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (k + 1) field)
        (RootIndexed.childrenAtGeneration k
          (smallInitialPopulation m N k field) field)
        (smallInitialPopulation m N (k + 1) field) at hfirst
      simpa [populationSize, smallInitialPopulation] using hfirst.card_le
  have hmonotone : ∀ n, populationSize n ≤ populationSize (n + 1) := by
    intro n
    let parents := smallInitialPopulation m N n field
    let selected := smallInitialPopulation m N (n + 1) field
    let value := RootIndexed.observedPositionAtGeneration
      (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field
    have hfirst : IsFirstNBy N value
        (RootIndexed.childrenAtGeneration n parents field) selected := by
      simpa [parents, selected, value, smallInitialPopulation] using hgood n
    have hdepth : ∀ p ∈ parents, p.2.length = n := by
      intro p hp
      exact Tail.firstNSelectedPopulation_depth m N n field p
        (by simpa [parents, smallInitialPopulation,
          Tail.firstNSelectedPopulation] using hp)
    have hchildren : ∀ p ∈ parents,
        ∃ i : ℕ, survive (field p.1 p.2) i := by
      intro p hp
      exact hmarks p.1 p.2
    have hparentsCapacity : parents.card ≤ N := by
      simpa [parents, populationSize] using hcapacity n
    have hle := smallInitialFirstN_card_ge N n parents field value selected
      hfirst hdepth hchildren hparentsCapacity
    simpa [parents, selected, populationSize] using hle
  have hgrowth : ∀ n, 0 < populationSize n → populationSize n < N →
      split n → populationSize n < populationSize (n + 1) := by
    intro n hpositive hsmall hsplitn
    let parents := smallInitialPopulation m N n field
    let selected := smallInitialPopulation m N (n + 1) field
    let value := RootIndexed.observedPositionAtGeneration
      (fun _ : Fin m => (0 : ℝ)) id id (n + 1) field
    have hfirst : IsFirstNBy N value
        (RootIndexed.childrenAtGeneration n parents field) selected := by
      simpa [parents, selected, value, smallInitialPopulation] using hgood n
    have hdepth : ∀ p ∈ parents, p.2.length = n := by
      intro p hp
      exact Tail.firstNSelectedPopulation_depth m N n field p
        (by simpa [parents, smallInitialPopulation,
          Tail.firstNSelectedPopulation] using hp)
    have hchildren : ∀ p ∈ parents,
        ∃ i : ℕ, survive (field p.1 p.2) i := by
      intro p hp
      exact hmarks p.1 p.2
    have hchosen : smallInitialActiveAddress m N n hm field ∈ parents := by
      have hnonempty := hpopulation n
      have hnonempty' : (Tail.firstNSelectedPopulation m N n field).Nonempty := by
        simpa [Tail.firstNSelectedPopulation] using hnonempty
      have hmem : smallInitialActiveAddress m N n hm field ∈
          Tail.firstNSelectedPopulation m N n field := by
        dsimp [smallInitialActiveAddress]
        rw [ite_eq_left hnonempty']
        exact (Tail.firstNSelectedEndpointMinAddress_mem_and_min m N n hm field
          hnonempty').1
      simpa [parents, smallInitialPopulation,
        Tail.firstNSelectedPopulation] using hmem
    have hsplit' : 2 ≤ Step.childCount
        (field (smallInitialActiveAddress m N n hm field).1
          (smallInitialActiveAddress m N n hm field).2) := by
      change field ∈ smallInitialActiveSplitEvent m N n hm at hsplitn
      simpa [smallInitialActiveSplitEvent, smallInitialActiveMark,
        offspringSplitSet] using hsplitn
    have hparentsSmall : parents.card < N := by
      simpa [parents, populationSize] using hsmall
    have hlt := smallInitialFirstN_card_gt_of_split N n hm parents field
      value selected hfirst hdepth hchildren hchosen hsplit' hparentsSmall
    simpa [parents, selected, populationSize] using hlt
  have hfrequently : ∃ᶠ n in atTop, split n := by
    simpa [split] using hsplit
  obtain ⟨n, hn⟩ := exists_eq_capacity_of_frequently_growing
    populationSize split hinitial hcapacity hmonotone hgrowth hfrequently
  exact ⟨n, hn⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
