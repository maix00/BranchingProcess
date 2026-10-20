/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingProcess.Offspring.Count
import Mathlib.Probability.BorelCantelli
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Address
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Nonempty
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.Independence.Finite
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Population

/-!
# Selected marks along an initially smaller population

The proof-chain declarations are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialActiveAddress`:
  the selected address used to sample an offspring mark at generation $n$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialActiveMark`:
  the offspring mark sampled at that address.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.smallInitialActiveSplitEvent`:
  the event that the sampled mark has at least two children.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.ae_frequently_smallInitialActiveSplitEvent`:
  under expected offspring count greater than one, these selected-mark split
  events occur infinitely often almost surely.

These declarations support the capacity-hitting argument and are kept in the
internal `Lemmas/CapacityHit/` proof family.

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

private lemma smallInitialActiveAddress_depth (m N n : ℕ) (hm : 0 < m)
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

private lemma measurable_smallInitialActiveAddress (m N n : ℕ) (hm : 0 < m)
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

private lemma smallInitialActiveAddress_fiber_measurable
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

private lemma smallInitialFutureRoots_countable (m N n : ℕ) (hm : 0 < m)
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

private lemma smallInitialFutureRoots_fiber_measurable
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

private lemma smallInitialFutureRoots_depth (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ field i, (smallInitialFutureRoots m N n hm field i).2.length = n := by
  intro field i
  exact smallInitialActiveAddress_depth m N n hm field

private lemma smallInitialFutureRoots_injective (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Function.Injective (smallInitialFutureRoots m N n hm field) := by
  intro i j _
  exact Subsingleton.elim _ _

/-- The actual adaptive mark is measurable when generation `n` is revealed. -/
private lemma measurable_smallInitialActiveMark_at_succ
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
  {field | 2 ≤ Step.childCount (smallInitialActiveMark m N n hm field)}

private lemma measurableSet_smallInitialActiveSplitEvent
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (Fin m × TreeNode ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    MeasurableSet (smallInitialActiveSplitEvent m N n hm) := by
  change MeasurableSet
    (smallInitialActiveMark m N n hm ⁻¹' offspringSplitSet)
  exact measurableSet_offspringSplitSet.preimage
    ((measurable_smallInitialActiveMark_at_succ m N n hm).mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1)) le_rfl)

/-- The address selected from the actual generation-`n` population has an
offspring mark with the original law, independent of the revealed past.
The fallback address is only reached if the selected population is empty;
its depth is still `n`, so the probabilistic statement is valid on the full
sample space. -/
private lemma smallInitialActiveMark_independent_and_law
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
private lemma smallInitialActiveMark_iIndepFun
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

/-- Under the supercriticality hypothesis, the actual predictable
selected address has a strictly positive one-generation chance to split. -/
private lemma smallInitialActiveMark_split_measure_pos
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
  have hsplit :=
    measure_pos_childCount_ge_two_of_expectedChildCount_gt_one μ hsupercritical
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
infinitely many generations almost surely under the supercriticality
assumption. This uses the adaptive fresh-mark law, rather than a fixed-root
trial schedule. -/
lemma ae_frequently_smallInitialActiveSplitEvent
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
    exact ⟨offspringSplitSet, measurableSet_offspringSplitSet, rfl⟩
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
  have hsplit :=
    measure_pos_childCount_ge_two_of_expectedChildCount_gt_one μ hsupercritical
  have hprob : ∀ n, ν (events n) = μ offspringSplitSet := by
    intro n
    have hmark := smallInitialActiveMark_independent_and_law m N n hm μ
    have hmarkMeas : Measurable (smallInitialActiveMark m N n hm) := by
      exact (measurable_smallInitialActiveMark_at_succ m N n hm).mono
        ((RootIndexed.stepFiltration
          (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1)) le_rfl
    change ν ((smallInitialActiveMark m N n hm) ⁻¹' offspringSplitSet) =
      μ offspringSplitSet
    rw [← Measure.map_apply hmarkMeas measurableSet_offspringSplitSet, hmark.2]
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


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
