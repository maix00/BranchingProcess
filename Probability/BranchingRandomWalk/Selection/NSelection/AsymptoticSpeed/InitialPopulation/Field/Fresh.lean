/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Hitting
import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.InitialPopulation.Trajectory.Population
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization
import Probability.Process.HittingTime.Declarations

/-!
# Fresh descendants at the capacity-hitting time

The actual smaller-start selected population reaches capacity at a stopping
generation. This file records that stopping time and prepares the selected
population's descendant field for the existing stopped-subtree factorization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The actual first-`N` selected population from `m` roots has reached
capacity at generation `n`. -/
def smallInitialPopulationAtCapacity (m N : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] (n : ℕ) :
    Set (FiniteRootStepField m ℕ ℝ) :=
  {field | (smallInitialPopulation m N n field).card = N}

/-- The first generation at which the actual smaller-start selected
population reaches capacity, or `⊤` if it never does. -/
noncomputable def smallInitialPopulationCapacityTime (m N : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    FiniteRootStepField m ℕ ℝ → WithTop ℕ :=
  ProbabilityTheory.firstDeclaredSuccess
    (smallInitialPopulationAtCapacity m N)

theorem measurableSet_smallInitialPopulationAtCapacity
    (m N n : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (smallInitialPopulationAtCapacity m N n) := by
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  have hpopulation : Measurable[F n] (smallInitialPopulation m N n) := by
    change Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (smallInitialPopulation m N n)
    exact RootIndexed.selectedPopulationTotalized_adapted
        N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
        measurable_id id measurable_id n
  have hcard : Measurable[F n]
      (fun field => (smallInitialPopulation m N n field).card) :=
    (measurable_of_countable fun s : Finset (RootIndexed.TreeNode (Fin m) ℕ) =>
      s.card).comp hpopulation
  change MeasurableSet[F n]
    {field | (smallInitialPopulation m N n field).card = N}
  exact hcard (measurableSet_singleton N)

theorem smallInitialPopulationCapacityTime_isStoppingTime
    (m N : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ))
      (smallInitialPopulationCapacityTime m N) := by
  exact ProbabilityTheory.firstDeclaredSuccess_isStoppingTime
    (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ))
    (smallInitialPopulationAtCapacity m N)
    (fun n => measurableSet_smallInitialPopulationAtCapacity m N n)

theorem smallInitialPopulationCapacityTime_eq_iff
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    smallInitialPopulationCapacityTime m N field = (n : WithTop ℕ) ↔
      field ∈ smallInitialPopulationAtCapacity m N n ∧
        ∀ j < n, field ∉ smallInitialPopulationAtCapacity m N j := by
  exact ProbabilityTheory.firstDeclaredSuccess_eq_iff
    (smallInitialPopulationAtCapacity m N) field n

theorem smallInitialPopulationCapacityTime_ne_top_iff
    (m N : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    smallInitialPopulationCapacityTime m N field ≠ ⊤ ↔
      ∃ n, field ∈ smallInitialPopulationAtCapacity m N n := by
  constructor
  · intro hfinite
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
    exact ⟨n, (smallInitialPopulationCapacityTime_eq_iff m N n field).1
      hn.symm |>.1⟩
  · rintro ⟨n, hn⟩ htop
    have hle : smallInitialPopulationCapacityTime m N field ≤ n :=
      (ProbabilityTheory.firstDeclaredSuccess_le_iff
        (smallInitialPopulationAtCapacity m N) field n).2 ⟨n, le_rfl, hn⟩
    rw [htop] at hle
    exact (WithTop.not_top_le_coe n) hle

/-- Enumerate a finite selected population in its address order. Away from a
capacity-sized population the vector uses a fixed default address. -/
noncomputable def smallInitialPopulationRootsOfFinset
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (population : Finset (RootIndexed.TreeNode (Fin m) ℕ)) :
    Fin N → RootIndexed.TreeNode (Fin m) ℕ := by
  classical
  by_cases hcard : population.card = N
  · exact fun i => population.orderEmbOfFin hcard i
  · exact fun _ => ((⟨0, hm⟩ : Fin m), [])

/-- The canonical enumeration at a deterministic generation. -/
noncomputable def smallInitialPopulationRootsAt
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Fin N → RootIndexed.TreeNode (Fin m) ℕ :=
  smallInitialPopulationRootsOfFinset m N hm
    (smallInitialPopulation m N n field)

/-- Enumerate the selected roots at the first capacity-hitting generation.
At `⊤` this is totalized by a fixed address. -/
noncomputable def smallInitialPopulationHitRoots
    (m N : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Fin N → RootIndexed.TreeNode (Fin m) ℕ :=
  match smallInitialPopulationCapacityTime m N field with
  | ⊤ => fun _ => ((⟨0, hm⟩ : Fin m), [])
  | (n : ℕ) => smallInitialPopulationRootsAt m N n hm field

theorem smallInitialPopulationRootsAt_mem
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hcapacity : field ∈ smallInitialPopulationAtCapacity m N n)
    (i : Fin N) :
    smallInitialPopulationRootsAt m N n hm field i ∈
      smallInitialPopulation m N n field := by
  classical
  have hcard : (smallInitialPopulation m N n field).card = N := hcapacity
  change smallInitialPopulationRootsOfFinset m N hm
      (smallInitialPopulation m N n field) i ∈ _
  simp [smallInitialPopulationRootsOfFinset, hcard]

theorem smallInitialPopulationHitRoots_eq_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n) :
    smallInitialPopulationHitRoots m N hm field =
      smallInitialPopulationRootsAt m N n hm field := by
  simp [smallInitialPopulationHitRoots, htime]

theorem smallInitialPopulationHitRoots_mem_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n)
    (i : Fin N) :
    smallInitialPopulationHitRoots m N hm field i ∈
      smallInitialPopulation m N n field := by
  have hcapacity : field ∈ smallInitialPopulationAtCapacity m N n :=
    (smallInitialPopulationCapacityTime_eq_iff m N n field).1 htime |>.1
  rw [smallInitialPopulationHitRoots_eq_at_time m N n hm field htime]
  exact smallInitialPopulationRootsAt_mem m N n hm field hcapacity i

theorem smallInitialPopulationHitRoots_injective_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n) :
    Function.Injective (smallInitialPopulationHitRoots m N hm field) := by
  rw [smallInitialPopulationHitRoots_eq_at_time m N n hm field htime]
  have hcapacity : field ∈ smallInitialPopulationAtCapacity m N n :=
    (smallInitialPopulationCapacityTime_eq_iff m N n field).1 htime |>.1
  have hcard : (smallInitialPopulation m N n field).card = N := hcapacity
  simp only [smallInitialPopulationRootsAt, smallInitialPopulationRootsOfFinset,
    dif_pos hcard]
  exact (smallInitialPopulation m N n field).orderEmbOfFin hcard |>.injective

theorem smallInitialPopulationHitRoots_depth_at_time
    (m N n : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (htime : smallInitialPopulationCapacityTime m N field = n)
    (i : Fin N) :
    (smallInitialPopulationHitRoots m N hm field i).2.length = n := by
  have hmem := smallInitialPopulationHitRoots_mem_at_time m N n hm field htime i
  exact Tail.firstNSelectedPopulation_depth m N n field _ hmem

theorem measurable_smallInitialPopulationRootsAt
    (m N n : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (smallInitialPopulationRootsAt m N n hm) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  have hpopulation : Measurable[F n] (smallInitialPopulation m N n) := by
    change Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (smallInitialPopulation m N n)
    exact RootIndexed.selectedPopulationTotalized_adapted
      N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
      measurable_id id measurable_id n
  exact (measurable_of_countable fun population :
      Finset (RootIndexed.TreeNode (Fin m) ℕ) =>
        smallInitialPopulationRootsOfFinset m N hm population).comp
    hpopulation

theorem countable_range_smallInitialPopulationHitRoots
    (m N : ℕ) (hm : 0 < m)
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    (Set.range (smallInitialPopulationHitRoots m N hm)).Countable :=
  Set.to_countable _

theorem measurableSet_smallInitialPopulationHitRoots_fiber
    (m N : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ roots, MeasurableSet[
      (smallInitialPopulationCapacityTime_isStoppingTime m N).measurableSpace]
      {field | smallInitialPopulationHitRoots m N hm field = roots} := by
  classical
  let τ := smallInitialPopulationCapacityTime m N
  let hτ := smallInitialPopulationCapacityTime_isStoppingTime m N
  let default : Fin N → RootIndexed.TreeNode (Fin m) ℕ :=
    fun _ => ((⟨0, hm⟩ : Fin m), [])
  intro roots
  have hdecomp : {field |
      smallInitialPopulationHitRoots m N hm field = roots} =
      ({field | τ field = ⊤} ∩ {field | default = roots}) ∪
        ⋃ n : ℕ, {field | τ field = (n : WithTop ℕ)} ∩
          {field | smallInitialPopulationRootsAt m N n hm field = roots} := by
    ext field
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_iUnion]
    cases htime : τ field with
    | top => simp [smallInitialPopulationHitRoots, τ, htime, default]
    | coe n =>
        simp only [smallInitialPopulationHitRoots, τ, htime,
          WithTop.coe_ne_top, false_and, false_or]
        constructor
        · intro h
          exact ⟨n, rfl, h⟩
        · rintro ⟨k, hk, hroots⟩
          have hnk : n = k := WithTop.coe_injective hk
          have hkn : k = n := hnk.symm
          subst k
          exact hroots
  rw [hdecomp]
  apply MeasurableSet.union
  · by_cases hdefault : default = roots
    · have htop : MeasurableSet[hτ.measurableSpace]
          {field | τ field = (⊤ : WithTop ℕ)} := by
        have htop_eq : {field | τ field = (⊤ : WithTop ℕ)} =
            ⋂ n : ℕ, {field | (n : WithTop ℕ) ≤ τ field} := by
          ext field
          constructor
          · intro htop
            change τ field = ⊤ at htop
            simp [htop]
          · intro hall
            cases htime : τ field with
            | top =>
                change τ field = ⊤
                exact htime
            | coe k =>
                have hk := (Set.mem_iInter.mp hall) (k + 1)
                change ((k + 1 : ℕ) : WithTop ℕ) ≤ τ field at hk
                rw [htime] at hk
                have hfalse : False := by
                  have hk' : k + 1 ≤ k := WithTop.coe_le_coe.mp hk
                  omega
                exact hfalse.elim
        rw [htop_eq]
        exact MeasurableSet.iInter fun n => hτ.measurableSet_ge' n
      simpa [hdefault] using htop
    · simp [hdefault]
  · apply MeasurableSet.iUnion
    intro n
    have hroots : MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) n]
        {field | smallInitialPopulationRootsAt m N n hm field = roots} :=
      measurable_smallInitialPopulationRootsAt m N n hm
        (measurableSet_singleton roots)
    have htime : MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) n]
        {field | τ field = (n : WithTop ℕ)} := by
      change MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) n]
        {field | smallInitialPopulationCapacityTime m N field = n}
      exact hτ.measurableSet_eq n
    rw [Set.inter_comm]
    exact (hτ.measurableSet_inter_eq_iff
      {field | smallInitialPopulationRootsAt m N n hm field = roots} n).2
        (hroots.inter htime)

theorem smallInitialPopulationHitRoots_factorization_on_finite
    (m N : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (A : Set (FiniteRootStepField m ℕ ℝ))
    (B : Set (Fin N → TreeNode ℕ → Step ℕ ℝ))
    (hA : MeasurableSet[
      (smallInitialPopulationCapacityTime_isStoppingTime m N).measurableSpace] A)
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      ((A ∩ {field | smallInitialPopulationCapacityTime m N field ≠ ⊤}) ∩
        RootIndexed.selectedSubtreeStepFieldVector
          (smallInitialPopulationHitRoots m N hm) ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        (A ∩ {field | smallInitialPopulationCapacityTime m N field ≠ ⊤}) *
        finiteRootStepFieldLaw μ N B := by
  have hdepth : ∀ field (n : ℕ),
      smallInitialPopulationCapacityTime m N field = (n : WithTop ℕ) →
        ∀ i, (smallInitialPopulationHitRoots m N hm field i).2.length = n := by
    intro field n htime i
    exact smallInitialPopulationHitRoots_depth_at_time
      m N n hm field htime i
  have hinjective : ∀ field,
      smallInitialPopulationCapacityTime m N field ≠ ⊤ →
        Function.Injective (smallInitialPopulationHitRoots m N hm field) := by
    intro field hfinite
    obtain ⟨n, htime⟩ := WithTop.ne_top_iff_exists.mp hfinite
    exact smallInitialPopulationHitRoots_injective_at_time
      m N n hm field htime.symm
  exact RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
    μ (smallInitialPopulationCapacityTime m N)
    (smallInitialPopulationCapacityTime_isStoppingTime m N)
    (smallInitialPopulationHitRoots m N hm)
    (countable_range_smallInitialPopulationHitRoots m N hm)
    (measurableSet_smallInitialPopulationHitRoots_fiber m N hm)
    hdepth hinjective A B hA hB

theorem ae_smallInitialPopulationCapacityTime_ne_top
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      smallInitialPopulationCapacityTime m N field ≠ ⊤ := by
  filter_upwards [finiteRootStepFieldLaw_ae_smallInitialPopulation_hits_capacity
    m N hm hmN μ hboundary hnonempty hsupercritical] with field hhit
  exact (smallInitialPopulationCapacityTime_ne_top_iff m N field).2 hhit

theorem smallInitialPopulationHitRoots_freshField_law
    (m N : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ)
    (B : Set (Fin N → TreeNode ℕ → Step ℕ ℝ))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      (RootIndexed.selectedSubtreeStepFieldVector
        (smallInitialPopulationHitRoots m N hm) ⁻¹' B) =
      finiteRootStepFieldLaw μ N B := by
  let P := finiteRootStepFieldLaw μ m
  let τ := smallInitialPopulationCapacityTime m N
  let finite : Set (FiniteRootStepField m ℕ ℝ) := {field | τ field ≠ ⊤}
  let fresh := RootIndexed.selectedSubtreeStepFieldVector
    (smallInitialPopulationHitRoots m N hm)
  have hfiniteAE : ∀ᵐ field ∂P, field ∈ finite := by
    exact ae_smallInitialPopulationCapacityTime_ne_top
      m N hm hmN μ hboundary hnonempty hsupercritical
  have htopZero : P {field | τ field = ⊤} = 0 := by
    have h := hfiniteAE
    rw [ae_iff] at h
    simpa [finite, τ] using h
  have hτ := smallInitialPopulationCapacityTime_isStoppingTime m N
  have htopMeasStopped : MeasurableSet[hτ.measurableSpace]
      {field | τ field = ⊤} := by
    have hdecomp : {field | τ field = ⊤} =
        (⋃ n : ℕ, {field | τ field = (n : WithTop ℕ)})ᶜ := by
      ext field
      cases htime : τ field <;> simp [htime]
    rw [hdecomp]
    exact (MeasurableSet.iUnion fun n =>
      hτ.measurableSet_eq_of_countable' n).compl
  have htopMeas : MeasurableSet {field | τ field = ⊤} :=
    hτ.measurableSpace_le _ htopMeasStopped
  have hfiniteProb : P finite = 1 := by
    have hfiniteEq : finite = {field | τ field = ⊤}ᶜ := by
      ext field
      simp [finite]
    rw [hfiniteEq, measure_compl htopMeas (by finiteness), measure_univ,
      htopZero]
    simp
  have hfactor := smallInitialPopulationHitRoots_factorization_on_finite
    m N hm μ Set.univ B MeasurableSet.univ hB
  have hfactor' : P (finite ∩ fresh ⁻¹' B) = P finite *
      finiteRootStepFieldLaw μ N B := by
    simpa [P, τ, finite, fresh, Set.univ_inter] using hfactor
  have heq : (finite ∩ fresh ⁻¹' B) =ᵐ[P] (fresh ⁻¹' B) := by
    filter_upwards [hfiniteAE] with field hfield
    simp [hfield]
  calc
    P (fresh ⁻¹' B) = P (finite ∩ fresh ⁻¹' B) :=
      (measure_congr heq).symm
    _ = P finite * finiteRootStepFieldLaw μ N B := hfactor'
    _ = finiteRootStepFieldLaw μ N B := by rw [hfiniteProb]; simp

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
