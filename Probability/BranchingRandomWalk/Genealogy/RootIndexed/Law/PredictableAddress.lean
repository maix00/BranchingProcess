/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Fresh-step law at a predictable genealogy address

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.stepFieldLaw_predictableAddress_map_eq`:
  under the product law of i.i.d. reproduction steps indexed by roots and
  Ulam--Harris addresses, a generation-measurable choice of a root/address
  at depth $n$ reads a step with the original one-step law.

For each fixed root/address coordinate, the reproduction step is independent
of all coordinates at smaller address depths. Partitioning by the selected
root/address and summing the resulting product probabilities gives the law
identity. Countability is required only for the range of the selected
root/address, which indexes this partition.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

set_option maxHeartbeats 1000000 in
/-- A generation-measurable choice of a root/address at depth `n` sees a
fresh reproduction step with exactly the original law. -/
theorem RootIndexed.stepFieldLaw_predictableAddress_map_eq
    {Root α X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hfiber : ∀ p, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
        {field | chosen field = p})
    (hdepth : ∀ field, (chosen field).2.length = n)
    (hcount : (Set.range chosen).Countable) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
      (fun field => field (chosen field).1 (chosen field).2) = μ := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  have hcoord_le (p : Root × TreeNode α) :
      RootIndexed.stepCoordinateSpace p ≤
        (inferInstance : MeasurableSpace (RootIndexed.StepField Root α X)) := by
    let hRoot : Measurable
        (fun field : RootIndexed.StepField Root α X => field p.1) :=
      measurable_pi_apply p.1
    let hAddress : Measurable
        (fun field : Combinatorics.Branching.StepField α X => field p.2) :=
      measurable_pi_apply p.2
    exact (hAddress.comp hRoot).comap_le
  have hindepCoords : ProbabilityTheory.iIndep
      (RootIndexed.stepCoordinateSpace (Root := Root) (α := α) (X := X)) P := by
    simpa [P] using
      RootIndexed.stepFieldLaw_coordinates_independent (Root := Root) μ
  have hindepPast (p : Root × TreeNode α) (hp : p.2.length = n) :
      ProbabilityTheory.Indep
        (RootIndexed.stepGenerationSpace
          (Root := Root) (α := α) (X := X) n)
        (RootIndexed.stepCoordinateSpace p) P := by
    have hdisj : Disjoint
        {q : Root × TreeNode α | q.2.length < n} ({p} : Set (Root × TreeNode α)) := by
      refine Set.disjoint_left.mpr ?_
      intro q hq hqp
      have hq' : q.2.length < n := hq
      have hqp' : q = p := Set.mem_singleton_iff.mp hqp
      rw [hqp'] at hq'
      omega
    have hindep := ProbabilityTheory.indep_iSup_of_disjoint
      (m := RootIndexed.stepCoordinateSpace
        (Root := Root) (α := α) (X := X)) (μ := P)
      hcoord_le hindepCoords hdisj
    rw [← RootIndexed.stepGenerationSpace_eq_coordinate_iSup
      (Root := Root) (α := α) (X := X) n] at hindep
    simpa only [iSup_singleton] using hindep

  have hfiberFull (p : Root × TreeNode α) :
      MeasurableSet {field | chosen field = p} :=
    ((RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X)).le n) _ (hfiber p)
  have hfiberPast (p : Root × TreeNode α) :
      MeasurableSet[RootIndexed.stepGenerationSpace
        (Root := Root) (α := α) (X := X) n]
        {field | chosen field = p} :=
    hfiber p
  have hmarkFiltration :
      Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (n + 1)]
        (fun field : RootIndexed.StepField Root α X =>
          field (chosen field).1 (chosen field).2) := by
    have hfiberSucc (p : Root × TreeNode α) : MeasurableSet[
        RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)]
        {field | chosen field = p} :=
      ((RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)).mono' (Nat.le_succ n)) _ (hfiber p)
    have hdepth' : ∀ field, (chosen field).2.length < n + 1 := by
      intro field
      rw [hdepth field]
      exact Nat.lt_succ_self n
    exact RootIndexed.selectedStep_measurable chosen hfiberSucc hdepth' hcount
  have hmarkMeas : Measurable
      (fun field : RootIndexed.StepField Root α X =>
        field (chosen field).1 (chosen field).2) :=
    hmarkFiltration.mono
      ((RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)).le (n + 1))
      le_rfl

  ext A hA
  rw [Measure.map_apply hmarkMeas hA]
  let fiber : (Root × TreeNode α) → Set (RootIndexed.StepField Root α X) :=
    fun p => {field | chosen field = p} ∩
      {field | field p.1 p.2 ∈ A}
  have hfiberMeas (p : Root × TreeNode α) : MeasurableSet (fiber p) := by
    have hcoordA : MeasurableSet[RootIndexed.stepCoordinateSpace p]
        {field | field p.1 p.2 ∈ A} := by
      rw [RootIndexed.stepCoordinateSpace,
        MeasurableSpace.measurableSet_comap]
      exact ⟨A, hA, rfl⟩
    have hcoordAFull : MeasurableSet {field : RootIndexed.StepField Root α X |
        field p.1 p.2 ∈ A} := by
      let hRoot : Measurable
          (fun field : RootIndexed.StepField Root α X => field p.1) :=
        measurable_pi_apply p.1
      let hAddress : Measurable
          (fun field : Combinatorics.Branching.StepField α X => field p.2) :=
        measurable_pi_apply p.2
      exact (hAddress.comp hRoot) hA
    exact (hfiberFull p).inter hcoordAFull
  have hpairRange : Pairwise (fun p q : Set.range chosen =>
      Disjoint (fiber p.1) (fiber q.1)) := by
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    intro field hp hq
    exact hpq (Subtype.ext ((hp.1.symm).trans hq.1))
  have hunion : (⋃ p : Set.range chosen, fiber p.1) =
      {field | field (chosen field).1 (chosen field).2 ∈ A} := by
    ext field
    simp only [Set.mem_iUnion, fiber, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, hp, hAfield⟩
      rw [hp]
      exact hAfield
    · intro hAfield
      exact ⟨⟨chosen field, ⟨field, rfl⟩⟩, rfl, hAfield⟩
  have hfiberMeasure (p : Root × TreeNode α) (hp : p.2.length = n) :
      P (fiber p) = P {field | chosen field = p} * μ A := by
    have hindep := (ProbabilityTheory.indep_iff_forall_indepSet P).mp
      (hindepPast p hp) {field | chosen field = p}
      {field | field p.1 p.2 ∈ A} (hfiberPast p) (by
        rw [RootIndexed.stepCoordinateSpace,
          MeasurableSpace.measurableSet_comap]
        exact ⟨A, hA, rfl⟩)
    have hfactor := hindep.measure_inter_eq_mul
    have hmarginal : P {field | field p.1 p.2 ∈ A} = μ A := by
      let hRoot : Measurable
          (fun field : RootIndexed.StepField Root α X => field p.1) :=
        measurable_pi_apply p.1
      let hAddress : Measurable
          (fun field : Combinatorics.Branching.StepField α X => field p.2) :=
        measurable_pi_apply p.2
      let eval : RootIndexed.StepField Root α X → Combinatorics.Branching.Step α X :=
        fun field => field p.1 p.2
      have heval : Measurable eval := hAddress.comp hRoot
      change P (eval ⁻¹' A) = μ A
      rw [← Measure.map_apply heval hA,
        RootIndexed.stepFieldLaw_coordinate_marginal (Root := Root) (α := α) μ p.1 p.2]
    simpa [fiber, hmarginal] using hfactor

  letI : Countable (Set.range chosen) := hcount
  have hchosenFibersPair : Pairwise (fun p q : Set.range chosen => Disjoint
      {field : RootIndexed.StepField Root α X | chosen field = p.1}
      {field | chosen field = q.1}) := by
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    intro field hp hq
    exact hpq (Subtype.ext (hp.symm.trans hq))
  have hchosenFibersMeas (p : Set.range chosen) :
      MeasurableSet {field : RootIndexed.StepField Root α X | chosen field = p.1} :=
    hfiberFull p.1
  have hchosenCover : (⋃ p : Set.range chosen,
      {field : RootIndexed.StepField Root α X | chosen field = p.1}) = Set.univ := by
    ext field
    constructor
    · intro _
      exact Set.mem_univ field
    · intro _
      rw [Set.mem_iUnion]
      refine ⟨⟨chosen field, ?_⟩, ?_⟩
      · exact Set.mem_range_self field
      · rfl
  have hfiberTsum : (∑' p : Set.range chosen,
      P {field | chosen field = p.1}) = 1 := by
    calc
      _ = P (⋃ p : Set.range chosen,
          {field | chosen field = p.1}) := by
            symm
            exact measure_iUnion hchosenFibersPair hchosenFibersMeas
      _ = 1 := by rw [hchosenCover, measure_univ]
  have hsumFiber :
      (∑' p : Set.range chosen, P (fiber p.1)) = μ A := by
    rw [show (∑' p : Set.range chosen, P (fiber p.1)) =
      ∑' p : Set.range chosen,
        P {field | chosen field = p.1} * μ A by
          apply tsum_congr
          intro p
          obtain ⟨field, hfield⟩ := p.2
          have hpdepth : p.1.2.length = n := by
            rw [← hfield]
            exact hdepth field
          exact hfiberMeasure p.1 hpdepth]
    calc
      _ = (∑' p : Set.range chosen,
          P {field | chosen field = p.1}) * μ A := ENNReal.tsum_mul_right
      _ = μ A := by rw [hfiberTsum]; simp
  change P {field | field (chosen field).1 (chosen field).2 ∈ A} = μ A
  rw [← hunion, measure_iUnion hpairRange (fun p => hfiberMeas p.1)]
  exact hsumFiber


end ProbabilityTheory.BranchingRandomWalk
