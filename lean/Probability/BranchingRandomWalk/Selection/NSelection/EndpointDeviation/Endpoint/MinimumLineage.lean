/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.EndpointMinimumAddress
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoments
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Nonempty
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Step.OrderedSupport

/-!
# Endpoint-minimizing lineages for fixed-capacity selection

The endpoint-minimizing particle in one generation has a leftmost child in
the next candidate population, almost surely under the paper's nonempty
offspring assumption. That child need not itself survive the global
selection step. The first-`N` property instead implies that the next selected
endpoint minimum is no larger than its endpoint. This is the pathwise bridge
needed to use predictable fresh-step moments for the endpoint minimum.
-/


open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 1000000

section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open Combinatorics.UlamHarris

private abbrev endpointPosition (m k : ℕ)
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ) : ℝ :=
  RootIndexed.positionAtGeneration (fun _ : Fin m => (0 : ℝ)) id k
    p.1 p.2 field

/-- A nonempty first-`N` segment contains a point no higher than any given
candidate. This is the order-theoretic content of first-`N` selection needed
for endpoint comparison. -/
private theorem exists_mem_le_of_isFirstNBy
    {ι V : Type*} [LinearOrder ι] [LinearOrder V]
    {N : ℕ} {value : ι → V} {candidates : Set ι}
    {selected : Finset ι}
    (hselected : IsFirstNBy N value candidates selected)
    (hN : 0 < N) (hcandidates : candidates.Nonempty)
    {q : ι} (hq : q ∈ candidates) :
    ∃ p ∈ selected, value p ≤ value q := by
  classical
  have hpop : selected.Nonempty :=
    hselected.nonempty_of_nonempty_candidates hN hcandidates
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image selected value hpop
  by_contra h
  have hq_lt : value q < value p := by
    exact lt_of_not_ge (fun hpq => h ⟨p, hp, hpq⟩)
  have hkey : valueKey value q < valueKey value p := by
    change toLex (value q, q) < toLex (value p, p)
    exact Prod.Lex.left q p hq_lt
  have hqselected := hselected.lower p hp q hq hkey
  exact (not_lt_of_ge (hpmin q hqselected)) hq_lt

/-- If the previous generation contains `p`, its slot-zero child survives,
and the next-generation candidate set satisfies the paper's lower-finiteness
condition, then the next selected endpoint minimum is at most the endpoint
of that child. -/
theorem firstNSelectedEndpointMinimum_succ_le_of_slotZero_candidate
    (m N k : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (hN : 0 < N)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N k field)
    (hdepth : p.2.length = k)
    (hslotZero : survive (field p.1 p.2) 0)
    (hgood : IsLowerFiniteBy
      (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ))
        id id (k + 1) field)
      (RootIndexed.childrenAtGeneration k
        (firstNSelectedPopulation m N k field) field)) :
    firstNSelectedEndpointMinimum m N (k + 1) field ≤
      endpointPosition m k field p +
        max (value' (field p.1 p.2) 0) 0 := by
  classical
  let parents := firstNSelectedPopulation m N k field
  let candidates := RootIndexed.childrenAtGeneration k parents field
  let q : RootIndexed.TreeNode (Fin m) ℕ := (p.1, p.2 ++ [0])
  have hq : q ∈ candidates := by
    exact RootIndexed.childAddress_mem_childrenAtGeneration k parents field
      p hp hdepth 0 hslotZero
  have hselected : IsFirstNBy N
      (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ))
        id id (k + 1) field) candidates
      (firstNSelectedPopulation m N (k + 1) field) := by
    change IsFirstNBy N
      (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ))
        id id (k + 1) field)
      (RootIndexed.childrenAtGeneration k
        (RootIndexed.selectedPopulationTotalized N
          (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id k field)
        field)
      (RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id (k + 1) field)
    exact RootIndexed.selectedPopulationTotalized_succ_spec N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id k field hgood
  have hqdepth : q.2.length = k + 1 := by
    simp [q, hdepth]
  have hqvalue :
      RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (k + 1) field q =
        endpointPosition m k field p + value' (field p.1 p.2) 0 := by
    calc
      RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (k + 1) field q =
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
            p.1 (p.2 ++ [0]) := by
              simp [RootIndexed.observedPositionAtGeneration,
                RootIndexed.positionAtGeneration, q, hdepth]
      _ = endpointPosition m k field p + value' (field p.1 p.2) 0 := by
        rw [RootIndexed.position_append_singleton]
        change RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
            p.1 p.2 + value' ((field p.1 p.2).map id) 0 =
          endpointPosition m k field p + value' (field p.1 p.2) 0
        simp [endpointPosition, RootIndexed.positionAtGeneration, hdepth]
  have hcandidates : candidates.Nonempty := ⟨q, hq⟩
  have hnextNonempty : (firstNSelectedPopulation m N (k + 1) field).Nonempty :=
    hselected.nonempty_of_nonempty_candidates hN hcandidates
  have hleCandidate :
      firstNSelectedEndpointMinimum m N (k + 1) field ≤
        RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id (k + 1) field q := by
    rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
      m N (k + 1) field hnextNonempty]
    rw [Finset.inf'_le_iff]
    obtain ⟨r, hr, hle⟩ :=
      exists_mem_le_of_isFirstNBy hselected hN hcandidates hq
    refine ⟨r, hr, ?_⟩
    have hrdepth := firstNSelectedPopulation_depth m N (k + 1) field r hr
    simpa [RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration, hrdepth] using hle
  rw [hqvalue] at hleCandidate
  exact hleCandidate.trans
    (add_le_add_right (le_max_left _ _) (endpointPosition m k field p))

/-- A depth-correct totalization of the endpoint-minimizing address. On the
empty-population branch it uses a fixed length-`k` address, so the predictable
fresh-step theorem applies on the entire sample space. -/
noncomputable def firstNSelectedEndpointMinAddressAtDepth
    (m N k : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) : RootIndexed.TreeNode (Fin m) ℕ :=
  if (firstNSelectedPopulation m N k field).Nonempty then
    firstNSelectedEndpointMinAddress m N k hm field
  else
    ((⟨0, hm⟩ : Fin m), List.replicate k 0)

theorem firstNSelectedEndpointMinAddressAtDepth_length
    (m N k : ℕ) (hm : 0 < m)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2.length = k := by
  classical
  by_cases hpop : (firstNSelectedPopulation m N k field).Nonempty
  · simp [firstNSelectedEndpointMinAddressAtDepth, hpop]
    exact firstNSelectedPopulation_depth m N k field
      (firstNSelectedEndpointMinAddress m N k hm field)
      ((firstNSelectedEndpointMinAddress_mem_and_min m N k hm field hpop).1)
  · simp [firstNSelectedEndpointMinAddressAtDepth, hpop]

theorem measurable_firstNSelectedEndpointMinAddressAtDepth
    (m N k : ℕ) (hm : 0 < m)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedEndpointMinAddressAtDepth m N k hm) := by
  classical
  have hpopulation : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedPopulation m N k) := by
    change Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (fun field => RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id k field)
    exact RootIndexed.selectedPopulationTotalized_adapted N
      Finset.univ (fun _ : Fin m => (0 : ℝ)) id measurable_id id
      measurable_id k
  have hnonempty : MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      {field : FiniteRootStepField m ℕ ℝ |
        (firstNSelectedPopulation m N k field).Nonempty} := by
    rw [show {field : FiniteRootStepField m ℕ ℝ |
        (firstNSelectedPopulation m N k field).Nonempty} =
        {field | firstNSelectedPopulation m N k field ≠ ∅} by
      ext field
      simp [Finset.nonempty_iff_ne_empty]]
    exact hpopulation (measurableSet_singleton
      (∅ : Finset (RootIndexed.TreeNode (Fin m) ℕ))).compl
  exact Measurable.ite hnonempty
    (measurable_firstNSelectedEndpointMinAddress m N k hm)
    measurable_const

/-- The predictable endpoint-minimizing addresses have the same uniform
fourth-moment bound as any predictable lineage. This is the fresh-step
moment estimate specialized to the measurable, depth-correct selector above.
-/
theorem finiteRootStepFieldLaw_integral_pow_four_sum_endpointMinAddressPositiveSlotZero_le
    (m n N : ℕ) (hm : 0 < m)
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hfour : HasLeftmostFourthMoment L) :
    Integrable (fun field =>
      (∑ k ∈ Finset.range n,
        max (value' (field
          (firstNSelectedEndpointMinAddressAtDepth m N k hm field).1
          (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2) 0) 0) ^ 4)
        (finiteRootStepFieldLaw L.sortedPotentialImage m) ∧
      (∫ field,
        (∑ k ∈ Finset.range n,
          max (value' (field
            (firstNSelectedEndpointMinAddressAtDepth m N k hm field).1
            (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2) 0) 0) ^ 4
        ∂finiteRootStepFieldLaw L.sortedPotentialImage m) ≤
        (n : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw := by
  let chosen : ∀ k, FiniteRootStepField m ℕ ℝ → Fin m ×
      TreeNode ℕ := fun k field =>
    firstNSelectedEndpointMinAddressAtDepth m N k hm field
  have hchosen : ∀ k, Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (chosen k) := by
    intro k
    change Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
      (firstNSelectedEndpointMinAddressAtDepth m N k hm)
    exact measurable_firstNSelectedEndpointMinAddressAtDepth m N k hm
  have hdepth : ∀ k field, (chosen k field).2.length = k := by
    intro k field
    exact firstNSelectedEndpointMinAddressAtDepth_length m N k hm field
  simpa [chosen] using
    finiteRootStepFieldLaw_integral_pow_four_sum_predictablePositiveSlotZero_le
      m n L chosen hchosen hdepth hfour

/-- Almost surely, every one-step increase of the selected endpoint minimum
is bounded by the positive part of the fresh slot-zero increment read at the
previous generation's endpoint-minimizing address. The law conditions are
the paper's boundary normalization and nonempty-offspring assumptions.
-/
theorem finiteRootStepFieldLaw_endpointMinimum_succ_le_predictablePositiveSlotZero_ae
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ field ∂finiteRootStepFieldLaw L.sortedPotentialImage m,
      ∀ k,
        firstNSelectedEndpointMinimum m N (k + 1) field ≤
          firstNSelectedEndpointMinimum m N k field +
            max (value' (field
              (firstNSelectedEndpointMinAddressAtDepth m N k hm field).1
              (firstNSelectedEndpointMinAddressAtDepth m N k hm field).2) 0) 0 := by
  classical
  have hboundarySorted :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptySorted : L.sortedPotentialImage nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hadmiss := RootIndexed.selectedPopulationTotalized_admissible_ae
    L.sortedPotentialImage hboundarySorted N Finset.univ
    (fun _ : Fin m => (0 : ℝ))
  have hpopulation := finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    m N hm hN L.sortedPotentialImage hboundarySorted hnonemptySorted
  have hordered : L.sortedPotentialImage orderedSteps = 1 := by
    rw [show orderedSteps = orderedBySteps realPotential by
      ext ξ
      simp [orderedBySteps, Step.IsOrderedBy, realPotential]]
    rw [L.sortedPotentialImage_orderedBy]
    simp
  have hfirstChild := finiteRootStepFieldLaw_all_first_child
    L.sortedPotentialImage hordered hnonemptySorted m
  filter_upwards [hadmiss, hpopulation, hfirstChild]
    with field hadmiss hpopulation hfirstChild
  intro k
  have hpopk : (firstNSelectedPopulation m N k field).Nonempty := by
    simpa [firstNSelectedPopulation] using hpopulation k
  let p := firstNSelectedEndpointMinAddress m N k hm field
  have hpmin := firstNSelectedEndpointMinAddress_mem_and_min
    m N k hm field hpopk
  have hp := hpmin.1
  have hpdepth := firstNSelectedPopulation_depth m N k field p hp
  have hslotZero := hfirstChild p.1 p.2
  have hgood : IsLowerFiniteBy
      (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ))
        id id (k + 1) field)
      (RootIndexed.childrenAtGeneration k
        (firstNSelectedPopulation m N k field) field) := by
    simpa [firstNSelectedPopulation] using hadmiss k
  have hstep := firstNSelectedEndpointMinimum_succ_le_of_slotZero_candidate
    m N k field hN p hp hpdepth hslotZero hgood
  have hminEq : firstNSelectedEndpointMinimum m N k field =
      endpointPosition m k field p := by
    rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
      m N k field hpopk]
    apply le_antisymm
    · rw [Finset.inf'_le_iff]
      refine ⟨p, hp, ?_⟩
      simp [endpointPosition, RootIndexed.positionAtGeneration, hpdepth]
    · rw [Finset.le_inf'_iff]
      intro q hq
      have hqdepth := firstNSelectedPopulation_depth m N k field q hq
      simpa [p, endpointPosition,
        RootIndexed.positionAtGeneration, hpdepth, hqdepth] using hpmin.2 q hq
  rw [← hminEq] at hstep
  have hchosenEq :
      firstNSelectedEndpointMinAddressAtDepth m N k hm field = p := by
    simp [firstNSelectedEndpointMinAddressAtDepth, hpopk, p]
  simpa [hchosenEq] using hstep

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
