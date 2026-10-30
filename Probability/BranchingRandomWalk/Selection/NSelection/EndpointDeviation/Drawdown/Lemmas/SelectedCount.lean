/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Combinatorics.BranchingWalk.Step.Basic
import Combinatorics.UlamHarris.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population

/-!
# Selected generation-address count bound

This internal estimate controls the sum of the probabilities that individual
addresses belong to the random selected population. If `P_j` is the
generation-`j` selected population and `|P_j| ≤ N` pointwise, then
\[
  \sum_{\substack{p=(r,u)\\ |u|=j}} \mathbb P(p\in P_j)\le N.
\]
The proof identifies the sum of membership indicators with `|P_j|` and
integrates the pointwise cardinality bound. It is used only in the
large-drawdown estimate.

## Internal proof declarations

- `tsum_generationAddress_selected_le` is the selected-address count estimate
  used by `Drawdown/Large.lean`.
-/

attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris

private abbrev GenerationAddress (m j : ℕ) :=
  {p : RootIndexed.TreeNode (Fin m) ℕ // p.2.length = j}

/-- The sum of the probabilities that each fixed generation-`j` address is
selected is at most `N`.  This is the random-finite-set decomposition: the
countable sum of membership indicators is exactly the cardinality of the
selected finset, pointwise. -/
lemma tsum_generationAddress_selected_le
    (m N j : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hmN : m ≤ N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    ∑' p : {p : RootIndexed.TreeNode (Fin m) ℕ // p.2.length = j},
      (finiteRootStepFieldLaw μ m)
        {field | p.1 ∈ firstNSelectedPopulation m N j field} ≤ N := by
  classical
  let P := finiteRootStepFieldLaw μ m
  let A : GenerationAddress m j → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | p.1 ∈ firstNSelectedPopulation m N j field}
  let g : GenerationAddress m j → FiniteRootStepField m ℕ ℝ → ℝ≥0∞ :=
    fun p => (A p).indicator fun _ => 1
  have hA (p : GenerationAddress m j) : MeasurableSet (A p) := by
    have hpop := firstNSelectedPopulation_measurable m N j
    simpa [A] using hpop (measurableSet_mem_finset p.1)
  have hg (p : GenerationAddress m j) : Measurable (g p) :=
    measurable_const.indicator (hA p)
  have hsum (field : FiniteRootStepField m ℕ ℝ) :
      ∑' p : GenerationAddress m j, g p field =
        (firstNSelectedPopulation m N j field).card := by
    let pop := firstNSelectedPopulation m N j field
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
      have hnot' : p.1 ∉ firstNSelectedPopulation m N j field := by
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
            have hp'' : p.1 ∈ firstNSelectedPopulation m N j field := by
              simpa [pop] using hp'
            simp [g, A, hp'']
          _ = selectedAddresses.card := by simp
      _ = pop.card := by simp [selectedAddresses, encode]
  have hsumA :
      ∑' p : GenerationAddress m j, P (A p) =
        ∫⁻ field, (firstNSelectedPopulation m N j field).card ∂P := by
    calc
      ∑' p, P (A p) = ∑' p, ∫⁻ field, g p field ∂P := by
        apply tsum_congr
        intro p
        rw [lintegral_indicator_const (hA p)]
        simp
      _ = ∫⁻ field, ∑' p, g p field ∂P := by
        symm
        exact lintegral_tsum (fun p => (hg p).aemeasurable)
      _ = ∫⁻ field, (firstNSelectedPopulation m N j field).card ∂P :=
        lintegral_congr hsum
  calc
    ∑' p : GenerationAddress m j, P (A p) =
        ∫⁻ field, (firstNSelectedPopulation m N j field).card ∂P := hsumA
    _ ≤ ∫⁻ _field, (N : ℝ≥0∞) ∂P := by
      apply lintegral_mono
      intro field
      change ((firstNSelectedPopulation m N j field).card : ℝ≥0∞) ≤
        (N : ℝ≥0∞)
      exact_mod_cast firstNSelectedPopulation_card_le m N j hmN field
    _ = N := by simp [P]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
