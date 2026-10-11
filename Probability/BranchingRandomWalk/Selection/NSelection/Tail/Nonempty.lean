/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.SelectedPopulationDrawdown

/-!
# Nonempty selected generations

Under the paper's nonempty-offspring and boundary-normalization assumptions,
the totalized first-`N` population is nonempty at every generation almost
surely, provided the initial population and selection capacity are nonempty.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open Combinatorics.Branching.Selection.NSelection

theorem finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∀ n, (RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field).Nonempty := by
  have hspec := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hboundary N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ))
  have hchildren := finiteRootStepFieldLaw_all_nonempty μ hnonempty m
  filter_upwards [hspec, hchildren] with field hspec hchildren
  intro n
  induction n with
  | zero =>
      change (RootIndexed.initialPopulation (Finset.univ : Finset (Fin m))).Nonempty
      apply Finset.card_pos.mp
      rw [RootIndexed.initialPopulation_card]
      simpa using hm
  | succ n ih =>
      let parents := RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field
      have hdepth : ∀ p ∈ parents, p.2.length = n := by
        intro p hp
        exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
          (fun _ => (0 : ℝ)) id id n field p hp
      have hcandidates : (RootIndexed.childrenAtGeneration n parents field).Nonempty := by
        rcases ih with ⟨p, hp⟩
        obtain ⟨i, hi⟩ := hchildren p.1 p.2
        exact ⟨(p.1, p.2 ++ [i]),
          RootIndexed.childAddress_mem_childrenAtGeneration n parents field
            p hp (hdepth p hp) i hi⟩
      have hselected : IsFirstNBy N
          (RootIndexed.observedPositionAtGeneration (fun _ : Fin m => (0 : ℝ))
            id id (n + 1) field)
          (RootIndexed.childrenAtGeneration n parents field)
          (RootIndexed.selectedPopulationTotalized N
            (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id
            (n + 1) field) := by
        simpa [parents] using hspec n
      exact hselected.nonempty_of_nonempty_candidates hN hcandidates

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
