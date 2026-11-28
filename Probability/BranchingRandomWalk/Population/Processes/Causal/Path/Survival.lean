/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Window
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.IndependentEventCount

/-!
# Finite-root survival from a single-root history event

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.measure_terminalPosition_avoidance_le_exp_of_pathSuccess`:
  for a measurable history event `C` compatible with the prescribed relative
  windows, `q≤P_μ(hasPathHistoryIn φ H 0 C)` implies
  `P_μ(∀p∈P_H, position(p)∉B)≤exp(-m q)` whenever paths in `C` end in `B`,
  for the existing population from `m` independent
  zero-position roots. It assumes only `0≤q≤1` and finite negative-exponential
  family weight almost surely, without boundary normalization or second moments.

This is the independent-root amplification used in B. Mallein,
*N-branching random walk with α-stable spine*, §4.4, proof of Lemma 4.8, arXiv:1503.03762v2.
The proof reuses the existing root-avoidance bound and the path-to-population
inclusion. It defines no new population or branching law.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Independent initial roots amplify any compatible single-root path success
probability. The weight condition only makes the total population's infinite-
weight guard almost surely inactive. See B. Mallein, *N-branching random walk
with α-stable spine*, §4.4, proof of Lemma 4.8, arXiv:1503.03762v2. -/
theorem measure_terminalPosition_avoidance_le_exp_of_pathSuccess
    {X : Type*} [MeasurableSpace X] (φ : Potential X)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hweight : ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞)
    (m H cutoff : ℕ) [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (corridor : Set (Fin (H + 1) → ℝ)) (hC : MeasurableSet corridor)
    (hfit : ∀ path ∈ corridor, path 0 = 0 → InRestartedWindows cutoff window path)
    (terminal : Set ℝ) (hterminal : ∀ path ∈ corridor, path (Fin.last H) ∈ terminal)
    (q : ℝ) (hq : 0 ≤ q) (hq_one : q ≤ 1)
    (hprob : q ≤ (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ).real
      (hasPathHistoryIn (ι := ℕ) φ H 0 corridor)) :
    let P := ofRestartedRealPositionSets (fun _ : Fin m => 0) φ φ.measurable_toFun
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff window hwindow upper hupper
    finiteRootStepFieldLaw μ m {field | ¬ ∃ p ∈ P H field,
      RootIndexed.position (fun _ : Fin m => 0) φ field p.1 p.2 ∈ terminal} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * q)) := by
  intro P
  let E := hasPathHistoryIn (ι := ℕ) φ H 0 corridor
  have hE : MeasurableSet E := measurableSet_hasPathHistoryIn φ H 0 corridor hC
  let s := {ξ : Step ℕ X | totalPotentialWeight φ (-1) ξ ≠ ∞}
  have hs : MeasurableSet s := (measurableSet_eq_fun
    (totalPotentialWeight_measurable φ (-1)) measurable_const).compl
  have hμ : μ s = 1 := by
    have h := (ae_mem_iff_measure_eq hs.nullMeasurableSet).1 hweight
    simpa using h
  have hall := RootIndexed.stepFieldLaw_ae_all_of_measure_one (Root := Fin m) hs μ hμ
  have hinclusion : ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      (¬ ∃ p ∈ P H field, RootIndexed.position (fun _ : Fin m => 0) φ field p.1 p.2 ∈ terminal) →
        ∀ r : Fin m, field r ∉ E := by
    filter_upwards [hall] with field hfield
    intro hempty r hr
    obtain ⟨u, hu, hsurvive, hpath⟩ := hr
    have hrelative := hfit (pathHistory φ H 0 (field r) u) hpath
      (by simpa using pathHistory_zero φ H 0 (field r) u)
    have hmem := mem_ofRestartedRealPositionSets_of_path
      (fun _ : Fin m => (0 : ℝ)) φ φ.measurable_toFun
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff H window hwindow upper hupper
      field r u hu (by simp [RootIndexed.mem_initialPopulation_iff]) hsurvive
      (fun v _ => hfield r v) (fun k hk => ?_)
    · apply hempty
      refine ⟨(r, u), hmem, ?_⟩
      have hx := hterminal _ hpath
      change pathHistory φ H 0 (field r) u ⟨H, Nat.lt_succ_self H⟩ ∈ terminal at hx
      rw [pathHistory_last φ H 0 (field r) u hu] at hx
      simpa [RootIndexed.position, RootIndexed.displace, Spine.pathPotential] using hx
    · let i : Fin (H + 1) := ⟨k, by omega⟩
      let a : Fin (H + 1) := ⟨restartAnchor cutoff k,
        (restartAnchor_le cutoff k).trans_lt (by omega)⟩
      have h := hrelative i
      change pathHistory φ H 0 (field r) u i - pathHistory φ H 0 (field r) u a ∈ window k at h
      rw [pathHistory_eq_positionAtGeneration (fun _ : Fin m => 0) φ φ.measurable_toFun
          H field (r, u) hu i,
        pathHistory_eq_positionAtGeneration (fun _ : Fin m => 0) φ φ.measurable_toFun
          H field (r, u) hu a] at h
      simpa [RootIndexed.relativePositionAtGeneration, RootIndexed.positionAtGeneration,
        i, a, List.take_take, Nat.min_eq_left (restartAnchor_le cutoff k)] using h
  exact (measure_mono_ae (s := {field | ¬ ∃ p ∈ P H field,
    RootIndexed.position (fun _ : Fin m => 0) φ field p.1 p.2 ∈ terminal})
    (t := {field | ∀ r : Fin m, field r ∉ E}) hinclusion).trans
    (RootIndexed.measure_finiteRootEventAvoidance_le_exp μ E hE m q hq hq_one hprob)

end ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation
