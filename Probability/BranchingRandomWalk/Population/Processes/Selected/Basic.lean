/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Candidates.Leftmost
import Probability.BranchingRandomWalk.Population.Candidates.Adapted
import MeasureTheory.MeasurableSpace.CountableEvaluation

/-!
# A measurable multi-root finite-candidate selection process

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.finiteLeftmostAtGeneration_of_adapted`:
  if the finite candidate pool at generation \(n\) is adapted, selecting its
  first \(N\) particles by the leftmost order remains adapted.
- `ProbabilityTheory.BranchingRandomWalk.selectedPopulation`: defines one
  recursively selected population from all \(m\) labelled roots.
- `ProbabilityTheory.BranchingRandomWalk.selectedPopulation_adapted`:
  under the stated measurable-selection premise, every selected generation
  is adapted to the multi-root domain flow.
- `ProbabilityTheory.BranchingRandomWalk.selectedPopulation_depth`:
  particles in generation \(n\) have address length \(n\).
- `ProbabilityTheory.BranchingRandomWalk.selectedPopulation_card_le`:
  every generation contains at most \(N\) selected particles.
- `ProbabilityTheory.BranchingRandomWalk.selectedPopulation_nonempty_of_first_child`:
  a first selected child at every nonempty generation keeps the selected population
  nonempty.

All `m` initial roots enter one common selection pool. At each generation
the process examines the first `N` child slots of every retained parent,
then keeps candidates of finite rank below `N`, with address-code tie
breaking. The process and full labelled population are adapted to the
multi-root domain filtration. `FullCandidateTruncation` proves equality
with full countable-child selection under ordered marks.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

theorem finiteLeftmostAtGeneration_of_adapted {m : ℕ}
    (N n : ℕ) (x : Fin m → ℝ)
    (candidates : FiniteRootStepField m ℕ ℝ → Finset (RootAddress m ℕ))
    (hcandidates : Measurable[multiRootStepFiltration (m := m) (X := ℝ) n] candidates) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (fun ω => finiteLeftmostAtGeneration N n x ω (candidates ω)) := by
  exact @Measurable.eval_of_countable_range
    (FiniteRootStepField m ℕ ℝ) (Finset (RootAddress m ℕ))
    (Finset (RootAddress m ℕ))
    (multiRootStepFiltration (m := m) (X := ℝ) n) inferInstance
    (fun ω s => finiteLeftmostAtGeneration N n x ω s) candidates
    (fun s _ => finiteLeftmostAtGeneration_fixed_measurable N n x s)
    (fun s _ => hcandidates (measurableSet_singleton s))
    (Set.Countable.mono (Set.subset_univ (Set.range candidates))
      Set.countable_univ)

/-- One common selected population from `m` labelled initial ancestors. -/
noncomputable def selectedPopulation {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) :
    ℕ → FiniteRootStepField m ℕ ℝ → Finset (RootAddress m ℕ)
  | 0, _ => initialRootAddresses m
  | n + 1, ω =>
      finiteLeftmostAtGeneration N (n + 1) x ω
        (multiRootCandidatesAtGeneration N n
          (selectedPopulation N x n ω) ω)

theorem selectedPopulation_adapted {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) :
    ∀ n, Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (selectedPopulation N x n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hcandidates := multiRootCandidatesAtGeneration_of_adapted
        N n (selectedPopulation N x n) ih
      exact finiteLeftmostAtGeneration_of_adapted N (n + 1) x
        (fun ω => multiRootCandidatesAtGeneration N n
          (selectedPopulation N x n ω) ω) hcandidates

theorem selectedPopulation_depth {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : FiniteRootStepField m ℕ ℝ)
    (p : RootAddress m ℕ) (hp : p ∈ selectedPopulation N x n ω) :
    p.2.length = n := by
  cases n with
  | zero =>
      simp [selectedPopulation, initialRootAddresses] at hp
      obtain ⟨i, _, rfl⟩ := hp
      rfl
  | succ n =>
      unfold selectedPopulation at hp
      unfold finiteLeftmostAtGeneration finiteLeftmost at hp
      have hcandidate : p ∈
          (multiRootCandidatesAtGeneration N n
            (selectedPopulation N x n ω) ω).filter
              (fun q => q.2.length = n + 1) :=
        (Finset.mem_filter.mp hp).1
      exact (Finset.mem_filter.mp hcandidate).2

/-- After the first selection step, the common population contains at most
`N` particles across all initial ancestors. -/
theorem selectedPopulation_card_le {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : FiniteRootStepField m ℕ ℝ) :
    (selectedPopulation N x (n + 1) ω).card ≤ N := by
  unfold selectedPopulation finiteLeftmostAtGeneration
  exact finiteLeftmost_card_le N x ω _

/-- Nonextinction holds on the pathwise event that every reproduction mark
encountered in the pre-sampled forest has a realized slot-zero child. Under
ordered support, the almost-sure at-least-one-child assumption gives
this event almost surely. -/
theorem selectedPopulation_nonempty_of_first_child {m : ℕ}
    (hm : 0 < m) (N : ℕ) (hN : 0 < N)
    (x : Fin m → ℝ) (ω : FiniteRootStepField m ℕ ℝ)
    (hfirst : ∀ r u, survive (ω r u) 0) :
    ∀ n, (selectedPopulation N x n ω).Nonempty := by
  classical
  intro n
  induction n with
  | zero =>
      let i : Fin m := ⟨0, hm⟩
      refine ⟨(i, []), ?_⟩
      change (i, ([] : List ℕ)) ∈ initialRootAddresses (α := ℕ) m
      rw [initialRootAddresses, Finset.mem_map]
      exact ⟨i, Finset.mem_univ _, rfl⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      let C := multiRootCandidatesAtGeneration N n
        (selectedPopulation N x n ω) ω
      have hpC : RootIndexed.childAddress p 0 ∈ C := by
        unfold C multiRootCandidatesAtGeneration
        apply multiRootCandidates_first_mem hN _ ω p
        · exact Finset.mem_filter.mpr
            ⟨hp, selectedPopulation_depth N x n ω p hp⟩
        · exact hfirst p.1 p.2
      have hC : C.Nonempty := ⟨RootIndexed.childAddress p 0, hpC⟩
      have hCdepth : ∀ q ∈ C, q.2.length = n + 1 := by
        intro q hq
        exact multiRootCandidatesAtGeneration_depth N n _ ω q hq
      have hfilter : C.filter (fun q => q.2.length = n + 1) = C :=
        Finset.filter_true_of_mem hCdepth
      change (finiteLeftmostAtGeneration N (n + 1) x ω C).Nonempty
      simp only [finiteLeftmostAtGeneration, hfilter]
      exact finiteLeftmost_nonempty N hN x ω C hC

end ProbabilityTheory.BranchingRandomWalk
