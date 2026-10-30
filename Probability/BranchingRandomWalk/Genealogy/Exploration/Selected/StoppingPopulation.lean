/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Mathlib.Probability.Process.Stopping
public import Probability.BranchingRandomWalk.Population.Processes.Selected.Basic

/-!
# Branching for a finite multi-root population at a stopping time

## Public declarations

The public declarations in namespace `ProbabilityTheory.BranchingRandomWalk`
are:

- `selectedPopulationAt N x τ ω` is
  \[
    \begin{cases}
      \varnothing,&\tau(\omega)=\top,\\
      \operatorname{selectedPopulation}(N,x,n,\omega),&\tau(\omega)=n.
    \end{cases}
  \]
- `selectedPopulationAt_cell_measurable N x τ hτ hfinite s` proves that the
  event of population value `s` is measurable in the stopped domain.
- `selectedPopulationAt_depth N x τ ω u hu n hn` states that every address in
  the selected population has length `n` whenever `τ ω = n`.

The selected law on each cell and the countable cell-mass sum are recorded in
`Selected/CellBranching/Stopping/RandomSize.lean`; the latter uses Mathlib's
general countable-fibre measure theorem. The partition includes `s = ∅`, so
extinction needs no separate case.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-! The concrete selected population read at a random generation. -/

noncomputable def selectedPopulationAt
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ) :
    FiniteRootStepField m ℕ ℝ → Finset (RootAddress m ℕ) :=
  fun ω => match τ ω with
    | ⊤ => ∅
    | (n : ℕ) => selectedPopulation N x n ω

theorem selectedPopulationAt_cell_measurable {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m ℕ)) :
    MeasurableSet[hτ.measurableSpace]
      {ω | selectedPopulationAt N x τ ω = s} := by
  classical
  let U : Set (FiniteRootStepField m ℕ ℝ) :=
    ⋃ n : ℕ, {ω | τ ω = (n : WithTop ℕ)} ∩
      {ω | selectedPopulation N x n ω = s}
  have hU : MeasurableSet[hτ.measurableSpace] U := by
    apply MeasurableSet.iUnion
    intro n
    have ht : MeasurableSet[hτ.measurableSpace]
        {ω | τ ω = (n : WithTop ℕ)} :=
      hτ.measurable (measurableSet_singleton (n : WithTop ℕ))
    have hp : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
        {ω | selectedPopulation N x n ω = s} :=
      selectedPopulation_adapted N x n (measurableSet_singleton s)
    have htgen' := (hτ.measurableSet_inter_eq_iff Set.univ n).1
        (MeasurableSet.univ.inter
          (hτ.measurable (measurableSet_singleton (n : WithTop ℕ))))
    have htgen : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
        {ω | τ ω = (n : WithTop ℕ)} := by
      (convert htgen' using 1; simp)
    have hpn := (hτ.measurableSet_inter_eq_iff
      {ω | selectedPopulation N x n ω = s} n).2
      (by simpa [Set.inter_comm] using htgen.inter hp)
    simpa [Set.inter_comm] using hpn
  have heq : {ω | selectedPopulationAt N x τ ω = s} = U := by
    ext ω
    constructor
    · intro hs
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          apply Set.mem_iUnion.mpr
          refine ⟨n, ?_, ?_⟩
          · exact htime
          · change selectedPopulationAt N x τ ω = s at hs
            simpa [selectedPopulationAt, htime] using hs
    · intro hs
      obtain ⟨n, ht, hp⟩ := Set.mem_iUnion.mp hs
      change selectedPopulationAt N x τ ω = s
      change (match τ ω with
        | ⊤ => ∅
        | (n : ℕ) => selectedPopulation N x n ω) = s
      rw [ht]
      exact hp
  rw [heq]
  exact hU

theorem selectedPopulationAt_depth {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootStepField m ℕ ℝ → WithTop ℕ)
    (ω : FiniteRootStepField m ℕ ℝ) (u : RootAddress m ℕ)
    (hu : u ∈ selectedPopulationAt N x τ ω) :
    ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n := by
  intro n hn
  simpa [selectedPopulationAt, hn] using
    selectedPopulation_depth N x n ω u (by simpa [selectedPopulationAt, hn] using hu)

end ProbabilityTheory.BranchingRandomWalk
