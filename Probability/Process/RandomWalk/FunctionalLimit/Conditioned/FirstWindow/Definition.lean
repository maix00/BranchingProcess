/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Adapted.Filtration
public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Process.RandomWalk.Path.Block.Law.Basic

/-!
# The prefix event for a first surviving window

The public declarations in this module are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.NoEarlierSurvivingPrefix`:
  for a candidate start $j$, the complement $B_j^c$ of Bolthausen's event
  that some earlier start survives until $\min(j,s+n)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.isFirstSurvivingWindow_iff_prefixFailure_and_survives`:
  $\{T_n=j\}=B_j^c\cap\{S_{j+k}\ge S_j,\ 1\le k\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurableSet_noEarlierSurvivingPrefix_prefix`:
  $B_j^c$ is measurable with respect to the first $j$ increments.

These are the event description and prefix measurability in Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks
Conditioned to Stay Positive*, Lemma 3.1, pp. 482--483, Ann. Probab.
4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The complement of Bolthausen's prefix event $B_j$: every earlier
start $s<j$ has already fallen strictly below $S_s$ by time
$\min(j,s+n)$. This depends only on the first $j$ increments.
See Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1, p. 482,
DOI 10.1214/aop/1176996098. -/
def NoEarlierSurvivingPrefix (n start : ℕ) (increment : ℕ → ℝ) : Prop :=
  ¬ ∃ s : Fin start, ∀ r : ℕ,
    (s : ℕ) < r → r ≤ min start ((s : ℕ) + n) →
      AdditivePath.displacement s increment ≤
        AdditivePath.displacement r increment

/-- Bolthausen's first window at $j$ is the intersection of the
prefix event $B_j^c$ and survival of the independent length-$n$ suffix.
This is the set identity used in Lemma 3.1, pp. 482--483. -/
lemma isFirstSurvivingWindow_iff_prefixFailure_and_survives
    (n start : ℕ) (increment : ℕ → ℝ) :
    IsFirstSurvivingWindow n start increment ↔
      NoEarlierSurvivingPrefix n start increment ∧
        SurvivesNonnegative n (fun k => increment (start + k)) := by
  constructor
  · intro hfirst
    refine ⟨?_, hfirst.1⟩
    intro hprefix
    obtain ⟨s, hs⟩ := hprefix
    apply hfirst.2 s
    apply (SurvivesNonnegative.shift_iff n s increment).2
    intro k
    let r := (s : ℕ) + ((k : ℕ) + 1)
    have hrle : r ≤ (s : ℕ) + n := by
      dsimp [r]
      omega
    by_cases hr : r ≤ start
    · exact hs r (by dsimp [r]; omega) (le_min hr hrle)
    · have hbefore : AdditivePath.displacement s increment ≤
          AdditivePath.displacement start increment :=
        hs start s.isLt (le_min le_rfl (by omega))
      have hindex : r - start - 1 < n := by
        dsimp [r] at *
        omega
      have hafter :=
        (SurvivesNonnegative.shift_iff n start increment).1 hfirst.1
          ⟨r - start - 1, hindex⟩
      have hrpos : start + ((r - start - 1) + 1) = r := by omega
      rw [hrpos] at hafter
      exact hbefore.trans hafter
  · rintro ⟨hprefix, hsurvive⟩
    refine ⟨hsurvive, ?_⟩
    intro s hwindow
    apply hprefix
    refine ⟨s, ?_⟩
    intro r hsr hrbound
    have hrle : r ≤ (s : ℕ) + n := (le_min_iff.mp hrbound).2
    have hindex : r - (s : ℕ) - 1 < n := by omega
    have hposition :=
      (SurvivesNonnegative.shift_iff n s increment).1 hwindow
        ⟨r - (s : ℕ) - 1, hindex⟩
    have hrpos : (s : ℕ) + ((r - (s : ℕ) - 1) + 1) = r := by omega
    rwa [hrpos] at hposition

/-- The event $B_j^c$ in Bolthausen's Lemma 3.1 is measurable with
respect to the first $j$ increments. -/
lemma measurableSet_noEarlierSurvivingPrefix_prefix (n start : ℕ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) start]
      {increment : ℕ → ℝ | NoEarlierSurvivingPrefix n start increment} := by
  let viable (s : Fin start) : Set (ℕ → ℝ) :=
    ⋂ r : ℕ,
      {increment | (s : ℕ) < r → r ≤ min start ((s : ℕ) + n) →
        AdditivePath.displacement s increment ≤
          AdditivePath.displacement r increment}
  have hviable (s : Fin start) :
      MeasurableSet[sequencePrefixFiltration (E := ℝ) start] (viable s) := by
    apply MeasurableSet.iInter
    intro r
    by_cases hr : (s : ℕ) < r ∧ r ≤ min start ((s : ℕ) + n)
    · have hrstart : r ≤ start := (le_min_iff.mp hr.2).1
      have hset :
          {increment : ℕ → ℝ | (s : ℕ) < r →
            r ≤ min start ((s : ℕ) + n) →
            AdditivePath.displacement s increment ≤
              AdditivePath.displacement r increment} =
          {increment | AdditivePath.displacement s increment ≤
            AdditivePath.displacement r increment} := by
        ext increment
        simp [hr.1, hr.2]
      rw [hset]
      exact measurableSet_le
        (displacement_measurable_prefix (E := ℝ) s.isLt.le)
        (displacement_measurable_prefix (E := ℝ) hrstart)
    · have hset :
          {increment : ℕ → ℝ | (s : ℕ) < r →
            r ≤ min start ((s : ℕ) + n) →
            AdditivePath.displacement s increment ≤
              AdditivePath.displacement r increment} = Set.univ := by
        ext increment
        by_cases hsr : (s : ℕ) < r
        · have hrle : ¬ r ≤ min start ((s : ℕ) + n) := by
            intro hle
            exact hr ⟨hsr, hle⟩
          simp [hsr, hrle]
        · simp [hsr]
      rw [hset]
      exact MeasurableSet.univ
  rw [show {increment : ℕ → ℝ | NoEarlierSurvivingPrefix n start increment} =
    (⋃ s : Fin start, viable s)ᶜ by
      ext increment
      simp [NoEarlierSurvivingPrefix, viable]]
  exact (MeasurableSet.iUnion hviable).compl

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
