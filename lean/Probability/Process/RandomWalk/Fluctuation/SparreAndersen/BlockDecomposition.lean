/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.InclusionExclusion

/-!
# Prefix inequalities for cyclic survival blocks

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_partialSum_le_of_start_le`:
  if the rotation at $k$ survives and $k\le t\le n$, then $S_k\le S_t$.
- `ProbabilityTheory.RandomWalk.cyclicSurvivalEvent_partialSum_le_of_before_start`:
  if the rotation at $k$ survives and $0\le t<k$, then
  $S_k\le S_n+S_t$.
- `ProbabilityTheory.RandomWalk.mem_cyclicSurvivalEvent_iff_partialSum`:
  the endpoint condition $S_n\ge0$ and these two families of prefix
  inequalities characterize $B_n^{k+1}$.
- `ProbabilityTheory.RandomWalk.mem_two_cyclicSurvivalEvents_iff_twoBlocks`:
  for $a<b$, $B_n^{a+1}\cap B_n^{b+1}$ is exactly survival on the
  disjoint cyclic blocks $[a,b)$ and $[b,n)\cup[0,a)$.
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent`:
  the adjacent-block conditions for any nonempty finite set of starts.
- `ProbabilityTheory.RandomWalk.precedingStarts`:
  for a time $t$, the selected starts strictly before $t$.
- `ProbabilityTheory.RandomWalk.mem_cyclicBlockEvent_of_forall_cyclicSurvivalEvent`:
  survival from every selected start implies every adjacent-block condition.
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent_selected_partialSum_mono`:
  the partial sums at selected block starts are nondecreasing in their
  natural order.
- `ProbabilityTheory.RandomWalk.forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent`:
  adjacent-block survival implies survival from every selected cyclic start.
- `ProbabilityTheory.RandomWalk.iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent`:
  the full event identity (A.5) for any nonempty set of selected starts.
- `ProbabilityTheory.RandomWalk.measurableSet_cyclicBlockEvent`:
  the adjacent-block event is measurable under every finite product law.
- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicBlock_sum`:
  $\mathbb P(S_n\ge0)$ is the alternating sum of the probabilities of
  adjacent-block events indexed by nonempty subsets of starts.

These are the two kinds of inequalities in the event $B_n^{k+1}$ of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events
in the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equation (A.3) (arXiv:cond-mat/9905252). They are the
pointwise ingredients of the block decomposition in equation (A.5).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A surviving rotation has nonnegative partial sums from its start
up to every later time before the end of the original vector. -/
theorem cyclicSurvivalEvent_partialSum_le_of_start_le
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : Fin (n + 1))
    (hkt : k.val ≤ t.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤ Fin.partialSum x t := by
  let j : Fin (n + 1) := ⟨t.val - k.val, by omega⟩
  have hsum : k.val + j.val ≤ n := by dsimp [j]; omega
  have hindex :
      (⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) = t := by
    apply Fin.ext
    dsimp [j]
    omega
  have hj := hx j
  change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
  simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex] at hj
  linarith

/-- A surviving rotation has nonnegative wrapped partial sums after
reaching the end of the original vector. -/
theorem cyclicSurvivalEvent_partialSum_le_of_before_start
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : Fin (n + 1))
    (htk : t.val < k.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤
      Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
  by_cases htzero : t.val = 0
  · have ht : t = 0 := Fin.ext htzero
    subst t
    have hlast := cyclicSurvivalEvent_partialSum_le_of_start_le
      x k (Fin.last n) (by simp [Fin.val_last, Nat.le_of_lt k.isLt]) hx
    simpa using hlast
  · let j : Fin (n + 1) := ⟨n - k.val + t.val, by omega⟩
    have hwrap : ¬ k.val + j.val ≤ n := by dsimp [j]; omega
    have hindex :
        (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1)) = t := by
      apply Fin.ext
      dsimp [j]
      omega
    have hj := hx j
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
    simp only [Fin.cyclicPartialSum, dite_eq_right hwrap, hindex] at hj
    linarith

/-- The explicit two-part description of the cyclic event $B_n^{k+1}$
in Bauer--Godrèche--Luck, Appendix A, equation (A.3). -/
theorem mem_cyclicSurvivalEvent_iff_partialSum
    {n : ℕ} (x : Fin n → ℝ) (k : Fin n) :
    x ∈ cyclicSurvivalEvent k ↔
      0 ≤ Fin.partialSum x (Fin.last n) ∧
      (∀ t : Fin (n + 1), k.val ≤ t.val →
        Fin.partialSum x k.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), t.val < k.val →
        Fin.partialSum x k.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t) := by
  constructor
  · intro hx
    have hlast := hx (Fin.last n)
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k (Fin.last n) at hlast
    rw [Fin.cyclicPartialSum_last_eq_of_zero
      (Fin.partialSum x) (Fin.partialSum_zero x) k] at hlast
    exact ⟨hlast, fun t hkt =>
      cyclicSurvivalEvent_partialSum_le_of_start_le x k t hkt hx,
      fun t htk =>
        cyclicSurvivalEvent_partialSum_le_of_before_start x k t htk hx⟩
  · rintro ⟨hlast, hfirst, hsecond⟩
    intro j
    by_cases hjlast : j = Fin.last n
    · subst j
      simpa [Fin.cyclicPartialSum_last_eq_of_zero
        (Fin.partialSum x) (Fin.partialSum_zero x) k] using hlast
    by_cases hsum : k.val + j.val ≤ n
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩
      have hkt : k.val ≤ t.val := by dsimp [t]; omega
      have h := hfirst t hkt
      have hnonneg :
          0 ≤ Fin.partialSum x t - Fin.partialSum x k.castSucc := by
        linarith
      simpa only [cyclicSurvivalEvent, Fin.cyclicPartialSum,
        dite_eq_left hsum] using hnonneg
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val - n, by omega⟩
      have htk : t.val < k.val := by
        dsimp [t]
        have hj : j.val < n := by
          have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
          have hjne : j.val ≠ n := by
            intro heq
            exact hjlast (Fin.ext (by simpa [Fin.val_last] using heq))
          omega
        omega
      have h := hsecond t htk
      have hnonneg :
          0 ≤ Fin.partialSum x (Fin.last n) -
            Fin.partialSum x k.castSucc + Fin.partialSum x t := by
        linarith
      simpa only [Fin.cyclicPartialSum, dite_eq_right hsum] using hnonneg

/-- The two-start case of Bauer--Godrèche--Luck, Appendix A,
equation (A.5): the intersection of two cyclic survival events is the
product condition on the two consecutive cyclic blocks. -/
theorem mem_two_cyclicSurvivalEvents_iff_twoBlocks
    {n : ℕ} (x : Fin n → ℝ) (a b : Fin n) (hab : a < b) :
    x ∈ cyclicSurvivalEvent a ∧ x ∈ cyclicSurvivalEvent b ↔
      (∀ t : Fin (n + 1), a.val ≤ t.val → t.val ≤ b.val →
        Fin.partialSum x a.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), b.val ≤ t.val →
        Fin.partialSum x b.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), t.val ≤ a.val →
        Fin.partialSum x b.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t) := by
  have habval : a.val < b.val := hab
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨_, haFirst, _⟩ :=
      (mem_cyclicSurvivalEvent_iff_partialSum x a).mp ha
    obtain ⟨_, hbFirst, hbSecond⟩ :=
      (mem_cyclicSurvivalEvent_iff_partialSum x b).mp hb
    refine ⟨fun t hat _ => haFirst t hat,
      hbFirst, fun t hta => ?_⟩
    exact hbSecond t (by omega)
  · rintro ⟨hfirstBlock, hsecondBlock, hwrapBlock⟩
    have hAB : Fin.partialSum x a.castSucc ≤
        Fin.partialSum x b.castSucc :=
      hfirstBlock b.castSucc (Nat.le_of_lt habval) le_rfl
    have hwrapAtA : Fin.partialSum x b.castSucc ≤
        Fin.partialSum x (Fin.last n) +
          Fin.partialSum x a.castSucc :=
      hwrapBlock a.castSucc le_rfl
    have hlast : 0 ≤ Fin.partialSum x (Fin.last n) := by
      linarith
    constructor
    · apply (mem_cyclicSurvivalEvent_iff_partialSum x a).mpr
      refine ⟨hlast, ?_, ?_⟩
      · intro t hat
        by_cases htb : t.val ≤ b.val
        · exact hfirstBlock t hat htb
        · have hbt : b.val ≤ t.val := by omega
          have hb := hsecondBlock t hbt
          linarith
      · intro t hta
        have hb := hwrapBlock t (Nat.le_of_lt hta)
        linarith
    · apply (mem_cyclicSurvivalEvent_iff_partialSum x b).mpr
      refine ⟨hlast, hsecondBlock, ?_⟩
      intro t htb
      by_cases hta : t.val ≤ a.val
      · exact hwrapBlock t hta
      · have hat : a.val ≤ t.val := by omega
        have htb' : t.val ≤ b.val := Nat.le_of_lt htb
        have ha := hfirstBlock t hat htb'
        linarith

/-- The selected start positions strictly before time `t`. -/
def precedingStarts {n : ℕ} (u : Finset (Fin n))
    (t : Fin (n + 1)) : Finset (Fin n) :=
  u.filter fun k => k.val < t.val

/-- The adjacent-block event from Bauer--Godrèche--Luck, Appendix A,
equation (A.5), indexed by a nonempty finite set of cyclic starts. At
time `t`, the predecessor in `u` gives the current block; before the
first start, the last block wraps across time `n`. -/
def cyclicBlockEvent {n : ℕ} (u : Finset (Fin n))
    (hu : u.Nonempty) : Set (Fin n → ℝ) :=
  {x | ∀ t : Fin (n + 1),
    if h : (precedingStarts u t).Nonempty then
      Fin.partialSum x ((precedingStarts u t).max' h).castSucc ≤
        Fin.partialSum x t
    else
      Fin.partialSum x (u.max' hu).castSucc ≤
        Fin.partialSum x (Fin.last n) + Fin.partialSum x t}

/-- Each selected cyclic survival event supplies the corresponding
adjacent-block inequalities. This is the immediate direction of
Bauer--Godrèche--Luck, Appendix A, equation (A.5). -/
theorem mem_cyclicBlockEvent_of_forall_cyclicSurvivalEvent
    {n : ℕ} (x : Fin n → ℝ) (u : Finset (Fin n))
    (hu : u.Nonempty)
    (hx : ∀ k ∈ u, x ∈ cyclicSurvivalEvent k) :
    x ∈ cyclicBlockEvent u hu := by
  intro t
  by_cases hpred : (precedingStarts u t).Nonempty
  · have hp := (precedingStarts u t).max'_mem hpred
    have hpu : (precedingStarts u t).max' hpred ∈ u :=
      (Finset.mem_filter.mp hp).1
    have hpt : ((precedingStarts u t).max' hpred).val < t.val :=
      (Finset.mem_filter.mp hp).2
    have hle := cyclicSurvivalEvent_partialSum_le_of_start_le
      x ((precedingStarts u t).max' hpred) t
      (Nat.le_of_lt hpt) (hx _ hpu)
    simpa [cyclicBlockEvent, hpred] using hle
  · let m := u.max' hu
    have hmU : m ∈ u := u.max'_mem hu
    have htm : t.val ≤ m.val := by
      by_contra hgt
      have hmPred : m ∈ precedingStarts u t :=
        Finset.mem_filter.mpr ⟨hmU, by omega⟩
      exact hpred ⟨m, hmPred⟩
    have hB := hx m hmU
    by_cases hlt : t.val < m.val
    · have hle := cyclicSurvivalEvent_partialSum_le_of_before_start
        x m t hlt hB
      simpa [cyclicBlockEvent, hpred, m] using hle
    · have hEq : t = m.castSucc := Fin.ext (by simp; omega)
      have hlast := (mem_cyclicSurvivalEvent_iff_partialSum x m).mp hB |>.1
      have hle : Fin.partialSum x m.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
        rw [hEq]
        linarith
      simpa [cyclicBlockEvent, hpred, m] using hle

/-- Adjacent-block survival makes the partial sums at selected block
starts nondecreasing. -/
theorem cyclicBlockEvent_selected_partialSum_mono
    {n : ℕ} (x : Fin n → ℝ) (u : Finset (Fin n))
    (hu : u.Nonempty) (hx : x ∈ cyclicBlockEvent u hu)
    {a b : Fin n} (ha : a ∈ u) (hb : b ∈ u) (hab : a ≤ b) :
    Fin.partialSum x a.castSucc ≤ Fin.partialSum x b.castSucc := by
  have hmono (l : Fin n) :
      ∀ (hl : l ∈ u) (k : Fin n), k ∈ u → k ≤ l →
        Fin.partialSum x k.castSucc ≤ Fin.partialSum x l.castSucc := by
    induction l using Fin.strong_induction_on with
    | h l ih =>
      intro hl k hk hkl
      by_cases hEq : k = l
      · subst k
        exact le_refl _
      have hklStrict : k < l := lt_of_le_of_ne hkl hEq
      have hpred : (precedingStarts u l.castSucc).Nonempty := by
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩⟩
        exact hklStrict
      let p := (precedingStarts u l.castSucc).max' hpred
      have hpMem := (precedingStarts u l.castSucc).max'_mem hpred
      have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
      have hpLt : p < l := (Finset.mem_filter.mp hpMem).2
      have hkp : k ≤ p :=
        (precedingStarts u l.castSucc).le_max' k
          (Finset.mem_filter.mpr ⟨hk, hklStrict⟩)
      have hlocal := hx l.castSucc
      have hpl : Fin.partialSum x p.castSucc ≤
          Fin.partialSum x l.castSucc := by
        simpa [cyclicBlockEvent, hpred, p] using hlocal
      exact (ih p hpLt hpU k hk hkp).trans hpl
  exact hmono b hb a ha hab

/-- The adjacent-block conditions imply every selected cyclic survival
event. The proof sums nonnegative complete blocks before the block
containing the requested time, as in Bauer--Godrèche--Luck,
Appendix A, equation (A.5). -/
theorem forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent
    {n : ℕ} (x : Fin n → ℝ) (u : Finset (Fin n))
    (hu : u.Nonempty) (hx : x ∈ cyclicBlockEvent u hu) :
    ∀ k ∈ u, x ∈ cyclicSurvivalEvent k := by
  let first := u.min' hu
  let last := u.max' hu
  have hfirstU : first ∈ u := u.min'_mem hu
  have hlastU : last ∈ u := u.max'_mem hu
  have hwrapPred : ¬ (precedingStarts u first.castSucc).Nonempty := by
    rintro ⟨p, hp⟩
    have hpU : p ∈ u := (Finset.mem_filter.mp hp).1
    have hpLt : p < first := (Finset.mem_filter.mp hp).2
    exact (not_lt_of_ge (u.min'_le p hpU)) hpLt
  have hwrapAtFirst := hx first.castSucc
  have hlastFirst : Fin.partialSum x last.castSucc ≤
      Fin.partialSum x (Fin.last n) +
        Fin.partialSum x first.castSucc := by
    simpa [cyclicBlockEvent, hwrapPred, first, last] using hwrapAtFirst
  have hfirstLast : Fin.partialSum x first.castSucc ≤
      Fin.partialSum x last.castSucc :=
    cyclicBlockEvent_selected_partialSum_mono x u hu hx
      hfirstU hlastU (u.min'_le_max' hu)
  have htotal : 0 ≤ Fin.partialSum x (Fin.last n) := by
    linarith
  intro k hk
  apply (mem_cyclicSurvivalEvent_iff_partialSum x k).mpr
  refine ⟨htotal, ?_, ?_⟩
  · intro t hkt
    by_cases hEq : t.val = k.val
    · have ht : t = k.castSucc := Fin.ext (by simpa using hEq)
      rw [ht]
    have hktStrict : k.val < t.val := by omega
    have hpred : (precedingStarts u t).Nonempty := by
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hktStrict⟩⟩
    let p := (precedingStarts u t).max' hpred
    have hpMem := (precedingStarts u t).max'_mem hpred
    have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
    have hkp : k ≤ p :=
      (precedingStarts u t).le_max' k
        (Finset.mem_filter.mpr ⟨hk, hktStrict⟩)
    have hlocal := hx t
    have hpt : Fin.partialSum x p.castSucc ≤
        Fin.partialSum x t := by
      simpa [cyclicBlockEvent, hpred, p] using hlocal
    exact (cyclicBlockEvent_selected_partialSum_mono x u hu hx
      hk hpU hkp).trans hpt
  · intro t htk
    have hkLast : Fin.partialSum x k.castSucc ≤
        Fin.partialSum x last.castSucc :=
      cyclicBlockEvent_selected_partialSum_mono x u hu hx
        hk hlastU (u.le_max' k hk)
    by_cases hpred : (precedingStarts u t).Nonempty
    · let p := (precedingStarts u t).max' hpred
      have hpMem := (precedingStarts u t).max'_mem hpred
      have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
      have hfirstP : Fin.partialSum x first.castSucc ≤
          Fin.partialSum x p.castSucc :=
        cyclicBlockEvent_selected_partialSum_mono x u hu hx
          hfirstU hpU (u.min'_le p hpU)
      have hlocal := hx t
      have hpt : Fin.partialSum x p.castSucc ≤
          Fin.partialSum x t := by
        simpa [cyclicBlockEvent, hpred, p] using hlocal
      linarith
    · have hlocal := hx t
      have hlt : Fin.partialSum x last.castSucc ≤
          Fin.partialSum x (Fin.last n) +
            Fin.partialSum x t := by
        simpa [cyclicBlockEvent, hpred, last] using hlocal
      linarith

/-- Bauer--Godrèche--Luck, Appendix A, equation (A.5), for any nonempty
finite set of selected cyclic starts: the intersection of the cyclic
survival events equals the adjacent-block event. -/
theorem iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent
    {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty) :
    (⋂ k ∈ u, cyclicSurvivalEvent k) = cyclicBlockEvent u hu := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · exact mem_cyclicBlockEvent_of_forall_cyclicSurvivalEvent x u hu
  · exact forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent x u hu

/-- The adjacent-block event is measurable because it is a finite
intersection of measurable cyclic survival events. -/
theorem measurableSet_cyclicBlockEvent
    {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty) :
    MeasurableSet (cyclicBlockEvent u hu) := by
  rw [← iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent u hu]
  exact MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => measurableSet_cyclicSurvivalEvent k

/-- Substituting the block decomposition (A.5) into the finite
inclusion--exclusion identity (A.4) of Bauer--Godrèche--Luck,
Appendix A. -/
theorem measureReal_nonnegative_endpoint_eq_cyclicBlock_sum
    {n : ℕ} (hn : 0 < n) (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] :
    μ.real {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          μ.real (if h : u.Nonempty then cyclicBlockEvent u h else ∅) := by
  rw [measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum hn μ]
  apply Finset.sum_congr rfl
  intro u hu
  have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
  simp only [dite_eq_left hnonempty]
  rw [iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent u hnonempty]

end ProbabilityTheory.RandomWalk

end
