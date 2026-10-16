/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Blocks
public import Probability.Process.RandomWalk.Path.Block.Law.FiniteProduct

/-!
# Probabilities of cyclic survival blocks

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicGapLengthAt`: the cyclic gap length
  at a natural block index, with value zero beyond the selected blocks.
- `ProbabilityTheory.RandomWalk.cyclicGapLength`: if a nonempty set of
  starts is ordered as $a_0<\cdots<a_{q-1}$, the $j$-th cyclic gap has
  length $a_{j+1}-a_j$ for $j+1<q$, and the last gap has length
  $n-a_{q-1}+a_0$.
- `ProbabilityTheory.RandomWalk.cyclicGapLength_pos`: every such gap is
  strictly positive.
- `ProbabilityTheory.RandomWalk.blockStart_cyclicGapLength_eq`:
  the cumulative gap lengths before the $j$-th start equal $a_j-a_0$.
- `ProbabilityTheory.RandomWalk.blockStart_cyclicGapLength_card`:
  the sum of all cyclic gap lengths is $n$.
- `ProbabilityTheory.RandomWalk.blockStart_add_cyclicGapLength_le`:
  each block endpoint lies among the first $n$ rotated increments.
- `ProbabilityTheory.RandomWalk.cyclicCoordinateReindex_block_eq`:
  within block $j$, rotating the full vector at $a_0$ and then moving to
  the block's offset gives the same increment as rotating at $a_j$.
- `ProbabilityTheory.RandomWalk.cyclicGapCoordinates`:
  the $j$-th consecutive increment block of the vector rotated at $a_0$.
- `ProbabilityTheory.RandomWalk.partialSum_cyclicGapCoordinates`:
  partial sums of that block are the cyclic partial sums started at $a_j$.
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent_gapSurvival`:
  every selected adjacent block has nonnegative partial sums on the
  intersection event (A.5).
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent_of_gapSurvival`:
  nonnegative partial sums on all adjacent blocks imply the intersection
  event (A.5).
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent_eq_gapSurvival`:
  (A.5) equals the event that every consecutive cyclic gap has a
  nonnegative partial-sum path.
- `ProbabilityTheory.RandomWalk.measure_pi_cyclicBlockEvent_eq_prod`:
  under an i.i.d. product law, the probability of the intersection in
  (A.5) is the product of the survival probabilities for its gap lengths,
  as in (A.6).
- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicGap_sum`:
  $\mathbb P(S_n\ge0)$ equals the alternating sum over nonempty selected
  starts of the products of their cyclic-gap survival probabilities.

These are the block lengths in M. Bauer, C. Godrèche, and J.-M. Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A, equation (A.6)
(arXiv:cond-mat/9905252).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The sequence of cyclic block lengths, extended by zero after the
last selected start. -/
def cyclicGapLengthAt {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty)
    (i : ℕ) : ℕ :=
  if h : i < u.card then
    let starts := u.orderEmbOfFin rfl
    if hnext : i + 1 < u.card then
      (starts ⟨i + 1, hnext⟩).val - (starts ⟨i, h⟩).val
    else
      n - (starts ⟨i, h⟩).val +
        (starts ⟨0, Finset.card_pos.mpr hu⟩).val
  else 0

/-- The cyclic length from a selected start to the next one, with the
last block wrapping from the largest start back to the smallest. -/
def cyclicGapLength {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : Fin u.card) : ℕ :=
  cyclicGapLengthAt u hu j.val

/-- Every block in the cyclic partition contains at least one increment. -/
theorem cyclicGapLength_pos {n : ℕ} (u : Finset (Fin n))
    (hu : u.Nonempty) (j : Fin u.card) :
    0 < cyclicGapLength u hu j := by
  let starts := u.orderEmbOfFin rfl
  unfold cyclicGapLength
  simp only [cyclicGapLengthAt, dite_eq_left j.isLt]
  by_cases h : j.val + 1 < u.card
  · simp only [dite_eq_left h]
    have hlt : j < (⟨j.val + 1, h⟩ : Fin u.card) := by
      exact Fin.lt_def.mpr (Nat.lt_succ_self _)
    have hstarts := starts.strictMono hlt
    exact Nat.sub_pos_of_lt hstarts
  · simp only [dite_eq_right h]
    have hlt := (starts j).isLt
    omega

/-- Before block `j`, the cyclic partition has traversed the distance
from its first selected start to its `j`-th selected start. -/
theorem blockStart_cyclicGapLength_eq {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : Fin u.card) :
    AdditivePath.blockStart
      (cyclicGapLengthAt u hu)
      j.val =
      (u.orderEmbOfFin rfl j).val -
        (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩).val := by
  let starts := u.orderEmbOfFin rfl
  have hmain (m : ℕ) (hm : m < u.card) :
      AdditivePath.blockStart
        (cyclicGapLengthAt u hu)
        m =
        (starts ⟨m, hm⟩).val -
          (starts ⟨0, Finset.card_pos.mpr hu⟩).val := by
    induction m with
    | zero => simp [AdditivePath.blockStart_zero]
    | succ m ih =>
        have hm' : m < u.card := by omega
        have hih := ih hm'
        rw [AdditivePath.blockStart_succ, hih]
        have hgap : cyclicGapLength u hu ⟨m, hm'⟩ =
            (starts ⟨m + 1, hm⟩).val - (starts ⟨m, hm'⟩).val := by
          simp only [cyclicGapLength, cyclicGapLengthAt,
            dite_eq_left hm', dite_eq_left hm]
          rfl
        change (starts ⟨m, hm'⟩).val -
            (starts ⟨0, Finset.card_pos.mpr hu⟩).val +
              cyclicGapLength u hu ⟨m, hm'⟩ = _
        rw [hgap]
        have h0m :
            (starts ⟨0, Finset.card_pos.mpr hu⟩).val ≤
              (starts ⟨m, hm'⟩).val := by
          exact (starts.monotone (Fin.le_def.mpr (Nat.zero_le m)))
        have hmnext :
            (starts ⟨m, hm'⟩).val <
              (starts ⟨m + 1, hm⟩).val := by
          exact starts.strictMono (Fin.lt_def.mpr (Nat.lt_succ_self m))
        omega
  exact hmain j.val j.isLt

/-- The consecutive cyclic gaps partition all `n` increments. -/
theorem blockStart_cyclicGapLength_card {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    AdditivePath.blockStart
      (cyclicGapLengthAt u hu)
      u.card = n := by
  have hcard : 0 < u.card := Finset.card_pos.mpr hu
  let last : Fin u.card :=
    ⟨u.card - 1, Nat.sub_lt hcard (Nat.succ_pos 0)⟩
  let first : Fin u.card := ⟨0, hcard⟩
  have hlast : last.val + 1 = u.card := by
    dsimp [last]
    omega
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  change AdditivePath.blockStart length u.card = n
  have hrewrite : AdditivePath.blockStart length u.card =
      AdditivePath.blockStart length (last.val + 1) :=
    congrArg (AdditivePath.blockStart length) hlast.symm
  rw [hrewrite, AdditivePath.blockStart_succ,
    blockStart_cyclicGapLength_eq u hu last]
  simp only [length]
  have hfinal : cyclicGapLength u hu last =
      n - (u.orderEmbOfFin rfl last).val +
        (u.orderEmbOfFin rfl first).val := by
    simp only [cyclicGapLength, cyclicGapLengthAt,
      dite_eq_left last.isLt,
      dite_eq_right (by omega : ¬ last.val + 1 < u.card)]
    rfl
  change (u.orderEmbOfFin rfl last).val -
      (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩).val +
        cyclicGapLength u hu last = n
  rw [hfinal]
  change (u.orderEmbOfFin rfl last).val -
      (u.orderEmbOfFin rfl first).val +
        (n - (u.orderEmbOfFin rfl last).val +
          (u.orderEmbOfFin rfl first).val) = n
  have hfirstLast :
      (u.orderEmbOfFin rfl first).val ≤
        (u.orderEmbOfFin rfl last).val := by
    exact (u.orderEmbOfFin rfl).monotone (Fin.le_def.mpr (by
      dsimp [first, last]
      omega))
  have hlastN := (u.orderEmbOfFin rfl last).isLt
  omega

/-- Every selected cyclic block lies inside the reindexed vector of
length `n`. -/
theorem blockStart_add_cyclicGapLength_le {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) (j : Fin u.card) :
    AdditivePath.blockStart
      (cyclicGapLengthAt u hu)
      j.val + cyclicGapLength u hu j ≤ n := by
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  have hmono := AdditivePath.blockStart_mono length
    (Nat.succ_le_of_lt j.isLt)
  rw [AdditivePath.blockStart_succ] at hmono
  have htotal := blockStart_cyclicGapLength_card u hu
  change AdditivePath.blockStart length u.card = n at htotal
  have hlen : length j.val = cyclicGapLength u hu j := by
    rfl
  rw [hlen, htotal] at hmono
  exact hmono

/-- Reindexing the whole vector from the first selected start agrees,
inside block `j`, with reindexing directly from that block's start. -/
theorem cyclicCoordinateReindex_block_eq {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : Fin u.card) (i : Fin (cyclicGapLength u hu j)) :
    Fin.cyclicCoordinateReindex hn
      (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
      ⟨AdditivePath.blockStart
        (cyclicGapLengthAt u hu)
        j.val + i.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          omega⟩ =
    Fin.cyclicCoordinateReindex hn (u.orderEmbOfFin rfl j)
      ⟨i.val, by
        have hbound := blockStart_add_cyclicGapLength_le u hu j
        omega⟩ := by
  let first := u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩
  let current := u.orderEmbOfFin rfl j
  have hfirstCurrent : first.val ≤ current.val := by
    exact (u.orderEmbOfFin rfl).monotone
      (Fin.le_def.mpr (Nat.zero_le _))
  have hstart := blockStart_cyclicGapLength_eq u hu j
  have hsum :
      first.val + AdditivePath.blockStart
        (cyclicGapLengthAt u hu)
        j.val = current.val := by
    dsimp [first, current]
    omega
  apply Fin.ext
  rw [Fin.cyclicCoordinateReindex_val,
    Fin.cyclicCoordinateReindex_val]
  dsimp [first, current] at hsum ⊢
  exact congrArg (fun m : ℕ => m % n) (by omega)

/-- The `j`-th block of the finite increment vector after rotating at
the first selected start. -/
noncomputable def cyclicGapCoordinates {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → ℝ) (j : Fin u.card) :
    Fin (cyclicGapLength u hu j) → ℝ :=
  fun i => x (Fin.cyclicCoordinateReindex hn
    (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
    ⟨AdditivePath.blockStart
      (cyclicGapLengthAt u hu)
      j.val + i.val, by
        have hbound := blockStart_add_cyclicGapLength_le u hu j
        omega⟩)

/-- The path within the `j`-th block is the cyclically restarted path
at that block's selected start. -/
theorem partialSum_cyclicGapCoordinates {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → ℝ) (j : Fin u.card)
    (t : Fin (cyclicGapLength u hu j + 1)) :
    Fin.partialSum (cyclicGapCoordinates hn u hu x j) t =
      Fin.cyclicPartialSum (Fin.partialSum x) (u.orderEmbOfFin rfl j)
        ⟨t.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          omega⟩ := by
  have hgap : cyclicGapLength u hu j ≤ n := by
    have hbound := blockStart_add_cyclicGapLength_le u hu j
    omega
  induction t using Fin.induction with
  | zero =>
      have hk : (u.orderEmbOfFin rfl j).val ≤ n :=
        Nat.le_of_lt (u.orderEmbOfFin rfl j).isLt
      have hidx :
          (⟨(u.orderEmbOfFin rfl j).val, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) =
            (u.orderEmbOfFin rfl j).castSucc := Fin.ext rfl
      simp [Fin.partialSum_zero, Fin.cyclicPartialSum, hk, hidx]
  | succ t ih =>
      rw [Fin.partialSum_succ, ih]
      have hstep := Fin.cyclicPartialSum_succ_eq_add_reindexedIncrement
        hn x (u.orderEmbOfFin rfl j)
        (⟨t.val, by omega⟩ : Fin n)
      have hleft :
          (⟨t.succ.val, by omega⟩ : Fin (n + 1)) =
            (⟨t.val, by omega⟩ : Fin n).succ := Fin.ext rfl
      have hright :
          (⟨t.castSucc.val, by omega⟩ : Fin (n + 1)) =
            (⟨t.val, by omega⟩ : Fin n).castSucc := Fin.ext rfl
      rw [hleft, hright, hstep]
      congr 1
      exact congrArg x (cyclicCoordinateReindex_block_eq hn u hu j t)

/-- Each block in the adjacent-block event is a surviving walk segment.
This is the forward direction in the probability factorization (A.6). -/
theorem cyclicBlockEvent_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → ℝ) (hx : x ∈ cyclicBlockEvent u hu)
    (j : Fin u.card) (t : Fin (cyclicGapLength u hu j + 1)) :
    0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t := by
  rw [partialSum_cyclicGapCoordinates hn u hu x j t]
  have hselected := forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent x u hu hx
    (u.orderEmbOfFin rfl j) (u.orderEmbOfFin_mem rfl j)
  exact hselected ⟨t.val, by
    have hbound := blockStart_add_cyclicGapLength_le u hu j
    omega⟩

/-- If every adjacent cyclic block survives, the original prefix path
satisfies the adjacent-block inequalities of (A.5). -/
theorem cyclicBlockEvent_of_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → ℝ)
    (hx : ∀ j : Fin u.card,
      ∀ t : Fin (cyclicGapLength u hu j + 1),
        0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t) :
    x ∈ cyclicBlockEvent u hu := by
  let starts := u.orderEmbOfFin rfl
  let first : Fin u.card := ⟨0, Finset.card_pos.mpr hu⟩
  let last : Fin u.card :=
    ⟨u.card - 1, Nat.sub_lt (Finset.card_pos.mpr hu) (Nat.succ_pos 0)⟩
  have hfirst : starts first = u.min' hu := by
    simpa [starts, first] using
      (Finset.orderEmbOfFin_zero (s := u) rfl (Finset.card_pos.mpr hu))
  have hlast : starts last = u.max' hu := by
    simpa [starts, last] using
      (Finset.orderEmbOfFin_last (s := u) rfl (Finset.card_pos.mpr hu))
  intro t
  by_cases hpred : (precedingStarts u t).Nonempty
  · let p := (precedingStarts u t).max' hpred
    have hpMem : p ∈ u :=
      (Finset.mem_filter.mp ((precedingStarts u t).max'_mem hpred)).1
    have hpt : p.val < t.val :=
      (Finset.mem_filter.mp ((precedingStarts u t).max'_mem hpred)).2
    let j : Fin u.card := (u.orderIsoOfFin rfl).symm ⟨p, hpMem⟩
    have hj : starts j = p := by
      dsimp [starts, j]
      exact congrArg Subtype.val
        ((u.orderIsoOfFin rfl).apply_symm_apply ⟨p, hpMem⟩)
    have hdistance : t.val - p.val ≤ cyclicGapLength u hu j := by
      by_cases hnext : j.val + 1 < u.card
      · let next : Fin u.card := ⟨j.val + 1, hnext⟩
        have hjnext : p < starts next := by
          rw [← hj]
          exact starts.strictMono (Fin.lt_def.mpr (Nat.lt_succ_self _))
        have htNext : t.val ≤ (starts next).val := by
          by_contra h
          have hnextMem : starts next ∈ precedingStarts u t :=
            Finset.mem_filter.mpr
              ⟨u.orderEmbOfFin_mem rfl next, by omega⟩
          have hpMax := (precedingStarts u t).le_max' _ hnextMem
          exact (not_lt_of_ge hpMax) hjnext
        have hgap : cyclicGapLength u hu j =
            (starts next).val - p.val := by
          rw [← hj]
          simp only [cyclicGapLength, cyclicGapLengthAt,
            dite_eq_left j.isLt, dite_eq_left hnext]
          rfl
        rw [hgap]
        omega
      · have hgap : cyclicGapLength u hu j =
            n - p.val + (starts first).val := by
          rw [← hj]
          simp only [cyclicGapLength, cyclicGapLengthAt,
            dite_eq_left j.isLt, dite_eq_right hnext]
          rfl
        rw [hgap]
        have hpN := p.isLt
        have htN := Nat.le_of_lt_succ t.isLt
        omega
    let d : Fin (cyclicGapLength u hu j + 1) :=
      ⟨t.val - p.val, Nat.lt_succ_of_le hdistance⟩
    have hlocal := hx j d
    rw [partialSum_cyclicGapCoordinates hn u hu x j d, hj] at hlocal
    have hsum : p.val + d.val ≤ n := by
      dsimp [d]
      have htN := Nat.le_of_lt_succ t.isLt
      omega
    have hindex :
        (⟨p.val + d.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) = t := by
      apply Fin.ext
      dsimp [d]
      omega
    have hineq : Fin.partialSum x p.castSucc ≤ Fin.partialSum x t := by
      simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex] at hlocal
      linarith
    simpa [cyclicBlockEvent, hpred, p] using hineq
  · have htFirst : t.val ≤ (starts first).val := by
      by_contra h
      have hmem : starts first ∈ precedingStarts u t :=
        Finset.mem_filter.mpr
          ⟨u.orderEmbOfFin_mem rfl first, by omega⟩
      exact hpred ⟨starts first, hmem⟩
    have hgap : cyclicGapLength u hu last =
        n - (starts last).val + (starts first).val := by
      simp only [cyclicGapLength, cyclicGapLengthAt,
        dite_eq_left last.isLt,
        dite_eq_right (by dsimp [last]; omega : ¬ last.val + 1 < u.card)]
      rfl
    have hd : n - (starts last).val + t.val ≤
        cyclicGapLength u hu last := by
      rw [hgap]
      omega
    let d : Fin (cyclicGapLength u hu last + 1) :=
      ⟨n - (starts last).val + t.val, Nat.lt_succ_of_le hd⟩
    have hlocal := hx last d
    rw [partialSum_cyclicGapCoordinates hn u hu x last d] at hlocal
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) (starts last)
      (⟨d.val, by
        have hbound := blockStart_add_cyclicGapLength_le u hu last
        omega⟩ : Fin (n + 1)) at hlocal
    have hlastN := (starts last).isLt
    have htarget : Fin.partialSum x (u.max' hu).castSucc ≤
        Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
      rw [← hlast]
      by_cases htZero : t.val = 0
      · have ht : t = 0 := Fin.ext htZero
        subst t
        have hsum : (starts last).val + d.val ≤ n := by
          dsimp [d]
          omega
        have hindex :
            (⟨(starts last).val + d.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) =
              Fin.last n := by
          apply Fin.ext
          dsimp [d]
          omega
        simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex,
          Fin.partialSum_zero, add_zero] at hlocal ⊢
        linarith
      · have hsum : ¬ (starts last).val + d.val ≤ n := by
          dsimp [d]
          omega
        have hindex :
            (⟨(starts last).val + d.val - n, by omega⟩ : Fin (n + 1)) =
              t := by
          apply Fin.ext
          dsimp [d]
          omega
        simp only [Fin.cyclicPartialSum, dite_eq_right hsum, hindex] at hlocal
        linarith
    simpa [cyclicBlockEvent, hpred, hlast] using htarget

/-- The event identity behind Bauer--Godrèche--Luck, Appendix A,
equation (A.6): the intersection of selected cyclic survival events is
the survival event of every disjoint consecutive block after one rotation. -/
theorem cyclicBlockEvent_eq_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    cyclicBlockEvent u hu =
      {x : Fin n → ℝ | ∀ j : Fin u.card,
        ∀ t : Fin (cyclicGapLength u hu j + 1),
          0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t} := by
  ext x
  constructor
  · intro hx j t
    exact cyclicBlockEvent_gapSurvival hn u hu x hx j t
  · intro hx
    exact cyclicBlockEvent_of_gapSurvival hn u hu x hx

private theorem measurableSet_nonnegativePartialSum (m : ℕ) :
    MeasurableSet {z : Fin m → ℝ |
      ∀ t : Fin (m + 1), 0 ≤ Fin.partialSum z t} := by
  have hpartial (t : Fin (m + 1)) :
      Measurable (fun z : Fin m → ℝ => Fin.partialSum z t) := by
    induction t using Fin.induction with
    | zero => simp
    | succ t ih =>
        have heq :
            (fun z : Fin m → ℝ => Fin.partialSum z t.succ) =
              fun z => Fin.partialSum z t.castSucc + z t := by
          funext z
          exact Fin.partialSum_succ z t
        rw [heq]
        exact ih.add (measurable_pi_apply t)
  have h : MeasurableSet (⋂ t : Fin (m + 1),
      {z : Fin m → ℝ | 0 ≤ Fin.partialSum z t}) :=
    MeasurableSet.iInter fun t =>
      measurableSet_Ici.preimage (hpartial t)
  simpa only [Set.iInter_ofPred] using h

/-- Bauer--Godrèche--Luck, Appendix A, equation (A.6): the selected cyclic
survival intersection factors into the survival probabilities of its
disjoint cyclic blocks under an IID finite product law. -/
theorem measure_pi_cyclicBlockEvent_eq_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    Measure.pi (fun _ : Fin n => ν) (cyclicBlockEvent u hu) =
      ∏ j : Fin u.card,
        Measure.pi (fun _ : Fin (cyclicGapLength u hu j) => ν)
          {z : Fin (cyclicGapLength u hu j) → ℝ |
            ∀ t : Fin (cyclicGapLength u hu j + 1),
              0 ≤ Fin.partialSum z t} := by
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  let event : ∀ j : Fin u.card, Set (Fin (length j.val) → ℝ) :=
    fun j => {z | ∀ t : Fin (length j.val + 1), 0 ≤ Fin.partialSum z t}
  have hmeas (j : Fin u.card) : MeasurableSet (event j) :=
    measurableSet_nonnegativePartialSum (length j.val)
  have htotal : AdditivePath.blockStart length u.card = n :=
    blockStart_cyclicGapLength_card u hu
  have hproduct := measure_pi_forall_variableConsecutiveBlockEvent_of_sum
    ν length u.card n htotal event hmeas
  let e := Fin.cyclicCoordinateReindex hn
    (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
  let T : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map T =
      Measure.pi (fun _ : Fin n => ν) := by
    simpa [T] using Measure.pi_map_piCongrLeft e.symm
      (fun _ : Fin n => ν)
  have hT (x : Fin n → ℝ) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ)
        e.symm x (e i))
  let blockEvent : Set (Fin n → ℝ) :=
    {y | ∀ j : Fin u.card,
      (fun i : Fin (length j.val) =>
        y ⟨AdditivePath.blockStart length j.val + i.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          have hi : i.val < cyclicGapLength u hu j := by
            exact i.isLt
          change AdditivePath.blockStart length j.val +
            cyclicGapLength u hu j ≤ n at hbound
          omega⟩) ∈ event j}
  have hevent : cyclicBlockEvent u hu = T ⁻¹' blockEvent := by
    rw [cyclicBlockEvent_eq_gapSurvival hn u hu]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, blockEvent]
    apply forall_congr'
    intro j
    have hvec :
        cyclicGapCoordinates hn u hu x j =
          (fun i : Fin (cyclicGapLength u hu j) =>
            T x ⟨AdditivePath.blockStart length j.val + i.val, by
              have hbound := blockStart_add_cyclicGapLength_le u hu j
              change AdditivePath.blockStart length j.val +
                cyclicGapLength u hu j ≤ n at hbound
              omega⟩) := by
      funext i
      exact (hT x _).symm
    rcases j with ⟨j, hj⟩
    simp only [event, length, hvec]
    rfl
  have hblockMeas : MeasurableSet blockEvent := by
    have heq : blockEvent = T.symm ⁻¹' cyclicBlockEvent u hu := by
      rw [hevent]
      ext y
      simp
    rw [heq]
    exact (measurableSet_cyclicBlockEvent u hu).preimage T.symm.measurable
  rw [hevent, ← Measure.map_apply T.measurable hblockMeas, hmap]
  change (Measure.pi (fun _ : Fin n => ν)) blockEvent = _
  calc
    (Measure.pi (fun _ : Fin n => ν)) blockEvent =
        ∏ j : Fin u.card,
          Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
      simpa only [blockEvent] using hproduct
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rfl

/-- Bauer--Godrèche--Luck, Appendix A, equation (A.6), with the finite
subset of selected starts used as the index of the alternating sum. -/
theorem measureReal_nonnegative_endpoint_eq_cyclicGap_sum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          (if hu : u.Nonempty then
            ∏ j : Fin u.card,
              (Measure.pi (fun _ : Fin (cyclicGapLength u hu j) => ν)).real
                {z : Fin (cyclicGapLength u hu j) → ℝ |
                  ∀ t : Fin (cyclicGapLength u hu j + 1),
                    0 ≤ Fin.partialSum z t}
          else 0) := by
  rw [measureReal_nonnegative_endpoint_eq_cyclicBlock_sum hn
    (Measure.pi (fun _ : Fin n => ν))]
  apply Finset.sum_congr rfl
  intro u hu
  have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
  simp only [dite_eq_left hnonempty]
  congr 1
  rw [MeasureTheory.measureReal_def,
    measure_pi_cyclicBlockEvent_eq_prod ν hn u hnonempty,
    ENNReal.toReal_prod]
  rfl

end ProbabilityTheory.RandomWalk

end
