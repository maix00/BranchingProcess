/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Algebra.BigOperators.AdditivePath.Block
public import Algebra.BigOperators.PartialSum
public import Algebra.BigOperators.CyclicReindex
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Cyclic gap compositions

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicGapLengthAt` and
  `ProbabilityTheory.RandomWalk.cyclicGapLength`: the consecutive positive
  gaps between selected cyclic starts, with the final gap returning to the
  first start.
- `ProbabilityTheory.RandomWalk.cyclicGapLength_pos`: each gap contains at
  least one increment.
- `ProbabilityTheory.RandomWalk.blockStart_cyclicGapLength_eq`:
  the cumulative length before a selected start is its distance from the
  first selected start.
- `ProbabilityTheory.RandomWalk.blockStart_cyclicGapLength_card`:
  the cyclic gaps partition all $n$ increments.
- `ProbabilityTheory.RandomWalk.blockStart_add_cyclicGapLength_le`:
  each selected block stays inside the length-$n$ rotated path.
- `ProbabilityTheory.RandomWalk.cyclicCoordinateReindex_block_eq`:
  rotating at the first selected start and taking a block agrees with
  rotating directly at that block's start.
- `ProbabilityTheory.RandomWalk.cyclicGapCoordinates` and
  `ProbabilityTheory.RandomWalk.partialSum_cyclicGapCoordinates`:
  the block's coordinate vector and its partial sums as a restarted path.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition`:
  the ordered gaps form a positive composition of $n$.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition_length` and
  `ProbabilityTheory.RandomWalk.cyclicGapComposition_blocksFun`:
  the number of parts equals the number of starts, and each part is its gap
  length.
- `ProbabilityTheory.RandomWalk.compositionSelectedStart` and
  `ProbabilityTheory.RandomWalk.compositionSelectedStart_strictMono`:
  the selected starts at composition boundaries and their strict ordering.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts`:
  a composition and an offset into its last part determine a set of cyclic
  starts.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts_card`,
  `ProbabilityTheory.RandomWalk.compositionSelectedStarts_nonempty`,
  `ProbabilityTheory.RandomWalk.compositionSelectedStarts_orderEmbOfFin`,
  and `ProbabilityTheory.RandomWalk.compositionSelectedStarts_first_val`:
  its cardinality, nonemptiness, increasing enumeration, and first start.
- `ProbabilityTheory.RandomWalk.cyclicGapLength_compositionSelectedStarts`
  and `ProbabilityTheory.RandomWalk.cyclicGapComposition_compositionSelectedStarts`:
  the selected starts recover the original gap lengths and composition.
- `ProbabilityTheory.RandomWalk.cyclicFirstStart_lt_lastGap` and
  `ProbabilityTheory.RandomWalk.cyclicGapComposition_sizeUpTo`:
  the first start is an allowed offset, and partial sums recover the block
  starts.
- `ProbabilityTheory.RandomWalk.exists_compositionSelectedStarts_cyclicGapComposition`:
  every nonempty set of cyclic starts is represented by a composition and
  an offset into its last part.

These constructions formalize the cyclic-gap decomposition in
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events in
the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equations (A.5)--(A.6), *Journal of Statistical Physics* 96
(1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252.
-/

@[expose] public section

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



/-- The positive cyclic gap lengths, ordered from the least selected start,
form a composition of the length of the increment vector. -/
def cyclicGapComposition {n : ℕ} (u : Finset (Fin n))
    (hu : u.Nonempty) : Composition n where
  blocks := List.ofFn (cyclicGapLength u hu)
  blocks_pos := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin u.card, cyclicGapLength u hu j = i := by
      rwa [List.mem_ofFn', Set.mem_range] at hi
    exact cyclicGapLength_pos u hu j
  blocks_sum := by
    rw [List.sum_ofFn]
    calc
      ∑ j : Fin u.card, cyclicGapLength u hu j =
          AdditivePath.blockStart (cyclicGapLengthAt u hu) u.card := by
            rw [AdditivePath.blockStart, Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_range.mp hi, cyclicGapLength]
      _ = n := blockStart_cyclicGapLength_card u hu

/-- A selected start determines exactly one part of the cyclic composition. -/
@[simp] theorem cyclicGapComposition_length {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    (cyclicGapComposition u hu).length = u.card := by
  simp [cyclicGapComposition, Composition.length]

/-- The parts of the cyclic composition are the cyclic gap lengths. -/
theorem cyclicGapComposition_blocksFun {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) (j : Fin u.card) :
    (cyclicGapComposition u hu).blocksFun
      (j.cast (cyclicGapComposition_length u hu).symm) =
        cyclicGapLength u hu j := by
  simp [cyclicGapComposition, Composition.blocksFun, Fin.cast]

/-- The first start may occupy any position before the end of the last
cyclic gap. The remaining starts are successive composition boundaries. -/
def compositionSelectedStart {n : ℕ} (c : Composition n)
    (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩))
    (j : Fin c.length) : Fin n :=
    ⟨a.val + c.sizeUpTo j.val, by
      have hlength : 0 < c.length := c.length_pos_of_pos hn
      have hlast : c.length - 1 + 1 = c.length := by omega
      have hle : c.sizeUpTo j.val ≤ c.sizeUpTo (c.length - 1) :=
        c.monotone_sizeUpTo (by omega)
      have hsum := c.sizeUpTo_succ
        (show c.length - 1 < c.length by omega)
      rw [hlast, c.sizeUpTo_length] at hsum
      change n = c.sizeUpTo (c.length - 1) +
        c.blocksFun
          ⟨c.length - 1, Nat.sub_lt hlength (by omega)⟩ at hsum
      omega⟩

/-- The translated composition boundaries occur in increasing order. -/
theorem compositionSelectedStart_strictMono {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    StrictMono (compositionSelectedStart c hn a) := by
  intro i j hij
  have hboundary : c.sizeUpTo i.val < c.sizeUpTo j.val := by
    have h := c.boundary.strictMono
      (show (⟨i.val, by omega⟩ : Fin (c.length + 1)) <
        ⟨j.val, by omega⟩ from hij)
    exact h
  change a.val + c.sizeUpTo i.val < a.val + c.sizeUpTo j.val
  omega

/-- The selected starts obtained by translating the composition boundaries
through an offset in the last cyclic gap. -/
def compositionSelectedStarts {n : ℕ} (c : Composition n)
    (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    Finset (Fin n) :=
  Finset.univ.image (compositionSelectedStart c hn a)

/-- Every part of the composition contributes one distinct selected start. -/
@[simp] theorem compositionSelectedStarts_card {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    (compositionSelectedStarts c hn a).card = c.length := by
  unfold compositionSelectedStarts
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  exact (compositionSelectedStart_strictMono c hn a).injective

/-- A positive-length composition produces at least one selected start. -/
theorem compositionSelectedStarts_nonempty {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    (compositionSelectedStarts c hn a).Nonempty := by
  apply Finset.card_pos.mp
  rw [compositionSelectedStarts_card]
  exact c.length_pos_of_pos hn

/-- Sorting the selected starts recovers the original order of the
composition boundaries. -/
theorem compositionSelectedStarts_orderEmbOfFin {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩))
    (j : Fin c.length) :
    (compositionSelectedStarts c hn a).orderEmbOfFin
      (compositionSelectedStarts_card c hn a) j =
        compositionSelectedStart c hn a j := by
  have hmem : ∀ j : Fin c.length,
      compositionSelectedStart c hn a j ∈
        compositionSelectedStarts c hn a := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have h := Finset.orderEmbOfFin_unique
    (compositionSelectedStarts_card c hn a) hmem
      (compositionSelectedStart_strictMono c hn a)
  exact congrFun h.symm j

/-- The first selected start equals the offset within the terminal gap. -/
theorem compositionSelectedStarts_first_val {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    ((compositionSelectedStarts c hn a).orderEmbOfFin rfl
      ⟨0, Finset.card_pos.mpr
        (compositionSelectedStarts_nonempty c hn a)⟩).val = a.val := by
  have hcard : (compositionSelectedStarts c hn a).card = c.length :=
    compositionSelectedStarts_card c hn a
  have hzero :
      (⟨0, c.length_pos_of_pos hn⟩ : Fin c.length).cast hcard.symm =
        ⟨0, Finset.card_pos.mpr
          (compositionSelectedStarts_nonempty c hn a)⟩ := by
    apply Fin.ext
    rfl
  have horder := compositionSelectedStarts_orderEmbOfFin c hn a
    ⟨0, c.length_pos_of_pos hn⟩
  have hcompare :
      (compositionSelectedStarts c hn a).orderEmbOfFin rfl
        ((⟨0, c.length_pos_of_pos hn⟩ : Fin c.length).cast hcard.symm) =
      (compositionSelectedStarts c hn a).orderEmbOfFin hcard
        ⟨0, c.length_pos_of_pos hn⟩ := by
    rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]
    rfl
  rw [← hzero, hcompare, horder]
  simp [compositionSelectedStart, Composition.sizeUpTo_zero]

/-- Consecutive translated boundaries have precisely the corresponding
composition-block lengths, including the last gap that wraps around $n$. -/
theorem cyclicGapLength_compositionSelectedStarts {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩))
    (j : Fin c.length) :
    cyclicGapLength
      (compositionSelectedStarts c hn a)
      (compositionSelectedStarts_nonempty c hn a)
      (j.cast (compositionSelectedStarts_card c hn a).symm) =
        c.blocksFun j := by
  let u := compositionSelectedStarts c hn a
  let hu : u.Nonempty := compositionSelectedStarts_nonempty c hn a
  have hcard : u.card = c.length := compositionSelectedStarts_card c hn a
  have hstart (i : Fin c.length) :
      (u.orderEmbOfFin rfl (i.cast hcard.symm)).val =
        a.val + c.sizeUpTo i.val := by
    have horder := compositionSelectedStarts_orderEmbOfFin c hn a i
    have hcompare :
        u.orderEmbOfFin rfl (i.cast hcard.symm) =
          u.orderEmbOfFin hcard i := by
      rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]
      rfl
    rw [hcompare, horder]
    rfl
  have hfirst :
      (u.orderEmbOfFin rfl
        ⟨0, Finset.card_pos.mpr hu⟩).val = a.val := by
    have hcast :
        (⟨0, c.length_pos_of_pos hn⟩ : Fin c.length).cast hcard.symm =
          ⟨0, Finset.card_pos.mpr hu⟩ := by
      apply Fin.ext
      rfl
    rw [← hcast, hstart]
    simp
  have hstep := c.sizeUpTo_succ' j
  change cyclicGapLength u hu (j.cast hcard.symm) = c.blocksFun j
  have hjlt : j.val < u.card := by omega
  by_cases hnext : j.val + 1 < c.length
  · have hnext' : j.val + 1 < u.card := by omega
    have hnextcast :
        (⟨j.val + 1, hnext⟩ : Fin c.length).cast hcard.symm =
          ⟨j.val + 1, hnext'⟩ := by
      apply Fin.ext
      rfl
    have hgap : cyclicGapLength u hu (j.cast hcard.symm) =
        (u.orderEmbOfFin rfl ⟨j.val + 1, hnext'⟩).val -
          (u.orderEmbOfFin rfl (j.cast hcard.symm)).val := by
      simp [cyclicGapLength, cyclicGapLengthAt, hjlt, hnext']
      congr 1
    rw [hgap, ← hnextcast, hstart, hstart]
    change (a.val + c.sizeUpTo (j.val + 1)) -
      (a.val + c.sizeUpTo j.val) = c.blocksFun j
    rw [hstep]
    omega
  · have hlast : j.val + 1 = c.length := by omega
    have hnext0 : ¬ j.val + 1 < u.card := by omega
    have hgap : cyclicGapLength u hu (j.cast hcard.symm) =
        n - (u.orderEmbOfFin rfl (j.cast hcard.symm)).val +
          (u.orderEmbOfFin rfl
            ⟨0, Finset.card_pos.mpr hu⟩).val := by
      simp [cyclicGapLength, cyclicGapLengthAt, hjlt, hnext0]
      congr 1
    rw [hgap, hstart, hfirst]
    change n - (a.val + c.sizeUpTo j.val) + a.val = c.blocksFun j
    rw [hlast, c.sizeUpTo_length] at hstep
    have hjlast : j =
        ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ := by
      apply Fin.ext
      change j.val = c.length - 1
      omega
    have hale : a.val ≤ c.blocksFun j := by
      rw [hjlast]
      exact a.isLt.le
    omega

/-- The composition-to-starts construction is a right inverse of the
cyclic-gap construction. -/
theorem cyclicGapComposition_compositionSelectedStarts {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    cyclicGapComposition (compositionSelectedStarts c hn a)
      (compositionSelectedStarts_nonempty c hn a) = c := by
  let u := compositionSelectedStarts c hn a
  let hu := compositionSelectedStarts_nonempty c hn a
  have hcard : u.card = c.length := compositionSelectedStarts_card c hn a
  apply Composition.ext
  change List.ofFn (cyclicGapLength u hu) = c.blocks
  calc
    List.ofFn (cyclicGapLength u hu) =
        List.ofFn (fun j : Fin c.length =>
          cyclicGapLength u hu (j.cast hcard.symm)) := by
            exact List.ofFn_congr hcard (cyclicGapLength u hu)
    _ = List.ofFn c.blocksFun := by
      congr 1
      funext j
      exact cyclicGapLength_compositionSelectedStarts c hn a j
    _ = c.blocks := c.ofFn_blocksFun

/-- The minimum selected start is one of the possible offsets within the
last cyclic gap. This is the multiplicity of the last part in the cyclic-gap
reindexing of Bauer--Godrèche--Luck, Appendix A, equation (A.6), used in the
derivation of equation (A.7). -/
theorem cyclicFirstStart_lt_lastGap {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    (u.orderEmbOfFin rfl
      ⟨0, Finset.card_pos.mpr hu⟩).val <
      cyclicGapLength u hu
        ⟨u.card - 1,
          Nat.sub_lt (Finset.card_pos.mpr hu) (by omega)⟩ := by
  have hcard : 0 < u.card := Finset.card_pos.mpr hu
  have hlast : ¬ u.card - 1 + 1 < u.card := by omega
  have hmax :
      (u.orderEmbOfFin rfl
        ⟨u.card - 1, Nat.sub_lt hcard (by omega)⟩).val < n :=
    (u.orderEmbOfFin rfl _).isLt
  simp [cyclicGapLength, cyclicGapLengthAt, hlast]
  split_ifs; omega

/-- The composition boundary before block `j` is the sum of the first `j`
cyclic gap lengths. -/
theorem cyclicGapComposition_sizeUpTo {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : ℕ) (hj : j ≤ u.card) :
    (cyclicGapComposition u hu).sizeUpTo j =
      AdditivePath.blockStart (cyclicGapLengthAt u hu) j := by
  induction j with
  | zero => simp
  | succ i ih =>
      have hi : i < u.card := by omega
      have hstep := (cyclicGapComposition u hu).sizeUpTo_succ
        (by simpa [cyclicGapComposition_length] using hi)
      rw [hstep, AdditivePath.blockStart_succ, ih (by omega)]
      congr 1
      simpa [Composition.blocksFun, cyclicGapLength] using
        (cyclicGapComposition_blocksFun u hu ⟨i, hi⟩)

/-- The least selected start supplies the offset within the last cyclic
gap, and the cyclic-gap composition reconstructs the selected set. -/
theorem exists_compositionSelectedStarts_cyclicGapComposition {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    ∃ hn : 0 < n,
      ∃ a : Fin ((cyclicGapComposition u hu).blocksFun
        ⟨(cyclicGapComposition u hu).length - 1,
          Nat.sub_lt ((cyclicGapComposition u hu).length_pos_of_pos hn)
            (by omega)⟩),
        compositionSelectedStarts (cyclicGapComposition u hu) hn a = u := by
  let c := cyclicGapComposition u hu
  have hn : 0 < n := by
    have hfirst := (u.orderEmbOfFin rfl
      ⟨0, Finset.card_pos.mpr hu⟩).isLt
    omega
  refine ⟨hn, ?_⟩
  have hlen : c.length = u.card := cyclicGapComposition_length u hu
  have hlastGap : c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ =
      cyclicGapLength u hu
        ⟨u.card - 1,
          Nat.sub_lt (Finset.card_pos.mpr hu) (by omega)⟩ := by
    have hlast :
        (⟨c.length - 1,
          Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : Fin c.length) =
          (⟨u.card - 1,
            Nat.sub_lt (Finset.card_pos.mpr hu) (by omega)⟩ :
              Fin u.card).cast hlen.symm := by
      apply Fin.ext
      simp [hlen]
    rw [hlast]
    exact cyclicGapComposition_blocksFun u hu _
  let a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩) :=
    ⟨(u.orderEmbOfFin rfl
      ⟨0, Finset.card_pos.mpr hu⟩).val, by
        rw [hlastGap]
        exact cyclicFirstStart_lt_lastGap u hu⟩
  refine ⟨a, ?_⟩
  have hmap (j : Fin c.length) :
      compositionSelectedStart c hn a j =
        u.orderEmbOfFin rfl (j.cast hlen) := by
    apply Fin.ext
    have hj : j.val < u.card := by omega
    have hstart := blockStart_cyclicGapLength_eq u hu
      (j.cast hlen)
    have hstart' :
        AdditivePath.blockStart (cyclicGapLengthAt u hu) j.val =
          (u.orderEmbOfFin rfl (j.cast hlen)).val -
            (u.orderEmbOfFin rfl
              ⟨0, Finset.card_pos.mpr hu⟩).val := by
      simpa only [Fin.val_cast] using hstart
    have hsize := cyclicGapComposition_sizeUpTo u hu j.val (by omega)
    change a.val + c.sizeUpTo j.val =
      (u.orderEmbOfFin rfl (j.cast hlen)).val
    have hmin :
        (u.orderEmbOfFin rfl
          ⟨0, Finset.card_pos.mpr hu⟩).val ≤
          (u.orderEmbOfFin rfl (j.cast hlen)).val := by
      exact (u.orderEmbOfFin rfl).monotone
        (Fin.le_def.mpr (Nat.zero_le _))
    dsimp [a]
    rw [hsize, hstart']
    omega
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [hmap]
    exact Finset.orderEmbOfFin_mem u rfl _
  · rw [compositionSelectedStarts_card, hlen]


end ProbabilityTheory.RandomWalk

end
