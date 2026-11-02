/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Algebra.BigOperators.CyclicReindex
public import Combinatorics.Sequence.Block
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Cyclic gaps of finite sequences

## Public declarations

Fix a nonempty $u\in\mathrm{Finset}(\mathrm{Fin}(n))$ with witness $hu$; put
$m=|u|$ and let $(s_j)_{j\in\mathrm{Fin}(m)}$ be the increasing enumeration
of $u$. Set
$g(k)=\operatorname{cyclicGapLengthAt}(u,hu,k)$ for $k\in\mathbb N$,
$\ell_j=\operatorname{cyclicGapLength}(u,hu,j)=g(j.\mathrm{val})$, and
$b_j=\operatorname{blockStart}(g,j)$. Here $hu$ is the proof that $u$ is
nonempty; the last gap wraps from the largest selected position to the least,
and $g(k)=0$ for $k\ge m$.

- `Combinatorics.Sequence.cyclicGapLengthAt` defines $g$, and
  `Combinatorics.Sequence.cyclicGapLength` defines $\ell_j$.
  `Combinatorics.Sequence.cyclicGapLength_pos` states $0<\ell_j$.
- `Combinatorics.Sequence.blockStart_cyclicGapLength_eq` identifies the start
  of block $j$ relative to the least selected position:
  \[
    b_{j.\mathrm{val}}=s_j.\mathrm{val}-s_0.\mathrm{val}.
  \]
  `Combinatorics.Sequence.blockStart_cyclicGapLength_card` gives $b_m=n$,
  and `Combinatorics.Sequence.blockStart_add_cyclicGapLength_le` gives
  $b_{j.\mathrm{val}}+\ell_j\le n$.
- `Combinatorics.Sequence.finCycle_block_eq` identifies whole-vector and
  block-local cyclic reindexing. For $q<n$, let $[q]_n$ denote the element
  $\langle q,h_q\rangle\in\mathrm{Fin}(n)$ supplied by that bound. Then for
  $i\in\mathrm{Fin}(\ell_j)$,
  \[
    \operatorname{finCycle}(s_0,[b_{j.\mathrm{val}}+i.\mathrm{val}]_n)
      =\operatorname{finCycle}(s_j,[i.\mathrm{val}]_n).
  \]
- For an additive commutative group $G$ and $x:\mathrm{Fin}(n)\to G$,
  `Combinatorics.Sequence.cyclicGapCoordinates` extracts the rotated block
  from $x:\mathrm{Fin}(n)\to G$; its $i$-th coordinate is
  $x(\operatorname{finCycle}(s_0,[b_{j.\mathrm{val}}+i.\mathrm{val}]_n))$.
  `Combinatorics.Sequence.partialSum_cyclicGapCoordinates` states that its
  partial sum at $t\le\ell_j$ equals
  $\operatorname{cyclicPartialSum}(\operatorname{partialSum}(x),s_j,[t]_{n+1})$,
  where $[t]_{n+1}\in\mathrm{Fin}(n+1)$ is the knot index with value $t$.
- `Combinatorics.Sequence.cyclicGapComposition` packages the ordered positive
  gap lengths as a composition of $n$ whose blocks are
  $(\ell_j)_{j\in\mathrm{Fin}(m)}$.
  `Combinatorics.Sequence.cyclicGapComposition_length` states that its length
  is $m$, and `Combinatorics.Sequence.cyclicGapComposition_blocksFun` gives
  its $j$-th part as $\ell_j$.
- For a composition $c$ of $n>0$, an offset $a$ in its last part, and
  $j\in\mathrm{Fin}(c.\mathrm{length})$,
  `Combinatorics.Sequence.compositionSelectedStart` is the element
  $a.\mathrm{val}+c.\mathrm{sizeUpTo}(j.\mathrm{val})$ of $\mathrm{Fin}(n)$.
  `Combinatorics.Sequence.compositionSelectedStarts` is the finite set of
  these elements as $j$ varies,
  $\{a.\mathrm{val}+c.\mathrm{sizeUpTo}(j.\mathrm{val}):
    j\in\mathrm{Fin}(c.\mathrm{length})\}$, and
  `Combinatorics.Sequence.compositionSelectedStarts_nonempty` proves that
  this set is nonempty.

The finite composition API is Mathlib's
`Mathlib.Combinatorics.Enumerative.Composition`. These cyclic gap operations
extend that API to finite subsets of a cyclic index set. Their use in the
random-walk inclusion--exclusion expansion is recorded in Bauer, Godrèche,
and Luck, *Statistics of persistent events in the binomial random walk: Will
the drunken sailor hit the sober man?*, Appendix A, equations (A.5)--(A.6),
*Journal of Statistical Physics* 96 (1999), 963--1019,
DOI 10.1023/A:1004636216365, arXiv:cond-mat/9905252.
-/

@[expose] public section

namespace Combinatorics.Sequence


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
    Combinatorics.Sequence.blockStart
      (cyclicGapLengthAt u hu)
      j.val =
      (u.orderEmbOfFin rfl j).val -
        (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩).val := by
  let starts := u.orderEmbOfFin rfl
  have hmain (m : ℕ) (hm : m < u.card) :
      Combinatorics.Sequence.blockStart
        (cyclicGapLengthAt u hu)
        m =
        (starts ⟨m, hm⟩).val -
          (starts ⟨0, Finset.card_pos.mpr hu⟩).val := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hm' : m < u.card := by omega
        have hih := ih hm'
        rw [Combinatorics.Sequence.blockStart_succ, hih]
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
    Combinatorics.Sequence.blockStart
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
  change Combinatorics.Sequence.blockStart length u.card = n
  have hrewrite : Combinatorics.Sequence.blockStart length u.card =
      Combinatorics.Sequence.blockStart length (last.val + 1) :=
    congrArg (Combinatorics.Sequence.blockStart length) hlast.symm
  rw [hrewrite, Combinatorics.Sequence.blockStart_succ,
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
    Combinatorics.Sequence.blockStart
      (cyclicGapLengthAt u hu)
      j.val + cyclicGapLength u hu j ≤ n := by
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  have hmono := Combinatorics.Sequence.blockStart_mono length
    (Nat.succ_le_of_lt j.isLt)
  rw [Combinatorics.Sequence.blockStart_succ] at hmono
  have htotal := blockStart_cyclicGapLength_card u hu
  change Combinatorics.Sequence.blockStart length u.card = n at htotal
  have hlen : length j.val = cyclicGapLength u hu j := by
    rfl
  rw [hlen, htotal] at hmono
  exact hmono

/-- Reindexing the whole vector from the first selected start agrees,
inside block `j`, with reindexing directly from that block's start. -/
theorem finCycle_block_eq {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : Fin u.card) (i : Fin (cyclicGapLength u hu j)) :
    finCycle
      (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
      ⟨Combinatorics.Sequence.blockStart
        (cyclicGapLengthAt u hu)
        j.val + i.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          omega⟩ =
    finCycle (u.orderEmbOfFin rfl j)
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
      first.val + Combinatorics.Sequence.blockStart
        (cyclicGapLengthAt u hu)
        j.val = current.val := by
    dsimp [first, current]
    omega
  apply Fin.ext
  rw [Fin.finCycle_val,
    Fin.finCycle_val]
  dsimp [first, current] at hsum ⊢
  exact congrArg (fun m : ℕ => m % n) (by omega)

variable {G : Type*} [AddCommGroup G]

/-- The `j`-th block of a finite increment vector after rotating at
the first selected start. -/
noncomputable def cyclicGapCoordinates {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G) (j : Fin u.card) :
    Fin (cyclicGapLength u hu j) → G :=
  fun i => x (finCycle
    (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
    ⟨Combinatorics.Sequence.blockStart
      (cyclicGapLengthAt u hu)
      j.val + i.val, by
        have hbound := blockStart_add_cyclicGapLength_le u hu j
        omega⟩)

/-- The path within the `j`-th block is the cyclically restarted path
at that block's selected start. -/
theorem partialSum_cyclicGapCoordinates {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G) (j : Fin u.card)
    (t : Fin (cyclicGapLength u hu j + 1)) :
    Fin.partialSum (cyclicGapCoordinates u hu x j) t =
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
      have hstep := Fin.cyclicPartialSum_succ_eq_add_finCycleIncrement
        x (u.orderEmbOfFin rfl j)
        (⟨t.val, by omega⟩ : Fin n)
      have hleft :
          (⟨t.succ.val, by omega⟩ : Fin (n + 1)) =
            (⟨t.val, by omega⟩ : Fin n).succ := Fin.ext rfl
      have hright :
          (⟨t.castSucc.val, by omega⟩ : Fin (n + 1)) =
            (⟨t.val, by omega⟩ : Fin n).castSucc := Fin.ext rfl
      rw [hleft, hright, hstep]
      congr 1
      exact congrArg x (finCycle_block_eq u hu j t)



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
          Combinatorics.Sequence.blockStart (cyclicGapLengthAt u hu) u.card := by
            rw [Combinatorics.Sequence.blockStart, Finset.sum_fin_eq_sum_range]
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

/-- The `j`-th selected start determined by a composition and an offset into
its final part. -/
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

/-- The set of cyclic starts determined by a composition and an offset in
its final part. -/
def compositionSelectedStarts {n : ℕ} (c : Composition n)
    (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    Finset (Fin n) :=
  Finset.univ.image (compositionSelectedStart c hn a)

/-- A positive composition gives at least one cyclic start. -/
theorem compositionSelectedStarts_nonempty {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    (compositionSelectedStarts c hn a).Nonempty := by
  refine ⟨compositionSelectedStart c hn a ⟨0, c.length_pos_of_pos hn⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨0, c.length_pos_of_pos hn⟩,
    Finset.mem_univ _, rfl⟩


end Combinatorics.Sequence

end
