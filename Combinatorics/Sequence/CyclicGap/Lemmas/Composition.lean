/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Combinatorics.Sequence.CyclicGap.Basic
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Internal inverse construction for cyclic gap compositions

## Internal proof declarations

- `compositionSelectedStart_strictMono` and
  `compositionSelectedStarts_card` show that composition boundaries translated
  by a terminal-gap offset form an ordered set of the expected cardinality.
- `compositionSelectedStarts_orderEmbOfFin` and
  `compositionSelectedStarts_first_val` identify its ordered enumeration and
  initial offset.
- `cyclicGapLength_compositionSelectedStarts`,
  `cyclicGapComposition_compositionSelectedStarts`,
  `cyclicFirstStart_lt_lastGap`, and `cyclicGapComposition_sizeUpTo` recover
  the composition gaps from those starts.
- `exists_compositionSelectedStarts_cyclicGapComposition` proves the inverse
  construction needed for the cyclic-gap/composition equivalence.

The helper definitions and inverse identities in this file prove the
composition-and-offset equivalence in `Combinatorics.Sequence.CyclicGap.Reindex`.
They are specific to that construction and are kept internal to the proof
module.
-/

section

namespace Combinatorics.Sequence

/-- The translated composition boundaries occur in increasing order. -/
lemma compositionSelectedStart_strictMono {n : ℕ}
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

/-- Every part of the composition contributes one distinct selected start. -/
@[simp] lemma compositionSelectedStarts_card {n : ℕ}
    (c : Composition n) (hn : 0 < n)
    (a : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) :
    (compositionSelectedStarts c hn a).card = c.length := by
  unfold compositionSelectedStarts
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  exact (compositionSelectedStart_strictMono c hn a).injective

/-- Sorting the selected starts recovers the original order of the
composition boundaries. -/
lemma compositionSelectedStarts_orderEmbOfFin {n : ℕ}
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
lemma compositionSelectedStarts_first_val {n : ℕ}
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
lemma cyclicGapLength_compositionSelectedStarts {n : ℕ}
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
lemma cyclicGapComposition_compositionSelectedStarts {n : ℕ}
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
lemma cyclicFirstStart_lt_lastGap {n : ℕ}
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
lemma cyclicGapComposition_sizeUpTo {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : ℕ) (hj : j ≤ u.card) :
    (cyclicGapComposition u hu).sizeUpTo j =
      Combinatorics.Sequence.blockStart (cyclicGapLengthAt u hu) j := by
  induction j with
  | zero => simp
  | succ i ih =>
      have hi : i < u.card := by omega
      have hstep := (cyclicGapComposition u hu).sizeUpTo_succ
        (by simpa [cyclicGapComposition_length] using hi)
      rw [hstep, Combinatorics.Sequence.blockStart_succ, ih (by omega)]
      congr 1
      simpa [Composition.blocksFun, cyclicGapLength] using
        (cyclicGapComposition_blocksFun u hu ⟨i, hi⟩)

/-- The least selected start supplies the offset within the last cyclic
gap, and the cyclic-gap composition reconstructs the selected set. -/
lemma exists_compositionSelectedStarts_cyclicGapComposition {n : ℕ}
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
        Combinatorics.Sequence.blockStart (cyclicGapLengthAt u hu) j.val =
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


end Combinatorics.Sequence

end
