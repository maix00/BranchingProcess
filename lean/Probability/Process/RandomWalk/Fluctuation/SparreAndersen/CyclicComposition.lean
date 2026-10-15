/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.BlockProbability
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Cyclic gap compositions

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicGapComposition`: the ordered positive
  cyclic gaps determined by a nonempty set of selected starts, as a
  composition of the path length.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition_length`: the number of
  parts is the number of selected starts.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition_blocksFun`: each part is
  the corresponding cyclic gap length.
- `ProbabilityTheory.RandomWalk.compositionSelectedStart`: the selected start
  at one composition boundary after a cyclic offset.
- `ProbabilityTheory.RandomWalk.compositionSelectedStart_strictMono`: the
  selected starts increase with their composition-boundary indices.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts`: a composition of
  $n$ and an offset smaller than its last part determine a set of starts in
  the cyclic interval of length $n$.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts_card`: the number of
  selected starts is the number of parts.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts_nonempty`: the
  selected-start set contains the first translated boundary.
- `ProbabilityTheory.RandomWalk.compositionSelectedStarts_orderEmbOfFin`:
  the increasing enumeration of the selected starts is the translated
  sequence of composition boundaries.
- `ProbabilityTheory.RandomWalk.cyclicGapLength_compositionSelectedStarts`:
  the cyclic gaps of these starts are the original composition parts.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition_compositionSelectedStarts`:
  reconstructing the cyclic-gap composition from its selected starts gives
  the original composition.
- `ProbabilityTheory.RandomWalk.cyclicFirstStart_lt_lastGap`: the least
  selected start lies within the last cyclic gap, so it is a valid offset.
- `ProbabilityTheory.RandomWalk.cyclicGapComposition_sizeUpTo`: the partial
  sums of the cyclic composition are the cyclic block starts.
- `ProbabilityTheory.RandomWalk.exists_compositionSelectedStarts_cyclicGapComposition`:
  every nonempty selected-start set is reconstructed from its cyclic-gap
  composition and the offset given by its least start.

This is the composition of $n$ used to regroup the products in Appendix A,
equations (A.6)--(A.7), of M. Bauer, C. Godrèche, and J.-M. Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?* (arXiv:cond-mat/9905252).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

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
last cyclic gap. This is the multiplicity of the last part in the
composition reindexing of Bauer--Godrèche--Luck, Appendix A, (A.7). -/
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
