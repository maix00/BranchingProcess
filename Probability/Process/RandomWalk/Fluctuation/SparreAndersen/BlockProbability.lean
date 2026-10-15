/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.BlockDecomposition
public import Probability.Process.RandomWalk.Path.Block.Law.FiniteProduct

/-!
# Probabilities of cyclic survival blocks

The public definitions and theorems in this file are:

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

These are the block lengths in M. Bauer, C. Godrèche, and J.-M. Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A, equation (A.6)
(arXiv:cond-mat/9905252).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The cyclic lengths between consecutive selected starts, with the
last block wrapping from the largest selected start back to the smallest. -/
def cyclicGapLength {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty)
    (j : Fin u.card) : ℕ :=
  let starts := u.orderEmbOfFin rfl
  if h : j.val + 1 < u.card then
    (starts ⟨j.val + 1, h⟩).val - (starts j).val
  else
    n - (starts j).val + (starts ⟨0, Finset.card_pos.mpr hu⟩).val

/-- Every block in the cyclic partition contains at least one increment. -/
theorem cyclicGapLength_pos {n : ℕ} (u : Finset (Fin n))
    (hu : u.Nonempty) (j : Fin u.card) :
    0 < cyclicGapLength u hu j := by
  let starts := u.orderEmbOfFin rfl
  unfold cyclicGapLength
  dsimp only
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
      (fun i => if h : i < u.card then cyclicGapLength u hu ⟨i, h⟩ else 0)
      j.val =
      (u.orderEmbOfFin rfl j).val -
        (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩).val := by
  let starts := u.orderEmbOfFin rfl
  have hmain (m : ℕ) (hm : m < u.card) :
      AdditivePath.blockStart
        (fun i => if h : i < u.card then cyclicGapLength u hu ⟨i, h⟩ else 0)
        m =
        (starts ⟨m, hm⟩).val -
          (starts ⟨0, Finset.card_pos.mpr hu⟩).val := by
    induction m with
    | zero => simp [AdditivePath.blockStart_zero]
    | succ m ih =>
        have hm' : m < u.card := by omega
        have hih := ih hm'
        rw [AdditivePath.blockStart_succ, hih]
        simp only [dite_eq_left hm']
        have hgap : cyclicGapLength u hu ⟨m, hm'⟩ =
            (starts ⟨m + 1, hm⟩).val - (starts ⟨m, hm'⟩).val := by
          simp only [cyclicGapLength, dite_eq_left hm]
          rfl
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
      (fun i => if h : i < u.card then cyclicGapLength u hu ⟨i, h⟩ else 0)
      u.card = n := by
  have hcard : 0 < u.card := Finset.card_pos.mpr hu
  let last : Fin u.card :=
    ⟨u.card - 1, Nat.sub_lt hcard (Nat.succ_pos 0)⟩
  let first : Fin u.card := ⟨0, hcard⟩
  have hlast : last.val + 1 = u.card := by
    dsimp [last]
    omega
  let length : ℕ → ℕ :=
    fun i => if h : i < u.card then cyclicGapLength u hu ⟨i, h⟩ else 0
  change AdditivePath.blockStart length u.card = n
  have hrewrite : AdditivePath.blockStart length u.card =
      AdditivePath.blockStart length (last.val + 1) :=
    congrArg (AdditivePath.blockStart length) hlast.symm
  rw [hrewrite, AdditivePath.blockStart_succ,
    blockStart_cyclicGapLength_eq u hu last]
  simp only [length, dite_eq_left last.isLt]
  have hfinal : cyclicGapLength u hu last =
      n - (u.orderEmbOfFin rfl last).val +
        (u.orderEmbOfFin rfl first).val := by
    simp only [cyclicGapLength, dite_eq_right (by omega : ¬ last.val + 1 < u.card)]
    rfl
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

end ProbabilityTheory.RandomWalk

end
