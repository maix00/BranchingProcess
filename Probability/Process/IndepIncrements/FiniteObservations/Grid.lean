/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Independent increments on finite observation grids

## Public declarations

* `finiteTimeGrid`: the canonical increasing enumeration
  `Fin ((s.card - 1) + 1) → Time` of a nonempty finite set `s` in a linear
  order.
* `finiteTimeGrid_monotone`: the canonical enumeration is monotone.
* `HasIndepIncrements.iIndepFun_finiteTimeGrid`: for every process `X` with
  independent increments,
  `iIndepFun (i ↦ (ω ↦ X (finiteTimeGrid s hs i.succ) ω -
  X (finiteTimeGrid s hs i.castSucc) ω)) P`.

If `s` is a nonempty finite set of ordered observation times, its canonical
enumeration `t_i` is monotone, and the successive increments are mutually
independent:

\[
\operatorname{iIndep}_P
  \left(\bigl(X_{t_{i+1}}-X_{t_i}\bigr)_{0\le i<|s|-1}\right).
\]
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Time Ω E : Type*} [LinearOrder Time] [MeasurableSpace Ω]
  [MeasurableSpace E] [Sub E] {P : Measure Ω} {X : Time → Ω → E}

/-- The increasing enumeration of a nonempty finite set of observation times,
presented with the `Fin (n + 1)` index expected by `HasIndepIncrements`. -/
noncomputable def finiteTimeGrid (s : Finset Time) (hs : s.Nonempty) :
    Fin ((s.card - 1) + 1) → Time :=
  fun i => s.orderEmbOfFin rfl (Fin.cast (Nat.sub_add_cancel (Finset.card_pos.mpr hs)) i)

/-- The canonical enumeration of a finite set is monotone. -/
lemma finiteTimeGrid_monotone (s : Finset Time) (hs : s.Nonempty) :
    Monotone (finiteTimeGrid s hs) := by
  intro i j hij
  exact (s.orderEmbOfFin rfl).monotone
    ((Fin.castOrderIso (Nat.sub_add_cancel (Finset.card_pos.mpr hs))).monotone hij)

/-- Consecutive values in the canonical sorted enumeration of any finite
observation set have mutually independent process increments. -/
theorem HasIndepIncrements.iIndepFun_finiteTimeGrid
    (hX : HasIndepIncrements X P) (s : Finset Time) (hs : s.Nonempty) :
    iIndepFun (fun (i : Fin (s.card - 1)) ω =>
      X (finiteTimeGrid s hs i.succ) ω -
        X (finiteTimeGrid s hs i.castSucc) ω) P :=
  hX (s.card - 1) (finiteTimeGrid s hs) (by
    intro i j hij
    exact (s.orderEmbOfFin rfl).monotone
      ((Fin.castOrderIso
        (Nat.sub_add_cancel (Finset.card_pos.mpr hs))).monotone hij))

end ProbabilityTheory
