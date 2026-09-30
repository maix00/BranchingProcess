module

public import Probability.Process.IndepIncrements.Disjoint
public import Mathlib.Data.Finset.Sort

/-!
# Independent increments on sorted finite time grids

An arbitrary finite set of observation times in a linear order has a canonical
increasing enumeration. Applying `HasIndepIncrements` to that enumeration
provides the elementary increments needed for finite-dimensional block-path
arguments, without choosing an enumeration in the theorem statement.
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

theorem finiteTimeGrid_monotone (s : Finset Time) (hs : s.Nonempty) :
    Monotone (finiteTimeGrid s hs) := by
  intro i j hij
  exact (s.orderEmbOfFin rfl).monotone
    ((Fin.castOrderIso (Nat.sub_add_cancel (Finset.card_pos.mpr hs))).monotone hij)

theorem finiteTimeGrid_strictMono (s : Finset Time) (hs : s.Nonempty) :
    StrictMono (finiteTimeGrid s hs) := by
  intro i j hij
  exact (s.orderEmbOfFin rfl).strictMono
    ((Fin.castOrderIso (Nat.sub_add_cancel (Finset.card_pos.mpr hs))).strictMono hij)

/-- Every observation time, including every chosen block endpoint, appears
on the canonical finite grid. -/
theorem finiteTimeGrid_range (s : Finset Time) (hs : s.Nonempty) :
    Set.range (finiteTimeGrid s hs) = s := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact s.orderEmbOfFin_mem rfl _
  · intro hx
    rw [← s.range_orderEmbOfFin rfl] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨Fin.cast (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm i, ?_⟩
    simp [finiteTimeGrid]

/-- Locate an observation time in the canonical finite grid. -/
noncomputable def finiteTimeGridIndex (s : Finset Time) (hs : s.Nonempty)
    (x : s) : Fin ((s.card - 1) + 1) :=
  Fin.cast (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm
    ((s.orderIsoOfFin rfl).symm x)

@[simp]
theorem finiteTimeGrid_index (s : Finset Time) (hs : s.Nonempty) (x : s) :
    finiteTimeGrid s hs (finiteTimeGridIndex s hs x) = x := by
  simp [finiteTimeGrid, finiteTimeGridIndex, Finset.orderEmbOfFin,
    Finset.orderIsoOfFin]

theorem finiteTimeGridIndex_strictMono (s : Finset Time) (hs : s.Nonempty) :
    StrictMono (finiteTimeGridIndex s hs) := by
  intro x y hxy
  exact (Fin.castOrderIso
    (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm).strictMono
      ((s.orderIsoOfFin rfl).symm.strictMono hxy)

/-- Consecutive values in the canonical sorted enumeration of any finite
observation set have mutually independent process increments. -/
theorem HasIndepIncrements.iIndepFun_finiteTimeGrid
    (hX : HasIndepIncrements X P) (s : Finset Time) (hs : s.Nonempty) :
    iIndepFun (fun (i : Fin (s.card - 1)) ω =>
      X (finiteTimeGrid s hs i.succ) ω -
        X (finiteTimeGrid s hs i.castSucc) ω) P :=
  hX (s.card - 1) (finiteTimeGrid s hs) (finiteTimeGrid_monotone s hs)

end ProbabilityTheory
