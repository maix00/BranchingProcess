module

public import Probability.Process.IndepIncrements.FiniteGrid
public import Probability.Process.IndepIncrements.BlockVectors

/-!
# Block positions on a common finite observation grid

A finite set of observation times can be sorted and extended constantly after
its final point. This connects the canonical finite grid to the general
adjacent-block position-vector independence theorem.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Time Ω : Type*} [LinearOrder Time] [MeasurableSpace Ω]

/-- Extend a finite sorted time grid constantly beyond its final point. -/
noncomputable def finiteTimeGridNat (s : Finset Time) (hs : s.Nonempty) : ℕ → Time :=
  fun k => finiteTimeGrid s hs
    ⟨min k (s.card - 1), by
      have hcard := Nat.sub_add_cancel (Finset.card_pos.mpr hs)
      omega⟩

theorem finiteTimeGridNat_monotone (s : Finset Time) (hs : s.Nonempty) :
    Monotone (finiteTimeGridNat s hs) := by
  intro i j hij
  apply finiteTimeGrid_monotone s hs
  exact Fin.mk_le_mk.mpr (by omega)

theorem finiteTimeGridNat_eq (s : Finset Time) (hs : s.Nonempty)
    (i : Fin ((s.card - 1) + 1)) :
    finiteTimeGridNat s hs i.val = finiteTimeGrid s hs i := by
  simp only [finiteTimeGridNat]
  have hi : i.val ≤ s.card - 1 := Nat.le_of_lt_succ i.isLt
  simp [Nat.min_eq_left hi]

/-- For arbitrary observation times on a common finite grid, all sampled
positions in two consecutive blocks form independent vectors. The positions
are measured relative to the left endpoint of their own block. -/
theorem HasIndepIncrements.indepFun_finiteGridBlockPositions
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, Measurable (X t))
    (s : Finset Time) (hs : s.Nonempty)
    (a b c : Fin ((s.card - 1) + 1)) :
    (fun ω (i : Finset.Ico a.val b.val) =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω -
        X (finiteTimeGrid s hs a) ω) ⟂ᵢ[P]
    (fun ω (i : Finset.Ico b.val c.val) =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω -
        X (finiteTimeGrid s hs b) ω) := by
  let t := finiteTimeGridNat s hs
  have ht : Monotone t := finiteTimeGridNat_monotone s hs
  have hXt : ∀ i, Measurable (X (t i)) := fun i => hXmeas (t i)
  have h := hX.indepFun_adjacentBlockPositionVectors t ht hXt a.val b.val c.val
  simpa [t, finiteTimeGridNat_eq s hs a,
    finiteTimeGridNat_eq s hs b] using h

/-- The same finite-dimensional independence statement with block endpoints
specified as observation times rather than grid indices. -/
theorem HasIndepIncrements.indepFun_finiteObservationBlockPositions
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, Measurable (X t))
    (s : Finset Time) (hs : s.Nonempty) (a b c : s) :
    (fun ω (i : Finset.Ico (finiteTimeGridIndex s hs a).val
        (finiteTimeGridIndex s hs b).val) =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω - X a ω) ⟂ᵢ[P]
    (fun ω (i : Finset.Ico (finiteTimeGridIndex s hs b).val
        (finiteTimeGridIndex s hs c).val) =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω - X b ω) := by
  have h := hX.indepFun_finiteGridBlockPositions hXmeas s hs
    (finiteTimeGridIndex s hs a) (finiteTimeGridIndex s hs b)
    (finiteTimeGridIndex s hs c)
  simpa [finiteTimeGrid_index] using h

end ProbabilityTheory
