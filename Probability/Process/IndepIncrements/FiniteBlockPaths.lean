/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

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

/-- Reading selected coordinates of a real-valued vector, with `none`
representing the zero coordinate at a block's initial time, is measurable. -/
theorem measurable_optionalCoordinateProjection {I J : Type*}
    (query : J → Option I) :
    Measurable (fun v : I → ℝ => fun j => (query j).elim 0 v) := by
  rw [measurable_pi_iff]
  intro j
  cases hq : query j with
  | none => simp
  | some i => simpa [hq] using (measurable_pi_apply i :
      Measurable (fun v : I → ℝ => v i))

/-- A queried observation time in a block either is the initial time, or
corresponds to an elementary grid interval ending at that time. -/
noncomputable def finiteBlockQueryIndex (s : Finset Time) (hs : s.Nonempty)
    (a b x : s) (hax : a ≤ x) (hxb : x ≤ b) :
    Option (Finset.Ico (finiteTimeGridIndex s hs a).val
      (finiteTimeGridIndex s hs b).val) := by
  classical
  by_cases hxa : x = a
  · exact none
  · have haxlt : a < x := lt_of_le_of_ne hax (Ne.symm hxa)
    have hidxlt := finiteTimeGridIndex_strictMono s hs haxlt
    have hidxle := (finiteTimeGridIndex_strictMono s hs).monotone hxb
    exact some ⟨(finiteTimeGridIndex s hs x).val - 1,
      Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩

omit [MeasurableSpace Ω] in
/-- Reading the coordinate selected by `finiteBlockQueryIndex` gives exactly
the observed process displacement. -/
theorem finiteBlockQueryIndex_eval (s : Finset Time) (hs : s.Nonempty)
    (a b x : s) (hax : a ≤ x) (hxb : x ≤ b)
    (X : Time → Ω → ℝ) (ω : Ω) :
    (finiteBlockQueryIndex s hs a b x hax hxb).elim 0 (fun i =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω - X a ω) =
      X x ω - X a ω := by
  classical
  by_cases hxa : x = a
  · subst x
    simp [finiteBlockQueryIndex]
  · have haxlt : a < x := lt_of_le_of_ne hax (Ne.symm hxa)
    have hidxlt := finiteTimeGridIndex_strictMono s hs haxlt
    have hpos : 0 < (finiteTimeGridIndex s hs x).val := by omega
    have hnat : (finiteTimeGridIndex s hs x).val - 1 + 1 =
        (finiteTimeGridIndex s hs x).val := by omega
    simp only [finiteBlockQueryIndex, dite_eq_right hxa, Option.elim_some]
    rw [hnat, finiteTimeGridNat_eq s hs (finiteTimeGridIndex s hs x),
      finiteTimeGrid_index s hs x]

/-- For arbitrary observation times on a common finite grid, all sampled
positions in two consecutive blocks form independent vectors. The positions
are measured relative to the left endpoint of their own block. -/
theorem HasIndepIncrements.indepFun_finiteGridBlockPositions
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
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
  have hXt : ∀ i, AEMeasurable (X (t i)) P := fun i => hXmeas (t i)
  have h := hX.indepFun_adjacentBlockPositionVectors t ht hXt a.val b.val c.val
  simpa [t, finiteTimeGridNat_eq s hs a,
    finiteTimeGridNat_eq s hs b] using h

/-- The same finite-dimensional independence statement with block endpoints
specified as observation times rather than grid indices. -/
theorem HasIndepIncrements.indepFun_finiteObservationBlockPositions
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
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

/-- Arbitrary coordinate projections of two finite block position vectors
remain independent. This includes each block's zero-valued initial point. -/
theorem HasIndepIncrements.indepFun_projectedFiniteObservationBlocks
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (s : Finset Time) (hs : s.Nonempty) (a b c : s)
    {J K : Type*}
    (left : J → Option (Finset.Ico (finiteTimeGridIndex s hs a).val
      (finiteTimeGridIndex s hs b).val))
    (right : K → Option (Finset.Ico (finiteTimeGridIndex s hs b).val
      (finiteTimeGridIndex s hs c).val)) :
    (fun ω j => (left j).elim 0 (fun i =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω - X a ω)) ⟂ᵢ[P]
    (fun ω j => (right j).elim 0 (fun i =>
      X (finiteTimeGridNat s hs (i.val + 1)) ω - X b ω)) := by
  exact (hX.indepFun_finiteObservationBlockPositions hXmeas s hs a b c).comp
    (measurable_optionalCoordinateProjection left)
    (measurable_optionalCoordinateProjection right)

/-- Any two families of queried observation times in adjacent blocks have
independent displacement vectors. The query index types may be arbitrary;
finite-dimensional applications take them to be finite subsets of time. -/
theorem HasIndepIncrements.indepFun_finiteObservationQueries
    {X : Time → Ω → ℝ} {P : Measure Ω}
    (hX : HasIndepIncrements X P)
    (hXmeas : ∀ t, AEMeasurable (X t) P)
    (s : Finset Time) (hs : s.Nonempty) (a b c : s)
    {J K : Type*} (left : J → s) (right : K → s)
    (hleft : ∀ j, a ≤ left j ∧ left j ≤ b)
    (hright : ∀ k, b ≤ right k ∧ right k ≤ c) :
    (fun ω j => X (left j) ω - X a ω) ⟂ᵢ[P]
    (fun ω k => X (right k) ω - X b ω) := by
  let qleft j := finiteBlockQueryIndex s hs a b (left j)
    (hleft j).1 (hleft j).2
  let qright k := finiteBlockQueryIndex s hs b c (right k)
    (hright k).1 (hright k).2
  have h := hX.indepFun_projectedFiniteObservationBlocks hXmeas s hs
    a b c qleft qright
  convert h using 1
  · funext ω j
    exact (finiteBlockQueryIndex_eval s hs a b (left j)
      (hleft j).1 (hleft j).2 X ω).symm
  · funext ω k
    exact (finiteBlockQueryIndex_eval s hs b c (right k)
      (hright k).1 (hright k).2 X ω).symm

end ProbabilityTheory
