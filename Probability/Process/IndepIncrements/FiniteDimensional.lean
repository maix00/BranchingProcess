/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Data.Finset.Sort
public import Probability.Process.StationaryIncrements.Basic

/-!
# Finite-dimensional laws from independent increments

The public declarations in this file concern processes valued in a measurable
additive commutative group `E` with measurable addition:

* `HasIndepIncrements.finiteDimensional_identDistrib`: matching increment
  laws and common zero values at an arbitrary anchor `t₀` imply
  $(X_{t_i})_i \stackrel{d}{=} (Y_{t_i})_i$ on a finite monotone grid starting
  at `t₀`.
* `HasIndepIncrements.translatedProcess_finiteDimensional_identDistrib`:
  stationary independent increments on an ordered additive time monoid imply
  $(X_{s+t_i}-X_s)_i \stackrel{d}{=} (X_{s'+t_i}-X_{s'})_i`.
* `HasIndepIncrements.finiteRestriction_identDistrib`: matching increment
  laws and zero starts imply equal laws of finite time restrictions.
* `HasIndepIncrements.aemeasurable_eval`: a zero start and measurable
  increments imply almost-everywhere measurability of each coordinate.
* `HasIndepIncrements.process_identDistrib_of_aemeasurable`: matching
  increment laws and measurable process maps imply equal process laws.
* `HasIndepIncrements.process_identDistrib`: on a countable time type,
  coordinate-measurable increments imply equal process laws.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Independent-increment processes with matching increment distributions and
common zero values at a chosen anchor have the same position-vector law on
every finite monotone grid starting at that anchor. The two processes may
live on different probability spaces. -/
theorem HasIndepIncrements.finiteDimensional_identDistrib
    {Time : Type*} [Preorder Time]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {X : Time → Ω → E} {Y : Time → Ω' → E}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    {start : Time}
    (hX : HasIndepIncrements X P) (hY : HasIndepIncrements Y Q)
    (hXstart : ∀ᵐ ω ∂P, X start ω = 0)
    (hYstart : ∀ᵐ ω ∂Q, Y start ω = 0)
    (hinc : ∀ s t : Time, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q)
    (n : ℕ) (grid : Fin (n + 1) → Time) (hgrid : Monotone grid)
    (hgridStart : grid 0 = start) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) => Y (grid i.succ) ω) P Q := by
  let dX : Fin n → Ω → E := fun i ω =>
    X (grid i.succ) ω - X (grid i.castSucc) ω
  let dY : Fin n → Ω' → E := fun i ω =>
    Y (grid i.succ) ω - Y (grid i.castSucc) ω
  have hXinc : iIndepFun dX P := by
    simpa [dX] using hX n grid hgrid
  have hYinc : iIndepFun dY Q := by
    simpa [dY] using hY n grid hgrid
  have hincLaw (i : Fin n) : IdentDistrib (dX i) (dY i) P Q := by
    exact hinc (grid i.castSucc) (grid i.succ)
      (hgrid (Fin.castSucc_le_succ i))
  have hvector : IdentDistrib (fun ω i => dX i ω) (fun ω i => dY i ω) P Q :=
    IdentDistrib.pi hincLaw hXinc hYinc
  let partialSums : (Fin n → E) → (Fin n → E) :=
    fun x i => Fin.partialSum x i.succ
  have hpartialSums : Measurable partialSums := by
    rw [measurable_pi_iff]
    intro i
    have hEval (j : Fin (n + 1)) :
        Measurable (fun x : Fin n → E => Fin.partialSum x j) := by
      induction j using Fin.induction with
      | zero => exact measurable_const
      | succ j ih =>
        have hm := ih.add (measurable_pi_apply j)
        have heq : (fun x : Fin n → E => Fin.partialSum x j.succ) =
            (fun x : Fin n → E => Fin.partialSum x j.castSucc) +
              (fun x : Fin n → E => x j) := by
          funext x
          simp only [Fin.partialSum_succ, Pi.add_apply]
        exact heq ▸ hm
    exact hEval i.succ
  have hpositions := hvector.comp hpartialSums
  have hXeq : (fun ω (i : Fin n) => X (grid i.succ) ω) =ᵐ[P]
      fun ω => partialSums (fun j => dX j ω) := by
    filter_upwards [hXstart] with ω hω
    funext i
    have htel := Fin.partialSum_differences
      (fun j : Fin (n + 1) => X (grid j) ω) i.succ
    have hbase : X (grid 0) ω = 0 := by simpa [hgridStart] using hω
    simpa [partialSums, dX, hbase] using htel.symm
  have hYeq : (fun ω (i : Fin n) => Y (grid i.succ) ω) =ᵐ[Q]
      fun ω => partialSums (fun j => dY j ω) := by
    filter_upwards [hYstart] with ω hω
    funext i
    have htel := Fin.partialSum_differences
      (fun j : Fin (n + 1) => Y (grid j) ω) i.succ
    have hbase : Y (grid 0) ω = 0 := by simpa [hgridStart] using hω
    simpa [partialSums, dY, hbase] using htel.symm
  have hXeq' : (partialSums ∘ (fun ω i => dX i ω)) =ᵐ[P]
      (fun ω (i : Fin n) => X (grid i.succ) ω) := by
    simpa [Function.comp_def] using hXeq.symm
  have hYeq' : (partialSums ∘ (fun ω i => dY i ω)) =ᵐ[Q]
      (fun ω (i : Fin n) => Y (grid i.succ) ω) := by
    simpa [Function.comp_def] using hYeq.symm
  have hXposMeas : AEMeasurable (fun ω (i : Fin n) => X (grid i.succ) ω) P :=
    hpositions.aemeasurable_fst.congr hXeq'
  have hYposMeas : AEMeasurable (fun ω (i : Fin n) => Y (grid i.succ) ω) Q :=
    hpositions.aemeasurable_snd.congr hYeq'
  exact (IdentDistrib.of_ae_eq hXposMeas hXeq).trans
    (hpositions.trans (IdentDistrib.of_ae_eq hYposMeas hYeq).symm)

/-- For a process over an ordered additive time space with stationary
independent increments, the finite-dimensional laws of increments after any
deterministic time agree. The time order is preserved by addition, and every
ordered pair has a duration represented by subtraction. No path regularity
assumption is required. -/
theorem HasIndepIncrements.translatedProcess_finiteDimensional_identDistrib
    {Time : Type*} [AddCommMonoid Time] [PartialOrder Time]
    [AddLeftMono Time] [ExistsAddOfLE Time] [Sub Time] [OrderedSub Time]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {process : Time → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements process P)
    (hstationary : HasStationaryIncrements process P) (s t : Time)
    (n : ℕ) (grid : Fin (n + 1) → Time) (hgrid : Monotone grid)
    (hgridStart : grid 0 = 0) :
    IdentDistrib
      (fun ω (i : Fin n) => process (s + grid i.succ) ω - process s ω)
      (fun ω (i : Fin n) => process (t + grid i.succ) ω - process t ω) P P := by
  let Xs : Time → Ω → E := fun u ω => process (s + u) ω - process s ω
  let Xt : Time → Ω → E := fun u ω => process (t + u) ω - process t ω
  have hXs : HasIndepIncrements Xs P := by
    intro m u hu
    have hu' : Monotone (fun i : Fin (m + 1) => s + u i) := by
      intro i j hij
      simpa [add_comm] using add_le_add_left (hu hij) s
    simpa [Xs, sub_sub_sub_cancel_right] using h m (fun i => s + u i) hu'
  have hXt : HasIndepIncrements Xt P := by
    intro m u hu
    have hu' : Monotone (fun i : Fin (m + 1) => t + u i) := by
      intro i j hij
      simpa [add_comm] using add_le_add_left (hu hij) t
    simpa [Xt, sub_sub_sub_cancel_right] using h m (fun i => t + u i) hu'
  have hXsStart : ∀ᵐ ω ∂P, Xs 0 ω = 0 := by
    filter_upwards [] with ω
    simp [Xs]
  have hXtStart : ∀ᵐ ω ∂P, Xt 0 ω = 0 := by
    filter_upwards [] with ω
    simp [Xt]
  have hinc : ∀ q r : Time, q ≤ r →
      IdentDistrib (fun ω => Xs r ω - Xs q ω)
        (fun ω => Xt r ω - Xt q ω) P P := by
    intro q r hqr
    let d : Time := r - q
    have hsum : q + d = r := add_tsub_cancel_of_le hqr
    have hs := hstationary (s + q) d
    have ht := hstationary (t + q) d
    simpa [Xs, Xt, d, add_assoc, hsum] using hs.trans ht.symm
  exact HasIndepIncrements.finiteDimensional_identDistrib
    (X := Xs) (Y := Xt) (P := P) (Q := P)
    hXs hXt hXsStart hXtStart hinc n grid hgrid hgridStart

/-- Matching increment laws imply matching restrictions of the position
processes to any finite set of times in a linear order with a least element.
The least element is prepended to the ordered finite set to anchor the
partial-sum reconstruction at the common zero start.
-/
theorem HasIndepIncrements.finiteRestriction_identDistrib
    {Time : Type*} [LinearOrder Time] [OrderBot Time]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {X : Time → Ω → E} {Y : Time → Ω' → E}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hX : HasIndepIncrements X P) (hY : HasIndepIncrements Y Q)
    (hXstart : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (hYstart : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hinc : ∀ s t : Time, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q)
    (I : Finset Time) :
    IdentDistrib (fun ω => I.restrict (X · ω))
      (fun ω => I.restrict (Y · ω)) P Q := by
  let grid : Fin (I.card + 1) → Time := fun i =>
    if hi : i = 0 then ⊥ else I.orderEmbOfFin rfl (i.pred hi)
  have hgrid : Monotone grid := by
    intro i j hij
    by_cases hi : i = 0
    · simp [grid, hi]
    · by_cases hj : j = 0
      · have hjval : j.val = 0 := by simp [hj]
        have hival : i.val = 0 := by
          have hij' := Fin.le_iff_val_le_val.mp hij
          omega
        exact False.elim (hi (Fin.ext hival))
      · have hpred : i.pred hi ≤ j.pred hj := by
          apply Fin.le_iff_val_le_val.mpr
          rw [Fin.val_pred, Fin.val_pred]
          exact Nat.sub_le_sub_right (Fin.le_iff_val_le_val.mp hij) 1
        simpa [grid, hi, hj] using (I.orderEmbOfFin rfl).monotone hpred
  have hstart : grid 0 = ⊥ := by simp [grid]
  have grid_succ (j : Fin I.card) : grid j.succ = I.orderEmbOfFin rfl j := by
    simp [grid]
  have hvec := hX.finiteDimensional_identDistrib hY hXstart hYstart hinc
    I.card grid hgrid hstart
  let e : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let reindex : (Fin I.card → E) → (i : I) → E := fun v i => v (e.symm i)
  have hreindex : Measurable reindex := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (e.symm i)
  have hvec' := hvec.comp hreindex
  have hXeq : (fun ω => reindex (fun j => X (grid j.succ) ω)) =ᵐ[P]
      fun ω => I.restrict (X · ω) := by
    filter_upwards [] with ω
    funext i
    change X (grid (e.symm i).succ) ω = X i.1 ω
    rw [grid_succ]
    have htime : I.orderEmbOfFin rfl (e.symm i) = i.1 := by
      rw [← Finset.coe_orderIsoOfFin_apply I rfl (e.symm i)]
      simp [e]
    rw [htime]
  have hYeq : (fun ω => reindex (fun j => Y (grid j.succ) ω)) =ᵐ[Q]
      fun ω => I.restrict (Y · ω) := by
    filter_upwards [] with ω
    funext i
    change Y (grid (e.symm i).succ) ω = Y i.1 ω
    rw [grid_succ]
    have htime : I.orderEmbOfFin rfl (e.symm i) = i.1 := by
      rw [← Finset.coe_orderIsoOfFin_apply I rfl (e.symm i)]
      simp [e]
    rw [htime]
  exact (IdentDistrib.of_ae_eq hvec'.aemeasurable_fst hXeq).symm.trans
    (hvec'.trans (IdentDistrib.of_ae_eq hvec'.aemeasurable_snd hYeq))

/-- Every coordinate of a zero-start independent-increment process is
almost-everywhere measurable when each increment is almost-everywhere
measurable.
-/
theorem HasIndepIncrements.aemeasurable_eval
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {E : Type*} [MeasurableSpace E] [SubNegZeroMonoid E]
    {X : Time → Ω → E} {P : Measure Ω}
    (hstart : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (hincrement : ∀ s t : Time, s ≤ t → AEMeasurable
      (fun ω => X t ω - X s ω) P) (t : Time) :
    AEMeasurable (fun ω => X t ω) P := by
  have heq : (fun ω => X t ω) =ᵐ[P] fun ω => X t ω - X ⊥ ω := by
    filter_upwards [hstart] with ω hω
    simp [hω]
  exact (hincrement ⊥ t bot_le).congr heq.symm

/-- On a linearly ordered time type with a least element, independent
increment processes with matching increment distributions and zero starts
have the same function-valued process law. This is Mathlib's
finite-dimensional-law uniqueness theorem applied to the generic increment
result above.
-/
theorem HasIndepIncrements.process_identDistrib_of_aemeasurable
    {Time : Type*} [LinearOrder Time] [OrderBot Time]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {X : Time → Ω → E} {Y : Time → Ω' → E}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hX : HasIndepIncrements X P) (hY : HasIndepIncrements Y Q)
    (hXstart : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (hYstart : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hinc : ∀ s t : Time, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q)
    (hXmeas : AEMeasurable (fun ω (t : Time) => X t ω) P)
    (hYmeas : AEMeasurable (fun ω (t : Time) => Y t ω) Q) :
    IdentDistrib (fun ω (t : Time) => X t ω)
      (fun ω t => Y t ω) P Q := by
  let μX : Measure (∀ t : Time, E) := P.map (fun ω t => X t ω)
  let μY : Measure (∀ t : Time, E) := Q.map (fun ω t => Y t ω)
  let fddX : ∀ I : Finset Time, Measure (∀ i : I, E) :=
    fun I => P.map (fun ω => I.restrict (X · ω))
  let fddY : ∀ I : Finset Time, Measure (∀ i : I, E) :=
    fun I => Q.map (fun ω => I.restrict (Y · ω))
  have hprojX : IsProjectiveLimit μX fddX := by
    exact isProjectiveLimit_map hXmeas
  have hprojY : IsProjectiveLimit μY fddY := by
    exact isProjectiveLimit_map hYmeas
  have hfinite (I : Finset Time) : IsFiniteMeasure (fddY I) := by
    rw [← hprojY I]
    infer_instance
  let _ : ∀ I, IsFiniteMeasure (fddY I) := hfinite
  have hprojXY : IsProjectiveLimit μX fddY := by
    intro I
    rw [hprojX I]
    exact (hX.finiteRestriction_identDistrib hY hXstart hYstart hinc I).map_eq
  have hmap : μX = μY := hprojXY.unique hprojY
  exact ⟨hXmeas, hYmeas, hmap⟩

/-- On a countable linearly ordered time type with a least element, independent
increment processes with matching increment distributions and zero starts
have the same function-valued process law. Coordinate measurability combines
using countability; the finite-dimensional-law uniqueness argument itself is
the preceding version, which accepts measurability of the whole process map.
-/
theorem HasIndepIncrements.process_identDistrib
    {Time : Type*} [LinearOrder Time] [OrderBot Time] [Countable Time]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {X : Time → Ω → E} {Y : Time → Ω' → E}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hX : HasIndepIncrements X P) (hY : HasIndepIncrements Y Q)
    (hXstart : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (hYstart : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hinc : ∀ s t : Time, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q)
    (hXincMeas : ∀ s t : Time, s ≤ t →
      AEMeasurable (fun ω => X t ω - X s ω) P)
    (hYincMeas : ∀ s t : Time, s ≤ t →
      AEMeasurable (fun ω => Y t ω - Y s ω) Q) :
    IdentDistrib (fun ω (t : Time) => X t ω)
      (fun ω t => Y t ω) P Q := by
  have hXmeas : AEMeasurable (fun ω (t : Time) => X t ω) P :=
    AEMeasurable.of_eval (fun t =>
      HasIndepIncrements.aemeasurable_eval hXstart hXincMeas t)
  have hYmeas : AEMeasurable (fun ω (t : Time) => Y t ω) Q :=
    AEMeasurable.of_eval (fun t =>
      HasIndepIncrements.aemeasurable_eval hYstart hYincMeas t)
  exact hX.process_identDistrib_of_aemeasurable hY hXstart hYstart hinc
    hXmeas hYmeas

end ProbabilityTheory

end
