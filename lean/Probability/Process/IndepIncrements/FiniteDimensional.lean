module

public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Finite-dimensional laws from independent increments

Two processes with independent increments, almost-surely zero initial values,
and matching one-increment laws have matching position laws on finite grids.
On a countable time type, Mathlib's finite-dimensional-law uniqueness theorem
then identifies their laws as function-valued processes.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The vector of partial sums associated with a finite vector of increments.
Coordinate `i` contains the first `i + 1` increments. -/
noncomputable def finiteIncrementSums {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.Iic i, x j

theorem measurable_finiteIncrementSums (n : ℕ) :
    Measurable (@finiteIncrementSums n) := by
  classical
  rw [measurable_pi_iff]
  intro i
  exact Finset.measurable_sum (Finset.Iic i)
    (fun j _ => measurable_pi_apply j)

/-- Independent-increment processes with matching increment distributions and
zero initial values have the same position-vector law on every finite
monotone grid. The two processes may live on different probability spaces.
-/
theorem HasIndepIncrements.finiteDimensional_identDistrib
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hX : HasIndepIncrements X P) (hY : HasIndepIncrements Y Q)
    (hXstart : ∀ᵐ ω ∂P, X ⊥ ω = 0)
    (hYstart : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hinc : ∀ s t : Time, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q)
    (n : ℕ) (grid : Fin (n + 1) → Time) (hgrid : Monotone grid)
    (hgridStart : grid 0 = ⊥) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) => Y (grid i.succ) ω) P Q := by
  let dX : Fin n → Ω → ℝ := fun i ω =>
    X (grid i.succ) ω - X (grid i.castSucc) ω
  let dY : Fin n → Ω' → ℝ := fun i ω =>
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
  let partialSums : (Fin n → ℝ) → (Fin n → ℝ) := finiteIncrementSums
  have hpartialSums : Measurable partialSums := measurable_finiteIncrementSums n
  have hpositions := hvector.comp hpartialSums
  have hXeq : (fun ω (i : Fin n) => X (grid i.succ) ω) =ᵐ[P]
      fun ω => partialSums (fun j => dX j ω) := by
    filter_upwards [hXstart] with ω hω
    funext i
    dsimp [partialSums, finiteIncrementSums, dX]
    have htel := Fin.sum_Iic_sub i (fun j => X (grid j) ω)
    have hbase : X (grid 0) ω = 0 := by simpa [hgridStart] using hω
    rw [htel, hbase]
    ring
  have hYeq : (fun ω (i : Fin n) => Y (grid i.succ) ω) =ᵐ[Q]
      fun ω => partialSums (fun j => dY j ω) := by
    filter_upwards [hYstart] with ω hω
    funext i
    dsimp [partialSums, finiteIncrementSums, dY]
    have htel := Fin.sum_Iic_sub i (fun j => Y (grid j) ω)
    have hbase : Y (grid 0) ω = 0 := by simpa [hgridStart] using hω
    rw [htel, hbase]
    ring
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

/-- Matching increment laws imply matching restrictions of the position
processes to any finite set of times in a linear order with a least element.
The least element is prepended to the ordered finite set to anchor the
partial-sum reconstruction at the common zero start.
-/
theorem HasIndepIncrements.finiteRestriction_identDistrib
    {Time : Type*} [LinearOrder Time] [OrderBot Time]
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
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
  let reindex : (Fin I.card → ℝ) → (i : I) → ℝ := fun v i => v (e.symm i)
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
almost-everywhere measurable when its increments have real-valued laws.
-/
theorem HasIndepIncrements.aemeasurable_eval
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {X : Time → Ω → ℝ} {P : Measure Ω}
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
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
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
  let μX : Measure (∀ t : Time, ℝ) := P.map (fun ω t => X t ω)
  let μY : Measure (∀ t : Time, ℝ) := Q.map (fun ω t => Y t ω)
  let fddX : ∀ I : Finset Time, Measure (∀ i : I, ℝ) :=
    fun I => P.map (fun ω => I.restrict (X · ω))
  let fddY : ∀ I : Finset Time, Measure (∀ i : I, ℝ) :=
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
    {X : Time → Ω → ℝ} {Y : Time → Ω' → ℝ}
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
