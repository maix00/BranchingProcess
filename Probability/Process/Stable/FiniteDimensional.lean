module

public import Probability.Process.Stable.Levy

/-!
# Finite-dimensional laws of stable-increment processes

Independent increments determine the joint law of positions on every finite
time grid once the initial value is fixed. This is the process-level bridge
needed to turn stable time-space scaling into equality of finite-dimensional
distributions.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

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

/-- Two processes with the same stable clock-increment laws and zero initial
value have the same law on every finite monotone grid after time zero. The
proof reconstructs each position as a partial sum of consecutive increments.
-/
theorem HasStableClockIncrements.finiteDimensional_identDistrib
    {Time : Type*} [Preorder Time] [OrderBot Time]
    {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
    {X Y : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y P)
    (n : ℕ) (grid : Fin (n + 1) → Time) (hgrid : Monotone grid)
    (hstart : grid 0 = ⊥) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) => Y (grid i.succ) ω) P P := by
  let dX : Fin n → Ω → ℝ := fun i ω => X (grid i.succ) ω - X (grid i.castSucc) ω
  let dY : Fin n → Ω → ℝ := fun i ω => Y (grid i.succ) ω - Y (grid i.castSucc) ω
  let incrementLaw : Measure (Fin n → ℝ) :=
    Measure.pi fun i : Fin n =>
      μ.map fun x => (clock (grid i.succ) - clock (grid i.castSucc)) ^ (1 / α) * x
  have hXinc : HasLaw (fun ω i => dX i ω) incrementLaw P := by
    simpa [dX, incrementLaw] using hX.increments_hasLaw_pi n grid hgrid
  have hYinc : HasLaw (fun ω i => dY i ω) incrementLaw P := by
    simpa [dY, incrementLaw] using hY.increments_hasLaw_pi n grid hgrid
  let partialSums : (Fin n → ℝ) → (Fin n → ℝ) := finiteIncrementSums
  have hpartialSums : Measurable partialSums := measurable_finiteIncrementSums n
  have hXsum : HasLaw (fun ω => partialSums (fun i => dX i ω))
      (incrementLaw.map partialSums) P := by
    exact (MeasurePreserving.hasLaw ⟨hpartialSums, rfl⟩).fun_comp hXinc
  have hYsum : HasLaw (fun ω => partialSums (fun i => dY i ω))
      (incrementLaw.map partialSums) P := by
    exact (MeasurePreserving.hasLaw ⟨hpartialSums, rfl⟩).fun_comp hYinc
  have hXeq : (fun ω (i : Fin n) => X (grid i.succ) ω) =ᵐ[P]
      fun ω => partialSums (fun j => dX j ω) := by
    filter_upwards [hX.ae_start_eq_zero] with ω hω
    funext i
    dsimp [partialSums, finiteIncrementSums, dX]
    have htel := Fin.sum_Iic_sub i (fun j => X (grid j) ω)
    have hbase : X (grid 0) ω = 0 := by simpa [hstart] using hω
    rw [htel, hbase]
    ring
  have hYeq : (fun ω (i : Fin n) => Y (grid i.succ) ω) =ᵐ[P]
      fun ω => partialSums (fun j => dY j ω) := by
    filter_upwards [hY.ae_start_eq_zero] with ω hω
    funext i
    dsimp [partialSums, finiteIncrementSums, dY]
    have htel := Fin.sum_Iic_sub i (fun j => Y (grid j) ω)
    have hbase : Y (grid 0) ω = 0 := by simpa [hstart] using hω
    rw [htel, hbase]
    ring
  exact (hXsum.congr hXeq).identDistrib (hYsum.congr hYeq)

/-- A stable Lévy process and its canonical time-space rescaling have the same
joint law at every finite monotone grid. This is the finite-dimensional form
of the self-similarity identity; it deliberately makes no path-space law
claim. -/
theorem IsStableLevyProcess.timeSpaceScale_positions_identDistrib
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (r : ℝ≥0) (hr : 0 < r)
    (n : ℕ) (grid : Fin (n + 1) → ℝ≥0) (hgrid : Monotone grid)
    (hstart : grid 0 = 0) :
    IdentDistrib
      (fun ω (i : Fin n) => X (grid i.succ) ω)
      (fun ω (i : Fin n) =>
        (r : ℝ) ^ (-(1 / α)) * X (r * grid i.succ) ω) P P := by
  apply h.increments.finiteDimensional_identDistrib
    (h.timeSpaceScale r hr).increments n grid hgrid ?_
  simpa using hstart

end ProbabilityTheory
