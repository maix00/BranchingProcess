/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.CadlagPath.FiniteDimensional
public import Probability.Process.IndepIncrements.Convergence
public import Probability.Process.IndepIncrements.FiniteDimensional
public import Probability.Process.Levy.PathLaw.UnitInterval

/-!
# Weak convergence of Lévy path laws on the unit interval

## Public declarations

- `ProbabilityTheory.IsLevyProcess.tendsto_unitIntervalPathLaw_of_tight_of_increment_convergence`:
  a tight family of unit-interval path laws converges weakly to a target Lévy
  path law when each rescaled interval increment converges in distribution to
  the corresponding target increment. In symbols, if
  \(\operatorname{Law}(X_i(T_i t)-X_i(T_i s))\Rightarrow
  \operatorname{Law}(Y_t-Y_s)\) for each \(0\le s\le t\le1\), and the laws
  of \(t\mapsto X_i(T_i t)\) are tight, then
  \(\operatorname{Law}(t\mapsto X_i(T_i t))\Rightarrow
  \operatorname{Law}(t\mapsto Y_t)\) in Skorokhod path space. Finite-grid
  position convergence follows from independent increments.

The theorem isolates the path-space step needed for process-level limit
arguments. Its increment-law hypothesis is supplied by a separate
domain-of-attraction or Lévy-process convergence theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.CadlagPath
open Skorokhod
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.IsLevyProcess

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {P : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
  {X : ∀ i, ℝ≥0 → Ω i → ℝ}
  {Ω₀ : Type*} [MeasurableSpace Ω₀]
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
  {Y : ℝ≥0 → Ω₀ → ℝ}

/-- Tightness and convergence of every rescaled interval increment imply weak
convergence of the corresponding unit-interval path laws for Lévy processes.
The increment limits are the increments of the target process, so the
finite-grid limit is its own path-law evaluation. -/
theorem tendsto_unitIntervalPathLaw_of_tight_of_increment_convergence
    (hX : ∀ i, IsLevyProcess (X i) (P i))
    (hY : IsLevyProcess Y P₀)
    (horizon : ι → ℝ≥0)
    (htight : IsTightMeasureSet
      {((hX i).unitIntervalPathLaw (horizon i) : Measure
        (CadlagPath unitInterval ℝ)) | i})
    (hincrement : ∀ (s t : unitInterval), s ≤ t →
      TendstoInDistribution
        (fun i ω => X i (horizon i * unitInterval.toNNReal t) ω -
          X i (horizon i * unitInterval.toNNReal s) ω)
        l id P
        (P₀.map (fun ω => Y (unitInterval.toNNReal t) ω -
          Y (unitInterval.toNNReal s) ω))) :
    Tendsto (fun i => hX i |>.unitIntervalPathLaw (horizon i)) l
      (nhds (hY.unitIntervalPathLaw 1)) := by
  let sourcePath : ∀ i, unitInterval → Ω i → ℝ := fun i t ω =>
    X i (horizon i * unitInterval.toNNReal t) ω
  let targetPath : unitInterval → Ω₀ → ℝ := fun t ω =>
    Y (unitInterval.toNNReal t) ω
  have hincrements (i : ι) : HasIndepIncrements (sourcePath i) (P i) := by
    intro n grid hgrid
    have htime : Monotone (fun j : Fin (n + 1) =>
        horizon i * unitInterval.toNNReal (grid j)) := by
      intro j k hjk
      exact mul_le_mul_of_nonneg_left (hgrid hjk) (horizon i).2
    simpa [sourcePath] using (hX i).indepIncrements n
      (fun j => horizon i * unitInterval.toNNReal (grid j)) htime
  have htargetIncrements : HasIndepIncrements targetPath P₀ := by
    intro n grid hgrid
    have htime : Monotone (fun j : Fin (n + 1) => unitInterval.toNNReal (grid j)) := by
      intro j k hjk
      exact hgrid hjk
    simpa [targetPath] using hY.indepIncrements n
      (fun j => unitInterval.toNNReal (grid j)) htime
  have htargetStart : ∀ᵐ ω ∂P₀, targetPath (⊥ : unitInterval) ω = 0 := by
    filter_upwards [hY.ae_start_eq_zero] with ω hω
    have htime : unitInterval.toNNReal (⊥ : unitInterval) = 0 := by
      apply Subtype.ext
      simp [unitInterval.toNNReal]
    simpa [targetPath, htime] using hω
  have htargetIncrementMeas (s t : unitInterval) :
      AEMeasurable (fun ω => targetPath t ω - targetPath s ω) P₀ := by
    exact (hY.aemeasurable_eval _).sub (hY.aemeasurable_eval _)
  have hgridConvergence
      (n : ℕ) (grid : Fin (n + 1) → unitInterval)
      (hgrid : StrictMono grid) (hgridStart : grid 0 = ⊥) :
      TendstoInDistribution (fun i ω j => sourcePath i (grid j) ω) l
        (fun ω j => targetPath (grid j) ω) P P₀ := by
    have hsourceStart : ∀ i, ∀ᵐ ω ∂P i, sourcePath i (grid 0) ω = 0 := by
      intro i
      filter_upwards [(hX i).ae_start_eq_zero] with ω hω
      have htime : unitInterval.toNNReal (⊥ : unitInterval) = 0 := by
        apply Subtype.ext
        simp [unitInterval.toNNReal]
      simpa [sourcePath, hgridStart, htime] using hω
    have hlimitProbability (j : Fin n) : IsProbabilityMeasure
        (P₀.map (fun ω => targetPath (grid j.succ) ω -
          targetPath (grid j.castSucc) ω)) := by
      exact (Measure.isProbabilityMeasure_map_iff
        (htargetIncrementMeas (grid j.castSucc) (grid j.succ))).2 inferInstance
    haveI : ∀ j : Fin n, IsProbabilityMeasure
        (P₀.map (fun ω => targetPath (grid j.succ) ω -
          targetPath (grid j.castSucc) ω)) := hlimitProbability
    have hinc (j : Fin n) : TendstoInDistribution
        (fun i ω => sourcePath i (grid j.succ) ω - sourcePath i (grid j.castSucc) ω)
        l id P
        (P₀.map (fun ω => targetPath (grid j.succ) ω -
          targetPath (grid j.castSucc) ω)) := by
      exact hincrement (grid j.castSucc) (grid j.succ)
        (hgrid.monotone (Fin.castSucc_le_succ j))
    have hpositions := HasIndepIncrements.tendstoInDistribution_positions_of_increment_convergence
      (grid := grid) hgrid.monotone hsourceStart hincrements hinc
    have htargetPositionsLaw :=
      htargetIncrements.hasLaw_finiteDimensional_of_incrementLaws
        htargetStart n grid hgrid.monotone hgridStart
        (fun j => htargetIncrementMeas (grid j.castSucc) (grid j.succ))
    exact TendstoInDistribution.congr_limit
      (Z' := fun ω j => targetPath (grid j) ω) hpositions
      htargetPositionsLaw.aemeasurable htargetPositionsLaw.map_eq.symm
  have hfinite (n : ℕ) (grid : Fin (n + 1) → unitInterval)
      (hgrid : StrictMono grid) (hgridStart : grid 0 = ⊥) :
      Tendsto (fun i => ((hX i).unitIntervalPathLaw (horizon i)).map
        (denseEvaluation grid)) l
        (nhds ((hY.unitIntervalPathLaw 1).map (denseEvaluation grid))) := by
    have hpositions := hgridConvergence n grid hgrid hgridStart
    have hsourceEval (i : ι) :=
      (hX i).unitIntervalPathLaw_finite_eval_hasLaw (horizon i) (n + 1) grid
    have htargetEval := hY.unitIntervalPathLaw_finite_eval_hasLaw 1 (n + 1) grid
    have hsourceLaw (i : ι) :
        ((P i).map (fun ω j => sourcePath i (grid j) ω)).toProbabilityMeasure =
          ((hX i).unitIntervalPathLaw (horizon i)).map (denseEvaluation grid) := by
      apply Subtype.ext
      exact (hsourceEval i).map_eq
    have htargetLaw :
        (P₀.map (fun ω j => targetPath (grid j) ω)).toProbabilityMeasure =
          (hY.unitIntervalPathLaw 1).map (denseEvaluation grid) := by
      apply Subtype.ext
      change P₀.map (fun ω j => Y (unitInterval.toNNReal (grid j)) ω) =
        (((hY.unitIntervalPathLaw 1 : ProbabilityMeasure
          (CadlagPath unitInterval ℝ)) : Measure (CadlagPath unitInterval ℝ)).map
            (fun f j => f (grid j)))
      simpa only [one_mul] using htargetEval.map_eq
    rw [← htargetLaw]
    apply hpositions.tendsto.congr'
    filter_upwards [] with i
    exact hsourceLaw i
  exact CadlagPath.ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation
    (fun i => hX i |>.unitIntervalPathLaw (horizon i))
    (hY.unitIntervalPathLaw 1) htight hfinite

end ProbabilityTheory.IsLevyProcess

end
