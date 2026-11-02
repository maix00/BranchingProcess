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
- `ProbabilityTheory.IsLevyProcess.tendsto_unitIntervalPathLaw_of_tight_of_time_marginal_convergence`:
  the same path-law convergence follows when every rescaled one-time marginal
  \(\operatorname{Law}(X_i(T_i t))\) converges to \(\operatorname{Law}(Y_t)\);
  stationarity and zero start identify each interval-increment law with its
  marginal at the interval length.

These theorems isolate the path-space step needed for process-level limit
arguments. Their increment-law and tightness hypotheses are supplied by a
separate domain-of-attraction or Lévy-process convergence theorem.
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
    have : ∀ j : Fin n, IsProbabilityMeasure
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

/-- Tightness and convergence of every rescaled one-time marginal imply weak
convergence of the corresponding unit-interval path laws for Lévy processes.
Stationary increments and the zero-start property identify the law of an
increment over `[s,t]` with the marginal law at time `t - s`; the preceding
increment criterion then gives the path-space limit. -/
theorem tendsto_unitIntervalPathLaw_of_tight_of_time_marginal_convergence
    (hX : ∀ i, IsLevyProcess (X i) (P i))
    (hY : IsLevyProcess Y P₀)
    (horizon : ι → ℝ≥0)
    (htight : IsTightMeasureSet
      {((hX i).unitIntervalPathLaw (horizon i) : Measure
        (CadlagPath unitInterval ℝ)) | i})
    (hmarginal : ∀ t : ℝ≥0,
      TendstoInDistribution
        (fun i ω => X i (horizon i * t) ω) l
        (fun ω => Y t ω) P P₀) :
    Tendsto (fun i => hX i |>.unitIntervalPathLaw (horizon i)) l
      (nhds (hY.unitIntervalPathLaw 1)) := by
  apply tendsto_unitIntervalPathLaw_of_tight_of_increment_convergence
    hX hY horizon htight
  intro s t hst
  let s' : ℝ≥0 := unitInterval.toNNReal s
  let t' : ℝ≥0 := unitInterval.toNNReal t
  let duration : ℝ≥0 := t' - s'
  have hst' : s' ≤ t' := hst
  have hsum : s' + duration = t' := add_tsub_cancel_of_le hst'
  have hsourceIdent (i : ι) :
      IdentDistrib
        (fun ω => X i (horizon i * t') ω - X i (horizon i * s') ω)
        (fun ω => X i (horizon i * duration) ω) (P i) (P i) := by
    have htime : horizon i * s' + horizon i * duration = horizon i * t' := by
      rw [← mul_add, hsum]
    simpa only [htime] using
      (hX i).stationaryIncrements.identDistrib_increment_of_ae_start
        (hX i).ae_start_eq_zero (horizon i * s')
        (horizon i * duration)
  have htargetIdent : IdentDistrib
      (fun ω => Y duration ω)
      (fun ω => Y t' ω - Y s' ω) P₀ P₀ := by
    simpa only [hsum] using
      (hY.stationaryIncrements.identDistrib_increment_of_ae_start
        hY.ae_start_eq_zero s' duration).symm
  have hincrementRealized : TendstoInDistribution
      (fun i ω => X i (horizon i * t') ω - X i (horizon i * s') ω) l
      (fun ω => Y t' ω - Y s' ω) P P₀ := by
    have hfromMarginal : TendstoInDistribution
        (fun i ω => X i (horizon i * duration) ω) l
        (fun ω => Y duration ω) P P₀ := hmarginal duration
    have hsourceEq : ∀ᶠ i in l,
        (P i).map (fun ω => X i (horizon i * duration) ω) =
        (P i).map (fun ω => X i (horizon i * t') ω -
          X i (horizon i * s') ω) :=
      Eventually.of_forall fun i => (hsourceIdent i).map_eq.symm
    have hsourceMeas (i : ι) : AEMeasurable
        (fun ω => X i (horizon i * t') ω - X i (horizon i * s') ω) (P i) :=
      (hX i).aemeasurable_eval _ |>.sub ((hX i).aemeasurable_eval _)
    have hincrement' := hfromMarginal.congr_map_eventually hsourceEq hsourceMeas
    have htargetMeas : AEMeasurable
        (fun ω => Y t' ω - Y s' ω) P₀ :=
      (hY.aemeasurable_eval _).sub (hY.aemeasurable_eval _)
    exact hincrement'.congr_limit htargetMeas htargetIdent.map_eq
  have htargetMeas : AEMeasurable
      (fun ω => Y t' ω - Y s' ω) P₀ :=
    (hY.aemeasurable_eval _).sub (hY.aemeasurable_eval _)
  let incrementLaw : Measure ℝ := P₀.map (fun ω => Y t' ω - Y s' ω)
  have : IsProbabilityMeasure incrementLaw :=
    (Measure.isProbabilityMeasure_map_iff htargetMeas).2 inferInstance
  have htargetMap : P₀.map (fun ω => Y t' ω - Y s' ω) =
      incrementLaw.map id := by
    simp [incrementLaw]
  exact hincrementRealized.congr_limit (Omega'' := ℝ) (μ'' := incrementLaw)
    (Z' := id) (aemeasurable_id : AEMeasurable id incrementLaw) htargetMap

end ProbabilityTheory.IsLevyProcess

end
