/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.FiniteDimensional.Dense
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Topology.Order.UnitInterval.Rational

/-!
# Self-similarity of stable Lévy path laws

## Public declarations

- `ProbabilityTheory.IsStableClockProcessLaw.unitInterval_measure_eq`:
  two probability measures on càdlàg paths over $[0,1]$ with the same strictly
  stable increment laws and clock have the same path law. Equality of the
  finite coordinate laws on the rational unit-interval grid determines the
  measure on Skorokhod space.
- `ProbabilityTheory.IsStableLevyProcess.unitIntervalPathLaw_timeSpaceScale`:
  for a strictly $\alpha$-stable Lévy process and every $r>0$,
  \[
    \mathcal L\bigl((r^{-1/\alpha}X_{rt})_{0\le t\le1}\bigr)
      =\mathcal L\bigl((X_t)_{0\le t\le1}\bigr).
  \]
  The proof first checks that the rescaled process has the same stable-clock
  path-law specification, then applies the dense-coordinate uniqueness result.
-/

@[expose] public section

open MeasureTheory
open MeasureTheory.CadlagPath
open ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Stable clock-process probability measures on the unit-interval càdlàg
path space are determined by their common clock and stable increment law. -/
theorem IsStableClockProcessLaw.unitInterval_measure_eq
    {α : ℝ} {μ : Measure ℝ}
    {P Q : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hQ : IsStableClockProcessLaw α μ unitInterval.clock Q) :
    P = Q := by
  let time : RationalCoordinate.UnitInterval → unitInterval :=
    RationalCoordinate.toUnitInterval
  have htimeMono : Monotone time := by
    intro s t hst
    change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
    exact_mod_cast hst
  have htimeBot : time ⊥ = ⊥ := by
    apply Subtype.ext
    simp [time, RationalCoordinate.toUnitInterval]
  have hP' : HasStableClockIncrements α μ
      (fun q : RationalCoordinate.UnitInterval => unitInterval.clock (time q))
      (fun q f => f (time q)) P := by
    simpa [time, IsStableClockProcessLaw, cadlagPathProcess] using
      hP.comp_time time htimeMono htimeBot
  have hQ' : HasStableClockIncrements α μ
      (fun q : RationalCoordinate.UnitInterval => unitInterval.clock (time q))
      (fun q f => f (time q)) Q := by
    simpa [time, IsStableClockProcessLaw, cadlagPathProcess] using
      hQ.comp_time time htimeMono htimeBot
  have hPmeas : AEMeasurable
      (fun (f : CadlagPath unitInterval ℝ)
          (q : RationalCoordinate.UnitInterval) => f (time q)) P :=
    AEMeasurable.of_eval fun q => hP'.aemeasurable_eval q
  have hQmeas : AEMeasurable
      (fun (f : CadlagPath unitInterval ℝ)
          (q : RationalCoordinate.UnitInterval) => f (time q)) Q :=
    AEMeasurable.of_eval fun q => hQ'.aemeasurable_eval q
  have hcoordinates :=
    hP'.process_identDistrib_of_aemeasurable hQ' hPmeas hQmeas
  have hdense : P.map (denseEvaluation time) = Q.map (denseEvaluation time) := by
    change P.map (fun (f : CadlagPath unitInterval ℝ)
        (q : RationalCoordinate.UnitInterval) => f (time q)) =
      Q.map (fun (f : CadlagPath unitInterval ℝ)
        (q : RationalCoordinate.UnitInterval) => f (time q))
    exact hcoordinates.map_eq
  have hfinite : ∀ I : Finset RationalCoordinate.UnitInterval,
      P.map (denseEvaluation (fun i : I => time i.1)) =
        Q.map (denseEvaluation (fun i : I => time i.1)) := by
    intro I
    let restrict : (RationalCoordinate.UnitInterval → ℝ) → I → ℝ :=
      fun f i => f i.1
    have hrestrict : Measurable restrict := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_pi_apply i.1
    have hcompose : restrict ∘ denseEvaluation time =
        denseEvaluation (fun i : I => time i.1) := by
      funext f i
      rfl
    calc
      P.map (denseEvaluation (fun i : I => time i.1)) =
          P.map (restrict ∘ denseEvaluation time) := by rw [hcompose]
      _ = (P.map (denseEvaluation time)).map restrict := by
        rw [Measure.map_map hrestrict (measurable_denseEvaluation time)]
      _ = (Q.map (denseEvaluation time)).map restrict := by rw [hdense]
      _ = Q.map (restrict ∘ denseEvaluation time) := by
        rw [Measure.map_map hrestrict (measurable_denseEvaluation time)]
      _ = Q.map (denseEvaluation (fun i : I => time i.1)) := by rw [hcompose]
  have htop : (⊤ : unitInterval) ∈ Set.range time := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [time, RationalCoordinate.toUnitInterval]
  exact MeasureTheory.CadlagPath.measure_eq_of_map_finiteDenseEvaluation_eq
    time RationalCoordinate.denseRange_toUnitInterval htimeMono htop P Q hfinite

/-- The unit-interval path law of a strictly stable Lévy process is invariant
under the stable time-space rescaling. -/
theorem IsStableLevyProcess.unitIntervalPathLaw_timeSpaceScale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (r : ℝ≥0) (hr : 0 < r) :
    ((h.timeSpaceScale r hr).toIsLevyProcess.unitIntervalPathLaw 1 :
      Measure (CadlagPath unitInterval ℝ)) =
    (h.toIsLevyProcess.unitIntervalPathLaw 1 :
      Measure (CadlagPath unitInterval ℝ)) := by
  exact IsStableClockProcessLaw.unitInterval_measure_eq
    (h.timeSpaceScale r hr).isStableClockProcessLaw_unitIntervalPathLaw
    h.isStableClockProcessLaw_unitIntervalPathLaw

end ProbabilityTheory

end
