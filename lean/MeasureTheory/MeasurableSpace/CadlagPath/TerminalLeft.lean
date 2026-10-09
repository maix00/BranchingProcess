/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.MeasurableSpace.CadlagPath
public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.TerminalLeft
public import Topology.Order.UnitInterval.Rational

/-!
# Measurability of the terminal left-limit modification

The left-limit functional and the path transformation that replaces the
terminal value by that left limit are Borel measurable for the Skorokhod
`J₁` path-space structure.
-/

@[expose] public section

open Filter
open Skorokhod
open scoped Topology

namespace MeasureTheory.CadlagPath

/-- The terminal left-limit functional is Borel measurable on Skorokhod path
space. It is the pointwise limit of evaluations along rational times increasing
to `1`. -/
theorem measurable_terminalLeftValue :
    Measurable
      (fun path : CadlagPath unitInterval ℝ =>
        Function.leftLim (fun s : unitInterval => path s) ⊤) := by
  let time := RationalCoordinate.toUnitInterval
  have htimeMono : Monotone time := by
    intro s t hst
    change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
    exact_mod_cast hst
  have hbotTop : (⊥ : unitInterval) < ⊤ := by
    norm_num [unitInterval]
  obtain ⟨u, _, hu, hulim⟩ :=
    RationalCoordinate.denseRange_toUnitInterval.exists_seq_strictMono_tendsto_of_lt
      htimeMono hbotTop
  have hwithin : Tendsto (fun n => time (u n)) atTop (𝓝[<] (⊤ : unitInterval)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hulim, Filter.Eventually.of_forall fun n => (hu n).2⟩
  have hlimit : Tendsto
      (fun n (path : CadlagPath unitInterval ℝ) => path (time (u n))) atTop
      (𝓝 fun path : CadlagPath unitInterval ℝ =>
        Function.leftLim (fun s : unitInterval => path s) ⊤) := by
    rw [tendsto_pi_nhds]
    intro path
    exact (path.isCadlag_toFun.tendsto_nhdsLT_leftLim ⊤).comp hwithin
  exact measurable_of_tendsto_metrizable
    (fun n => Skorokhod.measurable_apply (time (u n))) hlimit

/-- The terminal left-limit transformation is Borel measurable for the
Skorokhod `J₁` path-space structure. The proof checks the rational-coordinate
embedding: coordinates before `1` are unchanged, and the endpoint coordinate
is the measurable left-limit functional. -/
theorem measurable_terminalLeftPath :
    Measurable (terminalLeftPath :
      CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ) := by
  let evaluation := Skorokhod.rationalEvaluation
  have hevaluation : MeasurableEmbedding
      (evaluation : CadlagPath unitInterval ℝ →
        Skorokhod.RationalUnitIntervalTime → ℝ) :=
    Skorokhod.measurableEmbedding_rationalEvaluation
  have hleft : Measurable (fun path : CadlagPath unitInterval ℝ =>
      Function.leftLim (fun s : unitInterval => path s) ⊤) :=
    measurable_terminalLeftValue
  have hcoordinates : Measurable
      (evaluation ∘ terminalLeftPath : CadlagPath unitInterval ℝ →
        Skorokhod.RationalUnitIntervalTime → ℝ) := by
    rw [measurable_pi_iff]
    intro q
    change Measurable (fun path : CadlagPath unitInterval ℝ =>
      terminalLeftPath path (Skorokhod.rationalTimeToUnitInterval q))
    by_cases hq : Skorokhod.rationalTimeToUnitInterval q = ⊤
    · have heq : (fun path : CadlagPath unitInterval ℝ =>
          terminalLeftPath path (Skorokhod.rationalTimeToUnitInterval q)) = fun path =>
          Function.leftLim (fun s : unitInterval => path s) ⊤ := by
        funext path
        simp [terminalLeftPath, hq]
      rw [heq]
      exact hleft
    · have heq : (fun path : CadlagPath unitInterval ℝ =>
          terminalLeftPath path (Skorokhod.rationalTimeToUnitInterval q)) =
            fun path => path (Skorokhod.rationalTimeToUnitInterval q) := by
        funext path
        simp [terminalLeftPath, hq]
      rw [heq]
      exact Skorokhod.measurable_apply (Skorokhod.rationalTimeToUnitInterval q)
  exact hevaluation.measurable_comp_iff.mp hcoordinates

end MeasureTheory.CadlagPath

end
