/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Cadlag.FiniteDimensional.Dense
public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.Basic
public import Topology.Order.UnitInterval.Rational

/-!
# Terminal left-limit modification of càdlàg paths

On the compact unit interval, replacing the value of a càdlàg path at the top
endpoint by its left limit gives the endpoint convention used by left-continuous
path encodings. The transformation is Borel measurable for the Skorokhod
`J₁` path-space structure.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.Process.Path.Cadlag

/-- Replace the value of a real càdlàg path at the terminal time `1` by its
left limit there. -/
noncomputable def terminalLeftPath
    (path : CadlagPath unitInterval ℝ) : CadlagPath unitInterval ℝ :=
  ⟨(fun t => if t = ⊤ then Function.leftLim (fun s : unitInterval => path s) ⊤
      else path t),
    path.isCadlag_toFun.updateTop
      (Function.leftLim (fun s : unitInterval => path s) ⊤)⟩

@[simp]
theorem terminalLeftPath_apply_top (path : CadlagPath unitInterval ℝ) :
    terminalLeftPath path ⊤ = Function.leftLim (fun s : unitInterval => path s) ⊤ := by
  simp [terminalLeftPath]

@[simp]
theorem terminalLeftPath_apply_of_ne_top (path : CadlagPath unitInterval ℝ)
    {t : unitInterval} (ht : t ≠ ⊤) :
    terminalLeftPath path t = path t := by
  simp [terminalLeftPath, ht]

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
  let time := RationalCoordinate.toUnitInterval
  have htimeMono : Monotone time := by
    intro s t hst
    change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
    exact_mod_cast hst
  have htop : (⊤ : unitInterval) ∈ Set.range time := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    norm_num [time, RationalCoordinate.toUnitInterval]
  let evaluation := Skorokhod.denseEvaluation time
  have hevaluation : MeasurableEmbedding
      (evaluation : CadlagPath unitInterval ℝ →
        RationalCoordinate.UnitInterval → ℝ) :=
    Skorokhod.measurableEmbedding_denseEvaluation time
      RationalCoordinate.denseRange_toUnitInterval htimeMono htop
  have hleft : Measurable (fun path : CadlagPath unitInterval ℝ =>
      Function.leftLim (fun s : unitInterval => path s) ⊤) :=
    measurable_terminalLeftValue
  have hcoordinates : Measurable
      (evaluation ∘ terminalLeftPath : CadlagPath unitInterval ℝ →
        RationalCoordinate.UnitInterval → ℝ) := by
    rw [measurable_pi_iff]
    intro q
    change Measurable (fun path : CadlagPath unitInterval ℝ =>
      terminalLeftPath path (time q))
    by_cases hq : time q = ⊤
    · have heq : (fun path : CadlagPath unitInterval ℝ =>
          terminalLeftPath path (time q)) = fun path =>
          Function.leftLim (fun s : unitInterval => path s) ⊤ := by
        funext path
        simp [terminalLeftPath, hq]
      rw [heq]
      exact hleft
    · have heq : (fun path : CadlagPath unitInterval ℝ =>
          terminalLeftPath path (time q)) = fun path => path (time q) := by
        funext path
        simp [terminalLeftPath, hq]
      rw [heq]
      exact Skorokhod.measurable_apply (time q)
  exact hevaluation.measurable_comp_iff.mp hcoordinates

end ProbabilityTheory.Process.Path.Cadlag

end
