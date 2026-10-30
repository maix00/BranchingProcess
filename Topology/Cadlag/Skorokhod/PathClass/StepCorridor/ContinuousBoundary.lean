/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Path.TerminalLeft
public import Topology.Cadlag.Skorokhod.Maps.Continuous
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.UniformGrid
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Continuous path corridors

This file defines strict corridor events between continuous boundaries,
compares them with inward and outward step corridors, and constructs a
uniform-grid sandwich for a nonempty continuous corridor.

## Public declarations

- `continuousBoundaryCorridorSet lower upper` is the set of paths $f$ with
  $f(0)=0$ and $lower(t)<f(t)<upper(t)$ for all $t$;
  `relativeContinuousBoundaryCorridorSet` intersects it with the terminal-left
  path space.
- `corridorSet_subset_continuousBoundaryCorridorSet` and
  `continuousBoundaryCorridorSet_subset_corridorSet` compare the events when
  the step boundaries lie respectively inside or outside the continuous
  boundaries. The two `relative...subset...` results give the corresponding
  inclusions inside the terminal-left path space.
- `hasContinuousAdmissiblePath_of_witness` transfers a continuous strict
  witness to the step-corridor admissibility predicate;
  `exists_continuousCorridorCenter_with_uniformMargin` constructs a centered
  path with a common positive margin when the boundaries are pointwise
  separated and contain $0$ at the start.
- `ofContinuousMap_mem_terminalLeftPathSpace` embeds every continuous path
  into the terminal-left path space, and
  `exists_mem_relativeContinuousBoundaryCorridorSet` gives a path in the
  relative corridor under the same start and width assumptions.
- `exists_fine_uniformGrid_relativeCorridor_sandwich` gives inward and
  outward sampled step corridors whose events sandwich the relative
  continuous-boundary corridor whenever the mesh is sufficiently fine.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Skorokhod.PathClass.StepCorridor
/-- The paths starting at zero and lying strictly between two continuous
real-valued boundaries at every time. -/
def continuousBoundaryCorridorSet (lower upper : C(unitInterval, ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  {path | path ⊥ = 0 ∧ ∀ t : unitInterval, lower t < path t ∧ path t < upper t}

/-- The same corridor considered inside the endpoint convention `D₀`. -/
def relativeContinuousBoundaryCorridorSet (lower upper : C(unitInterval, ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.terminalLeftPathSpace ∩ continuousBoundaryCorridorSet lower upper

/-- A step corridor with inward boundaries is contained in the continuous
boundary corridor. The statement is pointwise and does not depend on the
choice of a partition. -/
theorem corridorSet_subset_continuousBoundaryCorridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (hinward : ∀ t, (lower t : EReal) < stepLower.eval t ∧
      stepUpper.eval t < (upper t : EReal)) :
    corridorSet stepUpper stepLower ⊆ continuousBoundaryCorridorSet lower upper := by
  intro path hpath
  rcases hpath with ⟨hzero, hcorridor⟩
  refine ⟨hzero, ?_⟩
  intro t
  constructor
  · apply EReal.coe_lt_coe_iff.mp
    exact (hinward t).1.trans (hcorridor t).1
  · apply EReal.coe_lt_coe_iff.mp
    exact (hcorridor t).2.trans (hinward t).2

/-- The continuous boundary corridor is contained in a step corridor with
outward boundaries. -/
theorem continuousBoundaryCorridorSet_subset_corridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (houtward : ∀ t, stepLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < stepUpper.eval t) :
    continuousBoundaryCorridorSet lower upper ⊆ corridorSet stepUpper stepLower := by
  intro path hpath
  rcases hpath with ⟨hzero, hcorridor⟩
  refine ⟨hzero, ?_⟩
  intro t
  constructor
  · exact (houtward t).1.trans (EReal.coe_lt_coe_iff.mpr (hcorridor t).1)
  · exact (EReal.coe_lt_coe_iff.mpr (hcorridor t).2).trans (houtward t).2

/-- A continuous path strictly between two finite-step boundaries witnesses
continuous admissibility of the corresponding step corridor. -/
theorem hasContinuousAdmissiblePath_of_witness
    (stepUpper stepLower : StepBoundary) (center : C(unitInterval, ℝ))
    (hcenterZero : center ⊥ = 0)
    (hcenter : ∀ t, stepLower.eval t < (center t : EReal) ∧
      (center t : EReal) < stepUpper.eval t) :
    HasContinuousAdmissiblePath stepUpper stepLower := by
  refine ⟨center, hcenterZero, ?_⟩
  refine ⟨hcenterZero, ?_⟩
  intro t
  exact hcenter t

/-- The same inward containment, restricted to `D₀`. -/
theorem relative_corridorSet_subset_relativeContinuousBoundaryCorridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (hinward : ∀ t, (lower t : EReal) < stepLower.eval t ∧
      stepUpper.eval t < (upper t : EReal)) :
    Skorokhod.terminalLeftPathSpace ∩ corridorSet stepUpper stepLower ⊆
      relativeContinuousBoundaryCorridorSet lower upper := by
  intro path hpath
  rcases hpath with ⟨hD₀, hcorridor⟩
  exact ⟨hD₀,
    corridorSet_subset_continuousBoundaryCorridorSet stepUpper stepLower lower upper
      hinward hcorridor⟩

/-- The same outward containment, restricted to `D₀`. -/
theorem relativeContinuousBoundaryCorridorSet_subset_relative_corridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (houtward : ∀ t, stepLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < stepUpper.eval t) :
    relativeContinuousBoundaryCorridorSet lower upper ⊆
      Skorokhod.terminalLeftPathSpace ∩ corridorSet stepUpper stepLower := by
  intro path hpath
  rcases hpath with ⟨hD₀, hcorridor⟩
  exact ⟨hD₀,
    continuousBoundaryCorridorSet_subset_corridorSet stepUpper stepLower lower upper
      houtward hcorridor⟩

/-- Strictly separated continuous boundaries admit a continuous center which
starts at zero and stays a uniform positive distance from both boundaries.
This is the compactness input for constructing finite step-corridor
approximations. -/
theorem exists_continuousCorridorCenter_with_uniformMargin
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ center : C(unitInterval, ℝ), ∃ margin : ℝ,
      0 < margin ∧ center ⊥ = 0 ∧
        ∀ t, lower t + margin ≤ center t ∧ center t + margin ≤ upper t := by
  let θ : ℝ := - lower ⊥ / (upper ⊥ - lower ⊥)
  have hden : 0 < upper ⊥ - lower ⊥ := by linarith [hstartLower, hstartUpper]
  have hθ : 0 < θ ∧ θ < 1 := by
    dsimp [θ]
    constructor
    · exact div_pos (neg_pos.mpr hstartLower) hden
    · rw [div_lt_one hden]
      linarith [hstartUpper]
  let center : C(unitInterval, ℝ) :=
    ⟨fun t => lower t + θ * (upper t - lower t),
      lower.continuous.add (continuous_const.mul (upper.continuous.sub lower.continuous))⟩
  have hwidthContinuous : Continuous fun t : unitInterval => upper t - lower t :=
    upper.continuous.sub lower.continuous
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set unitInterval).Nonempty from ⟨⊥, Set.mem_univ _⟩)
    hwidthContinuous.continuousOn
  have hwidth₀ : 0 < upper t₀ - lower t₀ := by
    have := hwidth t₀
    linarith
  let m₀ : ℝ := upper t₀ - lower t₀
  let margin : ℝ := min θ (1 - θ) * m₀ / 2
  have hm₀ : 0 < m₀ := by dsimp [m₀]; exact hwidth₀
  have hmargin : 0 < margin := by
    dsimp [margin]
    have hmin : 0 < min θ (1 - θ) := lt_min hθ.1 (by linarith [hθ.2])
    positivity
  refine ⟨center, margin, hmargin, ?_, ?_⟩
  · change lower ⊥ + θ * (upper ⊥ - lower ⊥) = 0
    dsimp [θ]
    field_simp [ne_of_gt hden]
    ring
  · intro t
    have hwidtht : m₀ ≤ upper t - lower t := by
      dsimp [m₀]
      exact ht₀ (Set.mem_univ t)
    have hleft : lower t + margin ≤ center t := by
      change lower t + margin ≤ lower t + θ * (upper t - lower t)
      have hθmin : min θ (1 - θ) ≤ θ := min_le_left _ _
      dsimp [margin]
      nlinarith [hwidtht, hθ.1, hθ.2]
    have hright : center t + margin ≤ upper t := by
      change lower t + θ * (upper t - lower t) + margin ≤ upper t
      have hθmin : min θ (1 - θ) ≤ 1 - θ := min_le_right _ _
      dsimp [margin]
      nlinarith [hwidtht, hθ.1, hθ.2]
    exact ⟨hleft, hright⟩

/-- A continuous path has no terminal jump, so it belongs to the source path
space `D₀`. -/
theorem ofContinuousMap_mem_terminalLeftPathSpace
    (path : C(unitInterval, ℝ)) :
    Skorokhod.ofContinuousMap path ∈ Skorokhod.terminalLeftPathSpace := by
  change Skorokhod.ofContinuousMap path ⊤ =
    Function.leftLim (fun t : unitInterval => Skorokhod.ofContinuousMap path t) ⊤
  have htop : (⊥ : unitInterval) < ⊤ := by norm_num [unitInterval]
  have hcontinuous : Tendsto (fun t : unitInterval => path t)
      (𝓝[<] (⊤ : unitInterval)) (𝓝 (path ⊤)) :=
    Filter.Tendsto.mono_left path.continuous.continuousAt.tendsto nhdsWithin_le_nhds
  have hleft := leftLim_eq_of_tendsto
    (h := nhdsLT_neBot_of_exists_lt ⟨⊥, htop⟩) hcontinuous
  simpa only [Skorokhod.ofContinuousMap_apply] using hleft.symm

/-- A strictly separated continuous corridor satisfying the pinned start
condition is nonempty even after restriction to `D₀`. -/
theorem exists_mem_relativeContinuousBoundaryCorridorSet
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ path, path ∈ relativeContinuousBoundaryCorridorSet lower upper := by
  obtain ⟨center, margin, hmargin, hcenter₀, hcenter⟩ :=
    exists_continuousCorridorCenter_with_uniformMargin lower upper hwidth
      hstartLower hstartUpper
  let path := Skorokhod.ofContinuousMap center
  refine ⟨path, ?_⟩
  constructor
  · exact ofContinuousMap_mem_terminalLeftPathSpace center
  · refine ⟨?_, ?_⟩
    · simpa [path, Skorokhod.ofContinuousMap_apply] using hcenter₀
    · intro t
      have ht := hcenter t
      constructor
      · exact lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) ht.1
      · exact lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) ht.2

private lemma sample_lt_add_two_of_abs {x y ε : ℝ} (hε : 0 < ε)
    (h : |x - y| < ε) : x < y + 2 * ε := by
  have hxy := (abs_lt.mp h).2
  linarith

private lemma sub_two_lt_sample_of_abs {x y ε : ℝ} (hε : 0 < ε)
    (h : |x - y| < ε) : y - 2 * ε < x := by
  have hxy := (abs_lt.mp h).1
  linarith

/-- Every strictly separated continuous corridor admits arbitrarily fine
uniform-grid inner and outer step corridors. The inner corridor lies inside
the continuous corridor and has a continuous witness; the target lies inside
the outer corridor. The conclusions remain valid after restriction to `D₀`.
This proves the deterministic set-sandwich part of continuous-boundary
approximation by the source's finite step corridors. -/
theorem exists_fine_uniformGrid_relativeCorridor_sandwich
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ center : C(unitInterval, ℝ), ∃ margin : ℝ,
      0 < margin ∧ center ⊥ = 0 ∧
        (∀ t, lower t + margin ≤ center t ∧ center t + margin ≤ upper t) ∧
        ∀ ε, 0 < ε → 3 * ε < margin →
          ∃ δ > 0, ∀ (blocks : ℕ) (hblocks : 0 < blocks),
            1 / (blocks : ℝ) < δ →
            let innerLower := uniformGridStepBoundary blocks hblocks lower (2 * ε)
            let innerUpper := uniformGridStepBoundary blocks hblocks upper (-2 * ε)
            let outerLower := uniformGridStepBoundary blocks hblocks lower (-2 * ε)
            let outerUpper := uniformGridStepBoundary blocks hblocks upper (2 * ε)
            (∀ t, (lower t : EReal) < innerLower.eval t ∧
              innerUpper.eval t < (upper t : EReal)) ∧
            (∀ t, outerLower.eval t < (lower t : EReal) ∧
              (upper t : EReal) < outerUpper.eval t) ∧
            HasContinuousAdmissiblePath innerUpper innerLower ∧
            HasContinuousAdmissiblePath outerUpper outerLower ∧
            Skorokhod.terminalLeftPathSpace ∩ corridorSet innerUpper innerLower ⊆
              relativeContinuousBoundaryCorridorSet lower upper ∧
            relativeContinuousBoundaryCorridorSet lower upper ⊆
              Skorokhod.terminalLeftPathSpace ∩ corridorSet outerUpper outerLower := by
  obtain ⟨center, margin, hmargin, hcenterZero, hcenter⟩ :=
    exists_continuousCorridorCenter_with_uniformMargin lower upper hwidth
      hstartLower hstartUpper
  refine ⟨center, margin, hmargin, hcenterZero, hcenter, ?_⟩
  intro ε hε hsmall
  obtain ⟨δL, hδL, herrorL⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error lower ε hε
  obtain ⟨δU, hδU, herrorU⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error upper ε hε
  let δ := min δL δU
  have hδ : 0 < δ := lt_min hδL hδU
  refine ⟨δ, hδ, ?_⟩
  intro blocks hblocks hmesh
  let innerLower := uniformGridStepBoundary blocks hblocks lower (2 * ε)
  let innerUpper := uniformGridStepBoundary blocks hblocks upper (-2 * ε)
  let outerLower := uniformGridStepBoundary blocks hblocks lower (-2 * ε)
  let outerUpper := uniformGridStepBoundary blocks hblocks upper (2 * ε)
  have hmeshL : 1 / (blocks : ℝ) < δL := hmesh.trans_le (min_le_left _ _)
  have hmeshU : 1 / (blocks : ℝ) < δU := hmesh.trans_le (min_le_right _ _)
  have hinward : ∀ t, (lower t : EReal) < innerLower.eval t ∧
      innerUpper.eval t < (upper t : EReal) := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [innerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [innerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (-2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : innerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) + 2 * ε : ℝ) : EReal) := by
      simpa [innerLower, iL, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (2 * ε) t
    have hevalU : innerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) - 2 * ε : ℝ) : EReal) := by
      simpa [innerUpper, iU, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (-2 * ε) t
    constructor
    · rw [hevalL]
      exact EReal.coe_lt_coe_iff.mpr (sample_lt_add_two_of_abs hε hsL)
    · rw [hevalU]
      exact EReal.coe_lt_coe_iff.mpr (sub_two_lt_sample_of_abs hε hsU)
  have houtward : ∀ t, outerLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < outerUpper.eval t := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [outerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [outerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (-2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : outerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) - 2 * ε : ℝ) : EReal) := by
      simpa [outerLower, iL, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (-2 * ε) t
    have hevalU : outerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) + 2 * ε : ℝ) : EReal) := by
      simpa [outerUpper, iU, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (2 * ε) t
    constructor
    · rw [hevalL]
      exact EReal.coe_lt_coe_iff.mpr (sub_two_lt_sample_of_abs hε hsL)
    · rw [hevalU]
      exact EReal.coe_lt_coe_iff.mpr (sample_lt_add_two_of_abs hε hsU)
  have hadmissible : HasContinuousAdmissiblePath innerUpper innerLower := by
    apply hasContinuousAdmissiblePath_of_witness innerUpper innerLower center
      hcenterZero
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [innerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [innerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (-2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : innerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) + 2 * ε : ℝ) : EReal) := by
      simpa [innerLower, iL, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (2 * ε) t
    have hevalU : innerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) - 2 * ε : ℝ) : EReal) := by
      simpa [innerUpper, iU, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (-2 * ε) t
    constructor
    · rw [hevalL]
      apply EReal.coe_lt_coe_iff.mpr
      have hfirst := (abs_lt.mp hsL).1
      calc
        lower (uniformGridTime blocks hblocks iL) + 2 * ε < lower t + 3 * ε := by linarith
        _ < lower t + margin := by linarith
        _ ≤ center t := (hcenter t).1
    · rw [hevalU]
      apply EReal.coe_lt_coe_iff.mpr
      have hsecond := (abs_lt.mp hsU).2
      have hcenterUpper : center t ≤ upper t - margin := by linarith [(hcenter t).2]
      calc
        center t ≤ upper t - margin := hcenterUpper
        _ < upper t - 3 * ε := by linarith
        _ < upper (uniformGridTime blocks hblocks iU) - 2 * ε := by linarith
  have hadmissibleOuter : HasContinuousAdmissiblePath outerUpper outerLower := by
    apply hasContinuousAdmissiblePath_of_witness outerUpper outerLower center hcenterZero
    intro t
    constructor
    · exact (houtward t).1.trans
        (EReal.coe_lt_coe_iff.mpr
          (lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) (hcenter t).1))
    · exact (EReal.coe_lt_coe_iff.mpr
        (lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) (hcenter t).2)).trans
        (houtward t).2
  exact ⟨hinward, houtward, hadmissible,
    hadmissibleOuter,
    relative_corridorSet_subset_relativeContinuousBoundaryCorridorSet
      innerUpper innerLower lower upper hinward,
    relativeContinuousBoundaryCorridorSet_subset_relative_corridorSet
      outerUpper outerLower lower upper houtward⟩

end Skorokhod.PathClass.StepCorridor

end
