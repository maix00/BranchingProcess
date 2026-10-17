/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceLower
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.Binning

/-!
# Spatial-bin coverage for the finite-variance tilted tube

The module-visible lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_staircaseBin_commonEvent_subset_centerWindow`:
  the same selection for every point in the middle endpoint window.

This is the bin-coverage step in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma
3.5. The horizontal-tube rate used with these bins is given in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, Lemma 3.1(ii).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube


/-- The bins in the staircase construction of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof
of Lemma 3.5, cover the full range of normalized relative starting
positions used there: for every $r/\Delta\in[-2/3,-1/3]$, there is
$0\le l<m$ with $b_l\le r/\Delta\le b_{l+1}$. -/
private lemma exists_staircaseBin_covering_relativeOffset
    {m : ℕ} (hm : 2 ≤ m) {offset : ℝ}
    (hoffsetLower : -(2 : ℝ) / 3 ≤ offset)
    (hoffsetUpper : offset ≤ -(1 : ℝ) / 3) :
    ∃ l : ℕ, l < m ∧ staircaseBinLower m l ≤ offset ∧
      offset ≤ staircaseBinUpper m l := by
  let scale : ℝ := 3 * (m : ℝ)
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  let x : ℝ := (offset + (2 : ℝ) / 3) * scale
  have hxLower : 0 ≤ x := by
    dsimp [x]
    apply mul_nonneg _ hscale.le
    linarith [hoffsetLower]
  have hxUpper : x ≤ (m : ℝ) := by
    calc
      x = (offset + (2 : ℝ) / 3) * scale := rfl
      _ ≤ ((1 : ℝ) / 3) * scale :=
        mul_le_mul_of_nonneg_right (by linarith [hoffsetUpper]) hscale.le
      _ = (m : ℝ) := by dsimp [scale]; ring
  let q : ℕ := ⌊x⌋₊
  have hqLower : (q : ℝ) ≤ x := by
    exact Nat.floor_le hxLower
  have hxFloor : x < (q : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  let l : ℕ := min q (m - 1)
  have hl : l < m := by
    dsimp [l]
    have hm' : m - 1 < m := by omega
    exact lt_of_le_of_lt (Nat.min_le_right _ _) hm'
  have hlLower : (l : ℝ) ≤ x := by
    dsimp [l]
    exact le_trans (by exact_mod_cast (Nat.min_le_left q (m - 1))) hqLower
  have hlUpper : x ≤ (l : ℝ) + 1 := by
    by_cases hq : q < m
    · have hlEq : l = q := by
        dsimp [l]
        apply Nat.min_eq_left
        omega
      rw [hlEq]
      exact le_of_lt hxFloor
    · have hmq : m ≤ q := by omega
      have hqle : (q : ℝ) ≤ (m : ℝ) := by
        exact le_trans hqLower hxUpper
      have hxeq : x = (m : ℝ) := by
        exact le_antisymm hxUpper (le_trans (by exact_mod_cast hmq : (m : ℝ) ≤ (q : ℝ)) hqLower)
      have hqeq : q = m := by
        exact_mod_cast (le_antisymm hqle (by exact_mod_cast hmq : (m : ℝ) ≤ (q : ℝ)))
      have hleq : l = m - 1 := by
        dsimp [l]
        rw [hqeq]
        exact Nat.min_eq_right (by omega)
      rw [hxeq, hleq]
      norm_cast
      omega
  have hoffsetForm : offset = -(2 : ℝ) / 3 + x / scale := by
    dsimp [x]
    field_simp [ne_of_gt hscale]
    ring
  have hscaleDivLower : (l : ℝ) / scale ≤ x / scale :=
    div_le_div_of_nonneg_right hlLower hscale.le
  have hscaleDivUpper : x / scale ≤ ((l + 1 : ℕ) : ℝ) / scale := by
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hlUpper
  refine ⟨l, hl, ?_, ?_⟩
  · change -(2 : ℝ) / 3 + (l : ℝ) / scale ≤ offset
    rw [hoffsetForm]
    linarith [hscaleDivLower]
  · change offset ≤ -(2 : ℝ) / 3 + (l : ℝ) / scale + 1 / scale
    rw [hoffsetForm]
    have hsuccessor : ((l + 1 : ℕ) : ℝ) / scale =
        (l : ℝ) / scale + 1 / scale := by
      push_cast
      ring
    linarith [hscaleDivUpper, hsuccessor]

/-- The central window $[r+D/3,r+2D/3]$ makes the relative lower edge
$r-y$ lie in $[-2D/3,-D/3]$, as used for each block in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of
Lemma 3.5. -/
private lemma relativeLowerEdge_mem_staircaseRange_of_centerWindow
    {width lowerEdge position : ℝ} (hwidth : 0 < width)
    (hposition : position ∈
      Set.Icc (lowerEdge + width / 3) (lowerEdge + 2 * width / 3)) :
    (lowerEdge - position) / width ∈
      Set.Icc (-(2 : ℝ) / 3) (-(1 : ℝ) / 3) := by
  rcases Set.mem_Icc.mp hposition with ⟨hpositionLower, hpositionUpper⟩
  rw [Set.mem_Icc]
  have hleft : (-(2 : ℝ) / 3) * width ≤ lowerEdge - position := by
    nlinarith [hpositionUpper]
  have hright : lowerEdge - position ≤ (-(1 : ℝ) / 3) * width := by
    nlinarith [hpositionLower]
  constructor
  · calc
      -(2 : ℝ) / 3 = ((-(2 : ℝ) / 3) * width) / width := by
        field_simp [ne_of_gt hwidth]
      _ ≤ (lowerEdge - position) / width :=
        (div_le_div_iff_of_pos_right hwidth).2 hleft
  · calc
      (lowerEdge - position) / width ≤
          ((-(1 : ℝ) / 3) * width) / width :=
        (div_le_div_iff_of_pos_right hwidth).2 hright
      _ = -(1 : ℝ) / 3 := by field_simp [ne_of_gt hwidth]

/-- For a starting offset in one spatial bin, the common narrowed-tube
event is contained in the desired horizontal tube and terminal window.
This is the deterministic bin-inclusion step in the staircase proof of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5. -/
private lemma horizontalTubeEndpointWindowEvent_subset_relativeHorizontalTubeEndpointWindowEvent
    {m l horizon : ℕ} {width v₁ v₂ lower : ℝ}
    (hm : 2 ≤ m)
    (hlower : staircaseBinLower m l * width ≤ lower)
    (hupper : lower ≤ staircaseBinUpper m l * width) :
    horizontalTubeEndpointWindowEvent
        (staircaseBinTubeParameter m l)
        (staircaseBinWidth m * width) horizon
        (staircaseBinEndpointLowerFraction m v₁)
        (staircaseBinEndpointUpperFraction m v₂) ⊆
      relativeHorizontalTubeEndpointWindowEvent lower width horizon v₁ v₂ := by
  have hbinWidth : 0 < staircaseBinWidth m := by
    dsimp [staircaseBinWidth]
    have hm' : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hdenom : 0 < 3 * (m : ℝ) := by positivity
    have hfrac : 1 / (3 * (m : ℝ)) < 1 := by
      rw [div_lt_one hdenom]
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith [hmR]
    linarith
  have hdelta : 1 / (3 * (m : ℝ)) + staircaseBinWidth m = 1 := by
    dsimp [staircaseBinWidth]
    ring
  have hbinAdjacent : staircaseBinUpper m l =
      staircaseBinLower m l + 1 / (3 * (m : ℝ)) := rfl
  have hparameterWidth :
      staircaseBinTubeParameter m l * staircaseBinWidth m =
        -staircaseBinUpper m l := by
    dsimp [staircaseBinTubeParameter]
    field_simp [ne_of_gt hbinWidth]
  have hnegativeParameterWidth :
      -staircaseBinTubeParameter m l * staircaseBinWidth m =
        staircaseBinUpper m l := by
    calc
      -staircaseBinTubeParameter m l * staircaseBinWidth m =
          -(staircaseBinTubeParameter m l *
            staircaseBinWidth m) := by ring
      _ = staircaseBinUpper m l := by rw [hparameterWidth]; ring
  have hpositiveParameterWidth :
      (1 - staircaseBinTubeParameter m l) * staircaseBinWidth m =
        staircaseBinWidth m + staircaseBinUpper m l := by
    calc
      (1 - staircaseBinTubeParameter m l) * staircaseBinWidth m =
          staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
      _ = staircaseBinWidth m + staircaseBinUpper m l := by
        rw [hparameterWidth]
        ring
  have hwidthDelta :
      staircaseBinWidth m + 1 / (3 * (m : ℝ)) = 1 := by
    rw [add_comm]
    exact hdelta
  have hleft :
      -staircaseBinTubeParameter m l *
          (staircaseBinWidth m * width) = staircaseBinUpper m l * width := by
    calc
      -staircaseBinTubeParameter m l *
          (staircaseBinWidth m * width) =
          (-staircaseBinTubeParameter m l *
            staircaseBinWidth m) * width := by ring
      _ = staircaseBinUpper m l * width := by rw [hnegativeParameterWidth]
  have hright :
      (1 - staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinLower m l + 1) * width := by
    calc
      (1 - staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((1 - staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (staircaseBinWidth m +
          staircaseBinUpper m l) * width := by rw [hpositiveParameterWidth]
      _ = (staircaseBinLower m l + 1) * width := by
        rw [hbinAdjacent]
        congr 1
        dsimp [staircaseBinWidth] at hdelta
        dsimp [staircaseBinWidth]
        linarith [hdelta]
  have hendpointLowerWidth :
      staircaseBinEndpointLowerFraction m v₁ *
          staircaseBinWidth m = v₁ := by
    dsimp [staircaseBinEndpointLowerFraction]
    field_simp [ne_of_gt hbinWidth]
  have hendpointUpperWidth :
      staircaseBinEndpointUpperFraction m v₂ *
          staircaseBinWidth m =
        v₂ - 1 / (3 * (m : ℝ)) := by
    dsimp [staircaseBinEndpointUpperFraction]
    field_simp [ne_of_gt hbinWidth]
  have hterminalLower :
      (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinUpper m l + v₁) * width := by
    have hwidthExpr :
        (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) * staircaseBinWidth m =
            v₁ + staircaseBinUpper m l := by
      calc
        _ = staircaseBinEndpointLowerFraction m v₁ *
              staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
        _ = v₁ + staircaseBinUpper m l := by
          rw [hendpointLowerWidth, hparameterWidth]
          ring
    calc
      (staircaseBinEndpointLowerFraction m v₁ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((staircaseBinEndpointLowerFraction m v₁ -
            staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (v₁ + staircaseBinUpper m l) * width := by rw [hwidthExpr]
      _ = (staircaseBinUpper m l + v₁) * width := by ring
  have hterminalUpper :
      (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
        (staircaseBinLower m l + v₂) * width := by
    have hwidthExpr :
        (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) * staircaseBinWidth m =
            staircaseBinLower m l + v₂ := by
      calc
        _ = staircaseBinEndpointUpperFraction m v₂ *
              staircaseBinWidth m -
            staircaseBinTubeParameter m l * staircaseBinWidth m := by ring
        _ = (v₂ - 1 / (3 * (m : ℝ))) +
              staircaseBinUpper m l := by
          rw [hendpointUpperWidth, hparameterWidth]
          ring
        _ = staircaseBinLower m l + v₂ := by rw [hbinAdjacent]; ring
    calc
      (staircaseBinEndpointUpperFraction m v₂ -
          staircaseBinTubeParameter m l) *
          (staircaseBinWidth m * width) =
          ((staircaseBinEndpointUpperFraction m v₂ -
            staircaseBinTubeParameter m l) *
            staircaseBinWidth m) * width := by ring
      _ = (staircaseBinLower m l + v₂) * width := by rw [hwidthExpr]
  intro increment hevent
  change InHorizontalTube (staircaseBinTubeParameter m l)
      (staircaseBinWidth m * width) horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc
        ((staircaseBinEndpointLowerFraction m v₁ -
            staircaseBinTubeParameter m l) *
            (staircaseBinWidth m * width))
        ((staircaseBinEndpointUpperFraction m v₂ -
            staircaseBinTubeParameter m l) *
            (staircaseBinWidth m * width)) at hevent
  rcases hevent with ⟨htube, hend⟩
  refine ⟨?_, ?_⟩
  · intro k
    have hk := htube k
    rw [hleft, hright] at hk
    constructor
    · exact le_trans hupper hk.1
    · have htop : (staircaseBinLower m l + 1) * width ≤ lower + width := by
        have hrewrite : (staircaseBinLower m l + 1) * width =
            staircaseBinLower m l * width + width := by ring
        rw [hrewrite]
        linarith [hlower]
      exact le_trans hk.2 htop
  · rw [hterminalLower, hterminalUpper] at hend
    rcases Set.mem_Icc.mp hend with ⟨hendLower, hendUpper⟩
    rw [Set.mem_Icc]
    constructor
    · nlinarith [hupper, hendLower]
    · nlinarith [hlower, hendUpper]

/-- For every positive tube width and every relative lower edge in
$[-2/3,-1/3]$, one of the staircase bins supplies a common narrowed-tube
event contained in the target tube and endpoint window. This packages the
bin selection and event inclusion used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. -/
private lemma exists_staircaseBin_commonEvent_subset_relativeTube
    {m horizon : ℕ} {width v₁ v₂ lower : ℝ}
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hrelativeLower : -(2 : ℝ) / 3 ≤ lower / width)
    (hrelativeUpper : lower / width ≤ -(1 : ℝ) / 3) :
    ∃ l : ℕ, l < m ∧
      horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width) horizon
          (staircaseBinEndpointLowerFraction m v₁)
          (staircaseBinEndpointUpperFraction m v₂) ⊆
        relativeHorizontalTubeEndpointWindowEvent lower width horizon v₁ v₂ := by
  obtain ⟨l, hl, hbinLower, hbinUpper⟩ :=
    exists_staircaseBin_covering_relativeOffset hm hrelativeLower hrelativeUpper
  have hlower : staircaseBinLower m l * width ≤ lower := by
    calc
      staircaseBinLower m l * width ≤ (lower / width) * width :=
        mul_le_mul_of_nonneg_right hbinLower hwidth.le
      _ = lower := by field_simp [ne_of_gt hwidth]
  have hupper : lower ≤ staircaseBinUpper m l * width := by
    calc
      lower = (lower / width) * width := by field_simp [ne_of_gt hwidth]
      _ ≤ staircaseBinUpper m l * width :=
        mul_le_mul_of_nonneg_right hbinUpper hwidth.le
  exact ⟨l, hl,
    horizontalTubeEndpointWindowEvent_subset_relativeHorizontalTubeEndpointWindowEvent
      hm hlower hupper⟩

/-- At every point of the central window used in the staircase proof, a
common narrowed-tube event is contained in the corresponding target event.
This combines the central-window geometry with the bin selection in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. -/
lemma exists_staircaseBin_commonEvent_subset_centerWindow
    {m horizon : ℕ} {width v₁ v₂ lowerEdge position : ℝ}
    (hm : 2 ≤ m) (hwidth : 0 < width)
    (hposition : position ∈
      Set.Icc (lowerEdge + width / 3) (lowerEdge + 2 * width / 3)) :
    ∃ l : ℕ, l < m ∧
      horizontalTubeEndpointWindowEvent
          (staircaseBinTubeParameter m l)
          (staircaseBinWidth m * width) horizon
          (staircaseBinEndpointLowerFraction m v₁)
          (staircaseBinEndpointUpperFraction m v₂) ⊆
        relativeHorizontalTubeEndpointWindowEvent
          (lowerEdge - position) width horizon v₁ v₂ := by
  have hrelative := relativeLowerEdge_mem_staircaseRange_of_centerWindow
    hwidth hposition
  exact exists_staircaseBin_commonEvent_subset_relativeTube hm hwidth
    hrelative.1 hrelative.2

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
