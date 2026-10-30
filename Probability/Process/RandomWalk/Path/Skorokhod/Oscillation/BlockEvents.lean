/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Probability.Process.RandomWalk.Path.Block.Law.TwoExcursions
public import Probability.Process.RandomWalk.Path.Representation.Cadlag
public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion.Basic

/-!
# Block-event consequences of normalized-path oscillations

This module translates violations of the double-excursion and endpoint
oscillation bounds for a normalized step path into finite-block events of its
underlying increments. These path-to-increment bounds are the interface used
by the block probability estimates.

## Public declarations

* `normalizedStepCadlagPathIcc_not_hasDoubleExcursionBound_subset_windowGrid`
  contains every path violating the double-excursion bound in a union of
  two-ordered-block-excursion events, with threshold `ε * scale n`.
* `normalizedStepCadlagPathIcc_not_hasEndpointOscillationBound_subset_boundaryBlocks`
  contains every path violating endpoint oscillation control in the union of
  the first and last block-prefix exceedance events, each with threshold
  `ε * scale n / 2`.
-/

open Skorokhod

@[expose] public section

namespace ProbabilityTheory.RandomWalk

private lemma existsNatAnchorForWindow {n width i l : ℕ}
    (hwidth : 0 < width) (hi : i < n) (hil : i ≤ l)
    (hspan : l - i ≤ width) :
    ∃ j : ℕ, j < n / width + 1 ∧ j * width ≤ i ∧
      i < j * width + width ∧ l < j * width + 2 * width := by
  let j := i / width
  have hmod : i % width < width := Nat.mod_lt i hwidth
  have hdecomp : i % width + j * width = i := by
    dsimp [j]
    simpa [Nat.mul_comm] using Nat.mod_add_div i width
  have hdiv : j ≤ n / width := by
    dsimp [j]
    exact Nat.div_le_div_right hi.le
  refine ⟨j, by omega, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Distance between two values of a normalized step path, expressed as the
scaled absolute difference of the corresponding partial sums. -/
theorem normalizedStepCadlagPathIcc_dist_eq
    (scale : ℕ → ℝ) (n : ℕ) (hscale : 0 < scale n)
    (increment : ℕ → ℝ) (s t : unitInterval) :
    dist (normalizedStepCadlagPathIcc scale n increment s)
        (normalizedStepCadlagPathIcc scale n increment t) =
      (scale n)⁻¹ *
        |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
          AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| := by
  rw [normalizedStepCadlagPathIcc_apply, normalizedStepPath,
    normalizedStepCadlagPathIcc_apply, normalizedStepPath, Real.dist_eq,
    ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hscale)]

/-- A strict excursion of the normalized path yields the corresponding raw
partial-sum excursion after multiplying by the positive spatial scale. -/
theorem normalizedStepCadlagPathIcc_dist_lt_implies_raw
    (scale : ℕ → ℝ) (n : ℕ) (hscale : 0 < scale n)
    (increment : ℕ → ℝ) (ε : ℝ) (s t : unitInterval)
    (hdist : ε < dist (normalizedStepCadlagPathIcc scale n increment s)
      (normalizedStepCadlagPathIcc scale n increment t)) :
    ε * scale n ≤
      |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
        AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| := by
  rw [normalizedStepCadlagPathIcc_dist_eq scale n hscale increment s t] at hdist
  have hdiv : ε <
      |AdditivePath.displacement ⌊(n : ℝ) * s⌋₊ increment -
        AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment| / scale n := by
    simpa [div_eq_mul_inv, mul_comm] using hdist
  exact le_of_lt ((lt_div_iff₀ hscale).mp hdiv)

/-- If a normalized random-walk path violates Billingsley's double-excursion
bound on a time interval shorter than `δ`, then two ordered large block
excursions occur in one member of the deterministic grid of windows of
length `width`. The window starts are integer multiples of `width`; this is
the path-to-increment bridge used by the probabilistic block estimates. -/
theorem normalizedStepCadlagPathIcc_not_hasDoubleExcursionBound_subset_windowGrid
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hscale : 0 < scale n)
    (δ ε : ℝ)
    (width : ℕ) (hwidth : 0 < width)
    (hwidthLower : (n : ℝ) * δ ≤ width)
    (increment : ℕ → ℝ)
    (hbad : ¬ Skorokhod.HasDoubleExcursionBound
      (normalizedStepCadlagPathIcc scale n increment) δ ε) :
    increment ∈ ⋃ j : Fin (n / width + 1),
      twoOrderedBlockExcursions (j.val * width) (2 * width)
        (ε * scale n) := by
  classical
  have hbad' := hbad
  simp only [Skorokhod.HasDoubleExcursionBound, not_forall, not_le] at hbad'
  rcases hbad' with ⟨s, t, u, hst, htu, huTop, hsu, x, y, z, w,
    hsx, hxy, hyt, htz, hzw, hwu, hmin⟩
  have hfirst : ε < dist
      (normalizedStepCadlagPathIcc scale n increment x)
      (normalizedStepCadlagPathIcc scale n increment y) := by
    exact lt_of_lt_of_le hmin (min_le_left _ _)
  have hsecond : ε < dist
      (normalizedStepCadlagPathIcc scale n increment z)
      (normalizedStepCadlagPathIcc scale n increment w) := by
    exact lt_of_lt_of_le hmin (min_le_right _ _)
  have hsuVal : (s : ℝ) < (u : ℝ) := by
    exact_mod_cast lt_trans hst htu
  have hsuReal : (u : ℝ) - (s : ℝ) < δ := by
    have hdist : |(s : ℝ) - (u : ℝ)| < δ := by
      simpa [Subtype.dist_eq, Real.dist_eq] using hsu
    rw [abs_of_nonpos (sub_nonpos.mpr hsuVal.le)] at hdist
    linarith
  have hxw : (x : ℝ) ≤ (w : ℝ) := by
    have hxw' : x ≤ w := le_trans hxy (le_trans hyt (le_trans htz hzw))
    exact_mod_cast hxw'
  have htimespan : (w : ℝ) - (x : ℝ) < δ := by
    have hsx' : (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hsx
    have hwu' : (w : ℝ) ≤ (u : ℝ) := by exact_mod_cast hwu
    linarith
  let i : ℕ := ⌊(n : ℝ) * (x : ℝ)⌋₊
  let j : ℕ := ⌊(n : ℝ) * (y : ℝ)⌋₊
  let k : ℕ := ⌊(n : ℝ) * (z : ℝ)⌋₊
  let l : ℕ := ⌊(n : ℝ) * (w : ℝ)⌋₊
  have htimeWidth : (n : ℝ) * ((w : ℝ) - (x : ℝ)) < width := by
    have hmul : (n : ℝ) * ((w : ℝ) - (x : ℝ)) <
        (n : ℝ) * δ := by gcongr
    exact lt_of_lt_of_le hmul hwidthLower
  have htimeWidth' : (n : ℝ) * (w : ℝ) - (n : ℝ) * (x : ℝ) < width := by
    nlinarith [htimeWidth]
  have hiNonneg : 0 ≤ (n : ℝ) * (x : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) x.property.1
  have hlNonneg : 0 ≤ (n : ℝ) * (w : ℝ) :=
    mul_nonneg (Nat.cast_nonneg n) w.property.1
  have hiFloorUpper : (n : ℝ) * (x : ℝ) < (i : ℝ) + 1 := by
    simpa [i] using Nat.lt_floor_add_one ((n : ℝ) * (x : ℝ))
  have hlFloorLower : (l : ℝ) ≤ (n : ℝ) * (w : ℝ) := by
    simpa [l] using Nat.floor_le hlNonneg
  have hspanNat : l - i ≤ width := by
    have hspanReal : (l : ℝ) < (i : ℝ) + (width : ℝ) + 1 := by
      dsimp [i] at hiFloorUpper
      dsimp [l] at hlFloorLower
      linarith
    have hspanCast : l < i + width + 1 := by exact_mod_cast hspanReal
    omega
  have hfloorOrder : i ≤ l := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left hxw (Nat.cast_nonneg n)
  have hlLtN : l < n := by
    have hwne : w ≠ ⊤ := by
      intro h
      subst w
      exact huTop (le_antisymm hwu le_top).symm
    have hwltOne : (w : ℝ) < 1 := by
      by_contra hnot
      have heq : (w : ℝ) = 1 := le_antisymm w.property.2
        (le_of_not_gt hnot)
      exact hwne (Subtype.ext heq)
    have hlReal : (l : ℝ) ≤ (n : ℝ) * (w : ℝ) := hlFloorLower
    have hmulPos : 0 < (n : ℝ) * (1 - (w : ℝ)) :=
      mul_pos (by exact_mod_cast hn) (by linarith)
    have hltReal : (l : ℝ) < n := by nlinarith [hlReal, hmulPos]
    exact_mod_cast hltReal
  have hiLtN : i < n := lt_of_le_of_lt hfloorOrder hlLtN
  have hindices : i ≤ j ∧ j ≤ k ∧ k ≤ l := by
    refine ⟨?_, ?_, ?_⟩
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (x : ℝ) ≤ (y : ℝ) by exact_mod_cast hxy)
        (Nat.cast_nonneg n)
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (y : ℝ) ≤ (z : ℝ) by
        exact_mod_cast le_trans hyt htz) (Nat.cast_nonneg n)
    · apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left (show (z : ℝ) ≤ (w : ℝ) by exact_mod_cast hzw)
        (Nat.cast_nonneg n)
  obtain ⟨anchor, hanchorLt, hanchorLe, hiUpper, hlUpper⟩ :=
    existsNatAnchorForWindow hwidth hiLtN hfloorOrder hspanNat
  let localI := i - anchor * width
  let localJ := j - anchor * width
  let localK := k - anchor * width
  let localL := l - anchor * width
  have hlocalOrder : localI ≤ localJ ∧ localJ ≤ localK ∧
      localK ≤ localL ∧ localL ≤ 2 * width := by
    dsimp [localI, localJ, localK, localL]
    omega
  let anchorIndex : Fin (n / width + 1) := ⟨anchor, hanchorLt⟩
  have hvalueDist (a b : unitInterval) (ia ib : ℕ)
      (hia : ia = ⌊(n : ℝ) * (a : ℝ)⌋₊)
      (hib : ib = ⌊(n : ℝ) * (b : ℝ)⌋₊) :
      ε < dist (normalizedStepCadlagPathIcc scale n increment a)
          (normalizedStepCadlagPathIcc scale n increment b) →
        ε * scale n ≤
          |AdditivePath.displacement ib increment -
            AdditivePath.displacement ia increment| := by
    intro hdist
    rw [normalizedStepCadlagPathIcc_dist_eq scale n hscale increment a b,
      ← hia, ← hib] at hdist
    have hdiv : ε <
        |AdditivePath.displacement ib increment -
          AdditivePath.displacement ia increment| / scale n := by
      simpa [div_eq_mul_inv, mul_comm, abs_sub_comm] using hdist
    exact (le_of_lt ((lt_div_iff₀ hscale).mp hdiv))
  have hrawFirst := hvalueDist x y i j rfl rfl hfirst
  have hrawSecond := hvalueDist z w k l rfl rfl hsecond
  have hshiftI := AdditivePath.displacement_natAdd_eq_sub increment
    (show anchor * width ≤ i by omega)
  have hshiftJ := AdditivePath.displacement_natAdd_eq_sub increment
    (show anchor * width ≤ j by omega)
  have hshiftK := AdditivePath.displacement_natAdd_eq_sub increment
    (show anchor * width ≤ k by omega)
  have hshiftL := AdditivePath.displacement_natAdd_eq_sub increment
    (show anchor * width ≤ l by omega)
  have hrawLocalFirst : ε * scale n ≤
      |AdditivePath.displacement localJ
          (fun m => increment (anchor * width + m)) -
        AdditivePath.displacement localI
          (fun m => increment (anchor * width + m))| := by
    rw [hshiftJ, hshiftI]
    have habs :
        |(AdditivePath.displacement j increment -
            AdditivePath.displacement (anchor * width) increment) -
          (AdditivePath.displacement i increment -
            AdditivePath.displacement (anchor * width) increment)| =
          |AdditivePath.displacement j increment -
            AdditivePath.displacement i increment| := by congr 1; ring
    rw [habs]
    exact hrawFirst
  have hrawLocalSecond : ε * scale n ≤
      |AdditivePath.displacement localL
          (fun m => increment (anchor * width + m)) -
        AdditivePath.displacement localK
          (fun m => increment (anchor * width + m))| := by
    rw [hshiftL, hshiftK]
    have habs :
        |(AdditivePath.displacement l increment -
            AdditivePath.displacement (anchor * width) increment) -
          (AdditivePath.displacement k increment -
            AdditivePath.displacement (anchor * width) increment)| =
          |AdditivePath.displacement l increment -
            AdditivePath.displacement k increment| := by congr 1; ring
    rw [habs]
    exact hrawSecond
  have hlocalEvent :
      (fun m => increment (anchor * width + m)) ∈
        twoOrderedPrefixExcursions (2 * width) (ε * scale n) := by
    refine ⟨localI, localJ, localK, localL,
      hlocalOrder.1, hlocalOrder.2.1, hlocalOrder.2.2.1,
      hlocalOrder.2.2.2, hrawLocalFirst, hrawLocalSecond⟩
  have hgridEvent : increment ∈
      twoOrderedBlockExcursions (anchor * width) (2 * width)
        (ε * scale n) := hlocalEvent
  exact Set.mem_iUnion.mpr ⟨anchorIndex, by simpa [anchorIndex] using hgridEvent⟩

private lemma split_abs_sub_at_half {a x y : ℝ}
    (hlarge : 2 * a ≤ |x - y|) : a ≤ |x| ∨ a ≤ |y| := by
  by_contra h
  push Not at h
  have htriangle : |x - y| ≤ |x| + |y| := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [le_abs_self x, neg_le_abs x,
      le_abs_self y, neg_le_abs y]
  linarith

/-- Failure of endpoint oscillation control for a normalized step path is
contained in the union of a first-window and a last-window prefix excursion.
The endpoint windows are handled in the general càdlàg layer; this theorem
only translates them to the underlying increments. -/
theorem normalizedStepCadlagPathIcc_not_hasEndpointOscillationBound_subset_boundaryBlocks
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hscale : 0 < scale n)
    (δ ε : ℝ) (hε : 0 < ε) (width : ℕ)
    (hwidthLower : (n : ℝ) * δ ≤ width)
    (increment : ℕ → ℝ)
    (hbad : ¬ Skorokhod.HasEndpointOscillationBound
      (normalizedStepCadlagPathIcc scale n increment) δ ε) :
    increment ∈ blockPrefixExceedance 0 width (ε * scale n / 2) ∪
      blockPrefixExceedance (n - width) width (ε * scale n / 2) := by
  classical
  have hbad' := hbad
  simp only [Skorokhod.HasEndpointOscillationBound, not_and_or] at hbad'
  have hthreshold : 0 < ε * scale n / 2 := by positivity
  rcases hbad' with hleft | hright
  · push Not at hleft
    rcases hleft with ⟨s, t, hs, ht, hdist⟩
    let i : ℕ := ⌊(n : ℝ) * s⌋₊
    let j : ℕ := ⌊(n : ℝ) * t⌋₊
    have hraw := normalizedStepCadlagPathIcc_dist_lt_implies_raw
      scale n hscale increment ε s t hdist
    have hlarge : 2 * (ε * scale n / 2) ≤
        |AdditivePath.displacement i increment -
          AdditivePath.displacement j increment| := by
      nlinarith [hraw]
    have hsplit := split_abs_sub_at_half hlarge
    have htimeI : (n : ℝ) * s < width := by
      have hmul : (n : ℝ) * s < (n : ℝ) * δ := by gcongr
      exact lt_of_lt_of_le hmul hwidthLower
    have htimeJ : (n : ℝ) * t < width := by
      have hmul : (n : ℝ) * t < (n : ℝ) * δ := by gcongr
      exact lt_of_lt_of_le hmul hwidthLower
    have hiLt : i < width := by
      have hiReal : (i : ℝ) ≤ (n : ℝ) * s := by
        dsimp [i]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) s.property.1)
      have : (i : ℝ) < width := lt_of_le_of_lt hiReal htimeI
      exact_mod_cast this
    have hjLt : j < width := by
      have hjReal : (j : ℝ) ≤ (n : ℝ) * t := by
        dsimp [j]
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) t.property.1)
      have : (j : ℝ) < width := lt_of_le_of_lt hjReal htimeJ
      exact_mod_cast this
    rcases hsplit with hi | hj
    · exact Or.inl <| blockPrefixExceedance_of_displacementDifference
        increment (start := 0) (finish := i) (length := width)
        hthreshold (by omega) (by omega) (by simpa [i, AdditivePath.displacement_zero] using hi)
    · exact Or.inl <| blockPrefixExceedance_of_displacementDifference
        increment (start := 0) (finish := j) (length := width)
        hthreshold (by omega) (by omega) (by simpa [j, AdditivePath.displacement_zero] using hj)
  · push Not at hright
    rcases hright with ⟨s, t, hsne, htne, hs, ht, hdist⟩
    let anchor : ℕ := n - width
    let i : ℕ := ⌊(n : ℝ) * s⌋₊
    let j : ℕ := ⌊(n : ℝ) * t⌋₊
    have hraw := normalizedStepCadlagPathIcc_dist_lt_implies_raw
      scale n hscale increment ε s t hdist
    have hiNonneg : 0 ≤ (n : ℝ) * s := mul_nonneg (Nat.cast_nonneg n) s.property.1
    have hjNonneg : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) t.property.1
    have hanchorReal : (anchor : ℝ) ≤ (n : ℝ) * s := by
      by_cases hwidthn : width ≤ n
      · have hcast : (anchor : ℝ) = (n : ℝ) - width := by
          simp [anchor, Nat.cast_sub hwidthn]
        rw [hcast]
        have hmul : (n : ℝ) * (1 - δ) < (n : ℝ) * s := by gcongr
        nlinarith [hwidthLower]
      · have hzero : anchor = 0 := by
          have hle : n ≤ width := by omega
          simp [anchor, Nat.sub_eq_zero_of_le hle]
        simpa [hzero] using hiNonneg
    have hiAnchor : anchor ≤ i := by
      rw [Nat.le_floor_iff hiNonneg]
      exact hanchorReal
    have hjanchorReal : (anchor : ℝ) ≤ (n : ℝ) * t := by
      by_cases hwidthn : width ≤ n
      · have hcast : (anchor : ℝ) = (n : ℝ) - width := by
          simp [anchor, Nat.cast_sub hwidthn]
        rw [hcast]
        have hmul : (n : ℝ) * (1 - δ) < (n : ℝ) * t := by gcongr
        nlinarith [hwidthLower]
      · have hzero : anchor = 0 := by
          have hle : n ≤ width := by omega
          simp [anchor, Nat.sub_eq_zero_of_le hle]
        simpa [hzero] using hjNonneg
    have hjAnchor : anchor ≤ j := by
      rw [Nat.le_floor_iff hjNonneg]
      exact hjanchorReal
    have hiLeN : i ≤ n := by
      have htime : (n : ℝ) * s ≤ (n : ℝ) := by
        calc
          (n : ℝ) * s ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left s.property.2 (Nat.cast_nonneg n)
          _ = (n : ℝ) := by ring
      exact Nat.floor_le_of_le htime
    have hjLeN : j ≤ n := by
      have htime : (n : ℝ) * t ≤ (n : ℝ) := by
        calc
          (n : ℝ) * t ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
          _ = (n : ℝ) := by ring
      exact Nat.floor_le_of_le htime
    have hilength : i - anchor ≤ width := by
      dsimp [anchor]
      omega
    have hjlength : j - anchor ≤ width := by
      dsimp [anchor]
      omega
    have hlarge : 2 * (ε * scale n / 2) ≤
        |(AdditivePath.displacement i increment -
            AdditivePath.displacement anchor increment) -
          (AdditivePath.displacement j increment -
            AdditivePath.displacement anchor increment)| := by
      have hiden :
          (AdditivePath.displacement i increment -
              AdditivePath.displacement anchor increment) -
            (AdditivePath.displacement j increment -
              AdditivePath.displacement anchor increment) =
            AdditivePath.displacement i increment - AdditivePath.displacement j increment := by
        ring
      rw [hiden]
      nlinarith [hraw]
    rcases split_abs_sub_at_half hlarge with hi | hj
    · exact Or.inr <| blockPrefixExceedance_of_displacementDifference
        increment (start := anchor) (finish := i) (length := width)
        hthreshold (by omega) hilength hi
    · exact Or.inr <| blockPrefixExceedance_of_displacementDifference
        increment (start := anchor) (finish := j) (length := width)
        hthreshold (by omega) hjlength hj

end ProbabilityTheory.RandomWalk

end
