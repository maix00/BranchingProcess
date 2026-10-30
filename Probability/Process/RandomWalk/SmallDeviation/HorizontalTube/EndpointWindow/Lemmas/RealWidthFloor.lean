/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Algebra.Order.Floor.Semifield
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic

/-!
# Integer-width approximation for endpoint-window events

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins`: an integer-width tube at width $\lfloor D\rfloor$ is contained in a real-width tube at width $D$ when the outer endpoint interval has a margin at least $1/D$. This is the geometric step used to transfer the integer-width finite-variance estimate to real widths.
-/

open ProbabilityTheory.RandomWalk

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- An integer-width horizontal tube at width $\lfloor D\rfloor$ is
contained in the real-width tube at width $D$. If the endpoint window
$[u,v]$ has margin $\gamma$ inside $[U,V]$ and $D\ge1/\gamma$, its absolute
endpoint interval is contained as well. This lets the integer-width form of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii), supply block estimates at the real
widths in the proof of Lemma 3.5. -/
lemma horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins
    {horizon : ℕ} {a u v U V margin width : ℝ}
    (hwidth : 0 ≤ width) (haLower : 0 ≤ a) (haUpper : a ≤ 1)
    (huLower : 0 ≤ u) (huv : u ≤ v) (hvUpper : v ≤ 1)
    (hmargin : 0 < margin) (hwidthLarge : 1 / margin ≤ width)
    (hmarginLower : U + margin ≤ u)
    (hmarginUpper : v + margin ≤ V) :
    horizontalTubeEndpointWindowEvent a (⌊width⌋₊ : ℝ) horizon u v ⊆
      horizontalTubeEndpointWindowEvent a width horizon U V := by
  let integerWidth : ℝ := (⌊width⌋₊ : ℝ)
  have hfloorLower : integerWidth ≤ width := by
    exact Nat.floor_le hwidth
  have hgapLower : 0 ≤ width - integerWidth := sub_nonneg.mpr hfloorLower
  have hgapUpper : width - integerWidth ≤ 1 := by
    have hfloorUpper : width < integerWidth + 1 := by
      exact Nat.lt_floor_add_one width
    linarith
  have hmarginScale : 1 ≤ margin * width := by
    simpa [mul_comm] using (div_le_iff₀ hmargin).1 hwidthLarge
  have hendpointLower : (U - a) * width ≤ (u - a) * integerWidth := by
    have hmarginCoeff : margin ≤ u - U := by linarith [hmarginLower]
    have hmarginProduct : margin * width ≤ (u - U) * width :=
      mul_le_mul_of_nonneg_right hmarginCoeff hwidth
    have hrounding : (u - a) * (width - integerWidth) ≤ 1 := by
      calc
        (u - a) * (width - integerWidth) ≤
            1 * (width - integerWidth) :=
          mul_le_mul_of_nonneg_right
            (show u - a ≤ (1 : ℝ) by linarith [huv, hvUpper, haLower])
            hgapLower
        _ = width - integerWidth := by ring
        _ ≤ 1 := hgapUpper
    have hidentity : (u - a) * integerWidth - (U - a) * width =
        (u - U) * width - (u - a) * (width - integerWidth) := by ring
    rw [← sub_nonneg]
    rw [hidentity]
    linarith
  have hendpointUpper : (v - a) * integerWidth ≤ (V - a) * width := by
    have hmarginCoeff : margin ≤ V - v := by linarith [hmarginUpper]
    have hmarginProduct : margin * width ≤ (V - v) * width :=
      mul_le_mul_of_nonneg_right hmarginCoeff hwidth
    have hrounding : -1 ≤ (v - a) * (width - integerWidth) := by
      calc
        -1 ≤ -(width - integerWidth) := by linarith [hgapUpper]
        _ = (-1) * (width - integerWidth) := by ring
        _ ≤ (v - a) * (width - integerWidth) :=
          mul_le_mul_of_nonneg_right
            (show (-1 : ℝ) ≤ v - a by linarith [huLower, haUpper])
            hgapLower
    have hidentity : (V - a) * width - (v - a) * integerWidth =
        (V - v) * width + (v - a) * (width - integerWidth) := by ring
    rw [← sub_nonneg]
    rw [hidentity]
    linarith
  have htubeLower : -a * width ≤ -a * integerWidth := by
    calc
      -a * width = -(a * width) := by ring
      _ ≤ -(a * integerWidth) := neg_le_neg
        (mul_le_mul_of_nonneg_left hfloorLower haLower)
      _ = -a * integerWidth := by ring
  have htubeUpper : (1 - a) * integerWidth ≤ (1 - a) * width :=
    mul_le_mul_of_nonneg_left hfloorLower (by linarith [haUpper])
  intro increment hevent
  change InHorizontalTube a integerWidth horizon increment ∧
      AdditivePath.displacement horizon increment ∈
        Set.Icc ((u - a) * integerWidth) ((v - a) * integerWidth) at hevent
  rcases hevent with ⟨htube, hend⟩
  refine ⟨?_, ?_⟩
  · intro k
    rcases htube k with ⟨hleft, hright⟩
    exact ⟨htubeLower.trans hleft, hright.trans htubeUpper⟩
  · rcases Set.mem_Icc.mp hend with ⟨hleft, hright⟩
    rw [Set.mem_Icc]
    exact ⟨hendpointLower.trans hleft, hright.trans hendpointUpper⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
