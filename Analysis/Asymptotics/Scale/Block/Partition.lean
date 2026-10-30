/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Sequence.BalancedPartition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat
import Analysis.Asymptotics.Scale.Block.Length

/-!
# Asymptotics of balanced block partitions

## Public declarations

- `Asymptotics.tendsto_balancedBlockShortLength_div_referenceLength` and
  `Asymptotics.tendsto_balancedBlockLongLength_div_referenceLength`: if the
  reference length and the number of reference blocks diverge, each of the
  two possible balanced lengths is asymptotic to the reference length.
- `Asymptotics.tendsto_balancedBlockPartition_of_vanishingReference`:
  a positive-density horizon split by a divergent sublinear reference length
  has a diverging block count, while both possible lengths preserve the
  reference and clock scales.

The finite balanced-list construction and its exact sum and length statements
are owned by `Combinatorics.Sequence.BalancedPartition`.
-/

@[expose] public section

open Filter Topology Combinatorics.Sequence

namespace Asymptotics

theorem tendsto_balancedBlockShortLength_div_referenceLength
    {total referenceLength : ℕ → ℕ}
    (href : Tendsto (fun n => (referenceLength n : ℝ)) atTop atTop)
    (hcount : Tendsto
      (fun n => (balancedBlockCount (total n) (referenceLength n) : ℝ))
      atTop atTop) :
    Tendsto
      (fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ)) atTop (nhds 1) := by
  let q : ℕ → ℕ := fun n => balancedBlockCount (total n) (referenceLength n)
  let r : ℕ → ℕ := fun n => total n % referenceLength n
  let extra : ℕ → ℕ := fun n => r n / q n
  let error : ℕ → ℝ := fun n => (extra n : ℝ) / (referenceLength n : ℝ)
  have hqPos : ∀ᶠ n in atTop, 0 < q n := by
    filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with n hn
    exact_mod_cast hn
  have hrefPos : ∀ᶠ n in atTop, 0 < referenceLength n := by
    filter_upwards [href.eventually (eventually_gt_atTop 0)] with n hn
    exact_mod_cast hn
  have herrorNonneg : ∀ᶠ n in atTop, 0 ≤ error n := by
    filter_upwards [hrefPos] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have herrorBound : ∀ᶠ n in atTop, error n ≤ 1 / (q n : ℝ) := by
    filter_upwards [hqPos, hrefPos] with n hq hn
    have hqR : 0 < (q n : ℝ) := by exact_mod_cast hq
    have hrefR : 0 < (referenceLength n : ℝ) := by exact_mod_cast hn
    have hr : r n ≤ referenceLength n := by
      dsimp [r]
      exact Nat.le_of_lt (Nat.mod_lt _ hn)
    have hcast : (extra n : ℝ) ≤ (r n : ℝ) / (q n : ℝ) := by
      dsimp [extra]
      exact Nat.cast_div_le
    have hquot : (r n : ℝ) / (q n : ℝ) ≤
        (referenceLength n : ℝ) / (q n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hr)
        (Nat.cast_nonneg (q n))
    calc
      error n ≤ ((r n : ℝ) / (q n : ℝ)) / (referenceLength n : ℝ) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      _ ≤ ((referenceLength n : ℝ) / (q n : ℝ)) /
          (referenceLength n : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hquot
          (inv_nonneg.mpr hrefR.le)
        simpa [div_eq_mul_inv] using hmul
      _ = 1 / (q n : ℝ) := by field_simp [hqR.ne', hrefR.ne']
  have hqTop : Tendsto (fun n => (q n : ℝ)) atTop atTop := by
    simpa [q] using hcount
  have hinv : Tendsto (fun n => 1 / (q n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp hqTop)
  have herror : Tendsto error atTop (nhds 0) :=
    squeeze_zero' herrorNonneg herrorBound hinv
  have heq : (fun n =>
      (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ)) =ᶠ[atTop] fun n => 1 + error n := by
    filter_upwards [hrefPos] with n hn
    have hshort : balancedBlockShortLength (total n) (referenceLength n) =
        referenceLength n + extra n := by
      rfl
    rw [hshort]
    dsimp [error]
    rw [Nat.cast_add]
    field_simp [show (referenceLength n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  have hsum : Tendsto (fun n => (1 : ℝ) + error n) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add herror
  exact hsum.congr' heq.symm

/-- The longer balanced length is also asymptotic to the reference length. -/
theorem tendsto_balancedBlockLongLength_div_referenceLength
    {total referenceLength : ℕ → ℕ}
    (href : Tendsto (fun n => (referenceLength n : ℝ)) atTop atTop)
    (hcount : Tendsto
      (fun n => (balancedBlockCount (total n) (referenceLength n) : ℝ))
      atTop atTop) :
    Tendsto
      (fun n => ((balancedBlockShortLength (total n) (referenceLength n) + 1 : ℕ) : ℝ) /
        (referenceLength n : ℝ)) atTop (nhds 1) := by
  have hshort := tendsto_balancedBlockShortLength_div_referenceLength href hcount
  have hrefInv : Tendsto (fun n => (referenceLength n : ℝ)⁻¹)
      atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp href
  have hsum : Tendsto
      (fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ) + (referenceLength n : ℝ)⁻¹)
      atTop (nhds 1) := by
    simpa using hshort.add hrefInv
  have heq : (fun n =>
      ((balancedBlockShortLength (total n) (referenceLength n) + 1 : ℕ) : ℝ) /
        (referenceLength n : ℝ)) =ᶠ[atTop]
      fun n => (balancedBlockShortLength (total n) (referenceLength n) : ℝ) /
        (referenceLength n : ℝ) + (referenceLength n : ℝ)⁻¹ := by
    filter_upwards [] with n
    rw [Nat.cast_add, Nat.cast_one]
    ring
  exact hsum.congr' heq.symm

/-- A positive-density horizon split into balanced blocks of vanishing
relative reference length has many blocks, and both possible block lengths
retain the reference scale. -/
theorem tendsto_balancedBlockPartition_of_vanishingReference
    {total reference : ℕ → ℕ} {duration clockLimit : ℝ}
    {clock : ℕ → ℝ}
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ)) atTop
      (nhds duration))
    (hduration : 0 < duration)
    (hreference : Tendsto reference atTop atTop)
    (hreferenceDensity : Tendsto
      (fun n => (reference n : ℝ) / (n : ℝ)) atTop (nhds 0))
    (hclockPos : ∀ᶠ n in atTop, 0 < clock n)
    (hreferenceClock : Tendsto
      (fun n => (reference n : ℝ) / clock n) atTop (nhds clockLimit)) :
    Tendsto
        (fun n => (balancedBlockCount (total n) (reference n) : ℝ))
        atTop atTop ∧
      Tendsto (fun n => balancedBlockShortLength (total n) (reference n))
        atTop atTop ∧
      Tendsto
        (fun n => balancedBlockShortLength (total n) (reference n) + 1)
        atTop atTop ∧
      Tendsto
        (fun n => (balancedBlockShortLength (total n) (reference n) : ℝ) /
          clock n) atTop (nhds clockLimit) ∧
      Tendsto
        (fun n =>
          ((balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
            clock n) atTop (nhds clockLimit) := by
  have hreferencePos : ∀ᶠ n in atTop, 0 < reference n :=
    hreference.eventually (eventually_gt_atTop 0)
  have hreferenceReal : Tendsto (fun n => (reference n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hreference
  have hcountNat : Tendsto (fun n => total n / reference n) atTop atTop :=
    tendsto_nat_div_atTop_of_positive_horizonRatio_of_zero_blockRatio
      htotal hduration hreferenceDensity hreferencePos
  have hcount : Tendsto
      (fun n => (balancedBlockCount (total n) (reference n) : ℝ))
      atTop atTop := by
    simpa only [Function.comp_def, balancedBlockCount] using
      (tendsto_natCast_atTop_atTop.comp hcountNat)
  have hshortReference := tendsto_balancedBlockShortLength_div_referenceLength
    (total := total) (referenceLength := reference)
    hreferenceReal hcount
  have hlongReference := tendsto_balancedBlockLongLength_div_referenceLength
    (total := total) (referenceLength := reference)
    hreferenceReal hcount
  have hshortTop : Tendsto
      (fun n => balancedBlockShortLength (total n) (reference n))
      atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ hreference
    filter_upwards [] with n
    exact Nat.le_add_right (reference n)
      ((total n % reference n) / balancedBlockCount (total n) (reference n))
  have hlongTop : Tendsto
      (fun n => balancedBlockShortLength (total n) (reference n) + 1)
      atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop ?_ hshortTop
    filter_upwards [] with n
    exact Nat.le_add_right
      (balancedBlockShortLength (total n) (reference n)) 1
  have hshortClock : Tendsto
      (fun n => (balancedBlockShortLength (total n) (reference n) : ℝ) /
        clock n) atTop (nhds clockLimit) := by
    have hproduct := hshortReference.mul hreferenceClock
    have heq : (fun n =>
        (balancedBlockShortLength (total n) (reference n) : ℝ) / clock n) =ᶠ[atTop]
        fun n =>
          ((balancedBlockShortLength (total n) (reference n) : ℝ) /
            (reference n : ℝ)) * ((reference n : ℝ) / clock n) := by
      filter_upwards [hreferencePos, hclockPos] with n hn hc
      have hreferenceNe : (reference n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hclockNe : clock n ≠ 0 := ne_of_gt hc
      field_simp [hreferenceNe, hclockNe]
    simpa only [one_mul] using hproduct.congr' heq.symm
  have hlongClock : Tendsto
      (fun n =>
        ((balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
          clock n) atTop (nhds clockLimit) := by
    have hproduct := hlongReference.mul hreferenceClock
    have heq : (fun n =>
        ((balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
          clock n) =ᶠ[atTop]
        fun n =>
          (((balancedBlockShortLength (total n) (reference n) + 1 : ℕ) : ℝ) /
            (reference n : ℝ)) * ((reference n : ℝ) / clock n) := by
      filter_upwards [hreferencePos, hclockPos] with n hn hc
      have hreferenceNe : (reference n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hclockNe : clock n ≠ 0 := ne_of_gt hc
      field_simp [hreferenceNe, hclockNe]
    simpa only [one_mul] using hproduct.congr' heq.symm
  exact ⟨hcount, hshortTop, hlongTop, hshortClock, hlongClock⟩

end Asymptotics

end
