/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Basic
public import Topology.Order.UnitInterval.Time

/-!
# Concatenating càdlàg paths on unit intervals

This file gives a deterministic path construction useful for extending
unit-time process segments to nonnegative time. At every integer boundary the
new segment supplies the right-hand value and the preceding segment supplies
the left limit.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace Topology

/-- Clamp the displacement from the left endpoint of an integer block to the
unit interval. -/
noncomputable def unitBlockParameter (n : ℕ) (t : ℝ≥0) : unitInterval :=
  ⟨min 1 (max 0 ((t : ℝ) - n)), by
    refine ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩

theorem monotone_unitBlockParameter (n : ℕ) :
    Monotone (unitBlockParameter n) := by
  intro s t hst
  apply Subtype.coe_le_coe.mpr
  dsimp [unitBlockParameter]
  have hconstOne : Monotone (fun _ : ℝ≥0 => (1 : ℝ)) := monotone_const
  have hconstZero : Monotone (fun _ : ℝ≥0 => (0 : ℝ)) := monotone_const
  have hsub : Monotone (fun t : ℝ≥0 => (t : ℝ) - n) := by
    intro s t hst
    exact sub_le_sub_right (show (s : ℝ) ≤ t from by exact_mod_cast hst) _
  exact (Monotone.min hconstOne (Monotone.max hconstZero hsub)) hst

theorem continuous_unitBlockParameter (n : ℕ) :
    Continuous (unitBlockParameter n) := by
  exact Continuous.subtype_mk (by fun_prop) (fun t => (unitBlockParameter n t).property)

private theorem floor_eq_of_bounds {t : ℝ≥0} {n : ℕ}
    (hn : (n : ℝ) ≤ t) (ht : (t : ℝ) < n + 1) :
    Nat.floor (t : ℝ) = n := by
  apply (Nat.floor_eq_iff (show (0 : ℝ) ≤ (t : ℝ) from t.2)).2
  exact ⟨hn, by exact_mod_cast ht⟩

theorem unitBlockParameter_eq_sub {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) :
    unitBlockParameter n t = ⟨(t : ℝ) - n, by
      constructor
      · have h := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
        rw [hfloor] at h
        linarith
      · have h := Nat.lt_floor_add_one (t : ℝ)
        rw [hfloor] at h
        linarith⟩ := by
  apply Subtype.ext
  dsimp [unitBlockParameter]
  have hfloorle : (n : ℝ) ≤ (t : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    rw [hfloor] at h
    exact h
  have hfloorlt : (t : ℝ) < n + 1 := by
    have h := Nat.lt_floor_add_one (t : ℝ)
    rw [hfloor] at h
    exact h
  rw [max_eq_right (show 0 ≤ (t : ℝ) - n by linarith),
    min_eq_right (show (t : ℝ) - n ≤ 1 by linarith)]

/-- The accumulated endpoint values of the first unit-time segments. -/
noncomputable def unitBlockEndpointSum
    (f : ℕ → CadlagPath unitInterval ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f i ⊤

/-- The path obtained by concatenating a sequence of unit-interval paths.
The integer part selects the block; the accumulated endpoint values translate
each later block. -/
noncomputable def concatenateUnitPaths
    (f : ℕ → CadlagPath unitInterval ℝ) (t : ℝ≥0) : ℝ :=
  unitBlockEndpointSum f (Nat.floor (t : ℝ)) +
    f (Nat.floor (t : ℝ)) (unitBlockParameter (Nat.floor (t : ℝ)) t)

/-- On the first unit interval, concatenation agrees with its first block if
the next block starts at zero. -/
theorem concatenateUnitPaths_eq_first
    (f : ℕ → CadlagPath unitInterval ℝ) (hstart : f 1 ⊥ = 0)
    (t : unitInterval) :
    concatenateUnitPaths f (UnitInterval.toNNReal t) = f 0 t := by
  by_cases ht : t = ⊤
  · subst t
    have hzero : (0 : unitInterval) = ⊥ := by
      apply Subtype.ext
      norm_num
    have hstart' : f 1 0 = 0 := by
      rw [hzero]
      exact hstart
    simp [concatenateUnitPaths, unitBlockEndpointSum, unitBlockParameter,
      hstart']
  · have htval : (t : ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro h
      apply ht
      exact Subtype.ext h
    have htoNNReal : ((UnitInterval.toNNReal t : ℝ≥0) : ℝ) = (t : ℝ) := rfl
    have hfloor : Nat.floor (UnitInterval.toNNReal t : ℝ) = 0 := by
      have ht0 : (0 : ℝ) ≤ (UnitInterval.toNNReal t : ℝ) :=
        (UnitInterval.toNNReal t).property
      apply (Nat.floor_eq_iff ht0).2
      constructor
      · norm_num
      · rw [htoNNReal]
        simpa using htval
    have hparam : unitBlockParameter 0 (UnitInterval.toNNReal t) = t := by
      have hval := congrArg (fun x : unitInterval => (x : ℝ))
        (unitBlockParameter_eq_sub hfloor)
      change (unitBlockParameter 0 (UnitInterval.toNNReal t) : ℝ) =
        (UnitInterval.toNNReal t : ℝ) - (0 : ℕ) at hval
      apply Subtype.ext
      calc
        (unitBlockParameter 0 (UnitInterval.toNNReal t) : ℝ) =
            (UnitInterval.toNNReal t : ℝ) - (0 : ℕ) := hval
        _ = (t : ℝ) := by rw [htoNNReal]; simp
    rw [concatenateUnitPaths, hfloor]
    simp [unitBlockEndpointSum, hparam]

private noncomputable def translatedUnitBlock
    (f : ℕ → CadlagPath unitInterval ℝ) (n : ℕ) (t : ℝ≥0) : ℝ :=
  unitBlockEndpointSum f n + f n (unitBlockParameter n t)

private theorem isCadlag_translatedUnitBlock
    (f : ℕ → CadlagPath unitInterval ℝ) (n : ℕ) :
    IsCadlag (translatedUnitBlock f n) := by
  have hcomp : IsCadlag (fun t : ℝ≥0 => f n (unitBlockParameter n t)) :=
    (f n).isCadlag_toFun.comp_monotone_continuous
      (monotone_unitBlockParameter n) (continuous_unitBlockParameter n)
  exact hcomp.continuous_comp (g := fun x => unitBlockEndpointSum f n + x) (by fun_prop)

private theorem floor_eventually_eq_right {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) :
    ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Ioi t] t, Nat.floor (s : ℝ) = n := by
  have hupper : (t : ℝ) < (n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (t : ℝ)
    rw [hfloor] at h
    exact h
  have heventUpper : ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Ioi t] t,
      (s : ℝ) < (n : ℝ) + 1 := by
    have hreal := isOpen_Iio.mem_nhds (mem_Iio.mpr hupper)
    have hsubtype : {s : ℝ≥0 | (s : ℝ) < (n : ℝ) + 1} ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.eventually hreal
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hsubtype
  filter_upwards [heventUpper, self_mem_nhdsWithin] with s hsUpper hsRight
  have hn_t : (n : ℝ) ≤ (t : ℝ) := by
    have hfloorle := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    rw [hfloor] at hfloorle
    exact hfloorle
  have ht_s : (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsRight.le
  exact floor_eq_of_bounds (t := s) (n := n) (hn_t.trans ht_s) hsUpper

private theorem floor_eventually_eq_left {t : ℝ≥0} {n : ℕ}
    (_hfloor : Nat.floor (t : ℝ) = n) (htInteger : (t : ℝ) = n) (hn : 0 < n) :
    ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Iio t] t, Nat.floor (s : ℝ) = n - 1 := by
  have hlower : ((n - 1 : ℕ) : ℝ) < (t : ℝ) := by
    have hfloorle := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    rw [_hfloor] at hfloorle
    have hpred : n - 1 < n := Nat.sub_lt hn (by decide)
    have hpred' : ((n - 1 : ℕ) : ℝ) < n := by exact_mod_cast hpred
    linarith
  have heventLower : ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Iio t] t,
      ((n - 1 : ℕ) : ℝ) < (s : ℝ) := by
    have hreal := isOpen_Ioi.mem_nhds (mem_Ioi.mpr hlower)
    have hsubtype : {s : ℝ≥0 | ((n - 1 : ℕ) : ℝ) < (s : ℝ)} ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.eventually hreal
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hsubtype
  filter_upwards [heventLower, self_mem_nhdsWithin] with s hsLower hsLeft
  have hupper : (s : ℝ) < ((n - 1 : ℕ) : ℝ) + 1 := by
    have hslt : (s : ℝ) < (t : ℝ) := by exact_mod_cast hsLeft
    rw [htInteger] at hslt
    have hsub : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast (Nat.sub_add_cancel hn)
    rw [hsub]
    exact hslt
  exact floor_eq_of_bounds (t := s) (n := n - 1) (le_of_lt hsLower) hupper

private theorem concatenate_eq_translated_of_floor
    (f : ℕ → CadlagPath unitInterval ℝ) {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) :
    concatenateUnitPaths f t = translatedUnitBlock f n t := by
  simp [concatenateUnitPaths, translatedUnitBlock, unitBlockEndpointSum, hfloor]

private theorem floor_eventually_eq_left_current {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) (hn : (n : ℝ) < (t : ℝ)) :
    ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Iio t] t, Nat.floor (s : ℝ) = n := by
  have hupper : (t : ℝ) < (n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (t : ℝ)
    rw [hfloor] at h
    exact h
  have heventLower : ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Iio t] t, (n : ℝ) < (s : ℝ) := by
    have hreal := isOpen_Ioi.mem_nhds (mem_Ioi.mpr hn)
    have hsubtype : {s : ℝ≥0 | (n : ℝ) < (s : ℝ)} ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.eventually hreal
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hsubtype
  have heventUpper : ∀ᶠ (s : ℝ≥0) in 𝓝[Set.Iio t] t,
      (s : ℝ) < (n : ℝ) + 1 := by
    have hreal := isOpen_Iio.mem_nhds (mem_Iio.mpr hupper)
    have hsubtype : {s : ℝ≥0 | (s : ℝ) < (n : ℝ) + 1} ∈ 𝓝 t :=
      continuous_subtype_val.continuousAt.eventually hreal
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hsubtype
  filter_upwards [heventLower, heventUpper] with s hsLower hsUpper
  exact floor_eq_of_bounds (t := s) (n := n) (le_of_lt hsLower) hsUpper

theorem isCadlag_concatenateUnitPaths
    (f : ℕ → CadlagPath unitInterval ℝ) :
    IsCadlag (concatenateUnitPaths f) := by
  refine ⟨?_, ?_⟩
  · intro t
    let n := Nat.floor (t : ℝ)
    have hfloor : Nat.floor (t : ℝ) = n := rfl
    have hvalue : concatenateUnitPaths f t = translatedUnitBlock f n t :=
      concatenate_eq_translated_of_floor f hfloor
    have heq : concatenateUnitPaths f =ᶠ[𝓝[Set.Ioi t] t]
        translatedUnitBlock f n := by
      filter_upwards [floor_eventually_eq_right hfloor] with s hs
      exact concatenate_eq_translated_of_floor f hs
    have hcont := (isCadlag_translatedUnitBlock f n).isRightContinuous t
    exact hcont.congr_of_eventuallyEq heq hvalue
  · intro t
    let n := Nat.floor (t : ℝ)
    have hfloor : Nat.floor (t : ℝ) = n := rfl
    have hfloorle : (n : ℝ) ≤ (t : ℝ) := by
      have h := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
      rw [hfloor] at h
      exact h
    by_cases htInteger : (t : ℝ) = n
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · have htzero_real : (t : ℝ) = 0 := by
          change (t : ℝ) = (n : ℝ) at htInteger
          rw [hn] at htInteger
          simpa using htInteger
        have htzero : t = 0 := NNReal.coe_injective htzero_real
        subst t
        have hfilter : 𝓝[Set.Iio (0 : ℝ≥0)] (0 : ℝ≥0) = ⊥ := by
          simp [nhdsWithin]
        refine ⟨0, ?_⟩
        rw [hfilter]
        exact tendsto_bot
      · let m := n - 1
        have hleftFloor := floor_eventually_eq_left hfloor htInteger hn
        have hEq : concatenateUnitPaths f =ᶠ[𝓝[Set.Iio t] t]
            translatedUnitBlock f m := by
          filter_upwards [hleftFloor] with s hs
          exact concatenate_eq_translated_of_floor f (by simpa [m] using hs)
        obtain ⟨l, hl⟩ := (isCadlag_translatedUnitBlock f m).tendsto_nhdsLT t
        exact ⟨l, hl.congr' hEq.symm⟩
    · have hnlt : (n : ℝ) < (t : ℝ) := lt_of_le_of_ne hfloorle (Ne.symm htInteger)
      have hleftFloor := floor_eventually_eq_left_current hfloor hnlt
      have hEq : concatenateUnitPaths f =ᶠ[𝓝[Set.Iio t] t]
          translatedUnitBlock f n := by
        filter_upwards [hleftFloor] with s hs
        exact concatenate_eq_translated_of_floor f hs
      obtain ⟨l, hl⟩ := (isCadlag_translatedUnitBlock f n).tendsto_nhdsLT t
      exact ⟨l, hl.congr' hEq.symm⟩

end Topology

end

@[expose] public section

namespace Topology

open scoped NNReal

/-- Below the current integer block, the clamped block parameter is the right
endpoint. -/
theorem unitBlockParameter_eq_top_of_lt_floor {t : ℝ≥0} {n : ℕ}
    (h : n < Nat.floor (t : ℝ)) :
    unitBlockParameter n t = ⊤ := by
  apply Subtype.ext
  dsimp [unitBlockParameter]
  have hfloor : (n : ℝ) + 1 ≤ (t : ℝ) := by
    have hn : n + 1 ≤ Nat.floor (t : ℝ) := Nat.succ_le_of_lt h
    have hle := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    exact le_trans (by exact_mod_cast hn) hle
  rw [min_eq_left (show (1 : ℝ) ≤ max 0 ((t : ℝ) - n) by
    rw [max_eq_right (show 0 ≤ (t : ℝ) - n by linarith)]
    linarith)]

/-- Beyond the current integer block, the clamped block parameter is the left
endpoint. -/
theorem unitBlockParameter_eq_bot_of_floor_lt {t : ℝ≥0} {n : ℕ}
    (h : Nat.floor (t : ℝ) < n) :
    unitBlockParameter n t = ⊥ := by
  apply Subtype.ext
  dsimp [unitBlockParameter]
  have hupper : (t : ℝ) < (n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (t : ℝ)
    have hn : Nat.floor (t : ℝ) + 1 ≤ n := Nat.succ_le_of_lt h
    have hn' : (Nat.floor (t : ℝ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [max_eq_left (show (t : ℝ) - n ≤ 0 by linarith)]
  simp

/-- A concatenated path is the finite sum of its translated block values up to
the current block. Blocks strictly after that block contribute zero when they
start at zero. -/
theorem concatenateUnitPaths_eq_finite_sum
    (f : ℕ → CadlagPath unitInterval ℝ) (hstart : ∀ n, f n ⊥ = 0)
    (t : ℝ≥0) :
    concatenateUnitPaths f t =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        f n (unitBlockParameter n t) := by
  let k := Nat.floor (t : ℝ)
  rw [concatenateUnitPaths]
  rw [Finset.sum_range_succ]
  have hleft :
      (∑ n ∈ Finset.range k, f n (unitBlockParameter n t)) =
        unitBlockEndpointSum f k := by
    unfold unitBlockEndpointSum
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n < Nat.floor (t : ℝ) := by simpa [k] using hn
    rw [unitBlockParameter_eq_top_of_lt_floor hn']
  simpa [k] using hleft.symm

/-- The same finite-sum formula can be padded by any number of later blocks.
Those blocks contribute zero because their clamped parameter is the left
endpoint and each block starts at zero. -/
theorem concatenateUnitPaths_eq_sum_range_of_floor_lt
    (f : ℕ → CadlagPath unitInterval ℝ) (hstart : ∀ n, f n ⊥ = 0)
    {t : ℝ≥0} {N : ℕ} (hN : Nat.floor (t : ℝ) < N) :
    concatenateUnitPaths f t =
      ∑ n ∈ Finset.range N, f n (unitBlockParameter n t) := by
  rw [concatenateUnitPaths_eq_finite_sum f hstart t]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hN))
  intro n hn hnnot
  have hn' : Nat.floor (t : ℝ) < n := by
    by_contra h
    have hnle : n ≤ Nat.floor (t : ℝ) := Nat.le_of_not_gt h
    have hnmem : n ∈ Finset.range (Nat.floor (t : ℝ) + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hnle)
    exact hnnot hnmem
  rw [unitBlockParameter_eq_bot_of_floor_lt hn']
  simp [hstart]

/-- Every increment of the concatenated path is the sum of the corresponding
increments contributed by the finitely many blocks visited before its right
endpoint. This is the pathwise decomposition used for the process-level
independence and convolution arguments. -/
theorem concatenateUnitPaths_increment_eq_sum
    (f : ℕ → CadlagPath unitInterval ℝ) (hstart : ∀ n, f n ⊥ = 0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    concatenateUnitPaths f t - concatenateUnitPaths f s =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (f n (unitBlockParameter n t) - f n (unitBlockParameter n s)) := by
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := by
    apply Nat.floor_mono
    exact_mod_cast hst
  have hs : Nat.floor (s : ℝ) < Nat.floor (t : ℝ) + 1 :=
    lt_of_le_of_lt hfloor (Nat.lt_succ_self _)
  have ht : Nat.floor (t : ℝ) < Nat.floor (t : ℝ) + 1 := Nat.lt_succ_self _
  rw [concatenateUnitPaths_eq_sum_range_of_floor_lt f hstart hs,
    concatenateUnitPaths_eq_sum_range_of_floor_lt f hstart ht]
  simp_rw [Finset.sum_sub_distrib]

/-- The lengths of the clamped pieces of `[0,t]` add to `t`. -/
theorem sum_unitBlockParameter_eq_time (t : ℝ≥0) :
    (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
      (unitBlockParameter n t : ℝ)) = (t : ℝ) := by
  have hfull :
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ)),
        (unitBlockParameter n t : ℝ)) = (Nat.floor (t : ℝ) : ℝ) := by
    calc
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ)),
          (unitBlockParameter n t : ℝ)) =
          ∑ n ∈ Finset.range (Nat.floor (t : ℝ)), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn' : n < Nat.floor (t : ℝ) := Finset.mem_range.mp hn
            rw [unitBlockParameter_eq_top_of_lt_floor hn']
            rfl
      _ = (Nat.floor (t : ℝ) : ℝ) := by simp
  have hcurrent :
      (unitBlockParameter (Nat.floor (t : ℝ)) t : ℝ) =
        (t : ℝ) - (Nat.floor (t : ℝ) : ℝ) := by
    exact congrArg Subtype.val
      (unitBlockParameter_eq_sub (t := t) (n := Nat.floor (t : ℝ)) rfl)
  rw [Finset.sum_range_succ, hfull, hcurrent]
  ring

/-- For two times `s ≤ t`, the durations contributed by all blocks up to
`floor t` add to the elapsed time. This is the clock identity required when
the stable convolution semigroup is applied block by block. -/
theorem sum_unitBlockParameter_increment_eq_time_sub
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
      ((unitBlockParameter n t : ℝ) - (unitBlockParameter n s : ℝ))) =
        (t : ℝ) - (s : ℝ) := by
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := by
    apply Nat.floor_mono
    exact_mod_cast hst
  have hs : Nat.floor (s : ℝ) < Nat.floor (t : ℝ) + 1 :=
    lt_of_le_of_lt hfloor (Nat.lt_succ_self _)
  have hsumS := sum_unitBlockParameter_eq_time s
  have hsumT := sum_unitBlockParameter_eq_time t
  have hsumS' :
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (unitBlockParameter n s : ℝ)) = (s : ℝ) := by
    calc
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (unitBlockParameter n s : ℝ)) =
          ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1),
            (unitBlockParameter n s : ℝ) := by
              symm
              apply Finset.sum_subset
                (Finset.range_mono (Nat.succ_le_of_lt hs))
              intro n hn hnnot
              have hn' : Nat.floor (s : ℝ) < n := by
                by_contra h
                have hnle : n ≤ Nat.floor (s : ℝ) := Nat.le_of_not_gt h
                exact hnnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hnle))
              rw [unitBlockParameter_eq_bot_of_floor_lt hn']
              simp
      _ = (s : ℝ) := hsumS
  rw [Finset.sum_sub_distrib, hsumT, hsumS']

end Topology

end
