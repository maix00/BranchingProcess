/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Basic
public import Topology.Order.UnitInterval.Time

/-!
# Concatenating càdlàg paths on unit intervals

## Public declarations

- `Topology.unitBlockEndpointSum`: for unit paths $f_i$, the accumulated
  endpoint is $\sum_{i=0}^{n-1} f_i(1)$ in an additive commutative monoid.
- `Topology.concatenateUnitPaths`: for $t\ge0$, the concatenated path is
  $C_f(t)=\sum_{i=0}^{\lfloor t\rfloor}f_i(\theta_i(t))$, where
  $\theta_i(t)$ is the clamped parameter in the $i$th unit block; continuous
  addition makes $C_f$ càdlàg.
- `Topology.concatenateUnitPaths_eq_first`: if $f_1(0)=0$, then
  $C_f(t)=f_0(t)$ for $t\in[0,1]$.
- `Topology.isCadlag_concatenateUnitPaths`: concatenating càdlàg unit paths
  gives a càdlàg path on nonnegative time.
- `Topology.concatenateUnitPaths_eq_finite_sum`: the concatenation is the
  finite sum of its block values up to the current block, without a condition
  on block starting values.
- `Topology.concatenateUnitPaths_eq_sum_range_of_floor_lt`: if every block
  starts at zero and $\lfloor t\rfloor<N$, then
  $C_f(t)=\sum_{i=0}^{N-1}f_i(\theta_i(t))$.
- `Topology.concatenateUnitPaths_increment_eq_sum`: if each block starts at
  zero, then for $0\le s\le t$,
  $C_f(t)-C_f(s)=\sum_{i=0}^{\lfloor t\rfloor}
  \bigl(f_i(\theta_i(t))-f_i(\theta_i(s))\bigr)$.

This file gives a deterministic path construction useful for extending
unit-time process segments to nonnegative time. The state space is any
topological additive commutative monoid. The càdlàg conclusion assumes
continuous addition, and the increment formula assumes an additive group. At
every integer boundary the new segment supplies the right-hand value and the
preceding segment supplies the left limit.

It uses the general block-time coordinate defined in
`Topology.Order.UnitInterval.Time`.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace Topology

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]

private lemma floor_eq_of_bounds {t : ℝ≥0} {n : ℕ}
    (hn : (n : ℝ) ≤ t) (ht : (t : ℝ) < n + 1) :
    Nat.floor (t : ℝ) = n := by
  apply (Nat.floor_eq_iff (show (0 : ℝ) ≤ (t : ℝ) from t.2)).2
  exact ⟨hn, by exact_mod_cast ht⟩

/-- The accumulated endpoint values of the first unit-time segments. -/
noncomputable def unitBlockEndpointSum
    (f : ℕ → CadlagPath unitInterval E) (n : ℕ) : E :=
  ∑ i ∈ Finset.range n, f i ⊤

/-- The path obtained by concatenating a sequence of unit-interval paths.
The integer part selects the block; the accumulated endpoint values translate
each later block. -/
noncomputable def concatenateUnitPaths
    (f : ℕ → CadlagPath unitInterval E) (t : ℝ≥0) : E :=
  unitBlockEndpointSum f (Nat.floor (t : ℝ)) +
    f (Nat.floor (t : ℝ)) (unitInterval.blockParameter (Nat.floor (t : ℝ)) t)

/-- On the first unit interval, concatenation agrees with its first block if
the next block starts at zero. -/
theorem concatenateUnitPaths_eq_first
    (f : ℕ → CadlagPath unitInterval E) (hstart : f 1 ⊥ = 0)
    (t : unitInterval) :
    concatenateUnitPaths f (unitInterval.toNNReal t) = f 0 t := by
  by_cases ht : t = ⊤
  · subst t
    have hzero : (0 : unitInterval) = ⊥ := by
      apply Subtype.ext
      norm_num
    have hstart' : f 1 0 = 0 := by
      rw [hzero]
      exact hstart
    simp [concatenateUnitPaths, unitBlockEndpointSum, unitInterval.blockParameter,
      hstart']
  · have htval : (t : ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro h
      apply ht
      exact Subtype.ext h
    have htoNNReal : ((unitInterval.toNNReal t : ℝ≥0) : ℝ) = (t : ℝ) := rfl
    have hfloor : Nat.floor (unitInterval.toNNReal t : ℝ) = 0 := by
      have ht0 : (0 : ℝ) ≤ (unitInterval.toNNReal t : ℝ) :=
        (unitInterval.toNNReal t).property
      apply (Nat.floor_eq_iff ht0).2
      constructor
      · rw [htoNNReal]
        simpa using t.property.1
      · rw [htoNNReal]
        simpa using htval
    have hparam : unitInterval.blockParameter 0 (unitInterval.toNNReal t) = t := by
      have hval := congrArg (fun x : unitInterval => (x : ℝ))
        (unitInterval.blockParameter_eq_sub hfloor)
      change (unitInterval.blockParameter 0 (unitInterval.toNNReal t) : ℝ) =
        (unitInterval.toNNReal t : ℝ) - (0 : ℕ) at hval
      apply Subtype.ext
      calc
        (unitInterval.blockParameter 0 (unitInterval.toNNReal t) : ℝ) =
            (unitInterval.toNNReal t : ℝ) - (0 : ℕ) := hval
        _ = (t : ℝ) := by rw [htoNNReal]; simp
    rw [concatenateUnitPaths, hfloor]
    simp [unitBlockEndpointSum, hparam]

private noncomputable def translatedUnitBlock
    (f : ℕ → CadlagPath unitInterval E) (n : ℕ) (t : ℝ≥0) : E :=
  unitBlockEndpointSum f n + f n (unitInterval.blockParameter n t)

private lemma isCadlag_translatedUnitBlock [ContinuousAdd E]
    (f : ℕ → CadlagPath unitInterval E) (n : ℕ) :
    IsCadlag (translatedUnitBlock f n) := by
  have hcomp : IsCadlag (fun t : ℝ≥0 => f n (unitInterval.blockParameter n t)) :=
    (f n).isCadlag_toFun.comp_monotone_continuous
      (unitInterval.monotone_blockParameter n) (unitInterval.continuous_blockParameter n)
  exact hcomp.continuous_comp (g := fun x => unitBlockEndpointSum f n + x) (by fun_prop)

private lemma floor_eventually_eq_right {t : ℝ≥0} {n : ℕ}
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

private lemma floor_eventually_eq_left {t : ℝ≥0} {n : ℕ}
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

private lemma concatenate_eq_translated_of_floor
    (f : ℕ → CadlagPath unitInterval E) {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) :
    concatenateUnitPaths f t = translatedUnitBlock f n t := by
  simp [concatenateUnitPaths, translatedUnitBlock, unitBlockEndpointSum, hfloor]

private lemma floor_eventually_eq_left_current {t : ℝ≥0} {n : ℕ}
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

theorem isCadlag_concatenateUnitPaths [ContinuousAdd E]
    (f : ℕ → CadlagPath unitInterval E) :
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

section FiniteSum

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]

/-- A concatenated path is the finite sum of its translated block values up to
the current block. -/
theorem concatenateUnitPaths_eq_finite_sum
    (f : ℕ → CadlagPath unitInterval E) (t : ℝ≥0) :
    concatenateUnitPaths f t =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        f n (unitInterval.blockParameter n t) := by
  let k := Nat.floor (t : ℝ)
  rw [concatenateUnitPaths]
  rw [Finset.sum_range_succ]
  have hleft :
      (∑ n ∈ Finset.range k, f n (unitInterval.blockParameter n t)) =
        unitBlockEndpointSum f k := by
    unfold unitBlockEndpointSum
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n < Nat.floor (t : ℝ) := by simpa [k] using hn
    rw [unitInterval.blockParameter_eq_top_of_lt_floor hn']
  change unitBlockEndpointSum f k + f k (unitInterval.blockParameter k t) =
    (∑ n ∈ Finset.range k, f n (unitInterval.blockParameter n t)) +
      f k (unitInterval.blockParameter k t)
  exact congrArg (fun x : E => x + f k (unitInterval.blockParameter k t)) hleft.symm

/-- The same finite-sum formula can be padded by any number of later blocks.
Those blocks contribute zero because their clamped parameter is the left
endpoint and each block starts at zero. -/
theorem concatenateUnitPaths_eq_sum_range_of_floor_lt
    (f : ℕ → CadlagPath unitInterval E) (hstart : ∀ n, f n ⊥ = 0)
    {t : ℝ≥0} {N : ℕ} (hN : Nat.floor (t : ℝ) < N) :
    concatenateUnitPaths f t =
      ∑ n ∈ Finset.range N, f n (unitInterval.blockParameter n t) := by
  rw [concatenateUnitPaths_eq_finite_sum f t]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hN))
  intro n hn hnnot
  have hn' : Nat.floor (t : ℝ) < n := by
    by_contra h
    have hnle : n ≤ Nat.floor (t : ℝ) := Nat.le_of_not_gt h
    have hnmem : n ∈ Finset.range (Nat.floor (t : ℝ) + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hnle)
    exact hnnot hnmem
  rw [unitInterval.blockParameter_eq_bot_of_floor_lt hn']
  simp [hstart]

end FiniteSum

section Increment

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]

/-- Every increment of the concatenated path is the sum of the corresponding
increments contributed by the finitely many blocks visited before its right
endpoint. This is the pathwise decomposition used for the process-level
independence and convolution arguments. -/

theorem concatenateUnitPaths_increment_eq_sum
    (f : ℕ → CadlagPath unitInterval E) (hstart : ∀ n, f n ⊥ = 0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    concatenateUnitPaths f t - concatenateUnitPaths f s =
      ∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (f n (unitInterval.blockParameter n t) - f n (unitInterval.blockParameter n s)) := by
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := by
    apply Nat.floor_mono
    exact_mod_cast hst
  have hs : Nat.floor (s : ℝ) < Nat.floor (t : ℝ) + 1 :=
    lt_of_le_of_lt hfloor (Nat.lt_succ_self _)
  have ht : Nat.floor (t : ℝ) < Nat.floor (t : ℝ) + 1 := Nat.lt_succ_self _
  rw [concatenateUnitPaths_eq_sum_range_of_floor_lt f hstart hs,
    concatenateUnitPaths_eq_sum_range_of_floor_lt f hstart ht]
  simp_rw [Finset.sum_sub_distrib]

end Increment


end Topology

end
