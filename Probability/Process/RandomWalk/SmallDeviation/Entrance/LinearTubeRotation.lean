/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.LinearPath
public import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Cyclic rotations of a path near an increasing line

If a finite partial-sum path stays close to the line `t ↦ t / 2`, rotating
the increments at a minimum produces a path in a fixed nonnegative corridor.
This is the deterministic input to the edge-offset entrance estimate.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

noncomputable def normalizedTime {n : ℕ} (j : Fin (n + 1)) : ℝ :=
  (j.val : ℝ) / (n : ℝ)

/-- The partial sum after cyclically starting at `k`, expressed from the
original partial-sum path. -/
def cyclicPartialSum {n : ℕ} (s : Fin (n + 1) → ℝ)
    (k : Fin n) (j : Fin (n + 1)) : ℝ :=
  if h : k.val + j.val ≤ n then
    s ⟨k.val + j.val, Nat.lt_succ_of_le h⟩ - s k.castSucc
  else
    s (Fin.last n) - s k.castSucc +
      s ⟨k.val + j.val - n, by omega⟩

/-- The path produced by cyclically rotating the increments encoded by `s`. -/
def cyclicRotatePath {n : ℕ} (s : Fin (n + 1) → ℝ) (k : Fin n) :
    Fin (n + 1) → ℝ :=
  fun j => cyclicPartialSum s k j

/-- The static offset corridor and its central terminal band. -/
def offsetCorridorPath {n : ℕ} (u : ℝ) (s : Fin (n + 1) → ℝ) : Prop :=
  (∀ j, s j ∈ Set.Icc (-u) (1 - u)) ∧
    s (Fin.last n) ∈ Set.Icc (1 / 3 - u) (2 / 3 - u)

/-- A finite family of measure-preserving cyclic rotations turns a pointwise
rotation-cover into the factor-`n` probability loss. -/
theorem measure_le_card_smul_of_finiteRotationCover
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (event safe : Set Ω) (rotate : Fin n → Ω → Ω)
    (hcover : event ⊆ ⋃ k, (rotate k) ⁻¹' safe)
    (hinvariant : ∀ k, μ ((rotate k) ⁻¹' safe) = μ safe) :
    μ event ≤ n • μ safe := by
  calc
    μ event ≤ μ (⋃ k, (rotate k) ⁻¹' safe) := measure_mono hcover
    _ ≤ ∑ k : Fin n, μ ((rotate k) ⁻¹' safe) := measure_iUnion_fintype_le μ _
    _ = ∑ _k : Fin n, μ safe := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hinvariant k
    _ = n • μ safe := by simp

/-- An open-set Portmanteau lower bound transfers to any event that eventually
contains the corresponding normalized-path preimage. -/
theorem TendstoInDistribution.measure_openEvent_le_liminf
    {I E Ω' : Type*} {Ω : I → Type*}
    {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {mE : MeasurableSpace E} [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {X : (i : I) → Ω i → E} {Z : Ω' → E} {l : Filter I}
    (h : MeasureTheory.TendstoInDistribution X l Z μ μ')
    [l.NeBot]
    {U : Set E} (hU : IsOpen U)
    (event : ∀ i, Set (Ω i))
    (hcover : ∀ᶠ i in l, X i ⁻¹' U ⊆ event i) :
    μ'.map Z U ≤ l.liminf (fun i => μ i (event i)) := by
  have hport := h.measure_map_le_liminf_of_isOpen hU
  have hcomp : ∀ᶠ i in l, (μ i).map (X i) U ≤ μ i (event i) := by
    filter_upwards [hcover] with i hi
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable i)
      hU.measurableSet]
    exact measure_mono hi
  have hsourceBounded : Filter.IsBoundedUnder (· ≥ ·) l
      (fun i => (μ i).map (X i) U) :=
    ⟨0, Filter.Eventually.of_forall fun _ => bot_le⟩
  have htargetLeOne (i : I) : μ i (event i) ≤ 1 := by
    calc
      μ i (event i) ≤ μ i Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have htargetBounded : Filter.IsCoboundedUnder (· ≥ ·) l
      (fun i => μ i (event i)) :=
    (Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall htargetLeOne)).isCoboundedUnder_ge
  exact hport.trans <| Filter.liminf_le_liminf hcomp hsourceBounded htargetBounded

/-- A middle offset is within `1/100` of one of finitely many mesh points. -/
theorem exists_middleOffset_meshPoint {u : ℝ}
    (hu : u ∈ Set.Icc (1 / 10) (9 / 10)) :
    ∃ k : ℕ, 10 ≤ k ∧ k ≤ 90 ∧ |u - (k : ℝ) / 100| ≤ 1 / 100 := by
  rcases hu with ⟨huLower, huUpper⟩
  let k : ℕ := ⌊100 * u⌋₊
  have huNonneg : 0 ≤ 100 * u := by linarith
  have hkLower : (k : ℝ) ≤ 100 * u := by
    simpa [k] using Nat.floor_le huNonneg
  have hkUpper : 100 * u < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one (100 * u)
  have hkLow : 10 ≤ k := by
    by_contra h
    have hkNat : k ≤ 9 := by omega
    have hkReal : (k : ℝ) + 1 ≤ 10 := by exact_mod_cast Nat.succ_le_succ hkNat
    have huReal : (10 : ℝ) ≤ 100 * u := by nlinarith
    linarith
  have hkHigh : k ≤ 90 := by
    have hkReal : (k : ℝ) ≤ 90 := by nlinarith
    exact_mod_cast hkReal
  have hmeshLower : (k : ℝ) / 100 ≤ u := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100)).2
    nlinarith
  have hmeshUpper : u < ((k : ℝ) + 1) / 100 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2
    nlinarith
  refine ⟨k, hkLow, hkHigh, ?_⟩
  rw [abs_le]
  constructor <;> nlinarith

/-- A small uniform tube around the mesh line at a middle offset lies strictly
inside the corresponding static corridor and its central endpoint band. -/
theorem linearTube_subset_middleOffsetCorridor
    {u center : ℝ} (hu : u ∈ Set.Icc (1 / 10) (9 / 10))
    (hucenter : |u - center| ≤ 1 / 100)
    (path : unitInterval → ℝ)
    (hpath : ∀ t, |path t - (1 / 2 - center) * (t : ℝ)| < 1 / 100) :
    (∀ t, path t ∈ Set.Ioo (-u) (1 - u)) ∧
      path ⊤ ∈ Set.Ioo (1 / 3 - u) (2 / 3 - u) := by
  rcases hu with ⟨huLower, huUpper⟩
  have hdiff := abs_le.mp hucenter
  have hall : ∀ t : unitInterval,
      -u < path t ∧ path t < 1 - u := by
    intro t
    have ht := t.property
    have ht0 : 0 ≤ (t : ℝ) := ht.1
    have ht1 : (t : ℝ) ≤ 1 := ht.2
    have hline := hpath t
    have hlineLower : 1 / 10 ≤ (1 / 2 - center) * (t : ℝ) + u := by
      have hcoeff : 49 / 100 ≤ 1 / 2 + u - center := by linarith
      calc
        1 / 10 ≤ (49 / 100) * (t : ℝ) + (1 / 10) * (1 - (t : ℝ)) := by
          nlinarith [ht0, ht1]
        _ ≤ (1 / 2 + u - center) * (t : ℝ) + u * (1 - (t : ℝ)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoeff ht0)
            (mul_le_mul_of_nonneg_right huLower (sub_nonneg.mpr ht1))
        _ = (1 / 2 - center) * (t : ℝ) + u := by ring
    have hlineUpper : 1 / 10 ≤ (1 - u) - (1 / 2 - center) * (t : ℝ) := by
      have hcoeff : 49 / 100 ≤ 1 / 2 + center - u := by linarith
      calc
        1 / 10 ≤ (49 / 100) * (t : ℝ) + (1 / 10) * (1 - (t : ℝ)) := by
          nlinarith [ht0, ht1]
        _ ≤ (1 / 2 + center - u) * (t : ℝ) + (1 - u) * (1 - (t : ℝ)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoeff ht0)
            (mul_le_mul_of_nonneg_right (by linarith : (1 / 10 : ℝ) ≤ 1 - u)
              (sub_nonneg.mpr ht1))
        _ = (1 - u) - (1 / 2 - center) * (t : ℝ) := by ring
    have hlineBounds := abs_lt.mp hline
    constructor
    · change -u < path t
      linarith
    · change path t < 1 - u
      linarith
  have htopTube : |path ⊤ - (1 / 2 - center)| < 1 / 100 := by
    simpa using hpath ⊤
  refine ⟨fun t => ?_, ?_⟩
  · exact hall t
  · rcases abs_lt.mp htopTube with ⟨htLower, htUpper⟩
    constructor
    · linarith
    · linarith

/-- A path starting at zero and uniformly within `ε < 1/16` of `t ↦ t/2`
has a cyclic rotation whose partial sums stay in `[0, 3/4]`.  Its terminal
sum lies in the central interval `[7/16, 9/16]`. -/
theorem exists_cyclicPartialSum_mem_Icc_of_linearTube
    {n : ℕ} (hn : 0 < n) (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j - normalizedTime j / 2| < ε) :
    ∃ k : Fin n,
      (∀ j, cyclicPartialSum s k j ∈ Set.Icc 0 (3 / 4)) ∧
      s (Fin.last n) ∈ Set.Icc (7 / 16) (9 / 16) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have htime_nonneg (j : Fin (n + 1)) : 0 ≤ normalizedTime j := by
    exact div_nonneg (Nat.cast_nonneg _) hnR.le
  have htime_le_one (j : Fin (n + 1)) : normalizedTime j ≤ 1 := by
    dsimp [normalizedTime]
    apply (div_le_one hnR).2
    exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hnear (j : Fin (n + 1)) :
      normalizedTime j / 2 - ε < s j ∧ s j < normalizedTime j / 2 + ε := by
    have h := abs_lt.mp (htube j)
    constructor <;> linarith
  have hlastTime : normalizedTime (Fin.last n) = 1 := by
    simp [normalizedTime, hnR.ne']
  have hlastNear := hnear (Fin.last n)
  rw [hlastTime] at hlastNear
  have hlast : s (Fin.last n) ∈ Set.Icc (7 / 16) (9 / 16) := by
    constructor <;> norm_num at * <;> linarith
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨k, hkmin⟩ := Finite.exists_min (fun i : Fin n => s i.castSucc)
  have hkzero : s k.castSucc ≤ 0 := by
    calc
      s k.castSucc ≤ s (⟨0, hn⟩ : Fin n).castSucc := hkmin _
      _ = 0 := by simpa using hs0
  have hmin_lt {p : Fin (n + 1)} (hp : p.val < n) :
      s k.castSucc ≤ s p := by
    have h := hkmin (⟨p.val, hp⟩ : Fin n)
    simpa using h
  have hmin_le (p : Fin (n + 1)) : s k.castSucc ≤ s p := by
    by_cases hp : p.val < n
    · exact hmin_lt hp
    · have hp' : p = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst p
      exact hkzero.trans (by linarith [hlast.1])
  have hknear := hnear k.castSucc
  have hktime : normalizedTime k.castSucc < 2 * ε := by
    have htime := htime_nonneg k.castSucc
    simp only [normalizedTime, Fin.val_castSucc] at hknear htime ⊢
    linarith
  refine ⟨k, ?_, hlast⟩
  intro j
  unfold cyclicPartialSum
  split_ifs with h
  · let p : Fin (n + 1) := ⟨k.val + j.val, Nat.lt_succ_of_le h⟩
    have hpTime : normalizedTime p = normalizedTime k.castSucc + normalizedTime j := by
      simp [normalizedTime, p, Fin.val_castSucc, Nat.cast_add, add_div]
    have hpNear := hnear p
    have hkNear := hnear k.castSucc
    have hrotLower : 0 ≤ s p - s k.castSucc := by
      linarith [hmin_le p]
    have hrotUpper : s p - s k.castSucc ≤ 3 / 4 := by
      linarith [hpNear.2, hkNear.1, hpTime, htime_le_one j,
        htime_nonneg k.castSucc, hε16]
    have hrotUpper' : s p ≤ 3 / 4 + s k.castSucc := by linarith [hrotUpper]
    simpa [p] using ⟨hmin_le p, hrotUpper'⟩
  · let p : Fin (n + 1) := ⟨k.val + j.val - n, by omega⟩
    have hpLt : p.val < n := by
      dsimp [p]
      omega
    have hpTimeLe : normalizedTime p ≤ normalizedTime k.castSucc := by
      dsimp [normalizedTime, p]
      apply div_le_div_of_nonneg_right
      · exact_mod_cast (show k.val + j.val - n ≤ k.val by omega)
      · exact hnR.le
    have hpNear := hnear p
    have hkNear := hnear k.castSucc
    have hrotLower : 0 ≤ s (Fin.last n) - s k.castSucc + s p := by
      have hpmin := hmin_lt hpLt
      linarith [hlast.1]
    have hrotUpper :
        s (Fin.last n) - s k.castSucc + s p ≤ 3 / 4 := by
      linarith [hlast.2, hpNear.2, hkNear.1, hpTimeLe, hε16]
    simpa [p] using ⟨hrotLower, hrotUpper⟩

/-- The decreasing-line counterpart, obtained by applying the increasing-line
statement to the negated path. -/
theorem exists_cyclicPartialSum_mem_Icc_of_negativeLinearTube
    {n : ℕ} (hn : 0 < n) (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j + normalizedTime j / 2| < ε) :
    ∃ k : Fin n,
      (∀ j, cyclicPartialSum s k j ∈ Set.Icc (-3 / 4) 0) ∧
      s (Fin.last n) ∈ Set.Icc (-9 / 16) (-7 / 16) := by
  have htubeNeg : ∀ j, |(fun i => -s i) j - normalizedTime j / 2| < ε := by
    intro j
    rw [show (fun i => -s i) j - normalizedTime j / 2 =
      -(s j + normalizedTime j / 2) by ring, abs_neg]
    exact htube j
  obtain ⟨k, hk, hend⟩ :=
    exists_cyclicPartialSum_mem_Icc_of_linearTube hn (fun i => -s i)
      (by simpa using congrArg Neg.neg hs0) hε hε16 htubeNeg
  refine ⟨k, ?_, ?_⟩
  · intro j
    have hneg : cyclicPartialSum (fun i => -s i) k j =
        -cyclicPartialSum s k j := by
      unfold cyclicPartialSum
      split_ifs <;> simp <;> ring
    have h := hk j
    rw [hneg] at h
    constructor <;> linarith [h.1, h.2]
  · rcases hend with ⟨hlower, hupper⟩
    constructor <;> linarith

/-- A cyclic rotation preserves the total sum at its terminal index. -/
theorem cyclicPartialSum_last {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs0 : s 0 = 0) (k : Fin n) :
    cyclicPartialSum s k (Fin.last n) = s (Fin.last n) := by
  unfold cyclicPartialSum
  split_ifs with h
  · simp only [Fin.val_last] at h ⊢
    have hk : k.val = 0 := by omega
    have hkzero : k.castSucc = 0 := by
      apply Fin.ext
      simp [hk]
    have hindex :
        (⟨k.val + n, Nat.lt_succ_of_le (by omega)⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_last]
      omega
    rw [hindex, hkzero, hs0]
    ring
  · simp only [Fin.val_last] at h ⊢
    have hindex :
        (⟨k.val + n - n, by omega⟩ : Fin (n + 1)) = k.castSucc := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_castSucc]
      omega
    rw [hindex]
    ring

/-- A path starting at zero and uniformly close to the offset-dependent line
`t ↦ (1/2 - u) * t` has a cyclic rotation in the offset corridor
`[-u, 1-u]`. Its terminal point lies in the central band
`[1/3-u, 2/3-u]`. The rotation is selected by a minimum of the first `n`
partial sums when the line is increasing, and by a maximum when it is
decreasing. -/
theorem exists_offsetCorridorPath_of_linearTube_allOffsets
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j - (1 / 2 - u) * normalizedTime j| < ε) :
    ∃ k : Fin n, offsetCorridorPath u (cyclicRotatePath s k) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let m : ℝ := 1 / 2 - u
  have hmCorridorLower : m - 1 / 2 = -u := by
    dsimp [m]
    ring
  have hmCorridorUpper : m + 1 / 2 = 1 - u := by
    dsimp [m]
    ring
  have htime_nonneg (j : Fin (n + 1)) : 0 ≤ normalizedTime j :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have htime_le_one (j : Fin (n + 1)) : normalizedTime j ≤ 1 := by
    dsimp [normalizedTime]
    apply (div_le_one hnR).2
    exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hnear (j : Fin (n + 1)) :
      m * normalizedTime j - ε < s j ∧
        s j < m * normalizedTime j + ε := by
    have h := abs_lt.mp (htube j)
    change -ε < s j - m * normalizedTime j ∧
      s j - m * normalizedTime j < ε at h
    constructor <;> linarith
  have hlastTime : normalizedTime (Fin.last n) = 1 := by
    simp [normalizedTime, hnR.ne']
  have hlastNear := hnear (Fin.last n)
  rw [hlastTime] at hlastNear
  have hend : s (Fin.last n) ∈ Set.Icc (1 / 3 - u) (2 / 3 - u) := by
    simp only [Set.mem_Icc]
    constructor <;> dsimp [m] at hlastNear ⊢ <;> linarith [hε16]
  have hlastRot (k : Fin n) :
      cyclicRotatePath s k (Fin.last n) = s (Fin.last n) := by
    simpa [cyclicRotatePath] using cyclicPartialSum_last s hs0 k
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  by_cases hmNonneg : 0 ≤ m
  · obtain ⟨k, hkmin⟩ := Finite.exists_min (fun i : Fin n => s i.castSucc)
    have hkzero : s k.castSucc ≤ 0 := by
      have hk := hkmin (⟨0, hn⟩ : Fin n)
      have hz : (⟨0, hn⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp
      rw [hz, hs0] at hk
      exact hk
    have hmin_p {p : Fin (n + 1)} (hp : p.val < n) :
        s k.castSucc ≤ s p := by
      have h := hkmin (⟨p.val, hp⟩ : Fin n)
      simpa using h
    refine ⟨k, ?_⟩
    refine ⟨fun j => ?_, ?_⟩
    ·
      change cyclicPartialSum s k j ∈ Set.Icc (-u) (1 - u)
      unfold cyclicPartialSum
      split_ifs with h
      · let p : Fin (n + 1) := ⟨k.val + j.val, Nat.lt_succ_of_le h⟩
        have hpTime : normalizedTime p = normalizedTime k.castSucc + normalizedTime j := by
          simp [normalizedTime, p, Fin.val_castSucc, Nat.cast_add, add_div]
        have hdiff : normalizedTime p - normalizedTime k.castSucc = normalizedTime j := by
          linarith [hpTime]
        have hpNear := hnear p
        have hkNear := hnear k.castSucc
        have hrotLower : -u ≤ s p - s k.castSucc := by
          by_cases hp : p.val < n
          · have hmin := hmin_p hp
            have hu0 : -u ≤ 0 := by rcases hu with ⟨hu0, hu1⟩; linarith
            linarith
          · have hpEqLast : p = Fin.last n := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            rw [hpEqLast]
            have hmargin : m - 1 / 2 ≤ m - ε := by linarith [hε16]
            rw [← hmCorridorLower]
            linarith [hlastNear.1, hkzero]
        have hrotUpper : s p - s k.castSucc ≤ 1 - u := by
          have hcoeff : m * normalizedTime j ≤ m := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (htime_le_one j) hmNonneg
          calc
            s p - s k.castSucc ≤ m * normalizedTime p -
                m * normalizedTime k.castSucc + 2 * ε := by
                  nlinarith [hpNear.2, hkNear.1]
            _ = m * normalizedTime j + 2 * ε := by rw [← hdiff]; ring
            _ ≤ m + 1 / 2 := by linarith [hcoeff, hε16]
            _ = 1 - u := hmCorridorUpper
        constructor
        · dsimp [p] at hrotLower ⊢
          linarith
        · dsimp [p] at hrotUpper ⊢
          linarith
      · let p : Fin (n + 1) := ⟨k.val + j.val - n, by omega⟩
        have hpLt : p.val < n := by dsimp [p]; omega
        have hpval : p.val + n = k.val + j.val := by dsimp [p]; omega
        have hpcast : (p.val : ℝ) + (n : ℝ) =
            (k.val : ℝ) + (j.val : ℝ) := by exact_mod_cast hpval
        have hpTime : normalizedTime p + 1 =
            normalizedTime k.castSucc + normalizedTime j := by
          dsimp [normalizedTime]
          field_simp [ne_of_gt hnR]
          nlinarith [hpcast]
        have hcoeff : 1 - normalizedTime k.castSucc +
            normalizedTime p = normalizedTime j := by linarith [hpTime]
        have hpNear := hnear p
        have hkNear := hnear k.castSucc
        have hrotLower : -u ≤
            s (Fin.last n) - s k.castSucc + s p := by
          have hmin := hmin_p hpLt
          rw [← hmCorridorLower]
          have hmargin : m - 1 / 2 ≤ m - ε := by linarith [hε16]
          linarith [hlastNear.1]
        have hrotUpper :
            s (Fin.last n) - s k.castSucc + s p ≤ 1 - u := by
          have hcoeffUpper : m * normalizedTime j ≤ m := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (htime_le_one j) hmNonneg
          calc
            s (Fin.last n) - s k.castSucc + s p ≤
                m * (1 - normalizedTime k.castSucc + normalizedTime p) +
                  3 * ε := by nlinarith [hlastNear.2, hkNear.1, hpNear.2]
            _ = m * normalizedTime j + 3 * ε := by rw [hcoeff]
            _ ≤ m + 1 / 2 := by linarith [hcoeffUpper, hε16]
            _ = 1 - u := hmCorridorUpper
        constructor
        · dsimp [p] at hrotLower ⊢
          linarith
        · dsimp [p] at hrotUpper ⊢
          linarith
    · rw [hlastRot k]
      exact hend
  · have hmNonpos : m ≤ 0 := le_of_not_ge hmNonneg
    obtain ⟨k, hkmax⟩ := Finite.exists_max (fun i : Fin n => s i.castSucc)
    have hkzero : 0 ≤ s k.castSucc := by
      have hk := hkmax (⟨0, hn⟩ : Fin n)
      have hz : (⟨0, hn⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp
      rw [hz, hs0] at hk
      exact hk
    have hmax_p {p : Fin (n + 1)} (hp : p.val < n) :
        s p ≤ s k.castSucc := by
      have h := hkmax (⟨p.val, hp⟩ : Fin n)
      simpa using h
    refine ⟨k, ?_⟩
    refine ⟨fun j => ?_, ?_⟩
    ·
      change cyclicPartialSum s k j ∈ Set.Icc (-u) (1 - u)
      unfold cyclicPartialSum
      split_ifs with h
      · let p : Fin (n + 1) := ⟨k.val + j.val, Nat.lt_succ_of_le h⟩
        have hpTime : normalizedTime p = normalizedTime k.castSucc + normalizedTime j := by
          simp [normalizedTime, p, Fin.val_castSucc, Nat.cast_add, add_div]
        have hdiff : normalizedTime p - normalizedTime k.castSucc = normalizedTime j := by
          linarith [hpTime]
        have hpNear := hnear p
        have hkNear := hnear k.castSucc
        have hcoeffLower : m ≤ m * normalizedTime j := by
          have hprod := mul_nonpos_of_nonpos_of_nonneg hmNonpos
            (sub_nonneg.mpr (htime_le_one j))
          nlinarith [hprod]
        have hrotLower : -u ≤ s p - s k.castSucc := by
          rw [← hmCorridorLower]
          have hmargin : m - 1 / 2 ≤ m * normalizedTime j - 2 * ε := by
            linarith [hcoeffLower, hε16]
          calc
            m - 1 / 2 ≤ m * normalizedTime j - 2 * ε := hmargin
            _ ≤ s p - s k.castSucc := by nlinarith [hpNear.1, hkNear.2, hdiff]
        have hrotUpper : s p - s k.castSucc ≤ 1 - u := by
          by_cases hp : p.val < n
          · have hmax := hmax_p hp
            have hu1 : 0 ≤ 1 - u := by rcases hu with ⟨hu0, hu1⟩; linarith
            linarith
          · have hpEqLast : p = Fin.last n := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            rw [hpEqLast]
            rw [← hmCorridorUpper]
            have hmargin : m + ε ≤ m + 1 / 2 := by linarith [hε16]
            linarith [hlastNear.2, hkzero]
        constructor
        · dsimp [p] at hrotLower ⊢
          linarith
        · dsimp [p] at hrotUpper ⊢
          linarith
      · let p : Fin (n + 1) := ⟨k.val + j.val - n, by omega⟩
        have hpLt : p.val < n := by dsimp [p]; omega
        have hpval : p.val + n = k.val + j.val := by dsimp [p]; omega
        have hpcast : (p.val : ℝ) + (n : ℝ) =
            (k.val : ℝ) + (j.val : ℝ) := by exact_mod_cast hpval
        have hpTime : normalizedTime p + 1 =
            normalizedTime k.castSucc + normalizedTime j := by
          dsimp [normalizedTime]
          field_simp [ne_of_gt hnR]
          nlinarith [hpcast]
        have hcoeff : 1 - normalizedTime k.castSucc +
            normalizedTime p = normalizedTime j := by linarith [hpTime]
        have hpNear := hnear p
        have hkNear := hnear k.castSucc
        have hcoeffLower : m ≤ m * normalizedTime j := by
          have hprod := mul_nonpos_of_nonpos_of_nonneg hmNonpos
            (sub_nonneg.mpr (htime_le_one j))
          nlinarith [hprod]
        have hrotLower : -u ≤
            s (Fin.last n) - s k.castSucc + s p := by
          rw [← hmCorridorLower]
          have hmargin : m - 1 / 2 ≤ m * normalizedTime j - 3 * ε := by
            linarith [hcoeffLower, hε16]
          calc
            m - 1 / 2 ≤ m * normalizedTime j - 3 * ε := hmargin
            _ ≤ s (Fin.last n) - s k.castSucc + s p := by
              nlinarith [hlastNear.1, hpNear.1, hkNear.2, hcoeff]
        have hrotUpper :
            s (Fin.last n) - s k.castSucc + s p ≤ 1 - u := by
          have hmax := hmax_p hpLt
          rw [← hmCorridorUpper]
          have hmargin : m + ε ≤ m + 1 / 2 := by linarith [hε16]
          linarith [hlastNear.2, hmax]
        constructor
        · dsimp [p] at hrotLower ⊢
          linarith
        · dsimp [p] at hrotUpper ⊢
          linarith
    · rw [hlastRot k]
      exact hend

/-- The edge tube near zero has a cyclic rotation in the offset corridor. -/
theorem exists_offsetCorridorPath_of_linearTube_lowerEdge
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc 0 (1 / 10))
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j - normalizedTime j / 2| < ε) :
    ∃ k : Fin n, offsetCorridorPath u (cyclicRotatePath s k) := by
  obtain ⟨k, hpath, hend⟩ :=
    exists_cyclicPartialSum_mem_Icc_of_linearTube hn s hs0 hε hε16 htube
  have hlast := cyclicPartialSum_last s hs0 k
  refine ⟨k, ?_⟩
  rcases hu with ⟨huLower, huUpper⟩
  refine ⟨fun j => ?_, ?_⟩
  · rcases hpath j with ⟨hlo, hhi⟩
    change cyclicPartialSum s k j ∈ Set.Icc (-u) (1 - u)
    simp only [Set.mem_Icc]
    constructor <;> linarith
  · rcases hend with ⟨hlo, hhi⟩
    change cyclicPartialSum s k (Fin.last n) ∈ Set.Icc (1 / 3 - u) (2 / 3 - u)
    rw [hlast]
    simp only [Set.mem_Icc]
    constructor <;> linarith

/-- The edge tube near one has a cyclic rotation in the offset corridor. -/
theorem exists_offsetCorridorPath_of_linearTube_upperEdge
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc (9 / 10) 1)
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j + normalizedTime j / 2| < ε) :
    ∃ k : Fin n, offsetCorridorPath u (cyclicRotatePath s k) := by
  obtain ⟨k, hpath, hend⟩ :=
    exists_cyclicPartialSum_mem_Icc_of_negativeLinearTube hn s hs0 hε hε16 htube
  have hlast := cyclicPartialSum_last s hs0 k
  refine ⟨k, ?_⟩
  rcases hu with ⟨huLower, huUpper⟩
  refine ⟨fun j => ?_, ?_⟩
  · rcases hpath j with ⟨hlo, hhi⟩
    change cyclicPartialSum s k j ∈ Set.Icc (-u) (1 - u)
    simp only [Set.mem_Icc]
    constructor <;> linarith
  · rcases hend with ⟨hlo, hhi⟩
    change cyclicPartialSum s k (Fin.last n) ∈ Set.Icc (1 / 3 - u) (2 / 3 - u)
    rw [hlast]
    simp only [Set.mem_Icc]
    constructor <;> linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
