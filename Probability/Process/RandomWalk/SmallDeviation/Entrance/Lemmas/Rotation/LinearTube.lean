/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Order.Filter.IsBounded
import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.Path.Linear
import Algebra.BigOperators.PartialSum

/-!
# Cyclic rotations of a path near an increasing line

## Internal proof declarations

The finite-path definitions and geometry lemmas used by the normal-domain
entrance proof are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.normalizedTime j =
  j.val / n`, `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.cyclicRotatePath s k j =
  Fin.cyclicPartialSum s k j`, and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.offsetCorridorPath u s` means
  $s_j\in[-u,1-u]$ for every $j\in[0,n]$ and
  $s_n\in[1/3-u,2/3-u]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_cyclicPartialSum_mem_Icc_of_linearTube`:
  if $n>0$, $s_0=0$, $0<\varepsilon<1/16$, and
  $|s_j-j/(2n)|<\varepsilon$ at every knot, then some cyclic rotation
  has all knots in $[0,3/4]$ and terminal value in $[7/16,9/16]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_offsetCorridorPath_of_linearTube_allOffsets`:
  if $n>0$,
  $u\in[0,1]$, $s_0=0$, and
  $|s_j-(1/2-u)j/n|<\varepsilon<1/16$ at every knot, then some cyclic
  rotation has all knots in $[-u,1-u]$ and terminal value in
  $[1/3-u,2/3-u]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_offsetCorridorPath_of_linearTube_lowerEdge`:
  if $u\in[0,1/10]$, $0<\varepsilon<1/16$, and the knots satisfy the
  preceding $t/2$-tube condition, they have a
  cyclic rotation in the same offset corridor.

The all-offset result chooses a minimum or maximum of the finite partial-sum
path according to the sign of the reference slope. The fixed-slope case is
used for the lower-edge entrance estimate.

These finite-path constructions and covers support Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7, used in
the proof of Chapter 3, Lemma 3.5. General cyclic-sum identities remain at
`Algebra.BigOperators.CyclicReindex`.
-/

section

open scoped BigOperators
open MeasureTheory Fin

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

noncomputable def normalizedTime {n : ℕ} (j : Fin (n + 1)) : ℝ :=
  (j.val : ℝ) / (n : ℝ)

/-- The path produced by cyclically rotating the increments encoded by `s`. -/
def cyclicRotatePath {n : ℕ} (s : Fin (n + 1) → ℝ) (k : Fin n) :
    Fin (n + 1) → ℝ :=
  fun j => cyclicPartialSum s k j

/-- The static offset corridor and its central terminal band. -/
def offsetCorridorPath {n : ℕ} (u : ℝ) (s : Fin (n + 1) → ℝ) : Prop :=
  (∀ j, s j ∈ Set.Icc (-u) (1 - u)) ∧
    s (Fin.last n) ∈ Set.Icc (1 / 3 - u) (2 / 3 - u)

/-- A path starting at zero and uniformly within `ε < 1/16` of `t ↦ t/2`
has a cyclic rotation whose partial sums stay in `[0, 3/4]`.  Its terminal
sum lies in the central interval `[7/16, 9/16]`. -/
lemma exists_cyclicPartialSum_mem_Icc_of_linearTube
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
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
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

/-- A path starting at zero and uniformly close to the offset-dependent line
`t ↦ (1/2 - u) * t` has a cyclic rotation in the offset corridor
`[-u, 1-u]`. Its terminal point lies in the central band
`[1/3-u, 2/3-u]`. The rotation is selected by a minimum of the first `n`
partial sums when the line is increasing, and by a maximum when it is
decreasing. -/
lemma exists_offsetCorridorPath_of_linearTube_allOffsets
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
    simpa [cyclicRotatePath] using Fin.cyclicPartialSum_last_eq_of_zero s hs0 k
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
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
lemma exists_offsetCorridorPath_of_linearTube_lowerEdge
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc 0 (1 / 10))
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |s j - normalizedTime j / 2| < ε) :
    ∃ k : Fin n, offsetCorridorPath u (cyclicRotatePath s k) := by
  obtain ⟨k, hpath, hend⟩ :=
    exists_cyclicPartialSum_mem_Icc_of_linearTube hn s hs0 hε hε16 htube
  have hlast := Fin.cyclicPartialSum_last_eq_of_zero s hs0 k
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
