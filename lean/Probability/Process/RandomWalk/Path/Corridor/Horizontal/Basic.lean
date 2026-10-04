/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window.Basic

/-!
# Horizontal corridors for deterministic walk paths

This file contains the finite, deterministic tube predicate and its order
properties.  Measurability and probabilities belong to the probability layer.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The first `n` partial sums stay in the width-`width` interval whose lower
endpoint is `-a * width`. Time zero is omitted. -/
def InHorizontalTube (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    -a * width ≤ AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤ (1 - a) * width

/-- A nonempty horizontal tube also constrains its terminal partial sum. -/
theorem InHorizontalTube.mem_endpoint {a width : ℝ} {n : ℕ}
    {increment : ℕ → ℝ} (h : InHorizontalTube a width n increment) (hn : 0 < n) :
    AdditivePath.displacement n increment ∈ Set.Icc (-a * width) ((1 - a) * width) := by
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk := h k
  have hindex : (k : ℕ) + 1 = n := by dsimp [k]; omega
  simpa [hindex] using hk

/-- The strict version of `InHorizontalTube`. -/
def InOpenHorizontalTube (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    -a * width < AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment < (1 - a) * width

/-- Staying in the centered lattice interval `1, ..., 2 * radius + 1`
from its midpoint is exactly staying in the symmetric horizontal tube of
radius `radius`.  This is the deterministic bridge from the finite-state
spectral model to the horizontal-tube formulation of Mogulskii's theorem. -/
theorem inClosedInterval_centered_iff_inHorizontalTube
    (radius n : ℕ) (increment : ℕ → ℝ) :
    InClosedInterval 1 (2 * radius + 1) n (radius + 1) increment ↔
      InHorizontalTube (1 / 2 : ℝ) (2 * radius) n increment := by
  simp only [InClosedInterval, InWindows, history_eq_fromIncrements,
    AdditivePath.fromIncrements, Set.mem_Icc, InHorizontalTube]
  constructor
  · intro h k
    have hk := h ⟨k + 1, by omega⟩
    push_cast at hk ⊢
    constructor <;> linarith
  · intro h k
    by_cases hk : (k : ℕ) = 0
    · rw [hk]
      simp only [AdditivePath.displacement_zero, add_zero]
      have hradius : (0 : ℝ) ≤ radius := by positivity
      constructor
      · linarith
      · linarith
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hjlt : j < n := by omega
      have htube := h ⟨j, hjlt⟩
      change -(1 / 2 : ℝ) * (2 * radius) ≤
          AdditivePath.displacement (j + 1) increment ∧
        AdditivePath.displacement (j + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * radius) at htube
      rw [hj]
      constructor <;> linarith

theorem InOpenHorizontalTube.closed {a width : ℝ} {n : ℕ}
    {increment : ℕ → ℝ} (h : InOpenHorizontalTube a width n increment) :
    InHorizontalTube a width n increment := by
  intro k
  exact ⟨(h k).1.le, (h k).2.le⟩

/-- A strict centered tube of positive length stays in every wider closed
centered interval and ends in the closed interval determined by its own
width.  This is the deterministic event inclusion used to turn functional
limit estimates into killed return-kernel estimates. -/
theorem InOpenHorizontalTube.staysIn_and_endpoint_centeredIcc
    {innerWidth outerWidth : ℝ} {n : ℕ} {increment : ℕ → ℝ}
    (h : InOpenHorizontalTube (1 / 2) innerWidth n increment)
    (hn : 0 < n) (hwidth : innerWidth ≤ outerWidth) :
    StaysIn (Set.Icc (-(outerWidth / 2)) (outerWidth / 2)) n 0 increment ∧
      AdditivePath.displacement n increment ∈
        Set.Icc (-(innerWidth / 2)) (innerWidth / 2) := by
  constructor
  · intro k
    have hk := h k
    simp only [zero_add]
    change -(outerWidth / 2) ≤ AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤ outerWidth / 2
    norm_num at hk
    constructor <;> nlinarith
  · have hend := h ⟨n - 1, by omega⟩
    have hsucc : n - 1 + 1 = n := by omega
    rw [hsucc] at hend
    change -(innerWidth / 2) ≤ AdditivePath.displacement n increment ∧
      AdditivePath.displacement n increment ≤ innerWidth / 2
    norm_num at hend
    ring_nf at hend ⊢
    exact ⟨hend.1.le, hend.2.le⟩

/-- A centered tube around the increment path controls a walk started from
any point in a centered initial interval.  The initial width is added to the
path width in the outer and terminal containment conditions. -/
theorem InOpenHorizontalTube.staysIn_and_endpoint_centeredIcc_from
    {pathWidth initialWidth outerWidth returnWidth : ℝ} {n : ℕ}
    {initial : ℝ} {increment : ℕ → ℝ}
    (h : InOpenHorizontalTube (1 / 2) pathWidth n increment)
    (hn : 0 < n)
    (hinitial : initial ∈ Set.Icc (-(initialWidth / 2)) (initialWidth / 2))
    (houter : initialWidth + pathWidth ≤ outerWidth)
    (hreturn : initialWidth + pathWidth ≤ returnWidth) :
    StaysIn (Set.Icc (-(outerWidth / 2)) (outerWidth / 2))
        n initial increment ∧
      initial + AdditivePath.displacement n increment ∈
        Set.Icc (-(returnWidth / 2)) (returnWidth / 2) := by
  have hpath := h.staysIn_and_endpoint_centeredIcc hn le_rfl
  constructor
  · intro k
    have hk := hpath.1 k
    have hi := hinitial
    constructor <;> nlinarith [hi.1, hi.2, hk.1, hk.2]
  · have hi := hinitial
    have hend := hpath.2
    constructor <;> nlinarith [hi.1, hi.2, hend.1, hend.2]

/-- Reflection of every increment exchanges the two horizontal-tube
parameters `a` and `1 - a`. -/
theorem inHorizontalTube_neg_iff (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    InHorizontalTube (1 - a) width n (fun k => -increment k) ↔
      InHorizontalTube a width n increment := by
  constructor <;> intro h k
  · have hk := h k
    rw [AdditivePath.displacement_neg] at hk
    constructor <;> linarith
  · have hk := h k
    rw [AdditivePath.displacement_neg]
    constructor <;> linarith

/-- Dividing every increment and the tube width by the same positive
constant preserves the horizontal-tube event. -/
theorem inHorizontalTube_div_iff
    (a width : ℝ) (n : ℕ) (increment : ℕ → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    InHorizontalTube a (width / sigma) n (fun k => increment k / sigma) ↔
      InHorizontalTube a width n increment := by
  have hsum (m : ℕ) :
      AdditivePath.displacement m (fun k => increment k / sigma) =
        AdditivePath.displacement m increment / sigma := by
    simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  simp only [InHorizontalTube]
  constructor <;> intro h k
  · have hk := h k
    rw [hsum,
      show -a * (width / sigma) = (-a * width) / sigma by ring,
      show (1 - a) * (width / sigma) = ((1 - a) * width) / sigma by ring]
      at hk
    exact ⟨(div_le_div_iff_of_pos_right hsigma).mp hk.1,
      (div_le_div_iff_of_pos_right hsigma).mp hk.2⟩
  · have hk := h k
    rw [hsum,
      show -a * (width / sigma) = (-a * width) / sigma by ring,
      show (1 - a) * (width / sigma) = ((1 - a) * width) / sigma by ring]
    exact ⟨(div_le_div_iff_of_pos_right hsigma).mpr hk.1,
      (div_le_div_iff_of_pos_right hsigma).mpr hk.2⟩

/-- Dividing every increment and the tube width by the same positive
constant preserves the strict horizontal-tube event. -/
theorem inOpenHorizontalTube_div_iff
    (a width : ℝ) (n : ℕ) (increment : ℕ → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    InOpenHorizontalTube a (width / sigma) n
        (fun k => increment k / sigma) ↔
      InOpenHorizontalTube a width n increment := by
  have hsum (m : ℕ) :
      AdditivePath.displacement m (fun k => increment k / sigma) =
        AdditivePath.displacement m increment / sigma := by
    simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  simp only [InOpenHorizontalTube]
  constructor <;> intro h k
  · have hk := h k
    rw [hsum,
      show -a * (width / sigma) = (-a * width) / sigma by ring,
      show (1 - a) * (width / sigma) = ((1 - a) * width) / sigma by ring]
      at hk
    exact ⟨(div_lt_div_iff_of_pos_right hsigma).mp hk.1,
      (div_lt_div_iff_of_pos_right hsigma).mp hk.2⟩
  · have hk := h k
    rw [hsum,
      show -a * (width / sigma) = (-a * width) / sigma by ring,
      show (1 - a) * (width / sigma) = ((1 - a) * width) / sigma by ring]
    exact ⟨(div_lt_div_iff_of_pos_right hsigma).mpr hk.1,
      (div_lt_div_iff_of_pos_right hsigma).mpr hk.2⟩

/-- Enlarging a horizontal tube increases its path event. -/
theorem inHorizontalTube_mono_width
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    {increment : ℕ → ℝ | InHorizontalTube a width₁ n increment} ⊆
      {increment | InHorizontalTube a width₂ n increment} := by
  intro increment hin k
  have hk := hin k
  constructor <;> nlinarith

end ProbabilityTheory.RandomWalk
