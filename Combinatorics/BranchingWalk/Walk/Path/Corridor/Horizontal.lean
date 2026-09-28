import Combinatorics.BranchingWalk.Walk.Path.Window

/-!
# Horizontal corridors for deterministic walk paths

This file contains the finite, deterministic tube predicate and its order
properties.  Measurability and probabilities belong to the probability layer.
-/

namespace Combinatorics.Branching.Walk

/-- The first `n` partial sums stay in the width-`width` interval whose lower
endpoint is `-a * width`. Time zero is omitted. -/
def InHorizontalTube (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    -a * width ≤ partialSum (k + 1) increment ∧
      partialSum (k + 1) increment ≤ (1 - a) * width

/-- The strict version of `InHorizontalTube`. -/
def InOpenHorizontalTube (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    -a * width < partialSum (k + 1) increment ∧
      partialSum (k + 1) increment < (1 - a) * width

/-- Staying in the centered lattice interval `1, ..., 2 * radius + 1`
from its midpoint is exactly staying in the symmetric horizontal tube of
radius `radius`.  This is the deterministic bridge from the finite-state
spectral model to the horizontal-tube formulation of Mogulskii's theorem. -/
theorem inClosedInterval_centered_iff_inHorizontalTube
    (radius n : ℕ) (increment : ℕ → ℝ) :
    InClosedInterval 1 (2 * radius + 1) n (radius + 1) increment ↔
      InHorizontalTube (1 / 2 : ℝ) (2 * radius) n increment := by
  simp only [InClosedInterval, InWindows, history, Set.mem_Icc,
    InHorizontalTube]
  constructor
  · intro h k
    have hk := h ⟨k + 1, by omega⟩
    push_cast at hk ⊢
    constructor <;> linarith
  · intro h k
    by_cases hk : (k : ℕ) = 0
    · rw [hk]
      simp only [partialSum_zero, add_zero]
      have hradius : (0 : ℝ) ≤ radius := by positivity
      constructor
      · linarith
      · linarith
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hjlt : j < n := by omega
      have htube := h ⟨j, hjlt⟩
      change -(1 / 2 : ℝ) * (2 * radius) ≤
          partialSum (j + 1) increment ∧
        partialSum (j + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * radius) at htube
      rw [hj]
      constructor <;> linarith

theorem InOpenHorizontalTube.closed {a width : ℝ} {n : ℕ}
    {increment : ℕ → ℝ} (h : InOpenHorizontalTube a width n increment) :
    InHorizontalTube a width n increment := by
  intro k
  exact ⟨(h k).1.le, (h k).2.le⟩

/-- Reflection of every increment exchanges the two horizontal-tube
parameters `a` and `1 - a`. -/
theorem inHorizontalTube_neg_iff (a width : ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    InHorizontalTube (1 - a) width n (fun k => -increment k) ↔
      InHorizontalTube a width n increment := by
  constructor <;> intro h k
  · have hk := h k
    rw [partialSum_neg] at hk
    constructor <;> linarith
  · have hk := h k
    rw [partialSum_neg]
    constructor <;> linarith

/-- Enlarging a horizontal tube increases its path event. -/
theorem inHorizontalTube_mono_width
    {a width₁ width₂ : ℝ} {n : ℕ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : width₁ ≤ width₂) :
    {increment : ℕ → ℝ | InHorizontalTube a width₁ n increment} ⊆
      {increment | InHorizontalTube a width₂ n increment} := by
  intro increment hin k
  have hk := hin k
  constructor <;> nlinarith

end Combinatorics.Branching.Walk
