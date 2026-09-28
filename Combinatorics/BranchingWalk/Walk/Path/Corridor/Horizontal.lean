import Combinatorics.BranchingWalk.Walk.Path.Basic

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
