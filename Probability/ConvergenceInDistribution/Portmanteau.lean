/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Basic

public section

/-!
# Event probabilities under convergence in distribution

The public theorems are:

- `MeasureTheory.TendstoInDistribution.measure_map_le_liminf_of_isOpen`:
  $\mu'(Z\in G)\le\liminf_i\mu_i(X_i\in G)$ for open $G$.
- `MeasureTheory.TendstoInDistribution.exists_eventually_measure_map_ge_pos_of_isOpen`:
  $\mu'(Z\in G)>0$ for open $G$ gives some $q>0$ with
  $\mu_i(X_i\in G)\ge q$ eventually.
- `MeasureTheory.TendstoInDistribution.lintegral_map_le_liminf_of_continuous_nonneg`:
  the lower Portmanteau bound for a nonnegative continuous test function.
- `MeasureTheory.TendstoInDistribution.limsup_measure_map_le_of_isClosed`:
  $\limsup_i\mu_i(X_i\in F)\le\mu'(Z\in F)$ for closed $F$.
- `MeasureTheory.TendstoInDistribution.tendsto_measure_map_of_null_frontier`:
  $\mu_i(X_i\in A)\to\mu'(Z\in A)$ when the limiting law gives
  zero mass to the frontier of $A$.
-/

open Filter ProbabilityTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {I E Ω' : Type*} {Ω : I → Type*}
  {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
  [HasOuterApproxClosed E]
  {X : (i : I) → Ω i → E} {Z : Ω' → E} {l : Filter I}

/-- Portmanteau lower bound for an open event, stated for random variables
converging in distribution. -/
theorem TendstoInDistribution.measure_map_le_liminf_of_isOpen
    (h : TendstoInDistribution X l Z μ μ')
    {G : Set E} (hG : IsOpen G) :
    μ'.map Z G ≤ l.liminf (fun i => (μ i).map (X i) G) := by
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG

/-- Positive mass of an open limiting event gives one positive lower bound
for its probabilities under all sufficiently late approximating laws. -/
theorem TendstoInDistribution.exists_eventually_measure_map_ge_pos_of_isOpen
    {E Ω Ω' : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z P P')
    {G : Set E} (hG : IsOpen G) (hpos : 0 < P'.map Z G) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ (P n).map (X n) G := by
  let mass : ℝ≥0∞ := P'.map Z G
  let probability : ℕ → ℝ≥0∞ := fun n => (P n).map (X n) G
  have hportmanteau : mass ≤ atTop.liminf probability := by
    simpa [mass, probability] using h.measure_map_le_liminf_of_isOpen hG
  let q : ℝ≥0∞ := (1 / 2) * mass
  have hmassPositive : 0 < mass := by simpa [mass] using hpos
  have hqPositive : 0 < q := by
    simpa [q] using
      (ENNReal.mul_pos (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0) hmassPositive.ne')
  have hmassNeTop : mass ≠ ⊤ := measure_ne_top _ _
  have hqStrict : q < mass := by
    have hmul := ENNReal.mul_lt_mul_right (ne_of_gt hmassPositive) hmassNeTop
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
    simpa [q, mul_comm] using hmul
  have hqLiminf : q < atTop.liminf probability := hqStrict.trans_le hportmanteau
  have hprobabilityBounded : Filter.IsBoundedUnder (· ≥ ·) atTop probability :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  refine ⟨q, hqPositive, ?_⟩
  filter_upwards [eventually_lt_of_lt_liminf hqLiminf hprobabilityBounded]
    with n hn
  exact hn.le

/-- Portmanteau also transfers expectations of nonnegative continuous
real-valued test functions. This is the integral form needed when a killed
transition is tested against a positive endpoint weight instead of only the
indicator of a survival event. -/
theorem TendstoInDistribution.lintegral_map_le_liminf_of_continuous_nonneg
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : (n : ℕ) → Ω n → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z μ μ')
    {f : E → ℝ} (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ'.map Z ≤
      atTop.liminf (fun n =>
        ∫⁻ x, ENNReal.ofReal (f x) ∂(μ n).map (X n)) := by
  apply MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hfnn
  intro G hG
  exact h.measure_map_le_liminf_of_isOpen hG

/-- Portmanteau upper bound for a closed event, stated for random variables
converging in distribution. -/
theorem TendstoInDistribution.limsup_measure_map_le_of_isClosed
    (h : TendstoInDistribution X l Z μ μ')
    {F : Set E} (hF : IsClosed F) :
    l.limsup (fun i => (μ i).map (X i) F) ≤ μ'.map Z F := by
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF

/-- Event probabilities converge when the limiting law gives no mass to the
event boundary. -/
theorem TendstoInDistribution.tendsto_measure_map_of_null_frontier
    (h : TendstoInDistribution X l Z μ μ')
    {event : Set E} (hboundary : μ'.map Z (frontier event) = 0) :
    Tendsto (fun i => (μ i).map (X i) event) l
      (nhds (μ'.map Z event)) := by
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h.tendsto hboundary

end MeasureTheory
