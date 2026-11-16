/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.FiniteVariance
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.FirstMoment
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Sequence
import Probability.MeasureTheory.Convergence.SecondMoment.FromPolynomialTails
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.PositiveInitialExponent
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Monotonicity
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.SingleRoot

/-!
# Endpoint convergence from the upper-tail estimate

## Public declarations

* `tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub` is the
  trajectory limit in Wang Yiyang's Theorem 1.1. With $a\in[0,1]$,
  $m_N=\lfloor N^a\rfloor$, and $H_N/\log^3N\to t>0$, the limit is
  $M_{H_N}/\log N\to -a+\pi^2\sigma^2t/2$ in $L^2$.
  The positive exponential moment of the leftmost displacement is required
  when $a=0$.
* `tendsto_integral_countableRootEndpointMinimum_div` gives the corresponding
  normalized expectation limit $\mathbb E[M_{H_N}/\log N]\to -a+\pi^2\sigma^2t/2$.
* `tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_initialExponent`:
  for the initial population $m_n=\lfloor N_n^a\rfloor$ at $0<a<1$, the
  model's centered-spine, cross-weight, and leftmost fourth-moment
  assumptions give $\left\|M_n/\log N_n-c\right\|_{L^2}\to0$ with
  $c=-a+\frac{\pi^2}{2}\sigma^2t$.
* `tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_singleRoot`:
  from a single zero-position root,
  $M_n/\log N_n\to\pi^2\sigma^2t/2$ in $L^2$ under the additional
  positive exponential-moment assumption of Theorem 1.1.
* `tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_fullCapacity`:
  from $N_n$ zero-position roots with lexicographic address order,
  $M_n/\log N_n\to-1+\pi^2\sigma^2t/2$ in $L^2$.

* `tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_upperTail`:
  write $c=-a+\frac{\pi^2}{2}\sigma^2t$ and $M_n$ for the selected minimum
  at generation $H_n$ from $m_n$ zero-position roots at capacity $N_n$.
  Under the finite-variance spine and fourth-moment hypotheses,
  $H_n/(\log N_n)^3\to t>0$ and $1\le m_n\le N_n^a$ eventually,
  a polynomial upper-tail estimate at $(c+\varepsilon)\log N_n$ for
  every $\varepsilon>0$ implies
  $\left\|M_n/\log N_n-c\right\|_{L^2}\to0$ on the common root-field law.

The lower tail and growing fourth moment are proved in the respective
endpoint modules. This is the final moment argument of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Moment step in the proof of Theorem 1.1, Chapter 4 of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026). A polynomial upper tail completes the two-sided
tail argument for convergence in $L^2$. -/
theorem tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_upperTail
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 ≤ a) (ht : 0 < t)
    {m N H : ℕ → ℕ}
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (hm : ∀ n, 0 < m n) (hcapacity : ∀ n, 0 < N n)
    (hmN : ∀ᶠ n in atTop, m n ≤ N n)
    (hma : ∀ᶠ n in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    let endpoint := fun n => @countableRootEndpointMinimum (m n) (N n) (H n) (horder n)
    (∀ ε : ℝ, 0 < ε → ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
        P {field | (c + ε) * Real.log (N n : ℝ) ≤ endpoint n field} ≤
          ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ)))) →
    Tendsto (fun n => eLpNorm (fun field => endpoint n field / Real.log (N n : ℝ) - c)
      2 P) atTop (𝓝 0) := by
  intro P c endpoint hupper
  let logN (n : ℕ) := Real.log (N n : ℝ)
  let X (n : ℕ) (field : CountableRootStepField ℕ ℝ) := endpoint n field / logN n
  have hlogN : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hmem (n : ℕ) : MemLp (fun field => X n field - c) 4 P := by
    by_cases hz : logN n = 0
    · simpa only [X, hz, div_zero, zero_sub] using (memLp_const (-c) (μ := P) (p := 4))
    · let _ := horder n
      exact (countableRootEndpointMinimum_div_sub_memLp_four_and_integral_bound
        (m n) (N n) (H n) (hm n) (hcapacity n) L hboundary hnonempty hfour (logN n) c hz).1
  have hmeas (n : ℕ) : Measurable (X n) := by
    let _ := horder n
    exact (measurable_countableRootEndpointMinimum (m n) (N n) (H n)).div_const _
  have hlogm : ∀ᶠ n in atTop, Real.log (m n : ℝ) ≤ a * logN n := by
    filter_upwards [hma] with n hn
    have hpos : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast hcapacity n
    simpa only [logN, Real.log_rpow hpos] using Real.log_le_log (by exact_mod_cast hm n) hn
  apply tendsto_eLpNorm_two_sub_const_zero_of_polynomial_tails_log_fourth_moment_of_scale
    8 P X c (fun n => (N n : ℝ)) (tendsto_natCast_atTop_atTop.comp hN) hmeas hmem
  · have hpow (r : ℝ) : r ^ (8 : ℝ) = r ^ (8 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast r 8
    simpa only [hpow] using
      eventually_countableRootEndpointMinimum_div_sub_integral_fourth_le_log_eighth
        horder L hboundary hnonempty hfour (c := c) hN hH (Eventually.of_forall hm) hlogm
  · intro ε hε
    let lower (n : ℕ) := (c - ε) * logN n
    have hlowerScale : Tendsto (fun n => lower n / logN n) atTop (𝓝 (c - ε)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hlogN.eventually_gt_atTop 0] with n hn
      exact (mul_div_cancel_right₀ _ hn.ne').symm
    let _ := tiltedPotentialLaw_isProbability realPotential L.sortedPotentialImage
      (L.sortedPotentialImage_hasBoundaryNormalization hboundary)
    obtain ⟨p₁, hp₁, h₁⟩ :=
      eventually_countableRootEndpointMinimum_le_polynomial_of_centeredFiniteVariance
        L.sortedPotentialImage (L.sortedPotentialImage_hasBoundaryNormalization hboundary)
        (by rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty])
        _ rfl hsigma hspine horder hN hH hlowerScale ht ha hmN (Eventually.of_forall hm) hma
        (show c - ε < c by linarith)
    obtain ⟨p₂, hp₂, h₂⟩ := hupper ε hε
    let p := min p₁ p₂
    refine ⟨2, p, by norm_num, lt_min hp₁ hp₂, ?_⟩
    filter_upwards [h₁, h₂, hlogN.eventually_gt_atTop 0] with n hn₁ hn₂ hn
    have hle : {field | X n field - c ≤ -ε} = {field | endpoint n field ≤ lower n} := by
      ext field
      change (X n field - c ≤ -ε) ↔ (endpoint n field ≤ (c - ε) * logN n)
      rw [← div_le_iff₀ hn]
      dsimp [X]
      constructor <;> intro h <;> linarith
    have hge : {field | ε ≤ X n field - c} =
        {field | (c + ε) * logN n ≤ endpoint n field} := by
      ext field
      change (ε ≤ X n field - c) ↔ ((c + ε) * logN n ≤ endpoint n field)
      rw [← le_div_iff₀ hn]
      dsimp [X]
      constructor <;> intro h <;> linarith
    have hscalePos : (0 : ℝ) < N n := by exact_mod_cast hcapacity n
    have hexp (q : ℝ) (hq : p ≤ q) : Real.exp (-q * logN n) ≤ 1 / (N n : ℝ) ^ p := by
      calc
        _ ≤ Real.exp (-p * logN n) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hq) hn.le)
        _ = 1 / (N n : ℝ) ^ p := by
          rw [Real.rpow_def_of_pos hscalePos, one_div, ← Real.exp_neg]
          congr 1
          ring
    have toReal_bound (s : Set (CountableRootStepField ℕ ℝ)) (q : ℝ)
        (hb : P s ≤ ENNReal.ofReal (Real.exp (-q * logN n))) :
        P.real s ≤ Real.exp (-q * logN n) := by
      simpa only [Measure.real, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [hle, hge]
    calc
      P.real (_ ∪ _) ≤ P.real {field | (c + ε) * logN n ≤ endpoint n field} +
          P.real {field | endpoint n field ≤ lower n} := measureReal_union_le _ _
      _ ≤ Real.exp (-p₂ * logN n) + Real.exp (-p₁ * logN n) :=
        add_le_add (toReal_bound _ _ hn₂) (toReal_bound _ _ hn₁)
      _ ≤ 2 / (N n : ℝ) ^ p := by
        have h := add_le_add (hexp p₂ (min_le_right _ _)) (hexp p₁ (min_le_left _ _))
        exact h.trans_eq (by ring)

/-- The case $0<a<1$ of Theorem 1.1, Chapter 4 of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026). The normalization is on the common root-field law. -/
theorem tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_initialExponent
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    {N H : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => eLpNorm (fun field =>
      @countableRootEndpointMinimum (Nat.floor ((N n : ℝ) ^ a)) (N n) (H n) (horder n) field /
        Real.log (N n : ℝ) - c) 2 P) atTop (𝓝 0) := by
  intro P c
  let m (n : ℕ) := Nat.floor ((N n : ℝ) ^ a)
  have hone (n : ℕ) : (1 : ℝ) ≤ (N n : ℝ) := by
    exact_mod_cast hcapacity n
  have hm (n : ℕ) : 0 < m n := by
    apply Nat.floor_pos.mpr
    exact Real.one_le_rpow (hone n) ha.le
  have hma (n : ℕ) : (m n : ℝ) ≤ (N n : ℝ) ^ a :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmN (n : ℕ) : m n ≤ N n := by
    have hle := Real.rpow_le_rpow_of_exponent_le (hone n) ha1.le
    rw [Real.rpow_one] at hle
    exact_mod_cast (hma n).trans hle
  apply tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_upperTail
    L hboundary hnonempty hfour hsigma hspine ha.le ht horder hm hcapacity
    (Eventually.of_forall hmN) (Eventually.of_forall hma) hN hH
  intro ε hε
  exact eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent hN
    L.sortedPotentialImage (L.sortedPotentialImage_hasBoundaryNormalization hboundary)
    (L.sortedPotentialImage_hasFiniteCrossWeight hboundary hcross)
    hsigma hspine ha ha1 ht (show c < c + ε by linarith) hH horder

noncomputable local instance endpointAddressOrder (m : ℕ) :
    LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

/-- The case $a=0$ of Theorem 1.1 in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4. The upper tail uses the logarithmic entrance, and the lower tail
and fourth moment give convergence in $L^2$. -/
theorem tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_singleRoot
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    (hexp : HasLeftmostPositiveExponentialMoment L)
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ht : 0 < t) {N H : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let c := (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => eLpNorm (fun field =>
      countableRootEndpointMinimum 1 (N n) (H n) field / Real.log (N n : ℝ) - c)
      2 P) atTop (𝓝 0) := by
  intro P c
  have hlimit := tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_upperTail
    L hboundary hnonempty hfour hsigma hspine (a := 0) le_rfl ht
    (m := fun _ => 1) (fun _ => endpointAddressOrder 1) (fun _ => by decide) hcapacity
    (Eventually.of_forall hcapacity) (Eventually.of_forall (fun _ => by simp)) hN hH
  apply (by simpa only [neg_zero, zero_add] using hlimit)
  intro ε hε
  exact eventually_singleRootEndpointMinimum_ge_le_polynomial L hboundary hcross hsuper hnonempty
    hexp hsigma hspine hN ht hH (by linarith)

/-- The case $a=1$ of Theorem 1.1 in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4. The upper tail uses the monotone comparison with the process
started from $\lfloor N^b\rfloor$ roots for $b<1$ close to one. -/
theorem tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_fullCapacity
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ht : 0 < t) {N H : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let c := -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => eLpNorm (fun field =>
      countableRootEndpointMinimum (N n) (N n) (H n) field / Real.log (N n : ℝ) - c)
      2 P) atTop (𝓝 0) := by
  intro P c
  have hboundaryμ := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hcrossμ := L.sortedPotentialImage_hasFiniteCrossWeight hboundary hcross
  have hnonemptyμ : L.sortedPotentialImage nonemptySupport = 1 := by
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  apply tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_upperTail
    L hboundary hnonempty hfour hsigma hspine (a := 1) zero_le_one ht
    (fun _ => inferInstance) hcapacity hcapacity (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => by rw [Real.rpow_one]) hN hH
  intro ε hε
  let d := min (1 / 2 : ℝ) (ε / 4)
  let b := 1 - d
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hb : 0 < b := by dsimp [b]; linarith [show d ≤ 1 / 2 from min_le_left _ _]
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hgap : -b + Real.pi ^ 2 / 2 * sigma ^ 2 * t < c + ε / 2 := by
    dsimp [b, c]
    linarith [show d ≤ ε / 4 from min_le_right _ _]
  obtain ⟨p, hp, hupper⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent hN
      L.sortedPotentialImage hboundaryμ hcrossμ hsigma hspine hb hb1 ht hgap hH
      (fun _ => inferInstance)
  refine ⟨p, hp, ?_⟩
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [hupper, hlog.eventually_gt_atTop 0] with n hup hlogn
  let m := Nat.floor ((N n : ℝ) ^ b)
  let x := (c + ε / 2) * Real.log (N n : ℝ)
  let y := (c + ε) * Real.log (N n : ℝ)
  let small := countableRootEndpointMinimum m (N n) (H n)
  let large := countableRootEndpointMinimum (N n) (N n) (H n)
  have hN1 : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hcapacity n
  have hm : 0 < m := Nat.floor_pos.mpr (Real.one_le_rpow hN1 hb.le)
  have hmN : m ≤ N n := by
    apply Nat.floor_le_of_le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hb1.le
  have hmono := measure_countableRootEndpointMinimum_le_mono_roots L.sortedPotentialImage
    hboundaryμ hnonemptyμ hm hmN (hcapacity n) (H n) x
  have hsmall : MeasurableSet {field | small field ≤ x} :=
    (measurable_countableRootEndpointMinimum m (N n) (H n)) measurableSet_Iic
  have hlarge : MeasurableSet {field | large field ≤ x} :=
    (measurable_countableRootEndpointMinimum (N n) (N n) (H n)) measurableSet_Iic
  have hxy : x < y := mul_lt_mul_of_pos_right (by linarith) hlogn
  change P {field | y ≤ large field} ≤ _
  calc
    _ ≤ P {field | large field ≤ x}ᶜ := by
      apply measure_mono
      intro field hf hle
      exact hxy.not_ge ((show y ≤ large field from hf).trans hle)
    _ ≤ P {field | small field ≤ x}ᶜ := by
      rw [prob_compl_eq_one_sub hlarge, prob_compl_eq_one_sub hsmall]
      exact tsub_le_tsub_left hmono _
    _ ≤ P {field | x ≤ small field} := by
      apply measure_mono
      intro field hf
      change x ≤ small field
      exact le_of_lt (lt_of_not_ge (show ¬ small field ≤ x from hf))
    _ ≤ _ := hup

/-- The trajectory limit of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Theorem 1.1. The number of initial particles is $\lfloor N^a\rfloor$
and every initial position is zero. The additional exponential moment
is assumed only in the single-root case. -/
theorem tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (ht : 0 < t)
    (hexp : a = 0 → HasLeftmostPositiveExponentialMoment L)
    {N H : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
    Tendsto (fun n => eLpNorm (fun field =>
      @countableRootEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n)
        (RootIndexed.addressLinearOrder (Fin ⌊(N n : ℝ) ^ a⌋₊) ℕ) field /
        Real.log (N n : ℝ) - c) 2 P) atTop (𝓝 0) := by
  intro P c
  let endpoint (m : ℕ → ℕ) n :=
    @countableRootEndpointMinimum (m n) (N n) (H n)
      (RootIndexed.addressLinearOrder (Fin (m n)) ℕ)
  change Tendsto (fun n => eLpNorm (fun field =>
    endpoint (fun k => ⌊(N k : ℝ) ^ a⌋₊) n field / Real.log (N n : ℝ) - c) 2 P)
    atTop (𝓝 0)
  rcases ha.1.eq_or_lt with hzero | hpos
  · subst a
    have hm : (fun n => ⌊(N n : ℝ) ^ (0 : ℝ)⌋₊) = fun _ => 1 := by
      funext n
      rw [Real.rpow_zero, Nat.floor_one]
    rw [hm]
    simpa [c, P, endpoint] using
      tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_singleRoot
        L hboundary hnonempty hsuper hcross hfour (hexp rfl) hsigma hspine ht hcapacity hN hH
  rcases ha.2.eq_or_lt with hone | hlt
  · subst a
    have hm : (fun n => ⌊(N n : ℝ) ^ (1 : ℝ)⌋₊) = N := by
      funext n
      rw [Real.rpow_one, Nat.floor_natCast]
    rw [hm]
    simpa [c, P, endpoint] using
      tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_fullCapacity
        L hboundary hnonempty hcross hfour hsigma hspine ht hcapacity hN hH
  exact tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_initialExponent
    L hboundary hnonempty hcross hfour hsigma hspine hpos hlt ht hcapacity hN hH
    (fun n => RootIndexed.addressLinearOrder (Fin ⌊(N n : ℝ) ^ a⌋₊) ℕ)

/-- The normalized endpoint expectation in Wang Yiyang, Theorem 1.1. -/
theorem tendsto_integral_countableRootEndpointMinimum_div
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hfour : HasLeftmostFourthMoment L)
    {sigma a t : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (sigma ^ 2))
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (ht : 0 < t)
    (hexp : a = 0 → HasLeftmostPositiveExponentialMoment L)
    {N H : ℕ → ℕ} (hcapacity : ∀ n, 0 < N n)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    Tendsto (fun n => ∫ field,
      @countableRootEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n)
        (RootIndexed.addressLinearOrder (Fin ⌊(N n : ℝ) ^ a⌋₊) ℕ) field /
        Real.log (N n : ℝ) ∂P) atTop (𝓝 (-a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t)) := by
  intro P
  let c := -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
  let m := fun n => ⌊(N n : ℝ) ^ a⌋₊
  let F (n : ℕ) (field : CountableRootStepField ℕ ℝ) :=
    @countableRootEndpointMinimum (m n) (N n) (H n)
      (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / Real.log (N n : ℝ)
  change Tendsto (fun n => ∫ field, F n field ∂P) atTop (𝓝 c)
  have hL2 : Tendsto (fun n => eLpNorm (F n - fun _ => c) 2 P) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub L hsuper hnonempty
      hboundary hcross hfour hsigma hspine ha ht hexp hcapacity hN hH
  have hL1 : Tendsto (fun n => eLpNorm (F n - fun _ => c) 1 P) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
      (fun _ => bot_le)
    intro n
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hF (n : ℕ) : Integrable (F n) P := by
    let _ := RootIndexed.addressLinearOrder (Fin (m n)) ℕ
    have hone : (1 : ℝ) ≤ N n := by exact_mod_cast hcapacity n
    have hm : 0 < m n := Nat.floor_pos.mpr (Real.one_le_rpow hone ha.1)
    have hfinite := finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
      (m n) (N n) (H n) hm (hcapacity n) L hboundary hnonempty
      (fourthMoment_implies_firstMoment L hfour)
    have hpreserving := RootIndexed.StepField.measurePreserving_first L.sortedPotentialImage (m n)
    exact (hpreserving.integrable_comp_of_integrable hfinite).div_const _
  simpa using tendsto_integral_of_L1' (fun _ => c) (Eventually.of_forall hF) hL1

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
