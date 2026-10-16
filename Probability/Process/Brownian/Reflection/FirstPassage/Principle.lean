/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassage.Approximation
public import Probability.Process.Brownian.Marginal.Gaussian
public import Probability.Distributions.Gaussian.Sign
public import Probability.Process.Path.FirstPassage.Reflection
public import Probability.Process.Path.Extrema.RunningMinimum

/-!
# Brownian first-passage reflection principle

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_hitAndAbove_eq_below`:
  for $a<0$, the probability of hitting $(-\infty,a]$ by time $1$
  and ending above $a$ equals the probability of ending below $a$.
- `ProbabilityTheory.IsBrownianReal.measure_firstPassageBelow_le_one`:
  for $a<0$, the probability of passage by time $1$ is twice the
  probability of a Brownian endpoint below $a$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_le_one`:
  the same probability identity for the running minimum at time $1$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_le`:
  for $t>0$ and $a<0$, $\mathbb P(m(t)\le a)=2\mathbb P(B(t)<a)$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_lt`:
  for $t>0$ and $a<0$, $\mathbb P(m(t)<a)=2\mathbb P(B(t)<a)$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_eq_of_neg`:
  for $t>0$ and $a<0$, $\mathbb P(m(t)=a)=0$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_eq`:
  for $t>0$ and every $a\in\mathbb R$, $\mathbb P(m(t)=a)=0$.
- `ProbabilityTheory.IsBrownianReal.measure_runningMinimum_lt_zero`:
  for $t>0$, $\mathbb P(m(t)<0)=1$.

This is the event form of the reflection principle in Theorem 2.1 of
S. J. Dilworth and Duncan Wright, *A direct proof of the reflection
principle for Brownian motion*, Theory Stoch. Process. 21(37):2 (2016),
1--3, arXiv:1810.01783. The same reflection principle underlies the
Lévy identity cited in Lemma 2.3 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- Brownian paths hitting a negative level by time `1` and ending above
it have the same probability as paths ending below it. -/
theorem IsBrownianReal.measure_hitAndAbove_eq_below
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ 1 ∧ a < f 1} =
      μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    reflectAfter f (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA
  let U : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1 ∧ a < f 1}
  let L : Set C(ℝ≥0, ℝ) := {f | f 1 < a}
  have hU : MeasurableSet U := by
    exact ((measurable_firstPassageBelow a) measurableSet_Iic).inter
      ((ContinuousMap.measurable_eval 1) measurableSet_Ioi)
  have hF : Measurable F := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        (min (firstPassageBelow f a) (1 : WithTop ℝ≥0)).untopA) :=
      ((measurable_firstPassageBelow a).min measurable_const).untopA
    exact measurable_reflectAfter_pair.comp (measurable_id.prodMk hT)
  have h0orig : ∀ᵐ ω ∂P, a < hB.continuousPathMap hBmeasurable ω 0 := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.eval_zero_ae_eq_zero] with ω hpath hzero
    rw [hpath 0, hzero]
    exact ha
  have h0meas : MeasurableSet {f : C(ℝ≥0, ℝ) | a < f 0} :=
    (ContinuousMap.measurable_eval 0) measurableSet_Ioi
  have h0 : ∀ᵐ f ∂μ, a < f 0 :=
    (ae_map_iff (hB.measurable_continuousPathMap hBmeasurable).aemeasurable
      h0meas).2 h0orig
  have hpre : F ⁻¹' U =ᵐ[μ] L := by
    filter_upwards [h0] with f hf0
    apply propext
    change (firstPassageBelow (F f) a ≤ 1 ∧ a < F f 1) ↔ f 1 < a
    have hevent := firstPassageBelow_le_one_reflectAfter_capped_iff f a
    have hL_hit (hf : f 1 < a) : firstPassageBelow f a ≤ 1 :=
      (firstPassageBelow_le_iff f a 1).2 ⟨1, le_rfl, hf.le⟩
    constructor
    · rintro ⟨hFH, hFend⟩
      have hH : firstPassageBelow f a ≤ 1 := hevent.mp hFH
      have hend := reflectAfter_firstPassageBelow_capped_apply_one f a hf0 hH
      change F f 1 = 2 * a - f 1 at hend
      linarith
    · intro hfL
      have hH := hL_hit hfL
      refine ⟨hevent.mpr hH, ?_⟩
      have hend := reflectAfter_firstPassageBelow_capped_apply_one f a hf0 hH
      change F f 1 = 2 * a - f 1 at hend
      linarith
  have hinv : μ.map F = μ :=
    hB.measure_reflectAfter_firstPassageBeforeOne_eq hBmeasurable a
  calc
    μ U = (μ.map F) U := by rw [hinv]
    _ = μ (F ⁻¹' U) := Measure.map_apply hF hU
    _ = μ L := measure_congr hpre

/-- The one-time reflection principle for a negative level: the
probability of passage by time `1` is twice the lower-tail probability
of the endpoint. -/
theorem IsBrownianReal.measure_firstPassageBelow_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | firstPassageBelow f a ≤ 1} =
      2 * μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let H : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1}
  let U : Set C(ℝ≥0, ℝ) := {f | firstPassageBelow f a ≤ 1 ∧ a < f 1}
  let L : Set C(ℝ≥0, ℝ) := {f | f 1 < a}
  have hLmeas : MeasurableSet L :=
    (ContinuousMap.measurable_eval 1) measurableSet_Iio
  have hAorig : ∀ᵐ ω ∂P, hB.continuousPathMap hBmeasurable ω 1 ≠ a := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.ae_eval_ne (by norm_num : (0 : ℝ≥0) < 1) a] with ω hpath hne
    rw [hpath 1]
    exact hne
  have hAmeas : MeasurableSet {f : C(ℝ≥0, ℝ) | f 1 ≠ a} :=
    (ContinuousMap.measurable_eval 1) (measurableSet_singleton a).compl
  have hA : ∀ᵐ f ∂μ, f 1 ≠ a :=
    (ae_map_iff (hB.measurable_continuousPathMap hBmeasurable).aemeasurable
      hAmeas).2 hAorig
  have hEq : H =ᵐ[μ] U ∪ L := by
    filter_upwards [hA] with f hfne
    apply propext
    change firstPassageBelow f a ≤ 1 ↔
      (firstPassageBelow f a ≤ 1 ∧ a < f 1) ∨ f 1 < a
    constructor
    · intro hhit
      rcases lt_or_gt_of_ne hfne with hlt | hgt
      · exact Or.inr hlt
      · exact Or.inl ⟨hhit, hgt⟩
    · rintro (⟨hhit, _⟩ | hlt)
      · exact hhit
      · exact (firstPassageBelow_le_iff f a 1).2 ⟨1, le_rfl, hlt.le⟩
  have hdisj : Disjoint U L := by
    apply Set.disjoint_left.mpr
    intro f hfU hfL
    exact (lt_asymm hfU.2) hfL
  have hreflect : μ U = μ L :=
    hB.measure_hitAndAbove_eq_below hBmeasurable ha
  calc
    μ H = μ (U ∪ L) := measure_congr hEq
    _ = μ U + μ L := measure_union hdisj hLmeas
    _ = 2 * μ L := by rw [hreflect, two_mul]

/-- The running minimum at time `1` obeys the one-time Brownian
reflection principle. -/
theorem IsBrownianReal.measure_runningMinimum_le_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f 1 ≤ a} =
      2 * μ {f : C(ℝ≥0, ℝ) | f 1 < a} := by
  have hset : {f : C(ℝ≥0, ℝ) | runningMinimum f 1 ≤ a} =
      {f | firstPassageBelow f a ≤ (1 : WithTop ℝ≥0)} := by
    ext f
    simpa using (runningMinimum_le_iff_firstPassageBelow_le f 1 a)
  rw [hset]
  exact hB.measure_firstPassageBelow_le_one hBmeasurable ha

private theorem runningMinimum_le_brownianPathScaling_iff
    (f : C(ℝ≥0, ℝ)) {t : ℝ≥0} (ht : 0 < t) (a : ℝ) :
    runningMinimum (brownianPathScaling t f) 1 ≤ (√t)⁻¹ * a ↔
      runningMinimum f t ≤ a := by
  have hfactor : 0 < ((√t)⁻¹ : ℝ) := by
    positivity
  rw [runningMinimum_le_iff_firstPassageBelow_le,
    runningMinimum_le_iff_firstPassageBelow_le,
    firstPassageBelow_le_iff, firstPassageBelow_le_iff]
  constructor
  · rintro ⟨u, hu, hvalue⟩
    refine ⟨t * u, ?_, ?_⟩
    · simpa using mul_le_mul_of_nonneg_left hu ht.le
    · change (√t)⁻¹ * f (t * u) ≤ (√t)⁻¹ * a at hvalue
      exact (mul_le_mul_iff_of_pos_left hfactor).mp hvalue
  · rintro ⟨u, hu, hvalue⟩
    refine ⟨u / t, ?_, ?_⟩
    · exact (div_le_one ht).2 hu
    · change (√t)⁻¹ * f (t * (u / t)) ≤ (√t)⁻¹ * a
      rw [mul_div_cancel₀ _ ht.ne']
      exact (mul_le_mul_iff_of_pos_left hfactor).mpr hvalue

/-- The reflection-principle formula for the running minimum at any
positive time. Brownian scaling reduces the assertion to time `1`. -/
theorem IsBrownianReal.measure_runningMinimum_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t ≤ a} =
      2 * μ {f : C(ℝ≥0, ℝ) | f t < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let S := brownianPathScaling t
  let A : Set C(ℝ≥0, ℝ) := {f | runningMinimum f t ≤ a}
  let C : Set C(ℝ≥0, ℝ) :=
    {f | runningMinimum f 1 ≤ (√t)⁻¹ * a}
  let D : Set C(ℝ≥0, ℝ) :=
    {f | f 1 < (√t)⁻¹ * a}
  let E : Set C(ℝ≥0, ℝ) := {f | f t < a}
  have hS : Measurable S := measurable_brownianPathScaling t
  have hC : MeasurableSet C := by
    have hfirst : MeasurableSet {f : C(ℝ≥0, ℝ) |
        firstPassageBelow f ((√t)⁻¹ * a) ≤ (1 : WithTop ℝ≥0)} :=
      (measurable_firstPassageBelow _) measurableSet_Iic
    convert hfirst using 1
    ext f
    exact runningMinimum_le_iff_firstPassageBelow_le f 1 _
  have hD : MeasurableSet D :=
    (ContinuousMap.measurable_eval 1) measurableSet_Iio
  have hA : S ⁻¹' C = A := by
    ext f
    exact runningMinimum_le_brownianPathScaling_iff f ht a
  have hE : S ⁻¹' D = E := by
    ext f
    change (√t)⁻¹ * f (t * 1) < (√t)⁻¹ * a ↔ f t < a
    simpa using (mul_lt_mul_iff_of_pos_left
      (by positivity : 0 < ((√t)⁻¹ : ℝ)))
  have hlaw : μ.map S = μ := by
    rw [Measure.map_map hS
      (hB.measurable_continuousPathMap hBmeasurable)]
    exact hB.measure_continuousPathMap_scale_eq hBmeasurable ht.ne'
  have hlevel : (√t)⁻¹ * a < 0 := mul_neg_of_pos_of_neg (by positivity) ha
  calc
    μ A = μ (S ⁻¹' C) := by rw [hA]
    _ = (μ.map S) C := (Measure.map_apply hS hC).symm
    _ = μ C := by rw [hlaw]
    _ = 2 * μ D := hB.measure_runningMinimum_le_one hBmeasurable hlevel
    _ = 2 * (μ.map S) D := by rw [hlaw]
    _ = 2 * μ (S ⁻¹' D) := by rw [Measure.map_apply hS hD]
    _ = 2 * μ E := by rw [hE]

/-- The strict running-minimum tail has the same reflection formula.
Approximate the level from below and use continuity of measure. -/
theorem IsBrownianReal.measure_runningMinimum_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t < a} =
      2 * μ {f : C(ℝ≥0, ℝ) | f t < a} := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let level : ℕ → ℝ := fun n => a - 1 / (n + 1 : ℝ)
  let A : ℕ → Set C(ℝ≥0, ℝ) := fun n =>
    {f | runningMinimum f t ≤ level n}
  let E : ℕ → Set C(ℝ≥0, ℝ) := fun n => {f | f t < level n}
  have hlevelNeg (n : ℕ) : level n < 0 := by
    dsimp [level]
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hlevelMono : Monotone level := by
    intro n m hnm
    dsimp [level]
    have hdiv : 1 / (m + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnm 1
    linarith
  have hAmono : Monotone A := by
    intro n m hnm f hf
    exact hf.trans (hlevelMono hnm)
  have hEmono : Monotone E := by
    intro n m hnm f hf
    exact hf.trans_le (hlevelMono hnm)
  have hlevelApprox {x : ℝ} (hx : x < a) :
      ∃ n : ℕ, x ≤ level n := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
    refine ⟨n, ?_⟩
    dsimp [level]
    linarith
  have hAunion : (⋃ n, A n) =
      {f : C(ℝ≥0, ℝ) | runningMinimum f t < a} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.trans_lt (by
        dsimp [level]
        have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith)
    · exact hlevelApprox
  have hEunion : (⋃ n, E n) =
      {f : C(ℝ≥0, ℝ) | f t < a} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.trans (by
        dsimp [level]
        have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith)
    · intro hf
      obtain ⟨n, hn⟩ := hlevelApprox (show (f t + a) / 2 < a by linarith)
      have hmid : f t < (f t + a) / 2 := by linarith
      exact ⟨n, hmid.trans_le hn⟩
  have hprob (n : ℕ) : μ (A n) = 2 * μ (E n) :=
    hB.measure_runningMinimum_le hBmeasurable ht (hlevelNeg n)
  calc
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t < a} =
        μ (⋃ n, A n) := by rw [hAunion]
    _ = ⨆ n, μ (A n) := hAmono.measure_iUnion
    _ = ⨆ n, 2 * μ (E n) := by simp_rw [hprob]
    _ = 2 * (⨆ n, μ (E n)) := (ENNReal.mul_iSup 2 _).symm
    _ = 2 * μ (⋃ n, E n) := by rw [hEmono.measure_iUnion]
    _ = 2 * μ {f : C(ℝ≥0, ℝ) | f t < a} := by rw [hEunion]

/-- A negative Brownian running-minimum level is not an atom. -/
theorem IsBrownianReal.measure_runningMinimum_eq_of_neg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t : ℝ≥0} (ht : 0 < t) {a : ℝ} (ha : a < 0) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t = a} = 0 := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let C : Set C(ℝ≥0, ℝ) := {f | runningMinimum f t ≤ a}
  let O : Set C(ℝ≥0, ℝ) := {f | runningMinimum f t < a}
  have hOmeas : MeasurableSet O :=
    (measurable_runningMinimum t) measurableSet_Iio
  have hOC : O ⊆ C := by
    intro f hf
    change runningMinimum f t < a at hf
    change runningMinimum f t ≤ a
    exact hf.le
  have hOFinite : μ O ≠ ∞ := by
    letI : IsProbabilityMeasure P :=
      (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
    exact measure_ne_top μ O
  have hdiff : C \ O = {f : C(ℝ≥0, ℝ) | runningMinimum f t = a} := by
    ext f
    change (runningMinimum f t ≤ a ∧ ¬ runningMinimum f t < a) ↔
      runningMinimum f t = a
    constructor
    · rintro ⟨hle, hnlt⟩
      exact le_antisymm hle (le_of_not_gt hnlt)
    · intro heq
      exact ⟨heq.le, by rw [heq]; exact lt_irrefl _⟩
  rw [← hdiff, measure_sdiff hOC hOmeas.nullMeasurableSet hOFinite,
    hB.measure_runningMinimum_le hBmeasurable ht ha,
    hB.measure_runningMinimum_lt hBmeasurable ht ha, tsub_self]

/-- A Brownian running minimum is strictly negative at every fixed
positive time. The levels $-1/(n+1)$ increase to zero, so continuity of
measure and Gaussian sign symmetry complete the reflection argument. -/
theorem IsBrownianReal.measure_runningMinimum_lt_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {t : ℝ≥0} (ht : 0 < t) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} = 1 := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  let level : ℕ → ℝ := fun n => -(1 / (n + 1 : ℝ))
  let A : ℕ → Set C(ℝ≥0, ℝ) := fun n =>
    {f | runningMinimum f t ≤ level n}
  let E : ℕ → Set C(ℝ≥0, ℝ) := fun n => {f | f t < level n}
  have hlevelNeg (n : ℕ) : level n < 0 := by
    dsimp [level]
    exact neg_neg_of_pos (by positivity)
  have hlevelMono : Monotone level := by
    intro n m hnm
    dsimp [level]
    apply neg_le_neg
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hAmono : Monotone A := by
    intro n m hnm f hf
    exact hf.trans (hlevelMono hnm)
  have hEmono : Monotone E := by
    intro n m hnm f hf
    exact hf.trans_le (hlevelMono hnm)
  have hAmeas (n : ℕ) : MeasurableSet (A n) := by
    have hfirst : MeasurableSet {f : C(ℝ≥0, ℝ) |
        firstPassageBelow f (level n) ≤ (t : WithTop ℝ≥0)} :=
      (measurable_firstPassageBelow _) measurableSet_Iic
    convert hfirst using 1
    ext f
    exact runningMinimum_le_iff_firstPassageBelow_le f t _
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    (ContinuousMap.measurable_eval t) measurableSet_Iio
  have hlevelApprox {x : ℝ} (hx : x < 0) :
      ∃ n : ℕ, x ≤ level n := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hx)
    refine ⟨n, ?_⟩
    dsimp [level]
    linarith
  have hAunion : (⋃ n, A n) =
      {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.trans_lt (hlevelNeg n)
    · exact hlevelApprox
  have hEunion : (⋃ n, E n) =
      {f : C(ℝ≥0, ℝ) | f t < 0} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.trans (hlevelNeg n)
    · intro hf
      obtain ⟨n, hn⟩ := hlevelApprox (show f t / 2 < 0 by linarith)
      have hhalf : f t < f t / 2 := by linarith
      exact ⟨n, hhalf.trans_le hn⟩
  have hprob (n : ℕ) : μ (A n) = 2 * μ (E n) :=
    hB.measure_runningMinimum_le hBmeasurable ht (hlevelNeg n)
  have hendpoint : μ {f : C(ℝ≥0, ℝ) | f t < 0} =
      gaussianReal 0 t (Set.Iio 0) := by
    have hpath := hB.measurable_continuousPathMap hBmeasurable
    have hset : MeasurableSet {f : C(ℝ≥0, ℝ) | f t < 0} :=
      (ContinuousMap.measurable_eval t) measurableSet_Iio
    calc
      μ {f : C(ℝ≥0, ℝ) | f t < 0} =
          P {ω | hB.continuousPathMap hBmeasurable ω t < 0} := by
            rw [Measure.map_apply hpath hset]
            rfl
      _ = P {ω | B t ω < 0} := by
            apply measure_congr
            filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable] with ω hω
            simp [hω t]
      _ = gaussianReal 0 t (Set.Iio 0) :=
            (hB.hasLaw_eval t).measure_eq measurableSet_Iio
  calc
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} =
        μ (⋃ n, A n) := by rw [hAunion]
    _ = ⨆ n, μ (A n) := hAmono.measure_iUnion
    _ = ⨆ n, 2 * μ (E n) := by simp_rw [hprob]
    _ = 2 * (⨆ n, μ (E n)) := (ENNReal.mul_iSup 2 _).symm
    _ = 2 * μ (⋃ n, E n) := by rw [hEmono.measure_iUnion]
    _ = 2 * μ {f : C(ℝ≥0, ℝ) | f t < 0} := by rw [hEunion]
    _ = 2 * gaussianReal 0 t (Set.Iio 0) := by rw [hendpoint]
    _ = 1 := gaussianReal_Iio_zero_two_mul ht

/-- The Brownian running minimum at a fixed positive time has no atoms.
Negative levels follow from the strict and closed reflection formulas;
zero follows from strict negativity; positive levels follow from the
path's initial value. -/
theorem IsBrownianReal.measure_runningMinimum_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {t : ℝ≥0} (ht : 0 < t) (a : ℝ) :
    let μ := P.map (hB.continuousPathMap hBmeasurable)
    μ {f : C(ℝ≥0, ℝ) | runningMinimum f t = a} = 0 := by
  dsimp
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  by_cases haNeg : a < 0
  · exact hB.measure_runningMinimum_eq_of_neg hBmeasurable ht haNeg
  by_cases haZero : a = 0
  · subst a
    letI : IsProbabilityMeasure P :=
      (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
    have hmeas : MeasurableSet
        {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0} :=
      (measurable_runningMinimum t) measurableSet_Iio
    have hcompl : μ {f : C(ℝ≥0, ℝ) | runningMinimum f t < 0}ᶜ = 0 :=
      (prob_compl_eq_zero_iff hmeas).2
        (hB.measure_runningMinimum_lt_zero hBmeasurable ht)
    apply le_antisymm
    · exact (measure_mono (show
      {f : C(ℝ≥0, ℝ) | runningMinimum f t = 0} ⊆
        {f | runningMinimum f t < 0}ᶜ from by
          intro f hf
          change runningMinimum f t = 0 at hf
          change ¬ runningMinimum f t < 0
          rw [hf]
          exact lt_irrefl _)).trans hcompl.le
    · exact bot_le
  · have haPos : 0 < a := lt_of_le_of_ne (le_of_not_gt haNeg) (Ne.symm haZero)
    have hpath0 : ∀ᵐ f ∂μ, f 0 = 0 := by
      have hset : MeasurableSet {f : C(ℝ≥0, ℝ) | f 0 = 0} :=
        (ContinuousMap.measurable_eval 0) (measurableSet_singleton 0)
      have horig : ∀ᵐ ω ∂P,
          hB.continuousPathMap hBmeasurable ω 0 = 0 := by
        filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
          hB.eval_zero_ae_eq_zero] with ω hpath hzero
        rw [hpath 0, hzero]
      exact (ae_map_iff
        (hB.measurable_continuousPathMap hBmeasurable).aemeasurable hset).2 horig
    have hne : ∀ᵐ f ∂μ, runningMinimum f t ≠ a := by
      filter_upwards [hpath0] with f hf0 heq
      have hle := runningMinimum_le f (show (0 : ℝ≥0) ≤ t from bot_le)
      rw [hf0, heq] at hle
      exact (not_le_of_gt haPos) hle
    simpa only [not_not] using (ae_iff).mp hne

end ProbabilityTheory

end
