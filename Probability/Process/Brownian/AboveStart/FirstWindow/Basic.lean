/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.ContinuousPathLaw
public import Probability.Process.Brownian.AboveStart.NonAntitone
public import Probability.Process.Path.AboveStart.FirstWindow.Tail

/-!
# Almost-sure finiteness of the first Brownian unit window

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStart_ne_top_eq_one`:
  for a Brownian path $B$, the first time $T$ with
  $B(T+u)\ge B(T)$ for every $u\in[0,1]$ is finite almost surely.
- `ProbabilityTheory.IsBrownianReal.tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top`:
  the probability that $T^{n+1}<\infty$ tends to one.
- `ProbabilityTheory.IsBrownianReal.tendsto_measure_firstNonnegativeWindowStartUpTo_eq_top`:
  the complementary probability tends to zero.

This is Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.2, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. Its proof uses Brownian scaling,
cited there to Paul Lévy, *Processus Stochastique et Mouvement Brownien*
(1945), p. 246.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Filter
open scoped NNReal Topology

namespace ProbabilityTheory

private theorem firstNonnegativeWindowStartUpTo_ne_top_iff
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    firstNonnegativeWindowStartUpTo f s ≠ ⊤ ↔
      ∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t := by
  classical
  unfold firstNonnegativeWindowStartUpTo
  split_ifs with h
  · constructor
    · intro _
      exact h
    · intro _
      exact WithTop.coe_ne_top
  · simp [h]

private theorem brownianPathScaling_windowStart_iff
    (f : C(ℝ≥0, ℝ)) {c : ℝ≥0} (hc : c ≠ 0) (t : ℝ≥0) :
    IsNonnegativeWindowStart (brownianPathScaling c f) t ↔
      IsNonnegativeWindowStartFor f (c * t) c := by
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
  have hfactor : 0 < ((√c)⁻¹ : ℝ) := by positivity
  constructor
  · intro h u
    let v : Set.Icc (0 : ℝ≥0) c := ⟨u.1, u.property⟩
    let w : Set.Icc (0 : ℝ≥0) 1 :=
      ⟨v.1 / c, div_nonneg v.property.1 hcpos.le,
        (div_le_one hcpos).2 v.property.2⟩
    have hwindow := h w
    have htime : c * (t + w.1) = c * t + v.1 := by
      rw [mul_add]
      change c * t + c * (↑u / c) = c * t + ↑u
      rw [mul_div_cancel₀ _ hc]
    change (√c)⁻¹ * f (c * t) ≤
      (√c)⁻¹ * f (c * (t + w.1)) at hwindow
    rw [htime] at hwindow
    exact (mul_le_mul_iff_of_pos_left hfactor).mp hwindow
  · intro h u
    let v : Set.Icc (0 : ℝ≥0) c :=
      ⟨c * u.1, mul_nonneg hcpos.le u.property.1,
        by simpa using mul_le_mul_of_nonneg_left u.property.2 hcpos.le⟩
    have hwindow := h v
    have htime : c * (t + u.1) = c * t + v.1 := by
      dsimp [v]
      rw [mul_add]
    have hscaled := (mul_le_mul_iff_of_pos_left hfactor).2 hwindow
    change (√c)⁻¹ * f (c * t) ≤
      (√c)⁻¹ * f (c * (t + u.1))
    rw [htime]
    exact hscaled

private theorem hasNonnegativeWindowBeforeUnit_iff_scaledFirstWindowUpTo_ne_top
    (f : C(ℝ≥0, ℝ)) {c : ℝ≥0} (hc : c ≠ 0) :
    HasNonnegativeWindowBeforeUnit f c ↔
      firstNonnegativeWindowStartUpTo (brownianPathScaling c f) (1 / c) ≠ ⊤ := by
  rw [firstNonnegativeWindowStartUpTo_ne_top_iff]
  constructor
  · rintro ⟨s, hs, hwindow⟩
    have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
    let t : ℝ≥0 := s / c
    have hct : c * t = s := by
      dsimp [t]
      exact mul_div_cancel₀ s hc
    refine ⟨t, ?_, ?_⟩
    · have hbound : t + 1 ≤ 1 / c := by
        apply (le_div_iff₀ hcpos).2
        calc
          (t + 1) * c = s + c := by
            rw [add_mul, one_mul, mul_comm t c, hct]
          _ ≤ 1 := hs
      exact hbound
    · rw [brownianPathScaling_windowStart_iff f hc t, hct]
      exact hwindow
  · rintro ⟨t, ht, hwindow⟩
    have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
    let s : ℝ≥0 := c * t
    refine ⟨s, ?_, ?_⟩
    · have hmul := mul_le_mul_of_nonneg_left ht hcpos.le
      have hmul' : c * (t + 1) ≤ 1 := by
        simpa [one_div, mul_inv_cancel₀ hc] using hmul
      have hsum : c * t + c ≤ 1 := by
        simpa [mul_add] using hmul'
      simpa [s, mul_comm] using hsum
    · rw [← brownianPathScaling_windowStart_iff f hc t]
      simpa [s] using hwindow

private noncomputable def bolthausenWindowDuration (n : ℕ) : ℝ≥0 :=
  1 / (n + 1)

private theorem bolthausenWindowDuration_pos (n : ℕ) :
    0 < bolthausenWindowDuration n := by
  rw [bolthausenWindowDuration]
  exact div_pos zero_lt_one (by positivity)

private theorem bolthausenWindowDuration_anti {n m : ℕ} (hnm : n ≤ m) :
    bolthausenWindowDuration m ≤ bolthausenWindowDuration n := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hnm 1

private theorem hasNonnegativeWindowBeforeUnit_mono_duration
    (f : C(ℝ≥0, ℝ)) {d d' : ℝ≥0} (hdd' : d' ≤ d)
    (h : HasNonnegativeWindowBeforeUnit f d) :
    HasNonnegativeWindowBeforeUnit f d' := by
  rcases h with ⟨t, ht, hwindow⟩
  refine ⟨t, ?_, ?_⟩
  · calc
      t + d' ≤ t + d := add_le_add_right hdd' t
      _ ≤ 1 := ht
  ·
    intro u
    exact hwindow ⟨u.1, u.property.1, u.property.2.trans hdd'⟩

private theorem exists_bolthausenWindowDuration_le (d : ℝ≥0) (hd : 0 < d) :
    ∃ n : ℕ, bolthausenWindowDuration n ≤ d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨n, hn⟩ := exists_nat_gt ((d : ℝ)⁻¹)
  have hn' : (d : ℝ)⁻¹ < (n : ℝ) + 1 := by
    exact hn.trans_le (by exact_mod_cast Nat.le_succ n)
  have hsmall : (1 : ℝ) / ((n : ℝ) + 1) < (d : ℝ) := by
    have hpos : 0 < (d : ℝ)⁻¹ := inv_pos.mpr hdR
    have h := one_div_lt_one_div_of_lt hpos hn'
    simpa [one_div, inv_inv] using h
  refine ⟨n, ?_⟩
  have hsmall' : bolthausenWindowDuration n < d := by
    change (1 : ℝ≥0) / (n + 1) < d
    exact_mod_cast hsmall
  exact hsmall'.le

/-- Bolthausen's Lemma 2.2: for a standard Brownian path, the first time
$T$ at which $B(T+u)\ge B(T)$ for every $u\in[0,1]$ is finite almost
surely. The proof follows Bolthausen's scaling argument: a positive
window of some duration occurs almost surely; scaling makes its duration
one without changing Brownian path law, as cited there to Lévy,
*Processus Stochastique et Mouvement Brownien* (Gauthier-Villars, Paris,
1945), p. 246. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStart_ne_top_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) :
    P {ω | firstNonnegativeWindowStart
      (hB.continuousPathMap hBmeasurable ω) ≠ ⊤} = 1 := by
  classical
  let path : Ω → C(ℝ≥0, ℝ) := hB.continuousPathMap hBmeasurable
  let A : ℕ → Set Ω := fun n =>
    {ω | HasNonnegativeWindowBeforeUnit (path ω)
      (bolthausenWindowDuration n)}
  let E : Set C(ℝ≥0, ℝ) :=
    {f | firstNonnegativeWindowStart f ≠ ⊤}
  let EΩ : Set Ω := {ω | path ω ∈ E}
  have hpath : Measurable path := hB.measurable_continuousPathMap hBmeasurable
  have hE : MeasurableSet E := by
    have hlt : MeasurableSet {f : C(ℝ≥0, ℝ) |
        firstNonnegativeWindowStart f < (⊤ : WithTop ℝ≥0)} := by
      exact measurable_firstNonnegativeWindowStart measurableSet_Iio
    convert hlt using 1
    ext f
    change firstNonnegativeWindowStart f ≠ ⊤ ↔
      firstNonnegativeWindowStart f < ⊤
    exact (WithTop.lt_top_iff_ne_top
      (x := firstNonnegativeWindowStart f)).symm
  have hAmeas (n : ℕ) : MeasurableSet (A n) := by
    let c := bolthausenWindowDuration n
    have hc : c ≠ 0 := (bolthausenWindowDuration_pos n).ne'
    have hscaled : Measurable (fun ω =>
        firstNonnegativeWindowStartUpTo
          (brownianPathScaling c (path ω)) (1 / c)) :=
      (measurable_firstNonnegativeWindowStartUpTo (1 / c)).comp
        ((measurable_brownianPathScaling c).comp hpath)
    have hEq : A n = {ω | firstNonnegativeWindowStartUpTo
        (brownianPathScaling c (path ω)) (1 / c) ≠ ⊤} := by
      ext ω
      exact hasNonnegativeWindowBeforeUnit_iff_scaledFirstWindowUpTo_ne_top
        (path ω) hc
    rw [hEq]
    have htarget : MeasurableSet
        {t : WithTop ℝ≥0 | t ≠ ⊤} := by
      convert (show MeasurableSet (Set.Iio (⊤ : WithTop ℝ≥0)) from
        measurableSet_Iio) using 1
      ext t
      exact WithTop.lt_top_iff_ne_top.symm
    exact hscaled htarget
  have hAmono : Monotone A := by
    intro n m hnm ω hω
    exact hasNonnegativeWindowBeforeUnit_mono_duration (path ω)
      (bolthausenWindowDuration_anti hnm) hω
  have hUnionAE : ∀ᵐ ω ∂P, ω ∈ ⋃ n, A n := by
    filter_upwards [hB.ae_exists_positiveWindowBeforeUnit,
      hB.continuousPathMap_ae_eq hBmeasurable] with ω hwindow hpathEq
    rcases hwindow with ⟨f, hf, d, hd, hfd⟩
    have hfeq : f = path ω := by
      ext t
      rw [hf t, hpathEq t]
    obtain ⟨n, hn⟩ := exists_bolthausenWindowDuration_le d hd
    have hshort : HasNonnegativeWindowBeforeUnit (path ω)
        (bolthausenWindowDuration n) := by
      rw [← hfeq]
      exact hasNonnegativeWindowBeforeUnit_mono_duration f hn hfd
    exact Set.mem_iUnion.mpr ⟨n, hshort⟩
  have hUnionProb : P (⋃ n, A n) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hAmeas)).mp
    exact hUnionAE
  have hmeasureLimit : Filter.Tendsto (fun n => P (A n)) Filter.atTop (𝓝 1) := by
    have hlimit := tendsto_measure_iUnion_atTop (μ := P) (s := A) hAmono
    change Filter.Tendsto (P ∘ A) Filter.atTop (𝓝 (P (⋃ n, A n))) at hlimit
    rw [hUnionProb] at hlimit
    exact hlimit
  have hscaledEvent (n : ℕ) :
      P {ω | firstNonnegativeWindowStart
          (brownianPathScaling (bolthausenWindowDuration n) (path ω)) ≠ ⊤} =
        P EΩ := by
    let c := bolthausenWindowDuration n
    have hc : c ≠ 0 := (bolthausenWindowDuration_pos n).ne'
    have hscalemeas : Measurable (brownianPathScaling c ∘ path) :=
      (measurable_brownianPathScaling c).comp hpath
    have hscalelaw := hB.measure_continuousPathMap_scale_eq
      hBmeasurable hc
    calc
      P {ω | firstNonnegativeWindowStart
          (brownianPathScaling c (path ω)) ≠ ⊤} =
          (P.map (brownianPathScaling c ∘ path)) E := by
            rw [Measure.map_apply hscalemeas hE]
            rfl
      _ = (P.map path) E := by rw [hscalelaw]
      _ = P EΩ := by
            rw [Measure.map_apply hpath hE]
            rfl
  have hsubset (n : ℕ) : A n ⊆ {ω | firstNonnegativeWindowStart
      (brownianPathScaling (bolthausenWindowDuration n) (path ω)) ≠ ⊤} := by
    intro ω hω
    have hc : bolthausenWindowDuration n ≠ 0 :=
      (bolthausenWindowDuration_pos n).ne'
    have hfinite :=
      (hasNonnegativeWindowBeforeUnit_iff_scaledFirstWindowUpTo_ne_top
        (path ω) hc).mp hω
    obtain ⟨t, ht, hwindow⟩ :=
      (firstNonnegativeWindowStartUpTo_ne_top_iff
        (brownianPathScaling (bolthausenWindowDuration n) (path ω))
        (1 / bolthausenWindowDuration n)).mp hfinite
    have hexists : ∃ t : ℝ≥0, IsNonnegativeWindowStart
        (brownianPathScaling (bolthausenWindowDuration n) (path ω)) t :=
      ⟨t, hwindow⟩
    let f := brownianPathScaling (bolthausenWindowDuration n) (path ω)
    obtain ⟨t₀, ht₀, hmin⟩ := exists_earliestNonnegativeWindowStart f hexists
    have heq : firstNonnegativeWindowStart f = t₀ :=
      (firstNonnegativeWindowStart_eq_coe_iff f t₀).mpr ⟨ht₀, hmin⟩
    change firstNonnegativeWindowStart f ≠ ⊤
    rw [heq]
    exact WithTop.coe_ne_top
  have hprobLower : 1 ≤ P EΩ := by
    apply le_of_tendsto_of_tendsto' hmeasureLimit tendsto_const_nhds
    intro n
    calc
      P (A n) ≤ P {ω | firstNonnegativeWindowStart
          (brownianPathScaling (bolthausenWindowDuration n) (path ω)) ≠ ⊤} :=
        measure_mono (hsubset n)
      _ = P EΩ := hscaledEvent n
  apply le_antisymm ?_ hprobLower
  calc
    P EΩ ≤ P Set.univ := measure_mono (Set.subset_univ EΩ)
    _ = 1 := measure_univ

/-- The Brownian first eligible window occurs before a sufficiently
large finite horizon with probability arbitrarily close to one. -/
theorem IsBrownianReal.tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) :
    Tendsto (fun n : ℕ => P {ω |
      firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) ((n : ℝ≥0) + 1) ≠ ⊤})
      atTop (nhds 1) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hpath : Measurable pathB :=
    hB.measurable_continuousPathMap hBmeasurable
  have : IsProbabilityMeasure (P.map pathB) :=
    (Measure.isProbabilityMeasure_map_iff hpath.aemeasurable).2 inferInstance
  have hfirstSet : MeasurableSet
      {f : C(ℝ≥0, ℝ) | firstNonnegativeWindowStart f ≠ ⊤} :=
    (measurable_firstNonnegativeWindowStart
      (measurableSet_singleton (⊤ : WithTop ℝ≥0))).compl
  have hfinite : P.map pathB
      {f | firstNonnegativeWindowStart f ≠ ⊤} = 1 := by
    rw [Measure.map_apply hpath hfirstSet]
    exact hB.measure_firstNonnegativeWindowStart_ne_top_eq_one
      hBmeasurable
  have hlimit := ProbabilityTheory.tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top
    (P.map pathB) hfinite
  convert hlimit using 1
  funext n
  have hset : MeasurableSet
      {f : C(ℝ≥0, ℝ) |
        firstNonnegativeWindowStartUpTo f ((n : ℝ≥0) + 1) ≠ ⊤} :=
    (measurable_firstNonnegativeWindowStartUpTo _
      (measurableSet_singleton (⊤ : WithTop ℝ≥0))).compl
  rw [Measure.map_apply hpath hset]
  rfl

/-- The Brownian probability of finding no eligible unit window before
the cutoff tends to zero. -/
theorem IsBrownianReal.tendsto_measure_firstNonnegativeWindowStartUpTo_eq_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t)) :
    Tendsto (fun n : ℕ => P {ω |
      firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) ((n : ℝ≥0) + 1) = ⊤})
      atTop (nhds 0) := by
  have hgood := hB.tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top
    hBmeasurable
  have hbad := ENNReal.Tendsto.sub tendsto_const_nhds hgood
    (Or.inl ENNReal.one_ne_top)
  have hmeas (n : ℕ) : MeasurableSet {ω |
      firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) ((n : ℝ≥0) + 1) ≠ ⊤} :=
    (((measurable_firstNonnegativeWindowStartUpTo _).comp
      (hB.measurable_continuousPathMap hBmeasurable))
      (measurableSet_singleton ⊤)).compl
  convert hbad using 1
  · funext n
    rw [show {ω | firstNonnegativeWindowStartUpTo
          (hB.continuousPathMap hBmeasurable ω) ((n : ℝ≥0) + 1) = ⊤} =
        {ω | firstNonnegativeWindowStartUpTo
          (hB.continuousPathMap hBmeasurable ω) ((n : ℝ≥0) + 1) ≠ ⊤}ᶜ by ext; simp,
      measure_compl (hmeas n), measure_univ]
    exact measure_ne_top _ _
  · simp

end ProbabilityTheory

end
