/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Meander.LastZero

/-!
# The terminal-excursion path law

The public objects and theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.lastZeroMeanderPathLaw`:
  the law of the normalized absolute Brownian path following its last
  zero before time one.
- `ProbabilityTheory.IsBrownianReal.isProbabilityMeasure_lastZeroMeanderPathLaw`:
  this law has total mass one.
- `ProbabilityTheory.IsBrownianReal.ae_lastZeroMeanderPathLaw_zero`:
  its paths start at zero almost surely.
- `ProbabilityTheory.IsBrownianReal.ae_lastZeroMeanderPathLaw_pos`:
  at each fixed positive time, its paths are positive almost surely.
- `ProbabilityTheory.IsBrownianReal.ae_lastZeroMeanderPathLaw_nonnegative`:
  its paths are nonnegative at every time almost surely.
- `ProbabilityTheory.IsBrownianReal.ae_lastZeroMeanderPathLaw_strictlyPositive`:
  its paths are strictly positive at every positive time almost surely.

The construction is the Brownian representation on pages 616--617 of
Donald L. Iglehart, *Functional Central Limit Theorems for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619,
Section 3. Iglehart attributes the finite-dimensional distribution
identification with the conditioned-walk limit to Barry Belkin,
*An invariance principle for conditioned recurrent random walk attracted
to a stable law*, Z. Wahrscheinlichkeitstheorie verw. Gebiete 21 (1972),
45--64, page 61.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The path-valued normalized Brownian terminal excursion. -/
noncomputable def IsBrownianReal.lastZeroMeanderPath
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    (ω : Ω) : C(unitInterval, ℝ) :=
  ContinuousMap.lastZeroMeanderTransform
    (restrictPathToUnitInterval
      (hB.continuousPathMap hmeasurable ω))

theorem IsBrownianReal.measurable_lastZeroMeanderPath
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    Measurable (hB.lastZeroMeanderPath hmeasurable) :=
  ContinuousMap.measurable_lastZeroMeanderTransform.comp
    (continuous_restrictPathToUnitInterval.measurable.comp
      (hB.measurable_continuousPathMap hmeasurable))

/-- Iglehart's normalized terminal-excursion law on continuous paths. -/
noncomputable def IsBrownianReal.lastZeroMeanderPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    Measure C(unitInterval, ℝ) :=
  P.map (hB.lastZeroMeanderPath hmeasurable)

noncomputable instance IsBrownianReal.isProbabilityMeasure_lastZeroMeanderPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    IsProbabilityMeasure (hB.lastZeroMeanderPathLaw hmeasurable) := by
  unfold IsBrownianReal.lastZeroMeanderPathLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable).2
    inferInstance

/-- The terminal-excursion law is supported on paths beginning at zero. -/
theorem IsBrownianReal.ae_lastZeroMeanderPathLaw_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ f ∂hB.lastZeroMeanderPathLaw hmeasurable, f 0 = 0 := by
  change ∀ᵐ f ∂P.map (hB.lastZeroMeanderPath hmeasurable), f 0 = 0
  apply (MeasureTheory.ae_map_iff
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable
    (p := fun f : C(unitInterval, ℝ) => f 0 = 0)
    ((isClosed_singleton.preimage
      (continuous_eval_const (0 : unitInterval))).measurableSet)).2
  exact (hB.ae_lastZeroMeanderTransform_positive hmeasurable).mono
    (fun ω hω => hω.1)

/-- Every fixed positive time has a positive value under the
terminal-excursion law. -/
theorem IsBrownianReal.ae_lastZeroMeanderPathLaw_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    (t : unitInterval) (ht : 0 < t) :
    ∀ᵐ f ∂hB.lastZeroMeanderPathLaw hmeasurable, 0 < f t := by
  change ∀ᵐ f ∂P.map (hB.lastZeroMeanderPath hmeasurable), 0 < f t
  apply (MeasureTheory.ae_map_iff
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable
    (p := fun f : C(unitInterval, ℝ) => 0 < f t)
    ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage
      (continuous_eval_const t) |>.measurableSet)).2
  exact (hB.ae_lastZeroMeanderTransform_positive hmeasurable).mono
    (fun ω hω => hω.2 t ht)

/-- The Iglehart path law is concentrated on the closed nonnegative cone. -/
theorem IsBrownianReal.ae_lastZeroMeanderPathLaw_nonnegative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ f ∂hB.lastZeroMeanderPathLaw hmeasurable,
      ∀ t : unitInterval, 0 ≤ f t := by
  have hclosed : IsClosed
      {f : C(unitInterval, ℝ) | ∀ t : unitInterval, 0 ≤ f t} := by
    have hset :
        {f : C(unitInterval, ℝ) | ∀ t : unitInterval, 0 ≤ f t} =
          ⋂ t : unitInterval, {f : C(unitInterval, ℝ) | 0 ≤ f t} := by
      ext f
      simp
    rw [hset]
    exact isClosed_iInter fun t =>
      (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).preimage
        (continuous_eval_const t)
  change ∀ᵐ f ∂P.map (hB.lastZeroMeanderPath hmeasurable),
    ∀ t : unitInterval, 0 ≤ f t
  apply (MeasureTheory.ae_map_iff
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable
    hclosed.measurableSet).2
  exact (hB.ae_lastZeroMeanderTransform_positive hmeasurable).mono
    (fun ω hω t => by
      by_cases ht : t = 0
      · subst t
        exact le_of_eq hω.1.symm
      · exact (hω.2 t (lt_of_le_of_ne bot_le (Ne.symm ht))).le)

/-- Continuous paths which are strictly positive at every positive time
form a Borel subset of the compact-open path space. -/
theorem measurableSet_strictlyPositiveAfterZero :
    MeasurableSet
      {f : C(unitInterval, ℝ) |
        ∀ t : unitInterval, 0 < t → 0 < f t} := by
  let K (n : ℕ) : Set unitInterval :=
    {t | 1 / ((n : ℝ) + 1) ≤ (t : ℝ)}
  have hcompact (n : ℕ) : IsCompact (K n) := by
    exact (isClosed_Ici.preimage continuous_subtype_val).isCompact
  have hset :
      {f : C(unitInterval, ℝ) |
        ∀ t : unitInterval, 0 < t → 0 < f t} =
        ⋂ n : ℕ, {f : C(unitInterval, ℝ) |
          Set.MapsTo f (K n) (Set.Ioi 0)} := by
    ext f
    constructor
    · intro hf
      simp only [Set.mem_iInter]
      intro n t ht
      change 1 / ((n : ℝ) + 1) ≤ (t : ℝ) at ht
      have htpos : (0 : ℝ) < t :=
        lt_of_lt_of_le (by positivity :
          (0 : ℝ) < 1 / ((n : ℝ) + 1)) ht
      exact hf t htpos
    · intro hf t ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
      exact (Set.mem_iInter.mp hf n)
        (show t ∈ K n from le_of_lt hn)
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    (ContinuousMap.isOpen_setOfPred_mapsTo (hcompact n)
      isOpen_Ioi).measurableSet

/-- Iglehart's normalized terminal Brownian excursion is strictly
positive throughout its positive-time interval almost surely. -/
theorem IsBrownianReal.ae_lastZeroMeanderPathLaw_strictlyPositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ f ∂hB.lastZeroMeanderPathLaw hmeasurable,
      ∀ t : unitInterval, 0 < t → 0 < f t := by
  change ∀ᵐ f ∂P.map (hB.lastZeroMeanderPath hmeasurable),
    ∀ t : unitInterval, 0 < t → 0 < f t
  apply (MeasureTheory.ae_map_iff
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable
    measurableSet_strictlyPositiveAfterZero).2
  exact (hB.ae_lastZeroMeanderTransform_positive hmeasurable).mono
    (fun ω hω => hω.2)

end ProbabilityTheory

end
