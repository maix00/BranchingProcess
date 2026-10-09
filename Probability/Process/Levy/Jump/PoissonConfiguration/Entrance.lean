/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.Process.Levy.Jump.PoissonConfiguration.JumpPath
public import Probability.RandomMeasure.Poisson.Basic
import Order.Bounds.Corridor
import Probability.RandomMeasure.Poisson.IndependentConfiguration
import Probability.RandomMeasure.Poisson.PathBound

/-!
# Entrance for a Poisson jump-sum model

The small-jump total variation and the unique large-jump configuration imply
the full, uncountable-time corridor event. This argument is pathwise; the
independent Poisson construction supplies positivity of its input event.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The sum of a small-jump integral and a large-jump integral, both indexed
by actual observation time. -/
noncomputable def poissonEntrancePath
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ))
    (t : unitInterval) (ω : Ωs × Ωb) : ℝ :=
  (∫ z in {z | z ∈ A ∧ z.1 ≤ t}, z.2
      ∂(poissonRandomMeasure Ks Xs ω.1)) +
    poissonJumpPath Kb Xb H ω.2 t

/-- A positive probability of small total variation and exactly one selected
large jump implies a positive full-path entrance probability. -/
theorem measure_poissonEntrancePath_pos_of_one_zero
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {mb : Measure (unitInterval × ℝ)} [SigmaFinite mb]
    (Ps : Measure Ωs) (Pb : Measure Ωb)
    (A J B : Set (unitInterval × ℝ))
    (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (lower upper target ρ ε margin : ℝ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ z ∈ J, |z.2 - target| < ρ)
    (hgood : 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∫⁻ z in A, ENNReal.ofReal |z.2|
        ∂(poissonRandomMeasure Ks Xs ω.1)) < ENNReal.ofReal ρ ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) J = 1 ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) B = 0}) :
    0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∀ t, lower + (margin - 2 * ρ) ≤
          poissonEntrancePath Ks Xs Kb Xb A (J ∪ B) t ω ∧
        poissonEntrancePath Ks Xs Kb Xb A (J ∪ B) t ω ≤
          upper - (margin - 2 * ρ)) ∧
      target - ε < poissonEntrancePath Ks Xs Kb Xb A (J ∪ B) ⊤ ω ∧
      poissonEntrancePath Ks Xs Kb Xb A (J ∪ B) ⊤ ω < target + ε} := by
  apply hgood.trans_le
  apply measure_mono
  intro ω hω
  obtain ⟨hvariation, hone, hzero⟩ := hω
  obtain ⟨p, hpK, hpJ, hbig⟩ :=
    poissonJumpPath_eq_singleJump_of_one_zero
      (m := mb) hJ hB ω.2 hone hzero
  let S : unitInterval → ℝ := fun t =>
    ∫ z in {z | z ∈ A ∧ z.1 ≤ t}, z.2
      ∂(poissonRandomMeasure Ks Xs ω.1)
  have hsmall : ∀ t, |S t| ≤ ρ :=
    poissonRandomMeasure_smallJumpPath_bound ω.1 A id ρ hρ hvariation
  have hpath := Order.Bounds.oneJump_staysInInterval_and_endsNear
    S (Xb p.1 p.2 ω.2).1 (Xb p.1 p.2 ω.2).2
    lower upper target ρ ε margin hε hl0 hu0 hly huy
    hsmall (hJwindow _ hpJ)
  have hdecomp : ∀ t,
      poissonEntrancePath Ks Xs Kb Xb A (J ∪ B) t ω =
        S t + (if (Xb p.1 p.2 ω.2).1 ≤ t then
          (Xb p.1 p.2 ω.2).2 else 0) := by
    intro t
    unfold poissonEntrancePath S
    rw [hbig t]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [hdecomp t]
    exact hpath.1 t
  · rw [hdecomp ⊤]
    simpa using hpath.2.1
  · rw [hdecomp ⊤]
    simpa using hpath.2.2

/-- The independent small- and large-jump Poisson sources provide a cutoff
for which the one-jump path enters the desired corridor with positive
probability. The cutoff is chosen before the positive-probability event. -/
theorem exists_poissonEntrancePath_pos
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ms mb : Measure (unitInterval × ℝ)} [SigmaFinite ms] [SigmaFinite mb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    (band : ℕ → Set (unitInterval × ℝ))
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ z, ENNReal.ofReal |z.2| ∂ms) ≠ ⊤)
    (haway : ∀ᵐ z ∂ms, ∀ᶠ n in Filter.atTop, z ∉ band n)
    {J B : Set (unitInterval × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (lower upper target ρ ε margin : ℝ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ z ∈ J, |z.2 - target| < ρ) :
    ∃ n, 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∀ t, lower + (margin - 2 * ρ) ≤
          poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) t ω ∧
        poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) t ω ≤
          upper - (margin - 2 * ρ)) ∧
      target - ε < poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) ⊤ ω ∧
      poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) ⊤ ω < target + ε} := by
  obtain ⟨n, hgood⟩ :=
    exists_independent_poissonSmallVariation_oneJump_pos
      hds hdb (fun z => ENNReal.ofReal |z.2|) band
      (by fun_prop) hband hfinite haway
      hJ hB hfinJ hfinB hJpos hdisj ρ hρ
  exact ⟨n, measure_poissonEntrancePath_pos_of_one_zero
    (mb := mb) Ps Pb (band n) J B hJ hB
    lower upper target ρ ε margin hρ hε hl0 hu0 hly huy
    hJwindow hgood⟩

/-- Two canonical Poisson point families realize the positive entrance
configuration on a genuine product probability space. -/
theorem exists_poissonEntrancePath_model
    (ms mb : Measure (unitInterval × ℝ))
    [SigmaFinite ms] [SigmaFinite mb]
    (band : ℕ → Set (unitInterval × ℝ))
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ z, ENNReal.ofReal |z.2| ∂ms) ≠ ⊤)
    (haway : ∀ᵐ z ∂ms, ∀ᶠ n in Filter.atTop, z ∉ band n)
    {J B : Set (unitInterval × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (lower upper target ρ ε margin : ℝ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ z ∈ J, |z.2 - target| < ρ) :
    ∃ (Ωs Ωb : Type) (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
      (Ps : Measure Ωs) (Pb : Measure Ωb)
      (Ks : ℕ → Ωs → ℕ)
      (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
      (Kb : ℕ → Ωb → ℕ)
      (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ),
      IsProbabilityMeasure Ps ∧ IsProbabilityMeasure Pb ∧
      IsPoissonPointFamily Ks Xs ms Ps ∧
      IsPoissonPointFamily Kb Xb mb Pb ∧
      ∃ n, 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
        (∀ t, lower + (margin - 2 * ρ) ≤
            poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) t ω ∧
          poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) t ω ≤
            upper - (margin - 2 * ρ)) ∧
        target - ε < poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) ⊤ ω ∧
        poissonEntrancePath Ks Xs Kb Xb (band n) (J ∪ B) ⊤ ω < target + ε} := by
  obtain ⟨Ωs, mΩs, Ps, Ks, Xs, hPs, hds⟩ := exists_isPoissonPointFamily ms
  obtain ⟨Ωb, mΩb, Pb, Kb, Xb, hPb, hdb⟩ := exists_isPoissonPointFamily mb
  let := mΩs
  let := mΩb
  let := hPs
  let := hPb
  refine ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, ?_⟩
  exact exists_poissonEntrancePath_pos hds hdb band hband hfinite haway
    hJ hB hfinJ hfinB hJpos hdisj
    lower upper target ρ ε margin hρ hε hl0 hu0 hly huy hJwindow

end ProbabilityTheory
