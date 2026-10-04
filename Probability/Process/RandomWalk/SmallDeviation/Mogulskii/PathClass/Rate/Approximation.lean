/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.PathClass.Approximation
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.PathClass.Rate.FiniteUnion
public import Mathlib.Topology.Order.Basic

/-!
# Approximation energies and the process theorem

The `M₃` rate implies that energy is antitone under set inclusion.  The
source's inner/outer approximation condition then forces both energy
sequences to converge to the same value.  Finally, fixed inner and outer
approximants squeeze the probability rate of any measurable set in class `M`.
The component `M₂` rate remains an explicit input through the `M₃` rate
hypothesis.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation

/-- If two `M₃` path sets are included and both have the same process rate
formula, their energies are ordered in the reverse direction. -/
theorem M3.hAlpha_antitone_of_subset_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (A B : M3 α) (hAB : A.toSet ⊆ B.toSet)
    (hApos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ A.toSet}).toReal)
    (hBpos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ B.toSet}).toReal)
    (hArate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x)
      l (𝓝 (κ * A.hAlpha)))
    (hBrate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x)
      l (𝓝 (κ * B.hAlpha))) :
    B.hAlpha ≤ A.hAlpha := by
  have hAfinite (x : I) : P {ω | paths x ω ∈ A.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ A.toSet} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hBfinite (x : I) : P {ω | paths x ω ∈ B.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ B.toSet} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
  have hratio :
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x) ≤ᶠ[l]
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x) := by
    filter_upwards [hApos, hBpos, hneg] with x hAx hBx hgx
    have hmeasure : P {ω | paths x ω ∈ A.toSet} ≤
        P {ω | paths x ω ∈ B.toSet} :=
      measure_mono (fun ω hω => hAB hω)
    have hreal := ENNReal.toReal_mono (hBfinite x) hmeasure
    have hlog := Real.log_le_log hAx hreal
    exact (div_le_div_right_of_neg hgx).2 hlog
  have hlim := le_of_tendsto_of_tendsto hBrate hArate hratio
  nlinarith [hκ]

/-- Cross-order of all inner and outer `M₃` energies, together with the
vanishing energy gap, implies existence of their common limit. -/
noncomputable def M3Approximation.energyLimits_of_crossOrder
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    (A : M3Approximation α G)
    (hcross : ∀ n m, M3.hAlpha (A.outer m) ≤ M3.hAlpha (A.inner n)) :
    M3EnergyLimits A := by
  let innerCost : ℕ → ℝ := fun n => M3.hAlpha (A.inner n)
  let outerCost : ℕ → ℝ := fun n => M3.hAlpha (A.outer n)
  have hCauchy : CauchySeq innerCost := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (A.energy_gap_tendsto_zero.eventually (Iio_mem_nhds hε))
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hgap := hN n hn
      have hcrossnm : outerCost n ≤ innerCost m := hcross m n
      dsimp [innerCost, outerCost] at hgap hcrossnm
      linarith
    · have hgap := hN m hm
      have hcrossmn : outerCost m ≤ innerCost n := hcross n m
      dsimp [innerCost, outerCost] at hgap hcrossmn
      linarith
  classical
  let hExists : ∃ L, Tendsto innerCost atTop (𝓝 L) :=
    cauchySeq_tendsto_of_complete hCauchy
  exact M3EnergyLimits.ofInnerTendsto (L := hExists.choose)
    (by simpa [innerCost] using hExists.choose_spec)

/-- The `M₃` probability rates order every inner/outer energy pair, so the
vanishing gap gives a common energy limit for an `M` approximation. -/
noncomputable def M3Approximation.energyLimits_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : M3Approximation α G)
    (hM3rate : ∀ C : M3 α,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.hAlpha))) :
    M3EnergyLimits A :=
  M3Approximation.energyLimits_of_crossOrder A (by
    intro n m
    exact M3.hAlpha_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner n) (A.outer m)
      (fun f hf => A.subset_outer m (A.inner_subset n hf))
      (hM3rate (A.inner n)).2.1 (hM3rate (A.outer m)).2.1
      (hM3rate (A.inner n)).2.2 (hM3rate (A.outer m)).2.2)

/-- The limiting `M₃` energy is independent of the chosen inner/outer
approximation, once the component probability rates are available. -/
theorem M3EnergyLimits.hAlpha_eq_of_approximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A B : M3Approximation α G)
    (hA : M3EnergyLimits A) (hB : M3EnergyLimits B)
    (hM3rate : ∀ C : M3 α,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.hAlpha))) :
    hA.hAlpha = hB.hAlpha := by
  have hBouter_le_Ainner (n : ℕ) :
      M3.hAlpha (B.outer n) ≤ M3.hAlpha (A.inner n) :=
    M3.hAlpha_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner n) (B.outer n)
      (fun f hf => B.subset_outer n (A.inner_subset n hf))
      (hM3rate (A.inner n)).2.1 (hM3rate (B.outer n)).2.1
      (hM3rate (A.inner n)).2.2 (hM3rate (B.outer n)).2.2
  have hAouter_le_Binner (n : ℕ) :
      M3.hAlpha (A.outer n) ≤ M3.hAlpha (B.inner n) :=
    M3.hAlpha_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (B.inner n) (A.outer n)
      (fun f hf => A.subset_outer n (B.inner_subset n hf))
      (hM3rate (B.inner n)).2.1 (hM3rate (A.outer n)).2.1
      (hM3rate (B.inner n)).2.2 (hM3rate (A.outer n)).2.2
  have hB_le_A : hB.outerLimit ≤ hA.innerLimit :=
    le_of_tendsto_of_tendsto hB.outer_tendsto hA.inner_tendsto
      (Filter.Eventually.of_forall hBouter_le_Ainner)
  have hA_le_B : hA.outerLimit ≤ hB.innerLimit :=
    le_of_tendsto_of_tendsto hA.outer_tendsto hB.inner_tendsto
      (Filter.Eventually.of_forall hAouter_le_Binner)
  have hAeq := hA.innerLimit_eq_outerLimit
  have hBeq := hB.innerLimit_eq_outerLimit
  change hA.innerLimit = hB.innerLimit
  linarith

/-- The process version of Mogul'skii's theorem for class `M`, assembled from
the `M₃` rates.  The `M₃` rate hypothesis is discharged by
`tendsto_log_m3_preimage_probability_ratio` once the component `M₂` rates are
available. -/
theorem tendsto_log_probability_ratio_of_M3Approximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : M3Approximation α G)
    (hGmeasurable : ∀ x, MeasurableSet {ω | paths x ω ∈ G})
    (hM3rate : ∀ C : M3 α,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.hAlpha))) :
    (∀ x, MeasurableSet {ω | paths x ω ∈ G}) ∧
    ∃ hLimits : M3EnergyLimits A,
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.hAlpha)) := by
  let hLimits : M3EnergyLimits A :=
    M3Approximation.energyLimits_of_probabilityRate P paths g hg hκ A hM3rate
  have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
  have hGfinite (x : I) : P {ω | paths x ω ∈ G} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ G} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hOuterFinite (n : ℕ) (x : I) :
      P {ω | paths x ω ∈ (M3.toSet (A.outer n))} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ (M3.toSet (A.outer n))} ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hGpos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ G}).toReal := by
    filter_upwards [(hM3rate (A.inner 0)).2.1] with x hx
    have hmeasure : P {ω | paths x ω ∈ (M3.toSet (A.inner 0))} ≤
        P {ω | paths x ω ∈ G} :=
      measure_mono (fun ω hω => A.inner_subset 0 hω)
    have hreal := ENNReal.toReal_mono (hGfinite x) hmeasure
    exact lt_of_lt_of_le (by simpa using hx) hreal
  refine ⟨hGmeasurable, hLimits, ?_⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    have houterLimit : Tendsto
        (fun n => κ * M3.hAlpha (A.outer n)) atTop
        (𝓝 (κ * hLimits.hAlpha)) := by
      have heq : hLimits.outerLimit = hLimits.hAlpha :=
        hLimits.hAlpha_eq_outerLimit.symm
      simpa [M3EnergyLimits.hAlpha, heq] using
        (tendsto_const_nhds.mul hLimits.outer_tendsto)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      houterLimit.eventually (Ioi_mem_nhds hy)
    let n := N
    have hn : y < κ * M3.hAlpha (A.outer n) := hN n le_rfl
    obtain ⟨_, _, hRate⟩ := hM3rate (A.outer n)
    have hRateEventually := hRate.eventually (Ioi_mem_nhds hn)
    have hbound : ∀ᶠ x in l,
        Real.log ((P {ω | paths x ω ∈ (M3.toSet (A.outer n))}).toReal) / g x ≤
          Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x := by
      filter_upwards [hGpos, (hM3rate (A.outer n)).2.1, hneg] with x hpx hox hgx
      have hmeasure : P {ω | paths x ω ∈ G} ≤
          P {ω | paths x ω ∈ (M3.toSet (A.outer n))} :=
        measure_mono (fun ω hω => A.subset_outer n hω)
      have hreal := ENNReal.toReal_mono (hOuterFinite n x) hmeasure
      have hlog := Real.log_le_log hpx hreal
      exact (div_le_div_right_of_neg hgx).2 hlog
    filter_upwards [hRateEventually, hbound] with x hx hxy
    exact lt_of_lt_of_le hx hxy
  · intro y hy
    have hinnerLimit : Tendsto
        (fun n => κ * M3.hAlpha (A.inner n)) atTop
        (𝓝 (κ * hLimits.hAlpha)) := by
      simpa [M3EnergyLimits.hAlpha] using
        (tendsto_const_nhds.mul hLimits.inner_tendsto)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hinnerLimit.eventually (Iio_mem_nhds hy)
    let n := N
    have hn : κ * M3.hAlpha (A.inner n) < y := hN n le_rfl
    obtain ⟨_, _, hRate⟩ := hM3rate (A.inner n)
    have hRateEventually := hRate.eventually (Iio_mem_nhds hn)
    have hbound : ∀ᶠ x in l,
        Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x ≤
          Real.log ((P {ω | paths x ω ∈ (M3.toSet (A.inner n))}).toReal) / g x := by
      filter_upwards [hGpos, (hM3rate (A.inner n)).2.1, hneg] with x hpx hix hgx
      have hmeasure : P {ω | paths x ω ∈ (M3.toSet (A.inner n))} ≤
          P {ω | paths x ω ∈ G} :=
        measure_mono (fun ω hω => A.inner_subset n hω)
      have hreal := ENNReal.toReal_mono (hGfinite x) hmeasure
      have hlog := Real.log_le_log hix hreal
      exact (div_le_div_right_of_neg hgx).2 hlog
    filter_upwards [hRateEventually, hbound] with x hx hxy
    exact lt_of_le_of_lt hxy hx

/-- The limiting energy attached to a set in class `M` is independent of the
chosen approximation witness, provided the component `M₃` probability rates
hold.  This is the probabilistic well-definedness assertion in the source. -/
theorem existsUnique_hAlpha_of_IsM
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hM3rate : ∀ C : M3 α,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.hAlpha))) :
    ∃! H : ℝ, ∃ A : M3Approximation α G,
      ∃ hLimits : M3EnergyLimits A, H = hLimits.hAlpha := by
  obtain ⟨A⟩ := hG
  let hLimits : M3EnergyLimits A :=
    M3Approximation.energyLimits_of_probabilityRate P paths g hg hκ A hM3rate
  refine ⟨hLimits.hAlpha, ⟨A, hLimits, rfl⟩, ?_⟩
  intro H hH
  obtain ⟨B, hB, hEq⟩ := hH
  have hEqAB := M3EnergyLimits.hAlpha_eq_of_approximation P paths g hg hκ
    A B hLimits hB hM3rate
  calc
    H = hB.hAlpha := hEq
    _ = hLimits.hAlpha := hEqAB.symm

/-- Process Theorem 2 for a set in class `M`, conditional on the `M₃` rates.
The result includes the unique approximation-independent energy value. -/
theorem tendsto_log_probability_ratio_of_IsM
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeasurable : ∀ x, MeasurableSet {ω | paths x ω ∈ G})
    (hM3rate : ∀ C : M3 α,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.hAlpha))) :
    (∀ x, MeasurableSet {ω | paths x ω ∈ G}) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
          l (𝓝 (κ * H)) := by
  have hUnique := existsUnique_hAlpha_of_IsM P paths g hg hκ hG hM3rate
  obtain ⟨A⟩ := hG
  obtain ⟨hmeas, hLimits, hRate⟩ :=
    tendsto_log_probability_ratio_of_M3Approximation P paths g hg hκ
      A hGmeasurable hM3rate
  refine ⟨hmeas, ?_⟩
  refine ⟨hLimits.hAlpha, ?_, ?_⟩
  · exact ⟨⟨A, hLimits, rfl⟩, hRate⟩
  · intro H hH
    have hEq := hUnique.unique hH.1 ⟨A, hLimits, rfl⟩
    rw [← hEq]

/-- Theorem 2 for class `M`, with the probabilistic input stated at the
source's single-corridor `M₂` level.  Finite unions are handled here by the
`M₃` rate lemma, and the approximation squeeze then gives the rate for `G`.
The exact `M₂` corridor measurability and rate remain explicit hypotheses. -/
theorem tendsto_log_probability_ratio_of_IsM_of_M2Rates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : IsM α G)
    (hGmeasurable : ∀ x, MeasurableSet {ω | paths x ω ∈ G})
    (hM2rate : ∀ C : M2Corridor,
      (∀ x, MeasurableSet {ω | paths x ω ∈ C.toSet}) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * (M2Corridor.energy α C).toReal))) :
    (∀ x, MeasurableSet {ω | paths x ω ∈ G}) ∧
      ∃! H : ℝ,
        (∃ A : M3Approximation α G, ∃ hLimits : M3EnergyLimits A,
          H = hLimits.hAlpha) ∧
        Tendsto
          (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
          l (𝓝 (κ * H)) := by
  apply tendsto_log_probability_ratio_of_IsM P paths g hg hκ hG hGmeasurable
  intro C
  have h := tendsto_log_m3_preimage_probability_ratio P C paths g hg hκ
    (fun x i => (hM2rate (C.pieces i)).1 x)
    (fun i => (hM2rate (C.pieces i)).2.1)
    (fun i => by
      simpa [M3.hAlpha] using (hM2rate (C.pieces i)).2.2)
  exact h

end ProbabilityTheory.RandomWalk.SmallDeviation

end
