/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Analysis.Asymptotics.LogSum
public import MeasureTheory.MeasurableSpace.CadlagPath.PathClass.StepCorridor.NullMeasurable
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnion
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Finite-union rates for null-measurable corridor events

The exact pointwise-strict `M₂` corridor is null-measurable under a finite path
law, and its pullback along an almost-everywhere measurable path map remains
null-measurable.  Consequently, the finite-union rate argument only needs
null-measurability of the component events.  The rate estimates themselves are
unchanged: they depend on component probabilities, not on Borel
representatives.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor Set
open scoped Topology
open scoped ENNReal

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- Pull the exact pointwise-strict `M₂` event back along an a.e. measurable
path-valued random variable.  This uses null-measurability under the pushforward
law and the quasi-measure-preserving property of the map to its law; no Borel
representative of the corridor event is required. -/
theorem ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (c : ContinuousAdmissibleStepCorridor)
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → CadlagPath unitInterval ℝ) (hX : AEMeasurable X P) :
    NullMeasurableSet (X ⁻¹' c.toSet) P := by
  let X' := hX.mk
  let Q : Measure (CadlagPath unitInterval ℝ) := P.map X'
  have hQfinite : IsFiniteMeasure Q := Measure.isFiniteMeasure_map P X'
  letI : IsFiniteMeasure Q := hQfinite
  have hcorridor : NullMeasurableSet c.toSet Q := c.nullMeasurableSet_toSet Q
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving X' P Q := by
    simpa [Q] using hX.measurable_mk.quasiMeasurePreserving P
  have hpreimage : NullMeasurableSet (X' ⁻¹' c.toSet) P := hcorridor.preimage hqmp
  have hae : X ⁻¹' c.toSet =ᵐ[P] X' ⁻¹' c.toSet := by
    exact Filter.EventuallyEq.preimage hX.ae_eq_mk c.toSet
  exact hpreimage.congr hae.symm

/-- Every finite union of the exact component `M₂` corridors is null-measurable
under a finite path law. -/
theorem FiniteCorridorUnion.nullMeasurableSet_toSet
    {α : ℝ} (G : FiniteCorridorUnion α) (P : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure P] : NullMeasurableSet G.toSet P := by
  rw [FiniteCorridorUnion.toSet]
  exact NullMeasurableSet.iUnion fun i => (G.pieces i).nullMeasurableSet_toSet P

/-- The finite-union logarithmic rate only needs null-measurability of each
component corridor event.  The returned measurability statement is correspondingly
`NullMeasurableSet`, which is enough for the probability law and does not assert
Borel measurability of the exact pointwise-strict union. -/
theorem tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} (G : FiniteCorridorUnion α)
    {I : Type*} {l : Filter I}
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (hNullMeasurable : ∀ x i,
      NullMeasurableSet {ω | paths x ω ∈ (G.pieces i).toSet} P)
    (hpos : ∀ i, ∀ᶠ x in l,
      0 < (P ({ω | paths x ω ∈ (G.pieces i).toSet})).toReal)
    (hcomponent : ∀ i, Tendsto
      (fun x => Real.log
        ((P {ω | paths x ω ∈ (G.pieces i).toSet}).toReal) / g x)
      l (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α
        (G.pieces i)).toReal))) :
    (∀ x, NullMeasurableSet {ω | paths x ω ∈ G.toSet} P) ∧
    (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ G.toSet}).toReal) ∧ Tendsto
  (fun x => Real.log ((P {ω | paths x ω ∈ G.toSet}).toReal) / g x)
      l (𝓝 (κ * G.realEnergy)) := by
  classical
  let component (x : I) (i : Fin G.count) : Set Ω :=
    {ω | paths x ω ∈ (G.pieces i).toSet}
  let componentProbability (x : I) (i : Fin G.count) : ℝ :=
    (P (component x i)).toReal
  let unionEvent (x : I) : Set Ω := {ω | paths x ω ∈ G.toSet}
  let unionProbability (x : I) : ℝ := (P (unionEvent x)).toReal
  let energy (i : Fin G.count) : ℝ≥0∞ := ContinuousAdmissibleStepCorridor.energy α (G.pieces i)
  have huniv : (Finset.univ : Finset (Fin G.count)).Nonempty :=
    ⟨⟨0, G.count_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_min_image Finset.univ energy huniv
  have henergyMin : G.energy = energy i₀ := by
    unfold FiniteCorridorUnion.energy finiteMinimumEnergy energy
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ i₀)
    · rw [Finset.le_inf'_iff]
      intro i hi
      exact hi₀ i (Finset.mem_univ i)
  have hUnionNullMeasurable (x : I) : NullMeasurableSet (unionEvent x) P := by
    rw [show unionEvent x = ⋃ i : Fin G.count, component x i by
      ext ω
      simp [unionEvent, FiniteCorridorUnion.toSet, component]]
    exact NullMeasurableSet.iUnion fun i => hNullMeasurable x i
  have hfiniteComponent (x : I) (i : Fin G.count) :
      P (component x i) ≠ ⊤ := by
    apply ne_of_lt
    calc
      P (component x i) ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hfiniteUnion (x : I) : P (unionEvent x) ≠ ⊤ := by
    apply ne_of_lt
    calc
      P (unionEvent x) ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hupper (x : I) : unionProbability x ≤
      ∑ i ∈ (Finset.univ : Finset (Fin G.count)), componentProbability x i := by
    have hevent : unionEvent x = ⋃ i : Fin G.count, component x i := by
      ext ω
      simp [unionEvent, FiniteCorridorUnion.toSet, component]
    have hsum : P (unionEvent x) ≤ ∑ i : Fin G.count, P (component x i) := by
      rw [hevent]
      exact measure_iUnion_fintype_le P (component x)
    have hsum_ne : (∑ i : Fin G.count, P (component x i)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.2
      intro i hi
      exact hfiniteComponent x i
    have hsum_toReal :
        (∑ i : Fin G.count, P (component x i)).toReal =
          ∑ i ∈ (Finset.univ : Finset (Fin G.count)), componentProbability x i := by
      simpa [componentProbability] using
        (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin G.count)))
          (f := fun i => P (component x i)) (by
            intro i hi
            exact hfiniteComponent x i))
    exact (ENNReal.toReal_mono hsum_ne hsum).trans_eq hsum_toReal
  have hlower (x : I) (i : Fin G.count) :
      componentProbability x i ≤ unionProbability x := by
    apply ENNReal.toReal_mono (hfiniteUnion x)
    apply measure_mono
    intro ω hω
    change paths x ω ∈ G.toSet
    rw [FiniteCorridorUnion.toSet]
    exact Set.mem_iUnion.2 ⟨i, hω⟩
  have hqpos : ∀ᶠ x in l, 0 < unionProbability x := by
    filter_upwards [hpos i₀] with x hx
    have hx' : 0 < componentProbability x i₀ := by
      simpa [componentProbability, component] using hx
    exact lt_of_lt_of_le hx' (hlower x i₀)
  have hupperEventually : ∀ᶠ x in l, unionProbability x ≤
      ∑ i ∈ (Finset.univ : Finset (Fin G.count)), componentProbability x i :=
    Filter.Eventually.of_forall hupper
  have hlowerEventually : ∀ᶠ x in l,
      componentProbability x i₀ ≤ unionProbability x :=
    Filter.Eventually.of_forall (fun x => hlower x i₀)
  have hcomponentPos : ∀ i : Fin G.count, ∀ᶠ x in l, 0 < componentProbability x i :=
    fun i => hpos i
  have hcomponentRate : ∀ i : Fin G.count, Tendsto
      (fun x => Real.log (componentProbability x i) / g x)
      l (𝓝 (κ * (energy i).toReal)) := by
    intro i
    simpa [componentProbability, component, energy] using hcomponent i
  have hEnergyMin : G.realEnergy = (energy i₀).toReal := by
    rw [FiniteCorridorUnion.realEnergy, henergyMin]
  have hrateLower : ∀ i : Fin G.count,
      κ * G.realEnergy ≤ κ * (energy i).toReal := by
    intro i
    have hle : energy i₀ ≤ energy i := hi₀ i (Finset.mem_univ i)
    have hreal := ENNReal.toReal_mono (ContinuousAdmissibleStepCorridor.energy_lt_top α (G.pieces i)).ne hle
    rw [hEnergyMin]
    exact mul_le_mul_of_nonneg_left hreal hκ.le
  have hrateEq : κ * (energy i₀).toReal = κ * G.realEnergy := by
    rw [← hEnergyMin]
  have hmain := Asymptotics.tendsto_log_finite_union_ratio
    (Finset.univ : Finset (Fin G.count)) huniv i₀ (Finset.mem_univ i₀)
    g unionProbability componentProbability
    (fun i => κ * (energy i).toReal) (κ * G.realEnergy)
    hg hqpos (Filter.Eventually.of_forall hupper) hlowerEventually
    (fun i hi => hcomponentPos i) (fun i hi => hcomponentRate i)
    (fun i hi => hrateLower i) hrateEq
  refine ⟨?_, hqpos, ?_⟩
  · intro x
    simpa [unionEvent] using hUnionNullMeasurable x
  · simpa [unionProbability, unionEvent] using hmain

/-- Use the exact `M₂` projection theorem to discharge the finite-union
null-measurability inputs whenever every path-valued random variable is a.e.
measurable. -/
theorem tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_aemeasurable_paths
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} (G : FiniteCorridorUnion α)
    {I : Type*} {l : Filter I}
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (hpaths : ∀ x, AEMeasurable (paths x) P)
    (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (hpos : ∀ i, ∀ᶠ x in l,
      0 < (P ({ω | paths x ω ∈ (G.pieces i).toSet})).toReal)
    (hcomponent : ∀ i, Tendsto
      (fun x => Real.log
        ((P {ω | paths x ω ∈ (G.pieces i).toSet}).toReal) / g x)
      l (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α
        (G.pieces i)).toReal))) :
    (∀ x, NullMeasurableSet {ω | paths x ω ∈ G.toSet} P) ∧
    (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ G.toSet}).toReal) ∧ Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ G.toSet}).toReal) / g x)
      l (𝓝 (κ * G.realEnergy)) := by
  apply tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable
    P G paths g hg hκ (fun x i => ?_) hpos hcomponent
  exact ContinuousAdmissibleStepCorridor.nullMeasurableSet_preimage_toSet_of_aemeasurable
    (G.pieces i) P (paths x) (hpaths x)

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
