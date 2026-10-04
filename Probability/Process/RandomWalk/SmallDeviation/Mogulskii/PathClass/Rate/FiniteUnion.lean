/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Analysis.Asymptotics.LogSum
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.PathClass.Energy

/-!
# Logarithmic rate of a finite union of corridor events

This is the finite-union step for class `M₃`.  It turns component `M₂`
corridor rates into the rate of their union.  The component rate and
measurability of each corridor event are explicit inputs; the theorem does not
assume or conceal the still separate `M₂` probability estimate.
-/

open Filter MeasureTheory Set
open scoped Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation

/-- The probability rate of an `M₃` finite union follows from the component
`M₂` rates.  The positive factor `κ` is the normalized cost coefficient;
because the union probability is dominated by the most likely component, its
rate is `κ` times the minimum corridor energy. -/
theorem tendsto_log_m3_preimage_probability_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} (G : M3 α)
    {I : Type*} {l : Filter I}
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (hMeasurable : ∀ x i, MeasurableSet {ω | paths x ω ∈ (G.pieces i).toSet})
    (hpos : ∀ i, ∀ᶠ x in l,
      0 < (P ({ω | paths x ω ∈ (G.pieces i).toSet})).toReal)
    (hcomponent : ∀ i, Tendsto
      (fun x => Real.log
        ((P {ω | paths x ω ∈ (G.pieces i).toSet}).toReal) / g x)
      l (𝓝 (κ * (M2Corridor.energy α
        (G.pieces i)).toReal))) :
    (∀ x, MeasurableSet {ω | paths x ω ∈ G.toSet}) ∧
    (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ G.toSet}).toReal) ∧ Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ G.toSet}).toReal) / g x)
      l (𝓝 (κ * G.hAlpha)) := by
  classical
  let component (x : I) (i : Fin G.count) : Set Ω :=
    {ω | paths x ω ∈ (G.pieces i).toSet}
  let componentProbability (x : I) (i : Fin G.count) : ℝ :=
    (P (component x i)).toReal
  let unionEvent (x : I) : Set Ω := {ω | paths x ω ∈ G.toSet}
  let unionProbability (x : I) : ℝ := (P (unionEvent x)).toReal
  let energy (i : Fin G.count) : ℝ≥0∞ := M2Corridor.energy α (G.pieces i)
  have huniv : (Finset.univ : Finset (Fin G.count)).Nonempty :=
    ⟨⟨0, G.count_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_min_image Finset.univ energy huniv
  have henergyMin : G.energy = energy i₀ := by
    unfold M3.energy finiteMinimumEnergy energy
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ i₀)
    · rw [Finset.le_inf'_iff]
      intro i hi
      exact hi₀ i (Finset.mem_univ i)
  have hUnionMeasurable (x : I) : MeasurableSet (unionEvent x) := by
    rw [show unionEvent x = ⋃ i : Fin G.count, component x i by
      ext ω
      simp [unionEvent, M3.toSet, component]]
    exact MeasurableSet.iUnion fun i => hMeasurable x i
  have hfiniteComponent (x : I) (i : Fin G.count) : P (component x i) ≠ ⊤ := by
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
      simp [unionEvent, M3.toSet, component]
    have hsum : P (unionEvent x) ≤ ∑ i : Fin G.count, P (component x i) := by
      rw [hevent]
      exact measure_iUnion_fintype_le P (component x)
    have hsum_ne : (∑ i : Fin G.count, P (component x i)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.2
      intro i hi
      exact (hfiniteComponent x i)
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
    rw [M3.toSet]
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
  have hAlphaMin : G.hAlpha = (energy i₀).toReal := by
    rw [M3.hAlpha, henergyMin]
  have hrateLower : ∀ i : Fin G.count,
      κ * G.hAlpha ≤ κ * (energy i).toReal := by
    intro i
    have hle : energy i₀ ≤ energy i := hi₀ i (Finset.mem_univ i)
    have hreal := ENNReal.toReal_mono (M2Corridor.energy_lt_top α (G.pieces i)).ne hle
    rw [hAlphaMin]
    exact mul_le_mul_of_nonneg_left hreal hκ.le
  have hrateEq : κ * (energy i₀).toReal = κ * G.hAlpha := by
    rw [← hAlphaMin]
  have hmain := Asymptotics.tendsto_log_finite_union_ratio
    (Finset.univ : Finset (Fin G.count)) huniv i₀ (Finset.mem_univ i₀)
    g unionProbability componentProbability
    (fun i => κ * (energy i).toReal) (κ * G.hAlpha)
    hg hqpos (Filter.Eventually.of_forall hupper) hlowerEventually
    (fun i hi => hcomponentPos i) (fun i hi => hcomponentRate i)
    (fun i hi => hrateLower i) hrateEq
  refine ⟨?_, hqpos, ?_⟩
  · simpa [unionEvent] using hUnionMeasurable
  · simpa [unionProbability, unionEvent] using hmain

end ProbabilityTheory.RandomWalk.SmallDeviation

end
