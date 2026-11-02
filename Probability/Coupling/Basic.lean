/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Couplings of probability measures

A coupling is a joint measure with prescribed first and second marginals.  The
definition is independent of any order, branching structure, or pathwise map.

For a measure `κ` on `X×Y`, being a coupling of `μ` and `ν` means

\[
(\operatorname{map}\,\mathrm{Prod.fst})\,κ=μ,
\qquad
(\operatorname{map}\,\mathrm{Prod.snd})\,κ=ν.
\]

For a relation `R : X → Y → Prop`, it holds almost everywhere under the
joint measure:

\[
R(p.1,p.2)\quad\text{for }κ.\mathrm{joint}\text{-almost every }p.
\]

## Public declarations

* `ProbabilityTheory.Coupling μ ν` consists of a measure `κ` on `X × Y` such
  that `κ.map Prod.fst = μ` and `κ.map Prod.snd = ν`.
* `ProbabilityTheory.Coupling.AESatisfies κ R` means
  `∀ᵐ p ∂κ.joint, R p.1 p.2`.
* `ProbabilityTheory.Coupling.ofVariables` and
  `ProbabilityTheory.Coupling.ofVariablesOfLaws` form the joint law of two
  measurable random variables on a common probability space.
* `ProbabilityTheory.Coupling.independent` is the product coupling;
  `ProbabilityTheory.Coupling.swap` exchanges the marginals; and
  `ProbabilityTheory.Coupling.map` pushes both coordinates through measurable
  maps.
* `ProbabilityTheory.Coupling.measure_event_le_add_of_ae_implication` transfers
  an almost-sure event implication under a coupling to the marginal bound
  $\nu(A)\leq\mu(B)+\mu(C)$.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A joint law whose coordinate marginals are `μ` and `ν`. -/
structure Coupling (μ : Measure X) (ν : Measure Y) where
  joint : Measure (X × Y)
  fst_joint : joint.map Prod.fst = μ
  snd_joint : joint.map Prod.snd = ν

namespace Coupling

instance {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ]
    (κ : Coupling μ ν) : IsProbabilityMeasure κ.joint where
  measure_univ := by
    have h := congrArg (fun m : Measure X => m Set.univ) κ.fst_joint
    simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using h

/-- A relation holds almost surely between the two coordinates of a coupling. -/
def AESatisfies {μ : Measure X} {ν : Measure Y} (κ : Coupling μ ν)
    (R : X → Y → Prop) : Prop :=
  ∀ᵐ p ∂κ.joint, R p.1 p.2

/-- Two measurable random variables on one measure space induce a coupling of
their laws.  This is the bridge from a common pre-sampled space to the
measure-level notion of coupling. -/
noncomputable def ofVariables {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → X) (V : Ω → Y)
    (hU : Measurable U) (hV : Measurable V) :
    Coupling (P.map U) (P.map V) where
  joint := P.map (fun ω => (U ω, V ω))
  fst_joint := by
    rw [Measure.map_map measurable_fst (hU.prod hV)]
    congr 1
  snd_joint := by
    rw [Measure.map_map measurable_snd (hU.prod hV)]
    congr 1

/-- A common-space realization whose two pushforward laws have already been
identified with the desired marginals. -/
noncomputable def ofVariablesOfLaws {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → X) (V : Ω → Y)
    (hU : Measurable U) (hV : Measurable V)
    (μ : Measure X) (ν : Measure Y)
    (hUlaw : P.map U = μ) (hVlaw : P.map V = ν) : Coupling μ ν where
  joint := P.map (fun ω => (U ω, V ω))
  fst_joint := by
    rw [Measure.map_map measurable_fst (hU.prod hV)]
    rw [show Prod.fst ∘ (fun ω => (U ω, V ω)) = U by funext ω; rfl]
    exact hUlaw
  snd_joint := by
    rw [Measure.map_map measurable_snd (hU.prod hV)]
    rw [show Prod.snd ∘ (fun ω => (U ω, V ω)) = V by funext ω; rfl]
    exact hVlaw

/-- The independent coupling of two probability measures. -/
noncomputable def independent (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Coupling μ ν where
  joint := μ.prod ν
  fst_joint := by simp
  snd_joint := by simp

/-- Exchange the two coordinates of a coupling. -/
noncomputable def swap {μ : Measure X} {ν : Measure Y}
    (κ : Coupling μ ν) : Coupling ν μ where
  joint := κ.joint.map Prod.swap
  fst_joint := by
    rw [Measure.map_map measurable_fst measurable_swap]
    rw [show Prod.fst ∘ Prod.swap = (Prod.snd : X × Y → Y) by funext p; rfl]
    exact κ.snd_joint
  snd_joint := by
    rw [Measure.map_map measurable_snd measurable_swap]
    rw [show Prod.snd ∘ Prod.swap = (Prod.fst : X × Y → X) by funext p; rfl]
    exact κ.fst_joint

/-- Push both coordinates of a coupling through measurable maps. -/
noncomputable def map {μ : Measure X} {ν : Measure Y}
    (κ : Coupling μ ν) {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    (f : X → X') (g : Y → Y') (hf : Measurable f) (hg : Measurable g) :
    Coupling (μ.map f) (ν.map g) where
  joint := κ.joint.map (fun p => (f p.1, g p.2))
  fst_joint := by
    rw [Measure.map_map measurable_fst
      ((hf.comp measurable_fst).prod (hg.comp measurable_snd))]
    rw [show Prod.fst ∘ (fun p : X × Y => (f p.1, g p.2)) = f ∘ Prod.fst by
      funext p; rfl]
    rw [← Measure.map_map hf measurable_fst, κ.fst_joint]
  snd_joint := by
    rw [Measure.map_map measurable_snd
      ((hf.comp measurable_fst).prod (hg.comp measurable_snd))]
    rw [show Prod.snd ∘ (fun p : X × Y => (f p.1, g p.2)) = g ∘ Prod.snd by
      funext p; rfl]
    rw [← Measure.map_map hg measurable_snd, κ.snd_joint]

/-- If membership in a target event implies, almost surely under the joint
measure, membership in one of two source events, then the target marginal
probability is at most the sum of the two source marginal probabilities. -/
theorem measure_event_le_add_of_ae_implication
    {μ : Measure X} {ν : Measure Y} (κ : Coupling μ ν)
    (A : Set Y) (B C : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (h : ∀ᵐ p ∂κ.joint,
      p.2 ∈ A → p.1 ∈ B ∨ p.1 ∈ C) :
    ν A ≤ μ B + μ C := by
  have hAmap : (κ.joint.map Prod.snd) A =
      κ.joint (Prod.snd ⁻¹' A) := Measure.map_apply measurable_snd hA
  have hBmap : (κ.joint.map Prod.fst) B =
      κ.joint (Prod.fst ⁻¹' B) := Measure.map_apply measurable_fst hB
  have hCmap : (κ.joint.map Prod.fst) C =
      κ.joint (Prod.fst ⁻¹' C) := Measure.map_apply measurable_fst hC
  calc
    ν A = κ.joint (Prod.snd ⁻¹' A) := by
      calc
        ν A = (κ.joint.map Prod.snd) A := by rw [κ.snd_joint]
        _ = κ.joint (Prod.snd ⁻¹' A) := hAmap
    _ ≤ κ.joint ((Prod.fst ⁻¹' B) ∪ (Prod.fst ⁻¹' C)) := by
      apply measure_mono_ae
      filter_upwards [h] with p hp
      intro hpA
      rcases hp (by simpa using hpA) with hpB | hpC
      · exact Or.inl hpB
      · exact Or.inr hpC
    _ ≤ κ.joint (Prod.fst ⁻¹' B) + κ.joint (Prod.fst ⁻¹' C) :=
      measure_union_le _ _
    _ = μ B + μ C := by
      calc
        _ = (κ.joint.map Prod.fst) B +
            (κ.joint.map Prod.fst) C := by rw [hBmap, hCmap]
        _ = μ B + μ C := by rw [κ.fst_joint]

end Coupling

end ProbabilityTheory
