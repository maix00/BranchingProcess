import Mathlib.MeasureTheory.Measure.Prod

/-!
# Couplings of probability measures

A coupling is a joint measure with prescribed first and second marginals.  The
definition is independent of any order, branching structure, or pathwise map.
-/

open MeasureTheory

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

/-- A pathwise relation holds under the joint law of a coupling. -/
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

end Coupling

end ProbabilityTheory
