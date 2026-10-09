/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Cadlag.FiniteDimensional.Dense
public import Probability.Process.Path.Skorokhod
public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Order.UnitInterval.Rational

/-!
# Measurable path-valued realizations of càdlàg processes

A real process with almost-surely càdlàg paths has an almost-everywhere
measurable realization in Skorokhod path space. The construction uses the
measurable embedding given by rational coordinates and extends its inverse
outside the set of càdlàg coordinate vectors by a fixed path.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.Path.Cadlag

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rational-coordinate map embeds real càdlàg paths on `[0,1]` into the
countable product of their rational-time values. -/
theorem rationalEvaluationEmbedding :
    MeasurableEmbedding
      (Skorokhod.denseEvaluation RationalCoordinate.toUnitInterval :
        CadlagPath unitInterval ℝ → RationalCoordinate.UnitInterval → ℝ) := by
  let time := RationalCoordinate.toUnitInterval
  have hstrict : StrictMono time := by
    intro q r hqr
    change ((q : ℚ) : ℝ) < ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have htop : (⊤ : unitInterval) ∈ Set.range time := by
    refine ⟨⊤, ?_⟩
    apply Subtype.ext
    norm_num [time, RationalCoordinate.toUnitInterval]
  exact Skorokhod.measurableEmbedding_denseEvaluation time
    RationalCoordinate.denseRange_toUnitInterval hstrict.monotone htop

/-- The canonical càdlàg path-valued map associated with a real process on
the unit interval. Outside the set of rational coordinate vectors that come
from a càdlàg path, it takes the fixed zero path. -/
noncomputable def pathMap (X : unitInterval → Ω → ℝ) :
    Ω → CadlagPath unitInterval ℝ :=
  Function.extend (Skorokhod.denseEvaluation RationalCoordinate.toUnitInterval)
    id (fun _ => Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval 0)) ∘
    fun ω q => X (RationalCoordinate.toUnitInterval q) ω

/-- If every process coordinate is almost-everywhere measurable, its
rational-coordinate path map is almost-everywhere measurable. -/
theorem aemeasurable_pathMap (X : unitInterval → Ω → ℝ) {P : Measure Ω}
    (hX : ∀ t, AEMeasurable (X t) P) :
    AEMeasurable (pathMap X) P := by
  have hcoords : AEMeasurable
      (fun ω (q : RationalCoordinate.UnitInterval) =>
        X (RationalCoordinate.toUnitInterval q) ω) P :=
    AEMeasurable.of_eval fun q => hX (RationalCoordinate.toUnitInterval q)
  exact (rationalEvaluationEmbedding.measurable_extend measurable_id
    measurable_const).comp_aemeasurable hcoords

/-- The process path law on Skorokhod space, formed from the almost-
everywhere measurable rational-coordinate realization. -/
noncomputable def pathLaw (P : Measure Ω) (X : unitInterval → Ω → ℝ)
    (_hX : ∀ t, AEMeasurable (X t) P) :
    Measure (CadlagPath unitInterval ℝ) :=
  P.map (pathMap X)

noncomputable instance pathLaw.instIsProbabilityMeasure
    (P : Measure Ω) [IsProbabilityMeasure P] (X : unitInterval → Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P) :
    IsProbabilityMeasure (pathLaw P X hX) := by
  unfold pathLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_pathMap X hX)).2 inferInstance

/-- The rational-coordinate realization agrees at every time with the
original process almost surely, provided the process has càdlàg paths almost
surely. -/
theorem pathMap_ae_eval_eq (X : unitInterval → Ω → ℝ) {P : Measure Ω}
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun s => X s ω)) (t : unitInterval) :
    (fun ω => pathMap X ω t) =ᵐ[P] X t := by
  filter_upwards [hcadlag] with ω hω
  let p : CadlagPath unitInterval ℝ := ⟨(fun s => X s ω), hω⟩
  have hcoords :
      (fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω) =
        Skorokhod.denseEvaluation RationalCoordinate.toUnitInterval p := by
    funext q
    rfl
  have hmap : pathMap X ω = p := by
    change Function.extend
      (Skorokhod.denseEvaluation RationalCoordinate.toUnitInterval)
      id (fun _ => Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval 0))
      ((fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω)) = p
    rw [hcoords]
    exact rationalEvaluationEmbedding.injective.extend_apply _ _ _
  rw [hmap]

/-- The path-valued realization has the expected pushforward law. -/
theorem hasLaw_pathMap (X : unitInterval → Ω → ℝ) {P : Measure Ω}
    (hX : ∀ t, AEMeasurable (X t) P) :
    HasLaw (pathMap X) (pathLaw P X hX) P where
  aemeasurable := aemeasurable_pathMap X hX
  map_eq := rfl

end ProbabilityTheory.Process.Path.Cadlag

end
