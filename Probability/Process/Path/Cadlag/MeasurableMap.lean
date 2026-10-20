/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.FiniteDimensional.Dense
public import Probability.Process.Path.Representation.Skorokhod
public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Order.UnitInterval.Rational
public import Topology.Cadlag.Skorokhod.Path.Scaling

/-!
# Measurable path-valued realizations of càdlàg processes

The public objects and theorems in this file are:

- `rationalEvaluationEmbedding`: the map $f\mapsto(f(q))_{q\in\mathbb Q\cap[0,1]}$
  embeds the càdlàg path space measurably.
- `pathMap`, `aemeasurable_pathMap`, and `pathLaw`: the measurable
  realization of $X$ and its pushforward law $P\circ X^{-1}$.
- `pathMap_ae_eval_eq`: for an almost-surely càdlàg process,
  $\operatorname{pathMap}(X)(t)=X_t$ almost surely.
- `pathMap_eq_cadlagunitIntervalPath` and
  `pathLaw_eq_cadlagunitIntervalPathLaw`: for an everywhere-continuous
  process, the rational realization and continuous-path realization agree.
- `pathLaw_smul`: for an almost-surely càdlàg real process `X`,
  $\operatorname{pathLaw}(P,qX)=\operatorname{pathLaw}(P,X)\circ
  (f\mapsto qf)^{-1}$ for every real `q`.
- `hasLaw_pathMap`: $\operatorname{Law}_P(\operatorname{pathMap}(X))=
  \operatorname{pathLaw}(P,X)$.

A real process with almost-surely càdlàg paths has an almost-everywhere
measurable realization in Skorokhod path space. The construction uses the
measurable embedding given by rational coordinates and extends its inverse
outside the set of càdlàg coordinate vectors by a fixed path.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.Process.Path.Cadlag

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rational-coordinate map embeds real càdlàg paths on `[0,1]` into the
countable product of their rational-time values. -/
theorem rationalEvaluationEmbedding :
    MeasurableEmbedding
      (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval :
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
  exact MeasureTheory.CadlagPath.measurableEmbedding_denseEvaluation time
    RationalCoordinate.denseRange_toUnitInterval hstrict.monotone htop

/-- The canonical càdlàg path-valued map associated with a real process on
the unit interval. Outside the set of rational coordinate vectors that come
from a càdlàg path, it takes the fixed zero path. -/
noncomputable def pathMap (X : unitInterval → Ω → ℝ) :
    Ω → CadlagPath unitInterval ℝ :=
  Function.extend (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval)
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
        MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval p := by
    funext q
    rfl
  have hmap : pathMap X ω = p := by
    change Function.extend
      (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval)
      id (fun _ => Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval 0))
      ((fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω)) = p
    rw [hcoords]
    exact rationalEvaluationEmbedding.injective.extend_apply _ _ _
  rw [hmap]

omit [MeasurableSpace Ω] in
/-- For an everywhere-continuous process, the rational-coordinate path
realization is the usual bundled continuous path at every sample. -/
theorem pathMap_eq_cadlagunitIntervalPath
    (B : ℝ≥0 → Ω → ℝ) (hB : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    pathMap (fun t ω => B (UnitInterval.toNNReal t) ω) ω =
      cadlagunitIntervalPath B hB ω := by
  let p := cadlagunitIntervalPath B hB ω
  have hcoords :
      (fun q : RationalCoordinate.UnitInterval =>
        B (UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω) =
        MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval p := by
    funext q
    rfl
  change Function.extend
    (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval)
    id (fun _ => Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval 0))
    (fun q : RationalCoordinate.UnitInterval =>
      B (UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q)) ω) = p
  rw [hcoords]
  exact rationalEvaluationEmbedding.injective.extend_apply _ _ _

/-- The rational-coordinate path law agrees with the law of the bundled
continuous path when a process has everywhere-continuous sample paths. -/
theorem pathLaw_eq_cadlagunitIntervalPathLaw
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ ω, Continuous (B · ω))
    (hBmeas : ∀ t, Measurable (B t)) :
    pathLaw P (fun t ω => B (UnitInterval.toNNReal t) ω)
      (fun t => (hBmeas (UnitInterval.toNNReal t)).aemeasurable) =
    cadlagunitIntervalPathLaw P B hB hBmeas := by
  unfold pathLaw cadlagunitIntervalPathLaw
  congr 1
  funext ω
  exact pathMap_eq_cadlagunitIntervalPath B hB ω

/-- The path-valued realization has the expected pushforward law. -/
theorem hasLaw_pathMap (X : unitInterval → Ω → ℝ) {P : Measure Ω}
    (hX : ∀ t, AEMeasurable (X t) P) :
    HasLaw (pathMap X) (pathLaw P X hX) P where
  aemeasurable := aemeasurable_pathMap X hX
  map_eq := rfl

omit [MeasurableSpace Ω] in
private lemma pathMap_eq_of_cadlag (X : unitInterval → Ω → ℝ) (ω : Ω)
    (hω : IsCadlag (fun t => X t ω)) :
    pathMap X ω = ⟨fun t => X t ω, hω⟩ := by
  let p : CadlagPath unitInterval ℝ := ⟨fun t => X t ω, hω⟩
  have hcoords :
      (fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω) =
        MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval p := by
    funext q
    rfl
  change Function.extend
      (MeasureTheory.CadlagPath.denseEvaluation
        RationalCoordinate.toUnitInterval)
      id (fun _ => Skorokhod.ofContinuousMap
        (ContinuousMap.const unitInterval 0))
      (fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω) = p
  rw [hcoords]
  exact rationalEvaluationEmbedding.injective.extend_apply _ _ _

/-- For an almost-surely càdlàg real process, pointwise scalar multiplication
pushes its rational-coordinate path law forward by `Skorokhod.scalePath`:
`pathLaw(P, q * X) = (pathLaw(P, X)).map (Skorokhod.scalePath q)`. -/
theorem pathLaw_smul (X : unitInterval → Ω → ℝ) {P : Measure Ω}
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) (q : ℝ) :
    pathLaw P (fun t ω => q * X t ω)
      (fun t => (hX t).const_mul q) =
    (pathLaw P X hX).map (Skorokhod.scalePath q) := by
  let Xq : unitInterval → Ω → ℝ := fun t ω => q * X t ω
  have hcadlagq : ∀ᵐ ω ∂P, IsCadlag (fun t => Xq t ω) := by
    filter_upwards [hcadlag] with ω hω
    have hωq := hω.const_smul q
    convert hωq using 1
  have hpathMapEq (ω : Ω) (hω : IsCadlag (fun t => X t ω)) :
      pathMap Xq ω = Skorokhod.scalePath q (pathMap X ω) := by
    have hωq := hω.const_smul q
    have hωq' : IsCadlag (fun t => Xq t ω) := by
      convert hωq using 1
    rw [pathMap_eq_of_cadlag Xq ω hωq',
      pathMap_eq_of_cadlag X ω hω]
    rfl
  have hae : pathMap Xq =ᵐ[P] Skorokhod.scalePath q ∘ pathMap X := by
    filter_upwards [hcadlag] with ω hω
    exact hpathMapEq ω hω
  have hXpath : AEMeasurable (pathMap X) P := aemeasurable_pathMap X hX
  have hscaleCont : Continuous (fun f : CadlagPath unitInterval ℝ =>
      Skorokhod.scalePath q f) := by
    exact Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)
  change P.map (pathMap Xq) =
    (P.map (pathMap X)).map (Skorokhod.scalePath q)
  calc
    P.map (pathMap Xq) = P.map (Skorokhod.scalePath q ∘ pathMap X) :=
      Measure.map_congr hae
    _ = (P.map (pathMap X)).map (Skorokhod.scalePath q) :=
      (AEMeasurable.map_map_of_aemeasurable
        hscaleCont.aemeasurable hXpath).symm

end ProbabilityTheory.Process.Path.Cadlag

end
