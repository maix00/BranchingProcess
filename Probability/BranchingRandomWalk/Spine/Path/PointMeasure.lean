module

public import Probability.BranchingRandomWalk.Spine.PointMeasureRandomWalk
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne

@[expose] public section

/-!
# Enumeration-free path many-to-one formula

Generation path intensity is defined by iterated integration against an
offspring random measure.  There is no child-slot type in these definitions,
so the ambient mark space may be uncountable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk

/-- Weighted intensity of complete ancestral histories through generation
`n`, starting at the scalar position `x`. -/
noncomputable def pointMeasureWeightedPathIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E)) :
    ∀ n : ℕ, ((Fin (n + 1) → ℝ) → ENNReal) → ℝ → ENNReal
  | 0, F, x => F (fun _ => x)
  | n + 1, F, x =>
      ∫⁻ ν, ∫⁻ z, PointProcess.exponentialWeight potential θ z *
        pointMeasureWeightedPathIterate potential θ law n
          (fun tail => F (prependHistory x tail)) (x + potential z) ∂ν ∂law

theorem pointMeasureWeightedPathIterate_succ
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (θ : ℝ) (law : Measure (Measure E))
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ENNReal) (x : ℝ) :
    pointMeasureWeightedPathIterate potential θ law (n + 1) F x =
      ∫⁻ ν, ∫⁻ z, PointProcess.exponentialWeight potential θ z *
        pointMeasureWeightedPathIterate potential θ law n
          (fun tail => F (prependHistory x tail)) (x + potential z) ∂ν ∂law :=
  rfl

theorem measurable_pointMeasureWeightedPathIterate_parameter
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential θ law) :
    ∀ (n : ℕ) {F : A → (Fin (n + 1) → ℝ) → ENNReal},
      Measurable (Function.uncurry F) →
      Measurable (fun p : A × ℝ =>
        pointMeasureWeightedPathIterate potential θ law n (F p.1) p.2)
  | 0, F, hF => by
      change Measurable (fun p : A × ℝ => F p.1 (fun _ => p.2))
      exact hF.comp (measurable_fst.prodMk (by
        rw [measurable_pi_iff]
        intro k
        exact measurable_snd))
  | n + 1, F, hF => by
      let tilted := PointProcess.tiltedLaw potential θ law
      let _ : IsProbabilityMeasure tilted :=
        PointProcess.tiltedLaw_isProbability hpotential θ law hnormalization
      let nextF : (A × ℝ) → (Fin (n + 1) → ℝ) → ENNReal :=
        fun p tail => F p.1 (prependHistory p.2 tail)
      have hnextF : Measurable (Function.uncurry nextF) := by
        change Measurable (fun q : (A × ℝ) × (Fin (n + 1) → ℝ) =>
          F q.1.1 (prependHistory q.1.2 q.2))
        exact hF.comp ((measurable_fst.comp measurable_fst).prodMk
          ((prependHistory_joint_measurable n).comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have hind := measurable_pointMeasureWeightedPathIterate_parameter
        hpotential θ law hnormalization n hnextF
      let G : (A × ℝ) × ℝ → ENNReal := fun p =>
        pointMeasureWeightedPathIterate potential θ law n
          (nextF p.1) (p.1.2 + p.2)
      have hG : Measurable G := by
        exact hind.comp (measurable_fst.prodMk
          ((measurable_snd.comp measurable_fst).add measurable_snd))
      have heq : (fun p : A × ℝ =>
          pointMeasureWeightedPathIterate potential θ law (n + 1)
            (F p.1) p.2) =
          fun p => ∫⁻ y, G (p, y) ∂tilted := by
        funext p
        rw [pointMeasureWeightedPathIterate_succ]
        exact (PointProcess.lintegral_tiltedLaw hpotential θ law
          (f := fun y => G (p, y))
          (hG.comp (measurable_const.prodMk measurable_id))).symm
      rw [heq]
      exact Measurable.lintegral_prod_right hG

theorem measurable_pointMeasureWeightedPathIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (θ : ℝ) (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential θ law)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) :
    Measurable (pointMeasureWeightedPathIterate potential θ law n F) := by
  let parameterized : Unit → (Fin (n + 1) → ℝ) → ENNReal := fun _ => F
  have hparameterized : Measurable (Function.uncurry parameterized) :=
    hF.comp measurable_snd
  have h := measurable_pointMeasureWeightedPathIterate_parameter
    hpotential θ law hnormalization n hparameterized
  have hcomp := h.comp ((measurable_const : Measurable
    (fun _ : ℝ => ())).prodMk measurable_id)
  convert hcomp using 1
  funext x
  rfl

/-- Unweighted intensity of complete ancestral histories. -/
noncomputable def pointMeasurePathIterate
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) :
    ∀ n : ℕ, ((Fin (n + 1) → ℝ) → ENNReal) → ℝ → ENNReal
  | 0, F, x => F (fun _ => x)
  | n + 1, F, x =>
      ∫⁻ ν, ∫⁻ z,
        pointMeasurePathIterate potential law n
          (fun tail => F (prependHistory x tail)) (x + potential z) ∂ν ∂law

theorem measurable_pointMeasurePathIterate_parameter
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    ∀ (n : ℕ) {F : A → (Fin (n + 1) → ℝ) → ENNReal},
      Measurable (Function.uncurry F) →
      Measurable (fun p : A × ℝ =>
        pointMeasurePathIterate potential law n (F p.1) p.2)
  | 0, F, hF => by
      change Measurable (fun p : A × ℝ => F p.1 (fun _ => p.2))
      exact hF.comp (measurable_fst.prodMk (by
        rw [measurable_pi_iff]
        intro k
        exact measurable_snd))
  | n + 1, F, hF => by
      let tilted := PointProcess.tiltedLaw potential (-1) law
      let _ : IsProbabilityMeasure tilted :=
        PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
      let nextF : (A × ℝ) → (Fin (n + 1) → ℝ) → ENNReal :=
        fun p tail => F p.1 (prependHistory p.2 tail)
      have hnextF : Measurable (Function.uncurry nextF) := by
        change Measurable (fun q : (A × ℝ) × (Fin (n + 1) → ℝ) =>
          F q.1.1 (prependHistory q.1.2 q.2))
        exact hF.comp ((measurable_fst.comp measurable_fst).prodMk
          ((prependHistory_joint_measurable n).comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have hind := measurable_pointMeasurePathIterate_parameter
        hpotential law hnormalization n hnextF
      let G : (A × ℝ) × ℝ → ENNReal := fun p =>
        pointMeasurePathIterate potential law n
          (nextF p.1) (p.1.2 + p.2)
      have hG : Measurable G := by
        exact hind.comp (measurable_fst.prodMk
          ((measurable_snd.comp measurable_fst).add measurable_snd))
      let W : (A × ℝ) × ℝ → ENNReal := fun p =>
        ENNReal.ofReal (Real.exp p.2) * G p
      have hW : Measurable W := by
        exact ((measurable_snd.exp.ennreal_ofReal).mul hG)
      have heq : (fun p : A × ℝ =>
          pointMeasurePathIterate potential law (n + 1) (F p.1) p.2) =
          fun p => ∫⁻ y, W (p, y) ∂tilted := by
        funext p
        change (∫⁻ ν, ∫⁻ z,
            G (p, potential z) ∂ν ∂law) = _
        simpa [W, tilted] using (PointProcess.lintegral_tiltedLaw_cancel
          hpotential (-1) law (f := fun y => G (p, y))
          (hG.comp (measurable_const.prodMk measurable_id))).symm
      rw [heq]
      exact Measurable.lintegral_prod_right hW

theorem measurable_pointMeasurePathIterate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F) :
    Measurable (pointMeasurePathIterate potential law n F) := by
  let parameterized : Unit → (Fin (n + 1) → ℝ) → ENNReal := fun _ => F
  have hparameterized : Measurable (Function.uncurry parameterized) :=
    hF.comp measurable_snd
  have h := measurable_pointMeasurePathIterate_parameter
    hpotential law hnormalization n hparameterized
  have hcomp := h.comp ((measurable_const : Measurable
    (fun _ : ℝ => ())).prodMk measurable_id)
  convert hcomp using 1
  funext x
  rfl

/-- Weighted many-to-one identity for arbitrary measurable functionals of
the complete ancestral history. -/
theorem pointMeasureWeightedPathManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      pointMeasureWeightedPathIterate potential (-1) law n F x =
        ∫⁻ increment, F (history n x increment)
          ∂pointMeasureIncrementLaw potential law
  | 0, F, hF, x => by
      let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
        pointMeasureIncrementLaw_isProbability hpotential law hnormalization
      have hhistory : ∀ increment : ℕ → ℝ,
          history 0 x increment = (fun _ : Fin 1 => x) := by
        intro increment
        funext k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        exact history_zero 0 x increment
      simp_rw [hhistory]
      simp [pointMeasureWeightedPathIterate]
  | n + 1, F, hF, x => by
      let tilted := PointProcess.tiltedLaw potential (-1) law
      let P := pointMeasureIncrementLaw potential law
      let _ : IsProbabilityMeasure tilted :=
        PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
      let _ : IsProbabilityMeasure P :=
        pointMeasureIncrementLaw_isProbability hpotential law hnormalization
      let tailF : (Fin (n + 1) → ℝ) → ENNReal := fun tail =>
        F (prependHistory x tail)
      have htailF : Measurable tailF :=
        hF.comp ((prependHistory_joint_measurable n).comp
          (measurable_const.prodMk measurable_id))
      let G : ℝ → ENNReal := fun y =>
        pointMeasureWeightedPathIterate potential (-1) law n tailF (x + y)
      have hG : Measurable G :=
        (measurable_pointMeasureWeightedPathIterate hpotential (-1) law
          hnormalization n htailF).comp
            (measurable_const.add measurable_id)
      calc
        pointMeasureWeightedPathIterate potential (-1) law (n + 1) F x =
            ∫⁻ y, G y ∂tilted := by
          rw [pointMeasureWeightedPathIterate_succ]
          exact (PointProcess.lintegral_tiltedLaw hpotential (-1) law
            (f := G) hG).symm
        _ = ∫⁻ y, ∫⁻ tail,
              F (prependHistory x (history n (x + y) tail)) ∂P ∂tilted := by
          apply lintegral_congr
          intro y
          exact pointMeasureWeightedPathManyToOne hpotential law
            hnormalization n htailF (x + y)
        _ = ∫⁻ increment, F (history (n + 1) x increment) ∂P := by
          change (∫⁻ y, ∫⁻ tail,
              F (prependHistory x (history n (x + y) tail))
                ∂Measure.infinitePi (fun _ : ℕ => tilted) ∂tilted) = _
          exact (lintegral_history_succ tilted n x hF).symm

/-- Unweighted path-functional many-to-one identity, with the reciprocal
terminal exponential weight on the spine path. -/
theorem pointMeasurePathManyToOne
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      pointMeasurePathIterate potential law n F x =
        ∫⁻ increment,
          ENNReal.ofReal (Real.exp (partialSum n increment)) *
            F (history n x increment)
          ∂pointMeasureIncrementLaw potential law
  | 0, F, hF, x => by
      let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
        pointMeasureIncrementLaw_isProbability hpotential law hnormalization
      have hhistory : ∀ increment : ℕ → ℝ,
          history 0 x increment = (fun _ : Fin 1 => x) := by
        intro increment
        funext k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        exact history_zero 0 x increment
      simp_rw [hhistory]
      simp [pointMeasurePathIterate, partialSum]
  | n + 1, F, hF, x => by
      let tilted := PointProcess.tiltedLaw potential (-1) law
      let P := pointMeasureIncrementLaw potential law
      let _ : IsProbabilityMeasure tilted :=
        PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
      let _ : IsProbabilityMeasure P :=
        pointMeasureIncrementLaw_isProbability hpotential law hnormalization
      let tailF : (Fin (n + 1) → ℝ) → ENNReal := fun tail =>
        F (prependHistory x tail)
      have htailF : Measurable tailF :=
        hF.comp ((prependHistory_joint_measurable n).comp
          (measurable_const.prodMk measurable_id))
      let G : ℝ → ENNReal := fun y =>
        pointMeasurePathIterate potential law n tailF (x + y)
      have hG : Measurable G :=
        (measurable_pointMeasurePathIterate hpotential law hnormalization
          n htailF).comp (measurable_const.add measurable_id)
      calc
        pointMeasurePathIterate potential law (n + 1) F x =
            ∫⁻ y, ENNReal.ofReal (Real.exp y) * G y ∂tilted := by
          change (∫⁻ ν, ∫⁻ z, G (potential z) ∂ν ∂law) = _
          simpa [tilted] using (PointProcess.lintegral_tiltedLaw_cancel
            hpotential (-1) law (f := G) hG).symm
        _ = ∫⁻ y, ENNReal.ofReal (Real.exp y) *
              (∫⁻ tail,
                ENNReal.ofReal (Real.exp (partialSum n tail)) *
                  F (prependHistory x (history n (x + y) tail)) ∂P)
              ∂tilted := by
          apply lintegral_congr
          intro y
          congr 1
          exact pointMeasurePathManyToOne hpotential law hnormalization
            n htailF (x + y)
        _ = ∫⁻ increment,
              ENNReal.ofReal (Real.exp (partialSum (n + 1) increment)) *
                F (history (n + 1) x increment) ∂P := by
          change (∫⁻ y, ENNReal.ofReal (Real.exp y) *
              (∫⁻ tail,
                ENNReal.ofReal (Real.exp (partialSum n tail)) *
                  F (prependHistory x (history n (x + y) tail))
                ∂Measure.infinitePi (fun _ : ℕ => tilted)) ∂tilted) = _
          exact (lintegral_history_succ_withWeight tilted n x hF).symm

/-- The weighted path sum in a labelled pre-sampled genealogy realizes the
enumeration-free random-measure path intensity. -/
theorem pointMeasureWeightedPathIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    pointMeasureWeightedPathIterate φ (-1)
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n F x =
      ∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ := by
  rw [pointMeasureWeightedPathManyToOne φ.measurable_toFun
    (μ.map (Combinatorics.Branching.stepPointMeasure
      (ι := ι) (X := E)))
    (pointMeasure_hasNormalization φ μ hboundary) n hF x]
  rw [pointMeasureIncrementLaw, pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]
  exact (weightedPathManyToOneCore φ μ hboundary n hF x).symm

/-- The unweighted path sum in a labelled pre-sampled genealogy realizes the
enumeration-free random-measure path intensity. -/
theorem pointMeasurePathIterate_map_stepPointMeasure
    {ι E : Type*} [Countable ι] [MeasurableSpace E] [Zero E]
    (φ : Combinatorics.Branching.Potential E)
    (μ : Measure (Combinatorics.Branching.Step ι E))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    pointMeasurePathIterate φ
        (μ.map (Combinatorics.Branching.stepPointMeasure
          (ι := ι) (X := E))) n F x =
      ∫⁻ ω, pathGeneration φ n F x ω ∂stepFieldLaw μ := by
  rw [pointMeasurePathManyToOne φ.measurable_toFun
    (μ.map (Combinatorics.Branching.stepPointMeasure
      (ι := ι) (X := E)))
    (pointMeasure_hasNormalization φ μ hboundary) n hF x]
  rw [pointMeasureIncrementLaw, pointMeasure_tiltedLaw_eq_tiltedPotentialLaw]
  exact (pathManyToOneCore φ μ hboundary n hF x).symm

end ProbabilityTheory.BranchingRandomWalk.Spine
