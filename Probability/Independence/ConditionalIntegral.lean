/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional integration for independent random variables

## Public declarations

- `ProbabilityTheory.IndepFun.condDistrib_ae_eq_const`: for measurable
  $X,Y$ into measurable value spaces, a probability measure $P$, and
  $X\perp Y$, if the value space of $Y$ is standard Borel, the conditional
  law of $Y$ given $X$ equals the marginal law of $Y$ almost everywhere.
- `ProbabilityTheory.IndepFun.condExp_prod_ae_eq_integral_map`:
  for any measurable independent pair and strongly measurable $f$ with
  $f(X,Y)\in L^1(P)$,
  $\mathbb E[f(X,Y)\mid X]=\int f(X,y)\,d(P\circ Y^{-1})(y)$ almost surely.
- `ProbabilityTheory.IndepFun.condExp_indicator_pairEvent_ae_eq_sectionProbability`:
  for measurable $E\subseteq A\times B$,
  $\mathbb E[\mathbf1_E(X,Y)\mid X](\omega)
   =(P\circ Y^{-1})\{y:(X(\omega),y)\in E\}$ almost surely.

The conditional-expectation identities use the product law of an independent
pair and Fubini's theorem. Only the explicit regular conditional distribution
statement requires a standard-Borel value space.
-/

open Filter MeasureTheory
open scoped MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory

variable {Sample Past Future Value : Type*}
  [MeasurableSpace Sample] [MeasurableSpace Past]
  [MeasurableSpace Future]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
  {P : Measure Sample} [IsProbabilityMeasure P]
  {X : Sample → Past} {Y : Sample → Future}

/-- The conditional distribution of an independent random variable is its
unconditional law. -/
theorem IndepFun.condDistrib_ae_eq_const (h : IndepFun X Y P)
    [StandardBorelSpace Future] [Nonempty Future]
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib Y X P =ᵐ[P.map X] Kernel.const Past (P.map Y) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd
    hX.aemeasurable hY.aemeasurable
  rw [h.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.compProd_const]

/-- Condition on `X` and integrate an independent input `Y` against its
unconditional law. -/
theorem IndepFun.condExp_prod_ae_eq_integral_map
    (h : IndepFun X Y P) (hX : Measurable X) (hY : Measurable Y)
    {f : Past × Future → Value} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun sample ↦ f (X sample, Y sample)) P) :
    condExp (MeasurableSpace.comap X inferInstance) P
        (fun sample ↦ f (X sample, Y sample)) =ᵐ[P]
      fun sample ↦ ∫ y, f (X sample, y) ∂P.map Y := by
  let pair : Sample → Past × Future := fun sample => (X sample, Y sample)
  let μPast : Measure Past := P.map X
  let μFuture : Measure Future := P.map Y
  let sectionIntegral : Past → Value := fun x => ∫ y, f (x, y) ∂μFuture
  have hpair : Measurable pair := hX.prodMk hY
  have hmap : P.map pair = μPast.prod μFuture := by
    simpa [pair, μPast, μFuture] using
      h.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hfJoint : Integrable f (P.map pair) := by
    apply (integrable_map_measure hf.aestronglyMeasurable hpair.aemeasurable).2
    simpa [pair, Function.comp_def] using hf_int
  have hfProd : Integrable f (μPast.prod μFuture) := by
    rw [← hmap]
    exact hfJoint
  have hsectionStrong : StronglyMeasurable sectionIntegral := by
    dsimp [sectionIntegral, μFuture]
    exact hf.integral_prod_right'
  have hsectionIntegrable : Integrable sectionIntegral μPast := by
    dsimp [sectionIntegral, μPast, μFuture]
    exact hfProd.integral_prod_left
  have hsectionCompStrong :
      StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun sample => sectionIntegral (X sample)) :=
    hsectionStrong.comp_measurable (Measurable.of_comap_le le_rfl)
  have hsectionCompIntegrable :
      Integrable (fun sample => sectionIntegral (X sample)) P :=
    (integrable_map_measure hsectionStrong.aestronglyMeasurable
      hX.aemeasurable).1 hsectionIntegrable
  have hsectionMeasurable (s : Set Sample)
      (hs : MeasurableSet[MeasurableSpace.comap X inferInstance] s)
      (hsfinite : P s < ⊤) :
      IntegrableOn (fun sample => sectionIntegral (X sample)) s P :=
    hsectionCompIntegrable.integrableOn
  have hsectionIntegral_eq (s : Set Sample)
      (hs : MeasurableSet[MeasurableSpace.comap X inferInstance] s)
      (hsfinite : P s < ⊤) :
      ∫ sample in s, sectionIntegral (X sample) ∂P =
        ∫ sample in s, f (X sample, Y sample) ∂P := by
    obtain ⟨A, hA, hpre⟩ := (MeasurableSpace.measurableSet_comap).1 hs
    rw [← hpre]
    have hAsection : AEStronglyMeasurable (A.indicator sectionIntegral) μPast :=
      hsectionStrong.aestronglyMeasurable.indicator₀ hA.nullMeasurableSet
    have hAprod : MeasurableSet (A ×ˢ (Set.univ : Set Future)) :=
      hA.prod MeasurableSet.univ
    have hAprodIndicator :
        AEStronglyMeasurable ((A ×ˢ (Set.univ : Set Future)).indicator f)
          (μPast.prod μFuture) :=
      hf.aestronglyMeasurable.indicator₀ hAprod.nullMeasurableSet
    have hAprodIndicatorJoint :
        AEStronglyMeasurable ((A ×ˢ (Set.univ : Set Future)).indicator f)
          (P.map pair) := by
      rw [hmap]
      exact hAprodIndicator
    calc
      ∫ sample in X ⁻¹' A, sectionIntegral (X sample) ∂P =
          ∫ sample, (A.indicator sectionIntegral) (X sample) ∂P := by
        calc
          _ = ∫ sample, (X ⁻¹' A).indicator
              (fun sample => sectionIntegral (X sample)) sample ∂P :=
                (integral_indicator (hA.preimage hX)).symm
          _ = _ := by
            apply integral_congr_ae
            exact ae_of_all P (fun sample => by
              by_cases hx : X sample ∈ A <;> simp [Set.indicator, hx])
      _ = ∫ x, A.indicator sectionIntegral x ∂μPast := by
        symm
        exact integral_map hX.aemeasurable hAsection
      _ = ∫ x in A, sectionIntegral x ∂μPast := integral_indicator hA
      _ = ∫ x in A, ∫ y, f (x, y) ∂μFuture ∂μPast := by
        rfl
      _ = ∫ z in A ×ˢ (Set.univ : Set Future), f z ∂μPast.prod μFuture := by
        simpa only [setIntegral_univ] using
          (setIntegral_prod f (s := A) (t := Set.univ) hfProd.integrableOn).symm
      _ = ∫ z, (A ×ˢ (Set.univ : Set Future)).indicator f z
          ∂μPast.prod μFuture := (integral_indicator hAprod).symm
      _ = ∫ z, (A ×ˢ (Set.univ : Set Future)).indicator f z ∂P.map pair := by
        rw [hmap]
      _ = ∫ sample, (A ×ˢ (Set.univ : Set Future)).indicator f (pair sample) ∂P := by
        exact integral_map hpair.aemeasurable hAprodIndicatorJoint
      _ = ∫ sample, (X ⁻¹' A).indicator
          (fun sample => f (X sample, Y sample)) sample ∂P := by
        congr 1
        funext sample
        by_cases hx : X sample ∈ A <;> simp [pair, Set.indicator, hx]
      _ = ∫ sample in X ⁻¹' A, f (X sample, Y sample) ∂P :=
        integral_indicator (hA.preimage hX)
  exact (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le
    hf_int hsectionMeasurable hsectionIntegral_eq
    hsectionCompStrong.aestronglyMeasurable).symm

/-- For independent random variables, the conditional expectation of the
indicator of a measurable pair event is the probability of its section under
the second marginal law. -/
theorem IndepFun.condExp_indicator_pairEvent_ae_eq_sectionProbability
    (h : IndepFun X Y P) (hX : Measurable X) (hY : Measurable Y)
    (E : Set (Past × Future)) (hE : MeasurableSet E) :
    condExp (MeasurableSpace.comap X inferInstance) P
        (fun sample => E.indicator (fun _ => (1 : ℝ)) (X sample, Y sample))
      =ᵐ[P] fun sample => (P.map Y).real {y | (X sample, y) ∈ E} := by
  let pair : Sample → Past × Future := fun sample => (X sample, Y sample)
  let f : Past × Future → ℝ := E.indicator (fun _ => (1 : ℝ))
  have hpair : Measurable pair := hX.prodMk hY
  have hpreimage : MeasurableSet (pair ⁻¹' E) := hE.preimage hpair
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hE
  have hfi : Integrable (fun sample => f (pair sample)) P :=
    (integrable_const (c := (1 : ℝ))).indicator hpreimage
  have hcond := h.condExp_prod_ae_eq_integral_map hX hY hf hfi
  have hsectionIntegral (x : Past) :
      (∫ y, f (x, y) ∂P.map Y) = (P.map Y).real {y | (x, y) ∈ E} := by
    let sectionEvent : Set Future := {y | (x, y) ∈ E}
    have hsection : MeasurableSet sectionEvent :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hfunction : (fun y => f (x, y)) =
        sectionEvent.indicator (fun _ => (1 : ℝ)) := by
      funext y
      simp [f, sectionEvent, Set.indicator]
    rw [hfunction]
    change (∫ y, sectionEvent.indicator (fun _ => (1 : ℝ)) y ∂P.map Y) =
      (P.map Y).real sectionEvent
    rw [integral_indicator_const (e := (1 : ℝ)) hsection,
      smul_eq_mul, mul_one]
  filter_upwards [hcond] with sample hsample
  rw [hsample, hsectionIntegral]

end ProbabilityTheory
