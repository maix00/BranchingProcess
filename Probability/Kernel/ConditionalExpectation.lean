/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Probability.Kernel.Composition.InfinitePi
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Conditional integration from an explicit joint kernel law

## Public declarations

* `ProbabilityTheory.HasCondDistrib.condLExp_eq`: for an s-finite measure `P`,
  a measurable observation `X` with sigma-finite `P` restricted to its
  generated sigma-algebra, its supplied native conditional law `κ`, and
  any measurable nonnegative payoff `g`,
  $E[g(X,Y)\mid X]=\int g(X,y)\,\kappa(X,dy)$. The kernel is s-finite;
  neither integrability nor a standard-Borel value space is assumed.

* `ProbabilityTheory.Kernel.condExp_of_jointLaw`: if
  $P\circ(X,Y)^{-1}=(P\circ X^{-1})\otimes\kappa$, then for strongly
  measurable $g$ with $g(X,Y)\in L^1(P)$,
  $E[g(X,Y)\mid X]=\int g(X,y)\,\kappa(X,dy)$ almost surely.

* `ProbabilityTheory.Kernel.condExp_coordinate_of_jointLaw`: if the conditional
  law of `(Yᵢ)ᵢ` given `X` is `⊗ᵢ κᵢ(X)`, then
  `E[g(Yᵢ) | X,(Yⱼ)_(j ≠ i)] = ∫ g dκᵢ(X)` for strongly measurable,
  integrable payoffs. Coordinate spaces are arbitrary measurable spaces.

* `ProbabilityTheory.Kernel.hasCondDistrib_of_condExp_generator`: a supplied
  probability kernel is the native `HasCondDistrib` of `Y` given `X` if its
  conditional indicator identities hold on a generating pi-system. No regular
  conditional-distribution existence or standard-Borel hypothesis is required.

The supplied joint-law identity identifies an existing conditional kernel;
no regular-conditional-distribution construction or standard-Borel
hypothesis is needed. The proof uses Mathlib's kernel Fubini theorem and
conditional-expectation uniqueness.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

/-- Integrate a conditional kernel identified by the joint law, on arbitrary
measurable value spaces. -/
theorem condExp_of_jointLaw {Ω A B E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hlaw : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X) ⊗ₘ κ)
    {g : A × B → E} (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    P[fun ω ↦ g (X ω, Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω ↦ ∫ y, g (X ω, y) ∂κ (X ω) := by
  have hj : Integrable g ((P.map X) ⊗ₘ κ) := by
    rw [← hlaw]
    exact (integrable_map_measure hg.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).mpr hgi
  let G : A → E := fun x ↦ ∫ y, g (x, y) ∂κ x
  have hG : StronglyMeasurable G := hg.integral_kernel_prod_right'
  have hGi : Integrable G (P.map X) := by
    change Integrable g ((Kernel.const Unit (P.map X) ⊗ₖ
      κ.prodMkLeft Unit) ()) at hj
    simpa only [Kernel.const_apply, Kernel.prodMkLeft_apply] using hj.integral_compProd
  have hcomp : Integrable (fun ω ↦ G (X ω)) P :=
    (integrable_map_measure hG.aestronglyMeasurable hX.aemeasurable).mp hGi
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hgi
    (fun _ _ _ ↦ hcomp.integrableOn) ?_ ?_).symm
  · rintro _ ⟨t, ht, rfl⟩ _
    change ∫ ω in X ⁻¹' t, G (X ω) ∂P = ∫ ω in X ⁻¹' t, g (X ω, Y ω) ∂P
    rw [← setIntegral_map ht hG.aestronglyMeasurable hX.aemeasurable]
    calc
      ∫ x in t, G x ∂P.map X =
          ∫ p in t ×ˢ Set.univ, g p ∂(P.map X) ⊗ₘ κ := by
        symm
        simpa only [setIntegral_univ] using
          Measure.setIntegral_compProd ht MeasurableSet.univ hj.integrableOn
      _ = ∫ p in t ×ˢ Set.univ, g p ∂P.map (fun ω ↦ (X ω, Y ω)) := by rw [hlaw]
      _ = _ := by
        rw [setIntegral_map (ht.prod MeasurableSet.univ) hg.aestronglyMeasurable
          (hX.prodMk hY).aemeasurable]
        simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
  · exact (hG.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

private lemma map_infinitePi_split {I : Type*} {B : I → Type*}
    [∀ i, MeasurableSpace (B i)] (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (ν i)] (i : I) :
    (Measure.infinitePi ν).map (fun y => ((fun j : {j : I // j ≠ i} => y j.1), y i)) =
      (Measure.infinitePi (fun j : {j : I // j ≠ i} => ν j.1)).prod (ν i) := by
  classical
  have hind := (iIndepFun_infinitePi (P := ν) (X := fun _ y => y)
    (fun _ => measurable_id)).indepFun_set {j | j ≠ i} {i} (by simp)
      (fun j => measurable_pi_apply j)
  have hs := hind.comp measurable_id (measurable_pi_apply (⟨i, rfl⟩ : ({i} : Set I)))
  change ProbabilityTheory.IndepFun (fun y : Π j, B j => fun j : {j : I // j ≠ i} => y j.1)
    (fun y => y i) (Measure.infinitePi ν) at hs
  rw [hs.map_prod_eq_prod_map_map
      (show Measurable (fun y : Π j, B j => fun j : {j : I // j ≠ i} => y j.1) from
        by fun_prop).aemeasurable
      (measurable_pi_apply i).aemeasurable,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective,
    Measure.infinitePi_map_eval]

/-- In a conditionally independent family, observing every other coordinate
leaves one coordinate's explicitly supplied conditional kernel unchanged. -/
theorem condExp_coordinate_of_jointLaw {Ω A I E : Type*} {B : I → Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [∀ i, MeasurableSpace (B i)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → Π i, B i) (hX : Measurable X) (hY : Measurable Y)
    (κ : (i : I) → Kernel A (B i)) [∀ i, IsMarkovKernel (κ i)]
    (hlaw : P.map (fun ω => (X ω, Y ω)) = (P.map X) ⊗ₘ infinitePi κ)
    (i : I) (g : B i → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω => g (Y ω i)) P) :
    P[fun ω => g (Y ω i) | MeasurableSpace.comap
      (fun ω => (X ω, fun j : {j : I // j ≠ i} => Y ω j.1)) inferInstance] =ᵐ[P]
      fun ω => ∫ b, g b ∂κ i (X ω) := by
  classical
  let R := Π j : {j : I // j ≠ i}, B j.1
  let split (y : Π i, B i) : R × B i := (fun j => y j.1, y i)
  let η : Kernel A R := infinitePi (fun j : {j : I // j ≠ i} => κ j.1)
  let ζ : Kernel (A × R) (B i) := (κ i).prodMkRight R
  have hsplit : Measurable split := by fun_prop
  have heq : (infinitePi κ).map split = η ⊗ₖ ζ := by
    apply Kernel.ext
    intro a
    rw [map_apply _ hsplit, infinitePi_apply, map_infinitePi_split]
    ext C hC
    rw [Measure.prod_apply hC, compProd_apply hC]
    rfl
  have hj : P.map (fun ω => ((X ω, fun j : {j : I // j ≠ i} => Y ω j.1), Y ω i)) =
      (P.map X) ⊗ₘ η ⊗ₘ ζ := by
    have h := congrArg (fun μ => μ.map (Prod.map id split)) hlaw
    rw [Measure.map_map (by fun_prop) (hX.prodMk hY),
      ← Measure.compProd_map hsplit, heq] at h
    have h' := congrArg (fun μ => μ.map MeasurableEquiv.prodAssoc.symm) h
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.compProd_assoc] at h'
    exact h'
  have hm : P.map (fun ω => (X ω, fun j : {j : I // j ≠ i} => Y ω j.1)) =
      (P.map X) ⊗ₘ η := by
    have h := congrArg Measure.fst hj
    rw [Measure.fst_map_prodMk (by fun_prop) (by fun_prop), Measure.fst_compProd] at h
    exact h
  have hcond := condExp_of_jointLaw P
    (fun ω => (X ω, fun j : {j : I // j ≠ i} => Y ω j.1)) (fun ω => Y ω i)
    (by fun_prop) (by fun_prop) ζ (by rw [hm]; exact hj)
    (g := fun p => g p.2) (hg.comp_measurable measurable_snd) hgi
  exact hcond

private lemma joint_rectangle_eq_of_condExp_indicator {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) (κ : Kernel A B) [IsMarkovKernel κ]
    {U : Set A} {V : Set B} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hc : P[fun ω => V.indicator (fun _ => (1 : ℝ)) (Y ω) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω => (κ (X ω)).real V) :
    P.map (fun ω => (X ω, Y ω)) (U ×ˢ V) = ((P.map X) ⊗ₘ κ) (U ×ˢ V) := by
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hpre : (fun ω => (X ω, Y ω)) ⁻¹' (U ×ˢ V) = X ⁻¹' U ∩ Y ⁻¹' V := rfl
  have hfi : Integrable (fun ω => V.indicator (fun _ => (1 : ℝ)) (Y ω)) P := by
    apply Integrable.of_bound
      ((stronglyMeasurable_const.indicator hV).comp_measurable hY).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hy : Y ω ∈ V <;> simp [hy]
  have hUX : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' U) := ⟨U, hU, rfl⟩
  have hl : (P.map (fun ω => (X ω, Y ω))).real (U ×ˢ V) =
      ∫ ω in X ⁻¹' U, V.indicator (fun _ => (1 : ℝ)) (Y ω) ∂P := by
    rw [Measure.real, Measure.map_apply hpair (hU.prod hV), hpre]
    change P.real (X ⁻¹' U ∩ Y ⁻¹' V) = _
    rw [← setIntegral_one_eq_measureReal, ← setIntegral_indicator (hV.preimage hY)]
    apply setIntegral_congr_fun (hU.preimage hX)
    intro ω _
    by_cases hy : Y ω ∈ V <;> simp [hy]
  have hr : ((P.map X) ⊗ₘ κ).real (U ×ˢ V) =
      ∫ ω in X ⁻¹' U, (κ (X ω)).real V ∂P := by
    rw [← setIntegral_one_eq_measureReal]
    have hi : IntegrableOn (fun _ : A × B => (1 : ℝ)) (U ×ˢ V) ((P.map X) ⊗ₘ κ) :=
      (integrable_const (1 : ℝ)).integrableOn
    rw [Measure.setIntegral_compProd hU hV hi]
    simp only [setIntegral_one_eq_measureReal]
    exact setIntegral_map hU ((κ.measurable_coe hV).ennreal_toReal.aestronglyMeasurable)
      hX.aemeasurable
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (P.map (fun ω => (X ω, Y ω))).real (U ×ˢ V) = ((P.map X) ⊗ₘ κ).real (U ×ˢ V)
  rw [hl, hr, ← setIntegral_condExp hX.comap_le hfi hUX]
  exact setIntegral_congr_ae (hU.preimage hX) (hc.mono fun _ hx _ => hx)

/-- Conditional indicator identities on a generating pi-system identify an
explicit conditional kernel on arbitrary measurable value spaces. -/
theorem hasCondDistrib_of_condExp_generator {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [mB : MeasurableSpace B]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) (κ : Kernel A B) [IsMarkovKernel κ]
    (C : Set (Set B)) (hgen : mB = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hc : ∀ V ∈ C, P[fun ω => V.indicator (fun _ => (1 : ℝ)) (Y ω) |
      MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω => (κ (X ω)).real V) :
    HasCondDistrib Y X κ P := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  apply Measure.ext_prod
  intro U V hU hV
  let ν := (P.map (fun ω => (X ω, Y ω))).restrict (U ×ˢ Set.univ)
  let η := ((P.map X) ⊗ₘ κ).restrict (U ×ˢ Set.univ)
  have hs (M : Measure (A × B)) {W : Set B} (hW : MeasurableSet W) :
      (M.restrict (U ×ˢ Set.univ)).snd W = M (U ×ˢ W) := by
    rw [Measure.snd_apply hW, Measure.restrict_apply (hW.preimage measurable_snd)]
    congr 1
    ext p
    simp [and_comm]
  have hν : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have heq : ν.snd = η.snd := by
    apply ext_of_generate_finite C hgen hpi
    · intro W hWC
      have hW : MeasurableSet W := by rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom hWC
      rw [show ν.snd W = _ from hs _ hW, show η.snd W = _ from hs _ hW]
      exact joint_rectangle_eq_of_condExp_indicator P X Y hX hY κ hU hW (hc W hWC)
    · rw [Measure.snd_univ, Measure.snd_univ]
      change (P.map (fun ω => (X ω, Y ω))).restrict (U ×ˢ Set.univ) Set.univ =
        ((P.map X) ⊗ₘ κ).restrict (U ×ˢ Set.univ) Set.univ
      rw [Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      have hset : U ×ˢ (Set.univ : Set B) = Prod.fst ⁻¹' U := by ext p; simp
      rw [hset, ← Measure.fst_apply hU, ← Measure.fst_apply hU,
        Measure.fst_map_prodMk hX hY, Measure.fst_compProd]
  have h := congrArg (fun μ => μ V) heq
  rw [show ν.snd V = _ from hs _ hV, show η.snd V = _ from hs _ hV] at h
  exact h

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasCondDistrib

open scoped ENNReal

/-- Nonnegative conditional integration of a supplied native conditional law.
The observation is measurable; the pair need only be almost surely measurable,
as already supplied by `HasCondDistrib`. -/
theorem condLExp_eq {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [SFinite P]
    {X : Ω → A} {Y : Ω → B} {κ : Kernel A B} [IsSFiniteKernel κ]
    (hd : HasCondDistrib Y X κ P) (hX : Measurable X)
    [SigmaFinite (P.trim hX.comap_le)]
    {g : A × B → ℝ≥0∞} (hg : Measurable g) :
    P⁻[fun ω => g (X ω, Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω => ∫⁻ y, g (X ω, y) ∂κ (X ω) := by
  let G : A → ℝ≥0∞ := fun x => ∫⁻ y, g (x, y) ∂κ x
  have hG : Measurable G := hg.lintegral_kernel_prod_right'
  refine (ae_eq_condLExp (hm := hX.comap_le) P
    (fun ω => g (X ω, Y ω)) (hG.comp (Measurable.of_comap_le le_rfl)) ?_).symm
  rintro _ ⟨U, hU, rfl⟩
  change ∫⁻ ω in X ⁻¹' U, G (X ω) ∂P = ∫⁻ ω in X ⁻¹' U, g (X ω, Y ω) ∂P
  rw [← setLIntegral_map hU hG hX]
  calc
    ∫⁻ x in U, G x ∂P.map X =
        ∫⁻ p in U ×ˢ Set.univ, g p ∂(P.map X) ⊗ₘ κ := by
      simpa only [Measure.restrict_univ] using
        (Measure.setLIntegral_compProd hg hU MeasurableSet.univ).symm
    _ = ∫⁻ p in U ×ˢ Set.univ, g p ∂P.map (fun ω => (X ω, Y ω)) := by
      rw [hd.map_eq]
    _ = _ := by
      rw [← lintegral_indicator (hU.prod MeasurableSet.univ),
        lintegral_map' (hg.indicator (hU.prod MeasurableSet.univ)).aemeasurable hd.aemeasurable,
        ← lintegral_indicator (hU.preimage hX)]
      apply lintegral_congr
      intro ω
      by_cases hω : X ω ∈ U <;> simp [hω]

end ProbabilityTheory.HasCondDistrib
