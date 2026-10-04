/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Stable.JumpModel.FiniteWindows
import Probability.Process.Stable.JumpModel.IncrementLaw
import Probability.Process.Stable.FiniteDimensional
import Probability.Process.Levy.Jump.PoissonConfiguration.Path

/-!
# Process law of the canonical cutoff jump path

The canonical entrance path uses the whole mark space for its small-jump
integral. Since its Poisson source is already restricted to the small-jump
band, this agrees almost surely at every fixed finite collection of times
with the explicitly cutoff path. The latter has independent stable
increments by the finite-window law.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem IsStrictlyAlphaStable.hasIndepIncrements_poissonEntrancePath_cutoff
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    HasIndepIncrements
      (fun t ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) t ω) (P := Ps.prod Pb) := by
  intro k t ht
  classical
  let S : Fin k → Set unitInterval := fun i => Set.Ioc (t i.castSucc) (t i.succ)
  have hS : ∀ i, MeasurableSet (S i) := fun _ => measurableSet_Ioc
  have hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    by_cases hij' : i < j
    · have hidx : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij')
      have htime := ht hidx
      exact (not_lt_of_ge htime) (hxj.1.trans_le hxi.2)
    · have hji' : j < i := lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm hij)
      have hidx : j.succ ≤ i.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hji')
      have htime := ht hidx
      exact (not_lt_of_ge htime) (hxi.1.trans_le hxj.2)
  have hsfirst := h.integrable_unitTime_smallJumpMark T hT hα n
  have hsmallNorm :
      (∫⁻ z : unitInterval × ℝ, ‖z.2‖ₑ
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) < ⊤ := by
    exact hasFiniteIntegral_iff_enorm.mpr hsfirst.hasFiniteIntegral
  have hsint := hds.ae_integrable_poissonRandomMeasure
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
    (by simpa only [Real.enorm_eq_ofReal_abs] using hsmallNorm)
  have hbigMass : ((volume : Measure unitInterval).prod
      (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (T.levyMeasure.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact T.levyMeasure_largeJumpBand_lt_top n
  have hbint := hdb.ae_integrable_of_finite_intensity
    (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbigMass
  let : ∀ i : Fin k, DecidablePred (fun z : unitInterval × ℝ => z.1 ∈ S i) :=
    fun _ z => Classical.propDecidable _
  have hsi : ∀ i, ∀ᵐ ω : Ωs ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω) := by
    intro i
    filter_upwards [hsint] with ω hω
    have hi := hω.indicator ((hS i).preimage measurable_fst)
    convert hi using 1
    funext z
    by_cases hz : z.1 ∈ S i <;> simp [hz]
  have hbi : ∀ i, ∀ᵐ ω : Ωb ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω) := by
    intro i
    filter_upwards [hbint] with ω hω
    have hi := hω.indicator ((hS i).preimage measurable_fst)
    convert hi using 1
    funext z
    by_cases hz : z.1 ∈ S i <;> simp [hz]
  let P : Measure (Ωs × Ωb) := Ps.prod Pb
  let W : Ωs × Ωb → Fin k → ℝ :=
    poissonWindowIntegralVector (Ks := Ks) (Xs := Xs) (Kb := Kb) (Xb := Xb) S
  let D : Ωs × Ωb → Fin k → ℝ := fun ω i =>
    poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n)
        (t i.succ) ω -
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n)
        (t i.castSucc) ω
  have hpath : ∀ i, ∀ᵐ ω ∂P, D ω i = W ω i := by
    intro i
    simpa [D, W, S, poissonWindowIntegralVector, Set.mem_Ioc] using
      ae_poissonEntrancePath_cutoff_sub_eq_timeWindow n hds hdb hsfirst
        (T.levyMeasure_largeJumpBand_lt_top n)
        (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i))
  have hvecAE : D =ᵐ[P] W := by
    filter_upwards [(ae_all_iff.2 hpath)] with ω hω
    exact funext hω
  have hwindowMap := h.measure_map_poissonWindowIntegralVector_eq_pi
    T hT hα n hds hdb S hS hdisj hsi hbi
  have hwindowMeas : AEMeasurable W P := by
    simpa [P, W] using
      poissonWindowIntegralVector_aemeasurable hds hdb S hS hsi hbi
  have hwindowLaw : HasLaw W
      (Measure.pi fun i : Fin k => μ.map fun x =>
        ((volume : Measure unitInterval) (S i)).toReal ^ (1 / α) * x) P :=
    ⟨hwindowMeas, hwindowMap⟩
  have hcutSingle : ∀ i, HasLaw (fun ω => D ω i)
      (μ.map fun x => (((volume : Measure unitInterval) (S i)).toReal ^
        (1 / α)) * x) P := by
    intro i
    have hae : (fun ω => D ω i) =ᵐ[P] (fun ω => W ω i) := by
      exact hpath i
    have hmeas : AEMeasurable (fun ω => D ω i) P :=
      ((measurable_pi_apply i).comp_aemeasurable hwindowMeas).congr hae.symm
    have hmap : P.map (fun ω => D ω i) =
        μ.map fun x => (((volume : Measure unitInterval) (S i)).toReal ^
          (1 / α)) * x := by
      simpa [P, D, S] using
        h.law_poissonEntrancePath_cutoff_increment T hT hα n hds hdb
          (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i))
    exact ⟨hmeas, hmap⟩
  have hDlaw : HasLaw D
      (Measure.pi fun i : Fin k => μ.map fun x =>
        ((volume : Measure unitInterval) (S i)).toReal ^ (1 / α) * x) P :=
    hwindowLaw.congr hvecAE
  have hiind : iIndepFun (fun i ω => D ω i) (μ := P) :=
    (iIndepFun_iff_hasLaw_pi_pi hcutSingle).mpr hDlaw
  have hcanonicalEq : ∀ i,
      (fun ω =>
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) (t i.succ) ω -
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) (t i.castSucc) ω) =ᵐ[P]
      (fun ω => D ω i) := by
    intro (i : Fin k)
    filter_upwards [
      ae_poissonEntrancePath_canonical_eq_cutoff n hds hdb (t i.succ),
      ae_poissonEntrancePath_canonical_eq_cutoff n hds hdb (t i.castSucc)] with ω h₁ h₂
    simp [D, h₁, h₂]
  have hcanonicalIndep : iIndepFun
      (fun (i : Fin k) ω =>
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) (t i.succ) ω -
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) (t i.castSucc) ω) (μ := P) :=
    (iIndepFun_congr hcanonicalEq).mpr hiind
  simpa [P] using hcanonicalIndep

set_option maxHeartbeats 1000000 in
theorem IsStrictlyAlphaStable.hasStableClockIncrements_poissonEntrancePath
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    HasStableClockIncrements α μ (fun t : unitInterval => (t : ℝ))
      (fun t ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) t ω) (Ps.prod Pb) := by
  let P : Measure (Ωs × Ωb) := Ps.prod Pb
  let clock : unitInterval → ℝ := fun t => (t : ℝ)
  have hstart := IsPoissonPointFamily.ae_poissonEntrancePath_canonical_start_eq_zero
    n hds hdb
  have hindep := h.hasIndepIncrements_poissonEntrancePath_cutoff
    T hT hα n hds hdb
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    exact hst
  · simp
  · simpa [P] using hstart
  · simpa [P] using hindep
  · intro s t hst
    let S : Unit → Set unitInterval := fun _ => Set.Ioc s t
    let W : Ωs × Ωb → Unit → ℝ :=
      poissonWindowIntegralVector (Ks := Ks) (Xs := Xs) (Kb := Kb) (Xb := Xb) S
    have hSi : ∀ i : Unit, MeasurableSet (S i) := fun _ => measurableSet_Ioc
    let : ∀ i : Unit, DecidablePred (fun z : unitInterval × ℝ => z.1 ∈ S i) :=
      fun _ z => Classical.propDecidable _
    have hsfirst := h.integrable_unitTime_smallJumpMark T hT hα n
    have hsmallNorm :
        (∫⁻ z : unitInterval × ℝ, ‖z.2‖ₑ
          ∂((volume : Measure unitInterval).prod
            (T.levyMeasure.restrict (smallJumpBand n)))) < ⊤ :=
      hasFiniteIntegral_iff_enorm.mpr hsfirst.hasFiniteIntegral
    have hsint := hds.ae_integrable_poissonRandomMeasure
      (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2))
      (by simpa only [Real.enorm_eq_ofReal_abs] using hsmallNorm)
    have hbigMass : ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
      have hmass := unitTime_prod_markWindow
        (T.levyMeasure.restrict (largeJumpBand n)) Set.univ
      simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
      rw [hmass]
      exact T.levyMeasure_largeJumpBand_lt_top n
    have hbint := hdb.ae_integrable_of_finite_intensity
      (by fun_prop : Measurable (fun z : unitInterval × ℝ => z.2)) hbigMass
    have hsi : ∀ i : Unit, ∀ᵐ ω : Ωs ∂Ps, Integrable
        (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
        (poissonRandomMeasure Ks Xs ω) := by
      intro i
      filter_upwards [hsint] with ω hω
      have hi := hω.indicator ((hSi i).preimage measurable_fst)
      convert hi using 1
      funext z
      by_cases hz : z.1 ∈ S i <;> simp [hz]
    have hbi : ∀ i : Unit, ∀ᵐ ω : Ωb ∂Pb, Integrable
        (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
        (poissonRandomMeasure Kb Xb ω) := by
      intro i
      filter_upwards [hbint] with ω hω
      have hi := hω.indicator ((hSi i).preimage measurable_fst)
      convert hi using 1
      funext z
      by_cases hz : z.1 ∈ S i <;> simp [hz]
    have hWmeas : AEMeasurable W (Ps.prod Pb) := by
      simpa [W] using poissonWindowIntegralVector_aemeasurable hds hdb S hSi hsi hbi
    have hcutAE :
        (fun ω => poissonEntrancePath Ks Xs Kb Xb
            (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω -
          poissonEntrancePath Ks Xs Kb Xb
            (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) s ω) =ᵐ[P]
        (fun ω => W ω ()) := by
      filter_upwards [ae_poissonEntrancePath_cutoff_sub_eq_timeWindow n hds hdb
        hsfirst (T.levyMeasure_largeJumpBand_lt_top n) s t hst] with ω hω
      simpa [W, S, poissonWindowIntegralVector, Set.mem_Ioc] using hω
    have hcanonicalAE :
        (fun ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
            (Set.univ ×ˢ largeJumpBand n) t ω -
          poissonEntrancePath Ks Xs Kb Xb Set.univ
            (Set.univ ×ˢ largeJumpBand n) s ω) =ᵐ[P]
        (fun ω => poissonEntrancePath Ks Xs Kb Xb
            (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω -
          poissonEntrancePath Ks Xs Kb Xb
            (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) s ω) := by
      filter_upwards [ae_poissonEntrancePath_canonical_eq_cutoff n hds hdb t,
        ae_poissonEntrancePath_canonical_eq_cutoff n hds hdb s] with ω ht hs
      simp [ht, hs]
    have hcanonicalWindowAE :
        (fun ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
            (Set.univ ×ˢ largeJumpBand n) t ω -
          poissonEntrancePath Ks Xs Kb Xb Set.univ
            (Set.univ ×ˢ largeJumpBand n) s ω) =ᵐ[P]
        (fun ω => W ω ()) :=
      hcanonicalAE.trans hcutAE
    have hmeas : AEMeasurable
        (fun ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) t ω -
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) s ω) P :=
      ((measurable_pi_apply ()).comp_aemeasurable hWmeas).congr
        hcanonicalWindowAE.symm
    have hmap : P.map (fun ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) t ω -
      poissonEntrancePath Ks Xs Kb Xb Set.univ
        (Set.univ ×ˢ largeJumpBand n) s ω) =
      μ.map fun x => (((volume : Measure unitInterval) (Set.Ioc s t)).toReal ^
        (1 / α)) * x := by
      rw [Measure.map_congr hcanonicalAE]
      exact h.law_poissonEntrancePath_cutoff_increment T hT hα n hds hdb s t hst
    have hlaw : HasLaw
        (fun ω => poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) t ω -
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) s ω)
        (μ.map fun x => (((volume : Measure unitInterval) (Set.Ioc s t)).toReal ^
          (1 / α)) * x) P := ⟨hmeas, hmap⟩
    have hvol : (((volume : Measure unitInterval) (Set.Ioc s t)).toReal) =
        (t : ℝ) - (s : ℝ) := by
      rw [unitInterval.volume_Ioc]
      exact ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hst))
    have hclock : clock t - clock s =
        ((volume : Measure unitInterval) (Set.Ioc s t)).toReal := by
      dsimp [clock]
      rw [hvol.symm]
    have hfunctions :
        (fun x => (clock t - clock s) ^ (1 / α) * x) =
          (fun x => (((volume : Measure unitInterval) (Set.Ioc s t)).toReal ^
            (1 / α)) * x) := by
      funext x
      rw [hclock]
    rw [hfunctions]
    exact hlaw

end ProbabilityTheory
