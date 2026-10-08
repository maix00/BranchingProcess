/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Process
public import Probability.Process.Path.Skorokhod

/-!
# Stable process laws on càdlàg path space

This file packages the canonical coordinate process on `CadlagPath` and its
stable clock-increment law. The finite-horizon path laws used by small
deviation arguments are instances of this general interface.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A path law with stable increment distributions for an arbitrary ordered
time axis and clock. This also covers finite-horizon restrictions such as
`unitInterval`. -/
def IsStableClockProcessLaw {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time] [MeasurableSpace (CadlagPath Time ℝ)]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (P : Measure (CadlagPath Time ℝ)) [IsProbabilityMeasure P] : Prop :=
  HasStableClockIncrements α μ clock cadlagPathProcess P

namespace IsStableClockProcessLaw

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable [MeasurableSpace (CadlagPath Time ℝ)]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {P : Measure (CadlagPath Time ℝ)} [IsProbabilityMeasure P]

/-- The reference increment law of a stable clock-process law is strictly
stable. -/
theorem strictlyStable (h : IsStableClockProcessLaw α μ clock P) :
    IsStrictlyAlphaStable α μ :=
  HasStableClockIncrements.strictlyStable h

/-- The canonical paths start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableClockProcessLaw α μ clock P) :
    ∀ᵐ f ∂P, f ⊥ = 0 := by
  simpa [IsStableClockProcessLaw, cadlagPathProcess] using
    HasStableClockIncrements.ae_start_eq_zero h

/-- The canonical process has independent increments. -/
theorem indepIncrements (h : IsStableClockProcessLaw α μ clock P) :
    HasIndepIncrements cadlagPathProcess P :=
  HasStableClockIncrements.indepIncrements h

/-- The increment of the canonical process over `[s,t]` has the stable law
scaled by the elapsed clock time. -/
theorem increment_hasLaw (h : IsStableClockProcessLaw α μ clock P)
    (s t : Time) (hst : s ≤ t) :
    HasLaw (fun f => f t - f s)
      (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P := by
  simpa [IsStableClockProcessLaw, cadlagPathProcess] using
    HasStableClockIncrements.increment_hasLaw h s t hst

/-- A stable clock-process law on càdlàg path space gives an actual process
with almost-surely càdlàg paths. -/
theorem isStableClockProcess (h : IsStableClockProcessLaw α μ clock P) :
    IsStableClockProcess α μ clock cadlagPathProcess P := by
  refine ⟨h, ae_of_all _ fun f => ?_⟩
  change IsCadlag (fun t => f t)
  exact f.isCadlag_toFun

end IsStableClockProcessLaw

namespace HasStableClockIncrements

variable {Time : Type*} [PartialOrder Time] [OrderBot Time]
  [TopologicalSpace Time] [MeasurableSpace (CadlagPath Time ℝ)]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Transfer a process' stable clock-increment specification to the law of
its bundled càdlàg paths. The pathwise evaluation identity is explicit; this
lets source models choose their own measurable path-valued realization. -/
theorem law_of_pathMap {X : Time → Ω → ℝ}
    (hX : HasStableClockIncrements α μ clock X P)
    {path : Ω → CadlagPath Time ℝ} {Q : Measure (CadlagPath Time ℝ)}
    [IsProbabilityMeasure Q]
    (hpath : HasLaw path Q P)
    (heval : ∀ t, Measurable (fun f : CadlagPath Time ℝ => f t))
    (hpathEval : ∀ t ω, path ω t = X t ω) :
    IsStableClockProcessLaw α μ clock Q := by
  refine ⟨hX.strictlyStable, hX.monotone_clock, hX.clock_bot, ?_, ?_, ?_⟩
  · have hmeas : Measurable (fun f : CadlagPath Time ℝ => f ⊥ = (0 : ℝ)) := by
      exact (heval ⊥).eq measurable_const
    apply (hpath.ae_iff hmeas).mp
    filter_upwards [hX.ae_start_eq_zero] with ω hω
    simpa [hpathEval] using hω
  · intro n t ht
    let sourceIncrement : Ω → Fin n → ℝ := fun ω i =>
      X (t i.succ) ω - X (t i.castSucc) ω
    let pathIncrement : CadlagPath Time ℝ → Fin n → ℝ := fun f i =>
      f (t i.succ) - f (t i.castSucc)
    let incrementLaw : Fin n → Measure ℝ := fun i =>
      μ.map fun x => (clock (t i.succ) - clock (t i.castSucc)) ^ (1 / α) * x
    have hsourceJoint : HasLaw sourceIncrement (Measure.pi incrementLaw) P := by
      simpa [sourceIncrement, incrementLaw] using hX.increments_hasLaw_pi n t ht
    have hpathJointSource : HasLaw (fun ω => pathIncrement (path ω))
        (Measure.pi incrementLaw) P := by
      refine hsourceJoint.congr (Filter.Eventually.of_forall fun ω => ?_)
      funext i
      simp [pathIncrement, sourceIncrement, hpathEval]
    have hpathIncrementMeasurable : Measurable pathIncrement := by
      apply Measurable.of_eval
      intro i
      exact (heval (t i.succ)).sub (heval (t i.castSucc))
    have hpathJoint : HasLaw pathIncrement (Measure.pi incrementLaw) Q := by
      have h := HasLaw.comp_of_hasLaw_comp
        hpathIncrementMeasurable.aemeasurable
        hpath HasLaw.id hpathJointSource
      simpa [Function.comp_def] using h
    have hcoordinate (i : Fin n) :
        HasLaw (fun f : CadlagPath Time ℝ => pathIncrement f i)
          (incrementLaw i) Q := by
      let evalIncrement : CadlagPath Time ℝ → ℝ := fun f =>
        f (t i.succ) - f (t i.castSucc)
      have hevalIncrement : Measurable evalIncrement := by
        exact (heval (t i.succ)).sub (heval (t i.castSucc))
      have hsource : HasLaw (fun ω => evalIncrement (path ω))
          (incrementLaw i) P := by
        have h := hX.increment_hasLaw (t i.castSucc) (t i.succ)
          (ht (Fin.castSucc_le_succ i))
        refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
        simp [evalIncrement, hpathEval]
      have h := HasLaw.comp_of_hasLaw_comp
        hevalIncrement.aemeasurable
        hpath HasLaw.id hsource
      simpa [evalIncrement, pathIncrement, Function.comp_def] using h
    exact (iIndepFun_iff_hasLaw_pi_pi hcoordinate).2 hpathJoint
  · intro s t hst
    let increment : CadlagPath Time ℝ → ℝ := fun f => f t - f s
    have hincrement : Measurable increment := (heval t).sub (heval s)
    have hsource : HasLaw (fun ω => increment (path ω))
        (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P := by
      have h := hX.increment_hasLaw s t hst
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [increment, hpathEval]
    have h := HasLaw.comp_of_hasLaw_comp
      hincrement.aemeasurable
      hpath HasLaw.id hsource
    simpa [increment, Function.comp_def, cadlagPathProcess] using h

end HasStableClockIncrements

end ProbabilityTheory

end
