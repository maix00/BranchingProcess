/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindowShift
public import Probability.Process.Brownian.AboveStart.FirstWindowContinuity

/-!
# Almost-sure continuity of Brownian first-window shifts

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_shiftAtFirstNonnegativeWindowStart`:
  $f\mapsto\Phi(f)$ is continuous at almost every Brownian path.
- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_shiftAtFirstNonnegativeWindowStartUpTo`:
  the same assertion for $\Phi_s$ at every fixed finite horizon $s$.

These are Erwin Bolthausen, *On a functional central limit theorem for
random walks conditioned to stay positive*, Lemma 2.5,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
The proof invokes Lemma 2.4 and continuity of time translation of
continuous paths.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

/-- Bolthausen's Lemma 2.5 for the unrestricted first-window shift. -/
theorem IsBrownianReal.ae_continuousAt_shiftAtFirstNonnegativeWindowStart
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    ∀ᵐ ω ∂P, ContinuousAt shiftAtFirstNonnegativeWindowStart
      (hB.continuousPathMap hBmeasurable ω) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hfiniteMeas : MeasurableSet
      {ω | firstNonnegativeWindowStart (pathB ω) ≠ ⊤} := by
    exact (measurable_firstNonnegativeWindowStart.comp
      (hB.measurable_continuousPathMap hBmeasurable))
        (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl
  have hfinite : ∀ᵐ ω ∂P,
      firstNonnegativeWindowStart (pathB ω) ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one hfiniteMeas).mpr
      (hB.measure_firstNonnegativeWindowStart_ne_top_eq_one hBmeasurable)
  filter_upwards [hfinite,
    hB.ae_continuousAt_firstNonnegativeWindowStart hBmeasurable]
    with ω hω hcont
  exact continuousAt_shiftAtFirstNonnegativeWindowStart_of_finite
    (pathB ω) hω hcont

/-- Bolthausen's Lemma 2.5 for every finite horizon. -/
theorem IsBrownianReal.ae_continuousAt_shiftAtFirstNonnegativeWindowStartUpTo
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ContinuousAt
      (fun f => shiftAtFirstNonnegativeWindowStartUpTo f s)
      (hB.continuousPathMap hBmeasurable ω) := by
  let pathB := hB.continuousPathMap hBmeasurable
  rcases lt_trichotomy s 1 with hs | hs | hs
  · have hconst : (fun f : C(ℝ≥0, ℝ) =>
        shiftAtFirstNonnegativeWindowStartUpTo f s) =
        fun _ => (⟨fun _ => -1, continuous_const⟩ : C(ℝ≥0, ℝ)) := by
      funext f
      simp [shiftAtFirstNonnegativeWindowStartUpTo,
        firstNonnegativeWindowStartUpTo_eq_top_of_lt_one f hs]
    exact Filter.Eventually.of_forall fun ω => by
      rw [hconst]
      exact continuousAt_const
  · subst s
    filter_upwards [hB.ae_continuousAt_firstNonnegativeWindowStart
      hBmeasurable,
      hB.ae_firstNonnegativeWindowStart_ne_zero hBmeasurable]
      with ω hcont hcut
    have hpositive : (0 : WithTop ℝ≥0) <
        firstNonnegativeWindowStart (pathB ω) :=
      lt_of_le_of_ne bot_le (Ne.symm hcut)
    exact continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_cutoff_lt
      (pathB ω) (by norm_num) (by simpa using hpositive) hcont
  · have hnoBoundary : ∀ᵐ ω ∂P,
        firstNonnegativeWindowStartUpTo (pathB ω) s ≠ s - 1 := by
      apply ae_iff.mpr
      simpa only [not_not] using
        hB.measure_firstNonnegativeWindowStartUpTo_eq_last
          hBmeasurable hs
    filter_upwards [hB.ae_continuousAt_firstNonnegativeWindowStart
      hBmeasurable, hnoBoundary] with ω hcont hboundary
    have hcut : firstNonnegativeWindowStart (pathB ω) ≠
        (s - 1 : WithTop ℝ≥0) := by
      intro heq
      have hsum : s - 1 + 1 = s := tsub_add_cancel_of_le hs.le
      have hfirst := firstNonnegativeWindowStartUpTo_eq_first_of_le
        (pathB ω) heq hsum.le
      exact hboundary (by simpa [WithTop.coe_sub] using hfirst)
    rcases lt_or_gt_of_ne hcut with hlt | hgt
    · have hfirst := firstNonnegativeWindowStartUpTo_eq_first_of_lt_cutoff
        (pathB ω) hs.le hlt
      have hfinite : firstNonnegativeWindowStartUpTo (pathB ω) s ≠ ⊤ := by
        rw [hfirst]
        exact (hlt.trans (WithTop.coe_lt_top (s - 1))).ne
      have hcontUp := continuousAt_firstNonnegativeWindowStartUpTo_of_ne_cutoff
        (pathB ω) hs.le hcont hcut
      exact continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_finite
        (pathB ω) s hfinite hcontUp
    · exact continuousAt_shiftAtFirstNonnegativeWindowStartUpTo_of_cutoff_lt
        (pathB ω) hs.le hgt hcont

end ProbabilityTheory

end
