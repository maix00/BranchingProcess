/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.Instances.NNReal.Lemmas

import Probability.Process.Levy.FiniteDimensional

/-!
# Fixed-time continuity of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.tendstoInDistribution_eval_nhdsGT_zero`:
  for a zero-start Lévy process, the law of $X_t$ converges to $\delta_0$ as
  $t\downarrow0$.
- `ProbabilityTheory.IsLevyProcess.ae_leftLim_eq_eval`: for each fixed
  $t>0$, an almost surely càdlàg process with stationary increments satisfies
  \[
    \mathbb P\!\left(X_{t-}=X_t\right)=1.
  \]

The proof compares increments over intervals approaching $t$ from the left
with increments over intervals of the same lengths starting at zero. Right
continuity at zero makes the latter converge almost surely to zero; uniqueness
of limits in distribution then identifies the former's càdlàg limit with
zero.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [AddGroup E] [MeasurableSpace E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [BorelSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
  [OpensMeasurableSpace E] [MeasurableSingletonClass E] [HasOuterApproxClosed E]
  {X : ℝ≥0 → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]

omit [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSingletonClass E]
  [HasOuterApproxClosed E] in
/-- For a Lévy process, the law of `X t` converges to the point mass at zero as
`t` decreases to zero.
The proof applies almost-sure right continuity at the initial time to the
coordinates and then passes from almost-sure convergence to convergence in
distribution. -/
theorem IsLevyProcess.tendstoInDistribution_eval_nhdsGT_zero
    (h : IsLevyProcess X P) :
    TendstoInDistribution (fun t ω => X t ω) (𝓝[>] (0 : ℝ≥0))
      (fun _ : Ω => (0 : E)) (fun _ : ℝ≥0 => P) P := by
  have hae_tendsto : ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => X t ω) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : E)) := by
    filter_upwards [h.ae_cadlag, h.ae_start_eq_zero] with ω hω hω₀
    simpa [hω₀] using (hω.isRightContinuous (0 : ℝ≥0)).tendsto
  exact tendstoInDistribution_of_ae_tendsto
    (fun t => h.aemeasurable_eval t) aemeasurable_const hae_tendsto

/-- At each fixed positive time, almost every càdlàg Lévy path is continuous
from the left. Stationarity identifies the left increments with increments
over intervals shrinking to the initial time. -/
theorem IsLevyProcess.ae_leftLim_eq_eval
    (h : IsLevyProcess X P) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (fun s => X s ω).leftLim t = X t ω := by
  let times : ℕ → ℝ≥0 := fun n => t * ((n : ℝ≥0) / ((n : ℝ≥0) + 1))
  let gap : ℕ → ℝ≥0 := fun n => t - times n
  let smallIncrement : ℕ → Ω → E := fun n ω => X (gap n) ω - X 0 ω
  let increment : ℕ → Ω → E := fun n ω => X t ω - X (times n) ω
  let jump : Ω → E := fun ω => X t ω - (fun s => X s ω).leftLim t

  have hratio : Tendsto (fun n : ℕ =>
      (n : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 (1 : ℝ≥0)) := by
    simpa using (tendsto_natCast_div_add_atTop (𝕜 := ℝ≥0) (1 : ℝ≥0))
  have htimes : Tendsto times atTop (𝓝 t) := by
    simpa [times] using hratio.const_mul t
  have hratio_lt (n : ℕ) :
      (n : ℝ≥0) / ((n : ℝ≥0) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.lt_succ_self n
  have htimes_lt (n : ℕ) : times n < t := by
    dsimp [times]
    calc
      t * ((n : ℝ≥0) / ((n : ℝ≥0) + 1)) < t * 1 :=
        mul_lt_mul_of_pos_left (hratio_lt n) ht
      _ = t := by simp
  have htimes_left : Tendsto times atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨htimes, Filter.Eventually.of_forall fun n => htimes_lt n⟩
  have hgap : Tendsto gap atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    simpa [gap] using hconst.sub htimes
  have hgap_pos (n : ℕ) : 0 < gap n := by
    exact tsub_pos_iff_lt.mpr (htimes_lt n)
  have hgap_right : Tendsto gap atTop (𝓝[>] (0 : ℝ≥0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hgap, Filter.Eventually.of_forall hgap_pos⟩

  have heval_gap : TendstoInDistribution (fun n ω => X (gap n) ω) atTop
      (fun _ : Ω => (0 : E)) (fun _ : ℕ => P) P := by
    refine ⟨fun n => h.aemeasurable_eval (gap n), aemeasurable_const, ?_⟩
    exact h.tendstoInDistribution_eval_nhdsGT_zero.tendsto.comp hgap_right
  have h_eval_small (n : ℕ) : (fun ω => X (gap n) ω) =ᵐ[P]
      smallIncrement n := by
    filter_upwards [h.ae_start_eq_zero] with ω hω
    simp [smallIncrement, hω]
  have hsmall_dist : TendstoInDistribution smallIncrement atTop
      (fun _ : Ω => (0 : E)) (fun _ : ℕ => P) P := by
    exact heval_gap.congr h_eval_small
      (Filter.Eventually.of_forall fun _ => rfl)

  have htime_add (n : ℕ) : times n + gap n = t := by
    dsimp [gap]
    exact add_tsub_cancel_of_le (le_of_lt (htimes_lt n))

  have hstationary_ident (n : ℕ) : IdentDistrib (increment n) (smallIncrement n) P P := by
    have hstationary := h.stationaryIncrements (times n) (gap n)
    simpa [increment, smallIncrement, htime_add n] using hstationary

  have hincrement_to_zero : TendstoInDistribution increment atTop
      (fun _ : Ω => (0 : E)) (fun _ : ℕ => P) P := by
    refine ⟨fun n => (hstationary_ident n).aemeasurable_fst,
      aemeasurable_const, ?_⟩
    apply hsmall_dist.tendsto.congr'
    filter_upwards with n
    apply Subtype.ext
    exact (hstationary_ident n).map_eq.symm

  have hae_tendsto : ∀ᵐ ω ∂P,
      Tendsto (fun n => increment n ω) atTop (𝓝 (jump ω)) := by
    filter_upwards [h.ae_cadlag] with ω hω
    have hleft := hω.tendsto_nhdsLT_leftLim t
    have hleft_seq := hleft.comp htimes_left
    have hdiff : Tendsto (fun n => X t ω - X (times n) ω) atTop
        (𝓝 (X t ω - (fun s => X s ω).leftLim t)) :=
      tendsto_const_nhds.sub hleft_seq
    simpa [increment, jump] using hdiff

  have hjump_meas : AEMeasurable jump P :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => (hstationary_ident n).aemeasurable_fst) hae_tendsto
  have hjump_dist : TendstoInDistribution increment atTop jump
      (fun _ : ℕ => P) P :=
    tendstoInDistribution_of_ae_tendsto
      (fun n => (hstationary_ident n).aemeasurable_fst) hjump_meas hae_tendsto
  have hunique := tendstoInDistribution_unique increment
    hincrement_to_zero hjump_dist
  have hjump_law : HasLaw jump (Measure.dirac 0) P := by
    refine ⟨hjump_meas, ?_⟩
    rw [← hunique]
    simp
  have hae_zero : ∀ᵐ ω ∂P, jump ω = 0 := by
    rw [hjump_law.ae_iff (p := fun x : E => x = 0) (by fun_prop)]
    simp
  filter_upwards [hae_zero] with ω hω
  dsimp [jump] at hω
  exact (sub_eq_zero.mp hω).symm

end ProbabilityTheory

end
