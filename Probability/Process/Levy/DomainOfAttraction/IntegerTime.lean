/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Process.Levy.MarginalLaws
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Domain-of-attraction limits at integer times of Lévy processes

## Public declarations

* `ProbabilityTheory.IsLevyProcess.tendstoInDistribution_normalized_eval_nat_of_domainOfAttraction`
  transfers a scalar domain-of-attraction limit for the time-one marginal to
  the corresponding normalized integer-time marginals of the process. If
  $\nu=\operatorname{Law}(X_1)$ and
  $a_n^{-1}(S_n-b_n)\Rightarrow\mu$ for i.i.d. increments of law $\nu$, then
  $a_n^{-1}(X_n-b_n)\Rightarrow\mu$.

The proof identifies the integer-time process marginal with the canonical
i.i.d. sum law using `IsLevyProcess.map_eval_nat_eq_iidSum`; the normalization
is then pushed through that law identity. This provides the integer-time
input for the process-level limit route recorded in
`docs/MOGULSKII_PROCESS_THEOREM_4_PROOF_ROUTE.md`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.IsLevyProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

/-- A scalar domain-of-attraction limit for the time-one marginal gives the
same normalized limit for the integer-time marginals of the Lévy process. -/
theorem tendstoInDistribution_normalized_eval_nat_of_domainOfAttraction
    (h : IsLevyProcess X P) (ν μ : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) = P.map (fun ω => X 1 ω))
    (scale center : ℕ → ℝ)
    (hDOA : IsInDomainOfAttractionAlong (ν : Measure ℝ) (μ : Measure ℝ)
      scale center) :
    TendstoInDistribution
      (fun n ω => (scale n)⁻¹ * (X (n : ℝ≥0) ω - center n))
      atTop id (fun _ : ℕ => P) (μ : Measure ℝ) := by
  have hnormalized_meas (n : ℕ) :
      AEMeasurable
        (fun ω => (scale n)⁻¹ * (X (n : ℝ≥0) ω - center n)) P := by
    exact (h.aemeasurable_eval (n : ℝ≥0)).sub aemeasurable_const |>.const_mul _
  have hnormalized_law (n : ℕ) (hn : 0 < n) :
      P.map (fun ω => (scale n)⁻¹ * (X (n : ℝ≥0) ω - center n)) =
        (iidSequenceLaw (ν : Measure ℝ)).map (normalizedIidSum scale center n) := by
    let total : (ℕ → ℝ) → ℝ := fun sequence =>
      ∑ k ∈ Finset.range n, sequence k
    let normalize : ℝ → ℝ := fun x => (scale n)⁻¹ * (x - center n)
    have htotal_meas : Measurable total := by
      exact Finset.measurable_sum (Finset.range n)
        (fun k _ => measurable_pi_apply k)
    have hnormalize_meas : Measurable normalize := by
      fun_prop
    have hraw := h.map_eval_nat_eq_iidSum n hn
    rw [← hν] at hraw
    calc
      P.map (fun ω => (scale n)⁻¹ * (X (n : ℝ≥0) ω - center n)) =
          P.map (normalize ∘ fun ω => X (n : ℝ≥0) ω) := rfl
      _ = (P.map (fun ω => X (n : ℝ≥0) ω)).map normalize :=
        (AEMeasurable.map_map_of_aemeasurable
          hnormalize_meas.aemeasurable (h.aemeasurable_eval _)).symm
      _ = ((iidSequenceLaw (ν : Measure ℝ)).map total).map normalize := by
        rw [hraw]
      _ = (iidSequenceLaw (ν : Measure ℝ)).map
          (normalizedIidSum scale center n) := by
        rw [Measure.map_map hnormalize_meas htotal_meas]
        rfl
  refine ⟨hnormalized_meas, aemeasurable_id, ?_⟩
  have hn_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  have hmaps : ∀ᶠ n : ℕ in atTop,
      (P.map (fun ω => (scale n)⁻¹ * (X (n : ℝ≥0) ω - center n))) =
        (iidSequenceLaw (ν : Measure ℝ)).map (normalizedIidSum scale center n) := by
    filter_upwards [hn_pos] with n hn
    exact hnormalized_law n hn
  exact hDOA.tendstoInDistribution.tendsto.congr' <| hmaps.mono fun n hn => by
    apply Subtype.ext
    exact hn.symm

end ProbabilityTheory.IsLevyProcess

end
