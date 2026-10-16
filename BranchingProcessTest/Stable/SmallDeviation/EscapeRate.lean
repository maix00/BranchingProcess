import Probability.Process.Stable.SmallDeviation.EscapeRate
import Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor
import Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint
import Probability.Process.Stable.SmallDeviation.EscapeRate.Law

open MeasureTheory Filter
open scoped NNReal Topology

section Applications

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {α d c b C D : ℝ} {μ : Measure ℝ}
variable {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {P : Measure Ω} {Q : Measure Ω'}
variable [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- The range escape-rate API needs only the stable process and the source's
two-sided mass condition. -/
example (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (ProbabilityTheory.stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) :=
  h.exists_rationalRange_escape_rate hcdf

/-- The centered corridor is an actual caller of the same escape-rate API,
with the common range constant returned as part of the witness. -/
example (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (ProbabilityTheory.stableCenteredLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, _, hcenter⟩ := h.exists_centeredCorridor_escape_rate hcdf
  exact ⟨C, hC, hcenter⟩

/-- The terminal-window ratio API exposes the exact `Ioc` event used by the
source, including when invoked without intermediate rate witnesses. -/
example (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) (hc : -1 < c) (hcb : c < b) (hb : b ≤ 1) :
    Tendsto
      (fun a : ℝ =>
        Real.log ((ProbabilityTheory.shiftedEndpointCorridorProbability
          P X d c b a).toReal) /
          Real.log ((ProbabilityTheory.shiftedCorridorProbability P X d a).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  exact h.tendsto_log_shiftedEndpointCorridor_div_log_shiftedCorridor
    hcdf hd hc hcb hb

/-- The translated corridor's logarithmic probability has the same rate as
the range event; this exercises relation (21) as a direct public application. -/
example (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1)
    (hd : -1 < d ∧ d < 1) :
    Tendsto
      (fun a : ℝ =>
        Real.log ((ProbabilityTheory.shiftedCorridorProbability P X d a).toReal) /
          Real.log ((ProbabilityTheory.rationalRangeProbability P X a).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  h.tendsto_log_shiftedCorridor_div_log_range hcdf hd

/-- Equal stable increment laws give the same escape-rate constant even when
the processes live on different probability spaces. -/
example (hX : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hY : ProbabilityTheory.IsStableLevyProcess α μ Y Q)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧
      ProbabilityTheory.cdf μ 0 < 1) :
    ∃ C : ℝ, C < 0 ∧
      Tendsto (ProbabilityTheory.stableRangeLogRate P X α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (ProbabilityTheory.stableRangeLogRate Q Y α)
        (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  obtain ⟨C, hC, hXrate⟩ :=
    hX.exists_rationalRange_escape_rate hcdf
  obtain ⟨D, hD, hYrate⟩ :=
    hY.exists_rationalRange_escape_rate hcdf
  have hCD := hX.escapeRate_constant_eq_of_same_law hY hXrate hYrate
  subst D
  exact ⟨C, hC, hXrate, hYrate⟩

end Applications

#check ProbabilityTheory.IsStableLevyProcess.exists_rationalRange_escape_rate
#check ProbabilityTheory.IsStableLevyProcess.exists_centeredCorridor_escape_rate
#check ProbabilityTheory.IsStableLevyProcess.exists_shiftedCorridor_escape_rate
#check ProbabilityTheory.IsStableLevyProcess.exists_shiftedEndpointCorridor_escape_rate
#check ProbabilityTheory.IsStableLevyProcess.tendsto_log_shiftedCorridor_div_log_range
#check
  ProbabilityTheory.IsStableLevyProcess.tendsto_log_shiftedEndpointCorridor_div_log_shiftedCorridor
#check ProbabilityTheory.IsStableLevyProcess.rationalRangeProbability_eq_of_same_law
#check ProbabilityTheory.IsStableLevyProcess.escapeRate_constant_eq_of_same_law

#print axioms ProbabilityTheory.IsStableLevyProcess.exists_rationalRange_escape_rate
#print axioms ProbabilityTheory.IsStableLevyProcess.exists_centeredCorridor_escape_rate
#print axioms ProbabilityTheory.IsStableLevyProcess.exists_shiftedCorridor_escape_rate
#print axioms ProbabilityTheory.IsStableLevyProcess.exists_shiftedEndpointCorridor_escape_rate
#print axioms ProbabilityTheory.IsStableLevyProcess.tendsto_log_shiftedCorridor_div_log_range
#print axioms
  ProbabilityTheory.IsStableLevyProcess.tendsto_log_shiftedEndpointCorridor_div_log_shiftedCorridor
#print axioms ProbabilityTheory.IsStableLevyProcess.rationalRangeProbability_eq_of_same_law
#print axioms ProbabilityTheory.IsStableLevyProcess.escapeRate_constant_eq_of_same_law
