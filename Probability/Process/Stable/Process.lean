/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Basic
public import Topology.Cadlag.Basic

/-!
# Stable clock processes

This layer adds almost-sure càdlàg paths to the general stable clock-increment
interface. Lévy processes and path laws are defined in their own modules.

The process interface is the conjunction of stable clock increments and
almost-sure càdlàg paths:

\[
\operatorname{IsStableClockProcess}(α,μ,\mathrm{clock},X,P)
\iff\operatorname{HasStableClockIncrements}(α,μ,\mathrm{clock},X,P)
\;\land\;
P\{\omega:t\mapsto X(t,\omega)\text{ is càdlàg}\}=1.
\]

## Public declarations

- `ProbabilityTheory.IsStableClockProcess α μ clock X P` specifies stable
  clock increments and almost-sure càdlàg paths:
  `HasStableClockIncrements α μ clock X P ∧ ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)`.
- `ProbabilityTheory.IsStableClockProcess.increments` projects the stable
  clock-increment specification.
- `ProbabilityTheory.IsStableClockProcess.ae_cadlag` gives the almost-sure
  càdlàg path property.
-/

open MeasureTheory Set
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stable independent-increment process on an arbitrary ordered time axis
with almost-surely càdlàg sample paths. For a general clock this need not be a
Lévy process. -/
def IsStableClockProcess {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (X : Time → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  HasStableClockIncrements α μ clock X P ∧
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)

namespace IsStableClockProcess

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The stable increment specification of a clock process. -/
theorem increments (h : IsStableClockProcess α μ clock X P) :
    HasStableClockIncrements α μ clock X P := h.1

/-- Clock-process sample paths are càdlàg almost surely. -/
theorem ae_cadlag (h : IsStableClockProcess α μ clock X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := h.2

end IsStableClockProcess

end ProbabilityTheory

end
