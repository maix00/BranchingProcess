/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.Process
public import Probability.Process.HittingTime.PopulationOverflow

/-!
# Overflow time for a causal finite selection process

Let \(R_n(\omega,S)\subseteq S\) be a causal measurable selection rule on
finite candidate populations \(S\subseteq\iota\). For a candidate process
\(C_n(\omega)\), the retained population is
\(P_n(\omega)=R_n(\omega,C_n(\omega))\), and its overflow time at capacity
\(N\) is
\[
  \tau_N(\omega)=\inf\{n\in\mathbb N:N<|P_n(\omega)|\},
\]
with \(\tau_N=\infty\) if the set is empty. The label type \(\iota\) is
arbitrary; the results use the causal selection interface and finite-set
cardinality only.

## Public declarations

- `CausalFiniteMechanism.overflowTime` defines \(\tau_N\) for the retained
  population \(R_n(\omega,C_n(\omega))\).
- `CausalFiniteMechanism.overflowTime_le_iff` characterizes
  \(\tau_N\le n\) by \(\exists j\le n,\;N<|P_j|\).
- `CausalFiniteMechanism.population_card_le_of_lt_overflowTime` gives
  \(|P_n|\le N\) before \(\tau_N\), and
  `CausalFiniteMechanism.population_card_gt_of_overflowTime_eq` gives
  \(N<|P_n|\) at a finite overflow time.
- `CausalFiniteMechanism.overflowTime_isStoppingTime` proves that measurable
  retained-population sizes make \(\tau_N\) a stopping time.
- `CausalFiniteMechanism.overflowTime_isStoppingTime_of_countable` derives
  measurable sizes from adapted finite candidate populations when the label
  type \(\iota\) is countable.
-/

open MeasureTheory

@[expose] public section

namespace MeasureTheory.Selection

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [MeasurableSpace ι]

namespace CausalFiniteMechanism

/-- The first generation at which the retained finite population exceeds `N`.
The value is `⊤` when overflow never occurs. -/
noncomputable def overflowTime
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι) (N : ℕ) : Ω → WithTop ℕ :=
  ProbabilityTheory.finsetPopulationOverflowTime (R.population candidates) N

theorem overflowTime_le_iff
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι)
    (N n : ℕ) (ω : Ω) :
    overflowTime F R candidates N ω ≤ n ↔
      ∃ j ≤ n, N < (R.population candidates j ω).card :=
  ProbabilityTheory.finsetPopulationOverflowTime_le_iff _ N n ω

theorem population_card_le_of_lt_overflowTime
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι)
    (N n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) < overflowTime F R candidates N ω) :
    (R.population candidates n ω).card ≤ N :=
  ProbabilityTheory.card_le_of_lt_finsetPopulationOverflowTime _ N n ω h

theorem population_card_gt_of_overflowTime_eq
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι)
    (N n : ℕ) (ω : Ω)
    (h : overflowTime F R candidates N ω = n) :
    N < (R.population candidates n ω).card :=
  ProbabilityTheory.card_gt_of_finsetPopulationOverflowTime_eq _ N n ω h

/-- Observable retained-population sizes make overflow a stopping time. -/
theorem overflowTime_isStoppingTime
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι)
    (hcard : ∀ n, Measurable[F n]
      (fun ω => (R.population candidates n ω).card))
    (N : ℕ) :
    IsStoppingTime F (overflowTime F R candidates N) := by
  apply ProbabilityTheory.populationOverflowTime_isStoppingTime F
    (fun n ω => (↑(R.population candidates n ω) : Set ι)) _ N
  intro n
  let _ : MeasurableSpace Ω := F n
  have hcoe : Measurable (fun ω =>
      ((R.population candidates n ω).card : ℕ∞)) :=
    (measurable_of_countable fun k : ℕ => (k : ℕ∞)).comp (hcard n)
  simpa only [ProbabilityTheory.encard_coe_finset] using hcoe

/-- For countable labels, adapted finite candidate populations yield an
observable retained size process and hence a stopping-time overflow event.
The theorem `overflowTime_isStoppingTime` accepts directly measurable sizes
for arbitrary labels. -/
theorem overflowTime_isStoppingTime_of_countable
    [Countable ι]
    (F : Filtration ℕ m)
    (R : CausalFiniteMechanism ℕ Ω ι (fun n => F n))
    (candidates : ℕ → Ω → Finset ι)
    (hcandidates : ∀ n, Measurable[F n] (candidates n))
    (N : ℕ) :
    IsStoppingTime F (overflowTime F R candidates N) := by
  apply overflowTime_isStoppingTime F R candidates _ N
  intro n
  let _ : MeasurableSpace Ω := F n
  have hpopulation : Measurable[F n] (R.population candidates n) :=
    R.measurable_population candidates hcandidates n
  have hcard : Measurable[F n]
      (fun ω => (R.population candidates n ω).card) :=
    (measurable_of_countable fun s : Finset ι => s.card).comp hpopulation
  exact hcard

end CausalFiniteMechanism

end MeasureTheory.Selection

end
