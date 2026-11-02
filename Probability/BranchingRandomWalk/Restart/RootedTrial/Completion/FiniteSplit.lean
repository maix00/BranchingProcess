/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
public import Probability.BranchingProcess.Offspring.FieldLaw
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.FiniteSplit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-sure finite completion of the first selected split

For a measurable finite selection `R` with almost-surely nonempty offspring and
positive one-step split probability, the selected population's first split has
finite completion almost surely. Writing `τ_R` for this completion, if
`μ {ξ | (R ξ).Nonempty} = 1` and
`0 < μ {ξ | 2 ≤ (R ξ).card}`, then
`(offspringFieldLaw μ) {ω | τ_R ω ≠ ⊤} = 1`.

## Public declarations

If the selected offspring is nonempty almost surely and a split has positive
one-step probability, the observable first-split completion is finite almost
surely:

\[\mu\{\xi:(R(\xi)).\operatorname{Nonempty}\}=1,\qquad
  \mu\{\xi:2\le|R(\xi)|\}>0
  \Longrightarrow
  \mathbb P_{\mathrm{field}}(\tau_R<\infty)=1.\]

* `ProbabilityTheory.BranchingRandomWalk.selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos`
  gives the stated finite-completion conclusion for a measurable finite
  selection under the nonemptiness and positive-split hypotheses.
-/

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal

@[expose] public section

section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

variable {α X : Type*}

/-- With positive one-step split probability and an almost surely nonempty
selected family, the selected population's first split has finite observable
completion almost surely.  Empty offspring remain allowed in the generic
step model; the nonemptiness premise is isolated here because extinction can
otherwise prevent every split. -/
theorem selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hnonempty : μ {ξ | (R ξ).Nonempty} = 1)
    (hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (R ξ).card})
    (hpositive : 0 < μ {ξ : Step α X | 2 ≤ (R ξ).card}) :
    ∀ᵐ ω ∂offspringFieldLaw μ,
      selectedPopulationSplitCompletion R ω ≠ ⊤ := by
  classical
  let noSplit : Set (Step α X) := {ξ | (R ξ).card < 2}
  let split : Set (Step α X) := {ξ | 2 ≤ (R ξ).card}
  let rootNoSplit : Set (Mark α (Step α X)) :=
    {η | (R (η [])).card < 2}
  let ν := offspringFieldLaw μ
  have hnoMeas : MeasurableSet noSplit := by
    dsimp [noSplit]
    exact (measurable_of_countable fun s : Finset α => s.card).comp hR
      measurableSet_Iio
  have hrootMeas : MeasurableSet rootNoSplit := by
    change MeasurableSet ((fun η : Mark α (Step α X) => η []) ⁻¹' noSplit)
    exact hnoMeas.preimage (measurable_pi_apply [])
  have hsplitMeas : MeasurableSet split := by
    simpa [split] using hsplit
  have hcomp : splitᶜ = noSplit := by
    ext ξ
    simp [split, noSplit]
  have hpartition : μ split + μ noSplit = 1 := by
    calc
      μ split + μ noSplit = μ split + μ splitᶜ := by rw [← hcomp]
      _ = μ Set.univ := measure_add_measure_compl hsplitMeas
      _ = 1 := measure_univ
  have hq : μ noSplit < 1 := by
    by_contra hnot
    have hle : 1 ≤ μ noSplit := le_of_not_gt hnot
    have hlt : μ noSplit < μ split + μ noSplit := by
      have hlt0 : 0 + μ noSplit < μ split + μ noSplit :=
        (ENNReal.add_lt_add_iff_right (measure_ne_top μ noSplit)).2
          (by simpa [split] using hpositive)
      simpa using hlt0
    rw [hpartition] at hlt
    exact (not_lt_of_ge hle hlt)
  have hrootLaw : ν rootNoSplit = μ noSplit := by
    change ν ((fun η : Mark α (Step α X) => η []) ⁻¹' noSplit) = μ noSplit
    rw [← Measure.map_apply (measurable_pi_apply []) hnoMeas,
      offspringFieldLaw_coordinate]
  have hnonemptyMeas : MeasurableSet
      {ξ : Step α X | (R ξ).Nonempty} := by
    have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hR
    have hcardPos : MeasurableSet {ξ : Step α X | 0 < (R ξ).card} :=
      hcard measurableSet_Ioi
    convert hcardPos using 1
    ext ξ
    simp [Finset.card_pos]
  have hpopNonempty := selectedPopulation_all_nonempty_ae μ R hnonempty
    hnonemptyMeas
  have hprefixMeas (n : ℕ) :
      MeasurableSet[generationFiltration (M := Step α X) n]
        (selectedPopulationNoSplitPrefix R n) :=
    selectedPopulationNoSplitPrefix_measurable R hR n
  have hrepresentative (n : ℕ) :
      Measurable[generationFiltration (M := Step α X) n]
        (selectedPopulationDepthRepresentative R n) :=
    selectedPopulationDepthRepresentative_measurable R hR n
  have hprefixRecurrence (n : ℕ) :
      ν (selectedPopulationNoSplitPrefix R (n + 1)) =
        ν (selectedPopulationNoSplitPrefix R n) * μ noSplit := by
    let chosen := selectedPopulationDepthRepresentative R n
    have hfactor := selectedSubtreeStepField_event_factorization μ n chosen
      (hrepresentative n) (Set.to_countable _)
      (selectedPopulationDepthRepresentative_length R n)
      (selectedPopulationNoSplitPrefix R n) rootNoSplit
      (hprefixMeas n) hrootMeas
    have heq : selectedPopulationNoSplitPrefix R (n + 1) =ᵐ[ν]
        selectedPopulationNoSplitPrefix R n ∩
          selectedSubtreeStepField chosen ⁻¹' rootNoSplit := by
      filter_upwards [hpopNonempty] with ω hpop
      exact propext (selectedPopulationNoSplitPrefix_succ_iff R n ω hpop)
    calc
      ν (selectedPopulationNoSplitPrefix R (n + 1)) =
          ν (selectedPopulationNoSplitPrefix R n ∩
            selectedSubtreeStepField chosen ⁻¹' rootNoSplit) := measure_congr heq
      _ = ν (selectedPopulationNoSplitPrefix R n) * ν rootNoSplit := hfactor
      _ = ν (selectedPopulationNoSplitPrefix R n) * μ noSplit := by rw [hrootLaw]
  have hprefixPower (n : ℕ) :
      ν (selectedPopulationNoSplitPrefix R n) = (μ noSplit) ^ n := by
    induction n with
    | zero => simp [selectedPopulationNoSplitPrefix]
    | succ n ih =>
        rw [hprefixRecurrence n, ih, pow_succ]
  have hpow : Filter.Tendsto (fun n : ℕ => (μ noSplit) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := μ noSplit) hq
  let forever : Set (Mark α (Step α X)) :=
    ⋂ n : ℕ, selectedPopulationNoSplitPrefix R n
  have hforever_eq : forever =
      {ω | selectedPopulationSplitCompletion R ω = ⊤} := by
    ext ω
    rw [Set.mem_iInter]
    constructor
    · intro hprefix
      have hraw : selectedPopulationRawSplitTime R ω = ⊤ := by
        cases hτ : selectedPopulationRawSplitTime R ω with
        | top => rfl
        | coe k =>
          have hdecl := (firstDeclaredSuccess_eq_iff
            (selectedPopulationSplitDeclaration R) ω k).mp hτ
          have hno := hprefix (k + 1) k (Nat.lt_succ_self k)
          have hsplit : 2 ≤ (StepSelection.population R (k + 1) ω).card := by
            simpa [selectedPopulationSplitDeclaration] using hdecl.1
          have hnot : (StepSelection.population R (k + 1) ω).card < 2 := by
            simpa [selectedPopulationNoSplitPrefix] using hno
          omega
      change selectedPopulationSplitCompletion R ω = ⊤
      rw [selectedPopulationSplitCompletion_eq_raw_add_one, hraw]
      simp
    · intro htop n k hk
      have hraw := selectedPopulationRawSplitTime_eq_top_of_completion_eq_top
        R ω htop
      have hnot : ω ∉ selectedPopulationSplitDeclaration R k := by
        intro hdecl
        have hle := (firstDeclaredSuccess_le_iff
          (selectedPopulationSplitDeclaration R) ω k).mpr ⟨k, le_rfl, hdecl⟩
        change selectedPopulationRawSplitTime R ω ≤ k at hle
        rw [hraw] at hle
        simp at hle
      have hcard : (StepSelection.population R (k + 1) ω).card < 2 := by
        simpa [selectedPopulationSplitDeclaration] using hnot
      exact hcard
  have hmeasureForever : ν forever = 0 := by
    apply le_antisymm ?_ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hpow
    filter_upwards with n
    rw [← hprefixPower n]
    apply measure_mono
    intro ω hω
    exact (Set.mem_iInter.mp hω) n
  rw [hforever_eq] at hmeasureForever
  have hae := (measure_eq_zero_iff_ae_notMem
    (μ := ν) (s := {ω | selectedPopulationSplitCompletion R ω = ⊤})).mp
      hmeasureForever
  simpa using hae

end ProbabilityTheory.BranchingRandomWalk

end
