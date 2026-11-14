/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Field
import all Probability.BranchingRandomWalk.Coupling.Field.Ranked.Lemmas.RecursiveStep
import all Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Lemmas.Past

/-!
# Product law of the recursive matched field

The selected-BRW and fallback fields are the two copies of one root-indexed
product field.
Predictable coordinate selection preserves the product law at every finite stage.
For every `n`, the main conclusion is

\[
  (\mathrm{stepFieldLaw}_{Root\oplus Root}\,\mu).map(F_n)
  = \mathrm{stepFieldLaw}_{Root}\,\mu.
\]

## Public declarations

* `RootIndexed.rankInstalledField_law` proves fixed-stage product-law
  preservation for a predictable rank-installed field.
* `RootIndexed.rankInstalledField_measurable_of_supports` derives the
  recursive measurability hypotheses from measurable, countably ranged
  selected-BRW and n-selected-BRW populations.
* `RootIndexed.rankInstalledField_law_of_supports` gives the product-law
  conclusion directly from those population-support hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection


/-- Every finite stage of predictable equal-rank installation has the same
complete product law as the original fallback field.  The hypotheses mention
only the actual random coordinate-map range and its generation-domain-flow
fibres; roots and offspring slots need not be countable. -/
theorem RootIndexed.rankInstalledField_law
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationDepth : ∀ n field p, p ∈ selectedBRWPopulation n field → p.2.length = n)
    (hfield : ∀ n, Measurable
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n))
    (hpast : ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation
        nSelectedBRWPopulation RootIndexed.StepField.left RootIndexed.StepField.right n field
          ).past n))
    (hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
        selectedBRWPopulation nSelectedBRWPopulation n field = roots}) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  intro n
  induction n with
  | zero =>
      exact RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective
  | succ n ih =>
      let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
      let prior := RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n
      let past := fun field => (prior field).past n
      let rightPast := RootIndexed.StepField.rightPast
        (Root := Root) (α := α) (X := X) n
      have hpastGlobal : Measurable past := (hpast n).mono
        (RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
      have hrestrict : Measurable
          (RootIndexed.StepField.past (Root := Root) (α := α) (X := X) n) :=
        (RootIndexed.StepField.past_measurable n).mono
          (RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) |>.le n) le_rfl
      have hright : Measurable
          (RootIndexed.StepField.right :
            RootIndexed.StepField (Root ⊕ Root) α X →
              RootIndexed.StepField Root α X) := by
        change Measurable (RootIndexed.StepField.reindex Sum.inr)
        apply measurable_pi_iff.mpr
        intro r
        apply measurable_pi_iff.mpr
        intro u
        exact (measurable_pi_apply u).comp
          (measurable_pi_apply (Sum.inr r))
      have hpastLaw : P.map past = P.map rightPast := by
        calc
          P.map past = (P.map prior).map (RootIndexed.StepField.past n) := by
            rw [Measure.map_map hrestrict (hfield n)]
            rfl
          _ = (RootIndexed.stepFieldLaw (Root := Root) μ).map
              (RootIndexed.StepField.past n) := by rw [ih]
          _ = (P.map RootIndexed.StepField.right).map
              (RootIndexed.StepField.past n) := by
            change (RootIndexed.stepFieldLaw (Root := Root) μ).map
                (RootIndexed.StepField.past n) =
              (P.map (RootIndexed.StepField.reindex Sum.inr)).map
                (RootIndexed.StepField.past n)
            rw [RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective]
          _ = P.map rightPast := by
            rw [Measure.map_map hrestrict hright]
            rfl
      have hglue := RootIndexed.stepFieldLaw_glueCoordinates μ n past
        (hpast n) hpastLaw
        (RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)
        (hcount n) (hfiber n)
        (RootIndexed.rankBlockChoice_future n
          (selectedBRWPopulationOrderKey n)
          (fun field => nSelectedBRWPopulationOrderKey n field (prior field))
          (selectedBRWPopulation n) (fun field => nSelectedBRWPopulation n field (prior field))
          (hselectedBRWPopulationDepth n))
        (RootIndexed.rankBlockChoice_injective n
          (selectedBRWPopulationOrderKey n)
          (fun field => nSelectedBRWPopulationOrderKey n field (prior field))
          (selectedBRWPopulation n) (fun field => nSelectedBRWPopulation n field (prior field)))
      rw [show RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) =
          (fun field => RootIndexed.StepField.glue n (past field)
            (RootIndexed.selectedCoordinateField
              (RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
                selectedBRWPopulation nSelectedBRWPopulation n) field)) by
        funext field
        exact RootIndexed.rankInstalledField_succ_eq_glue selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
          selectedBRWPopulation nSelectedBRWPopulation n field]
      exact hglue

/-- Under the support measurability hypotheses used by the recursive
rank-matching construction, every finite matched field is measurable. -/
theorem RootIndexed.rankInstalledField_measurable_of_supports
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | selectedBRWPopulation n field = s})
    (hselectedBRWPopulationRange : ∀ n, (Set.range (selectedBRWPopulation n)).Countable)
    (hnSelectedBRWPopulationFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field) = s})
    (hnSelectedBRWPopulationRange : ∀ n, (Set.range fun field => nSelectedBRWPopulation n field
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
        ).Countable)
    (hselectedBRWPopulationOrderKeyMeasurable : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (selectedBRWPopulationOrderKey n field) q <
        valueKey (selectedBRWPopulationOrderKey n field) p)
    (hnSelectedBRWPopulationOrderKeyMeasurable : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (nSelectedBRWPopulationOrderKey n field
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p) :
    ∀ n, Measurable
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n) := by
  have hleft : Measurable
      (RootIndexed.StepField.left :
        RootIndexed.StepField (Root ⊕ Root) α X →
          RootIndexed.StepField Root α X) := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp
      (measurable_pi_apply (Sum.inl r))
  have hright : Measurable
      (RootIndexed.StepField.right :
        RootIndexed.StepField (Root ⊕ Root) α X →
          RootIndexed.StepField Root α X) := by
    change Measurable (RootIndexed.StepField.reindex Sum.inr)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp
      (measurable_pi_apply (Sum.inr r))
  exact RootIndexed.rankInstalledField_measurable_of_stages
    selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation RootIndexed.StepField.left
      RootIndexed.StepField.right
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (hselectedBRWPopulationFiber n s))
    hselectedBRWPopulationRange
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (hnSelectedBRWPopulationFiber n s))
    hnSelectedBRWPopulationRange
    (fun n p q => (hselectedBRWPopulationOrderKeyMeasurable n p q).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl)
    (fun n p q => (hnSelectedBRWPopulationOrderKeyMeasurable n p q).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl)
    hleft hright

/-- Product law of the recursive matched field under support-level
measurability assumptions.  The auxiliary countability and fibre conditions
for the complete coordinate map are consequences, rather than inputs. -/
theorem RootIndexed.rankInstalledField_law_of_supports
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationDepth : ∀ n field p, p ∈ selectedBRWPopulation n field → p.2.length = n)
    (hselectedBRWPopulationFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | selectedBRWPopulation n field = s})
    (hselectedBRWPopulationRange : ∀ n, (Set.range (selectedBRWPopulation n)).Countable)
    (hnSelectedBRWPopulationFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field) = s})
    (hnSelectedBRWPopulationRange : ∀ n, (Set.range fun field => nSelectedBRWPopulation n field
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
        ).Countable)
    (hselectedBRWPopulationOrderKeyMeasurable : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (selectedBRWPopulationOrderKey n field) q <
        valueKey (selectedBRWPopulationOrderKey n field) p)
    (hnSelectedBRWPopulationOrderKeyMeasurable : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (nSelectedBRWPopulationOrderKey n field
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  have hfield := RootIndexed.rankInstalledField_measurable_of_supports
    selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationFiber hselectedBRWPopulationRange
    hnSelectedBRWPopulationFiber hnSelectedBRWPopulationRange hselectedBRWPopulationOrderKeyMeasurable hnSelectedBRWPopulationOrderKeyMeasurable
  have hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)).Countable := by
    intro n
    exact RootIndexed.rankBlockChoice_range_countable_of_supports n
      (selectedBRWPopulationOrderKey n)
      (fun field => nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (selectedBRWPopulation n)
      (fun field => nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hselectedBRWPopulationRange n) (hnSelectedBRWPopulationRange n)
  have hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
        selectedBRWPopulation nSelectedBRWPopulation n field = roots} := by
    intro n roots
    exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
      (selectedBRWPopulationOrderKey n)
      (fun field => nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (selectedBRWPopulation n)
      (fun field => nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hselectedBRWPopulationFiber n) (hselectedBRWPopulationRange n) (hnSelectedBRWPopulationFiber n) (hnSelectedBRWPopulationRange n)
      (hselectedBRWPopulationOrderKeyMeasurable n) (hnSelectedBRWPopulationOrderKeyMeasurable n) roots
  have hpast := RootIndexed.rankInstalledField_past_measurable selectedBRWPopulationOrderKey
    nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth hcount hfiber
  exact RootIndexed.rankInstalledField_law μ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
    hselectedBRWPopulationDepth hfield hpast hcount hfiber

end ProbabilityTheory.BranchingRandomWalk.Coupling
