/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Field

/-!
# Product law of the recursive matched field

Source and fallback are the two copies of one root-indexed product field.
Predictable coordinate selection preserves the product law at every finite stage.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection


/-- Every finite stage of predictable equal-rank installation has the same
complete product law as the original fallback field.  The hypotheses mention
only the actual random coordinate-map range and its generation-domain-flow
fibres; roots and offspring slots need not be countable. -/
theorem RootIndexed.rankInstalledField_law
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (hfield : ∀ n, Measurable
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n))
    (hpast : ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.rankInstalledField sourceValue targetValue source
        target RootIndexed.StepField.left RootIndexed.StepField.right n field
          ).past n))
    (hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
        source target n field = roots}) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  intro n
  induction n with
  | zero =>
      exact RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective
  | succ n ih =>
      let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
      let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
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
        (RootIndexed.rankInstalledBlockChoice sourceValue targetValue source target n)
        (hcount n) (hfiber n)
        (RootIndexed.rankBlockChoice_future n
          (sourceValue n)
          (fun field => targetValue n field (prior field))
          (source n) (fun field => target n field (prior field))
          (hsourceDepth n))
        (RootIndexed.rankBlockChoice_injective n
          (sourceValue n)
          (fun field => targetValue n field (prior field))
          (source n) (fun field => target n field (prior field)))
      rw [show RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) =
          (fun field => RootIndexed.StepField.glue n (past field)
            (RootIndexed.selectedCoordinateField
              (RootIndexed.rankInstalledBlockChoice sourceValue targetValue
                source target n) field)) by
        funext field
        exact RootIndexed.rankInstalledField_succ_eq_glue sourceValue targetValue
          source target n field]
      exact hglue

/-- Under the support measurability hypotheses used by the recursive
rank-matching construction, every finite matched field is measurable. -/
theorem RootIndexed.rankInstalledField_measurable_of_supports
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | source n field = s})
    (hsourceRange : ∀ n, (Set.range (source n)).Countable)
    (htargetFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | target n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) = s})
    (htargetRange : ∀ n, (Set.range fun field => target n field
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
        ).Countable)
    (hsourceKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (sourceValue n field) q <
        valueKey (sourceValue n field) p)
    (htargetKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (targetValue n field
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p) :
    ∀ n, Measurable
      (RootIndexed.rankInstalledField sourceValue targetValue source target
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
    sourceValue targetValue source target RootIndexed.StepField.left
      RootIndexed.StepField.right
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (hsourceFiber n s))
    hsourceRange
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (htargetFiber n s))
    htargetRange
    (fun n p q => (hsourceKey n p q).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl)
    (fun n p q => (htargetKey n p q).mono
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
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (hsourceFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | source n field = s})
    (hsourceRange : ∀ n, (Set.range (source n)).Countable)
    (htargetFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | target n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) = s})
    (htargetRange : ∀ n, (Set.range fun field => target n field
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
        ).Countable)
    (hsourceKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (sourceValue n field) q <
        valueKey (sourceValue n field) p)
    (htargetKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (targetValue n field
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  have hfield := RootIndexed.rankInstalledField_measurable_of_supports
    sourceValue targetValue source target hsourceFiber hsourceRange
    htargetFiber htargetRange hsourceKey htargetKey
  have hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target n)).Countable := by
    intro n
    exact RootIndexed.rankBlockChoice_range_countable_of_supports n
      (sourceValue n)
      (fun field => targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (source n)
      (fun field => target n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hsourceRange n) (htargetRange n)
  have hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
        source target n field = roots} := by
    intro n roots
    exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
      (sourceValue n)
      (fun field => targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (source n)
      (fun field => target n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hsourceFiber n) (hsourceRange n) (htargetFiber n) (htargetRange n)
      (hsourceKey n) (htargetKey n) roots
  have hpast := RootIndexed.rankInstalledField_past_measurable sourceValue
    targetValue source target hsourceDepth hcount hfiber
  exact RootIndexed.rankInstalledField_law μ sourceValue targetValue source target
    hsourceDepth hfield hpast hcount hfiber

end ProbabilityTheory.BranchingRandomWalk.Coupling
