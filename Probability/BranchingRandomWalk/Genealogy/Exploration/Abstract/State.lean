/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.ConditionalProbability
public import Probability.BranchingProcess.State.BranchingProperty
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Law

/-!
# State-update branching at selected generations

## Public declarations

In namespace `ProbabilityTheory.BranchingRandomWalk`:

* `selected_stateTree_family_condExp` gives the full conditional state-subtree
  law at a generation-measurably selected family of distinct roots:
  $E[g((V_{S_i}(\omega_{u_i}))_i)\mid\mathcal F_n]
   =\int g\,d\bigotimes_i P_{S_i}$.
* `stopped_stateTree_family_condExp_on_finite` gives the same conditional
  law under $P(\cdot\mid\tau<\infty)$, allowing positive probability of
  infinite stopping time. If the finite-time event has probability zero,
  its asserted branching identity is vacuous.
* `stopped_stateTree_family_condExp` gives the same identity with
  $\mathcal F_n$ replaced by $\mathcal F_\tau$ for an everywhere-finite
  stopping generation. Root states $S_i$ may be arbitrary stopped-measurable
  random variables. The selected root-family map has countable range and
  measurable singleton fibres.

Here $P_s$ is `BranchingProcess.stateTreeKernel μ F hF s`. The update $F$ is
jointly measurable, with no additive structure, and the offspring-mark law
$\mu$ is fixed. On surviving selected roots, `stateTree_subtree` identifies
these updated trees with the original descendants.

These are the independent-mark state-update forms of the branching property;
compare S. Valère Bitseki Penda and J.-F. Delmas, "Central limit theorem for
bifurcating Markov chains", Definition 2.1,
https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf.
The proof first selects independent descendant fields, then applies the
measurable state-tree map; it never translates states to an origin.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess

namespace ProbabilityTheory.BranchingRandomWalk

/-- Branching at a measurably selected generation for any measurable state update. -/
theorem selected_stateTree_family_condExp {ι α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F)) (n : ℕ)
    (roots : StepField α Mark → ι → TreeNode α)
    (hroots : Measurable[generationFiltration (M := Step α Mark) n] roots)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[generationFiltration (M := Step α Mark) n]
      {ω | roots ω = r})
    (hdepth : ∀ ω i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω))
    (s : StepField α Mark → ι → State)
    (hs : Measurable[generationFiltration (M := Step α Mark) n] s)
    (g : (ι → TreeNode α → Option State) → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
      (selectedSubtreeStepFieldVector roots ω i))) (offspringFieldLaw μ)) :
    condExp (generationFiltration (M := Step α Mark) n) (offspringFieldLaw μ)
        (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
          (selectedSubtreeStepFieldVector roots ω i))) =ᵐ[offspringFieldLaw μ]
      fun ω ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i ↦ stateTreeKernel μ F hF (s ω i)) := by
  exact condExp_stateTree_family _ _ (generationFiltration (M := Step α Mark) |>.le n)
    μ F hF s hs _ (selectedSubtreeStepFieldVector_measurable roots hroots hcount)
    (selectedSubtreeStepFieldVector_independent μ roots hroots hcount hfiber hdepth hinj)
    (selectedSubtreeStepFieldVector_law μ roots hroots hcount hfiber hdepth hinj) g hg hgi

/-- State subtrees at a finite stopping generation retain their current states
and have conditionally independent continuation laws. -/
theorem stopped_stateTree_family_condExp {ι α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (τ : StepField α Mark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (M := Step α Mark)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : StepField α Mark → ι → TreeNode α)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace] {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) → ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω))
    (s : StepField α Mark → ι → State) (hs : Measurable[hτ.measurableSpace] s)
    (g : (ι → TreeNode α → Option State) → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
      (selectedSubtreeStepFieldVector roots ω i))) (offspringFieldLaw μ)) :
    condExp hτ.measurableSpace (offspringFieldLaw μ)
        (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
          (selectedSubtreeStepFieldVector roots ω i))) =ᵐ[offspringFieldLaw μ]
      fun ω ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i ↦ stateTreeKernel μ F hF (s ω i)) := by
  exact condExp_stateTree_family _ _ hτ.measurableSpace_le μ F hF s hs _
    (selectedSubtreeStepFieldVector_measurable_of_measurable roots
      (hroots.mono hτ.measurableSpace_le le_rfl) hcount)
    (stopped_selectedSubtreeStepFieldVector_independent μ τ hτ hfinite roots hroots
      hcount hfiber hdepth hinj)
    (stopped_selectedSubtreeStepFieldVector_law μ τ hτ hfinite roots hroots
      hcount hfiber hdepth hinj) g hg hgi


/-- Branching on the finite-time event, which may have probability less than one.
Conditioning first on this stopped-measurable event preserves the same state
continuation laws. The zero-probability case is vacuous. -/
theorem stopped_stateTree_family_condExp_on_finite {ι α Mark State : Type*}
    [MeasurableSpace Mark] [MeasurableSpace State]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : State → Mark → State) (hF : Measurable (Function.uncurry F))
    (τ : StepField α Mark → WithTop ℕ)
    (hτ : IsStoppingTime (generationFiltration (M := Step α Mark)) τ)
    (hpositive : offspringFieldLaw μ {ω | τ ω ≠ ⊤} ≠ 0)
    (roots : StepField α Mark → ι → TreeNode α)
    (hroots : Measurable[hτ.measurableSpace] roots)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace] {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) → ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω))
    (s : StepField α Mark → ι → State) (hs : Measurable[hτ.measurableSpace] s)
    (g : (ι → TreeNode α → Option State) → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
      (selectedSubtreeStepFieldVector roots ω i))) (offspringFieldLaw μ)) :
    let P := (offspringFieldLaw μ)[|{ω | τ ω ≠ ⊤}]
    condExp hτ.measurableSpace P
        (fun ω ↦ g (fun i ↦ stateTree F (s ω i)
          (selectedSubtreeStepFieldVector roots ω i))) =ᵐ[P]
      fun ω ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i ↦ stateTreeKernel μ F hF (s ω i)) := by
  let P := offspringFieldLaw μ
  let E := {ω | τ ω ≠ ⊤}
  let C := P[|E]
  let Q := Measure.infinitePi (fun _ : ι ↦ offspringFieldLaw μ)
  let Y := selectedSubtreeStepFieldVector roots
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ)).compl
  have hEfull : MeasurableSet E := hτ.measurableSpace_le _ hE
  have hY : Measurable Y := selectedSubtreeStepFieldVector_measurable_of_measurable roots
    (hroots.mono hτ.measurableSpace_le le_rfl) hcount
  have : IsProbabilityMeasure C := cond_isProbabilityMeasure hpositive
  have hfactor (A : Set (StepField α Mark)) (hA : MeasurableSet[hτ.measurableSpace] A)
      (B : Set (ι → StepField α Mark)) (hB : MeasurableSet B) :
      C (A ∩ Y ⁻¹' B) = C A * Q B := by
    have hf := stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots hcount hfiber hdepth hinj A B hA hB
    calc
      C (A ∩ Y ⁻¹' B) = (P E)⁻¹ * P ((A ∩ E) ∩ Y ⁻¹' B) := by
        rw [cond_apply hEfull]
        congr 2
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage]
        tauto
      _ = (P E)⁻¹ * (P (A ∩ E) * Q B) := by rw [hf]
      _ = C A * Q B := by
        rw [cond_apply hEfull, Set.inter_comm E A, mul_assoc]
  have hlaw : C.map Y = Q := by
    ext B hB
    rw [Measure.map_apply hY hB]
    simpa only [Set.univ_inter, measure_univ, one_mul] using
      hfactor Set.univ MeasurableSet.univ B hB
  have hind : Indep hτ.measurableSpace (MeasurableSpace.comap Y inferInstance) C := by
    apply (indep_iff_forall_indepSet C).2
    intro A T hA hT
    obtain ⟨B, hB, rfl⟩ := hT
    apply (indepSet_iff_measure_inter_eq_mul (hτ.measurableSpace_le _ hA) (hY hB) C).2
    rw [← Measure.map_apply hY hB, hlaw]
    exact hfactor A hA B hB
  have hi : Integrable (fun ω ↦ g (fun i ↦ stateTree F (s ω i) (Y ω i))) C :=
    hgi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hpositive)
  exact condExp_stateTree_family _ C hτ.measurableSpace_le μ F hF s hs Y hY hind hlaw g hg hi

end ProbabilityTheory.BranchingRandomWalk
