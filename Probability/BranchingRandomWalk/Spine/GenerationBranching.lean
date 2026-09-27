import Probability.BranchingRandomWalk.Spine.Generation
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow

/-!
# First-generation branching decomposition

The root step and each child descendant field have their product law under the
pre-sampled i.i.d. step field. The generation-address equivalence records the
deterministic decomposition of generation `n + 1` into a first child slot and
a generation-`n` address inside that child's subtree.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Generation `n + 1` addresses are a first slot followed by a generation
`n` address. No distinguished or default slot is chosen. -/
def generationConsEquiv (ι : Type*) (n : ℕ) :
    ι × {v : TreeNode ι // v.length = n} ≃
      {u : TreeNode ι // u.length = n + 1} where
  toFun p := ⟨p.1 :: p.2.1, by simp [p.2.2]⟩
  invFun u := by
    have hpos : 0 < u.1.length := by omega
    have hne : u.1 ≠ [] := List.ne_nil_of_length_pos hpos
    exact (u.1.head hne, ⟨u.1.tail, by simp [List.length_tail, u.2]⟩)
  left_inv p := by
    rcases p with ⟨i, v⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  right_inv u := by
    apply Subtype.ext
    exact List.cons_head_tail
      (List.ne_nil_of_length_pos (by omega : 0 < u.1.length))

/-- The root reproduction step and the complete descendant step field below
any one child have the product of their marginal laws. -/
theorem root_subtreeStepField_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (i : ι) :
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι), subtreeStepField [i] ω)) =
      μ.prod (stepFieldLaw μ) := by
  have hrootPast : Measurable[generationFiltration
      (M := Combinatorics.Branching.Step ι X) 1]
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι))
      (subtreeStepField (X := X) [i]) (stepFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (generation_subtreeStepField_independent μ [i]) hrootPast.comap_le
  rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (subtreeStepField_measurable [i]).aemeasurable,
    stepFieldLaw_coordinate μ ([] : TreeNode ι),
    subtreeStepField_law μ [i]]

theorem pathPotential_cons
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : Combinatorics.Branching.StepField ι X)
    (i : ι) (v : TreeNode ι) :
    pathPotential φ ω (i :: v) =
      (ω []).potentialValue' φ i +
        pathPotential φ (subtreeStepField [i] ω) v := by
  rw [show i :: v = [i] ++ v from rfl]
  unfold pathPotential displaceWith
  rw [subtreeStepField_position_decomposition (ω.map φ) [i] v]
  have hmap : subtreeStepField [i] (ω.map φ) =
      Combinatorics.Branching.StepField.map φ
        (subtreeStepField [i] ω) := rfl
  rw [hmap]
  simp [displace, Combinatorics.Branching.StepField.map_apply,
    Step.potentialValue', Step.potentialAt?, value']

theorem weightedGenerationEndpoint_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      weightedGenerationEndpoint φ n f p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hp : Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathPotential φ p.2 u) :=
    (pathPotential_measurable φ [] u).comp measurable_snd
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  apply (show Measurable
      (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
        ENNReal.ofReal (Real.exp (-pathPotential φ p.2 u)) *
          f (p.1 + pathPotential φ p.2 u)) by fun_prop).indicator hevent

theorem generationEndpoint_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      generationEndpoint φ n f p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hp : Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathPotential φ p.2 u) :=
    (pathPotential_measurable φ [] u).comp measurable_snd
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  exact (hf.comp (measurable_fst.add hp)).indicator hevent

theorem measurable_weightedBranchingEndpointOperator
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (weightedBranchingEndpointOperator φ μ f) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.tsum
  intro i
  exact ((realizedPotentialWeight_measurable φ (-1) i).comp measurable_snd).mul
    (hf.comp (measurable_fst.add
      ((Step.potentialValue'_measurable φ i).comp measurable_snd)))

theorem measurable_branchingEndpointOperator
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (branchingEndpointOperator φ μ f) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.tsum
  intro i
  unfold survivingPotentialTest
  exact (hf.comp (measurable_fst.add
    ((Step.potentialValue'_measurable φ i).comp measurable_snd))).ite
      ((survive_measurableSet i).preimage measurable_snd) measurable_const

theorem measurable_weightedBranchingEndpointIterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (weightedBranchingEndpointIterate φ μ n f)
  | 0 => hf
  | n + 1 => measurable_weightedBranchingEndpointOperator φ μ
      (measurable_weightedBranchingEndpointIterate φ μ hf n)

theorem measurable_branchingEndpointIterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (branchingEndpointIterate φ μ n f)
  | 0 => hf
  | n + 1 => measurable_branchingEndpointOperator φ μ
      (measurable_branchingEndpointIterate φ μ hf n)

/-- The actual weighted generation `n + 1` is the sum of the weighted
generation-`n` observables in every surviving first-generation subtree. -/
theorem weightedGenerationEndpoint_succ
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    weightedGenerationEndpoint φ (n + 1) f x ω =
      ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
        weightedGenerationEndpoint φ n f
          (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) := by
  classical
  rw [weightedGenerationEndpoint]
  let generation : Set (TreeNode ι) := {u | u.length = n + 1}
  calc
    (∑' u : TreeNode ι, weightedGenerationTerm φ (n + 1) f x u ω) =
        ∑' u : TreeNode ι, generation.indicator
          (fun u => weightedGenerationTerm φ (n + 1) f x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = n + 1
      · simp [generation, hu]
      · simp [generation, hu, weightedGenerationTerm, Set.indicator]
    _ = ∑' u : generation,
        weightedGenerationTerm φ (n + 1) f x u.1 ω := by
      exact (tsum_subtype generation
        (fun u => weightedGenerationTerm φ (n + 1) f x u ω)).symm
    _ = ∑' p : ι × {v : TreeNode ι // v.length = n},
        weightedGenerationTerm φ (n + 1) f x
          ((generationConsEquiv ι n) p).1 ω := by
      exact (Equiv.tsum_eq (generationConsEquiv ι n)
        (fun u : generation =>
          weightedGenerationTerm φ (n + 1) f x u.1 ω)).symm
    _ = ∑' i : ι, ∑' v : {v : TreeNode ι // v.length = n},
        weightedGenerationTerm φ (n + 1) f x (i :: v.1) ω := by
      change (∑' p : ι × {v : TreeNode ι // v.length = n},
        weightedGenerationTerm φ (n + 1) f x (p.1 :: p.2.1) ω) = _
      exact ENNReal.tsum_prod (f := fun i
          (v : {v : TreeNode ι // v.length = n}) =>
        weightedGenerationTerm φ (n + 1) f x (i :: v.1) ω)
    _ = ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
        weightedGenerationEndpoint φ n f
          (x + (ω []).potentialValue' φ i)
          (subtreeStepField [i] ω) := by
      apply tsum_congr
      intro i
      rw [weightedGenerationEndpoint, ← ENNReal.tsum_mul_left]
      calc
        (∑' v : {v : TreeNode ι // v.length = n},
            weightedGenerationTerm φ (n + 1) f x (i :: v.1) ω) =
            ∑' v : {v : TreeNode ι // v.length = n},
              realizedPotentialWeight φ (-1) (ω []) i *
                weightedGenerationTerm φ n f
                  (x + (ω []).potentialValue' φ i) v.1
                  (subtreeStepField [i] ω) := by
          apply tsum_congr
          intro v
          by_cases hi : survive (ω []) i
          · by_cases hv : surviveAlong (subtreeStepField [i] ω) [] v.1
            · have hv' : surviveAlong ω [i] v.1 :=
                (surviveAlong_rebase ω [i] [] v.1).mp hv
              have hpath : surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong] using And.intro hi hv'
              have hmem : (i :: v.1).length = n + 1 ∧
                  surviveAlong ω [] (i :: v.1) :=
                ⟨by simp [v.2], hpath⟩
              have hmemSub : v.1.length = n ∧
                  surviveAlong (subtreeStepField [i] ω) [] v.1 :=
                ⟨v.2, hv⟩
              simp only [weightedGenerationTerm]
              simp only [Set.indicator_apply]
              simp only [Set.mem_ofPred_eq, hmem, hmemSub]
              rw [pathPotential_cons]
              simp only [realizedPotentialWeight, hi, ite_true, neg_one_mul]
              rw [show -((ω []).potentialValue' φ i +
                    pathPotential φ (subtreeStepField [i] ω) v.1) =
                  -(ω []).potentialValue' φ i +
                    -pathPotential φ (subtreeStepField [i] ω) v.1 by ring]
              rw [Real.exp_add, ENNReal.ofReal_mul
                (Real.exp_nonneg (-(ω []).potentialValue' φ i))]
              simp [add_assoc, mul_assoc]
            · have hv' : ¬ surviveAlong ω [i] v.1 := by
                intro h
                exact hv ((surviveAlong_rebase ω [i] [] v.1).mpr h)
              have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong, hi] using hv'
              simp [weightedGenerationTerm, v.2, hpath, hv,
                realizedPotentialWeight, hi]
          · have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
              simp [surviveAlong, hi]
            simp [weightedGenerationTerm, v.2, hpath,
              realizedPotentialWeight, hi]
        _ = ∑' v : TreeNode ι, {v | v.length = n}.indicator
              (fun v => realizedPotentialWeight φ (-1) (ω []) i *
                weightedGenerationTerm φ n f
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω)) v := by
          exact tsum_subtype {v : TreeNode ι | v.length = n}
            (fun v => realizedPotentialWeight φ (-1) (ω []) i *
              weightedGenerationTerm φ n f
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω))
        _ = ∑' v : TreeNode ι,
              realizedPotentialWeight φ (-1) (ω []) i *
                weightedGenerationTerm φ n f
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω) := by
          apply tsum_congr
          intro v
          by_cases hv : v.length = n
          · simp [hv]
          · simp [hv, weightedGenerationTerm]

/-- The corresponding unweighted generation decomposition. -/
theorem generationEndpoint_succ
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : Combinatorics.Branching.StepField ι X) :
    generationEndpoint φ (n + 1) f x ω =
      ∑' i : ι, survivingPotentialTest φ
        (fun y => generationEndpoint φ n f (x + y)
          (subtreeStepField [i] ω)) (ω []) i := by
  classical
  rw [generationEndpoint]
  let generation : Set (TreeNode ι) := {u | u.length = n + 1}
  calc
    (∑' u : TreeNode ι, generationTerm φ (n + 1) f x u ω) =
        ∑' u : TreeNode ι, generation.indicator
          (fun u => generationTerm φ (n + 1) f x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = n + 1
      · simp [generation, hu]
      · simp [generation, hu, generationTerm, Set.indicator]
    _ = ∑' u : generation, generationTerm φ (n + 1) f x u.1 ω := by
      exact (tsum_subtype generation
        (fun u => generationTerm φ (n + 1) f x u ω)).symm
    _ = ∑' p : ι × {v : TreeNode ι // v.length = n},
        generationTerm φ (n + 1) f x
          ((generationConsEquiv ι n) p).1 ω := by
      exact (Equiv.tsum_eq (generationConsEquiv ι n)
        (fun u : generation => generationTerm φ (n + 1) f x u.1 ω)).symm
    _ = ∑' i : ι, ∑' v : {v : TreeNode ι // v.length = n},
        generationTerm φ (n + 1) f x (i :: v.1) ω := by
      change (∑' p : ι × {v : TreeNode ι // v.length = n},
        generationTerm φ (n + 1) f x (p.1 :: p.2.1) ω) = _
      exact ENNReal.tsum_prod (f := fun i
          (v : {v : TreeNode ι // v.length = n}) =>
        generationTerm φ (n + 1) f x (i :: v.1) ω)
    _ = ∑' i : ι, survivingPotentialTest φ
        (fun y => generationEndpoint φ n f (x + y)
          (subtreeStepField [i] ω)) (ω []) i := by
      apply tsum_congr
      intro i
      unfold survivingPotentialTest
      by_cases hi : survive (ω []) i
      · simp only [hi, ite_true]
        rw [generationEndpoint]
        calc
          (∑' v : {v : TreeNode ι // v.length = n},
              generationTerm φ (n + 1) f x (i :: v.1) ω) =
              ∑' v : {v : TreeNode ι // v.length = n},
                generationTerm φ n f
                  (x + (ω []).potentialValue' φ i) v.1
                  (subtreeStepField [i] ω) := by
            apply tsum_congr
            intro v
            by_cases hv : surviveAlong (subtreeStepField [i] ω) [] v.1
            · have hv' : surviveAlong ω [i] v.1 :=
                  (surviveAlong_rebase ω [i] [] v.1).mp hv
              have hpath : surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong] using And.intro hi hv'
              simp [generationTerm, v.2, hpath, hv, pathPotential_cons,
                add_assoc]
            · have hv' : ¬ surviveAlong ω [i] v.1 := by
                intro h
                exact hv ((surviveAlong_rebase ω [i] [] v.1).mpr h)
              have hpath : ¬ surviveAlong ω [] (i :: v.1) := by
                simpa [surviveAlong, hi] using hv'
              simp [generationTerm, v.2, hpath, hv]
          _ = ∑' v : TreeNode ι, {v | v.length = n}.indicator
                (fun v => generationTerm φ n f
                  (x + (ω []).potentialValue' φ i) v
                  (subtreeStepField [i] ω)) v := by
            exact tsum_subtype {v : TreeNode ι | v.length = n}
              (fun v => generationTerm φ n f
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω))
          _ = ∑' v : TreeNode ι, generationTerm φ n f
                (x + (ω []).potentialValue' φ i) v
                (subtreeStepField [i] ω) := by
            apply tsum_congr
            intro v
            by_cases hv : v.length = n
            · simp [hv]
            · simp [hv, generationTerm]
      · simp only [hi, ite_false]
        apply ENNReal.tsum_eq_zero.mpr
        intro v
        simp [generationTerm, hi, surviveAlong]

/-- Expected actual weighted generation equals the recursively iterated
branching endpoint operator at every generation. -/
theorem lintegral_weightedGenerationEndpoint_eq_iterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ ω, weightedGenerationEndpoint φ n f x ω ∂stepFieldLaw μ) =
        weightedBranchingEndpointIterate φ μ n f x
  | 0, x => by
      simp [weightedBranchingEndpointIterate]
  | n + 1, x => by
      simp_rw [weightedGenerationEndpoint_succ]
      rw [lintegral_tsum]
      · rw [weightedBranchingEndpointIterate,
          weightedBranchingEndpointOperator, lintegral_tsum]
        · apply tsum_congr
          intro i
          let H : (Combinatorics.Branching.Step ι X ×
              Combinatorics.Branching.StepField ι X) → ENNReal := fun z =>
            realizedPotentialWeight φ (-1) z.1 i *
              weightedGenerationEndpoint φ n f
                (x + z.1.potentialValue' φ i) z.2
          have hH : Measurable H := by
            apply ((realizedPotentialWeight_measurable φ (-1) i).comp
              measurable_fst).mul
            exact (weightedGenerationEndpoint_joint_measurable φ n hf).comp
              (((measurable_const.add
                ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
                measurable_snd)
          have hpair : Measurable
              (fun ω : Combinatorics.Branching.StepField ι X =>
                (ω ([] : TreeNode ι), subtreeStepField [i] ω)) :=
            (measurable_pi_apply ([] : TreeNode ι)).prodMk
              (subtreeStepField_measurable [i])
          calc
            (∫⁻ ω, realizedPotentialWeight φ (-1) (ω []) i *
                weightedGenerationEndpoint φ n f
                  (x + (ω []).potentialValue' φ i)
                  (subtreeStepField [i] ω) ∂stepFieldLaw μ) =
                ∫⁻ z, H z ∂(stepFieldLaw μ).map
                  (fun ω => (ω ([] : TreeNode ι),
                    subtreeStepField [i] ω)) := by
              exact (lintegral_map hH hpair).symm
            _ = ∫⁻ z, H z ∂μ.prod (stepFieldLaw μ) := by
              rw [root_subtreeStepField_joint_law μ i]
            _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ := by
              exact lintegral_prod H hH.aemeasurable
            _ = ∫⁻ ξ, realizedPotentialWeight φ (-1) ξ i *
                  weightedBranchingEndpointIterate φ μ n f
                    (x + ξ.potentialValue' φ i) ∂μ := by
              apply lintegral_congr
              intro ξ
              change (∫⁻ η, realizedPotentialWeight φ (-1) ξ i *
                  weightedGenerationEndpoint φ n f
                    (x + ξ.potentialValue' φ i) η ∂stepFieldLaw μ) = _
              rw [lintegral_const_mul _
                (weightedGenerationEndpoint_measurable φ n hf
                  (x + ξ.potentialValue' φ i))]
              rw [lintegral_weightedGenerationEndpoint_eq_iterate φ μ hf n]
            _ = ∫⁻ ξ, realizedPotentialWeight φ (-1) ξ i *
                  weightedBranchingEndpointIterate φ μ n f
                    (x + ξ.potentialValue' φ i) ∂μ := rfl
        · intro i
          exact ((realizedPotentialWeight_measurable φ (-1) i).mul
            ((measurable_weightedBranchingEndpointIterate φ μ hf n).comp
              ((measurable_const : Measurable
                  (fun _ : Combinatorics.Branching.Step ι X => x)).add
                (Step.potentialValue'_measurable φ i)))).aemeasurable
      · intro i
        let H : (Combinatorics.Branching.Step ι X ×
            Combinatorics.Branching.StepField ι X) → ENNReal := fun z =>
          realizedPotentialWeight φ (-1) z.1 i *
            weightedGenerationEndpoint φ n f
              (x + z.1.potentialValue' φ i) z.2
        have hH : Measurable H := by
          apply ((realizedPotentialWeight_measurable φ (-1) i).comp
            measurable_fst).mul
          exact (weightedGenerationEndpoint_joint_measurable φ n hf).comp
            (((measurable_const.add
              ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
              measurable_snd)
        exact hH.comp ((measurable_pi_apply ([] : TreeNode ι)).prodMk
          (subtreeStepField_measurable [i])) |>.aemeasurable

/-- Expected actual unweighted generation equals its recursively iterated
branching endpoint operator at every generation. -/
theorem lintegral_generationEndpoint_eq_iterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ (n : ℕ) (x : ℝ),
      (∫⁻ ω, generationEndpoint φ n f x ω ∂stepFieldLaw μ) =
        branchingEndpointIterate φ μ n f x
  | 0, x => by
      simp [branchingEndpointIterate]
  | n + 1, x => by
      simp_rw [generationEndpoint_succ]
      rw [lintegral_tsum]
      · rw [branchingEndpointIterate,
          branchingEndpointOperator, lintegral_tsum]
        · apply tsum_congr
          intro i
          let H : (Combinatorics.Branching.Step ι X ×
              Combinatorics.Branching.StepField ι X) → ENNReal := fun z =>
            survivingPotentialTest φ
              (fun y => generationEndpoint φ n f (x + y) z.2) z.1 i
          have hH : Measurable H := by
            unfold H survivingPotentialTest
            exact ((generationEndpoint_joint_measurable φ n hf).comp
              (((measurable_const.add
                ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
                measurable_snd)).ite
              ((survive_measurableSet i).preimage measurable_fst)
              measurable_const
          have hpair : Measurable
              (fun ω : Combinatorics.Branching.StepField ι X =>
                (ω ([] : TreeNode ι), subtreeStepField [i] ω)) :=
            (measurable_pi_apply ([] : TreeNode ι)).prodMk
              (subtreeStepField_measurable [i])
          calc
            (∫⁻ ω, survivingPotentialTest φ
                (fun y => generationEndpoint φ n f (x + y)
                  (subtreeStepField [i] ω)) (ω []) i
                ∂stepFieldLaw μ) =
                ∫⁻ z, H z ∂(stepFieldLaw μ).map
                  (fun ω => (ω ([] : TreeNode ι),
                    subtreeStepField [i] ω)) := by
              exact (lintegral_map hH hpair).symm
            _ = ∫⁻ z, H z ∂μ.prod (stepFieldLaw μ) := by
              rw [root_subtreeStepField_joint_law μ i]
            _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ := by
              exact lintegral_prod H hH.aemeasurable
            _ = ∫⁻ ξ, survivingPotentialTest φ
                  (fun y => branchingEndpointIterate φ μ n f (x + y)) ξ i
                  ∂μ := by
              apply lintegral_congr
              intro ξ
              by_cases hi : survive ξ i
              · simp only [H, survivingPotentialTest, hi, ite_true]
                exact lintegral_generationEndpoint_eq_iterate φ μ hf n
                  (x + ξ.potentialValue' φ i)
              · simp [H, survivingPotentialTest, hi]
        · intro i
          unfold survivingPotentialTest
          exact (((measurable_branchingEndpointIterate φ μ hf n).comp
            ((measurable_const : Measurable
                (fun _ : Combinatorics.Branching.Step ι X => x)).add
              (Step.potentialValue'_measurable φ i))).ite
                (survive_measurableSet i) measurable_const).aemeasurable
      · intro i
        let H : (Combinatorics.Branching.Step ι X ×
            Combinatorics.Branching.StepField ι X) → ENNReal := fun z =>
          survivingPotentialTest φ
            (fun y => generationEndpoint φ n f (x + y) z.2) z.1 i
        have hH : Measurable H := by
          unfold H survivingPotentialTest
          exact ((generationEndpoint_joint_measurable φ n hf).comp
            (((measurable_const.add
              ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
              measurable_snd)).ite
            ((survive_measurableSet i).preimage measurable_fst)
            measurable_const
        exact hH.comp ((measurable_pi_apply ([] : TreeNode ι)).prodMk
          (subtreeStepField_measurable [i])) |>.aemeasurable

end ProbabilityTheory.BranchingRandomWalk.Spine
