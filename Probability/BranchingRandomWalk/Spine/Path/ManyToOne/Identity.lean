/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Generation
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess
import Probability.BranchingRandomWalk.Spine.Additive.PathLaw
import Probability.BranchingProcess.Spine.Tree.Density.PathPayoff

/-!
# Path-functional many-to-one identities

The test function sees the complete ancestral position history at times
`0, ..., n`.  The two identities correspond to the exponentially weighted
and unweighted branching sums. The weighted identity is obtained from the
general state-tree adapted-node theorem, through the independent-field law
transport and the observed spine-path law. No branching expectation is
reproved by induction. The right-hand measure is the auxiliary tilted IID
law, whose position law equals the spine under the changed tree measure.
Compare Zhan Shi, *Branching Random Walks* (2015), Theorems 1.1, 4.3 and
4.4(ii), DOI 10.1007/978-3-319-25372-5.

## Public declarations

- `weightedPathManyToOneCore` states
  $\mathbb E[\widehat Z_n(F,x)]=\mathbb E_{\widehat\mu}[F(H_n)]$ for a
  measurable path functional $F$ and the boundary-normalized tilted law.
- `pathManyToOneCore` states
  $\mathbb E[Z_n(F,x)]=\mathbb E_{\widehat\mu}
  [e^{S_n}F(H_n)]$, where $S_n$ is the increment displacement.
- `weightedPathManyToOne` and `pathManyToOne` give the same identities when
  the offspring mark space and the real-valued position space are separate,
  for every measurable displacement map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.RandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory Finset Preorder

private lemma stateTree_apply_additive {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (x : ℝ) (ω : StepField ι Mark) (u : List ι) :
    stateTree (fun x e => x + φ e) x ω u =
      if surviveAlong ω [] u then some (x + pathPotential φ ω u) else none := by
  classical
  by_cases hs : surviveAlong ω [] u <;>
    simp [stateTree, stateAlong?, hs, stateAlong_add, pathPotential]

private lemma prefix_survives {ι Mark : Type*} (ω : StepField ι Mark) (u : List ι)
    (hs : surviveAlong ω [] u) (k : ℕ) : surviveAlong ω [] (u.take k) :=
  surviveAlong_prefix ω (u.take k) (u.drop k) (by simpa only [List.take_append_drop] using hs)

private lemma tuple_take {ι : Type*} (u : List ι) {k : ℕ} (hk : k ≤ u.length) :
    List.ofFn (Fin.take k hk u.get) = u.take k := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i hi hj
    simp [Fin.take]

private lemma addressWeight_stateTree {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (x : ℝ) (ω : StepField ι Mark) (u : List ι) :
    BranchingProcess.Spine.addressWeight Additive.weight u.length u.get
      (BranchingProcess.State.treeHistory u.length
        (stateTree (fun x e => x + φ e) x ω)) =
      if surviveAlong ω [] u then ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) else 0 := by
  classical
  have hroot :
      ((BranchingProcess.State.treeHistory u.length (stateTree (fun x e => x + φ e) x ω))
        ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 Additive.weight ≠ 0 ∧
      ((BranchingProcess.State.treeHistory u.length (stateTree (fun x e => x + φ e) x ω))
        ⟨0, by simp⟩ ((), fun j : Fin 0 => j.elim0)).elim 0 Additive.weight ≠ ∞ := by
    simp [BranchingProcess.State.treeHistory]
  rw [BranchingProcess.Spine.addressWeight_eq_endpointRatio _ _ _ _ hroot]
  by_cases hs : surviveAlong ω [] u
  · have hparents (k : Fin u.length) :
        ((BranchingProcess.State.treeHistory u.length (stateTree (fun x e => x + φ e) x ω))
          ⟨k.1, mem_Iic.mpr k.isLt.le⟩ ((), Fin.take k.1 k.isLt.le u.get)).elim 0 Additive.weight ≠ 0 ∧
        ((BranchingProcess.State.treeHistory u.length (stateTree (fun x e => x + φ e) x ω))
          ⟨k.1, mem_Iic.mpr k.isLt.le⟩ ((), Fin.take k.1 k.isLt.le u.get)).elim 0 Additive.weight ≠ ∞ := by
      simp only [BranchingProcess.State.treeHistory, tuple_take u k.isLt.le]
      rw [stateTree_apply_additive, ite_eq_left (prefix_survives ω u hs k)]
      simp
    rw [ite_eq_left hparents, ite_eq_left hs]
    simp only [BranchingProcess.State.treeHistory, List.ofFn_get]
    rw [stateTree_apply_additive, ite_eq_left hs]
    have hz : (List.ofFn (fun j : Fin 0 => j.elim0) : List ι) = [] := by simp
    rw [hz, stateTree_root]
    simp only [Option.elim_some]
    have hweight : Additive.weight (x + pathPotential φ ω u) =
        Additive.weight x * ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) := by
      unfold Additive.weight
      rw [neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [hweight]
    simpa only [div_eq_mul_inv, mul_assoc] using
      (ENNReal.mul_div_cancel (Additive.weight_ne_zero x) (Additive.weight_ne_top x)
        (b := ENNReal.ofReal (Real.exp (-pathPotential φ ω u))))
  · rw [ite_eq_right hs]
    split_ifs
    · simp only [BranchingProcess.State.treeHistory, List.ofFn_get]
      rw [stateTree_apply_additive, ite_eq_right hs]
      simp
    · rfl

private lemma ancestralHistory_stateTree {ι Mark : Type*} [MeasurableSpace Mark]
    (φ : Potential Mark) (x : ℝ) (ω : StepField ι Mark) (u : List ι)
    (hs : surviveAlong ω [] u) (n : ℕ) :
    BranchingProcess.State.ancestralHistory x n u
      (stateTree (fun x e => x + φ e) x ω) = pathHistory φ n x ω u := by
  funext k
  simp only [BranchingProcess.State.ancestralHistory, pathHistory]
  rw [stateTree_apply_additive, ite_eq_left (prefix_survives ω u hs k)]
  rfl


/-- Weighted path-functional many-to-one identity for the pre-sampled
branching field. -/
theorem weightedPathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      (∫⁻ ω, weightedPathGeneration φ n F x ω ∂offspringFieldLaw μ) =
        ∫⁻ increment, F (history n x increment)
          ∂tiltedIncrementFieldLaw φ μ := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  intro n F hF x
  let s : {y // Additive.weight y ≠ 0 ∧ Additive.weight y ≠ ∞} :=
    ⟨x, Additive.weight_ne_zero x, Additive.weight_ne_top x⟩
  let harmonic := fun y (_ : Additive.weight y ≠ 0) (_ : Additive.weight y ≠ ∞) =>
    Additive.harmonic_weight φ μ hboundary y
  let G (t : List ι → Option ℝ) : ENNReal := ∑' u : List ι, if u.length = n then
    BranchingProcess.Spine.addressWeight Additive.weight u.length u.get
      (BranchingProcess.State.treeHistory u.length t) *
      F (BranchingProcess.State.ancestralHistory x n u t) else 0
  have hG : Measurable G := by
    apply Measurable.tsum
    intro u
    exact (((BranchingProcess.Spine.measurable_addressWeight Additive.measurable_weight _ _).comp
      (BranchingProcess.State.measurable_treeHistory _)).mul
      (hF.comp ((BranchingProcess.State.measurable_ancestralHistory x n u).mono
        (BranchingProcess.State.treeFiltration.le _) le_rfl))).ite
      (MeasurableSet.const _) measurable_const
  have hupdate : Measurable (Function.uncurry (fun (y : ℝ) (e : X) => y + φ e)) :=
    measurable_fst.add (φ.measurable_toFun.comp measurable_snd)
  have hm : Measurable (stateTree (fun x e => x + φ e) x : StepField ι X → List ι → Option ℝ) :=
    (stateTree_measurable (fun (y : ℝ) (e : X) => y + φ e) hupdate).comp
      (show Measurable (fun ω : StepField ι X => (x, ω)) from
        measurable_const.prodMk measurable_id)
  have heq (ω : StepField ι X) : G (stateTree (fun x e => x + φ e) x ω) =
      weightedPathGeneration φ n F x ω := by
    dsimp only [G, weightedPathGeneration]
    apply tsum_congr
    intro u
    rw [addressWeight_stateTree]
    by_cases hn : u.length = n <;> by_cases hs : surviveAlong ω [] u <;>
      simp [weightedPathGenerationTerm, hn, hs]
    rw [ancestralHistory_stateTree φ x ω u hs]
  have hmap := lintegral_map (μ := offspringFieldLaw μ) hG hm
  rw [Additive.map_stateTree_law] at hmap
  have hpath := BranchingProcess.Spine.lintegral_pathPayoff_eq
    (Additive.offspringKernel φ μ) Additive.measurable_weight harmonic s s n hF
  have hproj : Measurable (fun z : ℕ → ℝ => F (fun k : Fin (n + 1) => z k)) :=
    hF.comp (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  have hobs : Measurable (fun t : List ι → Option
      (ℝ ⊕ {y // Additive.weight y ≠ 0 ∧ Additive.weight y ≠ ∞}) =>
      fun n => (BranchingProcess.Spine.statePath s t n).1) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_subtype_coe.comp
      ((measurable_pi_apply k).comp (BranchingProcess.Spine.measurable_statePath s))
  have hright := lintegral_map
    (μ := BranchingProcess.Spine.treeKernel (Additive.offspringKernel φ μ)
      Additive.measurable_weight harmonic (some (Sum.inr s))) hproj hobs
  rw [Additive.map_spinePath_law φ μ hboundary x,
    lintegral_map hproj (RandomWalk.positionProcess_path_measurable x)] at hright
  calc
    _ = ∫⁻ t, G t ∂BranchingProcess.State.treeKernel
        (Additive.offspringKernel φ μ) (some x) := by
      rw [hmap]
      exact lintegral_congr fun ω => (heq ω).symm
    _ = ∫⁻ t, F (fun k => (BranchingProcess.Spine.statePath s t k).1)
        ∂BranchingProcess.Spine.treeKernel (Additive.offspringKernel φ μ)
          Additive.measurable_weight harmonic (some (Sum.inr s)) := hpath
    _ = _ := by
      convert hright.symm using 1
      apply lintegral_congr
      intro ξ
      congr 1
      funext k
      exact congrFun (history_eq_fromIncrements n x ξ) k

/-- Unweighted path-functional many-to-one identity, with the reciprocal
exponential weight determined by the terminal spine displacement. -/
theorem pathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration φ n F x ω ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (history n x increment)
        ∂tiltedIncrementFieldLaw φ μ := by
  let weightedTest : (Fin (n + 1) → ℝ) → ENNReal := fun history =>
    ENNReal.ofReal
      (Real.exp (history ⟨n, Nat.lt_succ_self n⟩ - x)) * F history
  have hweightedTest : Measurable weightedTest := by
    exact ((measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).sub
      measurable_const).exp.ennreal_ofReal.mul hF
  simp_rw [pathGeneration_eq_weightedPathGeneration]
  rw [weightedPathManyToOneCore φ μ hboundary n hweightedTest x]
  apply lintegral_congr
  intro increment
  unfold weightedTest
  rw [history_last]
  rw [AdditivePath.fromIncrements_apply]
  rw [show x + AdditivePath.displacement n increment - x =
    AdditivePath.displacement n increment by ring]

/-- Path-functional weighted many-to-one with separate mark and position
spaces.  The displacement map is only required to be measurable. -/
theorem weightedPathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPathGeneration (potential.comp d hd) n F x ω
        ∂offspringFieldLaw μ) =
      ∫⁻ increment, F (history n x increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  weightedPathManyToOneCore (potential.comp d hd) μ hboundary n hF x

/-- Path-functional unweighted many-to-one with separate mark and position
spaces. -/
theorem pathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration (potential.comp d hd) n F x ω
        ∂offspringFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          F (history n x increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  pathManyToOneCore (potential.comp d hd) μ hboundary n hF x

end ProbabilityTheory.BranchingRandomWalk.Spine
