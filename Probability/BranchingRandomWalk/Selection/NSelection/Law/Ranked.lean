/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Common offspring marks for ranked selection

## Public declarations

* `rankedPopulationTrajectory` is the trajectory of ranked positions obtained
  by repeating one branching-selection step with fresh marks for every rank.
* `rankedPopulationLaw` is the trajectory law for an initial vector with law
  `ρ` and an independent environment of i.i.d. offspring marks of law `μ`.
* `exists_rankedPopulationCoupling_of_capacity_le` couples the trajectory laws
  for jointly distributed initial vectors in increasing spatial order. For
  $N_1\le N_2$ and
  $X^2_{0,i}\le X^1_{0,i}$ almost surely at each $i<N_1$, the coupled
  trajectories satisfy $X^2_{n,i}\le X^1_{n,i}$ simultaneously for all $n,i$.
* `exists_rankedPopulationStepCoupling_of_capacity_le` gives the corresponding
  one-generation coupling, with $X^2_{1,i}\le X^1_{1,i}$ for $i<N_1$.
* `populationCountingMeasure` is the measure $\sum_{i<N}\delta_{x_i}$ of a
  ranked population, including multiplicities.
* `populationTrajectoryLaw` is the joint law of these counting measures over
  all generations.
* `populationTrajectoryLaw_translate` pushes the law from $N\delta_0$
  forward by translating every counting measure by $a$, giving the law from
  $N\delta_a$.

The construction uses common marks at the same parent rank and generation,
as in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.9 and
Corollaries 3.10–3.11. For the capacity comparison, the offspring law has
nonempty offspring and finite exponential weight almost surely under the
boundary-normalization assumptions of that work.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open MeasureTheory
open Combinatorics.Branching
open Frontier.AsymptoticSpeed

/-- The ranked recursion over the initial vector and the generation batches. -/
noncomputable def rankedPopulationTrajectory {N : ℕ}
    (sample : (Fin N → ℝ) × GenerationEnvironment N) : ℕ → Fin N → ℝ :=
  fun n => measurableRepairedInfiniteOffspringRun n sample

private theorem measurable_rankedPopulationTrajectory {N : ℕ} :
    Measurable (rankedPopulationTrajectory (N := N)) :=
  measurable_pi_iff.2 measurable_measurableRepairedInfiniteOffspringRun

/-- Independent initial population and offspring environment, pushed forward
to the whole trajectory. -/
noncomputable def rankedPopulationLaw {N : ℕ}
    (μ : Measure (Step ℕ ℝ)) (ρ : Measure (Fin N → ℝ)) :
    Measure (ℕ → Fin N → ℝ) :=
  (ρ.prod (generationEnvironmentLaw μ N)).map rankedPopulationTrajectory

private theorem measurePreserving_restrictRanks {N₁ N₂ : ℕ}
    (hcapacity : N₁ ≤ N₂) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    MeasurePreserving
      (fun (ω : GenerationEnvironment N₂) n => ω n ∘ Fin.castLE hcapacity)
      (generationEnvironmentLaw μ N₂) (generationEnvironmentLaw μ N₁) := by
  have hmeas : Measurable (fun (b : GenerationBatch N₂) => b ∘ Fin.castLE hcapacity) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (Fin.castLE hcapacity i)
  refine ⟨measurable_pi_iff.2 fun n => hmeas.comp (measurable_pi_apply n), ?_⟩
  unfold generationEnvironmentLaw
  rw [Measure.infinitePi_map_pi _ (fun _ => hmeas)]
  congr 1
  funext n
  unfold generationBatchLaw
  simp only [← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin N₂ => μ) (Fin.castLE_injective hcapacity)

private theorem rankedPopulationTrajectory_le_of_capacity_le {N₁ N₂ : ℕ}
    (hcapacity : N₁ ≤ N₂)
    (x : Fin N₁ → ℝ) (y : Fin N₂ → ℝ) (ω : GenerationEnvironment N₂)
    (hgoodSmall : ∀ n, IsGoodInfiniteOffspringBatch (ω n ∘ Fin.castLE hcapacity))
    (hgoodLarge : ∀ n, IsGoodInfiniteOffspringBatch (ω n))
    (hpositions : ∀ i, y (Fin.castLE hcapacity i) ≤ x i) :
    ∀ n i, rankedPopulationTrajectory (y, ω) n (Fin.castLE hcapacity i) ≤
      rankedPopulationTrajectory (x, fun n => ω n ∘ Fin.castLE hcapacity) n i := by
  let small : GenerationEnvironment N₁ := fun n => ω n ∘ Fin.castLE hcapacity
  have hrun {N : ℕ} (v : Fin N → ℝ) (env : GenerationEnvironment N)
      (hgood : ∀ n, IsGoodInfiniteOffspringBatch (env n)) (n : ℕ) :
      rankedPopulationTrajectory (v, env) n = infiniteOffspringRun env hgood v n := by
    unfold rankedPopulationTrajectory
    rw [measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
    apply infiniteOffspringRun_congr
    funext t
    exact repairGenerationBatch_eq_of_repairable (env t) (hgood t)
  intro n
  rw [hrun y ω hgoodLarge, hrun x small hgoodSmall]
  induction n with
  | zero => exact hpositions
  | succ n ih =>
    rw [infiniteOffspringRun_succ, infiniteOffspringRun_succ]
    let xs := infiniteOffspringRun small hgoodSmall x n
    let ys := infiniteOffspringRun ω hgoodLarge y n
    exact infiniteOffspringPosition_select_mono_of_capacity_le hcapacity xs ys (ω n)
      (infiniteOffspringFirstN xs (small n) (hgoodSmall n).finiteWeight)
      (infiniteOffspringFirstN ys (ω n) (hgoodLarge n).finiteWeight)
      (infiniteOffspringFirstN_spec xs (small n) (hgoodSmall n).finiteWeight)
      (infiniteOffspringFirstN_spec ys (ω n) (hgoodLarge n).finiteWeight)
      (infiniteOffspringFirstN_card xs (small n) (hgoodSmall n))
      (infiniteOffspringFirstN_card ys (ω n) (hgoodLarge n)) ih

private theorem rankedPopulationTrajectory_monotone {N : ℕ}
    (sample : (Fin N → ℝ) × GenerationEnvironment N) (h : Monotone sample.1) (n : ℕ) :
    Monotone (rankedPopulationTrajectory sample n) := by
  unfold rankedPopulationTrajectory
  rw [measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
  exact infiniteOffspringRun_monotone _ _ _ h n

/-- Share the marks at the same spatial rank at every generation. The law
of each trajectory includes its original initial vector at generation zero. -/
theorem exists_rankedPopulationCoupling_of_capacity_le
    {N₁ N₂ : ℕ} (hcapacity : N₁ ≤ N₂)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (ρ : Measure ((Fin N₁ → ℝ) × (Fin N₂ → ℝ))) [IsProbabilityMeasure ρ]
    (hsorted : ∀ᵐ z ∂ρ, Monotone z.1 ∧ Monotone z.2)
    (horder : ∀ᵐ z ∂ρ, ∀ i, z.2 (Fin.castLE hcapacity i) ≤ z.1 i) :
    let P := ρ.prod (generationEnvironmentLaw μ N₂)
    ∃ (Z₁ : _ → ℕ → Fin N₁ → ℝ) (Z₂ : _ → ℕ → Fin N₂ → ℝ),
      MeasurePreserving Z₁ P (rankedPopulationLaw μ (ρ.map Prod.fst)) ∧
      MeasurePreserving Z₂ P (rankedPopulationLaw μ (ρ.map Prod.snd)) ∧
      (∀ sample, Z₁ sample 0 = sample.1.1 ∧ Z₂ sample 0 = sample.1.2) ∧
      ∀ᵐ sample ∂P, ∀ n,
        Monotone (Z₁ sample n) ∧ Monotone (Z₂ sample n) ∧
        ∀ i, Z₂ sample n (Fin.castLE hcapacity i) ≤ Z₁ sample n i := by
  intro P
  let := generationEnvironmentLaw_isProbability μ N₂
  have hrestrict := measurePreserving_restrictRanks hcapacity μ
  let small (ω : GenerationEnvironment N₂) : GenerationEnvironment N₁ :=
    fun n => ω n ∘ Fin.castLE hcapacity
  have hsmall : Measurable small := hrestrict.measurable
  let Sample := ((Fin N₁ → ℝ) × (Fin N₂ → ℝ)) × GenerationEnvironment N₂
  let Z₁ : Sample → ℕ → Fin N₁ → ℝ :=
    rankedPopulationTrajectory ∘ Prod.map Prod.fst small
  let Z₂ : Sample → ℕ → Fin N₂ → ℝ :=
    rankedPopulationTrajectory ∘ Prod.map Prod.snd id
  refine ⟨Z₁, Z₂, ⟨measurable_rankedPopulationTrajectory.comp (by fun_prop), ?_⟩,
    ⟨measurable_rankedPopulationTrajectory.comp (by fun_prop), ?_⟩,
    fun _ => ⟨rfl, rfl⟩, ?_⟩
  · change P.map Z₁ = _
    rw [rankedPopulationLaw, ← hrestrict.map_eq,
      Measure.map_prod_map _ _ measurable_fst hsmall,
      Measure.map_map measurable_rankedPopulationTrajectory (by fun_prop)]
  · change P.map Z₂ = _
    rw [rankedPopulationLaw, ← Measure.map_id (μ := generationEnvironmentLaw μ N₂),
      Measure.map_prod_map _ _ measurable_snd measurable_id,
      Measure.map_map measurable_rankedPopulationTrajectory (by fun_prop)]
  have hlargeGood := generationEnvironmentLaw_ae_allGood μ hboundary hnonempty N₂
  have hsmallGood := hrestrict.quasiMeasurePreserving.ae
    (generationEnvironmentLaw_ae_allGood μ hboundary hnonempty N₁)
  have hfst := measurePreserving_fst (μ := ρ) (ν := generationEnvironmentLaw μ N₂)
  have hsnd := measurePreserving_snd (μ := ρ) (ν := generationEnvironmentLaw μ N₂)
  filter_upwards [hfst.quasiMeasurePreserving.ae horder, hfst.quasiMeasurePreserving.ae hsorted,
    hsnd.quasiMeasurePreserving.ae hlargeGood, hsnd.quasiMeasurePreserving.ae hsmallGood]
    with sample hpos hs hgoodLarge hgoodSmall n
  exact ⟨rankedPopulationTrajectory_monotone _ hs.1 n,
    rankedPopulationTrajectory_monotone _ hs.2 n,
    rankedPopulationTrajectory_le_of_capacity_le hcapacity sample.1.1 sample.1.2
      sample.2 hgoodSmall hgoodLarge hpos n⟩

/-- The generation-one marginal of the common-rank trajectory coupling. -/
theorem exists_rankedPopulationStepCoupling_of_capacity_le
    {N₁ N₂ : ℕ} (hcapacity : N₁ ≤ N₂)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (ρ : Measure ((Fin N₁ → ℝ) × (Fin N₂ → ℝ))) [IsProbabilityMeasure ρ]
    (hsorted : ∀ᵐ z ∂ρ, Monotone z.1 ∧ Monotone z.2)
    (horder : ∀ᵐ z ∂ρ, ∀ i, z.2 (Fin.castLE hcapacity i) ≤ z.1 i) :
    let P := ρ.prod (generationEnvironmentLaw μ N₂)
    ∃ (Z₁ : _ → Fin N₁ → ℝ) (Z₂ : _ → Fin N₂ → ℝ),
      MeasurePreserving Z₁ P ((rankedPopulationLaw μ (ρ.map Prod.fst)).map (Function.eval 1)) ∧
      MeasurePreserving Z₂ P ((rankedPopulationLaw μ (ρ.map Prod.snd)).map (Function.eval 1)) ∧
      ∀ᵐ sample ∂P, Monotone (Z₁ sample) ∧ Monotone (Z₂ sample) ∧
        ∀ i, Z₂ sample (Fin.castLE hcapacity i) ≤ Z₁ sample i := by
  obtain ⟨Z₁, Z₂, hZ₁, hZ₂, -, hle⟩ :=
    exists_rankedPopulationCoupling_of_capacity_le hcapacity μ hboundary hnonempty ρ hsorted horder
  exact ⟨_, _, MeasurePreserving.comp ⟨measurable_pi_apply 1, rfl⟩ hZ₁,
    MeasurePreserving.comp ⟨measurable_pi_apply 1, rfl⟩ hZ₂, hle.mono fun _ h => h 1⟩

/-- A counting measure retains repeated positions as separate particles. -/
noncomputable def populationCountingMeasure {N : ℕ} (x : Fin N → ℝ) : Measure ℝ :=
  ∑ i, Measure.dirac (x i)

private theorem measurable_populationCountingMeasure {N : ℕ} :
    Measurable (populationCountingMeasure (N := N)) := by
  unfold populationCountingMeasure
  exact Finset.measurable_sum _ fun i _ => Measure.measurable_dirac.comp (measurable_pi_apply i)

/-- The trajectory of particle counting measures under the ranked law. -/
noncomputable def populationTrajectoryLaw {N : ℕ}
    (μ : Measure (Step ℕ ℝ)) (ρ : Measure (Fin N → ℝ)) : Measure (ℕ → Measure ℝ) :=
  (rankedPopulationLaw μ ρ).map (fun path n => populationCountingMeasure (path n))

private theorem populationCountingMeasure_translate {N : ℕ} (a : ℝ) (x : Fin N → ℝ) :
    populationCountingMeasure (fun i => x i + a) =
      (populationCountingMeasure x).map (· + a) := by
  ext s hs
  have hshift : Measurable (fun x : ℝ => x + a) := by fun_prop
  simp [populationCountingMeasure, Measure.map_apply hshift hs,
    hs, hshift hs, Measure.dirac_apply', Set.indicator]
  congr 1

/-- With the same generation batches, translation holds at every generation.
Pushing the law of the counting measures forward gives the translated law. -/
theorem populationTrajectoryLaw_translate {N : ℕ} (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (a : ℝ) :
    populationTrajectoryLaw μ (Measure.dirac (fun _ : Fin N => a)) =
      (populationTrajectoryLaw μ (Measure.dirac (fun _ : Fin N => (0 : ℝ)))).map
        (fun path n => (path n).map (· + a)) := by
  let := generationEnvironmentLaw_isProbability μ N
  have hcount : Measurable (fun (path : ℕ → Fin N → ℝ) n =>
      populationCountingMeasure (path n)) :=
    measurable_pi_iff.2 fun n => measurable_populationCountingMeasure.comp (measurable_pi_apply n)
  have hshift : Measurable (fun (path : ℕ → Measure ℝ) n => (path n).map (· + a)) :=
    measurable_pi_iff.2 fun n => (Measure.measurable_map _ (by fun_prop)).comp (measurable_pi_apply n)
  have hsample (c : ℝ) : Measurable (fun (ω : GenerationEnvironment N) =>
      ((fun _ : Fin N => c), ω)) := measurable_const.prodMk measurable_id
  have hLaw (c : ℝ) :
      populationTrajectoryLaw μ (Measure.dirac (fun _ : Fin N => c)) =
        (generationEnvironmentLaw μ N).map (fun ω n =>
          populationCountingMeasure (rankedPopulationTrajectory ((fun _ => c), ω) n)) := by
    unfold populationTrajectoryLaw rankedPopulationLaw
    rw [Measure.map_map hcount measurable_rankedPopulationTrajectory, Measure.dirac_prod]
    exact Measure.map_map (hcount.comp measurable_rankedPopulationTrajectory) (hsample c)
  have hzero : Measurable (fun (ω : GenerationEnvironment N) n =>
      populationCountingMeasure (rankedPopulationTrajectory ((fun _ => 0), ω) n)) :=
    (hcount.comp measurable_rankedPopulationTrajectory).comp (hsample 0)
  rw [hLaw a, hLaw 0, Measure.map_map hshift hzero]
  apply congrArg (fun f => (generationEnvironmentLaw μ N).map f)
  funext ω n
  change populationCountingMeasure (rankedPopulationTrajectory ((fun _ => a), ω) n) =
    (populationCountingMeasure (rankedPopulationTrajectory ((fun _ => 0), ω) n)).map (· + a)
  simp only [rankedPopulationTrajectory, measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun]
  let env : GenerationEnvironment N := fun t => repairGenerationBatch (ω t)
  have hgood (t : ℕ) : IsGoodInfiniteOffspringBatch (env t) :=
    repairGenerationBatch_repairable (ω t)
  change populationCountingMeasure (infiniteOffspringRun env hgood (fun _ => a) n) =
    (populationCountingMeasure (infiniteOffspringRun env hgood (fun _ => 0) n)).map (· + a)
  have h := infiniteOffspringRun_shift env hgood (fun _ => 0) a n
  simp only [zero_add] at h
  rw [h]
  exact populationCountingMeasure_translate _ _

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
