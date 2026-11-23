/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.StoppingLine.Mass
public import Probability.BranchingProcess.State.Kernel
public import Probability.Process.Tree.Line.Optional
public import Mathlib.Probability.Martingale.Convergence
import all Probability.BranchingProcess.Spine.StoppingLine.Lemmas.Truncation
import Probability.BranchingProcess.Spine.Tree.Density.FiniteGeneration

/-!
# Generation truncation of a simple line

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.StoppingLine`:

* `martingale_truncatedMass` proves this is a native martingale in the
  original tree's generation filtration when `L` is a simple optional line.
* `ae_truncatedMass_eq` identifies this real mass almost surely with
  `(mass h (Line.truncate L n)).toReal`, using finite mean-harmonic mass.
* `integral_truncatedMass` proves `E[S_n] = 1` at every generation.
* `ae_tendsto_truncatedMass` proves almost-sure convergence to the native
  filtration limit process. Identifying that limit with full line mass requires
  the additional expectation-preservation hypothesis.

Assumptions are those of the existing finite-generation spine density:
measurable mean-harmonic weights on the finite positive region, an eligible
root, arbitrary measurable states and countable child slots. Simplicity uses
all states through a generation, including other branches. No higher moment,
path coverage or uniform integrability is assumed.

This is the mass recursion and martingale assertion in J. D. Biggins and
A. E. Kyprianou, *Measure change in multitype branching* (2004), §14,
Lemma 14.3, pp. 578–579, DOI 10.1239/aap/1086957585. The one-step conservation
identity is derived from the existing canonical spine density; stopped mass
is a sum of original tree weights, not another tree process.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.StoppingLine

open Classical MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

set_option backward.isDefEq.respectTransparency false in
/-- The mass frozen at `L` before generation `n`, together with the unexited
mass at `n`, is the martingale of Biggins–Kyprianou (2004), Lemma 14.3. -/
theorem martingale_truncatedMass
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {past : Set (Unit × List ι) → MeasurableSpace (List ι → Option S)}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsOptionalLine past L) (hs : hL.IsSimple State.treeFiltration) :
    Martingale (truncatedMass h L) (State.treeFiltration (ι := ι))
      (State.treeKernel Q (some s.1)) := by
  let P := State.treeKernel Q (some s.1)
  have hma (n : ℕ) : Measurable[State.treeFiltration n] (generationMass h L n) := by
    unfold generationMass
    apply measurable_generation_cut hh n
    intro z
    have hz := hs ((), List.ofFn z)
    rw [List.length_ofFn] at hz
    exact hz
  have hmb (n : ℕ) : Measurable[State.treeFiltration n] (unexitedMass h L n) := by
    unfold unexitedMass
    refine measurable_generation_cut hh n (fun z t =>
      ∀ k < n, ((), (List.ofFn z).take k) ∉ L t) ?_
    intro z
    have hz := measurable_line_test hL hs (List.ofFn z)
    rw [List.length_ofFn] at hz
    simpa only [List.length_ofFn] using hz
  have hba (n : ℕ) : (∫⁻ t, generationMass h L n t ∂P) < ∞ :=
    lt_of_le_of_lt (lintegral_generation_cut_le_one Q hh harmonic s n _) ENNReal.one_lt_top
  have hbb (n : ℕ) : (∫⁻ t, unexitedMass h L n t ∂P) < ∞ := by
    unfold unexitedMass
    exact lt_of_le_of_lt (lintegral_generation_cut_le_one Q hh harmonic s n
      (fun z t => ∀ k < n, ((), (List.ofFn z).take k) ∉ L t)) ENNReal.one_lt_top
  have hia (n : ℕ) : Integrable (fun t => (generationMass h L n t).toReal) P :=
    integrable_toReal_of_lintegral_ne_top
      ((hma n).mono (State.treeFiltration.le n) le_rfl).aemeasurable (hba n).ne
  have hib (n : ℕ) : Integrable (fun t => (unexitedMass h L n t).toReal) P :=
    integrable_toReal_of_lintegral_ne_top
      ((hmb n).mono (State.treeFiltration.le n) le_rfl).aemeasurable (hbb n).ne
  have hiaSum (n : ℕ) : Integrable
      (fun t => ∑ k ∈ range n, (generationMass h L k t).toReal) P := by
    exact integrable_finsetSum _ (fun k _ => hia k)
  have hadp : StronglyAdapted State.treeFiltration (truncatedMass h L) := by
    intro n
    apply StronglyMeasurable.add
    · apply Finset.stronglyMeasurable_fun_sum
      intro k hk
      exact (((hma k).mono (State.treeFiltration.mono (by simpa using (mem_range.mp hk).le))
        le_rfl).ennreal_toReal).stronglyMeasurable
    · exact (hmb n).ennreal_toReal.stronglyMeasurable
  refine martingale_of_setIntegral_eq_succ hadp (fun n => (hiaSum n).add (hib n)) ?_
  intro n B hB
  have he := lintegral_boundary_survival Q hh harmonic s hL hs n hB
  have hfinA : ∀ᵐ t ∂P.restrict B, generationMass h L n t < ∞ :=
    ae_restrict_of_ae (ae_lt_top ((hma n).mono (State.treeFiltration.le n) le_rfl) (hba n).ne)
  have hfinB (m : ℕ) : ∀ᵐ t ∂P.restrict B, unexitedMass h L m t < ∞ :=
    ae_restrict_of_ae (ae_lt_top ((hmb m).mono (State.treeFiltration.le m) le_rfl) (hbb m).ne)
  have hreal : (∫ t in B, (generationMass h L n t).toReal ∂P) +
      (∫ t in B, (unexitedMass h L (n + 1) t).toReal ∂P) =
      ∫ t in B, (unexitedMass h L n t).toReal ∂P := by
    rw [integral_toReal (((hma n).mono (State.treeFiltration.le n) le_rfl).aemeasurable) hfinA,
      integral_toReal (((hmb (n + 1)).mono (State.treeFiltration.le (n + 1)) le_rfl).aemeasurable)
        (hfinB (n + 1)),
      integral_toReal (((hmb n).mono (State.treeFiltration.le n) le_rfl).aemeasurable) (hfinB n)]
    have hai : (∫⁻ t in B, generationMass h L n t ∂P) ≠ ∞ :=
      (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)) (hba n)).ne
    have hbi : (∫⁻ t in B, unexitedMass h L (n + 1) t ∂P) ≠ ∞ :=
      (lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)) (hbb (n + 1))).ne
    exact (ENNReal.toReal_add hai hbi).symm.trans (congrArg ENNReal.toReal he)
  change (∫ t in B, (∑ k ∈ range n, (generationMass h L k t).toReal) +
    (unexitedMass h L n t).toReal ∂P) =
    ∫ t in B, (∑ k ∈ range (n + 1), (generationMass h L k t).toReal) +
      (unexitedMass h L (n + 1) t).toReal ∂P
  simp only [sum_range_succ]
  let F : (List ι → Option S) → ℝ := fun t =>
    ∑ k ∈ range n, (generationMass h L k t).toReal
  let A : (List ι → Option S) → ℝ := fun t => (generationMass h L n t).toReal
  let U : (List ι → Option S) → ℝ := fun t => (unexitedMass h L n t).toReal
  let V : (List ι → Option S) → ℝ := fun t => (unexitedMass h L (n + 1) t).toReal
  change (∫ t in B, (F + U) t ∂P) = ∫ t in B, ((F + A) + V) t ∂P
  have hF : Integrable F (P.restrict B) := (hiaSum n).integrableOn
  have hA : Integrable A (P.restrict B) := (hia n).integrableOn
  have hU : Integrable U (P.restrict B) := (hib n).integrableOn
  have hV : Integrable V (P.restrict B) := (hib (n + 1)).integrableOn
  simp only [Pi.add_apply]
  have hFA : Integrable (fun t => F t + A t) (P.restrict B) := hF.add hA
  rw [integral_add hF hU, integral_add hFA hV, integral_add hF hA]
  change (∫ t in B, A t ∂P) + (∫ t in B, V t ∂P) = ∫ t in B, U t ∂P at hreal
  linarith

/-- The real frozen mass is the actual existing truncated line's mass almost
surely. All its finitely many generation components are finite by normalization. -/
theorem ae_truncatedMass_eq
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    (L : (List ι → Option S) → Set (Unit × List ι))
    (hL : ∀ t, RootIndexed.IsLine (L t)) (n : ℕ) :
    (fun t => truncatedMass h L n t) =ᵐ[State.treeKernel Q (some s.1)]
      (fun t => (mass h (fun x => RootIndexed.Line.truncate (L x) n) t).toReal) := by
  have hfin : ∀ᵐ t ∂State.treeKernel Q (some s.1),
      ∀ k : ℕ, totalWeight h k (State.treeHistory k t) ≠ ∞ := by
    apply ae_all_iff.mpr
    intro k
    have hi := lintegral_totalWeight Q hh harmonic s k
    change (∫⁻ t, totalWeight h k (State.treeHistory k t)
      ∂State.treeKernel Q (some s.1)) = 1 at hi
    exact (ae_lt_top ((measurable_totalWeight hh k).comp (State.measurable_treeHistory k))
      (hi.trans_ne ENNReal.one_ne_top)).mono fun _ ht => ht.ne
  filter_upwards [hfin] with t ht
  have ha (k : ℕ) : generationMass h L k t ≠ ∞ := by
    apply (lt_of_le_of_lt ?_ (ht k).lt_top).ne
    unfold generationMass totalWeight
    apply tsum_le_tsum
    intro z
    dsimp only
    split_ifs <;> simp
  have hb : unexitedMass h L n t ≠ ∞ := by
    apply (lt_of_le_of_lt ?_ (ht n).lt_top).ne
    unfold unexitedMass totalWeight
    apply tsum_le_tsum
    intro z
    dsimp only
    split_ifs <;> simp
  rw [mass_truncate h L t (hL t) n,
    ENNReal.toReal_add (ENNReal.sum_ne_top.mpr (fun k _ => ha k)) hb,
    ENNReal.toReal_sum (fun k _ => ha k)]
  rfl

/-- The truncated line martingale preserves the normalized root expectation
(Biggins–Kyprianou (2004), Lemma 14.3, pp. 578–579). -/
theorem integral_truncatedMass
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {past : Set (Unit × List ι) → MeasurableSpace (List ι → Option S)}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsOptionalLine past L) (hs : hL.IsSimple State.treeFiltration) (n : ℕ) :
    (∫ t, truncatedMass h L n t ∂State.treeKernel Q (some s.1)) = 1 := by
  have hm := martingale_truncatedMass Q hh harmonic s hL hs
  have hi := hm.setIntegral_eq (i := 0) (j := n) (Nat.zero_le n) MeasurableSet.univ
  simpa only [setIntegral_univ, truncatedMass_zero, integral_const,
    Measure.restrict_univ, probReal_univ, one_smul] using hi.symm

/-- The nonnegative frozen-mass martingale converges almost surely, using
Mathlib's L¹-bounded submartingale convergence theorem. -/
theorem ae_tendsto_truncatedMass
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {past : Set (Unit × List ι) → MeasurableSpace (List ι → Option S)}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsOptionalLine past L) (hs : hL.IsSimple State.treeFiltration) :
    ∀ᵐ t ∂State.treeKernel Q (some s.1),
      Filter.Tendsto (fun n => truncatedMass h L n t) Filter.atTop
        (nhds (State.treeFiltration.limitProcess (truncatedMass h L)
          (State.treeKernel Q (some s.1)) t)) := by
  have hm := martingale_truncatedMass Q hh harmonic s hL hs
  have hpos (n : ℕ) (t : List ι → Option S) : 0 ≤ truncatedMass h L n t := by
    exact add_nonneg (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hnorm (n : ℕ) : (fun t : List ι → Option S => ‖truncatedMass h L n t‖) =
      truncatedMass h L n := by
    funext t
    exact Real.norm_of_nonneg (hpos n t)
  have hb (n : ℕ) : eLpNorm (truncatedMass h L n) 1
      (State.treeKernel Q (some s.1)) = 1 := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hm.integrable n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_eNorm (hm.integrable n), hnorm,
      integral_truncatedMass Q hh harmonic s hL hs, ENNReal.ofReal_one]
  exact hm.submartingale.ae_tendsto_limitProcess
    (lt_of_le_of_lt (iSup_le fun n => (hb n).le) ENNReal.one_lt_top)

end ProbabilityTheory.BranchingProcess.Spine.StoppingLine
