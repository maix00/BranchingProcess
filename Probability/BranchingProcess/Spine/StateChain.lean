/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Family.Marginals
public import Probability.Process.Markov.DoobTransform
public import Probability.Kernel.DoobTransform.Trajectory

/-!
# The state chain associated with the spine transition

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `eligibleStateKernel Q hh` is the generic Doob transform of the mean
  offspring kernel, restricted to `E = {s | 0 < h(s) < ∞}`.
* `eligibleStateKernel_isMarkovKernel`: the offspring harmonicity
  `E_s[∑ᵢ h(ξᵢ)] = h(s)` on `E` makes this kernel Markov.
* `eligibleStateKernel_map`: forgetting the eligible-state subtype gives
  exactly the selected-child marginal `spineChildKernel Q h`.
* `eligibleStateKernel_isMarkovChain`: its native trajectory is a Markov
  chain with transitions `(eligibleStateKernel Q hh)^(n-m)`.
* `partialTraj_spineChildKernel`: when `h` is finite and positive everywhere,
  the finite state-chain law has density `h(x_b)/h(x_a)` relative to the
  finite histories of the mean offspring kernel.

These are direct applications of the independent Doob-transform API.
They concern the state chain associated with the spine transition; they do
not assert identification with the ray extracted from a biased random tree.
The latter requires the tree's conditional reproduction laws. Compare
Zhan Shi, *Branching Random Walks*, LNM 2151 (2015), Chapter 4, §4.4,
Theorem 4.4(ii) and (4.8), DOI 10.1007/978-3-319-25372-5.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Finset
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]

/-- The spine transition on finite positive-weight states uses the generic Doob kernel. -/
noncomputable def eligibleStateKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) :
    Kernel {s // h s ≠ 0 ∧ h s ≠ ∞} {s // h s ≠ 0 ∧ h s ≠ ∞} :=
  Kernel.doobTransformOnPositive (meanChildKernel Q) hh

omit [MeasurableSpace ι] in
/-- Mean-harmonic offspring weights normalize the eligible spine transition. -/
theorem eligibleStateKernel_isMarkovKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    IsMarkovKernel (eligibleStateKernel Q hh) := by
  apply Kernel.doobTransformOnPositive_isMarkovKernel
  intro s hs ht
  exact (lintegral_meanChildKernel Q hh s).trans (harmonic s hs ht)

/-- The abstract chain's transition is the concrete joint bias's selected-child marginal. -/
theorem eligibleStateKernel_map [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (eligibleStateKernel Q hh s).map Subtype.val = spineChildKernel Q h s.1 := by
  rw [spineChildKernel_eq_doobTransform Q hh]
  exact Kernel.doobTransformOnPositive_map _ hh
    (fun s hs ht => (lintegral_meanChildKernel Q hh s).trans (harmonic s hs ht)) s

omit [MeasurableSpace ι] in
/-- The associated state process is the generic homogeneous Markov realization. -/
theorem eligibleStateKernel_isMarkovChain (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    letI := eligibleStateKernel_isMarkovKernel Q hh harmonic
    IsMarkovChain (fun n (w : ℕ → {s // h s ≠ 0 ∧ h s ≠ ∞}) => w n)
      Filtration.piLE
      (Kernel.traj (X := fun _ => {s // h s ≠ 0 ∧ h s ≠ ∞})
        (Kernel.historyKernel (eligibleStateKernel Q hh)) 0 (fun _ => s))
      (eligibleStateKernel Q hh) := by
  exact Kernel.doobTransformOnPositive_isMarkovChain _ hh
    (fun s hs ht => (lintegral_meanChildKernel Q hh s).trans (harmonic s hs ht)) s

/-- The finite spine-state path density is inherited from the general Doob identity. -/
theorem partialTraj_spineChildKernel [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ s, h s ≠ 0) (htop : ∀ s, h s ≠ ∞)
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S) :
    Kernel.partialTraj (X := fun _ => S) (Kernel.historyKernel (spineChildKernel Q h)) a b x =
      (Kernel.partialTraj (X := fun _ => S)
        (Kernel.historyKernel (meanChildKernel Q)) a b x).withDensity
        (fun y => h (y ⟨b, by simp⟩) / h (x ⟨a, by simp⟩)) := by
  rw [spineChildKernel_eq_doobTransform Q hh]
  exact Kernel.partialTraj_doobTransform _ hh hzero htop hab x

end ProbabilityTheory.BranchingProcess.Spine

end
