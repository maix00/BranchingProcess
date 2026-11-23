/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Basic
public import Probability.BranchingProcess.State.Kernel
public import Probability.Kernel.Sum
public import Combinatorics.BranchingWalk.Step.DistinguishedChild

/-!
# The canonical distinguished tree for a locally normalized offspring bias

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.LocalBias`:

* `reproductionKernel` uses the original offspring kernel for normal parents,
  and `Q(s,dξ) r(s,ξ,i)` for distinguished parents in the eligible domain.
* `reproductionKernel_normal`, `reproductionKernel_distinguished` give its
  two transition rules; `reproductionKernel_isMarkovKernel` normalizes it.
* `treeKernel` is the existing canonical state tree for that reproduction
  kernel; `treeKernel.isMarkovKernel` and `treeKernel_root` give its law and root.

This is the local-density generalization of the normal/special construction
in Zhan Shi, *Branching Random Walks* (2015), §4.4 after (4.8),
DOI 10.1007/978-3-319-25372-5. It reuses `State.treeKernel`, rather than
introducing another stochastic-process definition.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- Normal reproduction and the locally biased distinguished family/index. -/
noncomputable def reproductionKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) : Kernel (S ⊕ B.domain) (Step ι (S ⊕ B.domain)) :=
  Kernel.sumElim
    (Q.map (Step.map Sum.inl))
    (((familyChildKernel Q B).comap Subtype.val measurable_subtype_coe).map
      (fun p => Step.distinguishChild B.domain.Mem p.1 p.2))

omit [MeasurableSingletonClass ι] in
@[simp] theorem reproductionKernel_normal (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) (s : S) :
    reproductionKernel Q B (Sum.inl s) = (Q s).map (Step.map Sum.inl) := by
  rw [reproductionKernel, Kernel.sumElim_inl, Kernel.map_apply _ (Step.map_measurable measurable_inl)]

@[simp] theorem reproductionKernel_distinguished
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (B : LocalBias S ι) (hD : MeasurableSet B.domain) (s : B.domain) :
    reproductionKernel Q B (Sum.inr s) = (familyChildKernel Q B s).map
      (fun p => Step.distinguishChild B.domain.Mem p.1 p.2) := by
  rw [reproductionKernel, Kernel.sumElim_inr]
  have hm : Measurable (fun p : Step ι S × ι =>
      Step.distinguishChild B.domain.Mem p.1 p.2) :=
    Step.distinguishChild_measurable hD
  exact (Kernel.map_apply
    ((familyChildKernel Q B).comap (Subtype.val : B.domain → S) measurable_subtype_coe)
    hm s).trans (congrArg (Measure.map _)
      (Kernel.comap_apply (familyChildKernel Q B) measurable_subtype_coe s))

theorem reproductionKernel_isMarkovKernel
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) :
    IsMarkovKernel (reproductionKernel Q B) := by
  constructor
  intro s
  cases s with
  | inl s => rw [reproductionKernel_normal]; infer_instance
  | inr s =>
    rw [reproductionKernel_distinguished Q B hB.measurableSet_domain]
    let := familyChildKernel_isProbabilityMeasure Q B hB s.1 s.2
    infer_instance

/-- Entire distinguished tree on the native state-tree probability law. -/
noncomputable def treeKernel (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) :
    Kernel (Option (S ⊕ B.domain)) (List ι → Option (S ⊕ B.domain)) := by
  let := reproductionKernel_isMarkovKernel Q B hB
  exact State.treeKernel (reproductionKernel Q B)

instance treeKernel.isMarkovKernel (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) : IsMarkovKernel (treeKernel Q B hB) := by
  let := reproductionKernel_isMarkovKernel Q B hB
  exact State.treeKernel.isMarkovKernel _

theorem treeKernel_root (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) (s : Option (S ⊕ B.domain)) :
    (treeKernel Q B hB s).map (fun t => t []) = Measure.dirac s := by
  let := reproductionKernel_isMarkovKernel Q B hB
  exact State.treeKernel_root _ s

end ProbabilityTheory.BranchingProcess.Spine.LocalBias
