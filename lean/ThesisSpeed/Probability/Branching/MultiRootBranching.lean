import ThesisSpeed.Probability.Genealogy.MultiRoot
import ThesisSpeed.Probability.Branching.JointSubtrees

/-!
# Branching property for several initial ancestors

The address space is `Fin m × TreeNode`. Different initial ancestors have
different first coordinates. This file proves independence of all revealed
marks from all future marks, even when the future addresses have different
initial ancestors.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

@[instance_reducible] def multiCoordinateSpace {m : ℕ}
    (p : Fin m × TreeNode) : MeasurableSpace (MultiRootTree m) :=
  MeasurableSpace.comap (fun ω => ω p.1 p.2) inferInstance

@[instance_reducible] def multiPastSpace (m n : ℕ) :
    MeasurableSpace (MultiRootTree m) :=
  ⨆ p ∈ {p : Fin m × TreeNode | p.2.length < n}, multiCoordinateSpace p

@[instance_reducible] def multiFutureSpace (m n : ℕ) :
    MeasurableSpace (MultiRootTree m) :=
  ⨆ p ∈ {p : Fin m × TreeNode | n ≤ p.2.length}, multiCoordinateSpace p

theorem multiRootGenerationSpace_eq_past (m n : ℕ) :
    multiRootGenerationSpace m n = multiPastSpace m n := by
  apply le_antisymm
  · unfold multiRootGenerationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    have hle : multiCoordinateSpace (i, u) ≤ multiPastSpace m n := by
      unfold multiPastSpace
      exact le_iSup_of_le (i, u)
        (le_iSup_of_le (show (i, u) ∈
          {p : Fin m × TreeNode | p.2.length < n} from hu) le_rfl)
    apply hle
    exact ⟨t, ht, rfl⟩
  · unfold multiPastSpace
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact (multiRootMark_measurable m n p.1 p.2 hp).comap_le

theorem iid_multi_coordinates (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (m : ℕ) :
    iIndep multiCoordinateSpace (iidMultiRootLaw μ m) := by
  have h : iIndepFun
      (fun (p : Fin m × TreeNode) (ω : MultiRootTree m) =>
        ω p.1 p.2) (iidMultiRootLaw μ m) := by
    unfold iidMultiRootLaw iidMarkedTreeLaw
    simpa using (iIndepFun_uncurry_infinitePi'
      (μ := fun (_ : Fin m) (_ : TreeNode) => μ)
      (X := fun (_ : Fin m) (_ : TreeNode) => id)
      (fun _ _ => measurable_id))
  exact h.iIndep

/-- The joint past of every initial ancestor is independent of the joint
future of every initial ancestor. -/
theorem multiRoot_past_future_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    (m n : ℕ) :
    Indep (multiRootFiltration m n) (multiFutureSpace m n)
      (iidMultiRootLaw μ m) := by
  have hle : ∀ p : Fin m × TreeNode,
      multiCoordinateSpace p ≤
        (inferInstance : MeasurableSpace (MultiRootTree m)) := by
    intro p
    have hmeas : Measurable (fun ω : MultiRootTree m => ω p.1 p.2) :=
      (measurable_pi_apply p.2 :
        Measurable (fun ω : MarkedTree OffspringMark => ω p.2)).comp
          (measurable_pi_apply p.1 :
            Measurable (fun ω : MultiRootTree m => ω p.1))
    exact hmeas.comap_le
  have hdisj : Disjoint
      {p : Fin m × TreeNode | p.2.length < n}
      {p : Fin m × TreeNode | n ≤ p.2.length} := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    change p.2.length < n at hp
    change n ≤ p.2.length at hq
    exact (not_lt_of_ge hq) hp
  rw [show multiRootFiltration m n = multiRootGenerationSpace m n from rfl,
    multiRootGenerationSpace_eq_past]
  exact indep_iSup_of_disjoint hle (iid_multi_coordinates μ m) hdisj

/-- A finite vector of genealogical roots may belong to different initial
ancestors. -/
def multiRootSubtreeVector {m k : ℕ}
    (roots : Fin k → Fin m × TreeNode) (ω : MultiRootTree m) :
    Fin k → MarkedTree OffspringMark :=
  fun j v => ω (roots j).1 ((roots j).2 ++ v)

theorem multiRoot_rootedAddresses_injective {m k n : ℕ}
    (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    Function.Injective
      (fun p : Fin k × TreeNode =>
        (((roots p.1).1, (roots p.1).2 ++ p.2) : Fin m × TreeNode)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  change ((roots i).1, (roots i).2 ++ a) =
    ((roots j).1, (roots j).2 ++ b) at h
  have hrootIndex : (roots i).1 = (roots j).1 :=
    (Prod.mk.inj h).1
  have hpath : (roots i).2 ++ a = (roots j).2 ++ b :=
    (Prod.mk.inj h).2
  have hp := congrArg (List.take n) hpath
  have hrootPath : (roots i).2 = (roots j).2 := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj (Prod.ext hrootIndex hrootPath)
  subst j
  have hab : a = b := List.append_cancel_left hpath
  exact Prod.ext rfl hab

/-- The descendants of distinct labelled roots at one generation have the
joint law of independent marked trees, even when their initial ancestors
differ. -/
theorem fixed_multiRootSubtreeVector_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    (iidMultiRootLaw μ m).map (multiRootSubtreeVector roots) =
      Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin m × TreeNode => μ)
    (f := fun p : Fin k × TreeNode =>
      ((roots p.1).1, (roots p.1).2 ++ p.2))
    (multiRoot_rootedAddresses_injective roots hlen hinj)
  have hcurrySource := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin m) (_ : TreeNode) => μ)
  have hcurryTarget := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin k) (_ : TreeNode) => μ)
  change (Measure.infinitePi
    (fun _ : Fin m => Measure.infinitePi (fun _ : TreeNode => μ))).map
    (fun ω j v => ω (roots j).1 ((roots j).2 ++ v)) =
      Measure.infinitePi
        (fun _ : Fin k => Measure.infinitePi (fun _ : TreeNode => μ))
  rw [← hcurrySource, ← hcurryTarget, ← hflat]
  rw [Measure.map_map, Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (Fin k) TreeNode OffspringMark).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply
      ((roots p.1).1, (roots p.1).2 ++ p.2)
  · apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply ((roots j).2 ++ v)).comp
      (measurable_pi_apply (roots j).1)
  · exact (MeasurableEquiv.curry (Fin m) TreeNode OffspringMark).measurable

theorem multiRootSubtreeVector_measurable {m k : ℕ}
    (roots : Fin k → Fin m × TreeNode) :
    Measurable (multiRootSubtreeVector roots) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply ((roots j).2 ++ v)).comp
    (measurable_pi_apply (roots j).1)

theorem multiRootSubtreeVector_future_measurable {m k n : ℕ}
    (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n) :
    Measurable[multiFutureSpace m n]
      (multiRootSubtreeVector roots) := by
  apply (@measurable_pi_iff (MultiRootTree m) (Fin k)
    (fun _ => MarkedTree OffspringMark) (multiFutureSpace m n)
    (fun _ => inferInstance) (multiRootSubtreeVector roots)).2
  intro j
  apply (@measurable_pi_iff (MultiRootTree m) TreeNode
    (fun _ => OffspringMark) (multiFutureSpace m n)
    (fun _ => inferInstance)
    (fun ω v => multiRootSubtreeVector roots ω j v)).2
  intro v
  let p : Fin m × TreeNode :=
    ((roots j).1, (roots j).2 ++ v)
  have hp : n ≤ p.2.length := by
    simp [p, hlen j]
  have hle : multiCoordinateSpace p ≤ multiFutureSpace m n := by
    unfold multiFutureSpace
    exact le_iSup_of_le p
      (le_iSup_of_le
        (show p ∈ {q : Fin m × TreeNode | n ≤ q.2.length} from hp) le_rfl)
  have hcoord : Measurable[multiCoordinateSpace p]
      (fun ω : MultiRootTree m => ω p.1 p.2) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem fixed_multiRootSubtreeVector_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n) :
    Indep (multiRootFiltration m n)
      (MeasurableSpace.comap (multiRootSubtreeVector roots) inferInstance)
      (iidMultiRootLaw μ m) :=
  indep_of_indep_of_le_right
    (multiRoot_past_future_independent μ m n)
    (multiRootSubtreeVector_future_measurable roots hlen).comap_le

/-- Deterministic-time joint branching for several initial ancestors. -/
theorem fixed_multiRootSubtreeVector_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots)
    (A : Set (MultiRootTree m))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[multiRootFiltration m n] A)
    (hB : MeasurableSet B) :
    iidMultiRootLaw μ m (A ∩ multiRootSubtreeVector roots ⁻¹' B) =
      iidMultiRootLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  have hB' : MeasurableSet[MeasurableSpace.comap
      (multiRootSubtreeVector roots) inferInstance]
      (multiRootSubtreeVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_multiRootSubtreeVector_independent μ roots hlen).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (multiRootSubtreeVector_measurable roots) hB,
    fixed_multiRootSubtreeVector_law μ roots hlen hinj] at h
  exact h

end ThesisSpeed
