import Probability.Process.RandomWalk.FunctionalLimit.FiniteDimensional.IndependentBlocks

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional
open scoped Topology

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 0) increment =>
        AdditivePath.blockSum (AdditivePath.blockStart (fun _ => 0) j.val) 0 increment)
      (iidSequenceLaw ν) := by
  exact ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums
    ν (fun _ => 0) 0

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 0) increment =>
        AdditivePath.blockSum (j.val * 4) 4 increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_consecutiveBlockSums ν 0 4

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 0) increment =>
        AdditivePath.blockCoordinates
          (AdditivePath.blockStart (fun _ => 0) j.val) 0 increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockCoordinates
    ν (fun _ => 0) 0

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 2) increment =>
        AdditivePath.blockCoordinates
          (AdditivePath.blockStart (fun k => k + 1) j.val) (j.val + 1) increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockCoordinates
    ν (fun k => k + 1) 2

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 2) increment => AdditivePath.blockCoordinates (j.val * 3) 3 increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_consecutiveBlockCoordinates ν 2 3

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 1) increment =>
        AdditivePath.blockSum (AdditivePath.blockStart (fun _ => 2) j.val) 2 increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums
    ν (fun _ => 2) 1

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 2) increment =>
        AdditivePath.blockSum (AdditivePath.blockStart (fun k => k + 1) j.val)
          (j.val + 1) increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums
    ν (fun k => k + 1) 2

example (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun
      (fun (j : Fin 2) increment => AdditivePath.blockSum (j.val * 3) 3 increment)
      (iidSequenceLaw ν) :=
  ProbabilityTheory.RandomWalk.iIndepFun_consecutiveBlockSums ν 2 3

example {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blocks : ℕ) (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (ratio : Fin blocks → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds (ratio j)))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
          (length n j.val) increments / spatialScale n)
      atTop
      (fun z j => ratio j * z j)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => limit) := by
  simpa only [add_zero] using
    tendstoInDistribution_consecutiveBlockSums h blocks length spatialScale ratio
      (fun _ => 0) hblock hspatial hratio hcenter

example {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ} {c : ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blocks : ℕ) (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (ratio : Fin blocks → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds (ratio j)))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds c)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
          (length n j.val) increments / spatialScale n)
      atTop
      (fun z j => ratio j * z j + c)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => limit) := by
  exact tendstoInDistribution_consecutiveBlockSums h blocks length spatialScale ratio
    (fun _ => c) hblock hspatial hratio hcenter

#print axioms ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockCoordinates
#print axioms ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockEndpoints
