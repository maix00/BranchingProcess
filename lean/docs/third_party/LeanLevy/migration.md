# LeanLevy module migration

This table records the upstream module for each mathematical-topic module in
the Lean project. Lean declaration namespaces are preserved during this path
migration; duplicate API cleanup is tracked separately from file ownership.

| Upstream module | Project module |
| --- | --- |
| `LeanLevy/Fourier/PositiveDefinite.lean` | `Analysis/Fourier/PositiveDefinite.lean` |
| `LeanLevy/Fourier/Bochner.lean` | `Analysis/Fourier/Bochner.lean` |
| `LeanLevy/Fourier/MeasureFourier.lean` | Removed after replacing the duplicate Fourier transform with Mathlib's `charFun`. |
| `LeanLevy/Probability/Characteristic.lean` | `MeasureTheory/Measure/CharacteristicFunction/ProbabilityMeasure.lean` (retains only the repository-specific positive-definiteness proof; the wrapper and duplicate basic lemmas were removed). |
| `LeanLevy/Probability/WeakConvergence.lean` | Removed after replacing its specialized real-line Lévy continuity theorem with Mathlib's `ProbabilityMeasure.tendsto_iff_tendsto_charFun` in `Mathlib.MeasureTheory.Measure.LevyConvergence`. |
| `LeanLevy/Probability/Poisson.lean` | `Probability/Distributions/Poisson/Basic.lean` |
| `LeanLevy/Levy/InfiniteDivisible.lean` | `Probability/Distributions/InfinitelyDivisible/Basic.lean` |
| `LeanLevy/Levy/LevyMeasure.lean` | `Probability/Distributions/InfinitelyDivisible/LevyMeasure.lean` |
| `LeanLevy/Levy/CompensatedIntegral.lean` | `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Integrand.lean` |
| `LeanLevy/Levy/LevyKhintchine.lean` | `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Defs.lean` |
| `LeanLevy/Levy/LevyKhintchineProof.lean` | `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Representation.lean` |
| `LeanLevy/Levy/LevyKhintchineUniqueness.lean` | `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Uniqueness.lean` |
| `LeanLevy/RandomMeasure/PoissonPointFamily.lean` | `Probability/RandomMeasure/Poisson/PointFamily.lean` |
| `LeanLevy/RandomMeasure/PoissonRandomMeasure.lean` | `Probability/RandomMeasure/Poisson/Basic.lean` |

The `LeanLevy.+` Lake source glob has been removed. `LeanLevy/` is not retained
as a compatibility import layer. Duplicate `characteristicFun`, `fourierTransform`, and
`iteratedConv` definitions were removed in favor of Mathlib's `charFun` and the project's
shared `Measure.convPower`.
