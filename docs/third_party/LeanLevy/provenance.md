# LeanLevy source provenance

The retained modules listed in `migration.md` were adapted from [`slink/LeanLevy`](https://github.com/slink/LeanLevy),
upstream revision `7e73fd9b23ad52956ec2756a815889a783131ce4`. The upstream
license is MIT; its complete text is preserved in [LICENSE](LICENSE).

The original modules were copied into this Lean project and adapted to its
pinned Mathlib API. The following changes were already recorded when the
source was organized by mathematical topic:

- Poisson point-family and random-measure files were adapted to
  `Measurable.of_eval`, probability-map instances, and
  `Finset.prod_le_one₀`.
- A general sample-measurability theorem for Poisson random-measure integrals
  was added.
- Process-specific material was removed from the infinite-divisibility file;
  the Lévy–Khintchine proof no longer depends on a process-specific
  `CharacteristicExponent` module.
- General characteristic-function continuity material was moved into the
  characteristic-function layer.
- The continuous-log uniqueness lemma was made public for downstream stable
  law arguments.
- Additional compatibility changes were made for the Mathlib revision pinned
  in `lean/lakefile.toml`.

Each retained migrated Lean file keeps the upstream copyright and author
attribution, points to the preserved MIT license, and identifies the source
revision. Lean declaration namespaces are preserved where declarations remain.
During API consolidation, duplicate characteristic-function and Fourier
transform wrappers were removed in favor of Mathlib's `charFun`; duplicate
convolution powers were replaced with the project's shared `Measure.convPower`.
The specialized one-dimensional weak-convergence development was removed after
its statements were found in Mathlib's `MeasureTheory.Measure.LevyConvergence`.
