# Vendored LeanLevy measure layer

Source: https://github.com/slink/LeanLevy at commit `7e73fd9b23ad52956ec2756a815889a783131ce4` (MIT; see LICENSE).
The transitive measure/Fourier modules for the Lévy–Khintchine representation and uniqueness, plus the Poisson point-family and Poisson random-measure construction, are included. The Poisson sources were adapted to the pinned Mathlib API (`Measurable.of_eval`, automatic probability-map instances, and `Finset.prod_le_one₀`). A general sample-measurability theorem for Poisson random-measure integrals was added.
The `InfiniteDivisible` process-specific section was removed; `LevyKhintchineProof` no longer imports process-specific `CharacteristicExponent`. The generic continuity lemma for characteristic functions was moved into `Probability/Characteristic`. These changes avoid conflicting process definitions and adapt to this repository's pinned mathlib. Further version compatibility edits are in the vendored files.
The continuous-log uniqueness lemma in `LevyKhintchineUniqueness` is public so downstream stable-law arguments can reuse its proof.
