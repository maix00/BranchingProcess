# Vendored LeanLevy measure layer

Source: https://github.com/slink/LeanLevy at commit `7e73fd9b23ad52956ec2756a815889a783131ce4` (MIT; see LICENSE).
Only the transitive measure/Fourier modules for the Lévy–Khintchine representation and uniqueness are included.
The `InfiniteDivisible` process-specific section was removed; `LevyKhintchineProof` no longer imports process-specific `CharacteristicExponent`. The generic continuity lemma for characteristic functions was moved into `Probability/Characteristic`. These changes avoid conflicting process definitions and adapt to this repository's pinned mathlib. Further version compatibility edits are in the vendored files.
