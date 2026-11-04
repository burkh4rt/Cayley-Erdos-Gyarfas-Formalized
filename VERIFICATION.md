# Local verification

## Inputs

The reference text was extracted from the public [arXiv v1 source archive](https://arxiv.org/src/2611.05060v1). Its mathematical text from the introduction through the end of the paper matches the author's local arXiv manuscript.

| Input | Revision or SHA-256 |
| --- | --- |
| Lean | `v4.35.0-rc2` at `11acb17ec6b07a8f9e9173e6845197929540936b` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Challenge.lean | `103ee7afebd075772203581f09ab4da301acd2418c06178cb3deaa576bfd47b6` |
| Solution.lean | `24c07bb95a1f1386592a2498466c0285778d53d12c221df15b38f85359dbca86` |
| comparator.json | `d5373c8f18d22caa9af65cadbe67c48733b994fc456abb91e152a086e48f0a8c` |

## Source and metadata checks

* The source scanner passed for all 735 Lean files. The longest file has 1,498 lines. The independent Challenge has 109 lines, 4,886 bytes, five Mathlib imports and five intentional theorem holes.
* All nine Git dependencies matched the exact revisions in the project manifest. The Lean version matches Mathlib's toolchain file.
* The vendored dependency was reconstructed from upstream commit `7a412eae81e9510a684fd8c180cf1fbd47b8d00d` and the recorded patch. All 715 reconstructed source/license files matched both the manifest and the files included here.
* The metadata passed the starter's validator and the upstream formalization.yaml v0.4 JSON Schema at commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. Its result and alignment lists match all five theorem names in the Comparator configuration.

## Proof checks

The default `lake build` completed successfully on macOS arm64 (4,512 jobs). The additional `lake build OddOrder` completed successfully. The dependency build emitted deprecation warnings in the upstream port.

`python3 scripts/check-proof-status.py` inspected each of the five exported theorem declarations. Each depends on exactly `propext`, `Classical.choice` and `Quot.sound`.

The local Comparator run used a temporary copy of the submission configuration. Its only addition was the toolchain's bundled `nanoda_bin` and `con-ron` executables under `external_kernels`. The five theorem names and permitted axioms were unchanged. The figure-eight predicate is a fully specified dependency of the theorem statements. Leaving it out of `definition_names` makes Comparator check its body. On macOS the invocation was

```sh
lake comparator --inadvisably-no-sandbox --config /path/to/local-comparator.json
```

Comparator accepted the Challenge/Solution comparison and returned exit status 0. Con-ron verified 91,375 declarations, NanoDa accepted the Solution, and Lean's default kernel accepted the Solution. Comparator's final verdict was `Your solution is okay!`

This run used the native macOS toolchain without Bubblewrap. The repository's Linux workflow runs [the sandboxed command](scripts/verify-comparator.sh) on push. Linux sandbox verification and the author's personal review of the Challenge are pending for this snapshot.
