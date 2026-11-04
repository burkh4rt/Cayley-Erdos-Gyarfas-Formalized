# Odd-ordered Cayley graphs satisfy Erdős–Gyárfás

A Lean 4 formalization of Michael C. Burkhart's [arXiv:2611.05060v1](https://arxiv.org/abs/2611.05060v1). For a finite group of odd order, every undirected Cayley graph of degree at least three contains a simple cycle of length four, eight, sixteen, or a higher power of two. The paper proves the same conclusion for finite nilpotent groups. The formalization uses the namespace `CayleyErdősGyárfás`.

## Reviewed statements

[Challenge.lean](Challenge.lean) is the independent statement of record. It gives all standing hypotheses and defines a symmetric figure-eight in terms of two Mathlib cycles. Read it alongside §1 of the preprint. [REVIEW.md](REVIEW.md) maps each declaration to the paper and explains how the Lean proofs in §§2–3 compare with its arguments.

| Source | Claim in the Challenge |
| --- | --- |
| Theorem 1.1 | A Cayley graph of an odd-order group with at least three generators in its symmetric generating set contains a power-of-two-length cycle. |
| Paragraph following Theorem 1.1 | For a noncyclic odd-order group the graph contains two translated power-of-two-length cycles meeting at exactly one vertex. |
| Lemma 1.2 | A symmetric figure-eight in a quotient by an abelian normal subgroup lifts to one upstairs when the group has odd order. |
| Lemma 1.3 | A power-of-two cycle in a quotient by a normal 2-subgroup yields a power-of-two cycle upstairs. |
| Corollary 1.4 | A Cayley graph of a finite nilpotent group with at least three generators in its symmetric generating set contains a power-of-two cycle. |

[Solution.lean](Solution.lean) and its public imports supply the five proofs. The five `sorry` terms in the independent Challenge mark the statements that Comparator must verify. The figure-eight predicate has an explicit body on both sides. It is a dependency of compared theorems, so Comparator checks that its meaning agrees across the two modules.

The proof of the odd-order theorem uses Yawara Ishida's formal Feit–Thompson theorem and Singer-field construction. The [vendored source and provenance](vendor/odd-order/README.md) include the pinned upstream commit, compatibility patch and per-file checksums. The Challenge imports only Mathlib. Project authorship, licensing, AI use and review status are recorded in [formalization.yaml](formalization.yaml).

## Reproduce the checks

From the repository root, with the toolchain specified in `lean-toolchain` installed, run

```sh
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
python3 scripts/check-proof-status.py
```

The Linux CI workflow also runs the sandboxed three-kernel comparison. To reproduce it on Linux with Bubblewrap available, run

```sh
./scripts/verify-comparator.sh
```

The [local verification record](VERIFICATION.md) identifies the checks run on this preparation.

