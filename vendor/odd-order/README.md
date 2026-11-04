# Odd-order proof dependency

This directory vendors the actual source import closure of Feit–Thompson
and the Singer-field construction used by the Cayley formalization.
It is derived from [Yawara Ishida's odd-order development](https://github.com/yawara/odd-order)
at commit `7a412eae81e9510a684fd8c180cf1fbd47b8d00d`.
Original Apache-2.0 copyright notices and [LICENSE](LICENSE) are retained.

The port targets this repository's pinned Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. It adds module headers and public
visibility, updates the explicit-normality API, adjusts changed elaboration
and tactic calls, and disambiguates several local helper names. The small
`CompatV435` shim is proved from Mathlib. No mathematical hypothesis is
weakened and no axiom or admitted proof is added.

`port.patch` records the complete source differences from the pinned
upstream revision. `source-manifest.json` records the original and final
SHA-256 for each included file, together with the patch checksum.
Unrelated upstream files, including its large axiom-audit aggregate, are
not vendored. Each included Lean source uses the module system and is below
Palomar's 10,000-line limit.

To reconstruct and verify the exact vendored Lean files from an existing
upstream Git clone, run from the project root:

```sh
python3 scripts/reproduce-odd-order.py --upstream /path/to/odd-order \
  --output /tmp/reconstructed-odd-order
```

The command reads the pinned committed objects and leaves the clone unchanged.
The output directory must not already exist. Ordinary `lake build` compiles
the vendored source directly; it does not use proof artifacts from another
project or require a separately published compatibility fork.
