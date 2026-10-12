# Third-party sources and licenses

This project uses Mathlib at the revision in `lean/lake-manifest.json` and includes the following
pinned sources needed by the proof. Existing file headers and attribution are preserved.

| Source | Included files | Revision and records |
|---|---|---|
| [openai/math](https://github.com/openai/math) | `lean/upstream/` | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; [license](lean/upstream/LICENSE), unchanged sources |
| [qinz1yang/differential-geometry](https://github.com/qinz1yang/differential-geometry) | `lean/models_upstream/` | `bafefb7ce5ce7e40417641d67e6e95727b7bba1f`; [license](lean/models_upstream/LICENSE), [modifications](lean/models_upstream/MODIFICATIONS.md) |
| [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) | `lean/stage07/vendor/R4CoS/` | `7c3ae77166675436300aa85e2310f864a3cfcf2d`; [license](lean/stage07/vendor/R4CoS/LICENSE), [notice](lean/stage07/vendor/R4CoS/NOTICE), [renaming record](lean/stage07/VENDOR-CLASH.md) |

The classification-of-surfaces contribution included through Lean Pool originates from
[mccorvie/classification-of-surfaces](https://github.com/mccorvie/classification-of-surfaces).
The project's own license is [Apache-2.0](LICENSE). Lean, Mathlib and the external checking
tools are obtained separately; their repositories retain their respective notices.

## Review verification support

`comparator/LocalCompare.lean` adapts declaration equality and dependency traversal from
[Lean Comparator](https://github.com/leanprover/comparator), revision
`ca04cfc72b550331658ec314bf47685281bfd4bf`, Copyright (c) 2025 Lean FRO, LLC,
released under Apache-2.0. It is a local preflight, not the full Linux sandboxed tool.

The FC-style target uses the conventions of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), revision
`8b3ec608d55559e384ad359b3c83f1c2112df448`, released under Apache-2.0.
Reference metadata and `FormalConjecturesUtil.lean` are kept in the separate local preparation
workspace, outside this publication candidate. No complete FC checkout is vendored here.
