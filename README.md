# An attempt on the Yang-Mills mass gap: verified results and open obligations (Lean 4)

Version 1.0.0. DOI: 10.5281/zenodo.24095337

**This archive does not solve the Yang-Mills existence and mass gap problem and does not prove a
positive mass gap for any quantum Yang-Mills theory.** It is the checkable record of an attempt:
what was proved about the four-dimensional SU(2) Wilson lattice measure, what stayed open, and how
the automated search behind it drifted into reward hacking and was stopped on 2026-11-09.

## What is here

| Path | Content |
| --- | --- |
| `paper/paper_yang_mills_attempt.pdf` | The paper. Its first table lists every claimed result with its hypotheses. |
| `JesseMath/` | The whole Lean 4 corpus of the campaign, in three tiers (see below). |
| `tests/` | Negative controls: false shortcuts refuted on explicit models, and scope checks. |
| `engine-run/` | The solidSF research engine's unedited run on the campaign's audit documents (`run.json`, `report.md`; one local file path in `run.json` is shortened). |
| `clean_clone_lake_build.log` | Log of the clean-copy build of exactly these files (zero warnings). |
| `build_negative_control.log` | The same build rejecting an inserted false theorem and an inserted `sorry`. |
| `exhibits/` | The unapproved target statement and the halt record the paper refers to. |
| `MANIFEST.json` | SHA-256 of every Lean file, toolchain and Mathlib pins, source revision. |

## Rebuild

```bash
lake exe cache get
lake build --wfail JesseMath Controls
```

Every module ends with `#assert_zfc_axioms`, which fails the build if any declaration depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`.

## How to read the Lean: three tiers

This is the whole Lean corpus of the campaign, about 106,000 lines. A kernel check certifies each
stated implication. It does not certify that a statement means what its name suggests.

1. **Results we stand behind.** The theorems stated in the paper (its first table). They live in
   `LatticeYangMills`, `YangMillsWeakCoupling`, `YangMillsUniformHaarNeighbourhood`,
   `YangMillsContinuumCompactness`, `YangMillsOsterwalderSchraderInheritance`,
   `YangMillsWilsonPlaquetteTail`, `YangMillsWilsonSmallField`, `YangMillsForestSliceHessian`,
   `YangMillsWilsonLinkRadialPoincare`, `YangMillsPhysicalGap` and the control files in `tests/`.
2. **Other Wilson-measure modules.** Their header comments state their scope. We believe them
   sound and have not reviewed them line by line.
3. **Published as it is.** `YangMillsReconstructedGeneratorGap` (about 35,000 lines),
   `SussmanAlpogeBalaban` with the unrelated `JesseMath/Unified` and similar libraries it imports,
   and `FormalConjectures/DeepMindMillennium`. Some of this is real mathematics. It also contains
   the reward-hacking patterns the paper documents in Section 6: conclusions that enter as
   hypotheses, a "solution" structure whose mass gap is one of its own fields, theorems named after
   the worker that wrote them, and names borrowed from a third party. Read the hypotheses before
   trusting any statement here.

`FormalConjectures/DeepMindMillennium.lean` uses the name of Google DeepMind's `formal-conjectures`
project. solidSF has no affiliation with or endorsement from Google DeepMind. The published copy of
that file carries a notice at the top of its doc comment; that notice is the only edit made to any
source in this archive.

## What is not proved

Uniform multiscale control of the block-averaged measure, a unique continuum limit, Euclidean
covariance and reflection positivity of that limit, clustering, nontriviality, a positive decay rate
in physical time, and anything for groups other than SU(2). The paper states each as a numbered
Problem with what blocked it.

## Relation to earlier records

Zenodo record 10.5281/zenodo.22904674 (2026-09-22) claimed a proved mass gap. That claim was wrong
and is withdrawn; this record replaces it as our statement on the problem.

License: Apache-2.0.
