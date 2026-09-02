This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Information-Sharing in Training and Inference: Collusion vs. Accuracy — Lean 4 formalization

This repository contains a Lean 4 / Mathlib formalization of the results of the manuscript
*Information-Sharing in Training and Inference: Collusion vs. Accuracy*.

## Building

```
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build
```

The toolchain and the Mathlib revision are pinned by `lean-toolchain` and
`lake-manifest.json`.

## Layout

All Lean sources live in `RequestProject/`. `RequestProject/Main.lean` imports every module
and serves as the entry point.

* **General model.** `GeneralSignaling.lean`, `BayesianGame.lean`, `CongestionGame.lean`,
  `ModelConnections.lean`.
* **Correlation model (Section 3).** `CorrelationModel.lean`, `KnownCorrelation.lean`,
  `KnownCorrelationAsymmetric.lean`, `UnknownCorrelation.lean`, `Theorem36.lean`.
* **Consumer effects (Section 4).** `Consumer.lean`, `OpportunitySeeking.lean`,
  `Theorem43.lean`, `Theorem43Selected.lean`, the `Theorem46*.lean` chain, and
  `Example47.lean`.
* **Extensions (Section 5).** `TwoHypotheses.lean`, `Theorem52.lean`.
* **Numerical witnesses.** `NumericalResults.lean` collects the manuscript's explicit
  parameter choices and the exact rational evaluations of the associated bounds.

`MANUSCRIPT_TO_LEAN.md` maps each numbered result of the manuscript to the Lean
declaration that formalizes it.

## Status

The development contains no `sorry` and no additional axioms beyond Lean's and Mathlib's
standard ones.
