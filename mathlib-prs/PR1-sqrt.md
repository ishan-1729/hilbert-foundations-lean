# PR 1: `Real.sqrt` is analytic away from `0`

Open at: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:analyticAt-sqrt?expand=1

After opening, post a comment containing only the line `LLM-generated` to add the label. Topic labels (`t-analysis`) are added automatically from the files changed.

## Title

```text
feat(Analysis/SpecialFunctions/Sqrt): `Real.sqrt` is analytic away from `0`
```

## Description

```text
Add `Real.analyticAt_sqrt`: `√` is real analytic at every `x ≠ 0`, together with the `AnalyticWithinAt`, `AnalyticOnNhd` and `AnalyticOn` versions (the last two on `{0}ᶜ`), and the composition lemmas `AnalyticAt.sqrt`, `AnalyticWithinAt.sqrt`, `AnalyticOnNhd.sqrt` and `AnalyticOn.sqrt`, mirroring the existing `ContDiff*.sqrt` lemmas in the same file.

The proof is `ContDiffAt.analyticAt` applied to `contDiffAt_sqrt` at `n = ω`. `analyticAt_sqrt`, `AnalyticAt.sqrt` and `AnalyticOnNhd.sqrt` are tagged `@[fun_prop]` (`AnalyticWithinAt` and `AnalyticOn` are not `fun_prop` predicates).

---

The hypothesis is `x ≠ 0` rather than `0 < x`: for `x < 0`, `√` is locally constant, and the condition matches `contDiffAt_sqrt`. The shape follows `Real.analyticAt_arsinh` and `Real.analyticAt_log` / `AnalyticAt.log`.

AI use: I used Claude Code (Anthropic) to draft these lemmas and to compare them with the analogous `arsinh` and `log` API; I reviewed every line and can explain each choice. Checked locally with `lake build Mathlib.Analysis.SpecialFunctions.Sqrt`, `lake exe lint-style`, and `fun_prop` examples such as `AnalyticAt ℝ (fun y ↦ √(y ^ 2 + 1)) x`.
```
