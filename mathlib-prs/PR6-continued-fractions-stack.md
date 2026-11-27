# PR 6: periodic continued fractions (a stack of seven)

**Status:** all seven branches are pushed; no PR is opened.

The stack proves, for the regular continued fraction `GenContFract.of v` of an element `v` of a linearly ordered floor field: Euler's theorem (eventually periodic implies quadratic irrational), Lagrange's theorem (the converse), and Galois's two theorems (purely periodic if and only if reduced; the conjugate has the reversed period). Mathlib has none of this, and neither does Tau Ceti.

Read [NOTES-continued-fractions-stack.md](NOTES-continued-fractions-stack.md) before opening anything.

## The stack

| # | Branch | Adds | Lines | Depends on |
|---|---|---|---|---|
| 6.1 | `cf-of-den-pos-of-injective` | two small lemmas the rest needs | +18 | nothing |
| 6.2 | `cf-complete-quotient` | the complete quotients `vₙ` of a continued fraction and their basic API | +199 | 6.1 |
| 6.3 | `cf-periodic` | the definitions `IsEventuallyPeriodic` and `IsPurelyPeriodic` | +151 | 6.2 |
| 6.4 | `cf-periodic-quadratic-irrational` | Euler's theorem: eventually periodic implies quadratic irrational | +138 | 6.3 |
| 6.5 | `cf-lagrange` | Lagrange's theorem and the "if and only if" | +253 | 6.4 |
| 6.6 | `cf-galois-purely-periodic` | Galois's theorem: purely periodic if and only if reduced | +223 | 6.5 |
| 6.7 | `cf-galois-reversed-period` | Galois's theorem on the reversed period | +72 | 6.6 |

## How to open a stack on mathlib

- Each branch contains the commits of the ones before it. A PR from a fork can only target `master`, so until the earlier PRs are merged, a later PR shows their changes too.
- Mathlib handles this with a line in the description: `- [ ] depends on: #NNNN`, one per PR it depends on. A bot then labels the PR `blocked-by-other-PR` and removes the label when the dependency merges.
- **Open 6.1 first, alone.** It is 18 lines and tests whether the maintainers want this material. Open 6.2 once 6.1 has had a first review, and so on. Opening all seven at once as a new contributor with three PRs already open is likely to be read as flooding.
- When an earlier PR changes in review, the later branches must be rebuilt on top of it. Ask me and I will redo the stack.
- After opening each PR, post a comment containing only the line `LLM-generated`.

## 6.1 `cf-of-den-pos-of-injective`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-of-den-pos-of-injective?expand=1

Title:

```text
feat(Algebra/ContinuedFractions): positivity of denominators and injectivity of `GenContFract.of`
```

Description (draft; put it in your own words where you can):

```text
Adds two lemmas about the continued fraction `GenContFract.of v` of an element of a linear ordered floor field.

- `GenContFract.of_den_pos : 0 < (of v).dens n` in Computation/Approximations.lean, right after `of_den_mono` (+5 lines).
- `GenContFract.of_injective : Function.Injective (of : K → GenContFract K)` in Computation/ApproximationCorollaries.lean, at the end of the section `Convergence` (+12 lines, +1 line in the module docstring).

Proof route: `of_den_pos` is `dens 0 = 1` (`zeroth_den_eq_one`) plus monotonicity (`of_den_mono` through `monotone_nat_of_le_succ`). `of_injective` uses `of_convergence_epsilon` twice with `ε = |v - w| / 2` and the triangle inequality.

Prior art: mathlib has `zero_le_of_den`, `of_den_mono` and the conditional `succ_nth_fib_le_of_nth_den`, but no unconditional strict positivity and no injectivity statement. Tau Ceti has neither (only `Real.convDen_pos`, about `Rat.den` of `Real.convergent`, a different object). No open mathlib PR touches these two files' new lemmas (#39212 edits other continued-fraction files).

Checked: both modules and their importers (TerminatesIffRat, NumberTheory.DiophantineApproximation.ContinuedFractions, and the new files of the stack) build with no warnings; `lake exe lint-style` passes; `#print axioms` gives propext, Classical.choice, Quot.sound.

Motivation to state in the description: both are used by the following PRs on periodic continued fractions (`of_den_pos` for the formula `v = (vₙ₊₁ Aₙ + Aₙ₋₁) / (vₙ₊₁ Bₙ + Bₙ₋₁)`, `of_injective` to pass from equal expansions to equal values).

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.2 `cf-complete-quotient`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-complete-quotient?expand=1

Title:

```text
feat(Algebra/ContinuedFractions): complete quotients of a continued fraction
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.1)

New file Mathlib/Algebra/ContinuedFractions/Computation/CompleteQuotient.lean (198 lines) and one import line in Mathlib.lean.

Definition: `GenContFract.completeQuotient v n := (fun x ↦ (Int.fract x)⁻¹)^[n] v`, the complete quotients `v₀ = v`, `vₙ₊₁ = (fract vₙ)⁻¹`, for `[DivisionRing K] [LinearOrder K] [FloorRing K]` (the assumptions of `GenContFract.of`). It is a total sequence: after an integer `vₙ` all later values are `0`.

API:
- recurrences `completeQuotient_zero` (simp), `completeQuotient_succ`, `completeQuotient_succ'`, `completeQuotient_add`, `floor_add_inv_completeQuotient_succ`;
- link with the expansion: `of_completeQuotient_s` (the expansion of `vₙ` is the `n`-th tail), `of_completeQuotient_s_get?`, `of_completeQuotient_terminatedAt_iff`, `of_completeQuotient_terminates_iff`, `of_terminatedAt_iff_fract_completeQuotient_eq_zero`, `get?_of_eq_some_of_not_terminatedAt` (the `n`-th coefficient is `⟨1, ⌊vₙ₊₁⌋⟩`), `IntFractPair.stream_eq_some_of_ne_none`;
- over a field: `eq_completeQuotient_mul_contsAux_div` (`v = (vₙ₊₁ Aₙ + Aₙ₋₁) / (vₙ₊₁ Bₙ + Bₙ₋₁)`), `one_lt_completeQuotient_succ`, `one_lt_completeQuotient`, `completeQuotient_mul_contsAux_b_add_pos`.

Proof route: everything reduces to existing mathlib lemmas (`of_s_tail`, `of_s_head`, `IntFractPair.succ_nth_stream_eq_none_iff`, `succ_nth_stream_eq_some_iff`, `compExactValue_correctness_of_stream_eq_some`, `Function.iterate_*`).

Design decisions: a total `K`-valued sequence instead of the `Option`-valued `IntFractPair.stream`; defined as an iterate so that `Function.iterate_*` and `Function.IsPeriodicPt` apply by definition; no Gauss map is defined.

Prior art: mathlib has no complete quotients (the stream stores the pairs `⟨⌊vₙ⌋, fract vₙ⟩`). `eq_completeQuotient_mul_contsAux_div` is `compExactValue_correctness_of_stream_eq_some` restated, not a new proof. Open PR #45950 defines the Gauss map `x ↦ fract x⁻¹` on ℝ in Mathlib/Dynamics/Ergodic/GaussMap.lean for measure theory; nothing here overlaps, and a bridge lemma can follow once it lands. Tau Ceti has no complete quotient declaration (the words appear only in docstrings of its Algebra/ContinuedFractions/Approximations.lean).

Checked: module builds with no warnings; `lake exe lint-style` passes; `#lint` on a non-module copy gives 0 errors in 17 declarations; axioms are the three standard ones.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.3 `cf-periodic`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-periodic?expand=1

Title:

```text
feat(Algebra/ContinuedFractions): eventually periodic and purely periodic continued fractions
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.2)

New file Mathlib/Algebra/ContinuedFractions/Periodic.lean (150 lines) and one import line in Mathlib.lean.

Definitions, for any `g : GenContFract α`:
- `GenContFract.IsEventuallyPeriodic g := ¬g.Terminates ∧ ∃ N p, 0 < p ∧ ∀ n ≥ N, g.s.get? (n + p) = g.s.get? n`;
- `GenContFract.IsPurelyPeriodic g := ∃ p, g.partDens.get? p = some g.h ∧ ∀ n, g.s.get? (n + (p + 1)) = g.s.get? n`.

Lemmas: `IsEventuallyPeriodic.not_terminates`, `IsPurelyPeriodic.not_terminates`, `IsPurelyPeriodic.isEventuallyPeriodic`; for `of v`: `of_isEventuallyPeriodic_iff_partDens` (periodicity of the partial denominators), `of_isEventuallyPeriodic_iff` (`¬Terminates ∧ ∃ N p, 0 < p ∧ completeQuotient v (N + p) = completeQuotient v N`), `of_isPurelyPeriodic_iff` (`¬Terminates ∧ ∃ p, 0 < p ∧ completeQuotient v p = v`).

Proof route: `Function.Periodic.nat_mul` for non-termination; `of_injective` (PR 0) plus the tail description `of_completeQuotient_s_get?` (PR 1) for the two characterizations.

Design decisions: non-termination is part of `IsEventuallyPeriodic` because the periodicity condition alone holds for every terminating expansion; `IsPurelyPeriodic` writes the period as `p + 1` (the head is the first term of the period) and compares the head with a partial denominator only, so it is meant for regular continued fractions (documented). Characterizations are stated with `completeQuotient`, which is by definition the orbit of `x ↦ (fract x)⁻¹`, so the second one is `v ∈ Function.periodicPts _` up to unfolding; the docstring says so.

Imports: `ApproximationCorollaries` is imported privately for `of_injective` (it publicly imports order topology); `Algebra.Ring.Periodic` for `Function.Periodic.nat_mul`.

Prior art: nothing on periodic continued fractions in mathlib, in open mathlib PRs (searched: periodic / Lagrange / complete quotient / quadratic irrational / continued fraction; only #39212, #45950, #43595, #46382 appear, none related), or in Tau Ceti.

Checked: module builds with no warnings; style linter passes; `#lint` on a non-module copy gives 0 errors in 8 declarations; both definitions unfold by `Iff.rfl` in a test file; standard axioms only.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.4 `cf-periodic-quadratic-irrational`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-periodic-quadratic-irrational?expand=1

Title:

```text
feat(NumberTheory/ContinuedFractions): eventually periodic continued fractions are quadratic irrationals
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.3)

New file Mathlib/NumberTheory/ContinuedFractions/QuadraticIrrational.lean (137 lines), creating the directory Mathlib/NumberTheory/ContinuedFractions/ (next to NumberTheory/DiophantineApproximation), and one import line in Mathlib.lean.

Main result (Euler's theorem): `GenContFract.IsEventuallyPeriodic.natDegree_minpoly_eq_two (h : (of v).IsEventuallyPeriodic) : (minpoly ℚ v).natDegree = 2`, for `v` in any `[Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]`.

Supporting public lemmas, for any field `F` with `Algebra F K`: `adjoin_completeQuotient : F⟮completeQuotient v n⟯ = F⟮v⟯`, `completeQuotient_mem_adjoin`, `natDegree_minpoly_completeQuotient`.

'Quadratic irrational' is expressed as `(minpoly ℚ v).natDegree = 2`: algebraic (else the minimal polynomial is 0), root of a rational quadratic, not rational (else degree 1). Over ℝ this is equivalent to `Irrational x ∧ ∃ q : ℚ[X], q.natDegree = 2 ∧ aeval x q = 0` (checked in a test file, not part of the PR). No new predicate is defined.

Proof route: if `vₙ₊₁ = v` then `v = (v Aₙ + Aₙ₋₁) / (v Bₙ + Bₙ₋₁)` with rational continuants (`exists_gcf_pair_rat_eq_of_nth_contsAux`) and `Bₙ > 0`, so `v` is a root of a rational polynomial of degree 2; it is not rational because its expansion does not terminate (`terminates_iff_rat`). In general `v_{N+p} = v_N`, so this applies to `v_N`, and `v_N` has the same degree as `v` because `ℚ⟮v_N⟯ = ℚ⟮v⟯`.

Private helpers: `isIntegral_of_adjoin_simple_eq (h : F⟮x⟯ = F⟮y⟯) : IsIntegral F x → IsIntegral F y` (a general fact absent from mathlib; could be moved to FieldTheory/IntermediateField/Adjoin/Basic.lean on request), `exists_natDegree_eq_two_and_aeval_eq_zero`, `natDegree_minpoly_eq_two_of_completeQuotient_eq`.

Prior art: none in mathlib or open PRs. Tau Ceti has no such theorem; it has `IntermediateField.adjoin_simple_inv : K⟮x⁻¹⟯ = K⟮x⟯`, which is deliberately NOT added here (the inverse step is proved inline with `inv_mem`), and it uses the same formulation `(minpoly ℚ ξ).natDegree = 2` in `badlyApproximable_of_natDegree_minpoly_eq_two`.

Reference: Hardy–Wright, Theorem 176 (`hardy2008introduction`, already in references.bib).

Checked: module builds with no warnings; style linter passes; `#lint` 0 errors (7 declarations on the non-module copy); standard axioms only.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.5 `cf-lagrange`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-lagrange?expand=1

Title:

```text
feat(NumberTheory/ContinuedFractions): quadratic irrationals have eventually periodic continued fractions
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.4)

New file Mathlib/NumberTheory/ContinuedFractions/Lagrange.lean (238 lines), one import line in Mathlib.lean, one entry `steinig1992` in docs/references.bib (14 lines).

Main results, for `v` in a linear ordered floor field:
- `GenContFract.of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two (h : (minpoly ℚ v).natDegree = 2) : (of v).IsEventuallyPeriodic` (Lagrange);
- `GenContFract.of_isEventuallyPeriodic_iff_natDegree_minpoly_eq_two : (of v).IsEventuallyPeriodic ↔ (minpoly ℚ v).natDegree = 2` (Euler–Lagrange).

Proof route: Steinig's proof (Arch. Math. 59 (1992), 21–23), which does not use the conjugate. Each complete quotient `vₙ` is a root of an integer quadratic `Aₙ X² + Bₙ X + Cₙ` with the same discriminant `D` (explicit step `(A, B, C) ↦ (A k² + B k + C, 2 A k + B, A)`, `k = ⌊vₙ⌋`). If `Aₙ Cₙ ≥ 0` and `Aₙ₊₁ Cₙ₊₁ ≥ 0` with `vₙ > 1` then `|Bₙ₊₁| < |Bₙ|`, so `Aₙ Cₙ < 0` for infinitely many `n`. For those `n`, `|Aₙ|, |Bₙ|, |Cₙ| ≤ D` and `vₙ` is the only positive root, so `vₙ` takes finitely many values; two complete quotients coincide; conclude with `of_isEventuallyPeriodic_iff`.

Nine private lemmas on bare integer triples `(A, B, C)` with mathlib's `discrim`; no new public definitions. The integer quadratic comes from `IsLocalization.integerNormalization` applied to `minpoly ℚ v`.

Prior art: none in mathlib or open PRs. Tau Ceti has no Lagrange theorem for continued fractions; it has reduction theory of binary quadratic forms (BinaryQuadraticForm/LagrangeReduction.lean, IndefiniteReduction/Cycles.lean: Gauss cycles of reduced indefinite forms) and 'Lagrange's best approximation property', which are different statements. The helpers here are private and do not duplicate that API.

References: Hardy–Wright Theorem 177 (existing key); Steinig (new key `steinig1992`; data confirmed against the Crossref record of DOI 10.1007/BF01199010).

Checked: module builds with no warnings; style linter passes; `#lint` 0 errors (11 declarations on the non-module copy); standard axioms only; test file with √3, (3 + √7)/5, the golden ratio, rationals and non-algebraic numbers compiles.

Size: 238 lines of Lean, slightly above the usual budget only when the bib entry is counted.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.6 `cf-galois-purely-periodic`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-galois-purely-periodic?expand=1

Title:

```text
feat(NumberTheory/ContinuedFractions): purely periodic continued fractions and reduced quadratic irrationals
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.5)

New file Mathlib/NumberTheory/ContinuedFractions/PurelyPeriodic.lean WITHOUT the section 'The reversed period' (211 lines; the exact cut is saved at D:/Projects/mathlib-prs/scratch/lagrange/verify/PurelyPeriodic_pr5.lean), one import line in Mathlib.lean, one entry `galois1829` in docs/references.bib (11 lines).

Main results, for a quadratic irrational `v` in a linear ordered floor field `K`:
- `GenContFract.of_isPurelyPeriodic_iff_of_isConjRoot (h : (minpoly ℚ v).natDegree = 2) (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) : (of v).IsPurelyPeriodic ↔ 1 < v ∧ w ∈ Set.Ioo (-1) 0`;
- `GenContFract.of_isPurelyPeriodic_iff_of_natDegree_minpoly_eq_two (h : (minpoly ℚ v).natDegree = 2) : (of v).IsPurelyPeriodic ↔ 1 < v ∧ ∃ w ∈ Set.Ioo (-1 : K) 0, IsConjRoot ℚ v w`.

'`w` is the conjugate of `v`' is `IsConjRoot ℚ v w` and `v ≠ w` (mathlib's `IsConjRoot`: same minimal polynomial). No 'reduced' predicate or conjugation map is defined.

Proof route: the conjugates `wₙ` of the complete quotients are the images of `vₙ` under the `ℚ`-algebra map `ℚ⟮v⟯ → K` sending `v` to `w` (`algHomAdjoinIntegralEquiv`); they satisfy `wₙ₊₁ = (wₙ - ⌊vₙ⌋)⁻¹`. Order arguments are done for an abstract sequence `c` with this recurrence. Reduced ⇒ purely periodic: `-1 < wₙ < 0` for all `n`, so `⌊vₙ⌋ = ⌊-1/wₙ₊₁⌋` and `vₙ` is determined by `vₙ₊₁`; Lagrange gives `v_{N+p} = v_N`; descend to `v_p = v`. Purely periodic ⇒ reduced: all `vₙ > 1`; if all `wₙ ≥ 0` then `w` and `v` have the same expansion, so `w = v` (`of_injective`); hence some `wₙ < 0`, then `-1 < wₘ < 0` for `m > n`, and `w = wₘ` for `m` a multiple of the period (`Function.IsPeriodicPt.const_mul`).

Eight private lemmas. Two of them do not use the order and carry `omit [IsStrictOrderedRing K] in`.

Prior art: none in mathlib, open PRs, or Tau Ceti.

Reference: Galois, Annales de Mathématiques Pures et Appliquées 19 (1828–1829), 294–301 (new key `galois1829`, Numdam AMPA_1828-1829__19__294_0).

Checked: the full module builds with no warnings and passes the style linter; the PR-5 cut compiles as a non-module copy with `#lint` 0 errors in 10 declarations; standard axioms only; test file (golden ratio, 1 + √2 purely periodic, √2 not) compiles.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 6.7 `cf-galois-reversed-period`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:cf-galois-reversed-period?expand=1

Title:

```text
feat(NumberTheory/ContinuedFractions): the reversed period of a purely periodic continued fraction
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.6)

Adds the section 'The reversed period' to Mathlib/NumberTheory/ContinuedFractions/PurelyPeriodic.lean (64 lines) and the corresponding docstring lines (8 lines): this restores the working-tree version of the file (283 lines).

Public results, for a quadratic irrational `v` with conjugate `w` (`IsConjRoot ℚ v w`, `v ≠ w`):
- `GenContFract.completeQuotient_neg_inv_of_isConjRoot`: `completeQuotient v p = v → completeQuotient (-w⁻¹) p = -w⁻¹`;
- `GenContFract.floor_completeQuotient_neg_inv_of_isConjRoot`: `completeQuotient v (j + k + 1) = v → ⌊completeQuotient (-w⁻¹) k⌋ = ⌊completeQuotient v j⌋` (the period of `-1/w` is the period of `v` reversed);
- `GenContFract.IsPurelyPeriodic.neg_inv_of_isConjRoot`: `(of v).IsPurelyPeriodic → (of (-w⁻¹)).IsPurelyPeriodic`.

Proof route: with `wₙ` the conjugates of the complete quotients and `-1 < wₙ < 0` (previous PR), `-1/wₙ₊₁ = ⌊vₙ⌋ + 1/(-1/wₙ)`, so `-1/wₙ` is the first complete quotient of `-1/wₙ₊₁`; iterate.

It is a follow-up to the same file because it uses that file's private lemmas (`floor_neg_inv_succ`, `mem_Ioo_of_mem_Ioo`, `exists_conj_completeQuotient`).

Prior art: none in mathlib, open PRs, or Tau Ceti. Reference: Galois' paper (key `galois1829`, added by the previous PR).

Checked: the full module builds with no warnings; style linter passes; `#lint` 0 errors in 16 declarations on the non-module copy; standard axioms only; tests (period 2 case, golden ratio) compile.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's paper on periodic continued fractions that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## What was checked

- All modules of the stack build together without warnings; the style linter and `#lint` pass; the main theorems use only the standard axioms.
- The cut-down `PurelyPeriodic.lean` of 6.6 was built and linted as a module on its own.
- Not done: building each branch separately, the full mathlib build, `lake exe mk_all --check`, `lake exe shake`. Mathlib CI runs all of these on each PR.

## Points the final check left open

- No branch was built on its own: only the whole stack, and the 6.6 version of `PurelyPeriodic.lean`. Each file imports only earlier ones, so the risk is low, and CI builds each PR.
- 6.5 has 238 lines of Lean (253 with the import line and the bibliography entry), at the edge of the usual PR size. It contains one terminal `nlinarith` with explicit hints (`Lagrange.lean`, line 182).
- The private `isIntegral_of_adjoin_simple_eq` in `QuadraticIrrational.lean` is a general field-theory fact. A reviewer may ask to move it to `FieldTheory/IntermediateField/Adjoin/Basic.lean`, the file PR 5 edits.
- The docstring of `Lagrange.lean` says the proof follows Steinig (Arch. Math. 59 (1992), 21-23). The bibliographic data was checked against Crossref, but the paper itself was not read; read it (three pages) before you defend that sentence.
- Galois's theorem cites only Galois's own paper (Annales de Gergonne 19 (1828-1829), 294-301). No textbook reference was verified.
- A reviewer may ask for `1 ≤ (of v).dens n` instead of `of_den_pos`, or for 6.1 to be split into two one-lemma PRs. Both are trivial changes.
- The two new entries of `docs/references.bib` were not run through `bibtool`.
