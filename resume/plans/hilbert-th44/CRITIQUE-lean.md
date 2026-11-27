# Critique (lens: Lean feasibility) of `BLUEPRINT.md`, unit `th.44`

## Summary

The blueprint is not a plan: it prints all three new Lean files in full, says they were
type-checked, and keeps byte-identical copies in `ref/`. I checked those claims instead of the
individual steps.

1. **The printed code equals `ref/`.** I pulled the three `lean` code blocks of § 4.2–4.4 that start
   with `import` and compared them with the files in `ref/`: all three match byte for byte (220,
   123 and 163 lines). The longest line has 99 characters. None of the three files contains `sorry`,
   `admit`, `native_decide`, `axiom`, `unsafe` or `implemented_by`.
2. **The earlier check used the same code.** I rebuilt the concatenation of check (a) myself from
   `ref/`: imports of file 3 (without the file-2 import), then the bodies of files 1, 2 and 3. It
   differs from `.lake-local/scratch/th44b/CatA.lean` only in two blank lines and one extra
   `#print axioms` line that I added. Earlier result files: `CatA.out` says `[OK]` with axioms
   `[propext, Classical.choice, Quot.sound]`; `CatB.out` says `[OK]`.
3. **Independent recompile.** I compiled my own concatenation,
   `.lake-local/scratch/th44-critic-lean/MyCatA.lean`, with `leanc.py`. The result is in
   `MyCatA.out` in the same folder and is copied into the section "Recompile result" at the end of
   this file.
4. **Repository and `Hilbert17` statements match the current sources.** I re-read them:
   * `TotNonnegOver` (`ConstructionsAux9.lean:25`), `Theorem44` (`:54`)
   * `Theorem43For` (`ConstructionsAux10.lean:30`), `theorem44_of_theorem43For` (`:216`)
   * `QSOS` (`ConstructionsAux6.lean:237`), `sosIn_one` (`ConstructionsCloseAux5.lean:56`)
   * `eval₂_finSuccEquiv` (`Hilbert17/FinSuccEvaluation.lean:11`)
   * `exists_matching_signs_eval₂` (`Hilbert17/FiniteVariableTransfer.lean:25`)
   * `isSumSq_iff_nonneg_all_orders` (`Hilbert17/OrderingSeparation.lean:27`)

   `git status` shows a clean working tree. The 17:33 modification time of the `Hilbert17` sources
   (R2) is the time of the commit checkout, not an edit, so the stale-olean worry in R2 is
   theoretical.
5. **Mathlib names that I confirmed with `rg`** (the compile confirms the rest):
   * `AlgebraicIndependent.option_iff_transcendental` (`RingTheory/AlgebraicIndependent/Transcendental.lean:97`)
   * `Subfield.cardinalMk_closure_le_max`: a `lemma`, not a `theorem` (`SetTheory/Cardinal/Subfield.lean:73`)
   * `Algebraic.countable` (`Algebra/AlgebraicCard.lean:75`)
   * `Field.exists_primitive_element` (`FieldTheory/PrimitiveElement.lean:208`)
   * `IsLocalization.integerNormalization_spec` (`RingTheory/Localization/Integral.lean:53`)
   * `exists_isTranscendenceBasis_subset` (`RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:395`)
   * `IsRealClosed.nonneg_iff_isSquare` (`FieldTheory/IsRealClosed/Basic.lean:114`)
   * the scoped instances `Algebra` and `IsFractionRing` in `IntermediateField.algebraAdjoinAdjoin`
     (`FieldTheory/IntermediateField/Adjoin/Algebra.lean:39, 61`)
   * `AlgebraicIndependent.aevalEquivField`, named only in the warning of § 4.2:
     `RingTheory/AlgebraicIndependent/Adjoin.lean:41`. The § 5 table does not give its file.
6. **Import order and file sizes are fine.** The order is file 1 → file 2 → file 3. File 3 imports
   `ConstructionsClose`, which does not import anything new, so there is no cycle. The Tau Ceti
   module `TauCeti/FieldTheory/RealClosure/Basic` exists in `.lake/packages/TauCeti`, with oleans.
   `Hilbert17` is a `lean_lib` of the same workspace, so a module of `HilbertFoundations` can import
   it, as `TwoVariablesClose.lean` already does. The files have 220, 123 and 163 lines, which is
   realistic.
7. **No name clashes.** None of the 18 new names occurs as a whole word in `HilbertFoundations/`,
   `HilbertFoundations.lean`, `JordanPick/`, `Hilbert17/` or `scripts/`.

## Issues (most severe first)

1. **minor: the code was never compiled as three separate modules.** Check (a) and check (b) were
   concatenations. Two things leak across file boundaries in a concatenation and would not in the
   real files:
   * `set_option linter.unusedSectionVars false` (from file 1) also covers the file-3 part.
   * The real `--olean` build adds the module boundary.

   Neither can turn a success into an error. File 3 declares no `variable`, so at worst it gets a
   linter warning. There is no `private`, local notation or local attribute that could break.

   *Fix:* the compile order of § 4.0 (three `--olean` compiles) is already the right final check.
   The implementer must treat any warning there as a check to read, not as noise.
2. **minor: R4 overstates the import convention.** R4 says that only `Basic.lean` imports `Mathlib`
   directly, but `HilbertFoundations/CommentaryClose.lean` also does. So `import Mathlib` in file 1
   already has a precedent.

   *Fix:* keep `import Mathlib` as checked. Do not switch to `import HilbertFoundations.Basic`
   without a recompile.
3. **minor (documentation): the wiring list misses the axiom audit.** `scripts/AxiomsAudit.lean`
   imports the root module and audits every declaration in the `HilbertFoundations` namespace. It
   picks up the new file automatically once the root import of § 4.5 is added. This is worth one
   line in § 4.5, so that the implementer runs it after wiring. No change to the script itself is
   needed.
4. **minor (cosmetic): the § 5 table.** `Subfield.cardinalMk_closure_le_max` is a `lemma`, and
   `aevalEquivField` (cited in the warning) has no file entry. Neither affects the code.
5. **observation: fragile tactic steps.** R5 lists them correctly. They are the places to look at if
   a later mathlib bump breaks the build:
   * the `rfl` at the end of `evalAt_of_map_eq`
   * the `show` steps that unfold `AlgEquiv` to `RingHom` in `exists_poly_of_finite`
   * `simp only [..., ← evalAt_eq_eval₂]` after `rw [← Fin.cons_self_tail y]` in
     `nonempty_ringHom_real`

   The warning about `aevalEquivField` over `ℚ` (two `ℚ`-algebra structures on
   `FractionRing (MvPolynomial _ ℚ)`) is a genuine pitfall. The workaround, using only ring
   homomorphisms together with the scoped `IsFractionRing` instance, is the right design.

## Hardest steps

None is left open, and all of them compile. In order of difficulty:
1. building `K →+* ℝ` in Lemma 8(3);
2. clearing denominators of the minimal polynomial over `ℚ(t)` without a `ℚ`-algebra on the field
   of fractions;
3. density of algebraically independent points (Lemma 3).

The blueprint solves each of them with confirmed API.

## Recompile result

Output of `python .lake-local/leanc.py .lake-local/scratch/th44-critic-lean/MyCatA.lean`:

```
'HilbertFoundations.theorem44' depends on axioms: [propext, Classical.choice, Quot.sound]
'HilbertFoundations.theorem43For_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
[OK] .lake-local\scratch\th44-critic-lean\MyCatA.lean (953s)
```

No errors, and no warnings. The verification claim of the blueprint is confirmed independently.

**Verdict: sound.** The issues above are minor or documentation only.
