# Critique (Lean feasibility lens) of BLUEPRINT.md, unit `nombres.reciproque`

## Verdict: sound (small fixable points only)

The blueprint is unusually concrete: it does not just plan the proof, it ships the code
(Appendix 8 = `reference/*.lean`), and that code was type-checked as one scratch file.
I checked this claim myself and did not take it on trust.

### What I verified

1. **The compile evidence is consistent.**
   * `.lake-local/scratch/reciproque/RAll.out` holds the first run (FAIL, 2060 s). Its errors are
     exactly the `diag_mem` placeholder errors at l. 436, plus three unused-section-variable
     warnings.
   * `RAll.lean` was modified at 19:08:37, after that output was written (19:08:16).
   * `RAll2.out` (19:13:16) says `[OK] ... (152s)` with no other output. So there were no warnings,
     in particular no `declaration uses 'sorry'`.
   * The current `RAll.lean` has the fix (`droite_est _ _ _ _ u.1.ne_zero u.2.ne_zero`, l. 439) and
     the three `omit ... in` lines.
2. **The reference files are the compiled code.** I diffed the three `reference/*.lean` files
   (imports and module docstrings removed) against `RAll.lean`. They are identical apart from blank
   lines and one extra `open Polynomial` before the third namespace, which is harmless. The three
   ```lean blocks of Appendix 8 are byte-identical to the reference files.
3. **No forbidden constructs.** None of `sorry`, `admit`, `native_decide`, `axiom`,
   `implemented_by`, `unsafe` or `set_option` appears in RAll.lean or in the reference files.
4. **The repository state matches what was compiled against.**
   * `git status` is clean.
   * The `TheorieNombres`, `EquationsPrimitives`, `Radicaux` and `Basic` .oleans are newer than
     their sources.
   * No existing declaration or namespace clashes with the new names (`Realisation`, `Couronne`,
     `AGL`, `reciproque_corrigee*`, `card_dvd_of_reciproque`, `not_reciproqueGalois`).
   * `scripts/AxiomsAudit.lean` scans the whole `GaloisOeuvres` namespace, so it needs no change.
5. **The split-file risk (RISKS 1) was tested.**
   * Aux2 was compiled alone with its own import (`GaloisOeuvres.Basic`).
   * Aux1 was compiled alone with its own import (`GaloisOeuvres.Radicaux`).
   * Scratch copies: `.lake-local/scratch/reciproque-lean-critic/A1.lean` and `A2.lean`.
   * Results are in the "Standalone compile" section at the end of this file.
   * `Basic.lean` does `import Mathlib`, so both files see all of mathlib.
   * The only global instances in the dropped imports are `TheorieNombres.imag_*`,
     `fact_prime_7/19`, `fact_F7/G7` and `EquationsPrimitives.faithfulSMul_gal`. None of them is
     used by the Aux code: `versGal_injective` is proved by hand.
6. **Mathlib names: every one in section 5 exists, with a fitting type.** Each was checked by
   `rg`, and all of them also appear in compiled code. Locations:
   * `IsFractionRing.ringEquivOfRingEquivHom`: RingTheory/Localization/FractionRing.lean:477.
   * `FixedPoints.subfield`, `isIntegral`, `normal`, `toAlgAutMulEquiv`, `toAlgAut_surjective`:
     FieldTheory/Fixed.lean:103/250/274/375/379.
   * `MulSemiringAction.toAlgAut`: Algebra/Algebra/Equiv.lean:880.
   * `Gal.restrict_surjective`, `rootsEquivRoots`, `smul_rootsEquivRoots`, `restrict_smul`,
     `restrictDvd_surjective`: FieldTheory/PolynomialGaloisGroup.lean:119/153/169/192/244.
   * `Normal.minpoly_eq_iff_mem_orbit`: FieldTheory/Normal/Basic.lean:237.
   * `MulAction.IsPreprimitive.of_surjective`: GroupTheory/GroupAction/Primitive.lean:204.
   * `IsPreprimitive.of_isTrivialBlock_base`: GroupTheory/GroupAction/Primitive.lean:148.
   * `IsBlock.smul_eq_of_mem`: an alias at GroupTheory/GroupAction/Blocks.lean:283.
   * `isSolvable_gal_of_irreducible`: FieldTheory/AbelRuffini.lean:316.
   * `Subgroup.index_eq_two_iff`: GroupTheory/Index.lean:165.
   * `Subgroup.card_dvd_of_injective`: GroupTheory/Coset/Card.lean:82.
   * `Subgroup.subgroupOfEquivOfLe`: Algebra/Group/Subgroup/Map.lean:290.
   * `Nat.card_units`: Algebra/GroupWithZero/Units/Fintype.lean:41.
   * `Finite.one_lt_card_iff_nontrivial`: SetTheory/Cardinal/NatCard.lean:72.
   * `Module.finBasisOfFinrankEq`: LinearAlgebra/Dimension/Free.lean:347.
   * `Nat.pow_right_injective`: Data/Nat/Basic.lean:69.
   * `Nat.prime_dvd_prime_iff_eq`: Data/Nat/Prime/Defs.lean:187.
   * `card_rootSet_eq_natDegree`: FieldTheory/Separable.lean:439.
   * `AlgebraicClosure.isAlgClosed`: FieldTheory/IsAlgClosed/AlgebraicClosure.lean:203.
   * `MonoidHom.rangeRestrict_surjective`: Algebra/Group/Subgroup/Ker.lean:131.
   * `GaloisField.finrank`: FieldTheory/Finite/GaloisField.lean:78.
   * `RingHom.charZero`: Algebra/Ring/CharZero.lean:56.
   * The `CharZero (FractionRing R)` instance: Algebra/CharP/Algebra.lean:221.
   * `Matrix.mulVecLin`: used in LinearAlgebra/Matrix/ToLin.lean:289, `rfl` lemma to `mulVec`.
7. **Binders, universes and coercions in the section 4 statements are correct.**
   * `ReciproqueGalois` quantifies over `Type`. `X : Type` gives `Corps Γ`, `Cloture Γ : Type`, and
     `GaloisField ℓ 2 × GaloisField ℓ 2 : Type`.
   * `Corps` is an `abbrev` for a `Subfield` coerced to a type.
   * `Γ : Subgroup (Equiv.Perm X)` acts through `Subgroup` instances.
   * The `∃ (_ : Fact ℓ.Prime)` binder in `reciproque_corrigee_degre` is picked up as a local
     instance by `GaloisField ℓ ν`.
   * `AGL p (GaloisField p ν)` gets `Module (ZMod p)` from the `Algebra` instance.
8. **The import order is acyclic and correct.**
   * `Aux1 ← Radicaux ← Basic`; `Aux2 ← Basic`.
   * `Close ← TheorieNombres, EquationsPrimitives, Aux1, Aux2`.
   * None of the existing files imports the new ones.
   * File sizes (207 / 315 / 186 lines) are reasonable.
9. **The mathematics is correct.**
   * `AGL(1, q) ≀ C₂` in product action is primitive for `q ≥ 3`.
   * Its order `2 q² (q−1)²` with `q = ℓ²` does not divide `ℓ⁴(ℓ⁴−1)·4`.
   * The degree `ℓ⁴` is never 9 or 25.
   * One family covers every prime, including ℓ = 2, 3 and 5. That is better than the two
     families of the task.

## Issues (most severe first)

1. **minor: RISKS 1. The split-file compile was not run by the author.**
   * Fix: the result of my standalone compile is in the last section. If both passed, change
     RISKS 1 to "checked".
   * The Close file can only be checked after `--olean` builds of Aux1 and Aux2. The implementer
     must build them in order (Aux1 `--olean`, Aux2 `--olean`, then Close). Expect up to about
     35 min per file under memory pressure: the first RAll run took 2060 s.
2. **minor: global `Fact` instances `splitsΩ` and `splitsF`, and global `actionPerm` / `faithful`
   in Aux1.**
   * They are harmless today, because their discrimination-tree keys are specific
     (`equation Γ x₀`, `FractionRing (MvPolynomial X ℚ)`).
   * But the root module `GaloisOeuvres.lean` imports everything, and `actionPerm` puts a global
     `Equiv.Perm X` action on *every* `FractionRing (MvPolynomial X ℚ)`.
   * Suggested hygiene, not required: make `splitsΩ` and `splitsF` local instances or
     `scoped instance`, and make `actionPerm` scoped in `Realisation`. Then add
     `open scoped Realisation` where needed. The Close file only uses them through Aux1
     theorems whose statements already carry the instances, so it would likely need nothing.
     Doing this would require one more compile, so leave it unless a problem appears.
3. **minor (accuracy of section 5): "Not available in mathlib ... any MulSemiringAction ... on its
   fraction field" is slightly inaccurate.**
   * Mathlib has `IsFractionRing.mulSemiringAction G B L` (RingTheory/Localization/FractionRing.lean:671,
     an `@[instance_reducible] def`). It extends a `MulSemiringAction G B` to the fraction field.
     It also has `IsFractionRing.faithfulSMul`.
   * What is missing is only the `Equiv.Perm X` action on `MvPolynomial X ℚ`. The hand-made
     `actionPerm` is equivalent and already compiles, so no code change is needed. Reword the
     sentence.
4. **minor (readability): in Aux1 the variable is named `X` while `open Polynomial` makes
   `(Corps Γ)[X]` mean `Polynomial (Corps Γ)`.**
   * It is correct, because the notation token `[X]` does not refer to the variable, but it
     misleads readers.
   * Renaming the type variable to `L` (letters) or `α` would remove the ambiguity. Do it only
     together with another needed edit, since it costs a recompile.
5. **nit: brittle tactic patterns in Aux2.**
   * There are non-terminal `simp` calls followed by `field_simp`/`ring` (`d_inv`, `c_inv`,
     `droite`), and long `simp only ...; tauto` lines (l. 221–227, about 170 characters).
   * They compile on the pinned toolchain, and the repository already has many lines over 100
     characters (670), so this is acceptable.
   * If touched, factor the four `≠ 0` side goals of `couronne_soluble` into one helper lemma,
     for example `mul_inv_ne : a ≠ 0 → b ≠ 0 → a * b * a⁻¹ * b⁻¹ ≠ 0`.
(`MulSemiringAction.compHom` is an `abbrev` at Algebra/Ring/Action/Basic.lean:95, as the table
says.)

## The hardest parts and how they were made easier

* **Realization: Galois group = Γ.** This is the most dangerous step for instance search.
  * The blueprint's choices are the right ones: `equation := minpoly`, not a hand-made product;
    Ω is `AlgebraicClosure (Corps Γ)`, not a closure of F; and roots are moved by
    `Gal.rootsEquivRoots`, so no `IsScalarTower` is needed.
  * It also records the observed `Module.IsTorsionFree (Corps Γ) (Cloture Γ)` timeout and avoids
    it by going through the generic lemma `soluble_of_isSolvable_gal`. Keep that rule.
* **Primitivity transfer.** This uses `IsPreprimitive.of_surjective` along an equivariant map
  `X →ₑ[φ] rootSet`. It is cheap and compiled.
* **Corrected converse.** It reuses `exists_affine_indexing`. The only delicate part is the `subst`
  direction (eliminate `q` and `μ`), and the blueprint states it.

## Standalone compile of the split files (RISKS 1)

Run on 2026-11-27 with `python .lake-local/leanc.py`, one file at a time, on exact copies of the
reference files with their own import lists:

* `.lake-local/scratch/reciproque-lean-critic/A2.lean` (`import GaloisOeuvres.Basic`): **[OK]**,
  707 s, no errors, no warnings.
* `.lake-local/scratch/reciproque-lean-critic/A1.lean` (`import GaloisOeuvres.Radicaux`):
  **[OK]**, 126 s, no errors, no warnings.

So RISKS 1 is settled for Aux1 and Aux2. The Close file is the third segment of the
compiled `RAll.lean`, and it adds no declarations of its own beyond those in the two imported
files. It therefore needs only the `--olean` builds of Aux1 and Aux2 before its own compile.
Issue 1 above is reduced to "build in order".
