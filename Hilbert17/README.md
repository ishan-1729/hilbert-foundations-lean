# Hilbert17: Artin's theorem on definite polynomials (vendored)

The Lean files in this directory are not part of the formalization of Hilbert's *Foundations of
Geometry*. They are a copy of 18 files of another project, with the changes listed under
"Modifications", and contain a proof of Artin's theorem of 1927, the solution of Hilbert's
seventeenth problem, for polynomials with real coefficients: a polynomial in any number of
variables that takes no negative value is a sum of squares of rational functions. They are used in
two places. `HilbertFoundations/TwoVariablesClose.lean` derives from them the statement
`TwoVariableClaim` of the unit `s38.two_variables` (§ 38), Hilbert's theorem of 1893 on the definite
functions of two variables, which the book mentions without proof.
`HilbertFoundations/Theorem44Close.lean`, with its helper module `Theorem44CloseAux1.lean`, takes
from them two steps of Artin's argument, the separation of the non-sums of squares by orderings
and the transfer of sign conditions between real closed fields, and proves with them the statement
`Theorem44` of the unit `th.44` (Theorem 44, § 39).

## Source

| | |
|---|---|
| Repository | <https://github.com/pd4st8hb95-hub/hilbert17-lean> |
| Commit | `19cd90e0a2c0f5c0e034ee54d06f5e129561ee59` (14 October 2026) |
| Author | The upstream `README.md` names no author; the commits name the author as `Haitao-Ji` |
| Licence | None for these files; see below |
| Upstream toolchain | Lean `v4.32.1`, a copy of Mathlib (commit `520045ab14e26149ee970e2e617ca04b09bde5d6`) in the upstream directory `vendor/`, and 71 files of the Tau Ceti library, backported and copied into the upstream directory `TauCeti/` |

**Licence and copyright.** The upstream repository contains the text of the Apache License 2.0 in
its file `LICENSE`. Its file `THIRD_PARTY.md` says that this licence is kept for the attributed
upstream material and that no project-wide licence is assigned to the original contributions, and
its file `PROVENANCE.json` says the same. The attributed upstream material is the third-party code
in that repository: Mathlib and the other vendored packages, and the Tau Ceti files. None of it is
copied here. The Lean files copied here are the upstream repository's own contributions. They have
no copyright or licence header, and none has been added. On the statements of the upstream
repository no licence is granted for them.

The files of this directory are therefore not covered by the file `LICENSE` at the root of this
repository (Apache License 2.0). The copyright of the proof belongs to the upstream author, not to
this project. The files are reproduced here, with this attribution, so that the formalization
builds; this repository grants no licence for them. What is this project's is the file
`OrderingSeparation.lean`, which is rewritten, and the changed lines listed under "Modifications".

## Files

The file names are those of the upstream repository, where the files are at the root. The
namespaces (`Hilbert17`, `Hilbert17Target`, `Hilbert17Transfer`) and the names of the declarations
are unchanged.

| File | Lines | Contents |
|---|---|---|
| `Hilbert17/TargetSpec.lean` | 51 | The statements to be proved, as `Prop`s: `Hilbert17Target.Hilbert17Real` (a polynomial in `n` variables with real coefficients that takes no negative value is a sum of squares in the field of fractions) and `Hilbert17Target.Hilbert17RealCleared` (the form with a common denominator, below), with the definitions they are stated in. |
| `Hilbert17/ClearDenominators.lean` | 153 | For an integral domain `A` with field of fractions `F`: the image of `f : A` is a sum of squares in `F` if and only if `q² f` is a sum of squares in `A` for some `q ≠ 0` (`Hilbert17.isSumSq_fraction_iff`, `isSumSq_fraction_iff_explicit`); the case of the polynomials with real coefficients (`real_mvPolynomial_fraction_iff`). |
| `Hilbert17/FractionSemireal.lean` | 58 | The field of fractions of a polynomial ring over an ordered field is semireal, that is, `-1` is not a sum of squares in it (`Hilbert17.isSemireal_mvPolynomial_fraction`). |
| `Hilbert17/OrderingSeparation.lean` | 50 | In a semireal field an element is a sum of squares if and only if it is nonnegative in every ordering of the field (`Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`). Not the upstream file: see "Modifications". |
| `Hilbert17/CoefficientOrder.lean` | 34 | A ring homomorphism of a real closed field into an ordered field preserves the order (`Hilbert17Transfer.ringHom_monotone`, `ringHom_strictMono`). |
| `Hilbert17/ConditionalArtin.lean` | 91 | Artin's argument under a hypothesis. `Hilbert17.NegativePointTransfer R`: a polynomial with coefficients in `R` that takes a negative value at a point of an ordered field containing `R` takes a negative value at a point of `R`. From this hypothesis for `R = ℝ`: `hilbert17Real_of_negativePointTransfer`, `hilbert17RealCleared_of_negativePointTransfer`. |
| `Hilbert17/CoefficientSignPattern.lean` | 82 | If two ring homomorphisms of a ring `A` into ordered fields give the same signs to the coefficients of a polynomial over `A`, its two images vanish together, have the same degree and the same sign of the leading coefficient. |
| `Hilbert17/UniformRootCount.lean` | 127 | `Hilbert17Transfer.rootCountProjection p`, a finite set of elements of `A` whose signs determine the number of distinct roots of the image of `p` in a real closed field (`rootCount_map_eq_of_projection_sign_agree`), by the signed subresultant coefficients of Tau Ceti. |
| `Hilbert17/MonicQueryProjection.lean` | 163 | The same for the Tarski query of a monic polynomial `p` and a polynomial `q`, and for the number of roots of `p` at which finitely many polynomials have given signs (`tarskiQuery_map_eq_of_monicProjection_sign_agree`, `signCount_map_eq_of_monicPatternProjection_sign_agree`). |
| `Hilbert17/LocalizationSignDescent.lean` | 58 | The signs of finitely many elements of a localization `A[c⁻¹]` are determined by the signs of finitely many elements of `A` (`awaySignProjection`, `sign_eq_on_localization_of_sign_eq_on_projection`). |
| `Hilbert17/DegreeNormalization.lean` | 69 | `normalizedAtDegree p d`: the part of `p` of degree at most `d`, divided by the coefficient of `p` of degree `d`, a monic polynomial over the localization of `A` in which that coefficient is invertible (`normalizedAtDegree_monic`, `normalizedAtDegree_map`). |
| `Hilbert17/GeneralQueryProjection.lean` | 104 | The Tarski query for a polynomial `p` that need not be monic (`queryProjection`, `tarskiQuery_map_eq_of_queryProjection_sign_agree`). |
| `Hilbert17/GeneralPatternProjection.lean` | 78 | The existence of a root of `p` at which finitely many polynomials have given signs (`patternProjection`, `exists_root_signs_map_iff_of_patternProjection_sign_agree`). |
| `Hilbert17/WholeLineAlternatives.lean` | 126 | Over a real closed field, a system of sign conditions on finitely many polynomials in one variable has a solution if and only if it has one among the roots of the product of the nonzero polynomials of the system, or among the roots of the derivative of that product, or the signs are those at `−∞` or those at `+∞` (`exists_signs_iff_root_derivative_infinity`). |
| `Hilbert17/UniformOneVariable.lean` | 123 | Elimination of one variable: `wholeLineProjection Q`, a finite set of elements of `A` such that, for two ring homomorphisms of `A` into real closed fields that agree in sign on it, a system of sign conditions on the polynomials `Q j` has a solution in the one field if and only if it has one in the other (`exists_signs_map_iff_of_wholeLineProjection_sign_agree`). |
| `Hilbert17/FinSuccEvaluation.lean` | 31 | The evaluation of a polynomial in `n + 1` variables, read as a polynomial in one variable with coefficients in `n` variables (`eval₂_finSuccEquiv`). |
| `Hilbert17/FiniteVariableTransfer.lean` | 98 | The same transfer for polynomials in `n` variables, by induction on `n` (`exists_matching_signs_eval₂`, `exists_signs_eval₂_iff`), and the consequence for one polynomial with a negative value (`exists_negative_eval_of_exists_negative_eval₂`). |
| `Hilbert17/RealClosureTransfer.lean` | 46 | The hypothesis of `ConditionalArtin.lean` for every real closed field (`negativePointTransfer_of_isRealClosed`, with the real closure of an ordered field of Tau Ceti), and the final theorems `hilbert17Real_candidate` and `hilbert17RealCleared_candidate`. |

The files are 1,542 lines in all. They import Mathlib, each other, and seven modules of the Tau
Ceti library, a dependency of this package: `TauCeti.Algebra.Order.Ring.Ordering.Semireal`,
`TauCeti.Algebra.Polynomial.Eval.Infinity`, `TauCeti.FieldTheory.RealClosure.Basic`,
`TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots`,
`TauCeti.Geometry.RealAlgebraic.SignDetermination.WholeLine`,
`TauCeti.RingTheory.Polynomial.Reductum` and
`TauCeti.RingTheory.Polynomial.Subresultant.CauchyIndex`. With the modules these import, they need
83 modules of Tau Ceti.

The rest of the upstream repository is not copied: its other Lean files at the root
(`Hilbert17.lean`, `Hilbert17Full.lean`, `Hilbert17RealClosure.lean`, `RealInstance.lean`,
`TargetSanity.lean`, `CertificateNonnegative.lean`), its copies of Mathlib, of the other packages
and of the Tau Ceti files, and its checks, manifests and verification records.

The statement used by `HilbertFoundations/TwoVariablesClose.lean` is one:

* `Hilbert17Transfer.hilbert17RealCleared_candidate : Hilbert17Target.Hilbert17RealCleared`, in
  `Hilbert17/RealClosureTransfer.lean`: for every `n` and every `f : MvPolynomial (Fin n) ℝ` with
  `0 ≤ MvPolynomial.eval x f` for all `x : Fin n → ℝ`, there are `m`, a polynomial `q ≠ 0` and
  polynomials `p i`, `i : Fin m`, with `q ^ 2 * f = ∑ i, p i ^ 2`.

The statements used by `HilbertFoundations/Theorem44Close.lean` and its helper module
`HilbertFoundations/Theorem44CloseAux1.lean` are three:

* `Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`, in
  `Hilbert17/OrderingSeparation.lean`: in a semireal field an element is a sum of squares if and
  only if it is nonnegative in every ordering of the field (the statement of the rewritten file,
  see "Modifications");
* `Hilbert17Transfer.exists_matching_signs_eval₂`, in `Hilbert17/FiniteVariableTransfer.lean`:
  for two ring homomorphisms of a ring `A` into real closed fields that give the same signs to the
  elements of `A`, every point of the first field at which finitely many polynomials in `n`
  variables over `A` have given signs has a counterpart in the second with the same signs;
* `Hilbert17Transfer.eval₂_finSuccEquiv`, in `Hilbert17/FinSuccEvaluation.lean`: the evaluation of
  a polynomial in `n + 1` variables read as a polynomial in one variable over the polynomials in
  `n` variables.

The suffix `_candidate` is part of the upstream name; the theorem has no hypothesis other than that
`f` takes no negative value. The header comments of several files say "source draft", "not yet
elaborated" or "not yet compiled", and the docstring of `hilbert17Real_candidate` calls the theorem
a candidate. This is the wording of the upstream author from before the upstream build was
verified, and it is kept as it is. The files compile in this repository, and the axiom audit of
this repository (`scripts/AxiomsAudit.lean`) examines `HilbertFoundations.twoVariableClaim` and
`HilbertFoundations.theorem44` with everything their proofs depend on, so it covers the
declarations of this directory that the proofs use. In the same way the header of
`ConditionalArtin.lean` says that `NegativePointTransfer` is an unproved input: it is a hypothesis
of the theorems of that file, and
`negativePointTransfer_of_isRealClosed` in `RealClosureTransfer.lean` proves it.

## Modifications

The upstream repository is built with Lean `v4.32.1` and with its own copies of Mathlib and of Tau
Ceti files. Here the files are built with the toolchain of this repository: Lean `v4.36.0`, Mathlib
`v4.36.0`, and Tau Ceti at the commit `aa3cfad1274c06cff25f2b58848498b3c3f68d0f` as a dependency.
The changes made for this, and for the place of the files in this repository, are the following;
"upstream" is the commit named above.

1. **Module names.** The upstream modules are at the root (`import TargetSpec`); here they are
   `Hilbert17.TargetSpec` and so on. Seventeen import lines in nine files are rewritten:
   `ConditionalArtin` (4), `FiniteVariableTransfer` (2), `FractionSemireal` (1),
   `GeneralPatternProjection` (1), `GeneralQueryProjection` (3), `MonicQueryProjection` (1),
   `RealClosureTransfer` (2), `UniformOneVariable` (2), `UniformRootCount` (1).
2. **Mathlib modules that have moved.** `import Mathlib.Data.Real.Basic` is
   `import Mathlib.Basic.Real.Basic` (`TargetSpec`, `ClearDenominators`, `FractionSemireal`), and
   `import Mathlib.Data.Sign.Basic` is `import Mathlib.Basic.Sign.Basic` (`CoefficientSignPattern`,
   `LocalizationSignDescent`).
3. **The instance `IsRealClosed ℝ`.** The upstream file `RealInstance.lean`, an adaptation of a Tau
   Ceti file, proves that `ℝ` is real closed. It is not copied: Mathlib `v4.36.0` has the instance
   (`Mathlib.FieldTheory.IsRealClosed.Real`). In `ConditionalArtin.lean` the line
   `import RealInstance` is `import Mathlib.FieldTheory.IsRealClosed.Real`, and three lines
   `letI : IsRealClosed ℝ := …` are removed, one in `ConditionalArtin.lean`
   (`hilbert17Real_of_negativePointTransfer`) and two in `RealClosureTransfer.lean`
   (`hilbert17Real_candidate`, `hilbert17RealCleared_candidate`).
4. **Two lemmas deprecated in Mathlib `v4.36.0`.** In `CoefficientSignPattern.lean`
   (`map_eq_zero_iff_of_coeff_sign_agree`) the line `rw [Polynomial.ext_iff, Polynomial.ext_iff]`
   is `rw [← AddMonoidAlgebra.coeff_inj, ← AddMonoidAlgebra.coeff_inj, DFunLike.ext_iff,
   DFunLike.ext_iff]`, on two lines. In `DegreeNormalization.lean` (`normalizedAtDegree_monic`)
   `if_true` is `ite_true`.
5. **`OrderingSeparation.lean` is rewritten.** The upstream file (203 lines) proves the extension
   of a preordering of a field to an ordering (adjunction of one element, unions of chains, Zorn's
   lemma) on Mathlib's structure `RingPreordering`, which Mathlib `v4.36.0` has deprecated. The
   file of this directory (50 lines) keeps the one statement that the other files use,
   `Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`, with the same name and the same
   type, and proves it from the Tau Ceti library (`Subsemiring.IsPreordering.sumSq`,
   `Subsemiring.IsPreordering.isPreordering_adjoin`,
   `Subsemiring.IsPreordering.exists_linearOrder`). The other declarations of the upstream file
   are dropped. The proof in this file is this project's.

No statement that is kept has changed, and no declaration is renamed. By file, with the numbers of
the list above:

| File | Lines upstream | Lines here | Changes |
|---|---|---|---|
| `ClearDenominators.lean` | 153 | 153 | 2 |
| `CoefficientOrder.lean` | 34 | 34 | none |
| `CoefficientSignPattern.lean` | 81 | 82 | 2, 4 |
| `ConditionalArtin.lean` | 92 | 91 | 1, 3 |
| `DegreeNormalization.lean` | 69 | 69 | 4 |
| `FinSuccEvaluation.lean` | 31 | 31 | none |
| `FiniteVariableTransfer.lean` | 98 | 98 | 1 |
| `FractionSemireal.lean` | 58 | 58 | 1, 2 |
| `GeneralPatternProjection.lean` | 78 | 78 | 1 |
| `GeneralQueryProjection.lean` | 104 | 104 | 1 |
| `LocalizationSignDescent.lean` | 58 | 58 | 2 |
| `MonicQueryProjection.lean` | 163 | 163 | 1 |
| `OrderingSeparation.lean` | 203 | 50 | 5 |
| `RealClosureTransfer.lean` | 48 | 46 | 1, 3 |
| `TargetSpec.lean` | 51 | 51 | 2 |
| `UniformOneVariable.lean` | 123 | 123 | 1 |
| `UniformRootCount.lean` | 127 | 127 | 1 |
| `WholeLineAlternatives.lean` | 126 | 126 | none |

The three files without changes are identical, byte for byte, to the files of the upstream commit
(as stored in the upstream repository, with Unix line ends). In the fourteen files with the changes
1 to 4, the changed lines are 17 import lines for 1, 5 import lines for 2, one import line and
three removed lines for 3, and two lines of proofs for 4; every other line is the upstream line.

SHA-256 of the files of this directory (with Unix line ends):

```
8be61156da4b2dcd3c337b61de660675699d49837d8c5367c655bdf90c44001a  Hilbert17/ClearDenominators.lean
85c8261163b9370edb974f37f49539474c4c276534b508794f8ef42621d93952  Hilbert17/CoefficientOrder.lean
1e1815903813e1e20bb7c2b9f0bc98606a2e65f1f1bc9d5c20f5f2d401a5b159  Hilbert17/CoefficientSignPattern.lean
3a383e0ac6675a5da4aa300274b1ce9befd8a5d0d83a9285547d660253f459d5  Hilbert17/ConditionalArtin.lean
04a83180613eb38c8a69caee9c50340e7447b4c49485bfc5980d6e8682563427  Hilbert17/DegreeNormalization.lean
e044563c83d7aee875131b91f148fb91546f8ebad4d065d1959381478329ce8f  Hilbert17/FinSuccEvaluation.lean
0a97bdea0678df43ac01658916300f9aec6657615c4df6f9cdaa58ba22ce34cc  Hilbert17/FiniteVariableTransfer.lean
a039cabeac02899aacb23c6d0349c37c5939c11d02ce7d8fd1e678d2a93184a5  Hilbert17/FractionSemireal.lean
ff56540821fccbff2dc08cf9e98f7b04f5460dcdd15a6c6a7ae0bcba6a5a5698  Hilbert17/GeneralPatternProjection.lean
fdcb399663c64ede71d8e34e044facb1687fe5ba0a47190574ce99b9f94368f7  Hilbert17/GeneralQueryProjection.lean
892e9977644243e64b545ee7215f44ea94842e6803deaf27a80b1112f9967411  Hilbert17/LocalizationSignDescent.lean
73c46d185f086feff92e50e01a8139a1d614274d58bf632d98a4b6094d09d0f5  Hilbert17/MonicQueryProjection.lean
f2893679c9fdd1bced1fb5b6a76c890326e7d5406a5b64bb5831777fd79fb60b  Hilbert17/OrderingSeparation.lean
7e99b40ae5ffca5ded774a927b4c010a776c5122db5acc1083d06e2182eb942f  Hilbert17/RealClosureTransfer.lean
328b12f24d30a04cfed37f8892b93e70289ce5aea3499727c7b7124651d57e6d  Hilbert17/TargetSpec.lean
12b73b9bd35b9d85d9ada22e3d3f2a85ba7f7610065abf7117f3078af30fd5ad  Hilbert17/UniformOneVariable.lean
0f12bdeef86a432fef6ff1e7c644f0815f09a96710cca29923df678f6ed87606  Hilbert17/UniformRootCount.lean
6b81b99d9f897af8ce86e563dd5c4433f2f63a0931e6f6b8330cd6283ffd30f9  Hilbert17/WholeLineAlternatives.lean
```

What differs from the upstream repository outside the files:

* They are built as a further library of this package, `Hilbert17`, declared in `lakefile.toml`.
  The upstream `lakefile.toml` sets no Lean options, so the files are written for Lean's default
  values. The options of this package are `pp.unicode.fun = true` and `autoImplicit = false`; the
  library is declared with `autoImplicit = true`, which is Lean's default value, so that this
  option has for these files the value it has upstream.
* Mathlib and Tau Ceti are dependencies of this package, pinned in `lakefile.toml` and
  `lake-manifest.json`; the upstream repository builds against its own copies of them.
* There is no root module `Hilbert17.lean` here: the upstream one imports upstream files that
  are not copied. The library is declared with `globs = ["Hilbert17.+"]`, so that its modules are
  the files of this directory, and it is reached through `import Hilbert17.RealClosureTransfer`
  (`TwoVariablesClose.lean`), `import Hilbert17.FiniteVariableTransfer` and
  `import Hilbert17.OrderingSeparation` (`Theorem44Close.lean`), and
  `import Hilbert17.FinSuccEvaluation` (`Theorem44CloseAux1.lean`).
