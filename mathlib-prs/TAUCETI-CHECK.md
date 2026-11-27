# Tau Ceti overlap check

Checked on 26 November 2026 against a local copy of Tau Ceti `main` (commit 3f8fe7e), its roadmap repo and its GitHub pull requests. Each group of items was searched twice by independent agents; the second assumed the first had searched under the wrong names. The full findings, with every search run and every Tau Ceti declaration read, are in `out/tauceti-check.json`.

"Absent" means no statement of the result was found on `main`, on the roadmap or in an open PR. PR searches match only titles and descriptions, so "no open PR" is less certain than "not on main".

## Your open PRs and ready branches

| Item | Tau Ceti | What that means |
|---|---|---|
| `Real.sqrt` is analytic away from 0 (PR #46502) | Absent | Keep. Tau Ceti has only manifold-level and operator square-root versions. |
| Order structure on `MulOpposite` / `AddOpposite` (PR #46504) | Absent | Keep. Tau Ceti has no order instance on an opposite type. |
| Archimedean ordered rings are commutative (branch ready) | Absent | Keep. No commutativity result under `Archimedean`, for rings or groups. |
| Converse of Abel–Ruffini (branch ready) | Mostly there | Drop. Tau Ceti has the converse and the "if and only if" in characteristic 0, and more general versions of three of our helper lemmas. Our branch adds only the weaker hypothesis "the order of the Galois group is not divisible by the characteristic". |

## The remaining candidates

| Item | Tau Ceti | What that means |
|---|---|---|
| Lagrange's theorem on periodic continued fractions, Euler's converse, Galois's theorem on purely periodic ones | Absent | New. No notion of a periodic continued fraction exists there. |
| Galois's criterion for transitive groups of prime degree (solvable ⇔ no non-identity element fixes two points ⇔ inside AGL(1, p)), and for equations of prime degree | Mostly absent | New for general p. Tau Ceti has AGL(1, K) as a group and the case p = 5 only, by a different route. |
| A non-commutative ordered division ring (Hilbert § 33) | Absent | New. No skew Laurent or skew Hahn series there. |
| An irreducible polynomial stays irreducible over an extension of coprime degree | Special case | Tau Ceti has it for cyclotomic polynomials only. The general lemma is absent, though their proof would generalize. |
| ℝ is the unique Cauchy-complete Archimedean ordered field | Absent | New. |
| Algebra of `OrderType` | Absent | New. `OrderType` is not used in Tau Ceti at all. |
| Order isomorphisms for lexicographic sums and products | Absent | New. Only a comparison lemma for `Fin` exists. |
| Circle of Apollonius | Special case | Tau Ceti has one computation in ℂ for a special pair of points. The general Euclidean statement is absent. |
| Integral of √(r² − x²) | Special case | Tau Ceti has r = 1 only, as the distribution function of the semicircle law. |
| Sums-of-squares lemmas (`IsSumSq.inv`, four squares for rationals, nonnegative real polynomials) | Absent | New, small. |
| Every group of order below 60 is solvable | Nearly there | The statement is absent, but Tau Ceti has Burnside's p^a q^b theorem, which settles every order below 60 except 30 and 42. Low novelty. |
| Minimal normal subgroup of a finite solvable group is elementary abelian | Already there | Drop. Tau Ceti's version is more general. |
| A finite solvable group has a normal subgroup of prime index | Already there | Drop. Same statement, same name. |
| Solvable primitive groups have prime-power degree | Planned | Drop or wait. It is on Tau Ceti's roadmap in a more general form, and the ingredients are on `main`. |
| Order of PGL(n, q) | Already there | Drop. |
| Order of PSL(n, q) | Open PR | Drop. Tau Ceti PR #42302 covers it. |

## What is still worth doing, by novelty and impact

1. Lagrange's theorem on continued fractions (large).
2. Galois's criterion for transitive groups and equations of prime degree, general p (medium).
3. A non-commutative ordered division ring (large, needs a design discussion).
4. Archimedean ordered rings are commutative (branch ready).
5. Irreducibility over an extension of coprime degree (small).
6. ℝ as the unique Cauchy-complete Archimedean ordered field (small rewrite).
7. `OrderType` algebra and lexicographic order isomorphisms (small).
8. Circle of Apollonius, the √(r² − x²) integral, sums-of-squares lemmas (small).
