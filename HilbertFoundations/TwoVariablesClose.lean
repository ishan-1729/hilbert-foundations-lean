import HilbertFoundations.ConstructionsClose
import RealClosureTransfer

/-!
# § 38: definite functions of two variables

This file closes the unit **`s38.two_variables`** of `Constructions.lean` (§ 38):
`twoVariableClaim : TwoVariableClaim` — every polynomial `f ∈ ℝ[x, y]` that takes no negative value
on `ℝ²` is a quotient of two sums of squares of polynomials, `f · D = N` with `D ≠ 0`. This is
Hilbert's theorem of 1893 (*Über ternäre definite Formen*, Acta Math. 17).

## The theorem is not proved in this project

Hilbert's own proof, by the theory of ternary forms, is not formalized. The statement is the case
of two variables of Artin's theorem of 1927 (the solution of Hilbert's seventeenth problem): a
polynomial in any number of variables with real coefficients that takes no negative value is a sum
of squares of rational functions. That theorem is taken from two sources.

* The package `hilbert17`, a dependency of this project (`lakefile.toml`), none of whose code is
  copied here: the branch `lean-v4.36-tauceti` of the fork
  <https://github.com/ishan-1729/hilbert17-lean> of the repository
  <https://github.com/pd4st8hb95-hub/hilbert17-lean>, pinned to the commit
  `a1a089e7e5080a2a27f0e95bf7b0e760f62ed4e5`. The proof is the work of the author of that
  repository; the branch adapts it to the toolchain of this project, and its file `PORT-NOTES.md`
  lists every change. The upstream repository keeps the Apache License 2.0 for the third-party
  material it attributes and states that it assigns no project-wide licence to its own
  contributions; that is why its files are not copied into this repository. The statement used is
  that of the module `RealClosureTransfer`,

  `Hilbert17Transfer.hilbert17RealCleared_candidate : Hilbert17Target.Hilbert17RealCleared`,

  that is: for every `n` and every `f : MvPolynomial (Fin n) ℝ` with `0 ≤ eval x f` for all `x`,
  there are `m`, a polynomial `q ≠ 0` and polynomials `p₀, …, pₘ₋₁` with `q² f = ∑ pᵢ²`. (The suffix
  `_candidate` is the name the theorem has upstream; it has no hypothesis other than the
  nonnegativity of `f`.) The proof there is Artin's: the field of rational functions is formally
  real; an element of a formally real field that is not a sum of squares is negative in some
  ordering of the field; the ordered field of rational functions lies in a real closed field; and a
  polynomial with coefficients in `ℝ` that takes a negative value at a point of a real closed
  extension of `ℝ` takes a negative value at a point of `ℝⁿ`. The last step, the transfer of a
  system of sign conditions between two real closed fields, is proved there by elimination of one
  variable at a time.

* The Tau Ceti library (<https://github.com/TauCetiProject/TauCeti>, Apache License 2.0, pinned in
  `lakefile.toml` to the commit `aa3cfad1274c06cff25f2b58848498b3c3f68d0f`), a dependency of this
  project, none of whose code is copied here. The files of `hilbert17` take from it: the real
  closure of an ordered field (`TauCeti.RealClosure.exists_realClosure`); the extension of a
  preordering of a field to an ordering (`Subsemiring.IsPreordering.exists_linearOrder`); and, for
  polynomials in one variable over a real closed field, the count of roots and the Tarski query by
  signed subresultant coefficients
  (`Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc`,
  `Polynomial.tarskiQuery_eq_permanencesMinusVariations_signedPsc`), the determination of the sign
  conditions realized at the roots of a polynomial (`Polynomial.fullInverse_mulVec_tarskiQuery`),
  and the sample points of the line (`TauCeti.SignDetermination.exists_mem_signSamples_sign_eq`).

## What this file contributes

Only the passage from the statement of `hilbert17` to the form of `TwoVariableClaim`: for `n = 2`,
from `q ≠ 0` and `q² f = ∑ pᵢ²`, the denominator `D := q²` and the numerator `N := ∑ pᵢ²` are sums
of squares, `D ≠ 0`, and `f · D = N`.
-/

namespace HilbertFoundations

/-- **Hilbert's theorem on the definite functions of two variables** (unit `s38.two_variables`):
a polynomial in two variables with real coefficients that takes no negative value is a quotient of
two sums of squares of polynomials. It is the case `n = 2` of Artin's theorem as proved in the
package `hilbert17` (see the header of this file). -/
theorem twoVariableClaim : TwoVariableClaim := by
  intro f hf
  obtain ⟨m, q, p, hq, h⟩ := Hilbert17Transfer.hilbert17RealCleared_candidate 2 f hf
  refine ⟨∑ i : Fin m, p i ^ 2, q ^ 2, ?_, ?_, pow_ne_zero 2 hq, ?_⟩
  · exact IsSumSq.sum fun i _ => by rw [pow_two]; exact IsSumSq.mul_self (p i)
  · rw [pow_two]
    exact IsSumSq.mul_self q
  · rw [mul_comm]
    exact h

end HilbertFoundations
