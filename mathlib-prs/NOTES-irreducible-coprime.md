# Notes for PR 5: irreducibility over extensions of coprime degree

These notes are for you, so that you can defend every line in review without help. Setting: `K` and `L` are fields, `L` is a `K`-algebra (a field extension), `finrank K L` is the degree `[L : K]` (it is `0` when the extension is infinite).

## 1. `Irreducible.natDegree_dvd_finrank_of_aeval_eq_zero`

**Statement.** If `f : K[X]` is irreducible and `x : L` is a root of `f` (`aeval x f = 0`), then `f.natDegree ∣ finrank K L`.

**Why it is true.** `f` is irreducible and kills `x`, so `f` is the minimal polynomial of `x` up to its leading coefficient. The degree of the minimal polynomial is `[K(x) : K]`, which divides `[L : K]` by the tower law.

**The proof, line by line.**
- `natDegree_mul_C`: multiplying `f` by the nonzero constant `(leadingCoeff f)⁻¹` does not change its degree. The rewrite goes right to left, so the goal becomes a statement about `f * C (leadingCoeff f)⁻¹`.
- `minpoly.eq_of_irreducible hi hx`: that product is `minpoly K x`. Now the goal is `(minpoly K x).natDegree ∣ finrank K L`.
- `minpoly.degree_dvd`: exactly this, for `x` integral over `K`. Integrality holds because `x` is algebraic: it is a root of the nonzero polynomial `f`.

## 2. `Polynomial.Irreducible.natDegree_dvd_finrank` (existing, proof shortened)

**Statement (unchanged).** If `f` is irreducible and splits over `L`, then `f.natDegree ∣ finrank K L`.

**New proof.** A polynomial of positive degree that splits has a root; apply lemma 1 to that root. The old proof did the same thing inline in 11 lines.

**If asked "why touch an existing proof?"** Because lemma 1 is the same argument without the unnecessary `Splits` hypothesis; keeping both proofs would duplicate it.

## 3. `Irreducible.natDegree_dvd_finrank_mul_natDegree`

**Statement.** If `p : K[X]` is irreducible, `q : L[X]` is irreducible, and `q` divides `p` over `L`, then `p.natDegree ∣ finrank K L * q.natDegree`.

**Why it is true.** Let `M = L[X]/(q)`, a field of degree `deg q` over `L`, so of degree `[L : K] * deg q` over `K`. The class of `X` in `M` is a root of `q`, hence of `p`. Apply lemma 1 to `p` and the extension `M / K`.

**The proof, line by line.**
- `Fact (Irreducible q)`: mathlib's field structure on `AdjoinRoot q` needs irreducibility as a `Fact` instance.
- The `rw` turns `finrank K L * q.natDegree` into `finrank K (AdjoinRoot q)`: `AdjoinRoot.powerBasis_dim` says the power basis of `AdjoinRoot q` has `q.natDegree` elements, `PowerBasis.finrank` says that is `finrank L (AdjoinRoot q)`, and `finrank_mul_finrank` is the tower law.
- Lemma 1 with `x := AdjoinRoot.root q`. It remains to show `aeval (root q) p = 0`.
- `aeval_map_algebraMap` moves the evaluation to `p.map (algebraMap K L)`, `AdjoinRoot.aeval_eq` says evaluating at the root is the quotient map, and `AdjoinRoot.mk_eq_zero` says the quotient map kills exactly the multiples of `q`. That is the hypothesis `hqp`.

## 4. `Irreducible.map_of_coprime_natDegree_finrank` (the main result)

**Statement.** If `p : K[X]` is irreducible and `p.natDegree` is coprime to `finrank K L`, then `p.map (algebraMap K L)` is irreducible in `L[X]`.

**Why it is true.** Take an irreducible factor `q` of `p` over `L`. By lemma 3, `deg p` divides `[L : K] * deg q`. Since `deg p` is coprime to `[L : K]`, it divides `deg q`. So `deg p ≤ deg q`, and a divisor of `p` of degree at least `deg p` is `p` up to a unit. So `p` is associated to the irreducible `q`, hence irreducible.

**The proof, line by line.**
- `exists_irreducible_of_natDegree_pos`: a polynomial of positive degree over a field has an irreducible factor `q`. The degree of `p.map _` equals the degree of `p` (`natDegree_map`), which is positive because `p` is irreducible.
- `associated_of_dvd_of_natDegree_le hqp _ _`: if `q ∣ r`, `r ≠ 0` and `deg r ≤ deg q`, then `q` and `r` are associated. `.irreducible hq` transfers irreducibility along the association.
- The remaining goal is `(p.map _).natDegree ≤ q.natDegree`. After `natDegree_map`, it follows from divisibility (`Nat.le_of_dvd`, using `0 < deg q`), and the divisibility `deg p ∣ deg q` comes from lemma 3 and coprimality (`Nat.Coprime.dvd_of_dvd_mul_left`).

**Degenerate cases a reviewer may probe.**
- `L` infinite over `K`: `finrank K L = 0`, and `Nat.Coprime n 0` means `n = 1`. So the hypothesis forces `deg p = 1`, and the conclusion is trivially true. The docstring states this.
- `deg p = 1`: always coprime, and linear polynomials stay irreducible. Fine.
- The statement is false without coprimality: `X² − 2` over `ℚ(√2)`.

**Example to have in mind.** `X³ − 2` is irreducible over `ℚ`, and `[ℚ(i) : ℚ] = 2` is coprime to 3, so `X³ − 2` is irreducible over `ℚ(i)`.

## 5. `minpoly.map_eq_of_coprime_natDegree_finrank`

**Statement.** Let `E` be a domain that is an `L`-algebra (with the scalar tower `K → L → E`), and `x : E`. If `(minpoly K x).natDegree` is coprime to `finrank K L`, then `(minpoly K x).map (algebraMap K L) = minpoly L x`.

**Why it is true.** If `x` is integral over `K`: its minimal polynomial over `K` is irreducible (this is where `E` being a domain is used), so by the main result it stays irreducible over `L`; it is monic and kills `x`, and an irreducible monic polynomial that kills `x` is the minimal polynomial.

If `x` is not integral over `K`: mathlib defines `minpoly K x = 0`, of degree 0. Coprimality of `0` and `finrank K L` means `finrank K L = 1`, so `L` is finite over `K`. Then `x` is not integral over `L` either (integrality is transitive along a finite extension), so `minpoly L x = 0` as well, and both sides are `0`.

**The proof, line by line.**
- First case: `eq_of_irreducible_of_monic` with the three facts above (`irreducible hx` then the main result; `aeval_map_algebraMap` and `minpoly.aeval`; `(monic hx).map _`).
- Second case: `eq_zero hx` rewrites `minpoly K x` to `0`; `Nat.coprime_zero_left` turns the hypothesis into `finrank K L = 1`; `Module.finite_of_finrank_eq_succ` gives finiteness; then both minimal polynomials are rewritten to `0`, the second by contradiction with `isIntegral_trans`.

**If asked "why no integrality hypothesis?"** Because the statement is true without it, as the second case shows, and mathlib prefers the weakest hypotheses. The docstring says so.

## Placement and naming

- **File.** `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`, next to `minpoly.degree_dvd` and `Polynomial.Irreducible.natDegree_dvd_finrank`, which the new lemmas use and generalise. An earlier draft had them in `LinearDisjoint.lean`; nothing in the proof uses linear disjointness, so that was wrong.
- **Names.** Built from the statements: `map_of_coprime_natDegree_finrank` is "the `map` is irreducible, given coprimality of `natDegree` and `finrank`". The `_root_.` prefix is needed because the file is inside `namespace IntermediateField`.
- **No new imports.**

## Prior art

- Mathlib: `Polynomial.Irreducible.natDegree_dvd_finrank` (splitting case of lemma 1) and `minpoly.degree_dvd`. Nothing about coprime degree.
- Tau Ceti: `TauCeti.irreducible_cyclotomic_of_coprime_finrank`, the cyclotomic special case, proved by a different route (linear disjointness). The general lemma is absent there.

## What was checked

The module builds with no warnings, `lake exe lint-style` passes on it, `#lint` passes on the five declarations, and `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`. Test examples (including `X³ − 2` statements) compile in a scratch file. The full mathlib build was not run locally.
