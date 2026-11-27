# PR 5: irreducibility over extensions of coprime degree

**Status:** branch pushed, PR not opened. Small and self-contained (1 file, +53/−11 lines).

Open it here:
https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:irreducible-map-coprime?expand=1

Read [NOTES-irreducible-coprime.md](NOTES-irreducible-coprime.md) first: it explains every declaration and proof step, and lists the questions a reviewer is likely to ask.

## What the branch contains

One file, `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`:

- `Irreducible.map_of_coprime_natDegree_finrank` (new, the main result): an irreducible polynomial over `K` stays irreducible over an extension `L` when its degree is coprime to `[L : K]`.
- `minpoly.map_eq_of_coprime_natDegree_finrank` (new): under the same coprimality, the minimal polynomial of `x` over `K` is also its minimal polynomial over `L`.
- `Irreducible.natDegree_dvd_finrank_of_aeval_eq_zero` (new): if an irreducible `f` over `K` has a root in `L`, then `deg f` divides `[L : K]`.
- `Irreducible.natDegree_dvd_finrank_mul_natDegree` (new): if `q` is an irreducible factor of `p` over `L`, then `deg p` divides `[L : K] * deg q`.
- `Polynomial.Irreducible.natDegree_dvd_finrank` (existing): same statement, proof shortened from 11 lines to 3 by using the new root lemma.

## Title

```text
feat(FieldTheory/IntermediateField/Adjoin/Basic): irreducibility over extensions of coprime degree
```

## Labels

`t-algebra` is added automatically from the file path. After opening, post a comment containing only the line `LLM-generated`.

## Description

```text
Add `Irreducible.map_of_coprime_natDegree_finrank`: an irreducible polynomial over a field `K` remains irreducible over a field extension `L` whose degree is coprime to the degree of the polynomial. Also add the corresponding statement for minimal polynomials, `minpoly.map_eq_of_coprime_natDegree_finrank`.

The proof goes through two divisibility lemmas that are stated separately because they are useful on their own:
* `Irreducible.natDegree_dvd_finrank_of_aeval_eq_zero`: if an irreducible `f : K[X]` has a root in `L`, then `f.natDegree ∣ finrank K L`;
* `Irreducible.natDegree_dvd_finrank_mul_natDegree`: if `q` is an irreducible factor of `p.map (algebraMap K L)`, then `p.natDegree ∣ finrank K L * q.natDegree`.

The existing `Polynomial.Irreducible.natDegree_dvd_finrank` (which assumes that `f` splits but only uses one root) is now a three-line consequence of the first lemma; its statement is unchanged.

---

The lemmas are placed next to `Polynomial.Irreducible.natDegree_dvd_finrank` and `minpoly.degree_dvd`, which they generalise and use. No imports are added.

If `L` is infinite-dimensional over `K` then `finrank K L = 0`, so the coprimality hypothesis only holds in degree one; the docstring says so.

Prior art: I found no such statement in mathlib or in open PRs. The downstream library Tau Ceti has the special case of cyclotomic polynomials (`TauCeti.irreducible_cyclotomic_of_coprime_finrank`), proved through linear disjointness; the general statement is not there.

AI use: I used Claude Code (Anthropic) to write these proofs and to check them against mathlib's conventions. I have gone through each proof and can explain every step. Checked locally: the module builds without warnings, `lake exe lint-style` and `#lint` pass on it.
```

## Known review points

- The new lemmas are in the root `Irreducible` namespace, while their neighbour is `Polynomial.Irreducible.natDegree_dvd_finrank`. The root namespace gives dot notation (`hp.map_of_coprime_natDegree_finrank h`) without `open Polynomial`; a reviewer may still ask for the other one.
- The file has many reverse dependencies, so CI rebuilds a lot. That is expected for this file.
- Not run locally: the full mathlib build and `lake exe shake`. Mathlib's CI runs both.
