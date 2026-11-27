# PR 4: the converse of the Abel–Ruffini theorem

**Dropped on 26 November 2026.** Tau Ceti already has this theorem in characteristic 0, with more general versions of three of the helper lemmas (see [TAUCETI-CHECK.md](TAUCETI-CHECK.md)). The branch `abelRuffini-converse` was deleted from the fork. It still exists locally in `D:\Projects\mathlib4`. The rest of this file is kept for reference.

## The prior art

- **Where:** `TauCeti/FieldTheory/AbelRuffini.lean` in https://github.com/TauCetiProject/TauCeti, added by its PR #44963, "the converse of the Abel-Ruffini theorem in characteristic zero", merged 22 November 2026.
- **What Tau Ceti is:** a library downstream of mathlib whose code is written by AIs, with human-written roadmaps. Its README says it is incubated by the Lean FRO and the Mathlib Initiative.
- **Overlap:** it proves the same converse, and one theorem even has the same name (`solvableByRad_eq_top_of_isSolvable`, with different hypotheses). Our proof was written independently, from the Galois repo, but that repo's proof is dated 25 November, three days later. So this is not a first.
- **What is different here:** this version targets mathlib itself, works when the order of the Galois group is not divisible by the characteristic (not only characteristic 0), and its Galois-extension step has no induction on the degree.
- **Mathlib still lacks the theorem.** `AbelRuffini.lean` on master still says it proves one direction, and I found no mathlib PR for the converse.

What to ask on Zulip, in your own words: whether results from Tau Ceti are meant to be upstreamed to mathlib, whether anyone is already doing that for Abel–Ruffini, and whether a PR like this one would be welcome.

Tau Ceti may also be a better home for your AI-written formalizations than mathlib, since it is built for exactly that. Its contribution rules are in https://github.com/TauCetiProject/TauCetiRoadmap.

## What the branch contains

4 files, +184/−4 lines, no new files:

- `Mathlib/FieldTheory/AbelRuffini.lean`:
  - `mem_solvableByRad_of_isSolvable_gal`: the converse. If `p.Gal` is solvable and its order is not divisible by the characteristic, every root of `p` in an algebraically closed field is solvable by radicals.
  - `isSolvable_gal_iff_forall_mem_solvableByRad` and `mem_solvableByRad_iff_isSolvable_gal_minpoly`: the two "if and only if" forms.
  - `solvableByRad_eq_top_of_isSolvable`: the Galois-extension form, given enough roots of unity.
  - `isSolvable_gal_of_forall_mem_solvableByRad`, `solvableByRad.map_mem`, `solvableByRad.restrictScalars_eq_of_le`: supporting lemmas.
- `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`: `Gal.restrictMap`, the map from the Galois group of `p` over an extension to `p.Gal`, and its injectivity.
- `Mathlib/GroupTheory/Nilpotent.lean`: `Group.IsSolvable.exists_normal_index_prime`, a nontrivial finite solvable group has a normal subgroup of prime index.
- `docs/overview.yaml`: "Abel-Ruffini theorem (one direction)" becomes "Abel-Ruffini theorem".

## Title

```text
feat(FieldTheory/AbelRuffini): the converse of the Abel-Ruffini theorem
```

## Description

```text
Prove the converse of the Abel-Ruffini theorem: if the Galois group of `p : F[X]` is solvable and its order is not divisible by the characteristic of `F` (for example in characteristic zero), then the roots of `p` in an algebraically closed field are solvable by radicals (`mem_solvableByRad_of_isSolvable_gal`). Together with the existing direction this gives `isSolvable_gal_iff_forall_mem_solvableByRad` and `mem_solvableByRad_iff_isSolvable_gal_minpoly`.

Supporting results: `solvableByRad_eq_top_of_isSolvable` (a finite Galois extension with solvable group over a field with enough roots of unity is radical), `Polynomial.Gal.restrictMap` with its injectivity, and `Group.IsSolvable.exists_normal_index_prime`.

---

Proof. Let `S = solvableByRad F E`. If `S ≠ ⊤` in a Galois extension with solvable group, `Gal(E/S)` has a normal subgroup of prime index `q`, whose fixed field `M` is cyclic of degree `q` over `S`. `S` contains a primitive `q`-th root of unity, so by `exists_root_adjoin_eq_top_of_isCyclic`, `M = S(α)` with `α ^ q ∈ S`. But `S` is closed under roots, so `α ∈ S`, a contradiction. For a polynomial, `S` is perfect, the splitting field of `p` over `S` is Galois with group embedding in `p.Gal`, and the first part applies.

Prior art: the downstream library Tau Ceti has this converse in characteristic zero (TauCeti/FieldTheory/AbelRuffini.lean, TauCetiProject/TauCeti#44963). This PR was written independently of it and differs in the hypothesis (`NeZero (Nat.card p.Gal : F)` instead of `CharZero`) and in the proof of the Galois-extension step.

`[IsAlgClosed E]` cannot be dropped: over `E = ℚ(2cos(2π/7))`, a totally real cyclic cubic, `solvableByRad ℚ E = ⊥`.

Import increase: `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed` is imported for `IsSepClosed.hasEnoughRootsOfUnity`, and it brings in `Mathlib.NumberTheory.Cyclotomic.Basic`. `AbelRuffini.lean` is imported only by the Archive file. I can replace it with a private lemma if preferred.

If smaller PRs are easier to review, this splits into three: the group lemma, the `Gal.restrictMap` lemmas, and the theorem depending on both.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's works I had made the same way, and to check them against mathlib's conventions. I have gone through the argument and can explain each step. Checked locally: the three changed modules and their direct importers build without warnings, `lake exe lint-style` and `#lint` pass.
```

After opening, post a comment containing only the line `LLM-generated` to add the label.

## Known review points

- `[NeZero (Nat.card p.Gal : F)]` as an instance argument, where a reviewer may prefer plain `[CharZero F]`.
- The group lemma sits in `Nilpotent.lean`, next to `Subgroup.isCoatom_iff_index_prime`.
- `Gal.restrictMap` overlaps with `IntermediateField.restrictRestrictAlgEquivMapHom`.
- Not run locally: the full mathlib build and `lake exe shake`. Mathlib's CI runs both.
