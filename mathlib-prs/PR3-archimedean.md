# PR 3: Archimedean ordered rings are commutative

The branch `archimedean-commutative` is pushed to your fork, with the copyright header in the name Ishan Singh. Open the PR at:

https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:archimedean-commutative?expand=1

After opening, post a comment containing only the line `LLM-generated` to add the label.

Read [NOTES-archimedean.md](NOTES-archimedean.md) first. It explains each declaration, the proof step by step, and the questions a reviewer is likely to ask.

## What the branch contains

- New file `Mathlib/Algebra/Order/Archimedean/Commutative.lean` (82 lines) and one import line in `Mathlib.lean`.
- `Archimedean.isMulCommutative`: an Archimedean linearly ordered ring is commutative.
- `Archimedean.field`: the `Field` structure on an Archimedean linearly ordered division ring (Hilbert's theorem).
- One private helper, `mul_le_mul_comm_of_pos`.

This is not a port of the proof in the Hilbert repo. The agents found a shorter argument that needs no division, so the theorem holds for rings, not only division rings.

## Title

```text
feat(Algebra/Order/Archimedean): commutativity of Archimedean ordered rings
```

## Description

```text
Prove that an Archimedean linearly ordered ring is commutative (`Archimedean.isMulCommutative`), and deduce Hilbert's theorem that an Archimedean ordered division ring is a field (`Archimedean.field`).

The proof does not use a unit, associativity or division: the statement is for `NonUnitalNonAssocRing` with `IsOrderedAddMonoid` and `PosMulMono`. For `0 < a`, if `a * b - b * a` were positive, choose `n` with `a * a < n • (a * b - b * a)` and `k : ℤ` with `0 ≤ r < a` for `r := n • b - k • a`. Then `n • (a * b - b * a) = a * r - r * a ≤ a * r ≤ a * a`, a contradiction.

---

`Archimedean.isMulCommutative` is a theorem and `Archimedean.field` an `@[instance_reducible] def`, not instances, so that they are not tried in every search for `IsMulCommutative` or `Field`. This follows `IsPGroup.isMulCommutative_of_card_eq_prime_sq` / `IsPGroup.commGroupOfCardEqPrimeSq` and `Archimedean.floorRing`.

The file is new because the proof needs `Mathlib.GroupTheory.GroupAction.Ring`, which `Archimedean/Basic.lean` does not import. I am happy to move it if there is a better place.

The statement fails for semirings with mathlib's `Archimedean`; the module docstring gives the counterexample.

I searched master for an existing version (commutativity under `Archimedean`, Hölder-type results) and found none. `Mathlib/Algebra/Order/Module/HahnEmbedding.lean` works with Archimedean ordered division rings, which by this result are fields.

AI use: I used Claude Code (Anthropic) to find and write this proof and to check it against mathlib's conventions. I have gone through the argument and can explain each step. Checked locally: the module builds without warnings, `lake exe lint-style` and `#lint` pass, `#min_imports` reports the imports minimal.
```

## Before you open it

- Wait for a first human review on your two open PRs (#46502, #46504). Mathlib's policy warns new contributors against opening several AI-assisted PRs without engaging first.
- Be ready to reproduce the key identity on paper: `n • (a * b - b * a) = a * r - r * a` for `r = n • b - k • a`.
- The points a reviewer is most likely to push on: new file or `Archimedean/Basic.lean`; theorem or instance; the weak typeclass assumptions; the Hilbert reference (§32, Theorem 38 in Townsend's translation; later German editions number differently).
