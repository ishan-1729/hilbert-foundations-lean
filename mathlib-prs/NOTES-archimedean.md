# Notes for the submitter: `Mathlib/Algebra/Order/Archimedean/Commutative.lean`

Final verification found nothing to fix; I made no edits. The file has three declarations (one private, two public). Below: what each says, why it is true, why it is stated this way, and what a reviewer may ask.

## 0. Verification record

| Check | Result |
|---|---|
| Task files | `Mathlib/Algebra/Order/Archimedean/Commutative.lean` (new, 82 lines), `Mathlib.lean` (+1 line, alphabetical between `Class` and `Defs`) |
| Build `Mathlib.Algebra.Order.Archimedean.Commutative` | OK, 1832 jobs, no warnings; direct `lean` run of the file prints nothing |
| Modules importing it | only the umbrella `Mathlib.lean`; not rebuilt (it would rebuild the other task's files) |
| `lint-style` on the module and `Mathlib` | OK |
| `#lint` on identical scratch copy (`scratch/archimedean/Draft.lean`) | 0 errors, 15 linters |
| `#min_imports` (`scratch/archimedean/MinImp.lean`) | "Imports are minimal" |
| Axioms of `Archimedean.isMulCommutative`, `Archimedean.field`, and the division-ring corollary | `propext, Classical.choice, Quot.sound` |
| Hygiene | LF only, final newline, no trailing whitespace, no tabs, no line > 100 chars, no `sorry` / `#check` / `#eval` / scratch imports; header lines 2 and 4 carry the author name |
| Duplicate search with `import Mathlib` (`scratch/archimedean/Dup.lean`) | `exact?`, `simp`, `grind`, `infer_instance` all fail on the statements: not in master |
| Review major (global instance) | resolved: it is a `theorem`; `infer_instance` fails for `IsMulCommutative D` and `Field D` (tested) |
| Hilbert reference | I checked Townsend's English translation of the 1899 text (Project Gutenberg 17384, via archive.org): §32 is "The commutative law of multiplication for an archimedean number system" and contains Theorem 38; §33 / Theorem 39 is the non-Archimedean counterexample |
| Semiring counterexample | reviewer's file `scratch/archimedean-review-math/Semiring.lean` re-run by me: compiles, standard axioms |

My scratch files: `D:/Projects/mathlib-prs/scratch/archimedean/Verify.lean`, `D:/Projects/mathlib-prs/scratch/archimedean/Dup.lean`.

## 1. `private theorem mul_le_mul_comm_of_pos`

**Statement in words.** Let `R` be a ring, possibly without unit and possibly non-associative (`NonUnitalNonAssocRing`), with a linear order such that addition is monotone (`IsOrderedAddMonoid`), left multiplication by a nonnegative element is monotone (`PosMulMono`), and the order is Archimedean. If `0 < a` then `a * b ≤ b * a` for every `b`.

**Proof, step by step.**
1. Suppose not: `b * a < a * b`, so `d := a * b - b * a > 0` (`sub_pos`).
2. Archimedean property applied to `d > 0` and the element `a * a`: there is `n : ℕ` with `a * a < n • d`. This is `exists_lt_nsmul` (the additive version of `exists_lt_pow`, `Archimedean/Defs.lean`).
3. Division with remainder of `n • b` by `a > 0`: there is `k : ℤ` with `0 ≤ r` and `r < a`, where `r := n • b - k • a`. This is `existsUnique_zsmul_near_of_pos'` (additive version of `existsUnique_zpow_near_of_one_lt'`, `Archimedean/Basic.lean`); uniqueness is discarded with `-` in the pattern.
4. Identity: `a * r = n • (a * b) - k • (a * a)` and `r * a = n • (b * a) - k • (a * a)`, so `a * r - r * a = n • (a * b) - n • (b * a) = n • d`. The `k • (a * a)` terms cancel; that is the whole trick: `a` commutes with its own multiples. In Lean: `simp [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, nsmul_sub]`. Pulling `n •` and `k •` out of a product needs no associativity or unit, only that ℕ and ℤ act compatibly with multiplication; those instances come from `Mathlib.GroupTheory.GroupAction.Ring` (reason for that import).
5. `a * r - r * a ≤ a * r` because `r * a ≥ 0` (`sub_le_self`, `mul_nonneg` with `0 ≤ r`, `0 ≤ a`).
6. `a * r ≤ a * a` because `r ≤ a` and `0 ≤ a` (`mul_le_mul_of_nonneg_left`).
7. So `n • d ≤ a * a`, contradicting step 2 (`hn.not_ge`).

**Why these assumptions.** Steps 5 and 6 are the only places where order and multiplication interact, and both are "multiply on the left by a nonnegative element" (`r * 0 ≤ r * a` and `a * r ≤ a * a`), i.e. exactly `PosMulMono`. Subtraction is needed, so a ring, not a semiring. `LinearOrder` is needed for the contradiction argument and for step 3.

**Why private, why this name.** It is only an intermediate step (the public theorem gives equality). The name follows the naming convention (`mul_le_mul_comm` for `a * b ≤ b * a`, `_of_pos` for the hypothesis). Being private, it does not occupy a root-namespace name. It was split out at a reviewer's request so the main proof is short.

## 2. `theorem Archimedean.isMulCommutative (R : Type*) [NonUnitalNonAssocRing R] [LinearOrder R] [IsOrderedAddMonoid R] [PosMulMono R] [Archimedean R] : IsMulCommutative R`

**Statement in words.** In an Archimedean linearly ordered ring (unit and associativity not required; only left multiplication by nonnegative elements assumed monotone), `a * b = b * a` for all `a, b`. `IsMulCommutative R` is mathlib's Prop-valued mixin "multiplication on `R` is commutative" (`Mathlib/Algebra/Group/Semigroup.lean`).

**Proof, step by step.**
1. For `0 < a`: the helper gives `a * b ≤ b * a`. Applied to `-b` it gives `a * (-b) ≤ (-b) * a`, i.e. `-(a * b) ≤ -(b * a)`, i.e. `b * a ≤ a * b` (`simpa`). Antisymmetry gives `a * b = b * a` (local `have comm`).
2. General `a`: trichotomy. If `a < 0`, apply step 1 to `-a > 0` and cancel the signs (`simpa`). If `a = 0`, both sides are `0` (`simp`). If `a > 0`, step 1.
3. `IsMulCommutative.of_comm` turns `∀ a b, a * b = b * a` into `IsMulCommutative R`.

**How to use it.**
- `(Archimedean.isMulCommutative R).is_comm.comm : ∀ a b : R, a * b = b * a`
- `have := Archimedean.isMulCommutative R` and then `mul_comm' a b`
- for a unital ring, additionally `open scoped IsMulCommutative` to get `CommRing R` by instance search (tested).
- The task's target statement (`[DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D] [Archimedean D] : ∀ a b : D, a * b = b * a`) is the first bullet with `R := D`; `IsStrictOrderedRing` supplies `IsOrderedAddMonoid` and `PosMulMono` by instance (tested in `Verify.lean` and `Test.lean`).

**Why stated this way.**
- Conclusion `IsMulCommutative R` and not `∀ a b, a * b = b * a` or `CommRing R`: this is the current mathlib idiom (see `IsPGroup.isMulCommutative_of_card_eq_prime_sq`, whose older `∀ a b` form was deprecated in May 2026), and it works for every ring class at once through the scoped bundling instances in `Mathlib/Algebra/Ring/Defs.lean`.
- Name: `Archimedean.` namespace like `Archimedean.floorRing`; `isMulCommutative` is the conclusion.
- `R` explicit: there is no hypothesis from which `R` could be inferred, and it is used as `have := Archimedean.isMulCommutative R`.
- Mixins `IsOrderedAddMonoid` + `PosMulMono` instead of `IsOrderedRing`: `IsOrderedRing` needs a `Semiring` (unit), so the mixins are the only way to include non-unital rings; for unital rings they follow from `IsOrderedRing`/`IsStrictOrderedRing` by instance.

## 3. `@[instance_reducible] def Archimedean.field (K : Type*) [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K] : Field K`

**Statement in words.** An Archimedean linearly ordered division ring is a field (Hilbert, Grundlagen §32, Theorem 38). This is data: the `Field` structure whose operations are those of the given `DivisionRing` and whose extra axiom `mul_comm` comes from the theorem above.

**Proof/construction.** `where mul_comm := (Archimedean.isMulCommutative K).is_comm.comm`; all other fields are filled from the `DivisionRing K` instance by the structure-instance elaborator. Checked: `(Archimedean.field D).toDivisionRing = inst` holds by `with_reducible_and_instances rfl`, also from another `module` file (so the body is exposed), and if `D` is already a `Field` then `Archimedean.field D = inst` by the same `rfl` (no diamond).

**Why stated this way.**
- A `def`, not an instance: as an instance it would make every `Field` search look for an order and an `Archimedean` instance. Same pattern as `Archimedean.floorRing` and `littleWedderburn`.
- `@[instance_reducible]`: required for defs that are used as instances via `let := ...` so they unfold at instance transparency; `Archimedean.floorRing` and `IsPGroup.commGroupOfCardEqPrimeSq` carry the same attribute.
- `IsOrderedRing K` (bundled) rather than the mixins: for a unital ring it is the standard hypothesis and `IsStrictOrderedRing` implies it by instance.
- Usage: `let := Archimedean.field D`, after which `field_simp`, `mul_comm` etc. work (tested).

## 4. Module docstring and header

- Says what is proved, that the proof is not Hilbert's, lists the two public declarations, and has one paragraph on why there is no semiring version (see Q3 below). The reference line is free-form: `D. Hilbert, _Grundlagen der Geometrie_, Teubner, 1899, §32`.
- `set_option doc.verso true` / `doc.verso.suggestions false` and `@[expose] public section` match `Archimedean/Basic.lean`; `Field.Defs` and `Archimedean.Defs` are `public import` because `Field` and `Archimedean` occur in public statements, the other two imports are only used in proofs.

## 5. Questions a reviewer may ask

**Q1. Why is this not an instance?** Its conclusion `IsMulCommutative R` matches every type, so it would run a ring-and-order search on every failing `IsMulCommutative` query (subgroups, `Subgroup.Normal`, ...). A draft reviewer measured +19% to +37% heartbeats on such failing queries under `import Mathlib`. Master made a comparable instance a theorem in #45864, and `Mathlib/Algebra/Group/Defs.lean:114` records a deliberately omitted `IsMulCommutative` instance. I did not re-run those benchmarks.

**Q2. Why not get it from an embedding into ℝ?** Mathlib has `Archimedean.embedReal` only as an ordered additive group hom; the ring version was #27566, closed unmerged. That route needs a unit, strict order and `Data/Real`; the direct proof is about 12 lines, lives in `Algebra/Order`, and covers non-unital rings.

**Q3. Does it hold for semirings?** No, with mathlib's definition of `Archimedean` (`∀ x, ∀ y > 0, ∃ n, x ≤ n • y`). In a non-commutative linearly ordered division ring `A`, the set `S = {0} ∪ {a | 1 ≤ a ≤ n for some n : ℕ}` is closed under `+` and `*`, is Archimedean (if `y ∈ S`, `y > 0` then `y ≥ 1`, so `x ≤ n ≤ n • y`), and is not commutative: if `x y ≠ y x` in `A`, then `1 + (1 + |x|)⁻¹` and `1 + (1 + |y|)⁻¹` lie in `S` (both are in `[1, 2]`) and do not commute. Non-commutative ordered division rings exist (Hilbert §33, Theorem 39). The reduction is Lean-checked in `D:/Projects/mathlib-prs/scratch/archimedean-review-math/Semiring.lean`; it is not part of the PR. If a reviewer dislikes an unformalised remark in a docstring, delete that paragraph (lines 25-27).

**Q4. Is `Archimedean` necessary? `LinearOrder`?** Yes: Hilbert's §33 gives a non-commutative, non-Archimedean ordered division ring. With only a partial order the claim is false (any ring with the discrete order is vacuously ordered and Archimedean).

**Q5. Why only `PosMulMono`; what about `MulPosMono`?** The proof uses left multiplication only. The mirror statement (right multiplication only) holds by the same proof in the opposite ring; it was not added to keep the PR small. With `IsOrderedRing` both hold anyway.

**Q6. Why a new file?** The statement of `Archimedean.field` needs `Mathlib.Algebra.Field.Defs` and the proof needs `Mathlib.GroupTheory.GroupAction.Ring`; a draft reviewer checked that the proof cannot go into `Archimedean/Basic.lean` without new imports there (I did not re-check this). If a maintainer prefers `Basic.lean`, moving the three declarations is mechanical.

**Q7. Why `Archimedean.field` and not a general `DivisionRing + IsMulCommutative → Field` instance?** That scoped instance does not exist on master (ring analogues: `Mathlib/Algebra/Ring/Defs.lean`, namespace `IsMulCommutative`). It belongs in `Mathlib/Algebra/Field/Defs.lean` as a separate small PR; offer it. Until then `Archimedean.field` is the named entry point, parallel to `IsPGroup.commGroupOfCardEqPrimeSq`.

**Q8. Is this Hilbert's proof?** No. Hilbert estimates `ab - ba` using integer parts and division. The proof here uses one Euclidean division `n • b = k • a + r` and the identity `n • (ab - ba) = ar - ra`, so no inverses are needed. The source repo's port of Hilbert's estimates (`HilbertFoundations/NonPascalAux.lean`) was not used.

**Q9. Why `(Archimedean.isMulCommutative K).is_comm.comm`?** `IsMulCommutative` has the single field `is_comm : Std.Commutative (· * ·)`, whose field `comm` is `∀ a b, a * b = b * a`. Same spelling as `Mathlib/GroupTheory/PGroup.lean:572`.

**Q10. Universe polymorphism / computability?** `Type*` everywhere; `Archimedean.field` is computable (no `noncomputable` needed).

## 6. Before opening the PR

- The copyright header (lines 2 and 4 of the new file) carries the name Ishan Singh.
- Branch must contain only the new file and the one `Mathlib.lean` line.
- CI will run the full build, `mk_all` and `shake` checks that were not run here.
- Follow mathlib's current AI-use disclosure rules in the PR description; that statement is yours to write.