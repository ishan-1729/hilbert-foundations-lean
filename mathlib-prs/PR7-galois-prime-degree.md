# PR 7: Galois's criterion in prime degree (three PRs)

**Status:** all three branches are pushed; no PR is opened.

For a group acting faithfully and transitively on a set with a prime number `p` of elements: the group is solvable if and only if it has a normal subgroup of order `p`, if and only if no element other than the identity fixes two points (7.1). For an irreducible polynomial of prime degree this gives: its Galois group is solvable if and only if any two of its roots generate the splitting field (7.2). Mathlib has none of this. Tau Ceti has the criterion for `p = 5` only.

Read [NOTES-galois-prime-degree.md](NOTES-galois-prime-degree.md) before opening anything.

## The three PRs

| # | Branch | Adds | Lines | Depends on |
|---|---|---|---|---|
| 7.1 | `galois-prime-degree-group` | Galois's criterion for groups: solvable if and only if no non-identity element fixes two points | +230 | nothing |
| 7.2 | `galois-prime-degree-polynomial` | Galois's criterion for equations: solvable if and only if any two roots generate the splitting field | +179 | 7.1 |
| 7.3 | `galois-prime-degree-affine` | optional: solvable if and only if the group acts by maps `k ↦ a * k + b` of `ZMod p` | +85 | 7.1 |

- Open 7.1 first. 7.2 and 7.3 each contain the commit of 7.1, and each needs the line `- [ ] depends on: #NNNN` with the number of 7.1 in its description.
- 7.3 is optional. A reviewer may ask for its statement to go through mathlib's `AffineEquiv`; open it only if you want that discussion.
- After opening each PR, post a comment containing only the line `LLM-generated`.

## 7.1 `galois-prime-degree-group`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:galois-prime-degree-group?expand=1

Title:

```text
feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree
```

Description (draft; put it in your own words where you can):

```text
New file Mathlib/GroupTheory/GroupAction/PrimeDegree.lean (229 lines in this PR) and one line in Mathlib.lean (`public import Mathlib.GroupTheory.GroupAction.PrimeDegree`, between GroupAction.Pointwise and GroupAction.Primitive). Two public theorems, for a group G acting faithfully and transitively on a type X with (Nat.card X).Prime:
- MulAction.isSolvable_iff_exists_normal_card_eq_of_prime_card : Group.IsSolvable G ↔ ∃ N : Subgroup G, N.Normal ∧ Nat.card N = Nat.card X
- MulAction.isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card (Galois's criterion) : Group.IsSolvable G ↔ ∀ g : G, g ≠ 1 → (fixedBy X g).Subsingleton
Plus 11 private lemmas (list in the notes).

Proof route. Everything goes through a normal subgroup N of order p.
- solvable ⇒ N exists: well-founded induction replacing a nontrivial normal subgroup H by ⁅H, H⁆ (Group.IsSolvable.commutator_lt_of_ne_bot) until it is commutative; a nontrivial normal subgroup is transitive (the action is primitive by MulAction.IsPreprimitive.of_prime_card, then IsQuasiPreprimitive.isPretransitive_of_normal); a commutative transitive subgroup acts freely, so it has p elements.
- N exists ⇒ solvable: N is cyclic and equal to its centralizer, so the conjugation map G → MulAut N (MulAut.conjNormal) has kernel inside N and commutative target (IsCyclic.mulAutMulEquiv); conclude with Group.isSolvable_of_ker_le_range.
- N exists ⇒ only 1 fixes two points: if g fixes x and n • x with n ∈ N, then g n g⁻¹ = n, so g centralizes N = ⟨n⟩ and fixes a point, so g = 1.
- only 1 fixes two points ⇒ N exists: a point stabilizer has fewer than p elements, so a subgroup Q of order p (Sylow.exists_subgroup_card_pow_prime) has index < p; the number of Sylow p-subgroups is ≡ 1 mod p and divides that index, so it is 1 and Q is normal.

Design decisions. Stated for an arbitrary MulAction with FaithfulSMul and IsPretransitive (not only subgroups of Equiv.Perm); no Finite/Fintype hypothesis (finiteness of X and G follows from primality of Nat.card X and faithfulness); hypothesis (hp : (Nat.card X).Prime) as in MulAction.IsPreprimitive.of_prime_card; right-hand side written with MulAction.fixedBy and Set.Subsingleton; all helpers private. Module-system file: public imports only for what the statements mention, plain imports for proof-only dependencies (Primitive, Cyclic, Sylow), `public section`.

Prior art. Mathlib master (643371581c): nothing on solvable transitive groups of prime degree (searched; the only prime-degree Galois result is Polynomial.Gal.galActionHom_bijective_of_prime_degree, about S_p). Open mathlib PRs: about 28 `gh search prs` queries, nothing overlapping. Tau Ceti: the criterion exists only for p = 5 (via the classification of transitive subgroups of S₅); the general-p statement is absent. Private helpers that have Tau Ceti counterparts: eq_one_of_mem_centralizer and isCancelSMul_of_isMulCommutative (TauCeti GroupTheory/Perm/Centralizer.lean, stated there for subgroups of Equiv.Perm), isPretransitive_of_normal (TauCeti IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot). No minimal-normal-subgroup API, no prime-index lemma, no named AGL(1, p).

Checked locally. `lake build` of the module: OK, no warnings (trace log empty). `lake exe lint-style` on the module: OK. `#lint` (15 environment linters): 0 errors. `#print axioms` of both theorems: propext, Classical.choice, Quot.sound. Both statements restated verbatim in a scratch file with explicit universes u, v and proved by the theorems. Examples that compile: S₃ solvable via the criterion; S_p not solvable for p ≥ 5; A₅ not solvable; an element of a solvable transitive group of degree 7 fixing 0 and 1 is 1; any faithful transitive group of degree 2 is solvable. Hygiene: copyright header Ishan Singh, LF, final newline, no trailing whitespace, longest line 98, no sorry / set_option / debug commands.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's works that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 7.2 `galois-prime-degree-polynomial`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:galois-prime-degree-polynomial?expand=1

Title:

```text
feat(FieldTheory/Galois/PrimeDegree): solvability of irreducible polynomials of prime degree
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 7.1)

New file Mathlib/FieldTheory/Galois/PrimeDegree.lean (169 lines), one line in Mathlib.lean (`public import Mathlib.FieldTheory.Galois.PrimeDegree`, between Galois.Notation and Galois.Profinite), and the bib entry `galois1846` in docs/references.bib (8 lines + blank). Two public theorems for an irreducible f : F[X] with f.natDegree.Prime (no separability hypothesis):
- Polynomial.Gal.isSolvable_iff_forall_adjoin_pair_eq_top_of_prime_degree [f.IsSplittingField F E] : Group.IsSolvable f.Gal ↔ ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, x ≠ y → F⟮x, y⟯ = ⊤
- Polynomial.Gal.isSolvable_iff_forall_rootSet_subset_adjoin_pair_of_prime_degree (hE : (f.map (algebraMap F E)).Splits) : Group.IsSolvable f.Gal ↔ ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, x ≠ y → f.rootSet E ⊆ F⟮x, y⟯
Plus 5 private lemmas.

Proof route. Solvability is transported from f.Gal to Gal(E/F) along (IsSplittingField.algEquiv E f).autCongr. Separable case: Gal(E/F) acts faithfully and transitively on the p roots of f in E, so the group criterion of the previous PR (MulAction.isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card) applies; 'only 1 fixes x and y' is translated into F⟮x, y⟯ = ⊤ by the Galois correspondence (IsGalois.fixedField_eq_iff_fixingSubgroup_eq and IntermediateField.forall_mem_adjoin_smul_eq_self_iff). Inseparable case: natSepDegree divides the prime degree and is not equal to it, so f has one root, Gal(E/F) is trivial and both sides hold. The second theorem applies the first to K = adjoin F (f.rootSet E) (a splitting field by IntermediateField.adjoin_rootSet_isSplittingField) and lifts F⟮x, y⟯ = ⊤ in K to an inclusion in E (lift_adjoin, adjoin_le_iff).

Design decisions. The left side is about f.Gal, as in mathlib's solvability API (gal_X_pow_sub_C_isSolvable, solvableByRad.isSolvable); E is any splitting field in the first theorem (in particular f.SplittingField) and any extension where f splits in the second (e.g. ℂ over ℚ). The group criterion is applied to Gal(E/F), not to f.Gal acting through Polynomial.Gal.galAction, because the Galois correspondence is stated for Gal(E/F) (this is said in the implementation notes). Transitivity on the roots is NOT re-proved: it is derived from mathlib's Polynomial.Gal.galAction_isPretransitive through restrict_surjective and restrict_smul. The module docstring says that 'solvable' refers to the Galois group and that solvability by radicals is not treated. All helpers are private.

Prior art. Mathlib master: no equation form of the criterion; uses existing API (galAction_isPretransitive, restrict_surjective, restrict_smul, forall_mem_adjoin_smul_eq_self_iff, natSepDegree lemmas). mathlib has no MulEquiv.isSolvable_congr (grep on master), hence the 3-line transport `he`. Open mathlib PRs: `gh search prs`, nothing overlapping. Tau Ceti: equation form absent for general p (it has quintic-specific criteria via resolvents and labels); it has TauCeti.isPretransitive_rootSet_of_irreducible (ours is a private corollary of the mathlib lemma, for a splitting field only) and MulEquiv.isSolvable_congr (not added here).

Dependency. Needs the group-form PR only (one theorem). Independent of the affine-form PR: checked that the file uses nothing from the affine section and that the public import ZMod.Defs dropped in the PR-1 cut is already in the public import closure of Mathlib.FieldTheory.PolynomialGaloisGroup.

Checked locally. `lake build` of the module: OK, no warnings. `lake exe lint-style`: OK. `#lint`: 0 errors. `#print axioms` of both theorems: propext, Classical.choice, Quot.sound. Both statements restated verbatim in a scratch file with explicit universes and proved by the theorems; pointwise corollary (roots x ≠ y, z of f in E, f.Gal solvable ⟹ z ∈ F⟮x, y⟯) compiles. Authors' examples re-run: E = f.SplittingField; X^p - a irreducible ⟹ two distinct p-th roots of a generate the splitting field; every complex cube root of 2 lies in ℚ⟮x, y⟯ for two distinct ones; an irreducible rational polynomial of prime degree ≥ 5 with exactly two non-real roots has two roots that do not generate the others. Hygiene: header, LF, final newline, no trailing whitespace, longest line 99.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's works that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## 7.3 `galois-prime-degree-affine`

Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:galois-prime-degree-affine?expand=1

Title:

```text
feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree act by affine maps of `ZMod p`
```

Description (draft; put it in your own words where you can):

```text
- [ ] depends on: #NNNN  (replace NNNN with the number of PR 7.1)

85 lines appended to Mathlib/GroupTheory/GroupAction/PrimeDegree.lean (the file created by the group-form PR): three imports (public Mathlib.Data.ZMod.Defs; Mathlib.Algebra.Field.ZMod; Mathlib.Tactic.LinearCombination), a third bullet in the module docstring, and the section 'The affine form of the criterion' with one public theorem and two private lemmas.
- MulAction.isSolvable_iff_exists_equiv_zmod_of_prime_card {p : ℕ} [Fact p.Prime] (hX : Nat.card X = p) : Group.IsSolvable G ↔ ∃ e : X ≃ ZMod p, ∀ g : G, ∃ a b : ZMod p, ∀ x, e (g • x) = a * e x + b
(G acting faithfully and transitively on X.)

Proof route. →: take the normal subgroup N of order p from the group-form PR, a generator n of N and a base point x₀; k ↦ n ^ k.val • x₀ is a bijection ZMod p → X (N acts freely); for g ∈ G, g n g⁻¹ = n ^ a and g • x₀ = n ^ b • x₀, hence g • (n ^ k • x₀) = n ^ (a k + b) • x₀. ←: an affine map of ZMod p with two fixed points is the identity ((a - 1)(e x - e y) = 0 in a field), so only 1 fixes two points, and Galois's criterion applies.

Design decisions. Elementary statement with `∃ a b`, without a named affine group and without units: `a ≠ 0` is automatic (the docstring says so) and the weaker right-hand side makes the ← direction easier to apply (one just supplies a and b). Hypothesis shape `{p} [Fact p.Prime] (hX : Nat.card X = p)` as in mathlib's `isCyclic_of_prime_card`, so that `ZMod p` appears with the user's numeral (usable as `(Nat.card_zmod 5)` or `(Nat.card_fin 3)`). In the same file as the group form because it uses its private lemmas.

Prior art. Mathlib master: no such statement; mathlib's affine group of ZMod p would be `ZMod p ≃ᵃ[ZMod p] ZMod p` (AffineEquiv), not used here. Tau Ceti has a named `AffineGroup` (AGL(1, K)) with basic properties, but not this theorem; no named group is introduced here. Open mathlib PRs: nothing found.

Checked locally. Module build OK without warnings, lint-style OK, #lint 0 errors, axioms propext / Classical.choice / Quot.sound, statement restated verbatim with explicit universes. Examples re-run: S₃ acts on Fin 3 by affine maps of ZMod 3 (→ direction); the group of affine permutations of ZMod 5 is solvable by the ← direction with e = Equiv.refl, then fed back through the fixed-point criterion.

AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of Galois's works that I had made the same way, and to check them against mathlib's conventions. I have gone through each proof and can explain every step.
```

## What was checked

- Both modules build without warnings, the style linter and `#lint` pass, and the main theorems use only the standard axioms.
- The 7.1 version of the group file (without the affine section) was built and linted as a module, with the 7.2 file on top of it.
- A mathematical review tested the statements on `S₃`, the affine group of `ZMod 5`, `A₅`, and `X³ − 2`; it found no error.
- Not done: the full mathlib build, `lake exe mk_all --check`, `lake exe shake`, `bibtool` on the new bibliography entry. Mathlib CI runs these.

## Points to know before review

- Several general lemmas are private on purpose, because Tau Ceti has public versions of three of them (a centralizing element that fixes a point is 1; a commutative transitive subgroup acts freely; a nontrivial normal subgroup of a primitive group is transitive). A reviewer may ask to make them public. That is your call, case by case; the notes list them.
- 7.2 is about solvability of the Galois group, not solvability by radicals. The module docstring says so. Calling it "Galois's criterion (Proposition VIII)" may draw a comment.
- Not checked against the sources: the section number in the citation of Wielandt's *Finite permutation groups* (§11), and the page range 417-433 of the new bibliography entry `galois1846`.
- The hypotheses have two shapes: `(hp : (Nat.card X).Prime)` in 7.1 and `{p} [Fact p.Prime] (hX : Nat.card X = p)` in 7.3. The notes explain why.

