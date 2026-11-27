# Notes for the submitter: converse of Abel-Ruffini

Everything below was re-checked on the working tree (branch `wip-contrib` = master 643371581c + uncommitted changes). I changed no mathlib file in this pass.

## 0. Read this first

1. **Prior art exists in TauCeti (confirmed by me with `gh api`).** `github.com/TauCetiProject/TauCeti` (Apache-2.0, created 2026-06-02) has `TauCeti/FieldTheory/AbelRuffini.lean` (16 kB) from PR #44963 by `Hugo-Polloli`, title "[Merged by Bors] - feat(FieldTheory/AbelRuffini): the converse of the Abel-Ruffini theorem in characteristic zero". I looked only at its declaration headers: `solvableByRad.map_le_of_algHom`, `solvableByRad.restrictScalars_eq`, `Irreducible.forall_rootSet_mem_solvableByRad`, `IsPrimitiveRoot.isSeparable_of_finrank_dvd`, `TauCeti.solvableByRad_eq_top_of_isSolvable` (same name as ours; different hypotheses: `[Normal K L]`, a primitive `n`-th root with `finrank K L ∣ n`), `AlgHom.fieldRange_le_solvableByRad`, `isSolvable_iff_forall_mem_solvableByRad [CharZero F]`, `isSolvable_gal_iff_forall_rootSet_mem_solvableByRad [CharZero F]`. Your local source (`galois-oeuvres-lean`, only commit touching Radicaux*.lean is dated 2026-11-25) is later than that PR, so you cannot claim priority. Before opening a PR: read the TauCeti file, cite it, do not call the proof new, and ask (Zulip / TauCeti repo) whether they plan to upstream it.
2. **Mathlib requires you to disclose AI assistance** in the PR description and to be able to defend every line. These notes are for that.
3. When you commit, add only the four files of this task. `Mathlib.lean` and `Mathlib/Algebra/Order/Archimedean/Commutative.lean` in the working tree belong to another task.

## 1. `Group.IsSolvable.exists_normal_index_prime` (Mathlib/GroupTheory/Nilpotent.lean)

**Statement.** `(G) [Group G] [IsCoatomic (Subgroup G)] [Nontrivial G] [Group.IsSolvable G] : ∃ H : Subgroup G, H.Normal ∧ H.index.Prime`. A nontrivial solvable group in which every proper subgroup lies in a maximal subgroup (e.g. any finite group) has a normal subgroup of prime index. `@[to_additive]` generates `AddGroup.IsSolvable.exists_normal_index_prime`.

**Proof.**
1. `G` nontrivial solvable ⟹ `commutator G < ⊤` (`Group.IsSolvable.commutator_lt_top_of_nontrivial`).
2. Coatomic: a subgroup `≠ ⊤` lies below a coatom `H` (`eq_top_or_exists_le_coatom`).
3. `commutator G ≤ H` ⟹ `H` normal (`Subgroup.Normal.of_commutator_le`) and `G ⧸ H` commutative (`quotient_commutative_iff_commutator_le`).
4. `H` a normal coatom ⟹ `G ⧸ H` simple (`Group.isSimpleGroup_of_isCoatom`).
5. A commutative simple group has prime order (`Group.is_simple_iff_prime_card`); `H.index = Nat.card (G ⧸ H)`.

**Why this form.** `IsCoatomic (Subgroup G)` is all the proof uses, and neighbours use it (`isCyclic_of_isCoatom_subsingleton`, `frattini_nongenerating`, the `IsPGroup` lemma just below); `Finite G` provides it by instance. `G` explicit because it cannot be inferred from the conclusion. Placed in Nilpotent.lean because the sibling `Subgroup.isCoatom_iff_index_prime` (same last two lines) is there and no import is needed; Solvable.lean lacks `QuotientGroup.Simple`.

**Reviewer questions.**
- *Why Nilpotent.lean for a solvable-group lemma?* Imports and the sibling lemma; happy to move if a better home is named.
- *Order of the conjuncts?* `Group.IsNilpotent.exists_normal_index_eq_of_dvd_card` has `index = k ∧ Normal`; flipping ours is a trivial change.
- *Is the `have := ...quotient_commutative_iff_commutator_le.mpr hle` line needed?* Yes, it supplies the commutativity instance used by `is_simple_iff_prime_card`.

## 2. `Polynomial.Gal.splits_in_splittingField_map`, `restrictMap`, `restrictMap_injective` (Mathlib/FieldTheory/PolynomialGaloisGroup.lean)

**Statements.** For `p : F[X]` and a field extension `E/F`, write `L` for the splitting field of `p.map (algebraMap F E)` over `E`.
- `splits_in_splittingField_map p E`: `p` (mapped from `F`) splits in `L`.
- `restrictMap p E : (p.map (algebraMap F E)).Gal →* p.Gal`: an `E`-automorphism of `L` is in particular an `F`-automorphism of `L`, and it restricts to the splitting field of `p` over `F` (which embeds in `L`).
- `restrictMap_injective p E`: this map is injective. "The Galois group of `p` over a bigger field is a subgroup of the Galois group over `F`."

**Proofs.**
- Splits: `SplittingField.splits (p.map (algebraMap F E))` says `(p.map (F→E)).map (E→L)` splits; `map_map` and `IsScalarTower.algebraMap_eq` rewrite the composite `F→E→L` as `algebraMap F L`.
- Definition: `Gal.restrict p L` (existing; needs `Fact (p splits in L)`) composed with `AlgEquiv.restrictScalarsHom F : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L)`. Same `let h : Fact ...` pattern as `restrictComp` just above.
- Injective: suppose `σ ↦ 1`. An element of a polynomial Galois group is determined by its action on the roots in the splitting field (`Gal.ext`). The roots of `p.map (F→E)` in `L` are the roots of `p` in `L` (`rootSet_map`). `restrict_smul` says `σ` acts on a root `x` of `p` in `L` as `restrict p L σ` acts on the corresponding root in `p.SplittingField`; that is the identity, so `σ x = x`.

**Reviewer questions.**
- *Isn't this `IntermediateField.restrictRestrictAlgEquivMapHom`?* Yes, definitionally (checked by `rfl` by a reviewer), but the only injectivity lemma for it needs two intermediate fields of one field with `K ⊔ L = ⊤`, which is not our situation. Generalising that lemma would be a separate PR.
- *No lemma describing the action of `restrictMap`?* Only injectivity is needed; a `restrictMap_smul` could be added on request.
- *Why E explicit?* Same convention as `restrict p E`.

## 3. `solvableByRad.map_mem` (AbelRuffini.lean)

**Statement.** `(f : E →ₐ[F] K) (hx : x ∈ solvableByRad F E) : f x ∈ solvableByRad F K`.

**Proof.** `solvableByRad F E` is by definition the smallest intermediate field closed under taking `n`-th roots (`solvableByRad_le`). The preimage `(solvableByRad F K).comap f` is such a field: if `y^n` is in it, then `(f y)^n = f (y^n) ∈ solvableByRad F K`, so `f y ∈ solvableByRad F K` by `rad_mem`.

**Q.** *Why not `(solvableByRad F E).map f ≤ solvableByRad F K`?* Equivalent; the element form is what is used. (TauCeti has the `map_le` form.)

## 4. `solvableByRad.restrictScalars_eq_of_le`

**Statement.** If the intermediate field `M` of `E/F` satisfies `M ≤ solvableByRad F E`, then `(solvableByRad M E).restrictScalars F = solvableByRad F E`: radicals over `M` are radicals over `F`.

**Proof.** `≤`: `solvableByRad F E`, viewed as an intermediate field of `E/M` (`IntermediateField.extendScalars hM`), is closed under roots, so it contains `solvableByRad M E`. `≥`: `solvableByRad M E` viewed over `F` is closed under roots, so it contains `solvableByRad F E`.

**Q.** *Only used once with `le_rfl`?* Yes (with `M = solvableByRad F E`); stated as an equality because a one-sided `mem_of_le` was judged a misleading name by review.

## 5. `isSolvable_gal_of_forall_mem_solvableByRad`

**Statement.** `[IsAlgClosed E] {p : F[X]} (h : ∀ x ∈ p.rootSet E, x ∈ solvableByRad F E) : IsSolvable p.Gal`. Abel-Ruffini for a not necessarily irreducible polynomial; no characteristic assumption.

**Proof.** Induction on the factorisation (`WfDvdMonoid.induction_on_irreducible`): `p = 0` and `p` a unit (a constant) have trivial Galois group. For `q * p` with `q` irreducible and `p ≠ 0`: `q` has a root `x` in `E` (algebraically closed), it is a root of `q * p`, hence solvable by radicals, so `q.Gal` is solvable by the existing `isSolvable_gal_of_irreducible`; the roots of `p` are roots of `q * p`, so `p.Gal` is solvable by induction; conclude with the existing `gal_mul_isSolvable`.

**Q.** *Why `IsAlgClosed`?* Only to have a root of each irreducible factor in `E`; it is the form needed for the iff.

## 6. `solvableByRad_eq_top_of_isSolvable`

**Statement.** `[FiniteDimensional F E] [IsGalois F E] [IsSolvable Gal(E/F)] (hζ : (primitiveRoots (finrank F E) F).Nonempty) : solvableByRad F E = ⊤`. A finite Galois extension with solvable group over a base containing a primitive `[E:F]`-th root of unity is radical. Any characteristic.

**Proof.** Put `S = solvableByRad F E` and assume `S ≠ ⊤`.
1. `Gal(E/S)` is a subgroup of `Gal(E/F)` (`AlgEquiv.restrictScalarsHom_injective`), so solvable.
2. `|Gal(E/S)| = [E:S]` (`IsGalois.card_aut_eq_finrank`), and `[E:S] ≠ 1` because `S ≠ ⊤` (`finrank_eq_one_iff_eq_top`), so the group is nontrivial.
3. Section 1 gives `N` normal in `Gal(E/S)` of prime index. `M := fixedField N`. By the Galois correspondence `[M:S] = N.index` (`finrank_eq_fixingSubgroup_index`, `fixingSubgroup_fixedField`), a prime `q`; `M/S` is Galois since `N` is normal; a group of prime order is cyclic (`isCyclic_of_prime_card`).
4. Roots of unity: `[E:F] = ([S:F]·[E:M])·[M:S]` (tower law, `finrank_mul_finrank` twice), so if `ζ` is primitive of order `[E:F]`, then `ζ^([S:F]·[E:M])` is primitive of order `q` (`IsPrimitiveRoot.pow`), and stays primitive in `S` (`map_of_injective`).
5. Kummer (`exists_root_adjoin_eq_top_of_isCyclic S M`): there is `α ∈ M` with `α^q ∈ S` and `S(α) = M`.
6. `S` is closed under roots (`rad_mem`), so `α ∈ S`, hence `S(α) = ⊥`, so `⊥ = ⊤` among intermediate fields of `M/S`, i.e. `[M:S] = 1` (`bot_eq_top_iff_finrank_eq_one`). Contradiction with `q` prime.

**Reviewer questions.**
- *Hypothesis too strong (only prime orders are used)?* True; kept in the shape of `exists_root_adjoin_eq_top_of_isCyclic`. The weaker "for all primes `q ∣ finrank F E`" version was verified by a reviewer and is a small change if requested.
- *`[FiniteDimensional F E]` redundant?* It follows from `hζ` (`primitiveRoots 0 F = ∅`), kept for readability and parity with the Kummer lemma.
- *Why no induction?* The minimal-counterexample argument on the field `S` itself replaces the induction on the degree in your source file, and also removes the same-universe restriction.

## 7. `mem_solvableByRad_of_isSolvable_gal` (the converse)

**Statement.** `[IsAlgClosed E] {p : F[X]} [NeZero (Nat.card p.Gal : F)] (hp : IsSolvable p.Gal) {x : E} (hx : x ∈ p.rootSet E) : x ∈ solvableByRad F E`. If `p.Gal` is solvable and the characteristic of `F` does not divide `|p.Gal|` (automatic in characteristic 0), every root of `p` in an algebraically closed extension `E` is solvable by radicals over `F`.

**Proof.** `S := solvableByRad F E`.
1. `S` is perfect: let `q` be its exponential characteristic. Any `a ∈ S` has a `q`-th root `b` in `E` (`IsAlgClosed.exists_pow_nat_eq`), and `b ∈ S` by `rad_mem`. So Frobenius is surjective (`PerfectRing.ofSurjective`), `S` is a perfect field.
2. `K :=` splitting field of `p` over `S`. Normal (splitting field) and separable (perfect base), so `IsGalois S K` (`⟨⟩`: both fields by instance).
3. `Gal(K/S) = (p.map _).Gal` embeds in `p.Gal` (section 2). Hence solvable, and `[K:S] = |Gal(K/S)|` divides `|p.Gal|` (`Subgroup.card_dvd_of_injective`): `|p.Gal| = [K:S]·k`.
4. `|p.Gal| ≠ 0` in `E` (transport `NeZero` along the injective `F → E`), so `E` has a primitive root `ζ` of order `|p.Gal|` (instance `IsSepClosed.hasEnoughRootsOfUnity`, `HasEnoughRootsOfUnity.exists_isPrimitiveRoot`). `ζ^k` is primitive of order `[K:S]` and `(ζ^k)^[K:S] = 1 ∈ S`, so `ζ^k ∈ S`.
5. Section 6 for `K/S`: `solvableByRad S K = ⊤`.
6. `φ : K →ₐ[S] E` (`IsAlgClosed.lift`). Since `p` splits in `K`, the roots of `p` in `E` are the images of its roots in `K` (`Splits.image_rootSet`), so `x = φ y`. `y ∈ solvableByRad S K`, so `x ∈ solvableByRad S E` (section 3), and `solvableByRad S E ≤ solvableByRad F E` (section 4 with `M = S`).

**Reviewer questions.**
- *Why `IsAlgClosed E`?* Without enough radicals in `E` the statement is false: `E = ℚ(2cos(2π/7))` is a cyclic cubic, totally real field; if `y ∈ E \ ℚ` had `y^n ∈ ℚ`, its three conjugates would be real numbers of the form `y·(root of unity)`, i.e. only `±y`; so `ℚ` is closed under roots in `E` and `solvableByRad ℚ E = ⊥`. In characteristic zero "`p` splits in `E` and `E` has a primitive `|p.Gal|`-th root of unity" would suffice (verified by a reviewer, scratch `abel-ruffini-review-math/Test3.lean`); not included to keep one statement.
- *Why `NeZero (Nat.card p.Gal : F)` and not `CharZero F`?* It is exactly what step 4 needs, covers positive characteristic, and `CharZero` users get it by instance search (tested). Some condition is necessary: Artin-Schreier extensions (cyclic of degree `p` in characteristic `p`) are not radical. Precedent for such an instance argument: Maschke's theorem (`Mathlib/RepresentationTheory/Maschke.lean`). If a reviewer prefers `[CharZero F]`: replace step 1 by `have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective` and drop the divisibility bookkeeping.
- *Why the heavy import `RootsOfUnity.AlgebraicallyClosed`?* It holds the existing instance giving primitive roots in separably closed fields; it imports `NumberTheory.Cyclotomic.Basic`, raising the transitive imports of this leaf file from 3841 to 4626 modules. The alternative is an 8-line private lemma re-proving part of that instance (scratch `abel-ruffini-review-style/AR2.lean`, char-zero form), or a preliminary PR making that file lighter.
- *Inseparable `p`?* Fine: `S` is perfect, and e.g. for `X^p - t` over `𝔽_p(t)` the group is trivial and the root is a `p`-th root.

## 8. `isSolvable_gal_iff_forall_mem_solvableByRad`

**Statement.** Same hypotheses as section 7: `IsSolvable p.Gal ↔ ∀ x ∈ p.rootSet E, x ∈ solvableByRad F E`. **Proof.** Sections 7 and 5. This is the shape used by lean-eval and TauCeti (with `E = AlgebraicClosure F`); the `aeval x p = 0` form follows by `simp [mem_rootSet_of_ne hp]` (in scratch `Test.lean`).

## 9. `mem_solvableByRad_iff_isSolvable_gal_minpoly`

**Statement.** `[IsAlgClosed E] {x : E} [NeZero (Nat.card (minpoly F x).Gal : F)] : x ∈ solvableByRad F E ↔ IsIntegral F x ∧ IsSolvable (minpoly F x).Gal`. **Proof.** `→`: existing `isIntegral_of_mem_solvableByRad` and `isSolvable_gal_minpoly`. `←`: section 7 with `p = minpoly F x`, of which `x` is a root (`minpoly.ne_zero`, `minpoly.aeval`).

**Q.** *Why `IsIntegral F x ∧`?* For transcendental `x`, `minpoly F x = 0` has trivial (solvable) Galois group but `x` is not solvable by radicals. *The `NeZero` instance mentions `x`?* Yes; in characteristic zero it is inferred (tested with `simp` over `ℚ`, `ℂ`, `AlgebraicClosure F`).

## 10. Docs

Module docstring now says the file proves both directions, with the characteristic condition. `docs/overview.yaml`: only "(one direction)" removed. The docstring of `isSolvable_gal_of_irreducible` keeps "(one direction)" and points to the converse.

## 11. Review items: status

- Math major (`CharZero` → `NeZero`): done.
- Dup blocker (TauCeti prior art): confirmed real; not fixable in code; see section 0.
- Dup major (polynomial-level iff): done (sections 5, 8).
- Dup/style/math (group lemma: move, `to_additive`, `IsCoatomic`): done.
- Style major (heavy import): NOT changed, deliberately; must be disclosed in the PR (see section 7 Q&A). This is a judgement call a mathlib reviewer may overturn.
- Minor items: `mem_of_le` replaced by the equality; degree ≤ 4 corollaries removed (follow-up, code in scratch `Test.lean`); naming nits applied.

## 12. Verification record

Builds OK (10 modules), text linter OK, 15 environment linters 0 errors on 12 declarations, axioms only propext / Classical.choice / Quot.sound for all 12, LF / no trailing whitespace / final newline / max line 100, no `sorry`, no debug commands. Scratch: `D:/Projects/mathlib-prs/scratch/abel-ruffini/Verify.lean` (signatures, axioms, universes), `Test.lean` (usage examples), `Lint.lean`, `Count.lean` (import count on master).