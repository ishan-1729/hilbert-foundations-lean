# Notes for PR 7: Galois's criterion in prime degree

One section per PR. For each: what is stated, how it is proved step by step, and why the names, assumptions and file were chosen.

## 7.1 `galois-prime-degree-group`: Galois's criterion for groups: solvable if and only if no non-identity element fixes two points

Setting throughout: `G` a group acting on `X`, `[FaithfulSMul G X]` (only `1` acts as the identity), `[IsPretransitive G X]`, `hp : (Nat.card X).Prime`; write `p = Nat.card X`.

### Public theorems

**`MulAction.isSolvable_iff_exists_normal_card_eq_of_prime_card`** — `G` is solvable iff it has a normal subgroup of order `p`. Proof: the two private lemmas `exists_normal_card_eq_of_isSolvable` (→) and `isSolvable_of_normal_of_card_eq` (←).

**`MulAction.isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card`** (Galois's criterion) — `G` is solvable iff every `g ≠ 1` has at most one fixed point. `(fixedBy X g).Subsingleton` unfolds to `∀ x, g • x = x → ∀ y, g • y = y → x = y`. Proof: rewrite the left side with the previous theorem, then `eq_one_of_smul_eq_of_smul_eq` (→) and `exists_normal_card_eq_of_forall_subsingleton_fixedBy` (←).

### Private lemmas, in file order

1. `normal_of_card_eq_of_index_lt` — in a finite group, a subgroup `Q` of prime order `p` and index `< p` is normal. Steps: `Q` is a `p`-group (`IsPGroup.of_card`, order `p^1`); `p` does not divide its index (the index is positive and `< p`), so `Q` is a Sylow `p`-subgroup (`IsPGroup.toSylow`); the number of Sylow `p`-subgroups divides the index of one of them (`Sylow.card_dvd_index`), hence is `< p`, and is `≡ 1 mod p` (`card_sylow_modEq_one`), hence equals 1 (`Nat.ModEq.eq_of_lt_of_lt`); a unique Sylow subgroup is normal (`Sylow.normal_of_subsingleton`).
2. `card_stabilizer_lt` — if no `g ≠ 1` fixes two points and `x ≠ y`, then `|Stab(x)| < |X|`. Steps: the map `Stab(x) → X`, `k ↦ k • y` is injective (if `k • y = k' • y` then `k⁻¹k'` fixes `x` and `y`, so it is `1`); `x` is not in its range (`k • y = x = k • x` would give `y = x`); so the range is a proper subset (`Set.ncard_lt_card`).
3. `eq_one_of_mem_centralizer` — if `N` is a transitive subgroup, `g` commutes with all of `N` and `g • x = x`, then `g = 1`. Steps: any `y` is `n • x`; `g • n • x = n • g • x = n • x`; so `g` acts trivially and faithfulness gives `g = 1`.
4. `isCancelSMul_of_isMulCommutative` — a commutative transitive subgroup acts freely: an element of `N` fixing a point centralizes `N` (`Subgroup.le_centralizer`), apply 3.
5. `isPretransitive_of_normal` — a normal subgroup `N ≠ ⊥` is transitive. Steps: the action is primitive because `p` is prime (`IsPreprimitive.of_prime_card`); for a (quasi)primitive action a normal subgroup is transitive unless it fixes every point (`IsQuasiPreprimitive.isPretransitive_of_normal`); if `N` fixed every point, faithfulness would give `N = ⊥`.
6. `isPretransitive_of_normal_of_card_eq` — same with hypothesis `Nat.card N = p` (so `N ≠ ⊥` since `p > 1`).
7. `exists_normal_card_eq_of_ne_bot` — `G` finite solvable, `H` normal, `H ≠ ⊥` ⟹ there is a normal subgroup of order `p`. Well-founded induction on `H` (`WellFoundedLT.induction`; subgroups of a finite group). `H` is transitive by 5. If `⁅H, H⁆ = ⊥`, `H` is commutative (`commutator_self_eq_bot_iff`), hence free by 4, so `|H| = [H : Stab_H(x)] = |X|` (`index_stabilizer_of_transitive`, `IsCancelSMul.stabilizer_eq_bot`, `index_bot`). Otherwise `⁅H, H⁆ < H` (`Group.IsSolvable.commutator_lt_of_ne_bot`), it is normal (`commutator_normal`) and nontrivial: apply the induction hypothesis. `hH : H.Normal` is an explicit argument, not an instance binder, because `induction` must generalize it.
8. `exists_normal_card_eq_of_isSolvable` — apply 7 to `H = ⊤`. `X` is finite (`Nat.card X ≠ 0`), `G` is finite (it embeds in `Perm X` by `toPerm_injective`), and `⊤ ≠ ⊥` because `G` moves some point to a different point.
9. `eq_one_of_smul_eq_of_smul_eq` — with a normal `N` of order `p`: `g` fixing two distinct points `x, y` is `1`. Steps: `N` is cyclic (`isCyclic_of_prime_card`) and transitive (6); write `y = n • x`. The element `n⁻¹ (g n g⁻¹)` lies in `N` (normality), fixes `x`, and centralizes `N` (`N` commutative), so it is `1` by 3: `g` commutes with `n`. `n ≠ 1` since `x ≠ y`; every element of `N` is a power of `n` (`mem_zpowers_of_prime_card`), so `g` centralizes `N`; `g` fixes `x`; so `g = 1` by 3.
10. `exists_normal_card_eq_of_forall_subsingleton_fixedBy` — `p` divides `|G|` (`|G| = |Stab(x)| · p`), so there is a subgroup `Q` of order `p` (`Sylow.exists_subgroup_card_pow_prime` with exponent 1). From `[G:Q] · p = |G| = |Stab(x)| · p` get `[G:Q] = |Stab(x)| < p` (2), so `Q` is normal (1).
11. `isSolvable_of_normal_of_card_eq` — `Group.isSolvable_of_ker_le_range N.subtype MulAut.conjNormal`: `N` is solvable (cyclic), `MulAut N` is commutative (`IsCyclic.mulAutMulEquiv`), and the kernel of conjugation lies in `N`: if `g` centralizes `N`, pick `n ∈ N` with `n • (g • x) = x`; `n g` centralizes `N` and fixes `x`, so `n g = 1` (3) and `g = n⁻¹ ∈ N`.

### Why these choices

- **Assumptions.** Faithfulness and transitivity are both needed for `→` (the subgroup generated by a transposition in S₅ is solvable but fixes three points; a non-faithful action has a kernel fixing everything). No `Finite`/`Fintype` hypotheses: they follow from `hp`. Universe polymorphic (`Type*`, checked with explicit `u`, `v`).
- **`(hp : (Nat.card X).Prime)`** follows `MulAction.IsPreprimitive.of_prime_card`. The affine form (PR 3) uses `{p} [Fact p.Prime] (hX : Nat.card X = p)` because `ZMod p` appears in its statement; say this if asked about the inconsistency.
- **Names** are built from the statement: `isSolvable_iff_<rhs>_of_prime_card`.
- **Placement.** New leaf file next to `GroupAction/Primitive.lean`, `Jordan.lean`, `Iwasawa.lean`; nothing else has to be rebuilt.

### Likely reviewer questions

- *"Several private lemmas are general (3, 4, 5, 1). Make them public in GroupAction/Basic, Primitive, Sylow?"* — They are kept private to keep the PR focused; mathlib master does not have them (checked with `exact?` by the reviewers). Note for you: 3, 4, 5 have counterparts in Tau Ceti (for subgroups of `Equiv.Perm`, and `isPretransitive_of_normal_of_ne_bot`), which is why they were not offered as API. Lemma 1 (`normal_of_card_eq_of_index_lt`) and lemma 2 have no Tau Ceti counterpart found; you may agree to publish 1 in `Mathlib/GroupTheory/Sylow.lean` if asked. Your decision for 3-5.
- *"Why not state it for `G : Subgroup (Equiv.Perm X)`?"* — The MulAction form contains it (a subgroup of `Perm X` acts faithfully) and applies directly to Galois groups acting on roots (PR 2).
- *"Why `fixedBy ... Subsingleton` rather than a statement with points?"* — It is the mathlib object for the set of fixed points of one element; it unfolds definitionally to the pointwise statement (checked in the scratch file `verify/Verify.lean`).
- *"Is the reference right?"* — `[Wielandt-1964]` is an existing key in `docs/references.bib`. The section number `§11` was NOT checked against the book by any agent: check it (I believe the Galois and Burnside theorems on groups of prime degree are Theorems 11.6/11.7 there) or drop the `§11`.
- *"Why mixed `public import` / `import`?"* — Same pattern as e.g. `Mathlib/FieldTheory/Galois/Sylow.lean`: the statements only need the four public imports; Primitive, Cyclic and Sylow are used in proofs only.

## 7.2 `galois-prime-degree-polynomial`: Galois's criterion for equations: solvable if and only if any two roots generate the splitting field

Setting: fields `F`, `E`, `[Algebra F E]`, `f : F[X]`, `hf : Irreducible f`, `hp : f.natDegree.Prime`.

### Public theorems

**`Polynomial.Gal.isSolvable_iff_forall_adjoin_pair_eq_top_of_prime_degree`** — if `E` is a splitting field of `f`, then `f.Gal` is solvable iff any two distinct roots `x, y` of `f` in `E` generate `E` over `F` (`F⟮x, y⟯ = ⊤`). Proof, step by step:
1. `e : Gal(E/F) ≃* f.Gal` is `(IsSplittingField.algEquiv E f).autCongr` (two splitting fields are isomorphic; `f.Gal` is by definition `Gal(f.SplittingField/F)`). Solvability passes both ways (`Group.isSolvable_of_isSolvable_injective`, `Group.isSolvable_of_surjective`): this is `he`.
2. If `f` is separable: private lemma `isSolvable_iff_of_separable`.
3. If not: `subsingleton_rootSet_of_not_separable` gives at most one root; an automorphism is determined by its action on the roots (`faithfulSMul_rootSet`), and all roots are equal, so `Gal(E/F)` is trivial, hence solvable; the right side is vacuous (no two distinct roots).

**`Polynomial.Gal.isSolvable_iff_forall_rootSet_subset_adjoin_pair_of_prime_degree`** — if `f` splits in `E` (any extension, e.g. an algebraic closure), then `f.Gal` is solvable iff for any two distinct roots `x, y` in `E`, all roots of `f` in `E` lie in `F⟮x, y⟯` ("every root is a rational function of any two"). Proof: `K := adjoin F (f.rootSet E)` is a splitting field of `f` (`adjoin_rootSet_isSplittingField`); roots in `K` correspond to roots in `E` (`hroot`, by `simp [mem_rootSet]`); `key`: for `x y : K`, `F⟮x, y⟯ = ⊤` in `K` iff `f.rootSet E ⊆ F⟮x, y⟯` in `E` (lift to `E` with `lift_inj`, `lift_adjoin`, `lift_top`; `lift ⊤ = K = adjoin F (rootSet)`; then `adjoin_le_iff` and antisymmetry, the inclusion `F⟮x, y⟯ ≤ K` holding because `x, y ∈ K`). Then apply the first theorem to `K`.

### Private lemmas

- `faithfulSMul_rootSet` — for a splitting field `E`, `Gal(E/F)` acts faithfully on `f.rootSet E`: two automorphisms agreeing on the roots agree on `E`, because the roots generate `E` (`IsSplittingField.adjoin_rootSet`, `AlgHom.ext_of_adjoin_eq_top`). It is the `Gal(E/F)` analogue of mathlib's `Polynomial.Gal.galActionHom_injective`.
- `isPretransitive_rootSet` — for `f` irreducible, `Gal(E/F)` is transitive on `f.rootSet E`: mathlib gives `g : f.Gal` with `g • x = y` (`galAction_isPretransitive`); lift `g` to `σ : Gal(E/F)` (`restrict_surjective`, needs `Normal F E`, from `Normal.of_isSplittingField`); `restrict_smul` says `σ` and its restriction act the same way on roots.
- `adjoin_eq_top_iff_forall_eq_one` — in a finite Galois extension, `adjoin F S = ⊤` iff the only automorphism fixing every element of `S` is `1`. Steps: `⊤ = fixedField ⊥`; `fixedField H = K ↔ K.fixingSubgroup = H` (`IsGalois.fixedField_eq_iff_fixingSubgroup_eq`); a subgroup is `⊥` iff its elements are `1`; `σ` fixes `adjoin F S` pointwise iff it fixes `S` pointwise (`forall_mem_adjoin_smul_eq_self_iff`).
- `subsingleton_rootSet_of_not_separable` — `natSepDegree f` divides `natDegree f = p` (`Irreducible.natSepDegree_dvd_natDegree`), so it is `1` or `p`; it is `p` iff `f` is separable (`natSepDegree_eq_natDegree_iff`); so it is `1`; when `f` splits in `E` it is the number of distinct roots in `E` (`natSepDegree_eq_of_splits`). `classical` is needed because `rootSet` is defined through a `Finset` of roots.
- `isSolvable_iff_of_separable` — `E/F` is finite and Galois (`IsGalois.of_separable_splitting_field`); the root set has `natDegree f = p` elements (`card_rootSet_eq_natDegree`); apply the group criterion of PR 1 to `Gal(E/F)` acting on `f.rootSet E`; rewrite `F⟮x, y⟯ = ⊤` with the adjoin lemma; the two directions only convert between roots as elements of `E` and as elements of the subtype `f.rootSet E`.

### Why these choices

- **No `f.Separable` hypothesis**: the inseparable case is true (both sides hold) and costs 6 lines; the docstring says so.
- **`f.Gal` on the left**: mathlib's solvability results are about `f.Gal`. For `E = f.SplittingField` the statement applies directly (tested).
- **Two theorems**: the first is the clean field-theoretic statement; the second is the classical formulation and is the one usable with roots in `ℂ` (15-line corollary). If a reviewer wants only one, keep the first.
- **Hypothesis `f.natDegree.Prime`** and suffix `_of_prime_degree`: same as `Polynomial.Gal.galActionHom_bijective_of_prime_degree`.
- **Placement**: `Mathlib/FieldTheory/Galois/`, a new leaf file.

### Likely reviewer questions

- *"Why not apply the group criterion to `f.Gal` with `galAction` directly?"* — The translation to `F⟮x, y⟯ = ⊤` uses the Galois correspondence, which is stated for `Gal(E/F)`; going through `f.Gal` would need transporting `fixingSubgroup` along `restrict`. Said in the implementation notes.
- *"`he` should be `MulEquiv.isSolvable_congr`."* — That lemma does not exist in mathlib master (grep). You can offer to add it to `Mathlib/GroupTheory/Solvable.lean` in a separate PR; note it exists in Tau Ceti, so by your own rule you may prefer to keep the 3 lines.
- *"Make `adjoin_eq_top_iff_forall_eq_one` / `faithfulSMul_rootSet` public?"* — No Tau Ceti counterpart was found for these two or for `subsingleton_rootSet_of_not_separable`; you can agree to publish them (the adjoin lemma would go to `Mathlib/FieldTheory/Galois/Basic.lean`). `isPretransitive_rootSet` overlaps Tau Ceti: keep private.
- *"Is this Galois's Proposition VIII?"* — Galois states it for solvability by radicals (characteristic 0). The file proves the statement for solvability of the Galois group; the module docstring says the link with radicals is not treated (mathlib has only radicals ⟹ solvable group).
- *"Reference?"* — `galois1846`: Galois, *Mémoire sur les conditions de résolubilité des équations par radicaux*, J. Math. Pures Appl. 11 (1846). The page range 417-433 was typed from memory by an agent and I could not check it offline: verify it (e.g. on Gallica/Numdam) before submitting. The entry was typed in the layout of the neighbouring entries but NOT run through `bibtool` (not installed here); mathlib CI checks `bibtool --preserve.key.case=on --preserve.keys=on --pass.comments=on --print.use.tab=off -s -i docs/references.bib -o docs/references.bib` leaves the file unchanged.

## 7.3 `galois-prime-degree-affine`: optional: solvable if and only if the group acts by maps `k ↦ a * k + b` of `ZMod p`

This PR can be dropped without affecting PR 1 or PR 2. Submit it only if you are ready to discuss the shape of the statement (see the first question below).

### Public theorem

**`MulAction.isSolvable_iff_exists_equiv_zmod_of_prime_card`** — let `G` act faithfully and transitively on `X` with `Nat.card X = p` prime. Then `G` is solvable iff there is a bijection `e : X ≃ ZMod p` such that every `g` acts as `k ↦ a * k + b` for some `a b : ZMod p` depending on `g` (formally `e (g • x) = a * e x + b` for all `x`).

Proof: `subst hX` turns `p` into `Nat.card X`.
- (→) `exists_normal_card_eq_of_isSolvable` (PR 1) gives a normal `N` of order `p`; conclude with the private `exists_equiv_zmod_of_normal_of_card_eq`.
- (←) By Galois's criterion (PR 1) it suffices to show that `g` fixing `x ≠ y` is `1`. From `e x = a * e x + b` and `e y = a * e y + b`, subtract: `(a - 1) * (e x - e y) = 0` (`linear_combination`); `e x ≠ e y` and `ZMod p` is a field, so `a = 1`, then `b = 0`; so `e (g • z) = e z` for all `z`, `g` acts trivially, and `g = 1` by faithfulness.

### Private lemmas

- `bijective_pow_val_smul` — if `N` (order `p`) acts freely on `X` (`p` elements) and `n ≠ 1` in `N`, then `k ↦ n ^ k.val • x` is a bijection `ZMod p → X`. Both sides have `p` elements (`Nat.card_zmod`), so injectivity suffices (`Nat.bijective_iff_injective_and_card`). If `n ^ k.val • x = n ^ l.val • x` then `n ^ k.val = n ^ l.val` (freeness), so `k.val ≡ l.val` mod the order of `n` (`pow_inj_mod`), which is `p` (`orderOf_eq_prime`: `n ^ p = 1` and `n ≠ 1`); both are `< p`, so they are equal, and `ZMod.val` is injective. The `omit ... in` line removes the file-level faithfulness/transitivity assumptions, which this lemma does not use (the unused-variable linter requires it).
- `exists_equiv_zmod_of_normal_of_card_eq` — `N` normal of order `p` ⟹ the affine labelling exists. `N` is cyclic, transitive (PR 1) and free (PR 1); pick `x₀` and `n ≠ 1`; `f k = n ^ k.val • x₀` is bijective; `hf_nat`: `f (j : ZMod p) = n ^ j • x₀` for a natural number `j` (`ZMod.val_natCast`, `pow_mod_natCard`). Take `e = f⁻¹`. For `g`: `g n g⁻¹ ∈ N` is `n ^ a` and the element `m` of `N` with `m • x₀ = g • x₀` is `n ^ b` (`mem_powers_of_prime_card`, natural exponents). For `x = f k`: `g • n ^ k • x₀ = (g n g⁻¹) ^ k • g • x₀ = n ^ (a k) • n ^ b • x₀`; the `have` converts `a * k + b` in `ZMod p` to the cast of the natural number `a * k.val + b`, then `hf_nat` and a final `simp` with `conj_pow`.

### Why these choices / likely reviewer questions

- *"State it with mathlib's `AffineEquiv` (`ZMod p ≃ᵃ[ZMod p] ZMod p`) or as a monoid hom into an affine group."* — This was raised by an internal review and deliberately not done: the elementary form is directly usable in both directions (to prove solvability one supplies `a` and `b`), and the `AffineEquiv` form would need roughly 30 more lines to build the equivalences and a hom. If the reviewer insists, the honest options are to rework it or withdraw this PR; PR 1 and PR 2 do not depend on it. Do not introduce a named `AGL(1, p)`: Tau Ceti has one.
- *"Why may `a` be `0` in the statement?"* — It cannot actually be `0` (each `g` acts bijectively); leaving `a : ZMod p` unconstrained keeps the statement simple and makes `←` stronger. The docstring says "necessarily `a ≠ 0`".
- *"Why `[Fact p.Prime] (hX : Nat.card X = p)` here but `(hp : (Nat.card X).Prime)` in the other two theorems?"* — Because `ZMod p` occurs in this statement: with `Nat.card X` in place of `p` a user with `X = ZMod 5` or `Fin 5` could not give `Equiv.refl` without rewriting. Same shape as `isCyclic_of_prime_card`. The other two follow `IsPreprimitive.of_prime_card`.
- *"Why in this file?"* — It uses the private lemmas of PR 1 (`exists_normal_card_eq_of_isSolvable`, `isPretransitive_of_normal_of_card_eq`, `isCancelSMul_of_isMulCommutative`).
- *"`linear_combination` import for one line?"* — It replaces a 3-line manual ring computation; if the reviewer prefers fewer imports, `have : (a - 1) * (e x - e y) = 0 := by rw [sub_mul, mul_sub, mul_sub]; ...` is possible but was not written.

## Overlap with Tau Ceti

Main theorems: no overlap. Tau Ceti has the solvability criterion only for degree 5 (GroupTheory/Perm/TransitiveGroupLabel/Solvable.lean, FieldTheory/GaloisGroups/Label.lean, Quintic.lean, Resolvent/Quintic/*), plus general Frobenius-kernel / TI-subgroup material that does not state the prime-degree criterion; no general-p statement in the group form, the equation form or the affine form. Helpers with Tau Ceti counterparts, all PRIVATE in the contribution: eq_one_of_mem_centralizer and isCancelSMul_of_isMulCommutative (TauCeti GroupTheory/Perm/Centralizer.lean: Subgroup.eq_one_of_mem_centralizer_of_apply_eq, Subgroup.isCancelSMul_centralizer, there for subgroups of Equiv.Perm); isPretransitive_of_normal (TauCeti IsQuasiPreprimitive.isPretransitive_of_normal_of_ne_bot); isPretransitive_rootSet (TauCeti.isPretransitive_rootSet_of_irreducible, FieldTheory/GaloisGroups/Stabilizer.lean:169; ours is a private corollary of mathlib's galAction_isPretransitive for a splitting field). Tau Ceti also has MulEquiv.isSolvable_congr (GroupTheory/Solvable.lean:79), Group.IsSolvable.exists_normal_index_prime, the minimal-normal-subgroup API and a named AffineGroup: none of these is introduced (the transport of solvability is 3 inline lines). No Tau Ceti counterpart found for the private faithfulSMul_rootSet, adjoin_eq_top_iff_forall_eq_one, subsingleton_rootSet_of_not_separable, normal_of_card_eq_of_index_lt, card_stabilizer_lt. Open mathlib PRs: about 28 `gh search prs --repo leanprover-community/mathlib4` queries (prime degree, Galois criterion, solvable, transitive, Frobenius group, of_prime_card, affine ZMod, ...) returned nothing overlapping; keyword search cannot be exhaustive.

