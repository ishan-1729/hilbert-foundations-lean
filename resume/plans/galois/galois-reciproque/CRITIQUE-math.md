# Critique (mathematics lens) of BLUEPRINT.md — unit `nombres.reciproque`

Verdict: **sound**. I re-derived every lemma of section 3 on my own and found no false statement,
circular argument, arithmetic error or missing degenerate case. The final theorems match the
repository's definitions binder by binder. The remaining issues are minor: wording, and one
unsupported remark in RISKS.

## What was checked independently

### Target vs. repository
* `ReciproqueGalois` (TheorieNombres.lean l. 1786) has binders `K Ω : Type`, `[Field K] [CharZero K]
  [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]`, `f`, `[Fact splits]`, `ν`, `ν ≠ 0`, `ℓ^ν ≠ 9`,
  `ℓ^ν ≠ 25`, `Irreducible f`, `natDegree = ℓ^ν`, `IsPreprimitive (groupe f Ω) (rootSet)` and
  `SolubleParRadicaux f Ω`, with conclusion `∃ e, ∀ σ, groupeIndice f e σ ∈ AGammaL`. The blueprint
  quotes this exactly in 1.1. `reciproque_borne` (l. 1797) has the signature the blueprint uses in
  `card_dvd_of_reciproque`. All arguments are supplied in the reference code, in the right order,
  with `K := Corps Γ : Type` and `Ω := Cloture Γ : Type`, so the universe is correct.
* `exists_affine_indexing` (EquationsPrimitives.lean l. 1707) and `degre_primitive`
  (TheorieNombres.lean l. 2031) are quoted correctly.
* The status "proved (corrected)" (README l. 21, FAITHFULNESS l. 26) means that the printed claim
  is false or imprecise and the correct statement is proved. Both halves are delivered:
  `not_reciproqueGalois` for every prime, and `reciproque_corrigee` / `reciproque_corrigee_degre`.
* The reference files equal the compiled scratch `RAll.lean`. The declaration headers are
  identical, and the bodies differ only in imports and module docstrings. `RAll2.out` reports
  `[OK]` after the `diag_mem` repair recorded in `RAll.out`.

### Part A (realization)
* A1: `rename (σ∘τ) = rename σ ∘ rename τ` gives a left action with `σ • x_i = x_{σ i}`. Correct.
* A2: faithfulness follows from the injectivity of `X` and of `R → Frac R`. Correct.
* A3/A4: `f = minpoly_K(x_{x₀})`. The roots in F are exactly the letters: one direction by
  transitivity (Γ acts by K-algebra maps); the other by normality, `minpoly_eq_iff_mem_orbit` and
  `toAlgAut_surjective` (confirmed in FieldTheory/Fixed.lean l. 379 and Normal/Basic.lean l. 237).
  Correct.
* A5: characteristic 0 makes `f` separable, and split in F means #roots = deg. Correct.
* A6/A7: `restrict_surjective` needs `[Normal K F]`, which is the `FixedPoints.normal` instance
  (Fixed.lean l. 274). Injectivity follows from (a) and the injectivity of the letters. The
  transfer to Ω goes through `rootsEquivRoots` and `smul_rootsEquivRoots`. Correct; no
  IsScalarTower is needed.
* A8(c): mathlib's `IsPreprimitive.of_surjective` (GroupAction/Primitive.lean l. 204) needs only
  that the map on points is surjective. It pulls a block back with `IsBlock.preimage`, and φ need
  not be surjective. Correct.
* A8(b): the Galois group of f is a quotient of Γ, `minpoly | f`, then `restrictDvd_surjective`
  and `mem_solvableByRad_of_isSolvable`. Correct.

### Part B (counterexample)
* B1 1–6: re-derived. Rule 3 gives `(a b', b a')` and rule 4 gives `(a b', b a')`. In rule 5 the
  croisée inverse is `(b⁻¹, a⁻¹)`: from `σ(k) = (a k₂+n₁, b k₁+n₂)` one gets
  `σ⁻¹(y) = (b⁻¹(y₂−n₂), a⁻¹(y₁−n₁))`, so the first coordinate is `b⁻¹ y₂ + …`. Correct.
  Rule 6 comes from comparing first coordinates at (1,0) and (0,0). Correct.
* B2: index 2 via `index_eq_two_iff` with ε. Correct.
* B3: Step 1 gives `(c v₁, v₂) + (−v₁, −v₂) = ((c−1) v₁, 0)`, which is nonzero, and scaling then
  gives every `(x,0)`. Step 2 uses the swap and translations. Each use of "g fixes a point of B ⇒ gB = B"
  is valid for a block. This needs only one `c ∉ {0,1}`. F₄ has such an element (ω), so ℓ = 2 is
  covered. The remark that W(F₂) ≅ D₄ is imprimitive on 4 points is correct, and it is why ℓ²
  rather than ℓ is used. This agrees with the classical criterion: H ≀ C₂ in product action is
  primitive iff H is primitive and not regular, and AGL(1, q) with q ≥ 3 satisfies this.
* B4: `[W,W] ≤ P`, `[P,P] ≤ T` (the multipliers commute) and `[T,T] = 1`. Correct.
* B5: `δ(a,b) = d(a,b;0,0)` is injective (evaluate at (1,1)) and lands in P. With |W| = 2|P| this
  gives `2(q−1)² | |W|`. Correct. Also |W| = 2q²(q−1)², which is 288 for q = 4.
* B6: with `m = ℓ²−1`, `ℓ⁴−1 = m(m+2)`, and the divisibility reduces to
  `m | 2(m+1)²(m+2) = m(2m²+8m+10) + 4`, so `m | 4`. Then m = 3 (ℓ = 2) fails since `3 ∤ 4`, and
  for ℓ ≥ 3, m ≥ 8 > 4. Correct. Numerical checks: 960/18, 25920/128 = 202.5 and
  1560000/1152 = 1354.2 are all non-integers.
* B7: ν = 4. `ℓ⁴ ∈ {16} ∪ [81, ∞)` avoids 9 and 25. `|GaloisField ℓ 2| = ℓ²` needs `2 ≠ 0`
  (supplied). Every prime ℓ is covered by one family, which is stronger than the task's two-family
  route and correct.

### Part C (correction)
* C1/C2/C3: correct. C2 does not need finiteness. In C3 the map `k ↦ A k^{p^r}` is
  ZMod p-linear (Frobenius power is an algebra automorphism).
* C4: `q^μ = p^ν`, then μ ≠ 0, `q | p` so q = p, and μ = ν by injectivity of `p^·` (p ≥ 2).
  `groupeIndice f e σ = B⁻¹ ∘ e₀ ∘ σ ∘ e₀⁻¹ ∘ B` is affine with linear part `B⁻¹ M B`. Every
  translation lifts because `groupe f Ω` is the range of `galActionHom`. Correct.
* C5: degree `q^k` with k ≠ 0, since `natDegree ≠ 1` and irreducible polynomials have degree ≥ 1.
  Correct.

## Issues (most severe first)

1. **minor — RISKS item 11.** It states that "the request that triggered this work says the Galois
   formalization is to be folded into the Hilbert repository". Neither the task text nor anything I
   read supports this. An implementer could act on an instruction that nobody gave.
   *Fix:* delete item 11, or restate it neutrally without the attributed claim.

2. **minor — the corrected statement is weaker than Jordan's theorem, and this is said only in
   RISKS 10.** `reciproque_corrigee` omits that the point stabilizer acts irreducibly, although
   this follows from primitivity. That is acceptable, because the task asks only for "affine,
   containing all translations".
   *Fix (optional):* make the Lean reading text of section 7.2 say explicitly that irreducibility
   of the stabilizer is not stated. As written, it only says "necessary condition".

3. **minor — wording in Lemma B3.** "every block B containing 0 is `{0}`-or-smaller or
   everything" is awkward. The mathlib notion is `IsTrivialBlock B := B.Subsingleton ∨ B = univ`.
   *Fix:* write "B is a subsingleton or B = F × F".

4. **minor — Lemma A7 parenthesis.** "(any field extension of K in which f splits would do)" is
   true, but `ReciproqueGalois` also needs `IsAlgClosed Ω` and `Ω : Type`. A reader could take the
   parenthesis as license to choose a different Ω in the Lean code.
   *Fix:* add "for A7; the application in A9 needs Ω algebraically closed in `Type`, hence
   `AlgebraicClosure (Corps Γ)`".

5. **minor — the remark in 2.4 ("for p ≥ 7 …").** The condition is `p − 1 | 2`, i.e. p ≤ 3. So the
   remark also holds for p = 5, where degree 25 is excluded anyway. The remark is not wrong, but it
   should say why it stops at 7.
   *Fix:* "(for p ≥ 5 the divisibility fails, but degree 25 is excluded, so p ≥ 7)".

No fatal or major issue was found. The mathematics of sections 1 and 3 is correct and complete,
and the reference code that implements it compiled (`RAll2.out`: `[OK]`).
