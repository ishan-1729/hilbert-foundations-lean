# Blueprint: closing the unit `nombres.reciproque` (status "proved (corrected)")

**Verdict on the target.** The target `theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] :
¬ ReciproqueGalois ℓ` is **true as formalized**, for every prime `ℓ`. (Equivalently: the printed
claim `ReciproqueGalois ℓ` is false as formalized, for every prime `ℓ`.) One uniform
counterexample works for all `ℓ`: take `ν = 4`, the field `𝔽 = GaloisField ℓ 2` with `q = ℓ²`
elements, and the group `W(𝔽) = AGL(1, 𝔽) ≀ C₂` acting on the `q² = ℓ⁴` points of `𝔽 × 𝔽`
(substitutions `(k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` and `(k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)`,
`a, b ≠ 0`). It is solvable, primitive (because `q ≥ 4 ≥ 3`), of order `2 q² (q − 1)²`, and it is
the group of an irreducible equation of degree `ℓ⁴` over a field of characteristic `0`, with the
given action on the roots. `ℓ⁴` is never `9` or `25`. Under the printed claim, the order of the
group would divide `ℓ⁴ (ℓ⁴ − 1) · 4` (`reciproque_borne`); but `2 (ℓ² − 1)²` divides the order and
does not divide `ℓ⁴ (ℓ⁴ − 1) · 4` (that would force `ℓ² − 1 ∣ 4`, impossible since
`ℓ² − 1 ∈ {3, 8, 24, …}`). Numerically: `ℓ = 2`: `18 ∤ 960`; `ℓ = 3`: `128 ∤ 25920`; `ℓ = 5`:
`1152 ∤ 1560000`.

This replaces the route proposed in the task (two families: `ν = 3` monomial groups for `ℓ ≥ 3`,
and `GL(2,2) ≀ C₂` for `ℓ = 2`) by a single family, which moreover is a field-generic copy of code
that already compiles in the repository (`EquationsPrimitives.couronne`, written there for
`ZMod p` only).

The corrected statement (2) is also true and almost entirely available: its group-theoretic core
is the existing theorem `GaloisOeuvres.EquationsPrimitives.exists_affine_indexing`.

The status of each piece of Lean code below (compiled in a scratch file or not) is recorded in
section 4.0 and under RISKS.

---

## 1. TARGET

### 1.1 The statement to refute (existing; do not modify)

`GaloisOeuvres/TheorieNombres.lean`, line 1786, namespace `GaloisOeuvres.TheorieNombres`
(in scope there: `open Polynomial`, `variable {p : ℕ} [hp : Fact p.Prime]`):

```lean
def ReciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (f : K[X])
    [Fact ((f.map (algebraMap K Ω)).Splits)] (ν : ℕ), ν ≠ 0 → ℓ ^ ν ≠ 9 → ℓ ^ ν ≠ 25 →
    Irreducible f → f.natDegree = ℓ ^ ν →
    MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω) → SolubleParRadicaux f Ω →
    ∃ e : GaloisField ℓ ν ≃ f.rootSet Ω,
      ∀ σ : f.Gal, groupeIndice f e σ ∈ AGammaL (p := ℓ) (GaloisField ℓ ν)
```

### 1.2 The final theorems (new, in `GaloisOeuvres/TheorieNombresClose.lean`, namespace `GaloisOeuvres.TheorieNombres`)

(1) the printed claim is false, for every prime:

```lean
theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : ¬ ReciproqueGalois ℓ
```

(2) the corrected statement (Galois–Jordan), in the shape of `ReciproqueGalois` with the affine
group `AGL p (GaloisField p ν)` (new definition, 4.3) in place of `AGammaL`, and with the
translations:

```lean
theorem reciproque_corrigee {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)] {ν : ℕ} (hν : ν ≠ 0)
    (hirr : Irreducible f) (hdeg : f.natDegree = p ^ ν)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ e : GaloisField p ν ≃ f.rootSet Ω,
      (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL p (GaloisField p ν)) ∧
      ∀ b : GaloisField p ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b

theorem reciproque_corrigee_degre {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)]
    (hirr : Irreducible f) (hdeg : f.natDegree ≠ 1)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ (ℓ ν : ℕ) (_ : Fact ℓ.Prime), ν ≠ 0 ∧ f.natDegree = ℓ ^ ν ∧
      ∃ e : GaloisField ℓ ν ≃ f.rootSet Ω,
        (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL ℓ (GaloisField ℓ ν)) ∧
        ∀ b : GaloisField ℓ ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b
```

together with `theorem AGammaL_le_AGL` (Galois's substitutions are affine: the corrected
conclusion is a weakening of the printed one).

Remarks on the shape of (2), to be repeated in the Lean reading of the unit:
* No exception for the degrees `9` and `25` is needed.
* The degree hypothesis `hdeg` is not a restriction: by the existing `degre_primitive` the degree
  is a prime power (`reciproque_corrigee_degre`; the hypothesis `natDegree ≠ 1` only excludes the
  linear equation, whose single root cannot be labelled by a `GaloisField`).
* (2) is a necessary condition only; unlike Galois's group `AΓL(1, p^ν)` (`suffisance`), the
  affine group `AGL(ν, p)` is not solvable in general, so no converse of (2) is claimed.
  The printed claim is true for `ν = 1` (`reciproque_premier`, already proved), where
  `AΓL(1, p) = AGL(1, p)`.
* (2) omits one part of Jordan's full statement: that the stabilizer of a root (the linear parts
  `A`) acts irreducibly on `F_p^ν`, i.e. leaves no subgroup other than `0` and the whole space
  invariant. This is true (it follows from primitivity) but it is **not stated** in
  `reciproque_corrigee`. The Lean reading of the unit (section 7.2) must say both things
  explicitly: (2) is a necessary condition only, and the irreducibility of the stabilizer is not
  stated.

---

## 2. EXISTING MATERIAL (repository)

All of the following compile today (the `.olean` files are in `.lake/build`).

### 2.1 `GaloisOeuvres/Basic.lean` (namespace `GaloisOeuvres`, `open Polynomial`, `variable {K : Type*} [Field K]`)

```lean
def SolubleParRadicaux (p : K[X]) (Ω : Type*) [Field Ω] [Algebra K Ω] : Prop :=
  ∀ x ∈ p.rootSet Ω, x ∈ solvableByRad K Ω

noncomputable def groupe (p : K[X]) (Ω : Type*) [Field Ω] [Algebra K Ω]
    [Fact ((p.map (algebraMap K Ω)).Splits)] : Subgroup (Equiv.Perm (p.rootSet Ω)) :=
  (Gal.galActionHom p Ω).range
```

### 2.2 `GaloisOeuvres/Radicaux.lean` (namespace `GaloisOeuvres`)

```lean
theorem mem_solvableByRad_of_isSolvable {K Ω : Type*} [Field K] [CharZero K] [Field Ω]
    [Algebra K Ω] [IsAlgClosed Ω] {x : Ω} (hx : IsIntegral K x)
    (h : Group.IsSolvable (minpoly K x).Gal) : x ∈ solvableByRad K Ω
```

### 2.3 `GaloisOeuvres/TheorieNombres.lean` (namespace `GaloisOeuvres.TheorieNombres`; `variable {p : ℕ} [hp : Fact p.Prime]`)

Section `Substitutions`/`Resolubilite`: `variable (K : Type*) [Field K] [Finite K] [Algebra (ZMod p) K]`.

```lean
theorem frob_pow_apply (r : ℕ) (k : K) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K ^ r) k = k ^ p ^ r        -- l. 1422

def AGammaL : Subgroup (Equiv.Perm K) where                                         -- l. 1429
  carrier := {σ | ∃ r : ℕ, ∃ A : K, A ≠ 0 ∧ ∃ B : K, ∀ k, σ k = A * k ^ p ^ r + B}
  ...

theorem nombre_substitutions {ν : ℕ} (hν : ν ≠ 0) :                                 -- l. 1526
    Nat.card (AGammaL (p := p) (GaloisField p ν)) = p ^ ν * (p ^ ν - 1) * ν

noncomputable def groupeIndice {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (f : K[X])
    [Fact ((f.map (algebraMap K Ω)).Splits)] {ν : ℕ} (e : GaloisField p ν ≃ f.rootSet Ω) :
    f.Gal →* Equiv.Perm (GaloisField p ν) :=                                        -- l. 1683
  (e.symm.permCongrHom : Equiv.Perm (f.rootSet Ω) ≃* Equiv.Perm (GaloisField p ν)).toMonoidHom.comp
    (Gal.galActionHom f Ω)
-- so `groupeIndice f e σ k = e.symm (Gal.galActionHom f Ω σ (e k))` holds by `rfl`
-- (this is how `reciproque_premier` uses it: `change ψ.symm (e₀.symm (Gal.galActionHom f Ω σ (e₀ (ψ k)))) = _`)

theorem card_gal_dvd {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (f : K[X])
    [Fact ((f.map (algebraMap K Ω)).Splits)] {ν : ℕ} (hν : ν ≠ 0)
    (e : GaloisField p ν ≃ f.rootSet Ω)
    (h : ∀ σ, groupeIndice f e σ ∈ AGammaL (p := p) (GaloisField p ν)) :
    Nat.card f.Gal ∣ p ^ ν * (p ^ ν - 1) * ν                                        -- l. 1771

def ReciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : Prop := ...                           -- l. 1786, see 1.1

theorem reciproque_borne (ℓ : ℕ) [Fact ℓ.Prime] (H : ReciproqueGalois ℓ) (K Ω : Type) [Field K]
    [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (f : K[X])
    [Fact ((f.map (algebraMap K Ω)).Splits)] (ν : ℕ) (hν : ν ≠ 0) (h9 : ℓ ^ ν ≠ 9)
    (h25 : ℓ ^ ν ≠ 25) (hirr : Irreducible f) (hdeg : f.natDegree = ℓ ^ ν)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω)) (hsol : SolubleParRadicaux f Ω) :
    Nat.card f.Gal ∣ ℓ ^ ν * (ℓ ^ ν - 1) * ν                                        -- l. 1797

theorem reciproque_premier {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)] (hirr : Irreducible f)
    (hdeg : f.natDegree = p ^ 1) (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ e : GaloisField p 1 ≃ f.rootSet Ω,
      ∀ σ : f.Gal, groupeIndice f e σ ∈ AGammaL (p := p) (GaloisField p 1)          -- l. 1913

theorem degre_primitive {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)] (hirr : Irreducible f)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) : ∃ q k : ℕ, q.Prime ∧ f.natDegree = q ^ k      -- l. 2031
```

The first lines of the proofs of `reciproque_premier` / `degre_primitive` (existence of a root,
`Group.IsSolvable f.Gal` via mathlib's `isSolvable_gal_of_irreducible`, `Group.IsSolvable (groupe f Ω)`,
`Nat.card (f.rootSet Ω) = …` via `card_rootSet_eq_natDegree`) are reused verbatim in
`reciproque_corrigee` (see 4.3).

### 2.4 `GaloisOeuvres/EquationsPrimitives.lean` (namespace `GaloisOeuvres.EquationsPrimitives`; `open Polynomial MulAction OnePoint`)

Section `IndicesPremiers`: `variable {G X : Type*} [Group G] [MulAction G X]`.

```lean
theorem exists_affine_indexing [Group.IsSolvable G] [IsPreprimitive G X] [FaithfulSMul G X]
    [Finite X] [Nontrivial X] :
    ∃ q ν : ℕ, q.Prime ∧ ∃ e : X ≃ (Fin ν → ZMod q),
      (∀ g : G, ∃ M : Matrix (Fin ν) (Fin ν) (ZMod q), IsUnit M.det ∧
        ∃ b : Fin ν → ZMod q, ∀ x, e (g • x) = M.mulVec (e x) + b) ∧
      (∀ b : Fin ν → ZMod q, ∃ g : G, ∀ x, e (g • x) = e x + b)                     -- l. 1707
```

This is the group-theoretic content of (2) (regular normal elementary abelian subgroup `E ≅ (ℤ/q)^ν`
from `exists_regular_elementary_normal`, l. 195; conjugation acts linearly). Nothing of the
"minimal normal subgroup" theory has to be redone.

The same file contains, for `ZMod p` only (section `ContreExemple`, l. 671–897): `EstDroite`,
`EstCroisee`, private lemmas `dd dc cd cc d_inv c_inv not_d_c`, `droite`, `echange`, `couronne p`,
`produit p`, `index_produit`, private `smul_mem_of_block`, private `ligne_sub (hp : p ≠ 2)`,
`couronne_primitif (hp : p ≠ 2)`, `couronne_soluble`. These are the **model** for file Aux2 below:
the new file is the same text with `ZMod p` replaced by an arbitrary field `F` and with the single
mathematical change described in Lemma B3 (the constants `2, −1` of `ligne_sub`, which need
`p ≠ 2`, are replaced by `c, −1` with `c ∉ {0, 1}`). The private lemmas cannot be imported, and the
`ZMod p` versions do not cover `ℓ = 2, 3, 5` (they give degree `p²`, and `9`, `25` are excluded,
while for `p = 2` the group is imprimitive), which is why a field-generic copy is needed.
(Remark, not used: `2 p² (p − 1)²` divides `p² (p² − 1) · 2` iff `(p − 1)² ∣ (p − 1)(p + 1)` iff
`p − 1 ∣ p + 1` iff `p − 1 ∣ 2`, i.e. iff `p ∈ {2, 3}`; so the divisibility fails for every
`p ≥ 5`. But `p = 5` is the excluded degree `25`, so the existing `couronne p` (primitive for
`p ≠ 2`) refutes the claim in degree `p²` exactly for `p ≥ 7`. The uniform family over the field
with `ℓ²` elements is used instead because it also covers `ℓ = 2, 3, 5`.)

### 2.5 Related declarations that exist but are deliberately not imported

`GaloisOeuvres/AnalyseMemoire.lean` (namespace `GaloisOeuvres.AnalyseMemoire`,
`variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]`) has

```lean
theorem soluble_iff_isSolvable [CharZero K] [IsAlgClosed Ω] {p : K[X]} (hp : Irreducible p) :
    SolubleParRadicaux p Ω ↔ Group.IsSolvable p.Gal                                 -- l. 638
theorem degre_primitif {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] {p : K[X]} (hp : Irreducible p)
    (hprim : @EquationPrimitive K _ p Ω _ _ (splits_fact p))
    (hs : SolubleParRadicaux p Ω) : ∃ q ν : ℕ, q.Prime ∧ p.natDegree = q ^ ν       -- l. 793
```

and `GaloisOeuvres/Memoire/DegrePremier.lean` (l. 668) has `soluble_of_isSolvable_gal` (the
direction "solvable group ⇒ solvable by radicals" for an irreducible `p`). The new files need only
that direction, once; its six-line proof (from `mem_solvableByRad_of_isSolvable` and mathlib's
`Gal.restrictDvd_surjective`) is repeated in file Aux1 under the name
`Realisation.soluble_of_isSolvable_gal`, so that Aux1 imports nothing beyond
`GaloisOeuvres.Radicaux` (the import of `TheorieNombres.lean` itself). The direction "solvable by
radicals ⇒ solvable group" is taken, as in `reciproque_premier` and `degre_primitive`, directly
from mathlib's `isSolvable_gal_of_irreducible`. The prime-power degree is taken from
`TheorieNombres.degre_primitive` (2.3), which is stated with `groupe f Ω` exactly as
`ReciproqueGalois` is.

---

## 3. MATHEMATICAL PROOF

### Part A. Every finite transitive permutation group is the group of an equation

Throughout Part A: `X` is a finite set, `Γ` a subgroup of `Sym(X)` acting transitively on `X`
(in particular `X ≠ ∅`), `R = ℚ[x_i : i ∈ X]` the polynomial ring, `F = Frac(R)`.

**Lemma A1 (the action).** For `σ ∈ Sym(X)` let `σ_R : R → R` be the ring automorphism
`x_i ↦ x_{σ i}` (renaming of variables). Then `1_R = id` and `(στ)_R = σ_R ∘ τ_R`. Each ring
automorphism `h` of `R` extends to a field automorphism `h_F` of `F` with `h_F(a) = h(a)` for
`a ∈ R`, and `h ↦ h_F` is a group homomorphism. Hence `σ • y := (σ_R)_F (y)` is an action of
`Sym(X)` on `F` by field automorphisms, and `σ • x_i = x_{σ i}`.

*Proof.* `rename (σ ∘ τ) = rename σ ∘ rename τ` and `rename id = id` (mathlib
`MvPolynomial.rename_rename`, `rename_id`). The extension to fractions and its functoriality are
mathlib's `IsFractionRing.ringEquivOfRingEquiv`, `ringEquivOfRingEquivHom` (a monoid
homomorphism `(R ≃+* R) →* (F ≃+* F)`), `ringEquivOfRingEquiv_algebraMap`. ∎

**Lemma A2 (faithfulness).** `i ↦ x_i ∈ F` is injective. Consequently every subgroup `Γ ≤ Sym(X)`
acts faithfully on `F`.

*Proof.* The variables are distinct in `R` (`MvPolynomial.X_injective`, `ℚ` nontrivial) and `R → F`
is injective (`IsFractionRing.injective`). If `γ • y = γ' • y` for all `y`, then
`x_{γ i} = γ • x_i = γ' • x_i = x_{γ' i}`, so `γ i = γ' i` for all `i`, i.e. `γ = γ'`. ∎

**Lemma A3 (mathlib, Artin).** Let `K = F^Γ` be the subfield of the elements fixed by `Γ`
(`Γ` finite). Then: (i) every `y ∈ F` is integral over `K`; (ii) `F/K` is a normal extension;
(iii) every `K`-algebra automorphism of `F` is of the form `y ↦ γ • y` for some `γ ∈ Γ`.
(`FixedPoints.isIntegral`, `FixedPoints.normal`, `FixedPoints.toAlgAut_surjective`.) Moreover `K`
has characteristic `0`, being a subfield of `F ⊇ ℚ`.

**Lemma A4 (the equation and its roots).** Fix `x₀ ∈ X` and let `f ∈ K[T]` be the minimal
polynomial of `x_{x₀}` over `K`. Then `f` is monic and irreducible, `f` splits in `F`, and the
roots of `f` in `F` are exactly the `x_i`, `i ∈ X`. Hence `r_F : i ↦ x_i` is a bijection from `X`
onto the set `Roots_F(f)` of roots of `f` in `F`.

*Proof.* `f` is monic irreducible because `x_{x₀}` is integral over `K` (A3 (i)); it splits in `F`
because `F/K` is normal (A3 (ii)). Let `i ∈ X`. By transitivity `i = γ x₀` for some `γ ∈ Γ`, and
`y ↦ γ • y` is a `K`-algebra homomorphism `F → F` (it fixes `K` pointwise), so
`f(x_i) = f(γ • x_{x₀}) = γ • f(x_{x₀}) = 0`. Conversely let `y ∈ F` with `f(y) = 0`. As `f` is
irreducible and monic, `f` is the minimal polynomial of `y` over `K`; so `y` and `x_{x₀}` have the
same minimal polynomial, and since `F/K` is normal there is a `K`-automorphism `φ` of `F` with
`y = φ(x_{x₀})` (mathlib `Normal.minpoly_eq_iff_mem_orbit`). By A3 (iii), `φ = (γ • ·)` for some
`γ ∈ Γ`, so `y = γ • x_{x₀} = x_{γ x₀}`. Injectivity of `r_F` is A2. ∎

**Lemma A5 (the degree).** `deg f = |X|`.

*Proof.* `K` has characteristic `0` and `f` is irreducible, so `f` is separable; `f` splits in
`F`; hence the number of roots of `f` in `F` is `deg f` (mathlib `card_rootSet_eq_natDegree`).
By A4 that number is `|X|`. ∎

**Lemma A6 (the group).** Let `Gal(f)` be mathlib's `f.Gal` (the automorphism group of the abstract
splitting field), which acts on `Roots_E(f)` for every extension `E` of `K` in which `f` splits
(`Gal.galAction`). Let `ρ : Γ → Gal(f)` be the composite of `γ ↦ (γ • ·) ∈ Aut(F/K)` with mathlib's
restriction homomorphism `Gal.restrict f F : Aut(F/K) → Gal(f)`. Then
(a) `ρ(γ) • r_F(i) = r_F(γ i)` for all `γ ∈ Γ`, `i ∈ X`;
(b) `ρ` is surjective; (c) `ρ` is injective.

*Proof.* (a) mathlib `Gal.restrict_smul`: for `φ ∈ Aut(F/K)` and `y ∈ Roots_F(f)`,
`(restrict φ) • y = φ(y)`. With `φ = (γ • ·)` and `y = x_i`: `φ(y) = x_{γ i}`.
(b) `Gal.restrict f F` is surjective because `F/K` is normal (`Gal.restrict_surjective`), and
`γ ↦ (γ • ·)` is surjective onto `Aut(F/K)` by A3 (iii).
(c) If `ρ(γ) = 1` then by (a) `r_F(γ i) = r_F(i)` for all `i`, so `γ i = i` for all `i` (A4:
`r_F` injective), i.e. `γ = 1`. ∎

**Lemma A7 (passing to an algebraically closed field).** Let `Ω` be an algebraic closure of `K`
(for A7 alone any field extension of `K` in which `f` splits would do, and `F` and `Ω` need not
be related; but the application in A8 (b) and A9 / `ReciproqueGalois` needs `Ω` algebraically
closed and in `Type`, so take `Ω = AlgebraicClosure (Corps Γ)`, i.e. `Cloture Γ`).
Mathlib provides a bijection `θ : Roots_F(f) → Roots_Ω(f)` which commutes with the action of
`Gal(f)` (`Gal.rootsEquivRoots`, `Gal.smul_rootsEquivRoots`). Put `r = θ ∘ r_F : X → Roots_Ω(f)`.
Then `r` is a bijection and, for all `γ ∈ Γ`, `i ∈ X`,
`galActionHom f Ω (ρ γ) (r i) = r (γ i)`.

*Proof.* `ρ(γ) • θ(r_F i) = θ(ρ(γ) • r_F i) = θ(r_F(γ i))` by equivariance of `θ` and A6 (a); and
`galActionHom f Ω g y = g • y` by definition. ∎

**Lemma A8 (transfer of properties).**
(a) `|Gal(f)| = |Γ|`.
(b) If `Γ` is solvable, every root of `f` in `Ω` lies in `solvableByRad K Ω`
(`SolubleParRadicaux f Ω`).
(c) If `Γ` acts primitively on `X`, then `groupe f Ω` (the image of `Gal(f)` in
`Sym(Roots_Ω(f))`) acts primitively on `Roots_Ω(f)`.

*Proof.* (a) `ρ` is a bijection (A6). (b) `Gal(f)` is a homomorphic image of `Γ` (A6 (b)), hence
solvable. Let `x ∈ Ω` be a root of `f`; its minimal polynomial `m` over `K` divides `f`, so
`Gal(m)` is a quotient of `Gal(f)` (`Gal.restrictDvd_surjective`), hence solvable, and
`x ∈ solvableByRad K Ω` by the repository's converse of Abel–Ruffini
(`mem_solvableByRad_of_isSolvable`; characteristic `0`, `Ω` algebraically closed). (c) Let
`φ : Γ → groupe f Ω`, `γ ↦ galActionHom f Ω (ρ γ)`. By A7, `r` is a surjective map with
`r(γ i) = φ(γ) • r(i)`. Mathlib's `MulAction.IsPreprimitive.of_surjective` says precisely that a
surjective equivariant map (along any map of groups `φ`) carries a primitive action to a
primitive action. (Its proof: transitivity passes to the image; if `B` is a block downstairs then
`r⁻¹(B)` is a block upstairs, hence empty-or-singleton or everything, hence so is
`B = r(r⁻¹ B)`.) ∎

**Proposition A9 (what the printed claim would give).** Let `ℓ` be a prime and assume
`ReciproqueGalois ℓ`. Let `X` be a finite set (a type in `Type`), `Γ ≤ Sym(X)` solvable and
primitive, `|X| = ℓ^ν` with `ν ≠ 0`, `ℓ^ν ≠ 9, 25`. Then `|Γ|` divides `ℓ^ν (ℓ^ν − 1) ν`.

*Proof.* A primitive action is transitive, so A1–A8 apply (take any `x₀ ∈ X`; `X` is nonempty as
`|X| = ℓ^ν ≥ 2`). The equation `f` over `K`, with `Ω` the algebraic closure of `K`, satisfies all
hypotheses of `ReciproqueGalois ℓ`: `K, Ω` are fields in `Type` (because `X` is), `K` has
characteristic `0`, `Ω` is algebraically closed, `f` splits in `Ω`, `f` is irreducible (A4),
`deg f = ℓ^ν` (A5), `groupe f Ω` is primitive (A8 (c)) and `f` is solvable by radicals (A8 (b)).
The existing `reciproque_borne` gives `|Gal(f)| ∣ ℓ^ν (ℓ^ν − 1) ν`, and `|Gal(f)| = |Γ|`
(A8 (a)). ∎

### Part B. The groups `W(F) = AGL(1, F) ≀ C₂`

Throughout Part B, `F` is a field. For `a, b, n₁, n₂ ∈ F` consider the maps `F × F → F × F`

* `d = d(a, b; n₁, n₂) : (k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` ("droite"),
* `c = c(a, b; n₁, n₂) : (k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)` ("croisée").

A permutation `σ` of `F × F` *is droite with multipliers `(a, b)`* (`EstDroite a b σ`) if
`σ = d(a, b; n₁, n₂)` for some `n₁, n₂`, and *is croisée with multipliers `(a, b)`*
(`EstCroisee a b σ`) if `σ = c(a, b; n₁, n₂)` for some `n₁, n₂`.

**Lemma B1 (composition rules).** For permutations `σ, τ` of `F × F`:
1. droite`(a,b)` ∘ droite`(a',b')` is droite`(a a', b b')`;
2. droite`(a,b)` ∘ croisée`(a',b')` is croisée`(a a', b b')`;
3. croisée`(a,b)` ∘ droite`(a',b')` is croisée`(a b', b a')`;
4. croisée`(a,b)` ∘ croisée`(a',b')` is droite`(a b', b a')`;
5. if `a, b ≠ 0`, the inverse of a droite`(a,b)` is droite`(a⁻¹, b⁻¹)`, and the inverse of a
   croisée`(a,b)` is croisée`(b⁻¹, a⁻¹)`;
6. no permutation is both droite`(a,b)` with `a ≠ 0` and croisée`(a',b')`.

*Proof.* 1–4: direct substitution. For instance 3: if `τ(k) = (a' k₁ + n₁', b' k₂ + n₂')` and
`σ(k) = (a k₂ + n₁, b k₁ + n₂)`, then `σ(τ(k)) = (a b' k₂ + (a n₂' + n₁), b a' k₁ + (b n₁' + n₂))`.
5: if `σ(k) = (a k₁ + n₁, b k₂ + n₂)` then `σ(a⁻¹ k₁ − a⁻¹ n₁, b⁻¹ k₂ − b⁻¹ n₂) = k`, so
`σ⁻¹ k = (a⁻¹ k₁ + (−a⁻¹ n₁), b⁻¹ k₂ + (−b⁻¹ n₂))`; if `σ(k) = (a k₂ + n₁, b k₁ + n₂)` then
`σ(b⁻¹ k₂ − b⁻¹ n₂, a⁻¹ k₁ − a⁻¹ n₁) = k`. 6: if `σ` is both, compare first coordinates at
`(1, 0)` and at `(0, 0)`: `a + n₁ = n₁'` and `n₁ = n₁'`, so `a = 0`. ∎

**Definition.** `W(F)` ("couronne") is the set of permutations of `F × F` which are droite`(a,b)`
or croisée`(a,b)` for some `a, b ≠ 0`; `P(F)` ("produit") is the set of those which are
droite`(a,b)` for some `a, b ≠ 0`. By B1 (1–5) both are subgroups of `Sym(F × F)` (the identity is
droite`(1,1)`), and `P(F) ≤ W(F)`. The exchange `ε : (k₁, k₂) ↦ (k₂, k₁)` is croisée`(1,1)`, so
`ε ∈ W(F)`. For `a, b ≠ 0` the map `d(a, b; n₁, n₂)` is a permutation (inverse given in B1 (5)),
so it belongs to `P(F)`.

**Lemma B2.** `P(F)` has index `2` in `W(F)`.

*Proof.* (Criterion `Subgroup.index_eq_two_iff`: `H` has index 2 iff there is `a` such that for
every `b` exactly one of `b a ∈ H`, `b ∈ H` holds.) Take `a = ε`. If `b ∈ W(F)` is droite, then
`b ∈ P(F)` and `b ε` is croisée (B1 (2)), hence not in `P(F)` (B1 (6)). If `b` is croisée, then
`b ε` is droite (B1 (4)) so `b ε ∈ P(F)`, and `b ∉ P(F)` (B1 (6)). ∎

**Lemma B3 (primitivity).** `W(F)` acts transitively on `F × F`. If `F` has an element
`c ∉ {0, 1}` (i.e. `|F| ≥ 3`), the action is primitive.

*Proof.* Transitivity: the translation `d(1, 1; y₁ − x₁, y₂ − x₂)` maps `x` to `y`.
Primitivity: by transitivity it suffices to show that every block `B` containing `0 = (0,0)` is
trivial, i.e. `B` is a subsingleton or `B = F × F` (mathlib's `IsTrivialBlock B`:
`B.Subsingleton ∨ B = Set.univ`; criterion `IsPreprimitive.of_isTrivialBlock_base`). Recall that a
block satisfies: if `g ∈ W(F)`, `v ∈ B` and `g v ∈ B`, then `g B = B`, in particular `g w ∈ B` for
all `w ∈ B` (`IsBlock.smul_eq_of_mem`). Let `B` be a block with `0 ∈ B`. Then:
* (diag) for `a, b ≠ 0` and `w ∈ B`: `(a w₁, b w₂) ∈ B` (apply the remark to `g = d(a,b;0,0)`,
  `v = 0`, `g 0 = 0`);
* (swap) for `w ∈ B`: `(w₂, w₁) ∈ B` (`g = ε`, `v = 0`);
* (trans) for `u, w ∈ B`: `(w₁ + u₁, w₂ + u₂) ∈ B` (`g = d(1,1;u₁,u₂)`, `v = 0`, `g 0 = u ∈ B`).

Suppose `B ⊄ {0}` and pick `v ∈ B`, `v ≠ 0`.
*Step 1: if `v ∈ B` has `v₁ ≠ 0`, then `(x, 0) ∈ B` for every `x ∈ F`.* By (diag) with `(c, 1)`:
`(c v₁, v₂) ∈ B`; by (diag) with `(−1, −1)` (note `−1 ≠ 0` in every field): `(−v₁, −v₂) ∈ B`; by
(trans): `(c v₁ − v₁, v₂ − v₂) = ((c − 1) v₁, 0) ∈ B`, and `(c − 1) v₁ ≠ 0` because `c ≠ 1`. For
`x ≠ 0`, (diag) with `(x / ((c − 1) v₁), 1)` gives `(x, 0) ∈ B`; and `(0, 0) ∈ B`.
*Step 2.* If `v₁ ≠ 0` apply Step 1 to `v`; otherwise `v₂ ≠ 0` and we apply Step 1 to
`(v₂, v₁) ∈ B` (swap). So `(x, 0) ∈ B` for all `x`. By (swap), `(0, y) ∈ B` for all `y`. By (trans)
with `u = (x, 0)`, `w = (0, y)`: `(x, y) ∈ B`. So `B` is everything. ∎

(For `|F| = 2` the statement is false: `W(𝔽₂)` has order `8` on `4` points. In the application
`|F| = ℓ² ≥ 4`.)

**Lemma B4 (solvability).** `W(F)` is solvable; more precisely its third derived subgroup is
trivial.

*Proof.* Let `T ≤ P(F)` be the set of droite`(1,1)` elements (translations).
(i) `[W, W] ≤ P`: for `g, h ∈ W`, the commutator `g h g⁻¹ h⁻¹` is droite, by B1 in each of the
four cases (droite/croisée for `g` and for `h`): e.g. `g, h` croisées: `g h` droite, `g⁻¹`
croisée, `(g h) g⁻¹` croisée, `h⁻¹` croisée, product droite; the multipliers are products of
nonzero elements and their inverses, hence nonzero.
(ii) `[P, P] ≤ T`: for `g` droite`(a,b)` and `h` droite`(a',b')`, the commutator is
droite`(a a' a⁻¹ a'⁻¹, b b' b⁻¹ b'⁻¹)` = droite`(1,1)`.
(iii) `[T, T] = 1`: translations commute.
Hence `D¹ ≤ P`, `D² ≤ [P,P] ≤ T`, `D³ ≤ [T,T] = 1`. ∎

**Lemma B5 (a divisor of the order).** If `F` is finite with `q` elements,
`2 (q − 1)²` divides `|W(F)|`.

*Proof.* `δ : F^× × F^× → Sym(F × F)`, `(a, b) ↦ d(a, b; 0, 0)`, is an injective group
homomorphism with values in `P(F)` (evaluate at `(1,1)` for injectivity). By Lagrange
`(q − 1)² = |F^× × F^×|` divides `|P(F)|`. By B2, `|W(F)| = 2 |P(F)|`. ∎

(In fact `|W(F)| = 2 q² (q − 1)²`; the exact order is not needed.)

**Lemma B6 (arithmetic).** For every integer `ℓ ≥ 2`, `2 (ℓ² − 1)²` does not divide
`ℓ⁴ (ℓ⁴ − 1) · 4`.

*Proof.* Put `m = ℓ² − 1`, so `m ≥ 3`, `ℓ² = m + 1`, `ℓ⁴ = (m + 1)²`,
`ℓ⁴ − 1 = (m + 1)² − 1 = m (m + 2)`. Suppose `2 m² ∣ (m + 1)² · m (m + 2) · 4`. Since
`(m + 1)² · m (m + 2) · 4 = 2 m · [2 (m + 1)² (m + 2)]` and `2 m² = 2 m · m` with `2 m > 0`, we
get `m ∣ 2 (m + 1)² (m + 2)`. Now `2 (m + 1)² (m + 2) = m (2 m² + 8 m + 10) + 4` (expand:
`2 (m² + 2 m + 1)(m + 2) = 2 m³ + 8 m² + 10 m + 4`). Hence `m ∣ 4`, so `m ≤ 4`, so `m ∈ {3, 4}`.
`m = 3` is impossible since `3 ∤ 4`. `m = 4` means `ℓ² = 5`, impossible (`ℓ = 2` gives `4`,
`ℓ ≥ 3` gives `ℓ² ≥ 9`). ∎

**Theorem B7 (`not_reciproqueGalois`).** For every prime `ℓ`, `ReciproqueGalois ℓ` is false.

*Proof.* Assume `ReciproqueGalois ℓ`. Let `𝔽 = GaloisField ℓ 2`, a field (in `Type`) with
`|𝔽| = ℓ²` elements (`GaloisField.card ℓ 2`, as `2 ≠ 0`). `X = 𝔽 × 𝔽` has `ℓ⁴` elements, and
`Γ = W(𝔽) ≤ Sym(X)`. Since `|𝔽| = ℓ² ≥ 4 > 2`, the unit group `𝔽^×` has `ℓ² − 1 ≥ 2` elements,
so there is a unit `u ≠ 1`, i.e. an element `c = u ∉ {0, 1}`; by B3 `Γ` is primitive, and by B4 it
is solvable. Take `ν = 4`: `ν ≠ 0`; `ℓ⁴ ≠ 9` and `ℓ⁴ ≠ 25` because `ℓ⁴ = 16` for `ℓ = 2` and
`ℓ⁴ ≥ 81` for `ℓ ≥ 3`. By Proposition A9, `|Γ| ∣ ℓ⁴ (ℓ⁴ − 1) · 4`. By B5,
`2 (ℓ² − 1)² ∣ |Γ|`. Hence `2 (ℓ² − 1)² ∣ ℓ⁴ (ℓ⁴ − 1) · 4`, contradicting B6 (`ℓ ≥ 2`). ∎

### Part C. The corrected converse

**Definition (affine group).** For a prime `p` and a `ℤ/p`-vector space `V`, `AGL(V)` is the set
of permutations `σ` of `V` for which there are an invertible `ℤ/p`-linear map `A : V → V` and
`b ∈ V` with `σ(k) = A k + b` for all `k`.

**Lemma C1.** `AGL(V)` is a subgroup of `Sym(V)`.

*Proof.* `id = (A = id, b = 0)`. If `σ = (A, b)`, `τ = (A', b')` then
`σ τ (k) = A (A' k + b') + b = (A A') k + (A b' + b)`. If `σ = (A, b)` then
`σ (A⁻¹ k − A⁻¹ b) = k`, so `σ⁻¹ = (A⁻¹, −A⁻¹ b)`. ∎

**Lemma C2.** If `σ` is a permutation of `V`, `A : V → V` a `ℤ/p`-linear map (not assumed
invertible) and `b ∈ V` with `σ(k) = A k + b` for all `k`, then `σ ∈ AGL(V)`.

*Proof.* `A k = σ(k) − b`. Injective: `A k = A k'` gives `σ k = σ k'`, so `k = k'`. Surjective:
for `y ∈ V`, `A(σ⁻¹(y + b)) = (y + b) − b = y`. So `A` is a linear bijection, i.e. an invertible
linear map. (No finiteness is used.) ∎

**Lemma C3 (`AΓL(1, p^ν) ≤ AGL(ν, p)`).** Let `K` be a finite field of characteristic `p`. Every
`σ ∈ AGammaL K`, `σ(k) = A k^{p^r} + B` (`A ≠ 0`), is in `AGL(K)`.

*Proof.* `k ↦ A · k^{p^r}` is `ℤ/p`-linear, being the composite of the `r`-th power of the
Frobenius (a `ℤ/p`-algebra automorphism of `K`) with multiplication by `A`; apply C2. ∎

**Theorem C4 (`reciproque_corrigee`).** Let `K` be a field of characteristic `0`, `Ω ⊇ K`
algebraically closed, `f ∈ K[T]` irreducible of degree `p^ν` (`p` prime, `ν ≠ 0`), such that the
group of `f` acts primitively on the roots of `f` in `Ω` and `f` is solvable by radicals. Then
there is a bijection `e : GaloisField p ν → Roots_Ω(f)` such that, writing
`σ^e = e⁻¹ ∘ σ ∘ e` (this is `groupeIndice f e σ`): (i) `σ^e ∈ AGL(GaloisField p ν)` for every
`σ ∈ Gal(f)`; (ii) for every `b ∈ GaloisField p ν` there is `σ ∈ Gal(f)` with `σ^e(k) = k + b`
for all `k`.

*Proof.* As in the existing `degre_primitive`: `f` has a root `x ∈ Ω`, which is solvable by
radicals, so `Gal(f)` is solvable (mathlib `isSolvable_gal_of_irreducible`), so its image
`G = groupe f Ω ≤ Sym(Roots_Ω(f))` is solvable. `G` acts faithfully (it is a group of
permutations) and primitively (hypothesis) on the finite set `Y = Roots_Ω(f)`, and
`|Y| = deg f = p^ν ≥ 2` (`f` separable and split), so `Y` has at least two points. By
`exists_affine_indexing` there are a prime `q`, `μ ∈ ℕ`, and a bijection `e₀ : Y → (ℤ/q)^μ` such
that every `g ∈ G` satisfies `e₀(g y) = M (e₀ y) + c` for some matrix `M` and vector `c`
(depending on `g`), and for every `b` some `g ∈ G` satisfies `e₀(g y) = e₀ y + b`.
Counting: `q^μ = |Y| = p^ν`. As `p^ν > 1`, `μ ≠ 0`; then `q ∣ p^ν`, so `q ∣ p`, so `q = p` (both
prime); then `p^μ = p^ν` with `p ≥ 2` gives `μ = ν`.
`GaloisField p ν` is a `ℤ/p`-vector space of dimension `ν` (`GaloisField.finrank`, `ν ≠ 0`), so
there is a `ℤ/p`-linear isomorphism `B : GaloisField p ν → (ℤ/p)^ν` (coordinates in a basis).
Put `e = e₀⁻¹ ∘ B`. For `σ ∈ Gal(f)` let `g ∈ G` be its image; then for all `k`,
`σ^e(k) = B⁻¹(e₀(g(e₀⁻¹(B k)))) = B⁻¹(M (B k) + c) = (B⁻¹ M B) k + B⁻¹ c`, and `B⁻¹ M B` is
`ℤ/p`-linear, so `σ^e ∈ AGL` by C2 (which is why the invertibility of `M` need not be used). For
(ii): given `b`, take `g ∈ G` with `e₀(g y) = e₀ y + B b` and `σ ∈ Gal(f)` with image `g` (`G` is
the image of `Gal(f)`); then `σ^e(k) = B⁻¹(B k + B b) = k + b`. ∎

**Corollary C5 (`reciproque_corrigee_degre`).** If `f` is irreducible, not of degree `1`, with
primitive group and solvable by radicals, then `deg f = ℓ^ν` for a prime `ℓ` and some `ν ≠ 0`,
and the conclusion of C4 holds.

*Proof.* The existing `degre_primitive` gives `deg f = q^k` with `q` prime; `k ≠ 0` since
`deg f ≠ 1`; apply C4. ∎

---

## 4. LEAN ARCHITECTURE

### 4.0 What has been machine-checked

A single scratch file containing **all** the code of the three files below (same declarations,
same proofs, in the same order, with the three namespaces one after the other) was type-checked
with `python .lake-local/leanc.py`:

* `.lake-local/scratch/reciproque/RAll.lean` (imports `GaloisOeuvres.TheorieNombres` and
  `GaloisOeuvres.EquationsPrimitives`).

**Result (2026-11-27): `[OK]`, no error and no warning** (`python .lake-local/leanc.py
.lake-local/scratch/reciproque/RAll.lean`, Lean v4.36.0 / mathlib v4.36.0, 152 s of a warm run).
A first run found a single error (`diag_mem`: the two `≠ 0` proofs passed to `droite_est` must be
given explicitly, `droite_est _ _ _ _ u.1.ne_zero u.2.ne_zero`) and three "unused section
variable" warnings (fixed with `omit … in` before `aeval_lettre`, `exists_lettre_of_root`,
`smul_mem_of_block`); the code in the Appendix is the corrected, re-checked version. Since the
file contains `theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : ¬ ReciproqueGalois ℓ` and
`reciproque_corrigee`, both target statements are proved in Lean, modulo the split into three
files (RISKS 1).

**Split files, checked separately.** Exact copies of the two auxiliary reference files, with
their final import lists, were also type-checked on their own (byte-identical to
`reference/TheorieNombresCloseAux1.lean` and `reference/TheorieNombresCloseAux2.lean`):

* `.lake-local/scratch/reciproque-lean-critic/A1.lean` (Aux1, `import GaloisOeuvres.Radicaux`
  only): `[OK]`, no warning (126 s);
* `.lake-local/scratch/reciproque-lean-critic/A2.lean` (Aux2, `import GaloisOeuvres.Basic`
  only): `[OK]`, no warning (707 s).

The third file `TheorieNombresClose.lean` cannot be checked on its own before Aux1 and Aux2 exist
as `.olean` files; its code is the third part of `RAll.lean`, which compiled.

The complete code is reproduced in the Appendix (section 8), split into the three target files,
and the same three files are stored ready to copy in
`.lake-local/plans/galois-reciproque/reference/`. The implementer's job is: copy the three files
to `GaloisOeuvres/`, then **build strictly in this order**, one compile at a time, each with
`python .lake-local/leanc.py <file> --olean`:

1. `GaloisOeuvres/TheorieNombresCloseAux1.lean`,
2. `GaloisOeuvres/TheorieNombresCloseAux2.lean`,
3. `GaloisOeuvres/TheorieNombresClose.lean`,
4. only then (final wiring, section 7) add the three imports to `GaloisOeuvres.lean`.

A cold compile can take about 35 minutes (the first `RAll.lean` run took 2060 s); a timeout of the
Bash call is not a failure, just run the same command again. Fix whatever the import list of
file 3 exposes (see RISKS 1).
No `sorry`, `admit`, axiom, `native_decide`, `unsafe` or `implemented_by` occurs in the code.

Conventions followed (taken from the neighbouring files): French names for the objects Galois
names (`couronne`, `produit`, `EstDroite`, `lettre`, `racine`, …), English docstrings, two-space
indentation, lines ≤ 100 characters where practical, `namespace GaloisOeuvres.<Piece>`,
`open Polynomial`. **A new file must not contain a `/-!` block whose first line is
`## [piece.unit] …`**: `scripts/unit_table.py` treats every such block as a unit and reports
duplicate unit ids. Use an ordinary module docstring `/-! # Title … -/` at the top of each new
file (suggested texts below).

### 4.1 File 1: `GaloisOeuvres/TheorieNombresCloseAux1.lean` (≈ 200 lines)

* Module: `GaloisOeuvres.TheorieNombresCloseAux1`.
* Imports: `import GaloisOeuvres.Radicaux` (this brings `Mathlib`, `groupe`,
  `SolubleParRadicaux`, `mem_solvableByRad_of_isSolvable`).
* `open Polynomial`; namespace `GaloisOeuvres.TheorieNombres.Realisation`.
* Purpose: Part A. Every finite transitive group of permutations of a finite type `X : Type` is
  the group of an irreducible equation of degree `|X|` over a field of characteristic `0`, with the
  given action on the roots.
* Suggested module docstring: "# Every finite transitive permutation group is the group of an
  equation. Auxiliary file for the unit `nombres.reciproque` of *Sur la théorie des nombres*:
  the field `K` of the rational functions of the letters `x_i` (`i ∈ X`) invariant under `Γ`, the
  equation `∏ (T - x_i)` over `K` (defined as the minimal polynomial of one letter), and the
  identification of its group with `Γ`."

Main declarations (exact statements; proofs in the Appendix):

```lean
section Action
variable (X : Type)

abbrev Fonctions : Type := FractionRing (MvPolynomial X ℚ)                     -- F
noncomputable def lettre (i : X) : Fonctions X :=                               -- x_i
  algebraMap (MvPolynomial X ℚ) (Fonctions X) (MvPolynomial.X i)
theorem lettre_injective : Function.Injective (lettre X)                        -- A2
noncomputable def permRing : Equiv.Perm X →* (MvPolynomial X ℚ ≃+* MvPolynomial X ℚ)
noncomputable instance actionPerm : MulSemiringAction (Equiv.Perm X) (Fonctions X)   -- A1
theorem smul_lettre (σ : Equiv.Perm X) (i : X) : σ • lettre X i = lettre X (σ i)     -- A1
end Action

theorem soluble_of_isSolvable_gal {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] {p : K[X]} (hp : Irreducible p) (h : Group.IsSolvable p.Gal) :
    SolubleParRadicaux p Ω

section Corps
variable {X : Type} (Γ : Subgroup (Equiv.Perm X))

theorem smul_lettre' (γ : Γ) (i : X) : γ • lettre X i = lettre X (γ • i)
instance faithful : FaithfulSMul Γ (Fonctions X)                                -- A2
abbrev Corps : Type := ↥(FixedPoints.subfield Γ (Fonctions X))                  -- K = F^Γ
instance : CharZero (Corps Γ)
noncomputable def equation (x₀ : X) : (Corps Γ)[X] := minpoly (Corps Γ) (lettre X x₀)   -- f
abbrev Cloture : Type := AlgebraicClosure (Corps Γ)                             -- Ω
instance splitsΩ (x₀ : X) :
    Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Cloture Γ))).Splits)

variable [Finite X] (x₀ : X)

theorem equation_irreducible : Irreducible (equation Γ x₀)                      -- A4
instance splitsF : Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Fonctions X))).Splits)
noncomputable def versGal : Γ →* (equation Γ x₀).Gal :=                         -- ρ (A6)
  (Gal.restrict (equation Γ x₀) (Fonctions X)).comp
    (MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X))
theorem versGal_surjective : Function.Surjective (versGal Γ x₀)                 -- A6 (b)
theorem soluble [Group.IsSolvable Γ] : SolubleParRadicaux (equation Γ x₀) (Cloture Γ)  -- A8 (b)

section Transitif
variable [MulAction.IsPretransitive Γ X]

theorem aeval_lettre (i : X) : aeval (lettre X i) (equation Γ x₀) = 0           -- A4
theorem exists_lettre_of_root {y : Fonctions X} (hy : aeval y (equation Γ x₀) = 0) :
    ∃ i, y = lettre X i                                                         -- A4
noncomputable def racineF : X ≃ (equation Γ x₀).rootSet (Fonctions X)           -- r_F (A4)
theorem versGal_smul (γ : Γ) (i : X) :
    versGal Γ x₀ γ • racineF Γ x₀ i = racineF Γ x₀ (γ • i)                      -- A6 (a)
theorem versGal_injective : Function.Injective (versGal Γ x₀)                   -- A6 (c)
theorem natDegree_equation : (equation Γ x₀).natDegree = Nat.card X             -- A5
noncomputable def racine : X ≃ (equation Γ x₀).rootSet (Cloture Γ) :=           -- r (A7)
  (racineF Γ x₀).trans (Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ))
theorem galActionHom_racine (γ : Γ) (i : X) :
    Gal.galActionHom (equation Γ x₀) (Cloture Γ) (versGal Γ x₀ γ) (racine Γ x₀ i) =
      racine Γ x₀ (γ • i)                                                       -- A7
theorem card_gal : Nat.card (equation Γ x₀).Gal = Nat.card Γ                    -- A8 (a)
end Transitif

theorem primitif [MulAction.IsPreprimitive Γ X] :
    MulAction.IsPreprimitive (groupe (equation Γ x₀) (Cloture Γ))
      ((equation Γ x₀).rootSet (Cloture Γ))                                     -- A8 (c)
end Corps
```

Implementation notes (all reflected in the Appendix code):

* `permRing`: `toFun σ := (MvPolynomial.renameEquiv ℚ σ).toRingEquiv`; `map_one'` and `map_mul'`
  by `RingEquiv.ext`, a `change` to `MvPolynomial.rename …`, then `MvPolynomial.rename_id`,
  `MvPolynomial.rename_rename`.
* `actionPerm := MulSemiringAction.compHom (Fonctions X)
  ((IsFractionRing.ringEquivOfRingEquivHom (MvPolynomial X ℚ) (Fonctions X)).comp (permRing X))`.
  The action of a subgroup `Γ` is then mathlib's `Subgroup.mulSemiringAction`; nothing has to be
  declared for `Γ`, and `γ • y = (γ : Equiv.Perm X) • y` holds by `rfl` (this is how
  `smul_lettre'` is proved: `smul_lettre X (γ : Equiv.Perm X) i`).
* The equation is **`minpoly (Corps Γ) (lettre X x₀)`**, not a hand-made product `∏ (T − x_i)`:
  irreducibility is then `minpoly.irreducible (FixedPoints.isIntegral …)`, the splitting in `F` is
  `Normal.splits` (instance `FixedPoints.normal`), and the set of roots is obtained from
  `Normal.minpoly_eq_iff_mem_orbit` + `FixedPoints.toAlgAut_surjective` (Lemma A4). Nothing about
  `FixedPoints.minpoly`/`prodXSubSMul` is unfolded.
* `Ω := AlgebraicClosure (Corps Γ)` (not an algebraic closure of `F`): `F` and `Ω` are linked only
  through mathlib's `Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ)` and its
  equivariance `Gal.smul_rootsEquivRoots` (Lemma A7), so no `IsScalarTower` is ever needed.
* **Observed pitfall**: with the concrete fields, `mem_rootSet` for the pair
  `(Corps Γ, Cloture Γ)` makes instance synthesis time out on
  `Module.IsTorsionFree (Corps Γ) (Cloture Γ)` (it works for `(Corps Γ, Fonctions X)`).
  Therefore `soluble` is proved through the generic lemma `soluble_of_isSolvable_gal` (stated for
  arbitrary fields `K, Ω`, a copy of `Memoire.DegrePremier.soluble_of_isSolvable_gal`), and no
  other statement about roots in `Cloture Γ` uses `mem_rootSet`.
* **Notation, not a variable.** With `open Polynomial`, `(Corps Γ)[X]` is the polynomial-ring
  notation `Polynomial (Corps Γ)`; the letter `X` there is *not* the section variable
  `X : Type` (the type of the letters). This is correct (the reference code compiles) but
  misleading to read. Renaming the letter-type variable (e.g. to `α`) is cosmetic and costs a
  recompile; do it only if Aux1 has to be edited for another reason.
* **Instance hygiene (optional).** `actionPerm`, `splitsΩ` and `splitsF` are global instances;
  since the root module `GaloisOeuvres.lean` imports everything, `actionPerm` puts an
  `Equiv.Perm X` action on every `FractionRing (MvPolynomial X ℚ)` of the library. Nothing
  conflicts today (no other `Equiv.Perm` action on `MvPolynomial` or its fraction field exists in
  mathlib or the repository; mathlib's `IsFractionRing.mulSemiringAction` is a `def`, not an
  instance). The reference code keeps them global; making them `scoped instance`s of the
  namespace `Realisation` (and adding `open scoped Realisation` in file 3) is an acceptable
  variant at the cost of one extra compile (RISKS 3).
* `primitif`: exactly the pattern of `EquationsPrimitives.card_eq_prime_pow'`: an equivariant map
  `j : X →ₑ[φ] rootSet` with `toFun := racine Γ x₀`,
  `φ γ := (Gal.galActionHom _ _).rangeRestrict (versGal Γ x₀ γ)`, then
  `MulAction.IsPreprimitive.of_surjective (f := j) (racine Γ x₀).surjective`.

### 4.2 File 2: `GaloisOeuvres/TheorieNombresCloseAux2.lean` (≈ 300 lines)

* Module: `GaloisOeuvres.TheorieNombresCloseAux2`.
* Imports: `import GaloisOeuvres.Basic` (only `Mathlib` is used).
* namespace `GaloisOeuvres.TheorieNombres.Couronne`; `open MulAction`;
  `variable {F : Type*} [Field F]`.
* Purpose: Part B (Lemmas B1–B6): the group `AGL(1, F) ≀ C₂` over an arbitrary field, its
  primitivity when `F` has an element other than `0, 1`, its solvability, a divisor of its order,
  and the arithmetic lemma.
* Suggested module docstring: "# The groups `AGL(1, F) ≀ C₂`. Auxiliary file for the unit
  `nombres.reciproque`: for a field `F` with at least three elements, the group of the
  substitutions `(k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` and `(k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)` of
  `F × F` is primitive and solvable, and its order is divisible by `2 (|F| - 1)²`. For `F = ℤ/p`
  this is `EquationsPrimitives.couronne`."

Main declarations:

```lean
def EstDroite (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.1 + n₁, b * k.2 + n₂)
def EstCroisee (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.2 + n₁, b * k.1 + n₂)

-- B1, with `variable {a b a' b' : F} {σ τ : Equiv.Perm (F × F)}`
theorem dd (h : EstDroite a b σ) (h' : EstDroite a' b' τ) : EstDroite (a * a') (b * b') (σ * τ)
theorem dc (h : EstDroite a b σ) (h' : EstCroisee a' b' τ) : EstCroisee (a * a') (b * b') (σ * τ)
theorem cd (h : EstCroisee a b σ) (h' : EstDroite a' b' τ) : EstCroisee (a * b') (b * a') (σ * τ)
theorem cc (h : EstCroisee a b σ) (h' : EstCroisee a' b' τ) : EstDroite (a * b') (b * a') (σ * τ)
theorem d_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstDroite a b σ) : EstDroite a⁻¹ b⁻¹ σ⁻¹
theorem c_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstCroisee a b σ) : EstCroisee b⁻¹ a⁻¹ σ⁻¹
theorem not_d_c (h : EstDroite a b σ) (h' : EstCroisee a' b' σ) (ha : a ≠ 0) : False

def droite (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) : Equiv.Perm (F × F)   -- k ↦ (a k₁+n₁, b k₂+n₂)
def echange : Equiv.Perm (F × F) := Equiv.prodComm _ _
theorem droite_est (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    EstDroite a b (droite a b n₁ n₂ ha hb)
theorem echange_est : EstCroisee (1 : F) 1 echange

def couronne (F : Type*) [Field F] : Subgroup (Equiv.Perm (F × F))           -- W(F)
  -- carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ (EstDroite a b σ ∨ EstCroisee a b σ)}
def produit (F : Type*) [Field F] : Subgroup (Equiv.Perm (F × F))            -- P(F)
  -- carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ EstDroite a b σ}
theorem produit_le_couronne : produit F ≤ couronne F
theorem index_produit : ((produit F).subgroupOf (couronne F)).index = 2      -- B2

theorem smul_mem_of_block {G : Subgroup (Equiv.Perm (F × F))} {B : Set (F × F)}
    (hB : IsBlock G B) {σ : Equiv.Perm (F × F)} (hσ : σ ∈ G) {v : F × F} (hv : v ∈ B)
    (hσv : σ v ∈ B) {w : F × F} (hw : w ∈ B) : σ w ∈ B
theorem ligne_sub {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {B : Set (F × F)}
    (hB : IsBlock (couronne F) B) (h0 : (0, 0) ∈ B) {v : F × F} (hv : v ∈ B) (hv1 : v.1 ≠ 0)
    (x : F) : (x, 0) ∈ B                                                     -- B3, Step 1
theorem couronne_primitif (h3 : ∃ c : F, c ≠ 0 ∧ c ≠ 1) :
    IsPreprimitive (couronne F) (F × F)                                      -- B3
theorem couronne_soluble : Group.IsSolvable (couronne F)                     -- B4

def diag : Fˣ × Fˣ →* Equiv.Perm (F × F)                                     -- δ of B5
theorem diag_injective : Function.Injective (diag (F := F))
theorem diag_mem (u : Fˣ × Fˣ) : diag u ∈ produit F
theorem two_mul_dvd_card [Finite F] : 2 * (Nat.card F - 1) ^ 2 ∣ Nat.card (couronne F)   -- B5
theorem exists_ne_zero_ne_one [Finite F] (h : 2 < Nat.card F) : ∃ c : F, c ≠ 0 ∧ c ≠ 1
theorem arith (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ¬ (2 * (ℓ ^ 2 - 1) ^ 2 ∣ ℓ ^ 4 * (ℓ ^ 4 - 1) * 4)                        -- B6
```

Implementation notes:

* Everything from `EstDroite` to `couronne_soluble` is the text of
  `EquationsPrimitives.lean` l. 675–897 with `ZMod p` replaced by `F`, `(p := p)` by `(F := F)`,
  `couronne p`/`produit p` by `couronne F`/`produit F`, and with the lemmas made public
  (`theorem` instead of `private lemma`; they live in their own namespace `Couronne`). The only
  mathematical change is in `ligne_sub`: the original uses the multipliers `(2, 1)` and
  `(−1, −1)` and needs `(2 : ZMod p) ≠ 0`; the new one uses `(c, 1)` and `(−1, −1)` and obtains
  `((c − 1) v₁, 0) ∈ B` (Lemma B3, Step 1). `ligne_sub` is stated for blocks of `couronne F`
  directly (the generality `produit ≤ G` of the original is not needed).
* `two_mul_dvd_card`: `Subgroup.card_dvd_of_injective` applied to
  `diag.codRestrict (produit F) diag_mem`, then `Nat.card_prod`, `Nat.card_units`;
  `Subgroup.subgroupOfEquivOfLe produit_le_couronne` to pass from `(produit F).subgroupOf
  (couronne F)` to `produit F`; `Subgroup.index_mul_card` and `index_produit`.
* `exists_ne_zero_ne_one`: `Nat.card Fˣ = Nat.card F − 1 > 1` (`Nat.card_units`), so `Fˣ` is
  nontrivial (`Finite.one_lt_card_iff_nontrivial`) and contains `u ≠ 1`.
* `arith`: follows Lemma B6 literally (`m := ℓ ^ 2 − 1`); only `omega`, `ring`, `norm_num`,
  `interval_cases` and the `Nat` lemmas `Nat.pow_le_pow_left`, `Nat.sub_eq_of_eq_add`,
  `Nat.add_sub_cancel`, `Nat.mul_dvd_mul_iff_left`, `Nat.dvd_add_right`, `Nat.le_of_dvd`. Powers
  of literals are never left to `omega` (they are introduced through `calc … := by norm_num`).
* **Brittle proofs (optional clean-up).** Some proofs in the reference code are fragile against a
  toolchain change: a non-terminal `simp` followed by `field_simp`/`ring` (`d_inv`, `c_inv`,
  `droite`) and very long `simp only [...]; tauto` lines in `couronne_soluble` (the four `≠ 0`
  side goals). They compile on the pinned toolchain (v4.36.0). An implementer who must touch the
  file anyway may factor the side goals into one helper lemma (for example
  `a ≠ 0 → b ≠ 0 → a * b * a⁻¹ * b⁻¹ ≠ 0`, plus the mixed variants) and replace each non-terminal
  `simp` by `simp only [...]`; otherwise leave the code as it is.

### 4.3 File 3: `GaloisOeuvres/TheorieNombresClose.lean` (≈ 170 lines)

* Module: `GaloisOeuvres.TheorieNombresClose`.
* Imports: `GaloisOeuvres.TheorieNombres`, `GaloisOeuvres.EquationsPrimitives`,
  `GaloisOeuvres.TheorieNombresCloseAux1`, `GaloisOeuvres.TheorieNombresCloseAux2`.
* `open Polynomial`; namespace `GaloisOeuvres.TheorieNombres` (do **not** open
  `EquationsPrimitives` or `Couronne`: both contain a `couronne`). The `variable {p : ℕ}
  [hp : Fact p.Prime]` of `TheorieNombres.lean` does not carry over to a new file and is declared
  again (after the two declarations that take `p` explicitly).
* Purpose: Part C and Theorem B7; the two halves of the status "proved (corrected)".
* Suggested module docstring: "# The converse for primitive equations of degree `p^ν`: refutation
  and correction. Closes the unit `nombres.reciproque` of `TheorieNombres.lean`:
  `not_reciproqueGalois` (the printed claim is false for every prime, already in degree `p⁴`) and
  `reciproque_corrigee` (the group of a solvable primitive equation of degree `p^ν` consists of
  linear substitutions `k ↦ A k + b` of the `p^ν` indices and contains all the translations)."

Declarations:

```lean
/-- The linear substitutions `k ↦ A k + b` of a vector space over `ℤ/p`: the affine group. -/
def AGL (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∃ A : V ≃ₗ[ZMod p] V, ∃ b : V, ∀ k, σ k = A k + b}
  ...                                                                         -- C1

theorem mem_AGL_of_linearMap {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {σ : Equiv.Perm V} (A : V →ₗ[ZMod p] V) (b : V) (h : ∀ k, σ k = A k + b) :
    σ ∈ AGL p V                                                               -- C2

variable {p : ℕ} [hp : Fact p.Prime]

theorem AGammaL_le_AGL (K : Type*) [Field K] [Finite K] [Algebra (ZMod p) K] :
    AGammaL (p := p) K ≤ AGL p K                                              -- C3

theorem reciproque_corrigee …        -- C4, statement in 1.2
theorem reciproque_corrigee_degre …  -- C5, statement in 1.2

/-- What the printed claim would give for a solvable primitive group of degree `ℓ ^ ν`. -/
theorem card_dvd_of_reciproque (ℓ : ℕ) [Fact ℓ.Prime] (H : ReciproqueGalois ℓ) {X : Type}
    [Finite X] (Γ : Subgroup (Equiv.Perm X)) [MulAction.IsPreprimitive Γ X] [Group.IsSolvable Γ]
    (ν : ℕ) (hν : ν ≠ 0) (h9 : ℓ ^ ν ≠ 9) (h25 : ℓ ^ ν ≠ 25) (hX : Nat.card X = ℓ ^ ν) :
    Nat.card Γ ∣ ℓ ^ ν * (ℓ ^ ν - 1) * ν                                      -- A9

theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : ¬ ReciproqueGalois ℓ    -- B7
```

Implementation notes:

* `AGL`: `one_mem'` with `LinearEquiv.refl`, `mul_mem'` with `A'.trans A` and `A b' + b`,
  `inv_mem'` with `A.symm` and `-(A.symm b)` (`Equiv.Perm.inv_eq_iff_eq`).
* `mem_AGL_of_linearMap`: `LinearEquiv.ofBijective A ⟨inj, surj⟩` as in Lemma C2.
* `AGammaL_le_AGL`: the linear map is `(LinearMap.mulLeft (ZMod p) A).comp
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K ^ r).toLinearMap`; rewrite with
  `LinearMap.comp_apply`, `LinearMap.mulLeft_apply`, `AlgEquiv.toLinearMap_apply`,
  `frob_pow_apply`.
* `reciproque_corrigee`: first lines copied from `reciproque_premier` (root, solvability of
  `f.Gal` and of `groupe f Ω`, `Nat.card (f.rootSet Ω) = p ^ ν`); `Nontrivial (f.rootSet Ω)` from
  `Finite.one_lt_card_iff_nontrivial` and `Nat.one_lt_pow`; then
  `EquationsPrimitives.exists_affine_indexing (G := groupe f Ω) (X := f.rootSet Ω)` (the instances
  `Group.IsSolvable`, `IsPreprimitive` (the hypothesis `hprim`), `FaithfulSMul` (subgroup of
  `Equiv.Perm`), `Finite`, `Nontrivial` are found in the context). Identification
  `q = p`, `μ = ν` by `Nat.card_fun`, `Nat.card_zmod`, `Nat.prime_dvd_prime_iff_eq`,
  `Nat.Prime.dvd_of_dvd_pow`, `Nat.pow_right_injective`; **prove the equalities in the direction
  `p = q` and `ν = μ` before `subst`**, so that the variables produced by `obtain` (`q`, `μ`) are
  the ones eliminated. `B := (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p ν)
  (GaloisField.finrank p hν)).equivFun`, `e := B.toEquiv.trans e₀.symm`. For `σ`, the linear map
  is `(B.symm.toLinearMap.comp M.mulVecLin).comp B.toLinearMap` and the constant `B.symm c`;
  `groupeIndice f e σ k` is unfolded by
  `change B.symm (e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k)))) = _`.
* `card_dvd_of_reciproque`: `x₀` from `Nat.card_pos_iff`; then `reciproque_borne ℓ H (Corps Γ)
  (Cloture Γ) (equation Γ x₀) ν hν h9 h25 (equation_irreducible Γ x₀)
  ((natDegree_equation Γ x₀).trans hX) (primitif Γ x₀) (soluble Γ x₀)` and `card_gal`.
* `not_reciproqueGalois`: as in Theorem B7 with `F := GaloisField ℓ 2`, `ν := 4`.

### 4.4 Line estimates

| File | Lines (code as in the Appendix, plus module docstring) |
|---|---|
| `GaloisOeuvres/TheorieNombresCloseAux1.lean` | ≈ 200 |
| `GaloisOeuvres/TheorieNombresCloseAux2.lean` | ≈ 300 |
| `GaloisOeuvres/TheorieNombresClose.lean` | ≈ 175 |
| total | ≈ 675 |

---

## 5. MATHLIB / DEPENDENCY API

Every declaration below occurs in the type-checked scratch file (so it exists with the expected
type in mathlib v4.36.0) and/or was located with `rg`; paths are relative to
`.lake/packages/mathlib/Mathlib/`.

| Declaration | File |
|---|---|
| `MvPolynomial.rename`, `rename_X`, `rename_rename`, `rename_id`, `renameEquiv` | `Algebra/MvPolynomial/Rename.lean` |
| `MvPolynomial.X_injective` | `Algebra/MvPolynomial/Basic.lean` |
| `IsFractionRing.injective`, `IsFractionRing.ringEquivOfRingEquiv`, `ringEquivOfRingEquiv_algebraMap`, `ringEquivOfRingEquivHom` | `RingTheory/Localization/FractionRing.lean` |
| `MulSemiringAction.compHom` | `Algebra/Ring/Action/Basic.lean` |
| instance `MulSemiringAction (R ≃+* R) R` | `Algebra/Ring/Action/Group.lean` |
| instance `Subgroup.mulSemiringAction` | `Algebra/Ring/Action/Subobjects.lean` |
| `MulSemiringAction.toAlgAut` (`G →* A ≃ₐ[R] A`; application is `g • x` by `rfl`) | `Algebra/Algebra/Equiv.lean` |
| `FixedPoints.subfield`, `FixedPoints.isIntegral`, instance `FixedPoints.normal`, `FixedPoints.toAlgAut_surjective` | `FieldTheory/Fixed.lean` |
| `RingHom.charZero` | `Algebra/Ring/CharZero.lean` |
| instance `IsFractionRing.charZero : CharZero (FractionRing R)` | `Algebra/CharP/Algebra.lean` |
| `minpoly.irreducible`, `minpoly.monic`, `minpoly.aeval` | `FieldTheory/Minpoly/Basic.lean` |
| `minpoly.dvd`, `minpoly.eq_of_irreducible_of_monic` | `FieldTheory/Minpoly/Field.lean` |
| `Normal.splits` | `FieldTheory/Normal/Defs.lean` |
| `Normal.minpoly_eq_iff_mem_orbit` | `FieldTheory/Normal/Basic.lean` |
| `Polynomial.aeval_algHom_apply` | `Algebra/Polynomial/AlgebraMap.lean` |
| `Polynomial.mem_rootSet` | `Algebra/Polynomial/Roots.lean` |
| `Polynomial.card_rootSet_eq_natDegree`, `Irreducible.separable` | `FieldTheory/Separable.lean` |
| `Polynomial.Gal`, `Gal.restrict`, `Gal.restrict_surjective`, `Gal.restrict_smul`, `Gal.rootsEquivRoots`, `Gal.smul_rootsEquivRoots`, `Gal.galActionHom`, `Gal.restrictDvd_surjective` | `FieldTheory/PolynomialGaloisGroup.lean` |
| `AlgebraicClosure`, instance `AlgebraicClosure.isAlgClosed` | `FieldTheory/IsAlgClosed/AlgebraicClosure.lean` |
| `IsAlgClosed.splits`, `IsAlgClosed.exists_root` | `FieldTheory/IsAlgClosed/Basic.lean` |
| `isSolvable_gal_of_irreducible` | `FieldTheory/AbelRuffini.lean` |
| `MulAction.IsPreprimitive.of_surjective`, `MulAction.IsPreprimitive.of_isTrivialBlock_base` | `GroupTheory/GroupAction/Primitive.lean` |
| `MulAction.IsBlock.smul_eq_of_mem` | `GroupTheory/GroupAction/Blocks.lean` |
| `MulAction.exists_smul_eq` | `Algebra/Group/Action/Pretransitive.lean` |
| `Group.isSolvable_of_surjective`, `Subgroup.derivedSeries_one`, `Subgroup.derivedSeries_succ` | `GroupTheory/Solvable.lean` |
| `commutatorElement_eq_one_iff_mul_comm`, `Subgroup.commutator_def`, `Subgroup.commutator_le`, `Subgroup.commutator_mono` | `GroupTheory/Commutator/Basic.lean` |
| `Subgroup.index_eq_two_iff`, `Subgroup.index_mul_card` | `GroupTheory/Index.lean` |
| `Subgroup.card_dvd_of_injective` | `GroupTheory/Coset/Card.lean` |
| `Subgroup.subgroupOfEquivOfLe` | `Algebra/Group/Subgroup/Map.lean` |
| `MonoidHom.codRestrict` | `Algebra/Group/Submonoid/Operations.lean` |
| `MonoidHom.rangeRestrict_surjective` | `Algebra/Group/Subgroup/Ker.lean` |
| `Equiv.Perm.inv_eq_iff_eq`, instance `Equiv.Perm.applyFaithfulSMul` | `Algebra/Group/End.lean`, `Algebra/Group/Action/End.lean` |
| `Nat.card_units` | `Algebra/GroupWithZero/Units/Fintype.lean` |
| `Nat.card_prod`, `Nat.card_fun`, `Nat.card_zmod`, `Nat.card_congr`, `Nat.card_eq_fintype_card` | `SetTheory/Cardinal/Finite.lean` |
| `Finite.one_lt_card_iff_nontrivial` | `SetTheory/Cardinal/NatCard.lean` |
| `GaloisField`, `GaloisField.card`, `GaloisField.finrank` (instances `Field`, `Finite`, `Algebra (ZMod p)`, `FiniteDimensional (ZMod p)`) | `FieldTheory/Finite/GaloisField.lean` |
| `Module.finBasisOfFinrankEq` | `LinearAlgebra/Dimension/Free.lean` |
| `Matrix.mulVecLin` (`M.mulVecLin v = M.mulVec v` by `rfl`) | `LinearAlgebra/Matrix/ToLin.lean` |
| `LinearEquiv.ofBijective`, `LinearEquiv.ofBijective_apply` | `Algebra/Module/Submodule/Equiv.lean` |
| `LinearMap.mulLeft`, `LinearMap.mulLeft_apply` | `Algebra/Module/LinearMap/Defs.lean` |
| `Nat.prime_dvd_prime_iff_eq` | `Data/Nat/Prime/Defs.lean` |
| `Nat.Prime.dvd_of_dvd_pow` | `Data/Nat/Prime/Basic.lean` |
| `Nat.pow_right_injective` | `Data/Nat/Basic.lean` |

Repository dependencies: see section 2 (`reciproque_borne`, `ReciproqueGalois`, `groupeIndice`,
`AGammaL`, `frob_pow_apply`, `degre_primitive` in `TheorieNombres.lean`;
`exists_affine_indexing` in `EquationsPrimitives.lean`; `groupe`, `SolubleParRadicaux` in
`Basic.lean`; `mem_solvableByRad_of_isSolvable` in `Radicaux.lean`).

Not available in mathlib (and therefore built in file 1): the action of `Equiv.Perm σ` on
`MvPolynomial σ R` itself (as a `MulSemiringAction`), and any "every finite group is a Galois
group" statement. The *extension* of a ring action to the fraction field does exist in mathlib:
`IsFractionRing.mulSemiringAction G B L` (an `@[instance_reducible] noncomputable def`, l. 670),
with `IsFractionRing.smulDistribClass` (instance, l. 677) and `IsFractionRing.faithfulSMul`
(l. 688), all in `RingTheory/Localization/FractionRing.lean`. Its definition is literally
`MulSemiringAction.compHom L ((ringEquivOfRingEquivHom B L).comp (MulSemiringAction.toRingEquiv G B))`,
i.e. the same construction as the hand-written `actionPerm` of file 1, which therefore needs no
change.

---

## 6. RISKS

No mathematical gap is known: every lemma of section 3 is proved there in full, and the Lean code
of the Appendix follows it step by step. The remaining risks are practical.

1. **Split files: checked for Aux1 and Aux2; file 3 checked only inside `RAll.lean`.** Exact
   copies of Aux1 (importing only `GaloisOeuvres.Radicaux`) and Aux2 (importing only
   `GaloisOeuvres.Basic`) compiled `[OK]` with no warning
   (`.lake-local/scratch/reciproque-lean-critic/A1.lean`, `A2.lean`; section 4.0). File 3
   (`TheorieNombresClose.lean`) cannot be compiled before the `.olean`s of Aux1 and Aux2 exist; its
   code compiled as the last part of `RAll.lean`, which imported `GaloisOeuvres.TheorieNombres`
   and `GaloisOeuvres.EquationsPrimitives`, exactly the imports file 3 has besides Aux1/Aux2. The
   remaining risk is a name-resolution difference caused by the namespace split (e.g. a short name
   that resolved inside `RAll.lean` because all three namespaces were in one file); fix it by
   qualifying the name (`Realisation.…`, `Couronne.…`). Build strictly in order with
   `python .lake-local/leanc.py <file> --olean`: Aux1, then Aux2, then Close, then add the three
   imports to `GaloisOeuvres.lean`. A cold compile can take about 35 minutes.
2. **Instance synthesis on the concrete fields.** Observed in the first experiment: any use of
   `mem_rootSet` with `K = Corps Γ` and `S = Cloture Γ` times out while synthesizing
   `Module.IsTorsionFree (Corps Γ) (Cloture Γ)` (default 20000 heartbeats). The reference code
   avoids every such use (generic lemma `soluble_of_isSolvable_gal`; the root set in `Cloture Γ`
   is only handled through `Gal.rootsEquivRoots`). If a variant of the code needs such an instance
   after all, either state the step for abstract fields `K, Ω` first, or use
   `set_option synthInstance.maxHeartbeats 200000 in`. Do not replace `Cloture Γ` by an algebraic
   closure of `Fonctions X`: that needs an `IsScalarTower` and more instances of the same kind.
3. **Global instances introduced by file 1**: `actionPerm : MulSemiringAction (Equiv.Perm X)
   (FractionRing (MvPolynomial X ℚ))`, `faithful`, `CharZero (Corps Γ)`, `splitsΩ`, `splitsF`.
   Mathlib has no competing instance on these types: no `Equiv.Perm` action on `MvPolynomial`;
   `IsFractionRing.mulSemiringAction` is a `def`, not an instance; the OreLocalization `SMul`
   instances on `FractionRing` need an `IsScalarTower` over the base ring which does not exist
   here. The root file `GaloisOeuvres.lean` imports all pieces, so `actionPerm` is visible
   library-wide; this is a hygiene issue only. If a later file suffers from it (or if the
   implementer prefers it from the start, at the cost of one extra compile), make `actionPerm`,
   `splitsΩ` and `splitsF` `scoped instance`s of the namespace `Realisation` and add
   `open scoped Realisation` in file 3.
4. **`subst` direction and proof-irrelevant instances in `reciproque_corrigee`.** The prime `q` and
   the exponent `μ` returned by `exists_affine_indexing` are eliminated (`subst` with `p = q`,
   `ν = μ`), not `p` and `ν`. No `Fact q.Prime` instance is created before the `subst`. In
   `reciproque_corrigee_degre` the instance in the statement is the anonymous `⟨hq⟩` and the one
   used to call `reciproque_corrigee` is a local `Fact.mk hq`; they agree by proof irrelevance.
5. **Universe.** `ReciproqueGalois` quantifies over `K Ω : Type`. The realization is therefore
   written for `X : Type` only; `X = GaloisField ℓ 2 × GaloisField ℓ 2 : Type`, `Corps Γ : Type`,
   `Cloture Γ : Type`. Do not generalize `X` to `Type*` (the final application would then need
   universe annotations).
6. **Name clashes.** `Couronne.couronne`, `Couronne.produit`, `Couronne.droite`, … have the same
   short names as declarations of `GaloisOeuvres.EquationsPrimitives`; file 3 imports both and must
   refer to them with the qualifiers `Couronne.` / `EquationsPrimitives.` and open neither.
   `GaloisOeuvres.TheorieNombres.AGL` is new (no `AGL` identifier exists in the repository).
7. **Linter warnings, not errors.** The `variable` layout of file 1 was arranged so that each
   theorem takes only the hypotheses it uses (`[Finite X]`, `[MulAction.IsPretransitive Γ X]`,
   `[MulAction.IsPreprimitive Γ X]` in separate scopes); any remaining "unused section variable"
   or "overlapping instance parameters" warnings are harmless and can be silenced with `omit … in`.
8. **Compile time on this machine.** With three Lean processes sharing 16 GB, a file importing
   `Mathlib` takes 30–40 minutes of wall-clock time here (memory pressure, about 2–3 minutes of
   CPU). Plan one compile per file, not an edit–compile loop.
9. **Unit bookkeeping.** New files must not contain `## [piece.unit]` blocks (duplicate ids make
   `scripts/unit_table.py --check` fail). The status change of the unit itself is an edit of
   `TheorieNombres.lean` and belongs to the final wiring (section 7).
10. **What the corrected statement does not say.** `reciproque_corrigee` is a necessary condition
    (the group is contained in `AGL(ν, p)` and contains the translations); it is not a criterion,
    and it does not say that the point stabilizer is an irreducible linear group, although that
    follows from primitivity. This is the classical Galois–Jordan statement asked for; the Lean
    reading of the unit must say that it is not an equivalence and that the irreducibility of the
    stabilizer is not stated (proposed text in section 7).

---

## 7. NOTES FOR THE FINAL WIRING (not part of the implementation of the three files)

1. `GaloisOeuvres.lean`: add `import GaloisOeuvres.TheorieNombresCloseAux1`,
   `import GaloisOeuvres.TheorieNombresCloseAux2`, `import GaloisOeuvres.TheorieNombresClose`.
2. Unit block `## [nombres.reciproque]` in `TheorieNombres.lean` (l. 1738–1767): replace the end
   of the Lean reading (from "Proved here: …" to "… is not formalized.") and the status line.
   Proposed text:

   > **Lean reading.** Formalized as `ReciproqueGalois p`: an irreducible equation of degree `p^ν`
   > (`p^ν ≠ 9, 25`) with primitive group, solvable by radicals, admits a labelling of its roots by
   > the imaginaries under which its group consists of substitutions `k ↦ (ak + b)^(p^r)`. **This
   > claim is false, for every prime `p`** (`not_reciproqueGalois`, in
   > `TheorieNombresClose.lean`): for the field `F` with `p²` elements, the group
   > `AGL(1, p²) ≀ C₂` of the substitutions `(k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` and
   > `(k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)` of the `p⁴` points of `F × F` is primitive
   > (`Couronne.couronne_primitif`) and solvable (`Couronne.couronne_soluble`); it is the group of
   > an irreducible equation of degree `p⁴` over the field of the rational functions of `p⁴`
   > letters invariant under it (`Realisation.equation`, `Realisation.galActionHom_racine`,
   > `Realisation.primitif`, `Realisation.soluble`); and its order, a multiple of `2 (p² − 1)²`
   > (`Couronne.two_mul_dvd_card`), does not divide the number `p⁴ (p⁴ − 1) · 4` of Galois's
   > substitutions (`Couronne.arith`), which it would under the claim (`card_gal_dvd`,
   > `reciproque_borne`). So the exceptions are not only `9` and `25`. **What is true**
   > (Galois's idea as completed by Jordan), `reciproque_corrigee`: under the same hypotheses the
   > roots can be labelled by the imaginaries so that the group consists of *linear*
   > substitutions `k ↦ A k + b`, `A` an invertible linear map of the `ℤ/p`-vector space of the
   > imaginaries (`AGL`), and contains all the translations `k ↦ k + b`; Galois's substitutions
   > are of this kind (`AGammaL_le_AGL`), and the degree is necessarily `p^ν`
   > (`reciproque_corrigee_degre`). The corrected statement has no exceptional degrees and is only
   > a necessary condition, not a criterion; it also does not state the remaining part of Jordan's
   > theorem, that the stabilizer of a root acts irreducibly on the `ℤ/p`-vector space of the
   > imaginaries (true, by primitivity, but not formalized here). For `ν = 1` the printed claim itself is true (`reciproque_premier`,
   > Galois's theorem on equations of prime degree).
   >
   > **Status.** proved (corrected)

   Note for whoever regenerates `docs/UNITS.md`: `scripts/unit_table.py` lists only the
   declarations that follow a unit block in the same file, so the row of `nombres.reciproque`
   will keep listing the declarations of `TheorieNombres.lean`; the new ones are named in the
   reading. (Moving the unit block into `TheorieNombresClose.lean` would instead attach the old
   declarations to the preceding unit `nombres.suffisance`.)
3. `docs/FAITHFULNESS.md`: remove the bullet `nombres.reciproque` from the list of open/stated
   units (l. 98) and add a row to the corrections table of *Sur la théorie des nombres*:
   "`nombres.reciproque` | The group of a solvable primitive equation of degree `p^ν` need not
   consist of substitutions `k ↦ (ak+b)^(p^r)`: for every `p`, `AGL(1, p²) ≀ C₂` in degree `p⁴`
   is a counterexample, realized as the group of an equation. | The group consists of linear
   substitutions `k ↦ A k + b` and contains the translations; the printed claim for `ν = 1`."
4. `README.md`: status table (`proved (corrected)` +1, `stated (open here)` −1), the sentence
   about the two open units, and the list of Galois's errors (one more item).
5. Unit `nombres.caracteres` (remark, l. 2050): its sentence "Since the converse is false in
   general (it holds for `ν = 1`, `reciproque_premier`)" can now cite `not_reciproqueGalois`.
6. `scripts/AxiomsAudit.lean` needs no change (it audits the namespace `GaloisOeuvres`).

---

## 8. APPENDIX: complete reference code

The three files below are the type-checked scratch file `RAll.lean` cut at its namespace
boundaries, with the import lists and module docstrings of the target files. Identical
copies are in `.lake-local/plans/galois-reciproque/reference/`.

### 8.1 `GaloisOeuvres/TheorieNombresCloseAux1.lean`

```lean
import GaloisOeuvres.Radicaux

/-!
# Every finite transitive permutation group is the group of an equation

Auxiliary file for the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`).

Let `Γ` be a group of permutations of a finite set `X` of letters, transitive on `X`. The
substitutions of the letters act on the field `Fonctions X` of the rational functions of the
letters (rational coefficients); `Corps Γ` is the field of the functions invariant under `Γ`.
The letters are the roots of an irreducible equation `equation Γ x₀` over `Corps Γ` (the minimal
polynomial of one letter), of degree the number of letters (`natDegree_equation`), and the group
of this equation, acting on its roots in an algebraically closed field `Cloture Γ`, is `Γ` acting
on the letters: `versGal` is an isomorphism from `Γ` onto the group (`versGal_injective`,
`versGal_surjective`) and `racine` a labelling of the roots by the letters compatible with the
actions (`galActionHom_racine`). Hence the group of the equation is primitive if `Γ` is
(`primitif`), and the equation is solvable by radicals if `Γ` is solvable (`soluble`).
-/

open Polynomial

namespace GaloisOeuvres.TheorieNombres.Realisation

section Action

variable (X : Type)

/-- The field of rational functions of the letters. -/
abbrev Fonctions : Type := FractionRing (MvPolynomial X ℚ)

/-- The letter `x_i`. -/
noncomputable def lettre (i : X) : Fonctions X :=
  algebraMap (MvPolynomial X ℚ) (Fonctions X) (MvPolynomial.X i)

theorem lettre_injective : Function.Injective (lettre X) := fun _ _ h =>
  MvPolynomial.X_injective (IsFractionRing.injective (MvPolynomial X ℚ) (Fonctions X) h)

/-- The substitutions of the letters, as automorphisms of the polynomial ring. -/
noncomputable def permRing : Equiv.Perm X →* (MvPolynomial X ℚ ≃+* MvPolynomial X ℚ) where
  toFun σ := (MvPolynomial.renameEquiv ℚ σ).toRingEquiv
  map_one' := by
    apply RingEquiv.ext; intro q
    change MvPolynomial.rename (⇑(1 : Equiv.Perm X)) q = q
    rw [Equiv.Perm.coe_one, MvPolynomial.rename_id]; rfl
  map_mul' σ τ := by
    apply RingEquiv.ext; intro q
    change MvPolynomial.rename (⇑(σ * τ)) q = MvPolynomial.rename σ (MvPolynomial.rename τ q)
    rw [MvPolynomial.rename_rename]; rfl

/-- The substitutions of the letters act on the rational functions. -/
noncomputable instance actionPerm : MulSemiringAction (Equiv.Perm X) (Fonctions X) :=
  MulSemiringAction.compHom (Fonctions X)
    ((IsFractionRing.ringEquivOfRingEquivHom (MvPolynomial X ℚ) (Fonctions X)).comp (permRing X))

theorem smul_lettre (σ : Equiv.Perm X) (i : X) : σ • lettre X i = lettre X (σ i) := by
  change IsFractionRing.ringEquivOfRingEquiv ((MvPolynomial.renameEquiv ℚ σ).toRingEquiv)
    (algebraMap (MvPolynomial X ℚ) (Fonctions X) (MvPolynomial.X i)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap _ _ (MvPolynomial.rename σ (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]; rfl

end Action

/-- Solvable group ⇒ solvable by radicals. -/
theorem soluble_of_isSolvable_gal {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] {p : K[X]} (hp : Irreducible p) (h : Group.IsSolvable p.Gal) :
    SolubleParRadicaux p Ω := by
  intro x hx
  have hx' : aeval x p = 0 := (mem_rootSet.1 hx).2
  have hint : IsIntegral K x := IsAlgebraic.isIntegral ⟨p, hp.ne_zero, hx'⟩
  apply mem_solvableByRad_of_isSolvable hint
  exact Group.isSolvable_of_surjective
    (Gal.restrictDvd_surjective (minpoly.dvd K x hx') hp.ne_zero)

section Corps

variable {X : Type} (Γ : Subgroup (Equiv.Perm X))

theorem smul_lettre' (γ : Γ) (i : X) : γ • lettre X i = lettre X (γ • i) :=
  smul_lettre X (γ : Equiv.Perm X) i

instance faithful : FaithfulSMul Γ (Fonctions X) := ⟨fun {a b} h => by
  apply Subtype.ext; apply Equiv.ext; intro i
  apply lettre_injective X
  have := h (lettre X i)
  rwa [smul_lettre', smul_lettre'] at this⟩

/-- The field of the rational functions invariant under `Γ`. -/
abbrev Corps : Type := ↥(FixedPoints.subfield Γ (Fonctions X))

instance : CharZero (Corps Γ) :=
  (algebraMap (Corps Γ) (Fonctions X)).charZero

/-- The equation whose roots are the letters. -/
noncomputable def equation (x₀ : X) : (Corps Γ)[X] := minpoly (Corps Γ) (lettre X x₀)

/-- The algebraically closed field in which the roots are taken. -/
abbrev Cloture : Type := AlgebraicClosure (Corps Γ)

instance splitsΩ (x₀ : X) :
    Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Cloture Γ))).Splits) :=
  ⟨IsAlgClosed.splits _⟩

variable [Finite X] (x₀ : X)

theorem equation_irreducible : Irreducible (equation Γ x₀) :=
  minpoly.irreducible (FixedPoints.isIntegral Γ (Fonctions X) (lettre X x₀))

instance splitsF : Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Fonctions X))).Splits) :=
  ⟨Normal.splits inferInstance _⟩

/-- The group `Γ` as the group of the equation. -/
noncomputable def versGal : Γ →* (equation Γ x₀).Gal :=
  (Gal.restrict (equation Γ x₀) (Fonctions X)).comp
    (MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X))

theorem versGal_surjective : Function.Surjective (versGal Γ x₀) :=
  (Gal.restrict_surjective (equation Γ x₀) (Fonctions X)).comp
    (FixedPoints.toAlgAut_surjective Γ (Fonctions X))

theorem soluble [Group.IsSolvable Γ] : SolubleParRadicaux (equation Γ x₀) (Cloture Γ) :=
  soluble_of_isSolvable_gal (equation_irreducible Γ x₀)
    (Group.isSolvable_of_surjective (versGal_surjective Γ x₀))

section Transitif

variable [MulAction.IsPretransitive Γ X]

omit [Finite X] in
theorem aeval_lettre (i : X) : aeval (lettre X i) (equation Γ x₀) = 0 := by
  obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq Γ x₀ i
  have h : lettre X (γ • x₀) =
      MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X) γ (lettre X x₀) :=
    (smul_lettre' Γ γ x₀).symm
  have h0 : aeval (lettre X x₀) (equation Γ x₀) = 0 := minpoly.aeval _ _
  rw [h, aeval_algHom_apply, h0, map_zero]

omit [MulAction.IsPretransitive Γ X] in
theorem exists_lettre_of_root {y : Fonctions X} (hy : aeval y (equation Γ x₀) = 0) :
    ∃ i, y = lettre X i := by
  have h1 : minpoly (Corps Γ) y = minpoly (Corps Γ) (lettre X x₀) :=
    (minpoly.eq_of_irreducible_of_monic (equation_irreducible Γ x₀) hy
      (minpoly.monic (FixedPoints.isIntegral Γ (Fonctions X) (lettre X x₀)))).symm
  obtain ⟨φ, hφ⟩ := (Normal.minpoly_eq_iff_mem_orbit (Fonctions X)).mp h1
  obtain ⟨γ, rfl⟩ := FixedPoints.toAlgAut_surjective Γ (Fonctions X) φ
  exact ⟨γ • x₀, hφ.symm.trans (smul_lettre' Γ γ x₀)⟩

/-- The labelling of the roots (in the field of rational functions) by the letters. -/
noncomputable def racineF : X ≃ (equation Γ x₀).rootSet (Fonctions X) :=
  Equiv.ofBijective
    (fun i => ⟨lettre X i, mem_rootSet.mpr ⟨(equation_irreducible Γ x₀).ne_zero,
      aeval_lettre Γ x₀ i⟩⟩)
    ⟨fun _ _ h => lettre_injective X (congrArg Subtype.val h),
      fun y => by
        obtain ⟨i, hi⟩ := exists_lettre_of_root Γ x₀ (mem_rootSet.mp y.2).2
        exact ⟨i, Subtype.ext hi.symm⟩⟩

theorem versGal_smul (γ : Γ) (i : X) :
    versGal Γ x₀ γ • racineF Γ x₀ i = racineF Γ x₀ (γ • i) := by
  apply Subtype.ext
  exact (Gal.restrict_smul (MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X) γ)
    (racineF Γ x₀ i)).trans (smul_lettre' Γ γ i)

theorem versGal_injective : Function.Injective (versGal Γ x₀) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext; apply Equiv.ext; intro i
  have h := versGal_smul Γ x₀ γ i
  rw [hγ, one_smul] at h
  exact ((racineF Γ x₀).injective h).symm

theorem natDegree_equation : (equation Γ x₀).natDegree = Nat.card X := by
  rw [← card_rootSet_eq_natDegree (equation_irreducible Γ x₀).separable
    (Fact.out : ((equation Γ x₀).map (algebraMap (Corps Γ) (Fonctions X))).Splits),
    ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (racineF Γ x₀)).symm

/-- The labelling of the roots in `Ω` by the letters. -/
noncomputable def racine : X ≃ (equation Γ x₀).rootSet (Cloture Γ) :=
  (racineF Γ x₀).trans (Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ))

theorem galActionHom_racine (γ : Γ) (i : X) :
    Gal.galActionHom (equation Γ x₀) (Cloture Γ) (versGal Γ x₀ γ) (racine Γ x₀ i) =
      racine Γ x₀ (γ • i) := by
  change versGal Γ x₀ γ • Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ)
    (racineF Γ x₀ i) = _
  rw [Gal.smul_rootsEquivRoots, versGal_smul]; rfl

theorem card_gal : Nat.card (equation Γ x₀).Gal = Nat.card Γ :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨versGal_injective Γ x₀, versGal_surjective Γ x₀⟩)).symm

end Transitif

theorem primitif [MulAction.IsPreprimitive Γ X] :
    MulAction.IsPreprimitive (groupe (equation Γ x₀) (Cloture Γ))
      ((equation Γ x₀).rootSet (Cloture Γ)) := by
  let φ : Γ → groupe (equation Γ x₀) (Cloture Γ) := fun γ =>
    (Gal.galActionHom (equation Γ x₀) (Cloture Γ)).rangeRestrict (versGal Γ x₀ γ)
  let j : X →ₑ[φ] (equation Γ x₀).rootSet (Cloture Γ) :=
    { toFun := racine Γ x₀
      map_smul' := fun γ i => (galActionHom_racine Γ x₀ γ i).symm }
  exact MulAction.IsPreprimitive.of_surjective (f := j) (racine Γ x₀).surjective

end Corps

end GaloisOeuvres.TheorieNombres.Realisation
```

### 8.2 `GaloisOeuvres/TheorieNombresCloseAux2.lean`

```lean
import GaloisOeuvres.Basic

/-!
# The groups `AGL(1, F) ≀ C₂`

Auxiliary file for the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`).

For a field `F`, `couronne F` is the group of the substitutions
`(k₁, k₂) ↦ (a k₁ + n₁, b k₂ + n₂)` and `(k₁, k₂) ↦ (a k₂ + n₁, b k₁ + n₂)` (`a, b ≠ 0`) of the
points of `F × F`. It is solvable (`couronne_soluble`); it is primitive as soon as `F` has an
element other than `0` and `1` (`couronne_primitif`); and, `F` having `q` elements, its order is
divisible by `2 (q - 1)²` (`two_mul_dvd_card`). For `F = ℤ/p` this is the group
`EquationsPrimitives.couronne p`, and the proofs are the same, written for an arbitrary field.
`arith` is the arithmetic fact that makes these groups, for `q = ℓ²`, too large for Galois's
group of substitutions of `ℓ⁴` indices.
-/

namespace GaloisOeuvres.TheorieNombres.Couronne

open MulAction

variable {F : Type*} [Field F]

/-- `k ↦ (a k₁ + n₁, b k₂ + n₂)`. -/
def EstDroite (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.1 + n₁, b * k.2 + n₂)

/-- `k ↦ (a k₂ + n₁, b k₁ + n₂)`. -/
def EstCroisee (a b : F) (σ : Equiv.Perm (F × F)) : Prop :=
  ∃ n₁ n₂ : F, ∀ k, σ k = (a * k.2 + n₁, b * k.1 + n₂)

section Lemmes

variable {a b a' b' : F} {σ τ : Equiv.Perm (F × F)}

theorem dd (h : EstDroite a b σ) (h' : EstDroite a' b' τ) :
    EstDroite (a * a') (b * b') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₁' + n₁, b * n₂' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem dc (h : EstDroite a b σ) (h' : EstCroisee a' b' τ) :
    EstCroisee (a * a') (b * b') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₁' + n₁, b * n₂' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem cd (h : EstCroisee a b σ) (h' : EstDroite a' b' τ) :
    EstCroisee (a * b') (b * a') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₂' + n₁, b * n₁' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem cc (h : EstCroisee a b σ) (h' : EstCroisee a' b' τ) :
    EstDroite (a * b') (b * a') (σ * τ) := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  exact ⟨a * n₂' + n₁, b * n₁' + n₂, fun k => by
    rw [Equiv.Perm.mul_apply, h', h]; ext <;> simp <;> ring⟩

theorem d_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstDroite a b σ) : EstDroite a⁻¹ b⁻¹ σ⁻¹ := by
  obtain ⟨n₁, n₂, h⟩ := h
  refine ⟨-(a⁻¹ * n₁), -(b⁻¹ * n₂), fun k => ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  ext <;> simp <;> field_simp <;> ring

theorem c_inv (ha : a ≠ 0) (hb : b ≠ 0) (h : EstCroisee a b σ) : EstCroisee b⁻¹ a⁻¹ σ⁻¹ := by
  obtain ⟨n₁, n₂, h⟩ := h
  refine ⟨-(b⁻¹ * n₂), -(a⁻¹ * n₁), fun k => ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq, h]
  ext <;> simp <;> field_simp <;> ring

theorem not_d_c (h : EstDroite a b σ) (h' : EstCroisee a' b' σ) (ha : a ≠ 0) : False := by
  obtain ⟨n₁, n₂, h⟩ := h; obtain ⟨n₁', n₂', h'⟩ := h'
  have e1 := h (1, 0); have e0 := h (0, 0); have f1 := h' (1, 0); have f0 := h' (0, 0)
  rw [e1] at f1; rw [e0] at f0
  simp only [Prod.mk.injEq, mul_one, mul_zero, zero_add] at f1 f0
  exact ha (by linear_combination f1.1 - f0.1)

end Lemmes

/-- An explicit permutation `k ↦ (a k₁ + n₁, b k₂ + n₂)`. -/
def droite (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) : Equiv.Perm (F × F) where
  toFun k := (a * k.1 + n₁, b * k.2 + n₂)
  invFun k := (a⁻¹ * (k.1 - n₁), b⁻¹ * (k.2 - n₂))
  left_inv k := by ext <;> simp <;> field_simp
  right_inv k := by ext <;> simp <;> field_simp <;> ring

/-- The exchange of the two indices. -/
def echange : Equiv.Perm (F × F) := Equiv.prodComm _ _

theorem droite_est (a b n₁ n₂ : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    EstDroite a b (droite a b n₁ n₂ ha hb) := ⟨n₁, n₂, fun _ => rfl⟩

theorem echange_est : EstCroisee (1 : F) 1 echange :=
  ⟨0, 0, fun k => by simp [echange, Prod.swap]⟩

variable (F) in
/-- The group `AGL(1, F) ≀ C₂`. -/
def couronne : Subgroup (Equiv.Perm (F × F)) where
  carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ (EstDroite a b σ ∨ EstCroisee a b σ)}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, Or.inl ⟨0, 0, fun k => by simp⟩⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, ha, hb, hσ | hσ⟩ ⟨a', b', ha', hb', hτ | hτ⟩
    · exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', Or.inl (dd hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', Or.inr (dc hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha hb', mul_ne_zero hb ha', Or.inr (cd hσ hτ)⟩
    · exact ⟨_, _, mul_ne_zero ha hb', mul_ne_zero hb ha', Or.inl (cc hσ hτ)⟩
  inv_mem' := by
    rintro σ ⟨a, b, ha, hb, hσ | hσ⟩
    · exact ⟨_, _, inv_ne_zero ha, inv_ne_zero hb, Or.inl (d_inv ha hb hσ)⟩
    · exact ⟨_, _, inv_ne_zero hb, inv_ne_zero ha, Or.inr (c_inv ha hb hσ)⟩

variable (F) in
/-- Its subgroup `AGL(1, F) × AGL(1, F)`. -/
def produit : Subgroup (Equiv.Perm (F × F)) where
  carrier := {σ | ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ EstDroite a b σ}
  one_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, ⟨0, 0, fun k => by simp⟩⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, ha, hb, hσ⟩ ⟨a', b', ha', hb', hτ⟩
    exact ⟨_, _, mul_ne_zero ha ha', mul_ne_zero hb hb', dd hσ hτ⟩
  inv_mem' := by
    rintro σ ⟨a, b, ha, hb, hσ⟩
    exact ⟨_, _, inv_ne_zero ha, inv_ne_zero hb, d_inv ha hb hσ⟩

theorem produit_le_couronne : produit F ≤ couronne F := fun _ ⟨a, b, ha, hb, h⟩ =>
  ⟨a, b, ha, hb, Or.inl h⟩

theorem index_produit : ((produit F).subgroupOf (couronne F)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨echange, 1, 1, one_ne_zero, one_ne_zero, Or.inr echange_est⟩, ?_⟩
  rintro ⟨σ, a, b, ha, hb, hσ | hσ⟩
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact Or.inr ⟨⟨a, b, ha, hb, hσ⟩, fun ⟨a', b', ha', hb', h'⟩ =>
      not_d_c h' (dc hσ (echange_est (F := F))) ha'⟩
  · simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    exact Or.inl ⟨⟨_, _, mul_ne_zero ha one_ne_zero, mul_ne_zero hb one_ne_zero,
      cc hσ (echange_est (F := F))⟩, fun ⟨a', b', ha', hb', h'⟩ => not_d_c h' hσ ha'⟩

omit [Field F] in
theorem smul_mem_of_block {G : Subgroup (Equiv.Perm (F × F))}
    {B : Set (F × F)} (hB : IsBlock G B) {σ : Equiv.Perm (F × F)} (hσ : σ ∈ G)
    {v : F × F} (hv : v ∈ B) (hσv : σ v ∈ B) {w : F × F} (hw : w ∈ B) :
    σ w ∈ B := by
  have h := hB.smul_eq_of_mem (g := ⟨σ, hσ⟩) hv hσv
  rw [← h]
  exact ⟨w, hw, rfl⟩

theorem ligne_sub {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {B : Set (F × F)}
    (hB : IsBlock (couronne F) B) (h0 : (0, 0) ∈ B)
    {v : F × F} (hv : v ∈ B) (hv1 : v.1 ≠ 0) (x : F) : (x, 0) ∈ B := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hdiag : ∀ (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) w, w ∈ B → (a * w.1, b * w.2) ∈ B :=
    fun a b ha hb w hw => by
      have := smul_mem_of_block hB
        (produit_le_couronne ⟨a, b, ha, hb, droite_est a b 0 0 ha hb⟩) h0
        (by simpa [droite] using h0) hw
      simpa [droite] using this
  have htrans : ∀ u w, u ∈ B → w ∈ B → (w.1 + u.1, w.2 + u.2) ∈ B := fun u w hu hw => by
    have := smul_mem_of_block hB (produit_le_couronne ⟨1, 1, one_ne_zero, one_ne_zero,
      droite_est 1 1 u.1 u.2 one_ne_zero one_ne_zero⟩) h0 (by simpa [droite] using hu) hw
    simpa [droite] using this
  have hv' : ((c - 1) * v.1, 0) ∈ B := by
    have h1 := hdiag c 1 hc0 one_ne_zero v hv
    have h3 := hdiag (-1) (-1) hm1 hm1 v hv
    have := htrans _ _ h3 h1
    convert this using 2 <;> ring
  by_cases hx : x = 0
  · rw [hx]; exact h0
  · have hc : (c - 1) * v.1 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hc1) hv1
    have := hdiag (x / ((c - 1) * v.1)) 1 (div_ne_zero hx hc) one_ne_zero _ hv'
    convert this using 2
    · exact (div_mul_cancel₀ x hc).symm
    · simp

/-- **`AGL(1, F) ≀ C₂` is primitive** when `F` has at least three elements. -/
theorem couronne_primitif (h3 : ∃ c : F, c ≠ 0 ∧ c ≠ 1) :
    IsPreprimitive (couronne F) (F × F) := by
  obtain ⟨c, hc0, hc1⟩ := h3
  have htr : IsPretransitive (couronne F) (F × F) := by
    refine ⟨fun x y => ⟨⟨droite 1 1 (y.1 - x.1) (y.2 - x.2) one_ne_zero one_ne_zero,
      1, 1, one_ne_zero, one_ne_zero, Or.inl (droite_est _ _ _ _ _ _)⟩, ?_⟩⟩
    change droite 1 1 (y.1 - x.1) (y.2 - x.2) one_ne_zero one_ne_zero x = y
    ext <;> simp [droite]
  apply IsPreprimitive.of_isTrivialBlock_base (0, 0)
  intro B h0 hB
  by_cases hsub : B ⊆ {(0, 0)}
  · left; exact Set.subsingleton_singleton.anti hsub
  · right
    obtain ⟨v, hv, hv0⟩ := Set.not_subset.mp hsub
    have hsw : ∀ w, w ∈ B → (w.2, w.1) ∈ B := fun w hw => by
      have := smul_mem_of_block hB (σ := echange)
        ⟨1, 1, one_ne_zero, one_ne_zero, Or.inr echange_est⟩ h0 (by simpa [echange] using h0) hw
      simpa [echange, Prod.swap] using this
    have hrow : ∀ x : F, (x, 0) ∈ B := by
      by_cases hv1 : v.1 = 0
      · have hv2 : v.2 ≠ 0 := fun h => hv0 (Prod.ext hv1 h)
        exact ligne_sub hc0 hc1 hB h0 (hsw v hv) hv2
      · exact ligne_sub hc0 hc1 hB h0 hv hv1
    apply Set.eq_univ_of_forall
    intro w
    have h1 := hrow w.1
    have h2 := hsw _ (hrow w.2)
    have := smul_mem_of_block hB (σ := droite 1 1 w.1 0 one_ne_zero one_ne_zero)
      (produit_le_couronne ⟨1, 1, one_ne_zero, one_ne_zero, droite_est _ _ _ _ _ _⟩) h0
      (by simpa [droite] using h1) h2
    simpa [droite] using this

/-- **`AGL(1, F) ≀ C₂` is solvable.** -/
theorem couronne_soluble : Group.IsSolvable (couronne F) := by
  set W := couronne F
  let H : Subgroup W := (produit F).subgroupOf W
  let T : Subgroup W :=
    { carrier := {σ | EstDroite 1 1 (σ : Equiv.Perm (F × F))}
      one_mem' := ⟨0, 0, fun k => by simp⟩
      mul_mem' := fun ha hb => by simpa using dd ha hb
      inv_mem' := fun ha => by simpa using d_inv one_ne_zero one_ne_zero ha }
  have h1 : Subgroup.derivedSeries W 1 ≤ H := by
    rw [Subgroup.derivedSeries_one, commutator_def, Subgroup.commutator_le]
    rintro ⟨g, a, b, ha, hb, hg | hg⟩ - ⟨h, a', b', ha', hb', hh | hh⟩ -
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        dd (dd (dd hg hh) (d_inv ha hb hg)) (d_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        cc (cd (dc hg hh) (d_inv ha hb hg)) (c_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        dd (cc (cd hg hh) (c_inv ha hb hg)) (d_inv ha' hb' hh)⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨_, _, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto, by simp only [ne_eq, mul_eq_zero, inv_eq_zero, not_or]; tauto,
        cc (dc (cc hg hh) (c_inv ha hb hg)) (c_inv ha' hb' hh)⟩
  have h2 : Subgroup.derivedSeries W 2 ≤ T := by
    rw [Subgroup.derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨a, b, ha, hb, hg⟩ := Subgroup.mem_subgroupOf.mp hg
    obtain ⟨a', b', ha', hb', hh⟩ := Subgroup.mem_subgroupOf.mp hh
    have := dd (dd (dd hg hh) (d_inv ha hb hg)) (d_inv ha' hb' hh)
    have e1 : a * a' * a⁻¹ * a'⁻¹ = 1 := by field_simp
    have e2 : b * b' * b⁻¹ * b'⁻¹ = 1 := by field_simp
    rw [e1, e2] at this
    exact this
  have h3 : Subgroup.derivedSeries W 3 = ⊥ := by
    rw [eq_bot_iff, Subgroup.derivedSeries_succ]
    refine (Subgroup.commutator_mono h2 h2).trans ?_
    rw [Subgroup.commutator_le]
    rintro g ⟨n₁, n₂, hg⟩ h ⟨n₁', n₂', hh⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext; ext k
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh]; ring
    · simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hg, hh]; ring
  exact ⟨⟨3, h3⟩⟩

/-- The diagonal substitutions `k ↦ (a k₁, b k₂)`. -/
def diag : Fˣ × Fˣ →* Equiv.Perm (F × F) where
  toFun u := droite (u.1 : F) (u.2 : F) 0 0 u.1.ne_zero u.2.ne_zero
  map_one' := by ext k <;> simp [droite]
  map_mul' u v := by ext k <;> simp [droite, mul_assoc]

theorem diag_injective : Function.Injective (diag (F := F)) := by
  intro u v h
  have h1 : diag u (1, 1) = diag v (1, 1) := by rw [h]
  have h2 : ((u.1 : F) * 1 + 0, (u.2 : F) * 1 + 0) = ((v.1 : F) * 1 + 0, (v.2 : F) * 1 + 0) := h1
  simp only [mul_one, add_zero, Prod.mk.injEq] at h2
  exact Prod.ext (Units.ext h2.1) (Units.ext h2.2)

theorem diag_mem (u : Fˣ × Fˣ) : diag u ∈ produit F :=
  ⟨_, _, u.1.ne_zero, u.2.ne_zero, droite_est _ _ _ _ u.1.ne_zero u.2.ne_zero⟩

/-- The order of `AGL(1, F) ≀ C₂` is divisible by `2 (q - 1)²`, `q` the number of elements of `F`. -/
theorem two_mul_dvd_card [Finite F] : 2 * (Nat.card F - 1) ^ 2 ∣ Nat.card (couronne F) := by
  have h1 : (Nat.card F - 1) ^ 2 ∣ Nat.card (produit F) := by
    have := Subgroup.card_dvd_of_injective ((diag (F := F)).codRestrict (produit F) diag_mem)
      (fun u v h => diag_injective (congrArg Subtype.val h))
    rwa [Nat.card_prod, Nat.card_units, ← pow_two] at this
  have h2 : Nat.card ((produit F).subgroupOf (couronne F)) = Nat.card (produit F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe produit_le_couronne).toEquiv
  have h3 := ((produit F).subgroupOf (couronne F)).index_mul_card
  rw [index_produit, h2] at h3
  rw [← h3]
  exact Nat.mul_dvd_mul_left 2 h1

theorem exists_ne_zero_ne_one [Finite F] (h : 2 < Nat.card F) : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  have h1 : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  exact ⟨u, u.ne_zero, fun h => hu (Units.ext h)⟩

theorem arith (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : ¬ (2 * (ℓ ^ 2 - 1) ^ 2 ∣ ℓ ^ 4 * (ℓ ^ 4 - 1) * 4) := by
  have h4le : 4 ≤ ℓ ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ 2 = m + 1 := ⟨ℓ ^ 2 - 1, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have e1 : ℓ ^ 4 = (m + 1) ^ 2 := by rw [← hm]; ring
  have e2 : ℓ ^ 4 - 1 = m * (m + 2) := by
    rw [e1]; apply Nat.sub_eq_of_eq_add; ring
  rw [e2, e1, hm, Nat.add_sub_cancel]
  intro h
  have h' : 2 * m * m ∣ 2 * m * (2 * (m + 1) ^ 2 * (m + 2)) := by
    convert h using 1 <;> ring
  have h2 : m ∣ 2 * (m + 1) ^ 2 * (m + 2) :=
    (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2 * m)).mp h'
  have h4 : m ∣ 4 := by
    have h3 : m ∣ m * (2 * m ^ 2 + 8 * m + 10) + 4 := by convert h2 using 1; ring
    exact (Nat.dvd_add_right (dvd_mul_right m _)).mp h3
  have h5 : m ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  interval_cases m
  · omega
  · rcases hℓ.eq_or_lt with h2 | h2
    · rw [← h2] at hm; norm_num at hm
    · have h9 : 9 ≤ ℓ ^ 2 :=
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left h2 2
      omega

end GaloisOeuvres.TheorieNombres.Couronne
```

### 8.3 `GaloisOeuvres/TheorieNombresClose.lean`

```lean
import GaloisOeuvres.TheorieNombres
import GaloisOeuvres.EquationsPrimitives
import GaloisOeuvres.TheorieNombresCloseAux1
import GaloisOeuvres.TheorieNombresCloseAux2

/-!
# The converse for primitive equations of degree `p^ν`: refutation and correction

This file closes the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`), where Galois's claim is stated as `ReciproqueGalois`.

* `not_reciproqueGalois`: the claim is false for every prime `ℓ`, already in degree `ℓ⁴`. The
  group `AGL(1, ℓ²) ≀ C₂` of substitutions of `ℓ⁴` letters (`Couronne.couronne`) is primitive and
  solvable, it is the group of an equation (`Realisation.equation`), and its order does not divide
  the number `ℓ⁴ (ℓ⁴ - 1) · 4` of Galois's substitutions.
* `reciproque_corrigee`: what is true. The roots of a primitive equation of degree `p^ν` solvable
  by radicals can be labelled by the `p^ν` imaginaries so that its group consists of linear
  substitutions `k ↦ A k + b`, `A` an invertible linear map of the `ℤ/p`-vector space of the
  imaginaries (`AGL`), and contains all the translations. Galois's substitutions
  `k ↦ (a k + b)^(p^r)` are of this kind (`AGammaL_le_AGL`).
-/

open Polynomial

namespace GaloisOeuvres.TheorieNombres

/-- **The linear substitutions** `k ↦ A k + b` of the points of a vector space over `ℤ/p`
(`A` an invertible linear map): the affine group. -/
def AGL (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∃ A : V ≃ₗ[ZMod p] V, ∃ b : V, ∀ k, σ k = A k + b}
  one_mem' := ⟨LinearEquiv.refl _ _, 0, fun k => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨A, b, hσ⟩ ⟨A', b', hτ⟩
    exact ⟨A'.trans A, A b' + b, fun k => by
      rw [Equiv.Perm.mul_apply, hτ, hσ, map_add, LinearEquiv.trans_apply, add_assoc]⟩
  inv_mem' := by
    rintro σ ⟨A, b, hσ⟩
    refine ⟨A.symm, -(A.symm b), fun k => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hσ, map_add, map_neg, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    abel

theorem mem_AGL_of_linearMap {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {σ : Equiv.Perm V} (A : V →ₗ[ZMod p] V) (b : V) (h : ∀ k, σ k = A k + b) : σ ∈ AGL p V := by
  have hA : ∀ k, A k = σ k - b := fun k => by rw [h]; abel
  have hbij : Function.Bijective A := by
    constructor
    · intro k k' hk
      apply σ.injective
      rw [h, h, hk]
    · intro y
      refine ⟨σ.symm (y + b), ?_⟩
      rw [hA, Equiv.apply_symm_apply]; abel
  exact ⟨LinearEquiv.ofBijective A hbij, b, fun k => by rw [LinearEquiv.ofBijective_apply, h]⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- Galois's substitutions are linear substitutions: `AΓL(1, p^ν) ≤ AGL(ν, p)`. -/
theorem AGammaL_le_AGL (K : Type*) [Field K] [Finite K] [Algebra (ZMod p) K] :
    AGammaL (p := p) K ≤ AGL p K := by
  rintro σ ⟨r, A, -, B, h⟩
  refine mem_AGL_of_linearMap
    ((LinearMap.mulLeft (ZMod p) A).comp
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K ^ r).toLinearMap) B fun k => ?_
  rw [h, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearMap_apply,
    frob_pow_apply]

/-- **The corrected converse** (Galois, Jordan). -/
theorem reciproque_corrigee {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)] {ν : ℕ} (hν : ν ≠ 0)
    (hirr : Irreducible f) (hdeg : f.natDegree = p ^ ν)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ e : GaloisField p ν ≃ f.rootSet Ω,
      (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL p (GaloisField p ν)) ∧
      ∀ b : GaloisField p ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b := by
  classical
  have hdeg0 : (f.map (algebraMap K Ω)).degree ≠ 0 := by
    rw [degree_map]; exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap K Ω)) hdeg0
  have hxr : x ∈ f.rootSet Ω := by
    rw [mem_rootSet]; exact ⟨hirr.ne_zero, by rwa [aeval_def, eval₂_eq_eval_map]⟩
  have hG : Group.IsSolvable f.Gal :=
    isSolvable_gal_of_irreducible (hsol x hxr) hirr (mem_rootSet.mp hxr).2
  have : Group.IsSolvable (groupe f Ω) :=
    Group.isSolvable_of_surjective (Gal.galActionHom f Ω).rangeRestrict_surjective
  have hcard : Nat.card (f.rootSet Ω) = p ^ ν := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hirr.separable
      (Fact.out : (f.map (algebraMap K Ω)).Splits), hdeg]
  have hp2 := hp.out.two_le
  have : Nontrivial (f.rootSet Ω) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]; exact Nat.one_lt_pow hν hp.out.one_lt)
  obtain ⟨q, μ, hq, e₀, hlin, htr⟩ :=
    EquationsPrimitives.exists_affine_indexing (G := groupe f Ω) (X := f.rootSet Ω)
  have hcard' : q ^ μ = p ^ ν := by
    rw [← hcard, Nat.card_congr e₀, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard'
    exact (Nat.one_lt_pow hν hp.out.one_lt).ne hcard'
  have hpq : p = q := by
    have h1 : q ∣ p ^ ν := by rw [← hcard']; exact dvd_pow_self q hμ
    exact ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h1)).symm
  subst hpq
  have hνμ : ν = μ := (Nat.pow_right_injective hp2 hcard').symm
  subst hνμ
  let B : GaloisField p ν ≃ₗ[ZMod p] (Fin ν → ZMod p) :=
    (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p ν) (GaloisField.finrank p hν)).equivFun
  refine ⟨B.toEquiv.trans e₀.symm, fun σ => ?_, fun b => ?_⟩
  · obtain ⟨M, -, c, hM⟩ := hlin ⟨Gal.galActionHom f Ω σ, ⟨σ, rfl⟩⟩
    refine mem_AGL_of_linearMap ((B.symm.toLinearMap.comp M.mulVecLin).comp B.toLinearMap)
      (B.symm c) fun k => ?_
    change B.symm (e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k)))) = _
    have := hM (e₀.symm (B k))
    rw [Equiv.apply_symm_apply] at this
    change e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k))) = _ at this
    rw [this, map_add]
    rfl
  · obtain ⟨g, hg⟩ := htr (B b)
    obtain ⟨σ, hσ⟩ := g.2
    refine ⟨σ, fun k => ?_⟩
    change B.symm (e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k)))) = _
    have := hg (e₀.symm (B k))
    rw [Equiv.apply_symm_apply] at this
    rw [hσ]
    change e₀ ((g : Equiv.Perm (f.rootSet Ω)) (e₀.symm (B k))) = _ at this
    rw [this, map_add, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- **The corrected converse, with the degree.** -/
theorem reciproque_corrigee_degre {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)]
    (hirr : Irreducible f) (hdeg : f.natDegree ≠ 1)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ (ℓ ν : ℕ) (_ : Fact ℓ.Prime), ν ≠ 0 ∧ f.natDegree = ℓ ^ ν ∧
      ∃ e : GaloisField ℓ ν ≃ f.rootSet Ω,
        (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL ℓ (GaloisField ℓ ν)) ∧
        ∀ b : GaloisField ℓ ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b := by
  obtain ⟨q, k, hq, hk⟩ := degre_primitive f hirr hprim hsol
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hdeg (by rw [hk, pow_zero])
  have := Fact.mk hq
  exact ⟨q, k, ⟨hq⟩, hk0, hk, reciproque_corrigee f hk0 hirr hk hprim hsol⟩

/-- What the printed claim would give for a solvable primitive group of degree `ℓ ^ ν`. -/
theorem card_dvd_of_reciproque (ℓ : ℕ) [Fact ℓ.Prime] (H : ReciproqueGalois ℓ) {X : Type}
    [Finite X] (Γ : Subgroup (Equiv.Perm X)) [MulAction.IsPreprimitive Γ X] [Group.IsSolvable Γ]
    (ν : ℕ) (hν : ν ≠ 0) (h9 : ℓ ^ ν ≠ 9) (h25 : ℓ ^ ν ≠ 25) (hX : Nat.card X = ℓ ^ ν) :
    Nat.card Γ ∣ ℓ ^ ν * (ℓ ^ ν - 1) * ν := by
  obtain ⟨x₀⟩ : Nonempty X :=
    (Nat.card_pos_iff.mp (by rw [hX]; exact pow_pos (Fact.out : ℓ.Prime).pos ν)).1
  rw [← Realisation.card_gal Γ x₀]
  exact reciproque_borne ℓ H (Realisation.Corps Γ) (Realisation.Cloture Γ)
    (Realisation.equation Γ x₀) ν hν h9 h25 (Realisation.equation_irreducible Γ x₀)
    ((Realisation.natDegree_equation Γ x₀).trans hX) (Realisation.primitif Γ x₀)
    (Realisation.soluble Γ x₀)

/-- **Galois's converse claim, read literally, is false for every prime `ℓ`.** -/
theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : ¬ ReciproqueGalois ℓ := by
  intro H
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hF : Nat.card (GaloisField ℓ 2) = ℓ ^ 2 := GaloisField.card ℓ 2 two_ne_zero
  have h4le : 4 ≤ ℓ ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
  have h3 : ∃ c : GaloisField ℓ 2, c ≠ 0 ∧ c ≠ 1 :=
    Couronne.exists_ne_zero_ne_one (by rw [hF]; omega)
  have := Couronne.couronne_primitif h3
  have := Couronne.couronne_soluble (F := GaloisField ℓ 2)
  have hX : Nat.card (GaloisField ℓ 2 × GaloisField ℓ 2) = ℓ ^ 4 := by
    rw [Nat.card_prod, hF]; ring
  have hpow : ℓ ^ 4 = 16 ∨ 81 ≤ ℓ ^ 4 := by
    rcases hℓ.eq_or_lt with h | h
    · left; rw [← h]; norm_num
    · right
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ ℓ ^ 4 := Nat.pow_le_pow_left h 4
  have h := card_dvd_of_reciproque ℓ H (Couronne.couronne (GaloisField ℓ 2)) 4 (by norm_num)
    (by omega) (by omega) hX
  have h2 := (Couronne.two_mul_dvd_card (F := GaloisField ℓ 2)).trans h
  rw [hF] at h2
  exact Couronne.arith ℓ hℓ h2

end GaloisOeuvres.TheorieNombres
```

---

## 9. REJECTED CRITIQUES

None. Every issue raised by the two critiques of the previous version was checked and found
correct, and the blueprint was revised accordingly:

* RISKS item 11 (a "Hilbert repository" move): not supported by the request or by any repository
  file; deleted.
* The omission of the irreducibility of the point stabilizer is now stated in 1.2, RISKS 10 and
  the proposed Lean reading (7.2).
* The B3 wording now uses `IsTrivialBlock` (`B.Subsingleton ∨ B = Set.univ`).
* The A7 remark now says that the application needs `Ω` algebraically closed and in `Type`
  (`Ω = AlgebraicClosure (Corps Γ)`).
* The remark in 2.4 now says that the divisibility fails for every `p ≥ 5`, and that `p = 5` is
  left out only because `25` is an excluded degree.
* The separate compiles of Aux1 and Aux2 (critic's scratch files, byte-identical to `reference/`)
  are recorded in 4.0 and RISKS 1, together with the strict build order.
* The section 5 sentence about fraction-field actions is corrected:
  `IsFractionRing.mulSemiringAction` exists (checked by `rg`, `FractionRing.lean` l. 670–690).

Three suggestions are recorded as **optional** and deliberately **not** applied to the reference
code, because each one would invalidate the verified compiles of Aux1/Aux2 and cost a recompile
of about 35 minutes for no change in meaning: scoped instances (4.1 and RISKS 3), renaming the
letter-type variable `X` (4.1), and refactoring the fragile `simp` proofs in Aux2 (4.2). Each is
documented where an implementer will see it.
