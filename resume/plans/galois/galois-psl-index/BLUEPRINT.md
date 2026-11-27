# BLUEPRINT — `lettre.impossible_au_dela`: `PSL(2, p)` has no subgroup of index `p` for `p > 11`

**Verdict on the target: true as formalized.** No counterexample exists (this is Galois's theorem;
the checks made on the formal statement are listed in §6.1).

**Route.** A class-equation count inside the preimage `K ≤ SL(2, p)` of the hypothetical subgroup
`H ≤ PSL(2, p)`. No classification of subgroups (Dickson) is used. Ingredients: 2×2 matrix algebra
over a field, orbit–stabilizer for the conjugation action on subgroups, and a finite Diophantine
case analysis. The original sketch has been verified and simplified in three places (§3.0).

**How far this blueprint goes.** Besides the mathematics (§3) and the architecture (§4), §7 contains
the *complete Lean text* of all four new files. **These four texts have been type-checked together, with no error, in the scratch file
`.lake-local/scratch/psl-index/T9.lean`** (the four files concatenated, each in its own `section`
with exactly its own `open` lines, under `import Mathlib` + `import GaloisOeuvres.LettreChevalier`;
`[OK]` in 181 s), and `#print axioms GaloisOeuvres.LettreChevalier.abaissement_impossible` reports
only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, new axiom, `native_decide`,
`unsafe` or `implemented_by`. The implementer's job is therefore to copy §7 into the four files
and compile them in order; §3–§5 explain the proof so that any breakage can be repaired.

---------------------------------------------------------------------------------------------------

## 1. TARGET

File `GaloisOeuvres/LettreChevalier.lean`, lines 3152–3157, namespace
`GaloisOeuvres.LettreChevalier`:

```lean
/-- **Galois's impossibility claim**: for a prime `p > 11`, the modular group `PSL(2, p)` has no
subgroup of index `p`, so the modular equation of degree `p + 1` cannot be lowered to degree `p`.
Not proved here (it needs Dickson's classification of the subgroups of `PSL(2, q)`). -/
def AbaissementImpossible : Prop :=
  ∀ p : ℕ, ∀ _ : Fact p.Prime, 11 < p →
    ∀ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)), H.index ≠ p
```

Final theorem to be produced, in the new file `GaloisOeuvres/LettreChevalierClose.lean`:

```lean
namespace GaloisOeuvres.LettreChevalier

/-- Galois's impossibility claim (`lettre.impossible_au_dela`). -/
theorem abaissement_impossible : AbaissementImpossible
```

i.e. `GaloisOeuvres.LettreChevalier.abaissement_impossible :
GaloisOeuvres.LettreChevalier.AbaissementImpossible`. It is a three-line consequence of

```lean
namespace GaloisOeuvres.LettreChevalierClose

theorem no_subgroup_index_p (p : ℕ) [Fact p.Prime] (hp : 11 < p)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) (hH : H.index = p) :
    False
```

namely `intro p hp h11 H hH; haveI := hp; exact LettreChevalierClose.no_subgroup_index_p p h11 H hH`
(the binder `∀ _ : Fact p.Prime` of the definition is explicit, hence the `haveI`).

Existing files are not modified by the implementation of this blueprint. The later wiring (someone
else's job) consists of the following steps, in this order:
1. **(mandatory for CI coverage)** add the four new modules (`GaloisOeuvres.LettreChevalierCloseAux1`,
   `…Aux2`, `…Aux3`, `GaloisOeuvres.LettreChevalierClose`) as imports of `GaloisOeuvres.lean`.
   `lakefile.toml` declares only `[[lean_lib]] name = "GaloisOeuvres"` with
   `defaultTargets = ["GaloisOeuvres"]` and no globs, so a module not imported from
   `GaloisOeuvres.lean` is neither built nor axiom-audited by CI.
2. in `GaloisOeuvres/LettreChevalier.lean`, update the doc-comment of the unit
   `lettre.impossible_au_dela` (it says the result "needs that classification, which mathlib
   lacks") and its `**Status.**` line (currently "stated (open here)"); the new status line must
   name the proving theorem `GaloisOeuvres.LettreChevalier.abaissement_impossible` and its file
   `GaloisOeuvres/LettreChevalierClose.lean`, because `scripts/unit_table.py` lists only the
   declarations that follow the unit block *in the same file* and will therefore not find the
   theorem by itself.
3. **regenerate** `docs/UNITS.md` with `python scripts/unit_table.py` (never edit it by hand: CI
   runs `python3 scripts/unit_table.py --check` and then `git diff --exit-code docs/UNITS.md`, see
   `.github/workflows/ci.yml` lines 22–23, so a hand edit that differs from the generator's output
   fails CI).
4. update the other prose that calls the unit open: `README.md` line 29 and
   `docs/FAITHFULNESS.md` line 97.

---------------------------------------------------------------------------------------------------

## 2. EXISTING MATERIAL

All in `GaloisOeuvres/LettreChevalier.lean`, namespace `GaloisOeuvres.LettreChevalier`. The file
begins with `import GaloisOeuvres.Radicaux` (which gives `import Mathlib` transitively, through
`GaloisOeuvres/Basic.lean`), and has `open Polynomial Matrix Projectivization` and
`open scoped LinearAlgebra.Projectivization MatrixGroups`.

**Used by the proof (one declaration only):**

```lean
-- line 2370, inside `section DecompositionPSL`, which has `variable (p : ℕ) [Fact p.Prime]`
/-- `|PSL(2, p)| = (p + 1) p (p - 1) / 2` for odd `p`. -/
theorem card_PSL (hp2 : p ≠ 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) = (p + 1) * p * (p - 1) / 2
```

so its full signature is
`GaloisOeuvres.LettreChevalier.card_PSL (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : Nat.card … = …`
(`p` explicit).

**Available and related, but not needed** (listed so that nobody re-proves or misuses them):

```lean
-- line 2887
lemma card_of_index {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) (hH : H.index = p) :
    Nat.card H = (p + 1) * p * (p - 1) / 2 / p
-- line 2503
theorem prime_dvd_card_PSL (ℓ : ℕ) [Fact ℓ.Prime] :
    ℓ ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod ℓ))
-- line 2517
theorem index_ge (ℓ : ℕ) [Fact ℓ.Prime] (h5 : ℓ ≠ 2 ∧ ℓ ≠ 3)
    (K : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod ℓ))) (hK : K ≠ ⊤) :
    ℓ ≤ K.index
-- line 2894
theorem abaissement_5_7_11 :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)),
      H.index = 5 ∧ Nat.card H = 12) ∧
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)),
      H.index = 7 ∧ Nat.card H = 24) ∧
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 11)),
      H.index = 11 ∧ Nat.card H = 60)
-- line 2601
theorem stabilisateur {F : Type*} [Field F] (A : SL(2, F)) :
    (A • pt (some (0 : F)) = pt (some 0) ∧ A • pt (none : Option F) = pt none) ↔
      ∃ m : F, m ≠ 0 ∧ ∀ x : Option F, A • pt x = pt (Option.map (fun k => m ^ 2 * k) x)
-- line 2692: theorem cinq_seulement … : p = 5      (Galois's own partial argument)
```

(`card_of_index` states `Nat.card H` with a nested natural-number division; the proof below
prefers the multiplicative form `p * Nat.card H = (p + 1) * p * (p - 1) / 2`, obtained directly from
`card_PSL` and `Subgroup.index_mul_card`.)

**Facts about the existing definitions that matter.**

* `Matrix.ProjectiveSpecialLinearGroup n R` is, in mathlib
  (`Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`), an `abbrev` for
  `Matrix.SpecialLinearGroup n R ⧸ Subgroup.center (Matrix.SpecialLinearGroup n R)`. Hence
  `QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))` has type
  `SL(2, ZMod p) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)` on the nose.
* The repository contains **no** lemma about lifting from `PSL` to `SL`, about centralizers in
  `SL₂`, or about `|center SL(2, p)| = 2`. It talks to `PSL(2, p)` only through the permutation
  representation `rho` on `Option (ZMod p)` (line 812). The present proof does not use `rho`, and it
  never needs `|center| = 2` (Lemma E2 explains why).
* Mathlib has nothing on centralizers / tori / normalizers of tori in `SL₂` over a finite field
  (searched `Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`,
  `Mathlib/LinearAlgebra/Projectivization/PSL/`, `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/`).
  It has the center of `SL(n, R)` (`Matrix.SpecialLinearGroup.mem_center_iff`); we do not need it:
  only the trivial direction "scalar ⇒ central" is used, and it is proved by hand (Lemma C3).
* Name warning: the namespace `GaloisOeuvres.LettreChevalier` contains a definition `conjAct`
  (line 826, a `MulAction` of `PSL(2,p)` on permutations). Mathlib's conjugation type synonym is
  `ConjAct` (capital C). The three auxiliary files live in another namespace
  (`GaloisOeuvres.LettreChevalierClose`) and do not import `LettreChevalier`; the last file imports
  it but does not mention `ConjAct`. No clash.

---------------------------------------------------------------------------------------------------

## 3. MATHEMATICAL PROOF

### 3.0 Overview and notation

`F` is a field, `M₂(F)` the 2×2 matrices over `F`, `S = SL(2, F)`, `Zc` the center of `S`,
`G = PSL(2, F) = S / Zc`, `π : S → G` the quotient map. For `A ∈ M₂(F)` write
`a = A₀₀, b = A₀₁, c = A₁₀, d = A₁₁` and `tr A = a + d`.
`A` is **non-scalar**, written `NS(A)`, if `b ≠ 0 ∨ c ≠ 0 ∨ a ≠ d`.
For `A ∈ S`, `cen(A) = {X ∈ S : A X = X A}` is the centralizer of `A` in `S`.

Plan. Let `p > 11` be prime, `F = 𝔽_p`, and suppose `H ≤ G` has index `p`. Put `h = |H|`,
`z = |Zc|` and `K = π⁻¹(H) ≤ S`. Then `h = 2m(m+1)` where `p = 2m + 1`, `p ∤ h`, `Zc ≤ K`,
`|K| = h z`. For `x ∈ K ∖ Zc` let `D(x) = K ∩ cen(x)`. We show:

1. the sets `D(x) ∖ Zc` (`x ∈ K ∖ Zc`) partition `K ∖ Zc`, because commuting is an equivalence
   relation on the non-central elements of `S`;
2. `D(k x k⁻¹) = k D(x) k⁻¹` for `k ∈ K`;
3. the normalizer `N_K(D(x))` has order `|D(x)|` or `2|D(x)|`; this uses `(tr x)² ≠ 4`, which holds
   for `x ∈ K ∖ Zc` because `p ∤ |H|`;
4. `|D(x)| ≤ |cen(x)| ≤ 2p`.

Counting `K ∖ Zc` over the `K`-conjugacy classes of the subgroups `D(x)` gives
`|K| − z = Σ_i (|K| / (e_i a_i)) (a_i − z)` with `a_i = |D(x_i)|`, `e_i ∈ {1, 2}`. Dividing by `z`
(`c_i = a_i / z ≥ 2`, `q_i = h / (e_i c_i)`): `Σ_i q_i (c_i − 1) = h − 1` with `h = q_i e_i c_i`,
`c_i ≥ 2`, `2 c_i < h`, `h > 60`. An elementary case analysis shows that this is impossible.

Differences from the original sketch (each one checked below; none weakens the result):

* (a) The exact orders `p ∓ 1` of the tori are **not** needed. Only the crude bound `|cen(A)| ≤ 2p`
  for non-scalar `A` is used (Lemma C7); it needs no discriminant hypothesis. In the arithmetic the
  bound is used only as `2c_i < h`, i.e. `c_i ∉ {h, h/2}`.
* (b)–(d) The count is done in `K ≤ SL(2, p)` rather than in `H ≤ PSL(2, p)`: "the torus of an
  element of `PSL`" would require choosing lifts, and commuting in `PSL` means commuting up to sign
  in `SL`. In `SL` the relation is plain commutation. The price is that one counts `K ∖ Zc` instead
  of `H ∖ {1}`, and every cardinality is multiplied by `z = |Zc|`; `z` cancels at the end and its
  value (it is 2) is never needed.
* (e) The arithmetic is carried out with integers `q_i = h/(e_i c_i)` instead of fractions; the
  integrality of `q_i` makes two of the cases of the sketch immediate.

---

### 3.1 Part A — arithmetic

All variables are natural numbers; `x − y` is used only when `y ≤ x`.

**Lemma A0 (size of a term).** Let `h = q·e·c` with `e ∈ {1, 2}`, `c ≥ 2`, and `T = q(c − 1)`.
Then `T = qc − q` and `2q ≤ qc`. If `e = 1` then `h = qc`, `T = h − q` and `2T ≥ h`. If `e = 2`
then `h = 2qc`, `2T = h − 2q` and `4T ≥ h`. In all cases `4T ≥ h`. If `h > 0` then `q ≥ 1`.

*Proof.* `c ≥ 2` gives `2q ≤ qc`. If `e = 1`: `2T = 2h − 2q ≥ 2h − qc = h`. If `e = 2`:
`2T = 2qc − 2q = h − 2q` and `4T = 2h − 4q ≥ 2h − 2qc = h`. If `q = 0` then `h = 0`. ∎

**Lemma A1 (one term).** If `h > 60`, `e ∈ {1,2}`, `c ≥ 2`, `2c < h`, `h = q e c`, then
`q(c − 1) + 1 ≠ h`.

*Proof.* Let `X = qc` (so `2q ≤ X`) and suppose `X − q + 1 = h`.
If `e = 1`: `h = X`, hence `q = 1`, hence `h = c`, contradicting `2c < h`.
If `e = 2`: `h = 2X`, hence `X + q = 1`; then `(X, q) = (1, 0)` (the other possibility `(0, 1)`
violates `2q ≤ X`), so `h = 2`, contradicting `h > 60`. ∎

**Lemma A2′ (two terms, `e = (1, 2)`).** If `h > 60`, `c₁, c₂ ≥ 2`, `2c₂ < h`, `h = q₁c₁`,
`h = 2 q₂ c₂`, then `(q₁c₁ − q₁) + (q₂c₂ − q₂) + 1 ≠ h`.

*Proof.* Let `X₂ = q₂c₂`, so `h = q₁c₁ = 2X₂`, `2q₂ ≤ X₂`. Suppose equality; it reads
`X₂ + 1 = q₁ + q₂`.
* `c₁ = 2`: `2q₁ = 2X₂`, so `q₁ = X₂`, so `q₂ = 1`, so `X₂ = c₂` and `h = 2c₂`: contradicts
  `2c₂ < h`.
* `c₁ = 3`: `3q₁ = 2X₂`.
  If `c₂ = 2`: `X₂ = 2q₂`, so `q₁ = q₂ + 1` and `3q₂ + 3 = 4q₂`, `q₂ = 3`, `h = 2X₂ = 12`:
  contradicts `h > 60`.
  If `c₂ ≥ 3`: `3q₂ ≤ X₂`; from `q₁ = X₂ + 1 − q₂` and `3q₁ = 2X₂` we get `X₂ = 3q₂ − 3 < 3q₂`:
  contradiction.
* `c₁ ≥ 4`: `4q₁ ≤ q₁c₁ = 2X₂`, so `2q₁ ≤ X₂`; with `2q₂ ≤ X₂`: `q₁ + q₂ ≤ X₂ < X₂ + 1`. ∎

**Lemma A2 (two terms).** If `h > 60` and for `i = 1, 2`: `e_i ∈ {1,2}`, `c_i ≥ 2`, `2c_i < h`,
`h = q_i e_i c_i`, then `q₁(c₁ − 1) + q₂(c₂ − 1) + 1 ≠ h`.

*Proof.* Let `X_i = q_i c_i` (`2q_i ≤ X_i`; `q_i ≥ 1` by A0) and suppose
`(X₁ − q₁) + (X₂ − q₂) + 1 = h`.
* `e = (1,1)`: `h = X₁ = X₂`, so `q₁ + q₂ = h + 1`; but `2q_i ≤ h`, so `q₁ + q₂ ≤ h`.
* `e = (2,2)`: `h = 2X₁ = 2X₂`, so `X₁ + X₂ = h` and `q₁ + q₂ = 1`: contradicts `q₁, q₂ ≥ 1`.
* `e = (1,2)`: Lemma A2′.  `e = (2,1)`: Lemma A2′ with the two indices exchanged. ∎

**Lemma A3′ (three terms, all `e = 2`, `c₁ = 2`).** There are no `h > 60`, `q₁, q₂, q₃`,
`c₂, c₃ ≥ 2` with `2c₂ < h`, `2c₃ < h`, `h = 2(q₁·2) = 2(q₂c₂) = 2(q₃c₃)` and
`(2q₁ − q₁) + (q₂c₂ − q₂) + (q₃c₃ − q₃) + 1 = h`.

*Proof.* Put `P = 2q₁ = q₂c₂ = q₃c₃`, so `h = 2P`. The equation is
`q₁ + (P − q₂) + (P − q₃) + 1 = 2P`, i.e. `q₂ + q₃ = q₁ + 1`, i.e. `2(q₂ + q₃) = P + 2`.
* `c₂ = 2`: `P = 2q₂`, so `q₂ = q₁`, so `q₃ = 1`, so `P = c₃` and `h = 2c₃`: contradicts
  `2c₃ < h`.
* `c₃ = 2`: symmetric (`q₂ = 1`, `h = 2c₂`, contradicts `2c₂ < h`).
* Otherwise `c₂, c₃ ≥ 3`. Split each of `c₂`, `c₃` into the cases `3, 4, 5, ≥ 6`. In the case
  `c_j = k ∈ {3,4,5}` we have `P = k q_j`; in the case `c_j ≥ 6` we have `6q_j ≤ P`.
  - `(3,3)`: `2(P/3 + P/3) = P + 2`, `P = 6`, `h = 12`.
  - `(3,4)`, `(4,3)`: `2(P/3 + P/4) = P + 2`, `P = 12`, `h = 24`.
  - `(3,5)`, `(5,3)`: `2(P/3 + P/5) = P + 2`, `P = 30`, `h = 60`.
    These three contradict `h > 60`.
  - `(3, ≥6)`, `(≥6, 3)`: `2(q₂ + q₃) ≤ 2(P/3 + P/6) = P < P + 2`.
  - both `c₂, c₃ ≥ 4` (the remaining 9 of the 16 cases): `2(q₂ + q₃) ≤ 2(P/4 + P/4) = P < P + 2`.
  (Each case is a linear statement in the "atoms" `h, q₁, q₂, q₃, q₂c₂, q₃c₃`.) ∎

**Lemma A3 (three terms).** If `h > 60` and for `i = 1,2,3`: `e_i ∈ {1,2}`, `c_i ≥ 2`,
`2c_i < h`, `h = q_i e_i c_i`, then `q₁(c₁−1) + q₂(c₂−1) + q₃(c₃−1) + 1 ≠ h`.

*Proof.* Let `T_i = q_i(c_i − 1)` and suppose `T₁ + T₂ + T₃ = h − 1`. If some `e_i = 1`, then by A0
`2T_i ≥ h` and `4T_j ≥ h` for the two others, so `4(T₁ + T₂ + T₃) ≥ 4h > 4(h − 1)`:
contradiction. So all `e_i = 2`; then `h = 2X_i` with `X_i = q_i c_i`, all `X_i` are equal, and the
equation reads `X₁ + 1 = q₁ + q₂ + q₃`. If all `c_i ≥ 3` then `3q_i ≤ X_i = X₁` and
`q₁ + q₂ + q₃ ≤ X₁`: contradiction. Hence some `c_i = 2`, and Lemma A3′ applies after renaming the
indices so that this `i` is `1` (the hypotheses of A3′ are symmetric in the two other indices). ∎

**Lemma A4 (no class equation).** Let `s` be a finite set, `c, q, e : s → ℕ` and `h > 60`, such
that `e_i ∈ {1,2}`, `c_i ≥ 2`, `2c_i < h`, `h = q_i e_i c_i` for all `i ∈ s`. Then
`Σ_{i∈s} q_i (c_i − 1) + 1 ≠ h`.

*Proof.* Suppose equality. By A0, `4 q_i(c_i − 1) ≥ h` for each `i`, so
`|s|·h ≤ 4 Σ_i q_i(c_i−1) = 4(h − 1) < 4h` and `|s| ≤ 3`. If `|s| = 0` the sum is `0` and `h = 1`:
contradiction. If `|s| = 1, 2, 3`, write `s = {a}`, `{a,b}` (`a ≠ b`), `{a,b,d}` (pairwise
distinct) and apply A1, A2, A3. ∎

Independent check of A4 (not part of the proof): a brute-force search over all `h < 400` and all
multisets of at most four admissible terms finds solutions of `Σ q_i(c_i−1) = h − 1` only for
`h = 12` (`(c,e) = (3,1),(2,2)` and `(2,2),(3,2),(3,2)`), `h = 24` (`(2,2),(3,2),(4,2)`),
`h = 60` (`(2,2),(3,2),(5,2)`) — the subgroups `A₄ ≤ PSL(2,5)`, `S₄ ≤ PSL(2,7)`,
`A₅ ≤ PSL(2,11)` — in agreement with the lemma (script result recorded in §6.1).

---

### 3.2 Part B — an abstract counting theorem

**Lemma B1 (weighted class formula).** Let a finite group `Γ₀` act on a finite set `β` and let
`f : β → ℕ` be invariant (`f(g·b) = f(b)`). Let `Ω` be the set of orbits and choose for each
`ω ∈ Ω` a representative `b_ω ∈ ω` (in Lean: `ω.out`). Then
`Σ_{b ∈ β} f(b) = Σ_{ω ∈ Ω} (|Γ₀| / |Stab(b_ω)|) · f(b_ω)`.

*Proof.* `β` is the disjoint union of the fibres `β_ω = {b : [b] = ω}` of the quotient map, and
`β_ω` is the orbit of `b_ω`. On `β_ω`, `f` is constantly `f(b_ω)`, so
`Σ_{b∈β_ω} f(b) = |β_ω| f(b_ω)`. By orbit–stabilizer `|β_ω| = [Γ₀ : Stab(b_ω)]`, and
`[Γ₀ : Stab(b_ω)]·|Stab(b_ω)| = |Γ₀|` gives `|β_ω| = |Γ₀| / |Stab(b_ω)|` (exact division). ∎

**Lemma B2 (conjugation on subgroups).** Let `Γ` be a finite group. `Γ` acts on the finite set of
its subgroups by `k·C = kCk⁻¹`, and the stabilizer of `C` is the normalizer `N_Γ(C)`. Consequently,
for every conjugation-invariant `w : {subgroups of Γ} → ℕ`:
`Σ_C w(C) = Σ_ω (|Γ| / |N_Γ(C_ω)|) · w(C_ω)`, the sum being over the conjugacy classes `ω` of
subgroups and `C_ω` a chosen representative of `ω`.

*Proof.* B1 for the action of `ConjAct Γ` on `Subgroup Γ`. The stabilizer in `ConjAct Γ` and the
normalizer in `Γ` correspond under the bijection `ConjAct.ofConjAct` (mathlib:
`Subgroup.conjAct_pointwise_smul_iff : ConjAct.toConjAct g • H = H ↔ g ∈ normalizer H`), so they
have the same cardinality; and `|ConjAct Γ| = |Γ|`. ∎

**Lemma B3 (normalizer of a "class subgroup").** Let `Γ` be a finite group, `D ≤ Γ`, `x ∈ D`,
and assume
 (i) for all `n ∈ Γ`: `n x n⁻¹ ∈ D ⟹ n x n⁻¹ = x ∨ n x n⁻¹ = x⁻¹`;
 (ii) for all `n ∈ Γ`: `n x n⁻¹ = x ⟹ n ∈ D`.
Then `|N_Γ(D)| = |D|` or `|N_Γ(D)| = 2|D|`.

*Proof.* Let `N = N_Γ(D)`; `D ≤ N`, so `|D|` divides `|N|` (Lagrange).
Claim: if `n ∈ N ∖ D` then `n x n⁻¹ = x⁻¹`. Indeed `n x n⁻¹ ∈ D` because `x ∈ D` and `n`
normalizes `D`; by (i) it is `x` or `x⁻¹`; if it were `x`, then `n ∈ D` by (ii).
If `N ⊆ D` then `|N| ≤ |D|`. Otherwise fix `n₀ ∈ N ∖ D`. Let `n ∈ N ∖ D` and `m = n₀⁻¹ n`. Then
`m x m⁻¹ = n₀⁻¹ (n x n⁻¹) n₀ = n₀⁻¹ x⁻¹ n₀`, and `n₀⁻¹ x⁻¹ n₀ = n₀⁻¹ (n₀ x n₀⁻¹) n₀ = x` (using
the claim for `n₀`). So `m x m⁻¹ = x` and `m ∈ D` by (ii), i.e. `n = n₀ m ∈ n₀D`. Hence
`N ⊆ D ∪ n₀D` and `|N| ≤ 2|D|`. In both cases `0 < |N| ≤ 2|D|` and `|D| ∣ |N|`, so
`|N| = e|D|` with `e ∈ {1, 2}` (this `e` is the `e_i` of B4). ∎

**Theorem B4 (partition count).** Let `Γ` be a finite group, `Z ≤ Γ` a subgroup and
`D : Γ → {subgroups of Γ}` a map such that for all `x, y, k, n ∈ Γ`:
 (B4.1) `x ∉ Z ⟹ x ∈ D(x)`;
 (B4.2) `x ∉ Z ⟹ Z ≤ D(x)`;
 (B4.3) `x ∉ Z, y ∉ Z, y ∈ D(x) ⟹ D(y) = D(x)`;
 (B4.4) `x ∉ Z ⟹ k x k⁻¹ ∉ Z`;
 (B4.5) `y ∈ D(x) ⟹ k y k⁻¹ ∈ D(k x k⁻¹)`;
 (B4.6) `x ∉ Z, n x n⁻¹ ∈ D(x) ⟹ n x n⁻¹ = x ∨ n x n⁻¹ = x⁻¹`;
 (B4.7) `x ∉ Z, n x n⁻¹ = x ⟹ n ∈ D(x)`.
Then there are a finite index set `ι`, elements `x_i ∈ Γ ∖ Z` and numbers `e_i ∈ {1, 2}`
(`i ∈ ι`) such that `e_i·|D(x_i)|` divides `|Γ|` for every `i`, and

  `Σ_{i∈ι} (|Γ| / (e_i |D(x_i)|)) · (|D(x_i)| − |Z|) = |Γ| − |Z|`.

*Proof.*
Step 1 (`D` is conjugation-equivariant): `D(k x k⁻¹) = k D(x) k⁻¹` for all `k, x`.
"⊇" is (B4.5). "⊆": let `y ∈ D(k x k⁻¹)`. Apply (B4.5) with `k⁻¹` in place of `k`, `k x k⁻¹` in
place of `x`: `k⁻¹ y k ∈ D(k⁻¹ (k x k⁻¹) k) = D(x)`, i.e. `y ∈ k D(x) k⁻¹`.

Step 2 (weight). For a subgroup `C` put `w(C) = #{x ∈ Γ : x ∉ Z ∧ D(x) = C}`. Sorting the
elements `x ∉ Z` by the value `D(x)` gives `Σ_C w(C) = #{x : x ∉ Z} = |Γ| − |Z|`.

Step 3 (`w` is invariant). For `k ∈ Γ` the injective map `x ↦ k x k⁻¹` sends
`{x ∉ Z : D(x) = C}` into `{x ∉ Z : D(x) = kCk⁻¹}` by (B4.4) and Step 1. So
`w(C) ≤ w(kCk⁻¹)` for all `k, C`; applying this to `k⁻¹` and `kCk⁻¹` gives the reverse inequality.

Step 4 (value of `w`). If `x₀ ∉ Z` then `{x : x ∉ Z ∧ D(x) = D(x₀)} = D(x₀) ∖ Z`:
if `x ∉ Z` and `D(x) = D(x₀)` then `x ∈ D(x) = D(x₀)` by (B4.1); conversely if `x ∈ D(x₀)` and
`x ∉ Z`, then `D(x) = D(x₀)` by (B4.3). Since `Z ⊆ D(x₀)` by (B4.2),
`w(D(x₀)) = |D(x₀)| − |Z|`.

Step 5. By B2 and Steps 2–3, `|Γ| − |Z| = Σ_ω (|Γ| / |N_Γ(C_ω)|) w(C_ω)`. Let `ι` be the set of
classes `ω` with `w(C_ω) ≠ 0`; the terms outside `ι` vanish. For `i ∈ ι` choose `x_i ∉ Z` with
`D(x_i) = C_i` (possible since `w(C_i) > 0`). By B3 — its hypotheses (i), (ii) are (B4.6), (B4.7)
at `x_i`, and `x_i ∈ D(x_i)` by (B4.1) — the number
`e_i := |N_Γ(D(x_i))| / |D(x_i)|` is `1` or `2` and `|N_Γ(D(x_i))| = e_i |D(x_i)|`; this number
divides `|Γ|` (Lagrange for the normalizer). By Step 4 the `i`-th term is
`(|Γ| / (e_i |D(x_i)|)) (|D(x_i)| − |Z|)`. ∎

---

### 3.3 Part C — 2×2 matrices over a field `F`

**Lemma C1 (commutant of a non-scalar matrix).** Let `g, x ∈ M₂(F)`, `NS(g)`, `x g = g x`. Then
there are `α, β ∈ F` with `x = α·1 + β·g`, i.e.
`x₀₀ = α + β g₀₀`, `x₀₁ = β g₀₁`, `x₁₀ = β g₁₀`, `x₁₁ = α + β g₁₁`.

*Proof.* Write `g = (a b; c d)`. The entries `(0,0), (0,1), (1,0)` of `xg = gx` are
 (E00) `x₀₀ a + x₀₁ c = a x₀₀ + b x₁₀`, i.e. `x₀₁ c = b x₁₀`;
 (E01) `x₀₀ b + x₀₁ d = a x₀₁ + b x₁₁`, i.e. `b (x₀₀ − x₁₁) = x₀₁ (a − d)`;
 (E10) `x₁₀ a + x₁₁ c = c x₀₀ + d x₁₀`, i.e. `c (x₀₀ − x₁₁) = x₁₀ (a − d)`.
* Case `b ≠ 0`. Put `β = x₀₁ / b`, `α = x₀₀ − β a`. Then `α + βa = x₀₀`; `β b = x₀₁`;
  `b·(β c) = x₀₁ c = b x₁₀` by (E00), so `β c = x₁₀`; and
  `b·(α + β d) = b x₀₀ − (a − d) x₀₁ = b x₁₁` by (E01), so `α + β d = x₁₁`.
* Case `b = 0`, `c ≠ 0`. Put `β = x₁₀ / c`, `α = x₀₀ − β a`. Then `β c = x₁₀`;
  `c·(β b) = b x₁₀ = c x₀₁` by (E00), so `β b = x₀₁`; and
  `c·(α + β d) = c x₀₀ − (a − d) x₁₀ = c x₁₁` by (E10). (`b = 0` is not used here.)
* Case `b = 0`, `c = 0`; then `a ≠ d` by `NS(g)`. (E01) gives `(a − d) x₀₁ = 0`, so `x₀₁ = 0`;
  (E10) gives `(a − d) x₁₀ = 0`, so `x₁₀ = 0`. Put `β = (x₀₀ − x₁₁)/(a − d)`, `α = x₀₀ − β a`;
  then `α + β d = x₀₀ − β (a − d) = x₁₁`, and `β b = 0 = x₀₁`, `β c = 0 = x₁₀`. ∎

**Lemma C2 (the commutant is commutative).** If `NS(g)`, `x g = g x`, `y g = g y`, then
`x y = y x`.

*Proof.* By C1, `x = α + β g` and `y = α′ + β′ g`; substituting the eight entry formulas, each
entry of `xy − yx` is identically `0` (a polynomial identity in `α, β, α′, β′, a, b, c, d`). ∎

**Lemma C3 (scalar ⇒ central).** If `A ∈ SL(2, F)` has `A₀₁ = 0`, `A₁₀ = 0`, `A₀₀ = A₁₁`, then
`A` lies in the center of `SL(2, F)`.

*Proof.* The matrix of `A` is `a·1`, which commutes with every matrix. ∎

**Lemma C4 (rigidity).** Assume `2 ≠ 0` in `F`. Let `A, B ∈ SL(2, F)` with `NS(A)`,
`(tr A)² ≠ 4`, `tr B = tr A`, `B A = A B`. Then `B = A` or `B = A⁻¹`.

*Proof.* Let `t = tr A`. By C1 (with `g = A`, `x = B`), `B = α + β A`. Then
`det B = (α + βa)(α + βd) − β² bc = α² + αβ t + β² (ad − bc)`, and with `det A = det B = 1`:
 (E1) `α² + αβ t + β² − 1 = 0`  (it is `(det B − 1) − β² (det A − 1)`);
and `tr B = 2α + β t`, so
 (E2) `2α + β t − t = 0`, i.e. `2α = t(1 − β)`.
Multiply (E1) by 4 and substitute:
`0 = (2α)² + 2(2α)βt + 4β² − 4 = t²(1−β)² + 2t²β(1−β) + 4β² − 4 = (1−β)(1+β)(t² − 4)`.
(As an identity without substitution:
`(1−β)(1+β)(t²−4) = 4·(E1) − (2α + t + βt)·(E2)`; verified symbolically.)
As `t² ≠ 4`: `β = 1` or `β = −1`.
* `β = 1`: (E2) gives `2α = 0`, so `α = 0` (as `2 ≠ 0`) and `B = A`.
* `β = −1`: (E2) gives `2α = 2t`, so `α = t` and `B = t·1 − A = (d −b; −c a)`, which is the
  adjugate of `A`, i.e. `A⁻¹` (as `det A = 1`). ∎

**Lemma C5 (parabolic elements have scalar `p`-th power).** Let `F` have characteristic `p > 0`
with `2 ≠ 0` in `F`. Let `A ∈ SL(2, F)` with `(tr A)² = 4`. Then the matrix `A^p` is scalar:
`(A^p)₀₁ = 0`, `(A^p)₁₀ = 0`, `(A^p)₀₀ = (A^p)₁₁`.

*Proof.* Let `M` be the matrix of `A`, `t = tr A`, `s = t/2`; then `t = 2s` and `s² = 1`.
Cayley–Hamilton in dimension 2 with `det = 1`: `M² = t M − 1 = 2s M − 1`
(entrywise: `a² + bc = (a + d)a − 1` because `ad − bc = 1`; `ab + bd = (a + d) b`;
`ca + dc = (a + d) c`; `cb + d² = (a + d) d − 1`).
Claim (**C5′**): for every matrix `M` and scalar `s` with `s² = 1` and `M² = 2sM − 1`, and all
`n ≥ 0`: `M^{n+1} = (s^n (n + 1))·M − (s^{n+1} n)·1`.
`n = 0`: `M = 1·M − 0`. Step: `M^{n+2} = M^{n+1} M = s^n (n+1) M² − s^{n+1} n M
 = s^n (n+1)(2s M − 1) − s^{n+1} n M = s^{n+1} (n + 2) M − s^n (n+1)·1`, and `s^n = s^{n+2}`
because `s² = 1`.
Take `n + 1 = p`: the coefficient of `M` is `s^{p−1}·p = 0` in `F`, so
`M^p = −(s^p (p−1))·1` is a scalar matrix. ∎

**Lemma C6 (a monic quadratic has at most two roots).** `F` finite. For `u, v ∈ F`,
`#{α ∈ F : α² + uα + v = 0} ≤ 2`.

*Proof.* If there is no root, fine. Otherwise fix a root `α₀`. For any root `α`,
`(α − α₀)(α − (−u − α₀)) = (α² + uα + v) − (α₀² + uα₀ + v) = 0`, so `α ∈ {α₀, −u − α₀}`. ∎

**Lemma C7 (size of a centralizer).** `F` finite with `q` elements. If `A ∈ SL(2, F)` and `NS(A)`,
then `|cen(A)| ≤ 2q`.

*Proof.* Let `t = tr A` and `Q = {(α, β) ∈ F² : α² + (tβ) α + (β² − 1) = 0}`.
For fixed `β` the fibre `{α : (α,β) ∈ Q}` has at most 2 elements (C6), so `|Q| ≤ 2q`.
If `X ∈ cen(A)` then `XA = AX`, so by C1 `X = α + βA`, and `det X = 1`, `det A = 1` give
`α² + αβ t + β² = 1` exactly as in C4, i.e. `(α,β) ∈ Q`. Choose such a pair `f(X)` for every
`X ∈ cen(A)`. `f` is injective because `X` is recovered from `f(X) = (α,β)` as `α + βA`. Hence
`|cen(A)| ≤ |Q| ≤ 2q`. ∎

(C7 does not need `(tr A)² ≠ 4`. Nothing about the sharpness of the bound `2q` is used or needs
to be proved: only the inequality of C7 enters the proof.)

---

### 3.4 Part D — consequences in the group `S = SL(2, F)`

**Lemma D1.** If `A ∈ S` is not in the center of `S`, then `NS(A)`.
*Proof.* Contrapositive of C3. ∎

**Lemma D2 (centralizers of non-central elements are commutative).** If `A ∉ Zc` and
`X, Y ∈ cen(A)`, then `XY = YX`.
*Proof.* D1 and C2 (in matrices: `XA = AX`, `YA = AY`). ∎

**Lemma D3 (commuting non-central elements have the same centralizer).** If `A, B ∉ Zc` and
`B ∈ cen(A)`, then `cen(B) = cen(A)`.
*Proof.* Note `A ∈ cen(B)`. Let `Y ∈ cen(B)`. Both `A` and `Y` lie in `cen(B)`, so by D2 at `B`:
`AY = YA`, i.e. `Y ∈ cen(A)`. Conversely let `Y ∈ cen(A)`. Both `B` and `Y` lie in `cen(A)`, so by
D2 at `A`: `BY = YB`, i.e. `Y ∈ cen(B)`. ∎

**Lemma D4 (conjugates inside the centralizer).** Assume `2 ≠ 0` in `F`. Let `A ∉ Zc` with
`(tr A)² ≠ 4`, and `n ∈ S` with `n A n⁻¹ ∈ cen(A)`. Then `n A n⁻¹ = A` or `n A n⁻¹ = A⁻¹`.
*Proof.* `B = n A n⁻¹` satisfies `tr B = tr(n⁻¹ (n A)) = tr A` (`tr(XY) = tr(YX)`) and `BA = AB`;
apply C4 (with D1). ∎

**Lemma D5.** If `F` is finite and `A ∉ Zc`, then `|cen(A)| ≤ 2|F|`.  *Proof.* D1, C7. ∎

**Lemma D6.** If `char F = p > 0`, `2 ≠ 0` in `F`, `A ∈ S` and `(tr A)² = 4`, then `A^p ∈ Zc`.
*Proof.* C5, then C3 applied to the element `A^p ∈ S`. ∎

---

### 3.5 Part E — the theorem

Fix a prime `p > 11` and `F = ZMod p` (a field with `p` elements, of characteristic `p`, in which
`2 ≠ 0` because `p ≠ 2`). `S = SL(2, p)`, `Zc = center S`, `G = PSL(2, p) = S/Zc`, `π : S → G`.
Suppose `H ≤ G` with `[G : H] = p`; put `h = |H|`, `z = |Zc|` (`z ≥ 1`), `K = π⁻¹(H)`.

**Lemma E1 (numerics).** Let `p > 11` be prime and `p·h = (p+1)p(p−1)/2` (natural-number
division). Write `p = 2m + 1`; then `m ≥ 6` and `h = 2m(m + 1)`. Consequently `h > 60`,
`4p < h`, and `gcd(p, h) = 1`.

*Proof.* `p` is odd. `(p+1)p(p−1) = (2m+2)(2m+1)(2m) = 2·((2m+1)·(2m(m+1)))`, so
`(p+1)p(p−1)/2 = p·2m(m+1)`, and cancelling `p > 0`: `h = 2m(m+1)`. With `m ≥ 6`:
`h ≥ 84 > 60` and `h − 4p = 2m² − 6m − 4 > 0`. If the prime `p` divided `h = (2·m)·(m+1)` it
would divide `2`, `m` or `m + 1`, each of which is positive and smaller than `p = 2m + 1`:
impossible. So `gcd(p,h) = 1`. ∎

(The hypothesis of E1 holds for `h = |H|`: `p·|H| = [G:H]·|H| = |G| = (p+1)p(p−1)/2` by
`card_PSL`.)

**Lemma E2 (the preimage).** `Zc ≤ K`; `[S : K] = p`; `|K| = h·z`.

*Proof.* `π(Zc) = 1 ∈ H`. The index of a preimage under a surjective homomorphism equals the
index of the subgroup. Then `p·|K| = [S:K]·|K| = |S| = |G|·|Zc| = (p·h)·z`, and cancelling `p`:
`|K| = h z`. ∎

**Lemma E3 (elements of `K` are not parabolic).** If `x ∈ S`, `π(x) ∈ H` and `x ∉ Zc`, then
`(tr x)² ≠ 4`.

*Proof.* Suppose `(tr x)² = 4`. By D6, `x^p ∈ Zc`, so `π(x)^p = π(x^p) = 1`. Also `π(x) ∈ H`, so
`π(x)^h = 1` (Lagrange in `H`). As `gcd(p, h) = 1` (E1), `π(x) = 1`, i.e. `x ∈ Zc`:
contradiction. ∎

**Lemma E4 (the hypotheses of B4).** Let `Γ = K` (as a group), `Z = Zc` (viewed inside `K`,
legitimate by E2), and `D(x) = K ∩ cen(x)` for `x ∈ K`. Then (B4.1)–(B4.7) hold.

*Proof.* Membership: for `x, y ∈ K`, `y ∈ D(x) ⟺ x y = y x`.
(B4.1) `x` commutes with itself. (B4.2) central elements commute with `x`.
(B4.3) if `x, y ∈ K ∖ Zc` and `y` commutes with `x`, then `cen(y) = cen(x)` by D3, so
`D(y) = D(x)`.
(B4.4) `Zc` is normal: if `k x k⁻¹ ∈ Zc` then `x = k⁻¹ (k x k⁻¹) (k⁻¹)⁻¹ ∈ Zc`.
(B4.5) if `x y = y x` then `(k x k⁻¹)(k y k⁻¹) = k x y k⁻¹ = k y x k⁻¹ = (k y k⁻¹)(k x k⁻¹)`.
(B4.6) let `x ∈ K ∖ Zc`, `n ∈ K`, `n x n⁻¹ ∈ cen(x)`. By E3, `(tr x)² ≠ 4`, and D4 gives
`n x n⁻¹ ∈ {x, x⁻¹}`.
(B4.7) `n x n⁻¹ = x` means `n x = x n`, i.e. `n ∈ cen(x)`; and `n ∈ K`. ∎

**Theorem E5.** For a prime `p > 11`, `PSL(2, p)` has no subgroup of index `p`.

*Proof.* Suppose `H` is one. By B4 and E4 there are a finite `ι`, `x_i ∈ K ∖ Zc`, `e_i ∈ {1, 2}`
with `e_i a_i ∣ |K|` and `Σ_i (|K| / (e_i a_i)) (a_i − z) = |K| − z`, where `a_i = |D(x_i)|`.
* `z ∣ a_i` (Lagrange, `Zc ≤ D(x_i)`); write `a_i = z c_i`.
* `c_i ≥ 2`: `a_i > 0` gives `c_i ≠ 0`; if `c_i = 1` then `|D(x_i)| = |Zc|`, and `Zc ≤ D(x_i)`
  forces `Zc = D(x_i)`, but `x_i ∈ D(x_i) ∖ Zc`.
* `c_i ≤ z c_i = a_i ≤ |cen(x_i)| ≤ 2p` (D5 with `|F| = p`), hence `2c_i ≤ 4p < h` (E1).
* `e_i z c_i ∣ h z` (E2), hence `e_i c_i ∣ h`; write `h = e_i c_i q_i`.
Then `|K| / (e_i a_i) = (q_i e_i c_i z)/(e_i z c_i) = q_i` and `a_i − z = z (c_i − 1)`, so the
equation reads `z · Σ_i q_i (c_i − 1) = z h − z = z (h − 1)`. Cancelling `z > 0` and using
`h ≥ 1`: `Σ_i q_i (c_i − 1) + 1 = h`. This contradicts Lemma A4 (with `s = ι`; `h > 60` by E1). ∎

---------------------------------------------------------------------------------------------------

## 4. LEAN ARCHITECTURE

Four new files, in dependency order. None modifies an existing file. Conventions follow
`GaloisOeuvres/RadicauxAux.lean` (a module doc-comment at the top that lists the main results, one
namespace for the auxiliary development, short doc-comments on the main declarations).

| # | path | module | imports | lines (code of §7 + header) |
|---|------|--------|---------|------------------------------|
| 1 | `GaloisOeuvres/LettreChevalierCloseAux1.lean` | `GaloisOeuvres.LettreChevalierCloseAux1` | `Mathlib` | 154 |
| 2 | `GaloisOeuvres/LettreChevalierCloseAux2.lean` | `GaloisOeuvres.LettreChevalierCloseAux2` | `Mathlib` | 264 |
| 3 | `GaloisOeuvres/LettreChevalierCloseAux3.lean` | `GaloisOeuvres.LettreChevalierCloseAux3` | `Mathlib` | 307 |
| 4 | `GaloisOeuvres/LettreChevalierClose.lean` | `GaloisOeuvres.LettreChevalierClose` | `GaloisOeuvres.LettreChevalier`, Aux1, Aux2, Aux3 | 236 |

Files 1–3 are independent of each other and of the rest of the repository (`import Mathlib` is what
`GaloisOeuvres/Basic.lean` does), so they can be written and compiled in any order. All three use
`namespace GaloisOeuvres.LettreChevalierClose`. File 4 uses that namespace for the assembly and then
`namespace GaloisOeuvres.LettreChevalier` for the final theorem.

To compile a file so that later files can import it (from the repository root, one at a time):
`python .lake-local/leanc.py GaloisOeuvres/LettreChevalierCloseAux1.lean --olean`, likewise Aux2,
Aux3, and finally `python .lake-local/leanc.py GaloisOeuvres/LettreChevalierClose.lean --olean`.
`.lake/build/lib/lean/GaloisOeuvres/LettreChevalier.olean` already exists (file 4 imports it).
A run takes about 2–4 minutes when a Lean slot is free (recorded: 181 s and 126 s for the whole
`T9.lean`, 187 s for files 1–3 standalone); it takes much longer only while queued for one of the
3 machine-wide slots or under memory pressure.

### 4.1 File 1 — `LettreChevalierCloseAux1.lean` (Part A, arithmetic)

Purpose: Lemma A4 and its special cases. Pure `ℕ`. No `open` needed.

```lean
theorem one_term {h c q e : ℕ} (h60 : 60 < h) (he : e = 1 ∨ e = 2) (hc : 2 ≤ c)
    (hcb : 2 * c < h) (hq : h = q * e * c) : q * (c - 1) + 1 ≠ h                       -- A1

theorem two_terms_aux {h c₁ q₁ c₂ q₂ : ℕ} (h60 : 60 < h) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hcb₂ : 2 * c₂ < h) (hq₁ : h = 1 * (q₁ * c₁)) (hq₂ : h = 2 * (q₂ * c₂)) :
    q₁ * c₁ - q₁ + (q₂ * c₂ - q₂) + 1 ≠ h                                               -- A2′

theorem two_terms {h c₁ q₁ e₁ c₂ q₂ e₂ : ℕ} (h60 : 60 < h)
    (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hcb₁ : 2 * c₁ < h) (hcb₂ : 2 * c₂ < h) (hq₁ : h = q₁ * e₁ * c₁) (hq₂ : h = q₂ * e₂ * c₂) :
    q₁ * (c₁ - 1) + q₂ * (c₂ - 1) + 1 ≠ h                                               -- A2

theorem three_terms_aux {h q₁ c₂ q₂ c₃ q₃ : ℕ} (h60 : 60 < h)
    (hc₂ : 2 ≤ c₂) (hc₃ : 2 ≤ c₃) (hcb₂ : 2 * c₂ < h) (hcb₃ : 2 * c₃ < h)
    (hq₁ : h = 2 * (q₁ * 2)) (hq₂ : h = 2 * (q₂ * c₂)) (hq₃ : h = 2 * (q₃ * c₃))
    (H : q₁ * 2 - q₁ + (q₂ * c₂ - q₂) + (q₃ * c₃ - q₃) + 1 = h) : False                 -- A3′

theorem three_terms {h c₁ q₁ e₁ c₂ q₂ e₂ c₃ q₃ e₃ : ℕ} (h60 : 60 < h)
    (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2) (he₃ : e₃ = 1 ∨ e₃ = 2)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hc₃ : 2 ≤ c₃)
    (hcb₁ : 2 * c₁ < h) (hcb₂ : 2 * c₂ < h) (hcb₃ : 2 * c₃ < h)
    (hq₁ : h = q₁ * e₁ * c₁) (hq₂ : h = q₂ * e₂ * c₂) (hq₃ : h = q₃ * e₃ * c₃) :
    q₁ * (c₁ - 1) + q₂ * (c₂ - 1) + q₃ * (c₃ - 1) + 1 ≠ h                               -- A3

theorem no_class_equation {ι : Type*} (s : Finset ι) (h : ℕ) (c q e : ι → ℕ)
    (h60 : 60 < h) (he : ∀ i ∈ s, e i = 1 ∨ e i = 2) (hc : ∀ i ∈ s, 2 ≤ c i)
    (hcb : ∀ i ∈ s, 2 * c i < h) (hq : ∀ i ∈ s, h = q i * e i * c i) :
    ∑ i ∈ s, q i * (c i - 1) + 1 ≠ h                                                    -- A4
```

How the proofs go in Lean (the technique matters more than the exact text):
* `omega` treats a product of two variables as an opaque atom. So first normalise:
  `rw [Nat.mul_sub_one]` turns `q * (c - 1)` into `q * c - q`; `hq.trans (by ring)` turns
  `h = q * e * c` into `h = e * (q * c)`, which after `rcases he with rfl | rfl` is
  `h = 1 * (q * c)` or `h = 2 * (q * c)` — linear in the atom `q * c`.
* `2q ≤ qc` is `Nat.mul_le_mul_left q hc : q * 2 ≤ q * c`; similarly `q * k ≤ q * c` from
  `k ≤ c`. After `rcases (by omega : c = 2 ∨ c = 3 ∨ 4 ≤ c) with rfl | rfl | h4` the atom `q * 3`
  is linear and `omega` uses it directly.
* `q ≥ 1` (from `h > 0`) is needed only in `two_terms`, case `e = (2,2)`.
* In `no_class_equation`: `Finset.card_nsmul_le_sum` gives `|s|·h ≤ Σ 4T_i`; then
  `interval_cases hs : s.card`, and `Finset.card_eq_zero`, `Finset.card_eq_one`,
  `Finset.card_eq_two`, `Finset.card_eq_three` produce the elements; `Finset.sum_singleton`,
  `Finset.sum_pair`, `Finset.sum_insert` unfold the sum.

### 4.2 File 2 — `LettreChevalierCloseAux2.lean` (Part B, abstract counting)

Purpose: Lemmas B1, B2, B3 and Theorem B4. Needs `open scoped Pointwise` (the action of
`ConjAct Γ` on `Subgroup Γ` is the scoped instance `Subgroup.pointwiseMulAction`) and
`universe u`.

```lean
theorem sum_eq_sum_orbits {G β : Type*} [Group G] [Finite G] [MulAction G β] [Fintype β]
    [Fintype (MulAction.orbitRel.Quotient G β)]
    (f : β → ℕ) (hf : ∀ (g : G) (b : β), f (g • b) = f b) :
    ∑ b, f b = ∑ ω : MulAction.orbitRel.Quotient G β,
      Nat.card G / Nat.card (MulAction.stabilizer G ω.out) * f ω.out                    -- B1

theorem sum_subgroups_eq {Γ : Type*} [Group Γ] [Finite Γ] [Fintype (Subgroup Γ)]
    [Fintype (MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ))]
    (w : Subgroup Γ → ℕ) (hw : ∀ (k : Γ) (C : Subgroup Γ), w (ConjAct.toConjAct k • C) = w C) :
    ∑ C, w C = ∑ ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ),
      Nat.card Γ / Nat.card (Subgroup.normalizer (ω.out : Set Γ)) * w ω.out             -- B2

theorem card_filter_mem {Γ : Type*} [Group Γ] [Fintype Γ] (C : Subgroup Γ)
    [DecidablePred (· ∈ C)] :
    (Finset.univ.filter fun x : Γ => x ∈ C).card = Nat.card C                          -- helper

theorem card_normalizer {Γ : Type*} [Group Γ] [Finite Γ] (D : Subgroup Γ) (x : Γ) (hx : x ∈ D)
    (hinv : ∀ n : Γ, n * x * n⁻¹ ∈ D → n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹)
    (hcen : ∀ n : Γ, n * x * n⁻¹ = x → n ∈ D) :
    Nat.card (Subgroup.normalizer (D : Set Γ)) = Nat.card D ∨
      Nat.card (Subgroup.normalizer (D : Set Γ)) = 2 * Nat.card D                       -- B3

theorem partition_count {Γ : Type u} [Group Γ] [Finite Γ] (Z : Subgroup Γ) (D : Γ → Subgroup Γ)
    (hmem : ∀ x, x ∉ Z → x ∈ D x)
    (hZ : ∀ x, x ∉ Z → Z ≤ D x)
    (heq : ∀ x y, x ∉ Z → y ∉ Z → y ∈ D x → D y = D x)
    (hZconj : ∀ k x, x ∉ Z → k * x * k⁻¹ ∉ Z)
    (hconj : ∀ k x y, y ∈ D x → k * y * k⁻¹ ∈ D (k * x * k⁻¹))
    (hinv : ∀ x n, x ∉ Z → n * x * n⁻¹ ∈ D x → n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹)
    (hcen : ∀ x n, x ∉ Z → n * x * n⁻¹ = x → n ∈ D x) :
    ∃ (ι : Type u) (_ : Fintype ι) (x : ι → Γ) (e : ι → ℕ),
      (∀ i, x i ∉ Z) ∧ (∀ i, e i = 1 ∨ e i = 2) ∧
      (∀ i, e i * Nat.card (D (x i)) ∣ Nat.card Γ) ∧
      ∑ i, Nat.card Γ / (e i * Nat.card (D (x i))) * (Nat.card (D (x i)) - Nat.card Z) =
        Nat.card Γ - Nat.card Z                                                         -- B4
```

Notes.
* In mathlib v4.36.0 the normalizer takes a **set**: `Subgroup.normalizer (S : Set G)`
  (`Mathlib/Algebra/Group/Subgroup/Defs.lean` line 658). Always write
  `Subgroup.normalizer (D : Set Γ)`.
* B1 is proved by `Finset.sum_fiberwise` over the map `b ↦ Quotient.mk'' b`, not through
  `MulAction.selfEquivSigmaOrbits` (whose unfolding is awkward); the fibre over `ω` is identified
  with `MulAction.orbit G ω.out` by
  `rw [← MulAction.orbitRel_apply, ← Quotient.eq'', Quotient.out_eq']`, and its cardinality is
  `MulAction.index_stabilizer` + `Subgroup.index_mul_card`.
* In B2 an instance `Finite (ConjAct Γ)` is **not** found automatically; provide it with
  `haveI : Finite (ConjAct Γ) := Finite.of_equiv Γ ConjAct.toConjAct.toEquiv` (a compile of the
  first draft failed exactly here).
* In B4: `classical`, then `Fintype` instances by `Fintype.ofFinite`; `ι` is the subtype
  `{ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ) // w ω.out ≠ 0}`, `x` comes from
  `choose`, and `e i := Nat.card (normalizer (D (x i))) / Nat.card (D (x i))`.

### 4.3 File 3 — `LettreChevalierCloseAux3.lean` (Parts C and D, matrices and `SL(2, F)`)

Purpose: Lemmas C1–C7 and D1–D6. Header: `open Matrix`, `open scoped MatrixGroups`,
`variable {F : Type*} [Field F]`. (If the file had to grow beyond ~400 lines, split it after
`card_quadratic_le_two`; nothing else would change.)

```lean
theorem commutant_entries (g x : Matrix (Fin 2) (Fin 2) F)
    (hg : g 0 1 ≠ 0 ∨ g 1 0 ≠ 0 ∨ g 0 0 ≠ g 1 1) (hx : x * g = g * x) :
    ∃ α β : F, x 0 0 = α + β * g 0 0 ∧ x 0 1 = β * g 0 1 ∧ x 1 0 = β * g 1 0 ∧
      x 1 1 = α + β * g 1 1                                                             -- C1

theorem commute_of_commutant (g x y : Matrix (Fin 2) (Fin 2) F)
    (hg : g 0 1 ≠ 0 ∨ g 1 0 ≠ 0 ∨ g 0 0 ≠ g 1 1) (hx : x * g = g * x) (hy : y * g = g * y) :
    x * y = y * x                                                                       -- C2

theorem mem_center_of_scalar (A : SL(2, F)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0)
    (h : A 0 0 = A 1 1) : A ∈ Subgroup.center SL(2, F)                                  -- C3

theorem eq_or_eq_inv_of_commute (h2 : (2 : F) ≠ 0) (A B : SL(2, F))
    (hA : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1)
    (hdisc : (A 0 0 + A 1 1) ^ 2 ≠ 4)
    (htr : B 0 0 + B 1 1 = A 0 0 + A 1 1) (hcomm : B * A = A * B) : B = A ∨ B = A⁻¹     -- C4

theorem matrix_pow_succ_of_sq (M : Matrix (Fin 2) (Fin 2) F) (s : F) (hs2 : s * s = 1)
    (hCH : M * M = (2 * s) • M - 1) (n : ℕ) :
    M ^ (n + 1) = (s ^ n * ((n : F) + 1)) • M -
      (s ^ (n + 1) * (n : F)) • (1 : Matrix (Fin 2) (Fin 2) F)                          -- C5′

theorem pow_char_scalar (p : ℕ) [CharP F p] (hp : 0 < p) (h2 : (2 : F) ≠ 0) (A : SL(2, F))
    (ht : (A 0 0 + A 1 1) ^ 2 = 4) :
    (A ^ p) 0 1 = 0 ∧ (A ^ p) 1 0 = 0 ∧ (A ^ p) 0 0 = (A ^ p) 1 1                       -- C5

theorem card_quadratic_le_two [Fintype F] [DecidableEq F] (u v : F) :
    (Finset.univ.filter fun α : F => α * α + u * α + v = 0).card ≤ 2                   -- C6

theorem card_centralizer_le [Fintype F] (A : SL(2, F))
    (hA : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1) :
    Nat.card (Subgroup.centralizer ({A} : Set SL(2, F))) ≤ 2 * Fintype.card F           -- C7

theorem trace_conj (n A : SL(2, F)) :
    (n * A * n⁻¹) 0 0 + (n * A * n⁻¹) 1 1 = A 0 0 + A 1 1

theorem nonscalar_of_not_mem_center (A : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F)) :
    A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1                                               -- D1

theorem commute_of_mem_centralizer (A : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F))
    {X Y : SL(2, F)} (hX : X ∈ Subgroup.centralizer ({A} : Set SL(2, F)))
    (hY : Y ∈ Subgroup.centralizer ({A} : Set SL(2, F))) : X * Y = Y * X                -- D2

theorem centralizer_eq_of_mem (A B : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F))
    (hB : B ∉ Subgroup.center SL(2, F)) (hBA : B ∈ Subgroup.centralizer ({A} : Set SL(2, F))) :
    Subgroup.centralizer ({B} : Set SL(2, F)) = Subgroup.centralizer ({A} : Set SL(2, F))  -- D3

theorem conj_eq_or_eq_inv (h2 : (2 : F) ≠ 0) (A n : SL(2, F))
    (hA : A ∉ Subgroup.center SL(2, F)) (hdisc : (A 0 0 + A 1 1) ^ 2 ≠ 4)
    (hn : n * A * n⁻¹ ∈ Subgroup.centralizer ({A} : Set SL(2, F))) :
    n * A * n⁻¹ = A ∨ n * A * n⁻¹ = A⁻¹                                                 -- D4

theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0

theorem card_centralizer_le_zmod (p : ℕ) [Fact p.Prime] (A : SL(2, ZMod p))
    (hA : A ∉ Subgroup.center SL(2, ZMod p)) :
    Nat.card (Subgroup.centralizer ({A} : Set SL(2, ZMod p))) ≤ 2 * p                   -- D5

theorem pow_char_mem_center (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (A : SL(2, ZMod p))
    (ht : (A 0 0 + A 1 1) ^ 2 = 4) : A ^ p ∈ Subgroup.center SL(2, ZMod p)              -- D6
```

Notes.
* For `A : SL(2, F)`, `A i j` is the `(i,j)` entry (function coercion) and
  `(A : Matrix (Fin 2) (Fin 2) F)` the matrix; `Matrix.SpecialLinearGroup.coe_mul`, `coe_inv`
  (`↑(A⁻¹) = adjugate A`), `coe_pow`, `det_coe`, `ext`.
* A singleton centralizer is unfolded with `Subgroup.mem_centralizer_iff :
  g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h`, instantiated at `A` and `Set.mem_singleton A`
  (so `X ∈ centralizer {A}` gives `A * X = X * A`). This is what the §7 code does. If `hmemD` or
  D2–D4 ever need repair, the preferred tool is
  `Subgroup.mem_centralizer_singleton_iff {g k : G} : k ∈ Subgroup.centralizer {g} ↔ Commute k g`
  (`Mathlib/GroupTheory/Subgroup/Centralizer.lean` line 53); `Commute k g` unfolds (`Commute`,
  `SemiconjBy`) to `k * g = g * k`.
* `linear_combination` certificates (all verified symbolically with a computer algebra system;
  `e00`, `e01`, `e10` are the three entry equations of `x * g = g * x` after
  `simp only [Matrix.mul_apply, Fin.sum_univ_two]`):
  - C1, case `g 0 1 ≠ 0`, with `hβ : x 0 1 / g 0 1 * g 0 1 = x 0 1` and after
    `apply mul_left_cancel₀ hb`: entry `(1,0)`: `linear_combination -e00 - g 1 0 * hβ`;
    entry `(1,1)`: `linear_combination -e01 + (g 0 0 - g 1 1) * hβ`.
  - C1, case `g 1 0 ≠ 0`, with `hβ : x 1 0 / g 1 0 * g 1 0 = x 1 0` and after
    `apply mul_left_cancel₀ hc`: entry `(0,1)`: `linear_combination e00 - g 0 1 * hβ`;
    entry `(1,1)`: `linear_combination e10 + (g 0 0 - g 1 1) * hβ`.
  - C1, third case: `(g 0 0 - g 1 1) * x 0 1 = 0` is `linear_combination -e01` (after `rw [hb]`),
    `(g 0 0 - g 1 1) * x 1 0 = 0` is `linear_combination e10` (after `rw [hc]`), and the last
    entry is `linear_combination hβ`.
  - C4 (`t = A 0 0 + A 1 1`): `E1` is `linear_combination hdB - β ^ 2 * hdA`; `E2` is
    `linear_combination htr`; `key : (1 - β) * ((1 + β) * (t ^ 2 - 4)) = 0` is
    `linear_combination 4 * E1 - (2 * α + t + β * t) * E2`.
  - C6: `(α - α₀) * (α - (-u - α₀)) = 0` is `linear_combination hα - hα₀`.

### 4.4 File 4 — `LettreChevalierClose.lean` (Part E, assembly)

Header: imports as in the table; `open Matrix`, `open scoped MatrixGroups`; a module doc-comment
in the style of the repository (title "Lettre à Auguste Chevalier: l'impossibilité pour `p > 11`",
a summary of §3.0, and the list of main declarations).

```lean
namespace GaloisOeuvres.LettreChevalierClose

theorem conj_comm {G : Type*} [Group G] (a b c : G) (h : b * c = c * b) :
    (a * b * a⁻¹) * (a * c * a⁻¹) = (a * c * a⁻¹) * (a * b * a⁻¹)

theorem numerics {p h : ℕ} (hp : p.Prime) (h11 : 11 < p)
    (hh : p * h = (p + 1) * p * (p - 1) / 2) : 60 < h ∧ 4 * p < h ∧ Nat.Coprime p h     -- E1

theorem trace_sq_ne_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hcop : Nat.Coprime p (Nat.card H)) (x : SL(2, ZMod p))
    (hx : (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p)) x) ∈ H)
    (hxc : x ∉ Subgroup.center SL(2, ZMod p)) : (x 0 0 + x 1 1) ^ 2 ≠ 4                 -- E3

theorem no_subgroup_index_p (p : ℕ) [Fact p.Prime] (hp : 11 < p)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) (hH : H.index = p) :
    False                                                                               -- E2, E4, E5

end GaloisOeuvres.LettreChevalierClose

namespace GaloisOeuvres.LettreChevalier

theorem abaissement_impossible : AbaissementImpossible

end GaloisOeuvres.LettreChevalier
```

Inside `no_subgroup_index_p` (see the full text in §7.4):
* `π := QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))`, `K := H.comap π`,
  `Z := (Subgroup.center SL(2, ZMod p)).subgroupOf K`,
  `D x := (Subgroup.centralizer ({(x : SL(2, ZMod p))} : Set SL(2, ZMod p))).subgroupOf K`
  (so `Γ = ↥K`, and `Z`, `D x` are subgroups of `↥K`).
* Two membership lemmas are proved first and used everywhere:
  `hmemZ : ∀ x : K, x ∈ Z ↔ (x : SL(2, ZMod p)) ∈ Subgroup.center SL(2, ZMod p)` and
  `hmemD : ∀ x y : K, y ∈ D x ↔ (x : SL(2, ZMod p)) * y = y * x`
  (both from `Subgroup.mem_subgroupOf`). Coercions `K → SL(2, ZMod p)` are moved with
  `push_cast` / `exact_mod_cast` (`Subgroup.coe_mul`, `Subgroup.coe_inv` are `norm_cast` lemmas).
* `|K| = |H|·|Zc|` from `Subgroup.index_comap_of_surjective`, `Subgroup.index_mul_card` (twice) and
  `Subgroup.card_eq_card_quotient_mul_card_subgroup`; `|Z| = |Zc|` from
  `Subgroup.subgroupOfEquivOfLe`.
* The seven hypotheses of `partition_count` are `hB1 … hB7`, proved as in Lemma E4.
* The arithmetic of Theorem E5 is done with `choose c hc` (from `|Z| ∣ |D (x i)|`) and
  `choose q hq` (from `e i * c i ∣ |H|`), and ends with
  `no_class_equation Finset.univ (Nat.card H) c q e …`.

---------------------------------------------------------------------------------------------------

## 5. MATHLIB / DEPENDENCY API

Every declaration below was confirmed by `rg` in `.lake/packages/mathlib/Mathlib` (file given) or
in the Lean core sources of the toolchain (`Init/…`); those that occur in §7 were moreover
exercised by the scratch compile described there.

Group theory
* `Mathlib/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean`:
  `abbrev Matrix.ProjectiveSpecialLinearGroup n R := SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)`.
* `Mathlib/GroupTheory/QuotientGroup/Defs.lean`: `QuotientGroup.mk'`, `QuotientGroup.mk'_surjective`
  (line 100), `QuotientGroup.eq_one_iff {N : Subgroup G} [N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N`
  (line 120).
* `Mathlib/GroupTheory/Index.lean`: `Subgroup.index_comap_of_surjective (H) {f : G' →* G}
  (hf : Function.Surjective f) : (H.comap f).index = H.index` (line 66);
  `Subgroup.index_mul_card (H) : H.index * Nat.card H = Nat.card G` (line 360);
  `MulAction.index_stabilizer : (stabilizer G x).index = (orbit G x).ncard` (line 949).
* `Mathlib/GroupTheory/Coset/Card.lean`: `Subgroup.card_eq_card_quotient_mul_card_subgroup (s) :
  Nat.card α = Nat.card (α ⧸ s) * Nat.card s` (line 56); `Subgroup.card_subgroup_dvd_card`
  (line 72); `Subgroup.card_dvd_of_le (hHK : H ≤ K) : Nat.card H ∣ Nat.card K` (line 89).
* `Mathlib/Algebra/Group/Subgroup/Finite.lean`: `Subgroup.eq_of_le_of_card_ge {H K} [Finite K]
  (hle : H ≤ K) (hcard : Nat.card K ≤ Nat.card H) : H = K` (line 108); `Subgroup.card_le_of_le`
  (line 152).
* `Mathlib/Algebra/Group/Subgroup/Map.lean`: `Subgroup.subgroupOf`, `Subgroup.mem_subgroupOf`
  (line 315), `Subgroup.subgroupOfEquivOfLe (h : H ≤ K) : H.subgroupOf K ≃* H` (line 290),
  `Subgroup.mem_comap`.
* `Mathlib/Algebra/Group/Subgroup/Defs.lean`: `Subgroup.normalizer (S : Set G)` (line 658),
  `Subgroup.mem_normalizer_iff : g ∈ normalizer H ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H` (line 684),
  `Subgroup.le_normalizer : H ≤ normalizer H` (line 696), `Subgroup.Normal.conj_mem`.
* `Mathlib/GroupTheory/Subgroup/Centralizer.lean`: `Subgroup.centralizer`,
  `Subgroup.mem_centralizer_iff` (line 36), `Subgroup.center_le_centralizer` (line 72).
  For repairs only (not used by §7): `Subgroup.mem_centralizer_singleton_iff {g k : G} :
  k ∈ Subgroup.centralizer {g} ↔ Commute k g` (line 53).
* For repairs only (fallback of `hbound`, §6.3): `Subgroup.subgroupOfEquivOfLe`
  (`Mathlib/Algebra/Group/Subgroup/Map.lean` line 290), `Subgroup.card_le_of_le`
  (`Mathlib/Algebra/Group/Subgroup/Finite.lean` line 152).
* `Mathlib/GroupTheory/Subgroup/Center.lean`: `Subgroup.mem_center_iff : z ∈ center G ↔ ∀ g, g * z = z * g`
  (line 57), instance `Subgroup.instNormalCenter` (line 131).
* `Mathlib/GroupTheory/GroupAction/ConjAct.lean`: `ConjAct`, `ConjAct.toConjAct`,
  `ConjAct.ofConjAct`, `ConjAct.toConjAct_smul : toConjAct g • h = g * h * g⁻¹` (line 132),
  `ConjAct.toConjAct_inv`, `ConjAct.toConjAct_ofConjAct`, instance
  `MulDistribMulAction (ConjAct G) G` (line 179).
* `Mathlib/Algebra/Group/Subgroup/Pointwise.lean`: `Subgroup.pointwiseMulAction` (scoped instance,
  line 433), `Subgroup.mem_pointwise_smul_iff_inv_smul_mem`,
  `Subgroup.conjAct_pointwise_smul_iff : ConjAct.toConjAct g • H = H ↔ g ∈ normalizer H` (line 573).
* `Mathlib/GroupTheory/GroupAction/Defs.lean`: `MulAction.orbitRel`, `MulAction.orbitRel.Quotient`,
  `MulAction.orbitRel_apply`; `Quotient.eq''`, `Quotient.out_eq'`.
* `Mathlib/GroupTheory/OrderOfElement.lean`: `pow_card_eq_one' : x ^ Nat.card G = 1` (line 1207).
* `Mathlib/Data/Int/GCD.lean`: `pow_eq_one_iff_of_coprime (hmn : m.Coprime n) :
  a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1` (line 277).

Matrices and `ZMod`
* `Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean`: `Matrix.SpecialLinearGroup.ext` (line 107),
  `coe_inv` (161), `coe_mul` (165), `det_coe` (173), `coe_pow` (180), the `Fintype` instance
  (line 132).
* `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`: `Matrix.det_fin_two` (line 834).
* `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`: `Matrix.adjugate_fin_two` (line 372).
* `Mathlib/LinearAlgebra/Matrix/Trace.lean`: `Matrix.trace_fin_two` (241), `Matrix.trace_mul_comm`
  (155).
* `Matrix.mul_apply`, `Matrix.one_apply`, `Fin.sum_univ_two`.
* `Mathlib/Data/ZMod/Basic.lean`: instance `ZMod.charP` (line 110), `ZMod.natCast_eq_zero_iff`
  (line 518); `Mathlib/Data/ZMod/Defs.lean`: `ZMod.card` (line 162); `CharP.cast_eq_zero`.
* `Mathlib/Data/Nat/Prime/Defs.lean`: `Nat.prime_dvd_prime_iff_eq` (line 187);
  `Mathlib/Data/Nat/Prime/Basic.lean`: `Nat.Prime.eq_two_or_odd` (line 40);
  `Nat.Prime.coprime_iff_not_dvd`.

Finite sets, sums, cardinals
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`: `Finset.sum_fiberwise` (additive version
  of `prod_fiberwise`, line 282), `Finset.card_eq_sum_card_fiberwise` (line 1017; its hypothesis is
  a `Set.MapsTo`), `Finset.sum_filter_of_ne` (from `prod_filter_of_ne`, line 319),
  `Finset.sum_subtype` (from `prod_subtype`, line 470), `Finset.sum_pair` (from `prod_pair`,
  line 86).
* `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`: `Finset.card_nsmul_le_sum` (line 302),
  `Finset.card_le_mul_card_image` (line 411).
* `Mathlib/Data/Finset/Card.lean`: `Finset.card_le_two` (115), `Finset.card_eq_two` (801),
  `Finset.card_eq_three` (807), `Finset.card_sdiff_of_subset` (598),
  `Finset.card_image_of_injective` (257), `Finset.card_le_card_of_injOn`.
* `Mathlib/Data/Set/Card.lean`: `Nat.card_coe_set_eq` (662), `Set.ncard_coe_finset` (704),
  `Set.ncard_le_ncard` (690), `Set.ncard_union_le` (1051), `Set.ncard_image_le` (836).
* `Mathlib/SetTheory/Cardinal/Finite.lean`: `Nat.card_eq_fintype_card` (47), `Nat.card_congr`,
  `Nat.card_le_card_of_injective` (96), `Nat.card_pos` (87).
* Lean core (`Init/Data/Nat/…`): `Nat.mul_sub_one`, `Nat.eq_of_mul_eq_mul_left`,
  `Nat.div_eq_of_eq_mul_left`, `Nat.mul_div_cancel_left`, `Nat.dvd_of_mul_dvd_mul_right`,
  `Nat.le_mul_of_pos_left`, `Nat.pos_of_mul_pos_left`, `Nat.coprime_mul_iff_right`, `Nat.le_of_dvd`.

---------------------------------------------------------------------------------------------------

## 6. RISKS

### 6.1 Is the target true as formalized?

Yes. Points checked:
* The statement is `∀ p, Fact p.Prime → 11 < p → ∀ H : Subgroup PSL(2, ZMod p), H.index ≠ p`.
  `PSL(2, ZMod p)` is finite, so `Subgroup.index` is the genuine index (the convention
  "`index = 0` for infinite index" plays no role). The mathematical statement (no subgroup of index
  `p` in `PSL(2, p)` for primes `p > 11`) is Galois's theorem; the bound `11` is sharp
  (`abaissement_5_7_11` in the repository), and the proof of §3 produces exactly the exceptional
  solutions `h = 12, 24, 60` (`p = 5, 7, 11`) and no other.
* The proof of §3 uses of `p` only: `p` prime, `p ≥ 13` (through `h > 60` and `4p < h`), and
  `|PSL(2, p)| = (p+1)p(p−1)/2` (`card_PSL`, proved in the repository for `p ≠ 2`).
* Independent numerical checks made while writing the blueprint (Python, outside Lean): all
  `linear_combination` certificates of §4.3 expand to `0`; a brute-force search for `h < 400` finds
  solutions of the class equation of Lemma A4 only at `h ∈ {12, 24, 60}`.

### 6.2 Mathematical risks

None known. Every step of §3 is elementary and has been written out; the only "non-obvious" facts
are C1 (commutant of a non-scalar 2×2 matrix) and C4 (rigidity), both proved by explicit
computation. The hypothesis `2 ≠ 0` (i.e. `p ≠ 2`) is used in C4 and C5 and is available.

### 6.3 Formalization risks

* **Status of the Lean text.** The complete text of §7 compiled without errors (scratch `T9.lean`,
  see the top of this file). Only linter warnings remain (`push_neg` deprecated in favour of
  `push Not`, `haveI` → `have` style hints, one unused `simp` argument); they are not errors and may
  be cleaned up but need not be.
* **Environment difference for files 1–3.** In the check, files 1–3 were elaborated in an
  environment that also contained `GaloisOeuvres.LettreChevalier` (they were in the same scratch
  file as file 4). As separate files they will import only `Mathlib`. This can only matter if
  `LettreChevalier` (or `Radicaux`, which it imports) declares a global instance or `simp` attribute
  that a tactic in files 1–3 silently used; none is known. If a `simp` in file 1–3 fails when
  compiled alone, change its `import Mathlib` to `import GaloisOeuvres.LettreChevalier` (harmless:
  file 4 imports it anyway) — this is the fallback, not the plan.
* **Earlier failures already repaired (do not reintroduce).** (i) `first | ring | …` is wrong,
  because `ring` "succeeds" by falling back to `ring_nf` without closing the goal; use `ring1`.
  (ii) `Finset.card_le_card_of_injOn` takes `Set.MapsTo f ↑s ↑t` and `Set.InjOn f ↑s`: membership
  hypotheses arrive as `x ∈ ↑s`, so rewrite with `Finset.mem_coe` before `Finset.mem_filter`.
  (iii) a function `i ↦ …` produced by `refine ⟨…, fun i => …, …⟩` appears in goals as a
  beta-redex, on which `rw` fails; restate the goal with `show` first. (iv)
  `Subgroup.Normal.conj_mem inferInstance` does not elaborate; write
  `(inferInstance : (Subgroup.center SL(2, ZMod p)).Normal).conj_mem`. (v) for injectivity of
  `y ↦ ⟨↑↑y, _⟩`, `congrArg Subtype.val hab` must be elaborated without an expected type
  (`have h := congrArg Subtype.val hab; exact h` after two `apply Subtype.ext`), otherwise
  higher-order unification picks the wrong `Subtype.val`.

* **Brittle spots and their fallbacks.** These compile now but are the most likely to break after
  a small edit or a mathlib bump:
  - §7.3 `matrix_pow_succ_of_sq`, the closing `push_cast; module`. Fallback: replace by
    `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, Matrix.smul_apply] <;> ring`
    (after the existing `push_cast`).
  - §7.3 `pow_char_scalar`, `hCH`: `simp [...] <;> first | ring1 | linear_combination -hdet`.
    Fallback: drop the `first` combinator and treat the four entries separately
    (`fin_cases i <;> fin_cases j` then four bullets), each closed by its own `ring1` or named
    `linear_combination` (the diagonal entries use `hdet`, the off-diagonal ones `ring1`).
  - §7.1 `no_class_equation`: `simpa using Finset.card_nsmul_le_sum …`. Fallback: `have :=
    Finset.card_nsmul_le_sum s (fun i => 4 * (q i * (c i - 1))) h hterm`, then
    `rw [smul_eq_mul] at this` and finish with `omega`/`linarith`.
  - §7.4 `hbound`, the hand-built injection with two `apply Subtype.ext`. Fallback: compare
    cardinalities through `Subgroup.subgroupOfEquivOfLe` (`Mathlib/Algebra/Group/Subgroup/Map.lean`
    line 290, `(h : H ≤ K) : H.subgroupOf K ≃* H`) and `Subgroup.card_le_of_le`
    (`Mathlib/Algebra/Group/Subgroup/Finite.lean` line 152, `{H K : Subgroup G} [Finite K]
    (h : H ≤ K) : Nat.card H ≤ Nat.card K`) instead of constructing the injection.
* **Optional lint cleanup (not applied).** `haveI := hp` in `abaissement_impossible` triggers a
  style hint, and `push_neg` (two places, §7.2 and §7.3) is deprecated in favour of `push Not`
  (present in this mathlib: `Mathlib/Tactic/Push.lean`). These are warnings, not errors. The
  §7 text is kept exactly as compiled; an implementer may replace the last two lines of
  `abaissement_impossible` by `exact @LettreChevalierClose.no_subgroup_index_p p hp h11 H hH` and
  `push_neg at h` by `push Not at h`, but must then recompile.
* **Compile time.** A single run of `leanc.py` takes about 2–4 minutes when a slot is free
  (recorded 181 s, 126 s, 187 s); much longer only while queued for a slot or under memory pressure.
  Implementers should compile each of the four files once, fix all reported errors in one pass,
  and never iterate tactic-by-tactic. Lean reports the errors of all declarations of a file in one
  run, so batch the fixes.
* **`omega` and products.** `omega` fails on goals where the same quantity appears as `q * e * c`
  in one place and `q * c` in another; always normalise to `e * (q * c)` first (as in §7.1).
* **Instances.** `Finite (ConjAct Γ)` is not inferred (see §4.2). `Fintype (Subgroup Γ)` and
  `Fintype (orbitRel.Quotient …)` must be provided by `Fintype.ofFinite` under `classical`.
  `Fintype.card_subtype` is avoided on purpose (instance mismatch between `Subtype.fintype` and
  the instance found for `↥Z`); `card_filter_mem` goes through `Set.ncard` instead.
* **`subgroupOf` coercions** in file 4 are the most fragile part of the assembly; the two lemmas
  `hmemZ`, `hmemD` isolate them. If a `push_cast` / `exact_mod_cast` step fails, state the
  coerced equality explicitly with `show` and prove it with `Subgroup.coe_mul`, `Subgroup.coe_inv`.
* **`choose` on divisibility.** If `choose c hc using ha_dvd` refuses a hypothesis of the form
  `∀ i, a ∣ b i`, restate it first as `∀ i, ∃ c, b i = a * c` (definitionally the same on `ℕ`).
* **Docs.** After the proof is wired in, the unit text in `LettreChevalier.lean` (lines 3133–3157),
  `README.md` line 29 and `docs/FAITHFULNESS.md` line 97 still say that the unit is open and
  "needs Dickson's classification"; they must be updated by whoever does the wiring, following the
  four wiring steps of §1 (`docs/UNITS.md` is regenerated by `scripts/unit_table.py`, never edited
  by hand; the new modules must be imported from `GaloisOeuvres.lean` for CI to build and audit
  them).
* **No forbidden constructs.** The texts of §7 use no `sorry`, `admit`, axiom, `native_decide`,
  `unsafe` or `implemented_by`; `Classical.choice` enters only through `classical` / `choose`
  (standard).

### 6.4 REJECTED CRITIQUES

None. All nine points of the two critiques were checked and accepted:
B3 notation (multiplier renamed `e`); the C7 sharpness remark (now marked as unused);
`Subgroup.mem_centralizer_singleton_iff` (confirmed at `Mathlib/GroupTheory/Subgroup/Centralizer.lean`
line 53, §4.3 corrected); CI wiring (confirmed in `.github/workflows/ci.yml` lines 22–23,
`scripts/unit_table.py`, `lakefile.toml`; §1 rewritten); compile time (corrected in §4 and §6.3);
brittle spots (fallbacks recorded in §6.3); lint cleanup (recorded as optional in §6.3 but not
applied to §7, so that §7 stays exactly the text that compiled).

---------------------------------------------------------------------------------------------------

## 7. APPENDIX — COMPLETE LEAN TEXT OF THE FOUR FILES

The four files below are produced from the compiled scratch source by
`.lake-local/scratch/psl-index/gen_blueprint.py` and were checked together as `T9.lean` (no
errors; axioms `propext`, `Classical.choice`, `Quot.sound` only). Copy each block verbatim into the
indicated path, then compile in order with `python .lake-local/leanc.py <file> --olean`
(Aux1, Aux2, Aux3 in any order, then `LettreChevalierClose.lean`).

### 7.1 `GaloisOeuvres/LettreChevalierCloseAux1.lean` (154 lines)

```lean
import Mathlib

/-!
# Lettre à Auguste Chevalier, `lettre.impossible_au_dela`: the arithmetic

Auxiliary file for `GaloisOeuvres.LettreChevalierClose`. It proves that the "class equation"
`∑ i, q i * (c i - 1) + 1 = h` has no solution when `h > 60`, `h = q i * e i * c i`,
`e i ∈ {1, 2}`, `2 ≤ c i` and `2 * c i < h` (`no_class_equation`). For `h = 12, 24, 60` there are
solutions (the subgroups of index `p` of `PSL(2, p)` for `p = 5, 7, 11`).
-/

namespace GaloisOeuvres.LettreChevalierClose

theorem one_term {h c q e : ℕ} (h60 : 60 < h) (he : e = 1 ∨ e = 2) (hc : 2 ≤ c)
    (hcb : 2 * c < h) (hq : h = q * e * c) : q * (c - 1) + 1 ≠ h := by
  rw [Nat.mul_sub_one]
  have a : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc
  have b : h = e * (q * c) := hq.trans (by ring)
  intro H
  rcases he with rfl | rfl
  · have hq1 : q = 1 := by omega
    subst hq1
    omega
  · omega

theorem two_terms_aux {h c₁ q₁ c₂ q₂ : ℕ} (h60 : 60 < h) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hcb₂ : 2 * c₂ < h) (hq₁ : h = 1 * (q₁ * c₁)) (hq₂ : h = 2 * (q₂ * c₂)) :
    q₁ * c₁ - q₁ + (q₂ * c₂ - q₂) + 1 ≠ h := by
  intro H
  have a₁ : q₁ * 2 ≤ q₁ * c₁ := Nat.mul_le_mul_left q₁ hc₁
  have a₂ : q₂ * 2 ≤ q₂ * c₂ := Nat.mul_le_mul_left q₂ hc₂
  rcases (by omega : c₁ = 2 ∨ c₁ = 3 ∨ 4 ≤ c₁) with rfl | rfl | h4
  · have h1 : q₂ = 1 := by omega
    subst h1
    omega
  · rcases (by omega : c₂ = 2 ∨ 3 ≤ c₂) with rfl | h3
    · omega
    · have := Nat.mul_le_mul_left q₂ h3
      omega
  · have := Nat.mul_le_mul_left q₁ h4
    omega

theorem two_terms {h c₁ q₁ e₁ c₂ q₂ e₂ : ℕ} (h60 : 60 < h)
    (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2) (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂)
    (hcb₁ : 2 * c₁ < h) (hcb₂ : 2 * c₂ < h) (hq₁ : h = q₁ * e₁ * c₁) (hq₂ : h = q₂ * e₂ * c₂) :
    q₁ * (c₁ - 1) + q₂ * (c₂ - 1) + 1 ≠ h := by
  rw [Nat.mul_sub_one, Nat.mul_sub_one]
  have a₁ : q₁ * 2 ≤ q₁ * c₁ := Nat.mul_le_mul_left q₁ hc₁
  have a₂ : q₂ * 2 ≤ q₂ * c₂ := Nat.mul_le_mul_left q₂ hc₂
  have b₁ : h = e₁ * (q₁ * c₁) := hq₁.trans (by ring)
  have b₂ : h = e₂ * (q₂ * c₂) := hq₂.trans (by ring)
  have p₁ : 0 < q₁ := by
    rcases Nat.eq_zero_or_pos q₁ with h0 | h0
    · rw [h0] at b₁; simp at b₁; omega
    · exact h0
  have p₂ : 0 < q₂ := by
    rcases Nat.eq_zero_or_pos q₂ with h0 | h0
    · rw [h0] at b₂; simp at b₂; omega
    · exact h0
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · omega
  · exact two_terms_aux h60 hc₁ hc₂ hcb₂ b₁ b₂
  · intro H
    exact two_terms_aux h60 hc₂ hc₁ hcb₁ b₂ b₁ (by omega)
  · omega

theorem three_terms_aux {h q₁ c₂ q₂ c₃ q₃ : ℕ} (h60 : 60 < h)
    (hc₂ : 2 ≤ c₂) (hc₃ : 2 ≤ c₃) (hcb₂ : 2 * c₂ < h) (hcb₃ : 2 * c₃ < h)
    (hq₁ : h = 2 * (q₁ * 2)) (hq₂ : h = 2 * (q₂ * c₂)) (hq₃ : h = 2 * (q₃ * c₃))
    (H : q₁ * 2 - q₁ + (q₂ * c₂ - q₂) + (q₃ * c₃ - q₃) + 1 = h) : False := by
  have a₂ : q₂ * 2 ≤ q₂ * c₂ := Nat.mul_le_mul_left q₂ hc₂
  have a₃ : q₃ * 2 ≤ q₃ * c₃ := Nat.mul_le_mul_left q₃ hc₃
  rcases (by omega : c₂ = 2 ∨ c₂ = 3 ∨ c₂ = 4 ∨ c₂ = 5 ∨ 6 ≤ c₂) with rfl | rfl | rfl | rfl | h2
  · have h1 : q₃ = 1 := by omega
    subst h1
    omega
  all_goals
    rcases (by omega : c₃ = 2 ∨ c₃ = 3 ∨ c₃ = 4 ∨ c₃ = 5 ∨ 6 ≤ c₃) with rfl | rfl | rfl | rfl | h3
    · have h1 : q₂ = 1 := by omega
      subst h1
      omega
    all_goals
      first
      | omega
      | (have := Nat.mul_le_mul_left q₃ h3; omega)
      | (have := Nat.mul_le_mul_left q₂ h2; omega)
      | (have := Nat.mul_le_mul_left q₂ h2; have := Nat.mul_le_mul_left q₃ h3; omega)

theorem three_terms {h c₁ q₁ e₁ c₂ q₂ e₂ c₃ q₃ e₃ : ℕ} (h60 : 60 < h)
    (he₁ : e₁ = 1 ∨ e₁ = 2) (he₂ : e₂ = 1 ∨ e₂ = 2) (he₃ : e₃ = 1 ∨ e₃ = 2)
    (hc₁ : 2 ≤ c₁) (hc₂ : 2 ≤ c₂) (hc₃ : 2 ≤ c₃)
    (hcb₁ : 2 * c₁ < h) (hcb₂ : 2 * c₂ < h) (hcb₃ : 2 * c₃ < h)
    (hq₁ : h = q₁ * e₁ * c₁) (hq₂ : h = q₂ * e₂ * c₂) (hq₃ : h = q₃ * e₃ * c₃) :
    q₁ * (c₁ - 1) + q₂ * (c₂ - 1) + q₃ * (c₃ - 1) + 1 ≠ h := by
  rw [Nat.mul_sub_one, Nat.mul_sub_one, Nat.mul_sub_one]
  have a₁ : q₁ * 2 ≤ q₁ * c₁ := Nat.mul_le_mul_left q₁ hc₁
  have a₂ : q₂ * 2 ≤ q₂ * c₂ := Nat.mul_le_mul_left q₂ hc₂
  have a₃ : q₃ * 2 ≤ q₃ * c₃ := Nat.mul_le_mul_left q₃ hc₃
  have b₁ : h = e₁ * (q₁ * c₁) := hq₁.trans (by ring)
  have b₂ : h = e₂ * (q₂ * c₂) := hq₂.trans (by ring)
  have b₃ : h = e₃ * (q₃ * c₃) := hq₃.trans (by ring)
  intro H
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> rcases he₃ with rfl | rfl <;>
    try omega
  rcases (by omega : c₁ = 2 ∨ c₂ = 2 ∨ c₃ = 2 ∨ (3 ≤ c₁ ∧ 3 ≤ c₂ ∧ 3 ≤ c₃)) with
    rfl | rfl | rfl | ⟨h1, h2, h3⟩
  · exact three_terms_aux h60 hc₂ hc₃ hcb₂ hcb₃ b₁ b₂ b₃ H
  · exact three_terms_aux h60 hc₁ hc₃ hcb₁ hcb₃ b₂ b₁ b₃ (by omega)
  · exact three_terms_aux h60 hc₁ hc₂ hcb₁ hcb₂ b₃ b₁ b₂ (by omega)
  · have := Nat.mul_le_mul_left q₁ h1
    have := Nat.mul_le_mul_left q₂ h2
    have := Nat.mul_le_mul_left q₃ h3
    omega

theorem no_class_equation {ι : Type*} (s : Finset ι) (h : ℕ) (c q e : ι → ℕ)
    (h60 : 60 < h) (he : ∀ i ∈ s, e i = 1 ∨ e i = 2) (hc : ∀ i ∈ s, 2 ≤ c i)
    (hcb : ∀ i ∈ s, 2 * c i < h) (hq : ∀ i ∈ s, h = q i * e i * c i) :
    ∑ i ∈ s, q i * (c i - 1) + 1 ≠ h := by
  classical
  intro H
  have hterm : ∀ i ∈ s, h ≤ 4 * (q i * (c i - 1)) := by
    intro i hi
    have h2 := hc i hi
    rw [Nat.mul_sub_one]
    have a : q i * 2 ≤ q i * c i := Nat.mul_le_mul_left _ h2
    have b : h = e i * (q i * c i) := (hq i hi).trans (by ring)
    rcases he i hi with h3 | h3 <;> rw [h3] at b <;> omega
  have hcard : s.card * h ≤ 4 * ∑ i ∈ s, q i * (c i - 1) := by
    rw [Finset.mul_sum]
    simpa using Finset.card_nsmul_le_sum s (fun i => 4 * (q i * (c i - 1))) h hterm
  have hlt : s.card < 4 := by
    by_contra hge
    have : 4 * h ≤ s.card * h := Nat.mul_le_mul_right h (by omega)
    omega
  interval_cases hs : s.card
  · rw [Finset.card_eq_zero] at hs
    subst hs
    simp at H
    omega
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    rw [Finset.sum_singleton] at H
    exact one_term h60 (he a (by simp)) (hc a (by simp)) (hcb a (by simp)) (hq a (by simp)) H
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
    rw [Finset.sum_pair hab] at H
    exact two_terms h60 (he a (by simp)) (he b (by simp)) (hc a (by simp)) (hc b (by simp))
      (hcb a (by simp)) (hcb b (by simp)) (hq a (by simp)) (hq b (by simp)) H
  · obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp hs
    rw [Finset.sum_insert (by simp [hab, had]), Finset.sum_pair hbd] at H
    exact three_terms h60 (he a (by simp)) (he b (by simp)) (he d (by simp))
      (hc a (by simp)) (hc b (by simp)) (hc d (by simp))
      (hcb a (by simp)) (hcb b (by simp)) (hcb d (by simp))
      (hq a (by simp)) (hq b (by simp)) (hq d (by simp)) (by omega)

end GaloisOeuvres.LettreChevalierClose
```

### 7.2 `GaloisOeuvres/LettreChevalierCloseAux2.lean` (264 lines)

```lean
import Mathlib

/-!
# Lettre à Auguste Chevalier, `lettre.impossible_au_dela`: a counting theorem for finite groups

Auxiliary file for `GaloisOeuvres.LettreChevalierClose`.

* `sum_eq_sum_orbits`: the class formula with a weight that is constant on orbits.
* `sum_subgroups_eq`: the same for the conjugation action on subgroups (stabilizer = normalizer).
* `card_normalizer`: a subgroup `D` containing an element `x` whose conjugates inside `D` are `x`
  and `x⁻¹` only, and which contains the centralizer of `x`, has index at most 2 in its normalizer.
* `partition_count`: if the complement of a subgroup `Z` of a finite group is partitioned by the
  subgroups `D x` (minus `Z`), compatibly with conjugation, then
  `|Γ| - |Z| = ∑ i, |Γ| / (e i * |D (x i)|) * (|D (x i)| - |Z|)` with `e i ∈ {1, 2}`.
-/

open scoped Pointwise

namespace GaloisOeuvres.LettreChevalierClose

universe u

/-- weighted class formula -/
theorem sum_eq_sum_orbits {G β : Type*} [Group G] [Finite G] [MulAction G β] [Fintype β]
    [Fintype (MulAction.orbitRel.Quotient G β)]
    (f : β → ℕ) (hf : ∀ (g : G) (b : β), f (g • b) = f b) :
    ∑ b, f b = ∑ ω : MulAction.orbitRel.Quotient G β,
      Nat.card G / Nat.card (MulAction.stabilizer G ω.out) * f ω.out := by
  classical
  have key : ∀ ω : MulAction.orbitRel.Quotient G β,
      ∑ b ∈ Finset.univ.filter
        (fun b : β => (Quotient.mk'' b : MulAction.orbitRel.Quotient G β) = ω), f b =
        Nat.card G / Nat.card (MulAction.stabilizer G ω.out) * f ω.out := by
    intro ω
    have hmem : ∀ b : β, (Quotient.mk'' b : MulAction.orbitRel.Quotient G β) = ω ↔
        b ∈ MulAction.orbit G ω.out := by
      intro b
      rw [← MulAction.orbitRel_apply, ← Quotient.eq'', Quotient.out_eq']
    have h1 : ∀ b ∈ Finset.univ.filter
        (fun b : β => (Quotient.mk'' b : MulAction.orbitRel.Quotient G β) = ω),
        f b = f ω.out := by
      intro b hb
      rw [Finset.mem_filter, hmem] at hb
      obtain ⟨g, rfl⟩ := hb.2
      exact hf g _
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]
    congr 1
    have h2 : (Finset.univ.filter
        (fun b : β => (Quotient.mk'' b : MulAction.orbitRel.Quotient G β) = ω)).card =
        (MulAction.orbit G ω.out).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext b
      simp [hmem]
    rw [h2, ← MulAction.index_stabilizer]
    have h3 := Subgroup.index_mul_card (MulAction.stabilizer G ω.out)
    exact (Nat.div_eq_of_eq_mul_left Nat.card_pos h3.symm).symm
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun b : β => (Quotient.mk'' b : MulAction.orbitRel.Quotient G β)) (f := f)]
  exact Finset.sum_congr rfl fun ω _ => key ω

/-- conjugation version -/
theorem sum_subgroups_eq {Γ : Type*} [Group Γ] [Finite Γ] [Fintype (Subgroup Γ)]
    [Fintype (MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ))]
    (w : Subgroup Γ → ℕ) (hw : ∀ (k : Γ) (C : Subgroup Γ), w (ConjAct.toConjAct k • C) = w C) :
    ∑ C, w C = ∑ ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ),
      Nat.card Γ / Nat.card (Subgroup.normalizer (ω.out : Set Γ)) * w ω.out := by
  haveI : Finite (ConjAct Γ) := Finite.of_equiv Γ ConjAct.toConjAct.toEquiv
  have h := sum_eq_sum_orbits (G := ConjAct Γ) w (fun g C => by
    simpa using hw (ConjAct.ofConjAct g) C)
  rw [h]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h1 : Nat.card (ConjAct Γ) = Nat.card Γ := rfl
  have h2 : Nat.card (MulAction.stabilizer (ConjAct Γ) ω.out) =
      Nat.card (Subgroup.normalizer (ω.out : Set Γ)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
    rw [MulAction.mem_stabilizer_iff, ← Subgroup.conjAct_pointwise_smul_iff]
    simp
  rw [h1, h2]

theorem card_filter_mem {Γ : Type*} [Group Γ] [Fintype Γ] (C : Subgroup Γ)
    [DecidablePred (· ∈ C)] :
    (Finset.univ.filter fun x : Γ => x ∈ C).card = Nat.card C := by
  rw [← Set.ncard_coe_finset]
  show _ = (C : Set Γ).ncard
  congr 1
  ext x
  simp

theorem card_normalizer {Γ : Type*} [Group Γ] [Finite Γ] (D : Subgroup Γ) (x : Γ) (hx : x ∈ D)
    (hinv : ∀ n : Γ, n * x * n⁻¹ ∈ D → n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹)
    (hcen : ∀ n : Γ, n * x * n⁻¹ = x → n ∈ D) :
    Nat.card (Subgroup.normalizer (D : Set Γ)) = Nat.card D ∨
      Nat.card (Subgroup.normalizer (D : Set Γ)) = 2 * Nat.card D := by
  set N := Subgroup.normalizer (D : Set Γ) with hN
  have hDN : D ≤ N := Subgroup.le_normalizer
  have hdvd : Nat.card D ∣ Nat.card N := Subgroup.card_dvd_of_le hDN
  have hkey : ∀ n ∈ N, n ∉ D → n * x * n⁻¹ = x⁻¹ := by
    intro n hn hnD
    have h1 : n * x * n⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
    rcases hinv n h1 with h | h
    · exact absurd (hcen n h) hnD
    · exact h
  have hle : Nat.card N ≤ 2 * Nat.card D := by
    by_cases hex : ∃ n₀ ∈ N, n₀ ∉ D
    · obtain ⟨n₀, hn₀, hn₀D⟩ := hex
      have hsub : (N : Set Γ) ⊆ (D : Set Γ) ∪ (fun d => n₀ * d) '' (D : Set Γ) := by
        intro n hn
        by_cases hnD : n ∈ D
        · exact Or.inl hnD
        · right
          refine ⟨n₀⁻¹ * n, ?_, by group⟩
          apply hcen
          have e1 := hkey n hn hnD
          have e0 := hkey n₀ hn₀ hn₀D
          have e2 : n₀⁻¹ * x⁻¹ * n₀ = x := by
            rw [← e0]; group
          calc n₀⁻¹ * n * x * (n₀⁻¹ * n)⁻¹ = n₀⁻¹ * (n * x * n⁻¹) * n₀ := by group
            _ = x := by rw [e1, e2]
      calc Nat.card N = (N : Set Γ).ncard := rfl
        _ ≤ ((D : Set Γ) ∪ (fun d => n₀ * d) '' (D : Set Γ)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (D : Set Γ).ncard + ((fun d => n₀ * d) '' (D : Set Γ)).ncard := Set.ncard_union_le _ _
        _ ≤ (D : Set Γ).ncard + (D : Set Γ).ncard :=
            Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
        _ = 2 * Nat.card D := by rw [two_mul]; rfl
    · push_neg at hex
      have h1 : N ≤ D := fun n hn => hex n hn
      have h2 := Subgroup.card_le_of_le h1
      omega
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hNpos : 0 < Nat.card N := Nat.card_pos
  rw [hm] at hle hNpos ⊢
  have hm2 : m = 1 ∨ m = 2 := by
    have h1 : 0 < m := Nat.pos_of_mul_pos_left hNpos
    have h2 : m ≤ 2 := by
      by_contra h3
      have : Nat.card D * 3 ≤ Nat.card D * m := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  rcases hm2 with rfl | rfl
  · left; ring
  · right; ring

theorem partition_count {Γ : Type u} [Group Γ] [Finite Γ] (Z : Subgroup Γ) (D : Γ → Subgroup Γ)
    (hmem : ∀ x, x ∉ Z → x ∈ D x)
    (hZ : ∀ x, x ∉ Z → Z ≤ D x)
    (heq : ∀ x y, x ∉ Z → y ∉ Z → y ∈ D x → D y = D x)
    (hZconj : ∀ k x, x ∉ Z → k * x * k⁻¹ ∉ Z)
    (hconj : ∀ k x y, y ∈ D x → k * y * k⁻¹ ∈ D (k * x * k⁻¹))
    (hinv : ∀ x n, x ∉ Z → n * x * n⁻¹ ∈ D x → n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹)
    (hcen : ∀ x n, x ∉ Z → n * x * n⁻¹ = x → n ∈ D x) :
    ∃ (ι : Type u) (_ : Fintype ι) (x : ι → Γ) (e : ι → ℕ),
      (∀ i, x i ∉ Z) ∧ (∀ i, e i = 1 ∨ e i = 2) ∧
      (∀ i, e i * Nat.card (D (x i)) ∣ Nat.card Γ) ∧
      ∑ i, Nat.card Γ / (e i * Nat.card (D (x i))) * (Nat.card (D (x i)) - Nat.card Z) =
        Nat.card Γ - Nat.card Z := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Fintype (Subgroup Γ) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ)) := Fintype.ofFinite _
  have hDconj : ∀ (k x : Γ), x ∉ Z → D (k * x * k⁻¹) = ConjAct.toConjAct k • D x := by
    intro k x hx
    ext y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv]
    constructor
    · intro hy
      have h1 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
      have h2 := hconj k⁻¹ (k * x * k⁻¹) y hy
      rw [h1, inv_inv] at h2
      exact h2
    · intro hy
      have h1 : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
      have h2 := hconj k x _ hy
      rwa [h1] at h2
  let w : Subgroup Γ → ℕ := fun C => (Finset.univ.filter fun x : Γ => x ∉ Z ∧ D x = C).card
  have hwle : ∀ (k : Γ) (C : Subgroup Γ), w C ≤ w (ConjAct.toConjAct k • C) := by
    intro k C
    refine Finset.card_le_card_of_injOn (fun x => k * x * k⁻¹) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hZconj k x hx.2.1, by rw [hDconj k x hx.2.1, hx.2.2]⟩
    · intro a _ b _ hab
      simpa using hab
  have hw : ∀ (k : Γ) (C : Subgroup Γ), w (ConjAct.toConjAct k • C) = w C := by
    intro k C
    refine le_antisymm ?_ (hwle k C)
    have := hwle k⁻¹ (ConjAct.toConjAct k • C)
    rwa [ConjAct.toConjAct_inv, inv_smul_smul] at this
  have htotal : ∑ C, w C = Nat.card Γ - Nat.card Z := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := D)
      (s := Finset.univ.filter fun x : Γ => x ∉ Z) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    have h2 : ∀ C, (Finset.filter (fun a => D a = C)
        (Finset.univ.filter fun x : Γ => x ∉ Z)).card = w C := by
      intro C
      simp only [w, Finset.filter_filter]
    simp only [h2] at h1
    rw [← h1, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      Finset.card_univ, card_filter_mem, Nat.card_eq_fintype_card (α := Γ)]
  have hwval : ∀ x₀ : Γ, x₀ ∉ Z → w (D x₀) = Nat.card (D x₀) - Nat.card Z := by
    intro x₀ hx₀
    have h1 : (Finset.univ.filter fun x : Γ => x ∉ Z ∧ D x = D x₀) =
        (Finset.univ.filter fun x : Γ => x ∈ D x₀) \ (Finset.univ.filter fun x : Γ => x ∈ Z) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxZ, hxD⟩
        exact ⟨hxD ▸ hmem x hxZ, hxZ⟩
      · rintro ⟨hxD, hxZ⟩
        exact ⟨hxZ, heq x₀ x hx₀ hxZ hxD⟩
    have h2 : (Finset.univ.filter fun x : Γ => x ∈ Z) ⊆ (Finset.univ.filter fun x : Γ => x ∈ D x₀) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hZ x₀ hx₀ hx.2⟩
    show (Finset.univ.filter fun x : Γ => x ∉ Z ∧ D x = D x₀).card = _
    rw [h1, Finset.card_sdiff_of_subset h2, card_filter_mem, card_filter_mem]
  have hnorm : ∀ x₀ : Γ, x₀ ∉ Z →
      Nat.card (Subgroup.normalizer (D x₀ : Set Γ)) = Nat.card (D x₀) ∨
      Nat.card (Subgroup.normalizer (D x₀ : Set Γ)) = 2 * Nat.card (D x₀) := fun x₀ hx₀ =>
    card_normalizer (D x₀) x₀ (hmem x₀ hx₀) (fun n => hinv x₀ n hx₀) (fun n => hcen x₀ n hx₀)
  have horb := sum_subgroups_eq w hw
  have hrep : ∀ ω : {ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ) // w ω.out ≠ 0},
      ∃ x : Γ, x ∉ Z ∧ D x = ω.1.out := by
    rintro ⟨ω, hω⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hω)
    rw [Finset.mem_filter] at hx
    exact ⟨x, hx.2⟩
  choose x hxZ hxD using hrep
  refine ⟨{ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ) // w ω.out ≠ 0},
    inferInstance, x,
    fun i => Nat.card (Subgroup.normalizer (D (x i) : Set Γ)) / Nat.card (D (x i)), hxZ, ?_, ?_, ?_⟩
  · intro i
    have hpos : 0 < Nat.card (D (x i)) := Nat.card_pos
    show Nat.card (Subgroup.normalizer (D (x i) : Set Γ)) / Nat.card (D (x i)) = 1 ∨
      Nat.card (Subgroup.normalizer (D (x i) : Set Γ)) / Nat.card (D (x i)) = 2
    rcases hnorm (x i) (hxZ i) with h | h
    · left; rw [h, Nat.div_self hpos]
    · right; rw [h, Nat.mul_div_cancel _ hpos]
  · intro i
    show Nat.card (Subgroup.normalizer (D (x i) : Set Γ)) / Nat.card (D (x i)) *
      Nat.card (D (x i)) ∣ Nat.card Γ
    rw [Nat.div_mul_cancel (Subgroup.card_dvd_of_le Subgroup.le_normalizer)]
    exact Subgroup.card_subgroup_dvd_card _
  · have h1 : (∑ ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ),
        Nat.card Γ / Nat.card (Subgroup.normalizer (ω.out : Set Γ)) * w ω.out) =
        ∑ i : {ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ) // w ω.out ≠ 0},
          Nat.card Γ / Nat.card (Subgroup.normalizer ((i.1.out : Subgroup Γ) : Set Γ)) *
            w i.1.out := by
      rw [← Finset.sum_filter_of_ne
        (p := fun ω : MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ) => w ω.out ≠ 0)
        (fun ω _ h => right_ne_zero_of_mul h)]
      exact Finset.sum_subtype _ (by simp) _
    rw [← htotal, horb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    show Nat.card Γ / (Nat.card (Subgroup.normalizer (D (x i) : Set Γ)) / Nat.card (D (x i)) *
      Nat.card (D (x i))) * (Nat.card (D (x i)) - Nat.card Z) = _
    rw [Nat.div_mul_cancel (Subgroup.card_dvd_of_le Subgroup.le_normalizer), ← hxD i,
      hwval (x i) (hxZ i)]

end GaloisOeuvres.LettreChevalierClose
```

### 7.3 `GaloisOeuvres/LettreChevalierCloseAux3.lean` (307 lines)

```lean
import Mathlib

/-!
# Lettre à Auguste Chevalier, `lettre.impossible_au_dela`: centralizers in `SL(2, F)`

Auxiliary file for `GaloisOeuvres.LettreChevalierClose`. Elementary facts on 2×2 matrices over a
field: the commutant of a non-scalar matrix `g` is `F + F g` (`commutant_entries`), hence
commutative; two commuting non-central elements of `SL(2, F)` have the same centralizer
(`centralizer_eq_of_mem`); a conjugate of `A` commuting with `A` is `A` or `A⁻¹` when
`(tr A)² ≠ 4` (`conj_eq_or_eq_inv`); a centralizer of a non-central element has at most `2 |F|`
elements (`card_centralizer_le`); and `A ^ p` is central when `(tr A)² = 4` in characteristic `p`
(`pow_char_mem_center`).
-/

open Matrix
open scoped MatrixGroups

namespace GaloisOeuvres.LettreChevalierClose

variable {F : Type*} [Field F]

theorem commutant_entries (g x : Matrix (Fin 2) (Fin 2) F)
    (hg : g 0 1 ≠ 0 ∨ g 1 0 ≠ 0 ∨ g 0 0 ≠ g 1 1) (hx : x * g = g * x) :
    ∃ α β : F, x 0 0 = α + β * g 0 0 ∧ x 0 1 = β * g 0 1 ∧ x 1 0 = β * g 1 0 ∧
      x 1 1 = α + β * g 1 1 := by
  have e00 := congrFun (congrFun hx 0) 0
  have e01 := congrFun (congrFun hx 0) 1
  have e10 := congrFun (congrFun hx 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases hb : g 0 1 = 0
  swap
  · have hβ : x 0 1 / g 0 1 * g 0 1 = x 0 1 := div_mul_cancel₀ _ hb
    refine ⟨x 0 0 - x 0 1 / g 0 1 * g 0 0, x 0 1 / g 0 1, by ring, hβ.symm, ?_, ?_⟩
    · apply mul_left_cancel₀ hb
      linear_combination -e00 - g 1 0 * hβ
    · apply mul_left_cancel₀ hb
      linear_combination -e01 + (g 0 0 - g 1 1) * hβ
  by_cases hc : g 1 0 = 0
  swap
  · have hβ : x 1 0 / g 1 0 * g 1 0 = x 1 0 := div_mul_cancel₀ _ hc
    refine ⟨x 0 0 - x 1 0 / g 1 0 * g 0 0, x 1 0 / g 1 0, by ring, ?_, hβ.symm, ?_⟩
    · apply mul_left_cancel₀ hc
      linear_combination e00 - g 0 1 * hβ
    · apply mul_left_cancel₀ hc
      linear_combination e10 + (g 0 0 - g 1 1) * hβ
  have had : g 0 0 - g 1 1 ≠ 0 := by
    rcases hg with h | h | h
    · exact absurd hb h
    · exact absurd hc h
    · exact sub_ne_zero.mpr h
  have h01 : x 0 1 = 0 := by
    have : (g 0 0 - g 1 1) * x 0 1 = 0 := by rw [hb] at e01; linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_left had
  have h10 : x 1 0 = 0 := by
    have : (g 0 0 - g 1 1) * x 1 0 = 0 := by rw [hc] at e10; linear_combination e10
    exact (mul_eq_zero.mp this).resolve_left had
  have hβ : (x 0 0 - x 1 1) / (g 0 0 - g 1 1) * (g 0 0 - g 1 1) = x 0 0 - x 1 1 :=
    div_mul_cancel₀ _ had
  refine ⟨x 0 0 - (x 0 0 - x 1 1) / (g 0 0 - g 1 1) * g 0 0, (x 0 0 - x 1 1) / (g 0 0 - g 1 1),
    by ring, by rw [h01, hb, mul_zero], by rw [h10, hc, mul_zero], ?_⟩
  linear_combination hβ

theorem commute_of_commutant (g x y : Matrix (Fin 2) (Fin 2) F)
    (hg : g 0 1 ≠ 0 ∨ g 1 0 ≠ 0 ∨ g 0 0 ≠ g 1 1) (hx : x * g = g * x) (hy : y * g = g * y) :
    x * y = y * x := by
  obtain ⟨α, β, h00, h01, h10, h11⟩ := commutant_entries g x hg hx
  obtain ⟨α', β', k00, k01, k10, k11⟩ := commutant_entries g y hg hy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11, k00, k01, k10, k11] <;> ring

theorem mem_center_of_scalar (A : SL(2, F)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0)
    (h : A 0 0 = A 1 1) : A ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h] <;>
    ring

theorem eq_or_eq_inv_of_commute (h2 : (2 : F) ≠ 0) (A B : SL(2, F))
    (hA : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1)
    (hdisc : (A 0 0 + A 1 1) ^ 2 ≠ 4)
    (htr : B 0 0 + B 1 1 = A 0 0 + A 1 1) (hcomm : B * A = A * B) : B = A ∨ B = A⁻¹ := by
  have hx : (B : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hcomm, Matrix.SpecialLinearGroup.coe_mul]
  obtain ⟨α, β, h00, h01, h10, h11⟩ := commutant_entries _ _ hA hx
  have hdA := A.det_coe
  have hdB := B.det_coe
  rw [Matrix.det_fin_two] at hdA hdB
  rw [h00, h01, h10, h11] at hdB
  rw [h00, h11] at htr
  have E1 : α ^ 2 + α * β * (A 0 0 + A 1 1) + β ^ 2 - 1 = 0 := by
    linear_combination hdB - β ^ 2 * hdA
  have E2 : 2 * α + β * (A 0 0 + A 1 1) - (A 0 0 + A 1 1) = 0 := by
    linear_combination htr
  have key : (1 - β) * ((1 + β) * ((A 0 0 + A 1 1) ^ 2 - 4)) = 0 := by
    linear_combination 4 * E1 - (2 * α + (A 0 0 + A 1 1) + β * (A 0 0 + A 1 1)) * E2
  rcases mul_eq_zero.mp key with hβ | hβ
  · left
    have hβ1 : β = 1 := by linear_combination -hβ
    have hα : α = 0 := by
      have : 2 * α = 0 := by rw [hβ1] at E2; linear_combination E2
      exact (mul_eq_zero.mp this).resolve_left h2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hβ1, hα]
  · right
    rcases mul_eq_zero.mp hβ with hβ' | hβ'
    swap
    · exact absurd (sub_eq_zero.mp hβ') hdisc
    have hβ1 : β = -1 := by linear_combination hβ'
    have hα : α = A 0 0 + A 1 1 := by
      have : 2 * (α - (A 0 0 + A 1 1)) = 0 := by rw [hβ1] at E2; linear_combination E2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hβ1, hα]

theorem matrix_pow_succ_of_sq (M : Matrix (Fin 2) (Fin 2) F) (s : F) (hs2 : s * s = 1)
    (hCH : M * M = (2 * s) • M - 1) (n : ℕ) :
    M ^ (n + 1) = (s ^ n * ((n : F) + 1)) • M -
      (s ^ (n + 1) * (n : F)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : s ^ (n + 1 + 1) = s ^ n := by rw [pow_succ, pow_succ, mul_assoc, hs2, mul_one]
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hCH, hpow]
    push_cast
    module

theorem pow_char_scalar (p : ℕ) [CharP F p] (hp : 0 < p) (h2 : (2 : F) ≠ 0) (A : SL(2, F))
    (ht : (A 0 0 + A 1 1) ^ 2 = 4) :
    (A ^ p) 0 1 = 0 ∧ (A ^ p) 1 0 = 0 ∧ (A ^ p) 0 0 = (A ^ p) 1 1 := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hts : A 0 0 + A 1 1 = 2 * ((A 0 0 + A 1 1) / 2) := by field_simp
  have hs2 : (A 0 0 + A 1 1) / 2 * ((A 0 0 + A 1 1) / 2) = 1 := by
    field_simp
    linear_combination ht
  have hCH : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      (2 * ((A 0 0 + A 1 1) / 2)) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
    rw [← hts]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
      first
      | ring1
      | linear_combination -hdet
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hp0 : ((m : F) + 1) = 0 := by
    have := CharP.cast_eq_zero F (m + 1)
    push_cast at this
    exact this
  have hMp := matrix_pow_succ_of_sq (A : Matrix (Fin 2) (Fin 2) F) _ hs2 hCH m
  rw [hp0, mul_zero, zero_smul, zero_sub] at hMp
  have e : ∀ i j, (A ^ (m + 1)) i j =
      (-((((A 0 0 + A 1 1) / 2) ^ (m + 1) * (m : F)) • (1 : Matrix (Fin 2) (Fin 2) F))) i j := by
    intro i j
    rw [← hMp, ← Matrix.SpecialLinearGroup.coe_pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; simp
  · rw [e]; simp
  · rw [e, e]; simp

theorem card_quadratic_le_two [Fintype F] [DecidableEq F] (u v : F) :
    (Finset.univ.filter fun α : F => α * α + u * α + v = 0).card ≤ 2 := by
  rcases (Finset.univ.filter fun α : F => α * α + u * α + v = 0).eq_empty_or_nonempty with
    h | ⟨α₀, h₀⟩
  · simp [h]
  · rw [Finset.mem_filter] at h₀
    refine le_trans (Finset.card_le_card ?_) (Finset.card_le_two (a := α₀) (b := -u - α₀))
    intro α hα
    rw [Finset.mem_filter] at hα
    have h1 : (α - α₀) * (α - (-u - α₀)) = 0 := by linear_combination hα.2 - h₀.2
    rcases mul_eq_zero.mp h1 with h | h
    · simp [sub_eq_zero.mp h]
    · simp [sub_eq_zero.mp h]

theorem card_centralizer_le [Fintype F] (A : SL(2, F))
    (hA : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1) :
    Nat.card (Subgroup.centralizer ({A} : Set SL(2, F))) ≤ 2 * Fintype.card F := by
  classical
  let Q : Finset (F × F) := Finset.univ.filter fun q =>
    q.1 * q.1 + ((A 0 0 + A 1 1) * q.2) * q.1 + (q.2 * q.2 - 1) = 0
  have hQ : Q.card ≤ 2 * Fintype.card F := by
    refine le_trans (Finset.card_le_mul_card_image (f := Prod.snd) Q 2 (fun β _ => ?_))
      (Nat.mul_le_mul_left 2 (Finset.card_le_univ _))
    refine le_trans (Finset.card_le_card_of_injOn Prod.fst ?_ ?_)
      (card_quadratic_le_two ((A 0 0 + A 1 1) * β) (β * β - 1))
    · intro q hq
      have hq' : q ∈ Q ∧ q.2 = β := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      have hq1 : q.1 * q.1 + ((A 0 0 + A 1 1) * q.2) * q.1 + (q.2 * q.2 - 1) = 0 :=
        (Finset.mem_filter.mp hq'.1).2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hq'.2]
      exact hq1
    · intro q hq q' hq' h
      have h1 : q ∈ Q ∧ q.2 = β := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      have h2 : q' ∈ Q ∧ q'.2 = β := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      exact Prod.ext h (h1.2.trans h2.2.symm)
  have hdA := A.det_coe
  rw [Matrix.det_fin_two] at hdA
  have hex : ∀ x : Subgroup.centralizer ({A} : Set SL(2, F)), ∃ q : F × F, q ∈ Q ∧
      (x : SL(2, F)) 0 0 = q.1 + q.2 * A 0 0 ∧ (x : SL(2, F)) 0 1 = q.2 * A 0 1 ∧
      (x : SL(2, F)) 1 0 = q.2 * A 1 0 ∧ (x : SL(2, F)) 1 1 = q.1 + q.2 * A 1 1 := by
    intro x
    have hx := Subgroup.mem_centralizer_iff.mp x.2 A rfl
    have hx' : ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) * ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hx]
    obtain ⟨α, β, h00, h01, h10, h11⟩ := commutant_entries _ _ hA hx'
    refine ⟨(α, β), ?_, h00, h01, h10, h11⟩
    have hdx := (x : SL(2, F)).det_coe
    rw [Matrix.det_fin_two, h00, h01, h10, h11] at hdx
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination hdx - β ^ 2 * hdA
  choose f hfQ hf00 hf01 hf10 hf11 using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hf00, hf01, hf10, hf11, hxy]
  calc Nat.card (Subgroup.centralizer ({A} : Set SL(2, F)))
      = Fintype.card (Subgroup.centralizer ({A} : Set SL(2, F))) := Nat.card_eq_fintype_card
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Q.card := Finset.card_le_card (by
        intro q hq
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
        exact hfQ x)
    _ ≤ _ := hQ

theorem trace_conj (n A : SL(2, F)) :
    (n * A * n⁻¹) 0 0 + (n * A * n⁻¹) 1 1 = A 0 0 + A 1 1 := by
  have h := Matrix.trace_mul_comm ((n * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    ((n⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel_left, Matrix.trace_fin_two, Matrix.trace_fin_two] at h
  exact h

theorem nonscalar_of_not_mem_center (A : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F)) :
    A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1 := by
  by_contra h
  push_neg at h
  exact hA (mem_center_of_scalar A h.1 h.2.1 h.2.2)

theorem commute_of_mem_centralizer (A : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F))
    {X Y : SL(2, F)} (hX : X ∈ Subgroup.centralizer ({A} : Set SL(2, F)))
    (hY : Y ∈ Subgroup.centralizer ({A} : Set SL(2, F))) : X * Y = Y * X := by
  have hX' := Subgroup.mem_centralizer_iff.mp hX A (Set.mem_singleton A)
  have hY' := Subgroup.mem_centralizer_iff.mp hY A (Set.mem_singleton A)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  apply commute_of_commutant (A : Matrix (Fin 2) (Fin 2) F) _ _ (nonscalar_of_not_mem_center A hA)
  · rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hX']
  · rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hY']

theorem centralizer_eq_of_mem (A B : SL(2, F)) (hA : A ∉ Subgroup.center SL(2, F))
    (hB : B ∉ Subgroup.center SL(2, F)) (hBA : B ∈ Subgroup.centralizer ({A} : Set SL(2, F))) :
    Subgroup.centralizer ({B} : Set SL(2, F)) = Subgroup.centralizer ({A} : Set SL(2, F)) := by
  have hAB : A ∈ Subgroup.centralizer ({B} : Set SL(2, F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hBA A (Set.mem_singleton A)).symm
  ext Y
  constructor
  · intro hY
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact commute_of_mem_centralizer B hB hAB hY
  · intro hY
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact commute_of_mem_centralizer A hA hBA hY

theorem conj_eq_or_eq_inv (h2 : (2 : F) ≠ 0) (A n : SL(2, F))
    (hA : A ∉ Subgroup.center SL(2, F)) (hdisc : (A 0 0 + A 1 1) ^ 2 ≠ 4)
    (hn : n * A * n⁻¹ ∈ Subgroup.centralizer ({A} : Set SL(2, F))) :
    n * A * n⁻¹ = A ∨ n * A * n⁻¹ = A⁻¹ :=
  eq_or_eq_inv_of_commute h2 A (n * A * n⁻¹) (nonscalar_of_not_mem_center A hA) hdisc
    (trace_conj n A) (Subgroup.mem_centralizer_iff.mp hn A (Set.mem_singleton A)).symm

theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem card_centralizer_le_zmod (p : ℕ) [Fact p.Prime] (A : SL(2, ZMod p))
    (hA : A ∉ Subgroup.center SL(2, ZMod p)) :
    Nat.card (Subgroup.centralizer ({A} : Set SL(2, ZMod p))) ≤ 2 * p := by
  have := card_centralizer_le A (nonscalar_of_not_mem_center A hA)
  rwa [ZMod.card] at this

theorem pow_char_mem_center (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (A : SL(2, ZMod p))
    (ht : (A 0 0 + A 1 1) ^ 2 = 4) : A ^ p ∈ Subgroup.center SL(2, ZMod p) := by
  obtain ⟨h1, h2, h3⟩ := pow_char_scalar p (Fact.out : p.Prime).pos (two_ne_zero_zmod p hp2) A ht
  exact mem_center_of_scalar _ h1 h2 h3

end GaloisOeuvres.LettreChevalierClose
```

### 7.4 `GaloisOeuvres/LettreChevalierClose.lean` (236 lines)

```lean
import GaloisOeuvres.LettreChevalier
import GaloisOeuvres.LettreChevalierCloseAux1
import GaloisOeuvres.LettreChevalierCloseAux2
import GaloisOeuvres.LettreChevalierCloseAux3

/-!
# Lettre à Auguste Chevalier: l'impossibilité pour `p > 11`

Proof of the unit `lettre.impossible_au_dela` of `GaloisOeuvres.LettreChevalier`: for a prime
`p > 11`, `PSL(2, p)` has no subgroup of index `p` (`abaissement_impossible`).

The proof does not use Dickson's classification. Let `H` be a subgroup of index `p` and `K` its
preimage in `SL(2, p)`. The order of `H` is prime to `p`, so no non-central element of `K` has
trace `±2`. The centralizers of the non-central elements of `K` partition `K` minus the center, and
each of them has index at most 2 in its normalizer in `K`; counting the elements of `K` over the
conjugacy classes of these subgroups gives an equation in natural numbers
(`partition_count`), which has no solution when `|H| > 60` (`no_class_equation`).
-/

open Matrix
open scoped MatrixGroups

namespace GaloisOeuvres.LettreChevalierClose

theorem conj_comm {G : Type*} [Group G] (a b c : G) (h : b * c = c * b) :
    (a * b * a⁻¹) * (a * c * a⁻¹) = (a * c * a⁻¹) * (a * b * a⁻¹) := by
  have e1 : (a * b * a⁻¹) * (a * c * a⁻¹) = a * (b * c) * a⁻¹ := by group
  have e2 : (a * c * a⁻¹) * (a * b * a⁻¹) = a * (c * b) * a⁻¹ := by group
  rw [e1, e2, h]

theorem numerics {p h : ℕ} (hp : p.Prime) (h11 : 11 < p)
    (hh : p * h = (p + 1) * p * (p - 1) / 2) : 60 < h ∧ 4 * p < h ∧ Nat.Coprime p h := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · omega
    · exact h2
  obtain ⟨m, rfl⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have e1 : (2 * m + 1 + 1) * (2 * m + 1) * (2 * m + 1 - 1) / 2 =
      (2 * m + 1) * (2 * m * (m + 1)) := by
    have e2 : (2 * m + 1 + 1) * (2 * m + 1) * (2 * m + 1 - 1) =
        2 * ((2 * m + 1) * (2 * m * (m + 1))) := by
      rw [Nat.add_sub_cancel]; ring
    rw [e2, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [e1] at hh
  have hh' : h = 2 * m * (m + 1) := Nat.eq_of_mul_eq_mul_left hp.pos hh
  have hm : 6 ≤ m := by omega
  have hmm : 6 * m ≤ m * m := Nat.mul_le_mul_right m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [hh']; nlinarith
  · rw [hh']; nlinarith
  · rw [hh', Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    all_goals
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega

theorem trace_sq_ne_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hcop : Nat.Coprime p (Nat.card H)) (x : SL(2, ZMod p))
    (hx : (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p)) x) ∈ H)
    (hxc : x ∉ Subgroup.center SL(2, ZMod p)) : (x 0 0 + x 1 1) ^ 2 ≠ 4 := by
  intro ht
  apply hxc
  have h1 : (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p)) x) ^ p = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_char_mem_center p hp2 x ht)
  have h2 : (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p)) x) ^ Nat.card H = 1 := by
    have h3 := pow_card_eq_one' (G := H) (x := ⟨_, hx⟩)
    exact congrArg Subtype.val h3
  have h3 := (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
  exact (QuotientGroup.eq_one_iff x).mp h3

theorem no_subgroup_index_p (p : ℕ) [Fact p.Prime] (hp : 11 < p)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) (hH : H.index = p) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp2
  let π : SL(2, ZMod p) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set K : Subgroup SL(2, ZMod p) := H.comap π with hK
  have hidx : K.index = p := by
    rw [hK, Subgroup.index_comap_of_surjective H hπ, hH]
  have hcK : Subgroup.center SL(2, ZMod p) ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_comap]
    have : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]; exact H.one_mem
  have hcardH : p * Nat.card H = (p + 1) * p * (p - 1) / 2 := by
    rw [← GaloisOeuvres.LettreChevalier.card_PSL p hp2, ← Subgroup.index_mul_card H, hH]
  have hcardK : Nat.card K = Nat.card H * Nat.card (Subgroup.center SL(2, ZMod p)) := by
    have h1 := Subgroup.index_mul_card K
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, ZMod p))
    have h3 := Subgroup.index_mul_card H
    rw [hidx] at h1
    rw [hH] at h3
    have h4 : p * Nat.card K = p * (Nat.card H * Nat.card (Subgroup.center SL(2, ZMod p))) := by
      rw [h1, h2, ← h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos h4
  obtain ⟨h60, h4p, hcop⟩ := numerics (Fact.out : p.Prime) hp hcardH
  let Z : Subgroup K := (Subgroup.center SL(2, ZMod p)).subgroupOf K
  let D : K → Subgroup K := fun x =>
    (Subgroup.centralizer ({(x : SL(2, ZMod p))} : Set SL(2, ZMod p))).subgroupOf K
  have hcardZ : Nat.card Z = Nat.card (Subgroup.center SL(2, ZMod p)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcK).toEquiv
  have hmemZ : ∀ x : K, x ∈ Z ↔ (x : SL(2, ZMod p)) ∈ Subgroup.center SL(2, ZMod p) :=
    fun x => Subgroup.mem_subgroupOf
  have hmemD' : ∀ x y : K, y ∈ D x ↔ (y : SL(2, ZMod p)) ∈
      Subgroup.centralizer ({(x : SL(2, ZMod p))} : Set SL(2, ZMod p)) := fun x y =>
    Subgroup.mem_subgroupOf
  have hmemD : ∀ x y : K, y ∈ D x ↔ (x : SL(2, ZMod p)) * y = y * x := fun x y => by
    rw [hmemD', Subgroup.mem_centralizer_iff]
    constructor
    · intro h; exact h _ (Set.mem_singleton _)
    · intro h z hz; rw [Set.mem_singleton_iff.mp hz]; exact h
  have hB1 : ∀ x : K, x ∉ Z → x ∈ D x := fun x _ => (hmemD x x).mpr rfl
  have hB2 : ∀ x : K, x ∉ Z → Z ≤ D x := fun x _ y hy => by
    rw [hmemD]
    exact Subgroup.mem_center_iff.mp ((hmemZ y).mp hy) _
  have hB3 : ∀ x y : K, x ∉ Z → y ∉ Z → y ∈ D x → D y = D x := fun x y hx hy hyx => by
    rw [hmemZ] at hx hy
    rw [hmemD'] at hyx
    show (Subgroup.centralizer _).subgroupOf K = (Subgroup.centralizer _).subgroupOf K
    rw [centralizer_eq_of_mem _ _ hx hy hyx]
  have hB4 : ∀ k x : K, x ∉ Z → k * x * k⁻¹ ∉ Z := fun k x hx h => by
    rw [hmemZ] at hx h
    apply hx
    have e : ((k⁻¹ : K) : SL(2, ZMod p)) * ((k * x * k⁻¹ : K) : SL(2, ZMod p)) *
        ((k⁻¹ : K) : SL(2, ZMod p))⁻¹ = (x : SL(2, ZMod p)) := by
      push_cast
      group
    rw [← e]
    exact (inferInstance : (Subgroup.center SL(2, ZMod p)).Normal).conj_mem _ h _
  have hB5 : ∀ k x y : K, y ∈ D x → k * y * k⁻¹ ∈ D (k * x * k⁻¹) := fun k x y hy => by
    rw [hmemD] at hy ⊢
    have := conj_comm (k : SL(2, ZMod p)) x y hy
    exact_mod_cast this
  have hB6 : ∀ x n : K, x ∉ Z → n * x * n⁻¹ ∈ D x → n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹ :=
    fun x n hx hn => by
    rw [hmemZ] at hx
    rw [hmemD'] at hn
    have hn' : (n : SL(2, ZMod p)) * x * (n : SL(2, ZMod p))⁻¹ ∈
        Subgroup.centralizer ({(x : SL(2, ZMod p))} : Set SL(2, ZMod p)) := by
      exact_mod_cast hn
    have hd := trace_sq_ne_four p hp2 H hcop (x : SL(2, ZMod p)) x.2 hx
    rcases conj_eq_or_eq_inv h2 (x : SL(2, ZMod p)) (n : SL(2, ZMod p)) hx hd hn' with h | h
    · left
      apply Subtype.ext
      push_cast
      exact h
    · right
      apply Subtype.ext
      push_cast
      exact h
  have hB7 : ∀ x n : K, x ∉ Z → n * x * n⁻¹ = x → n ∈ D x := fun x n _ h => by
    rw [hmemD]
    exact_mod_cast (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨ι, _, x, e, hx, he, hdiv, hsum⟩ := partition_count Z D hB1 hB2 hB3 hB4 hB5 hB6 hB7
  have hbound : ∀ i, Nat.card (D (x i)) ≤ 2 * p := by
    intro i
    have h1 : ((x i : K) : SL(2, ZMod p)) ∉ Subgroup.center SL(2, ZMod p) := fun h =>
      hx i ((hmemZ _).mpr h)
    refine le_trans ?_ (card_centralizer_le_zmod p _ h1)
    exact Nat.card_le_card_of_injective
      (fun y : D (x i) => (⟨((y : K) : SL(2, ZMod p)), (hmemD' _ _).mp y.2⟩ :
        Subgroup.centralizer ({((x i : K) : SL(2, ZMod p))} : Set SL(2, ZMod p))))
      (fun a b hab => by
        apply Subtype.ext
        apply Subtype.ext
        have h := congrArg Subtype.val hab
        exact h)
  have hzpos : 0 < Nat.card Z := Nat.card_pos
  have hKz : Nat.card K = Nat.card H * Nat.card Z := by rw [hcardK, ← hcardZ]
  have ha_dvd : ∀ i, Nat.card Z ∣ Nat.card (D (x i)) := fun i =>
    Subgroup.card_dvd_of_le (hB2 (x i) (hx i))
  choose c hc using ha_dvd
  have hc2 : ∀ i, 2 ≤ c i := by
    intro i
    have hpos : 0 < Nat.card (D (x i)) := Nat.card_pos
    rw [hc i] at hpos
    have hc0 : c i ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hpos
      exact lt_irrefl _ hpos
    have hc1 : c i ≠ 1 := by
      intro h1
      have hcard : Nat.card (D (x i)) ≤ Nat.card Z := by rw [hc i, h1, mul_one]
      have h3 := Subgroup.eq_of_le_of_card_ge (hB2 (x i) (hx i)) hcard
      exact hx i (h3 ▸ hB1 (x i) (hx i))
    omega
  have hcle : ∀ i, c i ≤ 2 * p := by
    intro i
    have h1 := hbound i
    rw [hc i] at h1
    exact le_trans (Nat.le_mul_of_pos_left _ hzpos) h1
  have hei : ∀ i, 0 < e i := fun i => by rcases he i with h1 | h1 <;> omega
  have hecd : ∀ i, e i * c i ∣ Nat.card H := by
    intro i
    have h1 := hdiv i
    rw [hc i, hKz, show e i * (Nat.card Z * c i) = e i * c i * Nat.card Z by ring] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hzpos h1
  choose q hq using hecd
  have hq' : ∀ i, Nat.card H = q i * e i * c i := fun i => by rw [hq i]; ring
  have hterm : ∀ i, Nat.card K / (e i * Nat.card (D (x i))) *
      (Nat.card (D (x i)) - Nat.card Z) = Nat.card Z * (q i * (c i - 1)) := by
    intro i
    have hci : 0 < c i := by have := hc2 i; omega
    have hepos : 0 < e i * (Nat.card Z * c i) := Nat.mul_pos (hei i) (Nat.mul_pos hzpos hci)
    have e1 : Nat.card K / (e i * Nat.card (D (x i))) = q i := by
      rw [hc i, hKz]
      apply Nat.div_eq_of_eq_mul_left hepos
      rw [hq i]; ring
    rw [e1, hc i, ← Nat.mul_sub_one]
    ring
  have hS : Nat.card Z * ∑ i, q i * (c i - 1) = Nat.card Z * (Nat.card H - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_congr rfl (fun i _ => hterm i), hsum, hKz, Nat.mul_sub_one,
      Nat.mul_comm]
  have hfinal : ∑ i, q i * (c i - 1) + 1 = Nat.card H := by
    have h1 := Nat.eq_of_mul_eq_mul_left hzpos hS
    omega
  exact no_class_equation Finset.univ (Nat.card H) c q e h60 (fun i _ => he i) (fun i _ => hc2 i)
    (fun i _ => by have := hcle i; omega) (fun i _ => hq' i) hfinal

end GaloisOeuvres.LettreChevalierClose

namespace GaloisOeuvres.LettreChevalier

/-- **Galois's impossibility claim** (`lettre.impossible_au_dela`): for a prime `p > 11`, the
modular group `PSL(2, p)` has no subgroup of index `p`. -/
theorem abaissement_impossible : AbaissementImpossible := by
  intro p hp h11 H hH
  haveI := hp
  exact LettreChevalierClose.no_subgroup_index_p p h11 H hH

end GaloisOeuvres.LettreChevalier
```
