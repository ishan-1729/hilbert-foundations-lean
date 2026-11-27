# Notes for PR 6: periodic continued fractions

One section per PR of the stack, in order. For each: what is stated, how it is proved step by step, and why the names, assumptions and file were chosen.

## 6.1 `cf-of-den-pos-of-injective`: two small lemmas the rest needs

### What this PR contains
Two additions to existing files, nothing else. Take only these hunks (`git diff master -- Mathlib/Algebra/ContinuedFractions`).

### `GenContFract.of_den_pos : 0 < (of v).dens n`
*In words*: every denominator `Bₙ` of the convergents of the continued fraction of `v` is positive, whether or not the expansion has terminated.

*Proof, step by step*:
1. `zeroth_den_eq_one`: `B₀ = 1` (true for every `GenContFract`).
2. `of_den_mono`: `Bₙ ≤ Bₙ₊₁`. `monotone_nat_of_le_succ` turns this into `B₀ ≤ Bₙ`.
3. `0 < 1 = B₀ ≤ Bₙ`.

*Assumptions*: exactly the file's standing ones (`Field`, `LinearOrder`, `IsStrictOrderedRing`, `FloorRing`), the same as `of_den_mono`.

*Name and place*: follows `of_den_mono` (same `of_den_` prefix) and sits directly after it. The docstring copies the style of its neighbours ("Shows that ...").

*Likely questions*
- "Why not `1 ≤ (of v).dens n`?" The same proof gives it (drop the first step). Positivity is what the later PRs use. If the reviewer prefers, add `one_le_of_den` and derive `of_den_pos` from it; it is a two-line change.
- "Isn't this `succ_nth_fib_le_of_nth_den`?" That lemma needs a non-termination hypothesis (`n = 0 ∨ ¬TerminatedAt (n - 1)`); this one has none.
- "`((of v).contsAux (n + 1)).b` is used later, not `dens n`." They are definitionally equal (`dens n = (conts n).b = (contsAux (n + 1)).b`), and the later files use `of_den_pos` for both forms without rewriting.

### `GenContFract.of_injective`
*In words*: an element `v` is determined by its continued fraction.

*Proof, step by step*: suppose `of v = of w` and `v ≠ w`. Put `ε = |v - w| / 2 > 0`. `of_convergence_epsilon` gives `N`, `M` with `|v - cₙ| < ε` for `n ≥ N` and `|w - c'ₙ| < ε` for `n ≥ M`, where `cₙ`, `c'ₙ` are the convergents of `of v`, `of w`. Since `of v = of w`, `c'ₙ = cₙ`. At `n = max N M` the triangle inequality gives `|v - w| ≤ |v - cₙ| + |cₙ - w| < 2ε = |v - w|`, a contradiction (`linarith`).

*Assumptions*: the file's standing ones. No topology is needed (it uses the ε-form, not `of_convergence`). The Archimedean property comes from `FloorRing`.

*Place*: it must come after `of_convergence_epsilon`, which lives in this file.

*Likely questions*
- "Could this be proved without convergence, by induction on the stream?" Not directly: two values with the same infinite expansion are only shown equal by a limiting argument. The convergence lemma is the existing tool.
- "Why is it stated as `Function.Injective`?" So that `of_injective.eq_iff` and `of_injective h` are available; this is the usual mathlib form.
- "Split in two PRs?" Fine if asked: the two lemmas are independent.

### Before you open it
- `Mathlib.lean` is not touched by this PR.

## 6.2 `cf-complete-quotient`: the complete quotients `vₙ` of a continued fraction and their basic API

### Overview
The file introduces one definition and its API. It is the foundation for the periodicity PRs: periodicity of the expansion is equality of two complete quotients.

Notation used below: `vₙ = completeQuotient v n`, `Aₙ / Bₙ` the convergents of `of v`.

### The definition
`completeQuotient v n = (fun x ↦ (fract x)⁻¹)^[n] v`.
- Typeclasses `[DivisionRing K] [LinearOrder K] [FloorRing K]`: the ones of `GenContFract.of` and `IntFractPair.stream` in Computation/Basic.lean.
- If `vₙ` is an integer then `fract vₙ = 0`, `0⁻¹ = 0`, and all later values are `0`. This junk value is documented in the docstring; it is what makes the sequence total.
- Namespace `GenContFract`, like `GenContFract.of` and `IntFractPair`.
- `@[expose] public section`: the definition must unfold for the `rfl` proofs here and in the next files; Computation/Basic.lean and Approximations.lean use the same header.

### Lemmas, with proofs
- `completeQuotient_zero`: `rfl`.
- `completeQuotient_succ : vₙ₊₁ = (fract vₙ)⁻¹`: `Function.iterate_succ_apply'`.
- `completeQuotient_succ' : completeQuotient v (n + 1) = completeQuotient (fract v)⁻¹ n`: `rfl`, because `f^[n + 1] x` is by definition `f^[n] (f x)`.
- `completeQuotient_add : v_{m + n} = (vₙ)_m`: `Function.iterate_add_apply`. Note the order of indices (the docstring states it).
- `floor_add_inv_completeQuotient_succ : ⌊vₙ⌋ + (vₙ₊₁)⁻¹ = vₙ`: rewrite `vₙ₊₁`, `inv_inv`, `floor_add_fract`. True also after termination, since `0⁻¹⁻¹ = 0`.
- `of_completeQuotient_s : (of vₙ).s = (of v).s.drop n`: induction on `n` for all `v`. Step: `vₙ₊₁` is the `n`-th complete quotient of `(fract v)⁻¹`; the induction hypothesis gives the `n`-th tail of `(of (fract v)⁻¹).s`; mathlib's `of_s_tail` says that this sequence is `(of v).s.tail`; `Stream'.Seq.dropn_tail` finishes.
- `of_completeQuotient_s_get?`: previous lemma and `Stream'.Seq.drop_get?`.
- `of_completeQuotient_terminatedAt_iff`: `TerminatedAt n` means `s.get? n = none`; apply the previous lemma.
- `of_completeQuotient_terminates_iff`: one direction shifts the index by `m`; the other uses `terminated_stable` (terminated at `n` implies terminated at `m + n`).
- `of_terminatedAt_iff_fract_completeQuotient_eq_zero`: move to position `0` of the expansion of `vₙ`; mathlib's `of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none` and `IntFractPair.succ_nth_stream_eq_none_iff` say that this terminates iff the fractional part of the first stream entry is `0`; `simp` unfolds `stream_zero`.
- `get?_of_eq_some_of_not_terminatedAt`: again move to position `0` of `of vₙ`; `of_s_head : fract v ≠ 0 → (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩`.
- `IntFractPair.stream_eq_some_of_ne_none`: induction on `n`. If `stream v (n + 1) = some p`, `succ_nth_stream_eq_some_iff` gives `q` with `stream v n = some q`, `q.fr ≠ 0`, `p = IntFractPair.of q.fr⁻¹`. By induction `q = IntFractPair.of vₙ`, so `p = IntFractPair.of (fract vₙ)⁻¹ = IntFractPair.of vₙ₊₁`.
- `eq_completeQuotient_mul_contsAux_div` (needs `Field`): mathlib's `compExactValue_correctness_of_stream_eq_some` says `v = compExactValue (contsAux n) (contsAux (n + 1)) fr` when `stream v n = some ⟨_, fr⟩`. Here `fr = fract vₙ ≠ 0`, and `compExactValue` is then by definition `(fr⁻¹ * A + A') / (fr⁻¹ * B + B')` with `fr⁻¹ = vₙ₊₁`. The `simpa` only unfolds `compExactValue`, `nextConts`, `nextNum`, `nextDen`. Index convention: `contsAux (n + 1) = ⟨Aₙ, Bₙ⟩`, `contsAux n = ⟨Aₙ₋₁, Bₙ₋₁⟩`.
- `one_lt_completeQuotient_succ` (needs `IsStrictOrderedRing`): not terminated at `n` means `0 < fract vₙ < 1`, so its inverse is `> 1` (`one_lt_inv₀`).
- `one_lt_completeQuotient`: case `n = 0` is the hypothesis `1 < v`, case `n + 1` is the previous lemma.
- `completeQuotient_mul_contsAux_b_add_pos`: `vₙ₊₁ > 1 > 0`, `Bₙ > 0` (`of_den_pos`, PR 0), `Bₙ₋₁ ≥ 0` (`zero_le_of_contsAux_b`).

### Likely reviewer questions
- *Why not use `IntFractPair.stream`?* It is `Option`-valued, so every statement about two indices needs two existence hypotheses. `IntFractPair.stream_eq_some_of_ne_none` is the bridge.
- *Why is `Approximations` imported privately?* It is used only in proofs (`of_den_pos`, `zero_le_of_contsAux_b`); the statements need only `Computation.Translations`.
- *Relation to #45950 (Gauss map)?* That PR defines `x ↦ fract x⁻¹` on ℝ for ergodic theory. Here the map is `x ↦ (fract x)⁻¹`, on any floor division ring, and no map is named. `completeQuotient v (n + 1) = (gaussMap^[n] (fract v))⁻¹` can be added later.
- *Is `eq_completeQuotient_mul_contsAux_div` a duplicate?* It is the existing correctness lemma in readable form; say so in the description.
- *Why the name `get?_of_eq_some_of_not_terminatedAt`?* It mirrors mathlib's `get?_of_eq_some_of_succ_get?_intFractPair_stream`.

### Before you open it
- Mathlib.lean: add only `public import Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient` (after `Computation.Basic`). The branch already contains exactly this line.

## 6.3 `cf-periodic`: the definitions `IsEventuallyPeriodic` and `IsPurelyPeriodic`

### The two definitions
`g = [h; (a₀, b₀), (a₁, b₁), …]`, with `g.s` the sequence of pairs and `g.partDens` the sequence of the `bₙ`.

**`IsEventuallyPeriodic g`**: `g` does not terminate, and there are `N` and `p > 0` with `g.s.get? (n + p) = g.s.get? n` for all `n ≥ N`.
- Why the conjunct `¬g.Terminates`: after termination `g.s.get?` is constantly `none`, so the second condition holds for every terminating `g`. Without the conjunct every rational number would have an "eventually periodic" expansion and Euler's theorem would be false.

**`IsPurelyPeriodic g`**: there is `p` with `bₚ = h` and `g.s.get? (n + (p + 1)) = g.s.get? n` for all `n`.
- For a regular continued fraction `[c₀; c₁, c₂, …]` (`c₀ = h`, `cₙ₊₁ = bₙ`) this is `cₙ₊ₚ₊₁ = cₙ` for all `n ≥ 0`: the case `n = 0` is `bₚ = h`, the cases `n ≥ 1` are the condition on `s`.
- Why `p + 1` and not `p` with `0 < p`: the definition needs the index of the partial denominator that repeats the head, which is `period - 1`. Writing the period as `p + 1` avoids a truncated subtraction inside a definition. `of_isPurelyPeriodic_iff` gives the `0 < p` form.
- The head has no numerator, so the head is compared with `bₚ` only. For non-regular `g` the notion is therefore of little use; the docstring says it is meant for regular continued fractions.
- No `¬Terminates` conjunct: it follows (`IsPurelyPeriodic.not_terminates`).

Both are defined on `GenContFract α` with no assumption on `α`, because `GenContFract.of v` is a `GenContFract`, and `SimpContFract`/`ContFract` coerce to it.

### Lemmas, with proofs
- `IsEventuallyPeriodic.not_terminates`: first component.
- `IsPurelyPeriodic.not_terminates`: suppose `g` terminates at `n`. The periodicity hypothesis is literally `Function.Periodic g.s.get? (p + 1)`, so `Function.Periodic.nat_mul` gives `g.s.get? (p + n * (p + 1)) = g.s.get? p`. Since `p + n * (p + 1) ≥ n`, `terminated_stable` gives `g.s.get? (p + n * (p + 1)) = none`. Hence `g.s.get? p = none`, so `g.partDens.get? p = none` (`partDen_none_iff_s_none`), contradicting `= some g.h`.
- `IsPurelyPeriodic.isEventuallyPeriodic`: take `N = 0` and period `p + 1`.
- `of_isEventuallyPeriodic_iff_partDens` (`DivisionRing`): under non-termination, `(of v).s.get? n = some ⟨1, ⌊vₙ₊₁⌋⟩` for every `n` (`get?_of_eq_some_of_not_terminatedAt`), so two entries are equal iff their partial denominators are. One terminal `simp`.
- `of_isEventuallyPeriodic_iff` (`Field`, ordered): the non-termination conjunct is common (`and_congr_right`).
  - (⇒) Given `N`, `p`. Claim `v_{N+1+p} = v_{N+1}`. By `of_injective` it suffices that the two expansions agree. A `GenContFract` is a head and a sequence (`ext1`). Heads: the head of `of x` is `⌊x⌋`; `s.get? N = some ⟨1, ⌊v_{N+1}⌋⟩` and `s.get? (N + p) = some ⟨1, ⌊v_{N+p+1}⌋⟩`, and these are equal by periodicity at `n = N`. Sequences: the `n`-th entry of `of v_{N+1+p}` is entry `N + 1 + p + n` of `of v`, which by periodicity at `N + 1 + n ≥ N` is entry `N + 1 + n`, the `n`-th entry of `of v_{N+1}`.
  - The index shifts from `N` to `N + 1` because `s.get? n` stores `⌊vₙ₊₁⌋`: periodicity of `s` from `N` on controls the complete quotients from `N + 1` on.
  - (⇐) Given `v_{N+p} = v_N` and `n = N + k`: entry `N + k + p` of `of v` is entry `k` of `of v_{N+p} = of v_N`, which is entry `N + k` of `of v`.
- `of_isPurelyPeriodic_iff`:
  - (⇒) Non-termination by the lemma above. Claim `v_{p+1} = v`, by `of_injective`: heads agree because `bₚ = ⌊v_{p+1}⌋` and `bₚ = h = ⌊v⌋`; entry `n` of `of v_{p+1}` is entry `p + 1 + n` of `of v`, equal to entry `n`.
  - (⇐) Write the period as `p + 1`. `bₚ = ⌊v_{p+1}⌋ = ⌊v⌋ = h` and entry `n + (p + 1)` of `of v` is entry `n` of `of v_{p+1} = of v`.

### Likely reviewer questions
- *Why are the two definitions shaped differently?* See above; the docstrings explain it. If a reviewer insists on one shape, `IsPurelyPeriodic` can be stated with `0 < p` and `partDens.get? (p - 1)`; the proofs change little.
- *Why not state the results with `Function.periodicPts` / `Function.Periodic`?* `completeQuotient v p = v` is by definition `Function.IsPeriodicPt (fun x ↦ (fract x)⁻¹) p v`; statements with `completeQuotient` avoid a raw lambda in every statement, and the proofs do use the `Periodic`/`IsPeriodicPt` API (`Function.Periodic.nat_mul` here, `IsPeriodicPt.const_mul` in the Galois PR). Restating is a `rfl` if requested.
- *Why does a file under `Algebra/` import order topology?* Only privately, for `of_injective`, which is proved from `of_convergence_epsilon` in ApproximationCorollaries. The public import is only `Computation.CompleteQuotient`.
- *`by lia`?* It closes `N ≤ N + 1 + n`.
- *Why `Field` + `IsStrictOrderedRing` for the last two?* They are the assumptions of `of_injective`. `of_isEventuallyPeriodic_iff_partDens` needs only a division ring.

### Before you open it
- Mathlib.lean: add only `public import Mathlib.Algebra.ContinuedFractions.Periodic` (after `...ContinuedFractions.Euler`).

## 6.4 `cf-periodic-quadratic-irrational`: Euler's theorem: eventually periodic implies quadratic irrational

### Statement
**Euler's theorem**: if the continued fraction of `v` is eventually periodic, then the minimal polynomial of `v` over `ℚ` has degree `2`.

`(minpoly ℚ v).natDegree = 2` packs three facts: `v` is algebraic over `ℚ` (otherwise `minpoly ℚ v = 0`, degree `0`); `v` is a root of a rational polynomial of degree `2`; `v` is not rational (otherwise the degree is `1`). The module docstring explains this. `K` is any linear ordered floor field (ℝ is the main case); `Algebra ℚ K` exists because an ordered field has characteristic zero.

### Declarations and proofs
**`isIntegral_of_adjoin_simple_eq` (private)**: if `F⟮x⟯ = F⟮y⟯` and `x` is integral over `F`, so is `y`. Proof: `F⟮x⟯` is algebraic over `F` (`isAlgebraic_adjoin_simple`); `y` lies in `F⟮x⟯` (rewrite `mem_adjoin_simple_self F y` along the equality), so it is integral as an element of `F⟮x⟯`, and `IntermediateField.isIntegral_iff` transfers this to `L`.

**`adjoin_completeQuotient : F⟮vₙ⟯ = F⟮v⟯`**: induction on `n`. Step `F⟮vₙ₊₁⟯ = F⟮vₙ⟯` by two inclusions (`adjoin_simple_le_iff`): `vₙ₊₁ = (vₙ - ⌊vₙ⌋)⁻¹ ∈ F⟮vₙ⟯` (`fract x` is by definition `x - ⌊x⌋`; integers lie in every intermediate field); and `vₙ = ⌊vₙ⌋ + (vₙ₊₁)⁻¹ ∈ F⟮vₙ₊₁⟯` (`floor_add_inv_completeQuotient_succ`). No hypothesis on termination is needed: if `vₙ` is an integer both sides are `⊥`.

**`completeQuotient_mem_adjoin`**: immediate. It is used in the Galois PR to apply an algebra map `ℚ⟮v⟯ → K` to the complete quotients.

**`natDegree_minpoly_completeQuotient`**: if `v` is integral, `natDegree (minpoly F v) = finrank F F⟮v⟯` (`adjoin.finrank`), likewise for `vₙ` (integral by the private helper), and the two fields are equal. If `v` is not integral, neither is `vₙ`, and both minimal polynomials are `0`.

**`exists_natDegree_eq_two_and_aeval_eq_zero` (private)**: assume no termination and `vₙ₊₁ = v`. PR 1 gives `v = (v Aₙ + Aₙ₋₁) / (v Bₙ + Bₙ₋₁)` with positive denominator. `exists_gcf_pair_rat_eq_of_nth_contsAux` says the continuants are casts of rationals `a, b` and `a', b'`. Clearing the denominator: `b v² + (b' - a) v - a' = 0` (`linear_combination`). `b ≠ 0` since `Bₙ > 0` (`of_den_pos`). The polynomial is `C b * X ^ 2 + C (b' - a) * X + C (-a')`, of degree `2` by `natDegree_quadratic`.

**`natDegree_minpoly_eq_two_of_completeQuotient_eq` (private)**: with `q` from the previous lemma, `minpoly ℚ v ∣ q` gives degree `≤ 2`; `minpoly.two_le_natDegree_iff` gives degree `≥ 2` iff `v` is not in the range of `algebraMap ℚ K`; if `v = r` were rational, `terminates_iff_rat` would make the expansion terminate.

**Euler's theorem**: `of_isEventuallyPeriodic_iff` gives `v_{N+p} = v_N`. Put `u = v_N`. Its `p`-th complete quotient is `v_{p+N} = u` (`completeQuotient_add`), and `of u` does not terminate (`of_completeQuotient_terminates_iff`). So `minpoly ℚ u` has degree `2`, and `u` has the same degree as `v`.

### Likely reviewer questions
- *Why this formulation of 'quadratic irrational'?* It needs no new definition and is directly usable with `minpoly` API. The equivalence with `Irrational x ∧ ∃ q : ℚ[X], q.natDegree = 2 ∧ aeval x q = 0` over ℝ is a few lines (in scratch/lagrange/verify/Axioms.lean); offer it as a follow-up if wanted.
- *Why is the general helper private?* It belongs in `FieldTheory/IntermediateField/Adjoin/Basic.lean`; offer to move it there (as `IntermediateField.isIntegral_of_adjoin_simple_eq` or an iff). It was kept private to keep this PR to one new file.
- *Why a general `F` in the adjoin lemmas?* The proofs do not use `ℚ`; only the main theorem does.
- *File name?* `QuadraticIrrational.lean` holds the 'periodic implies quadratic irrational' half; `Euler.lean` would be confused with `Algebra/ContinuedFractions/Euler.lean` (Euler's continued fraction formula). Rename if the reviewer prefers.
- *Why a new directory?* Lagrange's and Galois' theorems (next PRs) go in the same directory; they are number theory, not general algebra of continued fractions.
- *Why `public section` without `@[expose]`?* The file has no definitions.

### Before you open it
- Mathlib.lean: add only `public import Mathlib.NumberTheory.ContinuedFractions.QuadraticIrrational` (after `...ClassNumber.FunctionField`; in the full stack it sorts after `Lagrange` and `PurelyPeriodic`).
- This file uses only declarations that are on master (`isAlgebraic_adjoin_simple`, `adjoin.finrank`).

## 6.5 `cf-lagrange`: Lagrange's theorem and the "if and only if"

### Statement
**Lagrange**: if `(minpoly ℚ v).natDegree = 2`, the continued fraction of `v` is eventually periodic. With PR 3 this gives the iff.

Notation: `vₙ` complete quotients, `f = A X² + B X + C` with integer coefficients, `discrim A B C = B² - 4AC` (mathlib's `discrim` from `Algebra.QuadraticDiscriminant`).

### The private lemmas, in file order
1. **`eq_of_quadratic_eq_zero_of_mul_neg`**: if `AC < 0`, `f` has at most one positive root. Let `x, y > 0` be roots with `x ≠ y`. Subtracting, `(x - y)(A(x + y) + B) = 0`, so `A(x + y) + B = 0`. Substituting `B = -A(x + y)` into `A·f(x) = 0` gives `AC = A² x y ≥ 0`, contradiction.
2. **`abs_le_discrim_of_mul_neg`**: if `AC < 0` then `|A|, |B|, |C| ≤ D`. `D = B² + 4|A||C|`; `|A|, |C| ≥ 1` (nonzero integers), so `|A| ≤ |A||C|` and `|C| ≤ |A||C|`; `|B| ≤ B²` for an integer (`Int.natAbs_le_self_sq`). `linarith` finishes.
3. **`finite_setOf_quadratic_eq_zero D`**: the set `S_D` of `x > 0` that are roots of some `(A, B, C)` with `AC < 0` and discriminant `D` is finite. By 2 the triple lies in the finite box `[-D, D]³` (`Set.finite_Icc` in `ℤ × ℤ × ℤ`), and by 1 each triple contributes at most one `x` (`Set.Subsingleton.finite`).
4. **`mul_neg_of_quadratic_eq_zero`**: if `A ≠ 0`, `AC ≥ 0` and `f` has a root `x > 0`, then `AB < 0`. From `A·f(x) = 0`: `AB·x = -(A² x² + AC) < 0`, and `x > 0`.
5. **`quadratic_completeQuotient_one`**: if `v` is irrational with `f(v) = 0`, `A ≠ 0`, `k = ⌊v⌋`, then `f(k) ≠ 0` and `f(k) v₁² + (2Ak + B) v₁ + A = 0`. Second part: substitute `v = k + 1/v₁` and multiply by `v₁²` (`field_simp`, `linear_combination`). First part: if `f(k) = 0` then `0 = f(v) - f(k) = (v - k)(A(v + k) + B)` with `v ≠ k`, so `v = -B/A - k` is rational, contradicting non-termination (`terminates_iff_rat`).
6. **`exists_quadratic_completeQuotient`**: every `vₙ` is a root of an integer quadratic with nonzero leading coefficient and discriminant `D`. Induction on `n` (for all `v, A, B, C`) with 5; the discriminant is preserved: `(2Ak + B)² - 4(Ak² + Bk + C)A = B² - 4AC` (`ring`).
7. **`exists_completeQuotient_quadratic_mul_neg`**: if moreover `v > 1`, some `vₙ > 0` is a root of a triple with `A'C' < 0` and discriminant `D`. Strong induction on `|B|`.
   - If `AC < 0`: take `n = 0`.
   - Else let `(A₁, B₁, C₁) = (f(k), 2Ak + B, A)`, with root `v₁ > 1`. If `A₁C₁ < 0`: take `n = 1`.
   - Else `AC ≥ 0` and `f(k)·A ≥ 0`. By 4 applied to `f` and the root `v > 0`: `AB < 0`. By 4 applied to `A X² + (2Ak + B) X + f(k)` (this is `f(k + X)`, with root `fract v = v - k > 0`): `A·B₁ < 0`. With `k ≥ 1`: `B² - B₁² = (B - B₁)(B + B₁) = 2k(-AB) + 2k(-AB₁) > 0`, so `|B₁| < |B|` (this is the `nlinarith` line; its two hints are exactly the two positive products). Apply the induction hypothesis to `v₁`; the `n`-th complete quotient of `v₁` is `vₙ₊₁` by definition.
8. **`exists_completeQuotient_add_eq`**: two complete quotients coincide. Otherwise `n ↦ vₙ` is injective, so the preimage of the finite set `S_D` is finite. But it is infinite: for each `N`, `v_{N+1} > 1` is an irrational root of a triple of discriminant `D` (6), and 7 applied to `v_{N+1}` gives `m = n + N + 1 > N` with `v_m ∈ S_D` (`Set.infinite_of_forall_exists_gt`).
9. **`exists_int_quadratic_eq_zero`**: a quadratic irrational is a root of `A X² + B X + C` with `A ≠ 0`, integers. `P = IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ v)` is an integer polynomial that is a nonzero integer multiple of the minimal polynomial; a coefficient of `P` vanishes iff the corresponding one of `minpoly` does (`IsFractionRing.coeff_integerNormalization_eq_zero_iff`). So `natDegree P < 3`, `P.coeff 2 ≠ 0` (leading coefficient of `minpoly`), and `aeval v P = 0` (`integerNormalization_aeval_eq_zero`); expand the sum over `range 3`.

**Lagrange**: `v` is irrational (a rational has minimal polynomial of degree `1`, `minpoly.natDegree_eq_one_iff`), so the expansion does not terminate; 9 gives a triple, 8 gives `v_{N+p} = v_N`, and `of_isEventuallyPeriodic_iff` (PR 2) concludes.

### Likely reviewer questions
- *Why Steinig's proof and not Hardy–Wright's?* The textbook proof bounds the coefficients using the conjugate root and convergent estimates. Steinig's uses only signs of integer coefficients, which is shorter to formalize and works verbatim over any ordered floor field.
- *Why bare triples and not `Polynomial` or `BinaryQuadraticForm`?* The helpers are private and only need the evaluation identity `A x² + B x + C = 0`; using `Polynomial` would add `aeval`/`coeff` bookkeeping for no reuse. No public API about quadratic forms is added.
- *`nlinarith`?* One terminal call with explicit hints; the identity above shows it is a linear combination of the two hints. `linarith` is likely enough if the reviewer asks.
- *Is `hA : A ≠ 0` used in lemma 4?* Yes, by `positivity` for `0 < A² x² + AC`; the unused-arguments linter passes.
- *Size?* 238 lines; the nine helpers are each short. If asked to split, lemmas 1–4 (pure algebra of integer quadratics) could go first, but they would then be public.
- *Is the citation right?* J. Steinig, *A proof of Lagrange's theorem on periodic continued fractions*, Arch. Math. (Basel) 59 (1992), no. 1, 21–23, DOI 10.1007/BF01199010 (matches Crossref). Read the paper once before submitting, so you can confirm the docstring's summary of the argument.

### Before you open it
- Mathlib.lean: add only `public import Mathlib.NumberTheory.ContinuedFractions.Lagrange`.
- docs/references.bib: add only the `steinig1992` entry (between `stanley2012` and `stenstrom1971`). The `galois1829` entry belongs to the next PR. `bibtool` formatting was not run; CI checks it.

## 6.6 `cf-galois-purely-periodic`: Galois's theorem: purely periodic if and only if reduced

### One file, two PRs
`PurelyPeriodic.lean` is shared with 6.7. The branch of 6.6 contains the first 211 lines' worth (the theorem "purely periodic if and only if reduced"); 6.7 adds the section on the reversed period and three sentences of the module docstring. The 6.6 version was built and linted as a module on its own.

### Statement
Let `v` have `(minpoly ℚ v).natDegree = 2` and let `w ≠ v` be a conjugate root (`IsConjRoot ℚ v w`, i.e. `minpoly ℚ v = minpoly ℚ w`). **Galois**: `of v` is purely periodic iff `1 < v` and `-1 < w < 0`.

Second form: purely periodic iff `1 < v` and some conjugate root lies in `(-1, 0)`. Such a root is automatically `≠ v`, and a quadratic has only two roots, so it is the conjugate.

### Private lemmas about an abstract sequence `c`
Throughout, `hc : ∀ n, c (n + 1) = (c n - ⌊vₙ⌋)⁻¹`.
- **`inv_sub_floor_mem_Ioo`**: if `x > 1` and `y < 0` then `(y - ⌊x⌋)⁻¹ ∈ (-1, 0)`. `⌊x⌋ ≥ 1`, so `y - ⌊x⌋ < -1`; inverting a number `< -1` lands in `(-1, 0)`.
- **`mem_Ioo_of_lt`**: if all `vₙ > 1` and `c m < 0`, then `c n ∈ (-1, 0)` for all `n > m`. Induction from `m + 1` with the previous lemma.
- **`mem_Ioo_of_mem_Ioo`**: if moreover `c 0 ∈ (-1, 0)`, then all `c n ∈ (-1, 0)`.
- **`floor_neg_inv_succ`**: if `c n ∈ (-1, 0)` then `⌊-(c (n+1))⁻¹⌋ = ⌊vₙ⌋`. Indeed `-(c (n+1))⁻¹ = ⌊vₙ⌋ - c n` with `0 < -c n < 1`.
- **`completeQuotient_eq_of_add_eq`**: if all `c n ∈ (-1, 0)` and `c` depends only on the value `vₙ` (`hc' : v_m = v_n → c m = c n`), then `v_{N+p} = v_N` implies `v_p = v`. Induction on `N`: from `v_{N+1+p} = v_{N+1}` get `c (N+p+1) = c (N+1)`, hence `⌊v_{N+p}⌋ = ⌊v_N⌋` by the previous lemma, hence `v_{N+p} = ⌊v_{N+p}⌋ + 1/v_{N+p+1} = ⌊v_N⌋ + 1/v_{N+1} = v_N`.
- **`exists_lt_zero`**: if `of v` does not terminate, all `vₙ > 1` and `c 0 ≠ v`, then some `c n < 0`. Suppose all `c n ≥ 0`. From `c (n+2) ≥ 0` get `c (n+1) ≥ ⌊v_{n+1}⌋ ≥ 1`, so `c n - ⌊vₙ⌋ > 0` (`hpos`). Then `c (n+1) = ⌊v_{n+1}⌋ + (positive) > 1`, so `c n - ⌊vₙ⌋ < 1`. Hence `⌊c n⌋ = ⌊vₙ⌋` (`hfl`) and `c (n+1) = (fract (c n))⁻¹`, i.e. `c n` is the `n`-th complete quotient of `c 0` (`hcq`). So `of (c 0)` and `of v` have the same head `⌊v⌋` and the same entries `⟨1, ⌊vₙ₊₁⌋⟩` (neither terminates: `fract (c n) = c n - ⌊vₙ⌋ ≠ 0`). `of_injective` gives `c 0 = v`, contradiction.

### Field-theory lemmas
- **`exists_conj_completeQuotient`** (no order needed, hence `omit`): there is `c` with `c 0 = w`, the recurrence `hc`, and `hc'`. `v` is integral (its minimal polynomial is nonzero). `algHomAdjoinIntegralEquiv ℚ hint` is mathlib's bijection between `ℚ`-algebra maps `ℚ⟮v⟯ → K` and roots of `minpoly ℚ v` in `K`; let `φ` be the map for the root `w`, so `φ v = w`. Put `c n = φ vₙ` (legal since `vₙ ∈ ℚ⟮v⟯`, PR 3). `φ` is a field homomorphism fixing integers, so `φ ((vₙ - ⌊vₙ⌋)⁻¹) = (c n - ⌊vₙ⌋)⁻¹`. `hc'` is `congrArg φ`.
- **`exists_ne_and_isConjRoot`**: a quadratic irrational has a conjugate `w ≠ v` in `K`. The minimal polynomial has degree `2` and a root in `K`, so it splits in `K` (`Polynomial.Splits.of_natDegree_eq_two`); it is separable (irreducible, characteristic zero); mathlib's `notMem_iff_exists_ne_and_isConjRoot` then turns 'not rational' into the existence of a different conjugate root.

### Main proofs
**`of_isPurelyPeriodic_iff_of_isConjRoot`**. Non-termination comes from Lagrange. Take `c` as above and rewrite purely periodic as `∃ p > 0, v_p = v` (PR 2).
- (⇒) `v = v_{p+1} > 1` (a complete quotient of positive index), so all `vₙ > 1`. `exists_lt_zero` gives `c n < 0` (as `c 0 = w ≠ v`). `v_{(n+1)(p+1)} = v` by `Function.IsPeriodicPt.const_mul`. Since `(n+1)(p+1) > n`, `c ((n+1)(p+1)) ∈ (-1, 0)`, and by `hc'` this value is `c 0 = w`.
- (⇐) All `c n ∈ (-1, 0)`. Lagrange gives `v_{N+p} = v_N` with `p > 0`; `completeQuotient_eq_of_add_eq` gives `v_p = v`.

**`of_isPurelyPeriodic_iff_of_natDegree_minpoly_eq_two`**: (⇒) pick `w` by `exists_ne_and_isConjRoot` and apply the first form. (⇐) `w < 0 < 1 < v` gives `v ≠ w`; apply the first form.

### Likely reviewer questions
- *Why `IsConjRoot` and `v ≠ w` instead of a conjugation function or a `Reduced` predicate?* It uses only existing mathlib notions and works in any ordered floor field; over ℝ one supplies the other root of the quadratic. The second form hides the choice of `w`.
- *Why an abstract sequence `c`?* It separates the order arguments from the field theory; the same lemmas are reused by the reversed-period PR.
- *Why `omit [IsStrictOrderedRing K] in`?* The two field-theory lemmas do not use the order; without `omit` the unused-section-variable linter fails. `omit ... in` must precede the docstring.
- *Does the proof need Lagrange in the (⇒) direction?* Only for non-termination; that also follows from pure periodicity, but `h` is a hypothesis anyway.
- *Only Galois' original paper is cited.* A textbook reference (e.g. Perron, *Die Lehre von den Kettenbrüchen*, on reduced quadratic irrationals) was not added because it could not be checked; add one if you have the book at hand.

### Before you open it
- Mathlib.lean: add only `public import Mathlib.NumberTheory.ContinuedFractions.PurelyPeriodic`.
- docs/references.bib: add only the `galois1829` entry (between `Gallier2011Notes` and `gartnerMatousek`).

## 6.7 `cf-galois-reversed-period`: Galois's theorem on the reversed period

### How to produce this PR
After the previous PR, replace the file by the working-tree version `Mathlib/NumberTheory/ContinuedFractions/PurelyPeriodic.lean` (283 lines). The diff is: one sentence in the first docstring paragraph, two 'Main results' bullets, one paragraph of implementation notes, and the section `### The reversed period`.

### Statements
`v` quadratic irrational, `w ≠ v` its conjugate, `c n = wₙ` the conjugates of the complete quotients (from `exists_conj_completeQuotient`).

If `v = [a₀; a₁, …, a_{p-1}, a₀, …]` is purely periodic with period `p`, then `-1/w = [a_{p-1}; a_{p-2}, …, a₀, a_{p-1}, …]`.

In Lean: the `k`-th partial quotient of `-1/w` is `⌊completeQuotient (-w⁻¹) k⌋`, the `j`-th of `v` is `⌊completeQuotient v j⌋`, and the theorem says they are equal when `j + k + 1 = p`, i.e. `j = p - 1 - k`.

### Proofs
- **`inv_fract_neg_inv_succ` (private)**: if `c n ∈ (-1, 0)` then `(fract (-(c (n+1))⁻¹))⁻¹ = -(c n)⁻¹`. `-(c (n+1))⁻¹ = ⌊vₙ⌋ - c n`, its floor is `⌊vₙ⌋` (`floor_neg_inv_succ`), so its fractional part is `-c n`.
- **`completeQuotient_neg_inv_add` (private)**: if all `c n ∈ (-1, 0)`, the `k`-th complete quotient of `-(c (m + k))⁻¹` is `-(c m)⁻¹`. Induction on `k` with `completeQuotient_succ'` and the previous lemma.
- **`exists_conj_completeQuotient_mem_Ioo` (private)**: packaging. If `v_{p+1} = v` then `v` is purely periodic, so by Galois' theorem `v > 1` and `w ∈ (-1, 0)`, hence all `c n ∈ (-1, 0)` (`mem_Ioo_of_mem_Ioo`).
- **`completeQuotient_neg_inv_of_isConjRoot`**: `p = 0` is `rfl`. For `p + 1`: `c (p + 1) = c 0 = w` because `v_{p+1} = v₀`; the previous lemma with `m = 0`, `k = p + 1` says the `(p+1)`-th complete quotient of `-(c (p+1))⁻¹ = -w⁻¹` is `-(c 0)⁻¹ = -w⁻¹`.
- **`floor_completeQuotient_neg_inv_of_isConjRoot`**: `w = c (j + k + 1) = c ((j + 1) + k)`; the `k`-th complete quotient of `-w⁻¹` is `-(c (j + 1))⁻¹`, whose floor is `⌊v_j⌋` (`floor_neg_inv_succ`).
- **`IsPurelyPeriodic.neg_inv_of_isConjRoot`**: by PR 2 it suffices that `of (-w⁻¹)` does not terminate and `-w⁻¹` equals its `p`-th complete quotient (above; the degree hypothesis comes from Euler's theorem applied to `v`). Non-termination: if `-w⁻¹ = q` were rational then `w = -q⁻¹` is rational, and a rational conjugate root of `v` equals `v` (`IsConjRoot.eq_algebraMap`), contradicting `v ≠ w`.

### Likely reviewer questions
- *Why not a separate file?* The proofs use three private lemmas of the first part; a second file would force them to become public API.
- *Why state the reversal through floors of complete quotients rather than `partDens`?* `⌊completeQuotient x k⌋` is the `k`-th partial quotient including the head (`k = 0`), so one statement covers all positions; `get?_of_eq_some_of_not_terminatedAt` (PR 1) converts to `(of x).s`.
- *Is `-1/w` again reduced?* Yes: its conjugate is `-1/v ∈ (-1, 0)` and `-1/w > 1`; the theorem proves pure periodicity directly instead.
- *`w = 0`?* Impossible under the hypotheses (`w` is irrational), and the proof does not need to treat it.

## Overlap with Tau Ceti

No overlap with any public declaration of the stack. Re-checked with rg on D:/Projects/tauceti-ref/TauCeti/TauCeti (commit 3f8fe7e3, 2026-11-26): no `IsEventuallyPeriodic`/`IsPurelyPeriodic`, no `completeQuotient` (the 12 files mentioning continued fractions contain the words 'complete quotient' only in docstrings of Algebra/ContinuedFractions/Approximations.lean), no injectivity of `GenContFract.of`, no Euler/Lagrange/Galois theorem on continued fractions. Related but different material: (1) `Real.convDen_pos` (NumberTheory/DiophantineApproximation/ContinuedFractions/Convergents.lean) is positivity of `Rat.den` of `Real.convergent`, not of `(GenContFract.of v).dens n`; (2) `TauCeti.IntermediateField.adjoin_simple_inv` is NOT added (the inverse step of `adjoin_completeQuotient` is inline); (3) BinaryQuadraticForm/LagrangeReduction.lean and IndefiniteReduction/Cycles.lean (Lagrange reduction and Gauss cycles of reduced indefinite forms) and BestApproximation.lean ('Lagrange's best approximation property') are different theorems; the integer-quadratic helpers of Lagrange.lean are private; (4) Tau Ceti's `badlyApproximable_of_natDegree_minpoly_eq_two` uses the same formulation `(minpoly ℚ ξ).natDegree = 2` of 'quadratic irrational', which is a hypothesis shape, not a declaration. Open mathlib PRs (gh search, 2026-11-27): only #39212 (partNumsStream, other files), #45950 (Gauss map in Dynamics/Ergodic/GaussMap.lean), #43595 (Liouville), #46382 (unpriming) mention continued fractions; none overlaps.

