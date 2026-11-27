import HilbertFoundations.Constructions
import HilbertFoundations.ConstructionsCloseAux3
import HilbertFoundations.ConstructionsCloseAux4
import HilbertFoundations.ConstructionsCloseAux5
import HilbertFoundations.ConstructionsCloseAux6
import HilbertFoundations.ConstructionsCloseAux7

/-!
# Constructions (§§ 38–39): Theorem 43, Theorem 44 with one parameter, the regular polygons, Malfatti

This file closes units of `Constructions.lean` that were stated there as open:

* **`th.43`** (Theorem 43) — `theorem43 : Theorem43`. Proved without Theorem 42, in the stronger
  form `theorem43_polynomial`: a polynomial with rational coefficients that never becomes negative
  is a sum of squares of *polynomials* with rational coefficients (Landau 1906; the denominator of
  Hilbert's quotient is `1`).
* **`s39.regular_polygons`** — `regularPolygonsClaim : RegularPolygonsClaim`. Every regular polygon
  constructible with the compass is constructible by straight-edge and transferer.
* **`s39.malfatti`** — `malfattiClaim : MalfattiClaim`. The circles of Malfatti of every triangle
  are constructible by straight-edge and transferer.

and proves, towards the units `th.44` and `s38.two_variables`:

* **`th.44`** (Theorem 44) — proved **in the case that Hilbert demonstrates**, "the co-ordinates of
  the given points are rational functions, having rational coefficients, of a single parameter
  `p`": `theorem44_one_parameter` (any finite set `S ⊆ ℚ(p)` of coordinates, by Lüroth's theorem),
  in particular `theorem44_single_parameter : ∀ p : ℝ, Theorem44For ℚ(p)`; and for given points
  with algebraic coordinates (`theorem44_algebraic`). The Prop `Theorem44` of `Constructions.lean`
  is the *general case* (any number of parameters), which Hilbert leaves open ("depends upon
  whether or not theorem 43 can be generalized … to cover the case of two or more variables"); it
  is proved here to be **equivalent** to that generalization
  (`theorem44_iff_generalized_theorem43`), which is Hilbert's seventeenth problem for the finitely
  generated subfields of `ℝ` (Artin 1927). `Theorem44` itself is proved in `Theorem44Close.lean`
  (`theorem44`), which imports this file, from that generalization (`theorem43For_closure`); the
  Artin–Schreier separation by orderings and the transfer of sign conditions used there are taken
  from the copied library `Hilbert17`, the real closure from the Tau Ceti library.
* **`s38.two_variables`**: Hilbert's theorem of 1893 for a polynomial of degree at most two in one
  of the variables (`twoVariableClaim_quadratic`). The theorem itself is proved in
  `TwoVariablesClose.lean`, from Artin's theorem as proved in the copied library `Hilbert17`.

It also contains the results on the unit **`th.42`** (Theorem 42) that do not need the
Hasse–Minkowski theorem. Theorem 42 itself is proved in `Theorem42Close.lean`, which imports this
file (`theorem42 : Theorem42`); the Hasse–Minkowski theorem used there is not proved in this
project and is taken from the Tau Ceti library, a dependency of the package. Proved here:

* in a number field every totally positive number is a sum of squares
  (`theorem42_sum_of_squares`), so that Theorem 42 is equivalent to "every sum of squares in a
  number field is a sum of four squares" (`theorem42_iff_pythagoras_number_le_four`);
* Theorem 42 is equivalent to the isotropy over `k` of the forms `x₁² + x₂² + x₃² + x₄² - α x₅²`,
  `α` totally positive (`theorem42_iff_isotropic`); the implication from a nontrivial zero of the
  form to the four squares, `four_squares_of_isotropic`, is the last step of `theorem42`;
* the conclusion of Theorem 42 holds in every field of characteristic `0` in which `-1` is a sum
  of three squares (`theorem42_of_neg_one_three_squares`; with three squares when `-1` is a sum of
  two, `theorem42_of_neg_one_two_squares`).

## The proofs

*Theorem 43* (`ConstructionsCloseAux.lean`). If `f ∈ ℚ[x]` has a real root, the minimal polynomial
of the root divides `f` twice (Hilbert's first case, unit `s38.factor_cases`), which reduces the
degree. Otherwise `f > 0` on `ℝ`, of degree `2m`, and `f ≥ c (1 + x² + … + x^{2m})` for some
`c > 0` (`real_pos_lower_bound`). For a rational `0 < ε < c`, `f - ε (1 + x² + … + x^{2m})` is
nonnegative, hence `g² + h²` with real polynomials `g`, `h` of degree `≤ m` (`real_psd_two_sq`,
by the fundamental theorem of algebra). Replacing the coefficients of `g`, `h` by rational
approximations `g̃`, `h̃` gives `f = g̃² + h̃² + R` where `R ∈ ℚ[x]` has even coefficients `≥ ε/2`
and odd coefficients of absolute value `≤ ε/2`; such an `R` is a sum of squares with positive
rational weights (`isSumSq_of_dominant`: `d x^{2j+1} + (|d|/2)(x^{2j} + x^{2j+2}) =
(|d|/2)(x^j ± x^{j+1})²`), and positive rational numbers are sums of four squares.

*Totally positive numbers* (`ConstructionsCloseAux2.lean`). For `α = a(θ)` in `k = ℚ(θ)` with
`a > 0` at the real roots of the minimal polynomial `p` of `θ`, the polynomial
`a + c p² (1 + a²)` never becomes negative for a suitable rational `c > 0`, hence is a sum of
squares by Theorem 43, and its value at `θ` is `α`.

*Regular polygons* (`ConstructionsCloseAux3.lean`). A number constructible with the compass lies
in a tower of square roots over `ℚ`. Every *totally real* number of such a tower lies in `Ω`
(`tower_totReal_mem_omega`, by induction on the tower: for `x = r + s √a` the trace `2r` and the
number `s² a` are totally real, `s² a` is totally nonnegative, hence a sum of squares of numbers of
`ℚ(s² a) ⊆ Ω`, and `x = r ± √(s² a)`). The number `cos (2π/N)` is totally real: its conjugates
satisfy the Chebyshev equation `T_N(z) = 1`, whose complex solutions are `cos (2πj/N)`. With
`N = 4n` this gives `cos (2πk/n)` and `sin (2πk/n)`.

*Theorem 44 with one parameter* (`ConstructionsCloseAux5.lean`). Hilbert's reduction of Theorem 44
over a domain `R` to "Theorem 43 for `R`" (`Theorem43For R`: a number of `R` that is nonnegative
for all real values of the parameters is a quotient of two sums of squares in `R`) is in
`ConstructionsAux10`. For `R = ℚ(p)` with `p` transcendental, the real embeddings of `R` are the
substitutions `p ↦ c`, `c` transcendental; a number `N(p)/D(p)` nonnegative under all of them gives
a polynomial `N D` that never becomes negative (the transcendental numbers are dense in `ℝ`), a sum
of squares by Theorem 43. For `p` algebraic, `R` is a number field and the qualitative Theorem 42
applies. Conversely Theorem 44 over `R`, applied to the single square root `√g`, gives
`Theorem43For R`: a sum of squares in `F(√(x² + y²))` that lies in `R` is a sum of squares in `F`.
When the coordinates of the given points are rational functions of `p`, the domain `R` they
generate is a subfield of `ℚ(p)`, hence `ℚ(q)` for a single `q` by Lüroth's theorem
(`ConstructionsCloseAux7.lean`).

*Two variables* (`ConstructionsCloseAux6.lean`). If `f = P(x) y² + Q(x) y + R(x) ≥ 0` on `ℝ²`, then
`P ≥ 0` and `4PR - Q² ≥ 0` on `ℝ`, both are sums of two squares of real polynomials, and
`4 P f = (2 P y + Q)² + (4 P R - Q²)`.

*Malfatti* (`ConstructionsCloseAux4.lean`). With the inradius `r`, the semiperimeter `s`, the
tangent lengths `x = s - a`, … and the distances `d`, `e`, `f` from the incenter `I` to the
vertices, the circle in the angle `A` has center `A + (t₁/x)(I - A)` and radius `(t₁/x) r`,
`t₁ = (s + d - r - e - f)/2`. The contact of two circles is `4 z t₁ t₂ = s (r + f - z)²`, from
`d e z = r (x + y) f` and Heron's formula `r² s = x y z`. All these numbers arise from the
coordinates of the vertices by the rational operations and square roots of sums of two squares.
-/

namespace HilbertFoundations

open Polynomial
open scoped Real

/-! ## Theorem 43 -/

/-- **Theorem 43, in the strong form**: a polynomial with rational coefficients that never becomes
negative for real `x` is a sum of squares of polynomials with rational coefficients. -/
theorem theorem43_polynomial {f : ℚ[X]} (hf : PSD f) : IsSumSq f :=
  psd_isSumSq hf

/-- **Theorem 43** (unit `th.43`). -/
theorem theorem43 : Theorem43 :=
  fun f hf => ⟨f, 1, psd_isSumSq hf, IsSumSq.one, one_ne_zero, mul_one f⟩

/-! ## Theorem 42: the results that do not need the Hasse–Minkowski theorem -/

/-- **The qualitative Theorem 42**: in a number field, every totally positive number is a sum of
squares of numbers of the field. -/
theorem theorem42_sum_of_squares (k : Type) [Field k] [NumberField k] (α : k)
    (h : TotallyPositive α) : IsSumSq α :=
  totallyPositive_isSumSq k α h

/-- Theorem 42 is equivalent to: in every number field, a sum of squares is a sum of four
squares. -/
theorem theorem42_iff_pythagoras_number_le_four :
    Theorem42 ↔ ∀ (k : Type) [Field k] [NumberField k] (α : k), IsSumSq α →
      ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 :=
  theorem42_iff_four_squares

/-- **Theorem 42 with three squares when `-1` is a sum of two squares**: in a field in which
`-1 = i² + j²`, every number is a sum of three squares,
`α = ((α+1)/2)² + (i (α-1)/2)² + (j (α-1)/2)²`. -/
theorem theorem42_of_neg_one_two_squares {k : Type*} [Field k] [CharZero k] {i j : k}
    (h : i ^ 2 + j ^ 2 = -1) (α : k) :
    ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 :=
  ⟨(α + 1) / 2, i * ((α - 1) / 2), j * ((α - 1) / 2), 0, by
    linear_combination (-(α - 1) ^ 2 / 4) * h⟩

/-- **Theorem 42 when `-1` is a sum of three squares**: in a field in which `-1 = i² + j² + l²`,
every number is a sum of four squares,
`α = ((α+1)/2)² + (i (α-1)/2)² + (j (α-1)/2)² + (l (α-1)/2)²`. So Theorem 42 holds for every number
field in which `-1` is a sum of three squares; in particular the isotropy over `k` of the form
`x₁² + x₂² + x₃² + x₄² - α x₅²` (what the Hasse–Minkowski theorem gives for a totally positive `α`)
implies that `α` is a sum of four squares, also when `x₅ = 0`. -/
theorem theorem42_of_neg_one_three_squares {k : Type*} [Field k] [CharZero k] {i j l : k}
    (h : i ^ 2 + j ^ 2 + l ^ 2 = -1) (α : k) :
    ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 :=
  ⟨(α + 1) / 2, i * ((α - 1) / 2), j * ((α - 1) / 2), l * ((α - 1) / 2), by
    linear_combination (-(α - 1) ^ 2 / 4) * h⟩

/-- **Theorem 42 from the isotropy of `x₁² + x₂² + x₃² + x₄² - α x₅²`**: if this form has a
nontrivial zero in a field `k` of characteristic `0`, then `α` is a sum of four squares in `k`.
(For a number field `k` and a totally positive `α` the form is isotropic at every completion of
`k`; that it is then isotropic over `k` is the Hasse–Minkowski theorem. `theorem42` in
`Theorem42Close.lean` takes that theorem from the Tau Ceti library and concludes with the present
statement.) -/
theorem four_squares_of_isotropic {k : Type*} [Field k] [CharZero k] {α x₁ x₂ x₃ x₄ x₅ : k}
    (h : x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 = α * x₅ ^ 2)
    (hne : x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 ∨ x₅ ≠ 0) :
    ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  by_cases h5 : x₅ = 0
  · -- a nontrivial zero of `x₁² + x₂² + x₃² + x₄²`: `-1` is a sum of three squares
    rw [h5, zero_pow two_ne_zero, mul_zero] at h
    have key : ∀ y a b c : k, y ≠ 0 → y ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 = 0 →
        ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
      intro y a b c hy hsum
      refine theorem42_of_neg_one_three_squares (i := a / y) (j := b / y) (l := c / y) ?_ α
      field_simp
      linear_combination hsum
    rcases hne with h1 | h2 | h3 | h4 | h5'
    · exact key x₁ x₂ x₃ x₄ h1 h
    · exact key x₂ x₁ x₃ x₄ h2 (by linear_combination h)
    · exact key x₃ x₁ x₂ x₄ h3 (by linear_combination h)
    · exact key x₄ x₁ x₂ x₃ h4 (by linear_combination h)
    · exact absurd h5 h5'
  · refine ⟨x₁ / x₅, x₂ / x₅, x₃ / x₅, x₄ / x₅, ?_⟩
    field_simp
    linear_combination -h

/-- **Theorem 42 is equivalent to the isotropy of the forms `x₁² + x₂² + x₃² + x₄² - α x₅²`** over
every number field `k`, for the totally positive numbers `α` of `k`: an instance of the
Hasse–Minkowski theorem over number fields (Hilbert's "ternary diophantine equation" being the case
of three variables). The isotropy is proved in `Theorem42Close.lean`
(`exists_isotropic_of_totallyPositive`, for `α ≠ 0`), from the Hasse–Minkowski theorem of the
Tau Ceti library, and Theorem 42 with it (`theorem42`). -/
theorem theorem42_iff_isotropic :
    Theorem42 ↔ ∀ (k : Type) [Field k] [NumberField k] (α : k), TotallyPositive α →
      ∃ x₁ x₂ x₃ x₄ x₅ : k, x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 = α * x₅ ^ 2 ∧
        (x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 ∨ x₅ ≠ 0) := by
  constructor
  · intro h k _ _ α hα
    obtain ⟨a, b, c, d, e⟩ := h k α hα
    exact ⟨a, b, c, d, 1, by rw [e]; ring, Or.inr (Or.inr (Or.inr (Or.inr one_ne_zero)))⟩
  · intro h k _ _ α hα
    obtain ⟨x₁, x₂, x₃, x₄, x₅, e, hne⟩ := h k α hα
    exact four_squares_of_isotropic e hne

/-! ## Theorem 44 -/

/-- **Theorem 43 for rational functions of one parameter**: a number of `ℚ(t)`, `t` transcendental,
that is nonnegative for all (transcendental) real values of the parameter is a quotient of two
sums of squares of numbers of `ℚ(t)`. -/
theorem theorem43_rational_functions {t : ℝ} (ht : Transcendental ℚ t) :
    Theorem43For (Subfield.closure ({t} : Set ℝ)) :=
  theorem43For_transcendental ht

/-- **Theorem 44 for a single parameter** `p` (the case Hilbert demonstrates): for the domain
`R = ℚ(p)` generated by one real number, the numbers of a tower of square roots over `R` are
constructible by straight-edge and transferer from `R` iff every radicand is nonnegative for all
real values of the parameter and either sign of the square roots. -/
theorem theorem44_single_parameter (p : ℝ) : Theorem44For (Subfield.closure ({p} : Set ℝ)) :=
  theorem44For_singleton p

/-- **Theorem 44 in the case that Hilbert demonstrates**: "the co-ordinates of the given points are
rational functions, having rational coefficients, of a single parameter `p`". For every finite set
`S` of numbers of `ℚ(p)` (the coordinates of the given points) and the domain `R = ℚ(S)` they
generate, the numbers of a tower of square roots over `R` are constructible by straight-edge and
transferer from `R` iff every radicand is nonnegative for all real values of the parameter and
either sign of the square roots. (`R` is `ℚ(q)` for a single `q`, by Lüroth's theorem.)

As everywhere in the reading of Theorem 44 (`RealTowerOver`), "all real values of the parameter"
means: under every embedding of the tower that is real on `R`. When `R = ℚ(p)` — Hilbert's case,
the parameter being "expressed in terms of the co-ordinates of the given points",
`theorem44_single_parameter` — these are the real values of `p`. When `R = ℚ(S)` is a proper
subfield of `ℚ(p)`, they are the real values of the generator `q` of `R`, which may be more than
the values `q(p)` for real `p`: for `S = {p²}`, `p` transcendental, the tower `√(p²)` does not
satisfy the condition (`p² ↦ c`, `c` a negative transcendental number, is a real value of the
parameter `q = p²`), and accordingly `|p| ∉ Ω(ℚ(p²))` (`abs_notMem_pythClosure_sq`). -/
theorem theorem44_one_parameter (p : ℝ) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Subfield.closure ({p} : Set ℝ)) :
    Theorem44For (Subfield.closure (S : Set ℝ)) :=
  theorem44For_of_subset_singleton p S hS

/-- **An example for Theorem 44 with one parameter** (and for the reading of "all real values of
the parameter"): from a given point `(p², 0)`, `p` transcendental, the segment `|p| = √(p²)` cannot
be constructed by straight-edge and transferer, although `p²` is positive: the radicand `p²` is
negative for the real values `c < 0` of the parameter `q = p²` of the domain `ℚ(p²)`. -/
theorem abs_notMem_pythClosure_sq {p : ℝ} (hp : Transcendental ℚ p) :
    ¬PythClosure ((Subfield.closure ({p ^ 2} : Set ℝ) : Subfield ℝ) : Set ℝ) |p| := by
  intro h
  have hq : Transcendental ℚ (p ^ 2) := hp.pow two_pos
  have hqR : p ^ 2 ∈ Subfield.closure ({p ^ 2} : Set ℝ) := Subfield.subset_closure rfl
  have hv : ValidTowerOver (Subfield.closure ({p ^ 2} : Set ℝ)) [p ^ 2] :=
    ⟨trivial, hqR, sq_nonneg p⟩
  have hle : towerFieldOver (Subfield.closure ({p ^ 2} : Set ℝ)) [p ^ 2] ≤
      pythSubfield (Subfield.closure ({p ^ 2} : Set ℝ)) := by
    show Subfield.closure _ ≤ _
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · exact PythClosure.base hy
    · rw [Set.mem_singleton_iff.1 hy, Real.sqrt_sq_eq_abs]; exact h
  have hr : RealTowerOver (Subfield.closure ({p ^ 2} : Set ℝ)) [p ^ 2] :=
    (theorem44For_singleton (p ^ 2) [p ^ 2] hv).2 fun x hx => hle hx
  have htn : TotNonnegOver (Subfield.closure ({p ^ 2} : Set ℝ))
      (Subfield.closure ({p ^ 2} : Set ℝ)) (p ^ 2) := hr.2
  obtain ⟨hgR, hσ⟩ := htn
  have hdense : Dense {y : ℝ | IsAlgebraic ℚ y}ᶜ :=
    (Algebraic.countable (R := ℚ) (A := ℝ)).dense_compl ℝ
  obtain ⟨c, hc, hc0⟩ := hdense.exists_mem_open (isOpen_Iio (a := (0 : ℝ))) ⟨-1, by norm_num⟩
  have hc' : Transcendental ℚ c := hc
  obtain ⟨s, hs, e⟩ := hσ (Complex.ofRealHom.comp (specialize hq hc'))
    fun y _ => ⟨specialize hq hc' y, rfl⟩
  have e' : ((specialize hq hc' ⟨p ^ 2, hgR⟩ : ℝ) : ℂ) = (s : ℂ) := e
  have e1 : specialize hq hc' ⟨p ^ 2, hgR⟩ = s := Complex.ofReal_injective e'
  have e2 : specialize hq hc' ⟨p ^ 2, hgR⟩ = aeval c (X : ℚ[X]) / aeval c (1 : ℚ[X]) :=
    specializeFun_eq hq hc' ⟨p ^ 2, hgR⟩ (N := X) (D := 1) (by simp) (by simp)
  rw [e2] at e1
  have e3 : c = s := by simpa using e1
  have hc1 : c < 0 := hc0
  linarith

/-- **Theorem 44 for given points with algebraic coordinates.** -/
theorem theorem44_algebraic (S : Finset ℝ) (hS : ∀ x ∈ S, IsAlgebraic ℚ x) :
    Theorem44For (Subfield.closure (S : Set ℝ)) :=
  theorem44For_of_algebraic S hS

/-- **The general case of Theorem 44 is equivalent to the generalization of Theorem 43** to the
domains generated by finitely many real numbers (several parameters): Hilbert's remark "the truth
of theorem 44 for the general case depends upon whether or not theorem 43 can be generalized",
with the converse. -/
theorem theorem44_iff_generalized_theorem43 :
    Theorem44 ↔ ∀ S : Finset ℝ, Theorem43For (Subfield.closure (S : Set ℝ)) :=
  theorem44_iff_theorem43For

/-- Theorem 44 over a single domain `R` is equivalent to Theorem 43 for `R`. -/
theorem theorem44For_iff (R : Subfield ℝ) : Theorem44For R ↔ Theorem43For R :=
  theorem44For_iff_theorem43For R

/-! ## Definite functions of two variables -/

/-- **Hilbert's theorem on the definite functions of two variables, for a polynomial of degree at
most two in `y`** (towards the unit `s38.two_variables`): if `P(x) y² + Q(x) y + R(x)` never
becomes negative, it is a quotient of two sums of squares of polynomials. -/
theorem twoVariableClaim_quadratic (P Q R : ℝ[X])
    (hf : ∀ x : Fin 2 → ℝ, 0 ≤ MvPolynomial.eval x
      (polyX P * MvPolynomial.X 1 ^ 2 + polyX Q * MvPolynomial.X 1 + polyX R)) :
    ∃ N D : MvPolynomial (Fin 2) ℝ, IsSumSq N ∧ IsSumSq D ∧ D ≠ 0 ∧
      (polyX P * MvPolynomial.X 1 ^ 2 + polyX Q * MvPolynomial.X 1 + polyX R) * D = N :=
  twoVariable_quadratic P Q R hf

/-! ## The problem of Malfatti -/

/-- **The problem of Malfatti** (unit `s39.malfatti`): the circles of Malfatti of every triangle
can be constructed by straight-edge and transferer. -/
theorem malfattiClaim : MalfattiClaim :=
  malfattiClaim_aux

/-! ## The regular polygons -/

/-- A number constructible with the compass lies in a tower of square roots. -/
theorem euclidClosure_tower {x : ℝ} (h : EuclidClosure x) :
    ∃ l : List ℝ, ValidTower l ∧ x ∈ towerField l := by
  induction h with
  | one => exact ⟨[], trivial, (towerField []).one_mem⟩
  | add _ _ iha ihb =>
    obtain ⟨l₁, h₁, ha⟩ := iha
    obtain ⟨l₂, h₂, hb⟩ := ihb
    exact ⟨l₁ ++ l₂, validTower_append h₁ h₂, Subfield.add_mem _
      (towerField_le_append_left _ _ ha) (towerField_le_append_right _ _ hb)⟩
  | sub _ _ iha ihb =>
    obtain ⟨l₁, h₁, ha⟩ := iha
    obtain ⟨l₂, h₂, hb⟩ := ihb
    exact ⟨l₁ ++ l₂, validTower_append h₁ h₂, Subfield.sub_mem _
      (towerField_le_append_left _ _ ha) (towerField_le_append_right _ _ hb)⟩
  | mul _ _ iha ihb =>
    obtain ⟨l₁, h₁, ha⟩ := iha
    obtain ⟨l₂, h₂, hb⟩ := ihb
    exact ⟨l₁ ++ l₂, validTower_append h₁ h₂, Subfield.mul_mem _
      (towerField_le_append_left _ _ ha) (towerField_le_append_right _ _ hb)⟩
  | div _ _ _ iha ihb =>
    obtain ⟨l₁, h₁, ha⟩ := iha
    obtain ⟨l₂, h₂, hb⟩ := ihb
    exact ⟨l₁ ++ l₂, validTower_append h₁ h₂, Subfield.div_mem _
      (towerField_le_append_left _ _ ha) (towerField_le_append_right _ _ hb)⟩
  | sqrt _ h0 ih =>
    obtain ⟨l, hl, ha⟩ := ih
    exact ⟨_ :: l, ⟨hl, ha, h0⟩, Subfield.subset_closure (Or.inr rfl)⟩

/-- **Every totally real number constructible with the compass is constructible by straight-edge
and transferer** (lies in `Ω`): Hilbert's criterion (Theorem 44 without parameters) in the form
used for the regular polygons. -/
theorem euclidClosure_totReal_mem_omega {x : ℝ} (h : EuclidClosure x)
    (hreal : ∀ (l : List ℝ) (hx : x ∈ towerField l) (σ : towerField l →+* ℂ),
      ∃ t : ℝ, σ ⟨x, hx⟩ = (t : ℂ)) : x ∈ Omega := by
  obtain ⟨l, hl, hx⟩ := euclidClosure_tower h
  exact tower_totReal_mem_omega l hl x ⟨hx, hreal l hx⟩

/-- **The regular polygons** (unit `s39.regular_polygons`): if the regular `n`-gon is constructible
with the compass, its vertices are constructible by straight-edge and transferer. -/
theorem regularPolygonsClaim : RegularPolygonsClaim := by
  intro n hn hc k
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by linarith
  have h2 : EuclidClosure 2 := by
    have := EuclidClosure.add .one .one
    norm_num at this
    exact this
  have half : ∀ x : ℝ, -π ≤ x → x ≤ π → EuclidClosure (Real.cos x) →
      EuclidClosure (Real.cos (x / 2)) := by
    intro x h1 h2' hx
    rw [Real.cos_half h1 h2']
    exact .sqrt (.div (.add .one hx) h2 two_ne_zero)
      (by have := Real.neg_one_le_cos x; linarith)
  have hpos : 0 < 2 * π / n := by positivity
  have hle : 2 * π / n ≤ π := by
    rw [div_le_iff₀ hnR]; nlinarith [Real.pi_pos]
  have e1 := half _ (by linarith [Real.pi_pos]) hle hc
  have e2 := half _ (by linarith [Real.pi_pos]) (by linarith) e1
  have e3 : 2 * π / n / 2 / 2 = 2 * π / ((4 * n : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e3] at e2
  obtain ⟨l, hl, hmem⟩ := euclidClosure_tower e2
  exact regular_polygon_of_tower (by omega) hl hmem k

end HilbertFoundations
