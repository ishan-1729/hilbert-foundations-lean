import HilbertFoundations.ConstructionsAux6

/-!
# Helper module for `Constructions.lean`: sums of squares (§ 38)

This module contains no unit of Hilbert's text. It formalizes the statements of Theorems 42 and 43
and proves:

* `theorem42_rat`, `theorem42_of_sq_eq_neg_one`, `totallyPositive_of_sum_sq`: Theorem 42 for `ℚ`
  (Lagrange's four-square theorem) and for fields containing `√-1`, and the necessity of total
  positivity;
* `psd_even_natDegree`: a nonzero definite polynomial has even degree;
* `sq_dvd_of_real_root`, `definite_sign`: Hilbert's dichotomy for an irreducible factor of a
  definite polynomial;
* `theorem43_of_negOneSumSq`, `theorem42_imp_theorem43`: **Hilbert's proof of Theorem 43 from
  Theorem 42**, by induction on the degree;
* `theorem43_natDegree_le_two`: Theorem 43 for polynomials of degree at most `2`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Polynomial

/-! ## Theorem 42 -/

/-- Hilbert's **totally positive** numbers of a field `k`: positive under every embedding of `k`
into `ℂ` with real image (every number, if there is no such embedding). -/
def TotallyPositive {k : Type*} [Field k] (α : k) : Prop :=
  ∀ σ : k →+* ℂ, (∀ x : k, (σ x).im = 0) → 0 < (σ α).re

/-- **Theorem 42** (Hilbert's statement, proved by Siegel in 1921): in every number field, every
totally positive number is a sum of four squares of numbers of the field. -/
def Theorem42 : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (α : k), TotallyPositive α →
    ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

/-- A nonnegative rational number is a sum of four squares of rational numbers (Lagrange). -/
theorem rat_sum_four_sq {q : ℚ} (hq : 0 ≤ q) : ∃ a b c d : ℚ, q = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = q.num := ⟨q.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)⟩
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (n * q.den)
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  refine ⟨a / q.den, b / q.den, c / q.den, d / q.den, ?_⟩
  have h' : (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n * q.den := by exact_mod_cast h
  have key : q * (q.den : ℚ) ^ 2 = (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    rw [h', show q * (q.den : ℚ) ^ 2 = (q * q.den) * q.den by ring, Rat.mul_den_eq_num, ← hn]
    push_cast; ring
  rw [div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div, ← add_div,
    eq_div_iff (pow_ne_zero 2 hd)]
  exact key

/-- **Theorem 42 for `ℚ`**: the only embedding of `ℚ` is real, so the totally positive rational
numbers are the positive ones, and they are sums of four squares. -/
theorem theorem42_rat (α : ℚ) (h : TotallyPositive α) :
    ∃ a b c d : ℚ, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  have h0 := h (Rat.castHom ℂ) (fun x => by simp)
  have : 0 < α := by simpa using h0
  exact rat_sum_four_sq this.le

/-- **Theorem 42 for fields containing `√-1`** (of characteristic `≠ 2`): every number is a sum of
two squares, `α = ((α + 1)/2)² + (i (α - 1)/2)²`. -/
theorem theorem42_of_sq_eq_neg_one {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {i : k}
    (hi : i ^ 2 = -1) (α : k) : ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨(α + 1) / 2, i * (α - 1) / 2, 0, 0, ?_⟩
  field_simp
  linear_combination (-(α - 1) ^ 2) * hi

/-- The condition of Theorem 42 is necessary: a nonzero sum of squares is totally positive. -/
theorem totallyPositive_of_sum_sq {k : Type*} [Field k] {α a b c d : k} (hα : α ≠ 0)
    (h : α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) : TotallyPositive α := by
  intro σ hσ
  have hreal : ∀ x : k, σ x = ((σ x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [hσ x])
  have hval : (σ α).re = (σ a).re ^ 2 + (σ b).re ^ 2 + (σ c).re ^ 2 + (σ d).re ^ 2 := by
    rw [h, map_add, map_add, map_add, map_pow, map_pow, map_pow, map_pow, hreal a, hreal b,
      hreal c, hreal d]
    simp [← Complex.ofReal_pow]
  have hne : (σ α).re ≠ 0 := by
    intro h0
    have : σ α = 0 := by rw [hreal α, h0]; simp
    exact hα ((map_eq_zero σ).1 this)
  have : 0 ≤ (σ α).re := by rw [hval]; positivity
  exact lt_of_le_of_ne this (Ne.symm hne)

/-! ## Definite polynomials -/

/-- A polynomial with rational coefficients that **never becomes negative** for real `x`. -/
def PSD (f : ℚ[X]) : Prop := ∀ x : ℝ, 0 ≤ aeval x f

/-- `f` is the **quotient of two sums of squares** of polynomials with rational coefficients:
`f · D = N` with `N`, `D` sums of squares and `D ≠ 0`. -/
def RepQSOS (f : ℚ[X]) : Prop :=
  ∃ N D : ℚ[X], IsSumSq N ∧ IsSumSq D ∧ D ≠ 0 ∧ f * D = N

/-- **Theorem 43**: every polynomial with rational coefficients that never becomes negative for
real `x` is a quotient of two sums of squares of polynomials with rational coefficients. -/
def Theorem43 : Prop := ∀ f : ℚ[X], PSD f → RepQSOS f

theorem isSumSq_C {q : ℚ} (hq : 0 ≤ q) : IsSumSq (C q : ℚ[X]) := by
  obtain ⟨a, b, c, d, rfl⟩ := rat_sum_four_sq hq
  have e : (C (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) : ℚ[X]) =
      C a * C a + (C b * C b + (C c * C c + (C d * C d + 0))) := by
    simp only [map_add, map_pow, add_zero]; ring
  rw [e]
  exact .sq_add _ (.sq_add _ (.sq_add _ (.sq_add _ .zero)))

theorem aeval_real_eq (f : ℚ[X]) (x : ℝ) : aeval x f = (f.map (algebraMap ℚ ℝ)).eval x := by
  rw [aeval_def, eval_map]

/-- A definite polynomial vanishing at `r` has a vanishing derivative there (`r` is a minimum). -/
theorem psd_derivative_eq_zero {f : ℚ[X]} (hf : PSD f) {r : ℝ} (hr : aeval r f = 0) :
    aeval r (derivative f) = 0 := by
  have hmin : IsLocalMin (fun x => (f.map (algebraMap ℚ ℝ)).eval x) r := by
    refine Filter.Eventually.of_forall fun x => ?_
    simp only
    rw [← aeval_real_eq, ← aeval_real_eq, hr]; exact hf x
  have := hmin.deriv_eq_zero
  rw [Polynomial.deriv, derivative_map, eval_map, ← aeval_def] at this
  exact this

/-- **Hilbert's dichotomy, first case**: an irreducible factor `p` of a definite `f` that has a
real root divides `f` twice. -/
theorem sq_dvd_of_real_root {f p : ℚ[X]} (hf : PSD f) (hp : Irreducible p) (hpf : p ∣ f) {r : ℝ}
    (hr : aeval r p = 0) : p ^ 2 ∣ f := by
  obtain ⟨g, rfl⟩ := hpf
  have hfr : aeval r (p * g) = 0 := by rw [map_mul, hr, zero_mul]
  have hd := psd_derivative_eq_zero hf hfr
  rw [derivative_mul, map_add, map_mul, map_mul, hr, zero_mul, add_zero] at hd
  have hsep : p.Separable := PerfectField.separable_of_irreducible hp
  have hpd := hsep.aeval_derivative_ne_zero hr
  have hgr : aeval r g = 0 := (mul_eq_zero.1 hd).resolve_left hpd
  have hmin := minpoly.dvd ℚ r hgr
  rw [← minpoly.eq_of_irreducible hp hr] at hmin
  obtain ⟨g', hg'⟩ := (dvd_mul_right p _).trans hmin
  exact ⟨g', by rw [hg']; ring⟩

/-- A polynomial without real roots has a constant sign (intermediate value theorem). -/
theorem definite_sign {p : ℚ[X]} (h : ∀ x : ℝ, aeval x p ≠ 0) :
    (∀ x : ℝ, 0 < aeval x p) ∨ ∀ x : ℝ, aeval x p < 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hc
  have hcont : Continuous fun t : ℝ => aeval t p := by
    simp_rw [aeval_real_eq]; exact (p.map (algebraMap ℚ ℝ)).continuous
  have hx' : aeval x p < 0 := lt_of_le_of_ne hx (h x)
  have hy' : 0 < aeval y p := lt_of_le_of_ne hy (Ne.symm (h y))
  obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (Set.mem_univ x) (Set.mem_univ y)
    hcont.continuousOn ⟨hx'.le, hy'.le⟩
  exact h z hz

/-- If `p² g` is definite, so is `g`. -/
theorem psd_of_sq_mul {p g : ℚ[X]} (hp : p ≠ 0) (hf : PSD (p ^ 2 * g)) : PSD g := by
  intro x
  by_contra hneg
  push Not at hneg
  have hcont : Continuous fun t : ℝ => aeval t g := by
    simp_rw [aeval_real_eq]; exact (g.map (algebraMap ℚ ℝ)).continuous
  have hopen : IsOpen {t : ℝ | aeval t g < 0} := isOpen_lt hcont continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x hneg
  have hinf : (Set.Ioo (x - ε) (x + ε)).Infinite := Set.Ioo_infinite (by linarith)
  have hpm : p.map (algebraMap ℚ ℝ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℚ ℝ).injective).2 hp
  have hfin : {t : ℝ | aeval t p = 0}.Finite := by
    refine (p.map (algebraMap ℚ ℝ)).roots.toFinset.finite_toSet.subset fun t ht => ?_
    change aeval t p = 0 at ht
    rw [aeval_real_eq] at ht
    simp [mem_roots hpm, ht]
  obtain ⟨t, ht, htp⟩ := (hinf.sdiff hfin).nonempty
  have hgt : aeval t g < 0 := hball (by rwa [← Real.ball_eq_Ioo] at ht)
  have hpt : aeval t p ≠ 0 := htp
  have := hf t
  rw [map_mul, map_pow] at this
  have h2 : 0 < aeval t p ^ 2 := by positivity
  nlinarith

/-- **A nonzero definite polynomial has even degree** (§ 38: "which, in any case, must evidently
be even"). -/
theorem psd_even_natDegree {f : ℚ[X]} (hf : PSD f) (hf0 : f ≠ 0) : Even f.natDegree := by
  set q := f.map (algebraMap ℚ ℝ) with hq
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).2 hf0
  have hdeg : q.natDegree = f.natDegree := natDegree_map _
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hpos : 0 < q.degree := by
    rw [degree_eq_natDegree hq0, hdeg]; exact_mod_cast hodd.pos
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hval : ∀ x : ℝ, 0 ≤ q.eval x := fun x => by rw [hq, ← aeval_real_eq]; exact hf x
  rcases lt_or_gt_of_ne hlc with hneg | hpos'
  · obtain ⟨x, hx⟩ := ((tendsto_atBot_of_leadingCoeff_nonpos hpos hneg.le).eventually
      (Filter.eventually_lt_atBot 0)).exists
    exact absurd (hval x) (not_le.2 hx)
  · set r := q.comp (-X) with hr
    have hrd : r.natDegree = q.natDegree := by
      rw [hr, natDegree_comp]; simp
    have hrlc : r.leadingCoeff = q.leadingCoeff * (-1) ^ q.natDegree := by
      rw [hr, leadingCoeff_comp (by simp)]; simp
    have hr0 : r ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hrlc
      have : q.leadingCoeff * (-1) ^ q.natDegree ≠ 0 := mul_ne_zero hlc (by simp)
      exact this hrlc.symm
    have hrpos : 0 < r.degree := by
      rw [degree_eq_natDegree hr0, hrd, hdeg]; exact_mod_cast hodd.pos
    have hrneg : r.leadingCoeff ≤ 0 := by
      rw [hrlc, hdeg, hodd.neg_one_pow]; linarith
    obtain ⟨x, hx⟩ := ((tendsto_atBot_of_leadingCoeff_nonpos hrpos hrneg).eventually
      (Filter.eventually_lt_atBot 0)).exists
    have : r.eval x = q.eval (-x) := by rw [hr, eval_comp]; simp
    rw [this] at hx
    exact absurd (hval (-x)) (not_le.2 hx)

/-! ## Hilbert's proof of Theorem 43 from Theorem 42 -/

/-- The consequence of Theorem 42 used in Hilbert's proof: for an irreducible polynomial `p`
without real roots, `-1` is a sum of four squares in the field `ℚ[x]/(p)` (all of whose conjugate
fields are imaginary). -/
def NegOneSumSq : Prop :=
  ∀ p : ℚ[X], Irreducible p → (∀ x : ℝ, aeval x p ≠ 0) →
    ∃ a b c d : AdjoinRoot p, (-1 : AdjoinRoot p) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2

theorem natDegree_sq_le {φ : ℚ[X]} {m : ℕ} (h : φ.natDegree ≤ m) : (φ ^ 2).natDegree ≤ 2 * m :=
  (natDegree_pow_le).trans (by omega)

/-- **Hilbert's step for an irreducible definite polynomial** `p` of degree `m`: from
`-1 = α² + β² + γ² + δ²` in `ℚ(θ)`, `F = 1 + φ² + ψ² + χ² + ρ²` (degree `≤ 2m - 2`) is divisible
by `p`, `F/p` is definite of degree `≤ m - 2`, and `p = F / (F/p)`. -/
theorem rep_irreducible_pos (hyp : NegOneSumSq) {p : ℚ[X]} (hp : Irreducible p)
    (hpos : ∀ x : ℝ, 0 < aeval x p)
    (ih : ∀ g : ℚ[X], g.natDegree < p.natDegree → PSD g → RepQSOS g) : RepQSOS p := by
  obtain ⟨a, b, c, d, habcd⟩ := hyp p hp (fun x => (hpos x).ne')
  have hp0 : p ≠ 0 := hp.ne_zero
  have hm : p.natDegree ≠ 0 := by
    intro h; exact hp.not_isUnit (isUnit_iff_degree_eq_zero.2 (by
      rw [degree_eq_natDegree hp0, h]; rfl))
  obtain ⟨φ₁, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨φ₂, rfl⟩ := AdjoinRoot.mk_surjective b
  obtain ⟨φ₃, rfl⟩ := AdjoinRoot.mk_surjective c
  obtain ⟨φ₄, rfl⟩ := AdjoinRoot.mk_surjective d
  have hmod : ∀ φ : ℚ[X], AdjoinRoot.mk p (φ % p) = AdjoinRoot.mk p φ := by
    intro φ
    rw [EuclideanDomain.mod_eq_sub_mul_div, map_sub, map_mul, AdjoinRoot.mk_self, zero_mul,
      sub_zero]
  have hdeg : ∀ φ : ℚ[X], (φ % p).natDegree ≤ p.natDegree - 1 := fun φ => by
    have := natDegree_mod_lt φ hm; omega
  set F : ℚ[X] := 1 + (φ₁ % p) ^ 2 + (φ₂ % p) ^ 2 + (φ₃ % p) ^ 2 + (φ₄ % p) ^ 2 with hF
  have hpF : p ∣ F := by
    rw [← AdjoinRoot.mk_eq_zero, hF]
    simp only [map_add, map_one, map_pow, hmod]
    linear_combination (-1 : AdjoinRoot p) * habcd
  obtain ⟨G, hG⟩ := hpF
  have hFsos : IsSumSq F := by
    rw [hF]
    have e : 1 + (φ₁ % p) ^ 2 + (φ₂ % p) ^ 2 + (φ₃ % p) ^ 2 + (φ₄ % p) ^ 2 =
        (φ₁ % p) * (φ₁ % p) + ((φ₂ % p) * (φ₂ % p) + ((φ₃ % p) * (φ₃ % p) +
          ((φ₄ % p) * (φ₄ % p) + (1 * 1 + 0)))) := by ring
    rw [e]; exact .sq_add _ (.sq_add _ (.sq_add _ (.sq_add _ (.sq_add _ .zero))))
  have hFpos : ∀ x : ℝ, 0 < aeval x F := fun x => by
    rw [hF]; simp only [map_add, map_one, map_pow]; positivity
  have hG0 : G ≠ 0 := by
    rintro rfl; have := hFpos 0; rw [hG, mul_zero, map_zero] at this; exact lt_irrefl _ this
  have hGpsd : PSD G := fun x => by
    have h1 := hFpos x
    rw [hG, map_mul] at h1
    exact (pos_of_mul_pos_right h1 (hpos x).le).le
  have hFdeg : F.natDegree ≤ 2 * (p.natDegree - 1) := by
    rw [hF]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_))
      ?_)) ?_)
    · simp
    all_goals exact natDegree_sq_le (hdeg _)
  have hGdeg : G.natDegree < p.natDegree := by
    have := natDegree_mul hp0 hG0
    rw [← hG] at this; omega
  obtain ⟨N, D, hN, hD, hD0, hND⟩ := ih G hGdeg hGpsd
  refine ⟨F * D, N, hFsos.mul hD, hN, ?_, ?_⟩
  · rw [← hND]; exact mul_ne_zero hG0 hD0
  · rw [← hND, hG]; ring

/-- The representation for a product `p g` with `p` irreducible and positive. -/
theorem rep_mul_of_pos (hyp : NegOneSumSq) {p g : ℚ[X]} (hp : Irreducible p)
    (hpos : ∀ x : ℝ, 0 < aeval x p) (hf : PSD (p * g))
    (ih : ∀ h : ℚ[X], h.natDegree < (p * g).natDegree → PSD h → RepQSOS h)
    (hg0 : g ≠ 0) : RepQSOS (p * g) := by
  have hp0 := hp.ne_zero
  have hdeg := natDegree_mul hp0 hg0
  have hpd : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hp)
  have hgpsd : PSD g := fun x => by
    have := hf x; rw [map_mul] at this
    exact nonneg_of_mul_nonneg_right (by linarith) (hpos x)
  obtain ⟨N₁, D₁, hN₁, hD₁, hD₁0, e₁⟩ :=
    rep_irreducible_pos hyp hp hpos (fun h hh hp' => ih h (by omega) hp')
  obtain ⟨N₂, D₂, hN₂, hD₂, hD₂0, e₂⟩ := ih g (by omega) hgpsd
  exact ⟨N₁ * N₂, D₁ * D₂, hN₁.mul hN₂, hD₁.mul hD₂, mul_ne_zero hD₁0 hD₂0, by
    rw [← e₁, ← e₂]; ring⟩

/-- **Hilbert's proof of Theorem 43**, by induction on the degree, from the consequence
`NegOneSumSq` of Theorem 42. -/
theorem theorem43_of_negOneSumSq (hyp : NegOneSumSq) : Theorem43 := by
  suffices ∀ n : ℕ, ∀ f : ℚ[X], f.natDegree = n → PSD f → RepQSOS f from
    fun f hf => this _ f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  have ih' : ∀ h : ℚ[X], h.natDegree < f.natDegree → PSD h → RepQSOS h :=
    fun h hh hp => ih _ (hn ▸ hh) h rfl hp
  by_cases hf0 : f = 0
  · exact ⟨0, 1, .zero, by simp, one_ne_zero, by simp [hf0]⟩
  by_cases hunit : IsUnit f
  · -- a positive constant
    obtain ⟨c, hc, rfl⟩ : ∃ c : ℚ, c ≠ 0 ∧ f = C c := by
      obtain ⟨c, hc, e⟩ := Polynomial.isUnit_iff.1 hunit
      exact ⟨c, hc.ne_zero, e.symm⟩
    have hc0 : 0 ≤ c := by have := hf 0; simpa using this
    exact ⟨C c, 1, isSumSq_C hc0, by simp, one_ne_zero,
      mul_one _⟩
  obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor hunit hf0
  obtain ⟨g, rfl⟩ := hpf
  have hp0 := hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; exact hf0 (mul_zero p)
  have hpd : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hp)
  by_cases hroot : ∃ r : ℝ, aeval r p = 0
  · obtain ⟨r, hr⟩ := hroot
    obtain ⟨g', hg'⟩ := sq_dvd_of_real_root hf hp (dvd_mul_right p g) hr
    have hg'0 : g' ≠ 0 := by rintro rfl; rw [mul_zero] at hg'; exact hf0 hg'
    have hg'psd : PSD g' := psd_of_sq_mul hp0 (hg' ▸ hf)
    have hdeg : g'.natDegree < (p * g).natDegree := by
      rw [hg', natDegree_mul (pow_ne_zero 2 hp0) hg'0, natDegree_pow]; omega
    obtain ⟨N, D, hN, hD, hD0, e⟩ := ih' g' hdeg hg'psd
    exact ⟨p * p * N, D, (IsSumSq.mul_self p).mul hN, hD, hD0, by rw [hg', ← e]; ring⟩
  · push Not at hroot
    rcases definite_sign hroot with hpos | hneg
    · exact rep_mul_of_pos hyp hp hpos hf ih' hg0
    · have e : p * g = (-p) * (-g) := by ring
      rw [e] at hf ih' ⊢
      have hassoc : Associated p (-p) := ⟨-1, by simp⟩
      exact rep_mul_of_pos hyp (hassoc.irreducible hp) (fun x => by simpa using hneg x) hf ih'
        (neg_ne_zero.2 hg0)

/-- Theorem 42 gives the hypothesis of Hilbert's proof: `ℚ[x]/(p)`, for `p` irreducible without
real roots, is a number field none of whose conjugate fields is real, so `-1` is totally positive
in it. -/
theorem negOneSumSq_of_theorem42 (h42 : Theorem42) : NegOneSumSq := by
  intro p hp hroot
  have : Fact (Irreducible p) := ⟨hp⟩
  have hp0 := hp.ne_zero
  have : FiniteDimensional ℚ (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have : NumberField (AdjoinRoot p) := ⟨⟩
  apply h42
  intro σ hσ
  exfalso
  set z := σ (AdjoinRoot.root p)
  have hz : aeval z p = 0 := by
    have h1 : σ (eval₂ (AdjoinRoot.of p) (AdjoinRoot.root p) p) = 0 := by
      rw [AdjoinRoot.eval₂_root, map_zero]
    rw [hom_eval₂] at h1
    have h2 : σ.comp (AdjoinRoot.of p) = algebraMap ℚ ℂ := RingHom.ext_rat _ _
    rw [h2] at h1
    rw [aeval_def]; exact h1
  have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [z, hσ])
  apply hroot z.re
  have : aeval ((z.re : ℝ) : ℂ) p = 0 := by rw [← hzr]; exact hz
  rw [show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl, aeval_algebraMap_apply] at this
  exact (map_eq_zero _).1 this

/-- **Theorem 42 implies Theorem 43** (Hilbert's proof). -/
theorem theorem42_imp_theorem43 (h42 : Theorem42) : Theorem43 :=
  theorem43_of_negOneSumSq (negOneSumSq_of_theorem42 h42)

/-- **Theorem 43 for degree at most 2**: `4a f = (2ax + b)² + (4ac - b²)`. -/
theorem theorem43_natDegree_le_two {f : ℚ[X]} (hf : PSD f) (hd : f.natDegree ≤ 2) :
    RepQSOS f := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : ℚ, f = C a * X ^ 2 + C b * X + C c := by
    refine ⟨f.coeff 2, f.coeff 1, f.coeff 0, ?_⟩
    ext n
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    rcases n with _ | _ | _ | n
    · simp
    · simp
    · simp
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  have hval : ∀ x : ℝ, 0 ≤ (a : ℝ) * x ^ 2 + b * x + c := fun x => by
    have := hf x; simpa using this
  have ha : 0 ≤ a := by
    by_contra ha; push Not at ha
    have ha' : (a : ℝ) < 0 := by exact_mod_cast ha
    set t := (|(b : ℝ)| + |(c : ℝ)| + 1) / (-(a : ℝ)) + 1 with ht
    have hf := hval t
    have ht1 : (a : ℝ) * t = -(|(b : ℝ)| + |(c : ℝ)| + 1) + a := by
      have ha0 : (a : ℝ) ≠ 0 := ha'.ne
      rw [ht]; field_simp
    have ht2 : 1 ≤ t := by
      have : 0 ≤ (|(b : ℝ)| + |(c : ℝ)| + 1) / (-(a : ℝ)) :=
        div_nonneg (by positivity) (by linarith)
      linarith
    have hbt : (b : ℝ) ≤ |(b : ℝ)| := le_abs_self _
    have hct : (c : ℝ) ≤ |(c : ℝ)| := le_abs_self _
    have h1 : (a : ℝ) * t + b ≤ -|(c : ℝ)| - 1 := by linarith
    have h3 : t * ((a : ℝ) * t + b) ≤ (a : ℝ) * t + b := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht2) (show 0 ≤ -((a : ℝ) * t + b) by
        linarith [abs_nonneg (c : ℝ)])]
    have : (a : ℝ) * t ^ 2 + b * t + c = t * ((a : ℝ) * t + b) + c := by ring
    linarith
  rcases ha.lt_or_eq with ha | rfl
  · have hdisc : 0 ≤ 4 * a * c - b ^ 2 := by
      have := hval (-(b : ℝ) / (2 * a))
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have h : ((4 * a * c - b ^ 2 : ℚ) : ℝ) = 4 * a * ((a : ℝ) * (-(b : ℝ) / (2 * a)) ^ 2 +
          b * (-(b : ℝ) / (2 * a)) + c) := by push_cast; field_simp; ring
      have : (0 : ℝ) ≤ ((4 * a * c - b ^ 2 : ℚ) : ℝ) := by rw [h]; positivity
      exact_mod_cast this
    refine ⟨(C (2 * a) * X + C b) * (C (2 * a) * X + C b) + C (4 * a * c - b ^ 2), C (4 * a),
      .sq_add _ (isSumSq_C hdisc), isSumSq_C (by linarith), by simp [ha.ne'], ?_⟩
    simp only [map_mul, map_sub, map_pow, map_ofNat]; ring
  · -- `a = 0`: then `b = 0` and `c ≥ 0`
    have hb : b = 0 := by
      by_contra hb
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have := hval ((-(c : ℝ) - 1) / b)
      rw [show ((0 : ℚ) : ℝ) * ((-(c : ℝ) - 1) / b) ^ 2 + b * ((-(c : ℝ) - 1) / b) + c = -1 by
        push_cast; field_simp; ring] at this
      linarith
    subst hb
    have hc : 0 ≤ c := by have := hval 0; simpa using this
    exact ⟨C c, 1, isSumSq_C hc, by simp, one_ne_zero, by
      simp⟩

end HilbertFoundations
