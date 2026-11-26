import HilbertFoundations.ConstructionsAux7

/-!
# Helper module for `ConstructionsClose.lean`: definite polynomials are sums of squares

This module contains no unit of Hilbert's text. It proves, by elementary means (no Theorem 42):

* `real_psd_two_sq`: a real polynomial that is nonnegative on `ℝ` is a sum of two squares of real
  polynomials (induction on the degree, with the fundamental theorem of algebra);
* `real_pos_lower_bound`: a real polynomial of degree `2m` that is positive on `ℝ` is bounded
  below by `c (1 + x² + … + x^{2m})` for some `c > 0` (compactness, with the reversed polynomial
  for `|x| ≥ 1`);
* `isSumSq_of_dominant`: a polynomial with rational coefficients of degree `≤ 2m` whose even
  coefficients dominate the odd ones is a sum of squares in `ℚ[x]`;
* `pos_isSumSq`: **a polynomial with rational coefficients that is positive on `ℝ` is a sum of
  squares of polynomials with rational coefficients** (the two real squares of `f - ε Σ x^{2i}` are
  approximated by polynomials with rational coefficients; the remainder is dominant);
* `psd_isSumSq`: the same for a polynomial that is nonnegative on `ℝ` (an irreducible factor with a
  real root divides it twice).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Polynomial

/-! ## Real definite polynomials are sums of two squares -/

/-- A real root of a nonnegative real polynomial is a double root. -/
theorem real_sq_dvd_of_root {f : ℝ[X]} (hf : ∀ x : ℝ, 0 ≤ f.eval x) {r : ℝ} (hr : f.eval r = 0) :
    ∃ h : ℝ[X], f = (X - C r) ^ 2 * h := by
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.2 hr
  have hmin : IsLocalMin (fun x => f.eval x) r :=
    Filter.Eventually.of_forall fun x => by simp only [hr]; exact hf x
  have hd := hmin.deriv_eq_zero
  rw [Polynomial.deriv] at hd
  have hgr : g.eval r = 0 := by
    rw [hg, derivative_mul] at hd
    simpa using hd
  obtain ⟨h, hh⟩ := dvd_iff_isRoot.2 hgr
  exact ⟨h, by rw [hg, hh]; ring⟩

/-- If `(x - r)² h` is nonnegative on `ℝ`, so is `h`. -/
theorem real_psd_of_sq_mul {r : ℝ} {h : ℝ[X]}
    (hf : ∀ x : ℝ, 0 ≤ ((X - C r) ^ 2 * h).eval x) : ∀ x : ℝ, 0 ≤ h.eval x := by
  have hcl : IsClosed {x : ℝ | 0 ≤ h.eval x} := isClosed_le continuous_const h.continuous
  have hsub : ({r}ᶜ : Set ℝ) ⊆ {x : ℝ | 0 ≤ h.eval x} := by
    intro x hx
    have hx' : x - r ≠ 0 := sub_ne_zero.2 hx
    have := hf x
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
    have h2 : 0 < (x - r) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right this h2
  intro x
  exact closure_minimal hsub hcl (dense_compl_singleton r x)

/-- **A real polynomial that is nonnegative on `ℝ` is a sum of two squares.** -/
theorem real_psd_two_sq : ∀ (n : ℕ) (f : ℝ[X]), f.natDegree = n → (∀ x : ℝ, 0 ≤ f.eval x) →
    ∃ a b : ℝ[X], f = a ^ 2 + b ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  by_cases hf0 : f = 0
  · exact ⟨0, 0, by simp [hf0]⟩
  by_cases hd : f.natDegree = 0
  · obtain ⟨c, rfl⟩ := natDegree_eq_zero.1 hd
    have hc : 0 ≤ c := by simpa using hf 0
    exact ⟨C (Real.sqrt c), 0, by rw [← C_pow, Real.sq_sqrt hc]; simp⟩
  have hdeg : 0 < (f.map (algebraMap ℝ ℂ)).degree := by
    rw [degree_map]; exact natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero hd)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz' : aeval z f = 0 := by rwa [IsRoot, eval_map, ← aeval_def] at hz
  by_cases him : z.im = 0
  · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hr : f.eval z.re = 0 := by
      rw [hzr, show ((z.re : ℝ) : ℂ) = algebraMap ℝ ℂ z.re from rfl, aeval_algebraMap_apply] at hz'
      simpa using hz'
    obtain ⟨h, hh⟩ := real_sq_dvd_of_root hf hr
    have hh0 : h ≠ 0 := by rintro rfl; exact hf0 (by rw [hh, mul_zero])
    have hpsd := real_psd_of_sq_mul (hh ▸ hf)
    have hdeg' : h.natDegree < n := by
      rw [← hn, hh, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero _)) hh0, natDegree_pow,
        natDegree_X_sub_C]
      omega
    obtain ⟨a, b, hab⟩ := ih _ hdeg' h rfl hpsd
    exact ⟨(X - C z.re) * a, (X - C z.re) * b, by rw [hh, hab]; ring⟩
  · obtain ⟨g, hg⟩ := f.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz' him
    set q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) with hq
    have hqe : q = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
      rw [hq, Complex.sq_norm, Complex.normSq_apply]
      simp only [map_add, map_mul, map_ofNat]
      ring
    have hqpos : ∀ x : ℝ, 0 < q.eval x := by
      intro x
      rw [hqe]
      simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
      positivity
    have hg0 : g ≠ 0 := by rintro rfl; exact hf0 (by rw [hg, mul_zero])
    have hq0 : q ≠ 0 := by rintro h; have := hqpos 0; rw [h] at this; simp at this
    have hq2 : 2 ≤ q.natDegree := by
      apply le_natDegree_of_ne_zero
      have : q.coeff 2 = 1 := by
        rw [hq]
        simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
        norm_num
      rw [this]; exact one_ne_zero
    have hpsd : ∀ x : ℝ, 0 ≤ g.eval x := by
      intro x
      have := hf x
      rw [hg, eval_mul] at this
      exact nonneg_of_mul_nonneg_right this (hqpos x)
    have hdeg' : g.natDegree < n := by
      rw [← hn, hg, natDegree_mul hq0 hg0]; omega
    obtain ⟨a, b, hab⟩ := ih _ hdeg' g rfl hpsd
    exact ⟨(X - C z.re) * a - C z.im * b, (X - C z.re) * b + C z.im * a, by
      rw [hg, hqe, hab]; ring⟩

/-- The two squares have at most half the degree. -/
theorem natDegree_le_of_sq_add_sq {a b f : ℝ[X]} {m : ℕ} (h : f = a ^ 2 + b ^ 2)
    (hf : f.natDegree ≤ 2 * m) : a.natDegree ≤ m ∧ b.natDegree ≤ m := by
  by_contra hc
  set d := max a.natDegree b.natDegree with hd
  have hdm : m < d := by
    by_contra h'
    push Not at h'
    exact hc ⟨(le_max_left _ _).trans h', (le_max_right _ _).trans h'⟩
  have hco : f.coeff (d + d) = a.coeff d ^ 2 + b.coeff d ^ 2 := by
    rw [h, coeff_add, sq, sq, coeff_mul_add_eq_of_natDegree_le (le_max_left _ _) (le_max_left _ _),
      coeff_mul_add_eq_of_natDegree_le (le_max_right _ _) (le_max_right _ _)]
    ring
  have h0 : f.coeff (d + d) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h0] at hco
  have ha0 : a.coeff d = 0 := by nlinarith [sq_nonneg (a.coeff d), sq_nonneg (b.coeff d)]
  have hb0 : b.coeff d = 0 := by nlinarith [sq_nonneg (a.coeff d), sq_nonneg (b.coeff d)]
  rcases max_choice a.natDegree b.natDegree with e | e
  · rw [hd, e] at ha0
    have : a = 0 := leadingCoeff_eq_zero.1 ha0
    have hda : d = 0 := by rw [hd, e, this, natDegree_zero]
    omega
  · rw [hd, e] at hb0
    have : b = 0 := leadingCoeff_eq_zero.1 hb0
    have hdb : d = 0 := by rw [hd, e, this, natDegree_zero]
    omega

/-! ## A lower bound for a positive polynomial -/

/-- `1 + x² + x⁴ + … + x^{2m}`. -/
noncomputable def evenSum (K : Type*) [Semiring K] (m : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (m + 1), X ^ (2 * i)

theorem evenSum_eval (m : ℕ) (x : ℝ) :
    (evenSum ℝ m).eval x = ∑ i ∈ Finset.range (m + 1), x ^ (2 * i) := by
  simp [evenSum, eval_finsetSum]

theorem evenSum_coeff_even (K : Type*) [Semiring K] {m i : ℕ} (hi : i ≤ m) :
    (evenSum K m).coeff (2 * i) = 1 := by
  rw [evenSum, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [coeff_X_pow, ite_eq_right (by omega)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem evenSum_coeff_odd (K : Type*) [Semiring K] (m j : ℕ) :
    (evenSum K m).coeff (2 * j + 1) = 0 := by
  rw [evenSum, finsetSum_coeff]
  exact Finset.sum_eq_zero fun i _ => by rw [coeff_X_pow, ite_eq_right (by omega)]

theorem evenSum_natDegree_le (K : Type*) [Semiring K] (m : ℕ) :
    (evenSum K m).natDegree ≤ 2 * m := by
  rw [evenSum]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_X_pow_le _).trans (by have := Finset.mem_range.1 hi; omega)

theorem evenSum_map (m : ℕ) : (evenSum ℚ m).map (algebraMap ℚ ℝ) = evenSum ℝ m := by
  simp [evenSum, Polynomial.map_sum]

/-- **A positive polynomial of degree `2m` is bounded below by a positive multiple of
`1 + x² + … + x^{2m}`.** -/
theorem real_pos_lower_bound {f : ℝ[X]} {m : ℕ} (hf : ∀ x : ℝ, 0 < f.eval x)
    (hm : f.natDegree = 2 * m) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, c * (evenSum ℝ m).eval x ≤ f.eval x := by
  have hf0 : f ≠ 0 := by rintro rfl; simpa using hf 0
  have key : ∀ x : ℝ, x ≠ 0 → f.reverse.eval x⁻¹ * x ^ (2 * m) = f.eval x := by
    intro x hx
    let _ := invertibleOfNonzero hx
    have := eval₂_reverse_mul_pow (RingHom.id ℝ) x f
    simpa [eval₂_id, invOf_eq_inv, hm] using this
  have hevpos : ∀ x : ℝ, x ≠ 0 → 0 < x ^ (2 * m) := fun x hx => by
    rw [pow_mul]; have : 0 < x ^ 2 := by positivity
    positivity
  have hrpos : ∀ y : ℝ, 0 < f.reverse.eval y := by
    have hne : ∀ y : ℝ, y ≠ 0 → 0 < f.reverse.eval y := by
      intro y hy
      have := key y⁻¹ (inv_ne_zero hy)
      rw [inv_inv] at this
      have h1 := hf y⁻¹
      rw [← this] at h1
      exact (mul_pos_iff_of_pos_right (hevpos _ (inv_ne_zero hy))).1 h1
    intro y
    by_cases hy : y = 0
    · subst hy
      have h0 : f.reverse.eval 0 = f.leadingCoeff := by
        rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
      have hcl : IsClosed {y : ℝ | 0 ≤ f.reverse.eval y} :=
        isClosed_le continuous_const f.reverse.continuous
      have hge : 0 ≤ f.reverse.eval 0 :=
        closure_minimal (fun y hy => (hne y hy).le) hcl (dense_compl_singleton (0 : ℝ) 0)
      have hne0 : f.reverse.eval 0 ≠ 0 := by rw [h0]; exact leadingCoeff_ne_zero.2 hf0
      exact lt_of_le_of_ne hge (Ne.symm hne0)
    · exact hne y hy
  obtain ⟨x₁, -, h₁⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by simp⟩ f.continuous.continuousOn
  obtain ⟨x₂, -, h₂⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by simp⟩ f.reverse.continuous.continuousOn
  have hmin : 0 < min (f.eval x₁) (f.reverse.eval x₂) := lt_min (hf x₁) (hrpos x₂)
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  refine ⟨min (f.eval x₁) (f.reverse.eval x₂) / (m + 1), by positivity, fun x => ?_⟩
  rw [evenSum_eval]
  by_cases hx : |x| ≤ 1
  · have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 hx
    have h1 : f.eval x₁ ≤ f.eval x := isMinOn_iff.1 h₁ x hx'
    have h2 : ∑ i ∈ Finset.range (m + 1), x ^ (2 * i) ≤ m + 1 := by
      calc ∑ i ∈ Finset.range (m + 1), x ^ (2 * i) ≤ ∑ i ∈ Finset.range (m + 1), (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => by
              rw [pow_mul]
              exact pow_le_one₀ (sq_nonneg x) ((sq_le_one_iff_abs_le_one x).2 hx)
        _ = m + 1 := by simp
    calc min (f.eval x₁) (f.reverse.eval x₂) / (m + 1) * ∑ i ∈ Finset.range (m + 1), x ^ (2 * i)
        ≤ min (f.eval x₁) (f.reverse.eval x₂) / (m + 1) * (m + 1) := by gcongr
      _ = min (f.eval x₁) (f.reverse.eval x₂) := by field_simp
      _ ≤ f.eval x₁ := min_le_left _ _
      _ ≤ _ := h1
  · push Not at hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx; linarith
    have hinv : x⁻¹ ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le, abs_inv]; exact inv_le_one_of_one_le₀ hx.le
    have h1 : f.reverse.eval x₂ ≤ f.reverse.eval x⁻¹ := isMinOn_iff.1 h₂ _ hinv
    have hxm := hevpos x hx0
    have h3 : f.reverse.eval x₂ * x ^ (2 * m) ≤ f.eval x := by rw [← key x hx0]; gcongr
    have hx2 : 1 ≤ x ^ 2 := (one_le_sq_iff_one_le_abs x).2 hx.le
    have h2 : ∑ i ∈ Finset.range (m + 1), x ^ (2 * i) ≤ (m + 1) * x ^ (2 * m) := by
      calc ∑ i ∈ Finset.range (m + 1), x ^ (2 * i)
          ≤ ∑ i ∈ Finset.range (m + 1), x ^ (2 * m) :=
            Finset.sum_le_sum fun i hi => by
              rw [pow_mul, pow_mul]
              exact pow_le_pow_right₀ hx2 (by have := Finset.mem_range.1 hi; omega)
        _ = (m + 1) * x ^ (2 * m) := by simp
    calc min (f.eval x₁) (f.reverse.eval x₂) / (m + 1) * ∑ i ∈ Finset.range (m + 1), x ^ (2 * i)
        ≤ min (f.eval x₁) (f.reverse.eval x₂) / (m + 1) * ((m + 1) * x ^ (2 * m)) := by gcongr
      _ = min (f.eval x₁) (f.reverse.eval x₂) * x ^ (2 * m) := by field_simp
      _ ≤ f.reverse.eval x₂ * x ^ (2 * m) := by gcongr; exact min_le_right _ _
      _ ≤ _ := h3

/-! ## Dominant polynomials are sums of squares -/

theorem isSumSq_C_mul_sq {q : ℚ} (hq : 0 ≤ q) (g : ℚ[X]) : IsSumSq (C q * (g * g)) :=
  (isSumSq_C hq).mul (IsSumSq.mul_self g)

/-- **A polynomial of degree `≤ 2m` whose even coefficients dominate the odd ones is a sum of
squares**: `d x^{2j+1} + (|d|/2)(x^{2j} + x^{2j+2}) = (|d|/2)(x^j ± x^{j+1})²`. -/
theorem isSumSq_of_dominant (η : ℚ) (hη : 0 ≤ η) : ∀ (m : ℕ) (R : ℚ[X]), R.natDegree ≤ 2 * m →
    (∀ j < m, |R.coeff (2 * j + 1)| ≤ 2 * η) → (∀ i < m, 2 * η ≤ R.coeff (2 * i)) →
    η ≤ R.coeff (2 * m) → IsSumSq R := by
  intro m
  induction m with
  | zero =>
    intro R hdeg _ _ h0
    have e := eq_C_of_natDegree_le_zero (p := R) (by simpa using hdeg)
    rw [e]
    exact isSumSq_C (hη.trans (by simpa using h0))
  | succ m ih =>
    intro R hdeg hodd heven htop
    set a := R.coeff (2 * (m + 1)) with ha
    set d := R.coeff (2 * m + 1) with hd
    have hdle : |d| ≤ 2 * η := hodd m (Nat.lt_succ_self m)
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℚ, s * s = 1 ∧ s * |d| = d := by
      rcases le_total 0 d with h | h
      · exact ⟨1, by norm_num, by rw [abs_of_nonneg h, one_mul]⟩
      · exact ⟨-1, by norm_num, by rw [abs_of_nonpos h]; ring⟩
    set R₁ : ℚ[X] := R - C a * X ^ (2 * (m + 1)) - C d * X ^ (2 * m + 1) - C (|d| / 2) * X ^ (2 * m)
      with hR₁
    have hco : ∀ N : ℕ, R₁.coeff N = R.coeff N - (if N = 2 * (m + 1) then a else 0) -
        (if N = 2 * m + 1 then d else 0) - (if N = 2 * m then |d| / 2 else 0) := by
      intro N
      simp only [hR₁, coeff_sub, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    have hdeg₁ : R₁.natDegree ≤ 2 * m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hco]
      by_cases h1 : N = 2 * m + 1
      · subst h1; rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega)]; ring
      by_cases h2 : N = 2 * (m + 1)
      · subst h2; rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega)]; ring
      rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
      ring
    have hR₁sos : IsSumSq R₁ := by
      apply ih R₁ hdeg₁
      · intro j hj
        rw [hco, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        simpa using hodd j (by omega)
      · intro i hi
        rw [hco, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
        simpa using heven i (by omega)
      · rw [hco, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
        have := heven m (Nat.lt_succ_self m)
        have habs := abs_nonneg d
        linarith
    have hcs : (C s : ℚ[X]) * C s = 1 := by rw [← C_mul, hs1, C_1]
    have hd2 : d = 2 * (|d| / 2) * s := by linear_combination (-1 : ℚ) * hs2
    have hcd : (C d : ℚ[X]) = 2 * C (|d| / 2) * C s :=
      (congrArg C hd2).trans (by simp only [map_mul, map_ofNat])
    have hca : (C (a - |d| / 2) : ℚ[X]) = C a - C (|d| / 2) := by simp
    have hrepr : R = R₁ + (C (|d| / 2) * ((X ^ m + C s * X ^ (m + 1)) * (X ^ m + C s * X ^ (m + 1)))
        + C (a - |d| / 2) * (X ^ (m + 1) * X ^ (m + 1))) := by
      rw [hR₁, hca, hcd]
      linear_combination (-(C (|d| / 2) : ℚ[X]) * X ^ (2 * m + 2)) * hcs
    rw [hrepr]
    refine hR₁sos.add ((isSumSq_C_mul_sq (by positivity) _).add (isSumSq_C_mul_sq ?_ _))
    have habs := abs_nonneg d
    linarith


/-! ## Approximation by polynomials with rational coefficients -/

/-- The polynomial `u 0 + u 1 x + … + u m x^m`. -/
noncomputable def polyOf {K : Type*} [Semiring K] (m : ℕ) (u : ℕ → K) : K[X] :=
  ∑ i ∈ Finset.range (m + 1), C (u i) * X ^ i

theorem polyOf_coeff {K : Type*} [Semiring K] (m : ℕ) (u : ℕ → K) (k : ℕ) :
    (polyOf m u).coeff k = if k < m + 1 then u k else 0 := by
  rw [polyOf, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem polyOf_natDegree_le {K : Type*} [Semiring K] (m : ℕ) (u : ℕ → K) :
    (polyOf m u).natDegree ≤ m :=
  natDegree_le_iff_coeff_eq_zero.2 fun N hN => by rw [polyOf_coeff, ite_eq_right (by omega)]

theorem polyOf_coeff_eq {K : Type*} [Semiring K] {m : ℕ} {p : K[X]} (hp : p.natDegree ≤ m) :
    polyOf m p.coeff = p := by
  ext k
  rw [polyOf_coeff]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem polyOf_map (m : ℕ) (u : ℕ → ℚ) :
    (polyOf m u).map (algebraMap ℚ ℝ) = polyOf m (fun i => (u i : ℝ)) := by
  simp [polyOf, Polynomial.map_sum]

theorem continuous_polyOf_coeff (m k : ℕ) :
    Continuous fun u : ℕ → ℝ => (polyOf m u).coeff k := by
  simp only [polyOf_coeff]
  split_ifs
  · exact continuous_apply k
  · exact continuous_const

theorem continuous_polyOf_sq_coeff (m k : ℕ) :
    Continuous fun u : ℕ → ℝ => ((polyOf m u) ^ 2).coeff k := by
  simp only [sq, coeff_mul]
  exact continuous_finsetSum _ fun ij _ =>
    (continuous_polyOf_coeff m ij.1).mul (continuous_polyOf_coeff m ij.2)

/-! ## Positive and definite polynomials with rational coefficients -/

/-- **A polynomial with rational coefficients that is positive on `ℝ` is a sum of squares of
polynomials with rational coefficients.** -/
theorem pos_isSumSq {f : ℚ[X]} (hf : ∀ x : ℝ, 0 < aeval x f) : IsSumSq f := by
  have hpsd : PSD f := fun x => (hf x).le
  have hf0 : f ≠ 0 := by rintro rfl; simpa using hf 0
  obtain ⟨m, hm⟩ := psd_even_natDegree hpsd hf0
  have hm' : f.natDegree = 2 * m := by omega
  set fR := f.map (algebraMap ℚ ℝ) with hfR
  have hfRe : ∀ x : ℝ, fR.eval x = aeval x f := fun x => (aeval_real_eq f x).symm
  have hdegR : fR.natDegree = 2 * m := by rw [hfR, natDegree_map, hm']
  obtain ⟨c, hc, hbound⟩ :=
    real_pos_lower_bound (f := fR) (fun x => by rw [hfRe]; exact hf x) hdegR
  obtain ⟨ε, hε0, hεc⟩ := exists_rat_btwn hc
  have hεR : (0 : ℝ) < ε := hε0
  have hε : 0 < ε := by exact_mod_cast hε0
  set F : ℝ[X] := fR - C (ε : ℝ) * evenSum ℝ m with hF
  have hFpsd : ∀ x : ℝ, 0 ≤ F.eval x := by
    intro x
    rw [hF, eval_sub, eval_mul, eval_C]
    have h1 := hbound x
    have hS : 0 ≤ (evenSum ℝ m).eval x := by
      rw [evenSum_eval]
      exact Finset.sum_nonneg fun i _ => by rw [pow_mul]; positivity
    nlinarith
  have hFdeg : F.natDegree ≤ 2 * m := by
    rw [hF]
    refine (natDegree_sub_le _ _).trans (max_le hdegR.le ?_)
    exact (natDegree_C_mul_le _ _).trans (evenSum_natDegree_le ℝ m)
  obtain ⟨a, b, hab⟩ := real_psd_two_sq _ F rfl hFpsd
  obtain ⟨ha, hb⟩ := natDegree_le_of_sq_add_sq hab hFdeg
  -- the coefficients of the two squares are approximated by rational numbers
  set U : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {w | ∀ k ∈ Finset.range (2 * m + 1),
      |(F - polyOf m w.1 ^ 2 - polyOf m w.2 ^ 2).coeff k| < (ε : ℝ) / 2} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ k ∈ Finset.range (2 * m + 1), {w : (ℕ → ℝ) × (ℕ → ℝ) |
        |(F - polyOf m w.1 ^ 2 - polyOf m w.2 ^ 2).coeff k| < (ε : ℝ) / 2} := by
      ext w; simp [hU]
    rw [this]
    refine isOpen_biInter_finset fun k _ => ?_
    refine isOpen_lt ?_ continuous_const
    refine continuous_abs.comp ?_
    simp only [coeff_sub]
    exact (continuous_const.sub ((continuous_polyOf_sq_coeff m k).comp continuous_fst)).sub
      ((continuous_polyOf_sq_coeff m k).comp continuous_snd)
  have hUne : U.Nonempty := by
    refine ⟨(a.coeff, b.coeff), fun k _ => ?_⟩
    simp only [polyOf_coeff_eq ha, polyOf_coeff_eq hb]
    rw [hab]
    simp only [sub_self, add_sub_cancel_left, coeff_zero, abs_zero]
    positivity
  have hdense : DenseRange (Prod.map (Pi.map fun (_ : ℕ) (q : ℚ) => (q : ℝ))
      (Pi.map fun (_ : ℕ) (q : ℚ) => (q : ℝ))) :=
    (DenseRange.piMap fun _ => Rat.denseRange_cast).prodMap
      (DenseRange.piMap fun _ => Rat.denseRange_cast)
  obtain ⟨⟨p, q⟩, hpq⟩ := hdense.exists_mem_open hUo hUne
  have hδ : ∀ k, k ≤ 2 * m → |(F - polyOf m (fun i => (p i : ℝ)) ^ 2 -
      polyOf m (fun i => (q i : ℝ)) ^ 2).coeff k| < (ε : ℝ) / 2 :=
    fun k hk => hpq k (Finset.mem_range.2 (by omega))
  set R : ℚ[X] := f - polyOf m p ^ 2 - polyOf m q ^ 2 with hR
  have hRmap : R.map (algebraMap ℚ ℝ) = C (ε : ℝ) * evenSum ℝ m +
      (F - polyOf m (fun i => (p i : ℝ)) ^ 2 - polyOf m (fun i => (q i : ℝ)) ^ 2) := by
    rw [hR, hF]
    simp only [Polynomial.map_sub, Polynomial.map_pow, polyOf_map, ← hfR]
    ring
  have hcoR : ∀ k, (R.coeff k : ℝ) = ε * (evenSum ℝ m).coeff k +
      (F - polyOf m (fun i => (p i : ℝ)) ^ 2 - polyOf m (fun i => (q i : ℝ)) ^ 2).coeff k := by
    intro k
    have := congrArg (fun P : ℝ[X] => P.coeff k) hRmap
    simpa only [coeff_map, coeff_add, coeff_C_mul, eq_ratCast] using this
  have hRdeg : R.natDegree ≤ 2 * m := by
    have h2 : ∀ u : ℕ → ℚ, (polyOf m u ^ 2).natDegree ≤ 2 * m := fun u =>
      natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (polyOf_natDegree_le m u))
    rw [hR]
    exact (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
      (max_le hm'.le (h2 p))) (h2 q))
  have hRsos : IsSumSq R := by
    refine isSumSq_of_dominant (ε / 4) (by positivity) m R hRdeg (fun j hj => ?_)
      (fun i hi => ?_) ?_
    · have h1 := hδ (2 * j + 1) (by omega)
      have h2 := hcoR (2 * j + 1)
      rw [evenSum_coeff_odd, mul_zero, zero_add] at h2
      rw [← h2] at h1
      have : ((|R.coeff (2 * j + 1)| : ℚ) : ℝ) ≤ ((2 * (ε / 4) : ℚ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    · have h1 := abs_lt.1 (hδ (2 * i) (by omega))
      have h2 := hcoR (2 * i)
      rw [evenSum_coeff_even ℝ (by omega : i ≤ m), mul_one] at h2
      have : ((2 * (ε / 4) : ℚ) : ℝ) ≤ ((R.coeff (2 * i) : ℚ) : ℝ) := by
        push_cast; linarith [h1.1]
      exact_mod_cast this
    · have h1 := abs_lt.1 (hδ (2 * m) le_rfl)
      have h2 := hcoR (2 * m)
      rw [evenSum_coeff_even ℝ le_rfl, mul_one] at h2
      have : ((ε / 4 : ℚ) : ℝ) ≤ ((R.coeff (2 * m) : ℚ) : ℝ) := by
        push_cast; linarith [h1.1]
      exact_mod_cast this
  have hfe : f = polyOf m p * polyOf m p + (polyOf m q * polyOf m q + R) := by rw [hR]; ring
  rw [hfe]
  exact .sq_add _ (.sq_add _ hRsos)

/-- **A polynomial with rational coefficients that is nonnegative on `ℝ` is a sum of squares of
polynomials with rational coefficients.** -/
theorem psd_isSumSq_aux : ∀ (n : ℕ) (f : ℚ[X]), f.natDegree = n → PSD f → IsSumSq f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  by_cases hf0 : f = 0
  · rw [hf0]; exact .zero
  by_cases hroot : ∃ r : ℝ, aeval r f = 0
  · obtain ⟨r, hr⟩ := hroot
    have hint : IsIntegral ℚ r := isAlgebraic_iff_isIntegral.1 ⟨f, hf0, hr⟩
    have hp := minpoly.irreducible hint
    obtain ⟨g', hg'⟩ := sq_dvd_of_real_root hf hp (minpoly.dvd ℚ r hr) (minpoly.aeval ℚ r)
    have hp0 := hp.ne_zero
    have hg'0 : g' ≠ 0 := by rintro rfl; rw [mul_zero] at hg'; exact hf0 hg'
    have hg'psd : PSD g' := psd_of_sq_mul hp0 (hg' ▸ hf)
    have hpd : 0 < (minpoly ℚ r).natDegree :=
      natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hp)
    have hdeg : g'.natDegree < n := by
      rw [← hn, hg', natDegree_mul (pow_ne_zero 2 hp0) hg'0, natDegree_pow]; omega
    have := ih _ hdeg g' rfl hg'psd
    rw [hg', sq]
    exact (IsSumSq.mul_self _).mul this
  · push Not at hroot
    exact pos_isSumSq fun x => lt_of_le_of_ne (hf x) (Ne.symm (hroot x))

theorem psd_isSumSq {f : ℚ[X]} (hf : PSD f) : IsSumSq f := psd_isSumSq_aux _ f rfl hf

end HilbertFoundations
