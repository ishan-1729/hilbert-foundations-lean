import HilbertFoundations.Constructions
import HilbertFoundations.ConstructionsCloseAux
import HilbertFoundations.ConstructionsCloseAux5

/-!
# Helper module for `ConstructionsClose.lean`: definite functions of two variables, quadratic case

This module contains no unit of Hilbert's text. It proves Hilbert's claim on the definite
polynomials of two variables (unit `s38.two_variables`, `TwoVariableClaim`, which stays open) in
the special case of a polynomial of degree at most `2` in one of the variables:

`f = P(x) y² + Q(x) y + R(x) ≥ 0` on `ℝ²` implies `f · D = N` with sums of squares `N`, `D ≠ 0`.

Then `P ≥ 0` and `4 P R - Q² ≥ 0` on `ℝ`, both are sums of two squares of real polynomials
(`real_psd_two_sq`), and `4 P f = (2 P y + Q)² + (4 P R - Q²)`. The denominator `4 P` is in general
not constant.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace HilbertFoundations

open Polynomial

/-- The polynomials in the first variable. -/
noncomputable def polyX : ℝ[X] →+* MvPolynomial (Fin 2) ℝ :=
  (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ)).toRingHom

theorem eval_polyX (x : Fin 2 → ℝ) (A : ℝ[X]) :
    MvPolynomial.eval x (polyX A) = A.eval (x 0) := by
  show MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0) A) = A.eval (x 0)
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  have h : (MvPolynomial.eval x).comp (algebraMap ℝ (MvPolynomial (Fin 2) ℝ)) = RingHom.id ℝ := by
    ext r; simp
  rw [h, MvPolynomial.eval_X, Polynomial.eval₂_id]

/-- **Hilbert's theorem on definite functions of two variables, for a polynomial of degree at most
two in `y`**: if `P(x) y² + Q(x) y + R(x)` never becomes negative, it is a quotient of two sums of
squares of polynomials. -/
theorem twoVariable_quadratic (P Q R : ℝ[X])
    (hf : ∀ x : Fin 2 → ℝ, 0 ≤ MvPolynomial.eval x
      (polyX P * MvPolynomial.X 1 ^ 2 + polyX Q * MvPolynomial.X 1 + polyX R)) :
    ∃ N D : MvPolynomial (Fin 2) ℝ, IsSumSq N ∧ IsSumSq D ∧ D ≠ 0 ∧
      (polyX P * MvPolynomial.X 1 ^ 2 + polyX Q * MvPolynomial.X 1 + polyX R) * D = N := by
  have hval : ∀ a b : ℝ, 0 ≤ P.eval a * b ^ 2 + Q.eval a * b + R.eval a := by
    intro a b
    have := hf ![a, b]
    simpa [eval_polyX] using this
  -- the leading coefficient never becomes negative
  have hP : ∀ a : ℝ, 0 ≤ P.eval a := by
    intro a
    by_contra hneg
    push Not at hneg
    obtain ⟨α, hα⟩ : ∃ α : ℝ, α = -P.eval a := ⟨_, rfl⟩
    have hαpos : 0 < α := by linarith
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |Q.eval a| + |R.eval a| + 1 := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = s / α + 1 := ⟨_, rfl⟩
    have hb1 : 1 ≤ b := by
      have : 0 ≤ s / α := by positivity
      linarith
    have hαb : s ≤ α * b := by
      have : α * b = s + α := by rw [hb, mul_add, mul_one, mul_comm, div_mul_cancel₀ _ hαpos.ne']
      linarith
    have h := hval a b
    have h1 : Q.eval a * b ≤ |Q.eval a| * b :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h2 : R.eval a ≤ |R.eval a| := le_abs_self _
    have h3 : s * b ≤ α * b * b := mul_le_mul_of_nonneg_right hαb (by linarith)
    have h4 : |R.eval a| ≤ |R.eval a| * b := le_mul_of_one_le_right (abs_nonneg _) hb1
    have h5 : P.eval a * b ^ 2 = -(α * b * b) := by rw [hα]; ring
    have h6 : s * b = |Q.eval a| * b + |R.eval a| * b + b := by rw [hs]; ring
    linarith
  -- where the leading coefficient vanishes, so does the middle one
  have hQ0 : ∀ a : ℝ, P.eval a = 0 → Q.eval a = 0 := by
    intro a hP0
    by_contra hQ
    have h := hval a (-(R.eval a + 1) / Q.eval a)
    have e : Q.eval a * (-(R.eval a + 1) / Q.eval a) = -(R.eval a + 1) := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hQ
    rw [hP0, zero_mul, zero_add, e] at h
    linarith
  -- the discriminant
  have eΔ : ∀ a : ℝ, (4 * P * R - Q ^ 2 : ℝ[X]).eval a =
      4 * P.eval a * R.eval a - Q.eval a ^ 2 := fun a => by simp
  have hΔ : ∀ a : ℝ, 0 ≤ (4 * P * R - Q ^ 2 : ℝ[X]).eval a := by
    intro a
    rw [eΔ]
    rcases (hP a).lt_or_eq with hpos | hzero
    · have h := hval a (-(Q.eval a) / (2 * P.eval a))
      have hne : P.eval a ≠ 0 := hpos.ne'
      have e : P.eval a * (-(Q.eval a) / (2 * P.eval a)) ^ 2 +
          Q.eval a * (-(Q.eval a) / (2 * P.eval a)) + R.eval a =
          (4 * P.eval a * R.eval a - Q.eval a ^ 2) / (4 * P.eval a) := by
        field_simp
        ring
      rw [e] at h
      by_contra hc
      push Not at hc
      have := div_neg_of_neg_of_pos hc (by linarith : (0 : ℝ) < 4 * P.eval a)
      linarith
    · have hQ := hQ0 a hzero.symm
      rw [← hzero, hQ]
      norm_num
  obtain ⟨k, l, hkl⟩ := real_psd_two_sq _ (4 * P * R - Q ^ 2) rfl hΔ
  have e1 : polyX k * polyX k + polyX l * polyX l = 4 * polyX P * polyX R - polyX Q ^ 2 := by
    have h := congrArg polyX hkl
    simp only [map_sub, map_mul, map_pow, map_add, map_ofNat] at h
    rw [h]; ring
  by_cases hP0 : P = 0
  · have hQ : Q = 0 := by
      apply Polynomial.funext
      intro a
      rw [Polynomial.eval_zero]
      exact hQ0 a (by rw [hP0, Polynomial.eval_zero])
    have hR : ∀ a : ℝ, 0 ≤ R.eval a := by
      intro a
      have h := hval a 0
      rw [hP0, hQ] at h
      simpa using h
    obtain ⟨g, h, hgh⟩ := real_psd_two_sq _ R rfl hR
    refine ⟨polyX g * polyX g + (polyX h * polyX h + 0), 1 * 1 + 0,
      .sq_add _ (.sq_add _ .zero), .sq_add _ .zero, by simp, ?_⟩
    have e2 : polyX R = polyX g ^ 2 + polyX h ^ 2 := by
      rw [hgh]; simp only [map_add, map_pow]
    rw [hP0, hQ, map_zero, e2]
    ring
  · obtain ⟨g, h, hgh⟩ := real_psd_two_sq _ P rfl hP
    have e2 : polyX P = polyX g ^ 2 + polyX h ^ 2 := by
      rw [hgh]; simp only [map_add, map_pow]
    refine ⟨(2 * polyX P * MvPolynomial.X 1 + polyX Q) * (2 * polyX P * MvPolynomial.X 1 + polyX Q) +
        (polyX k * polyX k + (polyX l * polyX l + 0)),
      (2 * polyX g) * (2 * polyX g) + ((2 * polyX h) * (2 * polyX h) + 0),
      .sq_add _ (.sq_add _ (.sq_add _ .zero)), .sq_add _ (.sq_add _ .zero), ?_, ?_⟩
    · intro hD
      apply hP0
      apply Polynomial.funext
      intro a
      have h1 := congrArg (MvPolynomial.eval ![a, 0]) hD
      simp only [map_add, map_mul, map_zero, map_ofNat, eval_polyX, Matrix.cons_val_zero] at h1
      rw [hgh, Polynomial.eval_zero, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_pow]
      nlinarith [sq_nonneg (g.eval a), sq_nonneg (h.eval a)]
    · linear_combination
        (-4 * (polyX P * MvPolynomial.X 1 ^ 2 + polyX Q * MvPolynomial.X 1 + polyX R)) * e2 - e1

end HilbertFoundations
