import HilbertFoundations.ConstructionsCloseAux

/-!
# Helper module for `ConstructionsClose.lean`: totally positive numbers are sums of squares

This module contains no unit of Hilbert's text. From `psd_isSumSq` (a definite polynomial with
rational coefficients is a sum of squares) it derives:

* `exists_psd_shift`: if `a > 0` at the real roots of a non-constant `p`, then
  `a + c p² (1 + a²)` is definite for a suitable rational `c > 0`;
* `exists_isSumSq_aeval`: for an algebraic `θ` and a polynomial `a` that is positive at the real
  conjugates of `θ`, `a(θ) = G(θ)` for a sum of squares `G ∈ ℚ[x]`;
* `totallyPositive_isSumSq`: **the qualitative Theorem 42** — in a number field every totally
  positive number is a sum of squares (of an unspecified number of terms);
* `theorem42_iff_four_squares`: Theorem 42 is equivalent to "in a number field every sum of squares
  is a sum of four squares".
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Polynomial Filter IntermediateField

/-- If `a` is positive at the real roots of the non-constant polynomial `p`, then
`a + c p² (1 + a²)` never becomes negative, for a suitable rational `c > 0`. -/
theorem exists_psd_shift {a p : ℚ[X]} (hp : 0 < p.natDegree)
    (h : ∀ r : ℝ, aeval r p = 0 → 0 < aeval r a) :
    ∃ c : ℚ, 0 < c ∧ PSD (a + C c * p ^ 2 * (1 + a ^ 2)) := by
  set pR := p.map (algebraMap ℚ ℝ) with hpR
  set aR := a.map (algebraMap ℚ ℝ) with haR
  have hpe : ∀ x : ℝ, pR.eval x = aeval x p := fun x => (aeval_real_eq p x).symm
  have hae : ∀ x : ℝ, aR.eval x = aeval x a := fun x => (aeval_real_eq a x).symm
  set φ : ℝ → ℝ := fun x => pR.eval x ^ 2 + (max (aR.eval x) 0) ^ 2 with hφ
  have hcont : Continuous φ :=
    (pR.continuous.pow 2).add ((aR.continuous.max continuous_const).pow 2)
  have hdeg : 0 < pR.degree := by
    rw [hpR, degree_map]; exact natDegree_pos_iff_degree_pos.1 hp
  have hlim : Tendsto φ (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun x : ℝ => ‖pR.eval x‖) (cocompact ℝ) atTop :=
      pR.tendsto_norm_atTop hdeg tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun x : ℝ => ‖pR.eval x‖ ^ 2) (cocompact ℝ) atTop :=
      (tendsto_pow_atTop two_ne_zero).comp h1
    refine tendsto_atTop_mono (fun x => ?_) h2
    simp only [hφ, Real.norm_eq_abs, sq_abs]
    have : 0 ≤ (max (aR.eval x) 0) ^ 2 := sq_nonneg _
    linarith
  obtain ⟨x₀, hx₀⟩ := hcont.exists_forall_le hlim
  have hδ : 0 < φ x₀ := by
    have hge : 0 ≤ φ x₀ := by simp only [hφ]; positivity
    refine lt_of_le_of_ne hge fun h0 => ?_
    simp only [hφ] at h0
    have h1 : pR.eval x₀ ^ 2 = 0 := by
      nlinarith [sq_nonneg (pR.eval x₀), sq_nonneg (max (aR.eval x₀) 0)]
    have h2 : (max (aR.eval x₀) 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (pR.eval x₀), sq_nonneg (max (aR.eval x₀) 0)]
    have h3 : pR.eval x₀ = 0 := by simpa using h1
    have h4 : max (aR.eval x₀) 0 = 0 := by simpa using h2
    have h5 := h x₀ (by rw [← hpe]; exact h3)
    rw [← hae] at h5
    have := le_max_left (aR.eval x₀) 0
    linarith
  obtain ⟨c, hc⟩ := exists_rat_gt (1 / φ x₀)
  have hc0 : (0 : ℝ) < c := lt_trans (by positivity) hc
  refine ⟨c, by exact_mod_cast hc0, fun x => ?_⟩
  have hval : aeval x (a + C c * p ^ 2 * (1 + a ^ 2)) =
      aeval x a + c * aeval x p ^ 2 * (1 + aeval x a ^ 2) := by
    simp [aeval_C]
  rw [hval]
  by_cases hax : 0 < aeval x a
  · positivity
  · push Not at hax
    have h1 : φ x = aeval x p ^ 2 := by
      simp only [hφ, hpe, hae, max_eq_right hax]; ring
    have h2 : φ x₀ ≤ aeval x p ^ 2 := h1 ▸ hx₀ x
    have h3 : 1 ≤ c * aeval x p ^ 2 := by
      have : 1 < c * φ x₀ := by
        rw [div_lt_iff₀ hδ] at hc; exact hc
      nlinarith
    nlinarith [sq_nonneg (aeval x a + 1), sq_nonneg (aeval x a)]

/-- For an algebraic `θ` and a polynomial `a` with rational coefficients that is positive at the
real roots of the minimal polynomial of `θ`, the number `a(θ)` is the value at `θ` of a sum of
squares of polynomials with rational coefficients. -/
theorem exists_isSumSq_aeval {K : Type*} [Field K] [Algebra ℚ K] {θ : K} (hθ : IsIntegral ℚ θ)
    (a : ℚ[X]) (h : ∀ r : ℝ, aeval r (minpoly ℚ θ) = 0 → 0 < aeval r a) :
    ∃ G : ℚ[X], IsSumSq G ∧ aeval θ G = aeval θ a := by
  obtain ⟨c, -, hpsd⟩ := exists_psd_shift (minpoly.natDegree_pos hθ) h
  exact ⟨_, psd_isSumSq hpsd, by simp [minpoly.aeval]⟩

theorem isSumSq_map {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) {s : A}
    (hs : IsSumSq s) : IsSumSq (f s) := by
  induction hs with
  | zero => rw [map_zero]; exact .zero
  | sq_add a _ ih => rw [map_add, map_mul]; exact .sq_add _ ih

/-- **The qualitative Theorem 42**: in a number field, every totally positive number is a sum of
squares of numbers of the field. -/
theorem totallyPositive_isSumSq (k : Type) [Field k] [NumberField k] (α : k)
    (h : TotallyPositive α) : IsSumSq α := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ k
  have hint : IsIntegral ℚ θ := IsIntegral.of_finite ℚ θ
  have hsurj : ∀ x : k, ∃ b : ℚ[X], aeval θ b = x := by
    intro x
    have h2 : x ∈ ℚ⟮θ⟯.toSubalgebra := by rw [hθ]; exact IntermediateField.mem_top
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h2
    exact h2
  obtain ⟨a, rfl⟩ := hsurj α
  have hpos : ∀ r : ℝ, aeval r (minpoly ℚ θ) = 0 → 0 < aeval r a := by
    intro r hr
    have hmem : (r : ℂ) ∈ (minpoly ℚ θ).rootSet ℂ := by
      rw [mem_rootSet]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, aeval_algebraMap_apply, hr, map_zero]
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly k ℂ θ] at hmem
    obtain ⟨φ, hφ⟩ := hmem
    have hφ' : φ θ = (r : ℂ) := hφ
    have hφb : ∀ b : ℚ[X], φ (aeval θ b) = ((aeval r b : ℝ) : ℂ) := by
      intro b
      rw [aeval_def, hom_eval₂, RingHom.ext_rat (φ.comp (algebraMap ℚ k)) (algebraMap ℚ ℂ), hφ',
        ← aeval_def, show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, aeval_algebraMap_apply]
      rfl
    have hreal : ∀ x : k, (φ x).im = 0 := by
      intro x
      obtain ⟨b, rfl⟩ := hsurj x
      rw [hφb]; simp
    have := h φ hreal
    rw [hφb] at this
    simpa using this
  obtain ⟨G, hG, hGe⟩ := exists_isSumSq_aeval hint a hpos
  rw [← hGe]
  exact isSumSq_map (aeval θ : ℚ[X] →ₐ[ℚ] k).toRingHom hG

/-- A nonzero sum of squares is totally positive. -/
theorem totallyPositive_of_isSumSq {k : Type*} [Field k] {α : k} (hα : α ≠ 0) (h : IsSumSq α) :
    TotallyPositive α := by
  intro σ hσ
  have hreal : ∀ x : k, σ x = ((σ x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [hσ x])
  have hnn : ∀ s : k, IsSumSq s → 0 ≤ (σ s).re := by
    intro s hs
    induction hs with
    | zero => simp
    | sq_add a _ ih =>
      rw [map_add, map_mul, hreal a, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
      nlinarith [mul_self_nonneg (σ a).re]
  have hne : (σ α).re ≠ 0 := by
    intro h0
    have : σ α = 0 := by rw [hreal α, h0]; simp
    exact hα ((map_eq_zero σ).1 this)
  exact lt_of_le_of_ne (hnn α h) (Ne.symm hne)

/-- **Theorem 42 is equivalent to: in every number field, a sum of squares is a sum of four
squares** (the Pythagoras number of a number field is at most `4`). -/
theorem theorem42_iff_four_squares :
    Theorem42 ↔ ∀ (k : Type) [Field k] [NumberField k] (α : k), IsSumSq α →
      ∃ a b c d : k, α = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  constructor
  · intro h42 k _ _ α hα
    by_cases h0 : α = 0
    · exact ⟨0, 0, 0, 0, by simp [h0]⟩
    · exact h42 k α (totallyPositive_of_isSumSq h0 hα)
  · intro h k _ _ α hα
    exact h k α (totallyPositive_isSumSq k α hα)

end HilbertFoundations
