import HilbertFoundations.Theorem44CloseAux1

/-!
# Helper module for `Theorem44Close.lean`: real zeros near a simple real zero

This module contains no unit of Hilbert's text.

* `exists_algebraicIndependent_near`: every ball of `ℝ^d` contains a point whose coordinates are
  algebraically independent over `ℚ` (one coordinate at a time: the real numbers algebraic over a
  countable ring are countable);
* `exists_neg_pos_of_simple_root`: a real polynomial with a simple root takes a negative and a
  positive value;
* `exists_root_near`: if `(τ₀, β₀)` is a simple real zero of `M ∈ ℚ[T₁, …, T_d][Y]`, then for every
  `τ` near `τ₀` the polynomial `M(τ; ·)` has a real root (intermediate value theorem).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Polynomial

noncomputable section

variable {d : ℕ}

/-- **Algebraically independent points are dense in `ℝ^d`.** -/
theorem exists_algebraicIndependent_near : ∀ (d : ℕ) (τ₀ : Fin d → ℝ) (δ : ℝ), 0 < δ →
    ∃ τ : Fin d → ℝ, dist τ τ₀ < δ ∧ AlgebraicIndependent ℚ τ := by
  intro d
  induction d with
  | zero =>
    intro τ₀ δ hδ
    refine ⟨τ₀, by simpa using hδ, algebraicIndependent_empty_type⟩
  | succ d ih =>
    intro τ₀ δ hδ
    obtain ⟨τ', hτ', hind⟩ := ih (Fin.tail τ₀) δ hδ
    have hcount : Countable (Algebra.adjoin ℚ (Set.range τ')) := by
      have h1 : (Subfield.closure (Set.range τ') : Set ℝ).Countable := by
        rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff]
        refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
        exact Cardinal.mk_le_aleph0_iff.2 (Set.finite_range τ').countable.to_subtype
      have h2 : (Algebra.adjoin ℚ (Set.range τ') : Set ℝ) ⊆ Subfield.closure (Set.range τ') := by
        intro x hx
        induction hx using Algebra.adjoin_induction with
        | mem x hx => exact Subfield.subset_closure hx
        | algebraMap q => rw [eq_ratCast]; exact SubfieldClass.ratCast_mem _ q
        | add x y _ _ hx hy => exact add_mem hx hy
        | mul x y _ _ hx hy => exact mul_mem hx hy
      exact (h1.mono h2).to_subtype
    have hdense : Dense {x : ℝ | IsAlgebraic (Algebra.adjoin ℚ (Set.range τ')) x}ᶜ :=
      (Algebraic.countable (R := Algebra.adjoin ℚ (Set.range τ')) (A := ℝ)).dense_compl ℝ
    obtain ⟨a, ha, haU⟩ :=
      hdense.exists_mem_open Metric.isOpen_ball ⟨τ₀ 0, Metric.mem_ball_self hδ⟩
    have hopt := (hind.option_iff_transcendental a).2 ha
    refine ⟨Fin.cons a τ', ?_, ?_⟩
    · rw [dist_pi_lt_iff hδ] at hτ' ⊢
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using haU
      · rw [Fin.cons_succ]; exact hτ' i
    · refine (algebraicIndependent_equiv' (finSuccEquiv d) ?_).2 hopt
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- A real polynomial with a simple root takes a negative and a positive value. -/
theorem exists_neg_pos_of_simple_root (f : ℝ[X]) (b : ℝ) (h0 : f.eval b = 0)
    (h1 : f.derivative.eval b ≠ 0) : ∃ y₁ y₂ : ℝ, f.eval y₁ < 0 ∧ 0 < f.eval y₂ := by
  have hq : (X - C b) * (f /ₘ (X - C b)) = f := mul_divByMonic_eq_iff_isRoot.2 h0
  set q := f /ₘ (X - C b) with hqdef
  have hqb : q.eval b = f.derivative.eval b := by
    rw [← hq]; simp
  have hqb0 : q.eval b ≠ 0 := hqb ▸ h1
  have hval : ∀ y : ℝ, f.eval y = (y - b) * q.eval y := by
    intro y; rw [← hq]; simp
  have hopen : IsOpen {y : ℝ | 0 < q.eval y * q.eval b} :=
    isOpen_lt continuous_const (q.continuous.mul continuous_const)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen b (by
    show 0 < q.eval b * q.eval b
    exact mul_self_pos.2 hqb0)
  have hm : 0 < q.eval (b - ε / 2) * q.eval b := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hp : 0 < q.eval (b + ε / 2) * q.eval b := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  rcases lt_or_gt_of_ne hqb0 with hneg | hpos
  · refine ⟨b + ε / 2, b - ε / 2, ?_, ?_⟩
    · rw [hval]; nlinarith
    · rw [hval]; nlinarith
  · refine ⟨b - ε / 2, b + ε / 2, ?_, ?_⟩
    · rw [hval]; nlinarith
    · rw [hval]; nlinarith

/-- `M(τ; c)` is a continuous function of `τ ∈ ℝ^d`. -/
theorem continuous_evalAt_left (M : (MvPolynomial (Fin d) ℚ)[X]) (c : ℝ) :
    Continuous fun τ : Fin d → ℝ => evalAt τ c M := by
  unfold evalAt
  simp_rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_eq_eval_map]
  exact continuous_finsetSum _ fun i _ =>
    (MvPolynomial.continuous_eval _).mul continuous_const

/-- **Persistence of a simple real root**: if `(τ₀, β₀)` is a simple real zero of `M`, then
`M(τ; ·)` has a real root for every `τ` near `τ₀`. -/
theorem exists_root_near (M : (MvPolynomial (Fin d) ℚ)[X]) (τ₀ : Fin d → ℝ) (β₀ : ℝ)
    (h0 : evalAt τ₀ β₀ M = 0) (h1 : evalAt τ₀ β₀ (derivative M) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : Fin d → ℝ, dist τ τ₀ < δ → ∃ β : ℝ, evalAt τ β M = 0 := by
  obtain ⟨y₁, y₂, hy₁, hy₂⟩ := exists_neg_pos_of_simple_root
    (M.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) τ₀)) β₀ h0 (by
      rw [Polynomial.derivative_map]; exact h1)
  have hopen : IsOpen ({τ : Fin d → ℝ | evalAt τ y₁ M < 0} ∩ {τ | 0 < evalAt τ y₂ M}) :=
    (isOpen_lt (continuous_evalAt_left M y₁) continuous_const).inter
      (isOpen_lt continuous_const (continuous_evalAt_left M y₂))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen τ₀ ⟨hy₁, hy₂⟩
  refine ⟨δ, hδ, fun τ hτ => ?_⟩
  obtain ⟨hn, hp⟩ := hball (Metric.mem_ball.2 hτ)
  have hcont : Continuous fun y : ℝ => evalAt τ y M :=
    (M.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) τ)).continuous
  obtain ⟨β, hβ⟩ := mem_range_of_exists_le_of_exists_ge hcont ⟨y₁, hn.le⟩ ⟨y₂, hp.le⟩
  exact ⟨β, hβ⟩

end

end HilbertFoundations
