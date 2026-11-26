import HilbertFoundations.ConstructionsCloseAux2

/-!
# Helper module for `ConstructionsClose.lean`: totally real numbers of a tower of square roots

This module contains no unit of Hilbert's text. It proves:

* `validTower_append`: two towers of square roots can be combined into one;
* `sqrt_mem_omega_of_pos_roots`: the square root of a number of `Ω` all of whose real conjugates
  are positive lies in `Ω` (it is a sum of squares of numbers of `ℚ(D) ⊆ Ω`);
* `tower_totReal_mem_omega`: **every totally real number of a tower of square roots lies in `Ω`**
  (induction on the tower, with the trace `2r` and the discriminant `4 s² a` of `r + s √a`);
* `cos_two_pi_div_mem_omega`: if `cos (2π/N)` lies in a tower of square roots, it lies in `Ω` (its
  conjugates are roots of the Chebyshev equation `T_N(z) = 1`, hence real);
* `regular_polygon_of_tower`: then the vertices of the regular `n`-gon, `4n = N`, have coordinates
  in `Ω`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Polynomial
open scoped Real

/-! ## Towers of square roots -/

theorem ratField_le (F : Subfield ℝ) : ratField ≤ F := by
  intro x hx
  obtain ⟨q, rfl⟩ := mem_ratField.1 hx
  exact SubfieldClass.ratCast_mem F q

theorem towerField_le_append_right (l₁ l₂ : List ℝ) :
    towerField l₂ ≤ towerField (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans fun x hx => Subfield.subset_closure (Or.inl hx)

theorem towerField_le_append_left (l₁ l₂ : List ℝ) :
    towerField l₁ ≤ towerField (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact ratField_le _
  | cons a l ih =>
    show Subfield.closure _ ≤ Subfield.closure _
    exact Subfield.closure_mono (Set.union_subset_union_left _ ih)

theorem validTower_append {l₁ l₂ : List ℝ} (h₁ : ValidTower l₁) (h₂ : ValidTower l₂) :
    ValidTower (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons a l ih => exact ⟨ih h₁.1, towerField_le_append_left l l₂ h₁.2.1, h₁.2.2⟩

/-- The numbers of a tower of square roots are algebraic. -/
theorem towerField_isAlgebraic :
    ∀ l : List ℝ, ValidTower l → ∀ x ∈ towerField l, IsAlgebraic ℚ x
  | [], _, x, hx => by
    obtain ⟨q, rfl⟩ := mem_ratField.1 hx
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q
  | a :: l, ⟨hv, ha, ha0⟩, x, hx => by
    have ih := towerField_isAlgebraic l hv
    obtain ⟨r, hr, s, hs, rfl⟩ := (towerField_quadExt ha ha0).repr x hx
    have hb : IsAlgebraic ℚ (Real.sqrt a) := by
      have : IsAlgebraic ℚ (Real.sqrt a ^ 2) := by rw [Real.sq_sqrt ha0]; exact ih a ha
      exact this.of_pow two_pos
    exact (ih r hr).add ((ih s hs).mul hb)

/-! ## Embeddings and conjugates -/

/-- `x` is **totally real** in `F`: every embedding of `F` into `ℂ` maps it to a real number. -/
def TotReal (F : Subfield ℝ) (x : ℝ) : Prop :=
  ∃ hx : x ∈ F, ∀ σ : F →+* ℂ, ∃ t : ℝ, σ ⟨x, hx⟩ = (t : ℂ)

theorem aeval_mem_subfield {F : Subfield ℝ} {D : ℝ} (hD : D ∈ F) (g : ℚ[X]) : aeval D g ∈ F := by
  rw [aeval_eq_sum_range]
  refine F.sum_mem fun i _ => ?_
  rw [Algebra.smul_def, eq_ratCast]
  exact F.mul_mem (SubfieldClass.ratCast_mem F _) (F.pow_mem hD i)

/-- An embedding maps a root of a polynomial with rational coefficients to a root. -/
theorem aeval_embedding_eq_zero {F : Subfield ℝ} (σ : F →+* ℂ) {x : ℝ} (hx : x ∈ F) (P : ℚ[X])
    (h : aeval x P = 0) : aeval (σ ⟨x, hx⟩) P = 0 := by
  have h1 : aeval (⟨x, hx⟩ : F) P = 0 := by
    apply Subtype.ext
    have : ((aeval (⟨x, hx⟩ : F) P : F) : ℝ) = aeval x P := by
      rw [aeval_def, aeval_def]
      refine (hom_eval₂ P (algebraMap ℚ F) F.subtype ⟨x, hx⟩).trans ?_
      rw [RingHom.ext_rat (F.subtype.comp (algebraMap ℚ F)) (algebraMap ℚ ℝ)]
      rfl
    rw [this, h]; rfl
  rw [aeval_def, ← RingHom.ext_rat (σ.comp (algebraMap ℚ F)) (algebraMap ℚ ℂ), ← hom_eval₂,
    ← aeval_def, h1, map_zero]

/-- Every root in `ℂ` of the minimal polynomial of a number of `F` is its image under an embedding
of `F` (for `F` algebraic over `ℚ`). -/
theorem exists_embedding_of_root {F : Subfield ℝ} (hF : ∀ x ∈ F, IsAlgebraic ℚ x) {D : ℝ}
    (hD : D ∈ F) {z : ℂ} (hz : aeval z (minpoly ℚ D) = 0) : ∃ σ : F →+* ℂ, σ ⟨D, hD⟩ = z := by
  have hinj : Function.Injective (F.subtype.toRatAlgHom) := Subtype.val_injective
  have : Algebra.IsAlgebraic ℚ F := ⟨fun x =>
    (isAlgebraic_algHom_iff (F.subtype.toRatAlgHom) hinj).1 (hF x x.2)⟩
  have hmin : minpoly ℚ D = minpoly ℚ (⟨D, hD⟩ : F) :=
    minpoly.algHom_eq (F.subtype.toRatAlgHom) hinj ⟨D, hD⟩
  have hint : IsIntegral ℚ (⟨D, hD⟩ : F) := Algebra.IsIntegral.isIntegral _
  have hmem : z ∈ (minpoly ℚ (⟨D, hD⟩ : F)).rootSet ℂ := by
    rw [mem_rootSet]; exact ⟨minpoly.ne_zero hint, by rw [← hmin]; exact hz⟩
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hmem
  obtain ⟨ψ, hψ⟩ := hmem
  exact ⟨ψ.toRingHom, hψ⟩

theorem sosIn_aeval {F : Subfield ℝ} {D : ℝ} (hD : D ∈ F) {G : ℚ[X]} (hG : IsSumSq G) :
    SOSIn F (aeval D G) := by
  induction hG with
  | zero => rw [map_zero]; exact .zero
  | sq_add g _ ih => rw [map_add, map_mul, ← sq]; exact .cons (aeval_mem_subfield hD g) ih

/-- **The square root of a number of `Ω` whose real conjugates are all positive lies in `Ω`**: the
number is a sum of squares of numbers of `ℚ(D) ⊆ Ω`. -/
theorem sqrt_mem_omega_of_pos_roots {D : ℝ} (hD : D ∈ Omega) (hint : IsIntegral ℚ D)
    (hroots : ∀ ρ : ℝ, aeval ρ (minpoly ℚ D) = 0 → 0 < ρ) : Real.sqrt D ∈ Omega := by
  obtain ⟨G, hG, hGe⟩ := exists_isSumSq_aeval hint X (by simpa using hroots)
  have := sosIn_aeval hD hG
  rw [hGe, aeval_X] at this
  exact this.sqrt_mem_omega le_rfl

/-! ## Totally real numbers of a tower -/

/-- **Every totally real number of a tower of square roots lies in `Ω`.** For `x = r + s √a` over
`F`, the trace `2r` and the discriminant `4 s² a` are totally real in `F`, the discriminant is
totally nonnegative, hence a sum of squares of numbers of `Ω`, and `x = r ± √(s² a)`. -/
theorem tower_totReal_mem_omega :
    ∀ l : List ℝ, ValidTower l → ∀ x : ℝ, TotReal (towerField l) x → x ∈ Omega
  | [], _, x, ⟨hx, _⟩ => ratField_le Omega hx
  | a :: l, ⟨hv, ha, ha0⟩, x, hx => by
    have ih := tower_totReal_mem_omega l hv
    have hE := towerField_quadExt ha ha0
    have halg := towerField_isAlgebraic l hv
    by_cases hbF : Real.sqrt a ∈ towerField l
    · have e := hE.eq_of_mem hbF
      rw [e] at hx; exact ih x hx
    obtain ⟨hxE, hσx⟩ := hx
    obtain ⟨r, hr, s, hs, hxrs⟩ := hE.repr x hxE
    have hsq : Real.sqrt a ^ 2 ∈ towerField l := hE.sq_mem
    have hDm : s ^ 2 * Real.sqrt a ^ 2 ∈ towerField l :=
      Subfield.mul_mem _ (Subfield.pow_mem _ hs 2) hsq
    have conj : ∀ σ : towerField l →+* ℂ, ∃ t₁ t₂ : ℝ, σ ⟨r, hr⟩ * 2 = (t₁ : ℂ) + t₂ ∧
        σ ⟨s ^ 2 * Real.sqrt a ^ 2, hDm⟩ * 4 = (((t₁ - t₂) ^ 2 : ℝ) : ℂ) := by
      intro σ
      obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (σ ⟨Real.sqrt a ^ 2, hsq⟩) two_pos
      obtain ⟨σ₁, e₁, h₁⟩ := exists_ext hE hbF σ τ hτ
      obtain ⟨σ₂, e₂, h₂⟩ := exists_ext hE hbF σ (-τ) (by rw [neg_sq]; exact hτ)
      obtain ⟨t₁, et₁⟩ := hσx σ₁
      obtain ⟨t₂, et₂⟩ := hσx σ₂
      have hxE' : (⟨x, hxE⟩ : towerField (a :: l)) =
          ⟨((⟨r, hr⟩ : towerField l) : ℝ), hE.le hr⟩ +
            ⟨((⟨s, hs⟩ : towerField l) : ℝ), hE.le hs⟩ * ⟨Real.sqrt a, hE.mem⟩ :=
        Subtype.ext (by simp [hxrs])
      rw [hxE', map_add, map_mul, e₁ ⟨r, hr⟩, e₁ ⟨s, hs⟩, h₁] at et₁
      rw [hxE', map_add, map_mul, e₂ ⟨r, hr⟩, e₂ ⟨s, hs⟩, h₂] at et₂
      refine ⟨t₁, t₂, ?_, ?_⟩
      · rw [← et₁, ← et₂]; ring
      · have : (⟨s ^ 2 * Real.sqrt a ^ 2, hDm⟩ : towerField l) =
            ⟨s, hs⟩ ^ 2 * ⟨Real.sqrt a ^ 2, hsq⟩ := Subtype.ext (by simp)
        rw [this, map_mul, map_pow, ← hτ]
        push_cast
        rw [← et₁, ← et₂]; ring
    have hrR : TotReal (towerField l) r := ⟨hr, fun σ => by
      obtain ⟨t₁, t₂, h1, -⟩ := conj σ
      refine ⟨(t₁ + t₂) / 2, ?_⟩
      have : σ ⟨r, hr⟩ = ((t₁ : ℂ) + t₂) / 2 := by rw [← h1]; ring
      rw [this]; push_cast; ring⟩
    have hDσ : ∀ σ : towerField l →+* ℂ, ∃ t : ℝ, 0 ≤ t ∧
        σ ⟨s ^ 2 * Real.sqrt a ^ 2, hDm⟩ = (t : ℂ) := by
      intro σ
      obtain ⟨t₁, t₂, -, h2⟩ := conj σ
      refine ⟨(t₁ - t₂) ^ 2 / 4, by positivity, ?_⟩
      have : σ ⟨s ^ 2 * Real.sqrt a ^ 2, hDm⟩ = (((t₁ - t₂) ^ 2 : ℝ) : ℂ) / 4 := by
        rw [← h2]; ring
      rw [this]; push_cast; ring
    have hrO : r ∈ Omega := ih r hrR
    have hDO : s ^ 2 * Real.sqrt a ^ 2 ∈ Omega :=
      ih _ ⟨hDm, fun σ => by obtain ⟨t, -, e⟩ := hDσ σ; exact ⟨t, e⟩⟩
    have hsqrtD : Real.sqrt (s ^ 2 * Real.sqrt a ^ 2) ∈ Omega := by
      by_cases hD0 : s ^ 2 * Real.sqrt a ^ 2 = 0
      · rw [hD0, Real.sqrt_zero]; exact Omega.zero_mem
      have hint : IsIntegral ℚ (s ^ 2 * Real.sqrt a ^ 2) := (halg _ hDm).isIntegral
      refine sqrt_mem_omega_of_pos_roots hDO hint fun ρ hρ => ?_
      have hz : aeval (ρ : ℂ) (minpoly ℚ (s ^ 2 * Real.sqrt a ^ 2)) = 0 := by
        rw [show ((ρ : ℝ) : ℂ) = algebraMap ℝ ℂ ρ from rfl, aeval_algebraMap_apply, hρ, map_zero]
      obtain ⟨σ, hσ⟩ := exists_embedding_of_root halg hDm hz
      obtain ⟨t, ht, e⟩ := hDσ σ
      have hρt : ρ = t := by rw [hσ] at e; exact_mod_cast e
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        have h0 : σ ⟨s ^ 2 * Real.sqrt a ^ 2, hDm⟩ = 0 := by rw [hσ]; simp
        have h1 := (map_eq_zero σ).1 h0
        exact hD0 (congrArg Subtype.val h1)
      rw [hρt] at hρ0 ⊢
      exact lt_of_le_of_ne ht (Ne.symm hρ0)
    have hsb : s * Real.sqrt a = Real.sqrt (s ^ 2 * Real.sqrt a ^ 2) ∨
        s * Real.sqrt a = -Real.sqrt (s ^ 2 * Real.sqrt a ^ 2) := by
      have hD' : s ^ 2 * Real.sqrt a ^ 2 = (s * Real.sqrt a) ^ 2 := by ring
      rw [hD', Real.sqrt_sq_eq_abs]
      rcases abs_choice (s * Real.sqrt a) with h | h <;> rw [h]
      · left; rfl
      · right; ring
    rw [hxrs]
    rcases hsb with h | h <;> rw [h]
    · exact Omega.add_mem hrO hsqrtD
    · exact Omega.add_mem hrO (Omega.neg_mem hsqrtD)

/-! ## The regular polygons -/

open Polynomial.Chebyshev in
/-- The complex solutions of the Chebyshev equation `T_N(z) = 1` are real. -/
theorem cheb_root_real {N : ℕ} (hN : N ≠ 0) {z : ℂ} (hz : (T ℂ N).eval z = 1) :
    ∃ t : ℝ, z = (t : ℂ) := by
  obtain ⟨w, rfl⟩ := Complex.cos_surjective z
  rw [T_complex_cos] at hz
  obtain ⟨j, hj⟩ := Complex.cos_eq_one_iff.1 hz
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hw : w = ((j * (2 * π) / N : ℝ) : ℂ) := by
    push_cast at hj ⊢
    field_simp
    linear_combination -hj
  exact ⟨Real.cos (j * (2 * π) / N), by rw [hw, Complex.ofReal_cos]⟩

open Polynomial.Chebyshev in
/-- **If `cos (2π/N)` lies in a tower of square roots, it lies in `Ω`.** -/
theorem cos_two_pi_div_mem_omega {N : ℕ} (hN : N ≠ 0) {l : List ℝ} (hv : ValidTower l)
    (hc : Real.cos (2 * π / N) ∈ towerField l) : Real.cos (2 * π / N) ∈ Omega := by
  refine tower_totReal_mem_omega l hv _ ⟨hc, fun σ => ?_⟩
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h0 : aeval (Real.cos (2 * π / N)) (T ℚ N - 1) = 0 := by
    rw [map_sub, map_one, aeval_def, eval₂_eq_eval_map, map_T, T_real_cos]
    have : ((N : ℤ) : ℝ) * (2 * π / N) = 2 * π := by push_cast; field_simp
    rw [this, Real.cos_two_pi, sub_self]
  have h1 := aeval_embedding_eq_zero σ hc _ h0
  rw [map_sub, map_one, aeval_def, eval₂_eq_eval_map, map_T, sub_eq_zero] at h1
  exact cheb_root_real hN h1

theorem cos_nat_mul_mem {θ : ℝ} (hc : Real.cos θ ∈ Omega) :
    ∀ j : ℕ, Real.cos (j * θ) ∈ Omega ∧ Real.cos ((j + 1 : ℕ) * θ) ∈ Omega
  | 0 => by simp [Omega.one_mem, hc]
  | j + 1 => by
    obtain ⟨h1, h2⟩ := cos_nat_mul_mem hc j
    refine ⟨h2, ?_⟩
    have : Real.cos ((j + 1 + 1 : ℕ) * θ) =
        2 * Real.cos θ * Real.cos ((j + 1 : ℕ) * θ) - Real.cos (j * θ) := by
      have e1 : ((j + 1 + 1 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have e2 : (j : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [e1, e2, Real.cos_add, Real.cos_sub]; ring
    rw [this]
    exact Omega.sub_mem (Omega.mul_mem (Omega.mul_mem (two_mem_subfield _) hc) h2) h1

/-- If `cos (2π/(4n))` lies in a tower of square roots, the vertices of the regular `n`-gon have
coordinates in `Ω`. -/
theorem regular_polygon_of_tower {n : ℕ} (hn : 1 ≤ n) {l : List ℝ} (hv : ValidTower l)
    (hc : Real.cos (2 * π / (4 * n : ℕ)) ∈ towerField l) (k : ℕ) :
    Real.cos (2 * π * k / n) ∈ Omega ∧ Real.sin (2 * π * k / n) ∈ Omega := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcO := cos_two_pi_div_mem_omega (N := 4 * n) (by omega) hv hc
  set θ : ℝ := 2 * π / (4 * n : ℕ) with hθ
  have hnθ : (n : ℝ) * θ = π / 2 := by rw [hθ]; push_cast; field_simp; ring
  have hsO : Real.sin θ ∈ Omega := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : Real.sin θ = Real.cos (m * θ) := by
      have e : (m : ℝ) * θ = π / 2 - θ := by rw [← hnθ]; push_cast; ring
      rw [e, Real.cos_pi_div_two_sub]
    rw [this]; exact (cos_nat_mul_mem hcO m).1
  have := cos_sin_nat_mul_mem hcO hsO (4 * k)
  have e : ((4 * k : ℕ) : ℝ) * θ = 2 * π * k / n := by
    rw [hθ]; push_cast; field_simp
  rwa [e] at this

end HilbertFoundations
