import HilbertFoundations.ConstructionsAux

/-!
# Helper module for `Constructions.lean`: Hilbert's constructions of Figs. 50 and 51

This module contains no unit of Hilbert's text. In the coordinate plane `Coord K 2` over an
ordered field `K` it proves the basic steps of constructions by straight-edge and transferer of
segments (`rt_inter`, `rt_inter'`, `rt_layOff'`, `rt_reflect`), Hilbert's construction of the
parallel (Fig. 50, `rt_parallelPt`) and, over a Pythagorean field, of a perpendicular (Fig. 51,
`rt_perp_exists`), with the algebra behind them: the lines of Fig. 51 meet
(`cross_sub_add_ne`), three points of a circle are not collinear (`circle_chord`) and the
identity behind the theorem on the altitudes of a triangle (`altitude_identity`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[simp] theorem xc_neg (X : Coord K 2) : xc (-X) = -xc X := rfl
@[simp] theorem yc_neg (X : Coord K 2) : yc (-X) = -yc X := rfl

/-! ### Algebraic lemmas for Fig. 51 -/

/-- If `|d| = |u| = |e|` and the three directions are pairwise independent, the lines `BD` and
`CE` of Fig. 51 (`B = A + u`, `C = A - u`, `D = A + d`, `E = A + e`) are not parallel. -/
theorem cross_sub_add_ne {u d e : Coord K 2} (hd : ip d d = ip u u) (he : ip e e = ip u u)
    (hud : crossProd2 u d ≠ 0) (hue : crossProd2 u e ≠ 0) (hde : crossProd2 d e ≠ 0) :
    crossProd2 (d - u) (e + u) ≠ 0 := by
  intro h
  have hx : d - u ≠ 0 := by
    intro h0; rw [sub_eq_zero] at h0; rw [h0, cross_self] at hud; exact hud rfl
  obtain ⟨l, hl⟩ := (cross_eq_zero_iff hx).1 h
  have h1 : xc e + xc u = l * (xc d - xc u) := by
    have := congrArg xc hl; simpa using this
  have h2 : yc e + yc u = l * (yc d - yc u) := by
    have := congrArg yc hl; simpa using this
  have hN := ip_self_pos hx
  simp only [ip_two] at hd he hN
  simp only [xc_sub, yc_sub] at hN
  have key : l * (l + 1) * ((xc d - xc u) * (xc d - xc u) + (yc d - yc u) * (yc d - yc u))
      = 0 := by
    linear_combination he + l * hd - (xc e + l * (xc d - xc u) - xc u) * h1 -
      (yc e + l * (yc d - yc u) - yc u) * h2
  rcases mul_eq_zero.1 key with k | k
  · rcases mul_eq_zero.1 k with k | k
    · subst k
      have : e = -u := by
        have : e + u = 0 := by rw [hl, zero_smul]
        exact eq_neg_of_add_eq_zero_left this
      rw [this] at hue; apply hue; simp only [crossProd2_def, xc_neg, yc_neg]; ring
    · have hl' : l = -1 := by linarith
      subst hl'
      have : e = -d := by
        have h3 : e + u = -(d - u) := by rw [hl, neg_one_smul]
        rw [← sub_eq_zero] at h3 ⊢
        rw [← h3]; abel
      rw [this] at hde; apply hde; simp only [crossProd2_def, xc_neg, yc_neg]; ring
  · exact absurd k hN.ne'

/-- Three distinct points of a circle are not collinear: if `|d| = |u| = |e|` and `d - u` is a
multiple `μ (e - u)` with `e ≠ u`, then `μ = 0` or `μ = 1`. -/
theorem circle_chord {u d e : Coord K 2} (hd : ip d d = ip u u) (he : ip e e = ip u u)
    (heu : e ≠ u) {μ : K} (h : d - u = μ • (e - u)) : μ = 0 ∨ μ = 1 := by
  have h1 : xc d - xc u = μ * (xc e - xc u) := by have := congrArg xc h; simpa using this
  have h2 : yc d - yc u = μ * (yc e - yc u) := by have := congrArg yc h; simpa using this
  have hN := ip_self_pos (sub_ne_zero.2 heu)
  simp only [ip_two] at hd he hN
  simp only [xc_sub, yc_sub] at hN
  have key : μ * (μ - 1) * ((xc e - xc u) * (xc e - xc u) + (yc e - yc u) * (yc e - yc u))
      = 0 := by
    linear_combination hd - μ * he - (xc d + xc u + μ * (xc e - xc u)) * h1 -
      (yc d + yc u + μ * (yc e - yc u)) * h2
  rcases mul_eq_zero.1 key with k | k
  · rcases mul_eq_zero.1 k with k | k
    · exact Or.inl k
    · exact Or.inr (by linarith)
  · exact absurd k hN.ne'

/-- The identity behind the theorem on the altitudes of a triangle. -/
theorem altitude_identity (F H B C : Coord K 2) :
    ip (F - H) (B - C) = ip (H - C) (F - B) - ip (H - B) (F - C) := by
  simp only [ip_two, xc_sub, yc_sub]; ring

/-- In a plane over a Pythagorean field, a nonzero segment can be laid off on every line:
`t² |v|² = |w|²` has a positive solution. -/
theorem exists_layoff_param [IsPythagorean K] {v w : Coord K 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ t : K, 0 < t ∧ t ^ 2 * ip v v = ip w w := by
  obtain ⟨c, hc0, hc⟩ := IsPythagorean.exists_sqrt_sq_add_sq (ip v w) (crossProd2 v w)
  rw [ip_sq_add_cross_sq] at hc
  have hv' := ip_self_pos hv
  have hw' := ip_self_pos hw
  have hcpos : 0 < c := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hc; nlinarith
  refine ⟨c / ip v v, div_pos hcpos hv', ?_⟩
  rw [div_pow, hc]; field_simp

/-! ### Constructions by straight-edge and transferer in the coordinate plane -/

section RT

variable {S : Set (Coord K 2)}

/-- The common point of two lines drawn with the straight-edge. -/
theorem rt_inter {P₁ P₂ P₃ P₄ : Coord K 2} (h1 : RulerTransferer S P₁)
    (h2 : RulerTransferer S P₂) (h3 : RulerTransferer S P₃) (h4 : RulerTransferer S P₄)
    (h12 : P₁ ≠ P₂) (h34 : P₃ ≠ P₄) (hc : crossProd2 (P₂ - P₁) (P₄ - P₃) ≠ 0) :
    RulerTransferer S
      ((crossProd2 (P₃ - P₁) (P₄ - P₃) / crossProd2 (P₂ - P₁) (P₄ - P₃)) • (P₂ - P₁) + P₁) :=
  RulerTransferer.meet h1 h2 h3 h4 h12 h34 (AffLine.left_mem_through h12)
    (AffLine.right_mem_through h12) (AffLine.left_mem_through h34) (AffLine.right_mem_through h34)
    (through_ne_of_cross h12 h34 hc) ((mem_through h12).2 ⟨_, rfl⟩)
    ((mem_through h34).2 ⟨_, inter_eq hc⟩)

/-- A point on two lines drawn with the straight-edge. -/
theorem rt_inter' {P₁ P₂ P₃ P₄ X : Coord K 2} (h1 : RulerTransferer S P₁)
    (h2 : RulerTransferer S P₂) (h3 : RulerTransferer S P₃) (h4 : RulerTransferer S P₄)
    (h12 : P₁ ≠ P₂) (h34 : P₃ ≠ P₄) (hc : crossProd2 (P₂ - P₁) (P₄ - P₃) ≠ 0)
    (hX1 : crossProd2 (P₂ - P₁) (X - P₁) = 0) (hX2 : crossProd2 (P₄ - P₃) (X - P₃) = 0) :
    RulerTransferer S X :=
  RulerTransferer.meet h1 h2 h3 h4 h12 h34 (AffLine.left_mem_through h12)
    (AffLine.right_mem_through h12) (AffLine.left_mem_through h34) (AffLine.right_mem_through h34)
    (through_ne_of_cross h12 h34 hc) ((mem_through_iff_cross h12).2 hX1)
    ((mem_through_iff_cross h34).2 hX2)

/-- Laying off the segment `AB` from `O` on the line `OQ`. -/
theorem rt_layOff' {O Q A B : Coord K 2} (hO : RulerTransferer S O) (hQ : RulerTransferer S Q)
    (hA : RulerTransferer S A) (hB : RulerTransferer S B) (hOQ : O ≠ Q) (hAB : A ≠ B) {t : K}
    (ht : t ≠ 0) (htt : t ^ 2 * ip (Q - O) (Q - O) = ip (B - A) (B - A)) :
    RulerTransferer S (t • (Q - O) + O) := by
  refine RulerTransferer.layOff hA hB hO hQ hAB hOQ (AffLine.left_mem_through hOQ)
    (AffLine.right_mem_through hOQ) ((mem_through hOQ).2 ⟨t, rfl⟩) ?_ ?_
  · intro e
    have : t • (Q - O) = 0 := by rw [← sub_eq_zero.2 e]; abel
    rcases smul_eq_zero.1 this with h | h
    · exact ht h
    · exact ne_zero_of_ne hOQ h
  · rw [segCong_iff, add_sub_cancel_right, ip_smul_left, ip_smul_right, ← mul_assoc, ← sq, htt]

/-- The reflection `2A - P` of a constructed point `P` in a constructed point `A ≠ P`. -/
theorem rt_reflect {A P : Coord K 2} (hA : RulerTransferer S A) (hP : RulerTransferer S P)
    (h : A ≠ P) : RulerTransferer S ((2 : K) • A - P) := by
  have := rt_layOff' (t := -1) hA hP hA hP h h (by norm_num) (by ring)
  convert this using 1
  apply ext2 <;> simp <;> ring

/-- **Hilbert's construction of the parallel** (Fig. 50): for a constructed point `P` outside the
line through the constructed points `A ≠ B`, the point `Q = P + 2 (B - A)` is constructible
(`C = 2A - P` with `AC = PA`, then `Q = 2B - C` with `BQ = CB`). -/
theorem rt_parallelPt {A B P : Coord K 2} (hA : RulerTransferer S A) (hB : RulerTransferer S B)
    (hP : RulerTransferer S P) (hc : crossProd2 (B - A) (P - A) ≠ 0) :
    RulerTransferer S (P + (2 : K) • (B - A)) := by
  have hAP : A ≠ P := by rintro rfl; simp at hc
  have hC := rt_reflect hA hP hAP
  have hBC : B ≠ (2 : K) • A - P := by
    intro e; apply hc
    have : P - A = -(B - A) := by rw [e]; apply ext2 <;> simp <;> ring
    rw [this]; simp only [crossProd2_def, xc_neg, yc_neg]; ring
  have hQ := rt_reflect hB hC hBC
  convert hQ using 1
  apply ext2 <;> simp <;> ring

/-- **Hilbert's construction of a perpendicular** (Fig. 51), over a Pythagorean field: if the
constructed point `P` lies outside the line through the constructed points `A ≠ B`, there are two
distinct constructed points `F`, `H` with `FH ⊥ AB`. -/
theorem rt_perp_exists [IsPythagorean K] {A B P : Coord K 2} (hA : RulerTransferer S A)
    (hB : RulerTransferer S B) (hP : RulerTransferer S P) (hc : crossProd2 (B - A) (P - A) ≠ 0) :
    ∃ F H : Coord K 2, RulerTransferer S F ∧ RulerTransferer S H ∧ F ≠ H ∧
      ip (F - H) (B - A) = 0 := by
  have hAB : A ≠ B := by rintro rfl; simp at hc
  have hAP : A ≠ P := by rintro rfl; simp at hc
  set u := B - A with hu
  have hu0 : u ≠ 0 := ne_zero_of_ne hAB
  -- `C = 2A - B`
  have hC := rt_reflect hA hB hAB
  set C := (2 : K) • A - B with hCdef
  have hCA : C - A = -u := by rw [hCdef, hu]; apply ext2 <;> simp <;> ring
  -- `D` on `AP` with `AD = AB`
  obtain ⟨δ, hδ0, hδ⟩ := exists_layoff_param (ne_zero_of_ne hAP) hu0
  have hD := rt_layOff' hA hP hA hB hAP hAB hδ0.ne' hδ
  set D := δ • (P - A) + A with hDdef
  -- `Q = P + 2(B - A)` and `E` on `AQ` with `AE = AB`
  have hQ := rt_parallelPt hA hB hP hc
  set Q := P + (2 : K) • (B - A) with hQdef
  have hQA : Q - A = (P - A) + (2 : K) • u := by rw [hQdef, hu]; abel
  have hcQ : crossProd2 u (Q - A) ≠ 0 := by
    rw [hQA, cross_add_right, cross_smul_right, cross_self]; simpa using hc
  have hAQ : A ≠ Q := by intro e; rw [e, sub_self] at hcQ; simp at hcQ
  obtain ⟨ε, hε0, hε⟩ := exists_layoff_param (ne_zero_of_ne hAQ) hu0
  have hE := rt_layOff' hA hQ hA hB hAQ hAB hε0.ne' hε
  set E := ε • (Q - A) + A with hEdef
  set d := D - A with hddef
  set e := E - A with hedef
  have hdv : d = δ • (P - A) := by rw [hddef, hDdef]; abel
  have hev : e = ε • (Q - A) := by rw [hedef, hEdef]; abel
  have hdd : ip d d = ip u u := by rw [hdv, ip_smul_left, ip_smul_right, ← mul_assoc, ← sq, hδ]
  have hee : ip e e = ip u u := by rw [hev, ip_smul_left, ip_smul_right, ← mul_assoc, ← sq, hε]
  have hud : crossProd2 u d ≠ 0 := by
    rw [hdv, cross_smul_right]; exact mul_ne_zero hδ0.ne' hc
  have hue : crossProd2 u e ≠ 0 := by
    rw [hev, cross_smul_right]; exact mul_ne_zero hε0.ne' hcQ
  have hde : crossProd2 d e ≠ 0 := by
    rw [hdv, hev, cross_smul_left, cross_smul_right, hQA, cross_add_right, cross_self,
      cross_smul_right, cross_comm (P - A) u]
    simp only [zero_add, mul_neg, neg_ne_zero]
    exact mul_ne_zero hδ0.ne' (mul_ne_zero hε0.ne' (mul_ne_zero two_ne_zero hc))
  -- the differences of the points
  have eDB : D - B = d - u := by rw [hddef, hu]; abel
  have eEC : E - C = e + u := by rw [hedef, show E - C = (E - A) - (C - A) by abel, hCA]; abel
  have eEB : E - B = e - u := by rw [hedef, hu]; abel
  have eDC : D - C = d + u := by rw [hddef, show D - C = (D - A) - (C - A) by abel, hCA]; abel
  have hcF : crossProd2 (D - B) (E - C) ≠ 0 := by
    rw [eDB, eEC]; exact cross_sub_add_ne hdd hee hud hue hde
  have hcH : crossProd2 (E - B) (D - C) ≠ 0 := by
    rw [eEB, eDC]
    exact cross_sub_add_ne hee hdd hue hud (by rw [cross_comm]; exact neg_ne_zero.2 hde)
  have hBD : B ≠ D := by intro h; rw [h, sub_self] at hcF; simp at hcF
  have hCE : C ≠ E := by intro h; rw [h, sub_self] at hcF; simp at hcF
  have hBE : B ≠ E := by intro h; rw [h, sub_self] at hcH; simp at hcH
  have hCD : C ≠ D := by intro h; rw [h, sub_self] at hcH; simp at hcH
  have hF := rt_inter hB hD hC hE hBD hCE hcF
  have hH := rt_inter hB hE hC hD hBE hCD hcH
  have eF := inter_eq hcF
  have eH := inter_eq hcH
  set sF := crossProd2 (C - B) (E - C) / crossProd2 (D - B) (E - C)
  set tF := crossProd2 (C - B) (D - B) / crossProd2 (D - B) (E - C)
  set sH := crossProd2 (C - B) (D - C) / crossProd2 (E - B) (D - C)
  set tH := crossProd2 (C - B) (E - B) / crossProd2 (E - B) (D - C)
  refine ⟨_, _, hF, hH, ?_, ?_⟩
  · intro hFH
    by_cases hs : sF = 0
    · -- `F = B` would lie on `CE`
      have hBF : B = tF • (E - C) + C := by
        have := eF; rw [hs, zero_smul, zero_add] at this; exact this
      have h2u : (2 : K) • u = tF • (e + u) := by
        rw [← eEC, show (2 : K) • u = B - C by rw [hu, hCdef]; apply ext2 <;> simp <;> ring]
        rw [hBF]; abel
      have := congrArg (crossProd2 u) h2u
      rw [cross_smul_right, cross_smul_right, cross_self, cross_add_right, cross_self,
        add_zero, mul_zero] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · rw [h, zero_smul] at h2u
        exact hu0 ((smul_eq_zero.1 h2u).resolve_left two_ne_zero)
      · exact hue h
    · have hrel : d - u = (sH / sF) • (e - u) := by
        rw [← eDB, ← eEB]
        have : sF • (D - B) = sH • (E - B) := add_right_cancel hFH
        rw [div_eq_inv_mul, ← smul_smul, ← this, smul_smul, inv_mul_cancel₀ hs, one_smul]
      have heu : e ≠ u := by intro h; rw [h, cross_self] at hue; exact hue rfl
      rcases circle_chord hdd hee heu hrel with h | h
      · rw [h, zero_smul, sub_eq_zero] at hrel; rw [hrel, cross_self] at hud; exact hud rfl
      · rw [h, one_smul, sub_left_inj] at hrel; rw [hrel, cross_self] at hde; exact hde rfl
  · have key := altitude_identity (sF • (D - B) + B) (sH • (E - B) + B) B C
    have hFB : sF • (D - B) + B - B = sF • (d - u) := by rw [eDB]; abel
    have hFC : sF • (D - B) + B - C = tF • (e + u) := by rw [eF, ← eEC]; abel
    have hHB : sH • (E - B) + B - B = sH • (e - u) := by rw [eEB]; abel
    have hHC : sH • (E - B) + B - C = tH • (d + u) := by rw [eH, ← eDC]; abel
    rw [hFB, hFC, hHB, hHC] at key
    simp only [ip_smul_left, ip_smul_right] at key
    have k1 : ip (d + u) (d - u) = 0 := by
      simp only [ip_add_left, ip_sub_right, hdd, ip_comm u d]; ring
    have k2 : ip (e - u) (e + u) = 0 := by
      simp only [ip_sub_left, ip_add_right, hee, ip_comm u e]; ring
    rw [k1, k2] at key
    have hBC : B - C = (2 : K) • u := by rw [hu, hCdef]; apply ext2 <;> simp <;> ring
    rw [hBC, ip_smul_right] at key
    have : (2 : K) * ip (sF • (D - B) + B - (sH • (E - B) + B)) u = 0 := by
      rw [key]; ring
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero

end RT

end Coord

end HilbertFoundations
