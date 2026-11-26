import HilbertFoundations.CommentaryCloseAux5

/-!
# The angle sum in the non-legendrian geometry (helper for `CommentaryClose.lean`)

`angleSumGt`: in the infinitesimal part of the elliptic plane (`EPt K`, `ELn K`,
CommentaryCloseAux4.lean) every triangle has angle sum greater than two right angles, in the sense
of `Conclusion.AngleSumGtTwoRight`.

For a triangle `a b c` (co-ordinates), with `Δ = dl a b c` twice its oriented area in the chart,
`p_a, p_b, p_c` the "cosine" components `Gf` of its angles and `w a, w b, w c` the lengths of the
lifts, the angle `α` is laid off at `c` on the prolongation of `ac` in the direction `yv`, the
remaining part of the exterior angle is laid off at `b` on `bc` in the direction `zv`, and `zv` falls
inside the angle `β` because of the identity (`excess_pos`)

`w_a w_b w_c Δ² - (w_a p_b p_c + w_b p_a p_c + w_c p_a p_b)
  = (w_b w_c - S_bc)(w_a w_c - S_ac)(w_a w_b - S_ab)(w_a w_b w_c + w_a S_bc + w_b S_ac + w_c S_ab)`,

whose right side is positive (the spherical excess).
-/

namespace HilbertFoundations

namespace Elliptic

open Coord Conclusion

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Twice the oriented area of the triangle `a b c` in the chart. -/
def dl (a b c : Coord K 2) : K := crossProd2 (b - a) (c - a)

/-- The "sine" component of the sum of the angles at `a` and `c`. -/
def mm (wa wc : K) (a b c : Coord K 2) : K :=
  wc * Gf a (b - a) (c - a) + wa * Gf c (a - c) (b - c)

/-- The "cosine" component of the rest of the exterior angle at `c`. -/
def cp (wa wc : K) (a b c : Coord K 2) : K :=
  wa * wc * dl a b c ^ 2 - Gf a (b - a) (c - a) * Gf c (a - c) (b - c)

/-- The direction at `c` making with the prolongation of `ac` the angle at `a`. -/
def yv (wa wc : K) (a b c : Coord K 2) : Coord K 2 :=
  (wc * Gf a (b - a) (c - a)) • (c - a) + (-(wa * dl a b c)) • jv c (c - a)

/-- The direction at `b` making with `bc` the rest of the exterior angle at `c`. -/
def zv (wa wb wc : K) (a b c : Coord K 2) : Coord K 2 :=
  (wb * cp wa wc a b c) • (c - b) + (dl a b c * mm wa wc a b c) • jv b (c - b)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_cycle1 (a b c : Coord K 2) : crossProd2 (c - b) (a - b) = dl a b c := by
  unfold dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_cycle2 (a b c : Coord K 2) : crossProd2 (c - a) (b - a) = -dl a b c := by
  unfold dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_cycle3 (a b c : Coord K 2) : crossProd2 (b - c) (c - a) = dl a b c := by
  unfold dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_cycle4 (a b c : Coord K 2) : crossProd2 (a - b) (c - b) = -dl a b c := by
  unfold dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_d_yv (wa wc : K) (a b c : Coord K 2) :
    crossProd2 (c - a) (yv wa wc a b c) = -(wa * dl a b c) * Gf c (c - a) (c - a) := by
  unfold yv; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_yv (wa wc : K) (a b c : Coord K 2) :
    crossProd2 (b - c) (yv wa wc a b c) = dl a b c * mm wa wc a b c := by
  unfold yv mm dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_yv (wa wc : K) (a b c : Coord K 2) :
    Gf c (b - c) (yv wa wc a b c) =
      -wc * Gf a (b - a) (c - a) * Gf c (a - c) (b - c) + wa * W c * dl a b c ^ 2 := by
  unfold yv dl; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_e_zv (wa wb wc : K) (a b c : Coord K 2) :
    crossProd2 (c - b) (zv wa wb wc a b c) =
      dl a b c * mm wa wc a b c * Gf b (c - b) (c - b) := by
  unfold zv; cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_a_zv (wa wb wc : K) (a b c : Coord K 2) :
    crossProd2 (a - b) (zv wa wb wc a b c) =
      -dl a b c * (wb * cp wa wc a b c - mm wa wc a b c * Gf b (c - b) (a - b)) := by
  have e : ∀ x y : K, crossProd2 (a - b) (x • (c - b) + y • jv b (c - b)) =
      -x * crossProd2 (b - a) (c - a) + y * Gf b (c - b) (a - b) := by
    intro x y; cring
  unfold zv; rw [e]; unfold dl; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_add_self (u y : Coord K 2) (c : K) :
    crossProd2 u (c • y + u) = c * crossProd2 u y := by
  simp only [crossProd2, xc_add, yc_add, xc_smul, yc_smul]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem excess_identity (wa wb wc x y z : K) :
    wa * wb * wc * (wa ^ 2 * wb ^ 2 * wc ^ 2 + 2 * z * x * y - wa ^ 2 * x ^ 2 - wb ^ 2 * y ^ 2 -
        wc ^ 2 * z ^ 2) - wb * (wa ^ 2 * x - z * y) * (wc ^ 2 * z - y * x) -
      (wc * (wa ^ 2 * x - z * y) + wa * (wc ^ 2 * z - y * x)) * (wb ^ 2 * y - x * z) =
    (wb * wc - x) * (wa * wc - y) * (wa * wb - z) * (wa * wb * wc + wa * x + wb * y + wc * z) := by
  ring

section Metric

variable [IsEuclidean K]

theorem kc_smul_left (P u v : Coord K 2) {c : K} (hc : 0 < c) : kc P (c • u) v = kc P u v := by
  rw [kc_comm, kc_smul_right _ _ _ hc, kc_comm]

theorem ww_sub_Sf_pos {P Q : Coord K 2} (h : Q ≠ P) : 0 < w P * w Q - Sf P Q := by
  have h1 := W_mul_W P Q
  have h2 := Gf_self_pos P (sub_ne_zero.2 h)
  have hw := mul_pos (w_pos P) (w_pos Q)
  have h3 : (w P * w Q) * (w P * w Q) = W P * W Q := by
    rw [mul_mul_mul_comm, w_mul_self, w_mul_self]
  by_contra hcon
  push Not at hcon
  have h4 : (w P * w Q) * (w P * w Q) ≤ Sf P Q * Sf P Q :=
    mul_self_le_mul_self hw.le (by linarith)
  nlinarith

/-- **The spherical excess is positive.** -/
theorem excess_pos {a b c : Coord K 2} (ha : InfPt a) (hb : InfPt b) (hc : InfPt c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    0 < w b * cp (w a) (w c) a b c - mm (w a) (w c) a b c * Gf b (c - b) (a - b) := by
  have key : w b * cp (w a) (w c) a b c - mm (w a) (w c) a b c * Gf b (c - b) (a - b) =
      (w b * w c - Sf b c) * (w a * w c - Sf a c) * (w a * w b - Sf a b) *
        (w a * w b * w c + w a * Sf b c + w b * Sf a c + w c * Sf a b) := by
    unfold cp mm dl
    rw [cr_sq_gram, Gf_cos a b c, Gf_cos c a b, Gf_cos b c a, Sf_comm c a, Sf_comm c b,
      Sf_comm b a, ← w_mul_self a, ← w_mul_self b, ← w_mul_self c]
    ring
  rw [key]
  have h1 := ww_sub_Sf_pos hbc.symm
  have h2 := ww_sub_Sf_pos hac.symm
  have h3 := ww_sub_Sf_pos hab.symm
  have hwa := w_pos a
  have hwb := w_pos b
  have hwc := w_pos c
  have s1 := Sf_pos hb hc
  have s2 := Sf_pos ha hc
  have s3 := Sf_pos ha hb
  have h4 : 0 < w a * w b * w c + w a * Sf b c + w b * Sf a c + w c * Sf a b := by positivity
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-- The direction `yv` at `c` makes with the prolongation of `ac` the angle at `a`. -/
theorem kc_d_yv {a b c : Coord K 2} (hca : c ≠ a) (hΔ : dl a b c ≠ 0) :
    kc c (c - a) (yv (w a) (w c) a b c) = kc a (c - a) (b - a) := by
  have hq : -(w a * dl a b c) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (w_pos a).ne' hΔ)
  have hpq : 0 < Gf a (b - a) (c - a) ^ 2 + (-(w a * dl a b c)) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hq)))
  have h1 : kc a (c - a) (b - a) = Gf a (b - a) (c - a) /
      rt (Gf a (b - a) (c - a) ^ 2 + (-(w a * dl a b c)) ^ 2) := by
    rw [kc_comm]
    refine kc_of_comp (k := 1) one_pos hpq (by rw [one_mul]) ?_
    unfold dl; rw [← w_mul_self a]; ring
  rw [h1]
  unfold yv
  exact kc_rot (sub_ne_zero.2 hca) _ _ hpq

/-- The directions `yv` at `c` and `zv` at `b` make equal angles with `cb` and `bc`. -/
theorem kc_yv_zv {a b c : Coord K 2} (hcb : c ≠ b) (hΔm : dl a b c * mm (w a) (w c) a b c ≠ 0) :
    kc c (yv (w a) (w c) a b c) (b - c) = kc b (zv (w a) (w b) (w c) a b c) (c - b) := by
  have hpq : 0 < cp (w a) (w c) a b c ^ 2 + (dl a b c * mm (w a) (w c) a b c) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hΔm)))
  have h1 : kc c (yv (w a) (w c) a b c) (b - c) = cp (w a) (w c) a b c /
      rt (cp (w a) (w c) a b c ^ 2 + (dl a b c * mm (w a) (w c) a b c) ^ 2) := by
    rw [kc_comm]
    refine kc_of_comp (k := w c) (w_pos c) hpq ?_ ?_
    · rw [Gf_yv]; unfold cp; rw [← w_mul_self c]; ring
    · rw [cr_yv, ← w_mul_self c]; ring
  have h2 : kc b (zv (w a) (w b) (w c) a b c) (c - b) = cp (w a) (w c) a b c /
      rt (cp (w a) (w c) a b c ^ 2 + (dl a b c * mm (w a) (w c) a b c) ^ 2) := by
    rw [kc_comm]
    unfold zv
    exact kc_rot (sub_ne_zero.2 hcb) _ _ hpq
  rw [h1, h2]

end Metric

/-! ### The angle sum -/

variable [HasInfinitesimal K] [IsEuclidean K]

/-- **Every triangle of the non-legendrian geometry has angle sum greater than two right
angles.** -/
theorem angleSumGt (A B C : EPt K) (h : IsTriangle (Line := ELn K) A B C) :
    AngleSumGtTwoRight (ELn K) A B C := by
  have hT : ¬Collinear (Line := CoordLine K 2) A.1 B.1 C.1 := fun hc => h (E_collinear_iff.2 hc)
  obtain ⟨hab, hac, hbc⟩ := AffPt.not_collinear_of_eq hT
  have hΔ : dl A.1 B.1 C.1 ≠ 0 := cr_ne_zero_of_not_collinear (fun hc => hT hc.swap12)
  have hΔ2 : 0 < dl A.1 B.1 C.1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hΔ))
  have hd : C.1 - A.1 ≠ 0 := sub_ne_zero.2 hac.symm
  have hGd := Gf_self_pos C.1 hd
  have hwA := w_pos A.1
  have hCA : C ≠ A := E_ne_iff.2 hac.symm
  have hBC : B ≠ C := E_ne_iff.2 hbc
  have hAB : A ≠ B := E_ne_iff.2 hab
  -- the point `X` on the prolongation of `AC`
  have hXinf : InfPt ((C.1 - A.1) + C.1) :=
    ⟨((E_inf C).1.sub (E_inf A).1).add (E_inf C).1, ((E_inf C).2.sub (E_inf A).2).add (E_inf C).2⟩
  obtain ⟨X, hX⟩ : ∃ X : EPt K, X.1 = (C.1 - A.1) + C.1 := ⟨⟨_, hXinf⟩, rfl⟩
  have hXC : X.1 - C.1 = C.1 - A.1 := by rw [hX, add_sub_cancel_right]
  have hXneC : X ≠ C := E_ne_iff.2 (fun e => hd (by rw [← hXC, e, sub_self]))
  have hACX : Between A C X := by
    show Between A.1 C.1 X.1
    rw [hX, AffPt.between_iff, AffPt.sbtw_iff_param]
    refine ⟨?_, 1 / 2, by norm_num, by norm_num, ?_⟩
    · intro e
      have hx := congrArg xc e
      have hy := congrArg yc e
      simp only [xc_add, xc_sub, yc_add, yc_sub] at hx hy
      exact hac (ext2 (by linarith) (by linarith))
    · apply ext2
      · simp only [xc_add, xc_smul, xc_sub]; ring
      · simp only [yc_add, yc_smul, yc_sub]; ring
  -- the point `Y`: the angle at `A` laid off at `C`
  have hcry := cr_d_yv (w A.1) (w C.1) A.1 B.1 C.1
  have hy0 : yv (w A.1) (w C.1) A.1 B.1 C.1 ≠ 0 := by
    intro e
    rw [e] at hcry
    have h0 : crossProd2 (C.1 - A.1) (0 : Coord K 2) = 0 := by cring
    rw [h0] at hcry
    exact (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hwA.ne' hΔ)) hGd.ne') hcry.symm
  obtain ⟨Y, c₁, hc₁, hY⟩ := exists_on_ray C hy0
  have hYa : Y.1 - A.1 = c₁ • yv (w A.1) (w C.1) A.1 B.1 C.1 + (C.1 - A.1) := by
    rw [← hY]; abel
  have hExt : ExteriorConfig (ELn K) A B C X Y := by
    refine ⟨hACX, ?_, ?_⟩
    · rw [E_angCong_iff, hXC, hY, kc_smul_right _ _ _ hc₁]
      exact (kc_d_yv hac.symm hΔ).symm
    · intro l hAl hCl
      rw [E_sameSide_iff_cr hAl hCl hCA, hYa, cr_add_self, hcry, cr_cycle2]
      have e : c₁ * (-(w A.1 * dl A.1 B.1 C.1) * Gf C.1 (C.1 - A.1) (C.1 - A.1)) *
          -dl A.1 B.1 C.1 = c₁ * w A.1 * Gf C.1 (C.1 - A.1) (C.1 - A.1) * dl A.1 B.1 C.1 ^ 2 := by
        ring
      rw [e]
      exact mul_pos (mul_pos (mul_pos hc₁ hwA) hGd) hΔ2
  refine ⟨h, X, Y, hExt, ?_⟩
  by_cases hint : Y ∈ Interior (Line := ELn K) X C B
  swap
  · exact Or.inl hint
  right
  -- the sum of the angles at `A` and `C` is less than two right angles
  obtain ⟨l₁, hCl₁, hXl₁⟩ := exists_line (Line := ELn K) hXneC.symm
  obtain ⟨l₂, hCl₂, hBl₂⟩ := exists_line (Line := ELn K) hBC.symm
  have hs2 := (hint l₁ l₂ hCl₁ hXl₁ hCl₂ hBl₂).2
  rw [E_sameSide_iff_cr hCl₂ hBl₂ hBC, hY, hXC, cr_smul_right, cr_yv, cr_cycle3] at hs2
  have hm : 0 < mm (w A.1) (w C.1) A.1 B.1 C.1 := by
    have e : c₁ * (dl A.1 B.1 C.1 * mm (w A.1) (w C.1) A.1 B.1 C.1) * dl A.1 B.1 C.1 =
        (c₁ * dl A.1 B.1 C.1 ^ 2) * mm (w A.1) (w C.1) A.1 B.1 C.1 := by ring
    rw [e] at hs2
    exact (pos_iff_pos_of_mul_pos hs2).1 (mul_pos hc₁ hΔ2)
  -- the point `Z`: the rest of the exterior angle laid off at `B`
  have he : C.1 - B.1 ≠ 0 := sub_ne_zero.2 hbc.symm
  have hGe := Gf_self_pos B.1 he
  have hcrz := cr_e_zv (w A.1) (w B.1) (w C.1) A.1 B.1 C.1
  have hΔm : dl A.1 B.1 C.1 * mm (w A.1) (w C.1) A.1 B.1 C.1 ≠ 0 := mul_ne_zero hΔ hm.ne'
  have hz0 : zv (w A.1) (w B.1) (w C.1) A.1 B.1 C.1 ≠ 0 := by
    intro e
    rw [e] at hcrz
    have h0 : crossProd2 (C.1 - B.1) (0 : Coord K 2) = 0 := by cring
    rw [h0] at hcrz
    exact (mul_ne_zero hΔm hGe.ne') hcrz.symm
  obtain ⟨Z, c₂, hc₂, hZ⟩ := exists_on_ray B hz0
  have hE := excess_pos (E_inf A) (E_inf B) (E_inf C) hab hac hbc
  refine ⟨Z, ?_, ?_⟩
  · show ∀ a b : ELn K, B ∈ a → C ∈ a → B ∈ b → A ∈ b → SameSide a Z A ∧ SameSide b Z C
    intro l₃ l₄ hBl₃ hCl₃ hBl₄ hAl₄
    constructor
    · rw [E_sameSide_iff_cr hBl₃ hCl₃ hBC.symm, hZ, cr_smul_right, hcrz, cr_cycle1]
      have e : c₂ * (dl A.1 B.1 C.1 * mm (w A.1) (w C.1) A.1 B.1 C.1 *
          Gf B.1 (C.1 - B.1) (C.1 - B.1)) * dl A.1 B.1 C.1 =
          c₂ * mm (w A.1) (w C.1) A.1 B.1 C.1 * Gf B.1 (C.1 - B.1) (C.1 - B.1) *
            dl A.1 B.1 C.1 ^ 2 := by ring
      rw [e]
      exact mul_pos (mul_pos (mul_pos hc₂ hm) hGe) hΔ2
    · rw [E_sameSide_iff_cr hBl₄ hAl₄ hAB, hZ, cr_smul_right, cr_a_zv, cr_cycle4]
      have e : c₂ * (-dl A.1 B.1 C.1 * (w B.1 * cp (w A.1) (w C.1) A.1 B.1 C.1 -
          mm (w A.1) (w C.1) A.1 B.1 C.1 * Gf B.1 (C.1 - B.1) (A.1 - B.1))) * -dl A.1 B.1 C.1 =
          c₂ * (w B.1 * cp (w A.1) (w C.1) A.1 B.1 C.1 -
            mm (w A.1) (w C.1) A.1 B.1 C.1 * Gf B.1 (C.1 - B.1) (A.1 - B.1)) *
            dl A.1 B.1 C.1 ^ 2 := by ring
      rw [e]
      exact mul_pos (mul_pos hc₂ hE) hΔ2
  · rw [E_angCong_iff, hY, hZ, kc_smul_left _ _ _ hc₁, kc_smul_left _ _ _ hc₂]
    exact kc_yv_zv hbc.symm hΔm

end Elliptic

end HilbertFoundations
