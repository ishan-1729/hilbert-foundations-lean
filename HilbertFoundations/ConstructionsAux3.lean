import HilbertFoundations.ConstructionsAux2

/-!
# Helper module for `Constructions.lean`: Theorem 40 in the coordinate plane

This module contains no unit of Hilbert's text. Over an ordered Pythagorean field `K`, in the
coordinate plane `Coord K 2`, it reduces Hilbert's problems 2, 4 and 5 to straight-edge and
transferer of segments:

* `rt_perp_through`: the perpendicular to a drawn line through any constructed point (Fig. 51 and
  Fig. 50), as soon as some constructed point lies outside the line;
* `rt_foot`: the foot of the perpendicular;
* `rt_angle_line`: problem 4, by laying off the two legs of a right triangle;
* `constr_imp_rt`, `rt_imp_constr`: **Theorem 40**, the elements constructible by problems 1–4
  (and by problem 5, when the given points are not all on one line) are exactly those
  constructible by straight-edge and transferer;
* `rt_collinear_of_axis`, `constr_perp_axis`: with two given points only, problem 5 leads outside
  the line, the straight-edge and transferer do not.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section RT

variable {S : Set (Coord K 2)}

/-- **The perpendicular through a constructed point** `X` to the drawn line `AB`, when a
constructed point `P` lies outside `AB`: a constructed point `Y ≠ X` with `XY ⊥ AB`. -/
theorem rt_perp_through [IsPythagorean K] {A B P X : Coord K 2} (hA : RulerTransferer S A)
    (hB : RulerTransferer S B) (hP : RulerTransferer S P) (hX : RulerTransferer S X)
    (hc : crossProd2 (B - A) (P - A) ≠ 0) :
    ∃ Y, RulerTransferer S Y ∧ Y ≠ X ∧ ip (Y - X) (B - A) = 0 := by
  obtain ⟨F, H, hF, hH, hFH, hip⟩ := rt_perp_exists hA hB hP hc
  have hip' : ip (H - F) (B - A) = 0 := by
    rw [show H - F = -(F - H) by abel, ip_neg_left, hip, neg_zero]
  by_cases hX' : crossProd2 (H - F) (X - F) = 0
  · obtain ⟨r, hr⟩ := (cross_eq_zero_iff (ne_zero_of_ne hFH)).1 hX'
    by_cases hXF : X = F
    · subst hXF; exact ⟨H, hH, hFH.symm, hip'⟩
    · refine ⟨F, hF, Ne.symm hXF, ?_⟩
      rw [show F - X = -(X - F) by abel, hr, ip_neg_left, ip_smul_left, hip', mul_zero, neg_zero]
  · refine ⟨X + (2 : K) • (H - F), rt_parallelPt hF hH hX hX', ?_, ?_⟩
    · intro e
      have : (2 : K) • (H - F) = 0 := by
        have := congrArg (· - X) e; simpa using this
      exact ne_zero_of_ne hFH ((smul_eq_zero.1 this).resolve_left two_ne_zero)
    · rw [add_sub_cancel_left, ip_smul_left, hip', mul_zero]

/-- **The foot of the perpendicular** from a constructed point `X` to the drawn line `AB` is
constructible (when a constructed point `P` lies outside `AB`). -/
theorem rt_foot [IsPythagorean K] {A B P X : Coord K 2} (hA : RulerTransferer S A)
    (hB : RulerTransferer S B) (hP : RulerTransferer S P) (hX : RulerTransferer S X)
    (hc : crossProd2 (B - A) (P - A) ≠ 0) :
    RulerTransferer S ((ip (X - A) (B - A) / ip (B - A) (B - A)) • (B - A) + A) := by
  have hAB : A ≠ B := by rintro rfl; simp at hc
  have hu := ne_zero_of_ne hAB
  by_cases hXl : crossProd2 (B - A) (X - A) = 0
  · have e := eq_smul_of_cross_eq_zero hu hXl
    rw [ip_comm] at e
    rw [← e]; simpa using hX
  · obtain ⟨Y, hY, hYX, hYip⟩ := rt_perp_through hA hB hP hX hc
    have hw := ne_zero_of_ne (Ne.symm hYX)
    have hcw : crossProd2 (B - A) (Y - X) ≠ 0 :=
      cross_ne_zero_of_ip hu hw (by rw [ip_comm]; exact hYip)
    refine rt_inter' hA hB hX hY hAB (Ne.symm hYX) hcw ?_ ?_
    · rw [add_sub_cancel_right, cross_smul_right, cross_self, mul_zero]
    · apply cross_eq_zero_of_ip hu hYip
      have hN := (ip_self_pos hu).ne'
      rw [show (ip (X - A) (B - A) / ip (B - A) (B - A)) • (B - A) + A - X =
        (ip (X - A) (B - A) / ip (B - A) (B - A)) • (B - A) - (X - A) by abel,
        ip_sub_left, ip_smul_left, div_mul_cancel₀ _ hN, sub_self]

/-- One of three non-collinear points lies outside a given line. -/
theorem exists_off_line {A O B O' A' : Coord K 2} (hn : ¬Collinear A O B) (h : O' ≠ A') :
    crossProd2 (A' - O') (A - O') ≠ 0 ∨ crossProd2 (A' - O') (O - O') ≠ 0 ∨
      crossProd2 (A' - O') (B - O') ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hc
  exact hn ⟨AffLine.through O' A' h, (mem_through_iff_cross h).2 h1,
    (mem_through_iff_cross h).2 h2, (mem_through_iff_cross h).2 h3⟩

theorem exists_rt_off_line {A O B O' A' : Coord K 2} (hA : RulerTransferer S A)
    (hO : RulerTransferer S O) (hB : RulerTransferer S B) (hn : ¬Collinear A O B)
    (h : O' ≠ A') : ∃ P, RulerTransferer S P ∧ crossProd2 (A' - O') (P - O') ≠ 0 := by
  rcases exists_off_line hn h with h | h | h
  · exact ⟨A, hA, h⟩
  · exact ⟨O, hO, h⟩
  · exact ⟨B, hB, h⟩

/-- For `N ⊥ a` in the plane, `(b × N)² |a|² = ⟪b, a⟫² |N|²`. -/
theorem cross_sq_of_perp {a N : Coord K 2} (ha : a ≠ 0) (hN : ip N a = 0) (b : Coord K 2) :
    crossProd2 b N ^ 2 * ip a a = ip b a ^ 2 * ip N N := by
  have hr : rot90 a ≠ 0 := by
    intro h; apply ha
    have h1 := congrArg xc h; have h2 := congrArg yc h
    simp at h1 h2; apply ext2 <;> simp [h1, h2]
  have hra : ip (rot90 a) a = 0 := by simp only [ip_two, xc_rot90, yc_rot90]; ring
  have hc := cross_eq_zero_of_ip ha hra hN
  obtain ⟨l, hl⟩ := (cross_eq_zero_iff hr).1 hc
  subst hl
  simp only [crossProd2_def, ip_two, xc_smul, yc_smul, xc_rot90, yc_rot90]; ring

/-- **Problem 4 by straight-edge and transferer**: a line through the constructed point `O'` that
forms with the half-ray `O'A'` an angle congruent to the angle `AOB` (with constructed `A, O, B`)
contains a constructed point `Z ≠ O'`. The construction: drop the perpendicular from `B` to `OA`
(foot `D`), lay off `OD` on `O'A'` (point `D'`), erect the perpendicular in `D'` and lay off `DB`
on it, on both sides. -/
theorem rt_angle_line [IsPythagorean K] {A O B A' O' B' : Coord K 2} (hA : RulerTransferer S A)
    (hO : RulerTransferer S O) (hB : RulerTransferer S B) (hA' : RulerTransferer S A')
    (hO' : RulerTransferer S O') (hn : ¬Collinear A O B) (hn' : ¬Collinear A' O' B')
    (hang : AngCong A O B A' O' B') :
    ∃ Z, RulerTransferer S Z ∧ Z ≠ O' ∧ crossProd2 (B' - O') (Z - O') = 0 := by
  have hm : crossProd2 (A - O) (B - O) ≠ 0 := cross_ne_zero_of_not_collinear (fun h => hn h.swap12)
  have hm' : crossProd2 (A' - O') (B' - O') ≠ 0 :=
    cross_ne_zero_of_not_collinear (fun h => hn' h.swap12)
  have hOA : O ≠ A := by intro e; rw [e, sub_self] at hm; simp at hm
  have hOB : O ≠ B := by intro e; rw [e, sub_self] at hm; simp at hm
  have hOA' : O' ≠ A' := by intro e; rw [e, sub_self] at hm'; simp at hm'
  have hOB' : O' ≠ B' := by intro e; rw [e, sub_self] at hm'; simp at hm'
  set u := A - O with hu
  set w := B - O with hw
  set a := A' - O' with ha
  set b := B' - O' with hb
  have hu0 : u ≠ 0 := ne_zero_of_ne hOA
  have ha0 : a ≠ 0 := ne_zero_of_ne hOA'
  have hNu := ip_self_pos hu0
  have hNa := ip_self_pos ha0
  set k := ip u w with hk
  set m := crossProd2 u w with hmdef
  rw [angCong_iff, AngleEq] at hang
  obtain ⟨hsign, hsq⟩ := hang
  -- the foot `D` of the perpendicular from `B` to `OA`
  have hD := rt_foot hO hA hB hB hm
  set D := (ip (B - O) (A - O) / ip (A - O) (A - O)) • (A - O) + O with hDdef
  have hDO : D - O = (k / ip u u) • u := by rw [hDdef, ip_comm]; abel
  have hDB : B - D = w - (k / ip u u) • u := by rw [hw, ← hDO]; abel
  have hBD : D ≠ B := by
    intro e
    have : w - (k / ip u u) • u = 0 := by rw [← hDB, e, sub_self]
    apply hm
    show crossProd2 u w = 0
    rw [show w = (k / ip u u) • u by rw [← sub_eq_zero]; exact this, cross_smul_right, cross_self,
      mul_zero]
  have hBD2 : ip (B - D) (B - D) = m ^ 2 / ip u u := by
    rw [hDB]
    have L := ip_sq_add_cross_sq u w
    rw [show m ^ 2 = ip u u * ip w w - k ^ 2 by rw [← L]; ring]
    have hNu' := hNu.ne'
    simp only [ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_comm w u]
    field_simp
    ring
  -- the lengths `|u|`, `|a|`
  obtain ⟨ru, hru0, hru⟩ := IsPythagorean.exists_sqrt_of_isSumSq (isSumSq_ip_self u)
  obtain ⟨ra, hra0, hra⟩ := IsPythagorean.exists_sqrt_of_isSumSq (isSumSq_ip_self a)
  have hru' : ru ≠ 0 := by rintro rfl; rw [← hru] at hNu; simp at hNu
  have hra' : ra ≠ 0 := by rintro rfl; rw [← hra] at hNa; simp at hNa
  -- the point `D'` on `O'A'` with `O'D' = OD`
  set τ := k / (ru * ra) with hτ
  have hD' : RulerTransferer S (τ • a + O') := by
    by_cases hk0 : k = 0
    · rw [hτ, hk0, zero_div, zero_smul, zero_add]; exact hO'
    · have hDO' : O ≠ D := by
        intro e
        have : (k / ip u u) • u = 0 := by rw [← hDO, ← e, sub_self]
        rcases smul_eq_zero.1 this with h | h
        · exact hk0 ((div_eq_zero_iff.1 h).resolve_right hNu.ne')
        · exact hu0 h
      refine rt_layOff' hO' hA' hO hD hOA' hDO' (div_ne_zero hk0 (mul_ne_zero hru' hra')) ?_
      rw [hDO, ip_smul_left, ip_smul_right, hτ, ← hra]
      rw [← hru]; field_simp
  -- the perpendicular in `D'`
  obtain ⟨P, hP, hPc⟩ := exists_rt_off_line hA hO hB hn hOA'
  obtain ⟨Y, hY, hYD, hYip⟩ := rt_perp_through hO' hA' hP hD' hPc
  set n := Y - (τ • a + O') with hn
  have hn0 : n ≠ 0 := sub_ne_zero.2 hYD
  obtain ⟨ρ, hρ0, hρ⟩ := exists_layoff_param hn0 (ne_zero_of_ne hBD)
  have hZp := rt_layOff' hD' hY hD hB (Ne.symm hYD) hBD hρ0.ne' hρ
  have hZm := rt_layOff' (t := -ρ) hD' hY hD hB (Ne.symm hYD) hBD (neg_ne_zero.2 hρ0.ne')
    (by rw [neg_sq]; exact hρ)
  set N := ρ • n with hNdef
  have hNa' : ip N a = 0 := by rw [hNdef, ip_smul_left, hYip, mul_zero]
  have hNN : ip N N = m ^ 2 / ip u u := by
    rw [hNdef, ip_smul_left, ip_smul_right, ← mul_assoc, ← sq, hρ, hBD2]
  have hN0 : N ≠ 0 := by
    rw [hNdef]; exact smul_ne_zero hρ0.ne' hn0
  -- the two candidates `O' + τ a ± N`
  have eZp : ρ • (Y - (τ • a + O')) + (τ • a + O') - O' = τ • a + N := by rw [hNdef]; abel
  have eZm : (-ρ) • (Y - (τ • a + O')) + (τ • a + O') - O' = τ • a - N := by
    rw [hNdef, neg_smul]; abel
  have hcT : crossProd2 b (τ • a) ^ 2 * ip a a = crossProd2 b N ^ 2 * ip a a := by
    rw [cross_sq_of_perp ha0 hNa' b, cross_smul_right, mul_pow]
    have L := ip_sq_add_cross_sq a b
    rw [cross_comm b a, neg_sq, ip_comm b a, hNN, hτ, div_pow, mul_pow, hru, hra]
    have hsq' : k ^ 2 * (ip a a * ip b b) = ip a b ^ 2 * (ip u u * ip w w) := hsq
    have L2 := ip_sq_add_cross_sq u w
    have key : k ^ 2 * crossProd2 a b ^ 2 = ip a b ^ 2 * m ^ 2 := by
      linear_combination hsq' + k ^ 2 * L - ip a b ^ 2 * L2
    have hNu' := hNu.ne'
    have hNa' := hNa.ne'
    calc k ^ 2 / (ip u u * ip a a) * crossProd2 a b ^ 2 * ip a a
        = (k ^ 2 * crossProd2 a b ^ 2) / ip u u := by field_simp
      _ = (ip a b ^ 2 * m ^ 2) / ip u u := by rw [key]
      _ = ip a b ^ 2 * (m ^ 2 / ip u u) := by ring
  have hprod : crossProd2 b (τ • a + N) * crossProd2 b (τ • a - N) = 0 := by
    rw [cross_add_right, cross_sub_right]
    have : crossProd2 b (τ • a) ^ 2 = crossProd2 b N ^ 2 :=
      mul_right_cancel₀ hNa.ne' hcT
    linear_combination this
  have hZne : ∀ s : K, s ≠ 0 → τ • a + s • N ≠ 0 := by
    intro s hs e
    have := congrArg (fun v => ip v a) e
    simp only [ip_add_left, ip_smul_left, hNa', mul_zero, add_zero, ip_zero_left] at this
    have hτ0 : τ = 0 := (mul_eq_zero.1 this).resolve_right hNa.ne'
    rw [hτ0, zero_smul, zero_add] at e
    exact hN0 ((smul_eq_zero.1 e).resolve_left hs)
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨_, hZp, ?_, by rw [eZp]; exact h⟩
    intro e; apply hZne 1 one_ne_zero
    rw [one_smul, ← eZp, e, sub_self]
  · refine ⟨_, hZm, ?_, by rw [eZm]; exact h⟩
    intro e; apply hZne (-1) (by norm_num)
    rw [neg_one_smul, ← sub_eq_add_neg, ← eZm, e, sub_self]

/-! ### Theorem 40 -/

/-- Every point constructible by straight-edge and transferer is constructible by problems
1–4. -/
theorem rt_imp_constr {p5 : Prop} {X : Coord K 2} (h : RulerTransferer S X) :
    Constr (L := CoordLine K 2) p5 S (.inl X) := by
  induction h with
  | given hA => exact Constr.given hA
  | @meet A B C D X a b _ _ _ _ hAB hCD hAa hBa hCb hDb hab hXa hXb iA iB iC iD =>
    exact Constr.meet (Constr.join iA iB hAB hAa hBa) (Constr.join iC iD hCD hCb hDb) hab hXa hXb
  | @layOff A B O Q X a _ _ _ _ hAB hOQ hOa hQa hXa hXO hseg iA iB iO iQ =>
    exact Constr.layOff iA iB iO (Constr.join iO iQ hOQ hOa hQa) hAB hOa hXa hXO hseg

theorem rtLine_imp_constr {p5 : Prop} {a : CoordLine K 2} (h : RulerTransfererLine S a) :
    Constr p5 S (.inr a) := by
  obtain ⟨A, B, hA, hB, hAB, hAa, hBa⟩ := h
  exact Constr.join (rt_imp_constr hA) (rt_imp_constr hB) hAB hAa hBa

/-- Every element constructible by problems 1–4 (and by problem 5, if three non-collinear points
are constructible) is constructible by straight-edge and transferer. -/
theorem constr_imp_rt [IsPythagorean K] {p5 : Prop}
    (hp5 : p5 → ∃ A O B : Coord K 2, RulerTransferer S A ∧ RulerTransferer S O ∧
      RulerTransferer S B ∧ ¬Collinear A O B)
    {e : Coord K 2 ⊕ CoordLine K 2} (h : Constr p5 S e) :
    Sum.elim (RulerTransferer S) (RulerTransfererLine S) e := by
  induction h with
  | given hA => exact RulerTransferer.given hA
  | @join A B a _ _ hAB hAa hBa iA iB => exact ⟨A, B, iA, iB, hAB, hAa, hBa⟩
  | @meet a b X _ _ hab hXa hXb ia ib =>
    obtain ⟨A, B, hA, hB, hAB, hAa, hBa⟩ := ia
    obtain ⟨C, D, hC, hD, hCD, hCb, hDb⟩ := ib
    exact RulerTransferer.meet hA hB hC hD hAB hCD hAa hBa hCb hDb hab hXa hXb
  | @parallel A a b _ _ hAa hAb hpar iA ia =>
    obtain ⟨A1, B1, h1, h2, h12, h1a, h2a⟩ := ia
    have hc : crossProd2 (B1 - A1) (A - A1) ≠ 0 := fun h =>
      hAa ((mem_line_iff_cross h12 h1a h2a).2 h)
    have hQ := rt_parallelPt h1 h2 iA hc
    have hu := ne_zero_of_ne h12
    have hAQ : A ≠ A + (2 : K) • (B1 - A1) := by
      intro e
      have : (2 : K) • (B1 - A1) = 0 := by have := congrArg (· - A) e; simpa using this.symm
      exact hu ((smul_eq_zero.1 this).resolve_left two_ne_zero)
    refine ⟨A, A + (2 : K) • (B1 - A1), iA, hQ, hAQ, hAb, ?_⟩
    have hnm : ¬Meets (Point := Coord K 2) (AffLine.through A _ hAQ) a := by
      rintro ⟨X, hXb, hXa⟩
      rw [mem_through_iff_cross] at hXb
      rw [mem_line_iff_cross h12 h1a h2a] at hXa
      rw [add_sub_cancel_left] at hXb
      obtain ⟨r, hr⟩ := (cross_eq_zero_iff (smul_ne_zero two_ne_zero hu)).1 hXb
      apply hc
      rw [show X - A1 = (X - A) + (A - A1) by abel, cross_add_right, hr, cross_smul_right,
        cross_smul_right, cross_self, mul_zero, mul_zero, zero_add] at hXa
      exact hXa
    have hb : ¬Meets (Point := Coord K 2) b a := fun ⟨X, h1, h2⟩ => hpar ⟨X, h2, h1⟩
    obtain ⟨b0, -, huniq⟩ := exists_unique_parallel (Point := Coord K 2) (Line := CoordLine K 2) hAa
    have e1 := huniq b ⟨hAb, hb⟩
    have e2 := huniq _ ⟨AffLine.left_mem_through hAQ, hnm⟩
    rw [e1, ← e2]; exact AffLine.right_mem_through hAQ
  | @layOff A B O X a _ _ _ _ hAB hOa hXa hXO hseg iA iB iO ia =>
    obtain ⟨A1, B1, h1, h2, h12, h1a, h2a⟩ := ia
    by_cases hO1 : O = A1
    · exact RulerTransferer.layOff iA iB iO h2 hAB (by rw [hO1]; exact h12) hOa h2a hXa hXO hseg
    · exact RulerTransferer.layOff iA iB iO h1 hAB hO1 hOa h1a hXa hXO hseg
  | @angle A O B A' O' B' b _ _ _ _ _ hn hn' hang hO'b hB'b iA iO iB iA' iO' =>
    obtain ⟨Z, hZ, hZO, hZc⟩ := rt_angle_line iA iO iB iA' iO' hn hn' hang
    have hm' : crossProd2 (A' - O') (B' - O') ≠ 0 :=
      cross_ne_zero_of_not_collinear (fun h => hn' h.swap12)
    have hOB' : O' ≠ B' := by intro e; rw [e, sub_self] at hm'; simp at hm'
    refine ⟨O', Z, iO', hZ, hZO.symm, hO'b, ?_⟩
    rw [mem_line_iff_cross hOB' hO'b hB'b]; exact hZc
  | @perp A a b hp _ _ hAb hperp iA ia =>
    obtain ⟨T1, T2, T3, h1, h2, h3, hn⟩ := hp5 hp
    obtain ⟨A1, B1, hA1, hB1, h12, h1a, h2a⟩ := ia
    obtain ⟨P, hP, hPc⟩ := exists_rt_off_line h1 h2 h3 hn h12
    obtain ⟨Y, hY, hYA, hYip⟩ := rt_perp_through hA1 hB1 hP iA hPc
    obtain ⟨O0, A0, B0, hO0a, hA0a, hO0b, hB0b, hR⟩ := hperp
    rw [isRightAngle_iff] at hR
    obtain ⟨hA0O, hB0O, hip⟩ := hR
    refine ⟨A, Y, iA, hY, hYA.symm, hAb, ?_⟩
    have hu := ne_zero_of_ne h12
    rw [mem_line_iff_cross hB0O.symm hO0b hB0b] at hAb ⊢
    have hO0 := (mem_line_iff_cross h12 h1a h2a).1 hO0a
    have hA0 := (mem_line_iff_cross h12 h1a h2a).1 hA0a
    have hd : crossProd2 (B1 - A1) (A0 - O0) = 0 := by
      rw [show A0 - O0 = (A0 - A1) - (O0 - A1) by abel, cross_sub_right, hA0, hO0, sub_zero]
    obtain ⟨r, hr⟩ := (cross_eq_zero_iff hu).1 hd
    have hr0 : r ≠ 0 := by
      rintro rfl; rw [zero_smul] at hr; exact hA0O (sub_eq_zero.1 hr)
    have hperp' : ip (B0 - O0) (B1 - A1) = 0 := by
      rw [hr, ip_comm, ip_smul_right] at hip
      exact (mul_eq_zero.1 hip).resolve_left hr0
    have k := cross_eq_zero_of_ip hu hperp' hYip
    rw [show Y - O0 = (Y - A) + (A - O0) by abel, cross_add_right, k, hAb, add_zero]

/-- **Theorem 40 in the coordinate plane** over an ordered Pythagorean field: the points and lines
constructible by problems 1–4 are exactly those constructible by straight-edge and transferer of
segments; with problem 5 as well, provided the given points are not all on one line. -/
theorem theorem40_coord [IsPythagorean K] {p5 : Prop} (S : Set (Coord K 2))
    (hp5 : p5 → ∃ A O B : Coord K 2, A ∈ S ∧ O ∈ S ∧ B ∈ S ∧ ¬Collinear A O B) :
    (∀ X : Coord K 2, Constr (L := CoordLine K 2) p5 S (.inl X) ↔ RulerTransferer S X) ∧
      ∀ a : CoordLine K 2, Constr p5 S (.inr a) ↔ RulerTransfererLine S a := by
  have hp5' : p5 → ∃ A O B : Coord K 2, RulerTransferer S A ∧ RulerTransferer S O ∧
      RulerTransferer S B ∧ ¬Collinear A O B := fun hp => by
    obtain ⟨A, O, B, hA, hO, hB, hn⟩ := hp5 hp
    exact ⟨A, O, B, .given hA, .given hO, .given hB, hn⟩
  exact ⟨fun X => ⟨fun h => constr_imp_rt hp5' h, rt_imp_constr⟩,
    fun a => ⟨fun h => constr_imp_rt hp5' h, rtLine_imp_constr⟩⟩

/-! ### Two given points: problem 5 is not reducible -/

/-- The axis `y = 0`. -/
noncomputable def xAxis : CoordLine K 2 :=
  AffLine.through (pt2 0 0) (pt2 1 0) (by intro e; have := congrArg xc e; simp at this)

/-- The axis `x = 0`. -/
noncomputable def yAxis : CoordLine K 2 :=
  AffLine.through (pt2 0 0) (pt2 0 1) (by intro e; have := congrArg yc e; simp at this)

theorem mem_xAxis {X : Coord K 2} : X ∈ (xAxis : CoordLine K 2) ↔ yc X = 0 := by
  rw [xAxis, mem_through_iff_cross]; simp [crossProd2_def]

theorem mem_yAxis {X : Coord K 2} : X ∈ (yAxis : CoordLine K 2) ↔ xc X = 0 := by
  rw [yAxis, mem_through_iff_cross]; simp [crossProd2_def]

/-- From the two points `(0, 0)`, `(1, 0)` the straight-edge and transferer construct only points
of the axis `y = 0`. -/
theorem rt_axis {X : Coord K 2}
    (h : RulerTransferer ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) X) : yc X = 0 := by
  induction h with
  | given hA =>
    rcases hA with rfl | rfl <;> simp
  | @meet A B C D X a b _ _ _ _ hAB hCD hAa hBa hCb hDb hab hXa hXb iA iB iC iD =>
    exfalso; apply hab
    have ha := line_unique hAB hAa hBa (mem_xAxis.2 iA) (mem_xAxis.2 iB)
    have hb := line_unique hCD hCb hDb (mem_xAxis.2 iC) (mem_xAxis.2 iD)
    rw [ha, hb]
  | @layOff A B O Q X a _ _ _ _ hAB hOQ hOa hQa hXa hXO hseg iA iB iO iQ =>
    have ha := line_unique hOQ hOa hQa (mem_xAxis.2 iO) (mem_xAxis.2 iQ)
    rw [ha] at hXa; exact mem_xAxis.1 hXa

/-- With the two given points `(0, 0)`, `(1, 0)`, problem 5 constructs the axis `x = 0`. -/
theorem constr_perp_yAxis :
    Constr (L := CoordLine K 2) True ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (.inr yAxis) := by
  have h01 : (pt2 0 0 : Coord K 2) ≠ pt2 1 0 := by
    intro e; have := congrArg xc e; simp at this
  have hO : Constr (L := CoordLine K 2) True ({pt2 0 0, pt2 1 0} : Set (Coord K 2))
      (.inl (pt2 0 0)) := Constr.given (by simp)
  have hE : Constr (L := CoordLine K 2) True ({pt2 0 0, pt2 1 0} : Set (Coord K 2))
      (.inl (pt2 1 0)) := Constr.given (by simp)
  refine Constr.perp trivial hO (Constr.join hO hE h01 (mem_xAxis.2 (by simp))
    (mem_xAxis.2 (by simp))) (mem_yAxis.2 (by simp)) ?_
  refine ⟨pt2 0 0, pt2 1 0, pt2 0 1, mem_xAxis.2 (by simp), mem_xAxis.2 (by simp),
    mem_yAxis.2 (by simp), mem_yAxis.2 (by simp), ?_⟩
  rw [isRightAngle_iff]
  refine ⟨h01.symm, ?_, ?_⟩
  · intro e; have := congrArg yc e; simp at this
  · simp [ip_two]

/-- … but the axis `x = 0` cannot be drawn with straight-edge and transferer. -/
theorem not_rtLine_yAxis :
    ¬RulerTransfererLine ({pt2 0 0, pt2 1 0} : Set (Coord K 2)) (yAxis : CoordLine K 2) := by
  rintro ⟨A, B, hA, hB, hAB, hAa, hBa⟩
  apply hAB
  apply ext2
  · rw [mem_yAxis.1 hAa, mem_yAxis.1 hBa]
  · rw [rt_axis hA, rt_axis hB]

end RT

end Coord

end HilbertFoundations
