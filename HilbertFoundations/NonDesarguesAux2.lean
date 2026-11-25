import HilbertFoundations.NonDesarguesAux

/-!
# The Moulton plane: congruence of segments and Archimedes's axiom (helper for `NonDesargues.lean`)

Hilbert's convention of § 23: "we will call two segments `AB` and `A'B'` congruent in this new
geometry, if the broken line extending between `A` and `B` has equal length, in the ordinary sense
of the word, with the broken line extending from `A'` to `B'`." The length of the broken line
between two points of a line is `segLen A B = |lam ℓ A - lam ℓ B|` (the parameter `lam` is the arc
length of the broken line); `segLen_eq_edist_left`, `segLen_eq_edist_right` and `segLen_add` show
that it is the ordinary length of the broken line. We prove IV 1–3 and V.
-/

namespace HilbertFoundations

namespace Moulton

/-! ### Length of the broken line between two points -/

/-- **The length of the broken line from `A` to `B`** (on the line through them). -/
noncomputable def segLen (A B : Pt) : ℝ := |lam (through A B) A - lam (through A B) B|

theorem segLen_eq {ℓ : Ln} {A B : Pt} (hA : A ∈ ℓ) (hB : B ∈ ℓ) :
    segLen A B = |lam ℓ A - lam ℓ B| := by
  by_cases h : A = B
  · subst h; simp [segLen]
  · rw [segLen, eq_through h hA hB]

theorem segLen_comm (A B : Pt) : segLen A B = segLen B A := by
  rw [segLen_eq (left_mem_through A B) (right_mem_through A B),
    segLen_eq (right_mem_through A B) (left_mem_through A B), abs_sub_comm]

theorem segLen_pos {A B : Pt} (h : A ≠ B) : 0 < segLen A B := by
  rw [segLen, abs_pos, sub_ne_zero]
  exact lam_ne (left_mem_through A B) (right_mem_through A B) h

/-- **Additivity** of the length of broken lines. -/
theorem segLen_add {A B C : Pt} (h : Btw A B C) : segLen A C = segLen A B + segLen B C := by
  obtain ⟨ℓ, hA, hB, hC, hs⟩ := h
  rw [segLen_eq hA hC, segLen_eq hA hB, segLen_eq hB hC]
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]; ring

/-- Ordinary (Euclidean) distance of two points. -/
noncomputable def edist (P Q : Pt) : ℝ := √((P.x - Q.x) ^ 2 + (P.y - Q.y) ^ 2)

/-- On the left part (`x ≤ 0`) of a broken line, `segLen` is the ordinary distance. -/
theorem segLen_eq_edist_left {m b : ℝ} {P Q : Pt} (hP : P ∈ Ln.graph m b) (hQ : Q ∈ Ln.graph m b)
    (hPx : P.x ≤ 0) (hQx : Q.x ≤ 0) : segLen P Q = edist P Q := by
  rw [segLen_eq hP hQ]
  simp only [mem_graph] at hP hQ
  simp only [lam, ulen, min_eq_left hPx, min_eq_left hQx, max_eq_right hPx, max_eq_right hQx,
    edist, hP, hQ, ht_of_nonpos hPx, ht_of_nonpos hQx]
  have : (b + m * P.x - (b + m * Q.x)) = m * (P.x - Q.x) := by ring
  rw [this, show (P.x - Q.x) ^ 2 + (m * (P.x - Q.x)) ^ 2 = (1 + m ^ 2) * (P.x - Q.x) ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, sL]
  simp only [mul_zero, add_zero]
  rw [← mul_sub, abs_mul, abs_of_pos (Real.sqrt_pos.2 (by positivity))]

/-- On the right part (`x ≥ 0`) of a broken line, `segLen` is the ordinary distance. -/
theorem segLen_eq_edist_right {m b : ℝ} {P Q : Pt} (hP : P ∈ Ln.graph m b)
    (hQ : Q ∈ Ln.graph m b) (hPx : 0 ≤ P.x) (hQx : 0 ≤ Q.x) : segLen P Q = edist P Q := by
  rw [segLen_eq hP hQ]
  simp only [mem_graph] at hP hQ
  simp only [lam, ulen, min_eq_right hPx, min_eq_right hQx, max_eq_left hPx, max_eq_left hQx,
    edist, hP, hQ, ht_of_nonneg hPx, ht_of_nonneg hQx]
  have : (b + tr m * P.x - (b + tr m * Q.x)) = tr m * (P.x - Q.x) := by ring
  rw [this, show (P.x - Q.x) ^ 2 + (tr m * (P.x - Q.x)) ^ 2
      = (1 + tr m ^ 2) * (P.x - Q.x) ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, sR]
  simp only [mul_zero, zero_add]
  rw [← mul_sub, abs_mul, abs_of_pos (Real.sqrt_pos.2 (by positivity))]

/-- On a vertical line, `segLen` is the ordinary distance. -/
theorem segLen_eq_edist_vert {c : ℝ} {P Q : Pt} (hP : P ∈ Ln.vert c) (hQ : Q ∈ Ln.vert c) :
    segLen P Q = edist P Q := by
  rw [segLen_eq hP hQ]
  simp only [mem_vert] at hP hQ
  simp [lam, edist, hP, hQ, Real.sqrt_sq_eq_abs]

/-! ### Sides of a point on a line -/

theorem sameSidePt_iff {ℓ : Ln} {O C X : Pt} (hO : O ∈ ℓ) (hC : C ∈ ℓ) (hOC : O ≠ C) :
    SameSidePt O C X ↔ X ∈ ℓ ∧ X ≠ O ∧ 0 < (lam ℓ X - lam ℓ O) * (lam ℓ C - lam ℓ O) := by
  unfold SameSidePt
  constructor
  · rintro ⟨-, hXO, ⟨ℓ', hC', hO', hX'⟩, hnb⟩
    have := eq_of_mem hOC hO' hC' hO hC
    subst this
    refine ⟨hX', hXO, ?_⟩
    rw [between_iff_btw, btw_iff hC' hO' hX'] at hnb
    have h1 := lam_ne hX' hO' hXO
    have h2 := lam_ne hC' hO' (Ne.symm hOC)
    unfold SB at hnb
    rcases lt_or_gt_of_ne h1 with h1 | h1 <;> rcases lt_or_gt_of_ne h2 with h2 | h2
    · nlinarith
    · exact (hnb (Or.inr ⟨h1, h2⟩)).elim
    · exact (hnb (Or.inl ⟨h2, h1⟩)).elim
    · nlinarith
  · rintro ⟨hX, hXO, hpos⟩
    refine ⟨Ne.symm hOC, hXO, ⟨ℓ, hC, hO, hX⟩, ?_⟩
    rw [between_iff_btw, btw_iff hC hO hX]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith

/-! ### Congruence of segments: axioms IV 1–3 -/

/-- **Congruence of segments** (§ 23): equal length of the broken lines. -/
noncomputable instance instHasSegCong : HasSegCong Pt := ⟨fun A B A' B' => segLen A B = segLen A' B'⟩

theorem segCong_iff {A B A' B' : Pt} : SegCong A B A' B' ↔ segLen A B = segLen A' B' := Iff.rfl

/-- If `AB` and `BC` have only `B` in common, `B` lies between `A` and `C`. -/
theorem btw_of_meetOnlyAt {A B C : Pt} (h : SegmentsMeetOnlyAt A B C) : Btw A B C := by
  obtain ⟨⟨ℓ, hA, hB, hC⟩, hAB, hBC, hX⟩ := h
  by_cases hAC : A = C
  · subst hAC
    exact (hAB (hX A (Or.inl rfl) (Or.inr (Or.inl rfl)))).elim
  have h1 := lam_ne hA hB hAB
  have h2 := lam_ne hA hC hAC
  have h3 := lam_ne hB hC hBC
  rw [btw_iff hA hB hC]
  have := (order_three h1 h2 h3).1
  rcases this with h | h | h
  · -- `A` between `B` and `C`
    have hb : Btw B A C := (btw_iff hB hA hC).2 h
    exact (hAB (hX A (Or.inl rfl) (Or.inr (Or.inr hb)))).elim
  · exact h
  · -- `C` between `A` and `B`
    have hb : Btw A C B := (btw_iff hA hC hB).2 h
    exact (hBC.symm (hX C (Or.inr (Or.inr hb)) (Or.inr (Or.inl rfl)))).elim

/-- **The linear axioms of congruence IV 1–3** hold in the Moulton plane. -/
instance instSegmentCongruence : SegmentCongruence Pt Ln where
  segCong_swap A B A' B' h := by
    simp only [segCong_iff] at *
    exact ⟨by rw [segLen_comm, h], by rw [h, segLen_comm]⟩
  ax_IV1 A B A' C' hAB hAC := by
    set ℓ := through A' C'
    have hA' := left_mem_through A' C'
    have hC' := right_mem_through A' C'
    have hd := segLen_pos hAB
    set d := segLen A B
    set ε : ℝ := if lam ℓ A' < lam ℓ C' then 1 else -1 with hε
    have hne := lam_ne hA' hC' hAC
    have hεC : 0 < ε * (lam ℓ C' - lam ℓ A') := by
      rw [hε]; split_ifs with h
      · linarith
      · push Not at h; have := lt_of_le_of_ne h (Ne.symm hne); linarith
    have hε2 : ε * ε = 1 := by rw [hε]; split_ifs <;> norm_num
    refine ⟨gam ℓ (lam ℓ A' + ε * d), ⟨?_, ?_⟩, ?_⟩
    · rw [sameSidePt_iff hA' hC' hAC, lam_gam]
      refine ⟨gam_mem ℓ _, fun e => ?_, ?_⟩
      · have := congrArg (lam ℓ) e; rw [lam_gam] at this
        have : ε * d = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · simp [h] at hε2
        · linarith
      · have : lam ℓ A' + ε * d - lam ℓ A' = ε * d := by ring
        rw [this, show ε * d * (lam ℓ C' - lam ℓ A') = d * (ε * (lam ℓ C' - lam ℓ A')) by ring]
        positivity
    · show d = segLen A' _
      rw [segLen_eq hA' (gam_mem ℓ _), lam_gam]
      have : lam ℓ A' - (lam ℓ A' + ε * d) = -(ε * d) := by ring
      rw [this, abs_neg, abs_mul, abs_of_pos hd]
      rw [hε]; split_ifs <;> simp
    · rintro Y ⟨hs, hc⟩
      rw [sameSidePt_iff hA' hC' hAC] at hs
      obtain ⟨hY, hYA, hpos⟩ := hs
      change d = segLen A' Y at hc
      rw [segLen_eq hA' hY] at hc
      rw [← gam_lam hY]
      congr 1
      -- `lam ℓ Y = lam ℓ A' + ε * d`
      have hsign : 0 < (lam ℓ Y - lam ℓ A') * ε := by
        have : 0 < (lam ℓ Y - lam ℓ A') * (lam ℓ C' - lam ℓ A') * (ε * (lam ℓ C' - lam ℓ A')) :=
          mul_pos hpos hεC
        have hsq : 0 < (lam ℓ C' - lam ℓ A') ^ 2 := by
          have := sub_ne_zero.2 hne; positivity
        nlinarith
      rw [hε] at hsign ⊢
      split_ifs at hsign ⊢ with h
      · rw [abs_sub_comm, abs_of_pos (by linarith)] at hc; linarith
      · rw [abs_of_pos (by linarith)] at hc; linarith
  ax_IV1_refl _ _ _ := rfl
  ax_IV2 A B A' B' A'' B'' _ _ _ h1 h2 := by
    simp only [segCong_iff] at *; rw [← h1, ← h2]
  ax_IV3 A B C A' B' C' h h' h1 h2 := by
    simp only [segCong_iff] at *
    rw [segLen_add (btw_of_meetOnlyAt h), segLen_add (btw_of_meetOnlyAt h'), h1, h2]

/-! ### Archimedes's axiom -/

/-- **Axiom V** holds in the Moulton plane. -/
instance instArchimedes : Archimedes Pt Ln where
  ax_V A B h0 hstep heq := by
    set ℓ := through (A 0) (A 1)
    have h01 : A 0 ≠ A 1 := h0.ne12
    have hmem : ∀ n, A n ∈ ℓ ∧ A (n + 1) ∈ ℓ := by
      intro n
      induction n with
      | zero => exact ⟨left_mem_through _ _, right_mem_through _ _⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        obtain ⟨ℓ', h1, h2, h3, -⟩ := hstep k
        have := eq_of_mem (hstep k).ne12 h1 h2 ih.1 ih.2
        subst this; exact h3
    set t : ℕ → ℝ := fun n => lam ℓ (A n) with ht
    set δ := t 1 - t 0 with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.2 (lam_ne (hmem 1).1 (hmem 0).1 (Ne.symm h01))
    have hstepδ : ∀ n, t (n + 1) - t n = δ := by
      intro n
      induction n with
      | zero => rfl
      | succ k ih =>
        have hb := (btw_iff (hmem k).1 (hmem k).2 (hmem (k + 1)).2).1 (hstep k)
        have he : segLen (A (k + 1)) (A (k + 1 + 1)) = segLen (A k) (A (k + 1)) := heq _ _
        rw [segLen_eq (hmem (k + 1)).1 (hmem (k + 1)).2, segLen_eq (hmem k).1 (hmem k).2] at he
        change |t (k + 1) - t (k + 1 + 1)| = |t k - t (k + 1)| at he
        change SB (t k) (t (k + 1)) (t (k + 1 + 1)) at hb
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at he; linarith
        · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at he; linarith
    have htn : ∀ n : ℕ, t n = t 0 + n * δ := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => push_cast; linarith [hstepδ k]
    obtain ⟨ℓ', h1, h2, hB, -⟩ := id h0
    have hℓ := eq_of_mem h01 h1 h2 (hmem 0).1 (hmem 0).2
    rw [hℓ] at hB
    have hb := (btw_iff (hmem 0).1 (hmem 0).2 hB).1 h0
    change SB (t 0) (t 1) (lam ℓ B) at hb
    obtain ⟨n, hn⟩ := exists_nat_gt (|lam ℓ B - t 0| / |δ|)
    have hδpos : 0 < |δ| := abs_pos.2 hδ0
    have hn' : |lam ℓ B - t 0| < n * |δ| := by rwa [div_lt_iff₀ hδpos] at hn
    refine ⟨n, (btw_iff (hmem 0).1 hB (hmem n).1).2 ?_⟩
    change SB (t 0) (lam ℓ B) (t n)
    rw [htn n]
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : 0 < δ := by rw [hδ]; linarith
      rw [abs_of_pos this, abs_of_pos (by linarith)] at hn'
      left; constructor <;> linarith
    · have : δ < 0 := by rw [hδ]; linarith
      rw [abs_of_neg this, abs_of_neg (by linarith)] at hn'
      right; constructor <;> nlinarith

end Moulton

end HilbertFoundations
