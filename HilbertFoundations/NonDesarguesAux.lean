import HilbertFoundations.Analytic

/-!
# The Moulton plane: incidence, order, parallels (helper module for `NonDesargues.lean`)

This module builds the plane geometry used in `NonDesargues.lean` for Theorem 33 (§ 23): the
*Moulton plane* (F. R. Moulton, "A simple non-desarguesian plane geometry", Trans. AMS 3 (1902),
the paper cited by the translator's note at the head of § 23), a variant of Hilbert's
construction in which the ellipse is replaced by the half-plane `x > 0`.

* Points are the points `(x, y)` of the ordinary plane (`Moulton.Pt`).
* The straight lines of the ordinary plane with slope `m ≥ 0` and the vertical lines are kept
  unchanged. A line `y = b + m x` with `m < 0` is replaced by the broken line which is
  `y = b + m x` for `x ≤ 0` and `y = b + 2 m x` for `x ≥ 0` (it is "refracted" when it crosses the
  `y`-axis). Uniformly: the line `graph m b` is `y = b + ht m x` with
  `ht m x = m x + min m 0 · max x 0`, and `vert c` is `x = c`.
* Each line is parametrized by the arc length of the broken line (`lam`, inverse `gam`), and
  "between" is betweenness of the parameters.

Here we prove the axioms of groups I (plane), II and III. The congruences (groups IV 1–5 and V)
are in `NonDesarguesAux2.lean`.
-/

namespace HilbertFoundations

namespace Moulton

/-! ### The slope transfer and the height of a broken line -/

/-- **Slope transfer** across the `y`-axis: a line of slope `m` for `x ≤ 0` has slope `tr m` for
`x ≥ 0`; `tr m = m` for `m ≥ 0` and `tr m = 2 m` for `m < 0`. -/
def tr (m : ℝ) : ℝ := m + min m 0

theorem tr_of_nonneg {m : ℝ} (h : 0 ≤ m) : tr m = m := by simp [tr, min_eq_right h]

theorem tr_of_neg {m : ℝ} (h : m < 0) : tr m = 2 * m := by
  simp [tr, min_eq_left h.le]; ring

theorem tr_strictMono : StrictMono tr := by
  intro a b h
  have : min a 0 ≤ min b 0 := min_le_min_right 0 h.le
  unfold tr; linarith

theorem tr_lt_tr {a b : ℝ} : tr a < tr b ↔ a < b := tr_strictMono.lt_iff_lt

theorem tr_inj {a b : ℝ} : tr a = tr b ↔ a = b := tr_strictMono.injective.eq_iff

/-- Inverse of the slope transfer. -/
noncomputable def trInv (k : ℝ) : ℝ := if 0 ≤ k then k else k / 2

theorem tr_trInv (k : ℝ) : tr (trInv k) = k := by
  unfold trInv
  split_ifs with h
  · exact tr_of_nonneg h
  · rw [tr_of_neg (by linarith)]; ring

/-- **Height** of the broken line of slope parameter `m` through `(0, 0)`: `m x` for `x ≤ 0`,
`tr m · x` for `x ≥ 0`. -/
def ht (m x : ℝ) : ℝ := m * x + min m 0 * max x 0

theorem ht_of_nonpos {m x : ℝ} (h : x ≤ 0) : ht m x = m * x := by
  simp [ht, max_eq_right h]

theorem ht_of_nonneg {m x : ℝ} (h : 0 ≤ x) : ht m x = tr m * x := by
  simp [ht, tr, max_eq_left h]; ring

theorem continuous_ht (m : ℝ) : Continuous (ht m) := by
  unfold ht; fun_prop

/-- The difference of two heights is monotone in `x` when the slopes are ordered. -/
theorem ht_sub_mono {m m' : ℝ} (h : m ≤ m') : Monotone fun x => ht m' x - ht m x := by
  intro x y hxy
  have h1 : min m 0 ≤ min m' 0 := min_le_min_right 0 h
  have h2 : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
  have h3 : 0 ≤ max x 0 := le_max_right _ _
  simp only [ht]
  nlinarith

theorem ht_sub_strictMono {m m' : ℝ} (h : m < m') : StrictMono fun x => ht m' x - ht m x := by
  intro x y hxy
  have h1 : min m 0 ≤ min m' 0 := min_le_min_right 0 h.le
  have h2 : max x 0 ≤ max y 0 := max_le_max_right 0 hxy.le
  have h3 : 0 ≤ max x 0 := le_max_right _ _
  simp only [ht]
  nlinarith

/-- Two broken lines of different slope parameters meet: the equation
`b + ht m x = b' + ht m' x` has a solution. -/
theorem exists_ht_eq {m m' : ℝ} (hm : m < m') (δ : ℝ) : ∃ x, ht m' x - ht m x = δ := by
  rcases le_or_gt δ 0 with hδ | hδ
  · refine ⟨δ / (m' - m), ?_⟩
    have hpos : 0 < m' - m := by linarith
    have hx : δ / (m' - m) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hδ hpos.le
    rw [ht_of_nonpos hx, ht_of_nonpos hx]
    field_simp
  · have hpos : 0 < tr m' - tr m := by have := tr_strictMono hm; linarith
    refine ⟨δ / (tr m' - tr m), ?_⟩
    have hx : 0 ≤ δ / (tr m' - tr m) := div_nonneg hδ.le hpos.le
    rw [ht_of_nonneg hx, ht_of_nonneg hx]
    field_simp

/-! ### Points and lines -/

/-- A **point** of the Moulton plane: a point `(x, y)` of the ordinary plane. -/
@[ext] structure Pt where
  /-- abscissa -/
  x : ℝ
  /-- ordinate -/
  y : ℝ

/-- A **straight line** of the Moulton plane: a vertical line `x = c`, or the broken line
`y = b + ht m x` (an ordinary line if `m ≥ 0`, refracted at the `y`-axis if `m < 0`). -/
inductive Ln
  /-- the vertical line `x = c` -/
  | vert (c : ℝ)
  /-- the broken line `y = b + ht m x` -/
  | graph (m b : ℝ)

/-- Incidence. -/
def OnL : Pt → Ln → Prop
  | P, .vert c => P.x = c
  | P, .graph m b => P.y = b + ht m P.x

instance instHasLines : HasLines Pt Ln := ⟨OnL⟩

@[simp] theorem mem_vert {P : Pt} {c : ℝ} : P ∈ Ln.vert c ↔ P.x = c := Iff.rfl

@[simp] theorem mem_graph {P : Pt} {m b : ℝ} : P ∈ Ln.graph m b ↔ P.y = b + ht m P.x := Iff.rfl

/-! ### Group I -/

/-- The slope parameter of the line through two points with different abscissae. -/
noncomputable def slopeThrough (A B : Pt) : ℝ :=
  if 0 ≤ (B.y - A.y) / (B.x - A.x) then (B.y - A.y) / (B.x - A.x)
  else (B.y - A.y) / ((B.x - A.x) + (max B.x 0 - max A.x 0))

/-- **The line through two points** (an explicit choice; unique by `eq_of_mem`). -/
noncomputable def through (A B : Pt) : Ln :=
  if A.x = B.x then .vert A.x else .graph (slopeThrough A B) (A.y - ht (slopeThrough A B) A.x)

theorem ht_sub_eq (m x₁ x₂ : ℝ) :
    ht m x₂ - ht m x₁ = m * (x₂ - x₁) + min m 0 * (max x₂ 0 - max x₁ 0) := by
  simp only [ht]; ring

theorem left_mem_through (A B : Pt) : A ∈ through A B := by
  unfold through; split_ifs <;> simp

theorem right_mem_through (A B : Pt) : B ∈ through A B := by
  unfold through
  split_ifs with h
  · simp [h]
  · simp only [mem_graph]
    have hd : B.x - A.x ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    suffices ht (slopeThrough A B) B.x - ht (slopeThrough A B) A.x = B.y - A.y by linarith
    rw [ht_sub_eq]
    unfold slopeThrough
    split_ifs with hs
    · rw [min_eq_right hs]; field_simp; ring
    · push Not at hs
      have hde : 0 ≤ (B.x - A.x) * (max B.x 0 - max A.x 0) := by
        rcases le_or_gt A.x B.x with h1 | h1
        · have : max A.x 0 ≤ max B.x 0 := max_le_max_right 0 h1
          exact mul_nonneg (by linarith) (by linarith)
        · have : max B.x 0 ≤ max A.x 0 := max_le_max_right 0 h1.le
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      generalize B.x - A.x = d at *
      generalize max B.x 0 - max A.x 0 = e at *
      generalize B.y - A.y = Δ at *
      have hdd : 0 < d * d := mul_self_pos.2 hd
      have hΔd : Δ * d < 0 := by
        rcases div_neg_iff.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith
      have hde' : 0 < d * (d + e) := by nlinarith
      have hne : d + e ≠ 0 := by intro h0; rw [h0] at hde'; simp at hde'
      have hneg : Δ / (d + e) < 0 := by
        rw [div_neg_iff]
        rcases lt_or_gt_of_ne hd with h1 | h1
        · left; constructor <;> nlinarith
        · right; constructor <;> nlinarith
      rw [min_eq_left hneg.le]
      field_simp

theorem eq_of_mem {A B : Pt} {ℓ₁ ℓ₂ : Ln} (h : A ≠ B) (hA : A ∈ ℓ₁) (hB : B ∈ ℓ₁)
    (hA' : A ∈ ℓ₂) (hB' : B ∈ ℓ₂) : ℓ₁ = ℓ₂ := by
  have hxy : A.x = B.x → A.y = B.y → False := fun h1 h2 => h (Pt.ext h1 h2)
  cases ℓ₁ with
  | vert c =>
    cases ℓ₂ with
    | vert c' => simp at hA hA'; rw [← hA, ← hA']
    | graph m b =>
      simp at hA hB hA' hB'
      exact (hxy (by rw [hA, hB]) (by rw [hA', hB', hA, hB])).elim
  | graph m b =>
    cases ℓ₂ with
    | vert c' =>
      simp at hA hB hA' hB'
      exact (hxy (by rw [hA', hB']) (by rw [hA, hB, hA', hB'])).elim
    | graph m' b' =>
      simp only [mem_graph] at hA hB hA' hB'
      have hx : A.x ≠ B.x := fun hx => hxy hx (by rw [hA, hB, hx])
      have hm : m = m' := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := (ht_sub_strictMono hlt).injective
            (show ht m' A.x - ht m A.x = ht m' B.x - ht m B.x by linarith)
          exact hx this
        · have := (ht_sub_strictMono hlt).injective
            (show ht m A.x - ht m' A.x = ht m B.x - ht m' B.x by linarith)
          exact hx this
      subst hm
      have : b = b' := by linarith
      rw [this]

theorem eq_through {A B : Pt} (h : A ≠ B) {a : Ln} (hA : A ∈ a) (hB : B ∈ a) : through A B = a :=
  eq_of_mem h (left_mem_through A B) (right_mem_through A B) hA hB

theorem through_comm {A B : Pt} (h : A ≠ B) : through B A = through A B :=
  eq_through h.symm (right_mem_through A B) (left_mem_through A B)

/-! ### The arc-length parametrization of the lines -/

/-- Arc length along a broken line, as a function of the abscissa: speeds `p` (for `x ≤ 0`) and
`q` (for `x ≥ 0`). -/
def ulen (p q x : ℝ) : ℝ := p * min x 0 + q * max x 0

/-- Its inverse. -/
noncomputable def uinv (p q t : ℝ) : ℝ := min t 0 / p + max t 0 / q

section Ulen

variable {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
include hp hq

theorem ulen_uinv (t : ℝ) : ulen p q (uinv p q t) = t := by
  rcases le_total t 0 with h | h
  · have h1 : uinv p q t = t / p := by simp [uinv, min_eq_left h, max_eq_right h]
    have h2 : t / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hp.le
    rw [h1, ulen, min_eq_left h2, max_eq_right h2]; field_simp; ring
  · have h1 : uinv p q t = t / q := by simp [uinv, min_eq_right h, max_eq_left h]
    have h2 : 0 ≤ t / q := div_nonneg h hq.le
    rw [h1, ulen, min_eq_right h2, max_eq_left h2]; field_simp; ring

theorem ulen_strictMono : StrictMono (ulen p q) := by
  intro x y hxy
  have h1 : min x 0 ≤ min y 0 := min_le_min_right 0 hxy.le
  have h2 : max x 0 ≤ max y 0 := max_le_max_right 0 hxy.le
  have h3 : min x 0 + max x 0 = x := by have := min_add_max x 0; linarith
  have h4 : min y 0 + max y 0 = y := by have := min_add_max y 0; linarith
  simp only [ulen]
  rcases lt_or_eq_of_le h1 with h5 | h5
  · nlinarith
  · have : max x 0 < max y 0 := by linarith
    nlinarith

theorem uinv_ulen (x : ℝ) : uinv p q (ulen p q x) = x :=
  (ulen_strictMono hp hq).injective (ulen_uinv hp hq _)

theorem uinv_strictMono : StrictMono (uinv p q) := by
  intro s t hst
  by_contra hle; push Not at hle
  have := (ulen_strictMono hp hq).monotone hle
  rw [ulen_uinv hp hq, ulen_uinv hp hq] at this
  linarith

end Ulen

theorem continuous_uinv (p q : ℝ) : Continuous (uinv p q) := by
  unfold uinv; fun_prop

/-- Speed of the left part (`x ≤ 0`) of the broken line of slope parameter `m`. -/
noncomputable def sL (m : ℝ) : ℝ := √(1 + m ^ 2)

/-- Speed of the right part (`x ≥ 0`). -/
noncomputable def sR (m : ℝ) : ℝ := √(1 + tr m ^ 2)

theorem sL_pos (m : ℝ) : 0 < sL m := Real.sqrt_pos.2 (by positivity)

theorem sR_pos (m : ℝ) : 0 < sR m := Real.sqrt_pos.2 (by positivity)

/-- **The arc-length parameter** of a point on a line: the ordinate on a vertical line; on a
broken line, the (signed) length of the broken line from the point of abscissa `0`. -/
noncomputable def lam : Ln → Pt → ℝ
  | .vert _, P => P.y
  | .graph m _, P => ulen (sL m) (sR m) P.x

/-- **The point of parameter `t`** on a line. -/
noncomputable def gam : Ln → ℝ → Pt
  | .vert c, t => ⟨c, t⟩
  | .graph m b, t => ⟨uinv (sL m) (sR m) t, b + ht m (uinv (sL m) (sR m) t)⟩

theorem gam_mem (ℓ : Ln) (t : ℝ) : gam ℓ t ∈ ℓ := by
  cases ℓ <;> simp [gam]

theorem lam_gam (ℓ : Ln) (t : ℝ) : lam ℓ (gam ℓ t) = t := by
  cases ℓ with
  | vert c => rfl
  | graph m b => exact ulen_uinv (sL_pos m) (sR_pos m) t

theorem gam_lam {ℓ : Ln} {P : Pt} (h : P ∈ ℓ) : gam ℓ (lam ℓ P) = P := by
  cases ℓ with
  | vert c => simp at h; ext <;> simp [gam, lam, h]
  | graph m b =>
    simp at h
    have := uinv_ulen (sL_pos m) (sR_pos m) P.x
    ext <;> simp [gam, lam, this, h]

theorem lam_inj {ℓ : Ln} {P Q : Pt} (hP : P ∈ ℓ) (hQ : Q ∈ ℓ) (h : lam ℓ P = lam ℓ Q) : P = Q := by
  rw [← gam_lam hP, ← gam_lam hQ, h]

theorem lam_ne {ℓ : Ln} {P Q : Pt} (hP : P ∈ ℓ) (hQ : Q ∈ ℓ) (h : P ≠ Q) : lam ℓ P ≠ lam ℓ Q :=
  fun e => h (lam_inj hP hQ e)

/-- On a broken line the parameter is increasing in the abscissa. -/
theorem lam_graph_lt {m b : ℝ} {P Q : Pt} :
    lam (.graph m b) P < lam (.graph m b) Q ↔ P.x < Q.x :=
  (ulen_strictMono (sL_pos m) (sR_pos m)).lt_iff_lt

theorem gam_graph_x (m b t : ℝ) : (gam (.graph m b) t).x = uinv (sL m) (sR m) t := rfl

/-! ### Betweenness -/

/-- `b` lies strictly between `a` and `c` (reals). -/
def SB (a b c : ℝ) : Prop := (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- **Between** in the Moulton plane: the three points lie on a line and the parameter of `B` lies
strictly between those of `A` and `C`. -/
def Btw (A B C : Pt) : Prop :=
  ∃ ℓ : Ln, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ ∧ SB (lam ℓ A) (lam ℓ B) (lam ℓ C)

instance instHasBetween : HasBetween Pt := ⟨Btw⟩

theorem between_iff_btw {A B C : Pt} : Between A B C ↔ Btw A B C := Iff.rfl

theorem SB.ne13 {a b c : ℝ} (h : SB a b c) : a ≠ c := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro e <;> subst e <;> linarith

theorem SB.symm {a b c : ℝ} (h : SB a b c) : SB c b a := by unfold SB at *; exact Or.symm h

theorem btw_iff {ℓ : Ln} {A B C : Pt} (hA : A ∈ ℓ) (hB : B ∈ ℓ) (hC : C ∈ ℓ) :
    Btw A B C ↔ SB (lam ℓ A) (lam ℓ B) (lam ℓ C) := by
  constructor
  · rintro ⟨ℓ', hA', hB', hC', h⟩
    have hAC : A ≠ C := fun e => h.ne13 (by rw [e])
    have := eq_of_mem hAC hA' hC' hA hC
    subst this; exact h
  · intro h; exact ⟨ℓ, hA, hB, hC, h⟩

theorem btw_gam (ℓ : Ln) {s t r : ℝ} : Btw (gam ℓ s) (gam ℓ t) (gam ℓ r) ↔ SB s t r := by
  rw [btw_iff (gam_mem ℓ s) (gam_mem ℓ t) (gam_mem ℓ r)]; simp [lam_gam]

theorem Btw.ne12 {A B C : Pt} (h : Btw A B C) : A ≠ B := by
  obtain ⟨ℓ, hA, hB, hC, h⟩ := h
  intro e; subst e; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem Btw.ne23 {A B C : Pt} (h : Btw A B C) : B ≠ C := by
  obtain ⟨ℓ, hA, hB, hC, h⟩ := h
  intro e; subst e; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

theorem Btw.ne13 {A B C : Pt} (h : Btw A B C) : A ≠ C := by
  obtain ⟨ℓ, hA, hB, hC, h⟩ := h
  intro e; subst e; exact h.ne13 rfl

theorem Btw.symm {A B C : Pt} (h : Btw A B C) : Btw C B A := by
  obtain ⟨ℓ, hA, hB, hC, h⟩ := h
  exact ⟨ℓ, hC, hB, hA, h.symm⟩

/-- The linear axioms of order hold in the Moulton plane. -/
instance instLineOrder : LineOrder Pt Ln where
  ax_I1 A B _ := ⟨through A B, left_mem_through A B, right_mem_through A B⟩
  ax_I2 A B a b h hA hB hA' hB' := eq_of_mem h hA hB hA' hB'
  ax_I7_line a := ⟨gam a 0, gam a 1, fun e => by
      have := congrArg (lam a) e; rw [lam_gam, lam_gam] at this; norm_num at this,
    gam_mem a 0, gam_mem a 1⟩
  between_onLine A B C h := by
    refine ⟨h.ne12, h.ne13, h.ne23, ?_⟩
    obtain ⟨ℓ, hA, hB, hC, -⟩ := h
    exact ⟨ℓ, hA, hB, hC⟩
  ax_II1 _ _ _ _ h := Btw.symm h
  ax_II2 A C a hA hC hAC := by
    have hne := lam_ne hA hC hAC
    refine ⟨⟨gam a ((lam a A + lam a C) / 2), ?_⟩, ⟨gam a (2 * lam a C - lam a A), ?_⟩⟩
    · rw [between_iff_btw, btw_iff hA (gam_mem a _) hC, lam_gam]
      rcases lt_or_gt_of_ne hne with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    · rw [between_iff_btw, btw_iff hA hC (gam_mem a _), lam_gam]
      rcases lt_or_gt_of_ne hne with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
  ax_II3 A B C hcol hAB hAC hBC := by
    obtain ⟨ℓ, hA, hB, hC⟩ := hcol
    simp only [between_iff_btw, btw_iff hA hB hC, btw_iff hB hA hC, btw_iff hA hC hB, SB]
    exact order_three (lam_ne hA hB hAB) (lam_ne hA hC hAC) (lam_ne hB hC hBC)
  ax_II4 A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD := by
    have hmem : ∀ i, ![A, B, C, D] i ∈ a := by
      intro i; fin_cases i <;> assumption
    have hinj : Function.Injective fun i => lam a (![A, B, C, D] i) := by
      intro i j hij
      have := lam_inj (hmem i) (hmem j) hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    obtain ⟨σ, h01, h12, h23⟩ := exists_perm_strictMono_four _ hinj
    refine ⟨σ, ?_, ?_, ?_, ?_⟩ <;> simp only [between_iff_btw] <;>
      rw [btw_iff (hmem _) (hmem _) (hmem _)] <;> exact Or.inl ⟨by order, by order⟩

theorem collinear_iff {A B C : Pt} : Collinear A B C ↔ ∃ ℓ : Ln, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := Iff.rfl

/-! ### Sides of a line; Pasch's axiom -/

/-- **The side function** of a line: zero exactly on the line; its sign tells the side. For a
broken line, `y - b - ht m x` (above or below); for `x = c`, `c - x`. -/
def sd : Ln → Pt → ℝ
  | .vert c, P => c - P.x
  | .graph m b, P => P.y - b - ht m P.x

theorem sd_eq_zero_iff {ℓ : Ln} {P : Pt} : sd ℓ P = 0 ↔ P ∈ ℓ := by
  cases ℓ with
  | vert c => simp [sd]; constructor <;> intro h <;> linarith
  | graph m b => simp [sd]; constructor <;> intro h <;> linarith

theorem sd_ne_zero {ℓ : Ln} {P : Pt} (h : P ∉ ℓ) : sd ℓ P ≠ 0 := fun e => h (sd_eq_zero_iff.1 e)

theorem continuous_sd_gam (ℓ n : Ln) : Continuous fun t => sd ℓ (gam n t) := by
  cases ℓ with
  | vert c =>
    cases n with
    | vert c' => simp only [sd, gam]; fun_prop
    | graph m b => simp only [sd, gam]; exact continuous_const.sub (continuous_uinv _ _)
  | graph m b =>
    cases n with
    | vert c' => simp only [sd, gam]; fun_prop
    | graph m' b' =>
      simp only [sd, gam]
      have h1 := continuous_uinv (sL m') (sR m')
      have h2 := (continuous_ht m').comp h1
      have h3 := (continuous_ht m).comp h1
      exact ((continuous_const.add h2).sub continuous_const).sub h3

/-- Along a line, the side function of another line is monotone or antitone. -/
theorem sd_gam_mono (ℓ n : Ln) :
    Monotone (fun t => sd ℓ (gam n t)) ∨ Antitone (fun t => sd ℓ (gam n t)) := by
  cases ℓ with
  | vert c =>
    cases n with
    | vert c' => left; intro s t _; simp [sd, gam]
    | graph m b =>
      right; intro s t hst
      have := (uinv_strictMono (sL_pos m) (sR_pos m)).monotone hst
      simp only [sd, gam]; linarith
  | graph m b =>
    cases n with
    | vert c' => left; intro s t hst; simp only [sd, gam]; linarith
    | graph m' b' =>
      have hu := (uinv_strictMono (sL_pos m') (sR_pos m')).monotone
      rcases le_total m m' with h | h
      · left; intro s t hst
        have := ht_sub_mono h (hu hst)
        simp only [sd, gam] at this ⊢; linarith
      · right; intro s t hst
        have := ht_sub_mono h (hu hst)
        simp only [sd, gam] at this ⊢; linarith

theorem sd_gam_lam {ℓ n : Ln} {P : Pt} (hP : P ∈ n) : sd ℓ (gam n (lam n P)) = sd ℓ P := by
  rw [gam_lam hP]

/-- A line crossing the segment `AB` separates `A` and `B`. -/
theorem sd_mul_neg_of_btw {ℓ : Ln} {A B X : Pt} (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hX : X ∈ ℓ)
    (h : Btw A X B) : sd ℓ A * sd ℓ B < 0 := by
  obtain ⟨n, hAn, hXn, hBn, hs⟩ := h
  have eA : sd ℓ (gam n (lam n A)) = sd ℓ A := sd_gam_lam hAn
  have eB : sd ℓ (gam n (lam n B)) = sd ℓ B := sd_gam_lam hBn
  have eX : sd ℓ (gam n (lam n X)) = 0 := by rw [sd_gam_lam hXn]; exact sd_eq_zero_iff.2 hX
  have hA0 := sd_ne_zero hA
  have hB0 := sd_ne_zero hB
  rcases sd_gam_mono ℓ n with hm | hm <;> rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : sd ℓ (gam n (lam n A)) ≤ sd ℓ (gam n (lam n X)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n X)) ≤ sd ℓ (gam n (lam n B)) := hm h2.le
    rw [eA, eX] at a1; rw [eX, eB] at a2
    have : sd ℓ A < 0 := lt_of_le_of_ne a1 hA0
    have : 0 < sd ℓ B := lt_of_le_of_ne a2 (Ne.symm hB0)
    nlinarith
  · have a1 : sd ℓ (gam n (lam n B)) ≤ sd ℓ (gam n (lam n X)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n X)) ≤ sd ℓ (gam n (lam n A)) := hm h2.le
    rw [eB, eX] at a1; rw [eX, eA] at a2
    have : sd ℓ B < 0 := lt_of_le_of_ne a1 hB0
    have : 0 < sd ℓ A := lt_of_le_of_ne a2 (Ne.symm hA0)
    nlinarith
  · have a1 : sd ℓ (gam n (lam n X)) ≤ sd ℓ (gam n (lam n A)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n B)) ≤ sd ℓ (gam n (lam n X)) := hm h2.le
    rw [eA, eX] at a1; rw [eX, eB] at a2
    have : 0 < sd ℓ A := lt_of_le_of_ne a1 (Ne.symm hA0)
    have : sd ℓ B < 0 := lt_of_le_of_ne a2 hB0
    nlinarith
  · have a1 : sd ℓ (gam n (lam n X)) ≤ sd ℓ (gam n (lam n B)) := hm h1.le
    have a2 : sd ℓ (gam n (lam n A)) ≤ sd ℓ (gam n (lam n X)) := hm h2.le
    rw [eB, eX] at a1; rw [eX, eA] at a2
    have : 0 < sd ℓ B := lt_of_le_of_ne a1 (Ne.symm hB0)
    have : sd ℓ A < 0 := lt_of_le_of_ne a2 hA0
    nlinarith

/-- Two points separated by a line are joined by a segment crossing it. -/
theorem exists_btw_of_sd_mul_neg {ℓ : Ln} {A B : Pt} (h : sd ℓ A * sd ℓ B < 0) :
    ∃ X, X ∈ ℓ ∧ Btw A X B := by
  have hAB : A ≠ B := by intro e; subst e; nlinarith [sq_nonneg (sd ℓ A)]
  set n := through A B
  have hAn := left_mem_through A B
  have hBn := right_mem_through A B
  set f := fun t => sd ℓ (gam n t) with hf
  have eA : f (lam n A) = sd ℓ A := sd_gam_lam hAn
  have eB : f (lam n B) = sd ℓ B := sd_gam_lam hBn
  have hc : Continuous f := continuous_sd_gam ℓ n
  have key : ∀ s t : ℝ, s < t → f s * f t < 0 → ∃ r, s < r ∧ r < t ∧ f r = 0 := by
    intro s t hst hneg
    rcases lt_or_gt_of_ne (show f s ≠ 0 by intro e; rw [e] at hneg; simp at hneg) with hs | hs
    · have ht : 0 < f t := by nlinarith
      obtain ⟨r, ⟨h1, h2⟩, hr⟩ := intermediate_value_Ioo hst.le hc.continuousOn ⟨hs, ht⟩
      exact ⟨r, h1, h2, hr⟩
    · have ht : f t < 0 := by nlinarith
      obtain ⟨r, ⟨h1, h2⟩, hr⟩ := intermediate_value_Ioo' hst.le hc.continuousOn ⟨ht, hs⟩
      exact ⟨r, h1, h2, hr⟩
  rcases lt_or_gt_of_ne (lam_ne hAn hBn hAB) with hlt | hlt
  · obtain ⟨r, h1, h2, hr⟩ := key _ _ hlt (by rw [eA, eB]; exact h)
    refine ⟨gam n r, sd_eq_zero_iff.1 hr, ?_⟩
    rw [btw_iff hAn (gam_mem n r) hBn, lam_gam]; exact Or.inl ⟨h1, h2⟩
  · obtain ⟨r, h1, h2, hr⟩ := key _ _ hlt (by rw [eA, eB, mul_comm]; exact h)
    refine ⟨gam n r, sd_eq_zero_iff.1 hr, ?_⟩
    rw [btw_iff hAn (gam_mem n r) hBn, lam_gam]; exact Or.inr ⟨h1, h2⟩

/-- **Sides of a line**: `A`, `B` lie on the same side of `ℓ` iff their side functions have the
same sign. -/
theorem sameSide_iff {ℓ : Ln} {A B : Pt} : SameSide ℓ A B ↔ 0 < sd ℓ A * sd ℓ B := by
  constructor
  · rintro ⟨hA, hB, hno⟩
    rcases lt_trichotomy (sd ℓ A * sd ℓ B) 0 with h | h | h
    · exact (hno (exists_btw_of_sd_mul_neg h)).elim
    · rcases mul_eq_zero.1 h with h | h
      · exact (sd_ne_zero hA h).elim
      · exact (sd_ne_zero hB h).elim
    · exact h
  · intro h
    have hA : A ∉ ℓ := fun hA => by rw [sd_eq_zero_iff.2 hA] at h; simp at h
    have hB : B ∉ ℓ := fun hB => by rw [sd_eq_zero_iff.2 hB] at h; simp at h
    refine ⟨hA, hB, ?_⟩
    rintro ⟨X, hX, hb⟩
    have := sd_mul_neg_of_btw hA hB hX hb
    linarith

/-- **Groups I and II of plane geometry** hold in the Moulton plane. -/
instance instPlaneOrder : PlaneOrder Pt Ln where
  ax_I7_noncollinear := by
    refine ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
    rintro ⟨ℓ, h1, h2, h3⟩
    cases ℓ with
    | vert c => simp at h1 h2; linarith
    | graph m b => simp [ht] at h1 h3; linarith
  ax_II5 A B C ℓ _ hA hB hC hX := by
    obtain ⟨X, hX, hb⟩ := hX
    have hAB := sd_mul_neg_of_btw hA hB hX hb
    have hC0 := sd_ne_zero hC
    rcases lt_or_gt_of_ne (show sd ℓ B * sd ℓ C ≠ 0 from mul_ne_zero (sd_ne_zero hB) hC0) with
      h | h
    · exact Or.inl (exists_btw_of_sd_mul_neg h)
    · right
      apply exists_btw_of_sd_mul_neg
      have : sd ℓ A * sd ℓ C * (sd ℓ B * sd ℓ B) < 0 := by
        have := mul_neg_of_neg_of_pos hAB h
        linarith [show sd ℓ A * sd ℓ B * (sd ℓ B * sd ℓ C) = sd ℓ A * sd ℓ C * (sd ℓ B * sd ℓ B)
          by ring]
      have hb2 : 0 < sd ℓ B * sd ℓ B := mul_self_pos.2 (sd_ne_zero hB)
      by_contra hc; push Not at hc
      nlinarith

/-! ### Parallels -/

theorem meets_vert_graph (c m b : ℝ) : Meets (Point := Pt) (Ln.vert c) (Ln.graph m b) :=
  ⟨⟨c, b + ht m c⟩, by simp, by simp⟩

theorem meets_graph_of_ne {m m' b b' : ℝ} (h : m ≠ m') :
    Meets (Point := Pt) (Ln.graph m b) (Ln.graph m' b') := by
  rcases lt_or_gt_of_ne h with h | h
  · obtain ⟨x, hx⟩ := exists_ht_eq h (b - b')
    exact ⟨⟨x, b + ht m x⟩, by simp, by simp; linarith⟩
  · obtain ⟨x, hx⟩ := exists_ht_eq h (b' - b)
    exact ⟨⟨x, b + ht m x⟩, by simp, by simp; linarith⟩

theorem meets_comm {a b : Ln} : Meets (Point := Pt) a b ↔ Meets (Point := Pt) b a := by
  constructor <;> rintro ⟨P, h1, h2⟩ <;> exact ⟨P, h2, h1⟩

/-- The parallel to `a` through `A`. -/
def par (a : Ln) (A : Pt) : Ln :=
  match a with
  | .vert _ => .vert A.x
  | .graph m _ => .graph m (A.y - ht m A.x)

/-- **Group III** (with group I) holds in the Moulton plane. -/
instance instPlaneParallels : PlaneParallels Pt Ln where
  ax_III a A hA := by
    refine ⟨par a A, ⟨?_, ?_⟩, ?_⟩
    · cases a <;> simp [par]
    · rintro ⟨P, h1, h2⟩
      cases a with
      | vert c => simp [par] at h1 h2; exact hA (by simp; linarith)
      | graph m b => simp [par] at h1 h2; exact hA (by simp; linarith)
    · rintro b ⟨hAb, hno⟩
      cases a with
      | vert c =>
        cases b with
        | vert c' => simp at hAb; simp [par, hAb]
        | graph m' b' => exact (hno ((meets_comm).1 (meets_vert_graph c m' b'))).elim
      | graph m b0 =>
        cases b with
        | vert c' => exact (hno (meets_vert_graph c' m b0)).elim
        | graph m' b' =>
          by_cases hm : m' = m
          · subst hm; simp at hAb; simp [par]; linarith
          · exact (hno (meets_graph_of_ne hm)).elim

end Moulton

end HilbertFoundations
