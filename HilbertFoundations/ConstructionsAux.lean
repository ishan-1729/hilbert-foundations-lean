import HilbertFoundations.Congruence
import HilbertFoundations.Analytic

/-!
# Helper module for `Constructions.lean`: constructions and the coordinate plane

This module contains no unit of Hilbert's text. It provides

* the generic notions of Chapter VII, for any system of points and lines with betweenness and
  congruence: perpendicular lines `Perp`, the constructions by Hilbert's problems 1–4 (and 5),
  `Constr`, and the constructions by straight-edge and transferer of segments,
  `RulerTransferer`, `RulerTransfererLine`;
* in the coordinate plane `Coord K 2` over an ordered field `K`: the algebra of the cross product
  `crossProd2` (and the quarter turn `rot90`), lines through two points (`mem_through_iff_cross`,
  `mem_line_iff_cross`, `collinear_iff_cross`, `through_ne_of_cross`), the common point of two
  lines (`inter_eq`) and right angles (`isRightAngle_iff`: a right angle is a zero inner
  product). The constructions themselves are in `ConstructionsAux2.lean`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

/-! ## Generic notions -/

/-- `a` and `b` are **perpendicular**: they meet in a point `O` and form a right angle there. -/
def Perp (P : Type u) {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P] (a b : L) :
    Prop :=
  ∃ O A B : P, O ∈ a ∧ A ∈ a ∧ O ∈ b ∧ B ∈ b ∧ IsRightAngle (L := L) A O B

/-- **The elements constructible by Hilbert's problems 1–4** (and, if `p5` holds, problem 5) from
a set `S` of given points. An element is a point (`Sum.inl`) or a straight line (`Sum.inr`).

* problem 1: the line through two constructed points (`join`), the common point of two distinct
  constructed lines (`meet`);
* problem 2: the parallel to a constructed line through a constructed point outside it
  (`parallel`);
* problem 3: the points of a constructed line at the distance of a constructed segment from a
  constructed point of the line, on either side (`layOff`);
* problem 4: a line through a constructed point `O'` forming with the half-ray from `O'` through a
  constructed point `A'` an angle congruent to an angle with constructed vertex and points
  (`angle`);
* problem 5: the perpendicular to a constructed line through a constructed point (`perp`). -/
inductive Constr {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] (p5 : Prop) (S : Set P) : P ⊕ L → Prop
  | given {A : P} : A ∈ S → Constr p5 S (.inl A)
  | join {A B : P} {a : L} : Constr p5 S (.inl A) → Constr p5 S (.inl B) → A ≠ B → A ∈ a →
      B ∈ a → Constr p5 S (.inr a)
  | meet {a b : L} {X : P} : Constr p5 S (.inr a) → Constr p5 S (.inr b) → a ≠ b → X ∈ a →
      X ∈ b → Constr p5 S (.inl X)
  | parallel {A : P} {a b : L} : Constr p5 S (.inl A) → Constr p5 S (.inr a) → A ∉ a → A ∈ b →
      Parallel (Point := P) a b → Constr p5 S (.inr b)
  | layOff {A B O X : P} {a : L} : Constr p5 S (.inl A) → Constr p5 S (.inl B) →
      Constr p5 S (.inl O) → Constr p5 S (.inr a) → A ≠ B → O ∈ a → X ∈ a → X ≠ O →
      SegCong O X A B → Constr p5 S (.inl X)
  | angle {A O B A' O' B' : P} {b : L} : Constr p5 S (.inl A) → Constr p5 S (.inl O) →
      Constr p5 S (.inl B) → Constr p5 S (.inl A') → Constr p5 S (.inl O') →
      ¬Collinear (Line := L) A O B → ¬Collinear (Line := L) A' O' B' → AngCong A O B A' O' B' →
      O' ∈ b → B' ∈ b → Constr p5 S (.inr b)
  | perp {A : P} {a b : L} : p5 → Constr p5 S (.inl A) → Constr p5 S (.inr a) → A ∈ b →
      Perp P a b → Constr p5 S (.inr b)

/-- **The points constructible by straight-edge and transferer of segments** from a set `S` of
given points: the common point of two distinct lines each drawn through two constructed points
(straight-edge), and the points of a line drawn through two constructed points at the distance of
a constructed segment from a constructed point of it, on either side (transferer). -/
inductive RulerTransferer {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    (S : Set P) : P → Prop
  | given {A : P} : A ∈ S → RulerTransferer S A
  | meet {A B C D X : P} {a b : L} : RulerTransferer S A → RulerTransferer S B →
      RulerTransferer S C → RulerTransferer S D → A ≠ B → C ≠ D → A ∈ a → B ∈ a → C ∈ b →
      D ∈ b → a ≠ b → X ∈ a → X ∈ b → RulerTransferer S X
  | layOff {A B O Q X : P} {a : L} : RulerTransferer S A → RulerTransferer S B →
      RulerTransferer S O → RulerTransferer S Q → A ≠ B → O ≠ Q → O ∈ a → Q ∈ a → X ∈ a →
      X ≠ O → SegCong O X A B → RulerTransferer S X

/-- The lines that can be drawn with the straight-edge: lines through two distinct constructed
points. -/
def RulerTransfererLine {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    (S : Set P) (a : L) : Prop :=
  ∃ A B : P, RulerTransferer S A ∧ RulerTransferer S B ∧ A ≠ B ∧ A ∈ a ∧ B ∈ a

/-! ## The coordinate plane -/

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Rotation by a right angle: `(x, y) ↦ (-y, x)`. -/
def rot90 (u : Coord K 2) : Coord K 2 := pt2 (-yc u) (xc u)

@[simp] theorem xc_rot90 (u : Coord K 2) : xc (rot90 u) = -yc u := rfl
@[simp] theorem yc_rot90 (u : Coord K 2) : yc (rot90 u) = xc u := rfl

theorem crossProd2_def (u v : Coord K 2) : crossProd2 u v = xc u * yc v - yc u * xc v := rfl

theorem cross_smul_left (c : K) (u v : Coord K 2) :
    crossProd2 (c • u) v = c * crossProd2 u v := by
  simp only [crossProd2_def, xc_smul, yc_smul]; ring

theorem cross_smul_right (c : K) (u v : Coord K 2) :
    crossProd2 u (c • v) = c * crossProd2 u v := by
  simp only [crossProd2_def, xc_smul, yc_smul]; ring

theorem cross_self (u : Coord K 2) : crossProd2 u u = 0 := by
  simp only [crossProd2_def]; ring

@[simp] theorem cross_zero_left (u : Coord K 2) : crossProd2 0 u = 0 := by
  simp [crossProd2_def]

@[simp] theorem cross_zero_right (u : Coord K 2) : crossProd2 u 0 = 0 := by
  simp [crossProd2_def]

theorem cross_comm (u v : Coord K 2) : crossProd2 u v = -crossProd2 v u := by
  simp only [crossProd2_def]; ring

theorem cross_add_left (u v w : Coord K 2) :
    crossProd2 (u + v) w = crossProd2 u w + crossProd2 v w := by
  simp only [crossProd2_def, xc_add, yc_add]; ring

theorem cross_sub_left (u v w : Coord K 2) :
    crossProd2 (u - v) w = crossProd2 u w - crossProd2 v w := by
  simp only [crossProd2_def, xc_sub, yc_sub]; ring

theorem cross_add_right (u v w : Coord K 2) :
    crossProd2 u (v + w) = crossProd2 u v + crossProd2 u w := by
  simp only [crossProd2_def, xc_add, yc_add]; ring

theorem cross_sub_right (u v w : Coord K 2) :
    crossProd2 u (v - w) = crossProd2 u v - crossProd2 u w := by
  simp only [crossProd2_def, xc_sub, yc_sub]; ring

/-- Lagrange's identity in the plane: `⟪u,v⟫² + (u × v)² = |u|² |v|²`. -/
theorem ip_sq_add_cross_sq (u v : Coord K 2) :
    ip u v ^ 2 + crossProd2 u v ^ 2 = ip u u * ip v v := by
  simp only [ip_two, crossProd2_def]; ring

theorem ne_zero_of_ne {A B : Coord K 2} (h : A ≠ B) : B - A ≠ 0 := sub_ne_zero.2 h.symm

theorem ip_self_pos' {u : Coord K 2} (h : u ≠ 0) : 0 < ip u u := ip_self_pos h

/-- A vector whose cross product with a nonzero vector `u` vanishes is a multiple of `u`. -/
theorem eq_smul_of_cross_eq_zero {u v : Coord K 2} (hu : u ≠ 0) (h : crossProd2 u v = 0) :
    v = (ip u v / ip u u) • u := by
  have hN := (ip_self_pos hu).ne'
  rw [crossProd2_def] at h
  have k1 : xc v * ip u u = ip u v * xc u := by
    rw [ip_two, ip_two]; linear_combination (-yc u) * h
  have k2 : yc v * ip u u = ip u v * yc u := by
    rw [ip_two, ip_two]; linear_combination (xc u) * h
  apply ext2
  · rw [xc_smul, div_mul_eq_mul_div, eq_div_iff hN]; exact k1
  · rw [yc_smul, div_mul_eq_mul_div, eq_div_iff hN]; exact k2

theorem cross_eq_zero_iff {u v : Coord K 2} (hu : u ≠ 0) :
    crossProd2 u v = 0 ↔ ∃ r : K, v = r • u := by
  constructor
  · intro h; exact ⟨_, eq_smul_of_cross_eq_zero hu h⟩
  · rintro ⟨r, rfl⟩; rw [cross_smul_right, cross_self, mul_zero]

/-- Two vectors orthogonal to the same nonzero vector are parallel. -/
theorem cross_eq_zero_of_ip {u x y : Coord K 2} (hu : u ≠ 0) (hx : ip x u = 0) (hy : ip y u = 0) :
    crossProd2 x y = 0 := by
  have hN := ip_self_pos hu
  rw [ip_two] at hN hx hy
  rw [crossProd2_def]
  have : (xc x * yc y - yc x * xc y) * (xc u * xc u + yc u * yc u) = 0 := by
    linear_combination (xc u * yc y - yc u * xc y) * hx - (xc u * yc x - yc u * xc x) * hy
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h hN.ne'

/-- A nonzero vector orthogonal to a nonzero vector `u` has a nonzero cross product with it. -/
theorem cross_ne_zero_of_ip {u w : Coord K 2} (hu : u ≠ 0) (hw : w ≠ 0) (h : ip u w = 0) :
    crossProd2 u w ≠ 0 := by
  intro hc
  have := ip_sq_add_cross_sq u w
  rw [h, hc] at this
  have h1 := ip_self_pos hu
  have h2 := ip_self_pos hw
  nlinarith

theorem mem_through {A B X : Coord K 2} (h : A ≠ B) :
    X ∈ AffLine.through A B h ↔ ∃ r : K, X = r • (B - A) + A := AffLine.mem_through_iff h

theorem mem_through_iff_cross {A B X : Coord K 2} (h : A ≠ B) :
    X ∈ AffLine.through A B h ↔ crossProd2 (B - A) (X - A) = 0 := by
  rw [mem_through, cross_eq_zero_iff (ne_zero_of_ne h)]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨r, by abel⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr]; abel⟩

/-- Membership in a line through two of its points. -/
theorem mem_line_iff_cross {a : CoordLine K 2} {A B X : Coord K 2} (h : A ≠ B) (hA : A ∈ a)
    (hB : B ∈ a) : X ∈ a ↔ crossProd2 (B - A) (X - A) = 0 := by
  rw [a.eq_through h hA hB]; exact mem_through_iff_cross h

theorem collinear_iff_cross {A B C : Coord K 2} (h : A ≠ B) :
    Collinear A B C ↔ crossProd2 (B - A) (C - A) = 0 := by
  constructor
  · rintro ⟨a, hA, hB, hC⟩; exact (mem_line_iff_cross h hA hB).1 hC
  · intro hc
    exact ⟨AffLine.through A B h, AffLine.left_mem_through h, AffLine.right_mem_through h,
      (mem_through_iff_cross h).2 hc⟩

theorem collinear_self_left (A C : Coord K 2) : Collinear A A C := by
  by_cases h : A = C
  · subst h
    have hne : A ≠ A + pt2 1 0 := by
      intro e; have := congrArg xc e; simp at this
    exact ⟨AffLine.through A _ hne, AffLine.left_mem_through _, AffLine.left_mem_through _,
      AffLine.left_mem_through _⟩
  · exact ⟨AffLine.through A C h, AffLine.left_mem_through _, AffLine.left_mem_through _,
      AffLine.right_mem_through _⟩

theorem cross_ne_zero_of_not_collinear {A B C : Coord K 2} (h : ¬Collinear A B C) :
    crossProd2 (B - A) (C - A) ≠ 0 := by
  have hAB : A ≠ B := by rintro rfl; exact h (collinear_self_left A C)
  intro hc; exact h ((collinear_iff_cross hAB).2 hc)

theorem not_collinear_of_cross {A B C : Coord K 2} (hc : crossProd2 (B - A) (C - A) ≠ 0) :
    ¬Collinear A B C := by
  have hAB : A ≠ B := by rintro rfl; simp at hc
  intro h; exact hc ((collinear_iff_cross hAB).1 h)

theorem not_collinear_iff_cross {A B C : Coord K 2} :
    ¬Collinear A B C ↔ crossProd2 (B - A) (C - A) ≠ 0 :=
  ⟨cross_ne_zero_of_not_collinear, not_collinear_of_cross⟩

/-- Two lines through `A, B` and `C, D` whose directions have a nonzero cross product are
distinct. -/
theorem through_ne_of_cross {A B C D : Coord K 2} (hAB : A ≠ B) (hCD : C ≠ D)
    (hc : crossProd2 (B - A) (D - C) ≠ 0) :
    AffLine.through A B hAB ≠ AffLine.through C D hCD := by
  intro e
  have hC : C ∈ AffLine.through A B hAB := e ▸ AffLine.left_mem_through hCD
  have hD : D ∈ AffLine.through A B hAB := e ▸ AffLine.right_mem_through hCD
  rw [mem_through_iff_cross] at hC hD
  apply hc
  rw [show D - C = (D - A) - (C - A) by abel, cross_sub_right, hC, hD, sub_zero]

/-- **The common point of two lines** `P₁P₂` and `P₃P₄` with independent directions. -/
theorem inter_eq {P₁ P₂ P₃ P₄ : Coord K 2} (hc : crossProd2 (P₂ - P₁) (P₄ - P₃) ≠ 0) :
    (crossProd2 (P₃ - P₁) (P₄ - P₃) / crossProd2 (P₂ - P₁) (P₄ - P₃)) • (P₂ - P₁) + P₁ =
      (crossProd2 (P₃ - P₁) (P₂ - P₁) / crossProd2 (P₂ - P₁) (P₄ - P₃)) • (P₄ - P₃) + P₃ := by
  set c := crossProd2 (P₂ - P₁) (P₄ - P₃) with hcdef
  apply ext2
  · simp only [xc_add, xc_smul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add' _ _ _ hc, div_add' _ _ _ hc,
      div_left_inj₀ hc]
    simp only [hcdef, crossProd2_def, xc_sub, yc_sub]; ring
  · simp only [yc_add, yc_smul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add' _ _ _ hc, div_add' _ _ _ hc,
      div_left_inj₀ hc]
    simp only [hcdef, crossProd2_def, xc_sub, yc_sub]; ring

/-! ### Right angles in the coordinate plane -/

theorem isRightAngle_iff {A O B : Coord K 2} :
    IsRightAngle (L := CoordLine K 2) A O B ↔ A ≠ O ∧ B ≠ O ∧ ip (A - O) (B - O) = 0 := by
  constructor
  · rintro ⟨hn, C, hb, hc⟩
    have hc' := cross_ne_zero_of_not_collinear (show ¬Collinear O A B from fun h =>
      hn h.swap12)
    have hAO : A ≠ O := by rintro rfl; simp at hc'
    have hBO : B ≠ O := by rintro rfl; simp at hc'
    refine ⟨hAO, hBO, ?_⟩
    rw [AffPt.between_iff, AffPt.sbtw_iff_param] at hb
    obtain ⟨-, t, ht0, ht1, hO⟩ := hb
    have hCO : C - O = (-((1 - t) / t)) • (A - O) := by
      subst hO; apply ext2 <;> simp <;> field_simp <;> ring
    rw [angCong_iff, AngleEq, hCO, ip_smul_right, ip_comm (B - O) (A - O)] at hc
    obtain ⟨hs, -⟩ := hc
    have hpos : 0 < (1 - t) / t := div_pos (by linarith) ht0
    rcases lt_trichotomy (ip (A - O) (B - O)) 0 with h | h | h
    · have : 0 < -((1 - t) / t) * ip (A - O) (B - O) := by nlinarith
      rw [sign_neg h, sign_pos this] at hs; exact absurd hs (by decide)
    · exact h
    · have : -((1 - t) / t) * ip (A - O) (B - O) < 0 := by nlinarith
      rw [sign_pos h, sign_neg this] at hs; exact absurd hs (by decide)
  · rintro ⟨hAO, hBO, h⟩
    have hc := cross_ne_zero_of_ip (ne_zero_of_ne hAO.symm) (ne_zero_of_ne hBO.symm) h
    refine ⟨fun hcol => ?_, (2 : K) • O - A, ?_, ?_⟩
    · exact (not_collinear_of_cross hc) hcol.swap12
    · rw [AffPt.between_iff, AffPt.sbtw_iff_param]
      refine ⟨fun e => hAO ?_, 2⁻¹, by norm_num, by norm_num, ?_⟩
      · have h1 := congrArg xc e
        have h2 := congrArg yc e
        simp at h1 h2
        apply ext2 <;> linarith
      · apply ext2 <;> simp <;> ring
    · rw [angCong_iff, AngleEq]
      have e1 : (2 : K) • O - A - O = -(A - O) := by apply ext2 <;> simp <;> ring
      rw [e1, ip_neg_right, ip_comm (B - O) (A - O), h]
      simp

end Coord

end HilbertFoundations
