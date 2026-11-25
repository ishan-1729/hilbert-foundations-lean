import HilbertFoundations.ConstructionsAux7

/-!
# Helper module for `Constructions.lean`: Fig. 52 and the examples of §§ 37, 39

This module contains no unit of Hilbert's text. It proves:

* `fig52`: Hilbert's construction of problem 4 (§ 36, Fig. 52, after § 14): with `D`, `C` the feet
  of the perpendiculars from `B` to the other side of `β` and to `l`, and `E` the foot of the
  perpendicular from `A` to `CD`, the angle `CAE` is congruent to `β` **iff `β` is acute** (for an
  obtuse `β` it is the supplementary angle);
* `right_triangle_example`: the right triangle with hypotenuse `1` and a leg `√2 - 1` exists in
  the real plane, but its third vertex is not constructible by straight-edge and transferer from
  the frame (§ 37);
* `apollonius_example`: a contact problem of Apollonius (the circles through two points tangent to
  a line) whose data are constructible but whose solutions are not (§ 39).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

open Coord

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The two-dimensional Gram identity behind Fig. 52: the chord `CD` of the circle with diameter
`AB` has `|CD|² |x|² |y|² = |AB|² (x × y)²`. -/
theorem gram_chord (b x y : Coord K 2) {δ γ : K} (hδ : δ * ip x x = ip b x)
    (hγ : γ * ip y y = ip b y) :
    ip x x * ip y y * ip (δ • x - γ • y) (δ • x - γ • y) = ip b b * crossProd2 x y ^ 2 := by
  have e : ip x x * ip y y * ip (δ • x - γ • y) (δ • x - γ • y) =
      (δ * ip x x) ^ 2 * ip y y - 2 * (δ * ip x x) * (γ * ip y y) * ip x y +
        (γ * ip y y) ^ 2 * ip x x := by
    simp only [ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_comm y x]; ring
  rw [e, hδ, hγ]; simp only [ip_two, crossProd2_def]; ring

/-- **Hilbert's construction of problem 4** (Fig. 52). `β = ∠BAX`, `l = AY`; `D`, `C` are the
feet of the perpendiculars from `B` to `AX` and to `AY`, `E` the foot of the perpendicular from
`A` to `CD`. When `β` is not a right angle, `B` is not on the perpendicular to `l` and `l ≠ AX`,
the points `C`, `D` are distinct, `E ≠ A`, and `∠CAE ≡ β` exactly when `β` is acute. -/
theorem fig52 {A B X Y C D E : Coord K 2} (hβ : ip (B - A) (X - A) ≠ 0)
    (hC0 : ip (B - A) (Y - A) ≠ 0) (hXY : crossProd2 (X - A) (Y - A) ≠ 0)
    (hD : D = (ip (B - A) (X - A) / ip (X - A) (X - A)) • (X - A) + A)
    (hC : C = (ip (B - A) (Y - A) / ip (Y - A) (Y - A)) • (Y - A) + A)
    (hE : E = (ip (A - C) (D - C) / ip (D - C) (D - C)) • (D - C) + C) :
    C ≠ D ∧ E ≠ A ∧ (AngCong C A E B A X ↔ 0 < ip (B - A) (X - A)) := by
  set b := B - A with hb
  set x := X - A with hx
  set y := Y - A with hy
  have hx0 : x ≠ 0 := by intro h; rw [h] at hXY; simp at hXY
  have hy0 : y ≠ 0 := by intro h; rw [h] at hXY; simp at hXY
  have hX := ip_self_pos hx0
  have hY := ip_self_pos hy0
  set δ := ip b x / ip x x with hδ
  set γ := ip b y / ip y y with hγ
  have hδ0 : δ ≠ 0 := div_ne_zero hβ hX.ne'
  have hγ0 : γ ≠ 0 := div_ne_zero hC0 hY.ne'
  have hd : D - A = δ • x := by rw [hD]; abel
  have hc : C - A = γ • y := by rw [hC]; abel
  set w := D - C with hw
  have hw' : w = δ • x - γ • y := by
    rw [hw, show D - C = (D - A) - (C - A) by abel, hd, hc]
  have hcw : crossProd2 (C - A) w = γ * δ * crossProd2 y x := by
    rw [hw', hc, cross_sub_right, cross_smul_left, cross_smul_left, cross_smul_right,
      cross_smul_right, cross_self]; ring
  have hCD : C ≠ D := by
    intro h
    have : w = 0 := by rw [hw, h, sub_self]
    have h2 : crossProd2 (C - A) w = 0 := by rw [this]; simp
    rw [hcw] at h2
    rw [cross_comm] at h2
    exact (mul_ne_zero (mul_ne_zero hγ0 hδ0) (neg_ne_zero.2 hXY)) h2
  have hw0 : w ≠ 0 := by rw [hw]; exact sub_ne_zero.2 (Ne.symm hCD)
  have hW := ip_self_pos hw0
  set μ := ip (A - C) w / ip w w with hμ
  set e := E - A with he
  have he' : e = (C - A) + μ • w := by rw [he, hE]; abel
  have hAC : A - C = -(C - A) := by abel
  have hew : ip e w = 0 := by
    rw [he', ip_add_left, ip_smul_left, hμ, hAC, ip_neg_left, div_mul_cancel₀ _ hW.ne']; ring
  have hce : ip (C - A) e = ip e e := by
    rw [show C - A = e - μ • w by rw [he']; abel, ip_sub_left, ip_smul_left, ip_comm w e, hew,
      mul_zero, sub_zero]
  have hee : ip e e * ip w w = crossProd2 (C - A) w ^ 2 := by
    have L := ip_sq_add_cross_sq (C - A) w
    have hμ' : μ * ip w w = -ip (C - A) w := by
      rw [hμ, hAC, ip_neg_left, div_mul_cancel₀ _ hW.ne']
    have h1 : ip e e = ip (C - A) (C - A) + μ * ip (C - A) w := by
      rw [← hce, he', ip_add_right, ip_smul_right]
    rw [h1]
    linear_combination (ip (C - A) w) * hμ' - L
  have he0 : e ≠ 0 := by
    intro h0
    have : crossProd2 (C - A) w = 0 := by
      have h1 := hee; rw [h0, ip_zero_left, zero_mul] at h1
      exact pow_eq_zero_iff two_ne_zero |>.1 h1.symm
    rw [hcw, cross_comm] at this
    exact (mul_ne_zero (mul_ne_zero hγ0 hδ0) (neg_ne_zero.2 hXY)) this
  have hE0 := ip_self_pos he0
  refine ⟨hCD, fun h => he0 (by rw [he, h, sub_self]), ?_⟩
  rw [angCong_iff, AngleEq]
  constructor
  · rintro ⟨hs, -⟩
    rw [hce, sign_pos hE0] at hs
    exact sign_eq_one_iff.1 hs.symm
  · intro hpos
    refine ⟨by rw [hce, sign_pos hE0, sign_pos hpos], ?_⟩
    have h5 := gram_chord b x y (δ := δ) (γ := γ) (by rw [hδ, div_mul_cancel₀ _ hX.ne'])
      (by rw [hγ, div_mul_cancel₀ _ hY.ne'])
    rw [← hw'] at h5
    have hP : ip b x = δ * ip x x := by rw [hδ, div_mul_cancel₀ _ hX.ne']
    have hCC : ip (C - A) (C - A) = γ ^ 2 * ip y y := by
      rw [hc, ip_smul_left, ip_smul_right]; ring
    have hcr : crossProd2 y x ^ 2 = crossProd2 x y ^ 2 := by rw [cross_comm, neg_sq]
    have key : (ip e e * ip b b * ip x x - ip b x ^ 2 * ip (C - A) (C - A)) * ip w w = 0 := by
      rw [hP, hCC]
      linear_combination (ip b b * ip x x) * hee + (ip b b * ip x x * (crossProd2 (C - A) w +
        γ * δ * crossProd2 y x)) * hcw - (δ ^ 2 * γ ^ 2 * ip x x) * h5 +
        (γ ^ 2 * δ ^ 2 * ip b b * ip x x) * hcr
    have key' : ip e e * ip b b * ip x x - ip b x ^ 2 * ip (C - A) (C - A) = 0 :=
      (mul_eq_zero.1 key).resolve_right hW.ne'
    rw [hce]
    linear_combination (ip e e) * key'

end Coord

/-! ## The right triangle of § 37 -/

/-- **Hilbert's example of § 37**: in the real plane there is a right triangle `ABC` with
hypotenuse `AB = 1` and leg `AC = √2 - 1` (it can be constructed with the compass), but no such
vertex `C` is constructible by straight-edge and transferer from the frame. -/
theorem right_triangle_example :
    (∃ C : Coord ℝ 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 ∧
        ip (C - pt2 0 0) (C - pt2 0 0) = (Real.sqrt 2 - 1) ^ 2) ∧
      ∀ C : Coord ℝ 2, ip (pt2 0 0 - C) (pt2 1 0 - C) = 0 →
        ip (C - pt2 0 0) (C - pt2 0 0) = (Real.sqrt 2 - 1) ^ 2 →
        ¬RulerTransferer (frameSet ℝ) C := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h21 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  constructor
  · set u := 3 - 2 * Real.sqrt 2 with hu
    have hu0 : 0 ≤ u - u ^ 2 := by
      have : u - u ^ 2 = (3 - 2 * Real.sqrt 2) * (2 * Real.sqrt 2 - 2) := by rw [hu]; ring
      rw [this]; apply mul_nonneg <;> nlinarith
    refine ⟨pt2 u (Real.sqrt (u - u ^ 2)), ?_, ?_⟩
    · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2]
      have := Real.sq_sqrt hu0
      nlinarith [this]
    · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2]
      have := Real.sq_sqrt hu0
      rw [hu] at this ⊢; nlinarith [this]
  · intro C hright hleg hC
    obtain ⟨hx, hy⟩ := rt_frame_iff_omega.1 hC
    -- `BC² = AB² - AC² = 2√2 - 2`
    have hBC : (1 - xc C) ^ 2 + (0 - yc C) ^ 2 = 2 * Real.sqrt 2 - 2 := by
      simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2] at hright hleg
      nlinarith [hright, hleg, h2]
    have hm := Omega.sqrt_sq_add_sq_mem (Omega.sub_mem Omega.one_mem hx)
      (Omega.sub_mem Omega.zero_mem hy)
    rw [hBC] at hm
    exact sqrt_two_sqrt_two_sub_two_not_mem hm

/-! ## A contact problem of Apollonius (§ 39) -/

/-- A circle with center `M` through `P` and `Q`, **tangent to the axis `y = 0` at `T`**: `T` lies
on the axis, the radius `MT` is perpendicular to it, and `MT = MP = MQ`. -/
def TangentCircle (P Q T M : Coord ℝ 2) : Prop :=
  yc T = 0 ∧ ip (M - T) (pt2 1 0) = 0 ∧ ip (M - T) (M - T) = ip (M - P) (M - P) ∧
    ip (M - T) (M - T) = ip (M - Q) (M - Q)

/-- **A contact problem of Apollonius that is not solvable by straight-edge and transferer**:
the points `P = (0, 1)` and `Q = (0, 2√2 - 2)` and the axis `y = 0` are constructible from the
frame; there are circles through `P` and `Q` tangent to the axis (constructible with the compass),
but neither the point of contact nor the center of any of them is constructible by straight-edge
and transferer: the point of contact is `(±√(2√2 - 2), 0)`. -/
theorem apollonius_example :
    RulerTransferer (frameSet ℝ) (pt2 0 1) ∧
      RulerTransferer (frameSet ℝ) (pt2 0 (2 * Real.sqrt 2 - 2)) ∧
      (∃ T M, TangentCircle (pt2 0 1) (pt2 0 (2 * Real.sqrt 2 - 2)) T M) ∧
      ∀ T M, TangentCircle (pt2 0 1) (pt2 0 (2 * Real.sqrt 2 - 2)) T M →
        ¬RulerTransferer (frameSet ℝ) T ∧ ¬RulerTransferer (frameSet ℝ) M := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h21 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have h22 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  set q := 2 * Real.sqrt 2 - 2 with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q ≠ 1 := by rw [hq]; intro h; nlinarith
  have hqΩ : q ∈ Omega := Omega.sub_mem (Omega.mul_mem (two_mem_subfield _) sqrt_two_mem)
    (two_mem_subfield _)
  refine ⟨rt_frame_iff_omega.2 ⟨by simp [Omega.zero_mem], by simp [Omega.one_mem]⟩,
    rt_frame_iff_omega.2 ⟨by simp [Omega.zero_mem], by simpa using hqΩ⟩, ?_, ?_⟩
  · refine ⟨pt2 (Real.sqrt q) 0, pt2 (Real.sqrt q) ((1 + q) / 2), ?_⟩
    have hs := Real.sq_sqrt hq0
    refine ⟨by simp, by simp [ip_two], ?_, ?_⟩
    · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2]; nlinarith [hs]
    · simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2]; nlinarith [hs]
  · rintro T M ⟨hT, hperp, h1, h2'⟩
    simp only [ip_two, xc_sub, yc_sub, xc_pt2, yc_pt2, hT] at hperp h1 h2'
    have hxM : xc M = xc T := by linarith
    -- `t² = q`
    have ht : xc T ^ 2 = q := by
      rw [hxM] at h1 h2'
      have hc : yc M * (2 - 2 * q) = 1 - q ^ 2 := by nlinarith
      have hc' : yc M = (1 + q) / 2 := by
        have h1q : (2 - 2 * q) ≠ 0 := by intro h; apply hq1; linarith
        field_simp; nlinarith
      rw [hc'] at h1; nlinarith
    have hnot : xc T ∉ Omega := by
      intro h
      have := Omega.abs_mem h
      rw [← Real.sqrt_sq_eq_abs, ht, hq] at this
      exact sqrt_two_sqrt_two_sub_two_not_mem this
    exact ⟨fun h => hnot (rt_frame_iff_omega.1 h).1,
      fun h => hnot (hxM ▸ (rt_frame_iff_omega.1 h).1)⟩

end HilbertFoundations
