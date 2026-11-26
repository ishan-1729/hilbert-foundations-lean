import HilbertFoundations.CommentaryCloseAux2

/-!
# The algebra of the elliptic metric in the gnomonic chart (helper for `CommentaryClose.lean`)

Dehn's non-legendrian geometry (unit `concl.non_legendrian`) is the part of an elliptic plane
infinitely near to a point, over a non-archimedean field. In the gnomonic (central) chart of the
sphere the points of that part are the pairs `(x, y)` of infinitesimal numbers, the great circles
are the straight lines, and the metric is given by the forms defined here: for points `P`, `Q` of
`K²`, lifted to `(P, 1)`, `(Q, 1)` in `K³`,

* `W P = 1 + ⟪P, P⟫`, `Sf P Q = 1 + ⟪P, Q⟫` are the inner products of the lifts;
* `Gf P u v = W P ⟪u, v⟫ - ⟪P, u⟫ ⟪P, v⟫` is the elliptic metric at `P` on tangent vectors;
* `cs P Q`, `sn P Q`, `tn P Q` are the cosine, the sine and the tangent of the elliptic distance;
* `kc P u v` is the cosine of the elliptic angle at `P` between the directions `u`, `v`.

Everything here is algebra over an ordered field `K` in which non-negative elements have square
roots (`IsEuclidean`, with the root function `rt`), together with the notion of an infinitesimal
element (`IsInf`).
-/

namespace HilbertFoundations

namespace Elliptic

open Coord

universe u

/-- A **euclidean** ordered field: every non-negative element is a square. -/
class IsEuclidean (K : Type u) [Field K] [LinearOrder K] : Prop where
  exists_sqrt : ∀ x : K, 0 ≤ x → ∃ y : K, 0 ≤ y ∧ y * y = x

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem eq_of_mul_self_eq {a b : K} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a = b * b) : a = b := by
  rcases mul_self_eq_mul_self_iff.1 h with e | e
  · exact e
  · have hb0 : b = 0 := le_antisymm (by linarith) hb
    rw [e, hb0, neg_zero]

/-- `p² = q²` and `p q ≥ 0` give `p = q`. -/
theorem eq_of_sq_eq_of_mul_nonneg {p q : K} (h : p ^ 2 = q ^ 2) (hpq : 0 ≤ p * q) : p = q := by
  have h' : (p - q) * (p + q) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · linarith
  · have hq : q = -p := by linarith
    rw [hq] at hpq
    have hp : p = 0 := by nlinarith [sq_nonneg p]
    rw [hq, hp, neg_zero]

/-! ### Square roots -/

section Sqrt

variable [IsEuclidean K]

/-- The non-negative square root of a non-negative element (`0` for negative elements). -/
noncomputable def rt (x : K) : K :=
  if h : 0 ≤ x then (IsEuclidean.exists_sqrt x h).choose else 0

omit [IsStrictOrderedRing K] in
theorem rt_nonneg (x : K) : 0 ≤ rt x := by
  unfold rt
  split_ifs with h
  · exact (IsEuclidean.exists_sqrt x h).choose_spec.1
  · exact le_rfl

omit [IsStrictOrderedRing K] in
theorem rt_mul_self {x : K} (h : 0 ≤ x) : rt x * rt x = x := by
  unfold rt
  split_ifs
  exact (IsEuclidean.exists_sqrt x h).choose_spec.2

theorem rt_eq {x y : K} (hy : 0 ≤ y) (h : y * y = x) : rt x = y :=
  eq_of_mul_self_eq (rt_nonneg x) hy (by
    rw [rt_mul_self (by rw [← h]; exact mul_self_nonneg y), h])

theorem rt_mul {x y : K} (hx : 0 ≤ x) (hy : 0 ≤ y) : rt (x * y) = rt x * rt y :=
  rt_eq (mul_nonneg (rt_nonneg x) (rt_nonneg y)) (by
    rw [mul_mul_mul_comm, rt_mul_self hx, rt_mul_self hy])

theorem rt_pos {x : K} (hx : 0 < x) : 0 < rt x :=
  lt_of_le_of_ne (rt_nonneg x) (fun e => by
    have h := rt_mul_self hx.le
    rw [← e, mul_zero] at h
    exact hx.ne h)

theorem rt_mul_self_eq {a : K} (ha : 0 ≤ a) : rt (a * a) = a := rt_eq ha rfl

end Sqrt

/-! ### Infinitesimal elements -/

/-- An **infinitesimal** element of an ordered field: smaller in absolute value than every
`1 / n`. -/
def IsInf (x : K) : Prop := ∀ n : ℕ, (n : K) * |x| ≤ 1

theorem isInf_zero : IsInf (0 : K) := fun n => by simp

omit [IsStrictOrderedRing K] in
theorem IsInf.neg {x : K} (hx : IsInf x) : IsInf (-x) := fun n => by rw [abs_neg]; exact hx n

theorem IsInf.mono {x y : K} (hy : IsInf y) (h : |x| ≤ |y|) : IsInf x := fun n =>
  (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)).trans (hy n)

theorem IsInf.add {x y : K} (hx : IsInf x) (hy : IsInf y) : IsInf (x + y) := fun n => by
  have h1 := hx (2 * n)
  have h2 := hy (2 * n)
  push_cast at h1 h2
  have h3 := abs_add_le x y
  have h4 : (n : K) * |x + y| ≤ n * (|x| + |y|) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
  linarith

theorem IsInf.sub {x y : K} (hx : IsInf x) (hy : IsInf y) : IsInf (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IsInf.abs_le_half {x : K} (hx : IsInf x) : |x| ≤ 1 / 2 := by
  have := hx 2
  push_cast at this
  linarith

theorem IsInf.abs_le_one {x : K} (hx : IsInf x) : |x| ≤ 1 := by
  have := hx.abs_le_half
  linarith

/-- An infinitesimal times a bounded element is infinitesimal. -/
theorem IsInf.mul_bdd {x y : K} (hx : IsInf x) (m : ℕ) (hy : |y| ≤ m) : IsInf (x * y) := fun n => by
  have h1 := hx (n * m)
  push_cast at h1
  rw [abs_mul]
  have h2 : (n : K) * (|x| * |y|) ≤ n * (|x| * m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (abs_nonneg x)) (Nat.cast_nonneg n)
  linarith

theorem IsInf.mul {x y : K} (hx : IsInf x) (hy : IsInf y) : IsInf (x * y) :=
  hx.mul_bdd 1 (by simpa using hy.abs_le_one)

theorem IsInf.natMul {x : K} (hx : IsInf x) (m : ℕ) : IsInf ((m : K) * x) := by
  rw [mul_comm]; exact hx.mul_bdd m (by simp)

/-- An element whose square is infinitesimal is infinitesimal. -/
theorem IsInf.of_mul_self {x : K} (hx : IsInf (x * x)) : IsInf x := fun n => by
  by_contra hcon
  push Not at hcon
  have h1 := hx (n * n)
  push_cast at h1
  rw [abs_mul] at h1
  have h2 : 1 < (n * |x|) * (n * |x|) := by nlinarith
  nlinarith

/-- Products of two elements of absolute value at most `1/2`. -/
theorem abs_mul_le_quarter {a b : K} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    -(1 / 4) ≤ a * b ∧ a * b ≤ 1 / 4 := by
  obtain ⟨a1, a2⟩ := abs_le.1 ha
  obtain ⟨b1, b2⟩ := abs_le.1 hb
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1),
      mul_nonneg (sub_nonneg.2 a2) (sub_nonneg.2 b2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b2),
      mul_nonneg (sub_nonneg.2 a2) (sub_nonneg.2 b1)]

/-! ### The forms -/

/-- `W P = 1 + ⟪P, P⟫`: the square of the length of the lift `(P, 1)`. -/
def W (P : Coord K 2) : K := 1 + ip P P

/-- `Sf P Q = 1 + ⟪P, Q⟫`: the inner product of the lifts. -/
def Sf (P Q : Coord K 2) : K := 1 + ip P Q

/-- The elliptic metric at `P` (up to the factor `W P ^ 2`). -/
def Gf (P u v : Coord K 2) : K := W P * ip u v - ip P u * ip P v

/-- The vector obtained from `u` by a quarter turn for the metric at `P` (up to a factor). -/
def jv (P u : Coord K 2) : Coord K 2 :=
  pt2 (-(W P * yc u - ip P u * yc P)) (W P * xc u - ip P u * xc P)

/-- Expands the forms into co-ordinates and calls `ring`. -/
macro "cring" : tactic =>
  `(tactic| (simp only [W, Sf, Gf, jv, crossProd2, ip_two, xc_sub, yc_sub, xc_add, yc_add,
      xc_smul, yc_smul, xc_pt2, yc_pt2, xc_zero, yc_zero]; ring))

theorem ip_self_nonneg (u : Coord K 2) : 0 ≤ ip u u := by
  rw [ip_two]; nlinarith [mul_self_nonneg (xc u), mul_self_nonneg (yc u)]

theorem ip_self_pos {u : Coord K 2} (hu : u ≠ 0) : 0 < ip u u := by
  rw [ip_two]
  by_contra hcon
  have h1 := mul_self_nonneg (xc u)
  have h2 := mul_self_nonneg (yc u)
  have hx : xc u * xc u = 0 := by linarith
  have hy : yc u * yc u = 0 := by linarith
  exact hu (ext2 (by simpa using mul_self_eq_zero.1 hx) (by simpa using mul_self_eq_zero.1 hy))

theorem W_pos (P : Coord K 2) : 0 < W P := by
  have := ip_self_nonneg P
  unfold W; linarith

theorem one_le_W (P : Coord K 2) : 1 ≤ W P := by
  have := ip_self_nonneg P
  unfold W; linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Sf_comm (P Q : Coord K 2) : Sf P Q = Sf Q P := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_comm (P u v : Coord K 2) : Gf P u v = Gf P v u := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_self (P u : Coord K 2) : Gf P u u = ip u u + crossProd2 P u ^ 2 := by cring

theorem Gf_self_nonneg (P u : Coord K 2) : 0 ≤ Gf P u u := by
  rw [Gf_self]; nlinarith [ip_self_nonneg u, sq_nonneg (crossProd2 P u)]

theorem Gf_self_pos (P : Coord K 2) {u : Coord K 2} (hu : u ≠ 0) : 0 < Gf P u u := by
  rw [Gf_self]; nlinarith [ip_self_pos hu, sq_nonneg (crossProd2 P u)]

theorem ip_le_Gf_self (P u : Coord K 2) : ip u u ≤ Gf P u u := by
  rw [Gf_self]; nlinarith [sq_nonneg (crossProd2 P u)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Lagrange's identity for the metric at `P`. -/
theorem lagrange (P u v : Coord K 2) :
    Gf P u v ^ 2 + W P * crossProd2 u v ^ 2 = Gf P u u * Gf P v v := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem W_mul_W (P Q : Coord K 2) : W P * W Q = Sf P Q ^ 2 + Gf P (Q - P) (Q - P) := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_swap (P Q : Coord K 2) : Gf P (Q - P) (Q - P) = Gf Q (P - Q) (P - Q) := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The cosine theorem, in the forms. -/
theorem Gf_cos (A B C : Coord K 2) : Gf A (B - A) (C - A) = W A * Sf B C - Sf A B * Sf A C := by
  cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_cr (P u v y : Coord K 2) :
    Gf P u v * crossProd2 u y - Gf P u y * crossProd2 u v = Gf P u u * crossProd2 v y := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gf_jv (P u v : Coord K 2) : Gf P v (jv P u) = W P * crossProd2 u v := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_jv (P u v : Coord K 2) : crossProd2 v (jv P u) = Gf P v u := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_smul_right (c : K) (u v : Coord K 2) : crossProd2 u (c • v) = c * crossProd2 u v := by
  cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_self (u : Coord K 2) : crossProd2 u u = 0 := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem cr_anticomm (u v : Coord K 2) : crossProd2 u v = -crossProd2 v u := by cring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The square of the determinant of the lifts is their Gram determinant. -/
theorem cr_sq_gram (A B C : Coord K 2) :
    crossProd2 (B - A) (C - A) ^ 2 = W A * W B * W C + 2 * Sf A B * Sf B C * Sf A C -
      W A * Sf B C ^ 2 - W B * Sf A C ^ 2 - W C * Sf A B ^ 2 := by cring

/-- A vector with zero cross product with `u ≠ 0` is a multiple of `u`. -/
theorem exists_smul_of_cr_eq_zero {u v : Coord K 2} (hu : u ≠ 0) (h : crossProd2 u v = 0) :
    v = (ip u v / ip u u) • u := by
  have hN := (ip_self_pos hu).ne'
  simp only [crossProd2] at h
  apply ext2
  · simp only [xc_smul]
    rw [div_mul_eq_mul_div, eq_div_iff hN]
    simp only [ip_two]
    linear_combination (-yc u) * h
  · simp only [yc_smul]
    rw [div_mul_eq_mul_div, eq_div_iff hN]
    simp only [ip_two]
    linear_combination (xc u) * h

/-! ### Distances and angles -/

section Metric

variable [IsEuclidean K]

/-- The length of the lift `(P, 1)`. -/
noncomputable def w (P : Coord K 2) : K := rt (W P)

theorem w_pos (P : Coord K 2) : 0 < w P := rt_pos (W_pos P)

theorem w_mul_self (P : Coord K 2) : w P * w P = W P := rt_mul_self (W_pos P).le

/-- The cosine of the elliptic distance of `P` and `Q`. -/
noncomputable def cs (P Q : Coord K 2) : K := Sf P Q / (w P * w Q)

/-- The sine of the elliptic distance of `P` and `Q`. -/
noncomputable def sn (P Q : Coord K 2) : K := rt (Gf P (Q - P) (Q - P)) / (w P * w Q)

/-- The tangent of the elliptic distance of `P` and `Q`. -/
noncomputable def tn (P Q : Coord K 2) : K := rt (Gf P (Q - P) (Q - P)) / Sf P Q

/-- The cosine of the elliptic angle at `P` between the directions `u` and `v`. -/
noncomputable def kc (P u v : Coord K 2) : K := Gf P u v / rt (Gf P u u * Gf P v v)

theorem cs_comm (P Q : Coord K 2) : cs P Q = cs Q P := by
  unfold cs; rw [Sf_comm, mul_comm]

theorem sn_comm (P Q : Coord K 2) : sn P Q = sn Q P := by
  unfold sn; rw [Gf_swap, mul_comm]

theorem sn_nonneg (P Q : Coord K 2) : 0 ≤ sn P Q :=
  div_nonneg (rt_nonneg _) (mul_pos (w_pos P) (w_pos Q)).le

theorem cs_sq_add_sn_sq (P Q : Coord K 2) : cs P Q ^ 2 + sn P Q ^ 2 = 1 := by
  have hw : (w P * w Q) ^ 2 = W P * W Q := by
    rw [mul_pow, sq, sq, w_mul_self, w_mul_self]
  have hG : rt (Gf P (Q - P) (Q - P)) ^ 2 = Gf P (Q - P) (Q - P) := by
    rw [sq, rt_mul_self (Gf_self_nonneg _ _)]
  rw [cs, sn, div_pow, div_pow, ← add_div, hG, hw, ← W_mul_W,
    div_self (mul_pos (W_pos P) (W_pos Q)).ne']

theorem sn_eq_of_cs_eq {P Q P' Q' : Coord K 2} (h : cs P Q = cs P' Q') : sn P Q = sn P' Q' := by
  have h1 := cs_sq_add_sn_sq P Q
  have h2 := cs_sq_add_sn_sq P' Q'
  rw [h] at h1
  exact eq_of_mul_self_eq (sn_nonneg _ _) (sn_nonneg _ _) (by linear_combination h1 - h2)

theorem sn_pos {P Q : Coord K 2} (h : Q ≠ P) : 0 < sn P Q :=
  div_pos (rt_pos (Gf_self_pos P (sub_ne_zero.2 h))) (mul_pos (w_pos P) (w_pos Q))

theorem tn_nonneg {P Q : Coord K 2} (hS : 0 < Sf P Q) : 0 ≤ tn P Q :=
  div_nonneg (rt_nonneg _) hS.le

theorem cs_eq_tn {P Q : Coord K 2} (hS : 0 < Sf P Q) : cs P Q = 1 / rt (1 + tn P Q ^ 2) := by
  have hG := rt_mul_self (Gf_self_nonneg P (Q - P))
  have key : (w P * w Q / Sf P Q) * (w P * w Q / Sf P Q) = 1 + tn P Q ^ 2 := by
    have e : w P * w Q * (w P * w Q) = Sf P Q ^ 2 + Gf P (Q - P) (Q - P) := by
      rw [mul_mul_mul_comm, w_mul_self, w_mul_self, W_mul_W]
    rw [div_mul_div_comm, e, tn, div_pow, sq (rt _), hG, ← sq, add_div,
      div_self (pow_ne_zero 2 hS.ne')]
  rw [← key, rt_mul_self_eq (div_nonneg (mul_pos (w_pos P) (w_pos Q)).le hS.le), one_div, inv_div,
    cs]

theorem cs_eq_iff_tn {P Q P' Q' : Coord K 2} (hS : 0 < Sf P Q) (hS' : 0 < Sf P' Q') :
    cs P Q = cs P' Q' ↔ tn P Q = tn P' Q' := by
  rw [cs_eq_tn hS, cs_eq_tn hS']
  constructor
  · intro h
    have h1 : rt (1 + tn P Q ^ 2) = rt (1 + tn P' Q' ^ 2) := by
      rw [one_div, one_div] at h; exact inv_injective h
    have h2 : 1 + tn P Q ^ 2 = 1 + tn P' Q' ^ 2 := by
      rw [← rt_mul_self (x := 1 + tn P Q ^ 2) (by positivity),
        ← rt_mul_self (x := 1 + tn P' Q' ^ 2) (by positivity), h1]
    exact eq_of_mul_self_eq (tn_nonneg hS) (tn_nonneg hS') (by linear_combination h2)
  · intro h; rw [h]

/-- **The cosine theorem** of the elliptic plane. -/
theorem kc_mul_sn {A B C : Coord K 2} (hB : B ≠ A) (hC : C ≠ A) :
    kc A (B - A) (C - A) * (sn A B * sn A C) = cs B C - cs A B * cs A C := by
  have hGb := Gf_self_pos A (sub_ne_zero.2 hB)
  have hGc := Gf_self_pos A (sub_ne_zero.2 hC)
  have hrb := (rt_pos hGb).ne'
  have hrc := (rt_pos hGc).ne'
  have hwA := (w_pos A).ne'
  have hwB := (w_pos B).ne'
  have hwC := (w_pos C).ne'
  rw [kc, rt_mul hGb.le hGc.le, sn, sn, cs, cs, cs, Gf_cos A B C, ← w_mul_self A]
  field_simp

theorem kc_comm (P u v : Coord K 2) : kc P u v = kc P v u := by
  unfold kc; rw [Gf_comm, mul_comm]

theorem kc_smul (P u v : Coord K 2) {c d : K} (hc : 0 < c) (hd : 0 < d) :
    kc P (c • u) (d • v) = kc P u v := by
  have e1 : Gf P (c • u) (d • v) = (c * d) * Gf P u v := by cring
  have e2 : Gf P (c • u) (c • u) * Gf P (d • v) (d • v) =
      ((c * d) * (c * d)) * (Gf P u u * Gf P v v) := by cring
  rw [kc, kc, e1, e2, rt_mul (mul_self_nonneg _)
    (mul_nonneg (Gf_self_nonneg _ _) (Gf_self_nonneg _ _)), rt_mul_self_eq (mul_pos hc hd).le,
    mul_div_mul_left _ _ (mul_pos hc hd).ne']

theorem kc_smul_right (P u v : Coord K 2) {d : K} (hd : 0 < d) : kc P u (d • v) = kc P u v := by
  have := kc_smul P u v one_pos hd
  rwa [one_smul] at this

/-- The cosine of an angle from its "cosine" and "sine" components. -/
theorem kc_of_comp {P u v : Coord K 2} {k p q : K} (hk : 0 < k) (hpq : 0 < p ^ 2 + q ^ 2)
    (h1 : Gf P u v = k * p) (h2 : W P * crossProd2 u v ^ 2 = k ^ 2 * q ^ 2) :
    kc P u v = p / rt (p ^ 2 + q ^ 2) := by
  rw [kc, ← lagrange, h1, h2, show (k * p) ^ 2 + k ^ 2 * q ^ 2 = (k * k) * (p ^ 2 + q ^ 2) by ring,
    rt_mul (mul_self_nonneg k) hpq.le, rt_mul_self_eq hk.le, mul_div_mul_left _ _ hk.ne']

omit [LinearOrder K] [IsStrictOrderedRing K] [IsEuclidean K] in
theorem cr_rot (P u : Coord K 2) (a q : K) :
    crossProd2 u (a • u + q • jv P u) = q * Gf P u u := by cring

/-- Turning the direction `u` at `P` by the angle of cosine `p / √(p² + q²)`. -/
theorem kc_rot {P u : Coord K 2} (hu : u ≠ 0) (p q : K) (hpq : 0 < p ^ 2 + q ^ 2) :
    kc P u ((w P * p) • u + q • jv P u) = p / rt (p ^ 2 + q ^ 2) := by
  refine kc_of_comp (k := w P * Gf P u u) (mul_pos (w_pos P) (Gf_self_pos P hu)) hpq ?_ ?_
  · cring
  · rw [cr_rot, ← w_mul_self P]; ring

/-- Two directions on the same side of `u` making the same angle with `u` are proportional. -/
theorem cr_eq_zero_of_kc_eq {P u v y : Coord K 2} (hu : u ≠ 0)
    (hs : 0 < crossProd2 u v * crossProd2 u y) (hk : kc P u v = kc P u y) :
    crossProd2 v y = 0 := by
  have hv : v ≠ 0 := by
    rintro rfl
    have : crossProd2 u (0 : Coord K 2) = 0 := by cring
    rw [this, zero_mul] at hs; exact lt_irrefl _ hs
  have hy : y ≠ 0 := by
    rintro rfl
    have : crossProd2 u (0 : Coord K 2) = 0 := by cring
    rw [this, mul_zero] at hs; exact lt_irrefl _ hs
  have hGu := Gf_self_pos P hu
  have hN1 := mul_pos hGu (Gf_self_pos P hv)
  have hN2 := mul_pos hGu (Gf_self_pos P hy)
  have hr1 := rt_pos hN1
  have hr2 := rt_pos hN2
  have E1 : Gf P u v ^ 2 + W P * crossProd2 u v ^ 2 =
      rt (Gf P u u * Gf P v v) * rt (Gf P u u * Gf P v v) :=
    (lagrange P u v).trans (rt_mul_self hN1.le).symm
  have E2 : Gf P u y ^ 2 + W P * crossProd2 u y ^ 2 =
      rt (Gf P u u * Gf P y y) * rt (Gf P u u * Gf P y y) :=
    (lagrange P u y).trans (rt_mul_self hN2.le).symm
  unfold kc at hk
  rw [div_eq_div_iff hr1.ne' hr2.ne'] at hk
  have hW := W_pos P
  -- the two cosines have the same sign
  have hcc : 0 ≤ Gf P u v * Gf P u y := by
    have h3 : Gf P u v * Gf P u y * rt (Gf P u u * Gf P y y) =
        Gf P u y ^ 2 * rt (Gf P u u * Gf P v v) := by linear_combination Gf P u y * hk
    have h3' : 0 ≤ Gf P u v * Gf P u y * rt (Gf P u u * Gf P y y) := by
      rw [h3]; exact mul_nonneg (sq_nonneg _) hr1.le
    exact nonneg_of_mul_nonneg_left h3' hr2
  have hsq : (Gf P u v * crossProd2 u y) ^ 2 = (Gf P u y * crossProd2 u v) ^ 2 := by
    have h4 : Gf P u v ^ 2 * (Gf P u y ^ 2 + W P * crossProd2 u y ^ 2) =
        Gf P u y ^ 2 * (Gf P u v ^ 2 + W P * crossProd2 u v ^ 2) := by
      rw [E1, E2]
      linear_combination (Gf P u v * rt (Gf P u u * Gf P y y) +
        Gf P u y * rt (Gf P u u * Gf P v v)) * hk
    have h5 : W P * ((Gf P u v * crossProd2 u y) ^ 2 - (Gf P u y * crossProd2 u v) ^ 2) = 0 := by
      linear_combination h4
    have := (mul_eq_zero.1 h5).resolve_left hW.ne'
    linarith
  have h6 : Gf P u v * crossProd2 u y = Gf P u y * crossProd2 u v :=
    eq_of_sq_eq_of_mul_nonneg hsq (by
      have : Gf P u v * crossProd2 u y * (Gf P u y * crossProd2 u v) =
          (Gf P u v * Gf P u y) * (crossProd2 u v * crossProd2 u y) := by ring
      rw [this]; exact mul_nonneg hcc hs.le)
  have h8 : Gf P u u * crossProd2 v y = 0 := by rw [← Gf_cr]; linear_combination h6
  exact (mul_eq_zero.1 h8).resolve_left hGu.ne'

end Metric

end Elliptic

end HilbertFoundations
