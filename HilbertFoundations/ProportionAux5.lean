import HilbertFoundations.ProportionAux4

/-!
# Helper module for `Proportion.lean`: the bisectors of the angles of a triangle (§ 16)

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV and axes
`ax`. It proves the fact which Hilbert's proof of Theorem 22 presupposes: **the bisectors of the
three angles of a triangle meet in a point** (`incenter_exists`), the point lying inside the three
angles. The proof is a computation in co-ordinates over the field of segments:

* betweenness in co-ordinates (`between_coords`: a point between `X` and `W` is `X + t (W - X)` with
  `0 < t < 1`), whence a criterion for two points to lie on the same side of a line (the signs of
  the cross products agree, `sameSide_of_side`) and for a point to lie inside an angle
  (`mem_interior_of_side`);
* the bisector at a vertex `V` (`bisector_of_coords`): if `X₁`, `Y₁` lie on the sides `VX`, `VY` at
  equal distances from `V`, every point `S = V + k ((X₁ - V) + (Y₁ - V))` with `k > 0` lies inside
  the angle and satisfies `∠XVS ≡ ∠SVY` (the triangles `VX₁S`, `VY₁S` have their three sides
  congruent, by the distance formula `len_sq`; then Theorem 16);
* the incentre `S = (a A + b B + c C) / (a + b + c)` (`a`, `b`, `c` the lengths of the sides) is of
  this form at each of the three vertices (algebraic identities `vertexB_alg`, `vertexC_alg`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

namespace Pas

/-! ### Algebraic identities -/

theorem rhombus_alg {K : Type*} [Field K] {a1 a2 b1 b2 s1 s2 k : K}
    (hpq : a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2) (hs1 : s1 = k * (a1 + b1))
    (hs2 : s2 = k * (a2 + b2)) :
    (a1 - s1) * (a1 - s1) + (a2 - s2) * (a2 - s2) =
      (b1 - s1) * (b1 - s1) + (b2 - s2) * (b2 - s2) := by
  subst hs1 hs2
  linear_combination (1 - 2 * k) * hpq

theorem vertexB_alg {K : Type*} [Field K] {xA xB xC u1 w1 p1 q1 a b c : K} (hD : a + b + c ≠ 0)
    (hc : c ≠ 0) (h1 : xB - xA = c * u1) (h2 : xA - xB = c * p1) (h3 : xC - xB = a * q1)
    (h4 : xC - xA = b * w1) :
    xA + b * c / (a + b + c) * (u1 + w1) - xB = a * c / (a + b + c) * (p1 + q1) := by
  have hp : p1 = -u1 := mul_left_cancel₀ hc (by linear_combination -h2 - h1)
  subst hp
  field_simp
  linear_combination (-(a + b + c) + c) * h1 + c * h3 - c * h4

theorem vertexC_alg {K : Type*} [Field K] {xA xB xC u1 w1 r1 z1 a b c : K} (hD : a + b + c ≠ 0)
    (hb : b ≠ 0) (h1 : xB - xA = c * u1) (h2 : xA - xC = b * r1) (h3 : xB - xC = a * z1)
    (h4 : xC - xA = b * w1) :
    xA + b * c / (a + b + c) * (u1 + w1) - xC = a * b / (a + b + c) * (r1 + z1) := by
  have hr : r1 = -w1 := mul_left_cancel₀ hb (by linear_combination -h2 - h4)
  subst hr
  field_simp
  linear_combination -b * h1 + b * h3 + (-(a + b + c) + b) * h4

theorem vertex_alg {K : Type*} [Field K] {p1 p2 q1 q2 k s1 s2 : K}
    (hq : q1 * q1 + q2 * q2 = 1) (hs1 : s1 = k * (p1 + q1)) (hs2 : s2 = k * (p2 + q2)) :
    q1 * s1 + q2 * s2 = k * (1 + (p1 * q1 + p2 * q2)) ∧
      (s1 * s1 + s2 * s2) - (q1 * s1 + q2 * s2) * (q1 * s1 + q2 * s2) =
        (k * (p1 * q2 - p2 * q1)) * (k * (p1 * q2 - p2 * q1)) := by
  subst hs1 hs2
  constructor
  · linear_combination k * hq
  · linear_combination (-(k * k * ((p1 + q1) * (p1 + q1) + (p2 + q2) * (p2 + q2)))) * hq

theorem cos_lt_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p1 p2 q1 q2 : K}
    (hp : p1 * p1 + p2 * p2 = 1) (hq : q1 * q1 + q2 * q2 = 1) (hx : p1 * q2 - p2 * q1 ≠ 0) :
    -1 < p1 * q1 + p2 * q2 ∧ p1 * q1 + p2 * q2 < 1 := by
  have e : (p1 * q1 + p2 * q2) * (p1 * q1 + p2 * q2) + (p1 * q2 - p2 * q1) * (p1 * q2 - p2 * q1) =
      1 := by
    linear_combination (q1 * q1 + q2 * q2) * hp + hq
  have h2 : 0 < (p1 * q2 - p2 * q1) * (p1 * q2 - p2 * q1) := mul_self_pos.2 hx
  constructor <;> nlinarith

/-- The tangent length `k (1 + cos A) = (b + c - a) / 2`, by the law of cosines. -/
theorem tangent_alg {K : Type*} [Field K] {a b c cA D : K} (hDdef : a + b + c = D) (hD : D ≠ 0)
    (hcos : a * a = b * b + c * c - 2 * b * c * cA) :
    2 * (b * c / D * (1 + cA)) = b + c - a := by
  subst hDdef
  field_simp
  linear_combination hcos

section Incircle

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)
include ax

/-- The cross product `(Y - X) × (Z - X)` in co-ordinates. -/
noncomputable def side (X Y Z : P) : G ax :=
  (px ax Y - px ax X) * (py ax Z - py ax X) - (py ax Y - py ax X) * (px ax Z - px ax X)

theorem mem_line_iff_side {X Y : P} (hXY : X ≠ Y) {l : L} (hX : X ∈ l) (hY : Y ∈ l) (Z : P) :
    Z ∈ l ↔ side ax X Y Z = 0 := mem_line_coords ax hXY hX hY Z

theorem collinear_iff_side {X Y Z : P} (hXY : X ≠ Y) :
    Collinear (Line := L) X Y Z ↔ side ax X Y Z = 0 := by
  constructor
  · rintro ⟨a, hX, hY, hZ⟩
    exact (mem_line_iff_side ax hXY hX hY Z).1 hZ
  · intro h
    obtain ⟨l, hX, hY⟩ := exists_line (Line := L) hXY
    exact ⟨l, hX, hY, (mem_line_iff_side ax hXY hX hY Z).2 h⟩

/-- **Betweenness in co-ordinates**: a point between `X` and `W` is `X + t (W - X)`, `0 < t < 1`. -/
theorem between_coords {X T W : P} (h : Between X T W) :
    ∃ t : G ax, 0 < t ∧ t < 1 ∧ px ax T - px ax X = t * (px ax W - px ax X) ∧
      py ax T - py ax X = t * (py ax W - py ax X) := by
  have hWX : W ≠ X := (ne13_of_between (Line := L) h).symm
  have hXT : X ≠ T := ne12_of_between (Line := L) h
  have hTW : T ≠ W := ne23_of_between (Line := L) h
  obtain ⟨c, s, hcs⟩ := ray_coords ax hWX
  have hT : T ∈ ray X W := mem_ray_of_between (L := L) h
  have hW : W ∈ ray X W := mem_ray_self' (L := L) hWX
  obtain ⟨t1, t2⟩ := hcs T hT
  obtain ⟨w1, w2⟩ := hcs W hW
  rw [px_sub] at t1 w1
  rw [py_sub] at t2 w2
  have hadd := len_add ax h
  have hpT := len_pos ax hXT
  have hpTW := len_pos ax hTW
  have hXW : 0 < len ax X W := by rw [hadd]; exact add_pos hpT hpTW
  have hne : len ax X W ≠ 0 := ne_of_gt hXW
  refine ⟨len ax X T / len ax X W, div_pos hpT hXW, (div_lt_one hXW).2 (by rw [hadd]; linarith),
    ?_, ?_⟩
  · rw [t1, w1]; field_simp
  · rw [t2, w2]; field_simp

theorem side_between (X Y : P) {Z W T : P} (h : Between Z T W) :
    ∃ t : G ax, 0 < t ∧ t < 1 ∧ side ax X Y T = (1 - t) * side ax X Y Z + t * side ax X Y W := by
  obtain ⟨t, h0, h1, e1, e2⟩ := between_coords ax h
  refine ⟨t, h0, h1, ?_⟩
  unfold side
  have ex : px ax T = px ax Z + t * (px ax W - px ax Z) := by linear_combination e1
  have ey : py ax T = py ax Z + t * (py ax W - py ax Z) := by linear_combination e2
  rw [ex, ey]; ring

/-- **Two points lie on the same side of a line** if their cross products have the same sign. -/
theorem sameSide_of_side {X Y : P} (hXY : X ≠ Y) {l : L} (hX : X ∈ l) (hY : Y ∈ l) {Z W : P}
    (h : 0 < side ax X Y Z * side ax X Y W) : SameSide l Z W := by
  have hZ : side ax X Y Z ≠ 0 := fun e => by rw [e, zero_mul] at h; exact lt_irrefl _ h
  have hW : side ax X Y W ≠ 0 := fun e => by rw [e, mul_zero] at h; exact lt_irrefl _ h
  refine ⟨fun hh => hZ ((mem_line_iff_side ax hXY hX hY Z).1 hh),
    fun hh => hW ((mem_line_iff_side ax hXY hX hY W).1 hh), ?_⟩
  rintro ⟨T, hT, hb⟩
  obtain ⟨t, h0, h1, e⟩ := side_between ax X Y hb
  rw [(mem_line_iff_side ax hXY hX hY T).1 hT] at e
  have e2 : 0 = (1 - t) * (side ax X Y Z * side ax X Y Z) + t * (side ax X Y Z * side ax X Y W) := by
    linear_combination (side ax X Y Z) * e
  have p1 := mul_pos h0 h
  have p2 := mul_pos (sub_pos.2 h1) (mul_self_pos.2 hZ)
  linarith

/-- **A point inside an angle**, in co-ordinates. -/
theorem mem_interior_of_side {A O B S : P} (hn : ¬Collinear (Line := L) A O B)
    (h1 : 0 < side ax O A S * side ax O A B) (h2 : 0 < side ax O B S * side ax O B A) :
    S ∈ Interior A O B := by
  obtain ⟨hAO, hBO, -⟩ := nc_ne ax hn
  intro a b hOa hAa hOb hBb
  exact ⟨sameSide_of_side ax (Ne.symm hAO) hOa hAa h1, sameSide_of_side ax (Ne.symm hBO) hOb hBb h2⟩

/-- The cross product along a half-ray scales with the distance. -/
theorem side_ray {V X Z : P} (hX : X ≠ V) (hZ : Z ∈ ray V X) (W : P) :
    side ax V Z W * len ax V X = side ax V X W * len ax V Z := by
  obtain ⟨c, s, hcs⟩ := ray_coords ax hX
  obtain ⟨z1, z2⟩ := hcs Z hZ
  obtain ⟨x1, x2⟩ := hcs X (mem_ray_self' (L := L) hX)
  rw [px_sub] at z1 x1
  rw [py_sub] at z2 x2
  unfold side
  rw [z1, z2, x1, x2]; ring

/-- The point of a half-ray at the unit distance, and the direction of the half-ray. -/
theorem unit_point {V X : P} (hVX : V ≠ X) :
    ∃ U : P, U ∈ ray V X ∧ len ax V U = 1 ∧
      px ax X - px ax V = len ax V X * (px ax U - px ax V) ∧
      py ax X - py ax V = len ax V X * (py ax U - py ax V) := by
  obtain ⟨U, hU, sU⟩ := segCong_layoff (L := L) ax.hOE hVX
  have hVU : V ≠ U := Ne.symm (ne_of_mem_ray hU)
  have hl : len ax V U = 1 := by rw [← len_E ax]; exact ((len_eq_iff ax ax.hOE hVU).2 sU).symm
  obtain ⟨c, s, hcs⟩ := ray_coords ax (Ne.symm hVX)
  obtain ⟨u1, u2⟩ := hcs U hU
  obtain ⟨x1, x2⟩ := hcs X (mem_ray_self' (L := L) (Ne.symm hVX))
  rw [px_sub] at u1 x1
  rw [py_sub] at u2 x2
  rw [hl, one_mul] at u1 u2
  exact ⟨U, hU, hl, by rw [x1, u1], by rw [x2, u2]⟩

/-- **The bisector of an angle in co-ordinates**: with `X₁`, `Y₁` on the sides at equal distances
from the vertex `V`, every point `S = V + k ((X₁ - V) + (Y₁ - V))`, `k > 0`, lies inside the angle
`∠XVY` and makes congruent angles with its sides. -/
theorem bisector_of_coords {X V Y X1 Y1 S : P} (hn : ¬Collinear (Line := L) X V Y)
    (hX1 : X1 ∈ ray V X) (hY1 : Y1 ∈ ray V Y) (hl : len ax V X1 = len ax V Y1) {k : G ax}
    (hk : 0 < k)
    (hSx : px ax S - px ax V = k * ((px ax X1 - px ax V) + (px ax Y1 - px ax V)))
    (hSy : py ax S - py ax V = k * ((py ax X1 - py ax V) + (py ax Y1 - py ax V))) :
    AngCong X V S S V Y ∧ S ∈ Interior X V Y := by
  obtain ⟨hXV, hYV, -⟩ := nc_ne ax hn
  have hX1V : X1 ≠ V := ne_of_mem_ray hX1
  have hY1V : Y1 ≠ V := ne_of_mem_ray hY1
  have n1 : ¬Collinear (Line := L) X1 V Y1 := not_collinear_of_mem_rays (L := L) hn hX1 hY1
  -- the cross products
  have hσ : side ax V X1 Y1 ≠ 0 := fun e =>
    n1 ((collinear_iff_side ax (Ne.symm hX1V)).2 e).swap12
  have sX' : side ax V X1 S = k * side ax V X1 Y1 := by unfold side; rw [hSx, hSy]; ring
  have sY' : side ax V Y1 S = -(k * side ax V X1 Y1) := by unfold side; rw [hSx, hSy]; ring
  have nX1S : ¬Collinear (Line := L) X1 V S := fun hh =>
    (mul_ne_zero (ne_of_gt hk) hσ) (sX' ▸ (collinear_iff_side ax (Ne.symm hX1V)).1 hh.swap12)
  have nY1S : ¬Collinear (Line := L) Y1 V S := fun hh => (neg_ne_zero.2
    (mul_ne_zero (ne_of_gt hk) hσ)) (sY' ▸ (collinear_iff_side ax (Ne.symm hY1V)).1 hh.swap12)
  obtain ⟨-, hSV, hX1S⟩ := nc_ne ax nX1S
  obtain ⟨-, -, hY1S⟩ := nc_ne ax nY1S
  -- the triangles `VX₁S`, `VY₁S` have their sides congruent
  have hpq : (px ax X1 - px ax V) * (px ax X1 - px ax V) + (py ax X1 - py ax V) * (py ax X1 - py ax V)
      = (px ax Y1 - px ax V) * (px ax Y1 - px ax V) + (py ax Y1 - py ax V) * (py ax Y1 - py ax V) := by
    have e1 := len_sq ax V X1
    have e2 := len_sq ax V Y1
    rw [hl] at e1
    linear_combination e2 - e1
  have hd := rhombus_alg hpq hSx hSy
  have e3 : len ax X1 S * len ax X1 S = len ax Y1 S * len ax Y1 S := by
    rw [len_sq, len_sq]; linear_combination hd
  have e4 : len ax X1 S = len ax Y1 S :=
    (mul_self_inj (len_nonneg ax X1 S) (len_nonneg ax Y1 S)).1 e3
  have c1 : SegCong V X1 V Y1 := (len_eq_iff ax (Ne.symm hX1V) (Ne.symm hY1V)).1 hl
  have c2 : SegCong X1 S Y1 S := (len_eq_iff ax hX1S hY1S).1 e4
  have c3 : SegCong V S V S := segCong_refl (Line := L) (Ne.symm hSV)
  have t1 : IsTriangle (Line := L) V X1 S := fun hh => nX1S hh.swap12
  have t2 : IsTriangle (Line := L) V Y1 S := fun hh => nY1S hh.swap12
  obtain ⟨-, -, -, a1, -, -⟩ := theorem16 (L := L) t1 t2 c1 c3 c2
  -- back to the sides `VX`, `VY`
  have hXr : X ∈ ray V X1 := mem_ray_comm hX1
  have hYr : Y ∈ ray V Y1 := mem_ray_comm hY1
  have hSr : S ∈ ray V S := mem_ray_self' (L := L) hSV
  have nXS : ¬Collinear (Line := L) X V S := not_collinear_of_mem_rays (L := L) nX1S hXr hSr
  have nYS : ¬Collinear (Line := L) Y V S := not_collinear_of_mem_rays (L := L) nY1S hYr hSr
  have a2 : AngCong X V S Y V S := angCong_of_sameAngle nX1S nY1S
    (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hX1) rfl)
    (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hY1) rfl) a1
  refine ⟨angCong_swap_right nXS nYS a2, ?_⟩
  -- the interior
  have lX := len_pos ax (Ne.symm hXV)
  have lY := len_pos ax (Ne.symm hYV)
  have l1 := len_pos ax (Ne.symm hX1V)
  have m1 := len_pos ax (Ne.symm hY1V)
  have r1 := side_ray ax hXV hX1 S
  have r2 := side_ray ax hXV hX1 Y
  have r3 := side_ray ax hYV hY1 X1
  have r4 := side_ray ax hYV hY1 S
  have r5 := side_ray ax hYV hY1 X
  have r6 := side_ray ax hXV hX1 Y1
  have anti : ∀ Z W : P, side ax V Z W = -side ax V W Z := fun Z W => by unfold side; ring
  have hσσ : 0 < side ax V X1 Y1 * side ax V X1 Y1 := mul_self_pos.2 hσ
  refine mem_interior_of_side ax hn ?_ ?_
  · -- `side V X S · side V X Y > 0`
    have k1 : side ax V X S * len ax V X1 = len ax V X * (k * side ax V X1 Y1) := by
      linear_combination -r1 + (len ax V X) * sX'
    have q1 : side ax V X1 Y * len ax V Y1 = len ax V Y * side ax V X1 Y1 := by
      linear_combination (len ax V Y1) * anti X1 Y - (len ax V Y) * anti X1 Y1 + r3
    have k2 : side ax V X Y * len ax V X1 * len ax V Y1 =
        len ax V X * len ax V Y * side ax V X1 Y1 := by
      linear_combination -(len ax V Y1) * r2 + (len ax V X) * q1
    have key : (side ax V X S * side ax V X Y) * (len ax V X1 * len ax V X1 * len ax V Y1) =
        (len ax V X * len ax V X * len ax V Y * k) * (side ax V X1 Y1 * side ax V X1 Y1) := by
      linear_combination (side ax V X Y * len ax V X1 * len ax V Y1) * k1 +
        (len ax V X * (k * side ax V X1 Y1)) * k2
    have hpos : 0 < (len ax V X * len ax V X * len ax V Y * k) *
        (side ax V X1 Y1 * side ax V X1 Y1) :=
      mul_pos (mul_pos (mul_pos (mul_pos lX lX) lY) hk) hσσ
    rw [← key] at hpos
    exact pos_of_mul_pos_left hpos (le_of_lt (mul_pos (mul_pos l1 l1) m1))
  · -- `side V Y S · side V Y X > 0`
    have k1 : side ax V Y S * len ax V Y1 = len ax V Y * (-(k * side ax V X1 Y1)) := by
      linear_combination -r4 + (len ax V Y) * sY'
    have q1 : side ax V Y1 X * len ax V X1 = -(len ax V X * side ax V X1 Y1) := by
      linear_combination (len ax V X1) * anti Y1 X + r6
    have k2 : side ax V Y X * len ax V Y1 * len ax V X1 =
        -(len ax V X * len ax V Y * side ax V X1 Y1) := by
      linear_combination -(len ax V X1) * r5 + (len ax V Y) * q1
    have key : (side ax V Y S * side ax V Y X) * (len ax V Y1 * len ax V Y1 * len ax V X1) =
        (len ax V Y * len ax V Y * len ax V X * k) * (side ax V X1 Y1 * side ax V X1 Y1) := by
      linear_combination (side ax V Y X * len ax V Y1 * len ax V X1) * k1 +
        (len ax V Y * (-(k * side ax V X1 Y1))) * k2
    have hpos : 0 < (len ax V Y * len ax V Y * len ax V X * k) *
        (side ax V X1 Y1 * side ax V X1 Y1) :=
      mul_pos (mul_pos (mul_pos (mul_pos lY lY) lX) hk) hσσ
    rw [← key] at hpos
    exact pos_of_mul_pos_left hpos (le_of_lt (mul_pos (mul_pos m1 m1) l1))

/-- The dot product `(Y - V) · (Z - V)` in co-ordinates. -/
noncomputable def dot (V Y Z : P) : G ax :=
  (px ax Y - px ax V) * (px ax Z - px ax V) + (py ax Y - py ax V) * (py ax Z - py ax V)

theorem coords_ne {X W : P} (h : X ≠ W) : px ax W - px ax X ≠ 0 ∨ py ax W - py ax X ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply (coords_bijective ax).1
  simp only [Prod.mk.injEq]
  exact ⟨(sub_eq_zero.1 hc.1).symm, (sub_eq_zero.1 hc.2).symm⟩

/-- **Betweenness from co-ordinates**: `X + t (W - X)` with `0 < t < 1` lies between `X` and `W`. -/
theorem between_of_coords {X T W : P} (hXW : X ≠ W) {t : G ax} (h0 : 0 < t) (h1 : t < 1)
    (hx : px ax T - px ax X = t * (px ax W - px ax X))
    (hy : py ax T - py ax X = t * (py ax W - py ax X)) : Between X T W := by
  have hd := coords_ne ax hXW
  -- a vector `c • (W - X)` with `c ≠ 0` is not zero
  have key : ∀ c : G ax, c ≠ 0 → ¬(c * (px ax W - px ax X) = 0 ∧ c * (py ax W - py ax X) = 0) := by
    rintro c hc ⟨e1, e2⟩
    rcases hd with h | h
    · exact h ((mul_eq_zero.1 e1).resolve_left hc)
    · exact h ((mul_eq_zero.1 e2).resolve_left hc)
  have hTX : X ≠ T := by
    rintro rfl
    exact key t (ne_of_gt h0) ⟨by linear_combination -hx, by linear_combination -hy⟩
  have hTW : T ≠ W := by
    rintro rfl
    exact key (1 - t) (ne_of_gt (sub_pos.2 h1)) ⟨by linear_combination hx, by linear_combination hy⟩
  have hcol : Collinear (Line := L) X W T := by
    rw [collinear_iff_side ax hXW]
    unfold side; rw [hx, hy]; ring
  rcases between_trichotomy (Line := L) hcol.swap23 hTX hXW hTW with hb | hb | hb
  · -- `X` between `T` and `W`
    exfalso
    obtain ⟨s, s0, s1, e1, e2⟩ := between_coords ax hb
    have hpos : 0 < t + s * (1 - t) := add_pos h0 (mul_pos s0 (sub_pos.2 h1))
    exact key _ (ne_of_gt hpos) ⟨by linear_combination -e1 - (1 - s) * hx,
      by linear_combination -e2 - (1 - s) * hy⟩
  · exact hb
  · -- `W` between `X` and `T`
    exfalso
    obtain ⟨s, s0, s1, e1, e2⟩ := between_coords ax hb
    have hpos : 0 < 1 - s * t := by nlinarith
    exact key _ (ne_of_gt hpos) ⟨by linear_combination e1 + s * hx, by linear_combination e2 + s * hy⟩

/-- **The foot of a perpendicular**, in co-ordinates: with `U` the point of the half-ray `VX` at
the unit distance and `τ = (U - V) · (S - V)` strictly between `0` and `VX`, the point
`F = V + τ (U - V)` lies between `V` and `X`, the angle `∠VFS` is a right angle, and
`SF² = (S - V)² - τ²`. -/
theorem foot_of_coords {V X U S : P} (hVX : V ≠ X) (_hU : U ∈ ray V X) (hlU : len ax V U = 1)
    (hx : px ax X - px ax V = len ax V X * (px ax U - px ax V))
    (hy : py ax X - py ax V = len ax V X * (py ax U - py ax V))
    (hS : ¬Collinear (Line := L) V X S) (h0 : 0 < dot ax V U S) (h1 : dot ax V U S < len ax V X) :
    ∃ F : P, Between V F X ∧ IsRightAngle (L := L) V F S ∧
      len ax S F * len ax S F = dot ax V S S - dot ax V U S * dot ax V U S := by
  set τ := dot ax V U S with hτ
  set d1 := px ax U - px ax V
  set d2 := py ax U - py ax V
  have hd : d1 * d1 + d2 * d2 = 1 := by
    have e := len_sq ax V U
    rw [hlU] at e
    linear_combination -e
  have lX := len_pos ax hVX
  set F := mkPt ax (px ax V + τ * d1) (py ax V + τ * d2)
  obtain ⟨fx, fy⟩ := mkPt_coords ax (px ax V + τ * d1) (py ax V + τ * d2)
  have hne : len ax V X ≠ 0 := ne_of_gt lX
  have hb : Between V F X := by
    refine between_of_coords ax hVX (t := τ / len ax V X) (div_pos h0 lX)
      ((div_lt_one lX).2 h1) ?_ ?_
    · rw [fx, hx]; field_simp; ring
    · rw [fy, hy]; field_simp; ring
  have hVF : V ≠ F := ne12_of_between (Line := L) hb
  have hFX : F ≠ X := ne23_of_between (Line := L) hb
  -- `S` is off the line `VX`
  obtain ⟨l, hVl, hXl⟩ := exists_line (Line := L) hVX
  have hFl : F ∈ l := mem_of_collinear (collinear_of_between (Line := L) hb).swap23 hVX hVl hXl
  have hSl : S ∉ l := fun h => hS ⟨l, hVl, hXl, h⟩
  have nVFS : ¬Collinear (Line := L) V F S := by
    rintro ⟨m, h1, h2, h3⟩
    exact hSl (by rw [line_unique hVF hVl hFl h1 h2]; exact h3)
  have nXFS : ¬Collinear (Line := L) X F S := by
    rintro ⟨m, h1, h2, h3⟩
    exact hSl (by rw [line_unique hFX.symm hXl hFl h1 h2]; exact h3)
  -- the distances `FV = τ`, `FX = VX - τ`
  have lFV : len ax F V = τ := by
    have e := len_sq ax F V
    have e' : len ax F V * len ax F V = τ * τ := by
      rw [e, fx, fy]; linear_combination (τ * τ) * hd
    exact (mul_self_inj (len_nonneg ax F V) (le_of_lt h0)).1 e'
  have lFX : len ax F X = len ax V X - τ := by
    have e := len_sq ax F X
    have e' : len ax F X * len ax F X = (len ax V X - τ) * (len ax V X - τ) := by
      have hx' : px ax X = px ax V + len ax V X * d1 := by linear_combination hx
      have hy' : py ax X = py ax V + len ax V X * d2 := by linear_combination hy
      rw [e, fx, fy, hx', hy']; linear_combination ((len ax V X - τ) * (len ax V X - τ)) * hd
    exact (mul_self_inj (len_nonneg ax F X) (le_of_lt (sub_pos.2 h1))).1 e'
  -- the points of the half-rays `FV`, `FX` at the unit distance
  obtain ⟨V', hV'r, lV', vx, vy⟩ := unit_point ax hVF.symm
  obtain ⟨X', hX'r, lX', xx, xy⟩ := unit_point ax hFX
  rw [lFV] at vx vy
  rw [lFX] at xx xy
  have v1 : px ax V' - px ax F = -d1 := mul_left_cancel₀ (ne_of_gt h0) (by
    rw [← vx, fx]; ring)
  have v2 : py ax V' - py ax F = -d2 := mul_left_cancel₀ (ne_of_gt h0) (by
    rw [← vy, fy]; ring)
  have x1 : px ax X' - px ax F = d1 := mul_left_cancel₀ (ne_of_gt (sub_pos.2 h1)) (by
    rw [← xx, fx]; linear_combination hx)
  have x2 : py ax X' - py ax F = d2 := mul_left_cancel₀ (ne_of_gt (sub_pos.2 h1)) (by
    rw [← xy, fy]; linear_combination hy)
  have nV'FS : ¬Collinear (Line := L) V' F S :=
    not_collinear_of_mem_rays (L := L) nVFS hV'r (mem_ray_self' (L := L) (nc_ne ax nVFS).2.1)
  have nX'FS : ¬Collinear (Line := L) X' F S :=
    not_collinear_of_mem_rays (L := L) nXFS hX'r (mem_ray_self' (L := L) (nc_ne ax nXFS).2.1)
  obtain ⟨hV'F, hSF, hV'S⟩ := nc_ne ax nV'FS
  obtain ⟨hX'F, -, hX'S⟩ := nc_ne ax nX'FS
  -- `SV' ≡ SX'`
  have e3 : len ax V' S * len ax V' S = len ax X' S * len ax X' S := by
    rw [len_sq, len_sq]
    have hv1 : px ax V' = px ax F - d1 := by linear_combination v1
    have hv2 : py ax V' = py ax F - d2 := by linear_combination v2
    have hx1 : px ax X' = px ax F + d1 := by linear_combination x1
    have hx2 : py ax X' = py ax F + d2 := by linear_combination x2
    rw [hv1, hv2, hx1, hx2, fx, fy]
    have : τ = d1 * (px ax S - px ax V) + d2 * (py ax S - py ax V) := rfl
    linear_combination (-4 : G ax) * this - 4 * τ * hd
  have c1 : SegCong F V' F X' :=
    (len_eq_iff ax hV'F.symm hX'F.symm).1 (by rw [lV', lX'])
  have c2 : SegCong V' S X' S :=
    (len_eq_iff ax hV'S hX'S).1 ((mul_self_inj (len_nonneg ax _ _) (len_nonneg ax _ _)).1 e3)
  have c3 : SegCong F S F S := segCong_refl (Line := L) hSF.symm
  obtain ⟨-, -, -, a1, -, -⟩ := theorem16 (L := L) (fun hh => nV'FS hh.swap12)
    (fun hh => nX'FS hh.swap12) c1 c3 c2
  have a2 : AngCong V F S X F S := angCong_of_sameAngle nV'FS nX'FS
    (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hV'r) rfl)
    (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hX'r) rfl) a1
  refine ⟨F, hb, ⟨nVFS, X, hb, angCong_swap_right nVFS nXFS a2⟩, ?_⟩
  rw [len_sq, fx, fy]
  have : τ = d1 * (px ax S - px ax V) + d2 * (py ax S - py ax V) := rfl
  unfold dot
  linear_combination (2 * τ) * this + τ * τ * hd

theorem unit_norm {V U : P} (h : len ax V U = 1) :
    (px ax U - px ax V) * (px ax U - px ax V) + (py ax U - py ax V) * (py ax U - py ax V) = 1 := by
  have e := len_sq ax V U
  rw [h] at e
  linear_combination -e

/-- A point inside an angle lies on neither side line. -/
theorem nc_of_interior {X V Y S : P} (hn : ¬Collinear (Line := L) X V Y) (h : S ∈ Interior X V Y) :
    ¬Collinear (Line := L) V X S ∧ ¬Collinear (Line := L) V Y S := by
  obtain ⟨hXV, hYV, -⟩ := nc_ne ax hn
  obtain ⟨a, hVa, hXa⟩ := exists_line (Line := L) (Ne.symm hXV)
  obtain ⟨b, hVb, hYb⟩ := exists_line (Line := L) (Ne.symm hYV)
  obtain ⟨s1, s2⟩ := h a b hVa hXa hVb hYb
  constructor
  · rintro ⟨m, h1, h2, h3⟩
    exact s1.1 (by rw [line_unique (Ne.symm hXV) hVa hXa h1 h2]; exact h3)
  · rintro ⟨m, h1, h2, h3⟩
    exact s2.1 (by rw [line_unique (Ne.symm hYV) hVb hYb h1 h2]; exact h3)

theorem cross_ne_of_rays {X V Y X1 Y1 : P} (h : ¬Collinear (Line := L) X V Y) (h1 : X1 ∈ ray V X)
    (h2 : Y1 ∈ ray V Y) :
    (px ax X1 - px ax V) * (py ax Y1 - py ax V) - (py ax X1 - py ax V) * (px ax Y1 - px ax V)
      ≠ 0 := by
  intro e
  have n1 : ¬Collinear (Line := L) X1 V Y1 := not_collinear_of_mem_rays (L := L) h h1 h2
  exact n1 ((collinear_iff_side ax (Ne.symm (ne_of_mem_ray h1))).2 e).swap12

set_option maxHeartbeats 1000000 in
/-- **The bisectors of the three angles of a triangle meet in a point** `S`, inside the three
angles, and **the perpendiculars from `S` to the three sides are congruent**, their feet lying
between the vertices (the incircle). -/
theorem incenter_exists {A B C : P} (hn : ¬Collinear (Line := L) A B C) :
    ∃ S : P, (S ∈ Interior B A C ∧ S ∈ Interior A B C ∧ S ∈ Interior A C B) ∧
      (AngCong B A S S A C ∧ AngCong A B S S B C ∧ AngCong A C S S C B) ∧
      ∃ Fa Fb Fc : P, Between B Fa C ∧ Between C Fb A ∧ Between A Fc B ∧
        IsRightAngle (L := L) B Fa S ∧ IsRightAngle (L := L) C Fb S ∧
        IsRightAngle (L := L) A Fc S ∧ SegCong S Fa S Fb ∧ SegCong S Fa S Fc := by
  obtain ⟨hAB, hCB, hAC⟩ := nc_ne ax hn
  have hBA := Ne.symm hAB
  have hBC := Ne.symm hCB
  have hCA := Ne.symm hAC
  have nBAC : ¬Collinear (Line := L) B A C := fun hh => hn hh.swap12
  have nACB : ¬Collinear (Line := L) A C B := fun hh => hn hh.swap23
  -- the points of the six half-rays at the unit distance
  obtain ⟨BA, hBAr, lBA, xB1, yB1⟩ := unit_point ax hAB
  obtain ⟨CA, hCAr, lCA, xC1, yC1⟩ := unit_point ax hAC
  obtain ⟨AB, hABr, lAB, xA2, yA2⟩ := unit_point ax hBA
  obtain ⟨CB, hCBr, lCB, xC2, yC2⟩ := unit_point ax hBC
  obtain ⟨AC, hACr, lAC, xA3, yA3⟩ := unit_point ax hCA
  obtain ⟨BC, hBCr, lBC, xB3, yB3⟩ := unit_point ax hCB
  have nu := unit_norm ax lBA
  have nw := unit_norm ax lCA
  have np := unit_norm ax lAB
  have nq := unit_norm ax lCB
  have nr := unit_norm ax lAC
  have nz := unit_norm ax lBC
  have xA2' : px ax A - px ax B = len ax A B * (px ax AB - px ax B) := by
    rw [xA2, len_comm ax B A]
  have yA2' : py ax A - py ax B = len ax A B * (py ax AB - py ax B) := by
    rw [yA2, len_comm ax B A]
  have xA3' : px ax A - px ax C = len ax A C * (px ax AC - px ax C) := by
    rw [xA3, len_comm ax C A]
  have yA3' : py ax A - py ax C = len ax A C * (py ax AC - py ax C) := by
    rw [yA3, len_comm ax C A]
  have xB3' : px ax B - px ax C = len ax B C * (px ax BC - px ax C) := by
    rw [xB3, len_comm ax C B]
  have yB3' : py ax B - py ax C = len ax B C * (py ax BC - py ax C) := by
    rw [yB3, len_comm ax C B]
  have ha : 0 < len ax B C := len_pos ax hBC
  have hb : 0 < len ax A C := len_pos ax hAC
  have hc : 0 < len ax A B := len_pos ax hAB
  have hDpos : 0 < len ax B C + len ax A C + len ax A B := by linarith
  have hD : len ax B C + len ax A C + len ax A B ≠ 0 := ne_of_gt hDpos
  -- the incentre
  obtain ⟨S, hS⟩ := (coords_bijective ax).2
    (px ax A + len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
      ((px ax BA - px ax A) + (px ax CA - px ax A)),
     py ax A + len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
      ((py ax BA - py ax A) + (py ax CA - py ax A)))
  simp only [Prod.mk.injEq] at hS
  obtain ⟨sx, sy⟩ := hS
  have sAx : px ax S - px ax A = len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
      ((px ax BA - px ax A) + (px ax CA - px ax A)) := by rw [sx]; ring
  have sAy : py ax S - py ax A = len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
      ((py ax BA - py ax A) + (py ax CA - py ax A)) := by rw [sy]; ring
  have sBx : px ax S - px ax B =
      len ax B C * len ax A B / (len ax B C + len ax A C + len ax A B) *
        ((px ax AB - px ax B) + (px ax CB - px ax B)) := by
    rw [sx]; exact vertexB_alg hD (ne_of_gt hc) xB1 xA2' xC2 xC1
  have sBy : py ax S - py ax B =
      len ax B C * len ax A B / (len ax B C + len ax A C + len ax A B) *
        ((py ax AB - py ax B) + (py ax CB - py ax B)) := by
    rw [sy]; exact vertexB_alg hD (ne_of_gt hc) yB1 yA2' yC2 yC1
  have sCx : px ax S - px ax C =
      len ax B C * len ax A C / (len ax B C + len ax A C + len ax A B) *
        ((px ax AC - px ax C) + (px ax BC - px ax C)) := by
    rw [sx]; exact vertexC_alg hD (ne_of_gt hb) xB1 xA3' xB3' xC1
  have sCy : py ax S - py ax C =
      len ax B C * len ax A C / (len ax B C + len ax A C + len ax A B) *
        ((py ax AC - py ax C) + (py ax BC - py ax C)) := by
    rw [sy]; exact vertexC_alg hD (ne_of_gt hb) yB1 yA3' yB3' yC1
  -- the bisectors
  obtain ⟨angA, intA⟩ := bisector_of_coords ax nBAC hBAr hCAr (lBA.trans lCA.symm)
    (div_pos (mul_pos hb hc) hDpos) sAx sAy
  obtain ⟨angB, intB⟩ := bisector_of_coords ax hn hABr hCBr (lAB.trans lCB.symm)
    (div_pos (mul_pos ha hc) hDpos) sBx sBy
  obtain ⟨angC, intC⟩ := bisector_of_coords ax nACB hACr hBCr (lAC.trans lBC.symm)
    (div_pos (mul_pos ha hb) hDpos) sCx sCy
  refine ⟨S, ⟨intA, intB, intC⟩, ⟨angA, angB, angC⟩, ?_⟩
  -- the cosines of the angles lie strictly between `-1` and `1`
  obtain ⟨cA0, -⟩ := cos_lt_one nu nw (cross_ne_of_rays ax nBAC hBAr hCAr)
  obtain ⟨cB0, -⟩ := cos_lt_one np nq (cross_ne_of_rays ax hn hABr hCBr)
  obtain ⟨cC0, -⟩ := cos_lt_one nr nz (cross_ne_of_rays ax nACB hACr hBCr)
  -- the laws of cosines
  have lawA : len ax B C * len ax B C = len ax A C * len ax A C + len ax A B * len ax A B -
      2 * len ax A C * len ax A B * ((px ax BA - px ax A) * (px ax CA - px ax A) +
        (py ax BA - py ax A) * (py ax CA - py ax A)) := by
    have e := len_sq ax B C
    have dx : px ax B - px ax C = len ax A B * (px ax BA - px ax A) -
        len ax A C * (px ax CA - px ax A) := by linear_combination xB1 - xC1
    have dy : py ax B - py ax C = len ax A B * (py ax BA - py ax A) -
        len ax A C * (py ax CA - py ax A) := by linear_combination yB1 - yC1
    rw [dx, dy] at e
    linear_combination e + (len ax A B * len ax A B) * nu + (len ax A C * len ax A C) * nw
  have lawB : len ax A C * len ax A C = len ax B C * len ax B C + len ax A B * len ax A B -
      2 * len ax B C * len ax A B * ((px ax AB - px ax B) * (px ax CB - px ax B) +
        (py ax AB - py ax B) * (py ax CB - py ax B)) := by
    have e := len_sq ax A C
    have dx : px ax A - px ax C = len ax A B * (px ax AB - px ax B) -
        len ax B C * (px ax CB - px ax B) := by linear_combination xA2' - xC2
    have dy : py ax A - py ax C = len ax A B * (py ax AB - py ax B) -
        len ax B C * (py ax CB - py ax B) := by linear_combination yA2' - yC2
    rw [dx, dy] at e
    linear_combination e + (len ax A B * len ax A B) * np + (len ax B C * len ax B C) * nq
  have lawC : len ax A B * len ax A B = len ax B C * len ax B C + len ax A C * len ax A C -
      2 * len ax B C * len ax A C * ((px ax AC - px ax C) * (px ax BC - px ax C) +
        (py ax AC - py ax C) * (py ax BC - py ax C)) := by
    have e := len_sq ax A B
    have dx : px ax A - px ax B = len ax A C * (px ax AC - px ax C) -
        len ax B C * (px ax BC - px ax C) := by linear_combination xA3' - xB3'
    have dy : py ax A - py ax B = len ax A C * (py ax AC - py ax C) -
        len ax B C * (py ax BC - py ax C) := by linear_combination yA3' - yB3'
    rw [dx, dy] at e
    linear_combination e + (len ax A C * len ax A C) * nr + (len ax B C * len ax B C) * nz
  -- the triangle inequalities
  have tA : len ax B C < len ax A C + len ax A B := by
    have e : (len ax A C + len ax A B) * (len ax A C + len ax A B) - len ax B C * len ax B C =
        2 * (len ax A C * len ax A B) * (1 + ((px ax BA - px ax A) * (px ax CA - px ax A) +
          (py ax BA - py ax A) * (py ax CA - py ax A))) := by linear_combination -lawA
    have hpos := mul_pos (mul_pos two_pos (mul_pos hb hc)) (neg_lt_iff_pos_add'.1 cA0)
    rw [← e] at hpos
    exact (mul_self_lt_mul_self_iff ha.le (add_pos hb hc).le).2 (sub_pos.1 hpos)
  have tB : len ax A C < len ax B C + len ax A B := by
    have e : (len ax B C + len ax A B) * (len ax B C + len ax A B) - len ax A C * len ax A C =
        2 * (len ax B C * len ax A B) * (1 + ((px ax AB - px ax B) * (px ax CB - px ax B) +
          (py ax AB - py ax B) * (py ax CB - py ax B))) := by linear_combination -lawB
    have hpos := mul_pos (mul_pos two_pos (mul_pos ha hc)) (neg_lt_iff_pos_add'.1 cB0)
    rw [← e] at hpos
    exact (mul_self_lt_mul_self_iff hb.le (add_pos ha hc).le).2 (sub_pos.1 hpos)
  have tC : len ax A B < len ax B C + len ax A C := by
    have e : (len ax B C + len ax A C) * (len ax B C + len ax A C) - len ax A B * len ax A B =
        2 * (len ax B C * len ax A C) * (1 + ((px ax AC - px ax C) * (px ax BC - px ax C) +
          (py ax AC - py ax C) * (py ax BC - py ax C))) := by linear_combination -lawC
    have hpos := mul_pos (mul_pos two_pos (mul_pos ha hb)) (neg_lt_iff_pos_add'.1 cC0)
    rw [← e] at hpos
    exact (mul_self_lt_mul_self_iff hc.le (add_pos ha hb).le).2 (sub_pos.1 hpos)
  -- the projections of `S` on the sides (tangent lengths)
  obtain ⟨vA1, vA2⟩ := vertex_alg (p1 := px ax CA - px ax A) (p2 := py ax CA - py ax A)
    (q1 := px ax BA - px ax A) (q2 := py ax BA - py ax A)
    (k := len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B)) nu (s1 := px ax S - px ax A)
    (s2 := py ax S - py ax A) (by rw [sAx]; ring) (by rw [sAy]; ring)
  obtain ⟨vB1, vB2⟩ := vertex_alg (p1 := px ax AB - px ax B) (p2 := py ax AB - py ax B)
    (q1 := px ax CB - px ax B) (q2 := py ax CB - py ax B) nq sBx sBy
  obtain ⟨vC1, vC2⟩ := vertex_alg (p1 := px ax BC - px ax C) (p2 := py ax BC - py ax C)
    (q1 := px ax AC - px ax C) (q2 := py ax AC - py ax C)
    (k := len ax B C * len ax A C / (len ax B C + len ax A C + len ax A B)) nr (s1 := px ax S - px ax C)
    (s2 := py ax S - py ax C) (by rw [sCx]; ring) (by rw [sCy]; ring)
  have gA := tangent_alg (D := len ax B C + len ax A C + len ax A B) rfl hD lawA
  have gB := tangent_alg (D := len ax B C + len ax A C + len ax A B) (by ring) hD lawB
  have gC := tangent_alg (D := len ax B C + len ax A C + len ax A B) (by ring) hD lawC
  have τA : 2 * dot ax A BA S = len ax A C + len ax A B - len ax B C := by
    unfold dot; linear_combination 2 * vA1 + gA
  have τB : 2 * dot ax B CB S = len ax B C + len ax A B - len ax A C := by
    unfold dot; linear_combination 2 * vB1 + gB
  have τC : 2 * dot ax C AC S = len ax B C + len ax A C - len ax A B := by
    unfold dot; linear_combination 2 * vC1 + gC
  -- the feet of the perpendiculars
  obtain ⟨nAB, -⟩ := nc_of_interior ax nBAC intA
  obtain ⟨-, nBC⟩ := nc_of_interior ax hn intB
  obtain ⟨nCA, -⟩ := nc_of_interior ax nACB intC
  obtain ⟨Fc, bc, rc, dc⟩ := foot_of_coords ax hAB hBAr lBA xB1 yB1 nAB (by linarith)
    (by linarith)
  obtain ⟨Fa, ba, ra, da⟩ := foot_of_coords ax hBC hCBr lCB xC2 yC2 nBC (by linarith)
    (by linarith)
  obtain ⟨Fb, bb, rb, db⟩ := foot_of_coords ax hCA hACr lAC xA3 yA3 nCA (by linarith)
    (by rw [len_comm]; linarith)
  refine ⟨Fa, Fb, Fc, ba, bb, bc, ra, rb, rc, ?_⟩
  -- the three perpendiculars have the same length `|ABC| / (a + b + c)`
  have eA : len ax A C * len ax A B *
        ((px ax CA - px ax A) * (py ax BA - py ax A) - (py ax CA - py ax A) * (px ax BA - px ax A)) =
      (px ax C - px ax A) * (py ax B - py ax A) - (py ax C - py ax A) * (px ax B - px ax A) := by
    rw [xC1, yB1, yC1, xB1]; ring
  have eB : len ax B C * len ax A B *
        ((px ax AB - px ax B) * (py ax CB - py ax B) - (py ax AB - py ax B) * (px ax CB - px ax B)) =
      (px ax A - px ax B) * (py ax C - py ax B) - (py ax A - py ax B) * (px ax C - px ax B) := by
    rw [xA2', yC2, yA2', xC2]; ring
  have eC : len ax B C * len ax A C *
        ((px ax BC - px ax C) * (py ax AC - py ax C) - (py ax BC - py ax C) * (px ax AC - px ax C)) =
      (px ax B - px ax C) * (py ax A - py ax C) - (py ax B - py ax C) * (px ax A - px ax C) := by
    rw [xB3', yA3', yB3', xA3']; ring
  have kAB : len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
        ((px ax CA - px ax A) * (py ax BA - py ax A) - (py ax CA - py ax A) * (px ax BA - px ax A)) =
      len ax B C * len ax A B / (len ax B C + len ax A C + len ax A B) *
        ((px ax AB - px ax B) * (py ax CB - py ax B) - (py ax AB - py ax B) * (px ax CB - px ax B)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eA, eB]; ring
  have kAC : len ax A C * len ax A B / (len ax B C + len ax A C + len ax A B) *
        ((px ax CA - px ax A) * (py ax BA - py ax A) - (py ax CA - py ax A) * (px ax BA - px ax A)) =
      len ax B C * len ax A C / (len ax B C + len ax A C + len ax A B) *
        ((px ax BC - px ax C) * (py ax AC - py ax C) - (py ax BC - py ax C) * (px ax AC - px ax C)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eA, eC]; ring
  have DA : len ax S Fa * len ax S Fa = (len ax B C * len ax A B / (len ax B C + len ax A C +
      len ax A B) * ((px ax AB - px ax B) * (py ax CB - py ax B) -
        (py ax AB - py ax B) * (px ax CB - px ax B))) * (len ax B C * len ax A B /
      (len ax B C + len ax A C + len ax A B) * ((px ax AB - px ax B) * (py ax CB - py ax B) -
        (py ax AB - py ax B) * (px ax CB - px ax B))) := by
    rw [da]; unfold dot; linear_combination vB2
  have DB : len ax S Fb * len ax S Fb = (len ax B C * len ax A C / (len ax B C + len ax A C +
      len ax A B) * ((px ax BC - px ax C) * (py ax AC - py ax C) -
        (py ax BC - py ax C) * (px ax AC - px ax C))) * (len ax B C * len ax A C /
      (len ax B C + len ax A C + len ax A B) * ((px ax BC - px ax C) * (py ax AC - py ax C) -
        (py ax BC - py ax C) * (px ax AC - px ax C))) := by
    rw [db]; unfold dot; linear_combination vC2
  have DC : len ax S Fc * len ax S Fc = (len ax A C * len ax A B / (len ax B C + len ax A C +
      len ax A B) * ((px ax CA - px ax A) * (py ax BA - py ax A) -
        (py ax CA - py ax A) * (px ax BA - px ax A))) * (len ax A C * len ax A B /
      (len ax B C + len ax A C + len ax A B) * ((px ax CA - px ax A) * (py ax BA - py ax A) -
        (py ax CA - py ax A) * (px ax BA - px ax A))) := by
    rw [dc]; unfold dot; linear_combination vA2
  obtain ⟨-, hSa, -⟩ := nc_ne ax ra.1
  obtain ⟨-, hSb, -⟩ := nc_ne ax rb.1
  obtain ⟨-, hSc, -⟩ := nc_ne ax rc.1
  have lab : len ax S Fa = len ax S Fb := (mul_self_inj (len_nonneg ax _ _) (len_nonneg ax _ _)).1
    (by rw [DA, DB, ← kAB, ← kAC])
  have lac : len ax S Fa = len ax S Fc := (mul_self_inj (len_nonneg ax _ _) (len_nonneg ax _ _)).1
    (by rw [DA, DC, ← kAB])
  exact ⟨(len_eq_iff ax hSa hSb).1 lab,
    (len_eq_iff ax hSa hSc).1 lac⟩

end Incircle

end Pas

end HilbertFoundations
