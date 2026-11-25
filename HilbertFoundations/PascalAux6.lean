import HilbertFoundations.PascalAux5

/-!
# Helper module for `Pascal.lean`: co-ordinates, lines and Pascal's theorem

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV, with
rectangular axes `ax`.

* **Co-ordinates**: every vector is uniquely `p + J s` with `p`, `s` on the axis `x`; `xc`, `yc` are
  additive.
* **Lines through `O`**: the vectors of a line `ℓ ≠ y` through `O` are those with `y = m x`, where
  `m` is the slope of `ℓ` (`mem_lineSub_iff_slope`); the vectors of `y` are those with `x = 0`.
* **The cross product** `cross d v = x_d y_v - y_d x_v`: for a direction `d ≠ 0` of a line `ℓ`
  through `O`, `v ∈ ℓ ↔ cross d v = 0`; hence a point lies on the line `XY` iff
  `cross (Y - X) (Z - X) = 0`, and two lines are parallel or equal iff the cross product of their
  directions vanishes.
* **Pascal's theorem** (`pascal`): a computation with these criteria in the field `G ax`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

/-- The cross product in co-ordinates. -/
def cr {K : Type*} [Field K] (x1 y1 x2 y2 : K) : K := x1 * y2 - y1 * x2

section Coords

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable (ax : Axes P L)

theorem coords_exists (v : V ax) :
    ∃ p s : V ax, p ∈ Xs ax ∧ s ∈ Xs ax ∧ v = p + jE ax s := by
  obtain ⟨p, q, hp, hq, e⟩ := exists_XY ax v
  refine ⟨p, -jE ax q, hp, (Xs ax).neg_mem (jE_Y ax hq), ?_⟩
  rw [map_neg, jE_jE_apply, neg_neg]; exact e

theorem coords_unique {p s p' s' : V ax} (hp : p ∈ Xs ax) (hs : s ∈ Xs ax) (hp' : p' ∈ Xs ax)
    (hs' : s' ∈ Xs ax) (h : p + jE ax s = p' + jE ax s') : p = p' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := XY_unique ax hp (jE_X ax hs) hp' (jE_X ax hs') h
  refine ⟨h1, ?_⟩
  have : jE ax (s - s') = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 (jE_injective ax this)

/-- The first co-ordinate. -/
noncomputable def xc (v : V ax) : G ax :=
  ⟨Classical.choose (coords_exists ax v), (Classical.choose_spec
    (Classical.choose_spec (coords_exists ax v))).1⟩

/-- The second co-ordinate. -/
noncomputable def yc (v : V ax) : G ax :=
  ⟨Classical.choose (Classical.choose_spec (coords_exists ax v)), (Classical.choose_spec
    (Classical.choose_spec (coords_exists ax v))).2.1⟩

theorem coords_eq (v : V ax) : v = (xc ax v : V ax) + jE ax (yc ax v) :=
  (Classical.choose_spec (Classical.choose_spec (coords_exists ax v))).2.2

theorem coords_of {v : V ax} (p s : G ax) (h : v = (p : V ax) + jE ax s) :
    xc ax v = p ∧ yc ax v = s := by
  obtain ⟨h1, h2⟩ := coords_unique ax (xc ax v).2 (yc ax v).2 p.2 s.2 ((coords_eq ax v).symm.trans h)
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

theorem xc_add (v w : V ax) : xc ax (v + w) = xc ax v + xc ax w := by
  refine (coords_of ax (xc ax v + xc ax w) (yc ax v + yc ax w) ?_).1
  rw [AddSubgroup.coe_add, AddSubgroup.coe_add, map_add]
  conv_lhs => rw [coords_eq ax v, coords_eq ax w]
  abel

theorem yc_add (v w : V ax) : yc ax (v + w) = yc ax v + yc ax w := by
  refine (coords_of ax (xc ax v + xc ax w) (yc ax v + yc ax w) ?_).2
  rw [AddSubgroup.coe_add, AddSubgroup.coe_add, map_add]
  conv_lhs => rw [coords_eq ax v, coords_eq ax w]
  abel

/-- The co-ordinates as an additive map. -/
noncomputable def xcHom : V ax →+ G ax :=
  ⟨⟨xc ax, by
    have := xc_add ax 0 0; rw [add_zero] at this
    exact (add_eq_left.1 this.symm)⟩, xc_add ax⟩

noncomputable def ycHom : V ax →+ G ax :=
  ⟨⟨yc ax, by
    have := yc_add ax 0 0; rw [add_zero] at this
    exact (add_eq_left.1 this.symm)⟩, yc_add ax⟩

theorem xc_sub (v w : V ax) : xc ax (v - w) = xc ax v - xc ax w := map_sub (xcHom ax) v w

theorem yc_sub (v w : V ax) : yc ax (v - w) = yc ax v - yc ax w := map_sub (ycHom ax) v w

theorem xc_zero : xc ax 0 = 0 := map_zero (xcHom ax)

theorem yc_zero : yc ax 0 = 0 := map_zero (ycHom ax)

theorem eq_zero_of_coords {v : V ax} (h1 : xc ax v = 0) (h2 : yc ax v = 0) : v = 0 := by
  rw [coords_eq ax v, h1, h2]; simp

theorem vec_ext {v w : V ax} (h1 : xc ax v = xc ax w) (h2 : yc ax v = yc ax w) : v = w := by
  rw [coords_eq ax v, coords_eq ax w, h1, h2]

theorem mem_Ys_iff (v : V ax) : v ∈ Ys ax ↔ xc ax v = 0 := by
  constructor
  · intro h
    have e : (0 : V ax) + v = (xc ax v : V ax) + jE ax (yc ax v) := by rw [zero_add]; exact coords_eq ax v
    obtain ⟨-, -⟩ : True ∧ True := ⟨trivial, trivial⟩
    have hv : v ∈ Ys ax := h
    have := XY_unique ax (Xs ax).zero_mem hv (xc ax v).2 (jE_X ax (yc ax v).2) e
    exact Subtype.ext this.1.symm
  · intro h
    rw [coords_eq ax v, h]
    simp only [ZeroMemClass.coe_zero, zero_add]
    exact jE_X ax (yc ax v).2

/-- The slope of a line `ℓ ≠ y` through `O`, as an element of the field. -/
noncomputable def slopeG {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) : G ax :=
  ⟨slope ax hO hℓ (eV ax), slope_mem ax hO hℓ (eV_mem ax)⟩

theorem slope_eq_mul {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) (u : G ax) :
    slope ax hO hℓ u = ((u * slopeG ax hO hℓ : G ax) : V ax) := by
  show slope ax hO hℓ u = mulV ax u (slope ax hO hℓ (eV ax))
  conv_lhs => rw [← mulV_one ax u.2]
  rw [mulV_def ax u.2, mulV_def ax u.2]
  exact slope_comm ax hO hℓ _ _ (eV_mem ax)

theorem mem_lineSub_iff_slope {ℓ : L} (hO : ax.O ∈ ℓ) (hℓ : ℓ ≠ ax.y) (v : V ax) :
    v ∈ lineSub (L := L) ℓ hO ↔ yc ax v = xc ax v * slopeG ax hO hℓ := by
  constructor
  · intro h
    have e := slope_eq ax hO hℓ (xc ax v).2 (yc ax v).2 (by rw [← coords_eq ax v]; exact h)
    rw [slope_eq_mul] at e
    exact Subtype.ext e.symm
  · intro h
    have := (slope_spec ax hO hℓ (xc ax v).2).2
    rw [slope_eq_mul, ← h, ← coords_eq ax v] at this
    exact this

/-- The **cross product** of two vectors in co-ordinates. -/
noncomputable def cross (v w : V ax) : G ax := cr (xc ax v) (yc ax v) (xc ax w) (yc ax w)

theorem cross_self (v : V ax) : cross ax v v = 0 := by unfold cross cr; ring

/-- A vector lies on the line through `O` in the direction `d ≠ 0` iff its cross product with `d`
vanishes. -/
theorem mem_lineSub_iff_cross {ℓ : L} (hO : ax.O ∈ ℓ) {d : V ax} (hd : d ∈ lineSub (L := L) ℓ hO)
    (hd0 : d ≠ 0) (v : V ax) : v ∈ lineSub (L := L) ℓ hO ↔ cross ax d v = 0 := by
  by_cases hy : ℓ = ax.y
  · subst hy
    have hd' : xc ax d = 0 := (mem_Ys_iff ax d).1 hd
    have hyd : yc ax d ≠ 0 := fun h => hd0 (eq_zero_of_coords ax hd' h)
    show v ∈ Ys ax ↔ _
    rw [mem_Ys_iff, cross, cr, hd', zero_mul, zero_sub, neg_eq_zero, mul_eq_zero, or_iff_right hyd]
  · rw [mem_lineSub_iff_slope ax hO hy] at hd ⊢
    have hxd : xc ax d ≠ 0 := fun h => hd0 (eq_zero_of_coords ax h (by rw [hd, h, zero_mul]))
    rw [cross, cr, hd]
    constructor
    · intro h; rw [h]; ring
    · intro h
      have : xc ax d * (yc ax v - xc ax v * slopeG ax hO hy) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hxd
      · exact sub_eq_zero.1 h1

/-- The parallel through `O` to a line. -/
theorem exists_par0 (l : L) : ∃ l0 : L, ax.O ∈ l0 ∧ ParEq (P := P) l l0 := by
  obtain ⟨m, hm, h⟩ := exists_parEq (P := P) l ax.O
  exact ⟨m, hm, h⟩

/-- **A point lies on the line `XY` iff `cross (Y - X) (Z - X) = 0`.** -/
theorem mem_line_iff_cross {X Y : P} (hXY : X ≠ Y) {l : L} (hX : X ∈ l) (hY : Y ∈ l) (Z : P) :
    Z ∈ l ↔ cross ax (toV ax.O Y - toV ax.O X) (toV ax.O Z - toV ax.O X) = 0 := by
  obtain ⟨l0, hO, hl0⟩ := exists_par0 ax l
  have hd := (mem_line_iff_sub hO hl0 hX Y).1 hY
  have hd0 : toV ax.O Y - toV ax.O X ≠ 0 := fun h => hXY (sub_eq_zero.1 h).symm
  rw [mem_line_iff_sub hO hl0 hX Z, mem_lineSub_iff_cross ax hO hd hd0]

/-- **Two lines are parallel or equal iff the cross product of their directions vanishes.** -/
theorem parEq_iff_cross {X Y X' Y' : P} (hXY : X ≠ Y) (hXY' : X' ≠ Y') {l m : L} (hX : X ∈ l)
    (hY : Y ∈ l) (hX' : X' ∈ m) (hY' : Y' ∈ m) :
    ParEq (P := P) l m ↔
      cross ax (toV ax.O Y - toV ax.O X) (toV ax.O Y' - toV ax.O X') = 0 := by
  obtain ⟨l0, hO, hl0⟩ := exists_par0 ax l
  obtain ⟨m0, hO', hm0⟩ := exists_par0 ax m
  have hd := (mem_line_iff_sub hO hl0 hX Y).1 hY
  have hd0 : toV ax.O Y - toV ax.O X ≠ 0 := fun h => hXY (sub_eq_zero.1 h).symm
  have he := (mem_line_iff_sub hO' hm0 hX' Y').1 hY'
  have he0 : toV ax.O Y' - toV ax.O X' ≠ 0 := fun h => hXY' (sub_eq_zero.1 h).symm
  rw [← mem_lineSub_iff_cross ax hO hd hd0]
  constructor
  · intro h
    have e : l0 = m0 := eq_of_parEq (parEq_trans (parEq_trans (parEq_symm hl0) h) hm0) hO hO'
    subst e; exact he
  · intro h
    have e : l0 = m0 := line_unique (ofV_ne_O ax he0).symm hO h hO' he
    subst e
    exact parEq_trans hl0 (parEq_symm hm0)

end Coords

/-! ### Pascal's theorem as a computation -/

section Algebra

variable {K : Type*} [Field K]

/-- A point on the line through `q` with direction `u` is `q + t u`. -/
theorem on_line_param {u1 u2 w1 w2 p1 p2 : K} (hD : cr u1 u2 w1 w2 ≠ 0)
    (h : cr u1 u2 p1 p2 = 0) : ∃ t : K, p1 = t * u1 ∧ p2 = t * u2 := by
  refine ⟨cr p1 p2 w1 w2 / cr u1 u2 w1 w2, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hD]
    unfold cr at *
    linear_combination w1 * h
  · rw [div_mul_eq_mul_div, eq_div_iff hD]
    unfold cr at *
    linear_combination w2 * h

theorem on_line_param' {u1 u2 w1 w2 p1 p2 : K} (hD : cr u1 u2 w1 w2 ≠ 0)
    (h : cr w1 w2 p1 p2 = 0) : ∃ t : K, p1 = t * w1 ∧ p2 = t * w2 := by
  refine ⟨cr u1 u2 p1 p2 / cr u1 u2 w1 w2, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, eq_div_iff hD]
    unfold cr at *
    linear_combination (-u1) * h
  · rw [div_mul_eq_mul_div, eq_div_iff hD]
    unfold cr at *
    linear_combination (-u2) * h

/-- **Pascal's theorem in co-ordinates.** The points are given by their co-ordinates relative to
the intersection `Q` of the two lines: `A`, `B`, `C` are multiples of `u`, `A'`, `B'`, `C'` of
`w`, with `u`, `w` independent. -/
theorem pascal_alg {u1 u2 w1 w2 a b c a' b' c' : K} (hD : cr u1 u2 w1 w2 ≠ 0)
    (h1 : cr (b' * w1 - c * u1) (b' * w2 - c * u2) (c' * w1 - b * u1) (c' * w2 - b * u2) = 0)
    (h2 : cr (a' * w1 - c * u1) (a' * w2 - c * u2) (c' * w1 - a * u1) (c' * w2 - a * u2) = 0) :
    cr (a' * w1 - b * u1) (a' * w2 - b * u2) (b' * w1 - a * u1) (b' * w2 - a * u2) = 0 := by
  have e1 : (b * b' - c * c') * cr u1 u2 w1 w2 = 0 := by
    unfold cr at *; linear_combination h1
  have e2 : (a * a' - c * c') * cr u1 u2 w1 w2 = 0 := by
    unfold cr at *; linear_combination h2
  have f1 := (mul_eq_zero.1 e1).resolve_right hD
  have f2 := (mul_eq_zero.1 e2).resolve_right hD
  unfold cr at *
  linear_combination (u1 * w2 - u2 * w1) * (f2 - f1)

end Algebra


section PascalThm

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- **Pascal's theorem** (Theorem 21) for a plane geometry with I 1–2, II, III, IV. -/
theorem pascal {g h : L} {Q A B C A' B' C' : P} (hgh : g ≠ h) (hQg : Q ∈ g) (hQh : Q ∈ h)
    (hA : A ∈ g) (hB : B ∈ g) (hC : C ∈ g) (hA' : A' ∈ h) (hB' : B' ∈ h) (hC' : C' ∈ h)
    (hAQ : A ≠ Q) (hBQ : B ≠ Q) (hCQ : C ≠ Q) (hA'Q : A' ≠ Q) (hB'Q : B' ≠ Q) (hC'Q : C' ≠ Q)
    (hAB : A ≠ B) {l l' m m' n n' : L} (hl : C ∈ l ∧ B' ∈ l) (hl' : B ∈ l' ∧ C' ∈ l')
    (hm : C ∈ m ∧ A' ∈ m) (hm' : A ∈ m' ∧ C' ∈ m') (hn : B ∈ n ∧ A' ∈ n)
    (hn' : A ∈ n' ∧ B' ∈ n') (h1 : ¬Meets (Point := P) l l') (h2 : ¬Meets (Point := P) m m') :
    ¬Meets (Point := P) n n' := by
  obtain ⟨ax, hO, -⟩ := exists_axes (L := L) (Ne.symm hAQ)
  subst hO
  -- points of `g` and `h` other than `Q` are distinct
  have gh : ∀ {X Y : P}, X ∈ g → Y ∈ h → X ≠ ax.O → X ≠ Y := by
    intro X Y hX hY hXQ e
    subst e
    exact hXQ (eq_of_mem_of_mem hgh hX hY hQg hQh)
  have z : toV ax.O ax.O = (0 : V ax) := (vzero_def (L := L) ax.O).symm
  have cg : ∀ Z : P, Z ∈ g ↔ cross ax (toV ax.O A) (toV ax.O Z) = 0 := by
    intro Z; rw [mem_line_iff_cross ax (Ne.symm hAQ) hQg hA Z, z, sub_zero, sub_zero]
  have ch : ∀ Z : P, Z ∈ h ↔ cross ax (toV ax.O A') (toV ax.O Z) = 0 := by
    intro Z; rw [mem_line_iff_cross ax (Ne.symm hA'Q) hQh hA' Z, z, sub_zero, sub_zero]
  have hD : cr (xc ax (toV ax.O A)) (yc ax (toV ax.O A)) (xc ax (toV ax.O A'))
      (yc ax (toV ax.O A')) ≠ 0 := by
    intro e
    have : A' ∈ g := (cg A').2 e
    exact hA'Q (eq_of_mem_of_mem hgh this hA' hQg hQh)
  have pg : ∀ {X : P}, X ∈ g → ∃ t : G ax, xc ax (toV ax.O X) = t * xc ax (toV ax.O A) ∧
      yc ax (toV ax.O X) = t * yc ax (toV ax.O A) := fun hX => on_line_param hD ((cg _).1 hX)
  have ph : ∀ {X : P}, X ∈ h → ∃ t : G ax, xc ax (toV ax.O X) = t * xc ax (toV ax.O A') ∧
      yc ax (toV ax.O X) = t * yc ax (toV ax.O A') := fun hX => on_line_param' hD ((ch _).1 hX)
  obtain ⟨b, xb, yb⟩ := pg hB
  obtain ⟨c, xcC, ycC⟩ := pg hC
  obtain ⟨b', xb', yb'⟩ := ph hB'
  obtain ⟨c', xc', yc'⟩ := ph hC'
  have par : ∀ {X Y X' Y' : P} {k k' : L}, X ≠ Y → X' ≠ Y' → X ∈ k → Y ∈ k → X' ∈ k' → Y' ∈ k' →
      (ParEq (P := P) k k' ↔ cr (xc ax (toV ax.O Y) - xc ax (toV ax.O X))
        (yc ax (toV ax.O Y) - yc ax (toV ax.O X)) (xc ax (toV ax.O Y') - xc ax (toV ax.O X'))
        (yc ax (toV ax.O Y') - yc ax (toV ax.O X')) = 0) := by
    intro X Y X' Y' k k' hXY hXY' hX hY hX' hY'
    rw [parEq_iff_cross ax hXY hXY' hX hY hX' hY', cross, xc_sub, xc_sub, yc_sub, yc_sub]
  have e1 := (par (gh hC hB' hCQ) (gh hB hC' hBQ) hl.1 hl.2 hl'.1 hl'.2).1 (Or.inr h1)
  have e2 := (par (gh hC hA' hCQ) (gh hA hC' hAQ) hm.1 hm.2 hm'.1 hm'.2).1 (Or.inr h2)
  have e1' : cr (b' * xc ax (toV ax.O A') - c * xc ax (toV ax.O A))
      (b' * yc ax (toV ax.O A') - c * yc ax (toV ax.O A))
      (c' * xc ax (toV ax.O A') - b * xc ax (toV ax.O A))
      (c' * yc ax (toV ax.O A') - b * yc ax (toV ax.O A)) = 0 := by
    rw [← xb', ← yb', ← xcC, ← ycC, ← xc', ← yc', ← xb, ← yb]; exact e1
  have e2' : cr ((1 : G ax) * xc ax (toV ax.O A') - c * xc ax (toV ax.O A))
      (1 * yc ax (toV ax.O A') - c * yc ax (toV ax.O A))
      (c' * xc ax (toV ax.O A') - 1 * xc ax (toV ax.O A))
      (c' * yc ax (toV ax.O A') - 1 * yc ax (toV ax.O A)) = 0 := by
    rw [one_mul, one_mul, one_mul, one_mul, ← xcC, ← ycC, ← xc', ← yc']; exact e2
  have e3 := pascal_alg hD e1' e2'
  rw [one_mul, one_mul, one_mul, one_mul, ← xb, ← yb, ← xb', ← yb'] at e3
  have hpar : ParEq (P := P) n n' :=
    (par (gh hB hA' hBQ) (gh hA hB' hAQ) hn.1 hn.2 hn'.1 hn'.2).2 e3
  rcases hpar with e | e
  · exfalso
    subst e
    have hng : n = g := line_unique hAB hn'.1 hn.1 hA hB
    rw [hng] at hn
    exact hA'Q (eq_of_mem_of_mem hgh hn.2 hA' hQg hQh)
  · exact e

end PascalThm

end Pas

end HilbertFoundations
