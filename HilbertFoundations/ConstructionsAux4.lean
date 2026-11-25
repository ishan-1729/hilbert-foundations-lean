import HilbertFoundations.ConstructionsAux3

/-!
# Helper module for `Constructions.lean`: Theorem 41 in the coordinate plane

This module contains no unit of Hilbert's text. Over an ordered field `K` (no square roots are
assumed), in the coordinate plane `Coord K 2`:

* `PythClosure B`: Hilbert's domain `Ω(R)`, the numbers obtained from the numbers of `B` by the
  four operations of arithmetic and the extraction of the square root of a sum of two squares;
* `rt_closed`: the coordinates of the points constructible by straight-edge and transferer
  (multiplied by a fixed factor `λ ≠ 0`) lie in every set closed under the five operations that
  contains those of the given points;
* `theorem41_coord`: if the given points contain the frame `(0,0)`, `(1,0)`, `(0,1)`, the
  constructible points are exactly those with coordinates in `Ω(R)`;
* `theorem41_needs_frame`: without the frame the converse fails (over `ℝ`);
* `rt_frame_iff_omega`: over `ℝ`, the points constructible from the frame are the points with
  coordinates in Hilbert's field `Ω`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

/-- **Hilbert's domain `Ω(R)`**: the numbers obtained from the numbers of `B` by finitely many
additions, subtractions, multiplications, divisions (by nonzero numbers) and extractions of the
square root of a sum of two squares (the nonnegative `z` with `z² = x² + y²`). -/
inductive PythClosure {K : Type*} [Field K] [LinearOrder K] (B : Set K) : K → Prop
  | base {x : K} : x ∈ B → PythClosure B x
  | add {x y : K} : PythClosure B x → PythClosure B y → PythClosure B (x + y)
  | sub {x y : K} : PythClosure B x → PythClosure B y → PythClosure B (x - y)
  | mul {x y : K} : PythClosure B x → PythClosure B y → PythClosure B (x * y)
  | div {x y : K} : PythClosure B x → PythClosure B y → y ≠ 0 → PythClosure B (x / y)
  | sqrt {x y z : K} : PythClosure B x → PythClosure B y → 0 ≤ z → z ^ 2 = x ^ 2 + y ^ 2 →
      PythClosure B z

/-- A predicate closed under Hilbert's five operations. -/
structure PythClosed {K : Type*} [Field K] [LinearOrder K] (T : K → Prop) : Prop where
  add : ∀ {x y : K}, T x → T y → T (x + y)
  sub : ∀ {x y : K}, T x → T y → T (x - y)
  mul : ∀ {x y : K}, T x → T y → T (x * y)
  div : ∀ {x y : K}, T x → T y → y ≠ 0 → T (x / y)
  sqrt : ∀ {x y z : K}, T x → T y → 0 ≤ z → z ^ 2 = x ^ 2 + y ^ 2 → T z

theorem pythClosure_closed {K : Type*} [Field K] [LinearOrder K] (B : Set K) :
    PythClosed (PythClosure B) :=
  ⟨.add, .sub, .mul, .div, .sqrt⟩

theorem PythClosure.mono {K : Type*} [Field K] [LinearOrder K] {B C : Set K} (h : B ⊆ C) {x : K}
    (hx : PythClosure B x) : PythClosure C x := by
  induction hx with
  | base hb => exact .base (h hb)
  | add _ _ h1 h2 => exact .add h1 h2
  | sub _ _ h1 h2 => exact .sub h1 h2
  | mul _ _ h1 h2 => exact .mul h1 h2
  | div _ _ hy h1 h2 => exact .div h1 h2 hy
  | sqrt _ _ hz hzz h1 h2 => exact .sqrt h1 h2 hz hzz

/-- `Ω(R)` is the smallest set containing `B` and closed under the five operations. -/
theorem PythClosure.le_of_closed {K : Type*} [Field K] [LinearOrder K] {B : Set K}
    {T : K → Prop} (hT : PythClosed T) (hB : ∀ x ∈ B, T x) {x : K} (hx : PythClosure B x) :
    T x := by
  induction hx with
  | base hb => exact hB _ hb
  | add _ _ h1 h2 => exact hT.add h1 h2
  | sub _ _ h1 h2 => exact hT.sub h1 h2
  | mul _ _ h1 h2 => exact hT.mul h1 h2
  | div _ _ hy h1 h2 => exact hT.div h1 h2 hy
  | sqrt _ _ hz hzz h1 h2 => exact hT.sqrt h1 h2 hz hzz

theorem PythClosed.neg {K : Type*} [Field K] [LinearOrder K] {T : K → Prop} (hT : PythClosed T) {x : K} (hx : T x) : T (-x) := by
  have := hT.sub (hT.sub hx hx) hx; simpa using this

theorem PythClosed.abs {K : Type*} [Field K] [LinearOrder K] {T : K → Prop} (hT : PythClosed T) {x : K} (hx : T x) : T |x| := by
  rcases abs_choice x with h | h <;> rw [h]
  · exact hx
  · exact hT.neg hx

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The coordinates of the points of `S`: Hilbert's domain `R` before closing it. -/
def coordSet (S : Set (Coord K 2)) : Set K := {x | ∃ X ∈ S, x = xc X ∨ x = yc X}

/-- The common point of two distinct lines `AB`, `CD`: the directions are independent and the
point is `A + r (B - A)` with `r = ((D - C) × (C - A)) / ((D - C) × (B - A))`. -/
theorem meet_param {A B C D X : Coord K 2} {a b : CoordLine K 2} (hAB : A ≠ B) (hCD : C ≠ D)
    (hAa : A ∈ a) (hBa : B ∈ a) (hCb : C ∈ b) (hDb : D ∈ b) (hab : a ≠ b) (hXa : X ∈ a)
    (hXb : X ∈ b) :
    crossProd2 (D - C) (B - A) ≠ 0 ∧
      X = (crossProd2 (D - C) (C - A) / crossProd2 (D - C) (B - A)) • (B - A) + A := by
  rw [a.eq_through hAB hAa hBa, mem_through] at hXa
  obtain ⟨r, rfl⟩ := hXa
  have hX := (mem_line_iff_cross hCD hCb hDb).1 hXb
  rw [show r • (B - A) + A - C = r • (B - A) - (C - A) by abel, cross_sub_right,
    cross_smul_right] at hX
  have hc : crossProd2 (D - C) (B - A) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, neg_eq_zero] at hX
    apply hab
    have hA : A ∈ b := by
      rw [mem_line_iff_cross hCD hCb hDb, show A - C = -(C - A) by abel]
      simp only [crossProd2_def, xc_neg, yc_neg] at hX ⊢; linear_combination -hX
    have hB : B ∈ b := by
      rw [mem_line_iff_cross hCD hCb hDb, show B - C = (B - A) - (C - A) by abel,
        cross_sub_right, h0, hX, sub_zero]
    exact line_unique hAB hAa hBa hA hB
  refine ⟨hc, ?_⟩
  have hr : r = crossProd2 (D - C) (C - A) / crossProd2 (D - C) (B - A) := by
    rw [eq_div_iff hc]; linear_combination hX
  rw [← hr]

section Forward

variable {S : Set (Coord K 2)} {T : K → Prop} (hT : PythClosed T) {l : K}
include hT

theorem closed_ip {u v : Coord K 2} (hu : T (l * xc u) ∧ T (l * yc u))
    (hv : T (l * xc v) ∧ T (l * yc v)) : T (l ^ 2 * ip u v) := by
  have := hT.add (hT.mul hu.1 hv.1) (hT.mul hu.2 hv.2)
  convert this using 1; rw [ip_two]; ring

theorem closed_cross {u v : Coord K 2} (hu : T (l * xc u) ∧ T (l * yc u))
    (hv : T (l * xc v) ∧ T (l * yc v)) : T (l ^ 2 * crossProd2 u v) := by
  have := hT.sub (hT.mul hu.1 hv.2) (hT.mul hu.2 hv.1)
  convert this using 1; rw [crossProd2_def]; ring

theorem closed_sub {u v : Coord K 2} (hu : T (l * xc u) ∧ T (l * yc u))
    (hv : T (l * xc v) ∧ T (l * yc v)) : T (l * xc (u - v)) ∧ T (l * yc (u - v)) := by
  constructor
  · have := hT.sub hu.1 hv.1; convert this using 1; simp; ring
  · have := hT.sub hu.2 hv.2; convert this using 1; simp; ring

theorem closed_affine {t : K} (ht : T t) {u v : Coord K 2} (hu : T (l * xc u) ∧ T (l * yc u))
    (hv : T (l * xc v) ∧ T (l * yc v)) :
    T (l * xc (t • (u - v) + v)) ∧ T (l * yc (t • (u - v) + v)) := by
  have h := closed_sub hT hu hv
  constructor
  · have := hT.add (hT.mul ht h.1) hv.1; convert this using 1; simp; ring
  · have := hT.add (hT.mul ht h.2) hv.2; convert this using 1; simp; ring

/-- **The coordinates of constructible points** (Hilbert's analysis in § 37): if the coordinates
of the given points, multiplied by `l ≠ 0`, satisfy a predicate `T` closed under the five
operations, so do those of every point constructible by straight-edge and transferer. -/
theorem rt_closed (hl : l ≠ 0) (hS : ∀ X ∈ S, T (l * xc X) ∧ T (l * yc X)) {X : Coord K 2}
    (h : RulerTransferer S X) : T (l * xc X) ∧ T (l * yc X) := by
  induction h with
  | given hA => exact hS _ hA
  | @meet A B C D X a b _ _ _ _ hAB hCD hAa hBa hCb hDb hab hXa hXb iA iB iC iD =>
    obtain ⟨hc, hX⟩ := meet_param hAB hCD hAa hBa hCb hDb hab hXa hXb
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    have hr : T (crossProd2 (D - C) (C - A) / crossProd2 (D - C) (B - A)) := by
      have := hT.div (closed_cross hT (closed_sub hT iD iC) (closed_sub hT iC iA))
        (closed_cross hT (closed_sub hT iD iC) (closed_sub hT iB iA)) (mul_ne_zero hl2 hc)
      convert this using 1; field_simp
    rw [hX]; exact closed_affine hT hr iB iA
  | @layOff A B O Q X a _ _ _ _ hAB hOQ hOa hQa hXa hXO hseg iA iB iO iQ =>
    rw [a.eq_through hOQ hOa hQa, mem_through] at hXa
    obtain ⟨t, rfl⟩ := hXa
    rw [segCong_iff, add_sub_cancel_right, ip_smul_left, ip_smul_right, ← mul_assoc, ← sq]
      at hseg
    set v := Q - O
    set w := B - A
    have hv : v ≠ 0 := ne_zero_of_ne hOQ
    have hNv := ip_self_pos hv
    have hvv : T (l ^ 2 * ip v v) := closed_ip hT (closed_sub hT iQ iO) (closed_sub hT iQ iO)
    have hvw : T (l ^ 2 * ip v w) := closed_ip hT (closed_sub hT iQ iO) (closed_sub hT iB iA)
    have hcw : T (l ^ 2 * crossProd2 v w) :=
      closed_cross hT (closed_sub hT iQ iO) (closed_sub hT iB iA)
    have hl2 : 0 < l ^ 2 := by positivity
    have hz : T (|t| * (l ^ 2 * ip v v)) := by
      refine hT.sqrt hvw hcw (by positivity) ?_
      have L := ip_sq_add_cross_sq v w
      rw [show (|t| * (l ^ 2 * ip v v)) ^ 2 = t ^ 2 * ip v v * ((l ^ 2) ^ 2 * ip v v) by
        rw [mul_pow, sq_abs]; ring, hseg]
      linear_combination (-(l ^ 2) ^ 2) * L
    have hat : T |t| := by
      have := hT.div hz hvv (by positivity)
      convert this using 1; field_simp
    have ht : T t := by
      rcases abs_choice t with h | h
      · rw [h] at hat; exact hat
      · have := hT.neg hat; rw [h, neg_neg] at this; exact this
    exact closed_affine hT ht iQ iO

end Forward

/-- The forward half of Theorem 41: the coordinates of the constructible points lie in `Ω(R)`. -/
theorem rt_coords_mem {S : Set (Coord K 2)} {X : Coord K 2} (h : RulerTransferer S X) :
    PythClosure (coordSet S) (xc X) ∧ PythClosure (coordSet S) (yc X) := by
  have := rt_closed (pythClosure_closed (coordSet S)) one_ne_zero
    (fun X hX => ⟨by rw [one_mul]; exact .base ⟨X, hX, Or.inl rfl⟩,
      by rw [one_mul]; exact .base ⟨X, hX, Or.inr rfl⟩⟩) h
  simpa using this

theorem pt2_ne_left {x y x' y' : K} (h : x ≠ x') : (pt2 x y : Coord K 2) ≠ pt2 x' y' := by
  intro e; exact h (by have := congrArg xc e; simpa using this)

theorem pt2_ne_right {x y x' y' : K} (h : y ≠ y') : (pt2 x y : Coord K 2) ≠ pt2 x' y' := by
  intro e; exact h (by have := congrArg yc e; simpa using this)

section Converse

variable {S : Set (Coord K 2)}
  (hO : (pt2 0 0 : Coord K 2) ∈ S) (hE : (pt2 1 0 : Coord K 2) ∈ S)
  (hE' : (pt2 0 1 : Coord K 2) ∈ S)
include hO hE hE'

/-- From `(x, 0)` to `(0, x)`. -/
theorem rt_rot {x : K} (h : RulerTransferer S (pt2 x 0)) : RulerTransferer S (pt2 0 x) := by
  by_cases hx : x = 0
  · subst hx; exact .given hO
  · have := rt_layOff' (t := x) (.given hO) (.given hE') (.given hO) h
      (pt2_ne_right zero_ne_one) (pt2_ne_left (Ne.symm hx)) hx (by simp [ip_two]; ring)
    convert this using 1; apply ext2 <;> simp

/-- From `(0, x)` to `(x, 0)`. -/
theorem rt_rot' {x : K} (h : RulerTransferer S (pt2 0 x)) : RulerTransferer S (pt2 x 0) := by
  by_cases hx : x = 0
  · subst hx; exact .given hO
  · have := rt_layOff' (t := x) (.given hO) (.given hE) (.given hO) h
      (pt2_ne_left zero_ne_one) (pt2_ne_right (Ne.symm hx)) hx (by simp [ip_two]; ring)
    convert this using 1; apply ext2 <;> simp

/-- The point `(x, y)` from `(x, 0)` and `(y, 0)` (two parallels to the axes). -/
theorem rt_pair {x y : K} (hx : RulerTransferer S (pt2 x 0)) (hy : RulerTransferer S (pt2 y 0)) :
    RulerTransferer S (pt2 x y) := by
  have hy' := rt_rot hO hE hE' hy
  by_cases hx0 : x = 0
  · subst hx0; exact hy'
  by_cases hy0 : y = 0
  · subst hy0; exact hx
  have h1 : RulerTransferer S (pt2 x 2) := by
    have := rt_parallelPt (.given hO) (.given hE') hx (by simp [crossProd2_def, hx0])
    convert this using 1; apply ext2 <;> simp
  have h2 : RulerTransferer S (pt2 2 y) := by
    have := rt_parallelPt (.given hO) (.given hE) hy' (by simp [crossProd2_def, hy0])
    convert this using 1; apply ext2 <;> simp
  refine rt_inter' hx h1 hy' h2 (pt2_ne_right (by norm_num)) (pt2_ne_left (by norm_num))
    (by norm_num [crossProd2_def]) (by norm_num [crossProd2_def]) (by norm_num [crossProd2_def])

/-- The projections of a constructible point to the axis. -/
theorem rt_proj {X : Coord K 2} (h : RulerTransferer S X) :
    RulerTransferer S (pt2 (xc X) 0) ∧ RulerTransferer S (pt2 (yc X) 0) := by
  constructor
  · by_cases hx : xc X = 0
    · rw [hx]; exact .given hO
    have h1 := rt_parallelPt (.given hO) (.given hE') h (by simp [crossProd2_def, hx])
    refine rt_inter' (.given hO) (.given hE) h h1 (pt2_ne_left zero_ne_one) ?_ ?_ ?_ ?_
    · intro e; have := congrArg yc (congrArg (· - X) e); simp at this
    · simp [crossProd2_def]
    · simp [crossProd2_def]
    · simp [crossProd2_def]
  · apply rt_rot' hO hE hE'
    by_cases hy : yc X = 0
    · rw [hy]; exact .given hO
    have h1 := rt_parallelPt (.given hO) (.given hE) h (by simp [crossProd2_def, hy])
    refine rt_inter' (.given hO) (.given hE') h h1 (pt2_ne_right zero_ne_one) ?_ ?_ ?_ ?_
    · intro e; have := congrArg xc (congrArg (· - X) e); simp at this
    · simp [crossProd2_def]
    · simp [crossProd2_def]
    · simp [crossProd2_def]

theorem rt_axis_addsub {x y c : K} (hx : RulerTransferer S (pt2 x 0))
    (hy : RulerTransferer S (pt2 y 0)) (hc : c = 1 ∨ c = -1) :
    RulerTransferer S (pt2 (x + c * y) 0) := by
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx
  have hQ : ∃ Q : Coord K 2, RulerTransferer S Q ∧ yc Q = 0 ∧ Q ≠ pt2 x 0 := by
    by_cases hx0 : x = 0
    · exact ⟨pt2 1 0, .given hE, by simp, by subst hx0; exact pt2_ne_left one_ne_zero⟩
    · exact ⟨pt2 0 0, .given hO, by simp, pt2_ne_left (Ne.symm hx0)⟩
  obtain ⟨Q, hQ, hQy, hQx⟩ := hQ
  have hc0 : c * y ≠ 0 := by rcases hc with rfl | rfl <;> simpa using hy0
  refine RulerTransferer.layOff (.given hO) hy hx hQ (pt2_ne_left (Ne.symm hy0)) hQx.symm
    (a := xAxis) (mem_xAxis.2 (by simp)) (mem_xAxis.2 hQy) (mem_xAxis.2 (by simp))
    (pt2_ne_left (by simpa using hc0)) ?_
  rw [segCong_iff]
  rcases hc with rfl | rfl <;> simp [ip_two]

theorem rt_axis_mul {x y : K} (hx : RulerTransferer S (pt2 x 0))
    (hy : RulerTransferer S (pt2 y 0)) : RulerTransferer S (pt2 (x * y) 0) := by
  by_cases hx0 : x = 0
  · subst hx0; simpa using hx
  by_cases hy0 : y = 0
  · subst hy0; simpa using hy
  by_cases hx1 : x = 1
  · subst hx1; simpa using hy
  have hQ := rt_rot hO hE hE' hy
  have hR := rt_parallelPt (.given hE) hQ hx (by
    simp [crossProd2_def]; exact ⟨hy0, sub_ne_zero.2 hx1⟩)
  apply rt_rot' hO hE hE'
  refine rt_inter' hx hR (.given hO) (.given hE') ?_ (pt2_ne_right zero_ne_one) ?_ ?_ ?_
  · intro e
    have := congrArg xc (congrArg (· - pt2 x 0) e); simp at this
  · simp [crossProd2_def]
  · simp [crossProd2_def]; ring
  · simp [crossProd2_def]

theorem rt_axis_inv {y : K} (hy : RulerTransferer S (pt2 y 0)) (hy0 : y ≠ 0) :
    RulerTransferer S (pt2 y⁻¹ 0) := by
  by_cases hy1 : y = 1
  · subst hy1; simpa using RulerTransferer.given (S := S) hE
  have hR := rt_parallelPt hy (.given hE') (.given hE) (by
    simp [crossProd2_def]; exact sub_ne_zero.2 hy1)
  apply rt_rot' hO hE hE'
  refine rt_inter' (.given hE) hR (.given hO) (.given hE') ?_ (pt2_ne_right zero_ne_one)
    ?_ ?_ ?_
  · intro e
    have := congrArg yc (congrArg (· - pt2 1 0) e); simp at this
  · simp [crossProd2_def]; exact hy0
  · simp [crossProd2_def]; field_simp; ring
  · simp [crossProd2_def]

theorem rt_axis_sqrt {x y z : K} (hx : RulerTransferer S (pt2 x 0))
    (hy : RulerTransferer S (pt2 y 0)) (hz : 0 ≤ z) (hzz : z ^ 2 = x ^ 2 + y ^ 2) :
    RulerTransferer S (pt2 z 0) := by
  by_cases hz0 : z = 0
  · subst hz0; exact .given hO
  have hP := rt_pair hO hE hE' hx hy
  have hPO : (pt2 0 0 : Coord K 2) ≠ pt2 x y := by
    intro e
    have h1 : x = 0 := by have := congrArg xc e; simpa using this.symm
    have h2 : y = 0 := by have := congrArg yc e; simpa using this.symm
    rw [h1, h2] at hzz; exact hz0 (by simpa using hzz)
  have := rt_layOff' (t := z) (.given hO) (.given hE) (.given hO) hP (pt2_ne_left zero_ne_one)
    hPO hz0 (by simp [ip_two]; linear_combination hzz)
  convert this using 1; apply ext2 <;> simp

/-- The numbers `x` with `(x, 0)` constructible are closed under the five operations. -/
theorem rt_axis_closed : PythClosed (fun x : K => RulerTransferer S (pt2 x 0)) where
  add hx hy := by simpa using rt_axis_addsub hO hE hE' hx hy (c := 1) (Or.inl rfl)
  sub hx hy := by
    have := rt_axis_addsub hO hE hE' hx hy (c := -1) (Or.inr rfl)
    rwa [neg_one_mul, ← sub_eq_add_neg] at this
  mul hx hy := rt_axis_mul hO hE hE' hx hy
  div hx hy hy0 := by
    rw [div_eq_mul_inv]; exact rt_axis_mul hO hE hE' hx (rt_axis_inv hO hE hE' hy hy0)
  sqrt hx hy hz hzz := rt_axis_sqrt hO hE hE' hx hy hz hzz

/-- **Theorem 41 in the coordinate plane** (over any ordered field): when the given points
contain the frame `(0,0)`, `(1,0)`, `(0,1)`, a point is constructible by straight-edge and
transferer iff its coordinates lie in `Ω(R)`, `R` the coordinates of the given points. -/
theorem theorem41_coord {X : Coord K 2} :
    RulerTransferer S X ↔
      PythClosure (coordSet S) (xc X) ∧ PythClosure (coordSet S) (yc X) := by
  refine ⟨rt_coords_mem, fun ⟨hx, hy⟩ => ?_⟩
  have hB : ∀ x ∈ coordSet S, RulerTransferer S (pt2 x 0) := by
    rintro x ⟨Y, hY, rfl | rfl⟩
    · exact (rt_proj hO hE hE' (.given hY)).1
    · exact (rt_proj hO hE hE' (.given hY)).2
  have h1 := PythClosure.le_of_closed (rt_axis_closed hO hE hE') hB hx
  have h2 := PythClosure.le_of_closed (rt_axis_closed hO hE hE') hB hy
  rw [eta2 X]; exact rt_pair hO hE hE' h1 h2

end Converse

end Coord

end HilbertFoundations
