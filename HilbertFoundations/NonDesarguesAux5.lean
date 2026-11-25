import HilbertFoundations.Analytic

/-!
# Hilbert's ellipse and the circles through `F` (helper for `NonDesargues.lean`, § 23)

Hilbert's construction in § 23 uses the ellipse `x² + 4y² = 1` (semi-axes `1` and `1/2`) and the
point `F = (3/2, 0)`, and needs that *no circle meets the ellipse in four real points and passes
through `F`*; in particular a circle through `F` and two points of the ellipse has no further point
in common with it. Here this is proved by an algebraic argument (not Hilbert's variational one):

* the points of the ellipse are `(cos θ, sin θ / 2)` (eccentric angle `θ`);
* for any `θ₁, θ₂, θ₃` and `θ₄ = -(θ₁ + θ₂ + θ₃)` the circle `circleStar θ₁ θ₂ θ₃`
  (coefficients `cD`, `cE`, `cG`) passes through the four points of eccentric angles `θ₁, …, θ₄`
  (Joachimsthal: four concyclic points of an ellipse have eccentric angles summing to `0`
  mod `2π`), and every circle through three distinct points of the ellipse is of this form;
* the power of `F` with respect to `circleStar θ₁ θ₂ θ₃` is `(3/4) g + 1/2` with
  `g = XY - (3/2) c (X + Y) + c² + 1 ≥ 0`, where `c = cos ((θ₁+θ₂)/2)`, `X = cos ((θ₁-θ₂)/2)`,
  `Y = cos ((θ₃-θ₄)/2)`; hence it is never `0`.
-/

namespace HilbertFoundations

namespace HilbertEllipse

open Real

/-- Hilbert's ellipse, with semi-axes `1` and `1/2` about the origin. -/
def OnEllipse (x y : ℝ) : Prop := x ^ 2 + 4 * y ^ 2 = 1

/-- The circle `x² + y² + D x + E y + G = 0` (every circle has such an equation). -/
def OnCircle (D E G x y : ℝ) : Prop := x ^ 2 + y ^ 2 + D * x + E * y + G = 0

/-! ### The symmetric doubly tangent circles -/

/-- **The circle symmetric to the `y`-axis and tangent to the ellipse at `(a, b)`** (`a ≠ 0`): its
centre `(0, k)` lies on the normal of the ellipse at `(a, b)` iff `k = -3b`, and it meets the
positive `x`-axis at `x = √(1 + 3b²)`. -/
theorem tangent_circle {a b : ℝ} (hE : OnEllipse a b) (ha : a ≠ 0) :
    (∀ k : ℝ, a * (4 * b) - (b - k) * a = 0 ↔ k = -3 * b) ∧
    ∀ x : ℝ, 0 < x →
      (x ^ 2 + (0 - -3 * b) ^ 2 = a ^ 2 + (b - -3 * b) ^ 2 ↔ x = √(1 + 3 * b ^ 2)) := by
  unfold OnEllipse at hE
  refine ⟨fun k => ⟨fun h => ?_, fun h => by subst h; ring⟩, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : a * (k + 3 * b) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact (ha h1).elim
    · linarith
  · have hx2 : x ^ 2 = 1 + 3 * b ^ 2 := by nlinarith
    rw [← hx2, Real.sqrt_sq hx.le]
  · have : x ^ 2 = 1 + 3 * b ^ 2 := by rw [h, Real.sq_sqrt (by positivity)]
    nlinarith

/-- **The greatest intercept** is `√7 / 2`, attained for `b = 1/2`, and `F` lies beyond it. -/
theorem max_intercept :
    (∀ a b : ℝ, OnEllipse a b → √(1 + 3 * b ^ 2) ≤ √7 / 2) ∧
    OnEllipse 0 (1 / 2) ∧ √(1 + 3 * (1 / 2) ^ 2) = √7 / 2 ∧ √7 / 2 < 3 / 2 := by
  have h7 : √7 / 2 = √(7 / 4) := by
    rw [Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨fun a b hE => ?_, by norm_num [OnEllipse], by rw [h7]; norm_num, ?_⟩
  · unfold OnEllipse at hE
    rw [h7]; apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg a]
  · rw [h7, show (3 : ℝ) / 2 = √(9 / 4) by
      rw [Real.sqrt_div (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-! ### The circle through four points of given eccentric angles -/

/-- `D`-coefficient of the circle through the points of eccentric angles `θ₁, θ₂, θ₃` and
`θ₄ = -(θ₁+θ₂+θ₃)`. -/
noncomputable def cD (t1 t2 t3 : ℝ) : ℝ :=
  -(3 / 8) * (cos t1 + cos t2 + cos t3 + cos (-(t1 + t2 + t3)))

/-- `E`-coefficient. -/
noncomputable def cE (t1 t2 t3 : ℝ) : ℝ :=
  (3 / 4) * (sin t1 + sin t2 + sin t3 + sin (-(t1 + t2 + t3)))

/-- `G`-coefficient. -/
noncomputable def cG (t1 t2 t3 : ℝ) : ℝ :=
  (3 / 16) * (cos (t1 + t2) + cos (t1 + t3) + cos (t1 + -(t1 + t2 + t3)) + cos (t2 + t3) +
    cos (t2 + -(t1 + t2 + t3)) + cos (t3 + -(t1 + t2 + t3))) - 5 / 8

theorem cos_mul_cos' (a b : ℝ) : cos a * cos b = (cos (a + b) + cos (a - b)) / 2 := by
  rw [cos_add, cos_sub]; ring

theorem sin_mul_sin' (a b : ℝ) : sin a * sin b = (cos (a - b) - cos (a + b)) / 2 := by
  rw [cos_add, cos_sub]; ring

/-- The power of the point `(cos θ, sin θ / 2)` of the ellipse with respect to `circleStar`. -/
theorem circleStar_eval (t1 t2 t3 t : ℝ) :
    cos t ^ 2 + (sin t / 2) ^ 2 + cD t1 t2 t3 * cos t + cE t1 t2 t3 * (sin t / 2) + cG t1 t2 t3 =
      (3 / 8) * cos (t + t) - (3 / 8) * (cos (t1 + t) + cos (t2 + t) + cos (t3 + t) +
        cos (-(t1 + t2 + t3) + t)) +
      (3 / 16) * (cos (t1 + t2) + cos (t1 + t3) + cos (t1 + -(t1 + t2 + t3)) + cos (t2 + t3) +
        cos (t2 + -(t1 + t2 + t3)) + cos (t3 + -(t1 + t2 + t3))) := by
  have hc2 : cos t ^ 2 = (1 + cos (t + t)) / 2 := by rw [← two_mul, cos_sq t]; ring_nf
  have hs2 : sin t ^ 2 = (1 - cos (t + t)) / 2 := by
    rw [← two_mul, sin_sq, cos_sq t]; ring_nf
  simp only [cD, cE, cG]
  have e1 := cos_mul_cos' t1 t; have e2 := cos_mul_cos' t2 t; have e3 := cos_mul_cos' t3 t
  have e4 := cos_mul_cos' (-(t1 + t2 + t3)) t
  have f1 := sin_mul_sin' t1 t; have f2 := sin_mul_sin' t2 t; have f3 := sin_mul_sin' t3 t
  have f4 := sin_mul_sin' (-(t1 + t2 + t3)) t
  have : (sin t / 2) ^ 2 = sin t ^ 2 / 4 := by ring
  rw [this, hc2, hs2]
  linear_combination (-(3 / 8)) * (e1 + e2 + e3 + e4) + (3 / 8) * (f1 + f2 + f3 + f4)

/-- `circleStar θ₁ θ₂ θ₃` passes through the point of eccentric angle `θ₁` (and, by symmetry, of
`θ₂`, `θ₃`, `θ₄`). -/
theorem circleStar_mem_left (t1 t2 t3 : ℝ) :
    OnCircle (cD t1 t2 t3) (cE t1 t2 t3) (cG t1 t2 t3) (cos t1) (sin t1 / 2) := by
  unfold OnCircle
  rw [circleStar_eval]
  have h1 : cos (t2 + t3) = cos (t1 + -(t1 + t2 + t3)) := by
    rw [show t1 + -(t1 + t2 + t3) = -(t2 + t3) by ring, cos_neg]
  have h2 : cos (t2 + -(t1 + t2 + t3)) = cos (t1 + t3) := by
    rw [show t2 + -(t1 + t2 + t3) = -(t1 + t3) by ring, cos_neg]
  have h3 : cos (t3 + -(t1 + t2 + t3)) = cos (t1 + t2) := by
    rw [show t3 + -(t1 + t2 + t3) = -(t1 + t2) by ring, cos_neg]
  rw [h1, h2, h3, add_comm t2 t1, add_comm t3 t1, add_comm (-(t1 + t2 + t3)) t1]
  ring

theorem cD_perm12 (t1 t2 t3 : ℝ) : cD t2 t1 t3 = cD t1 t2 t3 := by
  simp only [cD]; rw [show t2 + t1 + t3 = t1 + t2 + t3 by ring]; ring

theorem cE_perm12 (t1 t2 t3 : ℝ) : cE t2 t1 t3 = cE t1 t2 t3 := by
  simp only [cE]; rw [show t2 + t1 + t3 = t1 + t2 + t3 by ring]; ring

theorem cG_perm12 (t1 t2 t3 : ℝ) : cG t2 t1 t3 = cG t1 t2 t3 := by
  simp only [cG]; rw [show t2 + t1 + t3 = t1 + t2 + t3 by ring, add_comm t2 t1]; ring

theorem cD_perm13 (t1 t2 t3 : ℝ) : cD t3 t2 t1 = cD t1 t2 t3 := by
  simp only [cD]; rw [show t3 + t2 + t1 = t1 + t2 + t3 by ring]; ring

theorem cE_perm13 (t1 t2 t3 : ℝ) : cE t3 t2 t1 = cE t1 t2 t3 := by
  simp only [cE]; rw [show t3 + t2 + t1 = t1 + t2 + t3 by ring]; ring

theorem cG_perm13 (t1 t2 t3 : ℝ) : cG t3 t2 t1 = cG t1 t2 t3 := by
  simp only [cG]; rw [show t3 + t2 + t1 = t1 + t2 + t3 by ring, add_comm t3 t2, add_comm t3 t1,
    add_comm t2 t1]; ring

/-- `circleStar θ₁ θ₂ θ₃` passes through the three points of eccentric angles `θ₁, θ₂, θ₃`. -/
theorem circleStar_mem (t1 t2 t3 : ℝ) :
    OnCircle (cD t1 t2 t3) (cE t1 t2 t3) (cG t1 t2 t3) (cos t1) (sin t1 / 2) ∧
    OnCircle (cD t1 t2 t3) (cE t1 t2 t3) (cG t1 t2 t3) (cos t2) (sin t2 / 2) ∧
    OnCircle (cD t1 t2 t3) (cE t1 t2 t3) (cG t1 t2 t3) (cos t3) (sin t3 / 2) := by
  refine ⟨circleStar_mem_left t1 t2 t3, ?_, ?_⟩
  · have := circleStar_mem_left t2 t1 t3
    rwa [cD_perm12, cE_perm12, cG_perm12] at this
  · have := circleStar_mem_left t3 t2 t1
    rwa [cD_perm13, cE_perm13, cG_perm13] at this

/-! ### The power of `F` -/

/-- The key inequality: `XY - (3/2) c (X+Y) + c² + 1 ≥ 0` for `X, Y, c ∈ [-1, 1]`. -/
theorem key_ineq {X Y c : ℝ} (hX : -1 ≤ X ∧ X ≤ 1) (hY : -1 ≤ Y ∧ Y ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1) :
    0 ≤ X * Y - 3 / 2 * c * (X + Y) + c ^ 2 + 1 := by
  have e : X * Y - 3 / 2 * c * (X + Y) + c ^ 2 + 1 =
      ((1 + X) * (1 + Y) * ((1 - c) * (2 - c)) + (1 - X) * (1 - Y) * ((1 + c) * (2 + c)) +
        ((1 + X) * (1 - Y) + (1 - X) * (1 + Y)) * c ^ 2) / 4 := by ring
  rw [e]
  have h1 : 0 ≤ (1 + X) * (1 + Y) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (1 - X) * (1 - Y) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (1 + X) * (1 - Y) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (1 - X) * (1 + Y) := mul_nonneg (by linarith) (by linarith)
  have h5 : 0 ≤ (1 - c) * (2 - c) := mul_nonneg (by linarith) (by linarith)
  have h6 : 0 ≤ (1 + c) * (2 + c) := mul_nonneg (by linarith) (by linarith)
  positivity

/-- **The power of `F = (3/2, 0)` with respect to `circleStar θ₁ θ₂ θ₃` is positive**: no circle
meeting the ellipse in the four points of eccentric angles `θ₁, θ₂, θ₃, -(θ₁+θ₂+θ₃)` passes
through `F`. -/
theorem power_F_pos (t1 t2 t3 : ℝ) :
    0 < (3 / 2) ^ 2 + 0 ^ 2 + cD t1 t2 t3 * (3 / 2) + cE t1 t2 t3 * 0 + cG t1 t2 t3 := by
  set a := (t1 + t2) / 2
  set d1 := (t1 - t2) / 2
  set d2 := t3 + (t1 + t2) / 2
  have e1 : t1 = a + d1 := by simp only [a, d1]; ring
  have e2 : t2 = a - d1 := by simp only [a, d1]; ring
  have e3 : t3 = -a + d2 := by simp only [a, d2]; ring
  have e4 : -(t1 + t2 + t3) = -a - d2 := by simp only [a, d2]; ring
  have hS : cos t1 + cos t2 + cos t3 + cos (-(t1 + t2 + t3)) =
      2 * cos a * (cos d1 + cos d2) := by
    rw [e4, e1, e2, e3, cos_add, cos_sub, cos_add, cos_sub, cos_neg, sin_neg]; ring
  have hP : cos (t1 + t2) + cos (t1 + t3) + cos (t1 + -(t1 + t2 + t3)) + cos (t2 + t3) +
      cos (t2 + -(t1 + t2 + t3)) + cos (t3 + -(t1 + t2 + t3)) =
      2 * (2 * cos a ^ 2 - 1 + 2 * cos d1 * cos d2) := by
    rw [e4, e1, e2, e3]
    rw [show a + d1 + (a - d1) = 2 * a by ring, show a + d1 + (-a + d2) = d1 + d2 by ring,
      show a + d1 + (-a - d2) = d1 - d2 by ring, show a - d1 + (-a + d2) = -(d1 - d2) by ring,
      show a - d1 + (-a - d2) = -(d1 + d2) by ring, show -a + d2 + (-a - d2) = -(2 * a) by ring,
      cos_neg, cos_neg, cos_neg, cos_two_mul, cos_add, cos_sub]
    ring
  simp only [cD, cE, cG]
  rw [hS, hP]
  have := key_ineq ⟨neg_one_le_cos d1, cos_le_one d1⟩ ⟨neg_one_le_cos d2, cos_le_one d2⟩
    ⟨neg_one_le_cos a, cos_le_one a⟩
  nlinarith

/-! ### Every circle through three distinct points of the ellipse is a `circleStar` -/

/-- A line meets the unit circle in at most two points. -/
theorem line_circle {a b c x1 y1 x2 y2 x3 y3 : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (h1 : x1 ^ 2 + y1 ^ 2 = 1) (h2 : x2 ^ 2 + y2 ^ 2 = 1) (h3 : x3 ^ 2 + y3 ^ 2 = 1)
    (l1 : a * x1 + b * y1 + c = 0) (l2 : a * x2 + b * y2 + c = 0) (l3 : a * x3 + b * y3 + c = 0) :
    (x1 = x2 ∧ y1 = y2) ∨ (x1 = x3 ∧ y1 = y3) ∨ (x2 = x3 ∧ y2 = y3) := by
  have hN : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  -- the coordinate `T = -b x + a y` along the line determines the point, and `T² = N - c²`
  have hx : ∀ x y : ℝ, a * x + b * y + c = 0 →
      (a ^ 2 + b ^ 2) * x = -c * a - b * (-b * x + a * y) := by
    intro x y h; linear_combination a * h
  have hy : ∀ x y : ℝ, a * x + b * y + c = 0 →
      (a ^ 2 + b ^ 2) * y = -c * b + a * (-b * x + a * y) := by
    intro x y h; linear_combination b * h
  have hT : ∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 → a * x + b * y + c = 0 →
      (-b * x + a * y) ^ 2 = a ^ 2 + b ^ 2 - c ^ 2 := by
    intro x y h l
    have : a * x + b * y = -c := by linarith
    have e : (-b * x + a * y) ^ 2 = (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - (a * x + b * y) ^ 2 := by
      ring
    rw [e, h, this]; ring
  have hpt : ∀ x y x' y' : ℝ, a * x + b * y + c = 0 → a * x' + b * y' + c = 0 →
      -b * x + a * y = -b * x' + a * y' → x = x' ∧ y = y' := by
    intro x y x' y' l l' hTT
    have ex := hx x y l; have ex' := hx x' y' l'
    have ey := hy x y l; have ey' := hy x' y' l'
    rw [hTT] at ex ey
    constructor
    · have : (a ^ 2 + b ^ 2) * (x - x') = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    · have : (a ^ 2 + b ^ 2) * (y - y') = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
  have t1 := hT x1 y1 h1 l1
  have t2 := hT x2 y2 h2 l2
  have t3 := hT x3 y3 h3 l3
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (t1.trans t2.symm) with h | h
  · exact Or.inl (hpt _ _ _ _ l1 l2 h)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (t1.trans t3.symm) with h' | h'
  · exact Or.inr (Or.inl (hpt _ _ _ _ l1 l3 h'))
  · exact Or.inr (Or.inr (hpt _ _ _ _ l2 l3 (by linarith)))

/-- **Eccentric angle**: every point of the ellipse is `(cos θ, sin θ / 2)`. -/
theorem ellipse_param {x y : ℝ} (h : OnEllipse x y) : ∃ θ : ℝ, x = cos θ ∧ y = sin θ / 2 := by
  unfold OnEllipse at h
  have hx1 : -1 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  have hx2 : x ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  have hs : √(1 - x ^ 2) = 2 * |y| := by
    rw [show 1 - x ^ 2 = (2 * |y|) ^ 2 by rw [mul_pow, sq_abs]; linarith]
    exact Real.sqrt_sq (by positivity)
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨arccos x, (cos_arccos hx1 hx2).symm, ?_⟩
    rw [sin_arccos, hs, abs_of_nonneg hy]; ring
  · refine ⟨-arccos x, by rw [cos_neg, cos_arccos hx1 hx2], ?_⟩
    rw [sin_neg, sin_arccos, hs, abs_of_neg hy]; ring

/-- **Every circle through three distinct points of the ellipse is a `circleStar`** (with the
eccentric angles of the points). -/
theorem circle_eq_circleStar {D E G t1 t2 t3 : ℝ}
    (h1 : OnCircle D E G (cos t1) (sin t1 / 2)) (h2 : OnCircle D E G (cos t2) (sin t2 / 2))
    (h3 : OnCircle D E G (cos t3) (sin t3 / 2))
    (d12 : ¬(cos t1 = cos t2 ∧ sin t1 = sin t2)) (d13 : ¬(cos t1 = cos t3 ∧ sin t1 = sin t3))
    (d23 : ¬(cos t2 = cos t3 ∧ sin t2 = sin t3)) :
    D = cD t1 t2 t3 ∧ E = cE t1 t2 t3 ∧ G = cG t1 t2 t3 := by
  obtain ⟨k1, k2, k3⟩ := circleStar_mem t1 t2 t3
  unfold OnCircle at h1 h2 h3 k1 k2 k3
  set a := D - cD t1 t2 t3
  set b := (E - cE t1 t2 t3) / 2
  set c := G - cG t1 t2 t3
  have l1 : a * cos t1 + b * sin t1 + c = 0 := by simp only [a, b, c]; linarith
  have l2 : a * cos t2 + b * sin t2 + c = 0 := by simp only [a, b, c]; linarith
  have l3 : a * cos t3 + b * sin t3 + c = 0 := by simp only [a, b, c]; linarith
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · rcases line_circle hab (sin_sq_add_cos_sq t1 ▸ by ring) (sin_sq_add_cos_sq t2 ▸ by ring)
      (sin_sq_add_cos_sq t3 ▸ by ring) l1 l2 l3 with h | h | h
    · exact (d12 h).elim
    · exact (d13 h).elim
    · exact (d23 h).elim
  · push Not at hab
    rw [hab.1, hab.2] at l1
    have hc : c = 0 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have := hab.1; simp only [a] at this; linarith
    · have := hab.2; simp only [b] at this; linarith
    · simp only [c] at hc; linarith

/-- **A circle through `F` has at most two points in common with the ellipse.** -/
theorem circle_through_F {D E G : ℝ} (hF : OnCircle D E G (3 / 2) 0) {x1 y1 x2 y2 x3 y3 : ℝ}
    (e1 : OnEllipse x1 y1) (e2 : OnEllipse x2 y2) (e3 : OnEllipse x3 y3)
    (c1 : OnCircle D E G x1 y1) (c2 : OnCircle D E G x2 y2) (c3 : OnCircle D E G x3 y3) :
    (x1 = x2 ∧ y1 = y2) ∨ (x1 = x3 ∧ y1 = y3) ∨ (x2 = x3 ∧ y2 = y3) := by
  obtain ⟨t1, rfl, rfl⟩ := ellipse_param e1
  obtain ⟨t2, rfl, rfl⟩ := ellipse_param e2
  obtain ⟨t3, rfl, rfl⟩ := ellipse_param e3
  by_contra hne
  push Not at hne
  obtain ⟨n12, n13, n23⟩ := hne
  have d : ∀ u v : ℝ, (cos u = cos v → sin u / 2 ≠ sin v / 2) → ¬(cos u = cos v ∧ sin u = sin v) :=
    fun u v h h' => h h'.1 (by rw [h'.2])
  obtain ⟨hD, hE, hG⟩ := circle_eq_circleStar c1 c2 c3 (d _ _ n12) (d _ _ n13) (d _ _ n23)
  have := power_F_pos t1 t2 t3
  unfold OnCircle at hF
  rw [hD, hE, hG] at hF
  linarith

/-! ### `circleStar` meets the ellipse exactly in the four points, with multiplicity -/

/-- **Factorization**: the power of the point of eccentric angle `θ` with respect to
`circleStar θ₁ θ₂ θ₃` is `3 ∏ₖ sin ((θ - θₖ)/2)` (`θ₄ = -(θ₁+θ₂+θ₃)`); so this circle meets the
ellipse exactly in the four points of eccentric angles `θ₁, …, θ₄`, counted with multiplicity
(all real). -/
theorem circleStar_factor (t1 t2 t3 t : ℝ) :
    cos t ^ 2 + (sin t / 2) ^ 2 + cD t1 t2 t3 * cos t + cE t1 t2 t3 * (sin t / 2) + cG t1 t2 t3 =
      3 * (sin ((t - t1) / 2) * sin ((t - t2) / 2) * sin ((t - t3) / 2) *
        sin ((t - -(t1 + t2 + t3)) / 2)) := by
  rw [circleStar_eval]
  set u := t / 2
  set s := (t1 + t2) / 2
  set α := (t1 - t2) / 2
  set β := t3 + (t1 + t2) / 2
  have q1 : (t - t1) / 2 = u - (s + α) / 2 := by simp only [u, s, α]; ring
  have q2 : (t - t2) / 2 = u - (s - α) / 2 := by simp only [u, s, α]; ring
  have q3 : (t - t3) / 2 = u - (-s + β) / 2 := by simp only [u, s, β]; ring
  have q4 : (t - -(t1 + t2 + t3)) / 2 = u - (-s - β) / 2 := by simp only [u, s, β]; ring
  -- pair products
  have p12 : sin (u - (s + α) / 2) * sin (u - (s - α) / 2) = (cos α - cos (2 * u - 2 * s / 2)) / 2 := by
    rw [sin_mul_sin', show u - (s + α) / 2 - (u - (s - α) / 2) = -α by ring,
      show u - (s + α) / 2 + (u - (s - α) / 2) = 2 * u - 2 * s / 2 by ring, cos_neg]
  have p34 : sin (u - (-s + β) / 2) * sin (u - (-s - β) / 2) =
      (cos β - cos (2 * u + 2 * s / 2)) / 2 := by
    rw [sin_mul_sin', show u - (-s + β) / 2 - (u - (-s - β) / 2) = -β by ring,
      show u - (-s + β) / 2 + (u - (-s - β) / 2) = 2 * u + 2 * s / 2 by ring, cos_neg]
  rw [q1, q2, q3, q4, show ∀ w x y z : ℝ, w * x * y * z = (w * x) * (y * z) from fun _ _ _ _ => by
    ring, p12, p34]
  -- the left side, in the variables `u, s, α, β`
  have r0 : cos (t + t) = cos (4 * u) := by congr 1; simp only [u]; ring
  have r1 : cos (t1 + t) = cos (2 * u + s + α) := by congr 1; simp only [u, s, α]; ring
  have r2 : cos (t2 + t) = cos (2 * u + s - α) := by congr 1; simp only [u, s, α]; ring
  have r3 : cos (t3 + t) = cos (2 * u - s + β) := by congr 1; simp only [u, s, β]; ring
  have r4 : cos (-(t1 + t2 + t3) + t) = cos (2 * u - s - β) := by
    congr 1; simp only [u, s, β]; ring
  have r5 : cos (t1 + t2) = cos (2 * s) := by congr 1; simp only [s]; ring
  have r6 : cos (t1 + t3) = cos (α + β) := by congr 1; simp only [α, β]; ring
  have r7 : cos (t1 + -(t1 + t2 + t3)) = cos (α - β) := by
    congr 1; simp only [α, β]; ring
  have r8 : cos (t2 + t3) = cos (α - β) := by
    rw [← cos_neg]; congr 1; simp only [α, β]; ring
  have r9 : cos (t2 + -(t1 + t2 + t3)) = cos (α + β) := by
    rw [← cos_neg]; congr 1; simp only [α, β]; ring
  have r10 : cos (t3 + -(t1 + t2 + t3)) = cos (2 * s) := by
    rw [← cos_neg]; congr 1; simp only [s]; ring
  rw [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  have m1 := cos_mul_cos' α β
  have m2 := cos_mul_cos' α (2 * u + 2 * s / 2)
  have m3 := cos_mul_cos' β (2 * u - 2 * s / 2)
  have m4 := cos_mul_cos' (2 * u - 2 * s / 2) (2 * u + 2 * s / 2)
  have z1 : cos (α + (2 * u + 2 * s / 2)) = cos (2 * u + s + α) := by congr 1; ring
  have z2 : cos (α - (2 * u + 2 * s / 2)) = cos (2 * u + s - α) := by
    rw [← cos_neg]; congr 1; ring
  have z3 : cos (β + (2 * u - 2 * s / 2)) = cos (2 * u - s + β) := by congr 1; ring
  have z4 : cos (β - (2 * u - 2 * s / 2)) = cos (2 * u - s - β) := by
    rw [← cos_neg]; congr 1; ring
  have z5 : cos (2 * u - 2 * s / 2 + (2 * u + 2 * s / 2)) = cos (4 * u) := by congr 1; ring
  have z6 : cos (2 * u - 2 * s / 2 - (2 * u + 2 * s / 2)) = cos (2 * s) := by
    rw [← cos_neg]; congr 1; ring
  rw [z1, z2] at m2; rw [z3, z4] at m3; rw [z5, z6] at m4
  linear_combination (-(3 / 4)) * m1 + (3 / 4) * m2 + (3 / 4) * m3 - (3 / 4) * m4

/-- **No circle cutting the ellipse in four real points passes through `F`** (for every choice of
the four eccentric angles `θ₁, θ₂, θ₃, -(θ₁+θ₂+θ₃)`, distinct or coincident). -/
theorem no_four_point_circle_through_F (t1 t2 t3 : ℝ) :
    ¬OnCircle (cD t1 t2 t3) (cE t1 t2 t3) (cG t1 t2 t3) (3 / 2) 0 := by
  unfold OnCircle
  have := power_F_pos t1 t2 t3
  intro h; linarith

end HilbertEllipse

end HilbertFoundations
