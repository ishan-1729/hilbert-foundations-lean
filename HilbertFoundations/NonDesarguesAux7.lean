import HilbertFoundations.NonDesarguesAux5

/-!
# Hilbert's own geometry of § 23: doubly tangent circles and the configuration of Fig. 40
(helper for `NonDesargues.lean`)

* `exterior_bitangent_symmetric`: a circle which encloses the ellipse `x² + 4y² = 1` and has two
  distinct points in common with it (an exterior doubly tangent circle) has its centre on the
  `y`-axis, and the two points of contact are symmetric with respect to the `y`-axis
  (Hilbert: "All such circles must lie, as we can easily see, symmetrically with respect to the
  `y`-axis").
* `xaxis_no_circle`: the `x`-axis passes through `F` and cuts the ellipse in `(±1, 0)`; there is no
  circle through `(-1, 0)`, `(1, 0)`, `F`, so Hilbert's rule for the straight lines of the new
  geometry does not apply to it (nor to any line through `F` cutting the ellipse).
* The configuration of Fig. 40 in Hilbert's geometry, with the `x`-axis kept straight
  (`fig40_*`).
-/

namespace HilbertFoundations

namespace HilbertEllipse

open Real

/-! ### Exterior doubly tangent circles are symmetric to the `y`-axis -/

/-- **Exterior doubly tangent circles.** If the circle of centre `(h, k)` and squared radius `ρ`
encloses the ellipse (every point of the ellipse lies in the closed disc) and has two distinct
points `(x₁, y₁)`, `(x₂, y₂)` in common with it (at which it is then tangent to the ellipse), then
`h = 0`, and the two points are symmetric with respect to the `y`-axis. -/
theorem exterior_bitangent_symmetric {h k ρ x1 y1 x2 y2 : ℝ}
    (hin : ∀ x y : ℝ, OnEllipse x y → (x - h) ^ 2 + (y - k) ^ 2 ≤ ρ)
    (e1 : OnEllipse x1 y1) (e2 : OnEllipse x2 y2)
    (c1 : (x1 - h) ^ 2 + (y1 - k) ^ 2 = ρ) (c2 : (x2 - h) ^ 2 + (y2 - k) ^ 2 = ρ)
    (hne : x1 ≠ x2 ∨ y1 ≠ y2) : h = 0 ∧ y2 = y1 ∧ x2 = -x1 := by
  unfold OnEllipse at e1 e2
  have hd : 0 ≤ 1 - (y1 + y2) ^ 2 := by
    nlinarith [sq_nonneg (y1 - y2), sq_nonneg x1, sq_nonneg x2]
  set s := √(1 - (y1 + y2) ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - (y1 + y2) ^ 2 := Real.sq_sqrt hd
  have h2s : (x1 + x2) ^ 2 ≤ (2 * s) ^ 2 := by
    rw [mul_pow, hs2]; nlinarith [sq_nonneg (x1 - x2), sq_nonneg (y1 - y2)]
  have habs := sq_le_sq.1 h2s
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s)] at habs
  obtain ⟨hlo, hup⟩ := abs_le.1 habs
  -- the point of the ellipse of ordinate `(y₁ + y₂)/2` and abscissa `xm = ± s`
  have key : ∀ xm : ℝ, xm ^ 2 = s ^ 2 →
      (3 / 4) * (y1 - y2) ^ 2 + h * (x1 + x2 - 2 * xm) ≤ 0 := by
    intro xm hxm
    have hle := hin xm ((y1 + y2) / 2) (by unfold OnEllipse; rw [hxm, hs2]; ring)
    have eq : (3 / 4) * (y1 - y2) ^ 2 + h * (x1 + x2 - 2 * xm) =
        (xm - h) ^ 2 + ((y1 + y2) / 2 - k) ^ 2 - ρ := by
      linear_combination (-1 / 2 : ℝ) * c1 - (1 / 2 : ℝ) * c2 - hxm - hs2 + (1 / 2 : ℝ) * e1 +
        (1 / 2 : ℝ) * e2
    linarith
  -- if `y₁ = y₂` and `(x₁ + x₂)² = 4 s²`, the two points coincide
  have coinc : y1 = y2 → (x1 + x2) ^ 2 = 4 * s ^ 2 → False := by
    intro hy hx
    subst hy
    have h0 : (x1 - x2) ^ 2 = 0 := by
      linear_combination 2 * e1 + 2 * e2 - hx - 4 * hs2
    have : x1 = x2 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
    rcases hne with h' | h'
    · exact h' this
    · exact h' rfl
  have hyy : ∀ {t : ℝ}, (3 / 4) * (y1 - y2) ^ 2 + t ≤ 0 → 0 ≤ t → y1 = y2 ∧ t = 0 := by
    intro t h1 h2
    have h0 : (y1 - y2) ^ 2 = 0 := by linarith [sq_nonneg (y1 - y2)]
    exact ⟨sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), by linarith [sq_nonneg (y1 - y2)]⟩
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · exfalso
    obtain ⟨hy, ht⟩ := hyy (key s rfl) (mul_nonneg_of_nonpos_of_nonpos hneg.le (by linarith))
    have : x1 + x2 - 2 * s = 0 := by
      rcases mul_eq_zero.1 ht with h' | h'
      · exact absurd h' hneg.ne
      · exact h'
    exact coinc hy (by rw [show x1 + x2 = 2 * s by linarith]; ring)
  · subst hzero
    obtain ⟨hy, -⟩ := hyy (t := 0 * (x1 + x2 - 2 * s)) (key s rfl) (by simp)
    subst hy
    refine ⟨rfl, rfl, ?_⟩
    have : (x2 - x1) * (x2 + x1) = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.1 this with h' | h'
    · rcases hne with h'' | h''
      · exact absurd (by linarith) h''
      · exact absurd rfl h''
    · linarith
  · exfalso
    obtain ⟨hy, ht⟩ := hyy (key (-s) (by ring)) (mul_nonneg hpos.le (by linarith))
    have : x1 + x2 - 2 * -s = 0 := by
      rcases mul_eq_zero.1 ht with h' | h'
      · exact absurd h' hpos.ne'
      · exact h'
    exact coinc hy (by rw [show x1 + x2 = -(2 * s) by linarith]; ring)

/-! ### Lines through `F` -/

/-- The `x`-axis cuts the ellipse in `(-1, 0)` and `(1, 0)` and passes through `F = (3/2, 0)`. -/
theorem xaxis_cuts : OnEllipse (-1) 0 ∧ OnEllipse 1 0 := by
  constructor <;> norm_num [OnEllipse]

/-- **No circle passes through `(-1, 0)`, `(1, 0)` and `F`**: Hilbert's rule ("construct a circle
passing through the points `P` and `Q` and the fixed point `F`") is void for the `x`-axis. -/
theorem xaxis_no_circle :
    ¬∃ D E G : ℝ, OnCircle D E G (-1) 0 ∧ OnCircle D E G 1 0 ∧ OnCircle D E G (3 / 2) 0 := by
  rintro ⟨D, E, G, h1, h2, h3⟩
  unfold OnCircle at h1 h2 h3
  norm_num at h1 h2 h3
  linarith

/-! ### The configuration of Fig. 40 in Hilbert's geometry -/

/-- The closed region bounded by the ellipse. -/
def InEllipse (x y : ℝ) : Prop := x ^ 2 + 4 * y ^ 2 ≤ 1

/-- **The straight line of Hilbert's new geometry** arising from an ordinary line `g` which cuts
the ellipse in `P` and `Q`, when the circle through `P`, `Q`, `F` is `x² + y² + D x + E y + G = 0`:
the two parts of `g` outside the ellipse (from `P` and from `Q` outward) and the arc `PQ` of the
circle inside the ellipse (by `circle_through_F` the circle has no further common point with the
ellipse, so this is one arc). -/
def HLine (g : ℝ → ℝ → Prop) (D E G : ℝ) (x y : ℝ) : Prop :=
  (g x y ∧ 1 ≤ x ^ 2 + 4 * y ^ 2) ∨ (OnCircle D E G x y ∧ InEllipse x y)

/-- The `y`-axis. -/
def gY (x _ : ℝ) : Prop := x = 0

/-- The line through `(3/5, 2/5)` and `(-3/5, -2/5)`. -/
def gT (x y : ℝ) : Prop := y = 2 / 3 * x

/-- The circle through `(0, 1/2)`, `(0, -1/2)` and `F`, and it is the only one. -/
theorem circleY_spec :
    OnEllipse 0 (1 / 2) ∧ OnEllipse 0 (-1 / 2) ∧ OnCircle (-4 / 3) 0 (-1 / 4) 0 (1 / 2) ∧
    OnCircle (-4 / 3) 0 (-1 / 4) 0 (-1 / 2) ∧ OnCircle (-4 / 3) 0 (-1 / 4) (3 / 2) 0 ∧
    ∀ D E G : ℝ, OnCircle D E G 0 (1 / 2) → OnCircle D E G 0 (-1 / 2) → OnCircle D E G (3 / 2) 0 →
      D = -4 / 3 ∧ E = 0 ∧ G = -1 / 4 := by
  refine ⟨by norm_num [OnEllipse], by norm_num [OnEllipse], by norm_num [OnCircle],
    by norm_num [OnCircle], by norm_num [OnCircle], fun D E G h1 h2 h3 => ?_⟩
  unfold OnCircle at h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The circle through `(3/5, 2/5)`, `(-3/5, -2/5)` and `F`, and it is the only one. -/
theorem circleT_spec :
    OnEllipse (3 / 5) (2 / 5) ∧ OnEllipse (-3 / 5) (-2 / 5) ∧ gT (3 / 5) (2 / 5) ∧
    gT (-3 / 5) (-2 / 5) ∧ OnCircle (-173 / 150) (173 / 100) (-13 / 25) (3 / 5) (2 / 5) ∧
    OnCircle (-173 / 150) (173 / 100) (-13 / 25) (-3 / 5) (-2 / 5) ∧
    OnCircle (-173 / 150) (173 / 100) (-13 / 25) (3 / 2) 0 ∧
    ∀ D E G : ℝ, OnCircle D E G (3 / 5) (2 / 5) → OnCircle D E G (-3 / 5) (-2 / 5) →
      OnCircle D E G (3 / 2) 0 → D = -173 / 150 ∧ E = 173 / 100 ∧ G = -13 / 25 := by
  refine ⟨by norm_num [OnEllipse], by norm_num [OnEllipse], by norm_num [gT], by norm_num [gT],
    by norm_num [OnCircle], by norm_num [OnCircle], by norm_num [OnCircle],
    fun D E G h1 h2 h3 => ?_⟩
  unfold OnCircle at h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The broken line arising from the `y`-axis. -/
def lineY : ℝ → ℝ → Prop := HLine gY (-4 / 3) 0 (-1 / 4)

/-- The broken line arising from the line through `(±3/5, ±2/5)`. -/
def lineT : ℝ → ℝ → Prop := HLine gT (-173 / 150) (173 / 100) (-13 / 25)

/-- **Fig. 40, the two triangles.** `A = (3, 0)`, `B = (0, 3)`, `C = (3, 2)` and
`A' = (6, 0)`, `B' = (0, 6)`, `C' = (6, 4)` have their vertices on the `x`-axis, the broken
`y`-axis and the broken line `lineT` respectively; their sides lie on the ordinary lines
`x + y = 3`, `x + 3y = 9`, `x = 3` and `x + y = 6`, `x + 3y = 18`, `x = 6`, which do not meet the
(closed) ellipse, so that they are straight lines of the new geometry, homologous sides being
parallel. -/
theorem fig40_triangles :
    -- the vertices on the three lines
    ((0 : ℝ) = 0 ∧ (0 : ℝ) = 0) ∧ (lineY 0 3 ∧ lineY 0 6) ∧ (lineT 3 2 ∧ lineT 6 4) ∧
    -- the vertices on the sides
    ((3 : ℝ) + 0 = 3 ∧ (0 : ℝ) + 3 = 3) ∧ ((0 : ℝ) + 3 * 3 = 9 ∧ (3 : ℝ) + 3 * 2 = 9) ∧
    ((6 : ℝ) + 0 = 6 ∧ (0 : ℝ) + 6 = 6) ∧ ((0 : ℝ) + 3 * 6 = 18 ∧ (6 : ℝ) + 3 * 4 = 18) ∧
    -- the sides lie exterior to the ellipse
    (∀ x y : ℝ, InEllipse x y →
      x + y ≠ 3 ∧ x + 3 * y ≠ 9 ∧ x ≠ 3 ∧ x + y ≠ 6 ∧ x + 3 * y ≠ 18 ∧ x ≠ 6) ∧
    -- homologous sides are parallel
    (∀ x y : ℝ, ¬(x + y = 3 ∧ x + y = 6) ∧ ¬(x + 3 * y = 9 ∧ x + 3 * y = 18) ∧
      ¬(x = 3 ∧ x = 6)) := by
  refine ⟨⟨rfl, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, ?_⟩
  · left; norm_num [gY]
  · left; norm_num [gY]
  · left; norm_num [gT]
  · left; norm_num [gT]
  · intro x y h
    unfold InEllipse at h
    have hx : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
    have hy : 4 * y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hx1 : x ≤ 1 := by nlinarith
    have hy1 : y ≤ 1 / 2 := by nlinarith
    refine ⟨by intro e; linarith, by intro e; linarith, by intro e; linarith, by intro e; linarith,
      by intro e; linarith, by intro e; linarith⟩
  · intro x y
    refine ⟨fun ⟨h1, h2⟩ => by linarith, fun ⟨h1, h2⟩ => by linarith, fun ⟨h1, h2⟩ => by linarith⟩

/-- **Fig. 40, the joining lines.** The `x`-axis (`AA'`, kept straight), the broken `y`-axis
(`BB'`) and the broken line `lineT` (`CC'`) have no common point: the broken `y`-axis meets the
`x`-axis only in `(-1/6, 0)`, and `lineT` meets it in `(-26/75, 0)`. In particular the joining
lines are neither concurrent nor pairwise without common point. -/
theorem fig40_joining_lines :
    ¬(∃ x y : ℝ, y = 0 ∧ lineY x y ∧ lineT x y) ∧
    (lineY (-1 / 6) 0 ∧ ∀ x : ℝ, lineY x 0 → x = -1 / 6) ∧ lineT (-26 / 75) 0 := by
  have hY : ∀ x : ℝ, lineY x 0 → x = -1 / 6 := by
    intro x hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · unfold gY at h1; subst h1; norm_num at h2
    · unfold OnCircle at h1; unfold InEllipse at h2
      have : (x - 3 / 2) * (x + 1 / 6) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 this with h | h
      · nlinarith
      · linarith
  refine ⟨?_, ⟨?_, hY⟩, ?_⟩
  · rintro ⟨x, y, rfl, h1, h2⟩
    have := hY x h1
    subst this
    rcases h2 with ⟨h, -⟩ | ⟨h, -⟩
    · unfold gT at h; norm_num at h
    · unfold OnCircle at h; norm_num at h
  · right; norm_num [OnCircle, InEllipse]
  · right; norm_num [OnCircle, InEllipse]

end HilbertEllipse

end HilbertFoundations
