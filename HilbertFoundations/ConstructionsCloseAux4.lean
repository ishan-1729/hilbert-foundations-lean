import HilbertFoundations.Constructions

/-!
# Helper module for `ConstructionsClose.lean`: the problem of Malfatti

This module contains no unit of Hilbert's text. It proves `MalfattiClaim` (unit `s39.malfatti`):
the three circles of Malfatti of every triangle can be constructed by straight-edge and
transferer.

For a triangle `ABC` with sides `a`, `b`, `c`, perimeter `p = 2s`, incenter `I`, inradius `r`,
tangent lengths `x = s - a`, `y = s - b`, `z = s - c` and distances `d = IA`, `e = IB`, `f = IC`
(`d² = r² + x²`, …), the classical closed form is used: the circle in the angle `A` touches the
sides at the distance

`t₁ = (s + d - r - e - f) / 2`

from `A`, so its center is `A + (t₁/x) (I - A)` and its radius `(t₁/x) r`; cyclically for `B`, `C`.

* `malfatti_scalar`: the algebra, `d e z = r (x + y) f` and
  `4 z t₁ t₂ = s (r + f - z)²`, with `0 < t₁ < x`, `0 < t₂ < y`;
* `malfatti_real`: in coordinates relative to `A` — Heron's formula `r² s = x y z`, the tangency
  to the two sides, and the contact of two of the circles
  (`|O₁O₂|² = (c - t₁ - t₂)² + (r₁ - r₂)²` and `c - t₁ - t₂ = r + f - z`);
* `malfatti_vertex`: the same for points of the plane, with `O₁` inside the triangle;
* `malfattiClaim_aux`: `MalfattiClaim`; all the numbers used arise from the coordinates of the
  vertices by the rational operations and square roots of sums of two squares, so the centers are
  constructible by Theorem 41.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace HilbertFoundations

open Coord

/-- **The algebra of the circles of Malfatti.** With `r² (x + y + z) = x y z`, `d² = r² + x²`,
`e² = r² + y²`, `f² = r² + z²` and `2 t₁ = s + d - r - e - f`, `2 t₂ = s + e - r - d - f`:
`0 < t₁ < x`, `0 < t₂ < y` and `(r + f - z)² x y = 4 t₁ t₂ r²`. -/
theorem malfatti_scalar {x y z r d e f t₁ t₂ : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hr0 : 0 < r) (hr : r ^ 2 * (x + y + z) = x * y * z)
    (hd0 : 0 < d) (hd : d ^ 2 = r ^ 2 + x ^ 2) (he0 : 0 < e) (he : e ^ 2 = r ^ 2 + y ^ 2)
    (hf0 : 0 < f) (hf : f ^ 2 = r ^ 2 + z ^ 2)
    (ht₁ : 2 * t₁ = x + y + z + d - r - e - f) (ht₂ : 2 * t₂ = x + y + z + e - r - d - f) :
    0 < t₁ ∧ t₁ < x ∧ 0 < t₂ ∧ t₂ < y ∧ (r + f - z) ^ 2 * (x * y) = 4 * t₁ * t₂ * r ^ 2 := by
  have hr2 : 0 < r ^ 2 := pow_pos hr0 2
  -- `IA · IB · z = r c · IC`
  have hde : d * e * z = r * (x + y) * f := by
    have h1 : (d * e * z) ^ 2 = (r * (x + y) * f) ^ 2 := by
      have e1 : (d * e * z) ^ 2 = (r ^ 2 + x ^ 2) * (r ^ 2 + y ^ 2) * z ^ 2 := by
        rw [mul_pow, mul_pow, hd, he]
      have e2 : (r * (x + y) * f) ^ 2 = r ^ 2 * (x + y) ^ 2 * (r ^ 2 + z ^ 2) := by
        rw [mul_pow, mul_pow, hf]
      rw [e1, e2]
      linear_combination (-(x * y * z + r ^ 2 * (x + y + z) - 2 * z * r ^ 2)) * hr
    exact (sq_eq_sq₀ (by positivity) (by positivity)).1 h1
  have key : 4 * z * t₁ * t₂ = (x + y + z) * (r + f - z) ^ 2 := by
    have : 4 * z * t₁ * t₂ = z * (2 * t₁) * (2 * t₂) := by ring
    rw [this, ht₁, ht₂]
    linear_combination (-z) * hd - z * he + (z - (x + y + z)) * hf + 2 * hde - 2 * hr
  -- the hypotenuses
  have lt_hyp : ∀ {w u : ℝ}, 0 < w → 0 < u → w ^ 2 = r ^ 2 + u ^ 2 → u < w ∧ w < u + r := by
    intro w u hw hu h
    constructor
    · by_contra hc
      push Not at hc
      have := pow_le_pow_left₀ hw.le hc 2
      linarith
    · by_contra hc
      push Not at hc
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ u + r) hc 2
      nlinarith [mul_pos hu hr0]
  obtain ⟨hxd, hdx⟩ := lt_hyp hd0 hx hd
  obtain ⟨hye, hey⟩ := lt_hyp he0 hy he
  obtain ⟨hzf, hfz⟩ := lt_hyp hf0 hz hf
  -- `2 r < x + y`
  have hrxy : r ^ 2 < x * y := by
    have h1 : r ^ 2 * z < x * y * z := by nlinarith [mul_pos hr2 hx, mul_pos hr2 hy]
    exact lt_of_mul_lt_mul_right h1 hz.le
  have h2r : 2 * r < x + y := by
    by_contra hc
    push Not at hc
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x + y) hc 2
    nlinarith [sq_nonneg (x - y)]
  have hsum : 0 < t₁ + t₂ := by linarith
  have hprod : 0 < t₁ * t₂ := by
    have h1 : 0 < (x + y + z) * (r + f - z) ^ 2 :=
      mul_pos (by positivity) (pow_pos (by linarith) 2)
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hz.le (neg_nonneg.2 hc)]
  have ht1 : 0 < t₁ := by
    rcases le_or_gt t₁ 0 with h | h
    · have h2 : 0 < t₂ := by linarith
      nlinarith [mul_nonneg (neg_nonneg.2 h) h2.le]
    · exact h
  have ht2 : 0 < t₂ := by
    rcases le_or_gt t₂ 0 with h | h
    · nlinarith [mul_nonneg (neg_nonneg.2 h) ht1.le]
    · exact h
  refine ⟨ht1, by linarith, ht2, by linarith, ?_⟩
  have h3 : (x + y + z) * ((r + f - z) ^ 2 * (x * y)) = (x + y + z) * (4 * t₁ * t₂ * r ^ 2) := by
    linear_combination (-(x * y)) * key - 4 * t₁ * t₂ * hr
  exact mul_left_cancel₀ (by positivity : x + y + z ≠ 0) h3

theorem eq_zero_of_sq_add_sq {m n : ℝ} (h : 0 = m ^ 2 + n ^ 2) : m = 0 ∧ n = 0 := by
  have h1 : m ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg n]) (sq_nonneg m)
  have h2 : n ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg m]) (sq_nonneg n)
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 h1, pow_eq_zero_iff two_ne_zero |>.1 h2⟩

theorem pos_of_pairwise {m n o : ℝ} (h1 : 0 < m + n) (h2 : 0 < m + o) (h3 : 0 < n + o)
    (h4 : 0 < m * n * o) : 0 < m := by
  by_contra hc
  push Not at hc
  have hn : 0 < n := by linarith
  have ho : 0 < o := by linarith
  nlinarith [mul_nonneg (neg_nonneg.2 hc) (mul_pos hn ho).le]

/-- The sides, the tangent lengths and Heron's formula `r² s = x y z`, in coordinates relative to
the vertex `A`: `u = B - A`, `v = C - A`. -/
theorem malfatti_setup {u1 u2 v1 v2 a b c p r x y z : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ^ 2 = (v1 - u1) ^ 2 + (v2 - u2) ^ 2) (hb : b ^ 2 = v1 ^ 2 + v2 ^ 2)
    (hc : c ^ 2 = u1 ^ 2 + u2 ^ 2) (hk : u1 * v2 - u2 * v1 ≠ 0) (hp : p = a + b + c)
    (hr0 : 0 < r) (hrk : (r * p) ^ 2 = (u1 * v2 - u2 * v1) ^ 2)
    (hx : x = p / 2 - a) (hy : y = p / 2 - b) (hz : z = p / 2 - c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ r ^ 2 * (x + y + z) = x * y * z := by
  have hcp : 0 < c := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at hc
      obtain ⟨h1, h2⟩ := eq_zero_of_sq_add_sq hc
      exact hk (by rw [h1, h2]; ring)
  have hbp : 0 < b := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at hb
      obtain ⟨h1, h2⟩ := eq_zero_of_sq_add_sq hb
      exact hk (by rw [h1, h2]; ring)
  have hap : 0 < a := by
    rcases ha0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at ha
      obtain ⟨h1, h2⟩ := eq_zero_of_sq_add_sq ha
      have e1 : v1 = u1 := sub_eq_zero.1 h1
      have e2 : v2 = u2 := sub_eq_zero.1 h2
      exact hk (by rw [e1, e2]; ring)
  have hp0 : 0 < p := by rw [hp]; positivity
  have huv : u1 * v1 + u2 * v2 = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by
    linear_combination (1 / 2) * ha - (1 / 2) * hb - (1 / 2) * hc
  -- Heron's formula
  have heron : (u1 * v2 - u2 * v1) ^ 2 = 4 * (p / 2) * x * y * z := by
    have h1 : (u1 * v2 - u2 * v1) ^ 2 =
        (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) - (u1 * v1 + u2 * v2) ^ 2 := by ring
    rw [h1, ← hc, ← hb, huv, hx, hy, hz, hp]
    ring
  have hs : x + y + z = p / 2 := by rw [hx, hy, hz, hp]; ring
  have hrs : r ^ 2 * (x + y + z) = x * y * z := by
    rw [hs]
    have h1 : p * (r ^ 2 * (p / 2)) = p * (x * y * z) := by
      linear_combination (1 / 2) * hrk + (1 / 2) * heron
    exact mul_left_cancel₀ hp0.ne' h1
  have hxyz : 0 < x * y * z := by rw [← hrs, hs]; positivity
  have hxy : 0 < x + y := by
    have : x + y = c := by rw [hx, hy, hp]; ring
    rw [this]; exact hcp
  have hyz : 0 < y + z := by
    have : y + z = a := by rw [hy, hz, hp]; ring
    rw [this]; exact hap
  have hxz : 0 < x + z := by
    have : x + z = b := by rw [hx, hz, hp]; ring
    rw [this]; exact hbp
  have hx0 : 0 < x := pos_of_pairwise hxy hxz hyz hxyz
  have hy0 : 0 < y := pos_of_pairwise (m := y) (n := x) (o := z) (by rw [add_comm]; exact hxy)
    hyz hxz (by rw [mul_comm y x]; exact hxyz)
  have hz0 : 0 < z := pos_of_pairwise (m := z) (n := x) (o := y) (by rw [add_comm]; exact hxz)
    (by rw [add_comm]; exact hyz) hxy
    (by rw [mul_comm z x, mul_assoc, mul_comm z y, ← mul_assoc]; exact hxyz)
  exact ⟨hap, hbp, hcp, hx0, hy0, hz0, hrs⟩

/-- The distance from the incenter to the sides `AB`, `AC` is `r`: tangency of a circle with
center `A + l (I - A)` and radius `l r`. -/
theorem malfatti_tangent {u1 u2 v1 v2 i1 i2 b c p r l : ℝ} (hp0 : p ≠ 0)
    (hb : b ^ 2 = v1 ^ 2 + v2 ^ 2) (hc : c ^ 2 = u1 ^ 2 + u2 ^ 2)
    (hi1 : p * i1 = b * u1 + c * v1) (hi2 : p * i2 = b * u2 + c * v2)
    (hrk : (r * p) ^ 2 = (u1 * v2 - u2 * v1) ^ 2) :
    (u1 * i2 - u2 * i1) ^ 2 = c ^ 2 * r ^ 2 ∧
      (u1 * (l * i2) - u2 * (l * i1)) ^ 2 = (l * r) ^ 2 * (u1 ^ 2 + u2 ^ 2) ∧
      (v1 * (l * i2) - v2 * (l * i1)) ^ 2 = (l * r) ^ 2 * (v1 ^ 2 + v2 ^ 2) := by
  have hE : p * (u1 * i2 - u2 * i1) = c * (u1 * v2 - u2 * v1) := by
    linear_combination u1 * hi2 - u2 * hi1
  have hE2 : (u1 * i2 - u2 * i1) ^ 2 = c ^ 2 * r ^ 2 := by
    have h1 : p ^ 2 * (u1 * i2 - u2 * i1) ^ 2 = p ^ 2 * (c ^ 2 * r ^ 2) := by
      linear_combination (p * (u1 * i2 - u2 * i1) + c * (u1 * v2 - u2 * v1)) * hE - c ^ 2 * hrk
    exact mul_left_cancel₀ (pow_ne_zero 2 hp0) h1
  have hF : p * (v1 * i2 - v2 * i1) = -b * (u1 * v2 - u2 * v1) := by
    linear_combination v1 * hi2 - v2 * hi1
  have hF2 : (v1 * i2 - v2 * i1) ^ 2 = b ^ 2 * r ^ 2 := by
    have h1 : p ^ 2 * (v1 * i2 - v2 * i1) ^ 2 = p ^ 2 * (b ^ 2 * r ^ 2) := by
      linear_combination (p * (v1 * i2 - v2 * i1) - b * (u1 * v2 - u2 * v1)) * hF - b ^ 2 * hrk
    exact mul_left_cancel₀ (pow_ne_zero 2 hp0) h1
  exact ⟨hE2, by linear_combination l ^ 2 * hE2 + l ^ 2 * r ^ 2 * hc,
    by linear_combination l ^ 2 * hF2 + l ^ 2 * r ^ 2 * hb⟩

/-- The contact of the circles in the angles `A` and `B`: the distance of the centers
`A + l₁ (I - A)`, `B + l₂ (I - B)` is the sum of the radii `l₁ r`, `l₂ r`. -/
theorem malfatti_contact {u1 u2 v1 v2 i1 i2 a b c p r x y z d e f t₁ t₂ l₁ l₂ : ℝ}
    (ha : a ^ 2 = (v1 - u1) ^ 2 + (v2 - u2) ^ 2) (hb : b ^ 2 = v1 ^ 2 + v2 ^ 2)
    (hc : c ^ 2 = u1 ^ 2 + u2 ^ 2) (hp : p = a + b + c) (hp0 : p ≠ 0) (hc0 : c ≠ 0)
    (hi1 : p * i1 = b * u1 + c * v1) (hi2 : p * i2 = b * u2 + c * v2)
    (hE2 : (u1 * i2 - u2 * i1) ^ 2 = c ^ 2 * r ^ 2)
    (hx : x = p / 2 - a) (hy : y = p / 2 - b) (hz : z = p / 2 - c) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (ht₁ : 2 * t₁ = p / 2 + d - r - e - f) (ht₂ : 2 * t₂ = p / 2 + e - r - d - f)
    (hl1 : l₁ * x = t₁) (hl2 : l₂ * y = t₂)
    (hkey : (r + f - z) ^ 2 * (x * y) = 4 * t₁ * t₂ * r ^ 2) :
    (u1 + l₂ * (i1 - u1) - l₁ * i1) ^ 2 + (u2 + l₂ * (i2 - u2) - l₁ * i2) ^ 2 =
      (l₁ * r + l₂ * r) ^ 2 := by
  have huv : u1 * v1 + u2 * v2 = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by
    linear_combination (1 / 2) * ha - (1 / 2) * hb - (1 / 2) * hc
  have hxa : 2 * x = b + c - a := by rw [hx, hp]; ring
  have hiu : i1 * u1 + i2 * u2 = c * x := by
    have h1 : p * (i1 * u1 + i2 * u2) = p * (c * x) := by
      linear_combination u1 * hi1 + u2 * hi2 - b * hc + c * huv - c * x * hp -
        (c * (a + b + c) / 2) * hxa
    exact mul_left_cancel₀ hp0 h1
  have hcxy : c = x + y := by rw [hx, hy, hp]; ring
  have hwu : (u1 + l₂ * (i1 - u1) - l₁ * i1) * u1 + (u2 + l₂ * (i2 - u2) - l₁ * i2) * u2 =
      c * (r + f - z) := by
    linear_combination (1 - l₂) * (-hc) + (l₂ - l₁) * hiu -
      c * (l₂ * hcxy + hl2 + hl1 + (ht₁ + ht₂) / 2 - hz)
  have key2 : 4 * l₁ * l₂ * r ^ 2 = (r + f - z) ^ 2 := by
    have h1 : (x * y) * (4 * l₁ * l₂ * r ^ 2) = (x * y) * (r + f - z) ^ 2 := by
      linear_combination -hkey + 4 * r ^ 2 * (l₂ * y) * hl1 + 4 * r ^ 2 * t₁ * hl2
    exact mul_left_cancel₀ (mul_ne_zero hx0 hy0) h1
  have h1 : c ^ 2 * ((u1 + l₂ * (i1 - u1) - l₁ * i1) ^ 2 + (u2 + l₂ * (i2 - u2) - l₁ * i2) ^ 2) =
      c ^ 2 * (l₁ * r + l₂ * r) ^ 2 := by
    linear_combination
      ((u1 + l₂ * (i1 - u1) - l₁ * i1) ^ 2 + (u2 + l₂ * (i2 - u2) - l₁ * i2) ^ 2) * hc +
      ((u1 + l₂ * (i1 - u1) - l₁ * i1) * u1 + (u2 + l₂ * (i2 - u2) - l₁ * i2) * u2 +
        c * (r + f - z)) * hwu + (l₂ - l₁) ^ 2 * hE2 - c ^ 2 * key2
  exact mul_left_cancel₀ (pow_ne_zero 2 hc0) h1

/-- **The circles of Malfatti in coordinates relative to the vertex `A`**: `u = B - A`,
`v = C - A`, `i = I - A`. -/
theorem malfatti_real {u1 u2 v1 v2 i1 i2 a b c p r x y z d e f t₁ t₂ : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ^ 2 = (v1 - u1) ^ 2 + (v2 - u2) ^ 2) (hb : b ^ 2 = v1 ^ 2 + v2 ^ 2)
    (hc : c ^ 2 = u1 ^ 2 + u2 ^ 2) (hk : u1 * v2 - u2 * v1 ≠ 0) (hp : p = a + b + c)
    (hi1 : p * i1 = b * u1 + c * v1) (hi2 : p * i2 = b * u2 + c * v2)
    (hr0 : 0 < r) (hrk : (r * p) ^ 2 = (u1 * v2 - u2 * v1) ^ 2)
    (hx : x = p / 2 - a) (hy : y = p / 2 - b) (hz : z = p / 2 - c)
    (hd0 : 0 < d) (hd : d ^ 2 = r ^ 2 + x ^ 2) (he0 : 0 < e) (he : e ^ 2 = r ^ 2 + y ^ 2)
    (hf0 : 0 < f) (hf : f ^ 2 = r ^ 2 + z ^ 2)
    (ht₁ : 2 * t₁ = p / 2 + d - r - e - f) (ht₂ : 2 * t₂ = p / 2 + e - r - d - f) :
    0 < x ∧ 0 < t₁ ∧ t₁ < x ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
      (u1 + t₂ / y * (i1 - u1) - t₁ / x * i1) ^ 2 + (u2 + t₂ / y * (i2 - u2) - t₁ / x * i2) ^ 2 =
        (t₁ / x * r + t₂ / y * r) ^ 2 ∧
      (u1 * (t₁ / x * i2) - u2 * (t₁ / x * i1)) ^ 2 = (t₁ / x * r) ^ 2 * (u1 ^ 2 + u2 ^ 2) ∧
      (v1 * (t₁ / x * i2) - v2 * (t₁ / x * i1)) ^ 2 = (t₁ / x * r) ^ 2 * (v1 ^ 2 + v2 ^ 2) := by
  obtain ⟨hap, hbp, hcp, hx0, hy0, hz0, hrs⟩ :=
    malfatti_setup ha0 hb0 hc0 ha hb hc hk hp hr0 hrk hx hy hz
  have hs : x + y + z = p / 2 := by rw [hx, hy, hz, hp]; ring
  obtain ⟨ht1, ht1x, ht2, ht2y, hkey⟩ := malfatti_scalar hx0 hy0 hz0 hr0 hrs hd0 hd he0 he hf0 hf
    (by rw [hs]; exact ht₁) (by rw [hs]; exact ht₂)
  have hp0 : p ≠ 0 := by rw [hp]; positivity
  obtain ⟨hE2, htan1, htan2⟩ := malfatti_tangent (l := t₁ / x) hp0 hb hc hi1 hi2 hrk
  exact ⟨hx0, ht1, ht1x, hap, hbp, hcp,
    malfatti_contact ha hb hc hp hp0 hcp.ne' hi1 hi2 hE2 hx hy hz hx0.ne' hy0.ne' ht₁ ht₂
      (div_mul_cancel₀ _ hx0.ne') (div_mul_cancel₀ _ hy0.ne') hkey, htan1, htan2⟩

/-- **The circle of Malfatti in the angle `A`**: center `A + (t₁/x) (I - A)` inside the
triangle, radius `(t₁/x) r`; it touches `AB` and `AC`, and the circle in the angle `B`. -/
theorem malfatti_vertex {A B C I : Coord ℝ 2} {a b c p r x y z d e f t₁ t₂ : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ^ 2 = ip (C - B) (C - B)) (hb : b ^ 2 = ip (A - C) (A - C))
    (hc : c ^ 2 = ip (B - A) (B - A)) (hk : crossProd2 (B - A) (C - A) ≠ 0)
    (hp : p = a + b + c) (hIx : p * xc I = a * xc A + b * xc B + c * xc C)
    (hIy : p * yc I = a * yc A + b * yc B + c * yc C)
    (hr0 : 0 < r) (hrk : (r * p) ^ 2 = crossProd2 (B - A) (C - A) ^ 2)
    (hx : x = p / 2 - a) (hy : y = p / 2 - b) (hz : z = p / 2 - c)
    (hd0 : 0 < d) (hd : d ^ 2 = r ^ 2 + x ^ 2) (he0 : 0 < e) (he : e ^ 2 = r ^ 2 + y ^ 2)
    (hf0 : 0 < f) (hf : f ^ 2 = r ^ 2 + z ^ 2)
    (ht₁ : 2 * t₁ = p / 2 + d - r - e - f) (ht₂ : 2 * t₂ = p / 2 + e - r - d - f) :
    0 < t₁ / x * r ∧ InTriangle (A + (t₁ / x) • (I - A)) A B C ∧
      TangentToLine (A + (t₁ / x) • (I - A)) A B (t₁ / x * r) ∧
      TangentToLine (A + (t₁ / x) • (I - A)) A C (t₁ / x * r) ∧
      ip ((A + (t₁ / x) • (I - A)) - (B + (t₂ / y) • (I - B)))
        ((A + (t₁ / x) • (I - A)) - (B + (t₂ / y) • (I - B))) = (t₁ / x * r + t₂ / y * r) ^ 2 := by
  rw [crossProd2_def] at hk hrk
  simp only [xc_sub, yc_sub] at hk hrk
  obtain ⟨hx0, ht1, ht1x, hap, hbp, hcp, h1, h2, h3⟩ := malfatti_real
    (u1 := xc B - xc A) (u2 := yc B - yc A) (v1 := xc C - xc A) (v2 := yc C - yc A)
    (i1 := xc I - xc A) (i2 := yc I - yc A) ha0 hb0 hc0
    (by rw [ha, ip_two]; simp only [xc_sub, yc_sub]; ring)
    (by rw [hb, ip_two]; simp only [xc_sub, yc_sub]; ring)
    (by rw [hc, ip_two]; simp only [xc_sub, yc_sub]; ring) hk hp
    (by linear_combination hIx - xc A * hp) (by linear_combination hIy - yc A * hp)
    hr0 hrk hx hy hz hd0 hd he0 he hf0 hf ht₁ ht₂
  have hp0 : 0 < p := by rw [hp]; positivity
  have hl0 : 0 < t₁ / x := div_pos ht1 hx0
  have hl1 : t₁ / x < 1 := (div_lt_one hx0).2 ht1x
  generalize t₁ / x = l₁ at *
  generalize t₂ / y = l₂ at *
  have hxI : xc I = (a * xc A + b * xc B + c * xc C) / p :=
    eq_div_of_mul_eq hp0.ne' (by rw [mul_comm]; exact hIx)
  have hyI : yc I = (a * yc A + b * yc B + c * yc C) / p :=
    eq_div_of_mul_eq hp0.ne' (by rw [mul_comm]; exact hIy)
  have hone : (a + b + c) / p = 1 := by rw [← hp]; exact div_self hp0.ne'
  refine ⟨mul_pos hl0 hr0, ⟨1 - l₁ + l₁ * a / p, l₁ * b / p, l₁ * c / p, ?_, by positivity,
    by positivity, by linear_combination l₁ * hone, ?_⟩, ?_, ?_, ?_⟩
  · have : 0 ≤ l₁ * a / p := by positivity
    linarith
  · apply ext2
    · simp only [xc_add, xc_smul, xc_sub]
      rw [hxI]; ring
    · simp only [yc_add, yc_smul, yc_sub]
      rw [hyI]; ring
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_add, yc_add, xc_smul,
      yc_smul]
    linear_combination h2
  · simp only [TangentToLine, crossProd2_def, ip_two, xc_sub, yc_sub, xc_add, yc_add, xc_smul,
      yc_smul]
    linear_combination h3
  · simp only [ip_two, xc_sub, yc_sub, xc_add, yc_add, xc_smul, yc_smul]
    linear_combination h1

theorem inTriangle_rotate {O A B C : Coord ℝ 2} (h : InTriangle O B C A) : InTriangle O A B C := by
  obtain ⟨l, m, n, hl, hm, hn, hs, rfl⟩ := h
  refine ⟨n, l, m, hn, hl, hm, by linarith, ?_⟩
  apply ext2
  · simp only [xc_add, xc_smul]; ring
  · simp only [yc_add, yc_smul]; ring

/-- **The circles of Malfatti from given points**: if the frame and the vertices of the triangle
`ABC` are among the given points `S`, the centers of the three circles of Malfatti can be
constructed by straight-edge and transferer. -/
theorem malfatti_of_mem {S : Set (Coord ℝ 2)} {A B C : Coord ℝ 2} (hF : frameSet ℝ ⊆ S)
    (hAS : A ∈ S) (hBS : B ∈ S) (hCS : C ∈ S) (hk : crossProd2 (B - A) (C - A) ≠ 0) :
    ∃ (O₁ O₂ O₃ : Coord ℝ 2) (r₁ r₂ r₃ : ℝ), 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
      InTriangle O₁ A B C ∧ InTriangle O₂ A B C ∧ InTriangle O₃ A B C ∧
      TangentToLine O₁ A B r₁ ∧ TangentToLine O₁ A C r₁ ∧
      TangentToLine O₂ B A r₂ ∧ TangentToLine O₂ B C r₂ ∧
      TangentToLine O₃ C A r₃ ∧ TangentToLine O₃ C B r₃ ∧
      ip (O₁ - O₂) (O₁ - O₂) = (r₁ + r₂) ^ 2 ∧ ip (O₂ - O₃) (O₂ - O₃) = (r₂ + r₃) ^ 2 ∧
      ip (O₃ - O₁) (O₃ - O₁) = (r₃ + r₁) ^ 2 ∧
      RulerTransferer S O₁ ∧ RulerTransferer S O₂ ∧ RulerTransferer S O₃ := by
  have hkB : crossProd2 (C - B) (A - B) = crossProd2 (B - A) (C - A) := by
    simp only [crossProd2_def, xc_sub, yc_sub]; ring
  have hkC : crossProd2 (A - C) (B - C) = crossProd2 (B - A) (C - A) := by
    simp only [crossProd2_def, xc_sub, yc_sub]; ring
  -- the numbers obtained from the coordinates of the given points by the five operations
  have hT := pythClosure_closed (coordSet S)
  have mem : ∀ X ∈ S, PythClosure (coordSet S) (xc X) ∧ PythClosure (coordSet S) (yc X) :=
    fun X hX => ⟨.base ⟨X, hX, Or.inl rfl⟩, .base ⟨X, hX, Or.inr rfl⟩⟩
  obtain ⟨hAx, hAy⟩ := mem A hAS
  obtain ⟨hBx, hBy⟩ := mem B hBS
  obtain ⟨hCx, hCy⟩ := mem C hCS
  have h1 : PythClosure (coordSet S) 1 := by
    have := (mem (pt2 1 0) (hF frameSet_mem.2.1)).1
    simpa using this
  have h0 : PythClosure (coordSet S) 0 := by
    have := (mem (pt2 1 0) (hF frameSet_mem.2.1)).2
    simpa using this
  have h2 : PythClosure (coordSet S) 2 := by
    have := hT.add h1 h1
    norm_num at this
    exact this
  -- the sides
  have len : ∀ P Q : Coord ℝ 2, PythClosure (coordSet S) (xc P) → PythClosure (coordSet S) (yc P) →
      PythClosure (coordSet S) (xc Q) → PythClosure (coordSet S) (yc Q) →
      ∃ l : ℝ, 0 ≤ l ∧ l ^ 2 = ip (Q - P) (Q - P) ∧ PythClosure (coordSet S) l := by
    intro P Q hPx hPy hQx hQy
    have hnn : 0 ≤ ip (Q - P) (Q - P) := by
      rw [ip_two]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    refine ⟨Real.sqrt (ip (Q - P) (Q - P)), Real.sqrt_nonneg _, Real.sq_sqrt hnn,
      hT.sqrt (hT.sub hQx hPx) (hT.sub hQy hPy) (Real.sqrt_nonneg _) ?_⟩
    rw [Real.sq_sqrt hnn, ip_two]; simp only [xc_sub, yc_sub]; ring
  obtain ⟨a, ha0, ha, hTa⟩ := len B C hBx hBy hCx hCy
  obtain ⟨b, hb0, hb, hTb⟩ := len C A hCx hCy hAx hAy
  obtain ⟨c, hc0, hc, hTc⟩ := len A B hAx hAy hBx hBy
  -- the sides are positive
  have pos_of : ∀ {P Q : Coord ℝ 2} {l : ℝ}, 0 ≤ l → l ^ 2 = ip (Q - P) (Q - P) → P ≠ Q →
      0 < l := by
    intro P Q l hl0 hl hPQ
    rcases hl0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero, ip_two] at hl
      simp only [xc_sub, yc_sub] at hl
      have e1 : (xc Q - xc P) * (xc Q - xc P) = 0 :=
        le_antisymm (by linarith only [hl, mul_self_nonneg (yc Q - yc P)]) (mul_self_nonneg _)
      have e2 : (yc Q - yc P) * (yc Q - yc P) = 0 :=
        le_antisymm (by linarith only [hl, mul_self_nonneg (xc Q - xc P)]) (mul_self_nonneg _)
      exact hPQ (ext2 (by linarith [mul_self_eq_zero.1 e1]) (by linarith [mul_self_eq_zero.1 e2]))
  have hBC : B ≠ C := by
    rintro rfl
    apply hk; simp only [crossProd2_def]; ring
  have hCA : C ≠ A := by
    rintro rfl
    apply hk; simp only [crossProd2_def, xc_sub, yc_sub]; ring
  have hAB : A ≠ B := by
    rintro rfl
    apply hk; simp only [crossProd2_def, xc_sub, yc_sub]; ring
  have hap := pos_of ha0 ha hBC
  have hbp := pos_of hb0 hb hCA
  have hcp := pos_of hc0 hc hAB
  -- perimeter, inradius, tangent lengths
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = a + b + c := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; positivity
  have hTp : PythClosure (coordSet S) p := by rw [hp]; exact hT.add (hT.add hTa hTb) hTc
  have hTk : PythClosure (coordSet S) (crossProd2 (B - A) (C - A)) := by
    rw [crossProd2_def]; simp only [xc_sub, yc_sub]
    exact hT.sub (hT.mul (hT.sub hBx hAx) (hT.sub hCy hAy))
      (hT.mul (hT.sub hBy hAy) (hT.sub hCx hAx))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = |crossProd2 (B - A) (C - A)| / p := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos (abs_pos.2 hk) hp0
  have hTr : PythClosure (coordSet S) r := by rw [hr]; exact hT.div (hT.abs hTk) hTp hp0.ne'
  have hrk : (r * p) ^ 2 = crossProd2 (B - A) (C - A) ^ 2 := by
    rw [hr, div_mul_cancel₀ _ hp0.ne', sq_abs]
  have hTs : PythClosure (coordSet S) (p / 2) := hT.div hTp h2 two_ne_zero
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = p / 2 - a := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = p / 2 - b := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = p / 2 - c := ⟨_, rfl⟩
  have hTx : PythClosure (coordSet S) x := by rw [hx]; exact hT.sub hTs hTa
  have hTy : PythClosure (coordSet S) y := by rw [hy]; exact hT.sub hTs hTb
  have hTz : PythClosure (coordSet S) z := by rw [hz]; exact hT.sub hTs hTc
  -- the distances from the incenter to the vertices
  have hyp : ∀ w : ℝ, PythClosure (coordSet S) w →
      ∃ h : ℝ, 0 < h ∧ h ^ 2 = r ^ 2 + w ^ 2 ∧ PythClosure (coordSet S) h := by
    intro w hw
    have hnn : 0 < r ^ 2 + w ^ 2 := by positivity
    exact ⟨Real.sqrt (r ^ 2 + w ^ 2), Real.sqrt_pos.2 hnn, Real.sq_sqrt hnn.le,
      hT.sqrt hTr hw (Real.sqrt_nonneg _) (Real.sq_sqrt hnn.le)⟩
  obtain ⟨d, hd0, hd, hTd⟩ := hyp x hTx
  obtain ⟨e, he0, he, hTe⟩ := hyp y hTy
  obtain ⟨f, hf0, hf, hTf⟩ := hyp z hTz
  obtain ⟨t₁, ht₁⟩ : ∃ t : ℝ, t = (p / 2 + d - r - e - f) / 2 := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t : ℝ, t = (p / 2 + e - r - f - d) / 2 := ⟨_, rfl⟩
  obtain ⟨t₃, ht₃⟩ : ∃ t : ℝ, t = (p / 2 + f - r - d - e) / 2 := ⟨_, rfl⟩
  have hTt₁ : PythClosure (coordSet S) t₁ := by
    rw [ht₁]
    exact hT.div (hT.sub (hT.sub (hT.sub (hT.add hTs hTd) hTr) hTe) hTf) h2 two_ne_zero
  have hTt₂ : PythClosure (coordSet S) t₂ := by
    rw [ht₂]
    exact hT.div (hT.sub (hT.sub (hT.sub (hT.add hTs hTe) hTr) hTf) hTd) h2 two_ne_zero
  have hTt₃ : PythClosure (coordSet S) t₃ := by
    rw [ht₃]
    exact hT.div (hT.sub (hT.sub (hT.sub (hT.add hTs hTf) hTr) hTd) hTe) h2 two_ne_zero
  -- the incenter
  obtain ⟨I, hI⟩ : ∃ I : Coord ℝ 2, I = pt2 ((a * xc A + b * xc B + c * xc C) / p)
      ((a * yc A + b * yc B + c * yc C) / p) := ⟨_, rfl⟩
  have hIx : p * xc I = a * xc A + b * xc B + c * xc C := by
    rw [hI, xc_pt2, mul_comm]; exact div_mul_cancel₀ _ hp0.ne'
  have hIy : p * yc I = a * yc A + b * yc B + c * yc C := by
    rw [hI, yc_pt2, mul_comm]; exact div_mul_cancel₀ _ hp0.ne'
  have hTIx : PythClosure (coordSet S) (xc I) := by
    rw [hI, xc_pt2]
    exact hT.div (hT.add (hT.add (hT.mul hTa hAx) (hT.mul hTb hBx)) (hT.mul hTc hCx)) hTp hp0.ne'
  have hTIy : PythClosure (coordSet S) (yc I) := by
    rw [hI, yc_pt2]
    exact hT.div (hT.add (hT.add (hT.mul hTa hAy) (hT.mul hTb hBy)) (hT.mul hTc hCy)) hTp hp0.ne'
  -- the three circles
  obtain ⟨hr1, hin1, hA1, hA2, h12⟩ := malfatti_vertex (I := I) ha0 hb0 hc0 ha hb hc hk hp hIx hIy
    hr0 hrk hx hy hz hd0 hd he0 he hf0 hf (t₁ := t₁) (t₂ := t₂) (by rw [ht₁]; ring)
    (by rw [ht₂]; ring)
  obtain ⟨hr2, hin2, hB1, hB2, h23⟩ := malfatti_vertex (A := B) (B := C) (C := A) (I := I)
    hb0 hc0 ha0 hb hc ha (by rw [hkB]; exact hk) (by rw [hp]; ring)
    (by rw [hIx]; ring) (by rw [hIy]; ring) hr0 (by rw [hkB]; exact hrk) hy hz hx he0 he hf0 hf
    hd0 hd (t₁ := t₂) (t₂ := t₃) (by rw [ht₂]; ring) (by rw [ht₃]; ring)
  obtain ⟨hr3, hin3, hC1, hC2, h31⟩ := malfatti_vertex (A := C) (B := A) (C := B) (I := I)
    hc0 ha0 hb0 hc ha hb (by rw [hkC]; exact hk) (by rw [hp]; ring)
    (by rw [hIx]; ring) (by rw [hIy]; ring) hr0 (by rw [hkC]; exact hrk) hz hx hy hf0 hf hd0 hd
    he0 he (t₁ := t₃) (t₂ := t₁) (by rw [ht₃]; ring) (by rw [ht₁]; ring)
  -- the centers are constructible
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [div_zero, zero_mul] at hr1
    exact lt_irrefl _ hr1
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [div_zero, zero_mul] at hr2
    exact lt_irrefl _ hr2
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [div_zero, zero_mul] at hr3
    exact lt_irrefl _ hr3
  have cen : ∀ (P : Coord ℝ 2) (l : ℝ), PythClosure (coordSet S) (xc P) →
      PythClosure (coordSet S) (yc P) → PythClosure (coordSet S) l →
      RulerTransferer S (P + l • (I - P)) := by
    intro P l hPx hPy hl
    rw [theorem41 hF]
    simp only [xc_add, yc_add, xc_smul, yc_smul, xc_sub, yc_sub]
    exact ⟨hT.add hPx (hT.mul hl (hT.sub hTIx hPx)), hT.add hPy (hT.mul hl (hT.sub hTIy hPy))⟩
  exact ⟨A + (t₁ / x) • (I - A), B + (t₂ / y) • (I - B), C + (t₃ / z) • (I - C),
    t₁ / x * r, t₂ / y * r, t₃ / z * r, hr1, hr2, hr3, hin1, inTriangle_rotate hin2,
    inTriangle_rotate (inTriangle_rotate hin3), hA1, hA2, hB2, hB1, hC1, hC2, h12, h23, h31,
    cen A _ hAx hAy (hT.div hTt₁ hTx hx0), cen B _ hBx hBy (hT.div hTt₂ hTy hy0),
    cen C _ hCx hCy (hT.div hTt₃ hTz hz0)⟩

/-- **The problem of Malfatti** (`MalfattiClaim`): the three circles of Malfatti of every triangle
can be constructed by straight-edge and transferer. -/
theorem malfattiClaim_aux : MalfattiClaim := by
  intro A B C hncol
  have hk : crossProd2 (B - A) (C - A) ≠ 0 := by
    intro h0
    by_cases hAB : A = B
    · subst hAB; exact hncol (collinear_self_left A C)
    · exact hncol ((collinear_iff_cross hAB).2 h0)
  exact malfatti_of_mem (S := frameSet ℝ ∪ {A, B, C}) Set.subset_union_left
    (Set.mem_union_right _ (by simp)) (Set.mem_union_right _ (by simp))
    (Set.mem_union_right _ (by simp)) hk

end HilbertFoundations
