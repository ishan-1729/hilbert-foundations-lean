import HilbertFoundations.Proportion

/-!
# Helper module for `Areas.lean`: triangles in the co-ordinate plane over an ordered field

This module contains no unit of Hilbert's text. It is pure algebra over a linearly ordered field
`K` (in `Areas.lean`, `K` is the field of segments `Pas.G ax` of a plane geometry with the axioms
I 1–2, II, III, IV, and points are replaced by their co-ordinates).

* `det3 a b c`: the cross product `(b - a) × (c - a)` (twice the signed area).
* `Tr K`: a triple of points; `Tr.mem t p` (closed triangle), `Tr.int t p` (interior),
  `Tr.nd t` (non-degenerate). Membership is expressed by the signs of the three cross products,
  equivalently by barycentric co-ordinates (`Tr.mem_iff_bary`, `Tr.int_iff_bary`).
* Convexity, the interior of a sub-triangle lies in the interior (`int_of_sub`), the centroid, an
  interior point of one triangle lying in another gives a common interior point (`int_meet`),
  and the **closure lemma** (`mem_cover_of_int_cover`): a finite family of triangles covering the
  interior of a triangle covers the triangle.
* **Decompositions** `DecS S l` (finitely many non-degenerate triangles with pairwise disjoint
  interiors whose union is `S`), the **transversal decomposition** (`split`), the **cut** of a
  triangle by a straight line into triangles lying on either side of it (`cut1`, `cutAll`), and
  the **common refinement** (`refine_sub`): cutting a triangle by the side lines of a
  decomposition gives pieces each lying in a triangle of that decomposition.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Areas

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cross product `(b - a) × (c - a)`. -/
def det3 (a b c : K × K) : K := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

theorem det3_cyc (a b c : K × K) : det3 b c a = det3 a b c := by unfold det3; ring

theorem det3_swap (a b c : K × K) : det3 b a c = -det3 a b c := by unfold det3; ring

theorem det3_sum (a b c p : K × K) : det3 b c p + det3 c a p + det3 a b p = det3 a b c := by
  unfold det3; ring

/-- The point `α a + β b + γ c`. -/
def comb (α β γ : K) (a b c : K × K) : K × K :=
  (α * a.1 + β * b.1 + γ * c.1, α * a.2 + β * b.2 + γ * c.2)

/-- `det3 u v` is affine in its last argument. -/
theorem det3_comb (u v : K × K) {α β γ : K} (h : α + β + γ = 1) (a b c : K × K) :
    det3 u v (comb α β γ a b c) = α * det3 u v a + β * det3 u v b + γ * det3 u v c := by
  have hγ : γ = 1 - α - β := by linear_combination h
  subst hγ; unfold det3 comb; ring

/-- The point `p + s (q - p)`. -/
def lerp (s : K) (p q : K × K) : K × K := (p.1 + s * (q.1 - p.1), p.2 + s * (q.2 - p.2))

theorem det3_lerp (u v : K × K) (s : K) (p q : K × K) :
    det3 u v (lerp s p q) = (1 - s) * det3 u v p + s * det3 u v q := by
  unfold det3 lerp; ring

/-- Barycentric reconstruction: `D p = λ_a a + λ_b b + λ_c c` (scaled by `D`). -/
theorem det3_recon (a b c p : K × K) :
    det3 a b c * p.1 = det3 b c p * a.1 + det3 c a p * b.1 + det3 a b p * c.1 ∧
      det3 a b c * p.2 = det3 b c p * a.2 + det3 c a p * b.2 + det3 a b p * c.2 := by
  unfold det3; constructor <;> ring

/-- Three points on the line `bc` (with `b ≠ c`) are collinear. -/
theorem det3_eq_zero_of_line {b c x y z : K × K} (hbc : b ≠ c) (hx : det3 b c x = 0)
    (hy : det3 b c y = 0) (hz : det3 b c z = 0) : det3 x y z = 0 := by
  have e1 : (c.1 - b.1) * det3 x y z =
      (y.1 - x.1) * (det3 b c z - det3 b c x) - (z.1 - x.1) * (det3 b c y - det3 b c x) := by
    unfold det3; ring
  have e2 : (c.2 - b.2) * det3 x y z =
      (y.2 - x.2) * (det3 b c z - det3 b c x) - (z.2 - x.2) * (det3 b c y - det3 b c x) := by
    unfold det3; ring
  rw [hx, hy, hz] at e1 e2
  simp only [sub_self, mul_zero] at e1 e2
  by_contra hne
  apply hbc
  have h1 : c.1 - b.1 = 0 := by
    rcases mul_eq_zero.1 e1 with h | h
    · exact h
    · exact absurd h hne
  have h2 : c.2 - b.2 = 0 := by
    rcases mul_eq_zero.1 e2 with h | h
    · exact h
    · exact absurd h hne
  exact Prod.ext (by linarith) (by linarith)

/-- A triangle: a triple of points of the co-ordinate plane. -/
@[ext]
structure Tr (K : Type*) where
  a : K × K
  b : K × K
  c : K × K

namespace Tr

/-- Twice the signed area. -/
def D (t : Tr K) : K := det3 t.a t.b t.c

/-- The triangle is non-degenerate (its vertices are not collinear). -/
def nd (t : Tr K) : Prop := t.D ≠ 0

/-- The closed triangle. -/
def mem (t : Tr K) (p : K × K) : Prop :=
  0 ≤ t.D * det3 t.b t.c p ∧ 0 ≤ t.D * det3 t.c t.a p ∧ 0 ≤ t.D * det3 t.a t.b p

/-- The interior of the triangle. -/
def int (t : Tr K) (p : K × K) : Prop :=
  0 < t.D * det3 t.b t.c p ∧ 0 < t.D * det3 t.c t.a p ∧ 0 < t.D * det3 t.a t.b p

theorem mem_of_int {t : Tr K} {p : K × K} (h : t.int p) : t.mem p :=
  ⟨h.1.le, h.2.1.le, h.2.2.le⟩

/-- The rotated triangle `bca`. -/
def rot (t : Tr K) : Tr K := ⟨t.b, t.c, t.a⟩

/-- The reflected triangle `bac`. -/
def swap (t : Tr K) : Tr K := ⟨t.b, t.a, t.c⟩

theorem D_rot (t : Tr K) : t.rot.D = t.D := det3_cyc _ _ _

theorem D_swap (t : Tr K) : t.swap.D = -t.D := det3_swap _ _ _

theorem nd_rot {t : Tr K} : t.rot.nd ↔ t.nd := by unfold nd; rw [D_rot]

theorem nd_swap {t : Tr K} : t.swap.nd ↔ t.nd := by unfold nd; rw [D_swap, neg_ne_zero]

theorem mem_rot {t : Tr K} {p : K × K} : t.rot.mem p ↔ t.mem p := by
  unfold mem rot D; simp only
  rw [det3_cyc t.a t.b t.c]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, h1⟩

theorem int_rot {t : Tr K} {p : K × K} : t.rot.int p ↔ t.int p := by
  unfold int rot D; simp only
  rw [det3_cyc t.a t.b t.c]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, h1⟩

theorem mem_swap {t : Tr K} {p : K × K} : t.swap.mem p ↔ t.mem p := by
  unfold mem swap D; simp only
  rw [det3_swap t.a t.b t.c, det3_swap t.c t.b p, det3_swap t.a t.c p, det3_swap t.b t.a p]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem int_swap {t : Tr K} {p : K × K} : t.swap.int p ↔ t.int p := by
  unfold int swap D; simp only
  rw [det3_swap t.a t.b t.c, det3_swap t.c t.b p, det3_swap t.a t.c p, det3_swap t.b t.a p]
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The barycentric co-ordinate of `p` with respect to the vertex `a`. -/
def la (t : Tr K) (p : K × K) : K := det3 t.b t.c p / t.D
/-- The barycentric co-ordinate of `p` with respect to the vertex `b`. -/
def lb (t : Tr K) (p : K × K) : K := det3 t.c t.a p / t.D
/-- The barycentric co-ordinate of `p` with respect to the vertex `c`. -/
def lc (t : Tr K) (p : K × K) : K := det3 t.a t.b p / t.D

theorem nonneg_div_iff {D x : K} (hD : D ≠ 0) : 0 ≤ D * x ↔ 0 ≤ x / D := by
  have : x / D = (D * x) / (D * D) := by field_simp
  rw [this]
  constructor
  · intro h; exact div_nonneg h (mul_self_nonneg D)
  · intro h
    have hp : 0 < D * D := mul_self_pos.2 hD
    have := mul_nonneg h hp.le
    rwa [div_mul_cancel₀ _ hp.ne'] at this

theorem pos_div_iff {D x : K} (hD : D ≠ 0) : 0 < D * x ↔ 0 < x / D := by
  have : x / D = (D * x) / (D * D) := by field_simp
  rw [this]
  have hp : 0 < D * D := mul_self_pos.2 hD
  constructor
  · intro h; exact div_pos h hp
  · intro h
    have := mul_pos h hp
    rwa [div_mul_cancel₀ _ hp.ne'] at this

theorem mem_iff_l {t : Tr K} (ht : t.nd) {p : K × K} :
    t.mem p ↔ 0 ≤ t.la p ∧ 0 ≤ t.lb p ∧ 0 ≤ t.lc p := by
  unfold mem la lb lc
  rw [nonneg_div_iff ht, nonneg_div_iff ht, nonneg_div_iff ht]

theorem int_iff_l {t : Tr K} (ht : t.nd) {p : K × K} :
    t.int p ↔ 0 < t.la p ∧ 0 < t.lb p ∧ 0 < t.lc p := by
  unfold int la lb lc
  rw [pos_div_iff ht, pos_div_iff ht, pos_div_iff ht]

theorem l_sum {t : Tr K} (ht : t.nd) (p : K × K) : t.la p + t.lb p + t.lc p = 1 := by
  unfold la lb lc
  rw [← add_div, ← add_div, det3_sum]
  exact div_self ht

theorem l_recon {t : Tr K} (ht : t.nd) (p : K × K) : p = comb (t.la p) (t.lb p) (t.lc p) t.a t.b t.c := by
  obtain ⟨e1, e2⟩ := det3_recon t.a t.b t.c p
  unfold la lb lc comb
  have hD : t.D ≠ 0 := ht
  change t.D * p.1 = _ at e1
  change t.D * p.2 = _ at e2
  ext
  · simp only; field_simp; linear_combination e1
  · simp only; field_simp; linear_combination e2

/-- `la`, `lb`, `lc` are affine. -/
theorem la_comb (t : Tr K) {α β γ : K} (h : α + β + γ = 1) (x y z : K × K) :
    t.la (comb α β γ x y z) = α * t.la x + β * t.la y + γ * t.la z := by
  unfold la; rw [det3_comb _ _ h]; ring

theorem lb_comb (t : Tr K) {α β γ : K} (h : α + β + γ = 1) (x y z : K × K) :
    t.lb (comb α β γ x y z) = α * t.lb x + β * t.lb y + γ * t.lb z := by
  unfold lb; rw [det3_comb _ _ h]; ring

theorem lc_comb (t : Tr K) {α β γ : K} (h : α + β + γ = 1) (x y z : K × K) :
    t.lc (comb α β γ x y z) = α * t.lc x + β * t.lc y + γ * t.lc z := by
  unfold lc; rw [det3_comb _ _ h]; ring

theorem la_lerp (t : Tr K) (s : K) (p q : K × K) :
    t.la (lerp s p q) = (1 - s) * t.la p + s * t.la q := by
  unfold la; rw [det3_lerp]; ring

theorem lb_lerp (t : Tr K) (s : K) (p q : K × K) :
    t.lb (lerp s p q) = (1 - s) * t.lb p + s * t.lb q := by
  unfold lb; rw [det3_lerp]; ring

theorem lc_lerp (t : Tr K) (s : K) (p q : K × K) :
    t.lc (lerp s p q) = (1 - s) * t.lc p + s * t.lc q := by
  unfold lc; rw [det3_lerp]; ring

theorem la_a {t : Tr K} (ht : t.nd) : t.la t.a = 1 := by
  unfold la; rw [show det3 t.b t.c t.a = t.D by unfold Tr.D det3; ring]; exact div_self ht
theorem lb_a (t : Tr K) : t.lb t.a = 0 := by
  unfold lb; rw [show det3 t.c t.a t.a = 0 by unfold det3; ring, zero_div]
theorem lc_a (t : Tr K) : t.lc t.a = 0 := by
  unfold lc; rw [show det3 t.a t.b t.a = 0 by unfold det3; ring, zero_div]
theorem la_b (t : Tr K) : t.la t.b = 0 := by
  unfold la; rw [show det3 t.b t.c t.b = 0 by unfold det3; ring, zero_div]
theorem lb_b {t : Tr K} (ht : t.nd) : t.lb t.b = 1 := by
  unfold lb; rw [show det3 t.c t.a t.b = t.D by unfold Tr.D det3; ring]; exact div_self ht
theorem lc_b (t : Tr K) : t.lc t.b = 0 := by
  unfold lc; rw [show det3 t.a t.b t.b = 0 by unfold det3; ring, zero_div]
theorem la_c (t : Tr K) : t.la t.c = 0 := by
  unfold la; rw [show det3 t.b t.c t.c = 0 by unfold det3; ring, zero_div]
theorem lb_c (t : Tr K) : t.lb t.c = 0 := by
  unfold lb; rw [show det3 t.c t.a t.c = 0 by unfold det3; ring, zero_div]
theorem lc_c {t : Tr K} (ht : t.nd) : t.lc t.c = 1 := by unfold lc; exact div_self ht

/-- Barycentric description of the closed triangle. -/
theorem mem_iff_bary {t : Tr K} (ht : t.nd) {p : K × K} :
    t.mem p ↔ ∃ α β γ : K, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ p = comb α β γ t.a t.b t.c := by
  rw [mem_iff_l ht]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, _, _, h1, h2, h3, l_sum ht p, l_recon ht p⟩
  · rintro ⟨α, β, γ, h1, h2, h3, hs, rfl⟩
    rw [la_comb t hs, lb_comb t hs, lc_comb t hs, la_a ht, la_b, la_c, lb_a, lb_b ht, lb_c, lc_a,
      lc_b, lc_c ht]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> assumption

/-- Barycentric description of the interior. -/
theorem int_iff_bary {t : Tr K} (ht : t.nd) {p : K × K} :
    t.int p ↔ ∃ α β γ : K, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ p = comb α β γ t.a t.b t.c := by
  rw [int_iff_l ht]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, _, _, h1, h2, h3, l_sum ht p, l_recon ht p⟩
  · rintro ⟨α, β, γ, h1, h2, h3, hs, rfl⟩
    rw [la_comb t hs, lb_comb t hs, lc_comb t hs, la_a ht, la_b, la_c, lb_a, lb_b ht, lb_c, lc_a,
      lc_b, lc_c ht]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> assumption

theorem mem_a {t : Tr K} (ht : t.nd) : t.mem t.a := by
  rw [mem_iff_l ht, la_a ht, lb_a, lc_a]; norm_num
theorem mem_b {t : Tr K} (ht : t.nd) : t.mem t.b := by
  rw [mem_iff_l ht, la_b, lb_b ht, lc_b]; norm_num
theorem mem_c {t : Tr K} (ht : t.nd) : t.mem t.c := by
  rw [mem_iff_l ht, la_c, lb_c, lc_c ht]; norm_num

/-- The centroid. -/
def cen (t : Tr K) : K × K := comb (1 / 3) (1 / 3) (1 / 3) t.a t.b t.c

theorem int_cen {t : Tr K} (ht : t.nd) : t.int t.cen :=
  (int_iff_bary ht).2 ⟨1 / 3, 1 / 3, 1 / 3, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩

theorem la_cen {t : Tr K} (ht : t.nd) : t.la t.cen = 1 / 3 := by
  unfold cen; rw [la_comb t (by norm_num), la_a ht, la_b, la_c]; ring
theorem lb_cen {t : Tr K} (ht : t.nd) : t.lb t.cen = 1 / 3 := by
  unfold cen; rw [lb_comb t (by norm_num), lb_a, lb_b ht, lb_c]; ring
theorem lc_cen {t : Tr K} (ht : t.nd) : t.lc t.cen = 1 / 3 := by
  unfold cen; rw [lc_comb t (by norm_num), lc_a, lc_b, lc_c ht]; ring

/-- `t` is contained in `s` as soon as its vertices are (convexity). -/
theorem sub_of_vertices {t s : Tr K} (ht : t.nd) (hs : s.nd) (ha : s.mem t.a) (hb : s.mem t.b)
    (hc : s.mem t.c) {p : K × K} (hp : t.mem p) : s.mem p := by
  obtain ⟨α, β, γ, h1, h2, h3, hsum, rfl⟩ := (mem_iff_bary ht).1 hp
  rw [mem_iff_l hs] at ha hb hc ⊢
  rw [la_comb s hsum, lb_comb s hsum, lc_comb s hsum]
  refine ⟨?_, ?_, ?_⟩
  · have := mul_nonneg h1 ha.1; have := mul_nonneg h2 hb.1; have := mul_nonneg h3 hc.1; linarith
  · have := mul_nonneg h1 ha.2.1; have := mul_nonneg h2 hb.2.1; have := mul_nonneg h3 hc.2.1
    linarith
  · have := mul_nonneg h1 ha.2.2; have := mul_nonneg h2 hb.2.2; have := mul_nonneg h3 hc.2.2
    linarith

/-- If a non-degenerate triangle `t` lies in `s`, its interior lies in the interior of `s`. -/
theorem int_of_sub {t s : Tr K} (ht : t.nd) (hs : s.nd) (hsub : ∀ p, t.mem p → s.mem p)
    {p : K × K} (hp : t.int p) : s.int p := by
  obtain ⟨α, β, γ, h1, h2, h3, hsum, rfl⟩ := (int_iff_bary ht).1 hp
  have ha := (mem_iff_l hs).1 (hsub _ (mem_a ht))
  have hb := (mem_iff_l hs).1 (hsub _ (mem_b ht))
  have hc := (mem_iff_l hs).1 (hsub _ (mem_c ht))
  rw [int_iff_l hs, la_comb s hsum, lb_comb s hsum, lc_comb s hsum]
  -- a barycentric co-ordinate of `s` vanishing at the three vertices of `t` makes `t` degenerate
  have key : ∀ (f : K × K → K) (u v : K × K), u ≠ v → (∀ x, f x = det3 u v x / s.D) →
      0 ≤ f t.a → 0 ≤ f t.b → 0 ≤ f t.c → 0 < α * f t.a + β * f t.b + γ * f t.c := by
    intro f u v huv hf fa fb fc
    by_contra hneg
    push Not at hneg
    have e1 : α * f t.a = 0 := by
      have := mul_nonneg h1.le fa; have := mul_nonneg h2.le fb; have := mul_nonneg h3.le fc
      linarith
    have e2 : β * f t.b = 0 := by
      have := mul_nonneg h1.le fa; have := mul_nonneg h2.le fb; have := mul_nonneg h3.le fc
      linarith
    have e3 : γ * f t.c = 0 := by
      have := mul_nonneg h1.le fa; have := mul_nonneg h2.le fb; have := mul_nonneg h3.le fc
      linarith
    have z1 : det3 u v t.a = 0 := by
      have := (mul_eq_zero.1 e1).resolve_left h1.ne'
      rw [hf, div_eq_zero_iff] at this; exact this.resolve_right hs
    have z2 : det3 u v t.b = 0 := by
      have := (mul_eq_zero.1 e2).resolve_left h2.ne'
      rw [hf, div_eq_zero_iff] at this; exact this.resolve_right hs
    have z3 : det3 u v t.c = 0 := by
      have := (mul_eq_zero.1 e3).resolve_left h3.ne'
      rw [hf, div_eq_zero_iff] at this; exact this.resolve_right hs
    exact ht (det3_eq_zero_of_line huv z1 z2 z3)
  have hsD : s.D ≠ 0 := hs
  have nbc : s.b ≠ s.c := by
    intro e; apply hsD; unfold D det3; rw [e]; ring
  have nca : s.c ≠ s.a := by
    intro e; apply hsD; unfold D det3; rw [e]; ring
  have nab : s.a ≠ s.b := by
    intro e; apply hsD; unfold D det3; rw [e]; ring
  exact ⟨key s.la s.b s.c nbc (fun _ => rfl) ha.1 hb.1 hc.1,
    key s.lb s.c s.a nca (fun _ => rfl) ha.2.1 hb.2.1 hc.2.1,
    key s.lc s.a s.b nab (fun _ => rfl) ha.2.2 hb.2.2 hc.2.2⟩

theorem nd_ne_ab {t : Tr K} (ht : t.nd) : t.a ≠ t.b := by
  intro e; apply ht; unfold D det3; rw [e]; ring
theorem nd_ne_bc {t : Tr K} (ht : t.nd) : t.b ≠ t.c := by
  intro e; apply ht; unfold D det3; rw [e]; ring
theorem nd_ne_ca {t : Tr K} (ht : t.nd) : t.c ≠ t.a := by
  intro e; apply ht; unfold D det3; rw [e]; ring

end Tr

/-! ### Small positive parameters -/

theorem small_pos {u : K} (v : K) (hu : 0 < u) :
    ∃ ε : K, 0 < ε ∧ ∀ s : K, 0 < s → s < ε → 0 < (1 - s) * u + s * v := by
  refine ⟨u / (u + |v| + 1), div_pos hu (by positivity), fun s hs hsε => ?_⟩
  have hd : 0 < u + |v| + 1 := by positivity
  have h1 : s * (u + |v| + 1) < u := by rwa [lt_div_iff₀ hd] at hsε
  have h2 : -|v| ≤ v := neg_abs_le v
  nlinarith [abs_nonneg v]

theorem small_neg {u : K} (v : K) (hu : u < 0) :
    ∃ ε : K, 0 < ε ∧ ∀ s : K, 0 < s → s < ε → (1 - s) * u + s * v < 0 := by
  obtain ⟨ε, hε, h⟩ := small_pos (-v) (neg_pos.2 hu)
  exact ⟨ε, hε, fun s h1 h2 => by have := h s h1 h2; linarith⟩

/-- A common small parameter for finitely many conditions. -/
theorem eps_list {α : Type*} (R : List α) (Q : α → K → Prop)
    (h : ∀ r ∈ R, ∃ ε : K, 0 < ε ∧ ∀ s, 0 < s → s < ε → Q r s) :
    ∃ ε : K, 0 < ε ∧ ∀ r ∈ R, ∀ s, 0 < s → s < ε → Q r s := by
  induction R with
  | nil => exact ⟨1, one_pos, fun r hr => absurd hr List.not_mem_nil⟩
  | cons r R ih =>
    obtain ⟨ε1, h1, k1⟩ := h r List.mem_cons_self
    obtain ⟨ε2, h2, k2⟩ := ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    refine ⟨min ε1 ε2, lt_min h1 h2, fun r' hr' s hs hsε => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact k1 s hs (lt_of_lt_of_le hsε (min_le_left _ _))
    · exact k2 r' hr' s hs (lt_of_lt_of_le hsε (min_le_right _ _))

namespace Tr

/-- **Interior meets closed triangle ⇒ interiors meet.** -/
theorem int_meet {t s : Tr K} (ht : t.nd) (hs : s.nd) {p : K × K} (hp : t.int p) (hp' : s.mem p) :
    ∃ q, t.int q ∧ s.int q := by
  rw [int_iff_l ht] at hp
  rw [mem_iff_l hs] at hp'
  obtain ⟨ε, hε, hall⟩ := eps_list [t.la, t.lb, t.lc]
    (fun f s' => 0 < (1 - s') * f p + s' * f s.cen) (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact small_pos _ hp.1
      · exact small_pos _ hp.2.1
      · exact small_pos _ hp.2.2)
  set s0 := min (ε / 2) (1 / 2) with hs0
  have hs0p : 0 < s0 := lt_min (half_pos hε) (by norm_num)
  have hs0ε : s0 < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hs01 : s0 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨lerp s0 p s.cen, ?_, ?_⟩
  · rw [int_iff_l ht, la_lerp, lb_lerp, lc_lerp]
    exact ⟨hall t.la (by simp) s0 hs0p hs0ε, hall t.lb (by simp) s0 hs0p hs0ε,
      hall t.lc (by simp) s0 hs0p hs0ε⟩
  · rw [int_iff_l hs, la_lerp, lb_lerp, lc_lerp, la_cen hs, lb_cen hs, lc_cen hs]
    have h1 : 0 < 1 - s0 := by linarith
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg h1.le hp'.1, mul_nonneg h1.le hp'.2.1,
      mul_nonneg h1.le hp'.2.2]

/-- **Closure lemma**: finitely many triangles covering the interior of a non-degenerate triangle
cover the whole triangle. -/
theorem mem_cover_of_int_cover {t : Tr K} (ht : t.nd) (R : List (Tr K))
    (hcov : ∀ p, t.int p → ∃ r ∈ R, r.mem p) {p : K × K} (hp : t.mem p) : ∃ r ∈ R, r.mem p := by
  by_contra hno
  push Not at hno
  -- every triangle of `R` misses the points `p + s (g - p)` for small `s > 0`
  have key : ∀ r ∈ R, ∃ ε : K, 0 < ε ∧ ∀ s, 0 < s → s < ε → ¬r.mem (lerp s p t.cen) := by
    intro r hr
    have hnr := hno r hr
    unfold mem at hnr ⊢
    simp only [not_and_or, not_le] at hnr ⊢
    rcases hnr with h | h | h
    · obtain ⟨ε, hε, k⟩ := small_neg (r.D * det3 r.b r.c t.cen) h
      refine ⟨ε, hε, fun s h1 h2 => Or.inl ?_⟩
      rw [det3_lerp]; have := k s h1 h2; linarith
    · obtain ⟨ε, hε, k⟩ := small_neg (r.D * det3 r.c r.a t.cen) h
      refine ⟨ε, hε, fun s h1 h2 => Or.inr (Or.inl ?_)⟩
      rw [det3_lerp]; have := k s h1 h2; linarith
    · obtain ⟨ε, hε, k⟩ := small_neg (r.D * det3 r.a r.b t.cen) h
      refine ⟨ε, hε, fun s h1 h2 => Or.inr (Or.inr ?_)⟩
      rw [det3_lerp]; have := k s h1 h2; linarith
  obtain ⟨ε, hε, hall⟩ := eps_list R (fun r s => ¬r.mem (lerp s p t.cen)) key
  set s0 := min (ε / 2) (1 / 2)
  have hs0p : 0 < s0 := lt_min (half_pos hε) (by norm_num)
  have hs0ε : s0 < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hs01 : s0 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hint : t.int (lerp s0 p t.cen) := by
    rw [mem_iff_l ht] at hp
    rw [int_iff_l ht, la_lerp, lb_lerp, lc_lerp, la_cen ht, lb_cen ht, lc_cen ht]
    have h1 : 0 < 1 - s0 := by linarith
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg h1.le hp.1, mul_nonneg h1.le hp.2.1,
      mul_nonneg h1.le hp.2.2]
  obtain ⟨r, hr, hmem⟩ := hcov _ hint
  exact hall r hr s0 hs0p hs0ε hmem

end Tr

/-! ### Decompositions -/

/-- `l` is a **decomposition** of the region `S`: non-degenerate triangles with pairwise disjoint
interiors whose union is `S`. -/
def DecS (S : K × K → Prop) (l : List (Tr K)) : Prop :=
  (∀ r ∈ l, r.nd) ∧ l.Pairwise (fun r s => ∀ p, ¬(r.int p ∧ s.int p)) ∧
    ∀ p, S p ↔ ∃ r ∈ l, r.mem p

theorem DecS.single {t : Tr K} (ht : t.nd) : DecS t.mem [t] := by
  refine ⟨by simpa using ht, List.pairwise_singleton _ _, fun p => ?_⟩
  simp

theorem DecS.congr {S S' : K × K → Prop} (h : ∀ p, S p ↔ S' p) {l : List (Tr K)} (hl : DecS S l) :
    DecS S' l :=
  ⟨hl.1, hl.2.1, fun p => (h p).symm.trans (hl.2.2 p)⟩

theorem DecS.sub {S : K × K → Prop} {l : List (Tr K)} (hl : DecS S l) {r : Tr K} (hr : r ∈ l)
    {p : K × K} (hp : r.mem p) : S p :=
  (hl.2.2 p).2 ⟨r, hr, hp⟩

/-- Refining every triangle of a decomposition gives a decomposition. -/
theorem DecS.flatMap {S : K × K → Prop} {l : List (Tr K)} (hl : DecS S l) (g : Tr K → List (Tr K))
    (hg : ∀ r ∈ l, DecS r.mem (g r)) : DecS S (l.flatMap g) := by
  obtain ⟨hnd, hpw, hun⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 hq
    exact (hg r hr).1 q hq
  · rw [List.pairwise_flatMap]
    refine ⟨fun r hr => (hg r hr).2.1, ?_⟩
    refine hpw.imp_of_mem (fun {r s} hr hs hrs => ?_)
    intro q hq q' hq' p ⟨h1, h2⟩
    have i1 := Tr.int_of_sub ((hg r hr).1 q hq) (hnd r hr)
      (fun x hx => ((hg r hr).2.2 x).2 ⟨q, hq, hx⟩) h1
    have i2 := Tr.int_of_sub ((hg s hs).1 q' hq') (hnd s hs)
      (fun x hx => ((hg s hs).2.2 x).2 ⟨q', hq', hx⟩) h2
    exact hrs p ⟨i1, i2⟩
  · intro p
    rw [hun p]
    constructor
    · rintro ⟨r, hr, hp⟩
      obtain ⟨q, hq, hqp⟩ := ((hg r hr).2.2 p).1 hp
      exact ⟨q, List.mem_flatMap.2 ⟨r, hr, hq⟩, hqp⟩
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 hq
      exact ⟨r, hr, ((hg r hr).2.2 p).2 ⟨q, hq, hqp⟩⟩

/-! ### The transversal decomposition -/

/-- **Transversal decomposition**: for `x = b + s (c - b)` with `0 < s < 1`, the triangle `abc` is
decomposed into `abx` and `axc`. -/
theorem split {t : Tr K} (ht : t.nd) {s : K} (hs0 : 0 < s) (hs1 : s < 1) :
    DecS t.mem [⟨t.a, t.b, lerp s t.b t.c⟩, ⟨t.a, lerp s t.b t.c, t.c⟩] := by
  set x := lerp s t.b t.c with hx
  have hD : t.D ≠ 0 := ht
  -- the relevant cross products
  have d1 : det3 t.a t.b x = s * t.D := by rw [hx]; unfold Tr.D det3 lerp; ring
  have d2 : det3 t.a x t.c = (1 - s) * t.D := by rw [hx]; unfold Tr.D det3 lerp; ring
  have hs1' : 0 < 1 - s := by linarith
  have nd1 : (⟨t.a, t.b, x⟩ : Tr K).nd := by
    show det3 t.a t.b x ≠ 0; rw [d1]; exact mul_ne_zero hs0.ne' hD
  have nd2 : (⟨t.a, x, t.c⟩ : Tr K).nd := by
    show det3 t.a x t.c ≠ 0; rw [d2]; exact mul_ne_zero hs1'.ne' hD
  have e1 : ∀ p, det3 t.b x p = s * det3 t.b t.c p := by
    intro p; rw [hx]; unfold det3 lerp; ring
  have e2 : ∀ p, det3 x t.a p = s * det3 t.c t.a p - (1 - s) * det3 t.a t.b p := by
    intro p; rw [hx]; unfold det3 lerp; ring
  have e3 : ∀ p, det3 x t.c p = (1 - s) * det3 t.b t.c p := by
    intro p; rw [hx]; unfold det3 lerp; ring
  have e4 : ∀ p, det3 t.a x p = (1 - s) * det3 t.a t.b p - s * det3 t.c t.a p := by
    intro p; rw [hx]; unfold det3 lerp; ring
  -- membership in the two halves
  have m1 : ∀ p, (⟨t.a, t.b, x⟩ : Tr K).mem p ↔ 0 ≤ t.D * det3 t.b t.c p ∧
      0 ≤ s * (t.D * det3 t.c t.a p) - (1 - s) * (t.D * det3 t.a t.b p) ∧
      0 ≤ t.D * det3 t.a t.b p := by
    intro p
    have c1 : (det3 t.a t.b x) * det3 t.b x p = (s * s) * (t.D * det3 t.b t.c p) := by
      rw [d1, e1]; ring
    have c2 : (det3 t.a t.b x) * det3 x t.a p =
        s * (s * (t.D * det3 t.c t.a p) - (1 - s) * (t.D * det3 t.a t.b p)) := by
      rw [d1, e2]; ring
    have c3 : (det3 t.a t.b x) * det3 t.a t.b p = s * (t.D * det3 t.a t.b p) := by
      rw [d1]; ring
    show 0 ≤ (det3 t.a t.b x) * det3 t.b x p ∧ 0 ≤ (det3 t.a t.b x) * det3 x t.a p ∧
      0 ≤ (det3 t.a t.b x) * det3 t.a t.b p ↔ _
    rw [c1, c2, c3, mul_nonneg_iff_of_pos_left (mul_pos hs0 hs0),
      mul_nonneg_iff_of_pos_left hs0, mul_nonneg_iff_of_pos_left hs0]
  have m2 : ∀ p, (⟨t.a, x, t.c⟩ : Tr K).mem p ↔ 0 ≤ t.D * det3 t.b t.c p ∧
      0 ≤ t.D * det3 t.c t.a p ∧
      0 ≤ (1 - s) * (t.D * det3 t.a t.b p) - s * (t.D * det3 t.c t.a p) := by
    intro p
    have c1 : (det3 t.a x t.c) * det3 x t.c p = ((1 - s) * (1 - s)) * (t.D * det3 t.b t.c p) := by
      rw [d2, e3]; ring
    have c2 : (det3 t.a x t.c) * det3 t.c t.a p = (1 - s) * (t.D * det3 t.c t.a p) := by
      rw [d2]; ring
    have c3 : (det3 t.a x t.c) * det3 t.a x p =
        (1 - s) * ((1 - s) * (t.D * det3 t.a t.b p) - s * (t.D * det3 t.c t.a p)) := by
      rw [d2, e4]; ring
    show 0 ≤ (det3 t.a x t.c) * det3 x t.c p ∧ 0 ≤ (det3 t.a x t.c) * det3 t.c t.a p ∧
      0 ≤ (det3 t.a x t.c) * det3 t.a x p ↔ _
    rw [c1, c2, c3, mul_nonneg_iff_of_pos_left (mul_pos hs1' hs1'),
      mul_nonneg_iff_of_pos_left hs1', mul_nonneg_iff_of_pos_left hs1']
  have i1 : ∀ p, (⟨t.a, t.b, x⟩ : Tr K).int p →
      0 < s * (t.D * det3 t.c t.a p) - (1 - s) * (t.D * det3 t.a t.b p) := by
    intro p hp
    have c2 : (det3 t.a t.b x) * det3 x t.a p =
        s * (s * (t.D * det3 t.c t.a p) - (1 - s) * (t.D * det3 t.a t.b p)) := by
      rw [d1, e2]; ring
    have h := hp.2.1
    change 0 < (det3 t.a t.b x) * det3 x t.a p at h
    rw [c2] at h
    exact (mul_pos_iff_of_pos_left hs0).1 h
  have i2 : ∀ p, (⟨t.a, x, t.c⟩ : Tr K).int p →
      0 < (1 - s) * (t.D * det3 t.a t.b p) - s * (t.D * det3 t.c t.a p) := by
    intro p hp
    have c3 : (det3 t.a x t.c) * det3 t.a x p =
        (1 - s) * ((1 - s) * (t.D * det3 t.a t.b p) - s * (t.D * det3 t.c t.a p)) := by
      rw [d2, e4]; ring
    have h := hp.2.2
    change 0 < (det3 t.a x t.c) * det3 t.a x p at h
    rw [c3] at h
    exact (mul_pos_iff_of_pos_left hs1').1 h
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact nd1
    · exact nd2
  · rw [List.pairwise_pair]
    rintro p ⟨h1, h2⟩
    have := i1 p h1; have := i2 p h2; linarith
  · intro p
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [m1, m2]
    unfold Tr.mem
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hc : 0 ≤ s * (t.D * det3 t.c t.a p) - (1 - s) * (t.D * det3 t.a t.b p)
      · exact Or.inl ⟨h1, hc, h3⟩
      · exact Or.inr ⟨h1, h2, by linarith⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · refine ⟨h1, ?_, h3⟩
        have := mul_nonneg hs1'.le h3
        by_contra hu
        push Not at hu
        have := mul_neg_of_pos_of_neg hs0 hu
        linarith
      · refine ⟨h1, h2, ?_⟩
        have := mul_nonneg hs0.le h2
        by_contra hu
        push Not at hu
        have := mul_neg_of_pos_of_neg hs1' hu
        linarith

theorem DecS.swap2 {S : K × K → Prop} {r1 r2 : Tr K} (h : DecS S [r1, r2]) : DecS S [r2, r1] := by
  obtain ⟨hnd, hpw, hun⟩ := h
  refine ⟨fun r hr => hnd r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto),
    ?_, fun p => ?_⟩
  · rw [List.pairwise_pair] at hpw ⊢
    exact fun p hp => hpw p ⟨hp.2, hp.1⟩
  · rw [hun p]; simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left]; tauto

/-- Replacing the second piece of a decomposition into two by a decomposition of it. -/
theorem DecS.cons_refine {S : K × K → Prop} {r1 r2 : Tr K} (h : DecS S [r1, r2]) {m : List (Tr K)}
    (hm : DecS r2.mem m) : DecS S (r1 :: m) := by
  obtain ⟨hnd, hpw, hun⟩ := h
  have nd1 : r1.nd := hnd r1 (by simp)
  have nd2 : r2.nd := hnd r2 (by simp)
  have d12 : ∀ p, ¬(r1.int p ∧ r2.int p) := List.pairwise_pair.1 hpw
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact nd1
    · exact hm.1 r hr
  · refine List.Pairwise.cons (fun q hq p hp => ?_) hm.2.1
    exact d12 p ⟨hp.1, Tr.int_of_sub (hm.1 q hq) nd2 (fun x hx => (hm.2.2 x).2 ⟨q, hq, hx⟩) hp.2⟩
  · intro p
    rw [hun p]
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [hm.2.2 p]

/-! ### Cutting a triangle by a straight line -/

/-- The triangle `r` lies on one side of the line `uv` (closed half-planes). -/
def OnSide (u v : K × K) (r : Tr K) : Prop :=
  (∀ p, r.mem p → 0 ≤ det3 u v p) ∨ (∀ p, r.mem p → det3 u v p ≤ 0)

theorem onSide_of_vertices {u v : K × K} {r : Tr K} (hr : r.nd)
    (h : (0 ≤ det3 u v r.a ∧ 0 ≤ det3 u v r.b ∧ 0 ≤ det3 u v r.c) ∨
      (det3 u v r.a ≤ 0 ∧ det3 u v r.b ≤ 0 ∧ det3 u v r.c ≤ 0)) : OnSide u v r := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    intro p hp
    obtain ⟨α, β, γ, a1, a2, a3, hs, rfl⟩ := (Tr.mem_iff_bary hr).1 hp
    rw [det3_comb _ _ hs]
    have := mul_nonneg a1 h1; have := mul_nonneg a2 h2; have := mul_nonneg a3 h3; linarith
  · right
    intro p hp
    obtain ⟨α, β, γ, a1, a2, a3, hs, rfl⟩ := (Tr.mem_iff_bary hr).1 hp
    rw [det3_comb _ _ hs]
    have := mul_nonpos_iff.2 (Or.inl ⟨a1, h1⟩)
    have := mul_nonpos_iff.2 (Or.inl ⟨a2, h2⟩)
    have := mul_nonpos_iff.2 (Or.inl ⟨a3, h3⟩)
    linarith

theorem OnSide.mono {u v : K × K} {r q : Tr K} (h : OnSide u v r) (hq : ∀ p, q.mem p → r.mem p) :
    OnSide u v q := by
  rcases h with h | h
  · exact Or.inl fun p hp => h p (hq p hp)
  · exact Or.inr fun p hp => h p (hq p hp)

theorem cross_param {x y : K} (h : x * y < 0) : 0 < x / (x - y) ∧ x / (x - y) < 1 := by
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at h) with hx | hx
  · have hy : 0 < y := by
      by_contra hy; push Not at hy; nlinarith
    have hd : x - y < 0 := by linarith
    exact ⟨div_pos_of_neg_of_neg hx hd, (div_lt_one_of_neg hd).2 (by linarith)⟩
  · have hy : y < 0 := by
      by_contra hy; push Not at hy; nlinarith
    have hd : 0 < x - y := by linarith
    exact ⟨div_pos hx hd, (div_lt_one hd).2 (by linarith)⟩

theorem det3_cross (u v x y : K × K) (h : det3 u v x - det3 u v y ≠ 0) :
    det3 u v (lerp (det3 u v x / (det3 u v x - det3 u v y)) x y) = 0 := by
  rw [det3_lerp]; field_simp; ring

/-- Cut of a triangle whose vertices `a`, `b` lie strictly on different sides of the line. -/
noncomputable def cutAB (u v : K × K) (t : Tr K) : List (Tr K) :=
  if det3 u v t.c = 0 then
    [⟨t.c, t.a, lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b⟩,
      ⟨t.c, lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b, t.b⟩]
  else if 0 < det3 u v t.c * det3 u v t.a then
    [⟨t.c, t.a, lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b⟩,
      ⟨lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b, t.b,
        lerp (det3 u v t.b / (det3 u v t.b - det3 u v t.c)) t.b t.c⟩,
      ⟨lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b,
        lerp (det3 u v t.b / (det3 u v t.b - det3 u v t.c)) t.b t.c, t.c⟩]
  else
    [⟨t.c, lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b, t.b⟩,
      ⟨lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b, t.c,
        lerp (det3 u v t.c / (det3 u v t.c - det3 u v t.a)) t.c t.a⟩,
      ⟨lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b,
        lerp (det3 u v t.c / (det3 u v t.c - det3 u v t.a)) t.c t.a, t.a⟩]

theorem sides3 {f0 f1 f2 : K} (h : 0 ≤ f0 * f1) (h2 : f2 = 0) :
    (0 ≤ f0 ∧ 0 ≤ f1 ∧ 0 ≤ f2) ∨ (f0 ≤ 0 ∧ f1 ≤ 0 ∧ f2 ≤ 0) := by
  subst h2
  rcases le_total 0 f0 with h0 | h0
  · rcases le_total 0 f1 with h1 | h1
    · exact Or.inl ⟨h0, h1, le_rfl⟩
    · rcases h0.eq_or_lt with e | h0
      · exact Or.inr ⟨e.symm.le, h1, le_rfl⟩
      · rcases h1.eq_or_lt with e | h1
        · exact Or.inl ⟨h0.le, e ▸ le_rfl, le_rfl⟩
        · nlinarith
  · rcases le_total 0 f1 with h1 | h1
    · rcases h1.eq_or_lt with e | h1
      · exact Or.inr ⟨h0, e.symm.le, le_rfl⟩
      · rcases h0.eq_or_lt with e | h0
        · exact Or.inl ⟨e ▸ le_rfl, h1.le, le_rfl⟩
        · nlinarith
    · exact Or.inr ⟨h0, h1, le_rfl⟩

theorem cutAB_spec (u v : K × K) {t : Tr K} (ht : t.nd) (hab : det3 u v t.a * det3 u v t.b < 0) :
    DecS t.mem (cutAB u v t) ∧ ∀ r ∈ cutAB u v t, OnSide u v r := by
  obtain ⟨s0, s1⟩ := cross_param hab
  have hne : det3 u v t.a - det3 u v t.b ≠ 0 := by
    intro e; have : det3 u v t.a = det3 u v t.b := by linarith
    rw [this] at hab; nlinarith [mul_self_nonneg (det3 u v t.b)]
  have fx := det3_cross u v t.a t.b hne
  set x := lerp (det3 u v t.a / (det3 u v t.a - det3 u v t.b)) t.a t.b with hx
  set f := det3 u v with hf
  -- the first transversal decomposition (from `c` through `x`)
  have t1 : (⟨t.c, t.a, t.b⟩ : Tr K).nd := by
    show det3 t.c t.a t.b ≠ 0; rw [det3_cyc, det3_cyc]; exact ht
  have sp := split t1 s0 s1
  have sp' : DecS t.mem [⟨t.c, t.a, x⟩, ⟨t.c, x, t.b⟩] := by
    refine sp.congr (fun p => ?_)
    show (Tr.rot (Tr.rot t)).mem p ↔ t.mem p
    rw [Tr.mem_rot, Tr.mem_rot]
  have ndA : (⟨t.c, t.a, x⟩ : Tr K).nd := sp'.1 _ (by simp)
  have ndB : (⟨t.c, x, t.b⟩ : Tr K).nd := sp'.1 _ (by simp)
  have ha0 : f t.a ≠ 0 := by rintro e; rw [e] at hab; simp at hab
  unfold cutAB
  rw [← hf, ← hx]
  split_ifs with hc hca
  · -- the line passes through `c`
    refine ⟨sp', fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact onSide_of_vertices ndA (by
        show (0 ≤ f t.c ∧ 0 ≤ f t.a ∧ 0 ≤ f x) ∨ (f t.c ≤ 0 ∧ f t.a ≤ 0 ∧ f x ≤ 0)
        rw [hc, fx]
        rcases le_total 0 (f t.a) with h | h
        · exact Or.inl ⟨le_rfl, h, le_rfl⟩
        · exact Or.inr ⟨le_rfl, h, le_rfl⟩)
    · exact onSide_of_vertices ndB (by
        show (0 ≤ f t.c ∧ 0 ≤ f x ∧ 0 ≤ f t.b) ∨ (f t.c ≤ 0 ∧ f x ≤ 0 ∧ f t.b ≤ 0)
        rw [hc, fx]
        rcases le_total 0 (f t.b) with h | h
        · exact Or.inl ⟨le_rfl, le_rfl, h⟩
        · exact Or.inr ⟨le_rfl, le_rfl, h⟩)
  · -- `b` alone on its side
    have hbc : f t.b * f t.c < 0 := by
      have : 0 < (f t.c * f t.a) * (f t.a * f t.a) := mul_pos hca (mul_self_pos.2 ha0)
      nlinarith
    obtain ⟨r0, r1⟩ := cross_param hbc
    have hne2 : f t.b - f t.c ≠ 0 := by
      intro e; have : f t.b = f t.c := by linarith
      rw [this] at hbc; nlinarith [mul_self_nonneg (f t.c)]
    have fy := det3_cross u v t.b t.c hne2
    set y := lerp (f t.b / (f t.b - f t.c)) t.b t.c with hy
    have ndB' : (⟨x, t.b, t.c⟩ : Tr K).nd := by
      show det3 x t.b t.c ≠ 0; rw [det3_cyc t.c x t.b]; exact ndB
    have sp2 := split ndB' r0 r1
    have sp2' : DecS (⟨t.c, x, t.b⟩ : Tr K).mem [⟨x, t.b, y⟩, ⟨x, y, t.c⟩] :=
      sp2.congr (fun p => by
        show (Tr.rot ⟨t.c, x, t.b⟩).mem p ↔ _
        rw [Tr.mem_rot])
    refine ⟨sp'.cons_refine sp2', fun r hr => ?_⟩
    have ndx : (⟨x, t.b, y⟩ : Tr K).nd := sp2'.1 _ (by simp)
    have ndy : (⟨x, y, t.c⟩ : Tr K).nd := sp2'.1 _ (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine onSide_of_vertices ndA ?_
      show (0 ≤ f t.c ∧ 0 ≤ f t.a ∧ 0 ≤ f x) ∨ (f t.c ≤ 0 ∧ f t.a ≤ 0 ∧ f x ≤ 0)
      exact sides3 hca.le fx
    · refine onSide_of_vertices ndx ?_
      show (0 ≤ f x ∧ 0 ≤ f t.b ∧ 0 ≤ f y) ∨ (f x ≤ 0 ∧ f t.b ≤ 0 ∧ f y ≤ 0)
      rcases le_total 0 (f t.b) with h | h
      · exact Or.inl ⟨fx.symm.le, h, fy.symm.le⟩
      · exact Or.inr ⟨fx.le, h, fy.le⟩
    · refine onSide_of_vertices ndy ?_
      show (0 ≤ f x ∧ 0 ≤ f y ∧ 0 ≤ f t.c) ∨ (f x ≤ 0 ∧ f y ≤ 0 ∧ f t.c ≤ 0)
      rcases le_total 0 (f t.c) with h | h
      · exact Or.inl ⟨fx.symm.le, fy.symm.le, h⟩
      · exact Or.inr ⟨fx.le, fy.le, h⟩
  · -- `a` alone on its side
    have hca' : f t.c * f t.a < 0 := by
      rcases lt_or_gt_of_ne (mul_ne_zero hc ha0) with h | h
      · exact h
      · exact absurd h hca
    obtain ⟨r0, r1⟩ := cross_param hca'
    have hne2 : f t.c - f t.a ≠ 0 := by
      intro e; have : f t.c = f t.a := by linarith
      rw [this] at hca'; nlinarith [mul_self_nonneg (f t.a)]
    have fy := det3_cross u v t.c t.a hne2
    set y := lerp (f t.c / (f t.c - f t.a)) t.c t.a with hy
    have ndA' : (⟨x, t.c, t.a⟩ : Tr K).nd := by
      show det3 x t.c t.a ≠ 0; rw [← det3_cyc x t.c t.a]; exact ndA
    have sp2 := split ndA' r0 r1
    have sp2' : DecS (⟨t.c, t.a, x⟩ : Tr K).mem [⟨x, t.c, y⟩, ⟨x, y, t.a⟩] :=
      sp2.congr (fun p => by
        show (Tr.rot (Tr.rot ⟨t.c, t.a, x⟩)).mem p ↔ _
        rw [Tr.mem_rot, Tr.mem_rot])
    refine ⟨sp'.swap2.cons_refine sp2', fun r hr => ?_⟩
    have ndx : (⟨x, t.c, y⟩ : Tr K).nd := sp2'.1 _ (by simp)
    have ndy : (⟨x, y, t.a⟩ : Tr K).nd := sp2'.1 _ (by simp)
    have hcb : 0 ≤ f t.c * f t.b := by
      have : 0 < (f t.c * f t.a) * (f t.a * f t.b) := mul_pos_of_neg_of_neg hca' hab
      nlinarith [mul_self_nonneg (f t.a)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine onSide_of_vertices ndB ?_
      show (0 ≤ f t.c ∧ 0 ≤ f x ∧ 0 ≤ f t.b) ∨ (f t.c ≤ 0 ∧ f x ≤ 0 ∧ f t.b ≤ 0)
      rcases sides3 (f0 := f t.c) (f1 := f t.b) hcb fx with h | h
      · exact Or.inl ⟨h.1, h.2.2, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.2, h.2.1⟩
    · refine onSide_of_vertices ndx ?_
      show (0 ≤ f x ∧ 0 ≤ f t.c ∧ 0 ≤ f y) ∨ (f x ≤ 0 ∧ f t.c ≤ 0 ∧ f y ≤ 0)
      rcases le_total 0 (f t.c) with h | h
      · exact Or.inl ⟨fx.symm.le, h, fy.symm.le⟩
      · exact Or.inr ⟨fx.le, h, fy.le⟩
    · refine onSide_of_vertices ndy ?_
      show (0 ≤ f x ∧ 0 ≤ f y ∧ 0 ≤ f t.a) ∨ (f x ≤ 0 ∧ f y ≤ 0 ∧ f t.a ≤ 0)
      rcases le_total 0 (f t.a) with h | h
      · exact Or.inl ⟨fx.symm.le, fy.symm.le, h⟩
      · exact Or.inr ⟨fx.le, fy.le, h⟩

/-- **Cut of a triangle by the line `uv`** into triangles lying on either side of it. -/
noncomputable def cut1 (u v : K × K) (t : Tr K) : List (Tr K) :=
  if (0 ≤ det3 u v t.a ∧ 0 ≤ det3 u v t.b ∧ 0 ≤ det3 u v t.c) ∨
      (det3 u v t.a ≤ 0 ∧ det3 u v t.b ≤ 0 ∧ det3 u v t.c ≤ 0) then [t]
  else if det3 u v t.a * det3 u v t.b < 0 then cutAB u v t
  else if det3 u v t.b * det3 u v t.c < 0 then cutAB u v t.rot
  else cutAB u v t.rot.rot

theorem mixed_signs {fa fb fc : K}
    (h : ¬((0 ≤ fa ∧ 0 ≤ fb ∧ 0 ≤ fc) ∨ (fa ≤ 0 ∧ fb ≤ 0 ∧ fc ≤ 0)))
    (h1 : ¬fa * fb < 0) (h2 : ¬fb * fc < 0) : fc * fa < 0 := by
  push Not at h1 h2
  rcases lt_trichotomy fa 0 with a | a | a <;> rcases lt_trichotomy fb 0 with b | b | b <;>
    rcases lt_trichotomy fc 0 with c | c | c
  all_goals first
    | nlinarith
    | (exfalso; apply h; first
        | exact Or.inl ⟨by linarith, by linarith, by linarith⟩
        | exact Or.inr ⟨by linarith, by linarith, by linarith⟩)

theorem cut1_spec (u v : K × K) {t : Tr K} (ht : t.nd) :
    DecS t.mem (cut1 u v t) ∧ ∀ r ∈ cut1 u v t, OnSide u v r := by
  unfold cut1
  split_ifs with h0 h1 h2
  · exact ⟨DecS.single ht, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact onSide_of_vertices ht h0⟩
  · exact cutAB_spec u v ht h1
  · obtain ⟨d, s⟩ := cutAB_spec u v (Tr.nd_rot.2 ht) h2
    exact ⟨d.congr (fun p => Tr.mem_rot), s⟩
  · obtain ⟨d, s⟩ := cutAB_spec u v (Tr.nd_rot.2 (Tr.nd_rot.2 ht)) (mixed_signs h0 h1 h2)
    exact ⟨d.congr (fun p => by rw [Tr.mem_rot, Tr.mem_rot]), s⟩

/-- **Successive cuts** by the lines of a list. -/
noncomputable def cutAll : List ((K × K) × (K × K)) → Tr K → List (Tr K)
  | [], t => [t]
  | uv :: ls, t => (cut1 uv.1 uv.2 t).flatMap (cutAll ls)

theorem cutAll_spec (ls : List ((K × K) × (K × K))) {t : Tr K} (ht : t.nd) :
    DecS t.mem (cutAll ls t) ∧ ∀ r ∈ cutAll ls t, ∀ uv ∈ ls, OnSide uv.1 uv.2 r := by
  induction ls generalizing t with
  | nil => exact ⟨DecS.single ht, fun r _ uv huv => absurd huv List.not_mem_nil⟩
  | cons uv ls ih =>
    obtain ⟨d1, s1⟩ := cut1_spec uv.1 uv.2 ht
    refine ⟨d1.flatMap _ (fun q hq => (ih (d1.1 q hq)).1), fun r hr uv' huv' => ?_⟩
    obtain ⟨q, hq, hrq⟩ := List.mem_flatMap.1 hr
    rcases List.mem_cons.1 huv' with rfl | huv'
    · exact (s1 q hq).mono (fun p hp => ((ih (d1.1 q hq)).1.2.2 p).2 ⟨r, hrq, hp⟩)
    · exact (ih (d1.1 q hq)).2 r hrq uv' huv'

/-- The three side lines of the triangles of a list. -/
def edges (l : List (Tr K)) : List ((K × K) × (K × K)) :=
  l.flatMap (fun r => [(r.b, r.c), (r.c, r.a), (r.a, r.b)])

theorem det3_cen (u v : K × K) (r : Tr K) :
    det3 u v r.cen = (det3 u v r.a + det3 u v r.b + det3 u v r.c) / 3 := by
  unfold Tr.cen; rw [det3_comb _ _ (by norm_num)]; ring

/-- A triangle on one side of a line whose centroid lies on the side where `D' · det3 u v ≥ 0`
lies entirely on that side. -/
theorem onSide_inner {u v : K × K} {r : Tr K} (hr : r.nd) (huv : u ≠ v) (h : OnSide u v r)
    {D' : K} (hD' : 0 ≤ D' * det3 u v r.cen) : ∀ p, r.mem p → 0 ≤ D' * det3 u v p := by
  have hg : det3 u v r.cen ≠ 0 := by
    intro e
    rw [det3_cen] at e
    have hs : det3 u v r.a + det3 u v r.b + det3 u v r.c = 0 := by
      rcases div_eq_zero_iff.1 e with h | h
      · exact h
      · norm_num at h
    have va := Tr.mem_a hr; have vb := Tr.mem_b hr; have vc := Tr.mem_c hr
    rcases h with h | h
    · have a1 := h _ va; have a2 := h _ vb; have a3 := h _ vc
      exact hr (det3_eq_zero_of_line huv (by linarith) (by linarith) (by linarith))
    · have a1 := h _ va; have a2 := h _ vb; have a3 := h _ vc
      exact hr (det3_eq_zero_of_line huv (by linarith) (by linarith) (by linarith))
  rcases h with h | h
  · have hpos : 0 < det3 u v r.cen := lt_of_le_of_ne (h _ (Tr.mem_of_int (Tr.int_cen hr))) hg.symm
    have hD : 0 ≤ D' := (mul_nonneg_iff_of_pos_right hpos).1 hD'
    exact fun p hp => mul_nonneg hD (h p hp)
  · have hneg : det3 u v r.cen < 0 := lt_of_le_of_ne (h _ (Tr.mem_of_int (Tr.int_cen hr))) hg
    have hD : D' ≤ 0 := by
      by_contra hc; push Not at hc; have := mul_neg_of_pos_of_neg hc hneg; linarith
    exact fun p hp => mul_nonneg_of_nonpos_of_nonpos hD (h p hp)

/-- **Common refinement**: cutting a triangle `t` by all the side lines of a family `l'` of
non-degenerate triangles covering it gives triangles each lying in a triangle of `l'`. -/
theorem refine_sub {t : Tr K} (ht : t.nd) {l' : List (Tr K)} (hnd : ∀ r ∈ l', r.nd)
    (hcov : ∀ p, t.mem p → ∃ r ∈ l', r.mem p) :
    ∀ r ∈ cutAll (edges l') t, ∃ r' ∈ l', ∀ p, r.mem p → r'.mem p := by
  intro r hr
  obtain ⟨hd, hs⟩ := cutAll_spec (edges l') ht
  have hrnd := hd.1 r hr
  obtain ⟨r', hr', hg⟩ := hcov r.cen (hd.sub hr (Tr.mem_of_int (Tr.int_cen hrnd)))
  refine ⟨r', hr', fun p hp => ?_⟩
  have hnd' := hnd r' hr'
  have e1 : ((r'.b, r'.c) : (K × K) × (K × K)) ∈ edges l' :=
    List.mem_flatMap.2 ⟨r', hr', by simp⟩
  have e2 : ((r'.c, r'.a) : (K × K) × (K × K)) ∈ edges l' :=
    List.mem_flatMap.2 ⟨r', hr', by simp⟩
  have e3 : ((r'.a, r'.b) : (K × K) × (K × K)) ∈ edges l' :=
    List.mem_flatMap.2 ⟨r', hr', by simp⟩
  exact ⟨onSide_inner hrnd (Tr.nd_ne_bc hnd') (hs r hr _ e1) hg.1 p hp,
    onSide_inner hrnd (Tr.nd_ne_ca hnd') (hs r hr _ e2) hg.2.1 p hp,
    onSide_inner hrnd (Tr.nd_ne_ab hnd') (hs r hr _ e3) hg.2.2 p hp⟩

end Areas

end HilbertFoundations
