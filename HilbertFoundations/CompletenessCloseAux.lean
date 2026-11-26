import HilbertFoundations.Proportion
import HilbertFoundations.Analytic

/-!
# Helper module for `CompletenessClose.lean` (1): real charts of planes and the length of segments

This module contains no unit of Hilbert's text. It prepares the co-ordinates of a geometry of space
with groups I–V (used in `CompletenessClose.lean` for the units `s8.bolzano`, `s8.real_numbers`):

* `CC.PChart`: a **real chart** of a plane: co-ordinates `x, y` with values in a subfield `F` of `ℝ`,
  onto `F × F`, in which congruent segments are the segments of equal euclidean length and the points
  between `A` and `C` are the points `A + t (C - A)`, `0 < t < 1`. `CC.exists_chart`: a plane geometry
  with I–V has a chart (the field of segments of `Pascal.lean` is archimedean, hence a subfield of
  `ℝ`); `CC.exists_plane_chart`: so has every plane of a geometry of space.
* `CC.IsLen`: a **length** of segments: a positive real function of two points that is `0` on equal
  points, equal exactly on congruent segments, and additive on points lying between.
  `CC.exists_len`: a geometry of space with I–V having a plane has a length (lay the segment off on
  a fixed half-ray of a fixed plane and take the chart of that plane).
* `CC.PChart.len_eq`: a length is, on every plane, a constant multiple of the euclidean distance of
  the chart (an additive positive function on the positive part of a subfield of `ℝ` is linear,
  `CC.mu_linear`). Consequences: **Stewart's relation** `CC.stewart` for a point and three points of
  a line, and the existence of perpendicular unit segments `CC.exists_perp`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w

/-- The squared euclidean distance of two points in a chart `x, y`. -/
def sqd {P : Type u} (x y : P → ℝ) (X Y : P) : ℝ := (x X - x Y) ^ 2 + (y X - y Y) ^ 2

theorem sqd_nonneg {P : Type u} (x y : P → ℝ) (X Y : P) : 0 ≤ sqd x y X Y := by
  unfold sqd; positivity

/-- A **real chart** of the set `S` of points (a plane), with origin `O` and unit point `E`. -/
structure PChart (P : Type u) [HasBetween P] [HasSegCong P] (S : Set P) (O E : P) where
  x : P → ℝ
  y : P → ℝ
  F : Subfield ℝ
  xO : x O = 0
  yO : y O = 0
  xE : x E = 1
  yE : y E = 0
  inj : ∀ Z W, Z ∈ S → W ∈ S → x Z = x W → y Z = y W → Z = W
  memF : ∀ Z, Z ∈ S → x Z ∈ F ∧ y Z ∈ F
  onto : ∀ a ∈ F, ∀ b ∈ F, ∃ Z, Z ∈ S ∧ x Z = a ∧ y Z = b
  cong : ∀ X Y U V, X ∈ S → Y ∈ S → U ∈ S → V ∈ S → X ≠ Y → U ≠ V →
    (SegCong X Y U V ↔ sqd x y X Y = sqd x y U V)
  btw : ∀ A B C, A ∈ S → B ∈ S → C ∈ S → Between A B C →
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x B - x A = t * (x C - x A) ∧ y B - y A = t * (y C - y A)
  btw' : ∀ A B C (t : ℝ), A ∈ S → B ∈ S → C ∈ S → A ≠ C → 0 < t → t < 1 →
    x B - x A = t * (x C - x A) → y B - y A = t * (y C - y A) → Between A B C
  sqrtF : ∀ X Y, X ∈ S → Y ∈ S → Real.sqrt (sqd x y X Y) ∈ F

/-- A **length** of segments. -/
structure IsLen {P : Type u} [HasBetween P] [HasSegCong P] (ℓ : P → P → ℝ) : Prop where
  self : ∀ A, ℓ A A = 0
  pos : ∀ A B, A ≠ B → 0 < ℓ A B
  cong : ∀ A B C D, A ≠ B → C ≠ D → (SegCong A B C D ↔ ℓ A B = ℓ C D)
  add : ∀ A B C, Between A B C → ℓ A B + ℓ B C = ℓ A C

/-! ### Additive positive functions on a subfield of `ℝ` -/

theorem mu_linear (F : Subfield ℝ) (μ : ℝ → ℝ)
    (hadd : ∀ s ∈ F, ∀ t ∈ F, 0 < s → 0 < t → μ (s + t) = μ s + μ t)
    (hpos : ∀ t ∈ F, 0 < t → 0 < μ t) : ∀ t ∈ F, 0 < t → μ t = μ 1 * t := by
  have h1F : (1 : ℝ) ∈ F := F.one_mem
  have hmul : ∀ n : ℕ, 1 ≤ n → ∀ t ∈ F, 0 < t → μ ((n : ℝ) * t) = (n : ℝ) * μ t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro t _ _; simp
    | succ n hn ih =>
      intro t ht h0
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hnF : (n : ℝ) * t ∈ F := F.mul_mem (natCast_mem F n) ht
      have e : ((n + 1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by push_cast; ring
      rw [e, hadd _ hnF _ ht (mul_pos hn0 h0) h0, ih t ht h0]; push_cast; ring
  have hmono : ∀ s ∈ F, ∀ t ∈ F, 0 < s → s < t → μ s < μ t := by
    intro s hs t ht h0 hst
    have h := hadd s hs (t - s) (F.sub_mem ht hs) h0 (sub_pos.2 hst)
    rw [add_sub_cancel] at h
    rw [h]; linarith [hpos (t - s) (F.sub_mem ht hs) (sub_pos.2 hst)]
  have hrat : ∀ q : ℚ, 0 < q → μ (q : ℝ) = μ 1 * q := by
    intro q hq
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hnum.le
    have ha1 : 1 ≤ a := by
      have : (0 : ℤ) < (a : ℤ) := ha ▸ hnum
      exact_mod_cast this
    have hb1 : 1 ≤ q.den := q.den_pos
    have hqF : (q : ℝ) ∈ F := SubfieldClass.ratCast_mem F q
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have e : (q.den : ℝ) * (q : ℝ) = (a : ℝ) * 1 := by
      have h := congrArg (fun r : ℚ => (r : ℝ)) (Rat.mul_den_eq_num q)
      simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at h
      rw [mul_comm, h, ha]; simp
    have h1 := hmul q.den hb1 _ hqF hq0
    have h2 := hmul a ha1 1 h1F one_pos
    rw [e, h2] at h1
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.1 q.den_pos)
    refine mul_left_cancel₀ hd ?_
    linear_combination (-1 : ℝ) * h1 - μ 1 * e
  intro t ht h0
  have hμ1 := hpos 1 h1F one_pos
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : μ t / μ 1 < t := by rw [div_lt_iff₀ hμ1]; linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h'
    have hq0 : (0 : ℚ) < q := by
      have : (0 : ℝ) < q := lt_trans (div_pos (hpos t ht h0) hμ1) hq1
      exact_mod_cast this
    have h3 := hmono q (SubfieldClass.ratCast_mem F q) t ht (by exact_mod_cast hq0) hq2
    rw [hrat q hq0] at h3
    rw [div_lt_iff₀ hμ1] at hq1
    linarith
  · have h' : t < μ t / μ 1 := by rw [lt_div_iff₀ hμ1]; linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h'
    have hq0 : (0 : ℚ) < q := by
      have : (0 : ℝ) < q := lt_trans h0 hq1
      exact_mod_cast this
    have h3 := hmono t ht q (SubfieldClass.ratCast_mem F q) h0 hq1
    rw [hrat q hq0] at h3
    rw [lt_div_iff₀ hμ1] at hq2
    linarith

/-! ### A length in a chart -/

section ChartLen

variable {P : Type u} [HasBetween P] [HasSegCong P] {S : Set P} {O E : P} {ℓ : P → P → ℝ}

theorem PChart.sqd_pos (c : PChart P S O E) {X Y : P} (hX : X ∈ S) (hY : Y ∈ S) (h : X ≠ Y) :
    0 < sqd c.x c.y X Y := by
  rcases (sqd_nonneg c.x c.y X Y).lt_or_eq with h1 | h1
  · exact h1
  · exfalso; apply h
    unfold sqd at h1
    have hx : c.x X - c.x Y = 0 := by
      nlinarith [sq_nonneg (c.x X - c.x Y), sq_nonneg (c.y X - c.y Y)]
    have hy : c.y X - c.y Y = 0 := by
      nlinarith [sq_nonneg (c.x X - c.x Y), sq_nonneg (c.y X - c.y Y)]
    exact c.inj X Y hX hY (sub_eq_zero.1 hx) (sub_eq_zero.1 hy)

theorem PChart.ne (c : PChart P S O E) : O ≠ E := by
  intro e
  subst e
  exact zero_ne_one (c.xO.symm.trans c.xE)

/-- **A length is, on a plane, a multiple of the euclidean distance of a chart.** -/
theorem PChart.len_eq (c : PChart P S O E) (hℓ : IsLen ℓ) (hO : O ∈ S) (hE : E ∈ S) {X Y : P}
    (hX : X ∈ S) (hY : Y ∈ S) : ℓ X Y = ℓ O E * Real.sqrt (sqd c.x c.y X Y) := by
  classical
  have h0F : (0 : ℝ) ∈ c.F := c.F.zero_mem
  have hpt : ∀ t ∈ c.F, ∃ Z, Z ∈ S ∧ c.x Z = t ∧ c.y Z = 0 := fun t ht => c.onto t ht 0 h0F
  let μ : ℝ → ℝ := fun t => if h : t ∈ c.F then ℓ O (Classical.choose (hpt t h)) else 0
  have hμ : ∀ t ∈ c.F, ∀ Z, Z ∈ S → c.x Z = t → c.y Z = 0 → μ t = ℓ O Z := by
    intro t ht Z hZ hx hy
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hpt t ht)
    have e : Classical.choose (hpt t ht) = Z :=
      c.inj _ _ h1 hZ (h2.trans hx.symm) (h3.trans hy.symm)
    simp only [μ, ht, ↓reduceDIte, e]
  have sqd_axis : ∀ Z W, c.y Z = 0 → c.y W = 0 → sqd c.x c.y Z W = (c.x Z - c.x W) ^ 2 := by
    intro Z W h1 h2; unfold sqd; rw [h1, h2]; ring
  have hadd : ∀ s ∈ c.F, ∀ t ∈ c.F, 0 < s → 0 < t → μ (s + t) = μ s + μ t := by
    intro s hs t ht hs0 ht0
    obtain ⟨Zs, hZs, xs, ys⟩ := hpt s hs
    obtain ⟨Zt, hZt, xt, yt⟩ := hpt t ht
    obtain ⟨Zst, hZst, xst, yst⟩ := hpt (s + t) (c.F.add_mem hs ht)
    rw [hμ s hs Zs hZs xs ys, hμ t ht Zt hZt xt yt, hμ _ (c.F.add_mem hs ht) Zst hZst xst yst]
    have hOst : O ≠ Zst := by
      intro e; rw [← e, c.xO] at xst; linarith
    have hst0 : s + t ≠ 0 := by positivity
    have hb : Between O Zs Zst := by
      refine c.btw' O Zs Zst (s / (s + t)) hO hZs hZst hOst (by positivity) ?_ ?_ ?_
      · rw [div_lt_one (by positivity)]; linarith
      · have e : s / (s + t) * (s + t) = s := by field_simp
        rw [xs, xst, c.xO, sub_zero, sub_zero, e]
      · rw [ys, yst, c.yO]; ring
    have hOt : O ≠ Zt := by intro e; rw [← e, c.xO] at xt; linarith
    have hsst : Zs ≠ Zst := by intro e; rw [e, xst] at xs; linarith
    have hc : SegCong Zs Zst O Zt := by
      rw [c.cong Zs Zst O Zt hZs hZst hO hZt hsst hOt, sqd_axis _ _ ys yst,
        sqd_axis _ _ c.yO yt, xs, xst, c.xO, xt]
      ring
    rw [← hℓ.add O Zs Zst hb, (hℓ.cong Zs Zst O Zt hsst hOt).1 hc]
  have hpos : ∀ t ∈ c.F, 0 < t → 0 < μ t := by
    intro t ht ht0
    obtain ⟨Zt, hZt, xt, yt⟩ := hpt t ht
    rw [hμ t ht Zt hZt xt yt]
    exact hℓ.pos _ _ (by intro e; rw [← e, c.xO] at xt; linarith)
  have lin := mu_linear c.F μ hadd hpos
  have hμ1 : μ 1 = ℓ O E := hμ 1 c.F.one_mem E hE c.xE c.yE
  by_cases hXY : X = Y
  · subst hXY
    have : sqd c.x c.y X X = 0 := by unfold sqd; ring
    rw [hℓ.self, this, Real.sqrt_zero, mul_zero]
  · have hr0 : 0 < Real.sqrt (sqd c.x c.y X Y) := Real.sqrt_pos.2 (c.sqd_pos hX hY hXY)
    have hrF := c.sqrtF X Y hX hY
    obtain ⟨Zr, hZr, xr, yr⟩ := hpt _ hrF
    have hOr : O ≠ Zr := by intro e; rw [← e, c.xO] at xr; linarith
    have hc : SegCong X Y O Zr := by
      rw [c.cong X Y O Zr hX hY hO hZr hXY hOr, sqd_axis _ _ c.yO yr, c.xO, xr, zero_sub, neg_sq,
        Real.sq_sqrt (sqd_nonneg _ _ _ _)]
    rw [(hℓ.cong X Y O Zr hXY hOr).1 hc, ← hμ _ hrF Zr hZr xr yr, lin _ hrF hr0, hμ1]

theorem PChart.len_sq (c : PChart P S O E) (hℓ : IsLen ℓ) (hO : O ∈ S) (hE : E ∈ S) {X Y : P}
    (hX : X ∈ S) (hY : Y ∈ S) : ℓ X Y ^ 2 = ℓ O E ^ 2 * sqd c.x c.y X Y := by
  rw [c.len_eq hℓ hO hE hX hY, mul_pow, Real.sq_sqrt (sqd_nonneg _ _ _ _)]

/-- **Stewart's relation** in a plane with a chart. -/
theorem PChart.stewart (c : PChart P S O E) (hℓ : IsLen ℓ) (hO : O ∈ S) (hE : E ∈ S)
    {A B C Q : P} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hQ : Q ∈ S) (h : Between A B C) :
    ℓ Q B ^ 2 * ℓ A C = ℓ Q A ^ 2 * ℓ B C + ℓ Q C ^ 2 * ℓ A B - ℓ A B * ℓ B C * ℓ A C := by
  obtain ⟨t, t0, t1, ex, ey⟩ := c.btw A B C hA hB hC h
  have hx : c.x B = c.x A + t * (c.x C - c.x A) := by linarith
  have hy : c.y B = c.y A + t * (c.y C - c.y A) := by linarith
  have hd : Real.sqrt (sqd c.x c.y A C) ^ 2 = sqd c.x c.y A C := Real.sq_sqrt (sqd_nonneg _ _ _ _)
  have e1 : sqd c.x c.y A B = t ^ 2 * sqd c.x c.y A C := by
    unfold sqd; rw [hx, hy]; ring
  have e2 : sqd c.x c.y B C = (1 - t) ^ 2 * sqd c.x c.y A C := by
    unfold sqd; rw [hx, hy]; ring
  have lAB : ℓ A B = ℓ O E * (t * Real.sqrt (sqd c.x c.y A C)) := by
    rw [c.len_eq hℓ hO hE hA hB, e1, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq t0.le]
  have lBC : ℓ B C = ℓ O E * ((1 - t) * Real.sqrt (sqd c.x c.y A C)) := by
    rw [c.len_eq hℓ hO hE hB hC, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
  have lAC := c.len_eq (ℓ := ℓ) hℓ hO hE hA hC
  have key : sqd c.x c.y Q B = (1 - t) * sqd c.x c.y Q A + t * sqd c.x c.y Q C -
      t * (1 - t) * sqd c.x c.y A C := by
    unfold sqd; rw [hx, hy]; ring
  rw [c.len_sq hℓ hO hE hQ hA, c.len_sq hℓ hO hE hQ hB, c.len_sq hℓ hO hE hQ hC, lAB, lBC, lAC,
    key]
  linear_combination (ℓ O E ^ 3 * t * (1 - t) * Real.sqrt (sqd c.x c.y A C)) * hd

/-- **A perpendicular unit segment** in a plane with a chart, and its rigidity. -/
theorem PChart.perp (c : PChart P S O E) (hℓ : IsLen ℓ) (hO : O ∈ S) (hE : E ∈ S) :
    ∃ Fp, Fp ∈ S ∧ ℓ O Fp = ℓ O E ∧ ℓ E Fp ^ 2 = 2 * ℓ O E ^ 2 ∧
      ∀ Z, Z ∈ S → ¬(ℓ O Z ^ 2 = ℓ O E ^ 2 ∧ ℓ E Z ^ 2 = 2 * ℓ O E ^ 2 ∧
        ℓ Fp Z ^ 2 = 2 * ℓ O E ^ 2) := by
  obtain ⟨Fp, hFp, xF, yF⟩ := c.onto 0 c.F.zero_mem 1 c.F.one_mem
  have hk : 0 < ℓ O E := hℓ.pos _ _ c.ne
  have hk2 : ℓ O E ^ 2 ≠ 0 := by positivity
  refine ⟨Fp, hFp, ?_, ?_, ?_⟩
  · rw [c.len_eq hℓ hO hE hO hFp]
    have : sqd c.x c.y O Fp = 1 := by unfold sqd; rw [c.xO, c.yO, xF, yF]; ring
    rw [this, Real.sqrt_one, mul_one]
  · rw [c.len_sq hℓ hO hE hE hFp]
    have : sqd c.x c.y E Fp = 2 := by unfold sqd; rw [c.xE, c.yE, xF, yF]; ring
    rw [this]; ring
  · rintro Z hZ ⟨h1, h2, h3⟩
    rw [c.len_sq hℓ hO hE hO hZ] at h1
    rw [c.len_sq hℓ hO hE hE hZ] at h2
    rw [c.len_sq hℓ hO hE hFp hZ] at h3
    have e1 : sqd c.x c.y O Z = 1 := mul_left_cancel₀ hk2 (by linarith)
    have e2 : sqd c.x c.y E Z = 2 := mul_left_cancel₀ hk2 (by linarith)
    have e3 : sqd c.x c.y Fp Z = 2 := mul_left_cancel₀ hk2 (by linarith)
    unfold sqd at e1 e2 e3
    rw [c.xO, c.yO] at e1
    rw [c.xE, c.yE] at e2
    rw [xF, yF] at e3
    have hx0 : c.x Z = 0 := by nlinarith
    have hy0 : c.y Z = 0 := by nlinarith
    rw [hx0, hy0] at e1
    norm_num at e1

end ChartLen

/-! ### The chart of a plane geometry with I–V -/

section PlaneChart

variable {Q : Type u} {M : Type v} [HasLines Q M] [HasBetween Q] [HasSegCong Q] [HasAngCong Q]
  [hC : PlaneCongruence Q M] [hP : PlaneParallels Q M] [hV : Archimedes Q M]

include hC hP hV in
/-- **A plane geometry with I–V has a real chart** at any two distinct points. -/
theorem exists_chart {O E : Q} (hOE : O ≠ E) : Nonempty (PChart Q Set.univ O E) := by
  obtain ⟨ax, hO', hE'⟩ := Pas.exists_axes (L := M) hOE
  subst hO' hE'
  have := Pas.archimedean_G ax
  obtain ⟨ι⟩ := Real.nonemptyOrderRingHom (Pas.G ax)
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hmono : StrictMono ι := (OrderHomClass.mono ι).strictMono_of_injective hinj
  have key : ∀ X Y : Q, sqd (fun Z => ι (Pas.px ax Z)) (fun Z => ι (Pas.py ax Z)) X Y =
      ι (Pas.len ax X Y * Pas.len ax X Y) := by
    intro X Y
    rw [Pas.len_sq ax X Y]
    simp only [sqd, map_add, map_mul, map_sub]
    ring
  have hlen0 : ∀ X Y : Q, 0 ≤ ι (Pas.len ax X Y) := by
    intro X Y
    have := OrderHomClass.mono ι (Pas.len_nonneg ax X Y)
    rwa [map_zero] at this
  exact ⟨{
    x := fun Z => ι (Pas.px ax Z)
    y := fun Z => ι (Pas.py ax Z)
    F := (ι : Pas.G ax →+* ℝ).fieldRange
    xO := by
      show ι (Pas.xc ax (Pas.toV ax.O ax.O)) = 0
      rw [Pas.toV_O ax, Pas.xc_zero ax, map_zero]
    yO := by
      show ι (Pas.yc ax (Pas.toV ax.O ax.O)) = 0
      rw [Pas.toV_O ax, Pas.yc_zero ax, map_zero]
    xE := by
      show ι (Pas.xc ax (Pas.eV ax)) = 1
      rw [← Pas.coe_oneG ax, (Pas.coords_x ax 1).1, map_one]
    yE := by
      show ι (Pas.yc ax (Pas.eV ax)) = 0
      rw [← Pas.coe_oneG ax, (Pas.coords_x ax 1).2, map_zero]
    inj := fun Z W _ _ h1 h2 => (Pas.coords_bijective ax).1 (Prod.ext (hinj h1) (hinj h2))
    memF := fun Z _ => ⟨RingHom.mem_fieldRange.2 ⟨_, rfl⟩, RingHom.mem_fieldRange.2 ⟨_, rfl⟩⟩
    onto := by
      intro a ha b hb
      obtain ⟨p, rfl⟩ := RingHom.mem_fieldRange.1 ha
      obtain ⟨q, rfl⟩ := RingHom.mem_fieldRange.1 hb
      refine ⟨Pas.mkPt ax p q, trivial, ?_, ?_⟩
      · show ι (Pas.px ax (Pas.mkPt ax p q)) = ι p
        rw [(Pas.mkPt_coords ax p q).1]
      · show ι (Pas.py ax (Pas.mkPt ax p q)) = ι q
        rw [(Pas.mkPt_coords ax p q).2]
    cong := by
      intro X Y U V _ _ _ _ hXY hUV
      rw [key, key, hinj.eq_iff, ← Pas.len_eq_iff ax hXY hUV]
      exact (mul_self_inj (Pas.len_nonneg ax X Y) (Pas.len_nonneg ax U V)).symm
    btw := by
      intro A B C _ _ _ h
      obtain ⟨t, t0, t1, e1, e2⟩ := Pas.between_coords ax h
      refine ⟨ι t, ?_, ?_, ?_, ?_⟩
      · have := hmono t0; rwa [map_zero] at this
      · have := hmono t1; rwa [map_one] at this
      · show ι (Pas.px ax B) - ι (Pas.px ax A) = ι t * (ι (Pas.px ax C) - ι (Pas.px ax A))
        rw [← map_sub, e1, map_mul, map_sub]
      · show ι (Pas.py ax B) - ι (Pas.py ax A) = ι t * (ι (Pas.py ax C) - ι (Pas.py ax A))
        rw [← map_sub, e2, map_mul, map_sub]
    btw' := by
      intro A B C t _ _ _ hAC t0 t1 ex ey
      have ex' : ι (Pas.px ax B - Pas.px ax A) = t * ι (Pas.px ax C - Pas.px ax A) := by
        rw [map_sub, map_sub]; exact ex
      have ey' : ι (Pas.py ax B - Pas.py ax A) = t * ι (Pas.py ax C - Pas.py ax A) := by
        rw [map_sub, map_sub]; exact ey
      -- `t` is the image of an element of the field of segments
      have ht : ∃ t' : Pas.G ax, ι t' = t := by
        rcases Pas.coords_ne ax hAC with hd | hd
        · have hd' : ι (Pas.px ax C - Pas.px ax A) ≠ 0 := fun e => hd (hinj (e.trans (map_zero ι).symm))
          refine ⟨(Pas.px ax B - Pas.px ax A) / (Pas.px ax C - Pas.px ax A), ?_⟩
          rw [map_div₀, ex']; field_simp
        · have hd' : ι (Pas.py ax C - Pas.py ax A) ≠ 0 := fun e => hd (hinj (e.trans (map_zero ι).symm))
          refine ⟨(Pas.py ax B - Pas.py ax A) / (Pas.py ax C - Pas.py ax A), ?_⟩
          rw [map_div₀, ey']; field_simp
      obtain ⟨t', rfl⟩ := ht
      have t0' : 0 < t' := by
        have h : ι 0 < ι t' := by rw [map_zero]; exact t0
        exact hmono.lt_iff_lt.1 h
      have t1' : t' < 1 := by
        have h : ι t' < ι 1 := by rw [map_one]; exact t1
        exact hmono.lt_iff_lt.1 h
      refine Pas.between_of_coords ax hAC t0' t1' (hinj ?_) (hinj ?_)
      · rw [ex', map_mul]
      · rw [ey', map_mul]
    sqrtF := by
      intro X Y _ _
      rw [key, map_mul, Real.sqrt_mul_self (hlen0 X Y)]
      exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩ }⟩

end PlaneChart

/-! ### Geometry of space: charts of the planes, the length, Stewart's relation -/

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hG : SpaceGeometry P L Pl]

include hG

/-- **Every plane of a geometry of space with I–V has a real chart.** -/
theorem exists_plane_chart (β : Pl) {O E : P} (hO : O ∈ β) (hE : E ∈ β) (hOE : O ≠ E) :
    Nonempty (PChart P {Z | Z ∈ β} O E) := by
  classical
  have := planeCongruence (P := P) (L := L) (Pl := Pl) β
  have := planeArchimedes (P := P) (L := L) (Pl := Pl) β
  obtain ⟨c⟩ := exists_chart (Q := {A : P // A ∈ β})
    (M := {a : L // LiesInPlane (Point := P) a β}) (O := ⟨O, hO⟩) (E := ⟨E, hE⟩)
    (fun e => hOE (congrArg Subtype.val e))
  let X : P → ℝ := fun Z => if h : Z ∈ β then c.x ⟨Z, h⟩ else 0
  let Y : P → ℝ := fun Z => if h : Z ∈ β then c.y ⟨Z, h⟩ else 0
  have hX : ∀ Z (h : Z ∈ β), X Z = c.x ⟨Z, h⟩ := fun Z h => by simp only [X, h, ↓reduceDIte]
  have hY : ∀ Z (h : Z ∈ β), Y Z = c.y ⟨Z, h⟩ := fun Z h => by simp only [Y, h, ↓reduceDIte]
  have hs : ∀ Z W (hZ : Z ∈ β) (hW : W ∈ β), sqd X Y Z W = sqd c.x c.y ⟨Z, hZ⟩ ⟨W, hW⟩ := by
    intro Z W hZ hW; unfold sqd; rw [hX Z hZ, hX W hW, hY Z hZ, hY W hW]
  exact ⟨{
    x := X
    y := Y
    F := c.F
    xO := by rw [hX O hO]; exact c.xO
    yO := by rw [hY O hO]; exact c.yO
    xE := by rw [hX E hE]; exact c.xE
    yE := by rw [hY E hE]; exact c.yE
    inj := by
      intro Z W hZ hW h1 h2
      rw [hX Z hZ, hX W hW] at h1
      rw [hY Z hZ, hY W hW] at h2
      exact congrArg Subtype.val (c.inj ⟨Z, hZ⟩ ⟨W, hW⟩ trivial trivial h1 h2)
    memF := by
      intro Z hZ
      rw [hX Z hZ, hY Z hZ]; exact c.memF ⟨Z, hZ⟩ trivial
    onto := by
      intro a ha b hb
      obtain ⟨Z, -, h1, h2⟩ := c.onto a ha b hb
      exact ⟨Z.1, Z.2, by rw [hX Z.1 Z.2]; exact h1, by rw [hY Z.1 Z.2]; exact h2⟩
    cong := by
      intro A B U V hA hB hU hV hAB hUV
      rw [hs A B hA hB, hs U V hU hV]
      exact c.cong ⟨A, hA⟩ ⟨B, hB⟩ ⟨U, hU⟩ ⟨V, hV⟩ trivial trivial trivial trivial
        (fun e => hAB (congrArg Subtype.val e)) (fun e => hUV (congrArg Subtype.val e))
    btw := by
      intro A B C hA hB hC h
      rw [hX A hA, hX B hB, hX C hC, hY A hA, hY B hB, hY C hC]
      exact c.btw ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ trivial trivial trivial h
    btw' := by
      intro A B C t hA hB hC hAC t0 t1 ex ey
      rw [hX A hA, hX B hB, hX C hC] at ex
      rw [hY A hA, hY B hB, hY C hC] at ey
      exact c.btw' ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ t trivial trivial trivial
        (fun e => hAC (congrArg Subtype.val e)) t0 t1 ex ey
    sqrtF := by
      intro A B hA hB
      rw [hs A B hA hB]; exact c.sqrtF ⟨A, hA⟩ ⟨B, hB⟩ trivial trivial }⟩

/-- **A geometry of space with I–V having a plane has a length of segments**, normalised on a
given segment of the plane. -/
theorem exists_len (α₀ : Pl) {O E : P} (hO : O ∈ α₀) (hE : E ∈ α₀) (hOE : O ≠ E) :
    ∃ ℓ : P → P → ℝ, IsLen ℓ ∧ ℓ O E = 1 := by
  classical
  obtain ⟨c⟩ := exists_plane_chart (L := L) α₀ hO hE hOE
  have hlay : ∀ A B : P, A ≠ B → ∃ X, X ∈ ray O E ∧ SegCong A B O X :=
    fun A B h => segCong_layoff (L := L) h hOE
  let lay : P → P → P := fun A B => if h : A = B then O else Classical.choose (hlay A B h)
  have lay1 : ∀ A B, A ≠ B → lay A B ∈ ray O E := by
    intro A B h; simp only [lay, h, ↓reduceDIte]; exact (Classical.choose_spec (hlay A B h)).1
  have lay2 : ∀ A B, A ≠ B → SegCong A B O (lay A B) := by
    intro A B h; simp only [lay, h, ↓reduceDIte]; exact (Classical.choose_spec (hlay A B h)).2
  have rayα : ∀ X, X ∈ ray O E → X ∈ α₀ := fun X hX =>
    mem_plane_of_mem_ray (L := L) (α := α₀) (O := ⟨O, hO⟩) (A := ⟨E, hE⟩) hX
  have rayne : ∀ X, X ∈ ray O E → O ≠ X := fun X hX => (ne_of_mem_ray (L := L) hX).symm
  refine ⟨fun A B => if A = B then 0 else Real.sqrt (sqd c.x c.y O (lay A B)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro A; simp
  · intro A B h
    simp only [h, ↓reduceIte]
    exact Real.sqrt_pos.2 (c.sqd_pos hO (rayα _ (lay1 A B h)) (rayne _ (lay1 A B h)))
  · intro A B C D hAB hCD
    have hX := lay1 A B hAB
    have hX' := lay1 C D hCD
    have s1 := lay2 A B hAB
    have s2 := lay2 C D hCD
    have nX := rayne _ hX
    have nX' := rayne _ hX'
    simp only [hAB, hCD, ↓reduceIte]
    rw [Real.sqrt_inj (sqd_nonneg _ _ _ _) (sqd_nonneg _ _ _ _),
      ← c.cong O (lay A B) O (lay C D) hO (rayα _ hX) hO (rayα _ hX') nX nX']
    constructor
    · intro h
      exact segCong_trans (L := L) nX hAB nX' (segCong_symm (L := L) hAB nX s1)
        (segCong_trans (L := L) hAB hCD nX' h s2)
    · intro h
      exact segCong_trans (L := L) hAB nX hCD s1
        (segCong_trans (L := L) nX nX' hCD h (segCong_symm (L := L) hCD nX' s2))
  · intro A B C h
    have hAB := ne12_of_between (Line := L) h
    have hBC := ne23_of_between (Line := L) h
    have hAC := ne13_of_between (Line := L) h
    have hX := lay1 A B hAB
    have hX' := lay1 B C hBC
    have hY := lay1 A C hAC
    have nX := rayne _ hX
    have nX' := rayne _ hX'
    obtain ⟨W, hW⟩ := exists_beyond (Line := L) nX
    obtain ⟨Y', hY', sY'⟩ := segCong_layoff (L := L) hBC (ne23_of_between (Line := L) hW)
    have hb : Between O (lay A B) Y' :=
      between_of_mem_rays hW (mem_ray_self' (L := L) nX) hY'
    have sAC : SegCong A C O Y' := segCong_add (L := L) h hb (lay2 A B hAB) sY'
    have hY'ray : Y' ∈ ray O E := by
      have h1 : Y' ∈ ray O (lay A B) := mem_ray_of_between' hb
      rwa [ray_eq_of_mem hX] at h1
    have eY : Y' = lay A C := eq_of_segCong_ray (L := L) hAC hY'ray hY sAC (lay2 A C hAC)
    rw [eY] at hb sY'
    have nXY := ne23_of_between (Line := L) hb
    obtain ⟨t, t0, t1, ex, ey⟩ := c.btw O (lay A B) (lay A C) hO (rayα _ hX) (rayα _ hY) hb
    rw [c.xO] at ex
    rw [c.yO] at ey
    have hx : c.x (lay A B) = t * c.x (lay A C) := by linarith
    have hy : c.y (lay A B) = t * c.y (lay A C) := by linarith
    have e1 : sqd c.x c.y O (lay A B) = t ^ 2 * sqd c.x c.y O (lay A C) := by
      unfold sqd; rw [c.xO, c.yO, hx, hy]; ring
    have e2 : sqd c.x c.y (lay A B) (lay A C) = (1 - t) ^ 2 * sqd c.x c.y O (lay A C) := by
      unfold sqd; rw [c.xO, c.yO, hx, hy]; ring
    have e3 : sqd c.x c.y O (lay B C) = sqd c.x c.y (lay A B) (lay A C) := by
      rw [← c.cong O (lay B C) (lay A B) (lay A C) hO (rayα _ hX') (rayα _ hX) (rayα _ hY) nX' nXY]
      exact segCong_trans (L := L) nX' hBC nXY (segCong_symm (L := L) hBC nX' (lay2 B C hBC)) sY'
    simp only [hAB, hBC, hAC, ↓reduceIte]
    rw [e3, e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq t0.le,
      Real.sqrt_sq (by linarith)]
    ring
  · have e : lay O E = E := eq_of_segCong_ray (L := L) hOE (lay1 O E hOE)
      (mem_ray_self' (L := L) hOE.symm) (lay2 O E hOE) (segCong_refl (Line := L) hOE)
    have : sqd c.x c.y O E = 1 := by unfold sqd; rw [c.xO, c.yO, c.xE, c.yE]; ring
    simp only [hOE, ↓reduceIte]
    rw [e, this, Real.sqrt_one]

variable {ℓ : P → P → ℝ}

theorem IsLen.symm (hℓ : IsLen ℓ) (A B : P) : ℓ A B = ℓ B A := by
  by_cases h : A = B
  · rw [h]
  · exact (hℓ.cong A B B A h (Ne.symm h)).1
      (segCong_swap_right (Line := L) (segCong_refl (Line := L) h))

/-- **Stewart's relation**: for a point `Q` and a point `B` between `A` and `C`. -/
theorem stewart (γ : Pl) (hℓ : IsLen ℓ) {A B C : P} (Q : P) (h : Between A B C) :
    ℓ Q B ^ 2 * ℓ A C = ℓ Q A ^ 2 * ℓ B C + ℓ Q C ^ 2 * ℓ A B - ℓ A B * ℓ B C * ℓ A C := by
  have hAC := ne13_of_between (Line := L) h
  obtain ⟨β, hA, hQ, hC⟩ := exists_plane_three (L := L) γ (B := Q) hAC
  have hB : B ∈ β := mem_plane_of_between (L := L) h hA hC
  obtain ⟨c⟩ := exists_plane_chart (L := L) β hA hC hAC
  exact c.stewart hℓ hA hC hA hB hC hQ h

/-- **A perpendicular unit segment** at `O` to `OE` in a plane through `O`, `E`. -/
theorem exists_perp (hℓ : IsLen ℓ) (β : Pl) {O E : P} (hO : O ∈ β) (hE : E ∈ β) (hOE : O ≠ E) :
    ∃ Fp, Fp ∈ β ∧ ℓ O Fp = ℓ O E ∧ ℓ E Fp ^ 2 = 2 * ℓ O E ^ 2 ∧
      ∀ Z, Z ∈ β → ¬(ℓ O Z ^ 2 = ℓ O E ^ 2 ∧ ℓ E Z ^ 2 = 2 * ℓ O E ^ 2 ∧
        ℓ Fp Z ^ 2 = 2 * ℓ O E ^ 2) := by
  obtain ⟨c⟩ := exists_plane_chart (L := L) β hO hE hOE
  exact c.perp hℓ hO hE

end Space

end CC

end HilbertFoundations
