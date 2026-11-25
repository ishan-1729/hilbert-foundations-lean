import HilbertFoundations.PascalAux1

/-!
# Helper module for `Pascal.lean`: half-turns, translations and vectors

This module contains no unit of Hilbert's text. Plane geometry with I 1–2, II, III, IV.

* **Half-turns** (`ht M`): the point `X` goes to the point `X'` with `M` between `X` and `X'` and
  `MX ≡ MX'`. A half-turn is an isometry and an involution; isometries conjugate half-turns into
  half-turns (`isom_conj_ht`).
* **Dilatations** (`IsDil`): maps carrying every line to a parallel or to itself. Half-turns are
  dilatations; an isometric dilatation fixing a point `K` is the identity or the half-turn about `K`
  (`dil_fix`); hence the product of three half-turns is a half-turn (`ht_three`).
* **Translations** (`transl O`): the products `ht X * ht O`; they form a commutative group, acting
  simply transitively on the points.
* **Vectors** (`Vec O`): the points with the addition `u + v = τ_u v` (`τ_u` the translation taking
  `O` to `u`), a commutative group transferred from the translations. Isometries fixing `O` are
  additive; lines through `O` are subgroups; every line is a coset of the parallel through `O`; two
  distinct lines through `O` decompose the vectors as a direct sum.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Signs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
include hO

/-- Two points opposite to `X` with respect to `M` lie on the same half-ray from `M`. -/
theorem mem_ray_of_between_between {X M Y Y' : P} (h1 : Between X M Y) (h2 : Between X M Y') :
    Y' ∈ ray M Y := by
  have hYM : Y ≠ M := (ne23_of_between (Line := L) h1).symm
  have hY'M : Y' ≠ M := (ne23_of_between (Line := L) h2).symm
  have hXM : X ≠ M := ne12_of_between (Line := L) h1
  by_cases e : Y' = Y
  · subst e; exact mem_ray_self' (L := L) hYM
  obtain ⟨a, hXa, hMa, hYa⟩ := collinear_of_between (Line := L) h1
  have hY'a : Y' ∈ a := mem_right_of_between h2 hXa hMa
  have s1 := (OrderLin.sign_rule hMa hXa hXM.symm hXa hYa hXM hYM (ne13_of_between h1)).1 h1
  have s2 := (OrderLin.sign_rule hMa hXa hXM.symm hXa hY'a hXM hY'M (ne13_of_between h2)).1 h2
  have b1 := OrderLin.sgn_bounds M X Y
  have b2 := OrderLin.sgn_bounds M X Y'
  have b3 := OrderLin.sgn_bounds M X X
  have n1 := OrderLin.sgn_ne_zero (U := X) hYM
  have n2 := OrderLin.sgn_ne_zero (U := X) hY'M
  have n3 := OrderLin.sgn_ne_zero (U := X) hXM
  have hs : OrderLin.sgn M X Y = OrderLin.sgn M X Y' := by omega
  have nb : ¬Between Y M Y' := fun hb =>
    (OrderLin.sign_rule hMa hXa hXM.symm hYa hY'a hYM hY'M (Ne.symm e)).1 hb hs
  exact (mem_ray_or_between (L := L) (collinear_of_mem hMa hYa hY'a) hYM hY'M).resolve_right nb

end Signs

theorem perm_apply_inv {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem perm_inv_apply {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

section HalfTurns

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L]
include hC

theorem exists_opp_point {M X : P} (h : X ≠ M) : ∃ Y, Between X M Y ∧ SegCong M X M Y := by
  obtain ⟨D, hD⟩ := exists_beyond (Line := L) h
  obtain ⟨Y, hYr, hY⟩ := segCong_layoff (L := L) (Ne.symm h) (ne23_of_between (Line := L) hD)
  exact ⟨Y, between_of_mem_rays hD (mem_ray_self' (L := L) h) hYr, hY⟩

theorem opp_point_unique {M X Y Y' : P} (h1 : Between X M Y) (s1 : SegCong M X M Y)
    (h2 : Between X M Y') (s2 : SegCong M X M Y') : Y = Y' := by
  have hXM : X ≠ M := ne12_of_between (Line := L) h1
  have hYM : Y ≠ M := (ne23_of_between (Line := L) h1).symm
  exact eq_of_segCong_ray (L := L) hXM.symm (mem_ray_self' (L := L) hYM)
    (mem_ray_of_between_between h1 h2) s1 s2

/-- The point symmetric to `X` with respect to `M`. -/
noncomputable def htp (M X : P) : P := by
  classical
  exact if h : X = M then M else Classical.choose (exists_opp_point (L := L) h)

theorem htp_self (M : P) : htp (L := L) M M = M := by simp [htp]

theorem htp_spec {M X : P} (h : X ≠ M) :
    Between X M (htp (L := L) M X) ∧ SegCong M X M (htp (L := L) M X) := by
  simp only [htp, h, ↓reduceDIte]
  exact Classical.choose_spec (exists_opp_point (L := L) h)

theorem htp_eq_iff {M X Y : P} (h : X ≠ M) :
    htp (L := L) M X = Y ↔ Between X M Y ∧ SegCong M X M Y := by
  constructor
  · rintro rfl; exact htp_spec h
  · rintro ⟨h1, h2⟩
    exact opp_point_unique (htp_spec h).1 (htp_spec h).2 h1 h2

theorem htp_ne {M X : P} (h : X ≠ M) : htp (L := L) M X ≠ M :=
  (ne23_of_between (Line := L) (htp_spec h).1).symm

theorem htp_htp (M X : P) : htp (L := L) M (htp (L := L) M X) = X := by
  by_cases h : X = M
  · subst h; rw [htp_self, htp_self]
  · have hs := htp_spec (L := L) h
    rw [htp_eq_iff (htp_ne h)]
    exact ⟨between_symm hs.1, segCong_symm (L := L) (Ne.symm h) (Ne.symm (htp_ne h)) hs.2⟩

theorem htp_ray {M X Y : P} (hX : X ≠ M) (hY : Y ≠ M) (hc : Collinear (Line := L) M X Y) :
    X ∈ ray M Y ↔ htp (L := L) M X ∈ ray M (htp (L := L) M Y) := by
  obtain ⟨a, hMa, hXa, hYa⟩ := hc
  have hX'a : htp (L := L) M X ∈ a := mem_right_of_between (htp_spec hX).1 hXa hMa
  have hY'a : htp (L := L) M Y ∈ a := mem_right_of_between (htp_spec hY).1 hYa hMa
  have hX' := htp_ne (L := L) hX
  have hY' := htp_ne (L := L) hY
  have sX := (OrderLin.sign_rule hMa hXa (Ne.symm hX) hXa hX'a hX hX'
    (ne13_of_between (htp_spec hX).1)).1 (htp_spec hX).1
  have sY := (OrderLin.sign_rule hMa hXa (Ne.symm hX) hYa hY'a hY hY'
    (ne13_of_between (htp_spec hY).1)).1 (htp_spec hY).1
  have b1 := OrderLin.sgn_bounds M X X
  have b2 := OrderLin.sgn_bounds M X Y
  have b3 := OrderLin.sgn_bounds M X (htp (L := L) M X)
  have b4 := OrderLin.sgn_bounds M X (htp (L := L) M Y)
  have n1 := OrderLin.sgn_ne_zero (U := X) hX
  have n2 := OrderLin.sgn_ne_zero (U := X) hY
  have n3 := OrderLin.sgn_ne_zero (U := X) hX'
  have n4 := OrderLin.sgn_ne_zero (U := X) hY'
  rw [mem_ray, mem_ray, sameSidePt_iff_sgn hMa hXa (Ne.symm hX) hYa hXa hY hX,
    sameSidePt_iff_sgn hMa hXa (Ne.symm hX) hY'a hX'a hY' hX']
  omega

/-- A half-turn preserves the congruence of segments. -/
theorem htp_cong {M X Y : P} (hXY : X ≠ Y) :
    SegCong X Y (htp (L := L) M X) (htp (L := L) M Y) := by
  by_cases hX : X = M
  · subst hX; rw [htp_self]
    exact (htp_spec (L := L) (Ne.symm hXY)).2
  by_cases hY : Y = M
  · subst hY; rw [htp_self]
    exact segCong_swap (L := L) (htp_spec (L := L) hX).2
  have sX := htp_spec (L := L) hX
  have sY := htp_spec (L := L) hY
  by_cases hc : Collinear (Line := L) M X Y
  · obtain ⟨a, hMa, hXa, hYa⟩ := hc
    have hX'a : htp (L := L) M X ∈ a := mem_right_of_between sX.1 hXa hMa
    have hY'a : htp (L := L) M Y ∈ a := mem_right_of_between sY.1 hYa hMa
    exact seg_on_line sX.2 sY.2 hX hY (htp_ne hX) (htp_ne hY) (collinear_of_mem hMa hYa hXa)
      (collinear_of_mem hMa hY'a hX'a) hXY (htp_ray hX hY (collinear_of_mem hMa hXa hYa))
  · have F := pf (L := L) hX
    have nXMY : ¬Collinear (Line := L) X M Y := fun h => hc h.swap12
    have v := F.vertical nXMY sX.1 sY.1
    have nM : ¬Collinear (Line := L) M X Y := hc
    have nM' : ¬Collinear (Line := L) M (htp (L := L) M X) (htp (L := L) M Y) := by
      rintro ⟨a, hMa, hXa, hYa⟩
      exact hc ⟨a, hMa, mem_left_of_between sX.1 hMa hXa, mem_left_of_between sY.1 hMa hYa⟩
    exact (F.sas nM nM' sX.2 sY.2 v).1

/-- The **half-turn** (point reflection) about `M`. -/
noncomputable def ht (M : P) : Equiv.Perm P where
  toFun := htp (L := L) M
  invFun := htp (L := L) M
  left_inv := htp_htp (L := L) M
  right_inv := htp_htp (L := L) M

theorem ht_apply (M X : P) : ht (L := L) M X = htp (L := L) M X := rfl

theorem ht_isom (M : P) : ht (L := L) M ∈ isom (L := L) := fun _ _ h => htp_cong h

theorem ht_ht (M X : P) : ht (L := L) M (ht (L := L) M X) = X := htp_htp M X

theorem ht_mul_self (M : P) : ht (L := L) M * ht (L := L) M = 1 := by
  ext X; exact ht_ht M X

theorem ht_inv (M : P) : (ht (L := L) M)⁻¹ = ht (L := L) M :=
  inv_eq_of_mul_eq_one_right (ht_mul_self M)

theorem ht_self (M : P) : ht (L := L) M M = M := htp_self M

theorem ht_eq_iff {M X Y : P} (h : X ≠ M) :
    ht (L := L) M X = Y ↔ Between X M Y ∧ SegCong M X M Y := htp_eq_iff h

theorem ht_fix_iff {M X : P} : ht (L := L) M X = X ↔ X = M := by
  constructor
  · intro h
    by_contra hX
    have := (ht_eq_iff (L := L) hX).1 h
    exact ne13_of_between (Line := L) this.1 rfl
  · rintro rfl; exact ht_self _

/-- Isometries conjugate half-turns into half-turns. -/
theorem isom_conj_ht {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (M : P) :
    f * ht (L := L) M * f⁻¹ = ht (L := L) (f M) := by
  ext Y
  simp only [Equiv.Perm.mul_apply]
  by_cases hY : Y = f M
  · subst hY; simp [ht_self]
  have hX : f⁻¹ Y ≠ M := fun e => hY (by rw [← e]; simp)
  have hs := (ht_eq_iff (L := L) hX).1 rfl
  symm
  rw [ht_eq_iff (L := L) hY]
  have hb := isom_between hf hs.1
  simp only [perm_apply_inv] at hb
  refine ⟨hb, ?_⟩
  have hX' := htp_ne (L := L) hX
  have s1 := hf M (f⁻¹ Y) (Ne.symm hX)
  have s2 := hf M (ht (L := L) M (f⁻¹ Y)) (Ne.symm hX')
  simp only [perm_apply_inv] at s1
  have hfM : f M ≠ Y := Ne.symm hY
  have hfM' : f M ≠ f (ht (L := L) M (f⁻¹ Y)) := f.injective.ne (Ne.symm hX')
  exact segCong_trans (L := L) hfM (Ne.symm hX) hfM'
    (segCong_symm (L := L) (Ne.symm hX) hfM s1)
    (segCong_trans (L := L) (Ne.symm hX) (Ne.symm hX') hfM' hs.2 s2)

theorem exists_mid {X Y : P} (h : X ≠ Y) : ∃ M, ht (L := L) M X = Y := by
  let F := pf (L := L) h
  obtain ⟨Q, R, -, -, hQR, sQ, sR⟩ := F.bisector (S := Set.univ) rfl trivial trivial h
  have hQR' : Q ≠ R := OrderCore.ne_of_opp hQR
  obtain ⟨nX, nY⟩ := F.not_mem_bisector h hQR sQ sR hQR'
  obtain ⟨M, -, hM, sM⟩ := F.midpoint_of_equidistant (S := Set.univ) rfl trivial trivial trivial
    trivial hQR' h nX nY sQ sR
  exact ⟨M, (ht_eq_iff (L := L) (ne12_of_between (Line := L) hM)).2 ⟨hM, sM⟩⟩

/-- The midpoint of `X` and `Y` (`X` itself if `X = Y`). -/
noncomputable def midp (X Y : P) : P := by
  classical
  exact if h : X = Y then X else Classical.choose (exists_mid (L := L) h)

theorem ht_midp (X Y : P) : ht (L := L) (midp (L := L) X Y) X = Y := by
  by_cases h : X = Y
  · subst h; simp [midp, ht_self]
  · simp only [midp, h, ↓reduceDIte]
    exact Classical.choose_spec (exists_mid (L := L) h)

theorem ht_mid_unique {M N X : P} (h : ht (L := L) M X = ht (L := L) N X) : M = N := by
  by_cases hXM : X = M
  · subst hXM
    rw [ht_self] at h
    exact ht_fix_iff.1 h.symm
  by_cases hXN : X = N
  · subst hXN
    rw [ht_self] at h
    exact (ht_fix_iff.1 h).symm
  have h1 := (ht_eq_iff (L := L) hXM).1 rfl
  have h2 := (ht_eq_iff (L := L) hXN).1 h.symm
  exact midpoint_unique (L := L) h1.1 h2.1 h1.2 h2.2

end HalfTurns

section Dilatations

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- Two lines are **parallel or equal**. -/
def ParEq (l m : L) : Prop := l = m ∨ ¬Meets (Point := P) l m

theorem parEq_refl (l : L) : ParEq (P := P) l l := Or.inl rfl

theorem parEq_symm {l m : L} (h : ParEq (P := P) l m) : ParEq (P := P) m l := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr fun ⟨Z, h1, h2⟩ => h ⟨Z, h2, h1⟩

theorem parEq_trans {l m n : L} (h1 : ParEq (P := P) l m) (h2 : ParEq (P := P) m n) :
    ParEq (P := P) l n := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  by_cases e : l = n
  · exact Or.inl e
  right
  rintro ⟨Z, hZl, hZn⟩
  have hZm : Z ∉ m := fun hZm => h1 ⟨Z, hZl, hZm⟩
  obtain ⟨b, -, hb⟩ := exists_unique_parallel (Point := P) hZm
  have e1 := hb l ⟨hZl, h1⟩
  have e2 := hb n ⟨hZn, fun ⟨W, h3, h4⟩ => h2 ⟨W, h4, h3⟩⟩
  exact e (e1.trans e2.symm)

/-- Two lines parallel or equal with a common point are equal. -/
theorem eq_of_parEq {l m : L} (h : ParEq (P := P) l m) {Z : P} (hl : Z ∈ l) (hm : Z ∈ m) :
    l = m := by
  rcases h with h | h
  · exact h
  · exact absurd ⟨Z, hl, hm⟩ h

/-- Through every point there is a line parallel or equal to a given line. -/
theorem exists_parEq (l : L) (Z : P) : ∃ m : L, Z ∈ m ∧ ParEq (P := P) l m := by
  by_cases hZ : Z ∈ l
  · exact ⟨l, hZ, parEq_refl l⟩
  · obtain ⟨b, ⟨hb, hb'⟩, -⟩ := exists_unique_parallel (Point := P) hZ
    exact ⟨b, hb, parEq_symm (Or.inr hb')⟩

theorem parEq_unique {l m m' : L} {Z : P} (h : ParEq (P := P) l m) (h' : ParEq (P := P) l m')
    (hm : Z ∈ m) (hm' : Z ∈ m') : m = m' :=
  eq_of_parEq (parEq_trans (parEq_symm h) h') hm hm'

/-- `f` is a **dilatation**: it carries every line to a parallel line or to itself. -/
def IsDil (f : Equiv.Perm P) : Prop :=
  ∀ (X Y : P) (l m : L), X ≠ Y → X ∈ l → Y ∈ l → f X ∈ m → f Y ∈ m → ParEq (P := P) l m

theorem isDil_one : IsDil (L := L) (1 : Equiv.Perm P) := by
  intro X Y l m hXY hX hY hX' hY'
  exact Or.inl (line_unique hXY hX hY hX' hY')

theorem isDil_mul {f g : Equiv.Perm P} (hf : IsDil (L := L) f) (hg : IsDil (L := L) g) :
    IsDil (L := L) (f * g) := by
  intro X Y l m hXY hX hY hX' hY'
  have hg' : g X ≠ g Y := g.injective.ne hXY
  exact parEq_trans (hg X Y l _ hXY hX hY (mem_line_left hg') (mem_line_right hg'))
    (hf _ _ _ m hg' (mem_line_left hg') (mem_line_right hg') hX' hY')

theorem isDil_inv {f : Equiv.Perm P} (hf : IsDil (L := L) f) : IsDil (L := L) f⁻¹ := by
  intro X Y l m hXY hX hY hX' hY'
  have := hf (f⁻¹ X) (f⁻¹ Y) m l ((f⁻¹).injective.ne hXY) hX' hY'
    (by rw [perm_apply_inv]; exact hX) (by rw [perm_apply_inv]; exact hY)
  exact parEq_symm this

/-- A dilatation maps a line into the parallel through the image of one of its points. -/
theorem isDil_mem {f : Equiv.Perm P} (hf : IsDil (L := L) f) {l m : L} {X Y : P} (hX : X ∈ l)
    (hY : Y ∈ l) (hX' : f X ∈ m) (hm : ParEq (P := P) l m) : f Y ∈ m := by
  by_cases e : Y = X
  · subst e; exact hX'
  have hf' : f X ≠ f Y := f.injective.ne (Ne.symm e)
  have h1 := hf X Y l _ (Ne.symm e) hX hY (mem_line_left hf') (mem_line_right hf')
  have := parEq_unique h1 hm (mem_line_left hf') hX'
  rw [← this]; exact mem_line_right hf'

/-- Half-turns are dilatations. -/
theorem ht_isDil (M : P) : IsDil (L := L) (ht (L := L) M) := by
  intro X Y l m hXY hX hY hX' hY'
  have hX'Y' : ht (L := L) M X ≠ ht (L := L) M Y := (ht (L := L) M).injective.ne hXY
  have hisom := ht_isom (L := L) M
  -- the half-turn maps `l` into `m` and `m` into `l`
  have into1 : ∀ Z : P, Z ∈ l → ht (L := L) M Z ∈ m := by
    intro Z hZ
    have := isom_collinear hisom (collinear_of_mem hX hY hZ)
    exact mem_of_collinear this hX'Y' hX' hY'
  have into2 : ∀ Z : P, Z ∈ m → ht (L := L) M Z ∈ l := by
    intro Z hZ
    have := isom_collinear hisom (collinear_of_mem hX' hY' hZ)
    rw [ht_ht, ht_ht] at this
    exact mem_of_collinear this hXY hX hY
  by_cases e : l = m
  · exact Or.inl e
  right
  rintro ⟨Z, hZl, hZm⟩
  by_cases hZM : ht (L := L) M Z = Z
  · have hZ : Z = M := ht_fix_iff.1 hZM
    subst hZ
    have onl : ∀ W : P, W ∈ l → ht (L := L) Z W ∈ l := by
      intro W hW
      by_cases hWZ : W = Z
      · subst hWZ; rw [ht_self]; exact hW
      · exact mem_right_of_between ((ht_eq_iff (L := L) hWZ).1 rfl).1 hW hZl
    exact e (line_unique hX'Y' (onl X hX) (onl Y hY) hX' hY')
  · exact e (line_unique (Ne.symm hZM) hZl (into2 Z hZm) hZm (into1 Z hZl))

end Dilatations

section Translations

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-- An isometric dilatation fixing a point `K` is the identity or the half-turn about `K`. -/
theorem dil_fix {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hd : IsDil (L := L) f) {K : P}
    (hK : f K = K) : f = 1 ∨ f = ht (L := L) K := by
  have step : ∀ Y : P, Y ≠ K → f Y = Y ∨ f Y = ht (L := L) K Y := by
    intro Y hY
    have hl := isDil_mem hd (mem_line_left (Line := L) (Ne.symm hY)) (mem_line_right (Ne.symm hY))
      (by rw [hK]; exact mem_line_left (Line := L) (Ne.symm hY)) (parEq_refl _)
    have hfY : f Y ≠ K := fun e => hY (f.injective (e.trans hK.symm))
    have s := hf K Y (Ne.symm hY)
    rw [hK] at s
    rcases mem_ray_or_between (L := L) (collinear_of_mem (mem_line_left (Line := L) (Ne.symm hY))
      (mem_line_right (Ne.symm hY)) hl) hY hfY with hr | hb
    · left
      exact eq_of_segCong_ray (L := L) (Ne.symm hY) hr (mem_ray_self' (L := L) hY) s
        (segCong_refl (Line := L) (Ne.symm hY))
    · right
      exact ((ht_eq_iff (L := L) hY).2 ⟨hb, s⟩).symm
  by_cases h : ∃ Y, Y ≠ K ∧ f Y = Y
  · obtain ⟨Y1, hY1, hfY1⟩ := h
    left
    rcases isom_fix2 hf (Ne.symm hY1) hK hfY1 with h1 | h1
    · exact h1
    exfalso
    set l := line (Line := L) K Y1 (Ne.symm hY1)
    obtain ⟨Z, hZ⟩ := exists_not_mem (P := P) l
    have hZK : Z ≠ K := fun e => hZ (e ▸ mem_line_left _)
    have hZY1 : Z ≠ Y1 := fun e => hZ (e ▸ mem_line_right _)
    have hfZ : f Z ≠ Z := by rw [h1]; exact fun e => hZ (refl_fix_iff.1 e)
    have e1 : f Z = ht (L := L) K Z := (step Z hZK).resolve_left hfZ
    set k := line (Line := L) Y1 Z (Ne.symm hZY1)
    have hk := isDil_mem hd (mem_line_left (Line := L) (Ne.symm hZY1)) (mem_line_right (Ne.symm hZY1))
      (by rw [hfY1]; exact mem_line_left (Line := L) (Ne.symm hZY1)) (parEq_refl _)
    rw [e1] at hk
    have hKk : K ∈ k := mem_mid_of_between ((ht_eq_iff (L := L) hZK).1 rfl).1
      (mem_line_right _) hk
    have : l = k := line_unique (Ne.symm hY1) (mem_line_left _) (mem_line_right _) hKk
      (mem_line_left _)
    exact hZ (this ▸ mem_line_right _)
  · push Not at h
    right
    ext Y
    by_cases hY : Y = K
    · subst hY; rw [hK, ht_self]
    · exact (step Y hY).resolve_left (h Y hY)

/-- **The product of three half-turns is a half-turn.** -/
theorem ht_three (K M N : P) : ∃ Q : P, ht (L := L) N * ht (L := L) M * ht (L := L) K = ht Q := by
  obtain ⟨Q, hQX⟩ : ∃ Q : P, ht (L := L) Q (ht (L := L) N (ht (L := L) M K)) = K := by
    generalize ht (L := L) N (ht (L := L) M K) = X
    refine ⟨midp (L := L) K X, ?_⟩
    have h := congrArg (ht (L := L) (midp (L := L) K X)) (ht_midp (L := L) K X)
    rw [ht_ht] at h; exact h.symm
  have hφ : ht (L := L) Q * (ht (L := L) N * ht (L := L) M * ht (L := L) K) ∈ isom (L := L) :=
    (isom (L := L)).mul_mem (ht_isom Q) ((isom (L := L)).mul_mem ((isom (L := L)).mul_mem
      (ht_isom N) (ht_isom M)) (ht_isom K))
  have hφd : IsDil (L := L) (ht (L := L) Q * (ht (L := L) N * ht (L := L) M * ht (L := L) K)) :=
    isDil_mul (ht_isDil Q) (isDil_mul (isDil_mul (ht_isDil N) (ht_isDil M)) (ht_isDil K))
  have hφK : (ht (L := L) Q * (ht (L := L) N * ht (L := L) M * ht (L := L) K)) K = K := by
    simp only [Equiv.Perm.mul_apply, ht_self]; exact hQX
  rcases dil_fix hφ hφd hφK with h | h
  · refine ⟨Q, ?_⟩
    have := eq_inv_of_mul_eq_one_right h
    rw [this, ht_inv]
  · have h2 : ht (L := L) Q * (ht (L := L) N * ht (L := L) M) = 1 := by
      have : (ht (L := L) Q * (ht (L := L) N * ht (L := L) M)) * ht (L := L) K =
          1 * ht (L := L) K :=
        calc (ht (L := L) Q * (ht (L := L) N * ht (L := L) M)) * ht (L := L) K
            = ht (L := L) Q * (ht (L := L) N * ht (L := L) M * ht (L := L) K) := by
              simp only [mul_assoc]
          _ = ht (L := L) K := h
          _ = 1 * ht (L := L) K := (one_mul _).symm
      exact mul_right_cancel this
    have h3 : ht (L := L) N * ht (L := L) M = ht (L := L) Q := by
      rw [eq_inv_of_mul_eq_one_right h2, ht_inv]
    have h4 : ht (L := L) M Q = ht (L := L) N Q := by
      have := congrArg (fun g : Equiv.Perm P => ht (L := L) N (g Q)) h3
      simp only [Equiv.Perm.mul_apply, ht_ht, ht_self] at this
      rw [this]
    have hMN : M = N := ht_mid_unique h4
    subst hMN
    exact ⟨K, by rw [ht_mul_self, one_mul]⟩

/-- The **translations**: the products `ht X * ht O` (every product of two half-turns is of this
form, by `ht_three`). -/
def transl (O : P) : Subgroup (Equiv.Perm P) where
  carrier := {τ | ∃ X : P, τ = ht (L := L) X * ht (L := L) O}
  one_mem' := ⟨O, (ht_mul_self O).symm⟩
  mul_mem' := by
    rintro _ _ ⟨X, rfl⟩ ⟨Y, rfl⟩
    obtain ⟨Z, hZ⟩ := ht_three (L := L) Y O X
    exact ⟨Z, by rw [← hZ]; simp only [mul_assoc]⟩
  inv_mem' := by
    rintro _ ⟨X, rfl⟩
    obtain ⟨Z, hZ⟩ := ht_three (L := L) O X O
    refine ⟨Z, ?_⟩
    rw [← hZ, mul_inv_rev, ht_inv, ht_inv, mul_assoc, mul_assoc, ht_mul_self, mul_one]

theorem transl_comm {O : P} {a b : Equiv.Perm P} (ha : a ∈ transl (L := L) O)
    (hb : b ∈ transl (L := L) O) : a * b = b * a := by
  obtain ⟨X, rfl⟩ := ha
  obtain ⟨Y, rfl⟩ := hb
  obtain ⟨Z, hZ⟩ := ht_three (L := L) Y O X
  have h1 : ht (L := L) X * ht (L := L) O * ht (L := L) Y = ht (L := L) Y * ht (L := L) O *
      ht (L := L) X := by
    have := congrArg (·⁻¹) hZ
    simp only [mul_inv_rev, ht_inv] at this
    rw [hZ, ← this, mul_assoc]
  calc ht (L := L) X * ht (L := L) O * (ht (L := L) Y * ht (L := L) O)
      = ht (L := L) X * ht (L := L) O * ht (L := L) Y * ht (L := L) O := by simp only [mul_assoc]
    _ = ht (L := L) Y * ht (L := L) O * ht (L := L) X * ht (L := L) O := by rw [h1]
    _ = _ := by simp only [mul_assoc]

theorem transl_isom {O : P} {τ : Equiv.Perm P} (h : τ ∈ transl (L := L) O) : τ ∈ isom (L := L) := by
  obtain ⟨X, rfl⟩ := h
  exact (isom (L := L)).mul_mem (ht_isom X) (ht_isom O)

theorem transl_isDil {O : P} {τ : Equiv.Perm P} (h : τ ∈ transl (L := L) O) : IsDil (L := L) τ := by
  obtain ⟨X, rfl⟩ := h
  exact isDil_mul (ht_isDil X) (ht_isDil O)

/-- A translation is determined by the image of `O`. -/
theorem transl_ext {O : P} {a b : Equiv.Perm P} (ha : a ∈ transl (L := L) O)
    (hb : b ∈ transl (L := L) O) (h : a O = b O) : a = b := by
  obtain ⟨X, rfl⟩ := ha
  obtain ⟨Y, rfl⟩ := hb
  simp only [Equiv.Perm.mul_apply, ht_self] at h
  rw [ht_mid_unique h]

/-- The translation taking `O` to `u`. -/
noncomputable def tr (O u : P) : Equiv.Perm P := ht (L := L) (midp (L := L) O u) * ht (L := L) O

theorem tr_mem (O u : P) : tr (L := L) O u ∈ transl (L := L) O := ⟨_, rfl⟩

theorem tr_apply_O (O u : P) : tr (L := L) O u O = u := by
  simp only [tr, Equiv.Perm.mul_apply, ht_self, ht_midp]

theorem eq_tr {O : P} {τ : Equiv.Perm P} (h : τ ∈ transl (L := L) O) : τ = tr (L := L) O (τ O) :=
  transl_ext h (tr_mem O _) (tr_apply_O O _).symm

noncomputable instance translCommGroup (O : P) : CommGroup (transl (L := L) O) :=
  { (transl (L := L) O).toGroup with
    mul_comm := fun a b => Subtype.ext (transl_comm a.2 b.2) }

/-- The bijection between points and translations. -/
noncomputable def vecEquiv (O : P) : P ≃ Additive (transl (L := L) O) where
  toFun u := Additive.ofMul ⟨tr (L := L) O u, tr_mem O u⟩
  invFun τ := (Additive.toMul τ).1 O
  left_inv u := tr_apply_O O u
  right_inv τ := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_ofMul]
    exact (eq_tr (Additive.toMul τ).2).symm

end Translations

/-- **Vectors** with origin `O`: the points, with the addition of translations. -/
def Vec {P : Type u} (_O : P) : Type u := P

section Vectors

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]

noncomputable instance vecAddCommGroup (O : P) : AddCommGroup (Vec O) :=
  @Equiv.addCommGroup (Vec O) _ (vecEquiv (L := L) O) _

include hC hP

/-- A point as a vector. -/
def toV (O : P) (X : P) : Vec O := X

/-- A vector as a point. -/
def ofV {O : P} (v : Vec O) : P := v

theorem vadd_def {O : P} (u w : Vec O) : u + w = toV O (tr (L := L) O (ofV u) (ofV w)) := by
  show (vecEquiv (L := L) O).symm (vecEquiv (L := L) O u + vecEquiv (L := L) O w) = _
  simp only [vecEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, toMul_add, toMul_ofMul]
  show (tr (L := L) O u * tr (L := L) O w) O = _
  rw [Equiv.Perm.mul_apply]
  exact congrArg (tr (L := L) O u) (tr_apply_O (L := L) O w)

theorem vzero_def (O : P) : (0 : Vec O) = toV O O := rfl

theorem vneg_def {O : P} (u : Vec O) : -u = toV O (ht (L := L) O (ofV u)) := by
  apply neg_eq_of_add_eq_zero_right
  rw [vadd_def, vzero_def]
  show tr (L := L) O (ofV u) (ht (L := L) O (ofV u)) = O
  simp only [tr, Equiv.Perm.mul_apply]
  rw [ht_ht]
  have h := congrArg (ht (L := L) (midp (L := L) O (ofV u))) (ht_midp (L := L) O (ofV u))
  rw [ht_ht] at h
  exact h.symm

end Vectors

section VectorFacts

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

variable {O : P}

@[simp] theorem ofV_toV (X : P) : ofV (toV O X) = X := rfl

@[simp] theorem toV_ofV (v : Vec O) : toV O (ofV v) = v := rfl

theorem ofV_add (u w : Vec O) : ofV (u + w) = tr (L := L) O (ofV u) (ofV w) := by
  rw [vadd_def (L := L)]; rfl

theorem ofV_zero : ofV (0 : Vec O) = O := by rw [vzero_def (L := L)]; rfl

theorem ofV_neg (u : Vec O) : ofV (-u) = ht (L := L) O (ofV u) := by
  rw [vneg_def (L := L)]; rfl

theorem ofV_injective : Function.Injective (ofV (O := O)) := fun _ _ h => h

/-- The subgroup of the vectors on a line through `O`. -/
def lineSub (l : L) (hO : O ∈ l) : AddSubgroup (Vec O) where
  carrier := {v | ofV v ∈ l}
  zero_mem' := by
    show ofV (0 : Vec O) ∈ l
    rw [ofV_zero (L := L)]; exact hO
  add_mem' {u w} hu hw := by
    show ofV (u + w) ∈ l
    rw [ofV_add (L := L)]
    exact isDil_mem (transl_isDil (tr_mem O _)) hO hw (by rw [tr_apply_O]; exact hu)
      (parEq_refl l)
  neg_mem' {u} hu := by
    show ofV (-u) ∈ l
    rw [ofV_neg (L := L)]
    by_cases h : ofV u = O
    · rw [h, ht_self]; exact hO
    · exact mem_right_of_between ((ht_eq_iff (L := L) h).1 rfl).1 hu hO

theorem mem_lineSub {l : L} {hO : O ∈ l} {v : Vec O} : v ∈ lineSub (L := L) l hO ↔ ofV v ∈ l :=
  Iff.rfl

/-- **Isometries fixing `O` are additive.** -/
theorem isom_vadd {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f O = O) (u w : Vec O) :
    toV O (f (ofV (u + w))) = toV O (f (ofV u)) + toV O (f (ofV w)) := by
  rw [ofV_add (L := L), vadd_def (L := L)]
  simp only [ofV_toV]
  congr 1
  have hconj : f * tr (L := L) O (ofV u) * f⁻¹ ∈ transl (L := L) O := by
    refine ⟨f (midp (L := L) O (ofV u)), ?_⟩
    simp only [tr]
    rw [show f * (ht (L := L) (midp (L := L) O (ofV u)) * ht (L := L) O) * f⁻¹ =
        (f * ht (L := L) (midp (L := L) O (ofV u)) * f⁻¹) * (f * ht (L := L) O * f⁻¹) by group,
      isom_conj_ht hf, isom_conj_ht hf, hfO]
  have e := eq_tr hconj
  have hO' : (f * tr (L := L) O (ofV u) * f⁻¹) O = f (ofV u) := by
    simp only [Equiv.Perm.mul_apply]
    rw [show f⁻¹ O = O by rw [Equiv.Perm.inv_eq_iff_eq, hfO], tr_apply_O]
  rw [hO'] at e
  have := congrArg (fun g : Equiv.Perm P => g (f (ofV w))) e
  simp only [Equiv.Perm.mul_apply, perm_inv_apply] at this
  exact this

/-- The additive map of an isometry fixing `O`. -/
noncomputable def isomHom {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f O = O) :
    Vec O →+ Vec O where
  toFun v := toV O (f (ofV v))
  map_zero' := by
    show toV O (f (ofV (0 : Vec O))) = 0
    rw [ofV_zero (L := L), hfO, vzero_def (L := L)]
  map_add' u w := isom_vadd hf hfO u w

theorem isomHom_apply {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) (hfO : f O = O) (v : Vec O) :
    isomHom hf hfO v = toV O (f (ofV v)) := rfl

/-- The vector `A + v` for `v` on the parallel through `O` to a line `l ∋ A` lies on `l`, and
conversely: **every line is a coset of the parallel through `O`**. -/
theorem mem_line_iff_sub {l l0 : L} (hO : O ∈ l0) (hpar : ParEq (P := P) l l0) {A : P} (hA : A ∈ l)
    (X : P) : X ∈ l ↔ toV O X - toV O A ∈ lineSub (L := L) l0 hO := by
  rw [mem_lineSub, sub_eq_neg_add, ofV_add (L := L)]
  constructor
  · intro hX
    have h1 : tr (L := L) O (ofV (-toV O A)) A = O := by
      have := ofV_add (L := L) (-toV O A) (toV O A)
      rw [neg_add_cancel, ofV_zero (L := L)] at this
      exact this.symm
    exact isDil_mem (transl_isDil (tr_mem O _)) hA hX (by rw [h1]; exact hO) hpar
  · intro hX
    have h2 : tr (L := L) O A (tr (L := L) O (ofV (-toV O A)) X) = X := by
      have := ofV_add (L := L) (toV O A) (-toV O A + toV O X)
      rw [add_neg_cancel_left, ofV_add (L := L)] at this
      exact this.symm
    rw [← h2]
    exact isDil_mem (transl_isDil (tr_mem O A)) hO hX (by rw [tr_apply_O]; exact hA)
      (parEq_symm hpar)

/-- **Two distinct lines through `O` decompose the vectors as a direct sum.** -/
theorem exists_decomp {a b : L} (ha : O ∈ a) (hb : O ∈ b) (hab : a ≠ b) (v : Vec O) :
    ∃ p q : Vec O, p ∈ lineSub (L := L) a ha ∧ q ∈ lineSub (L := L) b hb ∧ v = p + q := by
  obtain ⟨m, hvm, hm⟩ := exists_parEq (P := P) b (ofV v)
  have hma : Meets (Point := P) m a := by
    by_contra hn
    exact hab (eq_of_parEq (parEq_trans hm (Or.inr hn : ParEq (P := P) m a)) hb ha).symm
  obtain ⟨p, hpm, hpa⟩ := hma
  refine ⟨toV O p, toV O (ofV v) - toV O p, hpa, ?_, by abel⟩
  exact (mem_line_iff_sub hb (parEq_symm hm) hpm (ofV v)).1 hvm

theorem decomp_unique {a b : L} (ha : O ∈ a) (hb : O ∈ b) (hab : a ≠ b) {v : Vec O}
    (h1 : v ∈ lineSub (L := L) a ha) (h2 : v ∈ lineSub (L := L) b hb) : v = 0 := by
  have : ofV v = O := eq_of_mem_of_mem hab h1 h2 ha hb
  exact ofV_injective (this.trans (ofV_zero (L := L)).symm)

end VectorFacts

end Pas

end HilbertFoundations
