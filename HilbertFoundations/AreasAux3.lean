import HilbertFoundations.AreasAux4

/-!
# Helper module for `Areas.lean`: triangles of a plane geometry and their co-ordinates

This module contains no unit of Hilbert's text. In a plane geometry with the axioms I 1–2, II,
III, IV (`PlaneCongruence`, `PlaneParallels`) and rectangular axes `ax` (Proportion.lean):

* `Tri P`: a triangle given by its three vertices; `TriRegion t` (the points of the triangle and
  of its interior: the points of the segments joining the vertex `a` with the points of the side
  `bc`), `TriInterior t` (the interior points);
* `Areas.co ax X`: the co-ordinates of a point in the field of segments `Pas.G ax`; betweenness,
  collinearity, `TriRegion`, `TriInterior` in co-ordinates (`mem_triRegion_iff`,
  `mem_triInterior_iff`, `collinear_iff_det3`);
* congruent triangles are the triangles with equal squared sides in co-ordinates (`cong_iff`);
* right angles in co-ordinates (`isRightAngle_iff_dot`), the feet of perpendiculars and the
  product of a side and the corresponding altitude (`foot_exists`, `foot_unique`,
  `len_mul_len_foot`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

/-- A **triangle** of the plane, given by its three vertices. -/
@[ext]
structure Tri (P : Type u) where
  a : P
  b : P
  c : P

/-- The **points of the triangle `t` and of its interior**: the points of the segments joining
the vertex `a` with the points of the side `bc` (extremities included). -/
def TriRegion {P : Type u} [HasBetween P] (t : Tri P) : Set P :=
  {X | ∃ Y, (Y = t.b ∨ Y = t.c ∨ Between t.b Y t.c) ∧ (X = t.a ∨ X = Y ∨ Between t.a X Y)}

/-- The **interior points of the triangle `t`**: the points between the vertex `a` and a point
within the side `bc`. -/
def TriInterior {P : Type u} [HasBetween P] (t : Tri P) : Set P :=
  {X | ∃ Y, Between t.b Y t.c ∧ Between t.a X Y}

/-- The image of a triangle under a map of the points. -/
def Tri.map {P : Type u} (f : P → P) (t : Tri P) : Tri P := ⟨f t.a, f t.b, f t.c⟩

/-- `t` is a genuine triangle: non-collinear vertices, the first two distinct. (In a plane with two
distinct points, non-collinear points are distinct; the clause `a ≠ b` only excludes the junk
"triangle" `AAA` of a plane consisting of a single point, where no line exists.) -/
def Tri.Nd {P : Type u} {L : Type v} [HasLines P L] (t : Tri P) : Prop :=
  ¬Collinear (Line := L) t.a t.b t.c ∧ t.a ≠ t.b

/-- Hilbert's congruence of triangles (§ 7, `TriCong`) for `Tri`. -/
def Tri.Cong {P : Type u} [HasSegCong P] [HasAngCong P] (t t' : Tri P) : Prop :=
  TriCong t.a t.b t.c t'.a t'.b t'.c

namespace Areas

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] [hP : PlaneParallels P L]
include hC hP

/-! ### Co-ordinates -/

/-- The co-ordinates of a point. -/
noncomputable def co (ax : Pas.Axes P L) (X : P) : Pas.G ax × Pas.G ax :=
  (Pas.px ax X, Pas.py ax X)

/-- The co-ordinates of the vertices of a triangle. -/
noncomputable def Tri.co (ax : Pas.Axes P L) (t : Tri P) : Tr (Pas.G ax) :=
  ⟨Areas.co ax t.a, Areas.co ax t.b, Areas.co ax t.c⟩

variable (ax : Pas.Axes P L)

theorem co_inj {X Y : P} (h : co ax X = co ax Y) : X = Y := (Pas.coords_bijective ax).1 h

theorem co_surj (p : Pas.G ax × Pas.G ax) : ∃ X : P, co ax X = p := by
  obtain ⟨X, hX⟩ := (Pas.coords_bijective ax).2 p
  exact ⟨X, hX⟩

/-- Betweenness in co-ordinates. -/
theorem between_iff_co {X T W : P} :
    Between X T W ↔ X ≠ W ∧ ∃ s : Pas.G ax, 0 < s ∧ s < 1 ∧ co ax T = lerp s (co ax X) (co ax W) := by
  constructor
  · intro h
    obtain ⟨s, h0, h1, e1, e2⟩ := Pas.between_coords ax h
    refine ⟨ne13_of_between (Line := L) h, s, h0, h1, ?_⟩
    show (Pas.px ax T, Pas.py ax T) = (Pas.px ax X + s * (Pas.px ax W - Pas.px ax X),
      Pas.py ax X + s * (Pas.py ax W - Pas.py ax X))
    exact Prod.ext (by simp only; linarith) (by simp only; linarith)
  · rintro ⟨hXW, s, h0, h1, e⟩
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [co, lerp] at e1 e2
    exact Pas.between_of_coords ax hXW h0 h1 (by linarith) (by linarith)

theorem lerp_zero (p q : Pas.G ax × Pas.G ax) : lerp 0 p q = p := by
  simp [lerp]

theorem lerp_one (p q : Pas.G ax × Pas.G ax) : lerp 1 p q = q := by
  refine Prod.ext ?_ ?_ <;> simp only [lerp] <;> ring

theorem lerp_self (s : Pas.G ax) (p : Pas.G ax × Pas.G ax) : lerp s p p = p := by
  refine Prod.ext ?_ ?_ <;> simp only [lerp] <;> ring

/-- The closed segment in co-ordinates. -/
theorem segE_iff {X T W : P} :
    (T = X ∨ T = W ∨ Between X T W) ↔
      ∃ s : Pas.G ax, 0 ≤ s ∧ s ≤ 1 ∧ co ax T = lerp s (co ax X) (co ax W) := by
  constructor
  · rintro (rfl | rfl | h)
    · exact ⟨0, le_rfl, zero_le_one, (lerp_zero ax _ _).symm⟩
    · exact ⟨1, zero_le_one, le_rfl, (lerp_one ax _ _).symm⟩
    · obtain ⟨-, s, h0, h1, e⟩ := (between_iff_co ax).1 h
      exact ⟨s, h0.le, h1.le, e⟩
  · rintro ⟨s, h0, h1, e⟩
    by_cases hXW : X = W
    · subst hXW; rw [lerp_self] at e; exact Or.inl (co_inj ax e)
    rcases h0.eq_or_lt with rfl | h0
    · rw [lerp_zero] at e; exact Or.inl (co_inj ax e)
    rcases h1.eq_or_lt with rfl | h1
    · rw [lerp_one] at e; exact Or.inr (Or.inl (co_inj ax e))
    exact Or.inr (Or.inr ((between_iff_co ax).2 ⟨hXW, s, h0, h1, e⟩))

/-- Collinearity in co-ordinates. -/
theorem collinear_iff_det3 {X Y Z : P} :
    Collinear (Line := L) X Y Z ↔ det3 (co ax X) (co ax Y) (co ax Z) = 0 := by
  by_cases hXY : X = Y
  · subst hXY
    have : det3 (co ax X) (co ax X) (co ax Z) = 0 := by unfold det3; ring
    rw [iff_true_intro this, iff_true]
    by_cases hXZ : X = Z
    · subst hXZ
      obtain ⟨l, hl⟩ := Pas.hl_of_ne (L := L) ax.hOE X
      exact ⟨l, hl, hl, hl⟩
    · obtain ⟨l, h1, h2⟩ := exists_line (Line := L) hXZ
      exact ⟨l, h1, h1, h2⟩
  · rw [Pas.collinear_iff_side ax hXY]
    rfl

theorem nd_iff {t : Tri P} : t.Nd (L := L) ↔ (Tri.co ax t).nd := by
  unfold Tri.Nd Tr.nd Tr.D
  rw [collinear_iff_det3 ax]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, fun e => h ?_⟩
    show det3 (co ax t.a) (co ax t.b) (co ax t.c) = 0
    rw [e]; unfold det3; ring

theorem ax_of_ne {A B : P} (h : A ≠ B) : Nonempty (Pas.Axes P L) :=
  ⟨(Pas.exists_axes (L := L) h).choose⟩

omit hC hP in
/-- `p = a + ρ ((b + σ (c - b)) - a)`, `ρ, σ ∈ [0, 1]`, describes the closed triangle. -/
theorem mem_iff_lerp {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {t : Tr K}
    (ht : t.nd) (p : K × K) :
    t.mem p ↔ ∃ ρ σ : K, 0 ≤ ρ ∧ ρ ≤ 1 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧ p = lerp ρ t.a (lerp σ t.b t.c) := by
  rw [Tr.mem_iff_bary ht]
  constructor
  · rintro ⟨α, β, γ, h1, h2, h3, hs, rfl⟩
    by_cases h0 : β + γ = 0
    · have hb : β = 0 := by linarith
      have hc : γ = 0 := by linarith
      refine ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one, ?_⟩
      subst hb hc
      have : α = 1 := by linarith
      subst this
      ext <;> simp [comb, lerp]
    · have hpos : 0 < β + γ := lt_of_le_of_ne (by linarith) (Ne.symm h0)
      refine ⟨β + γ, γ / (β + γ), by linarith, by linarith, div_nonneg h3 hpos.le,
        (div_le_one hpos).2 (by linarith), ?_⟩
      have hα : α = 1 - β - γ := by linarith
      subst hα
      ext <;> simp only [comb, lerp] <;> field_simp <;> ring
  · rintro ⟨ρ, σ, h1, h2, h3, h4, rfl⟩
    refine ⟨1 - ρ, ρ * (1 - σ), ρ * σ, by linarith, mul_nonneg h1 (by linarith), mul_nonneg h1 h3,
      by ring, ?_⟩
    ext <;> simp only [comb, lerp] <;> ring

omit hC hP in
/-- `p = a + ρ ((b + σ (c - b)) - a)`, `ρ, σ ∈ (0, 1)`, describes the interior. -/
theorem int_iff_lerp {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {t : Tr K}
    (ht : t.nd) (p : K × K) :
    t.int p ↔ ∃ ρ σ : K, 0 < ρ ∧ ρ < 1 ∧ 0 < σ ∧ σ < 1 ∧ p = lerp ρ t.a (lerp σ t.b t.c) := by
  rw [Tr.int_iff_bary ht]
  constructor
  · rintro ⟨α, β, γ, h1, h2, h3, hs, rfl⟩
    have hpos : 0 < β + γ := by linarith
    refine ⟨β + γ, γ / (β + γ), hpos, by linarith, div_pos h3 hpos,
      (div_lt_one hpos).2 (by linarith), ?_⟩
    have hα : α = 1 - β - γ := by linarith
    subst hα
    ext <;> simp only [comb, lerp] <;> field_simp <;> ring
  · rintro ⟨ρ, σ, h1, h2, h3, h4, rfl⟩
    refine ⟨1 - ρ, ρ * (1 - σ), ρ * σ, by linarith, mul_pos h1 (by linarith), mul_pos h1 h3,
      by ring, ?_⟩
    ext <;> simp only [comb, lerp] <;> ring

/-- **The closed triangle in co-ordinates.** -/
theorem mem_triRegion_iff {t : Tri P} (ht : t.Nd (L := L)) (X : P) :
    X ∈ TriRegion t ↔ (Tri.co ax t).mem (co ax X) := by
  rw [mem_iff_lerp ((nd_iff ax).1 ht)]
  constructor
  · rintro ⟨Y, hY, hX⟩
    obtain ⟨σ, s0, s1, eY⟩ := (segE_iff ax (X := t.b) (T := Y) (W := t.c)).1
      (by rcases hY with h | h | h <;> tauto)
    obtain ⟨ρ, r0, r1, eX⟩ := (segE_iff ax (X := t.a) (T := X) (W := Y)).1
      (by rcases hX with h | h | h <;> tauto)
    exact ⟨ρ, σ, r0, r1, s0, s1, by rw [eX, eY]; rfl⟩
  · rintro ⟨ρ, σ, r0, r1, s0, s1, e⟩
    obtain ⟨Y, hY⟩ := co_surj ax (lerp σ (co ax t.b) (co ax t.c))
    refine ⟨Y, ?_, ?_⟩
    · have := (segE_iff ax (X := t.b) (T := Y) (W := t.c)).2 ⟨σ, s0, s1, hY⟩
      rcases this with h | h | h <;> tauto
    · have := (segE_iff ax (X := t.a) (T := X) (W := Y)).2 ⟨ρ, r0, r1, by rw [e, hY]; rfl⟩
      rcases this with h | h | h <;> tauto

/-- **The interior of a triangle in co-ordinates.** -/
theorem mem_triInterior_iff {t : Tri P} (ht : t.Nd (L := L)) (X : P) :
    X ∈ TriInterior t ↔ (Tri.co ax t).int (co ax X) := by
  have hnd := (nd_iff ax).1 ht
  rw [int_iff_lerp hnd]
  constructor
  · rintro ⟨Y, hY, hX⟩
    obtain ⟨-, σ, s0, s1, eY⟩ := (between_iff_co ax).1 hY
    obtain ⟨-, ρ, r0, r1, eX⟩ := (between_iff_co ax).1 hX
    exact ⟨ρ, σ, r0, r1, s0, s1, by rw [eX, eY]; rfl⟩
  · rintro ⟨ρ, σ, r0, r1, s0, s1, e⟩
    obtain ⟨Y, hY⟩ := co_surj ax (lerp σ (co ax t.b) (co ax t.c))
    have hbc : t.b ≠ t.c := fun h => Tr.nd_ne_bc hnd (by simp only [Tri.co]; rw [h])
    have haY : t.a ≠ Y := by
      intro h
      apply hnd
      have : co ax t.a = lerp σ (co ax t.b) (co ax t.c) := by rw [h, hY]
      show det3 (co ax t.a) (co ax t.b) (co ax t.c) = 0
      rw [this]; unfold det3 lerp; ring
    refine ⟨Y, (between_iff_co ax).2 ⟨hbc, σ, s0, s1, hY⟩,
      (between_iff_co ax).2 ⟨haY, ρ, r0, r1, by rw [e, hY]; rfl⟩⟩

/-- The triangle whose vertices have the given co-ordinates. -/
noncomputable def unco (r : Tr (Pas.G ax)) : Tri P :=
  ⟨(co_surj ax r.a).choose, (co_surj ax r.b).choose, (co_surj ax r.c).choose⟩

theorem co_unco (r : Tr (Pas.G ax)) : Tri.co ax (unco (L := L) ax r) = r := by
  refine Tr.ext ?_ ?_ ?_ <;> simp only [Tri.co, unco] <;>
    first
    | rw [(co_surj ax r.a).choose_spec]
    | rw [(co_surj ax r.b).choose_spec]
    | rw [(co_surj ax r.c).choose_spec]

theorem unco_co (t : Tri P) : unco ax (Tri.co ax t) = t := by
  ext
  · exact co_inj ax (co_surj ax (co ax t.a)).choose_spec
  · exact co_inj ax (co_surj ax (co ax t.b)).choose_spec
  · exact co_inj ax (co_surj ax (co ax t.c)).choose_spec

theorem tri_co_inj {t t' : Tri P} (h : Tri.co ax t = Tri.co ax t') : t = t' := by
  rw [← unco_co ax t, h, unco_co]

/-- The interior of a triangle contained in another lies in the interior of the other. -/
theorem triInterior_mono {t t' : Tri P} (ht : t.Nd (L := L)) (ht' : t'.Nd (L := L))
    (h : TriRegion t ⊆ TriRegion t') : TriInterior t ⊆ TriInterior t' := by
  obtain ⟨ax⟩ := ax_of_ne (L := L) ht.2
  intro X hX
  rw [mem_triInterior_iff ax ht] at hX
  rw [mem_triInterior_iff ax ht']
  refine Tr.int_of_sub ((nd_iff ax).1 ht) ((nd_iff ax).1 ht') (fun p hp => ?_) hX
  obtain ⟨Y, rfl⟩ := co_surj ax p
  rw [← mem_triRegion_iff ax ht']
  exact h ((mem_triRegion_iff ax ht Y).2 hp)

theorem triInterior_sub {t : Tri P} : TriInterior t ⊆ TriRegion t := by
  rintro X ⟨Y, hY, hX⟩
  exact ⟨Y, Or.inr (Or.inr hY), Or.inr (Or.inr hX)⟩

/-! ### Lengths, right angles and feet of perpendiculars -/

theorem len_sq_co (X Y : P) : Pas.len ax X Y * Pas.len ax X Y =
    ((co ax X).1 - (co ax Y).1) * ((co ax X).1 - (co ax Y).1) +
      ((co ax X).2 - (co ax Y).2) * ((co ax X).2 - (co ax Y).2) :=
  Pas.len_sq ax X Y

theorem len_eq_of_sq {X Y X' Y' : P}
    (h : Pas.len ax X Y * Pas.len ax X Y = Pas.len ax X' Y' * Pas.len ax X' Y') :
    Pas.len ax X Y = Pas.len ax X' Y' := by
  have h1 := Pas.len_nonneg ax X Y
  have h2 := Pas.len_nonneg ax X' Y'
  nlinarith [mul_self_nonneg (Pas.len ax X Y - Pas.len ax X' Y'),
    mul_self_nonneg (Pas.len ax X Y + Pas.len ax X' Y')]

/-- **Congruent triangles in co-ordinates**: Hilbert's congruence of triangles is the equality
of the squared sides (Theorem 16 and the distance formula). -/
theorem cong_iff {t t' : Tri P} (ht : t.Nd (L := L)) (ht' : t'.Nd (L := L)) :
    t.Cong t' ↔ KCong (Tri.co ax t) (Tri.co ax t') := by
  obtain ⟨hab, hcb, hac⟩ := Pas.nc_ne ax ht.1
  obtain ⟨hab', hcb', hac'⟩ := Pas.nc_ne ax ht'.1
  have e : ∀ {X Y X' Y' : P}, X ≠ Y → X' ≠ Y' →
      (SegCong X Y X' Y' ↔ sqd (co ax X) (co ax Y) = sqd (co ax X') (co ax Y')) := by
    intro X Y X' Y' h h'
    rw [← Pas.len_eq_iff ax h h']
    constructor
    · intro e; unfold sqd; rw [← len_sq_co, ← len_sq_co, e]
    · intro e; apply len_eq_of_sq; unfold sqd at e; rw [len_sq_co, len_sq_co]; exact e
  constructor
  · rintro ⟨s1, s2, s3, -⟩
    exact ⟨(e hab hab').1 s1, (e hac hac').1 s2, (e (Ne.symm hcb) (Ne.symm hcb')).1 s3⟩
  · rintro ⟨s1, s2, s3⟩
    exact theorem16 ht.1 ht'.1 ((e hab hab').2 s1) ((e hac hac').2 s2)
      ((e (Ne.symm hcb) (Ne.symm hcb')).2 s3)

/-- The dot product of `X - F` and `Z - F`. -/
noncomputable def dotc (F X Z : P) : Pas.G ax :=
  ((co ax X).1 - (co ax F).1) * ((co ax Z).1 - (co ax F).1) +
    ((co ax X).2 - (co ax F).2) * ((co ax Z).2 - (co ax F).2)

theorem co_ne {X Y : P} (h : X ≠ Y) : co ax X ≠ co ax Y := fun e => h (co_inj ax e)

/-- **Right angles in co-ordinates**: `∠XFZ` is a right angle iff `X ≠ F`, `Z ≠ F` and the dot
product of `X - F` and `Z - F` vanishes. -/
theorem isRightAngle_iff_dot {X F Z : P} :
    IsRightAngle (L := L) X F Z ↔ X ≠ F ∧ Z ≠ F ∧ dotc ax F X Z = 0 := by
  -- the reflection `X'` of `X` in `F`
  obtain ⟨X', hX'⟩ := co_surj ax (2 * (co ax F).1 - (co ax X).1, 2 * (co ax F).2 - (co ax X).2)
  have key : ∀ (_ : X ≠ F) (_ : Z ≠ F), (dotc ax F X Z = 0 ↔
      Pas.len ax Z X * Pas.len ax Z X = Pas.len ax Z X' * Pas.len ax Z X') := by
    intro _ _
    rw [len_sq_co, len_sq_co, hX']
    simp only [dotc]
    constructor
    · intro h; linear_combination (-4 : Pas.G ax) * h
    · intro h; linear_combination (-1 / 4 : Pas.G ax) * h
  -- the cross product does not vanish when the dot product does
  have ndc : X ≠ F → Z ≠ F → dotc ax F X Z = 0 → ¬Collinear (Line := L) X F Z := by
    intro h1 h2 h3 hc
    rw [collinear_iff_det3 ax] at hc
    have n1 := co_ne ax h1
    have n2 := co_ne ax h2
    have hu : 0 < ((co ax X).1 - (co ax F).1) * ((co ax X).1 - (co ax F).1) +
        ((co ax X).2 - (co ax F).2) * ((co ax X).2 - (co ax F).2) := by
      by_contra hh
      apply n1
      have a := mul_self_nonneg ((co ax X).1 - (co ax F).1)
      have b := mul_self_nonneg ((co ax X).2 - (co ax F).2)
      exact Prod.ext (by nlinarith) (by nlinarith)
    have hv : 0 < ((co ax Z).1 - (co ax F).1) * ((co ax Z).1 - (co ax F).1) +
        ((co ax Z).2 - (co ax F).2) * ((co ax Z).2 - (co ax F).2) := by
      by_contra hh
      apply n2
      have a := mul_self_nonneg ((co ax Z).1 - (co ax F).1)
      have b := mul_self_nonneg ((co ax Z).2 - (co ax F).2)
      exact Prod.ext (by nlinarith) (by nlinarith)
    have lag : (dotc ax F X Z) * (dotc ax F X Z) + det3 (co ax X) (co ax F) (co ax Z) *
        det3 (co ax X) (co ax F) (co ax Z) =
        (((co ax X).1 - (co ax F).1) * ((co ax X).1 - (co ax F).1) +
          ((co ax X).2 - (co ax F).2) * ((co ax X).2 - (co ax F).2)) *
        (((co ax Z).1 - (co ax F).1) * ((co ax Z).1 - (co ax F).1) +
          ((co ax Z).2 - (co ax F).2) * ((co ax Z).2 - (co ax F).2)) := by
      simp only [dotc]; unfold det3; ring
    rw [h3, hc] at lag
    have := mul_pos hu hv
    linarith
  -- `F` lies between `X` and `X'`, and `FX ≡ FX'`
  have betw : X ≠ F → Between X F X' := by
    intro h1
    refine (between_iff_co ax).2 ⟨?_, 1 / 2, by norm_num, by norm_num, ?_⟩
    · intro e; subst e; apply h1; apply co_inj ax
      have e1 := congrArg Prod.fst hX'; have e2 := congrArg Prod.snd hX'
      simp only at e1 e2
      exact Prod.ext (by linear_combination e1 / 2) (by linear_combination e2 / 2)
    · rw [hX']; refine Prod.ext ?_ ?_ <;> simp only [lerp] <;> ring
  have cong : X ≠ F → SegCong F X F X' := by
    intro h1
    have hb := betw h1
    rw [← Pas.len_eq_iff ax (Ne.symm h1) (ne23_of_between (Line := L) hb)]
    apply len_eq_of_sq
    rw [len_sq_co, len_sq_co, hX']; ring
  have aux : ∀ (_ : ¬Collinear (Line := L) X F Z), Z ≠ X ∧ Z ≠ X' ∧
      ¬Collinear (Line := L) X' F Z := by
    intro hn
    obtain ⟨h1, -, -⟩ := Pas.nc_ne ax hn
    have hb := betw h1
    have nX'FZ : ¬Collinear (Line := L) X' F Z := not_collinear_of_between hn hb
    have hX'F : X' ≠ F := Ne.symm (ne23_of_between (Line := L) hb)
    refine ⟨fun e => ?_, fun e => ?_, nX'FZ⟩
    · rw [e] at hn; exact hn (collinear_of_ne (Line := L) h1)
    · rw [e] at nX'FZ; exact nX'FZ (collinear_of_ne (Line := L) hX'F)
  constructor
  · rintro ⟨hn, C, hC, hc⟩
    obtain ⟨h1, h2, -⟩ := Pas.nc_ne ax hn
    obtain ⟨hZX, hZX', nX'FZ⟩ := aux hn
    refine ⟨h1, h2, (key h1 h2).2 ?_⟩
    have hb := betw h1
    have hray : ray F X' = ray F C := ray_eq_of_mem (Pas.mem_ray_of_between_between (L := L) hC hb)
    have nZFC : ¬Collinear (Line := L) Z F C := fun h =>
      (not_collinear_of_between hn hC) h.swap13
    have hc' : AngCong X F Z Z F X' :=
      angCong_of_sameAngle hn nZFC (sameAngle_refl X F Z)
        (sameAngle_of_ray_eq rfl hray.symm) hc
    have hc'' : AngCong X F Z X' F Z :=
      angCong_swap_right hn (fun h => nX'FZ h.swap13) hc'
    have t := theorem10 (A := F) (B := X) (C := Z) (A' := F) (B' := X') (C' := Z)
      (fun h => hn h.swap12) (fun h => nX'FZ h.swap12) (cong h1)
      (segCong_refl (Line := L) (Ne.symm h2)) hc''
    rw [(Pas.len_eq_iff ax hZX hZX').2 (segCong_swap_left (Line := L)
      (segCong_swap_right (Line := L) t.2.2.1))]
  · rintro ⟨h1, h2, h3⟩
    have hn := ndc h1 h2 h3
    obtain ⟨hZX, hZX', nX'FZ⟩ := aux hn
    have hb := betw h1
    have sl := len_eq_of_sq ax ((key h1 h2).1 h3)
    have s : SegCong Z X Z X' := (Pas.len_eq_iff ax hZX hZX').1 sl
    have t := theorem16 (A := F) (B := X) (C := Z) (A' := F) (B' := X') (C' := Z)
      (fun h => hn h.swap12) (fun h => nX'FZ h.swap12) (cong h1)
      (segCong_refl (Line := L) (Ne.symm h2))
      (segCong_swap_left (Line := L) (segCong_swap_right (Line := L) s))
    exact ⟨hn, X', hb, angCong_swap_right hn nX'FZ t.2.2.2.1⟩

omit hC hP in
theorem foot_K {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {b c : K × K}
    (hbc : b ≠ c) (a : K × K) : ∃ τ : K, det3 b c (lerp τ b c) = 0 ∧
      (a.1 - (lerp τ b c).1) * (c.1 - b.1) + (a.2 - (lerp τ b c).2) * (c.2 - b.2) = 0 := by
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  obtain ⟨a1, a2⟩ := a
  have hn : (c1 - b1) * (c1 - b1) + (c2 - b2) * (c2 - b2) ≠ 0 := by
    intro h
    apply hbc
    have e1 : c1 - b1 = 0 := by nlinarith [mul_self_nonneg (c1 - b1), mul_self_nonneg (c2 - b2)]
    have e2 : c2 - b2 = 0 := by nlinarith [mul_self_nonneg (c1 - b1), mul_self_nonneg (c2 - b2)]
    simp only [Prod.mk.injEq]; constructor <;> linarith
  have e := div_mul_cancel₀ ((a1 - b1) * (c1 - b1) + (a2 - b2) * (c2 - b2)) hn
  refine ⟨((a1 - b1) * (c1 - b1) + (a2 - b2) * (c2 - b2)) /
    ((c1 - b1) * (c1 - b1) + (c2 - b2) * (c2 - b2)), ?_, ?_⟩
  · unfold det3 lerp; simp only; ring
  · unfold lerp; simp only
    linear_combination (-1 : K) * e

omit hC hP in
theorem prod_K {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c f x : K × K}
    (hf : det3 b c f = 0) (hx : det3 b c x = 0) (hxf : x ≠ f)
    (hd : (a.1 - f.1) * (x.1 - f.1) + (a.2 - f.2) * (x.2 - f.2) = 0) :
    ((b.1 - c.1) * (b.1 - c.1) + (b.2 - c.2) * (b.2 - c.2)) *
      ((a.1 - f.1) * (a.1 - f.1) + (a.2 - f.2) * (a.2 - f.2)) = det3 b c a * det3 b c a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  obtain ⟨f1, f2⟩ := f
  obtain ⟨x1, x2⟩ := x
  unfold det3 at *
  simp only at *
  have hw : 0 < (x1 - f1) * (x1 - f1) + (x2 - f2) * (x2 - f2) := by
    by_contra h
    apply hxf
    have e1 : x1 - f1 = 0 := by nlinarith [mul_self_nonneg (x1 - f1), mul_self_nonneg (x2 - f2)]
    have e2 : x2 - f2 = 0 := by nlinarith [mul_self_nonneg (x1 - f1), mul_self_nonneg (x2 - f2)]
    simp only [Prod.mk.injEq]; constructor <;> linarith
  have hcr : (c1 - b1) * (x2 - f2) - (c2 - b2) * (x1 - f1) = 0 := by linear_combination hx - hf
  have hvu : (a1 - f1) * (c1 - b1) + (a2 - f2) * (c2 - b2) = 0 := by
    have id : ((a1 - f1) * (c1 - b1) + (a2 - f2) * (c2 - b2)) *
        ((x1 - f1) * (x1 - f1) + (x2 - f2) * (x2 - f2)) =
        ((a1 - f1) * (x1 - f1) + (a2 - f2) * (x2 - f2)) *
          ((c1 - b1) * (x1 - f1) + (c2 - b2) * (x2 - f2)) +
        ((a1 - f1) * (x2 - f2) - (a2 - f2) * (x1 - f1)) *
          ((c1 - b1) * (x2 - f2) - (c2 - b2) * (x1 - f1)) := by ring
    rw [hd, hcr] at id
    simp only [zero_mul, mul_zero, add_zero] at id
    exact (mul_eq_zero.1 id).resolve_right hw.ne'
  have hdet : (c1 - b1) * (a2 - b2) - (c2 - b2) * (a1 - b1) =
      (c1 - b1) * (a2 - f2) - (c2 - b2) * (a1 - f1) := by linear_combination hf
  rw [hdet]
  linear_combination ((a1 - f1) * (c1 - b1) + (a2 - f2) * (c2 - b2)) * hvu

/-- **The foot of the perpendicular** from a point `A` off the line `BC` exists. -/
theorem foot_exists {A B C : P} (hBC : B ≠ C) (hA : ¬Collinear (Line := L) B C A) :
    ∃ F X : P, Collinear (Line := L) B C F ∧ Collinear (Line := L) B C X ∧ X ≠ F ∧
      IsRightAngle (L := L) A F X := by
  obtain ⟨ax⟩ := ax_of_ne (L := L) hBC
  obtain ⟨τ, h1, h2⟩ := foot_K (co_ne ax hBC) (co ax A)
  obtain ⟨F, hF⟩ := co_surj ax (lerp τ (co ax B) (co ax C))
  rw [← hF] at h1 h2
  have hFl : Collinear (Line := L) B C F := (collinear_iff_det3 ax).2 h1
  have hAF : A ≠ F := by
    rintro rfl; exact hA hFl
  have hBl : Collinear (Line := L) B C B := (collinear_iff_det3 ax).2 (by unfold det3; ring)
  have hCl : Collinear (Line := L) B C C := (collinear_iff_det3 ax).2 (by unfold det3; ring)
  have hdot : ∀ X : P, (∃ μ : Pas.G ax, co ax X - co ax F = μ • (co ax C - co ax B)) →
      dotc ax F A X = 0 := by
    rintro X ⟨μ, hμ⟩
    have e1 := congrArg Prod.fst hμ
    have e2 := congrArg Prod.snd hμ
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
    simp only [dotc]
    rw [show (co ax X).1 - (co ax F).1 = μ * ((co ax C).1 - (co ax B).1) by linarith,
      show (co ax X).2 - (co ax F).2 = μ * ((co ax C).2 - (co ax B).2) by linarith]
    linear_combination μ * h2
  have hτ : co ax F = lerp τ (co ax B) (co ax C) := hF
  by_cases hBF : B = F
  · refine ⟨F, C, hFl, hCl, ?_, (isRightAngle_iff_dot ax).2 ⟨hAF, ?_, hdot C ⟨1 - τ, ?_⟩⟩⟩
    · rw [← hBF]; exact Ne.symm hBC
    · rw [← hBF]; exact Ne.symm hBC
    · rw [hτ]; refine Prod.ext ?_ ?_ <;> simp [lerp] <;> ring
  · refine ⟨F, B, hFl, hBl, hBF, (isRightAngle_iff_dot ax).2 ⟨hAF, hBF, hdot B ⟨-τ, ?_⟩⟩⟩
    rw [hτ]; refine Prod.ext ?_ ?_ <;> simp [lerp]

/-- **Side times altitude**: if `F` is the foot of the perpendicular from `A` to the line `BC`,
then `BC · AF = |(C - B) × (A - B)|` in the field of segments. -/
theorem len_mul_len_foot {A B C F X : P} (hF : Collinear (Line := L) B C F)
    (hX : Collinear (Line := L) B C X) (hXF : X ≠ F) (hr : IsRightAngle (L := L) A F X) :
    Pas.len ax B C * Pas.len ax A F = |det3 (co ax B) (co ax C) (co ax A)| := by
  rw [collinear_iff_det3 ax] at hF hX
  obtain ⟨-, -, hd⟩ := (isRightAngle_iff_dot ax).1 hr
  have key := prod_K hF hX (co_ne ax hXF) hd
  have hsq : (Pas.len ax B C * Pas.len ax A F) * (Pas.len ax B C * Pas.len ax A F) =
      |det3 (co ax B) (co ax C) (co ax A)| * |det3 (co ax B) (co ax C) (co ax A)| := by
    rw [abs_mul_abs_self, ← key, ← len_sq_co, ← len_sq_co]; ring
  exact (mul_self_inj (mul_nonneg (Pas.len_nonneg ax B C) (Pas.len_nonneg ax A F))
    (abs_nonneg _)).1 hsq

end Areas

end HilbertFoundations
