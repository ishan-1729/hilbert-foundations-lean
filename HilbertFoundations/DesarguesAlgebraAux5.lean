import HilbertFoundations.DesarguesAlgebraAux4

/-!
# Helper for §§ 27, 29, 30: co-ordinates, Theorem 34, the plane inside a space, Theorem 35

Helper module of `DesarguesAlgebra.lean`.

* Co-ordinates (`Frame.xc`, `Frame.yc`) and the point `ptOf F x y` with given co-ordinates; the points
  of a line are `x = (x_B - x_A) t + x_A`, `y = (y_B - y_A) t + y_A` (`mem_ln_iff_coord`).
* **Theorem 34** (`th34_line`, `th34_converse`, `th34_right`).
* `PlaneInSpace P L P' L' Pl'`: the plane geometry `(P, L)` "regarded as a part of" the space
  geometry `(P', L', Pl')`: bijections of its points with the points of a plane `α` and of its lines
  with the lines lying in `α`, preserving and reflecting incidence and betweenness.
* `planeInSpace F`: a desarguesian plane is the plane `z = 0` of the coordinate space
  `AffPt K (Vec F × K)` over `K = (Seg F)ᵐᵒᵖ` (the segments acting on the right).
* `desarguesTheorem_of_planeInSpace`: conversely, a plane of a space geometry satisfying I and III
  satisfies Desargues's theorem.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v u' v' w'

namespace DesAlg

/-! ## Co-ordinates and Theorem 34 -/

section Alg

variable {D : Type*} [DivisionRing D]

/-- The parametrized line `x = v₁ t + p₁`, `y = v₂ t + p₂` is the solution set of a linear equation
with the coefficients on the left. -/
theorem line_eq_alg (p1 p2 v1 v2 : D) (h : v1 ≠ 0 ∨ v2 ≠ 0) :
    ∃ a b c : D, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ x y : D, (∃ t, x = v1 * t + p1 ∧ y = v2 * t + p2) ↔ a * x + b * y + c = 0 := by
  by_cases hv1 : v1 = 0
  · have hv2 : v2 ≠ 0 := h.resolve_left (not_not.2 hv1)
    refine ⟨1, 0, -p1, Or.inl one_ne_zero, fun x y => ?_⟩
    subst hv1
    constructor
    · rintro ⟨t, hx, -⟩; rw [hx]; simp
    · intro hxy
      have hx : x = p1 := by
        have : x + -p1 = 0 := by simpa using hxy
        rwa [← sub_eq_add_neg, sub_eq_zero] at this
      exact ⟨v2⁻¹ * (y - p2), by rw [hx]; simp,
        by rw [← mul_assoc, mul_inv_cancel₀ hv2, one_mul, sub_add_cancel]⟩
  · refine ⟨-(v2 * v1⁻¹), 1, -(-(v2 * v1⁻¹) * p1 + p2), Or.inr one_ne_zero, fun x y => ?_⟩
    have key : -(v2 * v1⁻¹) * v1 = -v2 := by rw [neg_mul, mul_assoc, inv_mul_cancel₀ hv1, mul_one]
    constructor
    · rintro ⟨t, hx, hy⟩
      rw [hx, hy, mul_add, ← mul_assoc, key, one_mul, neg_mul]; abel
    · intro hxy
      rw [one_mul] at hxy
      refine ⟨v1⁻¹ * (x - p1), by rw [← mul_assoc, mul_inv_cancel₀ hv1, one_mul, sub_add_cancel],
        ?_⟩
      have hy : y = -(-(v2 * v1⁻¹) * x) + (-(v2 * v1⁻¹) * p1 + p2) := by
        rw [← sub_eq_zero, ← hxy]; abel
      rw [hy]; simp only [neg_mul, neg_neg, mul_assoc, mul_sub]; abel

/-- Conversely, the solution set of `a x + b y + c = 0` (`a`, `b` not both zero) is a parametrized
line. -/
theorem eq_line_alg (a b c : D) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ p1 p2 v1 v2 : D, (v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x y : D, (∃ t, x = v1 * t + p1 ∧ y = v2 * t + p2) ↔ a * x + b * y + c = 0 := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := h.resolve_right (not_not.2 hb)
    refine ⟨-(a⁻¹ * c), 0, 0, 1, Or.inr one_ne_zero, fun x y => ?_⟩
    subst hb
    constructor
    · rintro ⟨t, hx, -⟩
      rw [hx, zero_mul, zero_add, zero_mul, add_zero, mul_neg, ← mul_assoc, mul_inv_cancel₀ ha,
        one_mul, neg_add_cancel]
    · intro hxy
      refine ⟨y, ?_, by rw [one_mul, add_zero]⟩
      rw [zero_mul, zero_add, eq_neg_iff_add_eq_zero, ← mul_right_inj' ha, mul_add, ← mul_assoc,
        mul_inv_cancel₀ ha, one_mul, mul_zero]
      simpa using hxy
  · refine ⟨0, b⁻¹ * -c, 1, b⁻¹ * -a, Or.inl one_ne_zero, fun x y => ?_⟩
    constructor
    · rintro ⟨t, hx, hy⟩
      subst hx hy
      have e : b * (b⁻¹ * -a * t + b⁻¹ * -c) = -a * t + -c := by
        rw [mul_add, mul_assoc, mul_inv_cancel_left₀ hb, mul_inv_cancel_left₀ hb]
      rw [one_mul, add_zero, e, neg_mul]; abel
    · intro hxy
      refine ⟨x, by rw [one_mul, add_zero], ?_⟩
      have k : b * y = -a * x + -c := by rw [neg_mul, ← sub_eq_zero, ← hxy]; abel
      rw [mul_assoc, ← mul_add, ← k, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

end Alg

section Coords

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [LineOrder P L]
  [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)] {F : Frame P}

open Vec MulOpposite

/-- The point with co-ordinates `x`, `y`. -/
noncomputable def ptOf (F : Frame P) (x y : Seg F) : P :=
  toP (op x • (ofP F.E : Vec F) + op y • ofP F.E')

theorem ofP_ptOf (x y : Seg F) :
    (ofP (ptOf F x y) : Vec F) = op x • ofP F.E + op y • ofP F.E' := rfl

theorem coord_unique {x y x' y' : Seg F}
    (h : (op x • ofP F.E + op y • ofP F.E' : Vec F) = op x' • ofP F.E + op y' • ofP F.E') :
    x = x' ∧ y = y' := by
  have h0 : (op x - op x') • (ofP F.E : Vec F) + (op y - op y') • ofP F.E' = 0 := by
    rw [sub_smul, sub_smul, sub_add_sub_comm, h, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.1 linearIndependent_EE' _ _ h0
  exact ⟨op_injective (sub_eq_zero.1 h1), op_injective (sub_eq_zero.1 h2)⟩

@[simp] theorem xc_ptOf (x y : Seg F) : F.xc (ptOf F x y) = x :=
  (coord_unique ((decomp (ptOf F x y)).symm.trans (ofP_ptOf x y))).1

@[simp] theorem yc_ptOf (x y : Seg F) : F.yc (ptOf F x y) = y :=
  (coord_unique ((decomp (ptOf F x y)).symm.trans (ofP_ptOf x y))).2

theorem ptOf_coords (X : P) : ptOf F (F.xc X) (F.yc X) = X := (decomp (F := F) X).symm

theorem eq_of_coords {X Y : P} (hx : F.xc X = F.xc Y) (hy : F.yc X = F.yc Y) : X = Y := by
  rw [← ptOf_coords (F := F) X, ← ptOf_coords (F := F) Y, hx, hy]

theorem comb (t a1 a2 b1 b2 : Seg F) :
    (op t • ((op b1 • ofP F.E + op b2 • ofP F.E') - (op a1 • ofP F.E + op a2 • ofP F.E')) +
      (op a1 • ofP F.E + op a2 • ofP F.E') : Vec F) =
    op ((b1 - a1) * t + a1) • ofP F.E + op ((b2 - a2) * t + a2) • ofP F.E' := by
  simp only [op_add, op_mul, op_sub, add_smul, mul_smul, sub_smul, smul_sub, smul_add]
  abel

/-- **The points of a line in co-ordinates.** -/
theorem mem_ln_iff_coord {A B X : P} (hAB : A ≠ B) :
    X ∈ (ln A B : L) ↔ ∃ t : Seg F, F.xc X = (F.xc B - F.xc A) * t + F.xc A ∧
      F.yc X = (F.yc B - F.yc A) * t + F.yc A := by
  rw [mem_ln_iff_smul (F := F) hAB]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨unop r, ?_⟩
    rw [decomp A, decomp B, decomp X, ← op_unop r, comb] at hr
    exact coord_unique hr
  · rintro ⟨t, hx, hy⟩
    refine ⟨op t, ?_⟩
    rw [decomp A, decomp B, decomp X, comb, ← hx, ← hy]

theorem ne_of_coords {A B : P} (h : A ≠ B) : F.xc B - F.xc A ≠ 0 ∨ F.yc B - F.yc A ≠ 0 := by
  by_contra hc
  simp only [not_or, not_not, sub_eq_zero] at hc
  exact h (eq_of_coords hc.1.symm hc.2.symm)

/-- **Theorem 34**: the co-ordinates of the points of a line satisfy an equation `a x + b y + c = 0`
with `a`, `b` on the left, not both zero; the points of the line are exactly its solutions. -/
theorem th34_line (l : L) : ∃ a b c : Seg F, (a ≠ 0 ∨ b ≠ 0) ∧
    ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0 := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  obtain ⟨a, b, c, hab, h⟩ := line_eq_alg (F.xc A) (F.yc A) (F.xc B - F.xc A) (F.yc B - F.yc A)
    (ne_of_coords hAB)
  refine ⟨a, b, c, hab, fun X => ?_⟩
  rw [← ln_eq hAB hA hB, mem_ln_iff_coord hAB]
  exact h _ _

/-- **Theorem 34, converse**: every equation `a x + b y + c = 0` with `a`, `b` not both zero
represents a straight line. -/
theorem th34_converse (a b c : Seg F) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ l : L, ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0 := by
  obtain ⟨p1, p2, v1, v2, hv, hiff⟩ := eq_line_alg a b c h
  have hAB : ptOf F p1 p2 ≠ ptOf F (v1 + p1) (v2 + p2) := by
    intro e
    have h1 := congrArg F.xc e
    have h2 := congrArg F.yc e
    simp only [xc_ptOf, yc_ptOf] at h1 h2
    rcases hv with hv | hv
    · exact hv (by rw [← add_left_inj p1, zero_add]; exact h1.symm)
    · exact hv (by rw [← add_left_inj p2, zero_add]; exact h2.symm)
  refine ⟨ln (ptOf F p1 p2) (ptOf F (v1 + p1) (v2 + p2)), fun X => ?_⟩
  rw [mem_ln_iff_coord hAB, ← hiff, xc_ptOf, xc_ptOf, yc_ptOf, yc_ptOf, add_sub_cancel_right,
    add_sub_cancel_right]

/-- **Equations with the coefficients on the right** (§ 27): `x a + y b + c = 0` represents a line
for all `a`, `b`, `c` (with `a`, `b` not both zero) iff the multiplication is commutative. -/
theorem th34_right :
    (∀ a b c : Seg F, (a ≠ 0 ∨ b ≠ 0) →
      ∃ l : L, ∀ X : P, X ∈ l ↔ F.xc X * a + F.yc X * b + c = 0) ↔
    ∀ s t : Seg F, s * t = t * s := by
  constructor
  · intro h s t
    obtain ⟨l, hl⟩ := h s (-1) 0 (Or.inr (neg_ne_zero.2 one_ne_zero))
    have hAB : ptOf F 0 0 ≠ ptOf F 1 s := fun e => by
      have := congrArg F.xc e; simp at this
    have hA : ptOf F 0 0 ∈ l := (hl _).2 (by simp)
    have hB : ptOf F 1 s ∈ l := (hl _).2 (by simp)
    have hQ : ptOf F t (s * t) ∈ l := by
      rw [← ln_eq hAB hA hB, mem_ln_iff_coord hAB]
      exact ⟨t, by simp, by simp⟩
    have := (hl _).1 hQ
    simp only [xc_ptOf, yc_ptOf, mul_neg, mul_one, add_zero] at this
    exact (sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact this)).symm
  · intro hc a b c h
    obtain ⟨l, hl⟩ := th34_converse (F := F) a b c h
    exact ⟨l, fun X => by rw [hl, hc a, hc b]⟩

theorem xc_O : F.xc F.O = 0 := by
  have h0 : (ofP F.O : Vec F) = op (0 : Seg F) • ofP F.E + op (0 : Seg F) • ofP F.E' := by
    rw [op_zero, zero_smul, zero_smul, add_zero]; rfl
  exact (coord_unique ((decomp (F := F) F.O).symm.trans h0)).1

theorem yc_O : F.yc F.O = 0 := by
  have h0 : (ofP F.O : Vec F) = op (0 : Seg F) • ofP F.E + op (0 : Seg F) • ofP F.E' := by
    rw [op_zero, zero_smul, zero_smul, add_zero]; rfl
  exact (coord_unique ((decomp (F := F) F.O).symm.trans h0)).2

/-- **A line through the origin** other than the second axis: `e x = y` (§ 27). -/
theorem origin_line {l : L} (hO : F.O ∈ l) (hl : l ≠ F.yl) :
    ∃ e : Seg F, ∀ X : P, X ∈ l ↔ F.yc X = e * F.xc X := by
  obtain ⟨B, hBl, hBy⟩ := exists_mem_not_mem (P := P) hl
  have hOB : F.O ≠ B := fun e => hBy (e ▸ F.O_yl)
  have hxB : F.xc B ≠ 0 := by
    intro h
    have k : (F.xc B).pt = F.O := congrArg Seg.pt h
    have k2 := F.xc_par B
    rw [k] at k2
    have e := pline_eq_of_mem k2
    rw [pline_of_mem F.O_yl] at e
    exact hBy (by rw [e]; exact mem_pline _ B)
  refine ⟨F.yc B * (F.xc B)⁻¹, fun X => ?_⟩
  rw [← ln_eq hOB hO hBl, mem_ln_iff_coord hOB, xc_O, yc_O]
  simp only [sub_zero, add_zero]
  constructor
  · rintro ⟨t, hx, hy⟩
    rw [hx, hy, mul_assoc, ← mul_assoc (F.xc B)⁻¹, inv_mul_cancel₀ hxB, one_mul]
  · intro h
    refine ⟨(F.xc B)⁻¹ * F.xc X, by rw [← mul_assoc, mul_inv_cancel₀ hxB, one_mul], ?_⟩
    rw [h, mul_assoc]

end Coords


/-! ## A plane "regarded as a part of" a space -/

/-- **The plane geometry `(P, L)` regarded as a part of the space geometry `(P', L', Pl')`**: the
points of `(P, L)` correspond one-to-one to the points of a plane `α` of the space, its lines to the
lines lying in `α`, so that incidence and betweenness are preserved and reflected. -/
structure PlaneInSpace (P : Type u) (L : Type v) (P' : Type u') (L' : Type v') (Pl' : Type w')
    [HasLines P L] [HasBetween P] [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P'] where
  /-- The plane of the space. -/
  plane : Pl'
  /-- The map on points. -/
  pt : P → P'
  /-- The map on lines. -/
  ln : L → L'
  pt_injective : Function.Injective pt
  pt_mem : ∀ X, pt X ∈ plane
  pt_surj : ∀ Y : P', Y ∈ plane → ∃ X, pt X = Y
  ln_injective : Function.Injective ln
  ln_in : ∀ l, LiesInPlane (Point := P') (ln l) plane
  ln_surj : ∀ m : L', LiesInPlane (Point := P') m plane → ∃ l, ln l = m
  mem_iff : ∀ (X : P) (l : L), pt X ∈ ln l ↔ X ∈ l
  between_iff : ∀ X Y Z : P, Between (pt X) (pt Y) (pt Z) ↔ Between X Y Z

/-! ## Sufficiency: the desarguesian plane inside the coordinate space -/

section Model

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)] (F : Frame P)

open Vec MulOpposite

/-- The embedding of the plane as `z = 0`. -/
noncomputable def embA :
    Vec F →ₗ[(Seg F)ᵐᵒᵖ] AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) :=
  LinearMap.inl (Seg F)ᵐᵒᵖ (Vec F) (Seg F)ᵐᵒᵖ

theorem embA_injective : Function.Injective (embA F) := LinearMap.inl_injective

/-- The point of the space corresponding to a point of the plane. -/
noncomputable def spt (X : P) : AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) := embA F (ofP X)

theorem spt_injective : Function.Injective (spt F) := fun _ _ h => ofP_injective (embA_injective F h)

instance : Module.Finite (Seg F)ᵐᵒᵖ (Vec F) := Module.Finite.of_basis basisEE'

theorem finrank_space : Module.finrank (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) = 3 := by
  rw [Module.finrank_prod, finrank_eq_two, Module.finrank_self]

/-- The plane `z = 0` of the space. -/
noncomputable def zPlane : AffPlane (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) :=
  ⟨AffineSubspace.mk' 0 (LinearMap.range (embA F)), by
    rw [AffineSubspace.direction_mk', LinearMap.finrank_range_of_inj (embA_injective F),
      finrank_eq_two]⟩

theorem mem_zPlane {Y : AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)} :
    Y ∈ zPlane F ↔ ∃ X : P, spt F X = Y := by
  show Y ∈ AffineSubspace.mk' 0 _ ↔ _
  rw [AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, LinearMap.mem_range]
  exact ⟨fun ⟨v, hv⟩ => ⟨toP v, hv⟩, fun ⟨X, hX⟩ => ⟨ofP X, hX⟩⟩

theorem spt_mem (X : P) : spt F X ∈ zPlane F := (mem_zPlane F).2 ⟨X, rfl⟩

/-- Two chosen points of a line. -/
theorem two_pts (l : L) : ∃ AB : P × P, AB.1 ≠ AB.2 ∧ AB.1 ∈ l ∧ AB.2 ∈ l := by
  obtain ⟨A, B, h, hA, hB⟩ := exists_two_points (Point := P) l
  exact ⟨(A, B), h, hA, hB⟩

theorem spt_eq_comb (X A B : P) (r : (Seg F)ᵐᵒᵖ) :
    spt F X = r • (spt F B - spt F A) + spt F A ↔
      (ofP X : Vec F) = r • (ofP B - ofP A) + ofP A := by
  unfold spt
  rw [← map_sub, ← map_smul, ← map_add]
  exact (embA_injective F).eq_iff

/-- The line of the space through the images of two distinct points. -/
noncomputable def slnOf {A B : P} (h : A ≠ B) : AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) :=
  AffLine.through (spt F A) (spt F B) ((spt_injective F).ne h)

theorem mem_slnOf {A B X : P} (h : A ≠ B) : spt F X ∈ slnOf F h ↔ X ∈ (ln A B : L) := by
  unfold slnOf
  rw [AffLine.mem_through_iff, mem_ln_iff_smul (F := F) h]
  exact exists_congr fun r => spt_eq_comb F X A B r

theorem slnOf_in {A B : P} (h : A ≠ B) :
    LiesInPlane (Point := AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) (slnOf F h) (zPlane F) := by
  intro Y hY
  unfold slnOf at hY
  rw [AffLine.mem_through_iff] at hY
  obtain ⟨r, rfl⟩ := hY
  exact (mem_zPlane F).2 ⟨toP (r • (ofP B - ofP A) + ofP A : Vec F), (spt_eq_comb F _ A B r).2 rfl⟩

/-- The line of the space corresponding to a line of the plane. -/
noncomputable def sln (l : L) : AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) :=
  slnOf F (two_pts (P := P) l).choose_spec.1

theorem mem_sln (X : P) (l : L) : spt F X ∈ sln F l ↔ X ∈ l := by
  obtain ⟨hAB, hA, hB⟩ := (two_pts (P := P) l).choose_spec
  rw [sln, mem_slnOf, ln_eq hAB hA hB]

theorem sln_in (l : L) : LiesInPlane (Point := AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) (sln F l)
    (zPlane F) :=
  slnOf_in F _

theorem spt_between (X Y Z : P) : Between (spt F X) (spt F Y) (spt F Z) ↔ Between X Y Z := by
  rw [AffPt.between_iff]
  by_cases hXZ : X = Z
  · subst hXZ
    exact ⟨fun h => absurd rfl h.left_ne_right, fun h => absurd rfl (ne13_of_between h)⟩
  have hd : spt F Z - spt F X ≠ 0 := sub_ne_zero.2 ((spt_injective F).ne (Ne.symm hXZ))
  have key : ∀ r : (Seg F)ᵐᵒᵖ, Sbtw (Seg F)ᵐᵒᵖ (spt F X) (r • (spt F Z - spt F X) + spt F X)
      (spt F Z) ↔ (0 < r ∧ r < 1) ∨ (1 < r ∧ r < 0) := by
    intro r
    have k := sbtw_param_iff (O := spt F X) hd (0 : (Seg F)ᵐᵒᵖ) r 1
    rwa [zero_smul, zero_add, one_smul, sub_add_cancel] at k
  rw [between_iff_param (F := F) hXZ]
  constructor
  · intro h
    have hs := h
    obtain ⟨⟨r, -, hr⟩, -, -⟩ := h
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
    rw [← hr, key] at hs
    rcases hs with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · refine ⟨unop r, k1, k2, ?_⟩
      rw [op_unop]
      exact (spt_eq_comb F Y X Z r).1 hr.symm
    · exact absurd (k1.trans k2) (lt_asymm (zero_lt_one (α := (Seg F)ᵐᵒᵖ)))
  · rintro ⟨t, ht0, ht1, hY⟩
    rw [(spt_eq_comb F Y X Z _).2 hY, key]
    exact Or.inl ⟨ht0, ht1⟩

theorem sln_injective : Function.Injective (sln F) := by
  intro l l' h
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have hA' : A ∈ l' := (mem_sln F A l').1 (h ▸ (mem_sln F A l).2 hA)
  have hB' : B ∈ l' := (mem_sln F B l').1 (h ▸ (mem_sln F B l).2 hB)
  exact line_unique hAB hA hB hA' hB'

theorem sln_surj (m : AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ))
    (hm : LiesInPlane (Point := AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) m (zPlane F)) :
    ∃ l, sln F l = m := by
  obtain ⟨Y1, Y2, hY, h1, h2⟩ := exists_two_points (Point := AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) m
  obtain ⟨X1, rfl⟩ := (mem_zPlane F).1 (hm _ h1)
  obtain ⟨X2, rfl⟩ := (mem_zPlane F).1 (hm _ h2)
  refine ⟨ln X1 X2, line_unique hY ((mem_sln F _ _).2 (mem_ln_left X1 X2))
    ((mem_sln F _ _).2 (mem_ln_right X1 X2)) h1 h2⟩

/-- **The desarguesian plane as the plane `z = 0` of the coordinate space.** -/
noncomputable def planeInSpace :
    PlaneInSpace P L (AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ))
      (AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) (AffPlane (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) where
  plane := zPlane F
  pt := spt F
  ln := sln F
  pt_injective := spt_injective F
  pt_mem := spt_mem F
  pt_surj _ hY := (mem_zPlane F).1 hY
  ln_injective := sln_injective F
  ln_in := sln_in F
  ln_surj := sln_surj F
  mem_iff := mem_sln F
  between_iff := spt_between F

instance fact_finrank_space :
    Fact (Module.finrank (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ) = 3) := ⟨finrank_space F⟩

/-- The coordinate space satisfies groups I, II, III (Analytic.lean). -/
theorem space_instances :
    SpaceOrder (AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) (AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ))
        (AffPlane (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) ∧
      SpaceParallels (AffPt (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ))
        (AffLine (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) (AffPlane (Seg F)ᵐᵒᵖ (Vec F × (Seg F)ᵐᵒᵖ)) :=
  ⟨AffPt.instSpaceOrder, AffPt.instSpaceParallels⟩

end Model

/-! ## Necessity: a plane of space satisfies Desargues's theorem -/

section Necessity

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneParallels P L]
  [Nonempty L] {P' : Type u'} {L' : Type v'} {Pl' : Type w'} [HasLines P' L'] [HasPlanes P' Pl']
  [HasBetween P'] [SpaceParallels P' L' Pl']

theorem PlaneInSpace.meets_iff (e : PlaneInSpace P L P' L' Pl') (a b : L) :
    Meets (Point := P') (e.ln a) (e.ln b) ↔ Meets (Point := P) a b := by
  constructor
  · rintro ⟨W, h1, h2⟩
    obtain ⟨X, rfl⟩ := e.pt_surj W (e.ln_in a W h1)
    exact ⟨X, (e.mem_iff X a).1 h1, (e.mem_iff X b).1 h2⟩
  · rintro ⟨X, h1, h2⟩
    exact ⟨e.pt X, (e.mem_iff X a).2 h1, (e.mem_iff X b).2 h2⟩

theorem PlaneInSpace.line_of (e : PlaneInSpace P L P' L' Pl') {A B : P} {m : L'} (hAB : A ≠ B) (hA : e.pt A ∈ m)
    (hB : e.pt B ∈ m) : ∃ l : L, e.ln l = m ∧ A ∈ l ∧ B ∈ l := by
  have hm := liesInPlane_of_mem (e.pt_injective.ne hAB) hA hB (e.pt_mem A) (e.pt_mem B)
  obtain ⟨l, rfl⟩ := e.ln_surj m hm
  exact ⟨l, rfl, (e.mem_iff A l).1 hA, (e.mem_iff B l).1 hB⟩

theorem PlaneInSpace.not_collinear (e : PlaneInSpace P L P' L' Pl') {A B C : P} (h : ¬Collinear A B C) :
    ¬Collinear (e.pt A) (e.pt B) (e.pt C) := by
  rintro ⟨m, hA, hB, hC⟩
  obtain ⟨l1, h1, -⟩ := exists_line_two (L := L) A A
  have hAB := nc_ne12 h h1
  obtain ⟨l, rfl, hAl, hBl⟩ := e.line_of hAB hA hB
  exact h ⟨l, hAl, hBl, (e.mem_iff C l).1 hC⟩

/-- **Necessity**: a plane geometry which is a part of a space geometry satisfying I and III
satisfies the second part of Desargues's theorem. -/
theorem desarguesII_of_planeInSpace (e : PlaneInSpace P L P' L' Pl') : DesarguesII P := by
  intro A B C A' B' C' a b c hn hn' hAa hA'a hBb hB'b hCc hC'c hab hac hbc hcp h1 h2
  have tr : ∀ {X Y X' Y' : P}, ParPts X Y X' Y' →
      ∃ xy x'y' : L', e.pt X ∈ xy ∧ e.pt Y ∈ xy ∧ e.pt X' ∈ x'y' ∧ e.pt Y' ∈ x'y' ∧
        ¬Meets (Point := P') xy x'y' := by
    rintro X Y X' Y' ⟨l1, l2, k1, k2, k3, k4, hn⟩
    exact ⟨e.ln l1, e.ln l2, (e.mem_iff _ _).2 k1, (e.mem_iff _ _).2 k2, (e.mem_iff _ _).2 k3,
      (e.mem_iff _ _).2 k4, fun h => hn ((e.meets_iff l1 l2).1 h)⟩
  have hcp' : ConcurrentOrParallel P' (e.ln a) (e.ln b) (e.ln c) := by
    rcases hcp with ⟨O, h1, h2, h3⟩ | ⟨p1, p2, p3⟩
    · exact Or.inl ⟨e.pt O, (e.mem_iff _ _).2 h1, (e.mem_iff _ _).2 h2, (e.mem_iff _ _).2 h3⟩
    · exact Or.inr ⟨fun h => p1 ((e.meets_iff _ _).1 h), fun h => p2 ((e.meets_iff _ _).1 h),
        fun h => p3 ((e.meets_iff _ _).1 h)⟩
  obtain ⟨bc, b'c', k1, k2, k3, k4, hn0⟩ := space_desargues (L := L') e.plane (e.pt_mem A)
    (e.pt_mem B) (e.pt_mem C) (e.pt_mem A') (e.pt_mem B') (e.pt_mem C') (e.not_collinear hn)
    (e.not_collinear hn') ((e.mem_iff _ _).2 hAa) ((e.mem_iff _ _).2 hA'a)
    ((e.mem_iff _ _).2 hBb) ((e.mem_iff _ _).2 hB'b) ((e.mem_iff _ _).2 hCc)
    ((e.mem_iff _ _).2 hC'c) (e.ln_injective.ne hab) (e.ln_injective.ne hac)
    (e.ln_injective.ne hbc) hcp' (tr h1) (tr h2)
  have hBC := nc_ne23 hn hBb
  have hB'C' := nc_ne23 hn' hB'b
  obtain ⟨l1, rfl, m1, m2⟩ := e.line_of hBC k1 k2
  obtain ⟨l2, rfl, m3, m4⟩ := e.line_of hB'C' k3 k4
  exact ⟨l1, l2, m1, m2, m3, m4, fun h => hn0 ((e.meets_iff l1 l2).2 h)⟩

/-- **Necessity**: Desargues's theorem (both parts). -/
theorem desarguesTheorem_of_planeInSpace (e : PlaneInSpace P L P' L' Pl') :
    DesarguesTheorem P :=
  ⟨desarguesI_of_II (desarguesII_of_planeInSpace e), desarguesII_of_planeInSpace e⟩

end Necessity

/-! ## Frames -/

theorem exists_frame {P : Type u} {L : Type v} [HasLines P L] [PlaneConnection P L] [Nonempty L] :
    Nonempty (Frame P) := by
  obtain ⟨l⟩ := ‹Nonempty L›
  obtain ⟨O, E, hOE, hO, hE⟩ := exists_two_points (Point := P) l
  obtain ⟨E', hE'⟩ := exists_not_mem (P := P) l
  exact ⟨⟨O, E, E', hOE, not_collinear_of_not_mem hO hE hOE hE'⟩⟩

end DesAlg

end HilbertFoundations
