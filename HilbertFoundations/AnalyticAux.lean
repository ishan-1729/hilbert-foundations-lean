import HilbertFoundations.Basic

/-!
# Coordinate geometry over an ordered division ring: groups I, II, III (helper for § 9)

Helper module of `Analytic.lean` (units `s9.*` are stated there). It builds the *coordinate
models* of Hilbert's § 9 generically, so that later files (Independence, NonDesargues,
DesarguesAlgebra, NonPascal, Constructions) can reuse them:

* `AffPt K V` — the points: the vectors of a left `K`-module `V` (a type synonym of `V`, so that
  the point type determines `K`); `Coord K n = AffPt K (Fin n → K)` is Hilbert's `(x, y)` (`n = 2`)
  or `(x, y, z)` (`n = 3`).
* `AffLine K V` — the straight lines: affine subspaces whose direction has dimension `1`.
* `AffPlane K V` — the planes: affine subspaces whose direction has dimension `2`.
* `Between A B C` is mathlib's strict betweenness `Sbtw K A B C`: `B = A + t (C - A)` with
  `0 < t < 1`.

`K` is any linearly ordered **division ring** (`DivisionRing K`, `LinearOrder K`,
`IsStrictOrderedRing K`), commutative or not; scalars act on the left. With `finrank K V = 2` the
structure is a plane geometry satisfying groups I, II, III (`PlaneOrder`, `PlaneParallels`); with
`finrank K V = 3` a space geometry (`SpaceOrder`, `SpaceParallels`). The proofs go through three
tools: the parametrization of a line (`AffLine.exists_param`, `sbtw_param_iff`), the *side
functional* of a line inside a plane (`exists_side_functional`: a linear form vanishing exactly on
the line; Hilbert's `ux + vy + w`), and dimension counting (mathlib's `finrank`).
-/

namespace HilbertFoundations

open Module

universe u v

/-- The **points** of the coordinate geometry over `K` with vectors `V`: a type synonym of `V`
that remembers the field (or skew field) of scalars. -/
def AffPt (_K : Type u) (V : Type v) : Type v := V

namespace AffPt

variable {K : Type u} {V : Type v}

instance instAddCommGroup [h : AddCommGroup V] : AddCommGroup (AffPt K V) := h

instance instModule [Ring K] [AddCommGroup V] [h : Module K V] : Module K (AffPt K V) := h

/-- A vector of `V` as a point. -/
def ofV (x : V) : AffPt K V := x

/-- The vector of a point. -/
def toV (x : AffPt K V) : V := x

@[simp] theorem toV_ofV (x : V) : toV (ofV (K := K) x) = x := rfl
@[simp] theorem ofV_toV (x : AffPt K V) : ofV (toV x) = x := rfl

section
variable [AddCommGroup V]
@[simp] theorem toV_add (x y : AffPt K V) : toV (x + y) = toV x + toV y := rfl
@[simp] theorem toV_sub (x y : AffPt K V) : toV (x - y) = toV x - toV y := rfl
@[simp] theorem toV_neg (x : AffPt K V) : toV (-x) = -toV x := rfl
@[simp] theorem toV_zero : toV (0 : AffPt K V) = 0 := rfl
@[simp] theorem toV_smul [Ring K] [Module K V] (c : K) (x : AffPt K V) :
    toV (c • x) = c • toV x := rfl
omit [AddCommGroup V] in
theorem toV_injective : Function.Injective (toV : AffPt K V → V) := fun _ _ h => h
end

end AffPt

/-- The coordinate space `K^n`: Hilbert's points `(x, y)` (`n = 2`) and `(x, y, z)` (`n = 3`). -/
abbrev Coord (K : Type u) (n : ℕ) : Type u := AffPt K (Fin n → K)

section Structures

variable (K : Type u) (V : Type v) [Ring K] [AddCommGroup V] [Module K V]

/-- The **straight lines** of the coordinate geometry: affine subspaces of dimension `1`. -/
@[ext]
structure AffLine where
  /-- The points of the line. -/
  carrier : AffineSubspace K (AffPt K V)
  finrank_direction : finrank K carrier.direction = 1

/-- The **planes** of the coordinate geometry: affine subspaces of dimension `2`. -/
@[ext]
structure AffPlane where
  /-- The points of the plane. -/
  carrier : AffineSubspace K (AffPt K V)
  finrank_direction : finrank K carrier.direction = 2

instance AffPt.instHasLines : HasLines (AffPt K V) (AffLine K V) := ⟨fun A a => A ∈ a.carrier⟩

instance AffPt.instHasPlanes : HasPlanes (AffPt K V) (AffPlane K V) := ⟨fun A α => A ∈ α.carrier⟩

end Structures

/-- **Betweenness** in the coordinate geometry: `B` lies strictly between `A` and `C`
(`B = A + t (C - A)`, `0 < t < 1`). -/
instance AffPt.instHasBetween {K : Type u} {V : Type v} [Ring K] [PartialOrder K] [AddCommGroup V]
    [Module K V] : HasBetween (AffPt K V) := ⟨fun A B C => Sbtw K A B C⟩

/-- Lines of `K^n`. -/
abbrev CoordLine (K : Type u) [Ring K] (n : ℕ) : Type u := AffLine K (Fin n → K)

/-- Planes of `K^n`. -/
abbrev CoordPlane (K : Type u) [Ring K] (n : ℕ) : Type u := AffPlane K (Fin n → K)

instance finrank_fin_fun_fact (K : Type u) [DivisionRing K] (n : ℕ) :
    Fact (finrank K (Fin n → K) = n) := ⟨Module.finrank_fin_fun K⟩

namespace AffPt

variable {K : Type u} {V : Type v}

section Ring

variable [Ring K] [AddCommGroup V] [Module K V]

theorem mem_line_iff {A : AffPt K V} {a : AffLine K V} : A ∈ a ↔ A ∈ a.carrier := Iff.rfl

theorem mem_plane_iff {A : AffPt K V} {α : AffPlane K V} : A ∈ α ↔ A ∈ α.carrier := Iff.rfl

theorem between_iff [PartialOrder K] {A B C : AffPt K V} : Between A B C ↔ Sbtw K A B C := Iff.rfl

theorem liesInPlane_iff {a : AffLine K V} {α : AffPlane K V} :
    LiesInPlane (Point := AffPt K V) a α ↔ a.carrier ≤ α.carrier := by
  rw [AffineSubspace.le_def']; rfl

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The vector `B - A` lies in the direction of an affine subspace containing `A` and `B`. -/
theorem sub_mem_direction {S : AffineSubspace K (AffPt K V)} {A B : AffPt K V} (hA : A ∈ S)
    (hB : B ∈ S) : B - A ∈ S.direction := by
  rw [← vsub_eq_sub]; exact AffineSubspace.vsub_mem_direction hB hA

theorem add_mem_of_mem_direction {S : AffineSubspace K (AffPt K V)} {A : AffPt K V} {v : AffPt K V}
    (hv : v ∈ S.direction) (hA : A ∈ S) : v + A ∈ S := by
  rw [← vadd_eq_add]; exact AffineSubspace.vadd_mem_of_mem_direction hv hA

theorem mem_iff_sub_mem_direction {S : AffineSubspace K (AffPt K V)} {O : AffPt K V} (hO : O ∈ S)
    (X : AffPt K V) : X ∈ S ↔ X - O ∈ S.direction := by
  rw [← vsub_eq_sub, AffineSubspace.vsub_right_mem_direction_iff_mem hO]

/-- The points of the line `AB`: `X = r (B - A) + A`. -/
theorem mem_affineSpan_pair_iff {A B X : AffPt K V} :
    X ∈ affineSpan K ({A, B} : Set (AffPt K V)) ↔ ∃ r : K, X = r • (B - A) + A := by
  have hX : X = (X - A) +ᵥ A := by rw [vadd_eq_add, sub_add_cancel]
  rw [hX, vadd_left_mem_affineSpan_pair]
  simp only [vsub_eq_sub, vadd_eq_add, add_left_inj]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

theorem finrank_direction_pair {A B : AffPt K V} (h : A ≠ B) :
    finrank K (affineSpan K ({A, B} : Set (AffPt K V))).direction = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.2 h)

/-- An affine subspace of dimension `d` containing an affine subspace of the same dimension is
equal to it. -/
theorem affineSubspace_eq_of_le {S T : AffineSubspace K (AffPt K V)} (hle : S ≤ T)
    [FiniteDimensional K T.direction] (hd : finrank K S.direction = finrank K T.direction)
    (hne : (S : Set (AffPt K V)).Nonempty) : S = T := by
  have hdir : S.direction = T.direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hd
  obtain ⟨A, hA⟩ := hne
  exact AffineSubspace.ext_of_direction_eq hdir ⟨A, hA, hle hA⟩

end DivisionRing

end AffPt

namespace AffLine

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

open AffPt

/-- **The line through two distinct points.** -/
def through (A B : AffPt K V) (h : A ≠ B) : AffLine K V :=
  ⟨affineSpan K {A, B}, finrank_direction_pair h⟩

theorem mem_through_iff {A B X : AffPt K V} (h : A ≠ B) :
    X ∈ through A B h ↔ ∃ r : K, X = r • (B - A) + A :=
  mem_affineSpan_pair_iff

theorem left_mem_through {A B : AffPt K V} (h : A ≠ B) : A ∈ through A B h :=
  left_mem_affineSpan_pair K A B

theorem right_mem_through {A B : AffPt K V} (h : A ≠ B) : B ∈ through A B h :=
  right_mem_affineSpan_pair K A B

instance finiteDimensional_direction (a : AffLine K V) :
    FiniteDimensional K a.carrier.direction :=
  Module.finite_of_finrank_pos (by rw [a.finrank_direction]; norm_num)

instance _root_.HilbertFoundations.AffPlane.finiteDimensional_direction (α : AffPlane K V) :
    FiniteDimensional K α.carrier.direction :=
  Module.finite_of_finrank_pos (by rw [α.finrank_direction]; norm_num)

/-- A line containing two distinct points `A`, `B` is the line `AB` (axiom I 2 in the model). -/
theorem carrier_eq (a : AffLine K V) {A B : AffPt K V} (h : A ≠ B) (hA : A ∈ a.carrier)
    (hB : B ∈ a.carrier) : a.carrier = affineSpan K {A, B} := by
  have hle : affineSpan K ({A, B} : Set (AffPt K V)) ≤ a.carrier := by
    rw [affineSpan_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hA
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hB
  exact (affineSubspace_eq_of_le hle (by rw [finrank_direction_pair h, a.finrank_direction])
    ⟨A, left_mem_affineSpan_pair K A B⟩).symm

theorem eq_through (a : AffLine K V) {A B : AffPt K V} (h : A ≠ B) (hA : A ∈ a)
    (hB : B ∈ a) : a = through A B h :=
  AffLine.ext (a.carrier_eq h hA hB)

theorem nonempty (a : AffLine K V) : ∃ O : AffPt K V, O ∈ a.carrier := by
  have hne : a.carrier ≠ ⊥ := by
    intro h
    have := a.finrank_direction
    rw [h, AffineSubspace.direction_bot, finrank_bot] at this
    exact absurd this (by norm_num)
  exact (AffineSubspace.nonempty_iff_ne_bot _).2 hne

/-- **Parametrization of a line**: every line is `{r d + O}` for a point `O` and a vector `d ≠ 0`. -/
theorem exists_param (a : AffLine K V) :
    ∃ (O d : AffPt K V), d ≠ 0 ∧ ∀ X : AffPt K V, X ∈ a ↔ ∃ r : K, X = r • d + O := by
  obtain ⟨O, hO⟩ := a.nonempty
  have hne : a.carrier.direction ≠ ⊥ := by
    intro h
    have := a.finrank_direction
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hB : d + O ∈ a.carrier := add_mem_of_mem_direction hd hO
  have hOB : O ≠ d + O := by
    intro h; apply hd0; have := congrArg (· - O) h; simpa using this.symm
  refine ⟨O, d, hd0, fun X => ?_⟩
  rw [mem_line_iff, a.carrier_eq hOB hO hB, mem_affineSpan_pair_iff]
  simp

end AffLine

/-! ### Parameters on a line and betweenness -/

section Param

variable {K : Type u} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- On the parameter line `K`: `y = x + t (z - x)` with `0 ≤ t ≤ 1` and `y ≠ x, z` iff `y` lies
strictly between `x` and `z`. -/
theorem param_between_iff (x y z : K) :
    ((∃ t : K, 0 ≤ t ∧ t ≤ 1 ∧ t * (z - x) + x = y) ∧ y ≠ x ∧ y ≠ z) ↔
      (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
  constructor
  · rintro ⟨⟨t, ht0, ht1, rfl⟩, hx, hz⟩
    rcases lt_trichotomy x z with h | h | h
    · left
      have hzx : 0 < z - x := sub_pos.2 h
      have h1 : 0 ≤ t * (z - x) := mul_nonneg ht0 hzx.le
      have h2 : t * (z - x) ≤ z - x := mul_le_of_le_one_left hzx.le ht1
      constructor
      · exact lt_of_le_of_ne (le_add_of_nonneg_left h1) (Ne.symm hx)
      · refine lt_of_le_of_ne ?_ hz
        calc t * (z - x) + x ≤ (z - x) + x := add_le_add_left h2 x
          _ = z := sub_add_cancel z x
    · subst h; simp at hx
    · right
      have hzx : z - x < 0 := sub_neg.2 h
      have h1 : t * (z - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hzx.le
      have h2 : z - x ≤ t * (z - x) := by
        have h3 : (1 - t) * (z - x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ht1) hzx.le
        have e : (1 - t) * (z - x) = (z - x) - t * (z - x) := by noncomm_ring
        rw [e] at h3; exact sub_nonpos.1 h3
      constructor
      · refine lt_of_le_of_ne ?_ (Ne.symm hz)
        calc z = (z - x) + x := (sub_add_cancel z x).symm
          _ ≤ t * (z - x) + x := add_le_add_left h2 x
      · exact lt_of_le_of_ne (add_le_of_nonpos_left h1) hx
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hzx : 0 < z - x := sub_pos.2 (h1.trans h2)
      refine ⟨⟨(y - x) * (z - x)⁻¹, ?_, ?_, ?_⟩, ne_of_gt h1, ne_of_lt h2⟩
      · exact mul_nonneg (sub_nonneg.2 h1.le) (inv_nonneg.2 hzx.le)
      · calc (y - x) * (z - x)⁻¹ ≤ (z - x) * (z - x)⁻¹ :=
              mul_le_mul_of_nonneg_right (sub_le_sub_right h2.le x) (inv_nonneg.2 hzx.le)
          _ = 1 := mul_inv_cancel₀ hzx.ne'
      · rw [inv_mul_cancel_right₀ hzx.ne', sub_add_cancel]
    · have hzx : z - x < 0 := sub_neg.2 (h1.trans h2)
      refine ⟨⟨(y - x) * (z - x)⁻¹, ?_, ?_, ?_⟩, ne_of_lt h2, ne_of_gt h1⟩
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 h2.le) (inv_nonpos.2 hzx.le)
      · calc (y - x) * (z - x)⁻¹ ≤ (z - x) * (z - x)⁻¹ :=
              mul_le_mul_of_nonpos_right (sub_le_sub_right h1.le x) (inv_nonpos.2 hzx.le)
          _ = 1 := mul_inv_cancel₀ hzx.ne
      · rw [inv_mul_cancel_right₀ hzx.ne, sub_add_cancel]

variable {V : Type v} [AddCommGroup V] [Module K V]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem smul_add_inj {O d : AffPt K V} (hd : d ≠ 0) {a b : K} :
    a • d + O = b • d + O ↔ a = b :=
  ⟨fun h => smul_left_injective K hd (add_right_cancel h), fun h => h ▸ rfl⟩

/-- **Betweenness in terms of parameters**: on the line `{r d + O}`, the point with parameter `y`
lies between those with parameters `x` and `z` iff `y` lies strictly between `x` and `z`. -/
theorem sbtw_param_iff {O d : AffPt K V} (hd : d ≠ 0) (x y z : K) :
    Sbtw K (x • d + O) (y • d + O) (z • d + O) ↔ (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
  rw [← param_between_iff]
  have e : ∀ t : K, AffineMap.lineMap (x • d + O) (z • d + O) t = (t * (z - x) + x) • d + O := by
    intro t
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_add_right_eq_sub, ← sub_smul,
      smul_smul, add_smul, add_assoc]
  simp only [Sbtw, Wbtw, affineSegment, Set.mem_image, Set.mem_Icc, e, smul_add_inj hd, ne_eq]
  constructor
  · rintro ⟨⟨t, ⟨h0, h1⟩, ht⟩, hx, hz⟩; exact ⟨⟨t, h0, h1, ht⟩, hx, hz⟩
  · rintro ⟨⟨t, h0, h1, ht⟩, hx, hz⟩; exact ⟨⟨t, ⟨h0, h1⟩, ht⟩, hx, hz⟩

end Param

/-- Of three distinct elements of a linear order, exactly one lies (strictly) between the other
two. -/
theorem order_three {α : Type*} [LinearOrder α] {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    (((y < x ∧ x < z) ∨ (z < x ∧ x < y)) ∨ ((x < y ∧ y < z) ∨ (z < y ∧ y < x)) ∨
        ((x < z ∧ z < y) ∨ (y < z ∧ z < x))) ∧
      ¬(((y < x ∧ x < z) ∨ (z < x ∧ x < y)) ∧ ((x < y ∧ y < z) ∨ (z < y ∧ y < x))) ∧
      ¬(((y < x ∧ x < z) ∨ (z < x ∧ x < y)) ∧ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))) ∧
      ¬(((x < y ∧ y < z) ∨ (z < y ∧ y < x)) ∧ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
      rcases lt_or_gt_of_ne hyz with h3 | h3 <;>
      first
      | (exfalso; order)
      | (refine Or.inl (Or.inl ⟨?_, ?_⟩) <;> order)
      | (refine Or.inl (Or.inr ⟨?_, ?_⟩) <;> order)
      | (refine Or.inr (Or.inl (Or.inl ⟨?_, ?_⟩)) <;> order)
      | (refine Or.inr (Or.inl (Or.inr ⟨?_, ?_⟩)) <;> order)
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)) <;> order)
      | (refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> order)
  all_goals rintro ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ <;> order

/-- Four distinct elements of a linear order can be arranged increasingly. -/
theorem exists_perm_strictMono_four {α : Type*} [LinearOrder α] (f : Fin 4 → α)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 4), f (σ 0) < f (σ 1) ∧ f (σ 1) < f (σ 2) ∧ f (σ 2) < f (σ 3) := by
  have hs : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  exact ⟨Tuple.sort f, hs (by decide), hs (by decide), hs (by decide)⟩

/-! ### Group I (linear part) and the linear axioms of order -/

namespace AffPt

section Linear

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **Group I, linear part** (I 1, I 2, first clause of I 7) in the coordinate geometry. -/
instance instConnection : Connection (AffPt K V) (AffLine K V) where
  ax_I1 A B h := ⟨AffLine.through A B h, AffLine.left_mem_through h, AffLine.right_mem_through h⟩
  ax_I2 A B a b h hA hB hA' hB' := (a.eq_through h hA hB).trans (b.eq_through h hA' hB').symm
  ax_I7_line a := by
    obtain ⟨O, d, hd, hmem⟩ := a.exists_param
    refine ⟨O, d + O, ?_, (hmem O).2 ⟨0, by simp⟩, (hmem _).2 ⟨1, by simp⟩⟩
    intro h; apply hd
    have := congrArg (· - O) h; simpa using this.symm

theorem collinear_of_mem_affineSpan {A B C : AffPt K V} (hAC : A ≠ C)
    (hB : B ∈ affineSpan K ({A, C} : Set (AffPt K V))) : Collinear A B C :=
  ⟨AffLine.through A C hAC, AffLine.left_mem_through hAC, hB, AffLine.right_mem_through hAC⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- **The linear axioms of order** II 1–4 (and `between_onLine`) in the coordinate geometry. -/
instance instLineOrder : LineOrder (AffPt K V) (AffLine K V) where
  between_onLine A B C h :=
    ⟨fun e => (Sbtw.ne_left h) e.symm, Sbtw.left_ne_right h, Sbtw.ne_right h,
      collinear_of_mem_affineSpan (Sbtw.left_ne_right h) (Wbtw.mem_affineSpan h.wbtw)⟩
  ax_II1 _ _ _ _ h := Sbtw.symm h
  ax_II2 A C a _ _ hAC := by
    have hd : C - A ≠ 0 := sub_ne_zero.2 hAC.symm
    refine ⟨⟨(2 : K)⁻¹ • (C - A) + A, ?_⟩, ⟨(2 : K) • (C - A) + A, ?_⟩⟩
    · have key := (sbtw_param_iff hd (0 : K) (2⁻¹) 1 (O := A)).2
        (Or.inl ⟨by positivity, inv_lt_one_of_one_lt₀ one_lt_two⟩)
      simpa [between_iff] using key
    · have key := (sbtw_param_iff hd (0 : K) 1 2 (O := A)).2 (Or.inl ⟨one_pos, one_lt_two⟩)
      simpa [between_iff] using key
  ax_II3 A B C hcol hAB hAC hBC := by
    obtain ⟨a, hA, hB, hC⟩ := hcol
    obtain ⟨O, d, hd, hmem⟩ := a.exists_param
    obtain ⟨x, rfl⟩ := (hmem A).1 hA
    obtain ⟨y, rfl⟩ := (hmem _).1 hB
    obtain ⟨z, rfl⟩ := (hmem _).1 hC
    have hxy : x ≠ y := fun h => hAB (by rw [h])
    have hxz : x ≠ z := fun h => hAC (by rw [h])
    have hyz : y ≠ z := fun h => hBC (by rw [h])
    simp only [between_iff, sbtw_param_iff hd]
    exact order_three hxy hxz hyz
  ax_II4 A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD := by
    obtain ⟨O, d, hd, hmem⟩ := a.exists_param
    obtain ⟨x, rfl⟩ := (hmem A).1 hA
    obtain ⟨y, rfl⟩ := (hmem _).1 hB
    obtain ⟨z, rfl⟩ := (hmem _).1 hC
    obtain ⟨w, rfl⟩ := (hmem _).1 hD
    have hpts : ∀ i, ![x • d + O, y • d + O, z • d + O, w • d + O] i = ![x, y, z, w] i • d + O := by
      intro i; fin_cases i <;> rfl
    have hinj : Function.Injective ![x, y, z, w] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    obtain ⟨σ, h01, h12, h23⟩ := exists_perm_strictMono_four _ hinj
    refine ⟨σ, ?_, ?_, ?_, ?_⟩ <;> simp only [hpts, between_iff, sbtw_param_iff hd] <;>
      exact Or.inl ⟨by order, by order⟩

end Linear

end AffPt

/-! ### The side functional of a line in a plane; Pasch; parallels

Everything here happens inside an affine subspace `S` of dimension `2`: a plane `α` of a space
geometry (`S = α.carrier`) or the whole plane of a plane geometry (`S = ⊤`). -/

namespace AffPt

section InPlane

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **The side functional** of a line `a` in a plane `S`: a linear form `f` and a point `O` of `a`
such that a point `X` of `S` lies on `a` iff `f (X - O) = 0`. In coordinates this is Hilbert's
`ux + vy + w`. -/
theorem exists_side_functional {S : AffineSubspace K (AffPt K V)} [FiniteDimensional K S.direction]
    (hS : finrank K S.direction = 2) (a : AffLine K V) (ha : a.carrier ≤ S) :
    ∃ (O : AffPt K V) (f : AffPt K V →ₗ[K] K), O ∈ a.carrier ∧
      ∀ X ∈ S, (X ∈ a.carrier ↔ f (X - O) = 0) := by
  obtain ⟨O, hO⟩ := a.nonempty
  have hWS : a.carrier.direction ≤ S.direction := AffineSubspace.direction_le ha
  have hlt : a.carrier.direction < S.direction := lt_of_le_of_ne hWS (fun h => by
    have := a.finrank_direction; rw [h, hS] at this; norm_num at this)
  obtain ⟨w, hwS, hwW⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨f, hfw, hfW⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hwW (Module.Projective.of_free)
  have hker : ∀ u ∈ a.carrier.direction, f u = 0 := fun u hu => by
    have : f u ∈ a.carrier.direction.map f := Submodule.mem_map_of_mem hu
    rw [hfW] at this; exact (Submodule.mem_bot K).1 this
  have hw0 : w ≠ 0 := fun h => hwW (h ▸ Submodule.zero_mem _)
  have hinf : a.carrier.direction ⊓ (K ∙ w) = ⊥ := by
    rw [eq_bot_iff]; intro v hv
    obtain ⟨hvW, hvw⟩ := Submodule.mem_inf.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvw
    by_cases hc : c = 0
    · simp [hc]
    · exfalso; apply hwW
      have := Submodule.smul_mem _ c⁻¹ hvW
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hsup : a.carrier.direction ⊔ (K ∙ w) = S.direction := by
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le hWS ((Submodule.span_singleton_le_iff_mem _ _).2 hwS))
    have := Submodule.finrank_sup_add_finrank_inf_eq a.carrier.direction (K ∙ w)
    rw [hinf, finrank_bot, a.finrank_direction, finrank_span_singleton hw0] at this
    rw [hS]; omega
  refine ⟨O, f, hO, fun X hX => ⟨fun hXa => hker _ (sub_mem_direction hO hXa), fun hf0 => ?_⟩⟩
  have hXO : X - O ∈ a.carrier.direction ⊔ (K ∙ w) := hsup ▸ sub_mem_direction (ha hO) hX
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hXO
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [← huv, map_add, hker u hu, map_smul, zero_add, smul_eq_mul] at hf0
  have hc : c = 0 := (mul_eq_zero.1 hf0).resolve_right hfw
  rw [hc, zero_smul, add_zero] at huv
  rw [mem_iff_sub_mem_direction hO, ← huv]; exact hu

theorem linear_lineMap_sub (f : AffPt K V →ₗ[K] K) (P Q O : AffPt K V) (t : K) :
    f (AffineMap.lineMap P Q t - O) = t * (f (Q - O) - f (P - O)) + f (P - O) := by
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have : t • (Q - P) + P - O = t • ((Q - O) - (P - O)) + (P - O) := by
    rw [sub_sub_sub_cancel_right]; abel
  rw [this, map_add, map_smul, map_sub, smul_eq_mul]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- **Hilbert's convention for the sides of a line** (§ 9): two points `P`, `Q` of the plane off the
line `a` are separated by `a` (some point of `a` lies between them) iff the side functional takes
values of opposite signs at them. -/
theorem exists_between_iff_mul_neg {S : AffineSubspace K (AffPt K V)} {a : AffLine K V}
    (ha : a.carrier ≤ S) {O : AffPt K V} {f : AffPt K V →ₗ[K] K}
    (hf : ∀ X ∈ S, (X ∈ a.carrier ↔ f (X - O) = 0)) {P Q : AffPt K V} (hP : P ∈ S) (hQ : Q ∈ S)
    (hPa : P ∉ a.carrier) (hQa : Q ∉ a.carrier) :
    (∃ X, X ∈ a.carrier ∧ Sbtw K P X Q) ↔ f (P - O) * f (Q - O) < 0 := by
  have hp : f (P - O) ≠ 0 := fun h => hPa ((hf P hP).2 h)
  have hq : f (Q - O) ≠ 0 := fun h => hQa ((hf Q hQ).2 h)
  constructor
  · rintro ⟨X, hXa, ⟨⟨t, ⟨h0, h1⟩, rfl⟩, hXP, hXQ⟩⟩
    have h := (hf _ (ha hXa)).1 hXa
    rw [linear_lineMap_sub] at h
    set p := f (P - O)
    set q := f (Q - O)
    have e : t * (q - p) + p = (1 - t) * p + t * q := by noncomm_ring
    rw [e] at h
    rcases lt_or_gt_of_ne hp with hp' | hp' <;> rcases lt_or_gt_of_ne hq with hq' | hq'
    · exfalso
      rcases h0.eq_or_lt with ht | ht
      · subst ht; simp at h; exact hp h
      · have : (1 - t) * p + t * q < 0 :=
          add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 h1) hp'.le)
            (mul_neg_of_pos_of_neg ht hq')
        exact this.ne h
    · exact mul_neg_of_neg_of_pos hp' hq'
    · exact mul_neg_of_pos_of_neg hp' hq'
    · exfalso
      rcases h0.eq_or_lt with ht | ht
      · subst ht; simp at h; exact hp h
      · have : 0 < (1 - t) * p + t * q :=
          add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 h1) hp'.le) (mul_pos ht hq')
        exact this.ne' h
  · intro hpq
    set p := f (P - O) with hpdef
    set q := f (Q - O) with hqdef
    have hpq' : p - q ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h] at hpq
      exact absurd hpq (not_lt.2 (mul_self_nonneg q))
    set t := p * (p - q)⁻¹ with ht
    have ht01 : 0 < t ∧ t < 1 := by
      rcases mul_neg_iff.1 hpq with ⟨hp', hq'⟩ | ⟨hp', hq'⟩
      · have hd : 0 < p - q := sub_pos.2 (hq'.trans hp')
        have hpp : p < p - q := by
          have := sub_lt_sub_left hq' p; rwa [sub_zero] at this
        exact ⟨mul_pos hp' (inv_pos.2 hd), by
          calc p * (p - q)⁻¹ < (p - q) * (p - q)⁻¹ := mul_lt_mul_of_pos_right hpp (inv_pos.2 hd)
            _ = 1 := mul_inv_cancel₀ hd.ne'⟩
      · have hd : p - q < 0 := sub_neg.2 (hp'.trans hq')
        exact ⟨mul_pos_of_neg_of_neg hp' (inv_lt_zero.2 hd), by
          calc p * (p - q)⁻¹ < (p - q) * (p - q)⁻¹ :=
                mul_lt_mul_of_neg_right (sub_lt_self p hq') (inv_lt_zero.2 hd)
            _ = 1 := mul_inv_cancel₀ hd.ne⟩
    have hX0 : f (AffineMap.lineMap P Q t - O) = 0 := by
      rw [linear_lineMap_sub, ← hpdef, ← hqdef, ht]
      have : p * (p - q)⁻¹ * (q - p) = -(p * (p - q)⁻¹ * (p - q)) := by noncomm_ring
      rw [this, inv_mul_cancel_right₀ hpq']; abel
    have hXS : AffineMap.lineMap P Q t ∈ S := AffineMap.lineMap_mem t hP hQ
    refine ⟨AffineMap.lineMap P Q t, (hf _ hXS).2 hX0, ⟨⟨t, ⟨ht01.1.le, ht01.2.le⟩, rfl⟩, ?_, ?_⟩⟩
    · intro h; rw [h] at hX0; exact hp hX0
    · intro h; rw [h] at hX0; exact hq hX0

/-- **Same side of a line** (§ 4) in terms of the side functional: Hilbert's convention of § 9. -/
theorem sameSide_iff_mul_pos {S : AffineSubspace K (AffPt K V)} {a : AffLine K V}
    (ha : a.carrier ≤ S) {O : AffPt K V} {f : AffPt K V →ₗ[K] K}
    (hf : ∀ X ∈ S, (X ∈ a.carrier ↔ f (X - O) = 0)) {P Q : AffPt K V} (hP : P ∈ S) (hQ : Q ∈ S) :
    SameSide a P Q ↔ 0 < f (P - O) * f (Q - O) := by
  constructor
  · rintro ⟨hPa, hQa, hno⟩
    have hp : f (P - O) ≠ 0 := fun h => hPa ((hf P hP).2 h)
    have hq : f (Q - O) ≠ 0 := fun h => hQa ((hf Q hQ).2 h)
    have := (exists_between_iff_mul_neg ha hf hP hQ hPa hQa).not.1 hno
    exact lt_of_le_of_ne (not_lt.1 this) (Ne.symm (mul_ne_zero hp hq))
  · intro h
    have hPa : P ∉ a.carrier := fun hPa => by rw [(hf P hP).1 hPa, zero_mul] at h; exact lt_irrefl _ h
    have hQa : Q ∉ a.carrier := fun hQa => by rw [(hf Q hQ).1 hQa, mul_zero] at h; exact lt_irrefl _ h
    refine ⟨hPa, hQa, fun hex => ?_⟩
    have := (exists_between_iff_mul_neg ha hf hP hQ hPa hQa).1 hex
    exact lt_asymm h this

/-- **Pasch's axiom** (II 5) inside a plane `S` of the coordinate geometry. -/
theorem pasch_in {S : AffineSubspace K (AffPt K V)} [FiniteDimensional K S.direction]
    (hS : finrank K S.direction = 2) (A B C : AffPt K V) (a : AffLine K V) (ha : a.carrier ≤ S)
    (hAS : A ∈ S) (hBS : B ∈ S) (hCS : C ∈ S) (hA : A ∉ a) (hB : B ∉ a) (hC : C ∉ a)
    (hX : ∃ X : AffPt K V, X ∈ a ∧ Between A X B) :
    (∃ Y : AffPt K V, Y ∈ a ∧ Between B Y C) ∨ ∃ Y : AffPt K V, Y ∈ a ∧ Between A Y C := by
  obtain ⟨O, f, -, hf⟩ := exists_side_functional hS a ha
  have hAB := (exists_between_iff_mul_neg ha hf hAS hBS hA hB).1 hX
  have hc : f (C - O) ≠ 0 := fun h => hC ((hf C hCS).2 h)
  rcases lt_or_gt_of_ne hc with hc' | hc'
  · rcases mul_neg_iff.1 hAB with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inr ((exists_between_iff_mul_neg ha hf hAS hCS hA hC).2 (mul_neg_of_pos_of_neg hp hc'))
    · exact Or.inl ((exists_between_iff_mul_neg ha hf hBS hCS hB hC).2 (mul_neg_of_pos_of_neg hq hc'))
  · rcases mul_neg_iff.1 hAB with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl ((exists_between_iff_mul_neg ha hf hBS hCS hB hC).2 (mul_neg_of_neg_of_pos hq hc'))
    · exact Or.inr ((exists_between_iff_mul_neg ha hf hAS hCS hA hC).2 (mul_neg_of_neg_of_pos hp hc'))

end InPlane

section Parallels

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **The axiom of parallels** inside a plane `S` of the coordinate geometry: through a point `A` of
`S` off a line `a` of `S` there is exactly one line of `S` not meeting `a`, namely `A + dir a`. -/
theorem exists_unique_parallel_in {S : AffineSubspace K (AffPt K V)}
    [FiniteDimensional K S.direction] (hS : finrank K S.direction = 2) (a : AffLine K V)
    (ha : a.carrier ≤ S) (A : AffPt K V) (hAS : A ∈ S) (hA : A ∉ a) :
    ∃! b : AffLine K V, b.carrier ≤ S ∧ A ∈ b ∧ ¬Meets (Point := AffPt K V) b a := by
  set W := a.carrier.direction with hW
  let b : AffLine K V := ⟨AffineSubspace.mk' A W, by
    rw [AffineSubspace.direction_mk']; exact a.finrank_direction⟩
  have hbmem : ∀ X, X ∈ b.carrier ↔ X - A ∈ W := fun X => by
    show X ∈ AffineSubspace.mk' A W ↔ _
    rw [AffineSubspace.mem_mk', vsub_eq_sub]
  refine ⟨b, ⟨?_, AffineSubspace.self_mem_mk' A W, ?_⟩, ?_⟩
  · rw [AffineSubspace.le_def']; intro X hX
    rw [mem_iff_sub_mem_direction hAS]
    exact AffineSubspace.direction_le ha ((hbmem X).1 hX)
  · rintro ⟨X, hXb, hXa⟩
    apply hA
    have h1 : -(X - A) ∈ W := Submodule.neg_mem _ ((hbmem X).1 hXb)
    have := add_mem_of_mem_direction h1 hXa
    rwa [neg_sub, sub_add_cancel] at this
  · rintro c ⟨hcS, hAc, hmeet⟩
    obtain ⟨O, hO⟩ := a.nonempty
    have hdir : c.carrier.direction = W := by
      by_contra hne
      have hinf : finrank K (c.carrier.direction ⊓ W : Submodule K (AffPt K V)) = 0 := by
        have hle : finrank K (c.carrier.direction ⊓ W : Submodule K (AffPt K V)) ≤ 1 := by
          rw [← c.finrank_direction]; exact Submodule.finrank_mono inf_le_left
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
        · exact h
        · exfalso; apply hne
          have h1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : c.carrier.direction ⊓ W ≤ _)
            (by rw [h, c.finrank_direction])
          have h2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : c.carrier.direction ⊓ W ≤ _)
            (by rw [h, a.finrank_direction])
          rw [← h1, h2]
      have hsup : c.carrier.direction ⊔ W = S.direction := by
        apply Submodule.eq_of_le_of_finrank_eq
          (sup_le (AffineSubspace.direction_le hcS) (AffineSubspace.direction_le ha))
        have := Submodule.finrank_sup_add_finrank_inf_eq c.carrier.direction W
        rw [hinf, c.finrank_direction, a.finrank_direction] at this
        rw [hS]; omega
      have hAO : A - O ∈ c.carrier.direction ⊔ W := hsup ▸ sub_mem_direction (ha hO) hAS
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hAO
      apply hmeet
      refine ⟨w + O, ?_, add_mem_of_mem_direction hw hO⟩
      have : w + O = -u + A := by
        have hw' : w = A - O - u := by rw [← huw]; abel
        rw [hw']; abel
      rw [this]; exact add_mem_of_mem_direction (Submodule.neg_mem _ hu) hAc
    apply AffLine.ext
    exact AffineSubspace.ext_of_direction_eq (by rw [hdir]; exact (AffineSubspace.direction_mk' A W).symm)
      ⟨A, hAc, AffineSubspace.self_mem_mk' A W⟩

end Parallels

/-! ### Group I in the plane and in space -/

section GroupI

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Points `O`, `u + O`, `w + O` with `u`, `w` linearly independent are not collinear. -/
theorem not_collinear_of_linearIndependent {O u w : AffPt K V} (h : LinearIndependent K ![u, w]) :
    ¬Collinear O (u + O) (w + O) := by
  rintro ⟨a, h1, h2, h3⟩
  obtain ⟨P, d, hd, hmem⟩ := a.exists_param
  obtain ⟨x, hx⟩ := (hmem _).1 h1
  obtain ⟨y, hy⟩ := (hmem _).1 h2
  obtain ⟨z, hz⟩ := (hmem _).1 h3
  have hu : u = (y - x) • d := by
    rw [sub_smul]
    calc u = (u + O) - O := by abel
      _ = _ := by rw [hy, hx]; abel
  have hw : w = (z - x) • d := by
    rw [sub_smul]
    calc w = (w + O) - O := by abel
      _ = _ := by rw [hz, hx]; abel
  rw [LinearIndependent.pair_iff] at h
  by_cases hyx : y - x = 0
  · have := h 1 0 (by rw [hu, hyx]; simp)
    exact one_ne_zero this.1
  · have := h ((z - x) * (y - x)⁻¹) (-1) (by
      rw [hu, hw, smul_smul, inv_mul_cancel_right₀ hyx]; simp)
    exact one_ne_zero (neg_eq_zero.1 this.2)

theorem collinear_of_mathlib [Nontrivial V] {A B C : AffPt K V}
    (h : _root_.Collinear K ({A, B, C} : Set (AffPt K V))) : Collinear A B C := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨p₀, v, hv⟩ := h
  simp only [vadd_eq_add] at hv
  by_cases hv0 : v = 0
  · obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hne : p₀ ≠ AffPt.ofV u + p₀ := by
      intro h; apply hu; have := congrArg (fun X => AffPt.toV (X - p₀)) h; simpa using this.symm
    refine ⟨AffLine.through p₀ _ hne, ?_, ?_, ?_⟩ <;>
    · rw [AffLine.mem_through_iff]
      refine ⟨0, ?_⟩
      first
      | (obtain ⟨r, hr⟩ := hv A (by simp); rw [hr, hv0]; simp)
      | (obtain ⟨r, hr⟩ := hv B (by simp); rw [hr, hv0]; simp)
      | (obtain ⟨r, hr⟩ := hv C (by simp); rw [hr, hv0]; simp)
  · have hne : p₀ ≠ v + p₀ := by
      intro h; apply hv0; have := congrArg (· - p₀) h; simpa using this.symm
    have key : ∀ X ∈ ({A, B, C} : Set (AffPt K V)), X ∈ AffLine.through p₀ _ hne := by
      intro X hX
      obtain ⟨r, hr⟩ := hv X hX
      rw [AffLine.mem_through_iff]; exact ⟨r, by rw [hr, add_sub_cancel_right]⟩
    exact ⟨_, key A (by simp), key B (by simp), key C (by simp)⟩

theorem linearIndependent_coe_basis {W : Submodule K (AffPt K V)} (b : Basis (Fin 2) K W) :
    LinearIndependent K ![(b 0 : AffPt K V), (b 1 : AffPt K V)] := by
  have := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  convert this using 1
  funext i; fin_cases i <;> rfl

theorem nonempty_plane (α : AffPlane K V) : ∃ O : AffPt K V, O ∈ α.carrier := by
  have hne : α.carrier ≠ ⊥ := by
    intro h
    have := α.finrank_direction
    rw [h, AffineSubspace.direction_bot, finrank_bot] at this
    exact absurd this (by norm_num)
  exact (AffineSubspace.nonempty_iff_ne_bot _).2 hne

/-- Every plane contains three non-collinear points (I 7, plane clause). -/
theorem exists_noncollinear_in_plane (α : AffPlane K V) :
    ∃ A B C : AffPt K V, A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ¬Collinear A B C := by
  obtain ⟨O, hO⟩ := nonempty_plane α
  let b := Module.finBasisOfFinrankEq K α.carrier.direction α.finrank_direction
  exact ⟨O, (b 0 : AffPt K V) + O, (b 1 : AffPt K V) + O, hO,
    add_mem_of_mem_direction (b 0).2 hO, add_mem_of_mem_direction (b 1).2 hO,
    not_collinear_of_linearIndependent (linearIndependent_coe_basis b)⟩

theorem finiteDimensional_of_fact {n : ℕ} [h : Fact (finrank K V = n + 1)] :
    FiniteDimensional K (AffPt K V) :=
  Module.finite_of_finrank_pos (by show 0 < finrank K V; rw [h.out]; omega)

/-- **Group I of plane geometry** in the coordinate plane (`finrank K V = 2`). -/
instance instPlaneConnection [Fact (finrank K V = 2)] :
    PlaneConnection (AffPt K V) (AffLine K V) where
  ax_I7_noncollinear := by
    have := finiteDimensional_of_fact (K := K) (V := V) (n := 1)
    let b := Module.finBasisOfFinrankEq K (AffPt K V) (show finrank K V = 2 from Fact.out)
    have hb : LinearIndependent K ![b 0, b 1] := by
      convert b.linearIndependent using 1; funext i; fin_cases i <;> rfl
    have := not_collinear_of_linearIndependent (O := 0) hb
    simp only [add_zero] at this
    exact ⟨0, b 0, b 1, this⟩

/-- **Group I of space geometry** (I 1–7) in the coordinate space (`finrank K V = 3`). -/
instance instSpaceConnection [hf : Fact (finrank K V = 3)] :
    SpaceConnection (AffPt K V) (AffLine K V) (AffPlane K V) where
  ax_I3 A B C h := by
    have := finiteDimensional_of_fact (K := K) (V := V) (n := 2)
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
      (show 0 < finrank K V by rw [hf.out]; omega)
    have hi : AffineIndependent K ![A, B, C] :=
      affineIndependent_iff_not_collinear_set.2 (fun hc => h (collinear_of_mathlib hc))
    refine ⟨⟨affineSpan K (Set.range ![A, B, C]), by
      rw [direction_affineSpan]; exact hi.finrank_vectorSpan (by simp)⟩, ?_, ?_, ?_⟩
    · exact mem_affineSpan K ⟨0, rfl⟩
    · exact mem_affineSpan K ⟨1, rfl⟩
    · exact mem_affineSpan K ⟨2, rfl⟩
  ax_I4 A B C α β h hA hB hC hA' hB' hC' := by
    have := finiteDimensional_of_fact (K := K) (V := V) (n := 2)
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
      (show 0 < finrank K V by rw [hf.out]; omega)
    have hi : AffineIndependent K ![A, B, C] :=
      affineIndependent_iff_not_collinear_set.2 (fun hc => h (collinear_of_mathlib hc))
    have hfr : finrank K (affineSpan K (Set.range ![A, B, C])).direction = 2 := by
      rw [direction_affineSpan]; exact hi.finrank_vectorSpan (by simp)
    have key : ∀ γ : AffPlane K V, A ∈ γ → B ∈ γ → C ∈ γ →
        γ.carrier = affineSpan K (Set.range ![A, B, C]) := by
      intro γ h1 h2 h3
      refine (affineSubspace_eq_of_le (S := affineSpan K (Set.range ![A, B, C])) ?_
        (by rw [hfr, γ.finrank_direction])
        ⟨A, mem_affineSpan K ⟨0, rfl⟩⟩).symm
      rw [affineSpan_le]; rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact h1
      · exact h2
      · exact h3
    exact AffPlane.ext ((key α hA hB hC).trans (key β hA' hB' hC').symm)
  ax_I5 A B a α h hA hB hA' hB' := by
    intro P hP
    have hle : affineSpan K ({A, B} : Set (AffPt K V)) ≤ α.carrier := by
      rw [affineSpan_le]; intro x hx
      rcases hx with rfl | hx
      · exact hA'
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hB'
    have : P ∈ a.carrier := hP
    rw [a.carrier_eq h hA hB] at this
    exact hle this
  ax_I6 α β A _ hA hB := by
    have := finiteDimensional_of_fact (K := K) (V := V) (n := 2)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq α.carrier.direction β.carrier.direction
    have hle := Submodule.finrank_le (α.carrier.direction ⊔ β.carrier.direction)
    have hV : finrank K (AffPt K V) = 3 := hf.out
    rw [α.finrank_direction, β.finrank_direction] at hsum
    have hne : α.carrier.direction ⊓ β.carrier.direction ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hsum; omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨hvα, hvβ⟩ := Submodule.mem_inf.1 hv
    refine ⟨v + A, ?_, add_mem_of_mem_direction hvα hA, add_mem_of_mem_direction hvβ hB⟩
    intro h; apply hv0; have := congrArg (· - A) h; simpa using this
  ax_I7_plane := exists_noncollinear_in_plane
  ax_I7_space := by
    have := finiteDimensional_of_fact (K := K) (V := V) (n := 2)
    let b := Module.finBasisOfFinrankEq K (AffPt K V) (show finrank K V = 3 from hf.out)
    refine ⟨0, b 0, b 1, b 2, ?_⟩
    rintro ⟨α, h0, h1, h2, h3⟩
    have hsub : ∀ i, b i ∈ α.carrier.direction := by
      intro i
      have := sub_mem_direction h0 (show b i ∈ α.carrier by fin_cases i <;> assumption)
      simpa using this
    have htop : α.carrier.direction = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩; exact hsub i
    have := α.finrank_direction
    rw [htop, finrank_top] at this
    have hV : finrank K (AffPt K V) = 3 := hf.out
    omega

end GroupI

/-! ### Groups I–III: the plane and the space -/

section Instances

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem finrank_top_direction {n : ℕ} [h : Fact (finrank K V = n)] :
    finrank K (⊤ : AffineSubspace K (AffPt K V)).direction = n := by
  rw [AffineSubspace.direction_top, finrank_top]; exact h.out

/-- **Groups I, II of plane geometry** in the coordinate plane (`finrank K V = 2`). -/
instance instPlaneOrder [Fact (finrank K V = 2)] : PlaneOrder (AffPt K V) (AffLine K V) :=
  { instPlaneConnection, instLineOrder with
    ax_II5 := fun A B C a _ hA hB hC hX => by
      have := finiteDimensional_of_fact (K := K) (V := V) (n := 1)
      exact pasch_in (S := ⊤) finrank_top_direction A B C a le_top
        (AffineSubspace.mem_top K _ A) (AffineSubspace.mem_top K _ B) (AffineSubspace.mem_top K _ C) hA hB hC hX }

/-- **Groups I, II of space geometry** in the coordinate space (`finrank K V = 3`). -/
instance instSpaceOrder [Fact (finrank K V = 3)] :
    SpaceOrder (AffPt K V) (AffLine K V) (AffPlane K V) :=
  { instSpaceConnection, instLineOrder with
    ax_II5 := fun A B C α a _ hA hB hC ha hAa hBa hCa hX =>
      pasch_in α.finrank_direction A B C a (liesInPlane_iff.1 ha) hA hB hC hAa hBa hCa hX }

/-- **Group III of plane geometry** in the coordinate plane. -/
instance instPlaneParallels [Fact (finrank K V = 2)] :
    PlaneParallels (AffPt K V) (AffLine K V) :=
  { instPlaneConnection with
    ax_III := fun a A hA => by
      have := finiteDimensional_of_fact (K := K) (V := V) (n := 1)
      obtain ⟨b, ⟨-, hb⟩, hu⟩ := exists_unique_parallel_in (S := ⊤) finrank_top_direction a
        le_top A (AffineSubspace.mem_top K _ A) hA
      exact ⟨b, hb, fun c hc => hu c ⟨le_top, hc⟩⟩ }

/-- **Group III of space geometry** in the coordinate space. -/
instance instSpaceParallels [Fact (finrank K V = 3)] :
    SpaceParallels (AffPt K V) (AffLine K V) (AffPlane K V) :=
  { instSpaceConnection with
    ax_III := fun α a A ha hA hAa => by
      obtain ⟨b, ⟨hb1, hb⟩, hu⟩ := exists_unique_parallel_in α.finrank_direction a
        (liesInPlane_iff.1 ha) A hA hAa
      exact ⟨b, ⟨liesInPlane_iff.2 hb1, hb⟩,
        fun c ⟨hc1, hc⟩ => hu c ⟨liesInPlane_iff.1 hc1, hc⟩⟩ }

end Instances

end AffPt

end HilbertFoundations
