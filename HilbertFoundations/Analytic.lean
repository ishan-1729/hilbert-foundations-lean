import HilbertFoundations.Basic
import HilbertFoundations.AnalyticAux3

/-!
# Compatibility of the axioms; complex number-systems (§§ 9, 13)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 9. Compatibility of the axioms
* § 13. Complex number-systems

## The coordinate models (helper modules)

The models of § 9 are built generically in two helper modules, so that later files can reuse them:

* `HilbertFoundations/AnalyticAux.lean` — groups I, II, III over any linearly ordered **division
  ring** `K` (commutative or not): points `AffPt K V` (vectors of a left `K`-module `V`), lines
  `AffLine K V` and planes `AffPlane K V` (affine subspaces of dimension 1 and 2), betweenness
  `Sbtw K`. Instances: `Connection`, `LineOrder` (any `V`); `PlaneConnection`, `PlaneOrder`,
  `PlaneParallels` (`finrank K V = 2`); `SpaceConnection`, `SpaceOrder`, `SpaceParallels`
  (`finrank K V = 3`). For `V = Fin n → K` the abbreviations are `Coord K n`, `CoordLine K n`,
  `CoordPlane K n`.
* `HilbertFoundations/AnalyticAux2.lean` — group IV over a linearly ordered **field** for `Coord K n`
  (metric congruence: `SegCong` by squared lengths, `AngCong` by cosines `Coord.AngleEq`), with
  laying off over **Pythagorean** fields (`IsPythagorean K`), and group V over **archimedean**
  fields. Instances `Coord.instPlaneGeometry : PlaneGeometry (Coord K 2) (CoordLine K 2)` and
  `Coord.instSpaceGeometry : SpaceGeometry (Coord K 3) (CoordLine K 3) (CoordPlane K 3)` for
  `[IsPythagorean K] [Archimedean K]`.

* `HilbertFoundations/AnalyticAux3.lean` — Hilbert's non-archimedean field `Ω(t)` of § 12
  (`OmegaT`: germs at `+∞` of the functions generated from `t`), a Pythagorean linearly ordered
  field that is not archimedean (used for § 13 here; reusable for § 12).

This file defines Hilbert's field `Ω` (`Omega`, `OmegaField`), proves its properties, and
instantiates the models over `Ω` and over `ℝ`; it then formalizes the laws 1–17 of § 13.

A file that needs a *different* congruence (or betweenness) on the same points must use a type
synonym of `Coord K n`, since the instances here are global.
-/

namespace HilbertFoundations

open Module

/-!
## [s9.consistency] The axioms are not contradictory

*(§ 9)*

> The axioms, which we have discussed in the previous chapter and have divided into five groups, are not contradictory to one another; that is to say, it is not possible to deduce from these axioms, by any logical process of reasoning, a proposition which is contradictory to any of them. To demonstrate this, it is sufficient to construct a geometry where all of the five groups are fulfilled.

**Lean reading.** "Not contradictory" is read semantically: `AxiomsConsistent` says that it is not the
case that every system of points, lines and planes satisfying all five groups (`SpaceGeometry`) is
impossible (`→ False`); a deduction of a contradiction from the axioms would be exactly a proof of
that universal statement. `AxiomsConsistentPlane` is the same for plane geometry. The second
sentence ("it is sufficient to construct a geometry") is `axiomsConsistent_of_model`: one model
gives consistency. The model itself is constructed below; `axiomsConsistent` (unit
`s9.space`) and `axiomsConsistentPlane` (unit `s9.relative_consistency`) prove the claim. Since
`Basic.lean` reads I 7 literally, some degenerate structures (a single line, no planes) also
satisfy the space axioms; the model used here is not of that kind (`omega_space_has_plane`, unit
`s9.space`), so the consistency proved is that of the intended geometry of space.

**Status.** proved
-/

/-- **The axioms I–V (space geometry) are not contradictory**: not every system satisfying them is
impossible. -/
def AxiomsConsistent : Prop :=
  ¬∀ (P : Type) (L : Type) (Pl : Type) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceGeometry P L Pl → False

/-- **The axioms I–V of plane geometry are not contradictory.** -/
def AxiomsConsistentPlane : Prop :=
  ¬∀ (P : Type) (L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneGeometry P L → False

/-- "It is sufficient to construct a geometry where all of the five groups are fulfilled." -/
theorem axiomsConsistent_of_model (P : Type) (L : Type) (Pl : Type) [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [HasSegCong P] [HasAngCong P] (h : SpaceGeometry P L Pl) :
    AxiomsConsistent :=
  fun hall => hall P L Pl h

theorem axiomsConsistentPlane_of_model (P : Type) (L : Type) [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] (h : PlaneGeometry P L) : AxiomsConsistentPlane :=
  fun hall => hall P L h

/-!
## [s9.omega] Hilbert's domain `Ω`

*(§ 9)*

> To this end, let us consider a domain $\Omega$ consisting of all of those algebraic numbers which may be obtained by beginning with the number one and applying to it a finite number of times the four arithmetical operations (addition, subtraction, multiplication, and division) and the operation $\sqrt{1+\omega^2}$, where $\omega$ represents a number arising from the five operations already given.

**Lean reading.** `IsOmega x` is the inductive predicate "`x` is obtained from `1` by finitely many
of the five operations": `1`; `a + b`, `a - b`, `a * b`, `a / b` (with `b ≠ 0`: division by zero is
not an operation) for `a`, `b` already obtained; `√(1 + ω²)` for `ω` already obtained (the
positive real square root; `1 + ω² > 0`, so no imaginaries arise). `Omega : Subfield ℝ` is the
set of such numbers, and `OmegaField` the corresponding type. Proved: `Ω` is a subfield of `ℝ`
closed under `ω ↦ √(1 + ω²)` (`Omega.sqrt_mem`), it is the *smallest* such subfield
(`Omega_le_of_closed`), and all its elements are algebraic numbers (`Omega.isAlgebraic`), as
Hilbert's "algebraic numbers" asserts. The real numbers are taken from mathlib's `ℝ`; that `Ω`
can be built from `ℚ` alone (as the closure inside the real algebraic numbers) is not needed.

**Status.** definition
-/

/-- `x` is obtained from `1` by finitely many additions, subtractions, multiplications, divisions
and operations `ω ↦ √(1 + ω²)`. -/
inductive IsOmega : ℝ → Prop
  | one : IsOmega 1
  | add {a b : ℝ} : IsOmega a → IsOmega b → IsOmega (a + b)
  | sub {a b : ℝ} : IsOmega a → IsOmega b → IsOmega (a - b)
  | mul {a b : ℝ} : IsOmega a → IsOmega b → IsOmega (a * b)
  | div {a b : ℝ} : IsOmega a → IsOmega b → b ≠ 0 → IsOmega (a / b)
  | sqrt {w : ℝ} : IsOmega w → IsOmega (Real.sqrt (1 + w ^ 2))

theorem IsOmega.zero : IsOmega 0 := by simpa using IsOmega.sub IsOmega.one IsOmega.one

/-- **Hilbert's field `Ω`** (§ 9) as a subfield of `ℝ`. -/
def Omega : Subfield ℝ where
  carrier := {x | IsOmega x}
  zero_mem' := IsOmega.zero
  one_mem' := IsOmega.one
  add_mem' := IsOmega.add
  mul_mem' := IsOmega.mul
  neg_mem' := fun {x} hx => by simpa using IsOmega.sub IsOmega.zero hx
  inv_mem' := fun x hx => by
    by_cases h : x = 0
    · rw [h, inv_zero]; exact IsOmega.zero
    · simpa using IsOmega.div IsOmega.one hx h

/-- The type of the numbers of `Ω`. -/
abbrev OmegaField : Type := Omega

theorem mem_Omega {x : ℝ} : x ∈ Omega ↔ IsOmega x := Iff.rfl

/-- `Ω` is closed under Hilbert's fifth operation. -/
theorem Omega.sqrt_mem {w : ℝ} (hw : w ∈ Omega) : Real.sqrt (1 + w ^ 2) ∈ Omega :=
  IsOmega.sqrt hw

/-- `Ω` is the smallest subfield of `ℝ` closed under `ω ↦ √(1 + ω²)`. -/
theorem Omega_le_of_closed (F : Subfield ℝ) (hF : ∀ w ∈ F, Real.sqrt (1 + w ^ 2) ∈ F) :
    Omega ≤ F := by
  intro x hx
  induction hx with
  | one => exact F.one_mem
  | add _ _ ha hb => exact F.add_mem ha hb
  | sub _ _ ha hb => exact F.sub_mem ha hb
  | mul _ _ ha hb => exact F.mul_mem ha hb
  | div _ _ _ ha hb => exact F.div_mem ha hb
  | sqrt _ hw => exact hF _ hw

/-- **The numbers of `Ω` are algebraic.** -/
theorem Omega.isAlgebraic {x : ℝ} (hx : x ∈ Omega) : IsAlgebraic ℚ x := by
  induction hx with
  | one => exact isAlgebraic_one
  | add _ _ ha hb => exact ha.add hb
  | sub _ _ ha hb => exact ha.sub hb
  | mul _ _ ha hb => exact ha.mul hb
  | div _ _ _ ha hb => rw [div_eq_mul_inv]; exact ha.mul hb.inv
  | @sqrt w _ hw =>
    apply IsAlgebraic.of_pow (n := 2) two_pos
    rw [Real.sq_sqrt (by positivity)]
    exact isAlgebraic_one.add (hw.mul hw |> fun h => by rw [sq]; exact h)

/-- `Ω` is a Pythagorean ordered field: closed under `ω ↦ √(1 + ω²)`. -/
instance OmegaField.instIsPythagorean : IsPythagorean OmegaField :=
  ⟨fun x => ⟨⟨Real.sqrt (1 + (x : ℝ) ^ 2), Omega.sqrt_mem x.2⟩, Real.sqrt_nonneg _, by
    apply Subtype.ext; simp [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (x : ℝ) ^ 2 by positivity)]⟩⟩

/-!
## [s9.points_lines] Points are pairs `(x, y)`, lines are ratios `(u : v : w)`

*(§ 9)*

> Let us regard a pair of numbers $(x, y)$ of the domain $\Omega$ as defining a point and the ratio of three such numbers $(u:v:w)$ of $\Omega$, where $u$, $v$ are not both equal to zero, as defining a straight line. Furthermore, let the existence of the equation \[ ux+vy+w = 0 \] express the condition that the point $(x, y)$ lies on the … straight line $(u:v:w)$.

**Lean reading.** Points are `Coord K 2` (`K = Ω` here; everything holds over any ordered field
`K`), the pair `(x, y)` being `AffPt.ofV ![x, y]`. Lines are encoded as one-dimensional affine
subspaces (`CoordLine K 2`), which the generic models of `AnalyticAux.lean` need; this unit proves
that they are exactly Hilbert's lines: every triple `(u, v, w)` with `(u, v) ≠ (0, 0)` has a line
`lineOfEq` whose points are the solutions of `ux + vy + w = 0` (`mem_lineOfEq`); every line is of
this form (`exists_eq_of_line`); and two triples give the same line iff they are proportional
(`lineOfEq_eq_iff`), so lines correspond one-to-one to the ratios `(u : v : w)`.

**Status.** proved (reading)
-/

namespace Coord

section Equations

variable {K : Type*}

/-- The point `(x, y)`. -/
def pt2 (x y : K) : Coord K 2 := AffPt.ofV ![x, y]

/-- The first coordinate. -/
def xc (X : Coord K 2) : K := AffPt.toV X 0

/-- The second coordinate. -/
def yc (X : Coord K 2) : K := AffPt.toV X 1

@[simp] theorem xc_pt2 (x y : K) : xc (pt2 x y) = x := rfl
@[simp] theorem yc_pt2 (x y : K) : yc (pt2 x y) = y := rfl

variable [Field K]

@[simp] theorem xc_add (X Y : Coord K 2) : xc (X + Y) = xc X + xc Y := rfl
@[simp] theorem yc_add (X Y : Coord K 2) : yc (X + Y) = yc X + yc Y := rfl
@[simp] theorem xc_sub (X Y : Coord K 2) : xc (X - Y) = xc X - xc Y := rfl
@[simp] theorem yc_sub (X Y : Coord K 2) : yc (X - Y) = yc X - yc Y := rfl
@[simp] theorem xc_smul (c : K) (X : Coord K 2) : xc (c • X) = c * xc X := rfl
@[simp] theorem yc_smul (c : K) (X : Coord K 2) : yc (c • X) = c * yc X := rfl
@[simp] theorem xc_zero : xc (0 : Coord K 2) = 0 := rfl
@[simp] theorem yc_zero : yc (0 : Coord K 2) = 0 := rfl

omit [Field K] in
theorem ext2 {X Y : Coord K 2} (hx : xc X = xc Y) (hy : yc X = yc Y) : X = Y := by
  apply AffPt.toV_injective; funext i; fin_cases i
  · exact hx
  · exact hy

omit [Field K] in
theorem eta2 (X : Coord K 2) : X = pt2 (xc X) (yc X) := ext2 rfl rfl

theorem ip_two (X Y : Coord K 2) : ip X Y = xc X * xc Y + yc X * yc Y := by
  rw [ip_def, Fin.sum_univ_two]; rfl

/-- The value of Hilbert's linear form `ux + vy + w` at a point. -/
def lin (u v w : K) (X : Coord K 2) : K := xc X * u + yc X * v + w

/-- A direction vector of the line `ux + vy + w = 0`. -/
def eqDir (u v : K) : Coord K 2 := pt2 v (-u)

open Classical in
/-- A point of the line `ux + vy + w = 0`. -/
noncomputable def eqBase (u v w : K) : Coord K 2 :=
  if v = 0 then pt2 (-w / u) 0 else pt2 0 (-w / v)

theorem lin_eqBase {u v : K} (h : u ≠ 0 ∨ v ≠ 0) (w : K) : lin u v w (eqBase u v w) = 0 := by
  unfold eqBase lin
  split_ifs with hv
  · have hu : u ≠ 0 := h.resolve_right (not_not.2 hv)
    simp [hv]; field_simp; ring
  · simp; field_simp; ring

theorem eqDir_ne_zero {u v : K} (h : u ≠ 0 ∨ v ≠ 0) : eqDir u v ≠ 0 := by
  intro h0
  have hx := congrArg xc h0
  have hy := congrArg yc h0
  simp [eqDir] at hx hy
  rcases h with h | h
  · exact h hy
  · exact h hx

theorem lin_add_smul_eqDir (u v w t : K) (X : Coord K 2) :
    lin u v w (t • eqDir u v + X) = lin u v w X := by
  simp [lin, eqDir]; ring

/-- **The line `(u : v : w)`**: the solutions of `ux + vy + w = 0`. -/
noncomputable def lineOfEq (u v w : K) (h : u ≠ 0 ∨ v ≠ 0) : CoordLine K 2 :=
  AffLine.through (eqBase u v w) (eqDir u v + eqBase u v w) (by
    intro e; apply eqDir_ne_zero h
    have := congrArg (· - eqBase u v w) e; simpa using this.symm)

theorem lin_eq_zero_iff {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) (X : Coord K 2) :
    lin u v w X = 0 ↔ ∃ t : K, X = t • eqDir u v + eqBase u v w := by
  constructor
  · intro hX
    have h0 := lin_eqBase h w
    -- `X - base` is orthogonal to `(u, v)`, hence a multiple of `(v, -u)`
    set B := eqBase u v w
    have hd : (xc X - xc B) * u + (yc X - yc B) * v = 0 := by
      unfold lin at hX h0; linear_combination hX - h0
    rcases h with hu | hv
    · refine ⟨-(yc X - yc B) / u, ext2 ?_ ?_⟩ <;> simp [eqDir]
      · field_simp; linear_combination hd
      · field_simp; ring
    · refine ⟨(xc X - xc B) / v, ext2 ?_ ?_⟩ <;> simp [eqDir]
      · field_simp; ring
      · field_simp; linear_combination hd
  · rintro ⟨t, rfl⟩
    rw [lin_add_smul_eqDir, lin_eqBase h]

theorem mem_lineOfEq {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) (X : Coord K 2) :
    X ∈ lineOfEq u v w h ↔ lin u v w X = 0 := by
  rw [lineOfEq, AffLine.mem_through_iff, lin_eq_zero_iff h, add_sub_cancel_right]

/-- Every straight line is the line of an equation `ux + vy + w = 0` with `(u, v) ≠ (0, 0)`. -/
theorem exists_eq_of_line (a : CoordLine K 2) :
    ∃ (u v w : K) (h : u ≠ 0 ∨ v ≠ 0), a = lineOfEq u v w h := by
  obtain ⟨O, d, hd, hmem⟩ := a.exists_param
  have hd' : xc d ≠ 0 ∨ yc d ≠ 0 := by
    by_contra hc; simp only [not_or, not_not] at hc; exact hd (ext2 (by simp [hc.1]) (by simp [hc.2]))
  have h : -yc d ≠ 0 ∨ xc d ≠ 0 := by
    rcases hd' with h | h
    · exact Or.inr h
    · exact Or.inl (neg_ne_zero.2 h)
  refine ⟨-yc d, xc d, xc O * yc d - yc O * xc d, h, ?_⟩
  have hO : O ∈ a := (hmem O).2 ⟨0, by simp⟩
  have hdO : d + O ∈ a := (hmem _).2 ⟨1, by simp⟩
  have hne : O ≠ d + O := by
    intro e; apply hd; have := congrArg (· - O) e; simpa using this.symm
  refine line_unique hne hO hdO ?_ ?_
  · rw [mem_lineOfEq]; simp only [lin]; ring
  · rw [mem_lineOfEq]; simp only [lin, xc_add, yc_add]; ring

theorem lin_smul (c u v w : K) (X : Coord K 2) : lin (c * u) (c * v) (c * w) X = c * lin u v w X := by
  simp only [lin]; ring

/-- Two equations define the same line iff their coefficients are proportional: lines are the
ratios `(u : v : w)`. -/
theorem lineOfEq_eq_iff {u v w u' v' w' : K} (h : u ≠ 0 ∨ v ≠ 0) (h' : u' ≠ 0 ∨ v' ≠ 0) :
    lineOfEq u v w h = lineOfEq u' v' w' h' ↔
      ∃ c : K, c ≠ 0 ∧ u' = c * u ∧ v' = c * v ∧ w' = c * w := by
  have hB : eqBase u v w ∈ lineOfEq u v w h := AffLine.left_mem_through _
  have hBd : eqDir u v + eqBase u v w ∈ lineOfEq u v w h := AffLine.right_mem_through _
  have hne : eqBase u v w ≠ eqDir u v + eqBase u v w := by
    intro e; apply eqDir_ne_zero h
    have := congrArg (· - eqBase u v w) e; simpa using this.symm
  constructor
  · intro e
    rw [e, mem_lineOfEq] at hB hBd
    have h0 := lin_eqBase h w
    set B := eqBase u v w
    have k : v * u' - u * v' = 0 := by
      have : lin u' v' w' (eqDir u v + B) - lin u' v' w' B = v * u' - u * v' := by
        simp only [lin, eqDir, xc_add, yc_add, xc_pt2, yc_pt2]; ring
      rw [← this, hB, hBd, sub_zero]
    obtain ⟨c, hu', hv'⟩ : ∃ c : K, u' = c * u ∧ v' = c * v := by
      rcases h with hu | hv
      · refine ⟨u' / u, by field_simp, ?_⟩
        field_simp; linear_combination -k
      · refine ⟨v' / v, ?_, by field_simp⟩
        field_simp; linear_combination k
    have hc : c ≠ 0 := by
      rintro rfl; simp at hu' hv'; rcases h' with h' | h' <;> contradiction
    refine ⟨c, hc, hu', hv', ?_⟩
    simp only [lin] at hB h0
    rw [hu', hv'] at hB
    linear_combination hB - c * h0
  · rintro ⟨c, hc, rfl, rfl, rfl⟩
    refine line_unique hne hB hBd ?_ ?_
    · rw [mem_lineOfEq, lin_smul, (mem_lineOfEq h _).1 hB, mul_zero]
    · rw [mem_lineOfEq, lin_smul, (mem_lineOfEq h _).1 hBd, mul_zero]

end Equations

end Coord

/-!
## [s9.connection_parallels] Axioms I 1–2 and III hold

*(§ 9)*

> Then, as one readily sees, axioms I, 1–2 and III are fulfilled.

**Lean reading.** `omega_planeParallels`: the coordinate plane over `Ω` is a `PlaneParallels`
geometry, i.e. satisfies group I of plane geometry (I 1, I 2, and the plane clauses of I 7, which
Hilbert does not mention but which are equally evident) and the axiom of parallels III. The proof is
generic (`AffPt.instPlaneConnection`, `AffPt.instPlaneParallels` in `AnalyticAux.lean`): it holds
over every ordered division ring, indeed every division ring for group I and III, with lines the
one-dimensional affine subspaces (by unit `s9.points_lines` these are Hilbert's lines). The
parallel to `a` through `A` is `A + dir a`, i.e. the line `(u : v : w')` with the same `u`, `v`.

**Status.** proved
-/

theorem omega_planeParallels : PlaneParallels (Coord OmegaField 2) (CoordLine OmegaField 2) :=
  inferInstance

/-- Over any division ring, groups I and III of plane geometry hold in `K²`. -/
theorem planeParallels_coord (K : Type*) [DivisionRing K] :
    PlaneParallels (Coord K 2) (CoordLine K 2) :=
  inferInstance

/-!
## [s9.real_numbers] The numbers of `Ω` are real

*(§ 9)*

> The numbers of the domain $\Omega$ are all real numbers.

**Lean reading.** By construction `Ω` is a subfield of `ℝ` (`Omega : Subfield ℝ`); the content of
the claim is that Hilbert's fifth operation never leads out of the reals, because its argument is
positive: `one_add_sq_pos` (`1 + ω² > 0`). Consequently `Ω` inherits the order of `ℝ`, which is what
the next sentence ("these numbers may be arranged according to magnitude") uses: `OmegaField` is a
linearly ordered field (`omega_isStrictOrderedRing`) whose order is that of `ℝ` (`omega_lt_iff`).

**Status.** proved
-/

theorem one_add_sq_pos (w : ℝ) : 0 < 1 + w ^ 2 := by positivity

theorem omega_isStrictOrderedRing : IsStrictOrderedRing OmegaField := inferInstance

theorem omega_lt_iff {x y : OmegaField} : x < y ↔ (x : ℝ) < y := Iff.rfl

/-!
## [s9.order] The order of the points of a line

*(§ 9)*

> If now we take into consideration the fact that these numbers may be arranged according to magnitude, we can easily make such necessary conventions concerning our points and straight lines as will also make the axioms of order (group II) hold. In fact, if $(x_1,y_1)$, $(x_2, y_2)$, $(x_3, y_3)$, $\ldots$ are any points whatever of a straight line, then this may be taken as their sequence on this straight line, providing the numbers $x_1$, $x_2$, $x_3,\ldots,$ or the numbers $y_1$, $y_2$, $y_3, \ldots,$ either all increase or decrease in the order of sequence given here.

**Lean reading.** Betweenness in the model is `Sbtw` (`B = A + t (C - A)`, `0 < t < 1`).
`Coord.between_iff_monotone` proves that this is Hilbert's convention: for three points of a line,
`X₂` lies between `X₁` and `X₃` iff the `x`-coordinates or the `y`-coordinates are strictly
increasing or strictly decreasing along `X₁, X₂, X₃`. For a sequence of any length,
`Coord.between_seq_iff_monotone`: distinct points `X₀, …, Xₙ₋₁` of a line are in this order (`Xⱼ`
lies between `Xᵢ` and `Xₖ` whenever `i < j < k`, the order of a sequence of points of § 4) iff
their `x`-coordinates or their `y`-coordinates are strictly increasing or strictly decreasing.
The linear axioms II 1–4 hold over every ordered division ring (`AffPt.instLineOrder`);
`omega_lineOrder` is the case of `Ω`.

**Status.** proved (reading)
-/

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Strict betweenness is preserved and reflected by an affine map `t ↦ t k + o` with `k ≠ 0`. -/
theorem strictBetween_affine {k : K} (hk : k ≠ 0) (o t₁ t₂ t₃ : K) :
    ((t₁ * k + o < t₂ * k + o ∧ t₂ * k + o < t₃ * k + o) ∨
        (t₃ * k + o < t₂ * k + o ∧ t₂ * k + o < t₁ * k + o)) ↔
      ((t₁ < t₂ ∧ t₂ < t₃) ∨ (t₃ < t₂ ∧ t₂ < t₁)) := by
  simp only [add_lt_add_iff_right]
  rcases lt_or_gt_of_ne hk with h | h
  · simp only [mul_lt_mul_right_of_neg h]; tauto
  · simp only [mul_lt_mul_iff_left₀ h]

/-- **Hilbert's convention for the order on a line** (§ 9). -/
theorem between_iff_monotone {X₁ X₂ X₃ : Coord K 2} (h : Collinear X₁ X₂ X₃) :
    Between X₁ X₂ X₃ ↔
      ((xc X₁ < xc X₂ ∧ xc X₂ < xc X₃) ∨ (xc X₃ < xc X₂ ∧ xc X₂ < xc X₁)) ∨
      ((yc X₁ < yc X₂ ∧ yc X₂ < yc X₃) ∨ (yc X₃ < yc X₂ ∧ yc X₂ < yc X₁)) := by
  obtain ⟨a, h₁, h₂, h₃⟩ := h
  obtain ⟨O, d, hd, hmem⟩ := a.exists_param
  obtain ⟨t₁, rfl⟩ := (hmem _).1 h₁
  obtain ⟨t₂, rfl⟩ := (hmem _).1 h₂
  obtain ⟨t₃, rfl⟩ := (hmem _).1 h₃
  rw [AffPt.between_iff, sbtw_param_iff hd]
  simp only [xc_add, yc_add, xc_smul, yc_smul]
  have hd' : xc d ≠ 0 ∨ yc d ≠ 0 := by
    by_contra hc; simp only [not_or, not_not] at hc
    exact hd (ext2 (by simp [hc.1]) (by simp [hc.2]))
  by_cases hx : xc d = 0
  · have hy : yc d ≠ 0 := hd'.resolve_left (not_not.2 hx)
    rw [strictBetween_affine hy]
    simp only [hx, mul_zero, zero_add, lt_irrefl, false_and, or_self, false_or]
  · rw [strictBetween_affine hx]
    by_cases hy : yc d = 0
    · simp only [hy, mul_zero, zero_add, lt_irrefl, false_and, or_self, or_false]
    · rw [strictBetween_affine hy, or_self]

/-- If all triples of a finite sequence are monotone and the first two terms increase, the
sequence is strictly increasing. -/
theorem strictMono_of_triples {α : Type*} [LinearOrder α] {n : ℕ} (s : Fin n → α)
    (H : ∀ i j k : Fin n, i < j → j < k → (s i < s j ∧ s j < s k) ∨ (s k < s j ∧ s j < s i))
    (h01 : ∀ i j : Fin n, i.val = 0 → j.val = 1 → s i < s j) : StrictMono s := by
  have key : ∀ (z k : Fin n), z.val = 0 → 0 < k.val → s z < s k := by
    intro z k hz hk
    by_cases hk1 : k.val = 1
    · exact h01 z k hz hk1
    · have hn : 1 < n := by omega
      let o : Fin n := ⟨1, hn⟩
      have h0o := h01 z o hz rfl
      rcases H z o k (by simp [Fin.lt_def, hz, o]) (by simp [Fin.lt_def, o]; omega) with h | h
      · exact h0o.trans h.2
      · exact absurd (h.2.trans h0o) (lt_irrefl _)
  intro i j hij
  by_cases hi : i.val = 0
  · exact key i j hi (by rw [Fin.lt_def] at hij; omega)
  · have hn : 0 < n := by omega
    let z : Fin n := ⟨0, hn⟩
    have hzi := key z i rfl (by omega)
    rcases H z i j (by simp [Fin.lt_def, z]; omega) hij with h | h
    · exact h.2
    · exact absurd (h.2.trans hzi) (lt_irrefl _)

/-- An injective finite sequence all of whose triples are monotone is strictly monotone. -/
theorem strictMono_or_strictAnti_iff_triples {α : Type*} [LinearOrder α] {n : ℕ} (s : Fin n → α)
    (hs : Function.Injective s) :
    (∀ i j k : Fin n, i < j → j < k → (s i < s j ∧ s j < s k) ∨ (s k < s j ∧ s j < s i)) ↔
      StrictMono s ∨ StrictAnti s := by
  constructor
  · intro H
    by_cases hn : n < 2
    · left; intro i j hij; rw [Fin.lt_def] at hij; omega
    · have hn' : 1 < n := by omega
      let z : Fin n := ⟨0, by omega⟩
      let o : Fin n := ⟨1, hn'⟩
      have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
      have hzo' : ∀ i j : Fin n, i.val = 0 → j.val = 1 → i = z ∧ j = o := fun i j hi hj =>
        ⟨Fin.ext hi, Fin.ext hj⟩
      rcases lt_or_gt_of_ne (hs.ne hzo) with h | h
      · left
        refine strictMono_of_triples s H fun i j hi hj => ?_
        obtain ⟨rfl, rfl⟩ := hzo' i j hi hj; exact h
      · right
        let t : Fin n → αᵒᵈ := fun i => OrderDual.toDual (s i)
        have ht : StrictMono t := by
          refine strictMono_of_triples t (fun i j k hij hjk => ?_) fun i j hi hj => ?_
          · simp only [t, OrderDual.toDual_lt_toDual]
            rcases H i j k hij hjk with h' | h'
            · exact Or.inr ⟨h'.2, h'.1⟩
            · exact Or.inl ⟨h'.2, h'.1⟩
          · obtain ⟨rfl, rfl⟩ := hzo' i j hi hj
            simp only [t, OrderDual.toDual_lt_toDual]; exact h
        intro i j hij
        exact OrderDual.toDual_lt_toDual.1 (ht hij)
  · rintro (h | h) i j k hij hjk
    · exact Or.inl ⟨h hij, h hjk⟩
    · exact Or.inr ⟨h hjk, h hij⟩

theorem strictMono_affine_iff {n : ℕ} (s : Fin n → K) {c : K} (hc : c ≠ 0) (o : K) :
    (StrictMono (fun i => s i * c + o) ∨ StrictAnti (fun i => s i * c + o)) ↔
      (StrictMono s ∨ StrictAnti s) := by
  rcases lt_or_gt_of_ne hc with h | h
  · have e1 : StrictMono (fun i => s i * c + o) ↔ StrictAnti s := by
      constructor
      · intro hm i j hij
        have := hm hij; simp only [add_lt_add_iff_right] at this
        exact (mul_lt_mul_right_of_neg h).1 this
      · intro hm i j hij
        simp only [add_lt_add_iff_right]; exact (mul_lt_mul_right_of_neg h).2 (hm hij)
    have e2 : StrictAnti (fun i => s i * c + o) ↔ StrictMono s := by
      constructor
      · intro hm i j hij
        have := hm hij; simp only [add_lt_add_iff_right] at this
        exact (mul_lt_mul_right_of_neg h).1 this
      · intro hm i j hij
        simp only [add_lt_add_iff_right]; exact (mul_lt_mul_right_of_neg h).2 (hm hij)
    rw [e1, e2, or_comm]
  · have e1 : StrictMono (fun i => s i * c + o) ↔ StrictMono s := by
      constructor
      · intro hm i j hij
        have := hm hij; simp only [add_lt_add_iff_right] at this
        exact (mul_lt_mul_iff_left₀ h).1 this
      · intro hm i j hij
        simp only [add_lt_add_iff_right]; exact (mul_lt_mul_iff_left₀ h).2 (hm hij)
    have e2 : StrictAnti (fun i => s i * c + o) ↔ StrictAnti s := by
      constructor
      · intro hm i j hij
        have := hm hij; simp only [add_lt_add_iff_right] at this
        exact (mul_lt_mul_iff_left₀ h).1 this
      · intro hm i j hij
        simp only [add_lt_add_iff_right]; exact (mul_lt_mul_iff_left₀ h).2 (hm hij)
    rw [e1, e2]

omit [IsStrictOrderedRing K] in
theorem strictMono_affine_zero {n : ℕ} (s : Fin n → K) (o : K) :
    (StrictMono (fun i => s i * 0 + o) ∨ StrictAnti (fun i => s i * 0 + o)) → StrictMono s := by
  rintro (h | h) i j hij
  · exact absurd (h hij) (by simp)
  · exact absurd (h hij) (by simp)

/-- **Hilbert's convention for sequences of points on a line** (§ 9): points `X₀, X₁, …, Xₙ₋₁` of a
line are in this order (every `Xⱼ` lies between `Xᵢ` and `Xₖ` for `i < j < k`) iff their
`x`-coordinates or their `y`-coordinates all increase or all decrease. -/
theorem between_seq_iff_monotone {n : ℕ} {X : Fin n → Coord K 2} {a : CoordLine K 2}
    (ha : ∀ i, X i ∈ a) (hinj : Function.Injective X) :
    (∀ i j k : Fin n, i < j → j < k → Between (X i) (X j) (X k)) ↔
      (StrictMono (fun i => xc (X i)) ∨ StrictAnti (fun i => xc (X i))) ∨
        (StrictMono (fun i => yc (X i)) ∨ StrictAnti (fun i => yc (X i))) := by
  obtain ⟨O, d, hd, hmem⟩ := a.exists_param
  choose s hs using fun i => (hmem (X i)).1 (ha i)
  have hsinj : Function.Injective s := fun i j h => hinj (by rw [hs i, hs j, h])
  have hx : (fun i => xc (X i)) = fun i => s i * xc d + xc O := by
    funext i; rw [hs i]; simp
  have hy : (fun i => yc (X i)) = fun i => s i * yc d + yc O := by
    funext i; rw [hs i]; simp
  have hB : (∀ i j k : Fin n, i < j → j < k → Between (X i) (X j) (X k)) ↔
      ∀ i j k : Fin n, i < j → j < k → (s i < s j ∧ s j < s k) ∨ (s k < s j ∧ s j < s i) := by
    refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun k => ?_
    rw [hs i, hs j, hs k, AffPt.between_iff, sbtw_param_iff hd]
  rw [hB, strictMono_or_strictAnti_iff_triples s hsinj, hx, hy]
  have hd' : xc d ≠ 0 ∨ yc d ≠ 0 := by
    by_contra hc; simp only [not_or, not_not] at hc
    exact hd (ext2 (by simp [hc.1]) (by simp [hc.2]))
  by_cases hxd : xc d = 0
  · have hyd : yc d ≠ 0 := hd'.resolve_left (not_not.2 hxd)
    rw [strictMono_affine_iff s hyd]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · rw [hxd] at h; exact Or.inl (strictMono_affine_zero s _ h)
      · exact h
  · rw [strictMono_affine_iff s hxd]
    by_cases hyd : yc d = 0
    · constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · rw [hyd] at h; exact Or.inl (strictMono_affine_zero s _ h)
    · rw [strictMono_affine_iff s hyd, or_self]

end Coord

theorem omega_lineOrder : LineOrder (Coord OmegaField 2) (CoordLine OmegaField 2) := inferInstance

/-!
## [s9.pasch] The sides of a line: axiom II 5

*(§ 9)*

> In order that axiom II, 5 shall be fulfilled, we have merely to assume that all points corresponding to values of $x$ and $y$ which make $ux+vy+w$ less than zero or greater than zero shall fall respectively upon the one side or upon the other side of the straight line $(u:v:w)$. We can easily convince ourselves that this convention is in accordance with those which precede, and by which the sequence of the points on a straight line has already been determined.

**Lean reading.** The sides of a line are not a separate convention in the model: they are defined
from betweenness (§ 4, `SameSide`). "This convention is in accordance with those which precede" is
then the theorem `Coord.sameSide_lineOfEq_iff`: two points off the line `(u : v : w)` lie on the
same side iff `ux + vy + w` has the same sign at both (and on opposite sides iff the signs differ,
`Coord.exists_between_lineOfEq_iff`). II 5 (Pasch) follows (`omega_planeOrder`); the proof
(`AffPt.pasch_in`) uses exactly this sign rule and holds over every ordered division ring.

**Status.** proved
-/

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The linear part `(x, y) ↦ ux + vy` of Hilbert's linear form. -/
def linForm (u v : K) : Coord K 2 →ₗ[K] K where
  toFun Z := xc Z * u + yc Z * v
  map_add' X Y := by simp only [xc_add, yc_add]; ring
  map_smul' c X := by simp only [xc_smul, yc_smul, smul_eq_mul, RingHom.id_apply]; ring

theorem lin_eq_linForm {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) (X : Coord K 2) :
    lin u v w X = linForm u v (X - eqBase u v w) := by
  have h0 := lin_eqBase h w
  simp only [linForm, LinearMap.coe_mk, AddHom.coe_mk, xc_sub, yc_sub]
  simp only [lin] at h0 ⊢
  linear_combination h0

theorem lineOfEq_side {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) :
    ∀ X ∈ (⊤ : AffineSubspace K (Coord K 2)),
      (X ∈ (lineOfEq u v w h).carrier ↔ linForm u v (X - eqBase u v w) = 0) := by
  intro X _
  rw [← lin_eq_linForm h]; exact mem_lineOfEq h X

/-- Points off the line `(u : v : w)` are separated by it iff `ux + vy + w` has opposite signs. -/
theorem exists_between_lineOfEq_iff {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) {P Q : Coord K 2}
    (hP : P ∉ lineOfEq u v w h) (hQ : Q ∉ lineOfEq u v w h) :
    (∃ X, X ∈ lineOfEq u v w h ∧ Between P X Q) ↔ lin u v w P * lin u v w Q < 0 := by
  rw [lin_eq_linForm h, lin_eq_linForm h]
  exact AffPt.exists_between_iff_mul_neg le_top (lineOfEq_side h) (AffineSubspace.mem_top K _ P)
    (AffineSubspace.mem_top K _ Q) hP hQ

/-- **Hilbert's convention for the sides of a line** (§ 9): two points lie on the same side of the
line `(u : v : w)` iff `ux + vy + w` has the same (nonzero) sign at both. -/
theorem sameSide_lineOfEq_iff {u v w : K} (h : u ≠ 0 ∨ v ≠ 0) (P Q : Coord K 2) :
    SameSide (lineOfEq u v w h) P Q ↔ 0 < lin u v w P * lin u v w Q := by
  rw [lin_eq_linForm h, lin_eq_linForm h]
  exact AffPt.sameSide_iff_mul_pos le_top (lineOfEq_side h) (AffineSubspace.mem_top K _ P)
    (AffineSubspace.mem_top K _ Q)

end Coord

theorem omega_planeOrder : PlaneOrder (Coord OmegaField 2) (CoordLine OmegaField 2) :=
  inferInstance

/-!
## [s9.laying_off] Laying off segments and angles

*(§ 9)*

> The laying off of segments and of angles follows by the known methods of analytical geometry.

**Lean reading.** Congruence in the model is metric (`Coord.instHasSegCong`: equal squared lengths;
`Coord.instHasAngCong`: equal cosines, `Coord.AngleEq`), the reading of Hilbert's "conventions"
made precise in units `s9.translation`, `s9.rotation` (translations and rotations preserve both).
Laying off is then: a segment `AB` is laid off from `A'` towards `C'` at `A' + λ (C' - A')`,
`λ = |AB| / |A'C'|` (`Coord.axiomIV1LayOff`); an angle `∠AOB` is laid off at `O'A'` towards `D'` at
`O' + x e₁ + y e₂`, `e₁ = A' - O'`, `e₂ ⊥ e₁` towards `D'`, with `x`, `y` given by the cosine and
the sine of `∠AOB` (`Coord.layOff_angle_in`, in any plane of `K²` or `K³`), and both are unique.
Both need square roots of sums of squares, i.e. a Pythagorean field (unit `s9.sqrt`); over `Ω`
they are `omega_layOff_segment`, `omega_layOff_angle`.

**Status.** proved (reading)
-/

theorem omega_layOff_segment : AxiomIV1LayOff (Coord OmegaField 2) := Coord.axiomIV1LayOff

theorem omega_layOff_angle : AxiomIV4LayOff (Coord OmegaField 2) :=
  PlaneAngleCongruence.ax_IV4 (Line := CoordLine OmegaField 2)

/-!
## [s9.translation] Translations

*(§ 9)*

> A transformation of the form \begin{eqnarray*} x' & = & x + a \\ y' & = & y + b \end{eqnarray*} produces a translation of segments and of angles.

**Lean reading.** The translation by the vector `t` (Hilbert's `t = (a, b)`; the lemmas hold in
`K^n` for every `n`) maps lines onto lines (`Coord.exists_line_translate`), preserves and reflects
betweenness (`Coord.between_translate`), and every segment and every angle is congruent to its
translate (`Coord.segCong_translate`, `Coord.angCong_translate`): "a translation of segments and
of angles" in the sense of the congruences of the model.

**Status.** proved
-/

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

theorem between_translate (t A B C : Coord K n) :
    Between (A + t) (B + t) (C + t) ↔ Between A B C := by
  simp only [AffPt.between_iff, AffPt.sbtw_iff_param, add_sub_add_right_eq_sub]
  have e : ∀ s : K, (B + t = s • (C - A) + (A + t) ↔ B = s • (C - A) + A) := fun s => by
    rw [← add_assoc]; exact add_left_inj t
  simp only [e, ne_eq, add_left_inj]

omit [IsStrictOrderedRing K] [LinearOrder K] in
theorem segCong_translate (t A B : Coord K n) : SegCong A B (A + t) (B + t) := by
  rw [segCong_iff, add_sub_add_right_eq_sub]

omit [IsStrictOrderedRing K] in
theorem angCong_translate (t A O B : Coord K n) : AngCong A O B (A + t) (O + t) (B + t) := by
  rw [angCong_iff, add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]; exact angleEq_refl _ _

omit [IsStrictOrderedRing K] [LinearOrder K] in
theorem exists_line_translate (t : Coord K n) (a : CoordLine K n) :
    ∃ a' : CoordLine K n, ∀ X, X + t ∈ a' ↔ X ∈ a := by
  obtain ⟨O, d, hd, hmem⟩ := a.exists_param
  have hne : O + t ≠ d + O + t := by
    intro e; apply hd; have := congrArg (· - (O + t)) e; simp only [sub_self] at this
    rw [this]; abel
  refine ⟨AffLine.through _ _ hne, fun X => ?_⟩
  rw [AffLine.mem_through_iff, hmem]
  have : d + O + t - (O + t) = d := by abel
  rw [this]
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← add_assoc] at hr; exact add_right_cancel hr⟩
  · rintro ⟨r, rfl⟩; exact ⟨r, by abel⟩

end Coord

/-!
## [s9.rotation] Rotations

*(§ 9)*

> Furthermore, if, in the accompanying figure, we represent the point $(0, 0)$ by $O$ and the point $(1, 0)$ by $E$, then, corresponding to a rotation of the angle $COE$ about $O$ as a center, any point $(x, y)$ is transformed into another point $(x', y')$ so related that \begin{eqnarray*} x' & = & \frac{a}{\sqrt{a^2+b^2}} x - \frac{b}{\sqrt{a^2+b^2}}y , \\ y' & = & \frac{b}{\sqrt{a^2+b^2}} x + \frac{a}{\sqrt{a^2+b^2}}y . \end{eqnarray*}

**Lean reading.** Figure 13 (reconstructed): `O = (0, 0)`, `E = (1, 0)`, `C = (a, b) ≠ O`; the
rotation turns the half-ray `OE` onto the half-ray `OC`. `Coord.rot a b r` is Hilbert's map with
`r = √(a² + b²)` given as a number with `r > 0`, `r² = a² + b²` (in `Ω` it exists by unit
`s9.sqrt`). Proved: the rotation is linear and preserves the inner product (`Coord.ip_rot`), hence
it maps lines onto lines (`Coord.exists_line_rot`), preserves and reflects betweenness
(`Coord.between_rot`), and every segment and angle is congruent to its image
(`Coord.segCong_rot`, `Coord.angCong_rot`); it maps `E` to the point of the half-ray `OC` at
distance `1` and the half-ray `OE` onto the half-ray `OC` (`Coord.rot_E`, `Coord.rot_mem_ray`,
`Coord.rot_ray_surj`), so it is the rotation "of the angle `COE` about `O`".

**Status.** proved (reading)
-/

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Hilbert's rotation** with `r = √(a² + b²)`. -/
def rot (a b r : K) (X : Coord K 2) : Coord K 2 :=
  pt2 (a / r * xc X - b / r * yc X) (b / r * xc X + a / r * yc X)

variable {a b r : K}

theorem rot_add (X Y : Coord K 2) : rot a b r (X + Y) = rot a b r X + rot a b r Y :=
  ext2 (by simp [rot]; ring) (by simp [rot]; ring)

theorem rot_sub (X Y : Coord K 2) : rot a b r (X - Y) = rot a b r X - rot a b r Y :=
  ext2 (by simp [rot]; ring) (by simp [rot]; ring)

theorem rot_smul (c : K) (X : Coord K 2) : rot a b r (c • X) = c • rot a b r X :=
  ext2 (by simp [rot]; ring) (by simp [rot]; ring)

theorem ip_rot (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) (X Y : Coord K 2) :
    ip (rot a b r X) (rot a b r Y) = ip X Y := by
  rw [ip_two, ip_two]
  simp only [rot, xc_pt2, yc_pt2]
  field_simp
  linear_combination -(xc X * xc Y + yc X * yc Y) * hr

theorem rot_injective (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) :
    Function.Injective (rot a b r) := by
  intro X Y h
  have : ip (X - Y) (X - Y) = 0 := by
    rw [← ip_rot hr hr0, rot_sub, h, sub_self, ip_zero_left]
  exact sub_eq_zero.1 (ip_self_eq_zero.1 this)

theorem between_rot (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) (A B C : Coord K 2) :
    Between (rot a b r A) (rot a b r B) (rot a b r C) ↔ Between A B C := by
  simp only [AffPt.between_iff, AffPt.sbtw_iff_param]
  have hinj := rot_injective hr hr0
  have e : ∀ s : K, (rot a b r B = s • (rot a b r C - rot a b r A) + rot a b r A ↔
      B = s • (C - A) + A) := fun s => by
    rw [← rot_sub, ← rot_smul, ← rot_add]; exact hinj.eq_iff
  simp only [e, ne_eq, hinj.eq_iff]

theorem segCong_rot (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) (A B : Coord K 2) :
    SegCong A B (rot a b r A) (rot a b r B) := by
  rw [segCong_iff, ← rot_sub, ip_rot hr hr0]

theorem angCong_rot (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) (A O B : Coord K 2) :
    AngCong A O B (rot a b r A) (rot a b r O) (rot a b r B) := by
  rw [angCong_iff, ← rot_sub, ← rot_sub]
  exact ⟨by rw [ip_rot hr hr0], by rw [ip_rot hr hr0, ip_rot hr hr0, ip_rot hr hr0]⟩

theorem exists_line_rot (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) (l : CoordLine K 2) :
    ∃ l' : CoordLine K 2, ∀ X, rot a b r X ∈ l' ↔ X ∈ l := by
  have hinj := rot_injective hr hr0
  obtain ⟨O, d, hd, hmem⟩ := l.exists_param
  have hne : rot a b r O ≠ rot a b r (d + O) := by
    intro e; apply hd; have := hinj e; have := congrArg (· - O) this; simpa using this.symm
  refine ⟨AffLine.through _ _ hne, fun X => ?_⟩
  rw [AffLine.mem_through_iff, hmem, ← rot_sub, add_sub_cancel_right]
  constructor
  · rintro ⟨s, hs⟩; exact ⟨s, hinj (by rw [hs, rot_add, rot_smul])⟩
  · rintro ⟨s, rfl⟩; exact ⟨s, by rw [rot_add, rot_smul]⟩

/-- The rotation maps `E = (1, 0)` to the point `C / r` of the half-ray `OC`, at distance `1`. -/
theorem rot_E (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) :
    rot a b r (pt2 1 0) = r⁻¹ • pt2 a b ∧ ip (rot a b r (pt2 1 0)) (rot a b r (pt2 1 0)) = 1 := by
  refine ⟨ext2 (by simp [rot]; ring) (by simp [rot]; ring), ?_⟩
  rw [ip_rot hr hr0, ip_two]; simp

/-- The rotation turns the half-ray `OE` into the half-ray `OC`. -/
theorem rot_mem_ray (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) {X : Coord K 2}
    (hX : X ∈ ray (0 : Coord K 2) (pt2 1 0)) : rot a b r X ∈ ray (0 : Coord K 2) (pt2 a b) := by
  have hE : pt2 (1 : K) 0 ≠ 0 := fun h => one_ne_zero (congrArg xc h)
  have hC : pt2 a b ≠ 0 := by
    intro h
    have ha : a = 0 := congrArg xc h
    have hb : b = 0 := congrArg yc h
    rw [ha, hb] at hr; simp at hr; exact hr0.ne' hr
  obtain ⟨c, hc, rfl⟩ := (AffPt.mem_ray_iff hE).1 hX
  rw [AffPt.mem_ray_iff hC]
  refine ⟨c * r⁻¹, mul_pos hc (inv_pos.2 hr0), ?_⟩
  rw [sub_zero, add_zero, add_zero, sub_zero, rot_smul, (rot_E hr hr0).1, smul_smul]

/-- The rotation maps the half-ray `OE` **onto** the half-ray `OC`. -/
theorem rot_ray_surj {a b r : K} (hr : r ^ 2 = a ^ 2 + b ^ 2) (hr0 : 0 < r) {Y : Coord K 2}
    (hY : Y ∈ ray (0 : Coord K 2) (pt2 a b)) :
    ∃ X ∈ ray (0 : Coord K 2) (pt2 1 0), rot a b r X = Y := by
  have hE : pt2 (1 : K) 0 ≠ 0 := fun h => one_ne_zero (congrArg xc h)
  have hC : pt2 a b ≠ 0 := by
    intro h
    have ha : a = 0 := congrArg xc h
    have hb : b = 0 := congrArg yc h
    rw [ha, hb] at hr; simp at hr; exact hr0.ne' hr
  obtain ⟨c, hc, rfl⟩ := (AffPt.mem_ray_iff hC).1 hY
  refine ⟨(c * r) • pt2 1 0, (AffPt.mem_ray_iff hE).2 ⟨c * r, mul_pos hc hr0, by simp⟩, ?_⟩
  rw [rot_smul, (rot_E hr hr0).1, smul_smul, sub_zero, add_zero, mul_assoc,
    mul_inv_cancel₀ hr0.ne', mul_one]

end Coord

/-!
## [s9.sqrt] `√(a² + b²)` belongs to `Ω`

*(§ 9)*

> Since the number \[ \sqrt{a^2+b^2} = a \sqrt{ 1 + \left( \frac{b}{a} \right)^2 } \] belongs to the domain $\Omega$, …

**Lean reading.** The identity as printed is false for `a < 0` (the left side is positive, the right
side negative) and meaningless for `a = 0`; `sqrt_identity_as_printed_false` gives the
counterexample `a = -1`, `b = 0`. Corrected: `√(a² + b²) = |a| √(1 + (b/a)²)` for `a ≠ 0`
(`sqrt_sq_add_sq_eq`), and for `a = 0` it is `|b|`. The conclusion is true:
`Omega.sqrt_sq_add_sq_mem` (`√(a² + b²) ∈ Ω` for `a, b ∈ Ω`), so that the coefficients of the
rotation of unit `s9.rotation` lie in `Ω`. Conversely, Hilbert's fifth operation is exactly what
laying off segments requires: if IV 1 holds in the coordinate plane over an ordered field `K`, then
`K` is Pythagorean (`isPythagorean_of_axiomIV1`).

**Status.** proved (corrected)
-/

theorem sqrt_sq_add_sq_eq {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Real.sqrt (a ^ 2 + b ^ 2) = |a| * Real.sqrt (1 + (b / a) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a)]
  congr 1; field_simp

theorem sqrt_identity_as_printed_false :
    ¬∀ a b : ℝ, a ≠ 0 → Real.sqrt (a ^ 2 + b ^ 2) = a * Real.sqrt (1 + (b / a) ^ 2) := by
  intro h
  have := h (-1) 0 (by norm_num)
  norm_num at this

theorem Omega.abs_mem {a : ℝ} (ha : a ∈ Omega) : |a| ∈ Omega := by
  rcases abs_choice a with h | h <;> rw [h]
  · exact ha
  · exact Omega.neg_mem ha

theorem Omega.sqrt_sq_add_sq_mem {a b : ℝ} (ha : a ∈ Omega) (hb : b ∈ Omega) :
    Real.sqrt (a ^ 2 + b ^ 2) ∈ Omega := by
  by_cases h : a = 0
  · rw [h, zero_pow two_ne_zero, zero_add, Real.sqrt_sq_eq_abs]; exact Omega.abs_mem hb
  · rw [sqrt_sq_add_sq_eq h]
    exact Omega.mul_mem (Omega.abs_mem ha) (Omega.sqrt_mem (Omega.div_mem hb ha))

/-- If segments can be laid off (IV 1) in the coordinate plane over `K`, then `K` is Pythagorean. -/
theorem isPythagorean_of_axiomIV1 (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (h : AxiomIV1LayOff (Coord K 2)) : IsPythagorean K := by
  constructor
  intro x
  have hB : (0 : Coord K 2) ≠ Coord.pt2 1 x := fun e => one_ne_zero (congrArg Coord.xc e).symm
  have hE : (0 : Coord K 2) ≠ Coord.pt2 1 0 := fun e => one_ne_zero (congrArg Coord.xc e).symm
  obtain ⟨B', ⟨hray, hcong⟩, -⟩ := h 0 (Coord.pt2 1 x) 0 (Coord.pt2 1 0) hB hE
  obtain ⟨c, hc, rfl⟩ := (AffPt.mem_ray_iff hE.symm).1 hray
  refine ⟨c, hc.le, ?_⟩
  rw [Coord.segCong_iff, Coord.ip_two, Coord.ip_two] at hcong
  simp at hcong
  linear_combination -hcong

/-!
## [s9.congruence] The axioms of congruence hold

*(§ 9)*

> … it follows that, under the conventions which we have made, the axioms of congruence (group IV) are all fulfilled.

**Lean reading.** "The conventions which we have made" (congruence by the motions of analytic
geometry) are made precise as metric congruence: equal lengths for segments, equal cosines for
angles (`Coord.instHasSegCong`, `Coord.instHasAngCong`); translations and rotations preserve both
(units `s9.translation`, `s9.rotation`), and conversely the metric congruences are exactly
Hilbert's: two segments are congruent iff one is carried onto the other by a rotation about `O`
followed by a translation (`Coord.segCong_iff_exists_motion`, over any ordered field: this
rotation needs no square root), and two angles are congruent iff such a motion carries the vertex
to the vertex and the two sides onto the two sides, in one order or the other
(`Coord.angCong_iff_exists_motion`, over any Pythagorean ordered field; the rotation is
multiplication by `w ū / (|u| |w|)` in complex notation, and the case of opposite orientation is
handled by sending the first side onto the second). No reflections are needed, since an angle is
an unordered pair of half-rays.
`omega_planeCongruence`: all axioms IV 1–6 (with groups I,
II) hold in the coordinate plane over `Ω`. The proof is generic: IV 2, IV 3, IV 5, IV 6 and the
well-definedness of angle congruence hold over every ordered field; laying off (IV 1, IV 4) needs
a Pythagorean field (`planeCongruence_of_isPythagorean`).

**Status.** proved (reading)
-/

theorem omega_planeCongruence : PlaneCongruence (Coord OmegaField 2) (CoordLine OmegaField 2) :=
  inferInstance

theorem planeCongruence_of_isPythagorean (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [IsPythagorean K] : PlaneCongruence (Coord K 2) (CoordLine K 2) :=
  inferInstance

/-- **Congruent segments are exactly those related by Hilbert's motions** (a rotation `rot a b r`
about `O` followed by a translation), over any ordered field. -/
theorem Coord.segCong_iff_exists_motion {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {A B A' B' : Coord K 2} (h : A ≠ B) :
    SegCong A B A' B' ↔ ∃ a b r : K, 0 < r ∧ r ^ 2 = a ^ 2 + b ^ 2 ∧
      ∃ t : Coord K 2, Coord.rot a b r A + t = A' ∧ Coord.rot a b r B + t = B' := by
  constructor
  · intro hs
    rw [Coord.segCong_iff, Coord.ip_two, Coord.ip_two] at hs
    set u := B - A with hu
    set v := B' - A' with hv
    have hu0 : u ≠ 0 := sub_ne_zero.2 h.symm
    have hN : 0 < Coord.ip u u := Coord.ip_self_pos hu0
    rw [Coord.ip_two] at hN
    set N := Coord.xc u * Coord.xc u + Coord.yc u * Coord.yc u with hNdef
    refine ⟨(Coord.xc u * Coord.xc v + Coord.yc u * Coord.yc v) / N,
      (Coord.xc u * Coord.yc v - Coord.yc u * Coord.xc v) / N, 1, one_pos, ?_, ?_⟩
    · field_simp
      linear_combination (Coord.xc u * Coord.xc u + Coord.yc u * Coord.yc u) * hs
    · have hrot : Coord.rot ((Coord.xc u * Coord.xc v + Coord.yc u * Coord.yc v) / N)
          ((Coord.xc u * Coord.yc v - Coord.yc u * Coord.xc v) / N) 1 u = v := by
        apply Coord.ext2
        · simp only [Coord.rot, Coord.xc_pt2]; field_simp; ring
        · simp only [Coord.rot, Coord.yc_pt2]; field_simp; ring
      refine ⟨A' - Coord.rot _ _ 1 A, by abel, ?_⟩
      rw [show Coord.rot ((Coord.xc u * Coord.xc v + Coord.yc u * Coord.yc v) / N)
          ((Coord.xc u * Coord.yc v - Coord.yc u * Coord.xc v) / N) 1 B =
          Coord.rot ((Coord.xc u * Coord.xc v + Coord.yc u * Coord.yc v) / N)
          ((Coord.xc u * Coord.yc v - Coord.yc u * Coord.xc v) / N) 1 u +
          Coord.rot ((Coord.xc u * Coord.xc v + Coord.yc u * Coord.yc v) / N)
          ((Coord.xc u * Coord.yc v - Coord.yc u * Coord.xc v) / N) 1 A by
        rw [← Coord.rot_add, hu, sub_add_cancel], hrot, hv]
      abel
  · rintro ⟨a, b, r, hr0, hr, t, hA, hB⟩
    rw [Coord.segCong_iff, ← hA, ← hB, add_sub_add_right_eq_sub, ← Coord.rot_sub,
      Coord.ip_rot hr hr0]

namespace Coord

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The cross product `u × v = x_u y_v - y_u x_v` of two vectors of the plane. -/
def crossProd2 (u v : Coord K 2) : K := xc u * yc v - yc u * xc v

/-- An auxiliary sign lemma: from `sign p = sign p'`, `p² q'² = p'² q²` and `q q' > 0`,
`p q' = p' q`. -/
theorem mul_eq_mul_of_sign_of_sq {p p' q q' : K} (hs : SignType.sign p = SignType.sign p')
    (h2 : p ^ 2 * q' ^ 2 = p' ^ 2 * q ^ 2) (hq : 0 < q * q') : p * q' = p' * q := by
  have h3 : (p * q' - p' * q) * (p * q' + p' * q) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · linear_combination h
  · have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hqq : 0 < q ^ 2 := lt_of_le_of_ne (sq_nonneg q) (Ne.symm (pow_ne_zero 2 hq0))
    have e : p * (q * q') + p' * q ^ 2 = 0 := by linear_combination q * h
    rcases lt_trichotomy p 0 with hp | hp | hp
    · have hp' : p' < 0 := by
        rw [sign_neg hp] at hs; exact sign_eq_neg_one_iff.1 hs.symm
      nlinarith [mul_neg_of_neg_of_pos hp hq, mul_neg_of_neg_of_pos hp' hqq]
    · subst hp
      have hp' : p' = 0 := by rw [sign_zero] at hs; exact sign_eq_zero_iff.1 hs.symm
      subst hp'; ring
    · have hp' : 0 < p' := by
        rw [sign_pos hp] at hs; exact sign_eq_one_iff.1 hs.symm
      nlinarith [mul_pos hp hq, mul_pos hp' hqq]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Lagrange's identity in the plane: `|u|² |v|² = ⟪u, v⟫² + (u × v)²`. -/
theorem ip_mul_ip_two (u v : Coord K 2) :
    ip u u * ip v v = ip u v ^ 2 + crossProd2 u v ^ 2 := by
  rw [ip_two, ip_two, ip_two, crossProd2]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The rotation with `(a, b) = (⟪w, u⟫, u × w)` in coordinates (it multiplies by `w ū`, in the
language of complex numbers). -/
theorem rot_formula (u w v : Coord K 2) (N : K) :
    rot (ip w u) (crossProd2 u w) N v =
      N⁻¹ • pt2 (xc w * ip u v - yc w * crossProd2 u v)
        (yc w * ip u v + xc w * crossProd2 u v) := by
  apply ext2
  · simp only [rot, xc_pt2, xc_smul, ip_two, crossProd2]; ring
  · simp only [rot, yc_pt2, yc_smul, ip_two, crossProd2]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem inv_mul_eq_of_eq_mul {N X c Y : K} (h : X = c * Y) : N⁻¹ * X = N⁻¹ * c * Y := by
  rw [h]; ring

/-- The rotation `rot ⟪w, u⟫ (u × w) N`, `N = |u| |w|`, followed by a translation, carries `O` to
`O'`, `A` into the half-ray `O'P` (`w = P - O'`) and, if it turns `v = B - O` into a positive
multiple of `Q - O'`, `B` into the half-ray `O'Q`. -/
theorem exists_motion_aux [IsPythagorean K] {A O B O' P Q : Coord K 2} (hu0 : A - O ≠ 0)
    (hP : P ≠ O') (hQ : Q ≠ O') (hP0 : P - O' ≠ 0)
    (hrotv : ∀ N : K, 0 < N → ∃ c : K, 0 < c ∧
      rot (ip (P - O') (A - O)) (crossProd2 (A - O) (P - O')) N (B - O) = c • (Q - O')) :
    ∃ a b r : K, 0 < r ∧ r ^ 2 = a ^ 2 + b ^ 2 ∧ ∃ t : Coord K 2,
      rot a b r O + t = O' ∧ rot a b r A + t ∈ ray O' P ∧ rot a b r B + t ∈ ray O' Q := by
  have huu : 0 < ip (A - O) (A - O) := ip_self_pos hu0
  obtain ⟨N, hN0, hN⟩ := IsPythagorean.exists_sqrt_sq_add_sq (ip (P - O') (A - O))
    (crossProd2 (A - O) (P - O'))
  have hNsq : N ^ 2 = ip (A - O) (A - O) * ip (P - O') (P - O') := by
    rw [hN, ip_comm (P - O') (A - O), ip_mul_ip_two]
  have hN0' : 0 < N := by
    rcases hN0.lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have := mul_pos huu (ip_self_pos hP0)
      rw [← hNsq, ← h0] at this; simp at this
  obtain ⟨c, hc, hrot⟩ := hrotv N hN0'
  refine ⟨_, _, N, hN0', hN, O' - rot (ip (P - O') (A - O)) (crossProd2 (A - O) (P - O')) N O,
    by abel, ?_, ?_⟩
  · rw [AffPt.mem_ray_iff hP]
    refine ⟨N⁻¹ * ip (A - O) (A - O), mul_pos (inv_pos.2 hN0') huu, ?_⟩
    have e : rot (ip (P - O') (A - O)) (crossProd2 (A - O) (P - O')) N (A - O) =
        (N⁻¹ * ip (A - O) (A - O)) • (P - O') := by
      rw [rot_formula]
      apply ext2
      · simp only [xc_pt2, xc_smul]; apply inv_mul_eq_of_eq_mul
        simp only [ip_two, crossProd2]; ring
      · simp only [yc_pt2, yc_smul]; apply inv_mul_eq_of_eq_mul
        simp only [ip_two, crossProd2]; ring
    rw [← e, rot_sub]; abel
  · rw [AffPt.mem_ray_iff hQ]
    refine ⟨c, hc, ?_⟩
    rw [← hrot, rot_sub]; abel

/-- **Congruent angles are exactly those related by Hilbert's motions** (§ 9): over a Pythagorean
ordered field, `∠AOB ≡ ∠A'O'B'` iff a rotation `rot a b r` about the origin followed by a
translation carries `O` to `O'` and the sides of `∠AOB` onto the sides of `∠A'O'B'` (in one order
or the other: an angle is a pair of half-rays). -/
theorem angCong_iff_exists_motion [IsPythagorean K] {A O B A' O' B' : Coord K 2}
    (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B') :
    AngCong A O B A' O' B' ↔ ∃ a b r : K, 0 < r ∧ r ^ 2 = a ^ 2 + b ^ 2 ∧ ∃ t : Coord K 2,
      rot a b r O + t = O' ∧
      ((rot a b r A + t ∈ ray O' A' ∧ rot a b r B + t ∈ ray O' B') ∨
        (rot a b r A + t ∈ ray O' B' ∧ rot a b r B + t ∈ ray O' A')) := by
  obtain ⟨hA'O', -, hO'B'⟩ := AffPt.not_collinear_of_eq h'
  have hB'O' : B' ≠ O' := hO'B'.symm
  obtain ⟨hu0, hv0⟩ := sub_ne_zero_of_not_collinear h
  obtain ⟨hu0', hv0'⟩ := sub_ne_zero_of_not_collinear h'
  have hcs := cauchySchwarz_pos h
  have hcs' := cauchySchwarz_pos h'
  rw [angCong_iff]
  constructor
  · intro hc
    have hL := ip_mul_ip_two (A - O) (B - O)
    have hL' := ip_mul_ip_two (A' - O') (B' - O')
    have hq0 : 0 < crossProd2 (A - O) (B - O) ^ 2 := by linarith
    have hq0' : 0 < crossProd2 (A' - O') (B' - O') ^ 2 := by linarith
    have hqne : crossProd2 (A - O) (B - O) ≠ 0 := fun e => by rw [e] at hq0; simp at hq0
    have hqne' : crossProd2 (A' - O') (B' - O') ≠ 0 := fun e => by rw [e] at hq0'; simp at hq0'
    have h2 : ip (A - O) (B - O) ^ 2 * crossProd2 (A' - O') (B' - O') ^ 2 =
        ip (A' - O') (B' - O') ^ 2 * crossProd2 (A - O) (B - O) ^ 2 := by
      have := hc.2; rw [hL, hL'] at this; linear_combination this
    have hdiv : ∀ x y : K, y ≠ 0 → 0 < x * y → 0 < x / y := fun x y hy hxy => by
      have : x / y = (x * y) / (y * y) := by field_simp
      rw [this]; exact div_pos hxy (mul_self_pos.2 hy)
    rcases lt_or_gt_of_ne (mul_ne_zero hqne hqne') with hqq | hqq
    · -- opposite orientations: the motion carries `OA` to `O'B'` and `OB` to `O'A'`
      have hpq : ip (A - O) (B - O) * crossProd2 (A' - O') (B' - O') =
          -(ip (A' - O') (B' - O') * crossProd2 (A - O) (B - O)) := by
        have := mul_eq_mul_of_sign_of_sq (q := crossProd2 (A - O) (B - O))
          (q' := -crossProd2 (A' - O') (B' - O')) hc.1 (by linear_combination h2)
          (by rw [mul_neg]; exact neg_pos.2 hqq)
        linear_combination -this
      have hμ : 0 < -crossProd2 (A - O) (B - O) / crossProd2 (A' - O') (B' - O') :=
        hdiv _ _ hqne' (by rw [neg_mul]; exact neg_pos.2 hqq)
      obtain ⟨a, b, r, hr0, hr, t, hO, hA, hB⟩ := exists_motion_aux (B := B) hu0 hB'O' hA'O' hv0'
        (fun N hN0 => ⟨N⁻¹ * (-crossProd2 (A - O) (B - O) / crossProd2 (A' - O') (B' - O') *
            ip (B' - O') (B' - O')),
          mul_pos (inv_pos.2 hN0) (mul_pos hμ (ip_self_pos hv0')), by
          rw [rot_formula]
          apply ext2
          · simp only [xc_pt2, xc_smul]; apply inv_mul_eq_of_eq_mul
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hqne']
            simp only [ip_two, crossProd2] at hpq ⊢
            linear_combination xc (B' - O') * hpq
          · simp only [yc_pt2, yc_smul]; apply inv_mul_eq_of_eq_mul
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hqne']
            simp only [ip_two, crossProd2] at hpq ⊢
            linear_combination yc (B' - O') * hpq⟩)
      exact ⟨a, b, r, hr0, hr, t, hO, Or.inr ⟨hA, hB⟩⟩
    · -- same orientation: the motion carries `OA` to `O'A'` and `OB` to `O'B'`
      have hpq : ip (A - O) (B - O) * crossProd2 (A' - O') (B' - O') =
          ip (A' - O') (B' - O') * crossProd2 (A - O) (B - O) := mul_eq_mul_of_sign_of_sq hc.1 h2 hqq
      have hμ : 0 < crossProd2 (A - O) (B - O) / crossProd2 (A' - O') (B' - O') :=
        hdiv _ _ hqne' hqq
      obtain ⟨a, b, r, hr0, hr, t, hO, hA, hB⟩ := exists_motion_aux (B := B) hu0 hA'O' hB'O' hu0'
        (fun N hN0 => ⟨N⁻¹ * (crossProd2 (A - O) (B - O) / crossProd2 (A' - O') (B' - O') *
            ip (A' - O') (A' - O')),
          mul_pos (inv_pos.2 hN0) (mul_pos hμ (ip_self_pos hu0')), by
          rw [rot_formula]
          apply ext2
          · simp only [xc_pt2, xc_smul]; apply inv_mul_eq_of_eq_mul
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hqne']
            simp only [ip_two, crossProd2] at hpq ⊢
            linear_combination xc (A' - O') * hpq
          · simp only [yc_pt2, yc_smul]; apply inv_mul_eq_of_eq_mul
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hqne']
            simp only [ip_two, crossProd2] at hpq ⊢
            linear_combination yc (A' - O') * hpq⟩)
      exact ⟨a, b, r, hr0, hr, t, hO, Or.inl ⟨hA, hB⟩⟩
  · rintro ⟨a, b, r, hr0, hr, t, hO, hcase⟩
    have hmA : rot a b r A + t - O' = rot a b r (A - O) := by rw [← hO, rot_sub]; abel
    have hmB : rot a b r B + t - O' = rot a b r (B - O) := by rw [← hO, rot_sub]; abel
    have hself : AngleEq (A - O) (B - O) (rot a b r (A - O)) (rot a b r (B - O)) :=
      angleEq_of_ip_eq (by rw [ip_rot hr hr0]) (by rw [ip_rot hr hr0]) (by rw [ip_rot hr hr0])
    rcases hcase with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · obtain ⟨c, hc, hcA⟩ := (AffPt.mem_ray_iff hA'O').1 hA
      obtain ⟨d, hd, hdB⟩ := (AffPt.mem_ray_iff hB'O').1 hB
      have e1 : rot a b r (A - O) = c • (A' - O') := by rw [← hmA, hcA]; abel
      have e2 : rot a b r (B - O) = d • (B' - O') := by rw [← hmB, hdB]; abel
      rw [e1, e2] at hself
      exact ((angleEq_smul_left hc hd).1 hself.symm).symm
    · obtain ⟨c, hc, hcA⟩ := (AffPt.mem_ray_iff hB'O').1 hA
      obtain ⟨d, hd, hdB⟩ := (AffPt.mem_ray_iff hA'O').1 hB
      have e1 : rot a b r (A - O) = c • (B' - O') := by rw [← hmA, hcA]; abel
      have e2 : rot a b r (B - O) = d • (A' - O') := by rw [← hmB, hdB]; abel
      rw [e1, e2] at hself
      have := (angleEq_smul_left hc hd).1 hself.symm
      exact (angleEq_comm_left.1 this).symm

end Coord

/-!
## [s9.archimedes] Archimedes's axiom holds

*(§ 9)*

> The same is true of the axiom of Archimedes.

**Lean reading.** `Ω` is archimedean, being a subfield of `ℝ` (`OmegaField.instArchimedean`), and
over every archimedean ordered field Axiom V holds in the coordinate geometry
(`Coord.axiomV`: the points `A₀, A₁, …` with equal consecutive segments are
`A₀ + k (A₁ - A₀)`, and the archimedean property of the field gives `n` with `B` between `A₀` and
`Aₙ`). `omega_archimedes` is the case of `Ω`.

**Status.** proved
-/

instance OmegaField.instArchimedean : Archimedean OmegaField := by
  rw [archimedean_iff_nat_lt]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (x : ℝ)
  exact ⟨n, show (x : ℝ) < ((n : OmegaField) : ℝ) by simpa using hn⟩

theorem omega_archimedes : Archimedes (Coord OmegaField 2) (CoordLine OmegaField 2) :=
  inferInstance

/-!
## [s9.relative_consistency] Every contradiction would appear in the arithmetic of `Ω`

*(§ 9)*

> From these considerations, it follows that every contradiction resulting from our system of axioms must also appear in the arithmetic related to the domain $\Omega$.

**Lean reading.** `omega_planeGeometry`: the coordinate plane over `Ω`, a structure built from the
arithmetic of `Ω` alone, satisfies all axioms I–V of plane geometry. Hence a contradiction derived
from the axioms would be a contradiction in this structure, i.e. in the arithmetic of `Ω`; in Lean
the conclusion is the consistency statement `axiomsConsistentPlane : AxiomsConsistentPlane` (Lean's
own consistency, which includes that of `ℝ` and hence of `Ω`, is the background). The relative
character ("must also appear in the arithmetic") is the fact that the model is defined from `Ω` by
explicit definitions.

**Status.** proved (reading)
-/

theorem omega_planeGeometry : PlaneGeometry (Coord OmegaField 2) (CoordLine OmegaField 2) :=
  inferInstance

theorem axiomsConsistentPlane : AxiomsConsistentPlane :=
  axiomsConsistentPlane_of_model (Coord OmegaField 2) (CoordLine OmegaField 2) omega_planeGeometry

/-!
## [s9.space] The geometry of space

*(§ 9)*

> The corresponding considerations for the geometry of space present no difficulties.

**Lean reading.** Points `(x, y, z)` of `Ω³`, lines and planes the affine subspaces of dimensions 1
and 2 (Hilbert's planes `ux + vy + wz + r = 0` of § 12, lines as intersections of two planes),
betweenness and congruence as in the plane. `omega_spaceGeometry`: all axioms I–V of space
geometry hold; the space versions of II 5, III and IV 4 are proved in each plane by the same plane
arguments (`AffPt.pasch_in`, `AffPt.exists_unique_parallel_in`, `Coord.layOff_angle_in`), and
I 3–7 by dimension counting. Hence `axiomsConsistent : AxiomsConsistent`, the claim of unit
`s9.consistency`.

**Status.** proved
-/

theorem omega_spaceGeometry :
    SpaceGeometry (Coord OmegaField 3) (CoordLine OmegaField 3) (CoordPlane OmegaField 3) :=
  inferInstance

/-- Over any linearly ordered division ring (commutative or not), groups I, II, III of space
geometry hold in `K³`. -/
theorem spaceOrder_spaceParallels_coord (K : Type*) [DivisionRing K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    SpaceOrder (Coord K 3) (CoordLine K 3) (CoordPlane K 3) ∧
      SpaceParallels (Coord K 3) (CoordLine K 3) (CoordPlane K 3) :=
  ⟨inferInstance, inferInstance⟩

/-- Over any Pythagorean ordered field, groups I–IV of space geometry hold in `K³`. -/
theorem spaceCongruence_of_isPythagorean (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [IsPythagorean K] :
    SpaceCongruence (Coord K 3) (CoordLine K 3) (CoordPlane K 3) ∧
      SpaceParallels (Coord K 3) (CoordLine K 3) (CoordPlane K 3) :=
  ⟨inferInstance, inferInstance⟩

theorem axiomsConsistent : AxiomsConsistent :=
  axiomsConsistent_of_model (Coord OmegaField 3) (CoordLine OmegaField 3) (CoordPlane OmegaField 3)
    omega_spaceGeometry

/-- The model is not degenerate: it has planes (and, by I 7, four points not in a plane), unlike
the trivial structures that the literal reading of I 7 admits. -/
theorem omega_space_has_plane :
    ∃ (α : CoordPlane OmegaField 3) (A B C : Coord OmegaField 3),
      A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ¬Collinear A B C := by
  have hli : LinearIndependent OmegaField
      ![(AffPt.ofV (Pi.single 0 1) : Coord OmegaField 3), AffPt.ofV (Pi.single 1 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun (congrArg AffPt.toV h) 0
    have h1 := congrFun (congrArg AffPt.toV h) 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  have hnc := AffPt.not_collinear_of_linearIndependent (O := 0) hli
  obtain ⟨α, h1, h2, h3⟩ := exists_plane (Plane := CoordPlane OmegaField 3) hnc
  exact ⟨α, _, _, _, h1, h2, h3, hnc⟩

/-!
## [s9.reals] The geometry over the real numbers

*(§ 9)*

> If, in the preceding development, we had selected the domain of all real numbers instead of the domain $\Omega$, we should have obtained likewise a geometry in which all of the axioms of groups I—V are valid.

**Lean reading.** `real_planeGeometry`, `real_spaceGeometry`: the coordinate plane `ℝ²` and space
`ℝ³` satisfy all axioms I–V (`ℝ` is a Pythagorean archimedean ordered field). The Axiom of
Completeness, which Hilbert does not claim here, is not addressed.

**Status.** proved
-/

theorem real_planeGeometry : PlaneGeometry (Coord ℝ 2) (CoordLine ℝ 2) := inferInstance

theorem real_spaceGeometry : SpaceGeometry (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) :=
  inferInstance

/-!
## [s9.countable] `Ω` is enumerable

*(§ 9)*

> For the purposes of our demonstration, however, it was sufficient to take the domain $\Omega$, containing on an enumerable set of elements.

**Lean reading.** "Containing on" is a misprint for "containing only". `Omega.countable`: `Ω` is
countable, being the set of values of the countably many expressions built from `1` by the five
operations (`OmegaExpr`, `IsOmega.exists_expr`); hence the Ω-geometry has countably many points
(`countable_omega_points`). Since `ℝ` is uncountable, `Ω ≠ ℝ` (`Omega_ne_top`): the countable model
is a genuinely different model of the axioms I–V.

**Status.** proved
-/

/-- Expressions built from `1` by the five operations of Hilbert. -/
inductive OmegaExpr
  | one
  | add (a b : OmegaExpr)
  | sub (a b : OmegaExpr)
  | mul (a b : OmegaExpr)
  | div (a b : OmegaExpr)
  | sqrt (a : OmegaExpr)
  deriving Countable

/-- The value of an expression. -/
noncomputable def OmegaExpr.eval : OmegaExpr → ℝ
  | one => 1
  | add a b => a.eval + b.eval
  | sub a b => a.eval - b.eval
  | mul a b => a.eval * b.eval
  | div a b => a.eval / b.eval
  | sqrt a => Real.sqrt (1 + a.eval ^ 2)

theorem IsOmega.exists_expr {x : ℝ} (h : IsOmega x) : ∃ e : OmegaExpr, e.eval = x := by
  induction h with
  | one => exact ⟨.one, rfl⟩
  | add _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.add a b, rfl⟩
  | sub _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.sub a b, rfl⟩
  | mul _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.mul a b, rfl⟩
  | div _ _ _ ha hb =>
    obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.div a b, rfl⟩
  | sqrt _ hw => obtain ⟨a, rfl⟩ := hw; exact ⟨.sqrt a, rfl⟩

theorem Omega.countable : (Omega : Set ℝ).Countable :=
  (Set.countable_range OmegaExpr.eval).mono fun _ hx => hx.exists_expr

instance OmegaField.instCountable : Countable OmegaField := Omega.countable.to_subtype

theorem countable_omega_points : Countable (Coord OmegaField 3) :=
  inferInstanceAs (Countable (Fin 3 → OmegaField))

theorem Omega_ne_top : Omega ≠ ⊤ := by
  intro h
  apply Cardinal.not_countable_real
  have := Omega.countable
  rw [h] at this
  simpa using this

/-! ## § 13. Complex number-systems

A "system of things" with Hilbert's operations is a type `α` with `+`, `*`, `0`, `1` and the
relation `<` (`a > b` is `b < a`, as in Hilbert's "we express this relation by writing `a > b` and
`b < a`"). Each law is a `Prop` about such a type. -/

section NumberSystems

variable (α : Type*) [Add α] [Mul α] [Zero α] [One α] [LT α]

/-!
## [s13.law1] Law 1: addition

*(§ 13)*

> 1. From the number $a$ and the number $b$, there is obtained by “addition” a definite number $c$, which we express by writing \[ a+b= c or c=a+b. \]

**Lean reading.** `Law1`: for all `a`, `b` there is exactly one `c` with `c = a + b`. Since the
addition of a Lean type is a function `α → α → α`, the law holds for every system (`law1_holds`):
"a definite number" is built into the encoding of the operation.

**Status.** definition
-/

/-- **Law 1.** -/
def Law1 : Prop := ∀ a b : α, ∃! c : α, c = a + b

omit [Mul α] [Zero α] [One α] [LT α] in
theorem law1_holds : Law1 α := fun a b => ⟨a + b, rfl, fun _ h => h⟩

/-!
## [s13.law2] Law 2: zero

*(§ 13)*

> 2. There exists a definite number, which we call $0$, such that, for every number $a$, we have \[ a+0= a and 0 + a = a. \]

**Lean reading.** `Law2`: the number `0` of the system satisfies `a + 0 = a` and `0 + a = a`. The
existential "there exists a number which we call `0`" is the choice of the constant `0`.

**Status.** definition
-/

/-- **Law 2.** -/
def Law2 : Prop := ∀ a : α, a + 0 = a ∧ 0 + a = a

/-!
## [s13.law3] Law 3: subtraction

*(§ 13)*

> 3. If $a$ and $b$ are two given numbers, there exists one and only one number $x$, and also one and only one number $y$, such that we have respectively \[ a+x = b, y+a=b. \]

**Lean reading.** `Law3`: for all `a`, `b`, there is a unique `x` with `a + x = b` and a unique `y`
with `y + a = b`.

**Status.** definition
-/

/-- **Law 3.** -/
def Law3 : Prop := ∀ a b : α, (∃! x : α, a + x = b) ∧ ∃! y : α, y + a = b

/-!
## [s13.law4] Law 4: multiplication

*(§ 13)*

> 4. From the number $a$ and the number $b$, there may be obtained in another way, namely, by “multiplication,” a definite number $c$, which we express by writing \[ ab = c or c = ab. \]

**Lean reading.** As law 1, for multiplication (`law4_holds`).

**Status.** definition
-/

/-- **Law 4.** -/
def Law4 : Prop := ∀ a b : α, ∃! c : α, c = a * b

omit [Add α] [Zero α] [One α] [LT α] in
theorem law4_holds : Law4 α := fun a b => ⟨a * b, rfl, fun _ h => h⟩

/-!
## [s13.law5] Law 5: one

*(§ 13)*

> 5. There exists a definite number, called $1$, such that, for every number $a$, we have \[ a\cdot 1 = a and 1 \cdot a = a. \]

**Lean reading.** `Law5`: `a * 1 = a` and `1 * a = a` for the constant `1`.

**Status.** definition
-/

/-- **Law 5.** -/
def Law5 : Prop := ∀ a : α, a * 1 = a ∧ 1 * a = a

/-!
## [s13.law6] Law 6: division

*(§ 13)*

> 6. If $a$ and $b$ are any arbitrarily given numbers, where $a$ is different from $0$, then there exists one and only one number $x$ and also one and only one number $y$ such that we have respectively \[ ax = b,\,ya=b. \]

**Lean reading.** `Law6`: for `a ≠ 0` and any `b` there is a unique `x` with `a x = b` and a unique
`y` with `y a = b`.

**Status.** definition
-/

/-- **Law 6.** -/
def Law6 : Prop := ∀ a b : α, a ≠ 0 → (∃! x : α, a * x = b) ∧ ∃! y : α, y * a = b

/-!
## [s13.law7] Law 7: associativity of addition

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … a + (b + c) & = & (a + b) + c

**Lean reading.** `Law7`: `a + (b + c) = (a + b) + c`.

**Status.** definition
-/

/-- **Law 7.** -/
def Law7 : Prop := ∀ a b c : α, a + (b + c) = (a + b) + c

/-!
## [s13.law8] Law 8: commutativity of addition

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … a+b & = & b+a

**Lean reading.** `Law8`: `a + b = b + a`.

**Status.** definition
-/

/-- **Law 8.** -/
def Law8 : Prop := ∀ a b : α, a + b = b + a

/-!
## [s13.law9] Law 9: associativity of multiplication

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … a(bc) & = & (ab)c

**Lean reading.** `Law9`: `a (b c) = (a b) c`.

**Status.** definition
-/

/-- **Law 9.** -/
def Law9 : Prop := ∀ a b c : α, a * (b * c) = (a * b) * c

/-!
## [s13.law10] Law 10: left distributivity

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … a(b + c) & = & ab+ac

**Lean reading.** `Law10`: `a (b + c) = a b + a c`.

**Status.** definition
-/

/-- **Law 10.** -/
def Law10 : Prop := ∀ a b c : α, a * (b + c) = a * b + a * c

/-!
## [s13.law11] Law 11: right distributivity

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … (a+b)c & = & ac+bc

**Lean reading.** `Law11`: `(a + b) c = a c + b c`.

**Status.** definition
-/

/-- **Law 11.** -/
def Law11 : Prop := ∀ a b c : α, (a + b) * c = a * c + b * c

/-!
## [s13.law12] Law 12: commutativity of multiplication

*(§ 13)*

> If $a$, $b$, $c$ are arbitrary numbers, the following laws of operation always hold:\\ … ab & = & ba.

**Lean reading.** `Law12`: `a b = b a`.

**Status.** definition
-/

/-- **Law 12.** -/
def Law12 : Prop := ∀ a b : α, a * b = b * a

/-!
## [s13.law13] Law 13: comparability

*(§ 13)*

> 13. If $a$, $b$ are any two distinct numbers, one of these, say $a$, is always greater ($>$) than the other. The other number is said to be the smaller of the two. We express this relation by writing \[ a > b and b < a. \]

**Lean reading.** `Law13` (literal): for `a ≠ b`, `a > b` or `b > a`. Taken literally (as
translated: "one of these, say `a`"), laws 13–16 do not exclude that `a > b` and `b > a` hold at
once (then `a > a` by 14): the relation "always true" satisfies them (`totalLT_laws` in unit
`s13.number_system`). What Hilbert means (the original has "a definite one of them", and "the
other number is said to be the smaller", i.e. it is not also the greater) is `Law13Asymm`:
moreover `a > b` excludes `b > a`. `Law13Asymm` also contains irreflexivity (`a = b`), which the
text never states for equal numbers but which "greater" tacitly carries; Hilbert's full law 13 is
read as `Law13 ∧ Law13Asymm`, and every positive result below (`real_laws`, `omega_laws`,
`omegaT_laws`) is proved for this full reading. The correspondence with ordered fields needs it.

**Status.** definition
-/

/-- **Law 13** (literal). -/
def Law13 : Prop := ∀ a b : α, a ≠ b → a > b ∨ b > a

/-- The tacit part of law 13: of `a > b` and `b > a` at most one holds. -/
def Law13Asymm : Prop := ∀ a b : α, a > b → ¬b > a

/-!
## [s13.law14] Law 14: transitivity

*(§ 13)*

> 14. If $a > b$ and $b > c$, then is also $a > c$.

**Lean reading.** `Law14`.

**Status.** definition
-/

/-- **Law 14.** -/
def Law14 : Prop := ∀ a b c : α, a > b → b > c → a > c

/-!
## [s13.law15] Law 15: monotonicity of addition

*(§ 13)*

> 15. If $a > b$, then is also $a+c > b+ c$ and $c+a > c+b$.

**Lean reading.** `Law15`.

**Status.** definition
-/

/-- **Law 15.** -/
def Law15 : Prop := ∀ a b c : α, a > b → a + c > b + c ∧ c + a > c + b

/-!
## [s13.law16] Law 16: monotonicity of multiplication

*(§ 13)*

> 16. If $a > b$ and $c>0$, then is also $ac>bc$ and $ca > cb$.

**Lean reading.** `Law16`.

**Status.** definition
-/

/-- **Law 16.** -/
def Law16 : Prop := ∀ a b c : α, a > b → c > 0 → a * c > b * c ∧ c * a > c * b

/-!
## [s13.law17] Law 17: Archimedes

*(§ 13)*

> 17. If $a$, $b$ are any two arbitrary numbers, such that $a > 0$ and $b > 0$, it is always possible to add $a$ to itself a sufficient number of times so that the resulting sum shall have the property that \[ a+a+a+ \cdots + a > b. \]

**Lean reading.** `repeatAdd a n` is the sum `a + a + ⋯ + a` of `n + 1` terms (left-nested, as
Hilbert writes it); `Law17`: for `a > 0`, `b > 0` some such sum exceeds `b`.

**Status.** definition
-/

/-- The sum `a + a + ⋯ + a` with `n + 1` terms. -/
def repeatAdd (a : α) : ℕ → α
  | 0 => a
  | n + 1 => repeatAdd a n + a

/-- **Law 17** (Archimedes). -/
def Law17 : Prop := ∀ a b : α, a > 0 → b > 0 → ∃ n : ℕ, repeatAdd α a n > b

/-- Laws 1–12 (the "theorems of connection"). -/
structure FieldLaws : Prop where
  law1 : Law1 α
  law2 : Law2 α
  law3 : Law3 α
  law4 : Law4 α
  law5 : Law5 α
  law6 : Law6 α
  law7 : Law7 α
  law8 : Law8 α
  law9 : Law9 α
  law10 : Law10 α
  law11 : Law11 α
  law12 : Law12 α

/-- Laws 13–16 (the "theorems of order"). -/
structure OrderLaws : Prop where
  law13 : Law13 α
  law14 : Law14 α
  law15 : Law15 α
  law16 : Law16 α

/-- Laws 1–16. -/
structure Laws1to16 : Prop extends FieldLaws α, OrderLaws α

/-- Laws 1–17: all the properties Hilbert lists for the real numbers. -/
structure Laws1to17 : Prop extends Laws1to16 α where
  law17 : Law17 α

end NumberSystems

/-!
## [s13.reals] The real numbers satisfy laws 1–17

*(§ 13)*

> The real numbers form, in their totality, a system of things having the following properties:

**Lean reading.** `real_laws`: `ℝ` satisfies laws 1–17, and the tacit asymmetry of law 13. The proof
is the general `laws_of_orderedField` (every linearly ordered field satisfies 1–16 and the
asymmetry) with `law17_iff_archimedean` (law 17 is mathlib's `Archimedean`). The unit is placed
after the laws, whose definitions it uses. The same holds for Hilbert's `Ω` (`omega_laws`).

**Status.** proved
-/

section OrderedFields

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem repeatAdd_eq (a : α) (n : ℕ) : repeatAdd α a n = (n + 1 : ℕ) • a := by
  induction n with
  | zero => simp [repeatAdd]
  | succ n ih => rw [repeatAdd, ih]; exact (succ_nsmul a (n + 1)).symm

/-- Every linearly ordered field satisfies laws 1–16 and the asymmetry of law 13. -/
theorem laws_of_orderedField : Laws1to16 α ∧ Law13Asymm α := by
  refine ⟨⟨⟨law1_holds α, fun a => ⟨add_zero a, zero_add a⟩, ?_, law4_holds α,
    fun a => ⟨mul_one a, one_mul a⟩, ?_, fun a b c => (add_assoc a b c).symm, add_comm,
    fun a b c => (mul_assoc a b c).symm, mul_add, add_mul, mul_comm⟩, ⟨?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · intro a b
    refine ⟨⟨b - a, by abel, fun x hx => ?_⟩, ⟨b - a, by abel, fun y hy => ?_⟩⟩
    · rw [← hx]; abel
    · rw [← hy]; abel
  · intro a b ha
    refine ⟨⟨a⁻¹ * b, by field_simp, fun x hx => ?_⟩, ⟨b * a⁻¹, by field_simp, fun y hy => ?_⟩⟩
    · rw [← hx]; field_simp
    · rw [← hy]; field_simp
  · intro a b h; exact (lt_or_gt_of_ne h).symm
  · intro a b c h1 h2; exact h2.trans h1
  · intro a b c h; exact ⟨by simpa using h, by simpa using h⟩
  · intro a b c h hc; exact ⟨mul_lt_mul_of_pos_right h hc, mul_lt_mul_of_pos_left h hc⟩
  · intro a b h h'; exact lt_asymm h h'

/-- **Law 17 is the archimedean property** of an ordered field. -/
theorem law17_iff_archimedean : Law17 α ↔ Archimedean α := by
  constructor
  · intro h
    refine ⟨fun x y hy => ?_⟩
    rcases le_or_gt x 0 with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · obtain ⟨n, hn⟩ := h y x hy hx
      rw [repeatAdd_eq] at hn
      exact ⟨n + 1, hn.le⟩
  · intro h a b ha _
    obtain ⟨n, hn⟩ := Archimedean.arch b ha
    refine ⟨n, ?_⟩
    rw [repeatAdd_eq, succ_nsmul]
    exact lt_of_le_of_lt hn (lt_add_of_pos_right _ ha)

theorem laws1to17_of_archimedean [Archimedean α] : Laws1to17 α :=
  ⟨laws_of_orderedField.1, law17_iff_archimedean.2 inferInstance⟩

end OrderedFields

theorem real_laws : Laws1to17 ℝ ∧ Law13Asymm ℝ :=
  ⟨laws1to17_of_archimedean, laws_of_orderedField.2⟩

theorem omega_laws : Laws1to17 OmegaField ∧ Law13Asymm OmegaField :=
  ⟨laws1to17_of_archimedean, laws_of_orderedField.2⟩

/-!
## [s13.number_system] Number systems; archimedean and non-archimedean

*(§ 13)*

> A system of things possessing only a portion of the above properties (1–17) is called a *complex number system*, or simply a *number system*. A number system is called *archimedean*, or *non-archimedean*, according as it does, or does not, satisfy condition (17).

**Lean reading.** A number system is a type with `+`, `*`, `0`, `1`, `<` satisfying some of the laws;
"archimedean" is `Law17`. What the full list corresponds to in mathlib is proved in both
directions: a linearly ordered field (`Field`, `LinearOrder`, `IsStrictOrderedRing`) satisfies laws
1–16 (`laws_of_orderedField`) and law 17 iff it is `Archimedean` (`law17_iff_archimedean`);
conversely, laws 1–12 give a `Field` structure with the same operations (`FieldLaws.toField`), and
laws 13–16 a `LinearOrder` with the same `<` (`OrderLaws.toLinearOrder`), which together form a
strict ordered field (`laws_isStrictOrderedRing`), archimedean under law 17 (`laws_archimedean`).
Two tacit hypotheses are needed and shown necessary: (1) the asymmetry of law 13 (`Law13Asymm`):
the rationals with the relation `<` replaced by "always" satisfy all of 1–17 as printed
(`totalLT_laws`) but are not ordered; (2) the existence of two distinct numbers: the one-element
system satisfies all of 1–17 (`punit_laws`) but is not a field (`0 = 1`).

**Status.** definition
-/

section Converse

variable {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α]

omit [LT α] in
theorem FieldLaws.zero_mul (h : FieldLaws α) (a : α) : 0 * a = 0 := by
  have e : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← h.law11, (h.law2 0).1, (h.law2 _).1]
  exact (h.law3 (0 * a) (0 * a + 0)).1.unique e rfl

omit [LT α] in
theorem FieldLaws.mul_zero (h : FieldLaws α) (a : α) : a * 0 = 0 := by
  rw [h.law12]; exact h.zero_mul a

open Classical in
/-- **Laws 1–12 give a field** (with the given operations), provided `0 ≠ 1`. -/
@[instance_reducible] noncomputable def FieldLaws.toField (h : FieldLaws α) (h01 : (0 : α) ≠ 1) : Field α :=
  let neg : α → α := fun a => Classical.choose (h.law3 a 0).1.exists
  let inv : α → α := fun a => if ha : a = 0 then 0 else Classical.choose (h.law6 a 1 ha).1.exists
  { add := (· + ·)
    add_assoc := fun a b c => (h.law7 a b c).symm
    zero := 0
    zero_add := fun a => (h.law2 a).2
    add_zero := fun a => (h.law2 a).1
    nsmul := nsmulRec
    neg := neg
    neg_add_cancel := fun a => by
      show neg a + a = 0
      rw [h.law8]; exact Classical.choose_spec (h.law3 a 0).1.exists
    add_comm := h.law8
    mul := (· * ·)
    left_distrib := h.law10
    right_distrib := h.law11
    zero_mul := h.zero_mul
    mul_zero := h.mul_zero
    mul_assoc := fun a b c => (h.law9 a b c).symm
    one := 1
    one_mul := fun a => (h.law5 a).2
    mul_one := fun a => (h.law5 a).1
    mul_comm := h.law12
    inv := inv
    exists_pair_ne := ⟨0, 1, h01⟩
    mul_inv_cancel := fun a ha => by
      show a * inv a = 1
      have e : inv a = Classical.choose (h.law6 a 1 ha).1.exists := by simp [inv, ha]
      rw [e]; exact Classical.choose_spec (h.law6 a 1 ha).1.exists
    inv_zero := by simp [inv]
    zsmul := @zsmulRec α _ _ ⟨neg⟩ nsmulRec
    nnqsmul := _
    qsmul := _ }

/-- **Laws 13–16 with the asymmetry of law 13 give a linear order** (with the given `<`). -/
@[instance_reducible] noncomputable def OrderLaws.toLinearOrder (h : OrderLaws α) (ha : Law13Asymm α) : LinearOrder α where
  le a b := a < b ∨ a = b
  lt := (· < ·)
  le_refl a := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with hab | rfl
    · rcases hbc with hbc | rfl
      · exact Or.inl (h.law14 c b a hbc hab)
      · exact Or.inl hab
    · exact hbc
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      refine ⟨Or.inl hab, ?_⟩
      rintro (hba | rfl)
      · exact ha b a hab hba
      · exact ha _ _ hab hab
    · rintro ⟨hab | rfl, hba⟩
      · exact hab
      · exact absurd (Or.inr rfl) hba
  le_antisymm a b hab hba := by
    rcases hab with hab | rfl
    · rcases hba with hba | rfl
      · exact absurd hba (ha b a hab)
      · rfl
    · rfl
  le_total a b := by
    by_cases e : a = b
    · exact Or.inl (Or.inr e)
    · rcases h.law13 a b e with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inl (Or.inl h')
  toDecidableLE := Classical.decRel _

/-- A field with a linear order in which `0 < 1`, addition is monotone and products of positives
are positive is a strict ordered field. -/
theorem isStrictOrderedRing_of_facts {β : Type*} [Field β] [LinearOrder β] (h01 : (0 : β) < 1)
    (hadd : ∀ a b c : β, a < b → c + a < c + b) (hmul : ∀ a b : β, 0 < a → 0 < b → 0 < a * b) :
    IsStrictOrderedRing β := by
  have hadd' : ∀ a b c : β, a ≤ b → c + a ≤ c + b := fun a b c hab => by
    rcases hab.lt_or_eq with hab | rfl
    · exact (hadd a b c hab).le
    · exact le_rfl
  have : IsOrderedAddMonoid β :=
    { add_le_add_left := fun a b hab c => by rw [add_comm a, add_comm b]; exact hadd' a b c hab
      add_le_add_right := fun a b hab c => hadd' a b c hab }
  have : ZeroLEOneClass β := ⟨h01.le⟩
  exact IsStrictOrderedRing.of_mul_pos hmul

/-- **Laws 1–16** (with the asymmetry of 13 and `0 ≠ 1`) **make the system a strict ordered
field.** -/
theorem laws_isStrictOrderedRing (h : Laws1to16 α) (ha : Law13Asymm α) (h01 : (0 : α) ≠ 1) :
    letI := h.toFieldLaws.toField h01
    letI := h.toOrderLaws.toLinearOrder ha
    IsStrictOrderedRing α := by
  -- facts in terms of the given operations
  obtain ⟨n, hn, -⟩ := (h.law3 1 0).1
  have h01' : (0 : α) < 1 := by
    rcases h.law13 0 1 h01 with h1 | h1
    · exfalso
      have k1 : (0 : α) < n := by
        have := (h.law15 0 1 n h1).1
        rw [(h.law2 n).2, hn] at this; exact this
      have k2 := (h.law16 0 1 n h1 k1).1
      rw [h.toFieldLaws.zero_mul, (h.law5 n).2] at k2
      exact ha _ _ k1 k2
    · exact h1
  have hadd : ∀ a b c : α, a < b → c + a < c + b := fun a b c hab => (h.law15 b a c hab).2
  have hmul : ∀ a b : α, 0 < a → 0 < b → 0 < a * b := fun a b ha' hb => by
    have := (h.law16 a 0 b ha' hb).1
    rwa [h.toFieldLaws.zero_mul] at this
  exact @isStrictOrderedRing_of_facts α (h.toFieldLaws.toField h01)
    (h.toOrderLaws.toLinearOrder ha) h01' hadd hmul

/-- With law 17, the ordered field of laws 1–16 is archimedean. -/
theorem laws_archimedean (h : Laws1to17 α) (ha : Law13Asymm α) (h01 : (0 : α) ≠ 1) :
    letI := h.toFieldLaws.toField h01
    letI := h.toOrderLaws.toLinearOrder ha
    Archimedean α := by
  let F := h.toFieldLaws.toField h01
  let O := h.toOrderLaws.toLinearOrder ha
  have := laws_isStrictOrderedRing h.toLaws1to16 ha h01
  exact law17_iff_archimedean.1 h.law17

end Converse

/-- The rationals with `<` replaced by the relation "always". -/
def TotalLT : Type := ℚ

instance : Field TotalLT := inferInstanceAs (Field ℚ)

instance : LT TotalLT := ⟨fun _ _ => True⟩

/-- **Law 13 as printed is too weak**: with `a < b` for all `a`, `b`, the rationals satisfy all of
laws 1–17 literally, but the relation is not an order (`a > a`). -/
theorem totalLT_laws : Laws1to17 TotalLT ∧ ¬Law13Asymm TotalLT := by
  have hF := (laws_of_orderedField (α := ℚ)).1.toFieldLaws
  refine ⟨⟨⟨hF, ⟨fun _ _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial,
    fun _ _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ _ _ => ⟨trivial, trivial⟩⟩⟩,
    fun _ _ _ _ => ⟨0, trivial⟩⟩, fun h => h 0 0 trivial trivial⟩

/-- **A one-element system satisfies all of laws 1–17**, but it is not a field. -/
theorem punit_laws : Laws1to17 PUnit ∧ (0 : PUnit) = 1 := by
  refine ⟨⟨⟨⟨law1_holds _, fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨⟨PUnit.unit, Subsingleton.elim _ _,
    fun _ _ => Subsingleton.elim _ _⟩, ⟨PUnit.unit, Subsingleton.elim _ _,
    fun _ _ => Subsingleton.elim _ _⟩⟩, law4_holds _, fun _ => ⟨rfl, rfl⟩,
    fun a _ ha => absurd (Subsingleton.elim a 0) ha, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩,
    ⟨fun a b h => absurd (Subsingleton.elim a b) h, fun _ _ _ h => absurd h (lt_irrefl _),
    fun _ _ _ h => absurd h (lt_irrefl _), fun _ _ _ h => absurd h (lt_irrefl _)⟩⟩,
    fun _ _ h => absurd h (lt_irrefl _)⟩, rfl⟩

/-!
## [s13.dependence] The laws are not independent

*(§ 13)*

> Not every one of the properties (1–17) given above is independent of the others. The problem arises to investigate the logical dependence of these properties.

**Lean reading.** One dependence suffices to prove the claim: `law8_of_others` derives the
commutativity of addition (law 8) from laws 3, 5, 7, 10, 11, by expanding `(a + b)(1 + 1)` with
both distributive laws and cancelling (law 3). The "investigation" of the dependence is announced,
not carried out, here (§§ 32, 33 answer two questions about law 12; Theorems 38, 39).

**Status.** proved
-/

theorem law8_of_others {α : Type*} [Add α] [Mul α] [Zero α] [One α] (h3 : Law3 α) (h5 : Law5 α)
    (h7 : Law7 α) (h10 : Law10 α) (h11 : Law11 α) : Law8 α := by
  intro a b
  have e1 : (a + b) * (1 + 1) = (a + b) + (a + b) := by rw [h10, (h5 _).1]
  have e2 : (a + b) * (1 + 1) = (a + a) + (b + b) := by
    rw [h11, h10, h10, (h5 a).1, (h5 b).1]
  have e3 : a + (b + (a + b)) = a + (a + (b + b)) := by
    rw [h7, h7 a a, ← e1, ← e2]
  have e4 : b + (a + b) = a + (b + b) := (h3 a _).1.unique e3 rfl
  have e5 : (b + a) + b = (a + b) + b := by rw [← h7, e4, h7]
  exact ((h3 b _).2.unique e5 rfl).symm

/-!
## [s13.omega_t] Law 17 is independent of laws 1–16: the system `Ω(t)`

*(§ 13)*

> We will here merely call attention to the fact that, in any case, the last of these conditions (17) is not a consequence of the remaining properties, since, for example, the complex number system $\Omega(t)$, considered in § 12, possesses all of the properties (1–16), but does not fulfil the law stated in (17).

**Lean reading.** `OmegaT` (helper module `AnalyticAux3.lean`) is Hilbert's `Ω(t)` of § 12: the
real functions of `t` obtained from `t` by the four operations (division by nonzero elements) and
`ω ↦ √(1 + ω²)`, identified when they agree for all large `t` (germs at `+∞`; the helper admits
`1` as a second generator, which is redundant since `1 = t / t`: `OmegaT.mem_omegaTSubring_iff_isGenT`
shows that the numbers of `OmegaT` are exactly the germs of the functions obtained from `t`
alone), ordered by
"`a > b` iff `a - b` is positive for all sufficiently large `t`" (`OmegaT.lt_iff_eventually`).
That this is a linear order rests on Hilbert's claim that every element is eventually zero,
positive or negative (`OmegaT.IsGen.trichotomy`); Hilbert derives it from algebraicity, the proof
here from the meromorphy of `s ↦ f(1/s)` at `s = 0⁺` and the intermediate value theorem.
`omegaT_laws`: `Ω(t)` satisfies laws 1–16 (and the asymmetry of 13) but not law 17 (`t > n` for
every natural number `n`, `OmegaT.natCast_lt_t`). Hence `law17_independent`: law 17 is not a
consequence of laws 1–16. `Ω(t)` is moreover a Pythagorean ordered field
(`OmegaT.instIsPythagorean`), so the coordinate models of § 9 over it satisfy groups I–IV.

**Status.** proved
-/

namespace OmegaT

open Filter

/-- The functions obtained from `t` **alone** (without the constant `1`) by Hilbert's five
operations. -/
inductive IsGenT : (ℝ → ℝ) → Prop
  | t : IsGenT id
  | add {f g : ℝ → ℝ} : IsGenT f → IsGenT g → IsGenT (f + g)
  | sub {f g : ℝ → ℝ} : IsGenT f → IsGenT g → IsGenT (f - g)
  | mul {f g : ℝ → ℝ} : IsGenT f → IsGenT g → IsGenT (f * g)
  | div {f g : ℝ → ℝ} : IsGenT f → IsGenT g → ¬(g =ᶠ[atTop] 0) → IsGenT (f / g)
  | sqrt {f : ℝ → ℝ} : IsGenT f → IsGenT (fun x => Real.sqrt (1 + f x ^ 2))

theorem IsGenT.isGen {f : ℝ → ℝ} (h : IsGenT f) : IsGen f := by
  induction h with
  | t => exact IsGen.t
  | add _ _ ha hb => exact ha.add hb
  | sub _ _ ha hb => exact ha.sub hb
  | mul _ _ ha hb => exact ha.mul hb
  | div _ _ hg ha hb => exact ha.div hb hg
  | sqrt _ ha => exact ha.sqrt

/-- The generator `1` of `IsGen` is redundant: every function of `IsGen` agrees for large `t` with
one obtained from `t` alone (`1 = t / t`). -/
theorem IsGen.exists_isGenT {f : ℝ → ℝ} (h : IsGen f) : ∃ g, IsGenT g ∧ g =ᶠ[atTop] f := by
  induction h with
  | t => exact ⟨id, IsGenT.t, EventuallyEq.rfl⟩
  | one =>
    refine ⟨id / id, IsGenT.t.div IsGenT.t ?_, ?_⟩
    · intro h
      obtain ⟨x, hx1, hx2⟩ := (h.and (eventually_gt_atTop (0 : ℝ))).exists
      simp only [id, Pi.zero_apply] at hx1
      linarith
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp [hx.ne']
  | add _ _ ha hb =>
    obtain ⟨a, ha, ea⟩ := ha; obtain ⟨b, hb, eb⟩ := hb
    exact ⟨a + b, ha.add hb, ea.add eb⟩
  | sub _ _ ha hb =>
    obtain ⟨a, ha, ea⟩ := ha; obtain ⟨b, hb, eb⟩ := hb
    exact ⟨a - b, ha.sub hb, ea.sub eb⟩
  | mul _ _ ha hb =>
    obtain ⟨a, ha, ea⟩ := ha; obtain ⟨b, hb, eb⟩ := hb
    exact ⟨a * b, ha.mul hb, ea.mul eb⟩
  | div _ _ hg ha hb =>
    obtain ⟨a, ha, ea⟩ := ha; obtain ⟨b, hb, eb⟩ := hb
    exact ⟨a / b, ha.div hb (fun h => hg (eb.symm.trans h)), ea.div eb⟩
  | sqrt _ ha =>
    obtain ⟨a, ha, ea⟩ := ha
    exact ⟨_, ha.sqrt, ea.mono fun x hx => by simp only [hx]⟩

/-- **`Ω(t)` is generated by `t` alone**: its numbers are exactly the germs of the functions
obtained from `t` by the five operations. -/
theorem mem_omegaTSubring_iff_isGenT {x : GermT} :
    x ∈ omegaTSubring ↔ ∃ f, IsGenT f ∧ (f : GermT) = x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := hf.exists_isGenT
    exact ⟨g, hg, Germ.coe_eq.2 e⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf.isGen, rfl⟩

end OmegaT

theorem omegaT_laws : Laws1to16 OmegaT ∧ Law13Asymm OmegaT ∧ ¬Law17 OmegaT :=
  ⟨laws_of_orderedField.1, laws_of_orderedField.2,
    fun h => OmegaT.not_archimedean (law17_iff_archimedean.1 h)⟩

/-- **Law 17 is not a consequence of laws 1–16** (with the asymmetry of law 13). -/
theorem law17_independent :
    ∃ (α : Type) (_ : Add α) (_ : Mul α) (_ : Zero α) (_ : One α) (_ : LT α),
      Laws1to16 α ∧ Law13Asymm α ∧ ¬Law17 α :=
  ⟨OmegaT, _, _, _, _, _, omegaT_laws⟩

end HilbertFoundations
