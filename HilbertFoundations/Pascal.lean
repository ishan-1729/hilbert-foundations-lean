import HilbertFoundations.Congruence
import HilbertFoundations.PascalAux8

/-!
# Demonstration of Pascal's theorem (§ 14, Theorem 21)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 14. Demonstration of Pascal's theorem

## Organisation

The setting is a plane geometry with the axioms I 1–2, II, III, IV (`PlaneCongruence`,
`PlaneParallels`), Hilbert's basis for Chapters III and IV. The development is in the helper
modules (which contain no units):

* `PascalAux1.lean`: isometries (permutations preserving the congruence of segments), the isometry
  of a congruence of triangles (by Theorem 17), rigidity, the reflections in lines.
* `PascalAux2.lean`: half-turns; the product of three half-turns is a half-turn; the translations
  form a commutative group; **vectors** `Vec O`; isometries fixing `O` are additive; lines are
  cosets of the lines through `O`.
* `PascalAux3.lean`: the theorem of the three reflections; the **rotations about `O` commute**;
  rectangular axes (`Axes`).
* `PascalAux4.lean`: the rotations as operators on the vectors; the **slope maps** of the lines
  through `O`; **all slope maps commute** (`slope_comm`).
* `PascalAux5.lean`: the points of the axis `x` with Hilbert's multiplication form an **ordered
  field** `G ax`.
* `PascalAux6.lean`: co-ordinates, lines and parallels in co-ordinates, **Pascal's theorem**
  (`Pas.pascal`) as a computation in this field.
* `PascalAux7.lean`, `PascalAux8.lean`: lengths of segments, half-rays in co-ordinates, right
  triangles and Hilbert's symbol `αc` (`Pas.base_eq`), the construction of a line cutting a given
  line at a given angle.

**The route of the proof.** Hilbert's first proof combines two ingredients: the lemma `αβc = βαc`
on right triangles (proved by him with the theorem on angles inscribed in a circle) and a
computation with these symbols. Here the lemma is obtained in a stronger, algebraic form: the
rotations about a point form a commutative group (the theorem of the three reflections), and
consequently the "cosine" and "sine" operators of all rotations commute; from this all the slope
maps of the lines through a point commute. This yields the field of segments of § 15 (Hilbert's
own multiplication, `PascalAux5.lean`) *before* Pascal's theorem, and Pascal's theorem becomes a
computation in co-ordinates over this field. Hilbert's lemma `αβc = βαc` is then a consequence
(unit `s14.alpha_beta`). Only the axioms Hilbert names are used: I 1–2, II, III, IV of plane
geometry; neither Archimedes's axiom nor any property of circles is assumed.

## API for other files

* `theorem21` (Pascal's theorem), `BaseOf` (Hilbert's `a = αc`), `baseOf_unique`, `baseOf_exists`,
  `alpha_beta_comm`, `baseOf_cancel`, `exists_line_at_angle'`;
* from the helper modules (namespace `Pas`): `isom`, `refl`, `ht`, `Vec`, `Axes`, `exists_axes`,
  `G` (the ordered field of segments of an axis, instances `fieldG`, `linOrdG`,
  `isStrictOrderedRingG`), `mulV`, `xc`, `yc`, `cross`, `mem_line_iff_cross`, `parEq_iff_cross`,
  `len`, `len_eq_iff`, `ray_coords`, `rightAngle_iff`, `cosA`, `base_eq`, `cosA_pos`.
-/

namespace HilbertFoundations

universe u v

variable {P : Type u} {L : Type v}

/-!
## [s14.basis] The axioms of Chapters III and IV

*(§ 14)*

> In this and the following chapter, we shall take as the basis of our discussion all of the plane axioms with the exception of the axiom of Archimedes; that is to say, the axioms I, 1–2 and II–IV. In the present chapter, we propose, by aid of these axioms, to establish Euclid's theory of proportion; that is, we shall establish it for the plane and that independently of the axiom of Archimedes.

**Lean reading.** The basis is a plane geometry with the instances `[PlaneCongruence P L]`
(I 1–2 with the plane clauses of I 7, II 1–5, IV 1–6) and `[PlaneParallels P L]` (III); the class
`Archimedes` is never assumed in Chapters III–IV unless a unit says so. All units of this file and
of `Proportion.lean` use exactly these hypotheses (or fewer: the laws of addition of § 15 use only
the linear axioms).

**Status.** remark
-/

/-!
## [s14.pascal_special] Pascal's theorem as a special case of the theorem on conics

*(§ 14)*

> For this purpose, we shall first demonstrate a proposition which is a special case of the well known theorem of Pascal usually considered in the theory of conic sections, and which we shall hereafter, for the sake of brevity, refer to simply as Pascal's theorem.

**Lean reading.** A historical remark: Theorem 21 is the theorem of Pascal (for a conic) in the
degenerate case where the conic is a pair of lines and the Pascal line is the line at infinity
(Pappus's theorem with the intersections replaced by parallelism). Projective geometry and conics
are not part of this formalization; nothing to prove.

**Status.** remark
-/

/-!
## [th.21] Theorem 21

*(§ 14)*

> (Pascal's theorem.) Given the two sets of points $A$, $B$, $C$ and $A'$, $B'$, $C'$ so situated respectively upon two intersecting straight lines that none of them fall at the intersection of these lines. If $CB'$ is parallel to $BC'$ and $CA'$ is also parallel to $AC'$, then $BA'$ is parallel to $AB'$. [Note: F. Schur has published in the *Math. Ann.*, Vol. 51, a very interesting proof of the theorem of Pascal, based upon the axioms I–II, IV.]

**Lean reading.** `theorem21`: plane geometry with I 1–2, II, III, IV (`PlaneCongruence`,
`PlaneParallels`), exactly Hilbert's basis (unit `s14.basis`). Two distinct lines `g`, `h` meet in
`O`; `A, B, C ∈ g`, `A', B', C' ∈ h`, all different from `O`. "Parallel" is Hilbert's notion
(`Parallel`: lines without a common point); the lines `CB'`, `BC'`, … are any lines through the
named points (unique by I 2). Correction: the hypothesis `A ≠ B` is added. Read literally (the
"two sets of points" not assumed to consist of distinct points) the theorem is false: if `A = B`,
the hypotheses force `A' = B'` (the parallels to `AC'` through `C` coincide) and the two lines of
the conclusion are one line, which is not parallel to itself; NonPascal.lean
(`pascal_literal_false`) gives the counterexample `C = (1,0)`, `A = B = (2,0)`, `A' = B' = (0,1)`,
`C' = (0,2)` in the real plane. No other distinctness is needed (`CB'` parallel to `BC'` already
forces `B ≠ C`, etc.). The proof (`Pas.pascal`) is not Hilbert's: after the construction of the
ordered field of segments from the commuting rotations (see the module docstring), the six points
are written `O + t·u` on `g` and `O + t·w` on `h`, the parallelisms become `b b' = c c'` and
`a a' = c c'` (cross products of directions vanish), whence `a a' = b b'`. Hilbert's first proof
also has gaps that this proof avoids: the perpendicular from `O` to `l` may coincide with `OA`
(then `λ'` is not an acute angle but the null angle, and the symbol `λ'` is undefined), and from
`νb' ≡ ν'a` (equal distances of the feet from `O`) the coincidence of the feet only follows when
they lie on the same side of `O`, a question of order which he does not discuss. The steps of his
computation, (1)–(6), are equalities of the operators `α` of `s14.alpha_c`, which commute
(`s14.alpha_beta`) and can be cancelled (`s14.alpha_cancel`); the second proof starts from the
construction `s14.angle_line`.

**Status.** proved (corrected)
-/

/-- **Theorem 21 (Pascal's theorem).** -/
theorem theorem21 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {g h : L} {O A B C A' B' C' : P} (hgh : g ≠ h)
    (hOg : O ∈ g) (hOh : O ∈ h) (hA : A ∈ g) (hB : B ∈ g) (hC : C ∈ g) (hA' : A' ∈ h)
    (hB' : B' ∈ h) (hC' : C' ∈ h) (hAO : A ≠ O) (hBO : B ≠ O) (hCO : C ≠ O) (hA'O : A' ≠ O)
    (hB'O : B' ≠ O) (hC'O : C' ≠ O) (hAB : A ≠ B) {l l' m m' n n' : L} (hl : C ∈ l ∧ B' ∈ l)
    (hl' : B ∈ l' ∧ C' ∈ l') (hm : C ∈ m ∧ A' ∈ m) (hm' : A ∈ m' ∧ C' ∈ m')
    (hn : B ∈ n ∧ A' ∈ n) (hn' : A ∈ n' ∧ B' ∈ n') (h1 : Parallel (Point := P) l l')
    (h2 : Parallel (Point := P) m m') : Parallel (Point := P) n n' :=
  Pas.pascal hgh hOg hOh hA hB hC hA' hB' hC' hAO hBO hCO hA'O hB'O hC'O hAB hl hl' hm hm' hn hn'
    h1 h2

/-!
## [s14.schur] Schur's proof of Pascal's theorem

*(§ 14)*

> [Note: F. Schur has published in the *Math. Ann.*, Vol. 51, a very interesting proof of the theorem of Pascal, based upon the axioms I–II, IV.]

**Lean reading.** A bibliographical note. Schur's theorem (1899) is the theorem of Pascal–Pappus
in its *projective* form (collinearity of the three intersections) in a geometry of space with the
axioms of connection, order and congruence; with "parallel" meaning "without common point", as in
Theorem 21, the statement needs the axiom of parallels (in the hyperbolic plane, which satisfies
I–II, IV, the parallel form fails). The projective form is not formalized here; the claim about
Schur's paper is not checked.

**Status.** remark
-/

/-!
## [s14.alpha_c] The symbol `αc`

*(§ 14)*

> In order to demonstrate this theorem, we shall first introduce the following notation. In a right triangle, the base $a$ is uniquely determined by the hypotenuse $c$ and the base angle $\alpha$ included by $a$ and $c$. We will express this fact briefly by writing \[ a=\alpha c. \] … Hence, the symbol $\alpha c$ always represents a definite segment, providing $c$ is any given segment whatever and $\alpha$ is any given acute angle.

**Lean reading.** `BaseOf A O B C₁ C₂ A₁ A₂` ("`A₁A₂ = α · C₁C₂` for `α = ∠AOB`"): there is a right
triangle `XYZ` (right angle `∠XYZ`, `IsRightAngle`) with `∠YXZ ≡ α`, hypotenuse `XZ ≡ C₁C₂` and base
`XY ≡ A₁A₂`. Plane geometry with I 1–2, II, III, IV. Uniqueness (`baseOf_unique`): two bases of the
same `α` and `c` are congruent; existence (`baseOf_exists`): for an acute angle (`IsAcute`) and a
genuine segment `c` there is a base. The proofs go through the field of segments: in a right triangle
`XY = XZ · cos α` (`Pas.base_eq`), where `cos α` is a field element depending only on the angle up
to congruence, positive for an acute angle (`Pas.cosA_pos`). Hilbert's uniqueness claim is the
congruence theorem "hypotenuse and acute angle" for right triangles, which he does not prove; it
needs the axiom of parallels only through the method used here (it holds in absolute geometry).

**Status.** proved
-/

/-- `A₁A₂` is **the base `αc`** of a right triangle with base angle `α = ∠AOB` and hypotenuse
`c = C₁C₂`. -/
def BaseOf [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    (A O B C1 C2 A1 A2 : P) : Prop :=
  ∃ X Y Z : P, IsRightAngle (L := L) X Y Z ∧ AngCong A O B Y X Z ∧ SegCong X Z C1 C2 ∧
    SegCong X Y A1 A2

section AlphaC

variable [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P] [PlaneCongruence P L]
  [PlaneParallels P L]

/-- In terms of lengths: `BaseOf α c a` means `a = c · cos α`. -/
theorem baseOf_len (ax : Pas.Axes P L) {A O B C1 C2 A1 A2 : P} (hn : ¬Collinear (Line := L) A O B)
    (hc : C1 ≠ C2) (ha : A1 ≠ A2) (h : BaseOf (L := L) A O B C1 C2 A1 A2) :
    Pas.len ax A1 A2 = Pas.len ax C1 C2 * Pas.cosA ax A O B := by
  obtain ⟨X, Y, Z, hr, hα, sc, sa⟩ := h
  have hn' : ¬Collinear (Line := L) Y X Z := fun hh => hr.1 hh.swap12
  obtain ⟨hXY, hZY, hXZ⟩ := Pas.nc_ne ax hr.1
  rw [← (Pas.len_eq_iff ax hXY ha).2 sa, Pas.base_eq ax hr, (Pas.len_eq_iff ax hXZ hc).2 sc,
    Pas.cosA_congr ax hn' hn (angCong_symm hn hn' hα)]

/-- **The base is uniquely determined** by the hypotenuse and the base angle. -/
theorem baseOf_unique {A O B C1 C2 A1 A2 A1' A2' : P} (hn : ¬Collinear (Line := L) A O B)
    (hc : C1 ≠ C2) (ha : A1 ≠ A2) (ha' : A1' ≠ A2') (h : BaseOf (L := L) A O B C1 C2 A1 A2)
    (h' : BaseOf (L := L) A O B C1 C2 A1' A2') : SegCong A1 A2 A1' A2' := by
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hc
  rw [← Pas.len_eq_iff ax ha ha', baseOf_len ax hn hc ha h, baseOf_len ax hn hc ha' h']

/-- **The symbol `αc` is defined** for an acute angle `α` and every segment `c`. -/
theorem baseOf_exists {A O B C1 C2 : P} (hα : IsAcute (L := L) A O B) (hc : C1 ≠ C2) :
    ∃ A1 A2 : P, A1 ≠ A2 ∧ BaseOf (L := L) A O B C1 C2 A1 A2 := by
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hc
  obtain ⟨X, Y, Z, hr, hang, hlen⟩ := Pas.exists_right_triangle ax hα (Pas.len_pos ax hc)
  obtain ⟨hXY, -, hXZ⟩ := Pas.nc_ne ax hr.1
  refine ⟨X, Y, hXY, X, Y, Z, hr, hang, ?_, segCong_refl (Line := L) hXY⟩
  exact (Pas.len_eq_iff ax hXZ hc).1 (by rw [hlen])

end AlphaC

/-!
## [s14.alpha_beta] The lemma `αβc = βαc`

*(§ 14)*

> Furthermore, if $c$ is any arbitrary segment and $\alpha$, $\beta$ are any two acute angles whatever, then the two segments $\alpha \beta c$ and $\beta \alpha c$ are always congruent; that is, we have \[ \alpha \beta c = \beta \alpha c, \] and, consequently, the symbols $\alpha$ and $\beta$ are interchangeable.

**Lean reading.** `alpha_beta_comm`: if `d = βc`, `e = αd`, `d' = αc`, `e' = βd'` (four relations
`BaseOf`, all segments genuine), then `e ≡ e'`; by `baseOf_exists` the four segments exist when `α`,
`β` are acute. Plane geometry with I 1–2, II, III, IV. Hilbert's proof (Fig. 18) puts `α` and `β`
on either side of `c = AB` at `A`, drops the perpendiculars `BC`, `BD`, `AE` and uses that `A`, `B`,
`C`, `D` lie on a circle (the right angles `ACB`, `ADB`) and the congruence of the inscribed angles
`ACD`, `ABD`, the theorem on inscribed angles which § 7 asserts without proof (`s7.circle_properties`,
open in Congruence.lean). Here the lemma follows from `a = c · cos α` (`s14.alpha_c`) and the
commutativity of the field of segments, which in turn rests on the commutativity of the rotations
(see the module docstring); no property of circles is used.

**Status.** proved
-/

/-- **`αβc = βαc`.** -/
theorem alpha_beta_comm [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {A O B A' O' B' C1 C2 D1 D2 E1 E2 D1' D2' E1' E2' : P}
    (hα : ¬Collinear (Line := L) A O B) (hβ : ¬Collinear (Line := L) A' O' B') (hc : C1 ≠ C2)
    (hd : D1 ≠ D2) (he : E1 ≠ E2) (hd' : D1' ≠ D2') (he' : E1' ≠ E2')
    (h1 : BaseOf (L := L) A' O' B' C1 C2 D1 D2) (h2 : BaseOf (L := L) A O B D1 D2 E1 E2)
    (h3 : BaseOf (L := L) A O B C1 C2 D1' D2') (h4 : BaseOf (L := L) A' O' B' D1' D2' E1' E2') :
    SegCong E1 E2 E1' E2' := by
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hc
  rw [← Pas.len_eq_iff ax he he', baseOf_len ax hα hd he h2, baseOf_len ax hβ hc hd h1,
    baseOf_len ax hβ hd' he' h4, baseOf_len ax hα hc hd' h3, mul_right_comm]

/-!
## [s14.alpha_cancel] The symbol `α` can be cancelled

*(§ 14)*

> Because of the significance of our symbols, we can conclude at once from this congruence that \[ \mu'\nu b' \equiv \mu'\nu' a, \] and, consequently, that\\ …

**Lean reading.** The step of Hilbert's computation that removes a symbol from both members:
`baseOf_cancel`: if `a = αc`, `a' = αc'` and `a ≡ a'`, then `c ≡ c'` (bases of right triangles with
the same base angle are congruent only if the hypotenuses are). Plane geometry with I 1–2, II, III,
IV. Proof: `a = c · cos α` with `cos α > 0`, and the field of segments has no zero divisors.

**Status.** proved
-/

/-- **Cancellation of a symbol `α`.** -/
theorem baseOf_cancel [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {A O B C1 C2 C1' C2' A1 A2 A1' A2' : P}
    (hα : ¬Collinear (Line := L) A O B) (hc : C1 ≠ C2) (hc' : C1' ≠ C2') (ha : A1 ≠ A2)
    (ha' : A1' ≠ A2') (h : BaseOf (L := L) A O B C1 C2 A1 A2)
    (h' : BaseOf (L := L) A O B C1' C2' A1' A2') (hs : SegCong A1 A2 A1' A2') :
    SegCong C1 C2 C1' C2' := by
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (L := L) hc
  have e := (Pas.len_eq_iff ax ha ha').2 hs
  rw [baseOf_len ax hα hc ha h, baseOf_len ax hα hc' ha' h'] at e
  have hpos : 0 < Pas.cosA ax A O B := by
    have h1 := Pas.len_pos ax ha
    rw [baseOf_len ax hα hc ha h] at h1
    exact pos_of_mul_pos_right h1 (le_of_lt (Pas.len_pos ax hc))
  rw [← Pas.len_eq_iff ax hc hc']
  exact mul_right_cancel₀ (ne_of_gt hpos) e

/-!
## [s14.angle_line] A line through a point cutting a line at a given angle

*(§ 14)*

> Having given any straight line whatever, together with an arbitrary angle and a point lying outside of the given line, we can, by constructing the given angle and drawing a parallel line, find a straight line passing through the given point and cutting the given straight line at the given angle.

**Lean reading.** `exists_line_at_angle'`: plane geometry with I 1–2, II, III, IV; for a line `a`,
an angle `∠UOV` (`¬Collinear U O V`) and a point `P ∉ a` there are points `X ≠ Y` of `a` with
`∠YXP ≡ ∠UOV`, i.e. the line `XP` through `P` cuts `a` at `X` under the given angle. Proof as
Hilbert says: lay off the angle at a point `X₀` of `a` towards `P` (IV 4), draw the parallel through
`P` (III); it meets `a` in `X`, and the angle at `X` is the corresponding angle (Theorem 19), on the
appropriate half-ray of `a` from `X`.

**Status.** proved
-/

theorem exists_line_at_angle' [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {a : L} {U O V Q : P}
    (hn : ¬Collinear (Line := L) U O V) (hQ : Q ∉ a) :
    ∃ X Y : P, X ∈ a ∧ Y ∈ a ∧ X ≠ Y ∧ AngCong U O V Y X Q :=
  Pas.exists_line_at_angle hn hQ

/-!
## [s14.second_proof] The second proof of Pascal's theorem

*(§ 14)*

> By means of this construction, we can demonstrate Pascal's theorem in the following very simple manner, for which, however, I am indebted to another source. … In case $D'$ coincides with one of the points $A'$, $B'$, $C'$, it is necessary to make a modification of this method, which evidently is not difficult to do.

**Lean reading.** A second proof of Theorem 21 (proved above by another route). Its steps (1*)–(6*)
use "a well known property of circles": a quadrilateral `CBD'A'` with `∠OCA' ≡ ∠OD'B` is
inscribed in a circle, and conversely the angles of inscribed quadrilaterals — the properties of the
circle that § 7 asserts (`s7.circle_properties`, proved in `CongruenceClose.lean`). The construction
it starts from is unit `s14.angle_line`. The proof is not formalized; the theorem it proves is
`theorem21`. Hilbert's closing remark (the case `D' ∈ {A', B', C'}`) concerns this proof only.

**Status.** remark
-/

end HilbertFoundations
