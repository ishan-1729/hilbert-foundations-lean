import HilbertFoundations.Pascal
import HilbertFoundations.ProportionAux3

/-!
# Algebra of segments, proportion, equations of lines and planes (§§ 15–17)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 15. An algebra of segments, based upon Pascal's theorem
* § 16. Proportion and the theorems of similitude
* § 17. Equations of straight lines and of planes

## Organisation

The setting is a plane geometry with I 1–2, II, III, IV (`PlaneCongruence`, `PlaneParallels`),
except for the laws of addition of § 15 (linear axioms only, `SegmentCongruence`) and the last part
of § 17 (Archimedes's axiom). The helper modules:

* `ProportionAux1.lean`: sums of segments from the linear axioms (`Pas.SegSum`), lengths add
  (`Pas.len_add`), Hilbert's product construction on an arbitrary right angle (`Pas.HilbertProd`)
  and its value `len c = len a · len b` (`Pas.hilbertProd_iff`).
* `ProportionAux2.lean`: Theorem 23 (`Pas.thales`, `Pas.thales_converse`), Theorem 22
  (`Pas.similar_prop`), the co-ordinates of points and the equations of lines.
* `ProportionAux3.lean`: betweenness on a line is the order of the field of segments; with
  Archimedes's axiom the field is archimedean.

The field of segments `Pas.G ax` (positive and negative segments of an axis, `PascalAux5.lean`) is
built from Hilbert's own multiplication; its commutativity and associativity come from the
commutation of the rotations (see Pascal.lean), and they are the content of Pascal's theorem.

## API for other files

`segSum_iff_len`, `segment_algebra`, `SegLt`, `segLt_iff`, `segSum_exists'`, `segSum_unique'`,
`segSum_comm'`, `segSum_assoc'`, `hilbertProd_iff'`, `hilbertProd_exists`, `hilbertProd_unique`,
`hilbertProd_comm`, `hilbertProd_assoc`, `hilbertProd_distrib`, `hilbertProd_quotient`,
`SegProportion`, `segProportion_iff`, `Similar`, `theorem22`, `theorem22_special`, `theorem23`,
`theorem23_converse`, `signed_segments_laws`, `signed_particular`, `coordinates_bijective`,
`perpendicular_coordinate`, `line_through_origin_eq`, `parallel_line_eq'`, `lines_are_linear`,
`linear_eqs_are_lines`, `archimedean_segments`, `exists_real_correspondence`,
`SpaceCoordinatesClaim`, `IdealElementsClaim`.
-/

namespace HilbertFoundations

universe u v

variable {P : Type u} {L : Type v}

section Algebra

variable [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P] [PlaneCongruence P L]
  [PlaneParallels P L]

theorem len_of_segSum (ax : Pas.Axes P L) {A1 A2 B1 B2 C1 C2 : P} (ha : A1 ≠ A2) (hb : B1 ≠ B2)
    (hc : C1 ≠ C2) (h : Pas.SegSum A1 A2 B1 B2 C1 C2) :
    Pas.len ax C1 C2 = Pas.len ax A1 A2 + Pas.len ax B1 B2 := by
  obtain ⟨X, Y, Z, hb', s1, s2, s3⟩ := h
  rw [← (Pas.len_eq_iff ax (ne13_of_between (Line := L) hb') hc).2 s3,
    ← (Pas.len_eq_iff ax (ne12_of_between (Line := L) hb') ha).2 s1,
    ← (Pas.len_eq_iff ax (ne23_of_between (Line := L) hb') hb).2 s2]
  exact Pas.len_add ax hb'

/-- Sums of segments are sums of lengths. -/
theorem segSum_iff_len (ax : Pas.Axes P L) {A1 A2 B1 B2 C1 C2 : P} (ha : A1 ≠ A2) (hb : B1 ≠ B2)
    (hc : C1 ≠ C2) :
    Pas.SegSum A1 A2 B1 B2 C1 C2 ↔ Pas.len ax C1 C2 = Pas.len ax A1 A2 + Pas.len ax B1 B2 := by
  refine ⟨len_of_segSum ax ha hb hc, fun h => ?_⟩
  obtain ⟨C1', C2', hc', hs⟩ := Pas.segSum_exists (L := L) ha hb
  have e := len_of_segSum ax ha hb hc' hs
  obtain ⟨X, Y, Z, hb', s1, s2, s3⟩ := hs
  refine ⟨X, Y, Z, hb', s1, s2, ?_⟩
  have : SegCong C1' C2' C1 C2 := (Pas.len_eq_iff ax hc' hc).1 (e.trans h.symm)
  exact segCong_trans (L := L) (ne13_of_between (Line := L) hb') hc' hc s3 this

/-- Every positive element of the field of segments is the length of a segment of the axis. -/
theorem pos_is_len (ax : Pas.Axes P L) {t : Pas.G ax} (ht : 0 < t) :
    Pas.len ax ax.O (Pas.ofV (t : Pas.V ax)) = t :=
  Pas.len_of_pos ax ((Pas.pos_iff_posG ax).1 ht)

end Algebra

/-!
## [s15.calculating] Calculating with segments

*(§ 15)*

> Pascal's theorem, which was demonstrated in the last section, puts us in a position to introduce into geometry a method of calculating with segments, in which all of the rules for calculating with real numbers remain valid without any modification.

**Lean reading.** `segment_algebra`: plane geometry with I 1–2, II, III, IV. Fix a unit segment
`OE` and axes `ax` with origin `O` and unit point `E` (`Pas.exists_axes`). Every genuine segment
`AB` has a length `len A B`, a positive element of the ordered field `Pas.G ax` (`Pas.fieldG`,
`Pas.linOrdG`, `Pas.isStrictOrderedRingG`); congruent segments are exactly the segments of equal
length, every positive element is a length (`pos_is_len`), Hilbert's sum is the sum of the lengths
(`segSum_iff_len`) and his product is their product (`hilbertProd_iff'`). So the segments with
Hilbert's operations are the positive part of an ordered field, and all rules of calculation of an
ordered field hold for them; § 17 adds the negative segments and the zero segment
(`signed_segments_laws`, the laws 1–16 of § 13). "All of the rules for calculating with real
numbers" is read as the laws of an ordered field; the completeness of the real numbers is not
meant (it fails, e.g. in the geometry over `Ω`).

**Status.** proved (reading)
-/

/-- **The algebra of segments is the positive part of an ordered field.** -/
theorem segment_algebra [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) :
    (∀ {A B : P}, A ≠ B → 0 < Pas.len ax A B) ∧
    (∀ {A B C D : P}, A ≠ B → C ≠ D → (SegCong A B C D ↔ Pas.len ax A B = Pas.len ax C D)) ∧
    (∀ {t : Pas.G ax}, 0 < t → Pas.len ax ax.O (Pas.ofV (t : Pas.V ax)) = t) ∧
    (∀ {A1 A2 B1 B2 C1 C2 : P}, A1 ≠ A2 → B1 ≠ B2 → C1 ≠ C2 →
      (Pas.SegSum A1 A2 B1 B2 C1 C2 ↔ Pas.len ax C1 C2 = Pas.len ax A1 A2 + Pas.len ax B1 B2)) ∧
    (∀ {A1 A2 B1 B2 C1 C2 : P}, A1 ≠ A2 → B1 ≠ B2 → C1 ≠ C2 →
      (Pas.HilbertProd (L := L) ax.O ax.E A1 A2 B1 B2 C1 C2 ↔
        Pas.len ax C1 C2 = Pas.len ax A1 A2 * Pas.len ax B1 B2)) :=
  ⟨fun h => Pas.len_pos ax h, fun h h' => (Pas.len_eq_iff ax h h').symm, fun ht => pos_is_len ax ht,
    fun ha hb hc => segSum_iff_len ax ha hb hc, fun ha hb hc => Pas.hilbertProd_iff ax ha hb hc⟩

/-!
## [s15.equal] "Equal" segments

*(§ 15)*

> Instead of the word “congruent” and the sign $\equiv$, we make use, in the algebra of segments, of the word “equal” and the sign $=$.

**Lean reading.** A convention of language: in the statements of §§ 15–17 "equal" segments are
congruent segments (`SegCong`), and segments are handled through representatives (pairs of distinct
points), every relation being invariant under congruence.

**Status.** definition
-/

/-!
## [s15.sum] The sum of two segments

*(§ 15)*

> If $A, B, C$ are three points of a straight line and if $B$ lies between $A$ and $C$, then we say that $c = AC$ is the *sum* of the two segments $a=AB$ and $b=BC$. We indicate this by writing \[ c=a+b. \]

**Lean reading.** `Pas.SegSum A₁ A₂ B₁ B₂ C₁ C₂`: there are `X`, `Y`, `Z` with `Y` between `X` and `Z`
and `XY ≡ A₁A₂`, `YZ ≡ B₁B₂`, `XZ ≡ C₁C₂` (the sum of segments up to congruence, "equal" being
"congruent"). Linear axioms only (`SegmentCongruence`: I 1–2, II 1–4, IV 1–3). The definition is
justified by `segSum_exists'` (every two segments have a sum, II 2 and IV 1) and `segSum_unique'`
(the sum is unique up to congruence, IV 3).

**Status.** definition
-/

theorem segSum_def [HasBetween P] [HasSegCong P] (A1 A2 B1 B2 C1 C2 : P) :
    Pas.SegSum A1 A2 B1 B2 C1 C2 ↔ ∃ X Y Z : P, Between X Y Z ∧ SegCong X Y A1 A2 ∧
      SegCong Y Z B1 B2 ∧ SegCong X Z C1 C2 := Iff.rfl

theorem segSum_exists' [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A1 A2 B1 B2 : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2) :
    ∃ C1 C2 : P, C1 ≠ C2 ∧ Pas.SegSum A1 A2 B1 B2 C1 C2 := Pas.segSum_exists (L := L) hA hB

theorem segSum_unique' [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A1 A2 B1 B2 C1 C2 C1' C2' : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2) (hC : C1 ≠ C2)
    (hC' : C1' ≠ C2') (h : Pas.SegSum A1 A2 B1 B2 C1 C2) (h' : Pas.SegSum A1 A2 B1 B2 C1' C2') :
    SegCong C1 C2 C1' C2' := Pas.segSum_unique (L := L) hA hB hC hC' h h'

/-!
## [s15.less] Smaller and larger segments

*(§ 15)*

> The segments $a$ and $b$ are said to be smaller than c, which fact we indicate by writing \[ a<c, b<c. \] On the other hand, $c$ is said to be larger than $a$ and $b$, and we indicate this by writing \[ c>a, c>b. \]

**Lean reading.** `SegLt A₁ A₂ C₁ C₂` (`a < c`): `c` is the sum of `a` and some segment (`c > a` is
the same relation read backwards). Plane geometry with I 1–2, II, III, IV: `segLt_iff`, `a < c` iff
the length of `a` is less than the length of `c` in the ordered field of segments; in particular
the relation is a strict linear order on the congruence classes.

**Status.** definition
-/

/-- `A₁A₂` is **smaller** than `C₁C₂`. -/
def SegLt [HasBetween P] [HasSegCong P] (A1 A2 C1 C2 : P) : Prop :=
  ∃ B1 B2 : P, B1 ≠ B2 ∧ Pas.SegSum A1 A2 B1 B2 C1 C2

theorem segLt_iff [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {A1 A2 C1 C2 : P}
    (ha : A1 ≠ A2) (hc : C1 ≠ C2) : SegLt A1 A2 C1 C2 ↔ Pas.len ax A1 A2 < Pas.len ax C1 C2 := by
  constructor
  · rintro ⟨B1, B2, hb, h⟩
    rw [len_of_segSum ax ha hb hc h]
    exact lt_add_of_pos_right _ (Pas.len_pos ax hb)
  · intro h
    have hd : 0 < Pas.len ax C1 C2 - Pas.len ax A1 A2 := sub_pos.2 h
    refine ⟨ax.O, Pas.ofV ((Pas.len ax C1 C2 - Pas.len ax A1 A2 : Pas.G ax) : Pas.V ax),
      Ne.symm (Pas.ofV_ne_O' ax hd), (segSum_iff_len ax ha (Ne.symm (Pas.ofV_ne_O' ax hd)) hc).2 ?_⟩
    rw [pos_is_len ax hd]; ring

/-!
## [s15.add_laws] The laws of addition

*(§ 15)*

> From the linear axioms of congruence (axioms IV, 1–3), we easily see that, for the above definition of addition of segments, the associative law \[ a+(b+c)=(a+b)+c, \] as well as the commutative law \[ a+b = b+a \] is valid.

**Lean reading.** Linear axioms only (`SegmentCongruence`: I 1–2, II 1–4, IV 1–3), as Hilbert says.
`segSum_comm'`: if `c = a + b` then `c = b + a`. `segSum_assoc'`: if `d = a + b`, `e = d + c` and
`f = b + c`, then `e = a + f`, i.e. `(a + b) + c = a + (b + c)`. Proof: lay off `a`, `b`, `c`
consecutively on one line and use the uniqueness of sums (IV 3).

**Status.** proved
-/

theorem segSum_comm' [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A1 A2 B1 B2 C1 C2 : P} (h : Pas.SegSum A1 A2 B1 B2 C1 C2) : Pas.SegSum B1 B2 A1 A2 C1 C2 :=
  Pas.segSum_comm (L := L) h

theorem segSum_assoc' [HasLines P L] [HasBetween P] [HasSegCong P] [SegmentCongruence P L]
    {A1 A2 B1 B2 C1 C2 D1 D2 E1 E2 F1 F2 : P} (hA : A1 ≠ A2) (hB : B1 ≠ B2) (hC : C1 ≠ C2)
    (hD : D1 ≠ D2) (hE : E1 ≠ E2) (hF : F1 ≠ F2) (h1 : Pas.SegSum A1 A2 B1 B2 D1 D2)
    (h2 : Pas.SegSum D1 D2 C1 C2 E1 E2) (h3 : Pas.SegSum B1 B2 C1 C2 F1 F2) :
    Pas.SegSum A1 A2 F1 F2 E1 E2 :=
  Pas.segSum_assoc (L := L) hA hB hC hD hE hF h1 h2 h3

/-!
## [s15.product] The product of two segments

*(§ 15)*

> In order to define geometrically the product of two segments $a$ and $b$, we shall make use of the following construction. Select any convenient segment, which, having been selected, shall remain constant throughout the discussion, and denote the same by $1$. Upon the one side of a right angle, lay off from the vertex $O$ the segment $1$ and also the segment $b$. … This parallel will cut off from the other side of the right angle a segment $c$. We call this segment $c$ the *product* of the segments $a$ and $b$, and indicate this relation by writing \[ c=ab. \]

**Lean reading.** `Pas.HilbertProd U₁ U₂ A₁ A₂ B₁ B₂ C₁ C₂` (`c = ab` with the unit `1 = U₁U₂`): there
are a right angle `∠P₁OP₂` (`IsRightAngle`, any right angle), points `E₁`, `B'` of the side `OP₁` with
`OE₁ ≡ 1`, `OB' ≡ b`, points `A'`, `C'` of the side `OP₂` with `OA' ≡ a`, `OC' ≡ c`, and the line
`B'C'` is the parallel to `E₁A'` through `B'` (or this line itself, when `b ≡ 1`). Plane geometry
with I 1–2, II, III, IV. Hilbert tacitly claims that the construction always gives a segment, that
it does not depend on the right angle chosen nor on the representatives: `hilbertProd_iff'`
(`c = ab` iff `len c = len a · len b` in the field of segments with unit `1`), whence
`hilbertProd_exists` and `hilbertProd_unique` (any two products are congruent, whatever the right
angles used). The proof maps the right angle onto the axes by an isometry and computes with the
cross product of the directions of the two parallels.

**Status.** definition
-/

theorem hilbertProd_def [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    (U1 U2 A1 A2 B1 B2 C1 C2 : P) :
    Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2 ↔
      ∃ O P1 P2 E1 A' B' C' : P, IsRightAngle (L := L) P1 O P2 ∧ E1 ∈ ray O P1 ∧
        SegCong O E1 U1 U2 ∧ B' ∈ ray O P1 ∧ SegCong O B' B1 B2 ∧ A' ∈ ray O P2 ∧
        SegCong O A' A1 A2 ∧ C' ∈ ray O P2 ∧ SegCong O C' C1 C2 ∧
        ∃ l m : L, E1 ∈ l ∧ A' ∈ l ∧ B' ∈ m ∧ C' ∈ m ∧ (l = m ∨ ¬Meets (Point := P) l m) :=
  Iff.rfl

section Product

variable [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P] [PlaneCongruence P L]
  [PlaneParallels P L]

theorem hp_iff (ax : Pas.Axes P L) {U1 U2 : P} (hO : ax.O = U1) (hE : ax.E = U2)
    {A1 A2 B1 B2 C1 C2 : P} (ha : A1 ≠ A2) (hb : B1 ≠ B2) (hc : C1 ≠ C2) :
    Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2 ↔
      Pas.len ax C1 C2 = Pas.len ax A1 A2 * Pas.len ax B1 B2 := by
  subst hO hE; exact Pas.hilbertProd_iff ax ha hb hc

/-- The product in lengths, for the axes with origin `U₁` and unit point `U₂`. -/
theorem hilbertProd_iff' {U1 U2 : P} (hU : U1 ≠ U2) {A1 A2 B1 B2 C1 C2 : P} (ha : A1 ≠ A2)
    (hb : B1 ≠ B2) (hc : C1 ≠ C2) :
    ∃ ax : Pas.Axes P L, ax.O = U1 ∧ ax.E = U2 ∧
      (Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2 ↔
        Pas.len ax C1 C2 = Pas.len ax A1 A2 * Pas.len ax B1 B2) := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  exact ⟨ax, hO, hE, hp_iff ax hO hE ha hb hc⟩

/-- A segment of given positive length. -/
theorem seg_of_len (ax : Pas.Axes P L) {t : Pas.G ax} (ht : 0 < t) :
    ax.O ≠ Pas.ofV (t : Pas.V ax) ∧ Pas.len ax ax.O (Pas.ofV (t : Pas.V ax)) = t :=
  ⟨Ne.symm (Pas.ofV_ne_O' ax ht), pos_is_len ax ht⟩

/-- **The product exists.** -/
theorem hilbertProd_exists {U1 U2 A1 A2 B1 B2 : P} (hU : U1 ≠ U2) (ha : A1 ≠ A2) (hb : B1 ≠ B2) :
    ∃ C1 C2 : P, C1 ≠ C2 ∧ Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2 := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  obtain ⟨hne, hl⟩ := seg_of_len ax (mul_pos (Pas.len_pos ax ha) (Pas.len_pos ax hb))
  exact ⟨ax.O, _, hne, (hp_iff ax hO hE ha hb hne).2 hl⟩

/-- **The product is unique** up to congruence, whatever right angles are used. -/
theorem hilbertProd_unique {U1 U2 A1 A2 B1 B2 C1 C2 C1' C2' : P} (hU : U1 ≠ U2) (ha : A1 ≠ A2)
    (hb : B1 ≠ B2) (hc : C1 ≠ C2) (hc' : C1' ≠ C2')
    (h : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2)
    (h' : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1' C2') : SegCong C1 C2 C1' C2' := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  rw [hp_iff ax hO hE ha hb hc] at h
  rw [hp_iff ax hO hE ha hb hc'] at h'
  exact (Pas.len_eq_iff ax hc hc').1 (h.trans h'.symm)

end Product

/-!
## [s15.mul_comm] The commutative law of multiplication

*(§ 15)*

> We shall now demonstrate that, for this definition of the multiplication of segments, the *commutative* law \[ ab=ba \] holds. … But, because the two dotted lines are, by Pascal's theorem, parallel, the segment $ba$ just found coincides with the segment $ab$ previously constructed, and our proposition is established.

**Lean reading.** `hilbertProd_comm`: if `c = ab` and `c' = ba` (same unit), then `c ≡ c'`. Plane
geometry with I 1–2, II, III, IV. Hilbert obtains it from Pascal's theorem applied to the two sides
of the right angle; here both commutativity and Pascal's theorem come from the commutation of the
slope maps (`Pas.slope_comm`, see Pascal.lean), and the law is the commutativity of the field of
segments.

**Status.** proved
-/

theorem hilbertProd_comm [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 A1 A2 B1 B2 C1 C2 C1' C2' : P}
    (hU : U1 ≠ U2) (ha : A1 ≠ A2) (hb : B1 ≠ B2) (hc : C1 ≠ C2) (hc' : C1' ≠ C2')
    (h : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2)
    (h' : Pas.HilbertProd (L := L) U1 U2 B1 B2 A1 A2 C1' C2') : SegCong C1 C2 C1' C2' := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  rw [hp_iff ax hO hE ha hb hc] at h
  rw [hp_iff ax hO hE hb ha hc'] at h'
  exact (Pas.len_eq_iff ax hc hc').1 (by rw [h, h', mul_comm])

/-!
## [s15.mul_assoc] The associative law of multiplication

*(§ 15)*

> In order to show that the *associative* law \[ a(bc)=(ab)c \] holds for the multiplication of segments, we construct first of all the segment $d=be$, then $da$, after that the segment $e=ba$, and finally $ec$. By virtue of Pascal's theorem, the extremities of the segments $da$ and $ec$ coincide, as may be clearly seen from figure 24. … If now we apply the commutative law which we have just demonstrated, we obtain the above formula, which expresses the associative law for the multiplication of two segments.

**Lean reading.** "`d = be`" is a misprint for `d = bc`. `hilbertProd_assoc`: if `d = bc`, `e = ad`,
`f = ab` and `e' = fc`, then `e ≡ e'`, i.e. `a(bc) = (ab)c`. Plane geometry with I 1–2, II, III,
IV; the associativity of the field of segments.

**Status.** proved
-/

theorem hilbertProd_assoc [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L]
    {U1 U2 A1 A2 B1 B2 C1 C2 D1 D2 E1 E2 F1 F2 E1' E2' : P} (hU : U1 ≠ U2) (ha : A1 ≠ A2)
    (hb : B1 ≠ B2) (hc : C1 ≠ C2) (hd : D1 ≠ D2) (he : E1 ≠ E2) (hf : F1 ≠ F2) (he' : E1' ≠ E2')
    (h1 : Pas.HilbertProd (L := L) U1 U2 B1 B2 C1 C2 D1 D2)
    (h2 : Pas.HilbertProd (L := L) U1 U2 A1 A2 D1 D2 E1 E2)
    (h3 : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 F1 F2)
    (h4 : Pas.HilbertProd (L := L) U1 U2 F1 F2 C1 C2 E1' E2') : SegCong E1 E2 E1' E2' := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  rw [hp_iff ax hO hE hb hc hd] at h1
  rw [hp_iff ax hO hE ha hd he] at h2
  rw [hp_iff ax hO hE ha hb hf] at h3
  rw [hp_iff ax hO hE hf hc he'] at h4
  exact (Pas.len_eq_iff ax he he').1 (by rw [h2, h4, h1, h3, mul_assoc])

/-!
## [s15.distrib] The distributive law

*(§ 15)*

> Finally, *the distributive* law \[ a(b+c) = ab+ac \] also holds for our algebra of segments. In order to demonstrate this, we construct the segments, $ab$, $ac$, … From the congruence of the two right-angled triangles which are shaded in the figure and the application of the theorem relating to the equality of the opposite sides of a parallelogram, the desired result follows.

**Lean reading.** `hilbertProd_distrib`: if `s = b + c`, `p = ab`, `q = ac` and `r = as`, then
`r = p + q`. Plane geometry with I 1–2, II, III, IV; the distributivity of the field of segments
(additivity of the slope maps, `Pas.slope_add`).

**Status.** proved
-/

theorem hilbertProd_distrib [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L]
    {U1 U2 A1 A2 B1 B2 C1 C2 S1 S2 P1 P2 Q1 Q2 R1 R2 : P} (hU : U1 ≠ U2) (ha : A1 ≠ A2)
    (hb : B1 ≠ B2) (hc : C1 ≠ C2) (hs : S1 ≠ S2) (hp : P1 ≠ P2) (hq : Q1 ≠ Q2) (hr : R1 ≠ R2)
    (h0 : Pas.SegSum B1 B2 C1 C2 S1 S2) (h1 : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 P1 P2)
    (h2 : Pas.HilbertProd (L := L) U1 U2 A1 A2 C1 C2 Q1 Q2)
    (h3 : Pas.HilbertProd (L := L) U1 U2 A1 A2 S1 S2 R1 R2) : Pas.SegSum P1 P2 Q1 Q2 R1 R2 := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  rw [segSum_iff_len ax hb hc hs] at h0
  rw [hp_iff ax hO hE ha hb hp] at h1
  rw [hp_iff ax hO hE ha hc hq] at h2
  rw [hp_iff ax hO hE ha hs hr] at h3
  rw [segSum_iff_len ax hp hq hr, h3, h0, h1, h2, mul_add]

/-!
## [s15.quotient] The quotient of two segments

*(§ 15)*

> If $b$ and $c$ are any two arbitrary segments, there is always a segment $a$ to be found such that $c=ab$. This segment $a$ is denoted by $\frac{c}{b}$ and is called the *quotient* of $c$ by $b$.

**Lean reading.** `hilbertProd_quotient`: for genuine `b`, `c` there is a genuine `a` with
`c = ab`, unique up to congruence (`hilbertProd_quotient_unique`). Plane geometry with I 1–2, II,
III, IV; `a` has the length `len c / len b`.

**Status.** proved
-/

theorem hilbertProd_quotient [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 B1 B2 C1 C2 : P} (hU : U1 ≠ U2)
    (hb : B1 ≠ B2) (hc : C1 ≠ C2) :
    ∃ A1 A2 : P, A1 ≠ A2 ∧ Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2 := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  have hlb := Pas.len_pos ax hb
  obtain ⟨hne, hl⟩ := seg_of_len ax (div_pos (Pas.len_pos ax hc) hlb)
  refine ⟨ax.O, _, hne, (hp_iff ax hO hE hne hb hc).2 ?_⟩
  rw [hl, div_mul_cancel₀ _ (ne_of_gt hlb)]

theorem hilbertProd_quotient_unique [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 A1 A2 A1' A2' B1 B2 C1 C2 : P}
    (hU : U1 ≠ U2) (ha : A1 ≠ A2) (ha' : A1' ≠ A2') (hb : B1 ≠ B2) (hc : C1 ≠ C2)
    (h : Pas.HilbertProd (L := L) U1 U2 A1 A2 B1 B2 C1 C2)
    (h' : Pas.HilbertProd (L := L) U1 U2 A1' A2' B1 B2 C1 C2) : SegCong A1 A2 A1' A2' := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  rw [hp_iff ax hO hE ha hb hc] at h
  rw [hp_iff ax hO hE ha' hb hc] at h'
  exact (Pas.len_eq_iff ax ha ha').1 (mul_right_cancel₀ (ne_of_gt (Pas.len_pos ax hb))
    (h.symm.trans h'))

/-!
## [s16.free_of_archimedes] Euclid's theory of proportion without Archimedes's axiom

*(§ 16)*

> By aid of the preceding algebra of segments, we can establish Euclid's theory of proportion in a manner free from objections and without making use of the axiom of Archimedes.

**Lean reading.** The units of § 16 assume only I 1–2, II, III, IV of plane geometry; the class
`Archimedes` appears nowhere in them.

**Status.** remark
-/

/-!
## [s16.proportion] Proportion

*(§ 16)*

> If $a,b,a',b'$ are any four segments whatever, the proportion \[ a:b=a':b' \] expresses nothing else than the validity of equation \[ ab'=ba'. \]

**Lean reading.** `SegProportion U₁ U₂ A₁ A₂ B₁ B₂ A₁' A₂' B₁' B₂'` (`a : b = a' : b'` with the unit
`U₁U₂` of § 15): there are segments `p = ab'` and `q = ba'` (Hilbert's products, `HilbertProd`) with
`p ≡ q`. Plane geometry with I 1–2, II, III, IV: `segProportion_iff`, the proportion holds iff
`len a · len b' = len b · len a'` in the field of segments.

**Status.** definition
-/

/-- The **proportion** `a : b = a' : b'` (with the unit segment `U₁U₂`). -/
def SegProportion [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    (U1 U2 A1 A2 B1 B2 A1' A2' B1' B2' : P) : Prop :=
  ∃ C1 C2 D1 D2 : P, C1 ≠ C2 ∧ D1 ≠ D2 ∧ Pas.HilbertProd (L := L) U1 U2 A1 A2 B1' B2' C1 C2 ∧
    Pas.HilbertProd (L := L) U1 U2 B1 B2 A1' A2' D1 D2 ∧ SegCong C1 C2 D1 D2

theorem segProportion_iff [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L)
    {A1 A2 B1 B2 A1' A2' B1' B2' : P} (ha : A1 ≠ A2) (hb : B1 ≠ B2) (ha' : A1' ≠ A2')
    (hb' : B1' ≠ B2') :
    SegProportion (L := L) ax.O ax.E A1 A2 B1 B2 A1' A2' B1' B2' ↔
      Pas.len ax A1 A2 * Pas.len ax B1' B2' = Pas.len ax B1 B2 * Pas.len ax A1' A2' := by
  constructor
  · rintro ⟨C1, C2, D1, D2, hc, hd, h1, h2, s⟩
    rw [hp_iff ax rfl rfl ha hb' hc] at h1
    rw [hp_iff ax rfl rfl hb ha' hd] at h2
    rw [← h1, ← h2]
    exact (Pas.len_eq_iff ax hc hd).2 s
  · intro h
    obtain ⟨hne, hl⟩ := seg_of_len ax (mul_pos (Pas.len_pos ax ha) (Pas.len_pos ax hb'))
    obtain ⟨hne', hl'⟩ := seg_of_len ax (mul_pos (Pas.len_pos ax hb) (Pas.len_pos ax ha'))
    refine ⟨_, _, _, _, hne, hne', (hp_iff ax rfl rfl ha hb' hne).2 hl,
      (hp_iff ax rfl rfl hb ha' hne').2 hl', (Pas.len_eq_iff ax hne hne').1 (by rw [hl, hl', h])⟩

/-!
## [s16.similar] Similar triangles

*(§ 16)*

> Definition. Two triangles are called *similar* when the corresponding angles are congruent.

**Lean reading.** `Similar A B C A' B' C'`: `ABC`, `A'B'C'` are triangles (non-collinear vertices)
and `∠A ≡ ∠A'`, `∠B ≡ ∠B'`, `∠C ≡ ∠C'` (`∠A = ∠BAC`, as in Basic.lean), the vertices corresponding
in the order written.

**Status.** definition
-/

/-- The triangles `ABC` and `A'B'C'` are **similar**. -/
def Similar [HasLines P L] [HasAngCong P] (A B C A' B' C' : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ IsTriangle (Line := L) A' B' C' ∧ AngCong B A C B' A' C' ∧
    AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'

/-!
## [th.22] Theorem 22

*(§ 16)*

> If $a,b$ and $a',b'$ are homologous sides of two similar triangles, we have the proportion \[ a:b=a':b' \]

**Lean reading.** `theorem22`: plane geometry with I 1–2, II, III, IV; for similar triangles
`ABC`, `A'B'C'` and any unit segment `U₁U₂`, the three proportions `AB : AC = A'B' : A'C'`,
`AB : BC = A'B' : B'C'`, `AC : BC = A'C' : B'C'` hold, i.e. every pair of homologous sides (the other
pairs are these with `a`, `b` exchanged, which is the same proportion read backwards). Hilbert
proves the case of right triangles laid off in one right angle (`theorem22_special`) and reduces the
general case to it through the incircles (the angle bisectors meet in a point `S`, the
perpendiculars `r` from `S` cut the sides into the segments `a_b`, `a_c`, …), a construction which he
does not justify (that the bisectors are concurrent and the feet lie on the sides). Here the proof
goes the other way: Theorem 23 is proved first (in co-ordinates over the field of segments), and
Theorem 22 follows by laying off `A'B'`, `A'C'` on the sides of the angle `A` (SAS) and the converse
of Theorem 19 (`Pas.similar_prop`); only two of the three angle congruences are used.

**Status.** proved
-/

/-- **Theorem 22.** -/
theorem theorem22 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 A B C A' B' C' : P} (hU : U1 ≠ U2)
    (h : Similar (L := L) A B C A' B' C') :
    SegProportion (L := L) U1 U2 A B A C A' B' A' C' ∧
      SegProportion (L := L) U1 U2 A B B C A' B' B' C' ∧
      SegProportion (L := L) U1 U2 A C B C A' C' B' C' := by
  obtain ⟨hn, hn', hA, hB, hC⟩ := h
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  subst hO hE
  obtain ⟨hAB, hCB, hAC⟩ := Pas.nc_ne ax hn
  obtain ⟨hAB', hCB', hAC'⟩ := Pas.nc_ne ax hn'
  have nBAC : ¬Collinear (Line := L) B A C := fun hh => hn hh.swap12
  have nBAC' : ¬Collinear (Line := L) B' A' C' := fun hh => hn' hh.swap12
  have nCAB : ¬Collinear (Line := L) C A B := fun hh => hn hh.swap13.swap12
  have nCAB' : ¬Collinear (Line := L) C' A' B' := fun hh => hn' hh.swap13.swap12
  have e1 := Pas.similar_prop ax hn hn' hA hB
  have e2 := Pas.similar_prop ax nBAC nBAC' hB hA
  have hA2 : AngCong C A B C' A' B' :=
    angCong_swap_left nBAC nCAB' (angCong_swap_right nBAC nBAC' hA)
  have e3 := Pas.similar_prop ax nCAB nCAB' hC hA2
  refine ⟨(segProportion_iff ax hAB hAC hAB' hAC').2 e1,
    (segProportion_iff ax hAB (Ne.symm hCB) hAB' (Ne.symm hCB')).2 ?_,
    (segProportion_iff ax hAC (Ne.symm hCB) hAC' (Ne.symm hCB')).2 ?_⟩
  · rw [Pas.len_comm ax A B, Pas.len_comm ax A' B']
    linear_combination e2
  · rw [Pas.len_comm ax A C, Pas.len_comm ax A' C', Pas.len_comm ax B C, Pas.len_comm ax B' C']
    linear_combination e3

/-!
## [s16.special_case] The special case: right triangles in one right angle

*(§ 16)*

> Proof. We shall first consider the special case where the angle included between $a$ and $b$ and the one included between $a'$ and $b'$ are right angles. … Then, according to our definition of the product of two segments, we have \[ b = ea, b' = ea', \] from which we obtain \[ ab'=ba', \] that is to say, \[ a:b=a':b'. \]

**Lean reading.** `theorem22_special`: two right triangles laid off in one right angle `∠X₁OY₁`
(`X₁, X₂` on one side, `Y₁, Y₂` on the other) with parallel (or equal) hypotenuses `X₁Y₁`, `X₂Y₂` have
proportional legs: `OX₁ · OY₂ = OY₁ · OX₂`. Plane geometry with I 1–2, II, III, IV; a special case
of Theorem 23 (`Pas.thales`). Hilbert's `e` (the segment cut off by the parallel through the unit
point) is the common ratio.

**Status.** proved
-/

theorem theorem22_special [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {O X1 X2 Y1 Y2 : P}
    (hr : IsRightAngle (L := L) X1 O Y1) (hX2 : X2 ∈ ray O X1) (hY2 : Y2 ∈ ray O Y1) {l m : L}
    (hX1l : X1 ∈ l) (hY1l : Y1 ∈ l) (hX2m : X2 ∈ m) (hY2m : Y2 ∈ m)
    (hpar : l = m ∨ ¬Meets (Point := P) l m) :
    Pas.len ax O X1 * Pas.len ax O Y2 = Pas.len ax O Y1 * Pas.len ax O X2 :=
  Pas.thales ax hr.1 hX2 hY2 hX1l hY1l hX2m hY2m hpar

/-!
## [th.23] Theorem 23

*(§ 16)*

> If two parallel lines cut from the sides of an arbitrary angle the segments $a,b$ and $a',b'$ respectively, then we have always the proportion \[ a: b = a': b'. \] Conversely, if the four segments $a,b,a',b$ fulfill this proportion and if $a,a'$ and $b,b'$ are laid off upon the two sides respectively of an arbitrary angle, then the straight lines joining the extremities of $a$ and $b$ and of $a'$ and $b'$ are parallel to each other.

**Lean reading.** "`a, b, a', b`" is a misprint for `a, b, a', b'`. Plane geometry with I 1–2, II,
III, IV. The angle is `∠X₁VY₁`; `a = VX₁`, `a' = VX₂` lie on the side `VX₁`, `b = VY₁`, `b' = VY₂` on
the side `VY₁`. `theorem23`: if the lines `X₁Y₁`, `X₂Y₂` are parallel (no common point), then
`a : b = a' : b'` (for any unit segment). `theorem23_converse`: if `a : b = a' : b'`, then the lines
`X₁Y₁`, `X₂Y₂` are parallel **or coincide**, and they coincide iff `a ≡ a'` (then also `b ≡ b'`).
As printed the converse is false in this degenerate case: for `a' = a`, `b' = b` the proportion
holds and the two "straight lines joining the extremities" are one line, not parallel in Hilbert's
sense. Proof (`Pas.thales`): the points of a side are `V + t·u`, `t` the length; two lines are
parallel or equal iff the cross product of their directions vanishes, which for
`X₁Y₁` and `X₂Y₂` is `(a'b - ab')·(u × w)` with `u × w ≠ 0`.

**Status.** proved (corrected)
-/

/-- **Theorem 23**, direct part. -/
theorem theorem23 [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 V0 X1 X2 Y1 Y2 : P} (hU : U1 ≠ U2)
    (hn : ¬Collinear (Line := L) X1 V0 Y1) (hX2 : X2 ∈ ray V0 X1) (hY2 : Y2 ∈ ray V0 Y1) {l m : L}
    (hX1l : X1 ∈ l) (hY1l : Y1 ∈ l) (hX2m : X2 ∈ m) (hY2m : Y2 ∈ m)
    (hpar : Parallel (Point := P) l m) :
    SegProportion (L := L) U1 U2 V0 X1 V0 Y1 V0 X2 V0 Y2 := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  subst hO hE
  obtain ⟨hX1V, hY1V, -⟩ := Pas.nc_ne ax hn
  rw [segProportion_iff ax (Ne.symm hX1V) (Ne.symm hY1V) (Ne.symm (ne_of_mem_ray hX2))
    (Ne.symm (ne_of_mem_ray hY2))]
  exact Pas.thales ax hn hX2 hY2 hX1l hY1l hX2m hY2m (Or.inr hpar)

/-- **Theorem 23**, converse (corrected: the lines may coincide, exactly when `a ≡ a'`). -/
theorem theorem23_converse [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] {U1 U2 V0 X1 X2 Y1 Y2 : P} (hU : U1 ≠ U2)
    (hn : ¬Collinear (Line := L) X1 V0 Y1) (hX2 : X2 ∈ ray V0 X1) (hY2 : Y2 ∈ ray V0 Y1) {l m : L}
    (hX1l : X1 ∈ l) (hY1l : Y1 ∈ l) (hX2m : X2 ∈ m) (hY2m : Y2 ∈ m)
    (h : SegProportion (L := L) U1 U2 V0 X1 V0 Y1 V0 X2 V0 Y2) :
    (Parallel (Point := P) l m ∧ ¬SegCong V0 X1 V0 X2) ∨
      (l = m ∧ SegCong V0 X1 V0 X2 ∧ SegCong V0 Y1 V0 Y2) := by
  obtain ⟨ax, hO, hE⟩ := Pas.exists_axes (L := L) hU
  subst hO hE
  obtain ⟨hX1V, hY1V, hXY⟩ := Pas.nc_ne ax hn
  have hX2V := ne_of_mem_ray hX2
  have hY2V := ne_of_mem_ray hY2
  rw [segProportion_iff ax (Ne.symm hX1V) (Ne.symm hY1V) (Ne.symm hX2V) (Ne.symm hY2V)] at h
  have hp := Pas.thales_converse ax hn hX2 hY2 hX1l hY1l hX2m hY2m h
  by_cases hx : X2 = X1
  · subst hx
    have hl : l = m := by
      rcases hp with e | e
      · exact e
      · exact absurd ⟨X2, hX1l, hX2m⟩ e
    refine Or.inr ⟨hl, segCong_refl (Line := L) (Ne.symm hX1V), ?_⟩
    have hlen : Pas.len ax V0 Y1 = Pas.len ax V0 Y2 :=
      mul_left_cancel₀ (ne_of_gt (Pas.len_pos ax (Ne.symm hX1V))) (by rw [mul_comm]; linear_combination -h)
    exact (Pas.len_eq_iff ax (Ne.symm hY1V) (Ne.symm hY2V)).1 hlen
  · left
    have hlm : l ≠ m := by
      intro e
      subst e
      have hV : V0 ∈ l := mem_of_collinear (collinear_of_mem_ray hX2).swap13 hx hX2m hX1l
      exact hn (collinear_of_mem hX1l hV hY1l)
    refine ⟨hp.resolve_left hlm, fun s => hx ?_⟩
    exact eq_of_segCong_ray (L := L) (Ne.symm hX1V) hX2 (mem_ray_self' (L := L) hX1V) s
      (segCong_refl (Line := L) (Ne.symm hX1V))

/-!
## [s16.fundamental] The fundamental theorem of the theory of proportion

*(§ 16)*

> From the theorem just demonstrated, we can easily deduce the fundamental theorem in the theory of proportion. This theorem may be stated as follows:

**Lean reading.** A remark introducing Theorem 23; in Hilbert's order Theorem 23 is deduced from
Theorem 22, here the order of the proofs is reversed (see `th.22`).

**Status.** remark
-/

/-!
## [s17.signed] Negative segments and the rules of § 13

*(§ 17)*

> To the system of segments already discussed, let us now add a second system. We will distinguish the segments of the new system from those of the former one by means of a special sign, and will call them “*negative*” segments in contradistinction to the “*positive*” segments already considered. If we introduce also the segment $O$, which is determined by a single point, and make other appropriate conventions, then all of the rules deduced in § 13 for calculating with real numbers will hold equally well here for calculating with segments.

**Lean reading.** The signed segments are realized as the points of an axis `x` with origin `O`
and unit point `E` (`Pas.G ax`, the vectors of `x`): the points of the half-ray `OE` are the positive
segments (`Pas.PosG`, the segment `OX`), the points of the opposite half-ray the negative ones, `O`
the segment `0`. The "appropriate conventions" are the addition of vectors (translations) and
Hilbert's construction of the product, which makes sense for points on either side of `O`
(`Pas.mulV`). `signed_segments_laws`: with these operations the laws 1–16 of § 13 hold (and the
asymmetry of `>`), i.e. `Pas.G ax` is an ordered field (`Pas.fieldG`, `Pas.isStrictOrderedRingG`;
laws in the form of Analytic.lean, `laws_of_orderedField`); on positive segments the operations are
those of § 15 (`segment_algebra`). Plane geometry with I 1–2, II, III, IV.

**Status.** proved (reading)
-/

theorem signed_segments_laws [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) :
    Laws1to16 (Pas.G ax) ∧ Law13Asymm (Pas.G ax) :=
  laws_of_orderedField

/-!
## [s17.particular] Particular rules

*(§ 17)*

> We call special attention to the following particular propositions: We have always $a\cdot 1 = 1\cdot a=a$. If $a\cdot b=0$, then either $a=0$, or $b=0$. If $a>b$ and $c>0$, then $ac>bc$.

**Lean reading.** `signed_particular`: in the field of signed segments `Pas.G ax` (plane geometry
with I 1–2, II, III, IV): `a·1 = 1·a = a`; `a·b = 0` implies `a = 0` or `b = 0`; `a > b` and `c > 0`
imply `ac > bc`.

**Status.** proved
-/

theorem signed_particular [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) (a b c : Pas.G ax) :
    (a * 1 = a ∧ 1 * a = a) ∧ (a * b = 0 → a = 0 ∨ b = 0) ∧ (a > b → c > 0 → a * c > b * c) :=
  ⟨⟨mul_one a, one_mul a⟩, fun h => mul_eq_zero.1 h, fun h hc => mul_lt_mul_of_pos_right h hc⟩

/-!
## [s17.coordinates] Rectangular co-ordinates

*(§ 17)*

> In a plane $\alpha$, we now take two straight lines cutting each other in $O$ at right angles as the fixed axes of rectangular co-ordinates, and lay off from $O$ upon these two straight lines the arbitrary segments $x$ and $y$. … The segments $x$ and $y$ are called the co-ordinates of $P$. Every point of the plane $\alpha$ is uniquely determined by its co-ordinates $x$, $y$, which may be positive, negative, or zero.

**Lean reading.** Plane geometry with I 1–2, II, III, IV. The axes are `x = OE` and the
perpendicular `y` at `O` (`Pas.Axes`; they form a right angle, `Pas.axes_right'`), the segment `y`
being laid off on `y` by the rotation `J` (taking `E` to the point `F` of `y`). The co-ordinates of a
point `Z` are `Pas.px ax Z`, `Pas.py ax Z`: `Z = x + J y` in vectors. `perpendicular_coordinate`:
the perpendicular to the axis `x` at its point `x ≠ 0` (the points `Z` off `x` with `∠OxZ` right)
is the set of points with first co-ordinate `x`, which is Hilbert's construction (the second
co-ordinate is the same with the axes exchanged by `J`). `coordinates_bijective`: every point is
uniquely determined by its co-ordinates, and every pair of signed segments is the pair of
co-ordinates of a point.

**Status.** proved
-/

theorem coordinates_bijective [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) :
    Function.Bijective (fun Z : P => (Pas.px ax Z, Pas.py ax Z)) :=
  Pas.coords_bijective ax

theorem perpendicular_coordinate [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {x : Pas.G ax} (hx : x ≠ 0)
    {Z : P} (hZ : Z ∉ ax.x) :
    IsRightAngle (L := L) ax.O (Pas.ofV (x : Pas.V ax)) Z ↔ Pas.px ax Z = x :=
  Pas.perp_iff_px ax hx hZ

/-!
## [s17.line_origin] The equation of a line through the origin

*(§ 17)*

> Let $l$ be a straight line in the plane $\alpha$, such that it shall pass through $O$ and also through a point $C$ having the co-ordinates $a,b$. If $x,y$ are the co-ordinates … of any point on $l$, it follows at once from theorem 22 that \[ a: b = x: y, \] or \[ bx-ay = 0, \] is the equation of the straight line $l$.

**Lean reading.** `line_through_origin_eq`: for `C ≠ O` with co-ordinates `(a, b)` and the line
`l = OC`, a point `Z` lies on `l` iff `b·x - a·y = 0` for its co-ordinates `(x, y)` ("is the
equation": the points of `l` are exactly the solutions). Plane geometry with I 1–2, II, III, IV.
Proof by the cross product (`Pas.mem_line_iff_cross`), not by Theorem 22 (Hilbert's derivation
needs Theorem 22 for the right triangles `O(x,0)Z`, which are similar but not laid off in one right
angle; it also silently covers points on either side of `O`).

**Status.** proved
-/

theorem line_through_origin_eq [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {C : P} (hC : C ≠ ax.O)
    {l : L} (hO : ax.O ∈ l) (hCl : C ∈ l) (Z : P) :
    Z ∈ l ↔ Pas.py ax C * Pas.px ax Z - Pas.px ax C * Pas.py ax Z = 0 :=
  Pas.line_origin_eq ax hC hO hCl Z

/-!
## [s17.parallel_line] The equation of a parallel

*(§ 17)*

> If $l'$ is a straight line parallel to $l$ and cutting off from the $x$-axis the segment $c$, then we may obtain the equation of the straight line $l'$ by replacing, in the equation for $l$, the segment $x$ by the segment $x-c$. The desired equation will then be of the form \[ bx-ay-bc=0. \]

**Lean reading.** `parallel_line_eq'`: if `l' ∥ l` (or `l' = l`) and `l'` passes through the point
`(c, 0)` of the axis `x`, then `Z ∈ l'` iff `b·x - a·y - b·c = 0`. Plane geometry with I 1–2, II,
III, IV. Lines parallel to the axis `x` cut off no segment from it; their equations (`y = const`)
are covered by `lines_are_linear`.

**Status.** proved
-/

theorem parallel_line_eq' [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {C : P} (hC : C ≠ ax.O)
    {l l' : L} (hO : ax.O ∈ l) (hCl : C ∈ l) (c : Pas.G ax) (hc : Pas.mkPt ax c 0 ∈ l')
    (hpar : l = l' ∨ Parallel (Point := P) l l') (Z : P) :
    Z ∈ l' ↔ Pas.py ax C * Pas.px ax Z - Pas.px ax C * Pas.py ax Z - Pas.py ax C * c = 0 :=
  Pas.parallel_line_eq ax hC hO hCl c hc hpar Z

/-!
## [s17.linear] Lines are given by linear equations

*(§ 17)*

> From these considerations, we may easily conclude, independently of the axiom of Archimedes, that every straight line of a plane is represented by an equation which is linear in the co-ordinates $x$, $y$, and, conversely, every such linear equation represents a straight line when the co-ordinates are segments appertaining to the geometry in question.

**Lean reading.** Plane geometry with I 1–2, II, III, IV (no Archimedes). `lines_are_linear`: for
every line `l` there are `a`, `b`, `c` in the field of segments, `a ≠ 0` or `b ≠ 0`, with
`Z ∈ l ↔ a·x + b·y + c = 0`. `linear_eqs_are_lines`: for every such equation there is a line whose
points are exactly its solutions.

**Status.** proved
-/

theorem lines_are_linear [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) (l : L) :
    ∃ a b c : Pas.G ax, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ Z : P, Z ∈ l ↔ a * Pas.px ax Z + b * Pas.py ax Z + c = 0 :=
  Pas.exists_line_eq ax l

theorem linear_eqs_are_lines [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] (ax : Pas.Axes P L) {a b : Pas.G ax}
    (hab : a ≠ 0 ∨ b ≠ 0) (c : Pas.G ax) :
    ∃ l : L, ∀ Z : P, Z ∈ l ↔ a * Pas.px ax Z + b * Pas.py ax Z + c = 0 :=
  Pas.exists_line_of_eq ax hab c

/-!
## [s17.space] Co-ordinates in space

*(§ 17)*

> The corresponding results for the geometry of space may be easily deduced.

**Lean reading.** `SpaceCoordinatesClaim`: for a space geometry with I–IV (`SpaceCongruence`,
`SpaceParallels`) having a plane, there are an ordered field `K` and a bijection of the points onto
`K³` under which the planes are exactly the solution sets of the linear equations
`a x + b y + c z + d = 0`, `(a, b, c) ≠ 0`. (A plane is needed: by the literal reading of I 7 a single
line without planes satisfies the space axioms.) Not proved here: the plane results of this file
apply to plane geometries, and transferring them to space needs the restriction of the congruences
to a plane of space as a plane geometry and the construction of a third axis, which is not carried
out.

**Status.** stated (open here)
-/

/-- **Hilbert's claim** (§ 17): co-ordinates in space, planes given by linear equations. -/
def SpaceCoordinatesClaim : Prop :=
  ∀ (P : Type u) (L : Type v) (Pl : Type u) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceCongruence P L Pl → SpaceParallels P L Pl → Nonempty Pl →
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (f : P ≃ K × K × K), ∀ α : Pl, ∃ a b c d : K, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        ∀ Z : P, Z ∈ α ↔ a * (f Z).1 + b * (f Z).2.1 + c * (f Z).2.2 + d = 0

/-!
## [s17.analytic] Analytic geometry

*(§ 17)*

> The remaining parts of geometry may now be developed by the usual methods of analytic geometry.

**Lean reading.** A programmatic remark; nothing to prove.

**Status.** remark
-/

/-!
## [s17.no_archimedes] Archimedes's axiom has not been used

*(§ 17)*

> So far in this chapter, we have made absolutely no use of the axiom of Archimedes.

**Lean reading.** Checked by the hypotheses: no unit of Pascal.lean or of §§ 15–17 before this one
assumes the class `Archimedes`.

**Status.** remark
-/

/-!
## [s17.reals] With Archimedes's axiom: the points of a line and the real numbers

*(§ 17)*

> If now we assume the validity of this axiom, we can arrange a definite correspondence between the points on any straight line in space and the real numbers. This may be accomplished in the following manner. … From the axiom of Archimedes, we now easily see that, upon the basis of this association, to each arbitrary point of a straight line there corresponds a single, definite, real number, and, indeed, such that this correspondence possesses the following property: If $A$, $B$, $C$ are any three points on a straight line and $\alpha$, $\beta$, $\gamma$ are the corresponding real numbers, and, if $B$ lies between $A$ and $C$, then one of the inequalities, \[ \alpha<\beta<\gamma or \alpha>\beta>\gamma, \] is always fulfilled.

**Lean reading.** `exists_real_correspondence`: plane geometry with I 1–2, II, III, IV and V
(`Archimedes`); for every line `ℓ` there is a map `f` of the points to `ℝ`, one-to-one on `ℓ`, such
that if `B` lies between `A` and `C` (points of `ℓ`) then `f A < f B < f C` or `f A > f B > f C`.
Construction: with axes on `ℓ`, Archimedes's axiom makes the field of segments archimedean
(`Pas.archimedean_G`: the multiples `n·y` of a segment exceed any segment), hence it embeds into `ℝ`
as an ordered field (mathlib's `Real.nonemptyOrderRingHom`), and `f` is this embedding applied to the
co-ordinate on `ℓ`. Hilbert's own construction (the dyadic points `±m/2ⁿ` obtained by bisection,
every point being then determined by the dyadic points on either side) is not followed; the map
built here also sends the point at the distance `m/2ⁿ` (unit `OE`) to the number `m/2ⁿ`, being a
field homomorphism. Departure: "any straight line in space" is read for a plane geometry, i.e. for the lines
of a plane; a space version needs the restriction of the congruences of space to a plane (see
`s17.space`).

**Status.** proved (reading)
-/

/-- **The points of a line correspond to the real numbers** (with Archimedes's axiom). -/
theorem exists_real_correspondence [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] [Archimedes P L] (ℓ : L) :
    ∃ f : P → ℝ, (∀ Z W : P, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      ∀ A B C : P, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A) := by
  obtain ⟨f, h1, h2, -⟩ := Pas.exists_real_coord (P := P) (L := L) ℓ
  exact ⟨f, h1, h2⟩

/-- With Archimedes's axiom the field of segments is archimedean. -/
theorem archimedean_segments [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] [Archimedes P L] (ax : Pas.Axes P L) :
    Archimedean (Pas.G ax) :=
  Pas.archimedean_G ax

/-!
## [s17.omega] The numbers of `Ω` correspond to points

*(§ 17)*

> From the development given in § 9, p. \pageref{folio27}, it is evident, that to every number belonging to the field of algebraic numbers $\Omega$, there must exist a corresponding point upon the straight line.

**Lean reading.** `omega_points`: plane geometry with I–V; for every line `ℓ` the correspondence of
`s17.reals` can be chosen so that every number of Hilbert's field `Ω` (`Omega`, Analytic.lean: the
smallest field of reals closed under `ω ↦ √(1 + ω²)`) is the number of a point of `ℓ`. "The field
of algebraic numbers `Ω`" is Hilbert's `Ω` of § 9 (a field of algebraic numbers, not the field of
all of them). Proof: the image of the field of segments in `ℝ` is a subfield, and it is closed under
`√(1 + w²)` because the field of segments is Pythagorean (`Pas.pythagorean`: the hypotenuse of the
right triangle with legs `1` and `t` has the length `h` with `h² = 1 + t²`, from the identity
`cos² + sin² = 1` of the rotations, `Pas.pyth_rot`); so it contains `Ω` (`Omega_le_of_closed`).

**Status.** proved
-/

theorem omega_points [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [PlaneCongruence P L] [PlaneParallels P L] [Archimedes P L] (ℓ : L) :
    ∃ f : P → ℝ, (∀ Z W : P, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      (∀ A B C : P, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      ∀ ω : ℝ, ω ∈ Omega → ∃ Z : P, Z ∈ ℓ ∧ f Z = ω :=
  Pas.exists_real_coord (P := P) (L := L) ℓ

/-!
## [s17.depends] Whether every real number corresponds to a point depends on the geometry

*(§ 17)*

> Whether to every real number there corresponds a point cannot in general be established, but depends upon the geometry to which we have reference.

**Lean reading.** `real_points_depend`, with the two analytic geometries of § 9 (Analytic.lean),
both satisfying all the plane axioms I–V (`omega_planeGeometry`, `real_planeGeometry`): in the
geometry over `Ω`, for no line `ℓ` and no map `f` of the points to `ℝ` is every real number the image
of a point of `ℓ` (the points are countable, `ℝ` is not); in the geometry over `ℝ`, the line
`y = 0` with the co-ordinate `x` is a one-to-one correspondence with all of `ℝ` having the property
of `s17.reals`. So the axioms I–V do not decide the question.

**Status.** proved
-/

theorem real_points_depend :
    (∀ (ℓ : CoordLine OmegaField 2) (f : Coord OmegaField 2 → ℝ),
      ¬∀ ω : ℝ, ∃ Z : Coord OmegaField 2, Z ∈ ℓ ∧ f Z = ω) ∧
    (∃ (ℓ : CoordLine ℝ 2) (f : Coord ℝ 2 → ℝ),
      (∀ Z W : Coord ℝ 2, Z ∈ ℓ → W ∈ ℓ → f Z = f W → Z = W) ∧
      (∀ A B C : Coord ℝ 2, A ∈ ℓ → B ∈ ℓ → C ∈ ℓ → Between A B C →
        (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      ∀ ω : ℝ, ∃ Z : Coord ℝ 2, Z ∈ ℓ ∧ f Z = ω) := by
  constructor
  · intro ℓ f h
    have hc : Countable (Coord OmegaField 2) :=
      (inferInstance : Countable (Fin 2 → OmegaField))
    have hr : Set.range f = Set.univ := by
      ext ω
      obtain ⟨Z, -, hZ⟩ := h ω
      exact ⟨fun _ => trivial, fun _ => ⟨Z, hZ⟩⟩
    exact Cardinal.not_countable_real (hr ▸ Set.countable_range f)
  · have h1 : (0 : ℝ) ≠ 0 ∨ (1 : ℝ) ≠ 0 := Or.inr one_ne_zero
    set ℓ := Coord.lineOfEq (0 : ℝ) 1 0 h1
    have mem : ∀ Z : Coord ℝ 2, Z ∈ ℓ ↔ Coord.yc Z = 0 := by
      intro Z
      rw [Coord.mem_lineOfEq h1 Z, Coord.lin]
      constructor <;> intro hh <;> linarith
    refine ⟨ℓ, Coord.xc, fun Z W hZ hW h => Coord.ext2 h (by rw [(mem Z).1 hZ, (mem W).1 hW]),
      fun A B C hA hB hC hb => ?_, fun ω => ⟨Coord.pt2 ω 0, (mem _).2 rfl, rfl⟩⟩
    have := (Coord.between_iff_monotone ⟨ℓ, hA, hB, hC⟩).1 hb
    rw [(mem A).1 hA, (mem B).1 hB, (mem C).1 hC] at this
    rcases this with h | h
    · exact h
    · exfalso; rcases h with h | h <;> exact lt_irrefl _ h.1

/-!
## [s17.ideal] Ideal elements: the ordinary analytic geometry of space

*(§ 17)*

> However, it is always possible to generalize the original system of points, straight lines, and planes by the addition of “ideal” or “irrational” elements, so that, upon any straight line of the corresponding geometry, a point corresponds without exception to every system of three real numbers. By the adoption of suitable conventions, it may also be seen that, in this generalized geometry, all of the axioms I–V are valid. This geometry, generalized by the addition of irrational elements, is nothing else than the ordinary analytic geometry of space.

**Lean reading.** "Upon any straight line … to every system of three real numbers" conflates two
statements: on a line a point corresponds to every real number, and in space a point corresponds to
every triple of real numbers. `IdealElementsClaim`: every space geometry with I–V having a plane
has an extension (`SpaceEmbedding`: the old relations are those induced) into the analytic geometry
of space over `ℝ` (`Coord ℝ 3`, which satisfies I–V, `real_spaceGeometry`). Not proved here: it
needs the co-ordinates of space (`s17.space`) and the identification of the congruences with the
euclidean distance and angle of `ℝ³`. What is proved for a plane is the embedding of the field of
segments into `ℝ` (`s17.reals`, `s17.omega`).

**Status.** stated (open here)
-/

/-- **Hilbert's claim** (§ 17): every archimedean geometry of space extends to the analytic geometry
of space over `ℝ`. -/
def IdealElementsClaim : Prop :=
  ∀ (P : Type) (L : Type) (Pl : Type) [HasLines P L] [HasPlanes P Pl] [HasBetween P]
    [HasSegCong P] [HasAngCong P], SpaceGeometry P L Pl → Nonempty Pl →
    Nonempty (SpaceEmbedding P L Pl (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3))

end HilbertFoundations
