import HilbertFoundations.DesarguesAlgebra
import HilbertFoundations.NonPascalAux3

/-!
# Pascal's theorem and non-pascalian geometry (§§ 31–35, Theorems 36–39)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 31. Two theorems concerning the possibility of proving Pascal's theorem
* § 32. The commutative law of multiplication for an archimedean number system
* § 33. The commutative law of multiplication for a non-archimedean number system
* § 34. Proof of the two propositions concerning Pascal's theorem. Non-pascalian geometry.
* § 35. The demonstration, by means of the theorems of Pascal and Desargues, of any theorem relating to points of intersection

## The development (helper modules)

* `NonPascalAux.lean` — the skew Laurent series `SkewLaurent K σ` (series `∑ s^k T_k` with
  coefficients in a division ring `K`, multiplied with `T s = s σ(T)`): ring, division ring (the
  inverse by "equating the like powers of `s`"), ordered division ring (positivity = sign of the
  first coefficient); Hilbert's expressions `T` (`TSeries`, the Laurent series in `t` over `ℚ`),
  the automorphism `T(t) ↦ T(2t)` (`sigma2`) and Hilbert's `Ω(s, t)` (`OmegaST`); the proof of
  Theorem 38 (Hilbert's argument, `not_pos_comm_sub`, `mul_comm_of_archimedean`,
  `theorem38_laws`); the cardinality of `Ω(s, t)`; quaternions with a total relation `<`.
* `NonPascalAux2.lean` — Pascal's theorem as a proposition (`PascalTheorem`); in a plane with
  I 1–2, II, III and the second part of Desargues's theorem, Pascal's theorem holds iff
  dilatations with a common centre commute iff Hilbert's multiplication of segments (§ 24) is
  commutative (`pascal_iff_law12`); segments "equal" by translation (`TrEqual`) and law 17
  (`law17_seg`); Theorem 36 (`theorem36_plane`, `theorem36_space`); the failure of Pascal's
  theorem in the coordinate space over a non-commutative ordered division ring
  (`not_pascal_of_noncomm`, `omega_space_nonpascal`); identities in the co-ordinates (§ 35).
* `NonPascalAux3.lean` — checks added in review: the literal Theorem 21 (without `A ≠ B`) fails in
  the real plane (`not_pascalTheoremLiteral_real`); the reading of axiom V by translations holds in
  the real plane (`archimedesTr_real`), so the hypothesis of Theorem 36 is satisfiable; the
  equation of a line is unique up to a factor (`line_ratio_unique`, § 35).

## How "Pascal's theorem" is read

`NonPascal.PascalTheorem P` (Aux2) is Theorem 21 of § 14 for a plane geometry `(P, L)`: for two
lines `g ≠ h` through `O`, points `A, B, C ∈ g` (pairwise distinct) and `A', B', C' ∈ h`, all
different from `O`, `CB' ∥ BC'` and `CA' ∥ AC'` imply `BA' ∥ AB'`, where `∥` is Hilbert's
parallelism (lines without common point, `DesAlg.ParPts`). The distinctness of `A, B, C` is tacit
in Hilbert ("two sets of points"); without `A ≠ B` the statement is false in every plane (for
`A = B` the hypotheses force `A' = B'` and the conclusion `AA' ∥ AA'` fails), while `B ≠ C`,
`A ≠ C` and the distinctness of `A', B', C'` follow from the hypotheses. The literal statement
(`PascalTheoremLiteral`, without `A ≠ B`, `B ≠ C`, `A ≠ C`) is refuted in Lean in the real plane
(`not_pascalTheoremLiteral_real`, unit `th.36`) and implies `PascalTheorem`
(`pascalTheorem_of_literal`), so the added hypothesis only weakens the statement. The definition is made
here because `Pascal.lean` (Chapter III, with congruence) is not imported. For a space geometry,
"Pascal's theorem holds" means: it holds in every plane `α` (the points `{A // A ∈ α}` and the
lines lying in `α`, the restriction of `Order.lean`).

## How "axiom V without congruence" is read

Axiom V needs a notion of "equal" segments (§ 8). Without the axioms of congruence the only one
available is that of § 24, obtained "by suitable constructions" with parallels: here
`TrEqual L A B A' B'` — a translation (a dilatation without fixed point, built from I and III)
carries `A` to `A'` and `B` to `B'` — and axiom V is `ArchimedesWith P (TrEqual L)` (Basic.lean,
unit `s8.equality`). This is the weakest natural choice (oriented translates only), so the form of
Theorem 36 proved here is the strongest. The reading is not vacuous: in the real plane the
translations are the maps `X ↦ X + v` and axiom V in this form holds (`archimedesTr_real`).
-/

namespace HilbertFoundations

open DesAlg NonPascal

universe u v w

/-!
## [s31.desargues_space] Desargues's theorem from the axioms of space

*(§ 31)*

> As is well known, Desargues's theorem (theorem 32) may be demonstrated by the aid of axioms I, II, III; that is to say, by the use, essentially, of the axioms of space.

**Lean reading.** `desargues_of_space`: in a space geometry satisfying I and III (`SpaceParallels`;
the order axioms are not needed), every plane `α`, with its points and the lines lying in it,
satisfies both parts of Desargues's theorem (`DesarguesTheorem`, Theorem 32). This is
`planes_of_space_desarguesian` of `DesarguesAlgebra.lean` (proof by the spatial argument,
`space_desargues`).

**Status.** proved
-/

theorem desargues_of_space {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [SpaceParallels P L Pl] (α : Pl) :
    DesarguesTheorem {A : P // A ∈ α} :=
  planes_of_space_desarguesian α

/-!
## [s31.desargues_needs_space] Desargues's theorem needs the space axioms

*(§ 31)*

> In § 23, we have shown that the demonstration of this theorem without the aid of the space axioms of group I and without the axioms of congruence (group IV) is impossible, even if we make use of the axiom of Archimedes.

**Lean reading.** A reference to the non-desarguesian geometry of § 23 (Theorem 33), formalized in
`NonDesargues.lean`, which this file does not import. Nothing new is claimed here.

**Status.** remark
-/

/-!
## [s31.pascal_with_congruence] Pascal's and Desargues's theorems from the axioms of congruence

*(§ 31)*

> Upon the basis of axioms I, 1–2, II, III, IV and, hence, by the exclusion of the axioms of space but with the assistance, essentially, of the axioms of congruence, we have, in § 14, deduced Pascal's theorem and, consequently, according to § 22, also Desargues's theorem.

**Lean reading.** A reference to Theorem 21 (§ 14, `Pascal.lean`) and to § 22 (`Desargues.lean`),
which this file does not import; nothing new is claimed. (The plane of § 35 is assumed to satisfy
both theorems, as these sections provide.)

**Status.** remark
-/

/-!
## [s31.question] The influence of the axiom of Archimedes

*(§ 31)*

> The question arises as to whether Pascal's theorem can be demonstrated without the assistance of the axioms of congruence. Our investigation will show that in this respect Pascal's theorem is very different from Desargues's theorem; for, in the demonstration of Pascal's theorem, the admission or exclusion of the axiom of Archimedes is of decided influence.

**Lean reading.** An announcement of Theorems 36 and 37; the contrast with Desargues's theorem is
that Desargues's theorem follows from I, II, III (`desargues_of_space`) with or without V, while
Pascal's theorem follows from I, II, III, V (`theorem36`) but not from I, II, III (`theorem37`).

**Status.** remark
-/

/-!
## [th.36] Theorem 36

*(§ 31)*

> Pascal's theorem (theorem 21) may be demonstrated by means of the axioms I, II, III, V; that is to say, without the assistance of the axioms of congruence and with the aid of the axiom of Archimedes.

**Lean reading.** `theorem36`: in a space geometry with I, II, III (`SpaceOrder`, `SpaceParallels`),
Pascal's theorem (`PascalTheorem`, see the module header) holds in every plane `α` in which axiom V
holds, V being read with the equality of segments of § 24 (`TrEqual`: equal = translates of each
other, see the module header; Hilbert's "without the assistance of the axioms of congruence"
leaves no other equality). Axiom V is assumed in the plane `α` only, since the equality is defined
by constructions in a plane; no congruence relation occurs. The proof is Hilbert's § 34: the
planes are desarguesian (`desargues_of_space`), so the segments of § 24 form a desarguesian number
system (`seg_dns`); V gives law 17 (`law17_seg`); Theorem 38 gives law 12 (`theorem38_laws`); and
law 12 for every frame is Pascal's theorem (`pascal_iff_law12`). The plane form, with Desargues's
theorem in place of the space axioms, is `theorem36_plane` (unit `s31.plane_condition`).

Two checks of the reading. `theorem36_hypothesis_real`: the hypothesis "axiom V for `TrEqual`" is
satisfiable — it holds in the real plane, where every translation is `X ↦ X + v`
(`tr_eq_add_real`), so Theorem 36 is not vacuous. `pascal_literal_false`: Theorem 21 read literally
(without `A ≠ B`) is false in the real plane (`C = (1,0)`, `A = B = (2,0)`, `A' = B' = (0,1)`,
`C' = (0,2)`: the hypotheses hold and `BA'`, `AB'` coincide), so the distinctness in
`PascalTheorem` is a necessary correction of Theorem 21, not a weakening of Theorem 36; and
`pascalTheorem_of_literal` shows that the corrected form is implied by the literal one.

**Status.** proved (reading)
-/

theorem theorem36 {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [SpaceOrder P L Pl] [SpaceParallels P L Pl] (α : Pl) :
    haveI := nonempty_lines_of_plane (P := P) (L := L) α
    ArchimedesWith {A : P // A ∈ α} (TrEqual (P := {A : P // A ∈ α})
      {a : L // LiesInPlane (Point := P) a α}) →
      PascalTheorem {A : P // A ∈ α} (L := {a : L // LiesInPlane (Point := P) a α}) :=
  theorem36_space α

/-- The hypothesis of Theorem 36 (axiom V with the equality by translation) holds in the real
plane: it is not vacuous. -/
theorem theorem36_hypothesis_real :
    haveI := realLine_nonempty
    ArchimedesWith (Coord ℝ 2) (TrEqual (P := Coord ℝ 2) (CoordLine ℝ 2)) :=
  archimedesTr_real

/-- Theorem 21 read literally (without `A ≠ B`) is false: the distinctness is needed. -/
theorem pascal_literal_false : ¬PascalTheoremLiteral (Coord ℝ 2) (L := CoordLine ℝ 2) ∧
    ∀ (P : Type u) (L : Type v) [HasLines P L],
      PascalTheoremLiteral P (L := L) → PascalTheorem P (L := L) :=
  ⟨not_pascalTheoremLiteral_real, fun _ _ _ h => pascalTheorem_of_literal h⟩

/-!
## [th.37] Theorem 37

*(§ 31)*

> Pascal's theorem (theorem 21) cannot be demonstrated by means of the axioms I, II, III alone; that is to say, by exclusion of the axioms of congruence and also the axiom of Archimedes.

**Lean reading.** `theorem37`: there is a space geometry (in `Type`) satisfying I, II, III
(`SpaceOrder`, `SpaceParallels`) with a plane `α` in which Pascal's theorem fails. The model is
Hilbert's (§ 34): the space of § 29 over the desarguesian number system `Ω(s, t)` of § 33, i.e. the
coordinate space `Coord Ω(s,t)ᵐᵒᵖ 3` (numbers acting on the right, as in `dns_space`), whose
axioms come from the ordered-division-ring structure of `Ω(s, t)` (`OmegaST.isStrictOrderedRing`).
Pascal's theorem fails in the plane `z = 0` with the configuration `C = (1, 0)`, `A = (t, 0)`,
`B = (s, 0)`, `A' = (0, 1)`, `C' = (0, t)`, `B' = (0, s⁻¹ t)` (the product taken in
`Ω(s,t)ᵐᵒᵖ`, i.e. `t s⁻¹` in `Ω(s, t)`), because `ts ≠ st` (`not_pascal_of_noncomm`: in the
co-ordinate space over any ordered division ring with two non-commuting numbers `u`, `v`, the
configuration with `t, s` replaced by `u, v` violates Pascal's theorem). The model has no congruence relation at all, and axiom V
fails in it (unit `s34.nonarchimedean`).

**Status.** proved
-/

theorem theorem37 : ∃ (P L Pl : Type) (_ : HasLines P L) (_ : HasPlanes P Pl) (_ : HasBetween P),
    SpaceOrder P L Pl ∧ SpaceParallels P L Pl ∧
      ∃ α : Pl, ¬PascalTheorem {A : P // A ∈ α} (L := {a : L // LiesInPlane (Point := P) a α}) :=
  ⟨Coord OmegaSTᵐᵒᵖ 3, CoordLine OmegaSTᵐᵒᵖ 3, CoordPlane OmegaSTᵐᵒᵖ 3, inferInstance,
    inferInstance, inferInstance, omega_space_nonpascal⟩

/-!
## [s31.plane_condition] Desargues's theorem in place of the space axioms

*(§ 31)*

> In the statement of these two theorems, we may, by virtue of the general theorem 35, replace the space axioms I, 3–7 by the plane condition that Desargues's theorem (theorem 32) shall be valid.

**Lean reading.** The plane forms. `theorem36_plane'`: a plane geometry with I 1–2, II, III
(`PlaneOrder`, `PlaneParallels`), at least one line, the second part of Desargues's theorem (by
`first_part_of_second` equivalent to the whole theorem) and axiom V (equality of § 24) satisfies
Pascal's theorem. `theorem37_plane`: there is a plane geometry with I 1–2, II, III and
Desargues's theorem (both parts) in which Pascal's theorem fails (the plane `α` of `theorem37`,
desarguesian by `desargues_of_space`). Theorem 35 is not needed as a lemma: Desargues's theorem
is exactly what the proof of Theorem 36 uses, and the counterexample is a plane of space.

**Status.** proved
-/

theorem theorem36_plane' {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesTheorem P)
    (hV : ArchimedesWith P (TrEqual (P := P) L)) : PascalTheorem P (L := L) :=
  theorem36_plane hD.2 hV

theorem theorem37_plane : ∃ (P L : Type) (_ : HasLines P L) (_ : HasBetween P),
    PlaneOrder P L ∧ PlaneParallels P L ∧ Nonempty L ∧ DesarguesTheorem P ∧
      ¬PascalTheorem P (L := L) := by
  obtain ⟨-, -, α, hα⟩ := omega_space_nonpascal
  exact ⟨{X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α},
    {a : CoordLine OmegaSTᵐᵒᵖ 3 // LiesInPlane (Point := Coord OmegaSTᵐᵒᵖ 3) a α},
    inferInstance, inferInstance, inferInstance, inferInstance,
    nonempty_lines_of_plane (P := Coord OmegaSTᵐᵒᵖ 3) (L := CoordLine OmegaSTᵐᵒᵖ 3) α,
    desargues_of_space α, hα⟩

/-!
## [s32.intro] Laws of operation and geometry

*(§ 32)*

> The demonstration of theorems 36 and 37 rests essentially upon certain mutual relations concerning the laws of operation and the fundamental propositions of arithmetic, a knowledge of which is of itself of interest.

**Lean reading.** An announcement of Theorems 38 and 39.

**Status.** remark
-/

/-!
## [th.38] Theorem 38

*(§ 32)*

> For an archimedean number system, the commutative law of multiplication is a necessary consequence of the remaining laws of operation; that is to say, if a number system possesses the properties 1–11, 13–17 given in § 13, it follows necessarily that this system satisfies also formula 12.

**Lean reading.** `theorem38`: a type with `+`, `·`, `0`, `1`, `<` satisfying `Law1`–`Law11` and
`Law13`–`Law17` of § 13 (`DesarguesianNumberSystem` and `Law17`), law 13 read with its tacit
asymmetry (`Law13Asymm`), satisfies `Law12`. The proof is Hilbert's (units `s32.*`): the laws make
the system an ordered division ring (`toDivisionRing`, `toLinearOrder`, `isStrictOrderedRing`;
if `0 = 1` the system has one element and is commutative), law 17 is the archimedean property
(`law17_iff_archimedean'`), and `mul_comm_of_archimedean` is Hilbert's argument. Gap in the
statement: the asymmetry cannot be dropped — `quatTotal_laws`: the quaternions over `ℚ` with the
relation `<` true for all pairs satisfy laws 1–11 and 13–17 as printed (13: "one of these is
always greater" holds, both are) but not law 12. So "properties 1–11, 13–17" must include the
asymmetry that the word "the other number is said to be the smaller" presupposes.

**Status.** proved (reading)
-/

theorem theorem38 {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α]
    (h : DesarguesianNumberSystem α) (ha : Law13Asymm α) (h17 : Law17 α) : Law12 α :=
  theorem38_laws h ha h17

/-- The same in the language of ordered division rings. -/
theorem theorem38_divisionRing {D : Type*} [DivisionRing D] [LinearOrder D]
    [IsStrictOrderedRing D] [Archimedean D] (a b : D) : a * b = b * a :=
  mul_comm_of_archimedean a b

/-- Without the asymmetry of law 13 the theorem fails. -/
theorem theorem38_needs_asymmetry : DesarguesianNumberSystem QuatTotal ∧ Law17 QuatTotal ∧
    ¬Law13Asymm QuatTotal ∧ ¬Law12 QuatTotal :=
  quatTotal_laws

/-!
## [s32.integers] Integers commute with every number

*(§ 32)*

> Let us observe first of all that, if $a$ is an arbitrary number of the system, and, if \[ n = 1+1+\cdots+1 \] is a positive integral rational number, then for $n$ and $a$ the commutative law of multiplication always holds.

**Lean reading.** `integers_commute`: with `n = 1 + 1 + ⋯ + 1` (`repeatAdd α 1 k`, `k + 1` terms)
and `a + a + ⋯ + a` (`repeatAdd α a k`), `a n = a + ⋯ + a = n a`, from law 5 and the two
distributive laws 10, 11 only, exactly as Hilbert computes.

**Status.** proved
-/

theorem integers_commute {α : Type*} [Add α] [Mul α] [Zero α] [One α] [LT α] (h5 : Law5 α)
    (h10 : Law10 α) (h11 : Law11 α) (a : α) (k : ℕ) :
    a * repeatAdd α 1 k = repeatAdd α a k ∧ repeatAdd α 1 k * a = repeatAdd α a k := by
  induction k with
  | zero => exact ⟨(h5 a).1, (h5 a).2⟩
  | succ k ih =>
    simp only [repeatAdd]
    rw [h10, h11, ih.1, ih.2, (h5 a).1, (h5 a).2]
    exact ⟨rfl, rfl⟩

/-!
## [s32.reduction] Reduction to positive numbers

*(§ 32)*

> Suppose now, in contradiction to our hypothesis, $a, b$ to be numbers of this system, for which the commutative law of multiplication does not hold. It is then at once evident that we may make the assumption that we have \[ a> 0 \text{, } b > 0 \text{, } ab-ba > 0. \]

**Lean reading.** `exists_pos_comm_sub` (in an ordered division ring): if `a b ≠ b a`, there are
`a, b > 0` with `a b - b a > 0` (replace `a`, `b` by `-a`, `-b` when negative, `0` commutes, and
exchange `a`, `b` if `a b - b a < 0`).

**Status.** proved
-/

theorem reduction_to_positive {D : Type*} [DivisionRing D] [LinearOrder D]
    [IsStrictOrderedRing D] {a b : D} (h : a * b ≠ b * a) :
    ∃ a b : D, 0 < a ∧ 0 < b ∧ 0 < a * b - b * a :=
  exists_pos_comm_sub h

/-!
## [s32.number_c] The number `c`

*(§ 32)*

> By virtue of condition 6 of § 13, there exists a number $c(> 0)$, such that \[ (a+b+1) c = ab-ba. \]

**Lean reading.** `exists_c`: for `a, b > 0` with `a b - b a > 0` there is `c > 0` with
`(a + b + 1) c = a b - b a` (`c = (a + b + 1)⁻¹ (a b - b a)`, law 6; positive by law 16).

**Status.** proved
-/

theorem exists_c {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D] {a b : D}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < a * b - b * a) :
    ∃ c : D, 0 < c ∧ (a + b + 1) * c = a * b - b * a := by
  have h1 : (0 : D) < a + b + 1 := add_pos (add_pos ha hb) one_pos
  exact ⟨(a + b + 1)⁻¹ * (a * b - b * a), mul_pos (inv_pos.2 h1) hD,
    by rw [← mul_assoc, mul_inv_cancel₀ h1.ne', one_mul]⟩

/-!
## [s32.numbers_d_m_n] The numbers `d`, `m`, `n`

*(§ 32)*

> Finally, if we select a number $d$, satisfying simultaneously the inequalities \[ d> 0 \text{, } d < 1 \text{, } d<c, \] and denote by $m$ and $n$ two such integral rational numbers $\ge 0$ that we have respectively \[ md < a \le (m+1) d \] and \[ nd < b \le (n+1) d \] then the existence of the numbers $m$ and $n$ is an immediate consequence of the theorem of Archimedes (theorem 17, § 13).

**Lean reading.** `exists_d`: for `c > 0` there is `d` with `0 < d < 1`, `d < c` (half of
`min c 1`). `exists_floor_mul`: in an archimedean ordered division ring, for `a > 0`, `d > 0` there
is an integer `m ≥ 0` with `m d < a ≤ (m + 1) d` (from Archimedes, via
`existsUnique_sub_zsmul_mem_Ioc`).

**Status.** proved
-/

theorem exists_d {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D] {c : D}
    (hc : 0 < c) : ∃ d : D, 0 < d ∧ d < 1 ∧ d < c := by
  have hhalf : (2 : D)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_two
  have he : 0 < min c 1 := lt_min hc one_pos
  have hde : min c 1 * (2 : D)⁻¹ < min c 1 := by
    have := mul_lt_mul_of_pos_left hhalf he; rwa [mul_one] at this
  exact ⟨min c 1 * (2 : D)⁻¹, mul_pos he (inv_pos.2 two_pos),
    hde.trans_le (min_le_right _ _), hde.trans_le (min_le_left _ _)⟩

theorem exists_m {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [Archimedean D] {a d : D} (ha : 0 < a) (hd : 0 < d) :
    ∃ m : ℤ, 0 ≤ m ∧ (m : D) * d < a ∧ a ≤ ((m + 1 : ℤ) : D) * d :=
  exists_floor_mul ha hd

/-!
## [s32.estimates] Hilbert's estimates

*(§ 32)*

> Recalling now the remark made at the beginning of this proof, we have by the multiplication of the last inequalities \begin{align*} ab &\leqq mnd^2 + (m+n+1)d^2\\ ba &> mnd^2, \end{align*} and, hence, by subtraction \[ ab-ba \leqq (m+n+1)d^2. \]

**Lean reading.** `hilbert_estimates`: from `m d < a ≤ (m + 1) d`, `n d < b ≤ (n + 1) d` (`a, b,
d > 0`, `n ≥ 0`): `a b ≤ m n d² + (m + n + 1) d²`, `b a > m n d²`, and `a b - b a < (m + n + 1) d²`
(strict; Hilbert's `≦` is correct, only not sharp). "The remark made at the beginning" is the commutation of the
integers `m`, `n` with `d` (`Int.cast_comm`, unit `s32.integers`).

**Status.** proved
-/

theorem estimates {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]
    {a b d : D} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) {m n : ℤ} (hn0 : 0 ≤ n)
    (hA1 : (m : D) * d < a) (hA2 : a ≤ ((m + 1 : ℤ) : D) * d) (hB1 : (n : D) * d < b)
    (hB2 : b ≤ ((n + 1 : ℤ) : D) * d) :
    a * b ≤ ((m * n : ℤ) : D) * (d * d) + ((m + n + 1 : ℤ) : D) * (d * d) ∧
      ((m * n : ℤ) : D) * (d * d) < b * a ∧
      a * b - b * a < ((m + n + 1 : ℤ) : D) * (d * d) :=
  hilbert_estimates ha hb hd hn0 hA1 hA2 hB1 hB2

/-!
## [s32.contradiction] The contradiction

*(§ 32)*

> We have, however, \[ md<a \text{, } nd<b, \text{, } d<1 \] and, consequently, \[ (m+n+1)d<a+b+1; \] i.e., \[ ab-ba<(a+b+1)d, \] or, since $d<c$, we have \[ ab-ba<(a+b+1)c. \] This inequality stands in contradiction to the definition of the number $c$, and, hence, the validity of the theorem 38 follows.

**Lean reading.** `hilbert_sum_estimate`: `(m + n + 1) d < a + b + 1`; then
`a b - b a < (m + n + 1) d² < (a + b + 1) d < (a + b + 1) c = a b - b a`
(`not_pos_comm_sub`): in an archimedean ordered division ring `a b - b a` is never positive for
`a, b > 0`, whence Theorem 38 with `reduction_to_positive`.

**Status.** proved
-/

theorem sum_estimate {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]
    {a b d : D} {m n : ℤ} (hA1 : (m : D) * d < a) (hB1 : (n : D) * d < b) (hd1 : d < 1) :
    ((m + n + 1 : ℤ) : D) * d < a + b + 1 :=
  hilbert_sum_estimate hA1 hB1 hd1

theorem comm_sub_not_pos {D : Type*} [DivisionRing D] [LinearOrder D] [IsStrictOrderedRing D]
    [Archimedean D] {a b : D} (ha : 0 < a) (hb : 0 < b) : ¬0 < a * b - b * a :=
  not_pos_comm_sub ha hb

/-!
## [th.39] Theorem 39

*(§ 33)*

> For a non-archimedean number system, the commutative law of multiplication is not a necessary consequence of the remaining laws of operation; that is to say, there exists a system of numbers possessing the properties 1–11, 13–16 mentioned in § 13, but for which the commutative law (12) of multiplication is not valid. A desarguesian number system, in the sense of § 28, is such a system.

**Lean reading.** `theorem39`: there is a number system (in `Type`) satisfying laws 1–11 and 13–16
(`DesarguesianNumberSystem`, the asymmetry of 13, `0 ≠ 1`) in which law 12 fails, and law 17 fails
too ("for a non-archimedean number system"): Hilbert's `Ω(s, t)` (`OmegaST`, units `s33.*`). The
last sentence is read as: the example is a desarguesian number system in the sense of § 28 (by
definition, the laws 1–11, 13–16), which `OmegaST.dns` states. It is moreover an ordered division
ring in mathlib's sense (`OmegaST.isStrictOrderedRing`).

**Status.** proved (reading)
-/

theorem theorem39 : ∃ (α : Type) (_ : Add α) (_ : Mul α) (_ : Zero α) (_ : One α) (_ : LT α),
    DesarguesianNumberSystem α ∧ Law13Asymm α ∧ (0 : α) ≠ 1 ∧ ¬Law12 α ∧ ¬Law17 α :=
  ⟨OmegaST, _, _, _, _, _, OmegaST.dns.1, OmegaST.dns.2.1, OmegaST.dns.2.2, OmegaST.not_law12,
    OmegaST.not_law17⟩

/-!
## [s33.expressions_T] The expressions `T`

*(§ 33)*

> Proof. Let $t$ be a parameter and $T$ any expression containing a finite or infinite number of terms, say of the form \[ T=r_0t^n + r_1t^{n+1} + r_2t^{n+2} + r_3t^{n+3} + \ldots, \] where $r_0(\neq 0), r_1, r_2 \ldots$ are arbitrary rational numbers and $n$ is an arbitrary integral rational number $\gtreqqless 0$.

**Lean reading.** `TSeries = SkewLaurent ℚ 1`: the families `(r_k)_{k ∈ ℤ}` of rationals vanishing
below some exponent (mathlib's `HahnSeries ℤ ℚ`, the formal Laurent series in `t`); the expression
`T` with `r₀ ≠ 0` at `tⁿ` is the series whose lowest non-zero coefficient is at `n`, and `0` is the
empty expression. With `σ = 1` the multiplication is the usual one of Laurent series, commutative
(`SkewLaurent.mul_comm_of_one`); `TSeries.isStrictOrderedRing`: ordered by the sign of the first
coefficient.

**Status.** definition
-/

theorem tSeries_def : TSeries = SkewLaurent ℚ 1 := rfl

theorem tSeries_mul_comm (x y : TSeries) : x * y = y * x := SkewLaurent.mul_comm_of_one x y

/-!
## [s33.expressions_S] The expressions `S` and the system `Ω(s, t)`

*(§ 33)*

> Moreover, let $s$ be another parameter and $S$ any expression having a finite or infinite number of terms, say of the form \begin{equation*} S = s^mT_0 + s^{m+1}T_1 + s^{m+2}T_2 + \ldots , \end{equation*} where $T_0 (\ne 0), T_1, T_2, \ldots $ denote arbitrary expressions of the form $T$ and $m$ is again an arbitrary integral rational number $\lesseqqgtr 0$. We will regard the totality of all the expressions of the form $S$ as a complex number system $\Omega(s,\!t)$, …

**Lean reading.** `OmegaST = SkewLaurent TSeries sigma2`: the families `(T_k)_{k ∈ ℤ}` of
expressions `T` vanishing below some exponent, `S = ∑ s^k T_k` with the coefficients written on the
right as in Hilbert's `s^m T₀`. `OmegaST.single_eq`: the element with the single coefficient `T` at
`k` is the product `s^k T` of the power `s^k` of `s = OmegaST.s` and the number `T`, so the notation
`s^k T_k` is the product in `Ω(s, t)`. "Finite or infinite": all such families, not only finite
sums.

**Status.** definition
-/

theorem omegaST_def : OmegaST = SkewLaurent TSeries sigma2 := rfl

theorem omegaST_term (k : ℤ) (T : TSeries) :
    (SkewLaurent.single k T : OmegaST) = OmegaST.s ^ k * SkewLaurent.single 0 T :=
  OmegaST.single_eq k T

/-!
## [s33.formula_1] The rule `t s = 2 s t`

*(§ 33)*

> … for which we will assume the following laws of operation; namely, we will operate with $s$ and $t$ according to the laws 7–11 of § 13, as with parameters, while in place of rule 12 we will apply the formula \begin{equation} ts = 2st. \end{equation}

**Lean reading.** The multiplication of `Ω(s, t)` is that of the skew series with
`σ = sigma2 : T(t) ↦ T(2t)`, i.e. `T s = s T(2t)`; `OmegaST.t_mul_s`: formula (1), `t s = 2 s t`,
for `t = OmegaST.t` (the expression `T = t`) and `s = OmegaST.s`. Laws 7–11 are those of the ring
`OmegaST` (unit `s33.laws_1_5`). Formula (1) and laws 7–11 determine the product of two terms:
`(s^i T)(s^j T') = s^{i+j} T(2^j t) T'` (`SkewLaurent.single_mul_single`, unit `s33.product`).

**Status.** proved
-/

theorem formula_1 : OmegaST.t * OmegaST.s = 2 * (OmegaST.s * OmegaST.t) := OmegaST.t_mul_s

/-!
## [s33.sum] The sum

*(§ 33)*

> If, now, $S'$, $S''$ are any two expressions of the form $S$, say … then, by combination, we can evidently form a new expression $S'+S''$ which is of the form $S$, and is, moreover, uniquely determined. This expression $S' + S''$ is called the sum of the numbers represented by $S'$ and $S''$.

**Lean reading.** The sum is coefficientwise (`SkewLaurent.coeff_add`), the sum of two families
vanishing below some exponent again vanishes below some exponent (it is the sum of mathlib's
Hahn series). Uniqueness is built into the encoding (an operation is a function).

**Status.** definition
-/

theorem sum_coeff (S' S'' : OmegaST) (k : ℤ) : (S' + S'').coeff k = S'.coeff k + S''.coeff k :=
  SkewLaurent.coeff_add S' S'' k

/-!
## [s33.product] The product

*(§ 33)*

> By the multiplication of the two expressions $S'$ and $S''$ term by term, we obtain another expression of the form … This expression, by the aid of formula (1), is evidently a definite single-valued expression of the form $S$ and we will call it the product of the numbers represented by $S'$ and $S''$.

**Lean reading.** The coefficient of `s^n` in `S' S''` is the finite sum of the products of terms
`(s^i T'_i)(s^j T''_j) = s^{i+j} T'_i(2^j t) T''_j` with `i + j = n` (`SkewLaurent.coeff_mul_Icc`:
finitely many terms, since both families vanish below some exponent). `product_of_terms` is the
rule for two terms, which uses formula (1) (`T s^j = s^j T(2^j t)`).

**Status.** definition
-/

theorem product_of_terms (i j : ℤ) (T' T'' : TSeries) :
    (SkewLaurent.single i T' * SkewLaurent.single j T'' : OmegaST) =
      SkewLaurent.single (i + j) ((sigma2 ^ j) T' * T'') :=
  SkewLaurent.single_mul_single i j T' T''

theorem product_coeff {S' S'' : OmegaST} {a b : ℤ} (h' : ∀ k < a, S'.coeff k = 0)
    (h'' : ∀ k < b, S''.coeff k = 0) (n : ℤ) :
    (S' * S'').coeff n =
      ∑ i ∈ Finset.Icc a (n - b), (sigma2 ^ (n - i)) (S'.coeff i) * S''.coeff (n - i) :=
  SkewLaurent.coeff_mul_Icc h' h'' n

/-!
## [s33.laws_1_5] Laws 1–5 (and 7–11)

*(§ 33)*

> This method of calculation shows at once the validity of the laws 1–5 given in Section 13 for calculating with numbers.

**Lean reading.** `omega_laws_1_5`: laws 1–5 hold in `Ω(s, t)`, and with them the laws 7–11 which
Hilbert prescribes "as with parameters" (associativity of the product is the cocycle identity
`σ^{j}σ^{l} = σ^{j+l}`, `SkewLaurent.mul_assoc'`).

**Status.** proved
-/

theorem omega_laws_1_5 : Law1 OmegaST ∧ Law2 OmegaST ∧ Law3 OmegaST ∧ Law4 OmegaST ∧
    Law5 OmegaST ∧ Law7 OmegaST ∧ Law8 OmegaST ∧ Law9 OmegaST ∧ Law10 OmegaST ∧
    Law11 OmegaST := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11, -⟩ := OmegaST.dns.1
  exact ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10, h11⟩

/-!
## [s33.law_6] Law 6

*(§ 33)*

> The validity of law 6 of that section is also not difficult to establish. … By equating the like powers of $s$ in the two members of the equation \[ S'S''=S''', \] we find, first of all, in a definite manner an integral number $m''$ as exponent, and then such a succession of expressions \[ T''_0 \text{, } T''_1 \text{, } T''_2 \ldots \] that, by aid of formula (1), the expression \[ S''=s^{m''}T''_0+s^{m''+1}T''_1+s^{m''+2}T''_2 \dots \] satisfies equation (2). With this our theorem is established.

**Lean reading.** `right_inverse`: for `S' ≠ 0` with lowest term `s^m T'_m` the series
`rinv S' m`, whose coefficients `T''_k` are found successively from the equations "coefficient of
`s^n` in `S' S''` = coefficient of `s^n` in `1`" (`SkewLaurent.invSeq`, `invSeq_spec`: each step
divides by `T'_m(2^{…} t) ≠ 0`, possible because the expressions `T` form a field), satisfies
`S' · rinv S' m = 1`; then `S'' = rinv S' m · S'''` solves `S' S'' = S'''` (`right_division`). Law 6 as stated in
§ 13 also asks for `y S' = S'''` and for uniqueness, which Hilbert does not discuss; they follow
since a ring in which every non-zero element has a right inverse is a division ring
(`omega_law6`). Hilbert's "first coefficient `r'₀` of `T'₀`" is the condition `S' ≠ 0`.

**Status.** proved
-/

theorem right_inverse {S' : OmegaST} {m : ℤ} (hlow : ∀ k < m, S'.coeff k = 0)
    (hm : S'.coeff m ≠ 0) : S' * SkewLaurent.rinv S' m = 1 :=
  SkewLaurent.mul_rinv hlow hm

theorem right_division {S' : OmegaST} {m : ℤ} (hlow : ∀ k < m, S'.coeff k = 0)
    (hm : S'.coeff m ≠ 0) (S''' : OmegaST) : S' * (SkewLaurent.rinv S' m * S''') = S''' := by
  rw [← mul_assoc, right_inverse hlow hm, one_mul]

theorem omega_law6 : Law6 OmegaST := OmegaST.dns.1.law6

/-!
## [s33.order] The order of `Ω(s, t)`; laws 13–16

*(§ 33)*

> In order, finally, to render possible an order of sequence of the numbers of our system $\Omega(s, t)$, we make the following conventions. Let a number of this system be called greater or less than 0 according as in the expression $S$, which represents it, the first coefficient $r_0$ of $T_0$ is greater or less than zero. Given any two numbers $a$, $b$ of the complex number system under consideration, we say that $a<b$ or $a>b$ according as … we have $a-b < 0$ or $> 0$. It is seen immediately that, with these conventions, the laws 13–16 of § 13 are valid; that is to say, $\Omega (s, t)$ is a desarguesian number system (see § 28).

**Lean reading.** The order of `OmegaST` is the lexicographic order of the coefficients
(mathlib's order on `Lex (HahnSeries ℤ TSeries)`), and that of `TSeries` the lexicographic order
of the rationals `r_k`. `omega_pos_iff` is Hilbert's convention: `S > 0` iff the first non-zero
coefficient `T₀` is positive, i.e. iff the first coefficient `r₀` of `T₀` is positive
(`tSeries_pos_iff`); `a < b` iff `b - a > 0` (`sub_pos`). `OmegaST.dns`: laws 1–11 and 13–16 hold
(with the asymmetry of 13 and `0 ≠ 1`), so `Ω(s, t)` is a desarguesian number system. Law 16 holds
because `T(t) ↦ T(2t)` preserves signs (`sigma2_pos_iff`).

**Status.** proved
-/

theorem omega_pos_iff (S : OmegaST) :
    0 < S ↔ ∃ m, (∀ k < m, S.coeff k = 0) ∧ 0 < S.coeff m :=
  SkewLaurent.pos_iff S

theorem tSeries_pos_iff (T : TSeries) :
    0 < T ↔ ∃ n, (∀ k < n, T.coeff k = 0) ∧ 0 < T.coeff n :=
  SkewLaurent.pos_iff T

theorem omegaST_lt_iff (a b : OmegaST) : a < b ↔ 0 < b - a := sub_pos.symm

theorem omega_dns : DesarguesianNumberSystem OmegaST ∧ Law13Asymm OmegaST ∧ (0 : OmegaST) ≠ 1 :=
  OmegaST.dns

/-!
## [s33.not_commutative] Law 12 fails in `Ω(s, t)`

*(§ 33)*

> As equation (1) shows, law 12 of § 13 is not fulfilled by our complex number system and, consequently, the validity of theorem 39 is fully established.

**Lean reading.** `OmegaST.t_mul_s_ne`: `t s ≠ s t`, since `t s = 2 s t` and `s t ≠ 0`.

**Status.** proved
-/

theorem omega_not_law12 : OmegaST.t * OmegaST.s ≠ OmegaST.s * OmegaST.t ∧ ¬Law12 OmegaST :=
  ⟨OmegaST.t_mul_s_ne, OmegaST.not_law12⟩

/-!
## [s33.not_archimedean] Law 17 fails in `Ω(s, t)`

*(§ 33)*

> In conformity with theorem 38, Archimedes's theorem (theorem 17, § 13) does not hold for the number system $\Omega (s, t)$ which we have just constructed.

**Lean reading.** Both ways: `omega_not_law17_of_theorem38` derives it from Theorem 38 (law 17
would give law 12); `OmegaST.not_law17` directly: `s > 0` and `n s < 1` for every natural `n`
(`OmegaST.nsmul_s_lt_one`), `s` is infinitely small.

**Status.** proved
-/

theorem omega_not_law17_of_theorem38 : ¬Law17 OmegaST := fun h =>
  OmegaST.not_law12 (theorem38 OmegaST.dns.1 OmegaST.dns.2.1 h)

theorem omega_s_infinitesimal (n : ℕ) : 0 < OmegaST.s ∧ n • OmegaST.s < 1 :=
  ⟨OmegaST.s_pos, OmegaST.nsmul_s_lt_one n⟩

/-!
## [s33.enumerable] Enumerability

*(§ 33)*

> We wish also to call attention to the fact that the number system $\Omega (s, t)$, as well as the systems $\Omega$ and $\Omega (t)$ made use of in § 9 and § 12, respectively, contains only an enumerable set of numbers.

**Lean reading.** False for `Ω(s, t)` as defined: the expressions `T` with infinitely many terms
already form a non-enumerable set (`tSeries_not_countable`: the series `∑_{n ∈ A} tⁿ`, `A ⊆ ℕ`,
are pairwise different, and there are non-enumerably many sets `A`), and they are numbers of
`Ω(s, t)` (`omegaST_not_countable`). The claim is true for `Ω` (`OmegaField.instCountable`,
Analytic.lean) and for `Ω(t)` (proved in `Independence.lean`, unit of § 12, not imported here).
Corrected statement: the sub-system generated by `s` and `t` (the division ring `omegaST₀`, the
closure of `{s, t}` under the four operations) is enumerable (`omegaST₀_countable`) and is a
non-commutative, non-archimedean desarguesian number system (`omegaST₀_dns`), so Theorem 39 holds
with an enumerable system, which is presumably what Hilbert had in mind (the expressions obtained
from `s`, `t` by the rational operations).

**Status.** proved (corrected)
-/

theorem omega_st_uncountable : ¬Countable TSeries ∧ ¬Countable OmegaST :=
  ⟨tSeries_not_countable, omegaST_not_countable⟩

theorem omega_countable : Countable OmegaField := inferInstance

theorem omegaST₀_dns : Countable omegaST₀ ∧ DesarguesianNumberSystem omegaST₀ ∧
    Law13Asymm omegaST₀ ∧ (0 : omegaST₀) ≠ 1 ∧ ¬Law12 omegaST₀ ∧ ¬Law17 omegaST₀ :=
  ⟨omegaST₀_countable, (OmegaST.laws_of_sub _).1, (OmegaST.laws_of_sub _).2.1,
    (OmegaST.laws_of_sub _).2.2, omegaST₀_not_law12, omegaST₀_not_law17⟩

/-!
## [s34.segment_algebra] The algebra of segments of a geometry with I, II, III

*(§ 34)*

> If, in a geometry of space, all of the axioms I, II, III are fulfilled, then Desargues's theorem (theorem 32) is also valid, and, consequently, according to \S§ 24–26, pp. \pageref{folio79}–\pageref{folio89}, it is possible to introduce into this geometry an algebra of segments for which the rules 1–11, 13–16 of § 13 are all valid.

**Lean reading.** `space_segment_algebra`: for a space geometry with I, II, III, every plane `α`
and every frame `F` of `α` (the fixed lines `OE`, `OE'` of § 24), the segments of § 24 form a
desarguesian number system (laws 1–11, 13–16, with the asymmetry of 13): `desargues_of_space` and
`seg_dns`.

**Status.** proved
-/

theorem space_segment_algebra {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [SpaceOrder P L Pl] [SpaceParallels P L Pl] (α : Pl)
    (F : Frame {A : P // A ∈ α}) :
    haveI := nonempty_lines_of_plane (P := P) (L := L) α
    DesarguesianNumberSystem (DesAlg.Seg (L := {a : L // LiesInPlane (Point := P) a α}) F) ∧
      Law13Asymm (DesAlg.Seg (L := {a : L // LiesInPlane (Point := P) a α}) F) := by
  have := nonempty_lines_of_plane (P := P) (L := L) α
  exact seg_dns (desargues_of_space α).2 F

/-!
## [s34.archimedes] Archimedes's axiom gives law 17 for the segments

*(§ 34)*

> If we assume now that the axiom (V) of Archimedes is valid for our geometry, then evidently Archimedes's theorem (theorem 17 of § 13) also holds for our algebra of segments, …

**Lean reading.** `archimedes_law17`: in a plane with I 1–2, II, III and the second part of
Desargues's theorem, axiom V with the equality of § 24 (`TrEqual`) gives law 17 for the segments of
every frame (`law17_seg`). For `0 < y < x` the points `A_k = k y` of `OE` satisfy the hypotheses of
V: `A_1` lies between `A_0 = O` and `x`, `A_{k+1}` between `A_k` and `A_{k+2}` (the order of the
segments is that of the line, `Seg.between_iff`), and `A_m A_{m+1}`, `A_n A_{n+1}` are translates
of each other (the translation `O ↦ n y - m y`, which is the addition of segments by
`hsumPt_eq`); V then gives `x < k y`. "Evidently" hides this identification of the sum of
segments with a translation, which needs the second part of Desargues's theorem.

**Status.** proved (reading)
-/

theorem archimedes_law17 {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) (F : Frame P)
    (hV : ArchimedesWith P (TrEqual (P := P) L)) : Law17 (DesAlg.Seg F) :=
  haveI : Fact (DesarguesII P) := ⟨hD⟩
  law17_seg F hV

/-!
## [s34.commutative] Hence the commutative law

*(§ 34)*

> … and, consequently, by virtue of theorem 38, the commutative law of multiplication is valid.

**Lean reading.** `archimedes_law12`: under the hypotheses of `archimedes_law17`, law 12 holds for
the segments: Theorem 38 applied to the desarguesian number system of the segments (`seg_dns`).

**Status.** proved
-/

theorem archimedes_law12 {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) (F : Frame P)
    (hV : ArchimedesWith P (TrEqual (P := P) L)) : Law12 (DesAlg.Seg F) :=
  theorem38 (seg_dns hD F).1 (seg_dns hD F).2 (archimedes_law17 hD F hV)

/-!
## [s34.pascal_is_commutativity] The commutative law is Pascal's theorem

*(§ 34)*

> Since, however, the definition of the product of two segments, as introduced in § 24 (figure 42) and which is the definition here also under discussion, agrees with the definition in § 15 (figure 22), it follows from the construction made in § 15 that the commutative law of multiplication is here nothing else than Pascal's theorem. Consequently, the validity of theorem 36 is established.

**Lean reading.** `pascal_iff_commutative`: in a plane with I 1–2, II 1–4, III and the second part
of Desargues's theorem, Pascal's theorem holds iff the multiplication of segments of § 24 is
commutative for every frame (`pascal_iff_law12`). The proof makes Hilbert's Fig. 23 precise with
dilatations: the product `a b` is the image of `a` under the dilatation with centre `O` mapping `E`
to `b` (`hmulPt_eq`), so commutativity for the frames with origin `O` is the commutativity of the
dilatations with centre `O`, and a Pascal configuration with centre `O` is exactly the statement
that two such dilatations `δ : C ↦ B`, `ε : C ↦ A` satisfy `ε δ⁻¹ = δ⁻¹ ε` on the second line
(`pascal_of_centreComm`, `centreComm_of_pascal`). Hilbert only uses "commutative ⇒ Pascal"; both
directions are proved, for all frames since Pascal's theorem concerns all centres. With
`archimedes_law12` this gives Theorem 36 (`theorem36_plane'`, `theorem36`).

**Status.** proved
-/

theorem pascal_iff_commutative {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [LineOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) :
    PascalTheorem P (L := L) ↔ ∀ F : Frame P, Law12 (DesAlg.Seg F) :=
  pascal_iff_law12 hD

/-!
## [s34.nonpascal_geometry] The non-pascalian geometry

*(§ 34)*

> In order to demonstrate theorem 37, let us consider again the desarguesian number system $\Omega(s, t)$ introduced in $\S$ 33, and construct, in the manner described in $\S$ 29, a geometry of space for which all of the axioms I, II, III are fulfilled. However, Pascal's theorem will not hold for this geometry; for, the commutative law of multiplication is not valid in the desarguesian number system $\Omega(s, t)$.

**Lean reading.** `nonpascal_geometry`: the space of § 29 over `Ω(s, t)` (`Coord Ω(s,t)ᵐᵒᵖ 3`,
the model of `dns_space`) satisfies `SpaceOrder` and `SpaceParallels`, and Pascal's theorem fails in
one of its planes. The failure is derived from the non-commutativity directly in co-ordinates
(`not_pascal_of_noncomm`: a configuration built on two non-commuting numbers), not through the
algebra of segments of that plane; by `pascal_iff_commutative` the segments of that plane then do
not commute either.

**Status.** proved
-/

theorem nonpascal_geometry :
    SpaceOrder (Coord OmegaSTᵐᵒᵖ 3) (CoordLine OmegaSTᵐᵒᵖ 3) (CoordPlane OmegaSTᵐᵒᵖ 3) ∧
      SpaceParallels (Coord OmegaSTᵐᵒᵖ 3) (CoordLine OmegaSTᵐᵒᵖ 3) (CoordPlane OmegaSTᵐᵒᵖ 3) ∧
      ∃ α : CoordPlane OmegaSTᵐᵒᵖ 3, ¬PascalTheorem {X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α}
        (L := {a : CoordLine OmegaSTᵐᵒᵖ 3 // LiesInPlane (Point := Coord OmegaSTᵐᵒᵖ 3) a α}) :=
  omega_space_nonpascal

/-!
## [s34.nonarchimedean] The non-pascalian geometry is non-archimedean

*(§ 34)*

> According to theorem 36, the non-pascalian geometry is then necessarily also a non-archimedean geometry.

**Lean reading.** `nonpascal_nonarchimedean`: in the plane `α` of `nonpascal_geometry` where
Pascal's theorem fails, axiom V (with the equality of § 24) fails, by Theorem 36 (`theorem36`).

**Status.** proved
-/

theorem nonpascal_nonarchimedean : ∃ α : CoordPlane OmegaSTᵐᵒᵖ 3,
    haveI := nonempty_lines_of_plane (P := Coord OmegaSTᵐᵒᵖ 3) (L := CoordLine OmegaSTᵐᵒᵖ 3) α
    ¬PascalTheorem {X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α}
        (L := {a : CoordLine OmegaSTᵐᵒᵖ 3 // LiesInPlane (Point := Coord OmegaSTᵐᵒᵖ 3) a α}) ∧
      ¬ArchimedesWith {X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α} (TrEqual (P := {X : Coord OmegaSTᵐᵒᵖ 3 // X ∈ α})
        {a : CoordLine OmegaSTᵐᵒᵖ 3 // LiesInPlane (Point := Coord OmegaSTᵐᵒᵖ 3) a α}) := by
  obtain ⟨-, -, α, hα⟩ := omega_space_nonpascal
  exact ⟨α, hα, fun hV => hα (theorem36 α hV)⟩

/-!
## [s34.any_dimension] Not even in a geometry of any number of dimensions

*(§ 34)*

> By adopting the hypothesis we have, it is evident that we cannot demonstrate Pascal's theorem, providing we regard our geometry of space as a part of a geometry of an arbitrary number of dimensions in which, besides the points, straight lines, and planes, still other linear elements are present, and providing there exists for these elements a corresponding system of axioms of connection and of order, as well as the axiom of parallels.

**Lean reading.** As in unit `s30.any_dimension`, "a geometry of an arbitrary number of dimensions"
is read as the coordinate geometry `Ω(s,t)ᵐᵒᵖⁿ` over the same ordered division ring (`n ≥ 3`), whose
linear elements are the affine subspaces. `nonpascal_any_dimension`: the non-pascalian space is a
part of it for every `n ≥ 3` (injective on points, betweenness preserved and reflected, lines and
planes going to affine subspaces of dimension 1 and 2: `coordinate_space_any_dimension`), so the
higher-dimensional axioms of connection, order and parallels (which hold in the coordinate
geometry over any ordered division ring) do not give Pascal's theorem either. An axiom system for
`n` dimensions is not formalized; the reading replaces it by its standard model.

**Status.** proved (reading)
-/

theorem nonpascal_any_dimension {n : ℕ} (hn : 3 ≤ n) :
    ∃ f : Coord OmegaSTᵐᵒᵖ 3 → AffPt OmegaSTᵐᵒᵖ (Fin n → OmegaSTᵐᵒᵖ), Function.Injective f ∧
      (∀ A B C : Coord OmegaSTᵐᵒᵖ 3, Between A B C ↔ Sbtw OmegaSTᵐᵒᵖ (f A) (f B) (f C)) ∧
      (∀ l : CoordLine OmegaSTᵐᵒᵖ 3, ∃ S : AffineSubspace OmegaSTᵐᵒᵖ
          (AffPt OmegaSTᵐᵒᵖ (Fin n → OmegaSTᵐᵒᵖ)),
        Module.finrank OmegaSTᵐᵒᵖ S.direction = 1 ∧ ∀ X : Coord OmegaSTᵐᵒᵖ 3, X ∈ l ↔ f X ∈ S) ∧
      (∀ π : CoordPlane OmegaSTᵐᵒᵖ 3, ∃ S : AffineSubspace OmegaSTᵐᵒᵖ
          (AffPt OmegaSTᵐᵒᵖ (Fin n → OmegaSTᵐᵒᵖ)),
        Module.finrank OmegaSTᵐᵒᵖ S.direction = 2 ∧ ∀ X : Coord OmegaSTᵐᵒᵖ 3, X ∈ π ↔ f X ∈ S) :=
  coordinate_space_any_dimension hn

/-!
## [s35.form] The form of a proposition about points of intersection

*(§ 35)*

> Every proposition relating to points of intersection in a plane has necessarily The form: Select, first of all, an arbitrary system of points and straight lines satisfying respectively the condition that certain ones of these points are situated on certain ones of the straight lines. If, in some known manner, we construct the straight lines joining the given points and determine the points of intersection of the given lines, we shall obtain finally a definite system of three straight lines, of which our proposition asserts that they all pass through the same point.

**Lean reading.** A description, not a theorem. It is not formalized as a syntax of constructions;
the units below formalize Hilbert's argument through its algebraic core, the co-ordinate
expression `A(p₁, …, p_r)` of such a proposition (units `s35.identity`, `s35.conclusion`).

**Status.** remark
-/

/-!
## [s35.real_coordinates] Real co-ordinates in an archimedean plane

*(§ 35)*

> Suppose we now have a plane geometry in which all of the axioms I 1–2, II \ldots, V are valid. According to $\S$ 17, pp. \pageref{folio53}–\pageref{folio56}, we may now find, by making use of a rectangular pair of axes, for each point a corresponding pair of numbers $(x,y)$ and for each straight line a ratio of three definite numbers $(u:v:w)$. Here, the numbers $x, y, u, v, w$ are all *real* numbers, of which $u, v$ cannot both be zero. The condition showing that the given point is situated upon the given straight line, viz.: \begin{equation}ux+vy+w=0\end{equation} is an equation in the ordinary sense of the word.

**Lean reading.** Hilbert's co-ordinates come from § 17 (congruence and rectangular axes, not
available here). The form proved here, without congruence: in a plane with I 1–2, II, III, the
second part of Desargues's theorem and axiom V (equality of § 24), with any frame (two axes and
unit points): every point has co-ordinates in the segments (`coords_bijective`, § 27), every line
has an equation `a x + b y + c = 0` with `(a, b) ≠ (0, 0)` (`theorem34`), and the segments are
real numbers: `real_coordinates` gives an injective map into `ℝ` preserving sums, products and
order (the segments form an archimedean ordered field by Theorems 36/38, which embeds into `ℝ`,
`ConditionallyCompleteLinearOrderedField.inducedOrderRingHom`). "For each point a corresponding pair
of numbers" is `point_coordinates` (the co-ordinates are a bijection of the points with the pairs of
segments), and "for each straight line a ratio of three definite numbers" is `line_equation` with
`line_ratio`: two equations of the same line are proportional (`(a', b', c') = k (a, b, c)`,
`k ≠ 0`; this needs only Desargues's theorem, the factor standing on the left). Rectangular axes play
no role.

**Status.** proved (reading)
-/

theorem real_coordinates {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
    (hV : ArchimedesWith P (TrEqual (P := P) L)) (F : Frame P) :
    ∃ φ : DesAlg.Seg F → ℝ, Function.Injective φ ∧ (∀ a b, φ (a + b) = φ a + φ b) ∧
      (∀ a b, φ (a * b) = φ a * φ b) ∧ (∀ a b, a < b ↔ φ a < φ b) := by
  have : Fact (DesarguesII P) := ⟨hD⟩
  let := segField hD (theorem36_plane hD hV) F
  have : Archimedean (DesAlg.Seg F) := law17_iff_archimedean'.1 (law17_seg F hV)
  let φ := ConditionallyCompleteLinearOrderedField.inducedOrderRingHom (DesAlg.Seg F) ℝ
  have hmono : StrictMono φ := φ.monotone'.strictMono_of_injective φ.toRingHom.injective
  exact ⟨φ, φ.toRingHom.injective, fun a b => map_add φ a b, fun a b => map_mul φ a b,
    fun a b => hmono.lt_iff_lt.symm⟩

theorem point_coordinates {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (F : Frame P) :
    Function.Bijective (fun X : P => (F.xc X, F.yc X)) :=
  coords_bijective F

theorem line_ratio {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) (F : Frame P) (l : L)
    {a b c a' b' c' : DesAlg.Seg F} (h : a ≠ 0 ∨ b ≠ 0) (h' : a' ≠ 0 ∨ b' ≠ 0)
    (hl : ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0)
    (hl' : ∀ X : P, X ∈ l ↔ a' * F.xc X + b' * F.yc X + c' = 0) :
    ∃ k : DesAlg.Seg F, k ≠ 0 ∧ a' = k * a ∧ b' = k * b ∧ c' = k * c :=
  line_ratio_unique hD F l h h' hl hl'

theorem line_equation {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P) (F : Frame P)
    (l : L) : ∃ a b c : DesAlg.Seg F, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ X : P, X ∈ l ↔ a * F.xc X + b * F.yc X + c = 0 :=
  theorem34 hD F l

/-!
## [s35.omega_model] The numbers of `Ω` as co-ordinates

*(§ 35)*

> Conversely, in case $x, y, u, v, w$ are numbers of the algebraic domain $\Omega$ of $\S$ 9, and $u, v$ are not both zero, we may certainly assume that each pair of numbers $(x,y)$ gives a point and that each ratio of three numbers $(u:v:w)$ gives a straight line in the geometry in question.

**Lean reading.** Read as Hilbert's argument uses it: the geometry over `Ω` (§ 9) is itself a
plane geometry with I–V (`omega_planeGeometry`), its points are the pairs `(x, y)` and its lines the
ratios `(u : v : w)` with `(u, v) ≠ (0, 0)` (`Coord.mem_lineOfEq`, `Coord.exists_eq_of_line`), so a
proposition valid in every plane geometry with I–V holds for all values in `Ω`. The stronger
reading — that the points with co-ordinates in `Ω` exist in *every* plane geometry with I–V
(constructible with congruence) — is not formalized here.

**Status.** proved (reading)
-/

theorem omega_model : PlaneGeometry (Coord OmegaField 2) (CoordLine OmegaField 2) ∧
    (∀ (u v w : OmegaField) (h : u ≠ 0 ∨ v ≠ 0) (X : Coord OmegaField 2),
      X ∈ Coord.lineOfEq u v w h ↔ Coord.lin u v w X = 0) ∧
    ∀ a : CoordLine OmegaField 2, ∃ (u v w : OmegaField) (h : u ≠ 0 ∨ v ≠ 0),
      a = Coord.lineOfEq u v w h :=
  ⟨omega_planeGeometry, fun _ _ _ h X => Coord.mem_lineOfEq h X, Coord.exists_eq_of_line⟩

/-!
## [s35.identity] The expression vanishes identically

*(§ 35)*

> If, for all the points and straight lines which occur in connection with any theorem relating to intersections in a plane, we introduce the corresponding pairs and triples of numbers, then such a theorem asserts that a definite expression $A(p_1,p_2,\ldots,p_r)$ with real coefficients and depending rationally upon certain parameters $p_1,p_2,\ldots,p_r$ always vanishes as soon as we put for each of these parameters a number of the main $\Omega$ considered in $\S$ 9. We conclude from this that the expression $A(p_1,p_2,\dots,p_r)$ must also vanish identically in accordance with the laws 7–12 of $\S$ 13.

**Lean reading.** The rational expression is `A = N / Dn` with polynomials `N`, `Dn ≠ 0`;
"vanishes for all values in `Ω`" is read where it is defined (`Dn ≠ 0`). `identity_real`: for real
coefficients, `N` is then the zero polynomial (`N · Dn` vanishes on the infinite box `Ωʳ`,
`MvPolynomial.funext_set`), i.e. vanishes identically by the laws of a commutative field.
`identity_integral`: for integral coefficients (which is what constructions from free parameters
produce) the same holds, and then `N` vanishes in every commutative ring — the form needed to
apply the identity in another number system (unit `s35.conclusion`). The passage from a
proposition to its expression `A` is Hilbert's and is not formalized (unit `s35.form`).

**Status.** proved (reading)
-/

theorem omega_infinite : (Omega : Set ℝ).Infinite :=
  Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := ℝ)) fun n => natCast_mem Omega n

theorem identity_real {r : ℕ} (N Dn : MvPolynomial (Fin r) ℝ) (hD : Dn ≠ 0)
    (h : ∀ x : Fin r → ℝ, (∀ i, x i ∈ Omega) → MvPolynomial.eval x Dn ≠ 0 →
      MvPolynomial.eval x N = 0) : N = 0 := by
  have hprod : N * Dn = 0 := by
    refine MvPolynomial.funext_set (fun _ => (Omega : Set ℝ)) (fun _ => omega_infinite) ?_
    intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at hx
    rw [map_mul, map_zero]
    by_cases hd : MvPolynomial.eval x Dn = 0
    · rw [hd, mul_zero]
    · rw [h x hx hd, zero_mul]
  exact (mul_eq_zero.1 hprod).resolve_right hD

theorem identity_integral {r : ℕ} (N Dn : MvPolynomial (Fin r) ℤ) (hD : Dn ≠ 0)
    (h : ∀ x : Fin r → OmegaField, MvPolynomial.aeval x Dn ≠ 0 → MvPolynomial.aeval x N = 0)
    (R : Type*) [CommRing R] (x : Fin r → R) : MvPolynomial.aeval x N = 0 :=
  vanishes_of_vanishes_on_omega N Dn hD h R x

/-!
## [s35.segment_field] The algebra of segments of a pascalian plane is a field

*(§ 35)*

> Since, according to $\S$ 32, Desargues's theorem holds for the geometry in question, it follows that we certainly can make use of the algebra of segments introduced in $\S$ 24, and because Pascal's theorem is equally valid in this case, the commutative law of multiplication is also. Hence, for this algebra of segments, all of the laws 7–12 of $\S$ 13 are valid.

**Lean reading.** "§ 32" is a misprint for § 22 (Desargues's theorem from I 1–2, II–IV). Both
theorems are hypotheses here (this file has no congruence). `segment_field`: in a plane with
I 1–2, II, III, the second part of Desargues's theorem and Pascal's theorem, the segments of every
frame satisfy laws 7–12 (indeed form a commutative field, `segField`), by `pascal_iff_commutative`.

**Status.** proved
-/

theorem segment_field {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
    (hP : PascalTheorem P (L := L)) (F : Frame P) :
    Law7 (DesAlg.Seg F) ∧ Law8 (DesAlg.Seg F) ∧ Law9 (DesAlg.Seg F) ∧ Law10 (DesAlg.Seg F) ∧
      Law11 (DesAlg.Seg F) ∧ Law12 (DesAlg.Seg F) := by
  obtain ⟨h7, h8, h9, h10, h11⟩ := seg_laws_7_11 hD F
  exact ⟨h7, h8, h9, h10, h11, (pascal_iff_law12 hD).1 hP F⟩

/-!
## [s35.same_coordinates] The new algebra of segments and the old co-ordinates

*(§ 35)*

> If we take as our axes in this new algebra of segments the co-ordinate axes already used and consider the unit points $E$, $E'$ as suitably established, we see that the new algebra of segments is nothing else than the system of co-ordinates previously employed.

**Lean reading.** Hilbert's "co-ordinates previously employed" are those of § 17, defined with
congruence (Chapter III), which this file does not import. The identification is proved where
those co-ordinates are literal co-ordinates, in the analytic plane over `ℝ` (the model of I–V
used in § 9): `same_coordinates` (`SameCoordinatesClaim`) — with the axes of co-ordinates as fixed
lines and the unit points `E = (1, 0)`, `E' = (0, 1)` ("suitably established"), the sum and the
product of § 24 of two segments of the `x`-axis have as abscissa the sum and the product of the
abscissae (`same_coordinates_real`: Hilbert's constructions computed with the parallels of the
plane, `mem_pline_through`). For an abstract plane with I–V the identification with the § 17
co-ordinates is not formalized; the argument of § 35 does not need it, since the identity of unit
`s35.identity` is evaluated directly in the new algebra (`intersection_propositions`), whose
co-ordinates describe the plane by Theorem 34 (`line_equation`) and are real numbers in the
archimedean case (`real_coordinates`).

**Status.** proved (reading)
-/

/-- **Hilbert's identification** (§ 35), in the analytic plane over `ℝ`. -/
def SameCoordinatesClaim : Prop :=
  haveI := realLine_nonempty
  ∀ F : Frame (Coord ℝ 2), F.O = Coord.pt2 0 0 → F.E = Coord.pt2 1 0 → F.E' = Coord.pt2 0 1 →
    ∀ a b : DesAlg.Seg (L := CoordLine ℝ 2) F,
      Coord.xc (a + b).pt = Coord.xc a.pt + Coord.xc b.pt ∧
        Coord.xc (a * b).pt = Coord.xc a.pt * Coord.xc b.pt

theorem same_coordinates : SameCoordinatesClaim :=
  fun F hO hE hE' a b => same_coordinates_real F hO hE hE' a b

/-!
## [s35.conclusion] Every proposition about points of intersection follows from Pascal and Desargues

*(§ 35)*

> In order to show that, for the new algebra of segments, the expression $A(p_1, p_2, \ldots, p_r)$ vanishes identically, it is sufficient to apply the theorems of Pascal and Desargues. Consequently we see that: *Every proposition relative to points of intersection in the geometry in question must always, by the aid of suitably constructed auxiliary points and straight lines, turn out to be a combination of the theorems of Pascal and Desargues. Hence for the proof of the validity of a theorem relating to points of intersection, we need not have resource to the theorems of congruence.*

**Lean reading.** Read through the co-ordinate expression of the proposition (unit `s35.identity`):
`identity_for_segments` — if an integral expression `N / Dn` (`Dn ≠ 0`) vanishes for all values in
`Ω`, then `N` vanishes for all values in the segments of any plane with I 1–2, II, III satisfying
Desargues's and Pascal's theorems (the segments form a commutative field, `segField`); no
congruence is used. This is the precise content of Hilbert's argument. Not formalized: (1) the
correspondence between a proposition about points of intersection and its expression (a syntax of
constructions, and the degenerate positions in which a construction is undefined — Hilbert's
argument is silent about them, and a proposition must be read as excluding them); (2) the
proof-theoretic form "a combination of the theorems of Pascal and Desargues with auxiliary points";
what is proved is the semantic form: such a proposition holds in every plane with I 1–2, II, III in
which the two theorems hold, so the axioms of congruence are not needed. Hilbert's "real
coefficients" are replaced by integral ones, the only ones that make sense in another number
system.

**Status.** proved (reading)
-/

theorem intersection_propositions {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [PlaneOrder P L] [PlaneParallels P L] [Nonempty L] (hD : DesarguesII P)
    (hP : PascalTheorem P (L := L)) (F : Frame P) {r : ℕ} (N Dn : MvPolynomial (Fin r) ℤ)
    (hDn : Dn ≠ 0)
    (h : ∀ x : Fin r → OmegaField, MvPolynomial.aeval x Dn ≠ 0 → MvPolynomial.aeval x N = 0) :
    letI := segField hD hP F
    ∀ x : Fin r → DesAlg.Seg F, MvPolynomial.aeval x N = 0 :=
  identity_for_segments hD hP F N Dn hDn h

end HilbertFoundations
