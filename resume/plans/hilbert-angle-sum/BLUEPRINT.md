# BLUEPRINT — `concl.angle_sum`: the angle sum of one triangle decides that of all triangles

Unit `concl.angle_sum` of `HilbertFoundations/Commentary.lean`. Plan directory:
`.lake-local/plans/hilbert-angle-sum/`. All new Lean files go to `HilbertFoundations/`
(`AngleSumCloseAux1.lean` … `AngleSumCloseAux14.lean`, with the two extra split files
`AngleSumCloseAux8b.lean` and `AngleSumCloseAux12b.lean`, and `AngleSumClose.lean`; 17 files, § 4.15);
no existing file is modified.

*Revision note.* This version incorporates two independent critiques (one mathematical, one on Lean
feasibility). All of their points were checked and accepted (one partly, as an option); the changes
are made in place, and the section "REJECTED CRITIQUES" at the end records the single point not
adopted as mandatory and why.

**Verdict on the target.** The target statement is **true as formalized** (no counterexample; the
degenerate one-point geometry, in which `IsTriangle X X X` holds, is harmless because there all three
predicates are false, see § 6, R1). The proof below is elementary and uses neither parallels, nor
Archimedes, nor continuity. It is a rigorous reconstruction of Hartshorne, *Geometry: Euclid and
Beyond*, § 34 (Saccheri and Lambert quadrilaterals), with one substantial simplification: the
passage from a triangle to its Saccheri quadrilateral is done with the two half-turns about the
midpoints of `CA`, `CB`, which removes every case distinction on the position of the foot of the
altitude (§ 3, Stage G).

Status of verification: the mathematics was checked by hand, line by line (and re-derived
independently by a critic, who found it correct up to four unstated incidence facts, now supplied).
The two new geometric configurations (Stage E and Stage G) were also tested numerically in the
hyperbolic plane, which only exercises the acute branch; the obtuse branch (`Pos₊`, `GtSupp`, E3) is
justified by the logical proof alone (§ 6, R3). All definitions of § 4, **every statement of
§ 4.1–4.13**, the final theorem (assuming the two results it rests on) and complete proofs of about
thirty basic lemmas were type-checked in scratch files (Appendix A reproduces the first; § 6, R12
lists exactly what was confirmed). Everything else is unverified Lean and must be treated as a
careful design, not as code.

---------------------------------------------------------------------------------------------------

## 1. TARGET

File `HilbertFoundations/Commentary.lean`, inside `namespace HilbertFoundations`, `namespace Conclusion`
(the namespace `Conclusion` runs from line 320 to line 1193). Lines 608–638 and 715–721:

```lean
section AngleSum

variable {P L : Type*} [HasLines P L] [HasBetween P] [HasAngCong P]

variable (L) in
def ExteriorConfig (A B C X Y : P) : Prop :=
  Between A C X ∧ AngCong C A B X C Y ∧ ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B

variable (L) in
def AngleSumEqTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    Y ∈ Interior (Line := L) X C B ∧ AngCong Y C B C B A

variable (L) in
def AngleSumLtTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    Y ∈ Interior (Line := L) X C B ∧ ∃ Z ∈ Interior (Line := L) Y C B, AngCong Z C B C B A

variable (L) in
def AngleSumGtTwoRight (A B C : P) : Prop :=
  IsTriangle (Line := L) A B C ∧ ∃ X Y : P, ExteriorConfig L A B C X Y ∧
    (Y ∉ Interior (Line := L) X C B ∨ ∃ Z ∈ Interior (Line := L) C B A, AngCong Y C B Z B C)

end AngleSum

/-- **Dehn's theorem on the angle sum** (the generalization of Legendre's theorem). -/
def AngleSumTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → ∀ A B C A' B' C' : P, IsTriangle (Line := L) A' B' C' →
      (AngleSumGtTwoRight L A B C → AngleSumGtTwoRight L A' B' C') ∧
      (AngleSumEqTwoRight L A B C → AngleSumEqTwoRight L A' B' C') ∧
      (AngleSumLtTwoRight L A B C → AngleSumLtTwoRight L A' B' C')
```

(`IsTriangle A B C := ¬Collinear A B C`, `Basic.lean` line 1446.)

**Final theorem** (new file `HilbertFoundations/AngleSumClose.lean`):

```lean
namespace HilbertFoundations
namespace Conclusion

/-- **Dehn's theorem on the angle sum** (unit `concl.angle_sum`), proved in every plane satisfying
groups I, II, IV. -/
theorem angleSumTheorem : AngleSumTheorem
```

Meaning of the three predicates (used throughout). `X` lies on `AC` beyond `C`; the half-ray `CY`
is the copy of `∠A` laid off at `C` on `CX`, on the side of `B`. By uniqueness of laying off (IV 4)
the half-rays `CX`, `CY` do not depend on the witnesses. Writing `∠B* := ∠A₁CB` for the copy of
`∠B = ∠CBA` laid off at `C` on `CB` on the side of `X` (also unique), the predicates say:
`Eq`: half-ray `CY` = half-ray `CA₁`; `Lt`: `CA₁` lies inside `∠YCB`; `Gt`: `CY` lies inside
`∠A₁CB` (or `Y` is not inside `∠XCB`, which never happens: Lemma G6). So the three predicates are
the three possible positions of `A₁` with respect to the line `CY`.

---------------------------------------------------------------------------------------------------

## 2. EXISTING MATERIAL

Everything below was read in the repository (types copied). `P L` are the point and line types.
"Frame lemma" means a theorem of `namespace Frame` taking `(F : Frame P L)`; in plane geometry one
uses `F := planeFrame hl` (`hl : ∀ X : P, ∃ l : L, X ∈ l`), the only plane being `Set.univ`
(`(planeFrame hl).IsPl S` is by definition `S = Set.univ`, proved by `rfl`; membership in
`Set.univ` by `trivial`; `LineIn l Set.univ` by `fun _ _ => trivial`).

### 2.1 What the repository has, and what it does not have

*Has* (Hilbert's first edition numbers its theorems differently from the later editions; the
repository follows the first edition, where § 7 ends with Theorem 20):
Theorems 10, 11, 16 (SAS, ASA, SSS), 12 (supplements), vertical angles, 13 (transfer of an interior
half-ray), 14 (addition of angles, corrected form), 15 (right angles congruent), base angles and their
converse, uniqueness and existence of midpoints, the perpendicular bisector, crossbar,
"position of a half-ray" (`interior_or_interior`), the definition of `AngLt` with one compatibility
lemma, and — in the helper modules of `Pascal.lean` — **isometries of the plane, reflections in
lines and half-turns, all under `PlaneCongruence` only** (the sections used below do not assume
`PlaneParallels`; this was checked on the `variable` lines: `PascalAux1.lean` lines 35, 173, 363;
`PascalAux2.lean` lines 32 and 68–251).

*Does not have* (all of this is built in § 3/§ 4): transitivity / irreflexivity / trichotomy of
`AngLt`, monotonicity of angle addition, comparison of segments usable without parallels
(`Proportion.SegLt` is tied to the segment calculus), the exterior angle theorem (later editions'
Theorem 22), feet of perpendiculars from a point and their uniqueness, "two perpendiculars to a line
do not meet" in a directly usable form, Saccheri and Lambert quadrilaterals, anything about angle
sums without parallels. `Areas.IsFoot` and `ConstructionsAux.Perp` exist but are stated with
`IsRightAngle` and are used only with parallels; they are **not** reused (name clash avoided: the new
predicate is `AngSum.Foot`, the new segment comparison `AngSum.SLt`).

### 2.2 `Basic.lean`

```lean
def Collinear [HasLines Point Line] (A B C : Point) : Prop := ∃ a : Line, A ∈ a ∧ B ∈ a ∧ C ∈ a
def Meets [Membership Point Line] (a b : Line) : Prop := ∃ P : Point, P ∈ a ∧ P ∈ b
theorem Collinear.swap12 (h : Collinear A B C) : Collinear B A C
theorem Collinear.swap23 (h : Collinear A B C) : Collinear A C B
theorem Collinear.swap13 (h : Collinear A B C) : Collinear C B A
theorem exists_line {A B : Point} (h : A ≠ B) : ∃ a : Line, A ∈ a ∧ B ∈ a
theorem line_unique {A B : Point} {a b : Line} (h : A ≠ B) (ha : A ∈ a) (hb : B ∈ a)
    (ha' : A ∈ b) (hb' : B ∈ b) : a = b
theorem exists_two_points (a : Line) : ∃ A B : Point, A ≠ B ∧ A ∈ a ∧ B ∈ a
noncomputable def line (A B : Point) (h : A ≠ B) : Line
theorem mem_line_left {A B : Point} (h : A ≠ B) : A ∈ line A B h
theorem mem_line_right {A B : Point} (h : A ≠ B) : B ∈ line A B h
theorem eq_line {A B : Point} (h : A ≠ B) {a : Line} (ha : A ∈ a) (hb : B ∈ a) : a = line A B h
theorem line_comm {A B : Point} (h : A ≠ B) : line B A h.symm = line A B h
theorem collinear_of_ne {A B : Point} (h : A ≠ B) : Collinear A B A
theorem ne12_of_between (h : Between A B C) : A ≠ B
theorem ne13_of_between (h : Between A B C) : A ≠ C
theorem ne23_of_between (h : Between A B C) : B ≠ C
theorem collinear_of_between (h : Between A B C) : Collinear A B C
theorem between_symm (h : Between A B C) : Between C B A
theorem not_between_swap12 (h : Between A B C) : ¬Between B A C
theorem not_between_swap23 (h : Between A B C) : ¬Between A C B
theorem between_trichotomy (h : Collinear A B C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Between B A C ∨ Between A B C ∨ Between A C B
theorem exists_between (h : A ≠ C) : ∃ B, Between A B C
theorem exists_beyond (h : A ≠ C) : ∃ D, Between A C D
def SameSidePt [HasLines Point Line] [HasBetween Point] (O A A' : Point) : Prop :=
  A ≠ O ∧ A' ≠ O ∧ Collinear A O A' ∧ ¬Between A O A'
def ray [HasLines Point Line] [HasBetween Point] (O A : Point) : Set Point := {X | SameSidePt O A X}
def SameSide [Membership Point Line] [HasBetween Point] (a : Line) (A B : Point) : Prop :=
  A ∉ a ∧ B ∉ a ∧ ¬∃ X : Point, X ∈ a ∧ Between A X B
def OppositeSides [Membership Point Line] [HasBetween Point] (a : Line) (A B : Point) : Prop :=
  A ∉ a ∧ B ∉ a ∧ ∃ X : Point, X ∈ a ∧ Between A X B
def Interior {Point : Type u} [HasLines Point Line] [HasBetween Point] (A O B : Point) : Set Point :=
  {X | ∀ a b : Line, O ∈ a → A ∈ a → O ∈ b → B ∈ b → SameSide a X B ∧ SameSide b X A}
def IsTriangle {Point : Type u} [HasLines Point Line] (A B C : Point) : Prop := ¬Collinear A B C
class PlaneCongruence (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point]
    [HasSegCong Point] [HasAngCong Point] : Prop
    extends PlaneAngleCongruence Point Line, TriangleCongruence Point Line
theorem segCong_refl (h : A ≠ B) : SegCong A B A B
theorem segCong_swap_left (h : SegCong A B A' B') : SegCong B A A' B'
theorem segCong_swap_right (h : SegCong A B A' B') : SegCong A B B' A'
theorem angCong_refl (h : ¬Collinear A O B) : AngCong A O B A O B
theorem angCong_swap_left (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong B O A A' O' B'
theorem angCong_swap_right (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A O B B' O' A'
```

### 2.3 `OrderAux.lean` / `Order.lean`

```lean
theorem collinear_of_mem {A B C : P} {a : L} (hA : A ∈ a) (hB : B ∈ a) (hC : C ∈ a) : Collinear A B C
theorem Collinear.perm231 {A B C : P} (h : Collinear A B C) : Collinear B C A
theorem Collinear.perm312 {A B C : P} (h : Collinear A B C) : Collinear C A B
theorem eq_of_mem_of_mem {a b : L} {X Y : P} (hab : a ≠ b) (hXa : X ∈ a) (hXb : X ∈ b)
    (hYa : Y ∈ a) (hYb : Y ∈ b) : X = Y
theorem mem_of_collinear {A B C : P} {a : L} (h : Collinear A B C) (hAB : A ≠ B) (hA : A ∈ a)
    (hB : B ∈ a) : C ∈ a
theorem not_collinear_of_not_mem {A B C : P} {a : L} (hA : A ∈ a) (hB : B ∈ a) (hAB : A ≠ B)
    (hC : C ∉ a) : ¬Collinear A B C
theorem exists_mem_not_mem {a b : L} (h : a ≠ b) : ∃ X : P, X ∈ a ∧ X ∉ b
theorem exists_not_mem (a : L) : ∃ X : P, X ∉ a                         -- [PlaneConnection]
-- namespace OrderCore (instance `PlaneOrder.toPlaneOrderCore` makes these available):
theorem OrderCore.sameSide_trans {a : L} (h1 : SameSide a A B) (h2 : SameSide a B C) : SameSide a A C
theorem OrderCore.opp_of_sameSide_opp {a : L} (h1 : SameSide a A B) (h2 : OppositeSides a B C) :
    OppositeSides a A C
theorem OrderCore.sameSide_of_opp_opp {a : L} (h1 : OppositeSides a A B) (h2 : OppositeSides a B C) :
    SameSide a A C
theorem OrderCore.ne_of_opp {a : L} (h : OppositeSides a A B) : A ≠ B
theorem OrderCore.between_of_between_between₂' (h1 : Between A B C) (h2 : Between A C D) : Between A B D
-- namespace OrderLin:
theorem OrderLin.trans₂ (h1 : Between A B C) (h2 : Between A C D) : Between A B D ∧ Between B C D
theorem OrderLin.trans₁ (h1 : Between A B C) (h2 : Between B C D) : Between A B D ∧ Between A C D
```

### 2.4 `CongruenceAux.lean` (linear lemmas, sides, interiors, frames)

```lean
theorem mem_mid_of_between {a : L} (h : Between A B C) (hA : A ∈ a) (hC : C ∈ a) : B ∈ a
theorem mem_right_of_between {a : L} (h : Between A B C) (hA : A ∈ a) (hB : B ∈ a) : C ∈ a
theorem mem_left_of_between {a : L} (h : Between A B C) (hB : B ∈ a) (hC : C ∈ a) : A ∈ a
theorem ne_of_mem_not_mem {l : L} (hX : X ∈ l) (hY : Y ∉ l) : Y ≠ X
theorem collinear_iff_mem_line [Connection P L] {A B X : P} (h : A ≠ B) :
    Collinear A B X ↔ X ∈ line (Line := L) A B h
theorem ray_eq_of_mem (hX : X ∈ ray O A) : ray O X = ray O A
theorem mem_ray_comm (hX : X ∈ ray O A) : A ∈ ray O X
theorem ne_of_mem_ray (hX : X ∈ ray O A) : X ≠ O
theorem ne_of_mem_ray' (hX : X ∈ ray O A) : A ≠ O
theorem collinear_of_mem_ray (hX : X ∈ ray O A) : Collinear O A X
theorem mem_ray_of_between (h : Between O X A) : X ∈ ray O A
theorem mem_ray_of_between' (h : Between O A X) : X ∈ ray O A
theorem mem_ray_self' (h : A ≠ O) : A ∈ ray O A
theorem mem_ray_or_between (h : Collinear O A X) (hA : A ≠ O) (hX : X ≠ O) : X ∈ ray O A ∨ Between A O X
theorem not_mem_ray_of_between (h : Between A O X) : X ∉ ray O A
theorem mem_ray_cases (hX : X ∈ ray O A) (hY : Y ∈ ray O A) : X = Y ∨ Between O X Y ∨ Between O Y X
theorem between_of_mem_rays (h : Between A O B) (hX : X ∈ ray O A) (hY : Y ∈ ray O B) : Between X O Y
theorem not_collinear_of_mem_rays (h : ¬Collinear A O B) (hX : X ∈ ray O A) (hY : Y ∈ ray O B) :
    ¬Collinear X O Y
theorem not_collinear_of_between (h : ¬Collinear A O B) (hb : Between A O C) : ¬Collinear C O B
theorem not_collinear_swap {A O B : P} (h : ¬Collinear A O B) : ¬Collinear B O A
theorem ne_of_not_collinear (h : ¬Collinear A O B) (hl : ∃ l : L, O ∈ l) : A ≠ O ∧ B ≠ O ∧ A ≠ B
theorem sameSide_symm' (h : SameSide l A B) : SameSide l B A
theorem opp_symm' (h : OppositeSides l A B) : OppositeSides l B A
theorem sameSide_refl' (h : A ∉ l) : SameSide l A A
theorem sameSide_or_opp' (hA : A ∉ l) (hB : B ∉ l) : SameSide l A B ∨ OppositeSides l A B
theorem not_sameSide_of_opp' (h : OppositeSides l A B) : ¬SameSide l A B
theorem sameSide_of_between_mem' (hX : X ∈ l) (hY : Y ∉ l) (h : Between X Z Y) : SameSide l Z Y
theorem opp_of_between_mem (hZ : Z ∈ l) (hX : X ∉ l) (h : Between X Z Y) : OppositeSides l X Y
theorem sameSide_of_ray (hOl : O ∈ l) (hA : A ∉ l) (hX : X ∈ ray O A) : SameSide l A X
theorem mem_ray_of_sameSide (hOl : O ∈ l) (hc : Collinear O A X) (hXO : X ≠ O)
    (h : SameSide l A X) : X ∈ ray O A
theorem interior_iff (hA : A ≠ O) (hB : B ≠ O) :
    X ∈ Interior A O B ↔ SameSide (line (Line := L) O A hA.symm) X B ∧
      SameSide (line (Line := L) O B hB.symm) X A
theorem interior_swap : Interior A O B = Interior (Line := L) B O A
theorem mem_interior_of_between (h : ¬Collinear A O B) (hb : Between A X B) :
    X ∈ Interior (Line := L) A O B
def LineIn {P : Type u} {L : Type v} [HasLines P L] (l : L) (S : Set P) : Prop := ∀ X : P, X ∈ l → X ∈ S
structure Frame (P : Type u) (L : Type v) [HasLines P L] [HasBetween P] [HasAngCong P] where
  IsPl : Set P → Prop
  line_through : ∀ X : P, ∃ l : L, X ∈ l
  ...
  layoff : ∀ S, IsPl S → ∀ (A O B : P) (l : L) (O' A' D' : P), ¬Collinear A O B → LineIn l S →
    O' ∈ l → A' ∈ l → A' ≠ O' → D' ∈ S → D' ∉ l →
      ∃ B', B' ∈ S ∧ SameSide l B' D' ∧ AngCong A O B A' O' B'
  layoff_unique : ∀ S, IsPl S → ∀ (A O B : P) (l : L) (O' A' B' B'' : P), ¬Collinear A O B →
    LineIn l S → O' ∈ l → A' ∈ l → A' ≠ O' → B' ∈ S → B'' ∈ S → SameSide l B' B'' →
      AngCong A O B A' O' B' → AngCong A O B A' O' B'' → ray O' B' = ray O' B''
def planeFrame [PlaneAngleCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l) : Frame P L
  -- IsPl S := S = Set.univ
theorem Frame.ne (h : ¬Collinear A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B
theorem Frame.crossbar (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S)
    (h : ¬Collinear B A C) (hDi : D ∈ Interior B A C) : ∃ Y, Between B Y C ∧ Y ∈ ray A D
theorem Frame.mem_interior_of_ray (hS : F.IsPl S) (hO : O ∈ S) (hA : A ∈ S) (hB : B ∈ S)
    (hX : X ∈ S) (h : ¬Collinear A O B) (hXi : X ∈ Interior A O B) (hY : Y ∈ ray O X) :
    Y ∈ Interior A O B
theorem Frame.interior_or_interior (hS : F.IsPl S) (hO : O ∈ S) (hH : H ∈ S) (hK : K ∈ S)
    (hL : L' ∈ S) (hHL : ¬Collinear H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear H O K) :
    K ∈ Interior H O L' ∨ H ∈ Interior K O L'
```

### 2.5 `CongruenceAux2.lean` – `CongruenceAux8.lean`, `Congruence.lean`

```lean
theorem segCong_symm (hAB : A ≠ B) (hA'B' : A' ≠ B') (h : SegCong A B A' B') : SegCong A' B' A B
theorem segCong_trans (hAB : A ≠ B) (hCD : C ≠ D) (hEF : E ≠ F) (h1 : SegCong A B C D)
    (h2 : SegCong C D E F) : SegCong A B E F
theorem segCong_swap (h : SegCong A B A' B') : SegCong B A B' A'
theorem segCong_layoff (hAB : A ≠ B) (hA'C' : A' ≠ C') : ∃ B', B' ∈ ray A' C' ∧ SegCong A B A' B'
theorem eq_of_segCong_ray' (hX : X ∈ ray A' C') (hY : Y ∈ ray A' C') (h : SegCong A' X A' Y) : X = Y
theorem between_of_segCong_ray (h : Between A C B) (hC' : C' ∈ ray A' B')
    (h1 : SegCong A C A' C') (h2 : SegCong A B A' B') : Between A' C' B'
theorem nc_of (hX : X ∈ a) (hY : Y ∈ a) (hXY : X ≠ Y) (hZ : Z ∉ a) :
    ¬Collinear X Y Z ∧ ¬Collinear X Z Y ∧ ¬Collinear Z X Y ∧ ¬Collinear Y X Z ∧
      ¬Collinear Y Z X ∧ ¬Collinear Z Y X
theorem eq_of_collinear_collinear (hn : ¬Collinear A B C) (h1 : Collinear A C X)
    (h2 : Collinear B C X) : X = C
theorem angCong_symm (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') : AngCong A' O' B' A O B
theorem angCong_trans (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (h'' : ¬Collinear A'' O'' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A' O' B' A'' O'' B'') : AngCong A O B A'' O'' B''
theorem angCong_rays (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') (hX : X ∈ ray O A) (hY : Y ∈ ray O B) (hX' : X' ∈ ray O' A')
    (hY' : Y' ∈ ray O' B') : AngCong X O Y X' O' Y'
theorem nc_of_interior (hA : A ≠ O) (hB : B ≠ O) (hX : X ∈ Interior (Line := L) A O B) :
    ¬Collinear A O X ∧ ¬Collinear B O X
theorem Frame.sas (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hA : AngCong B A C B' A' C') :
    SegCong B C B' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'
theorem Frame.sss (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hBC : SegCong B C B' C') :
    AngCong B A C B' A' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'
theorem Frame.angLt_congr {A₁ O₁ B₁ A₂ O₂ B₂ : P} (h1 : ¬Collinear A₁ O₁ B₁)
    (h2 : ¬Collinear A₂ O₂ B₂) (hX : Between A₁ X B₁) (hc : AngCong A O B A₁ O₁ X)
    (h : ¬Collinear A O B) (hc12 : AngCong A₁ O₁ B₁ A₂ O₂ B₂) :
    ∃ Y, Between A₂ Y B₂ ∧ AngCong A O B A₂ O₂ Y                    -- CongruenceAux5.lean
theorem mem_interior_of_rays_plane {A' B' : P} (hAO : A ≠ O) (hBO : B ≠ O)
    (hX : X ∈ Interior (Line := L) A O B) (hA' : A' ∈ ray O A) (hB' : B' ∈ ray O B) :
    X ∈ Interior (Line := L) A' O B'                                 -- CongruenceAux6.lean, [PlaneOrder]
theorem line_through_of_ne {P : Type u} {L : Type v} [HasLines P L] [PlaneConnection P L]
    {X Y : P} (h : X ≠ Y) : ∀ Z : P, ∃ l : L, Z ∈ l                  -- CongruenceAux6.lean
def RightAng {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasAngCong P] (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between B O C ∧ AngCong A O B A O C   -- CongruenceAux8.lean
theorem Frame.rt_side (h : RightAng (L := L) A O B) (hB2 : B' ≠ O) (hc : Collinear (Line := L) O B B') :
    RightAng (L := L) A O B'
theorem Frame.rt_symm (h : RightAng (L := L) A O B) : RightAng (L := L) B O A
theorem Frame.rt_arm (h : RightAng (L := L) A O B) (hA2 : A' ≠ O) (hc : Collinear (Line := L) O A A') :
    RightAng (L := L) A' O B
theorem Frame.rt_congr (h : RightAng (L := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hc : AngCong A O B A' O' B') : RightAng (L := L) A' O' B'
theorem Frame.rt_cong (h : RightAng (L := L) A O B) (h' : RightAng (L := L) A' O' B') :
    AngCong A O B A' O' B'
-- Congruence.lean, plane geometry, [PlaneCongruence P L]:
theorem theorem12 {A B C D A' B' C' D' : P} (h : ¬Collinear (Line := L) A B C)
    (h' : ¬Collinear (Line := L) A' B' C') (hc : AngCong A B C A' B' C') (hD : Between A B D)
    (hD' : Between A' B' D') : AngCong C B D C' B' D'
theorem vertical_angles {A O B C D : P} (h : ¬Collinear (Line := L) A O B)
    (h1 : Between A O C) (h2 : Between B O D) : AngCong A O B C O D
theorem theorem13 {A O B A' O' B' X : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hc : AngCong A O B A' O' B')
    (hX : X ∈ Interior (Line := L) A O B) :
    ∃ Y, Y ∈ Interior (Line := L) A' O' B' ∧ AngCong A O X A' O' Y ∧ AngCong B O X B' O' Y
theorem theorem14 {O H K M O' H' K' M' : P} (hMO : M ≠ O) (hMO' : M' ≠ O')
    (hHM : ¬Collinear (Line := L) H O M) (hKM : ¬Collinear (Line := L) K O M)
    (hHK : ¬Collinear (Line := L) H O K) (hH'M' : ¬Collinear (Line := L) H' O' M')
    (hK'M' : ¬Collinear (Line := L) K' O' M') (hH'K' : ¬Collinear (Line := L) H' O' K')
    (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M')
    (hside : (SameSide (line (Line := L) O M hMO.symm) H K ∧
        SameSide (line (Line := L) O' M' hMO'.symm) H' K') ∨
      (OppositeSides (line (Line := L) O M hMO.symm) H K ∧
        OppositeSides (line (Line := L) O' M' hMO'.symm) H' K')) :
    AngCong H O K H' O' K'
def AngLt [HasLines P L] [HasBetween P] [HasAngCong P] (A O B A' O' B' : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ¬Collinear (Line := L) A' O' B' ∧
    ∃ X, Between A' X B' ∧ AngCong A O B A' O' X
```

`IsRightAngle`, `IsAcute`, `IsObtuse` (`Congruence.lean` 434, 852, 856) also exist; they are **not**
used: the working notion of right angle is `RightAng` (it has the API `rt_side`, `rt_arm`,
`rt_symm`, `rt_congr`, `rt_cong`), and "acute / right / obtuse" is expressed by comparison with the
supplement (`LtSupp`, `EqSupp`, `GtSupp`, § 3 Stage B), which never needs a second right angle.

### 2.6 `PascalAux1.lean`, `PascalAux2.lean` (namespace `Pas`; only `[PlaneCongruence P L]`)

```lean
def Pas.PresCong (f : P → P) : Prop := ∀ X Y : P, X ≠ Y → SegCong X Y (f X) (f Y)
def Pas.isom : Subgroup (Equiv.Perm P)            -- carrier {f | PresCong f}
theorem Pas.isom_cong {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {X Y : P} (h : X ≠ Y) :
    SegCong X Y (f X) (f Y)
theorem Pas.isom_collinear (hf : f ∈ isom (L := L)) {X Y Z : P} (h : Collinear (Line := L) X Y Z) :
    Collinear (Line := L) (f X) (f Y) (f Z)
theorem Pas.isom_between (hf : f ∈ isom (L := L)) {X Y Z : P} (h : Between X Y Z) :
    Between (f X) (f Y) (f Z)
theorem Pas.isom_inv (hf : f ∈ isom (L := L)) : f⁻¹ ∈ isom (L := L)
theorem Pas.isom_collinear_iff (hf : f ∈ isom (L := L)) {X Y Z : P} :
    Collinear (Line := L) (f X) (f Y) (f Z) ↔ Collinear (Line := L) X Y Z
theorem Pas.isom_between_iff (hf : f ∈ isom (L := L)) {X Y Z : P} :
    Between (f X) (f Y) (f Z) ↔ Between X Y Z
theorem Pas.exists_isom_of_tri {A B C A' B' C' : P} (h : ¬Collinear (Line := L) A B C)
    (h' : ¬Collinear (Line := L) A' B' C') (hAB0 : A ≠ B) (sAB : SegCong A B A' B')
    (sAC : SegCong A C A' C') (sBC : SegCong B C B' C') :
    ∃ f ∈ isom (L := L), f A = A' ∧ f B = B' ∧ f C = C'
noncomputable def Pas.refl (l : L) : Equiv.Perm P
theorem Pas.refl_isom (l : L) : refl (P := P) l ∈ isom (L := L)
theorem Pas.refl_fix {l : L} {X : P} (hX : X ∈ l) : refl l X = X
theorem Pas.refl_refl (l : L) (X : P) : refl l (refl l X) = X
theorem Pas.refl_fix_iff {l : L} {X : P} : refl l X = X ↔ X ∈ l
theorem Pas.refl_opp {l : L} {X : P} (hX : X ∉ l) : OppositeSides l X (refl l X)
theorem Pas.exists_eqd {X Y : P} (h : X ≠ Y) :
    ∃ m : L, (∀ Z : P, Z ∈ m ↔ Z ≠ X ∧ Z ≠ Y ∧ SegCong Z X Z Y) ∧ refl m X = Y ∧
      OppositeSides m X Y
-- PascalAux2.lean, section HalfTurns (lines 66–251):
theorem Pas.mem_ray_of_between_between {X M Y Y' : P} (h1 : Between X M Y) (h2 : Between X M Y') :
    Y' ∈ ray M Y                                                   -- [LineOrder]
noncomputable def Pas.ht (M : P) : Equiv.Perm P
theorem Pas.ht_isom (M : P) : ht (L := L) M ∈ isom (L := L)
theorem Pas.ht_ht (M X : P) : ht (L := L) M (ht (L := L) M X) = X
theorem Pas.ht_self (M : P) : ht (L := L) M M = M
theorem Pas.ht_eq_iff {M X Y : P} (h : X ≠ M) :
    ht (L := L) M X = Y ↔ Between X M Y ∧ SegCong M X M Y
theorem Pas.ht_fix_iff {M X : P} : ht (L := L) M X = X ↔ X = M
noncomputable def Pas.midp (X Y : P) : P
theorem Pas.ht_midp (X Y : P) : ht (L := L) (midp (L := L) X Y) X = Y
```

Further isometry API in `PascalAux1.lean` (section `Isometries`, `[PlaneCongruence P L]` only;
`variable {f : Equiv.Perm P}`), copied from the file:

```lean
-- l. 62
theorem Pas.hl_of_ne {X Y : P} (h : X ≠ Y) : ∀ Z : P, ∃ l : L, Z ∈ l
-- l. 117
theorem Pas.isom_line (hf : f ∈ isom (L := L)) (l : L) : ∃ l' : L, ∀ Z : P, f Z ∈ l' ↔ Z ∈ l
-- l. 124
noncomputable def Pas.imLine (f : Equiv.Perm P) (hf : f ∈ isom (L := L)) (l : L) : L
theorem Pas.mem_imLine (hf : f ∈ isom (L := L)) (l : L) (Z : P) : f Z ∈ imLine f hf l ↔ Z ∈ l
theorem Pas.mem_imLine' (hf : f ∈ isom (L := L)) (l : L) (Z : P) :
    Z ∈ imLine f hf l ↔ f⁻¹ Z ∈ l
-- l. 135
theorem Pas.isom_sameSide (hf : f ∈ isom (L := L)) {l : L} {X Y : P} (h : SameSide l X Y) :
    SameSide (imLine f hf l) (f X) (f Y)
-- l. 146
theorem Pas.isom_opp (hf : f ∈ isom (L := L)) {l : L} {X Y : P} (h : OppositeSides l X Y) :
    OppositeSides (imLine f hf l) (f X) (f Y)
-- l. 153
theorem Pas.isom_ray (hf : f ∈ isom (L := L)) {O A X : P} (h : X ∈ ray O A) :
    f X ∈ ray (f O) (f A)
-- l. 160
theorem Pas.isom_meets_iff (hf : f ∈ isom (L := L)) {l m : L} :
    Meets (Point := P) (imLine f hf l) (imLine f hf m) ↔ Meets (Point := P) l m
-- l. 389 (section Reflections)
theorem Pas.isom_fix_line (hf : f ∈ isom (L := L)) {A B : P} (hAB : A ≠ B) (hA : f A = A)
    (hB : f B = B) {X : P} (hX : Collinear (Line := L) A B X) : f X = X
```

And in `CongruenceAux5.lean` (namespace `Frame`, variables `[hT : TriangleCongruence P L]
(F : Frame P L) {S : Set P} {A B … : P}`), the converse of the alternate-angle theorem without
parallels (not needed by the route below, which uses C8 instead, but available):

```lean
-- l. 117
theorem Frame.parallel_of_alternate (hS : F.IsPl S) {a b : L} (ha : LineIn a S) (hb : LineIn b S)
    {Pa Qb : P} (hA : A ∈ a) (hB : B ∈ b) (hAB : A ≠ B) (hPa : Pa ∈ a) (hQb : Qb ∈ b)
    (hopp : OppositeSides (line (Line := L) A B hAB) Pa Qb) (hc : AngCong Pa A B Qb B A) :
    ¬Meets (Point := P) a b
```

Where they are used: `Pas.mem_imLine` gives G3(9) ("the image under `ρ` of the line `CB₁` is the
line `AB`", see § 3) directly; `Pas.isom_ray` transports half-rays under `ρ`, `ρ'`, `refl m`
without `angCong_rays` book-keeping; `Pas.isom_fix_line` can replace the hand-made argument
"`Z ∈ l ↔ g Z ∈ l`" of D3 for points of the base line.

Important: do **not** `open Pas` in the new files (`Pas.refl` would compete with the root `refl` of
mathlib); write `Pas.refl`, `Pas.ht`, `Pas.isom` in full.

### 2.7 `Commentary.lean`

The definitions of § 1, and `angleSumEqTwoRight_of_parallels` (line 652) as a model of how the
frame is used in plane geometry (`set F := planeFrame (P := P) (L := L) hl`,
`F.layoff Set.univ rfl … (fun _ _ => trivial) … trivial …`, `F.crossbar rfl trivial trivial trivial
trivial …`).

---------------------------------------------------------------------------------------------------

## 3. MATHEMATICAL PROOF

### 3.0 Conventions

* A plane with groups I, II, IV is fixed (`[PlaneCongruence P L]`), together with the hypothesis
  `hl : ∀ X : P, ∃ l : L, X ∈ l` ("every point lies on a line"). This hypothesis is **necessary**:
  the one-point geometry without lines satisfies `PlaneCongruence`, and there `¬Collinear X X X`,
  every point is interior to every "angle", and most lemmas below are false. In the final theorem
  `hl` comes from `Between A C X` (part of each predicate) and `line_through_of_ne`. With `hl`,
  `¬Collinear A O B` gives `A ≠ O`, `B ≠ O`, `A ≠ B` (`ne_of_not_collinear h (hl O)`); this is used
  silently below ("genuine angle").
* `∠AOB` is the triple `A O B`; all angles that occur are genuine (non-collinear), and each time an
  `AngCong` lemma is applied the two non-collinearity hypotheses must be supplied. The proofs below
  name the reason whenever it is not immediate.
* `∠AOB < ∠A'O'B'` is the repository's `AngLt A O B A' O' B'`: both angles genuine and
  `∠AOB ≡ ∠A'O'X` for some `X` between `A'` and `B'`.
* "The line `UV`" is `line U V h`; statements "for the line `UV`" are best stated for an arbitrary
  `l : L` with `U ∈ l`, `V ∈ l` (as `ExteriorConfig` does) or converted with `eq_line` / `line_unique`.
* A **right angle** is `RightAng A O B` (`¬Collinear A O B ∧ ∃ C, Between B O C ∧ AngCong A O B A O C`).
  Its API (all Frame lemmas, no plane hypothesis): `rt_side` (move `B` along the line `OB`, also to the
  opposite half-ray), `rt_arm` (move `A` along the line `OA`), `rt_symm`, `rt_congr`, `rt_cong`.
* An **isometry** is an `f ∈ Pas.isom` (a permutation of the points preserving the congruence of
  segments); `Pas.refl l` is the reflection in the line `l`, `Pas.ht M` the half-turn about `M`.
* **Degenerate arguments.** `SegCong` and `AngCong` are unconstrained ("junk") on degenerate
  arguments: Axiom IV 2 (`AxiomIV2`, `Basic.lean` l. 1197) is stated only for `A ≠ B` etc., so
  `SegCong A A X Y` says nothing. Rule: **every lemma that transports `SegCong` or `SLt`
  (`segCong_trans`, `segCong_symm`, C2, C3) needs both distinctness hypotheses of each segment
  involved, and every lemma that transports `AngCong` needs the non-collinearity of both angles.**
  In Stages D–F every compared segment is a side of a right angle, so its `≠` comes from
  `ne_of_nc hl` of that `RightAng` (e.g. `RightAng B A C` gives `B ≠ A`, `C ≠ A`).

The proof has eight stages. Stages 0–C are tools; D–F prove that all Saccheri quadrilaterals have
summit angles of the same type; G attaches to every triangle a Saccheri quadrilateral whose type is
equivalent to each of the three predicates; H concludes.

---

### Stage 0. Plane tools and isometries (file `Aux1`)

**0.1 (wrappers).** Plane forms of Frame lemmas, each proved by instantiating `planeFrame hl` with
`S := Set.univ`: `crossbar`, `layoff`, `layoff_unique`, `interior_or_interior`,
`mem_interior_of_ray`. The Frame lemmas `rt_side`, `rt_arm`, `rt_symm`, `rt_congr`, `rt_cong`,
`sas`, `sss` need no plane argument; they can be called as `(fr hl).rt_congr …`, `(fr hl).sas …`
(short wrappers for the first four are listed in § 4.1 for convenience). Statements in § 4.

**0.2 (`mem_ray_of_angCong`).** If `∠AOB` is genuine, `O, A ∈ l`, `B, B'` lie on the same side of
`l` and `∠AOB ≡ ∠AOB'`, then `B' ∈ ray O B`.
*Proof.* `layoff_unique` with `(A O B) := (A O B)`, `O' := O`, `A' := A`, the two points `B`, `B'`
(`angCong_refl` for the first) gives `ray O B = ray O B'`; `B' ∈ ray O B'` by `mem_ray_self'`
(`B' ≠ O` because `B' ∉ l`). ∎

**0.3 (`opp_of_interior`).** If `∠AOC` is genuine, `B ∈ Interior A O C`, and `k` is a line through
`O` and `B`, then `A`, `C` lie on opposite sides of `k`.
*Proof.* `crossbar` (with `(B A C D) := (A O C B)`) gives `Y` with `Between A Y C`, `Y ∈ ray O B`;
`Y ∈ k` (`collinear_of_mem_ray`, `mem_of_collinear`, `B ≠ O` from `nc_of_interior`). `A ∉ k`:
otherwise `O, A, B` are collinear, contradicting `nc_of_interior` (`¬Collinear A O B`). Conclude with
`opp_of_between_mem`. ∎

**0.4 (`interior_trans`, order of half-rays).** If `∠AOC` is genuine, `X ∈ Interior A O C` and
`Y ∈ Interior X O C`, then `Y ∈ Interior A O C` and `X ∈ Interior A O Y`.
*Proof.* `crossbar` for `X`: `X₀` with `Between A X₀ C`, `X₀ ∈ ray O X`. Then `X ∈ ray O X₀`
(`mem_ray_comm`), and `Y ∈ Interior X₀ O C` (`mem_interior_of_rays_plane` with `X₀ ∈ ray O X`,
`C ∈ ray O C`). `∠X₀OC` is genuine (`nc_of_interior` applied to `X₀ ∈ Interior A O C`, which holds by
`mem_interior_of_between`). `crossbar` for `Y`: `Y₀` with `Between X₀ Y₀ C`, `Y₀ ∈ ray O Y`.
From `Between C Y₀ X₀` and `Between C X₀ A` (`between_symm`), `OrderLin.trans₂` gives
`Between C Y₀ A` and `Between Y₀ X₀ A`. Hence `Y₀ ∈ Interior A O C` (`mem_interior_of_between`) and
`Y ∈ Interior A O C` (`mem_interior_of_ray`, `Y ∈ ray O Y₀`). `∠AOY₀` is genuine (`nc_of_interior`),
so `X₀ ∈ Interior A O Y₀` (`mem_interior_of_between` with `Between A X₀ Y₀`), then
`X₀ ∈ Interior A O Y` (`mem_interior_of_rays_plane`, `Y ∈ ray O Y₀`), then `X ∈ Interior A O Y`
(`mem_interior_of_ray`, `X ∈ ray O X₀`). ∎

**0.5 (`sameSide_of_not_meets`).** If the lines `m`, `k` have no common point and `X, Y ∈ m`, then
`X`, `Y` lie on the same side of `k`.
*Proof.* `X, Y ∉ k`; a point of `k` between `X` and `Y` lies on `m` (`mem_mid_of_between`). ∎
(`Meets` is symmetric, `not_meets_symm`; C8, D5 and F1(b) below are used in both orders without
comment.)

**0.6 (`isom_angCong`).** If `f` is an isometry and `∠XYZ` is genuine, then `∠XYZ ≡ ∠f(X)f(Y)f(Z)`.
*Proof.* `Frame.sss` for the triangles `Y X Z` and `f(Y) f(X) f(Z)` (first conjunct), the image
being non-collinear by `Pas.isom_collinear_iff`. ∎

**0.7 (`isom_rightAng`).** Isometries map right angles to right angles. *Proof.* `rt_congr` and 0.6. ∎

**0.8 (`isom_sameSide_self`, `isom_opp_self`).** Let `f` be an isometry and `l` a line with
`Z ∈ l ↔ f Z ∈ l` for all `Z`. Then `SameSide l X Y → SameSide l (f X) (f Y)` and
`OppositeSides l X Y → OppositeSides l (f X) (f Y)`.
*Proof.* Non-membership by the hypothesis. If `W ∈ l` lies between `f X` and `f Y`, write
`W = f (f⁻¹ W)`; `f⁻¹ W ∈ l` by the hypothesis and `Between X (f⁻¹ W) Y` by `Pas.isom_between_iff`;
contradiction. If `Z ∈ l` lies between `X` and `Y`, then `f Z ∈ l` lies between `f X`, `f Y`
(`Pas.isom_between`). ∎

**0.9 (half-turns).** For `X ≠ M`: `Between X M (ht M X)` and `SegCong M X M (ht M X)`
(`(Pas.ht_eq_iff h).1 rfl`). If `M ∈ l`: `X ∈ l ↔ ht M X ∈ l` (for `X = M` by `ht_self`; otherwise
`mem_right_of_between` / `mem_left_of_between`). For `A ≠ C` and `D := Pas.midp A C`:
`ht D A = C` (`Pas.ht_midp`), `ht D C = A` (`Pas.ht_ht`), `A ≠ D` (else `ht D A = A` by `ht_self`),
hence `Between A D C`.

---

### Stage A. The order of angles (file `Aux2`)

**A1 (`angLt_of_interior`).** If `∠AOB`, `∠A'O'B'` are genuine, `X ∈ Interior A' O' B'` and
`∠AOB ≡ ∠A'O'X`, then `∠AOB < ∠A'O'B'`.
*Proof.* `crossbar` gives `Y` with `Between A' Y B'`, `Y ∈ ray O' X`; `angCong_rays` moves `X` to `Y`
(`∠A'O'X` is genuine by `nc_of_interior`). ∎

**A2 (`angLt_interior`).** If `∠AOB < ∠A'O'B'`, there is `X ∈ Interior A' O' B'` with
`∠AOB ≡ ∠A'O'X`. *Proof.* The `X` of the definition and `mem_interior_of_between`. ∎

**A3 (`angLt_congr_left`).** `∠AOB < β` and `∠AOB ≡ ∠A₁O₁B₁` (genuine) imply `∠A₁O₁B₁ < β`.
*Proof.* `angCong_symm`, `angCong_trans`. ∎

**A4 (`angLt_congr_right`).** `α < ∠A'O'B'` and `∠A'O'B' ≡ ∠A₁O₁B₁` (genuine) imply `α < ∠A₁O₁B₁`.
*Proof.* This is `Frame.angLt_congr`. ∎

Consequences (each by A3 or A4 with `angCong_swap_*` of `angCong_refl`, or `angCong_rays` of
`angCong_refl`): `angLt_swap_left` (`∠AOB < β → ∠BOA < β`), `angLt_swap_right`
(`α < ∠A'O'B' → α < ∠B'O'A'`), `angLt_rays_left`, `angLt_rays_right` (replace the points on the
sides by other points of the same half-rays).

**A5 (`angLt_irrefl`).** Not `∠AOB < ∠AOB`.
*Proof.* Let `Between A X B`, `∠AOB ≡ ∠AOX`. With `l` the line `OA`: `SameSide l X B`
(`sameSide_of_between_mem'`, `A ∈ l`, `B ∉ l`). By 0.2, `X ∈ ray O B`, so `Collinear O B X`; also
`Collinear A B X`. `eq_of_collinear_collinear` (with `(A B C) := (A O B)`) gives `X = B`,
contradicting `Between A X B`. ∎

**A6 (`angLt_trans`).** `α < β` and `β < γ` imply `α < γ`.
*Proof.* Let `β = ∠A'O'B'`, `γ = ∠A₂O₂B₂`, and `Between A₂ Y B₂`, `β ≡ ∠A₂O₂Y`. `∠A₂O₂Y` is genuine
(`nc_of_interior`). By A4, `α < ∠A₂O₂Y`: there is `W` with `Between A₂ W Y`, `α ≡ ∠A₂O₂W`.
`OrderCore.between_of_between_between₂'` gives `Between A₂ W B₂`. ∎

**A7 (`angLt_asymm`, `angLt_not_angCong`).** `α < β` excludes `β < α` and excludes `α ≡ β`.
*Proof.* A6 + A5; A3 + A5. ∎

**A8 (`angLt_trichotomy`).** For genuine `α = ∠AOB`, `β = ∠A'O'B'`: `α < β` or `α ≡ β` or `β < α`.
*Proof.* Let `l'` be the line `O'A'`. `layoff` gives `B₁` with `SameSide l' B₁ B'`,
`α ≡ ∠A'O'B₁`. If `Collinear B₁ O' B'`: `B₁ ∈ ray O' B'` (`mem_ray_of_sameSide`), so `α ≡ β`
(`angCong_rays`). Otherwise `interior_or_interior` (with `H := B₁`, `K := B'`, `L' := A'`, vertex
`O'`) gives `B' ∈ Interior B₁ O' A'` or `B₁ ∈ Interior B' O' A'`. In the second case
(`interior_swap`) A1 gives `α < β`. In the first case A1 gives `∠A'O'B' < ∠A'O'B₁` (with
`angCong_refl`) and A4 (with `∠A'O'B₁ ≡ α`) gives `β < α`. ∎

**A9 (`angLt_supp`, supplements reverse the order).** If `∠AOB < ∠A'O'B'`, `Between A O C` and
`Between A' O' C'`, then `∠C'O'B' < ∠COB`.
*Proof.* Let `Between A' X B'`, `∠AOB ≡ ∠A'O'X`. `theorem12` gives `∠BOC ≡ ∠XO'C'`, i.e. (swaps)
`∠C'O'X ≡ ∠COB`. Claim: `B' ∈ Interior C' O' X`. With `interior_iff`: (1) the line `O'C'` is the
line `O'A'`, and `SameSide (O'A') X B'` by `sameSide_of_between_mem'`; (2) let `k` be the line
`O'X`; `A', B' ∉ k` (otherwise `A', X, B'` and `O'` would be collinear), `OppositeSides k A' B'`
(`X` between), `OppositeSides k A' C'` (`O'` between; `C' ∉ k`), hence `SameSide k B' C'`
(`OrderCore.sameSide_of_opp_opp`). By A1 (`angCong_refl`) `∠C'O'B' < ∠C'O'X`, and A4 concludes. ∎

---

### Stage B. Addition of angles; types of angles (files `Aux3`, `Aux4`)

**B1 (`angLt_add`, monotonicity of addition).** Let `∠AOC`, `∠A'O'C'` be genuine,
`B ∈ Interior A O C`, `B' ∈ Interior A' O' C'`. If (`∠AOB < ∠A'O'B'` or `∠AOB ≡ ∠A'O'B'`) and
`∠BOC < ∠B'O'C'`, then `∠AOC < ∠A'O'C'`.
*Proof.*
Step 1. There is `B₁ ∈ Interior A' O' C'` with `∠AOB ≡ ∠A'O'B₁` and (`B₁ = B'` or
`B' ∈ Interior B₁ O' C'`). In the congruent case take `B₁ := B'`. In the other case A2 gives
`B₁ ∈ Interior A' O' B'` with `∠AOB ≡ ∠A'O'B₁`; apply 0.4 to the angle `∠C'O'A'` with
`X := B'` (`B' ∈ Interior C' O' A'` by `interior_swap`) and `Y := B₁` (`B₁ ∈ Interior B' O' A'`):
`B₁ ∈ Interior C' O' A'` and `B' ∈ Interior C' O' B₁`; apply `interior_swap` to both.
Step 2. `∠BOC < ∠B₁O'C'`. If `B₁ = B'` this is the hypothesis. Otherwise A1 (with `angCong_refl`)
gives `∠C'O'B' < ∠C'O'B₁` (as `B' ∈ Interior C' O' B₁`), the swaps give `∠B'O'C' < ∠B₁O'C'`, and A6.
Step 3. A2: `C₁ ∈ Interior B₁ O' C'` with `∠BOC ≡ ∠B₁O'C₁`.
Step 4. 0.4 (angle `∠A'O'C'`, `X := B₁`, `Y := C₁`): `C₁ ∈ Interior A' O' C'`, `B₁ ∈ Interior A' O' C₁`.
Step 5. `theorem14` with `(O H K M) := (O A C B)`, `(O' H' K' M') := (O' A' C₁ B₁)`: the six
angles are genuine (`nc_of_interior` for `B`, `B₁`, `C₁`); `h1 := ∠AOB ≡ ∠A'O'B₁`;
`h2 := ∠COB ≡ ∠C₁O'B₁` (swaps of Step 3); `hside` is the second alternative: `A, C` on opposite
sides of the line `OB` (0.3) and `A', C₁` on opposite sides of the line `O'B₁` (0.3 for
`B₁ ∈ Interior A' O' C₁`). Conclusion: `∠AOC ≡ ∠A'O'C₁`.
Step 6. A1 with `C₁ ∈ Interior A' O' C'`. ∎

**Definition (types).** For a triple `A O B`:
* `LtSupp A O B` : `∠AOB` genuine and `∃ C, Between A O C ∧ ∠AOB < ∠COB` ("acute");
* `EqSupp A O B` : `∠AOB` genuine and `∃ C, Between A O C ∧ ∠AOB ≡ ∠COB` ("right");
* `GtSupp A O B` : `∠AOB` genuine and `∃ C, Between A O C ∧ ∠COB < ∠AOB` ("obtuse");
* `SameType A O B A' O' B'` : the three equivalences `LtSupp ↔ LtSupp`, `EqSupp ↔ EqSupp`,
  `GtSupp ↔ GtSupp`. (Trivially reflexive, symmetric, transitive.)

**B2 (`ltSupp_iff`, `eqSupp_iff`, `gtSupp_iff`).** For *every* `C` with `Between A O C`:
`LtSupp A O B ↔ (∠AOB genuine ∧ ∠AOB < ∠COB)`, and likewise for `EqSupp`, `GtSupp`.
*Proof.* If `C₀` is the witness, `C ∈ ray O C₀` (`Pas.mem_ray_of_between_between`), so
`∠C₀OB ≡ ∠COB` (`angCong_rays` of `angCong_refl`; `∠C₀OB` is genuine by
`not_collinear_of_between`); A4 / `angCong_trans` / A3. ∎

**B3 (exclusivity).** No angle satisfies two of `LtSupp`, `EqSupp`, `GtSupp`.
*Proof.* Use one `C` for both (B2): `α < σ ∧ α ≡ σ`, `α < σ ∧ σ < α`, `α ≡ σ ∧ σ < α` are excluded
by A7 (for the last, `angCong_symm`). ∎

**B4 (`sameType_of_angCong`).** Congruent genuine angles have the same type.
*Proof.* Let `∠AOB ≡ ∠A'O'B'`, `Between A O C`, `Between A' O' C'` (`exists_beyond`). `theorem12`
and swaps give `∠COB ≡ ∠C'O'B'`. Each property transfers by A3, A4, `angCong_trans` (using B2 to
choose the supplements); the converse directions by `angCong_symm`. ∎
Corollary (`sameType_rays`): `X ∈ ray O A`, `Y ∈ ray O B` ⟹ `SameType A O B X O Y`.

**B5 (`sameType_swap`).** `SameType A O B B O A`.
*Proof.* Let `Between A O C`, `Between B O D`. `vertical_angles` (for `∠COB`, with `Between C O A`,
`Between B O D`) gives `∠COB ≡ ∠AOD`. From `∠AOB < ∠COB`: A4 gives `∠AOB < ∠AOD`, the swaps give
`∠BOA < ∠DOA`, i.e. `LtSupp B O A`. Same for the other two; the converse by symmetry of the
statement. ∎

**B6 (`ltSupp_of_angLt`, `gtSupp_of_angLt`).** If `α < β` and `LtSupp β`, then `LtSupp α`. If
`β < α` and `GtSupp β`, then `GtSupp α`.
*Proof.* Let `σ(α)`, `σ(β)` be supplements. By A9, `α < β` gives `σ(β) < σ(α)`. Then
`α < β < σ(β) < σ(α)` (A6). Second claim: `β < α` gives `σ(α) < σ(β)`, and
`σ(α) < σ(β) < β < α`. ∎

**B7 (`sameType_of_cases`).** If one of three conditions `c₁, c₂, c₃` holds and
`c₁ → LtSupp α ∧ LtSupp β`, `c₂ → EqSupp α ∧ EqSupp β`, `c₃ → GtSupp α ∧ GtSupp β`, then
`SameType α β`. *Proof.* In each case the two angles have a common type and, by B3, no other. ∎

**B8 (types from a copy of the angle on the side of its supplement).** Let `∠AOB` be genuine,
`Between A O C`, and `∠AOB ≡ ∠XOB`.
(a) `ltSupp_of_copy`: if `X ∈ Interior C O B`, then `LtSupp A O B`.
(b) `eqSupp_of_copy`: if `X ∈ ray O C`, then `EqSupp A O B`.
(c) `gtSupp_of_copy`: if `∠XOB` is genuine (`¬Collinear X O B`, an explicit hypothesis) and
`C ∈ Interior X O B`, then `GtSupp A O B`.
*Proof.* (a) `X ∈ Interior B O C` (`interior_swap`) and `∠AOB ≡ ∠BOX`: A1 gives `∠AOB < ∠BOC`; swap.
(b) `angCong_rays`. (c) A1 with `angCong_refl` (needs `∠BOC` genuine — from `h` and `Between A O C`
— and `∠BOX` genuine — the extra hypothesis; note that `AngCong A O B X O B` does **not** give it,
since `AngCong` is unconstrained on degenerate triples, and `C ∈ Interior X O B` gives it only by
unfolding `Interior`): `∠BOC < ∠BOX`; A4 with `∠BOX ≡ ∠BOA`; swaps. At the only use (G7, `Pos₊`,
with `X := A₁`, `O := C`, `B := H`) the extra hypothesis is the field `TriConf.ncH'`. ∎

---

### Stage C. Comparison of segments; perpendiculars (file `Aux5`)

**Definition.** `SLt A B C D` (`AB < CD`): `∃ X, Between C X D ∧ SegCong A B C X`.

**C1 (`sLt_trichotomy`).** For `A ≠ B`, `C ≠ D`: `SLt A B C D ∨ SegCong A B C D ∨ SLt C D A B`.
*Proof.* `segCong_layoff`: `X ∈ ray C D`, `SegCong A B C X`. `mem_ray_cases` (for `X` and
`D ∈ ray C D`): `X = D` (middle), `Between C X D` (left), or `Between C D X`. In the last case lay
`CD` off on `ray A B`: `Y ∈ ray A B`, `SegCong C D A Y`; `between_of_segCong_ray` (with
`Between C D X`, `SegCong C D A Y`, `SegCong C X A B`) gives `Between A Y B`. ∎

**C2 (`sLt_congr_left`, `sLt_congr_right`).** `SLt` is compatible with congruence of either
segment, **provided the compared segments are genuine**: left version with `A ≠ B`, `A' ≠ B'`;
right version with `A ≠ B` and `C' ≠ D'` (the hypothesis `A ≠ B` is indispensable: the step
`SegCong A B C X`, `SegCong C X C' X'` ⟹ `SegCong A B C' X'` is `segCong_trans`, which needs
`A ≠ B`, and nothing in `SLt A B C D` forces it, because `SegCong A A _ _` is unconstrained).
*Proof.* Left: `segCong_trans`. Right (`SegCong C D C' D'`): let `Between C W D`,
`SegCong A B C W`; `C ≠ W`; `segCong_layoff` gives `W' ∈ ray C' D'` with `SegCong C W C' W'`;
`between_of_segCong_ray` (with `Between C W D`, `SegCong C W C' W'`, `SegCong C D C' D'`) gives
`Between C' W' D'`; `segCong_trans` (with `A ≠ B`, `C ≠ W`, `C' ≠ W'`) gives `SegCong A B C' W'`.
(This proof compiled, see R12.) ∎

**C3 (`sLt_exists_beyond`).** If `SLt A B C D` (`A ≠ B`), there is `E` with `Between A B E` and
`SegCong C D A E`. *Proof.* Lay `CD` off on `ray A B` (`E`); `between_of_segCong_ray` with
`Between C X D`, `B ∈ ray A E` (`mem_ray_comm`), `SegCong C X A B`, `SegCong C D A E`. ∎

**C4 (`between_refl_of_rightAng`).** If `G, F ∈ l` and `RightAng G F X`, then
`Between X F (Pas.refl l X)`.
*Proof.* `X ∉ l` (the angle is genuine). Let `X' := refl l X`; `OppositeSides l X X'`
(`Pas.refl_opp`). By definition of `RightAng` there is `C` with `Between X F C`,
`∠GFX ≡ ∠GFC`. By 0.6 for `refl l` (which fixes `G`, `F`): `∠GFX ≡ ∠GFX'`. `C` and `X'` are on the
same side of `l` (both opposite to `X`: `opp_of_between_mem`, `OrderCore.sameSide_of_opp_opp`).
`layoff_unique` (angle `G F X`, line `l`, `O' := F`, `A' := G`, points `C`, `X'`) gives
`ray F C = ray F X'`, so `X' ∈ ray F C`; `between_of_mem_rays` (`Between X F C`, `X ∈ ray F X`,
`X' ∈ ray F C`) gives `Between X F X'`. ∎

**C5 (`no_two_right`).** `RightAng F' F X` and `RightAng F F' X` are contradictory.
*Proof.* Let `l` be the line `FF'` (`F ≠ F'`), `X' := refl l X ≠ X`. By C4 twice, `Between X F X'`
and `Between X F' X'`; so `F`, `F'` lie on the line `XX'`, which is therefore `l`; but `X ∉ l`. ∎

**Definition.** `Foot l X F` : `F ∈ l ∧ X ∉ l ∧ ∀ G ∈ l, G ≠ F → RightAng G F X`.

**C6 (`exists_foot`, `foot_of_rightAng`, `foot_unique`, `foot_map`).**
(a) For `X ∉ l` there is `F` with `Foot l X F`.
(b) If `G, F ∈ l` and `RightAng G F X`, then `Foot l X F`.
(c) `Foot l X F` and `Foot l X F'` imply `F = F'`.
(d) If `f` is an isometry with `f Z ∈ l` for all `Z ∈ l`, then `Foot l X F → Foot l (f X) (f F)`.
*Proof.* (a) `Pas.refl_opp` gives `F ∈ l` with `Between X F (refl l X)`. For `G ∈ l`, `G ≠ F`:
`∠GFX` is genuine and `∠GFX ≡ ∠GF(refl l X)` by 0.6; this is `RightAng G F X` (witness
`C := refl l X`). (b) For `G' ∈ l`, `G' ≠ F`: `rt_arm`. (c) If `F ≠ F'`: `RightAng F' F X` and
`RightAng F F' X` contradict C5. (d) Choose `G₀ ∈ l`, `G₀ ≠ F` (`exists_two_points`); 0.7 gives
`RightAng (f G₀) (f F) (f X)` with `f G₀, f F ∈ l`; apply (b). ∎

**C7 (`rightAng_collinear`).** `RightAng G F X` and `RightAng G F Y` imply `Collinear F X Y`.
*Proof.* Let `l` be the line `GF`; `X, Y ∉ l`. If `SameSide l X Y`: `rt_cong` and 0.2 give
`Y ∈ ray F X`. Otherwise `OppositeSides l X Y`; let `Between X F C` (`exists_beyond`); `C` and `Y`
are on the same side of `l`, `RightAng G F C` (`rt_side`), so `Y ∈ ray F C` as before, and `C`,
hence `Y`, lies on the line `FX`. ∎

**C8 (`perp_not_meets`).** Let `F, X ∈ a`, `F', Y ∈ b`, `RightAng F' F X`, `RightAng F F' Y`. Then
`a` and `b` have no common point ("two perpendiculars to the line `FF'` do not meet").
*Proof.* Let `Z ∈ a ∩ b`. `Z ≠ F` (otherwise `F ∈ b`, and `F, F', Y` are collinear), `Z ≠ F'`.
`rt_side` gives `RightAng F' F Z` and `RightAng F F' Z`, contradicting C5. ∎

**C9 (`sameSide_perp`).** Let `F, X ∈ a`, `RightAng F' F X`, `RightAng F F' W`. Then
`SameSide a W F'`.
*Proof.* Let `b` be the line `F'W`. By C8, `a` and `b` do not meet; 0.5. ∎

**C10 (`exists_perp_at`).** For `F ∈ l` there is a line `m ∋ F` such that `RightAng G F Z` for all
`Z ∈ m`, `Z ≠ F` and all `G ∈ l`, `G ≠ F`.
*Proof.* Choose `G₀ ∈ l`, `G₀ ≠ F`; `G₁ := Pas.ht F G₀`, so `Between G₀ F G₁` and
`SegCong F G₀ F G₁` (0.9). `Pas.exists_eqd` (for `G₀ ≠ G₁`) gives `m` with
`Z ∈ m ↔ Z ≠ G₀ ∧ Z ≠ G₁ ∧ SegCong Z G₀ Z G₁`, `refl m G₀ = G₁` and `OppositeSides m G₀ G₁`. `F ∈ m`.
Let `Z ∈ m`, `Z ≠ F`. `m ≠ l` (`G₀ ∉ m`), so `Z ∉ l` (`eq_of_mem_of_mem`), and `∠G₀FZ` is genuine.
0.6 for `refl m` (fixing `F`, `Z`): `∠G₀FZ ≡ ∠G₁FZ`; with swaps this is `RightAng Z F G₀` (witness
`C := G₁`). `rt_symm`, then `rt_arm` to an arbitrary `G ∈ l`, `G ≠ F`. ∎

---

### Stage D. Exterior angle; quadrilaterals with two right angles; Saccheri quadrilaterals (files `Aux6`, `Aux7`)

**D1 (`ext_angle`, exterior angle theorem).** If `A, B, C` are not collinear and `Between B C D`,
then `∠BAC < ∠ACD` and `∠ABC < ∠ACD`.
*Proof.* First claim. Let `M := Pas.midp A C`, `f := Pas.ht M`, so `f A = C`, `f C = A`,
`Between A M C` (0.9). `B ≠ M` (`M` is on the line `AC`, `B` is not); `B' := f B`, `Between B M B'`.
By 0.6 (`∠BAC` genuine): `∠BAC ≡ ∠B'CA`, hence (`angCong_swap_right`) `∠BAC ≡ ∠ACB'`
(`∠B'CA` is genuine as an image). Claim: `B' ∈ Interior A C D`; with `interior_iff`
(`A ≠ C`, `D ≠ C`):
(1) `SameSide (line CA) B' D`: `B, B'` are on opposite sides of the line `AC` (`M` between, `M` on the
line, `B` off it), and `B, D` are on opposite sides (`C` between; `D` is off the line `AC`,
otherwise `B` would be on it); `OrderCore.sameSide_of_opp_opp`.
(2) `SameSide (line CD) B' A`: the line `CD` is the line `BC` =: `n`. `SameSide n M A`
(`sameSide_of_between_mem'` with `C ∈ n`, `A ∉ n`, `Between C M A`); in particular `M ∉ n`, so
`B' ∉ n` (otherwise the line `BB' = n` contains `M`); `SameSide n M B'`
(`sameSide_of_between_mem'` with `B ∈ n`, `Between B M B'`); `OrderCore.sameSide_trans`.
A1 gives `∠BAC < ∠ACD` (`∠ACD` is genuine: `D ∉ line AC`).
Second claim. Let `Between A C E` (`exists_beyond`). The first claim for the triangle `B A C`
(roles: `A := B`, `B := A`, `C := C`, `D := E`; `¬Collinear B A C`) gives `∠ABC < ∠BCE`.
`vertical_angles` (`∠BCE` genuine, `Between B C D`, `Between E C A`) gives `∠BCE ≡ ∠DCA`; A4 and
`angLt_swap_right`. ∎

**Definitions.**
* `BiRight A B C D` : `A ≠ B`, `RightAng B A C`, `RightAng A B D`, and `C, D` on the same side of
  every line through `A`, `B`. (Base `AB`; `C` "above" `A`, `D` "above" `B`.)
* `Saccheri A B C D` : `BiRight A B C D ∧ SegCong A C B D`. (Summit `CD`, summit angles `∠ACD`, `∠BDC`.)
* `Lambert M B D N` : `RightAng B M N`, `RightAng M B D`, `RightAng M N D` (three right angles, at
  `M`, `B`, `N`; fourth angle `∠BDN`).

**D2 (basic facts on `BiRight A B C D`).** With `l` the line `AB`:
(a) `biRight_symm`: `BiRight B A D C` (`sameSide_symm'`).
(b) `C, D ∉ l`; the lines `AC` and `BD` have no common point (C8 with `RightAng B A C`,
`RightAng A B D`); hence `D ∉ line AC`, `C ∉ line BD`, `C ≠ D`, `∠ACD` and `∠BDC` are genuine.
(c) `SameSide (line AC) B D` and `SameSide (line BD) A C` (C9).

**D3 (`saccheri_refl`).** Let `Saccheri A B C D`. There are a line `m` and points `M, N ∈ m` such
that `refl m A = B`, `refl m C = D`, `Between A M B`, `Between C N D`, and `Lambert M B D N`.
*Proof.* `Pas.exists_eqd` for `A ≠ B`: a line `m` with `refl m A = B` and
`OppositeSides m A B`; so `A, B ∉ m` and there is `M ∈ m` with `Between A M B`. Put `g := refl m`;
`g B = A` (`Pas.refl_refl`). Let `l` be the line `AB`. `Z ∈ l ↔ g Z ∈ l`: if `Z ∈ l`, then
`Collinear A B Z` gives `Collinear B A (g Z)` (`Pas.isom_collinear`); conversely apply this to `g Z`
and `g (g Z) = Z`. `m ≠ l` (`A ∉ m`), so there is `W ∈ m`, `W ∉ l` (`exists_mem_not_mem`), and
`g W = W`. Let `C' := g C`; `C' ∉ l`.
`SameSide l C C'`: by `sameSide_or_opp'` for `C`, `W`. If `SameSide l C W`, then `SameSide l C' W`
(0.8) and conclude by transitivity. If `OppositeSides l C W`, then `OppositeSides l C' W` (0.8) and
conclude by `OrderCore.sameSide_of_opp_opp`. Hence `SameSide l C' D`.
`RightAng A B C'` (0.7 applied to `RightAng B A C`). By `rt_cong`, `∠ABD ≡ ∠ABC'`; by 0.2,
`C' ∈ ray B D`. `SegCong B C' B D` (`g` gives `SegCong A C B C'`; with `SegCong A C B D`,
`segCong_symm`/`segCong_trans`). `eq_of_segCong_ray'` gives `C' = D`. So `g C = D`, `g D = C`.
`C ∉ m` (otherwise `D = g C = C`, against D2(b)); `Pas.refl_opp` gives `OppositeSides m C D`:
`N ∈ m` with `Between C N D`. `N ∉ l` (`C, D` on the same side of `l`), so `M ≠ N` and `m` is the
line `MN`.
`RightAng B M N`: `∠AMN` is genuine (`N ∉ l`, `A ≠ M`); 0.6 for `g` gives `∠AMN ≡ ∠BMN`; with swaps
this is `RightAng N M A` (witness `B`, `Between A M B`); `rt_side` to `B`, `rt_symm`.
`RightAng M B D`: `rt_arm` from `RightAng A B D` (`M ≠ B` by `ne23_of_between` from
`Between A M B`; `Collinear B A M` from `collinear_of_between` and a permutation).
`RightAng M N D`: `M` is not on the line `CD` (otherwise that line contains `M ≠ N`, both in `m`, so
it is `m`, and `C ∈ m`); so `∠CNM` is genuine; 0.6 for `g`: `∠CNM ≡ ∠DNM`; with swaps this is
`RightAng M N C` (witness `D`); `rt_side` to `D`. ∎

**D4 (`saccheri_summit`).** `Saccheri A B C D` implies `∠ACD ≡ ∠BDC`.
*Proof.* 0.6 for `g = refl m` of D3: `∠ACD ≡ ∠g(A)g(C)g(D) = ∠BDC`. ∎

**D5 (`saccheri_not_meets`).** In a Saccheri quadrilateral the line of the base and the line of
the summit have no common point.
*Proof.* With `M, N` of D3: `RightAng N M B` (`rt_symm`) and `RightAng M N D`; C8 for the line
`AB ∋ M, B` and the line `CD ∋ N, D`. ∎

**D6 (`biRight_lt`, `biRight_gt`).** Let `BiRight A B C D`.
(a) If `SLt A C B D`, then `∠BDC < ∠ACD`.
(b) If `SLt B D A C`, then `∠ACD < ∠BDC`.
*Proof.* (a) Let `Between B E D`, `SegCong A C B E`. `Saccheri A B C E`: `RightAng A B E`
(`rt_side`), `SameSide l C E` (transitivity with `SameSide l E D` from
`sameSide_of_between_mem'`). By D4, `∠ACE ≡ ∠BEC`. By D5 the line `CE` does not meet `l`.
Claim: `E ∈ Interior A C D`. `interior_or_interior` at the vertex `C` with `L' := A`, `H := E`,
`K := D`: hypotheses `¬Collinear E C A` (`E ∉ line AC`, as `E` is on the line `BD`, D2(b)),
`SameSide (line CA) E D` (0.5: the lines `BD` and `AC` do not meet), `¬Collinear E C D`
(`C ∉ line BD`). It gives `D ∈ Interior E C A` or `E ∈ Interior D C A`. The first is impossible: it
gives `SameSide (line CE) D A`; but `OppositeSides (line CE) B D` (`E` between; `B ∉ line CE` by D5)
and `SameSide (line CE) A B` (0.5 and D5), hence `OppositeSides (line CE) A D`. So
`E ∈ Interior D C A = Interior A C D`.
A1 (with `angCong_refl`): `∠ACE < ∠ACD`; A3: `∠BEC < ∠ACD`.
D1 for the triangle `C, D, E` (roles `A := C`, `B := D`, `C := E`, `D := B`; `Between D E B`):
`∠CDE < ∠CEB`. As `E ∈ ray D B`, `∠CDE` is `∠CDB`; with the swaps `∠BDC < ∠BEC`. A6. 
(b) Apply (a) to `BiRight B A D C`. ∎

---

### Stage E. The outside lemma (files `Aux8`, `Aux8b`)

Setting for E1–E4: `Saccheri A B C D`; `l` the line `AB`, `s` the line `CD`; `Between C D P`
(`P` on the summit line beyond `D`); `Between A B Q`; `RightAng B Q P` (so `Q` is the foot of `P` on
`l`). By D5, `l` and `s` do not meet; `P ∈ s`. Let `q` be the line `QP` (`Q ≠ P`: `RightAng B Q P`
is genuine), `a` the line `AC`, `b` the line `BD`. By C8: `q` does not meet `a`
(`RightAng Q A C` by `rt_arm` from `RightAng B A C` with `Q ≠ A`, `Collinear A B Q`;
`RightAng A Q P` by `rt_arm` from `RightAng B Q P` with `A ≠ Q`, `Collinear Q B A`), and `q` does
not meet `b` (`RightAng Q B D` by `rt_arm`, `B ≠ Q`; `RightAng B Q P`); `a` and `b` do not meet (D2).

**E0 (incidence facts of the setting; Lean: the structure `OutConf`, § 4.8).** In addition:
(i) `Q ∈ l` (`Collinear A B Q`), `A, B, Q` pairwise distinct (`Between A B Q`).
(ii) `P ∉ l` and `Q ∉ s` (both because `l ∩ s = ∅`, D5; `P ∈ s`, `Q ∈ l`).
(iii) `s ≠ q`: `Q ∈ q` but `Q ∉ s`. Consequently `s ∩ q = {P}`: two distinct lines have at most
one common point (`eq_of_mem_of_mem`), and `P` is common.
(iv) `A ∉ q`: otherwise `q` contains `Q` and `A`, which are distinct points of `l`, so `q = l`
(`line_unique`); but `P ∈ q` and `P ∉ l` (ii). Likewise `B ∉ q` (with `B ≠ Q`).
(v) `C, D ∉ q`: `C ∈ a`, `D ∈ b`, and `q` meets neither `a` nor `b`.
(vi) `C, A ∉ b` and `D, B ∉ a` (as `a ∩ b = ∅`); `C, D ∉ l`, `A, B ∉ s` (as `l ∩ s = ∅`).
Every side-of-a-line statement below is then one application of 0.5 (`sameSide_of_not_meets`, for
two points of a line not meeting the given one) or of `sameSide_of_between_mem'` /
`opp_of_between_mem` (for a betweenness with an endpoint on the given line), and every membership
in an angle interior is one application of `mem_interior_iff` (4.1) to two such statements.

**E1 (auxiliary quadrilaterals).** Let `E ∈ q`, `E ≠ Q`, with `SameSide l E P` and
`SegCong B D Q E`. Then `Saccheri B Q D E` and `Saccheri A Q C E`; consequently
`∠BDE ≡ ∠QED`, `∠ACE ≡ ∠QEC` (D4), and the lines `DE`, `CE` do not meet `l` (D5).
*Proof.* `RightAng Q B D`, `RightAng B Q E` (`rt_side` from `RightAng B Q P`), `SameSide l D E`
(`D, P ∈ s`: 0.5; then transitivity); `RightAng Q A C`, `RightAng A Q E` (`rt_arm`),
`SameSide l C E`; `SegCong A C Q E` by transitivity (`segCong_trans` with `A ≠ C`, `B ≠ D`,
`Q ≠ E`, after `segCong_symm`). Additional facts recorded with E1 (Lean: the structure `OutAux`):
`E ∉ l` (from `SameSide l E P`); the line `d := DE` and the line
`c := CE` exist (`D ≠ E`, `C ≠ E`, since `C, D ∉ q`, E0(v)) and do not meet `l` (D5 for the two
auxiliary quadrilaterals). Separately (E1 is also used with `E := P` in E4, where it fails):
if `E ∈ q` and `E ≠ P`, then `E ∉ s`, because by E0(iii) `s ∩ q = {P}` (Lean: `outConf_not_mem_s`).
∎

**E2 (`saccheri_out_lt`).** If `SLt B D Q P`, then `∠ACD < ∠BDP`.
*Proof.* Let `Between Q E P`, `SegCong B D Q E`; E1 applies (`SameSide l E P` by
`sameSide_of_between_mem'`). `E ∉ s`: by E0(iii) `s ≠ q` and `s ∩ q = {P}`, and `E ≠ P`
(`Between Q E P`); Lean: `outConf_not_mem_s`.
(f1) `E ∈ Interior B D P`: `SameSide (line DB) E P` (0.5: `q` does not meet the line `BD`);
`SameSide s E B`: `SameSide s E Q` (`sameSide_of_between_mem'`, `P ∈ s`, `Q ∉ s`,
`Between P E Q`) and `SameSide s Q B` (0.5).
(f2) `E ∈ Interior A C D`: `SameSide (line CA) E D`: `SameSide (CA) E Q` (0.5), `SameSide (CA) B Q`
(`sameSide_of_between_mem'` with `A ∈ CA`, `Between A B Q`), `SameSide (CA) B D` (D2(c)).
`SameSide s E A`: `SameSide s E Q` and `SameSide s Q A` (0.5).
(f3) `C ∈ Interior Q E D`: `SameSide q C D`: `SameSide q A C`, `SameSide q B D` (0.5),
`SameSide q B A` (`sameSide_of_between_mem'` with `Q ∈ q`, `A ∉ q` (E0(iv)), `Between Q B A`).
`SameSide (line ED) C Q`: `OppositeSides (ED) C P` (`D` between; `C ∉ ED`: otherwise the line `ED` contains `C ≠ D`, so it
is `s`, and `E ∈ s`) and
`OppositeSides (ED) Q P` (`E` between; `Q ∉ ED` because `Q ∈ l` and `d ∩ l = ∅` by E1);
`OrderCore.sameSide_of_opp_opp`.
(f4) D1 for the triangle `E, C, D` and `Between C D P`: `∠ECD < ∠EDP`.
From (f3), A1: `∠QEC < ∠QED`; with E1 (A3, A4): `∠ACE < ∠BDE`.
B1 with vertex `C`, triple `(A, E, D)` and vertex `D`, triple `(B, E, P)`: hypotheses (f2), (f1),
`∠ACE < ∠BDE`, `∠ECD < ∠EDP`. Conclusion: `∠ACD < ∠BDP`. ∎

**E3 (`saccheri_out_gt`).** If `SLt Q P B D`, then `∠BDP < ∠ACD`.
*Proof.* C3: `E` with `Between Q P E`, `SegCong B D Q E`; E1 applies (`SameSide l E P` by
`sameSide_of_ray`). `E ∉ s` (E0(iii), `E ≠ P` from `Between Q P E`; `outConf_not_mem_s`).
(g1) `P ∈ Interior B D E`: `SameSide (line DB) P E` (0.5); `SameSide (line DE) P B`:
`SameSide (DE) P Q` (`sameSide_of_between_mem'`, `E ∈ DE`, `Q ∉ DE` (`Q ∈ l`, `d ∩ l = ∅`),
`Between E P Q`) and
`SameSide (DE) Q B` (0.5, E1).
(g2) `P ∈ Interior A C E`: `SameSide (line CA) P E` (0.5); `SameSide (line CE) P A`:
`SameSide (CE) P Q` and `SameSide (CE) Q A` (0.5, E1).
(g3) `D ∈ Interior Q E C`: `SameSide q D C` (as in (f3), using `A ∉ q`); `SameSide (line EC) D Q`:
`SameSide (EC) D P` (`sameSide_of_between_mem'`, `C ∈ EC`, `P ∉ EC` — otherwise the line `EC`
contains `C ≠ P`, so it is `s`, and `E ∈ s` —, `Between C D P`) and
`SameSide (EC) P Q` (`sameSide_of_between_mem'`, `E ∈ EC`, `Q ∉ EC` (`Q ∈ l`, `c ∩ l = ∅`),
`Between E P Q`).
(g4) D1: `∠ECD < ∠EDP`.
From (g3), A1 and E1: `∠BDE < ∠ACE`.
By A8 for `∠BDP`, `∠ACD`: if `∠BDP < ∠ACD` we are done. Otherwise `∠ACD < ∠BDP` or
`∠ACD ≡ ∠BDP`. As `P ∈ ray C D`, the same holds with `∠ACP` in place of `∠ACD`; and (g4) reads
`∠PCE < ∠PDE`. B1 with vertex `C`, triple `(A, P, E)` and vertex `D`, triple `(B, P, E)`:
`∠ACE < ∠BDE`, contradicting `∠BDE < ∠ACE` (A7). ∎

**E4 (`saccheri_out_eq`).** If `SegCong B D Q P`, then `∠ACD ≡ ∠BDP`.
*Proof.* E1 with `E := P`: `∠BDP ≡ ∠QPD` and `∠ACP ≡ ∠QPC`. `D ∈ ray P C`, `P ∈ ray C D`:
`∠QPD` is `∠QPC` and `∠ACP` is `∠ACD` (`angCong_rays`). ∎

**E5 (`saccheri_out_type`).** In the setting above:
`SLt B D Q P → LtSupp C D B`; `SegCong B D Q P → EqSupp C D B`; `SLt Q P B D → GtSupp C D B`.
*Proof.* `P` is a supplement point of `∠CDB` (`Between C D P`). By D4, `∠ACD ≡ ∠BDC`. E2 gives
`∠BDC < ∠BDP`, i.e. `∠CDB < ∠PDB`; E4 gives `∠CDB ≡ ∠PDB`; E3 gives `∠PDB < ∠CDB`. ∎

*Remark (why this lemma is the heart of the matter).* The comparison (D6) of the sides of a
quadrilateral with two right angles only relates angles at the summit of *one* quadrilateral; it is
compatible with a distance function along the summit line that first decreases and then increases.
E2–E3 exclude this, and they need the exterior angle theorem for the triangle `C D E` together with
the monotonicity of angle addition (B1).

---

### Stage F. Lambert quadrilaterals; all Saccheri quadrilaterals have the same type (files `Aux9`, `Aux10`)

**F1 (basic facts on `Lambert M B D N`).**
(a) `lambert_symm`: `Lambert M N D B` (`rt_symm` for the angle at `M`).
(b) The line `MB` and the line `ND` do not meet (C8 with `RightAng N M B`, `RightAng M N D`); the
line `MN` and the line `BD` do not meet (C8 with `RightAng B M N`, `RightAng M B D`).
(c) `lambert_nc`: `B, D, N` are not collinear (otherwise `N` lies on the line `BD` and on the line
`MN`); `M, B, N, D` are pairwise distinct.

**F2 (`lambert_double`).** Let `Lambert M B D N`, `t` the line `MN`, `g := Pas.refl t`. Then
`Between B M (g B)`, `Between D N (g D)`, `Saccheri (g B) B (g D) D`, and `∠BDN ≡ ∠(g B)(g D)N`.
*Proof.* C4 with `RightAng N M B` and with `RightAng M N D`. `RightAng (g B) B D` (`rt_arm` from
`RightAng M B D`); its image under `g` (0.7, `g (g B) = B`) is `RightAng B (g B) (g D)`. The line
through `g B`, `B` is the line `MB`; `g D` and `D` lie on the line `ND`, which does not meet it
(F1(b)): same side by 0.5. `SegCong (g B) (g D) B D` because `g` is an isometry. The congruence of
angles is 0.6 (`g N = N`). ∎

**F3 (`lambert_cut`).** Let `Lambert M B D N` and `Between M B₀ B`. There is `D₁` with
`Between N D₁ D` and `Lambert M B₀ D₁ N`.
*Proof.* Let `l` be the line `MB`. C10 at `B₀ ∈ l`: a line `m ∋ B₀`, perpendicular to `l`. Choose
`Z₀ ∈ m`, `Z₀ ≠ B₀`. C9 (line `m`, `F := B₀`, `X := Z₀`) with `RightAng M B₀ Z₀` and
`RightAng B₀ M N` (`rt_arm`): `SameSide m N M`. Likewise with `RightAng B B₀ Z₀` and
`RightAng B₀ B D`: `SameSide m D B`. `OppositeSides m M B` (`opp_of_between_mem`). Hence
`OppositeSides m N D` (`OrderCore.opp_of_sameSide_opp` twice): there is `D₁ ∈ m` with
`Between N D₁ D`. `D₁ ≠ B₀` (`D₁` is on the line `ND`, which does not meet `l`, F1(b)).
`RightAng B₀ M N` (`rt_arm`), `RightAng M B₀ D₁` (C10), `RightAng M N D₁` (`rt_side`). ∎

**F4 (`lambert_nest`).** Let `Lambert M B D N`, `Between M B₀ B`, `Between N D₁ D`,
`Lambert M B₀ D₁ N`. Then `SameType B D N B₀ D₁ N`.
*Proof.* Let `t` be the line `MN`, `g := refl t`, `B₀* := g B₀`, `D₁* := g D₁`. By F2 for the small
quadrilateral: `Between B₀ M B₀*`, `Between D₁ N D₁*`, `Σ := Saccheri B₀* B₀ D₁* D₁`, and
`∠B₀D₁N ≡ ∠B₀*D₁*N`. Order on the two lines (`OrderLin.trans₁`): from `Between B₀* M B₀`,
`Between M B₀ B`: `Between B₀* B₀ B`; from `Between D₁* N D₁`, `Between N D₁ D`:
`Between D₁* N D` and `Between D₁* D₁ D`.
Let `x := B₀D₁`, `h := BD`. By C1: `SLt B₀ D₁ B D` (`x < h`), or `SegCong B₀ D₁ B D`, or
`SLt B D B₀ D₁`.
*The type of `∠B₀D₁N`.* E5 for `Σ` with `P := D`, `Q := B` (`Between D₁* D₁ D`,
`Between B₀* B₀ B`, `RightAng B₀ B D` by `rt_arm`): in the three cases `LtSupp D₁* D₁ B₀`,
`EqSupp D₁* D₁ B₀`, `GtSupp D₁* D₁ B₀`. As `N ∈ ray D₁ D₁*`, B4 (`sameType_rays`) and B5 turn this
into `LtSupp B₀ D₁ N`, `EqSupp B₀ D₁ N`, `GtSupp B₀ D₁ N`.
*Comparison of the two angles.* `Q₂ := BiRight B₀* B D₁* D`: `RightAng B B₀* D₁*` (`rt_arm` from
`Σ`), `RightAng B₀* B D` (`rt_arm`), `D₁*, D` on the same side of `l` (0.5, F1(b)). Its sides are
`B₀*D₁* ≡ x` and `BD = h`; its summit angles are `∠B₀*D₁*D`, which is `∠B₀*D₁*N` (as
`D ∈ ray D₁* N`) `≡ ∠B₀D₁N`, and `∠BDD₁*`, which is `∠BDN` (as `D₁* ∈ ray D N`).
- `x < h`: D6(a) for `Q₂` (`SLt B₀* D₁* B D` by `sLt_congr_left`, with `B₀ ≠ D₁`, `B₀* ≠ D₁*`
  from the right angles at `B₀`, `B₀*`, and `SegCong B₀ D₁ B₀* D₁*` from `g`): `∠BDD₁* < ∠B₀*D₁*D`, i.e. `∠BDN < ∠B₀D₁N`;
  B6: `LtSupp B D N`.
- `x ≡ h`: `Saccheri B₀* B D₁* D`; D4: `∠B₀*D₁*D ≡ ∠BDD₁*`, i.e. `∠B₀D₁N ≡ ∠BDN`; B4: `EqSupp B D N`.
- `h < x`: D6(b) (`SLt B D B₀* D₁*` by `sLt_congr_right`, with `B ≠ D` — this is where its
  hypothesis `A ≠ B` is used — and `B₀* ≠ D₁*`): `∠B₀*D₁*D < ∠BDD₁*`, i.e. `∠B₀D₁N < ∠BDN`; B6: `GtSupp B D N`.
B7 concludes. ∎

**F5 (`lambert_shrink`, `lambert_shrink2`).** Let `Lambert M B D N`.
(a) If `B₀ = B` or `Between M B₀ B`, there is `D₁` with `Lambert M B₀ D₁ N` and
`SameType B D N B₀ D₁ N`.
(b) If moreover `N₀ = N` or `Between M N₀ N`, there is `D₀` with `Lambert M B₀ D₀ N₀` and
`SameType B D N B₀ D₀ N₀`.
*Proof.* (a) Trivial if `B₀ = B`; otherwise F3 and F4. (b) By (a) get `D₁`; F1(a):
`Lambert M N D₁ B₀`; by (a) again (shrinking `N` to `N₀`) get `D₀` with `Lambert M N₀ D₀ B₀` and
`SameType N D₁ B₀ N₀ D₀ B₀`; F1(a) and B5 (`∠ND₁B₀` and `∠B₀D₁N` have the same type, etc.). ∎

**F6 (`lambert_unique`).** `Lambert M B D N` and `Lambert M B D' N` imply `D = D'`.
*Proof.* C7: `Collinear B D D'` and `Collinear N D D'`. If `D ≠ D'`, the line `DD'` contains `B`
and `N`, so `B, D, N` are collinear, against F1(c). ∎

**F7 (`lambert_transport`).** Let `Lambert M' B' D' N'`, `RightAng B₁ M N₁`,
`SegCong M' B' M B₁`, `SegCong M' N' M N₁`. There is `D₁` with `Lambert M B₁ D₁ N₁` and
`SameType B' D' N' B₁ D₁ N₁`.
*Proof.* `rt_cong`: `∠B'M'N' ≡ ∠B₁MN₁`. `Frame.sas` for the triangles `M'B'N'`, `MB₁N₁`:
`SegCong B' N' B₁ N₁`. `Pas.exists_isom_of_tri`: an isometry `f` with `f M' = M`, `f B' = B₁`,
`f N' = N₁`. `D₁ := f D'`; the three right angles by 0.7; the type by 0.6 and B4. ∎

**F8 (`lambert_sameType`).** Any two Lambert quadrilaterals `M B D N`, `M' B' D' N'` satisfy
`SameType B D N B' D' N'`.
*Proof.* `segCong_layoff`: `B₁ ∈ ray M B` with `SegCong M' B' M B₁`, `N₁ ∈ ray M N` with
`SegCong M' N' M N₁`. `RightAng B₁ M N₁` (`rt_arm`, `rt_side`). F7: `D₁`, `Lambert M B₁ D₁ N₁`,
same type as the second quadrilateral. By `mem_ray_cases` (`B₁`, `B ∈ ray M B`) there is `B₀` with
(`B₀ = B` or `Between M B₀ B`) and (`B₀ = B₁` or `Between M B₀ B₁`): take `B₀ := B₁` if `B₁ = B` or
`Between M B₁ B`, and `B₀ := B` if `Between M B B₁`. Likewise `N₀`. F5(b) twice: `D₀`, `D₀'` with
`Lambert M B₀ D₀ N₀`, `Lambert M B₀ D₀' N₀`, of the types of `M B D N` and of `M B₁ D₁ N₁`. F6:
`D₀ = D₀'`. Chain the four `SameType`. ∎

**F9 (`saccheri_sameType`).** Any two Saccheri quadrilaterals `A B C D`, `A' B' C' D'` satisfy
`SameType A C D A' C' D'`.
*Proof.* D3: `Lambert M B D N` with `Between C N D`; D4 and B4: `SameType A C D B D C`;
`N ∈ ray D C` and B4: `SameType B D C B D N`. Same for the second; F8. ∎

---

### Stage G. Triangles (files `Aux11`, `Aux12`, `Aux12b`, `Aux13`, `Aux14`)

Let `A, B, C` be non-collinear. Notation: `D := midp A C`, `E := midp B C`, `ρ := ht D`,
`ρ' := ht E`; so `Between A D C`, `Between B E C`, `ρ A = C`, `ρ C = A`, `ρ' B = C`, `ρ' C = B` (0.9).

**G1 (the midline).** `D ≠ E`; let `e` be the line `DE`. Then `A, B, C ∉ e`, and `A, B` are on the
same side of `e`.
*Proof.* The lines `AC` and `CB` are distinct and meet only in `C`; `D ≠ C` is on the first,
`E ≠ C` on the second: `D ≠ E`. If `A ∈ e`, then `e` is the line `AC` (`A ≠ D`), so `E` is on both
lines, `E = C`; same for `C ∈ e`; if `B ∈ e`, `e` is the line `CB` and `D = C`.
`OppositeSides e A C` (`D` between), `OppositeSides e B C` (`E` between);
`OrderCore.sameSide_of_opp_opp`. ∎

**G2 (feet).** Let `Foot e A F`, `Foot e B G`, `Foot e C H` (C6(a)). Then `ρ F = H`, `ρ' G = H`,
`SegCong F A G B`, `F ≠ G`, and `Saccheri F G A B`.
*Proof.* `ρ` maps `e` into `e` (0.9, `D ∈ e`); C6(d): `Foot e (ρ A) (ρ F) = Foot e C (ρ F)`; C6(c):
`ρ F = H`. Same for `ρ'`, `G`. `ρ` gives `SegCong A F C H`, `ρ'` gives `SegCong B G C H`; hence
`SegCong A F B G`, and `segCong_swap`. If `F = G`: choose `G' ∈ e`, `G' ≠ F`; `RightAng G' F A` and
`RightAng G' F B` give `Collinear F A B` (C7); `B ∈ ray F A` (`mem_ray_of_sameSide`, G1);
`eq_of_segCong_ray'` gives `A = B`. `BiRight F G A B`: `RightAng G F A` and `RightAng F G B` from
the feet, the sides from G1 (every line through `F`, `G` is `e`). ∎

G1 and G2 are packaged as the structure `MidConf` (§ 4.11).

**G3 (the configuration at `C`).** Put `B₁ := ρ B`, `A₁ := ρ' A`; choose `X` with `Between A C X`
and `Y` with `Between B₁ C Y` (`B₁ ≠ C`, since `ρ B = C = ρ A` would give `A = B`). Then:
1. `∠CAB ≡ ∠XCY`.
2. `Y` and `B` are on the same side of the line `AC`. (So `ExteriorConfig L A B C X Y`.)
3. `Y ∈ Interior X C B`.
4. `∠CBA ≡ ∠BCA₁`; `A₁, C, B` are not collinear.
5. `A₁` and `Y` are on the same side of the line `CB`.
6. `∠FAB ≡ ∠HCB₁`; `B₁, C, H` are not collinear; `A₁, C, H` are not collinear.
7. `∠B₁CH ≡ ∠A₁CH`.
8. `A₁` and `Y` are on the same side of the line `CH`.
9. `H` and `B` are on the same side of the line `CY`.
*Proof.*
(1) 0.6 for `ρ`: `∠CAB ≡ ∠ACB₁` (image non-collinear). `vertical_angles` (`Between A C X`,
`Between B₁ C Y`): `∠ACB₁ ≡ ∠XCY`.
(2) `B ≠ D` (`B` is not on the line `AC`), `Between B D B₁`. `OppositeSides (AC) B B₁` (`D` between;
`B₁ ∉ AC`, otherwise the line `DB₁ = AC` contains `B`). `OppositeSides (AC) B₁ Y` (`C` between).
`OrderCore.sameSide_of_opp_opp`, `sameSide_symm'`.
(3) `interior_iff` (`X ≠ C`, `B ≠ C`). First condition: the line `CX` is the line `AC`; use (2).
Second: let `n` be the line `CB`. `SameSide n D A` (`sameSide_of_between_mem'`: `C ∈ n`, `A ∉ n`,
`Between C D A`), so `D ∉ n`; `B₁ ∉ n` (otherwise `n ∋ B, B₁` contains `D`); `SameSide n D B₁`
(`sameSide_of_between_mem'`: `B ∈ n`, `Between B D B₁`). Hence `SameSide n A B₁`.
`OppositeSides n A X`, `OppositeSides n B₁ Y` (`C` between). Therefore `SameSide n X Y`
(`OrderCore.opp_of_sameSide_opp`, `OrderCore.sameSide_of_opp_opp`).
(4) 0.6 for `ρ'`: `(C, B, A) ↦ (B, C, A₁)`.
(5) `A ≠ E`, `Between A E A₁`, `E ∈ n`: `OppositeSides n A A₁`. With `OppositeSides n A X` and
`SameSide n X Y` from (3): `SameSide n A₁ Y`.
(6) `∠FAB` is genuine (G2, D2(b)); 0.6 for `ρ`: `(F, A, B) ↦ (H, C, B₁)`. Likewise
`∠GBA ≡ ∠HCA₁` by `ρ'`, with `(G, B, A) ↦ (H, C, A₁)`.
(7) D4 for `Saccheri F G A B`: `∠FAB ≡ ∠GBA`. Combine with (6) and swap.
(8) `SegCong C A₁ C B₁` (`ρ'` gives `SegCong B A C A₁`, `ρ` gives `SegCong A B C B₁`).
`A₁ ≠ B₁`: `SameSide n A B₁` (see (3)) and `OppositeSides n A A₁` (see (5)). Let `k` be the line
`CH`; `A₁, B₁ ∉ k` by (6). If `SameSide k B₁ A₁`: by (7) (in the form `∠HCB₁ ≡ ∠HCA₁`) and 0.2,
`A₁ ∈ ray C B₁`, and `eq_of_segCong_ray'` gives `A₁ = B₁`. So `OppositeSides k A₁ B₁`; with
`OppositeSides k B₁ Y` (`C` between): `SameSide k A₁ Y`.
(9) Let `y` be the line `CY` (it contains `B₁`). `y` does not meet `e`: if `Z ∈ y ∩ e`, then
`ρ Z ∈ e` and `Collinear C B₁ Z` gives `Collinear A B (ρ Z)`, so the line `AB` meets `e`, against D5
for `Saccheri F G A B` (in Lean: `Z ∈ y` gives `ρ Z ∈ Pas.imLine ρ hρ y` by `Pas.mem_imLine`, and
the line `Pas.imLine ρ hρ y` contains `ρ C = A` and `ρ B₁ = B`, hence is the line `AB` by
`line_unique`). Hence `SameSide y H E` (0.5, with `H, E ∈ e`); in particular `H ∉ y` and `E ∉ y`
(both are components of this `SameSide`; explicitly, they hold because `y ∩ e = ∅` and `H, E ∈ e`).
`B ∉ y` (otherwise `y` contains `C ≠ B`, so `y` is the line `CB`, which contains `E`, against
`E ∉ y`), and `SameSide y E B` (`sameSide_of_between_mem'`: `C ∈ y`, `B ∉ y`, `Between C E B`).
Transitivity (`OrderCore.sameSide_trans`). ∎

Statement G3 is packaged as the structure `TriConf` (§ 4).

**G4 (canonical witnesses).** If `ExteriorConfig L A B C X' Y'`, then `X' ∈ ray C X` and
`Y' ∈ ray C Y`.
*Proof.* `Pas.mem_ray_of_between_between`. `∠CAB ≡ ∠XCY'` (`angCong_rays`); `Y'` and `Y` are on the
same side of the line `AC` (both on the side of `B`); `layoff_unique` at `C` on the line `AC` with
`A' := X`: `ray C Y = ray C Y'`. ∎

**G5 (positions).** Let `y` be the line `CY`. Exactly one of the following holds:
`Pos₋`: `SameSide y A₁ B`; `Pos₀`: `A₁ ∈ y`; `Pos₊`: `OppositeSides y A₁ B`. (`B ∉ y` by G3.9.)

**G6 (predicates ↔ positions).**
`AngleSumLtTwoRight L A B C ↔ Pos₋`, `AngleSumEqTwoRight L A B C ↔ Pos₀`,
`AngleSumGtTwoRight L A B C ↔ Pos₊`.
*Proof.* Let `n` be the line `CB`.
(`Pos₀ →`) `A₁ ∈ ray C Y` (`mem_ray_of_sameSide` with G3.5). From G3.4:
`∠A₁CB ≡ ∠CBA`, hence `∠YCB ≡ ∠CBA` (`angCong_rays`). Witnesses `X`, `Y`, with G3.1–3.
(`Pos₋ →`) `A₁ ∈ Interior Y C B` (`interior_iff`: `Pos₋` and G3.5). Witnesses `X`, `Y`, `Z := A₁`.
(`Pos₊ →`) `interior_or_interior` at `C` with `L' := B`, `H := A₁`, `K := Y` (G3.4, G3.5,
`A₁ ∉ y`): `Y ∈ Interior A₁ C B` or `A₁ ∈ Interior Y C B`; the second contradicts `Pos₊`.
`theorem13` with `∠A₁CB ≡ ∠ABC` and `Y ∈ Interior A₁ C B`: `Z ∈ Interior A B C` with
`∠BCY ≡ ∠CBZ`. Witnesses `X`, `Y`, second alternative with `Z` (`interior_swap`, swaps).
(`→ Pos`) Let `X', Y'` be the witnesses of a predicate; by G4 all conditions transfer to `X, Y`:
`∠Y'CB ≡ …` to `∠YCB ≡ …` (`angCong_rays`), `Interior Y' C B = Interior Y C B` and
`Interior X' C B = Interior X C B` (`mem_interior_of_rays_plane`, both inclusions), and
`Y' ∈ Interior X C B` always holds (`mem_interior_of_ray`, G3.3).
- `Eq`: `∠YCB ≡ ∠CBA ≡ ∠A₁CB`; `Y`, `A₁` on the same side of `n` (G3.5); 0.2: `A₁ ∈ ray C Y`; `Pos₀`.
- `Lt`: `Z ∈ Interior Y C B`, `∠ZCB ≡ ∠CBA ≡ ∠A₁CB`; `Z` is on the side of `Y`, hence of `A₁`,
  of `n`; 0.2: `A₁ ∈ ray C Z`; so `A₁ ∈ Interior Y C B` (`mem_interior_of_ray`); `Pos₋`.
- `Gt`: the first alternative `Y' ∉ Interior X' C B` is impossible. Second: `Z ∈ Interior C B A`,
  `∠YCB ≡ ∠ZBC`. `theorem13` with `∠CBA ≡ ∠BCA₁`: `W ∈ Interior B C A₁` with `∠CBZ ≡ ∠BCW`. Then
  `∠BCY ≡ ∠BCW`, and `W`, `Y` are on the same side of `n` (both on the side of `A₁`); 0.2:
  `Y ∈ ray C W`; `Y ∈ Interior B C A₁` (`mem_interior_of_ray`); 0.3: `Pos₊`. ∎

**G7 (positions → types).** `Pos₋ → LtSupp B₁ C H`, `Pos₀ → EqSupp B₁ C H`, `Pos₊ → GtSupp B₁ C H`.
*Proof.* `Y` is a supplement point of `∠B₁CH`, and `∠B₁CH ≡ ∠A₁CH` (G3.7). Let `k` be the line `CH`.
`Pos₀`: `A₁ ∈ ray C Y` (`mem_ray_of_sameSide`, G3.8); B8(b).
`Pos₋`: with G3.9, `SameSide y A₁ H`; with G3.8, `A₁ ∈ Interior Y C H` (`interior_iff`); B8(a).
`Pos₊`: with G3.9, `OppositeSides y A₁ H`. `interior_or_interior` at `C` with `L' := H`,
`H := A₁`, `K := Y` (G3.6, G3.8, `A₁ ∉ y`): `Y ∈ Interior A₁ C H` or `A₁ ∈ Interior Y C H`; the
second gives `SameSide y A₁ H`. B8(c). ∎

**G8 (`tri_saccheri`).** For non-collinear `A, B, C` there are `F, G` with `Saccheri F G A B` and
`AngleSumLtTwoRight L A B C ↔ LtSupp F A B`, `AngleSumEqTwoRight L A B C ↔ EqSupp F A B`,
`AngleSumGtTwoRight L A B C ↔ GtSupp F A B`.
*Proof.* By G3.6, B4 and B5, `SameType F A B B₁ C H`. By G6 it suffices to show `Pos₋ ↔ LtSupp B₁ C H`
etc. `→` is G7. `←`: by G5 one of the positions holds; the two others would give, by G7, a second
type, against B3. ∎

---

### Stage H. Conclusion (file `AngleSumClose.lean`)

**H1 (`angleSumTheorem`).** Let `A' B' C'` be a triangle and assume, say, `AngleSumGtTwoRight L A B C`.
The predicate contains `IsTriangle A B C` and `Between A C X`, so `A ≠ C` and
`hl := line_through_of_ne …`. G8 for both triangles gives Saccheri quadrilaterals `F G A B`,
`F' G' A' B'`; F9 gives `SameType F A B F' A' B'`. Then
`Gt(ABC) → GtSupp F A B → GtSupp F' A' B' → Gt(A'B'C')`. Same for `Eq`, `Lt`. ∎

(This skeleton — the final file with the statements of G8 and F9 assumed — was type-checked, see
§ 6, R12.)

---------------------------------------------------------------------------------------------------

## 4. LEAN ARCHITECTURE

### 4.0 Conventions for all new files

* Directory `HilbertFoundations/`; 17 modules, forming one chain of imports in this order:
  `AngleSumCloseAux1`, `Aux2`, …, `Aux8`, **`Aux8b`**, `Aux9`, `Aux10`, `Aux11`, `Aux12`,
  **`Aux12b`**, `Aux13`, `Aux14`, `AngleSumClose` (full names
  `HilbertFoundations.AngleSumCloseAux8b` etc.). Each file imports exactly its predecessor in this
  list; `Aux1` imports `HilbertFoundations.PascalAux2` (which brings `Congruence`, `PascalAux1`);
  `Aux13` additionally imports `HilbertFoundations.Commentary`; `AngleSumClose` imports
  `HilbertFoundations.Commentary` and `HilbertFoundations.AngleSumCloseAux14`.
* **Build procedure (mandatory).** Never run `lake`. A file is checked with
  `python .lake-local/leanc.py HilbertFoundations/AngleSumCloseAuxN.lean` (type-check only). Because
  each file imports its predecessor, a **finished** file must be compiled once more with
  `python .lake-local/leanc.py HilbertFoundations/AngleSumCloseAuxN.lean --olean`, which writes the
  `.olean` that the next file needs; without `--olean` the next file cannot be checked. Finish (and
  `--olean`) each file before starting the next one: compile slots are shared machine-wide (at most
  three Lean processes), a compile can wait minutes for a slot, and an edit to an earlier file
  invalidates the `.olean`s of all later ones (recompile them in order with `--olean`).
  No existing file is edited. (Adding the new modules to `HilbertFoundations.lean`, changing the
  status line of the unit `concl.angle_sum` in `Commentary.lean` and the list in the header of
  `CommentaryClose.lean` is the later wiring step, not part of this blueprint.)
* Every file starts like the neighbouring helper modules (`CongruenceAux8.lean`,
  `PascalAux1.lean`): a module docstring saying that it is a helper module containing no unit of
  Hilbert's text, then

  ```lean
  set_option linter.unusedSectionVars false

  namespace HilbertFoundations

  namespace AngSum

  universe u v

  section            -- definitions first (if any), in a section WITHOUT `include`

  variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  ...
  end

  section

  variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
    [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  include hC hl
  ...
  end

  end AngSum

  end HilbertFoundations
  ```

  So **every theorem of the development takes `hl` as its first explicit argument** (`foo hl …`),
  whether it needs it or not. This convention, the wrappers 0.1 and complete proofs of several
  lemmas were type-checked (Appendix A; § 6, R12); copy the working forms from there.
* Do not `open Pas`. Write `Pas.refl l X`, `Pas.ht (L := L) M X`, `Pas.midp (L := L) A C`,
  `f ∈ Pas.isom (L := L)`.
* Names that would be shadowed/confusing are avoided: `Foot` (not `IsFoot`, which exists in
  `Areas.lean`), `SLt` (not `SegLt`, which exists in `Proportion.lean`).
* Implicit arguments: as in the repository, write `Collinear (Line := L) …`,
  `Interior (Line := L) …`, `AngLt (L := L) …`, `RightAng (L := L) …`, `line (Line := L) U V h`,
  and give `(L := L)` / `(Line := L)` to lemmas whose statements mention only points
  (`segCong_symm (L := L)`, `angCong_trans (L := L)`, `mem_ray_self' (L := L)`,
  `ne12_of_between (Line := L)`, `exists_beyond (Line := L)` …).
* The frame: `abbrev fr : Frame P L := planeFrame hl`; use `(fr hl).lemma (S := Set.univ) rfl
  trivial …`; never bind the frame with `have` (its field `IsPl` must unfold), use it as a term or
  with `let`/`set`.
* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`.

Line estimates include docstrings and are rough (± 40 %); if a file threatens to exceed about
400 lines, split it at a lemma boundary and keep the chain of imports.

Common `variable` line for points in the statements below (add to each theorem section, right
after `(hl : …)`; with `autoImplicit = false` every identifier must be bound):
`{A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}`.
(`P'` is the point called `P` in § 3, since the letter `P` is the type of points.) With this line
every statement of § 4.1–4.13 elaborated (R12); all other identifiers are bound locally in the
statements (`{B₀ D₁ : P}`, `{M' N' : P}`, `{k n : L}`, …).

**Collinear permutations.** The most frequent small type error in the scratch compiles was a wrong
`Collinear` permutation (`swap12`, `swap23`, `swap13`, `perm231`, `perm312`). Always state the
target first, `have hc : Collinear (Line := L) N D D₁ := (collinear_of_between hb).swap23`, and only
then pass `hc` to `rt_side`/`rt_arm` (whose `Collinear` argument is in the order vertex, old point,
new point).

---

### 4.1 `HilbertFoundations/AngleSumCloseAux1.lean` — plane tools and isometries (Stage 0), ≈ 330 lines

Imports: `HilbertFoundations.PascalAux2`.

```lean
abbrev fr : Frame P L := planeFrame hl
theorem ne_of_nc (h : ¬Collinear (Line := L) A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B
theorem crossbar (h : ¬Collinear (Line := L) B A C) (hD : D ∈ Interior (Line := L) B A C) :
    ∃ Y, Between B Y C ∧ Y ∈ ray A D
theorem layoff (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l) (hne : A' ≠ O')
    (hD : D ∉ l) : ∃ B', SameSide l B' D ∧ AngCong A O B A' O' B'
theorem layoff_unique (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l)
    (hne : A' ≠ O') {B' B'' : P} (hs : SameSide l B' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A O B A' O' B'') : ray O' B' = ray O' B''
theorem mem_ray_of_angCong (h : ¬Collinear (Line := L) A O B) (hO : O ∈ l) (hA : A ∈ l)
    (hs : SameSide l B B') (hc : AngCong A O B A O B') : B' ∈ ray O B                       -- 0.2
theorem interior_or_interior {L' : P} (hHL : ¬Collinear (Line := L) H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear (Line := L) H O K) :
    K ∈ Interior (Line := L) H O L' ∨ H ∈ Interior (Line := L) K O L'
theorem mem_interior_of_ray (h : ¬Collinear (Line := L) A O B)
    (hX : X ∈ Interior (Line := L) A O B) (hY : Y ∈ ray O X) : Y ∈ Interior (Line := L) A O B
theorem interior_rays (h : ¬Collinear (Line := L) A O B) (hA' : A' ∈ ray O A) (hB' : B' ∈ ray O B) :
    Interior (Line := L) A O B = Interior (Line := L) A' O B'
      -- two inclusions by `mem_interior_of_rays_plane` (and `mem_ray_comm`)
theorem mem_interior_iff {k n : L} (h : ¬Collinear (Line := L) A O B) (hOk : O ∈ k) (hAk : A ∈ k)
    (hOn : O ∈ n) (hBn : B ∈ n) :
    X ∈ Interior (Line := L) A O B ↔ SameSide k X B ∧ SameSide n X A
      -- `interior_iff` with arbitrary lines through the sides (`eq_line`)
theorem opp_of_interior (h : ¬Collinear (Line := L) A O C) (hB : B ∈ Interior (Line := L) A O C)
    {k : L} (hO : O ∈ k) (hBk : B ∈ k) : OppositeSides k A C                                 -- 0.3
theorem interior_trans (h : ¬Collinear (Line := L) A O C) (hX : X ∈ Interior (Line := L) A O C)
    (hY : Y ∈ Interior (Line := L) X O C) :
    Y ∈ Interior (Line := L) A O C ∧ X ∈ Interior (Line := L) A O Y                          -- 0.4
theorem sameSide_of_not_meets {k m : L} (h : ¬Meets (Point := P) m k) (hX : X ∈ m) (hY : Y ∈ m) :
    SameSide k X Y                                                                           -- 0.5
theorem not_meets_symm {k m : L} (h : ¬Meets (Point := P) m k) : ¬Meets (Point := P) k m
theorem rt_side (h : RightAng (L := L) A O B) (hB' : B' ≠ O) (hc : Collinear (Line := L) O B B') :
    RightAng (L := L) A O B'
theorem rt_arm (h : RightAng (L := L) A O B) (hA' : A' ≠ O) (hc : Collinear (Line := L) O A A') :
    RightAng (L := L) A' O B
theorem rt_symm (h : RightAng (L := L) A O B) : RightAng (L := L) B O A
theorem rt_cong (h : RightAng (L := L) A O B) (h' : RightAng (L := L) A' O' B') :
    AngCong A O B A' O' B'
theorem isom_nc {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : ¬Collinear (Line := L) (f X) (f Y) (f Z)
theorem isom_angCong {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : AngCong X Y Z (f X) (f Y) (f Z)                     -- 0.6
theorem isom_rightAng {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : RightAng (L := L) X Y Z) : RightAng (L := L) (f X) (f Y) (f Z)                      -- 0.7
theorem isom_sameSide_self {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (hmap : ∀ Z : P, Z ∈ l ↔ f Z ∈ l) (h : SameSide l X Y) : SameSide l (f X) (f Y)          -- 0.8
theorem isom_opp_self {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (hmap : ∀ Z : P, Z ∈ l ↔ f Z ∈ l) (h : OppositeSides l X Y) : OppositeSides l (f X) (f Y)
theorem ht_spec {M : P} (h : X ≠ M) :
    Between X M (Pas.ht (L := L) M X) ∧ SegCong M X M (Pas.ht (L := L) M X)                  -- 0.9
theorem ht_mem {M : P} (hM : M ∈ l) : X ∈ l ↔ Pas.ht (L := L) M X ∈ l
theorem midp_spec (h : A ≠ C) :
    Between A (Pas.midp (L := L) A C) C ∧ Pas.ht (L := L) (Pas.midp (L := L) A C) A = C ∧
      Pas.ht (L := L) (Pas.midp (L := L) A C) C = A
```

### 4.2 `HilbertFoundations/AngleSumCloseAux2.lean` — the order of angles (Stage A), ≈ 300 lines

Imports: `HilbertFoundations.AngleSumCloseAux1`.

```lean
theorem angLt_of_interior (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hX : X ∈ Interior (Line := L) A' O' B') (hc : AngCong A O B A' O' X) :
    AngLt (L := L) A O B A' O' B'                                                            -- A1
theorem angLt_interior (h : AngLt (L := L) A O B A' O' B') :
    ∃ X, X ∈ Interior (Line := L) A' O' B' ∧ AngCong A O B A' O' X                           -- A2
theorem angLt_congr_left (h : AngLt (L := L) A O B A' O' B')
    (h₁ : ¬Collinear (Line := L) A₁ O₁ B₁) (hc : AngCong A O B A₁ O₁ B₁) :
    AngLt (L := L) A₁ O₁ B₁ A' O' B'                                                         -- A3
theorem angLt_congr_right (h : AngLt (L := L) A O B A' O' B')
    (h₁ : ¬Collinear (Line := L) A₁ O₁ B₁) (hc : AngCong A' O' B' A₁ O₁ B₁) :
    AngLt (L := L) A O B A₁ O₁ B₁                                                            -- A4
theorem angLt_swap_left (h : AngLt (L := L) A O B A' O' B') : AngLt (L := L) B O A A' O' B'
theorem angLt_swap_right (h : AngLt (L := L) A O B A' O' B') : AngLt (L := L) A O B B' O' A'
theorem angLt_rays_left (h : AngLt (L := L) A O B A' O' B') (hX : X ∈ ray O A) (hY : Y ∈ ray O B) :
    AngLt (L := L) X O Y A' O' B'
theorem angLt_rays_right (h : AngLt (L := L) A O B A' O' B') (hX : X ∈ ray O' A')
    (hY : Y ∈ ray O' B') : AngLt (L := L) A O B X O' Y
theorem angLt_irrefl : ¬AngLt (L := L) A O B A O B                                           -- A5
theorem angLt_trans {A₂ O₂ B₂ : P} (h1 : AngLt (L := L) A O B A' O' B')
    (h2 : AngLt (L := L) A' O' B' A₂ O₂ B₂) : AngLt (L := L) A O B A₂ O₂ B₂                  -- A6
theorem angLt_asymm (h1 : AngLt (L := L) A O B A' O' B') (h2 : AngLt (L := L) A' O' B' A O B) :
    False                                                                                    -- A7
theorem angLt_not_angCong (h1 : AngLt (L := L) A O B A' O' B') (h2 : AngCong A O B A' O' B') :
    False
theorem angLt_trichotomy (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B') :
    AngLt (L := L) A O B A' O' B' ∨ AngCong A O B A' O' B' ∨ AngLt (L := L) A' O' B' A O B   -- A8
theorem angLt_supp (h : AngLt (L := L) A O B A' O' B') (hC : Between A O C)
    (hC' : Between A' O' C') : AngLt (L := L) C' O' B' C O B                                 -- A9
```

### 4.3 `HilbertFoundations/AngleSumCloseAux3.lean` — addition of angles; types (Stage B, first half), ≈ 260 lines

Imports: `HilbertFoundations.AngleSumCloseAux2`.

```lean
-- definitions (section without `include`)
variable (L) in
/-- `∠AOB` is less than its supplementary angle ("acute"). -/
def LtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) A O B C O B
variable (L) in
/-- `∠AOB` is congruent to its supplementary angle ("right"). -/
def EqSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngCong A O B C O B
variable (L) in
/-- `∠AOB` is greater than its supplementary angle ("obtuse"). -/
def GtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) C O B A O B
variable (L) in
/-- The angles `∠AOB`, `∠A'O'B'` have the same type. -/
def SameType (A O B A' O' B' : P) : Prop :=
  (LtSupp L A O B ↔ LtSupp L A' O' B') ∧ (EqSupp L A O B ↔ EqSupp L A' O' B') ∧
    (GtSupp L A O B ↔ GtSupp L A' O' B')

-- theorems
theorem angLt_add (h : ¬Collinear (Line := L) A O C) (hB : B ∈ Interior (Line := L) A O C)
    (h' : ¬Collinear (Line := L) A' O' C') (hB' : B' ∈ Interior (Line := L) A' O' C')
    (h1 : AngLt (L := L) A O B A' O' B' ∨ AngCong A O B A' O' B')
    (h2 : AngLt (L := L) B O C B' O' C') : AngLt (L := L) A O C A' O' C'                     -- B1
theorem ltSupp_iff (hC : Between A O C) :
    LtSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngLt (L := L) A O B C O B               -- B2
theorem eqSupp_iff (hC : Between A O C) :
    EqSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngCong A O B C O B
theorem gtSupp_iff (hC : Between A O C) :
    GtSupp L A O B ↔ ¬Collinear (Line := L) A O B ∧ AngLt (L := L) C O B A O B
theorem not_ltSupp_eqSupp (h1 : LtSupp L A O B) (h2 : EqSupp L A O B) : False                -- B3
theorem not_ltSupp_gtSupp (h1 : LtSupp L A O B) (h2 : GtSupp L A O B) : False
theorem not_eqSupp_gtSupp (h1 : EqSupp L A O B) (h2 : GtSupp L A O B) : False
theorem sameType_refl (A O B : P) : SameType L A O B A O B
theorem sameType_symm (h : SameType L A O B A' O' B') : SameType L A' O' B' A O B
theorem sameType_trans {A₂ O₂ B₂ : P} (h1 : SameType L A O B A' O' B')
    (h2 : SameType L A' O' B' A₂ O₂ B₂) : SameType L A O B A₂ O₂ B₂
theorem sameType_of_cases {c₁ c₂ c₃ : Prop} (hc : c₁ ∨ c₂ ∨ c₃)
    (h₁ : c₁ → LtSupp L A O B ∧ LtSupp L A' O' B') (h₂ : c₂ → EqSupp L A O B ∧ EqSupp L A' O' B')
    (h₃ : c₃ → GtSupp L A O B ∧ GtSupp L A' O' B') : SameType L A O B A' O' B'               -- B7
```

### 4.4 `HilbertFoundations/AngleSumCloseAux4.lean` — types of angles (Stage B, second half), ≈ 280 lines

Imports: `HilbertFoundations.AngleSumCloseAux3`.

```lean
theorem sameType_of_angCong (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') (hc : AngCong A O B A' O' B') :
    SameType L A O B A' O' B'                                                                -- B4
theorem sameType_rays (h : ¬Collinear (Line := L) A O B) (hX : X ∈ ray O A) (hY : Y ∈ ray O B) :
    SameType L A O B X O Y
theorem sameType_swap (h : ¬Collinear (Line := L) A O B) : SameType L A O B B O A            -- B5
theorem ltSupp_of_angLt (h : AngLt (L := L) A O B A' O' B') (h' : LtSupp L A' O' B') :
    LtSupp L A O B                                                                           -- B6
theorem gtSupp_of_angLt (h : AngLt (L := L) A' O' B' A O B) (h' : GtSupp L A' O' B') :
    GtSupp L A O B
theorem ltSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX : X ∈ Interior (Line := L) C O B) : LtSupp L A O B        -- B8
theorem eqSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX : X ∈ ray O C) : EqSupp L A O B
theorem gtSupp_of_copy (h : ¬Collinear (Line := L) A O B) (hC : Between A O C)
    (hc : AngCong A O B X O B) (hX' : ¬Collinear (Line := L) X O B)
    (hX : C ∈ Interior (Line := L) X O B) : GtSupp L A O B
```

(`hX'` is needed, see B8(c); at the use in G7 pass `T.ncH' : ¬Collinear (Line := L) A₁ C H`,
which is already in the order `X O B` with `X := A₁`, `O := C`, `B := H`.)

### 4.5 `HilbertFoundations/AngleSumCloseAux5.lean` — segments; perpendiculars (Stage C), ≈ 380 lines

Imports: `HilbertFoundations.AngleSumCloseAux4`.

```lean
-- definitions
/-- `AB < CD`. -/
def SLt (A B C D : P) : Prop := ∃ X, Between C X D ∧ SegCong A B C X
/-- `F` is the foot of the perpendicular from `X` to `l`. -/
def Foot (l : L) (X F : P) : Prop :=
  F ∈ l ∧ X ∉ l ∧ ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F X

-- theorems
theorem sLt_trichotomy (hAB : A ≠ B) (hCD : C ≠ D) :
    SLt A B C D ∨ SegCong A B C D ∨ SLt C D A B                                              -- C1
theorem sLt_congr_left (h : SLt A B C D) (hAB : A ≠ B) (hA'B' : A' ≠ B')
    (hc : SegCong A B A' B') : SLt A' B' C D                                                 -- C2
theorem sLt_congr_right (h : SLt A B C D) (hAB : A ≠ B) (hC'D' : C' ≠ D')
    (hc : SegCong C D C' D') : SLt A B C' D'
      -- complete proof (compiled, R12):
      -- obtain ⟨W, hW, hcW⟩ := h
      -- have hCW : C ≠ W := ne12_of_between (Line := L) hW
      -- obtain ⟨W', hW'r, hcW'⟩ := segCong_layoff (L := L) hCW hC'D'
      -- have b := between_of_segCong_ray (L := L) hW hW'r hcW' hc
      -- have hC'W' : C' ≠ W' := ne12_of_between (Line := L) b
      -- exact ⟨W', b, segCong_trans (L := L) hAB hCW hC'W' hcW hcW'⟩
theorem sLt_exists_beyond (h : SLt A B C D) (hAB : A ≠ B) :
    ∃ E, Between A B E ∧ SegCong C D A E                                                     -- C3
theorem between_refl_of_rightAng (hG : G ∈ l) (hF : F ∈ l) (h : RightAng (L := L) G F X) :
    Between X F (Pas.refl l X)                                                               -- C4
theorem no_two_right {F' : P} (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' X) :
    False                                                                                    -- C5
theorem exists_foot (hX : X ∉ l) : ∃ F, Foot l X F                                           -- C6
theorem foot_of_rightAng (hG : G ∈ l) (hF : F ∈ l) (h : RightAng (L := L) G F X) : Foot l X F
theorem foot_unique {F' : P} (h : Foot l X F) (h' : Foot l X F') : F = F'
theorem foot_map {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L)) (hmap : ∀ Z : P, Z ∈ l → f Z ∈ l)
    (h : Foot l X F) : Foot l (f X) (f F)
theorem rightAng_collinear (h1 : RightAng (L := L) G F X) (h2 : RightAng (L := L) G F Y) :
    Collinear (Line := L) F X Y                                                              -- C7
theorem perp_not_meets {a b : L} {F' : P} (hF : F ∈ a) (hX : X ∈ a) (hF' : F' ∈ b) (hY : Y ∈ b)
    (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' Y) : ¬Meets (Point := P) a b -- C8
theorem sameSide_perp {a : L} {F' W : P} (hF : F ∈ a) (hX : X ∈ a)
    (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' W) : SameSide a W F'        -- C9
theorem exists_perp_at (hF : F ∈ l) :
    ∃ m : L, F ∈ m ∧ ∀ Z : P, Z ∈ m → Z ≠ F → ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F Z -- C10
```

### 4.6 `HilbertFoundations/AngleSumCloseAux6.lean` — exterior angle; Saccheri quadrilaterals (Stage D, D1–D5), ≈ 380 lines

Imports: `HilbertFoundations.AngleSumCloseAux5`.

```lean
-- definitions
variable (L) in
/-- A quadrilateral `ABDC` with right angles at `A`, `B`; `C`, `D` on the same side of `AB`. -/
def BiRight (A B C D : P) : Prop :=
  A ≠ B ∧ RightAng (L := L) B A C ∧ RightAng (L := L) A B D ∧
    ∀ l : L, A ∈ l → B ∈ l → SameSide l C D
variable (L) in
/-- A Saccheri quadrilateral with base `AB`, sides `AC ≡ BD`, summit `CD`. -/
def Saccheri (A B C D : P) : Prop := BiRight L A B C D ∧ SegCong A C B D
variable (L) in
/-- A Lambert quadrilateral: right angles at `M`, `B`, `N`; fourth angle `∠BDN`. -/
def Lambert (M B D N : P) : Prop :=
  RightAng (L := L) B M N ∧ RightAng (L := L) M B D ∧ RightAng (L := L) M N D

-- theorems
theorem ext_angle (h : ¬Collinear (Line := L) A B C) (hD : Between B C D) :
    AngLt (L := L) B A C A C D ∧ AngLt (L := L) A B C A C D                                  -- D1
theorem biRight_mk (hAB : A ≠ B) (hA : A ∈ l) (hB : B ∈ l) (h1 : RightAng (L := L) B A C)
    (h2 : RightAng (L := L) A B D) (hs : SameSide l C D) : BiRight L A B C D
theorem biRight_symm (h : BiRight L A B C D) : BiRight L B A D C                             -- D2
theorem biRight_not_meets (h : BiRight L A B C D) {a b : L} (hA : A ∈ a) (hC : C ∈ a)
    (hB : B ∈ b) (hD : D ∈ b) : ¬Meets (Point := P) a b
theorem biRight_nc (h : BiRight L A B C D) :
    ¬Collinear (Line := L) A C D ∧ ¬Collinear (Line := L) B D C ∧ C ≠ D
/-- Helper for D3: a reflection exchanging two points of `l` maps `l` onto itself. -/
theorem refl_mem_line_iff (hA : A ∈ l) (hB : B ∈ l) (hAB : A ≠ B) (e : Pas.refl m A = B) :
    ∀ Z : P, Z ∈ l ↔ Pas.refl m Z ∈ l
      -- `Pas.isom_collinear` (with `Pas.refl_isom`), `Pas.refl_refl` (`Pas.refl m B = A`),
      -- `mem_of_collinear`; the converse by applying the forward direction to `Pas.refl m Z`
theorem saccheri_refl (h : Saccheri L A B C D) :
    ∃ (m : L) (M N : P), Pas.refl m A = B ∧ Pas.refl m C = D ∧ M ∈ m ∧ N ∈ m ∧
      Between A M B ∧ Between C N D ∧ Lambert L M B D N                                      -- D3
theorem saccheri_summit (h : Saccheri L A B C D) : AngCong A C D B D C                       -- D4
theorem saccheri_not_meets (h : Saccheri L A B C D) {l s : L} (hA : A ∈ l) (hB : B ∈ l)
    (hC : C ∈ s) (hD : D ∈ s) : ¬Meets (Point := P) l s                                      -- D5
theorem saccheri_lambert (h : Saccheri L A B C D) :
    ∃ M N : P, Between A M B ∧ Between C N D ∧ Lambert L M B D N
```

### 4.7 `HilbertFoundations/AngleSumCloseAux7.lean` — comparison in a quadrilateral with two right angles (D6), ≈ 200 lines

Imports: `HilbertFoundations.AngleSumCloseAux6`.

```lean
theorem biRight_lt (h : BiRight L A B C D) (hlt : SLt A C B D) : AngLt (L := L) B D C A C D  -- D6(a)
theorem biRight_gt (h : BiRight L A B C D) (hlt : SLt B D A C) : AngLt (L := L) A C D B D C  -- D6(b)
```

### 4.8 `HilbertFoundations/AngleSumCloseAux8.lean` — the outside lemma, part 1 (Stage E: E0, E1, E2), ≈ 380 lines

Imports: `HilbertFoundations.AngleSumCloseAux7`.

The seven lines of Stage E are **fields / bound variables of type `L`** (never `line … h` terms:
then no `line` term ever has to be rewritten), bundled in two `Prop`-structures, in the style of
`TriConf`. Definitions go in a section without `include`.

```lean
-- definitions (section without `include`)
variable (L) in
/-- The setting of Stage E (Lemma E0): `l = AB`, `s = CD`, `q = QP'`, `a = AC`, `b = BD`. -/
structure OutConf (A B C D P' Q : P) (l s q a b : L) : Prop where
  sac : Saccheri L A B C D
  hP : Between C D P'
  hQ : Between A B Q
  hr : RightAng (L := L) B Q P'
  hAl : A ∈ l
  hBl : B ∈ l
  hQl : Q ∈ l
  hCs : C ∈ s
  hDs : D ∈ s
  hPs : P' ∈ s
  hQq : Q ∈ q
  hPq : P' ∈ q
  hAa : A ∈ a
  hCa : C ∈ a
  hBb : B ∈ b
  hDb : D ∈ b
  nls : ¬Meets (Point := P) l s
  nqa : ¬Meets (Point := P) q a
  nqb : ¬Meets (Point := P) q b
  nab : ¬Meets (Point := P) a b
  hPl : P' ∉ l
  hQs : Q ∉ s
  hAq : A ∉ q
  hBq : B ∉ q
  hsq : s ≠ q

variable (L) in
/-- The auxiliary point `E ∈ q` of Lemma E1, with the lines `d = DE`, `c = CE`. -/
structure OutAux (A B C D P' Q E : P) (l s q a b d c : L) : Prop where
  hEq : E ∈ q
  hEQ : E ≠ Q
  sideE : SameSide l E P'
  sac1 : Saccheri L B Q D E
  sac2 : Saccheri L A Q C E
  ang1 : AngCong B D E Q E D
  ang2 : AngCong A C E Q E C
  hDd : D ∈ d
  hEd : E ∈ d
  hCc : C ∈ c
  hEc : E ∈ c
  ndl : ¬Meets (Point := P) d l
  ncl : ¬Meets (Point := P) c l

-- theorems (section with `include hC hl`)
theorem exists_outConf (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') :
    ∃ l s q a b : L, OutConf L A B C D P' Q l s q a b                                       -- E0
theorem outConf_not_mem_s {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEP : E ≠ P') : E ∉ s
theorem outConf_aux {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hEq : E ∈ q) (hEQ : E ≠ Q) (hside : SameSide l E P') (hc : SegCong B D Q E) :
    ∃ d c : L, OutAux L A B C D P' Q E l s q a b d c                                        -- E1
theorem outConf_lt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P'                                       -- E2
theorem saccheri_out_lt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P'
      -- obtain ⟨l, s, q, a, b, O⟩ := exists_outConf hl h hP hQ hr; exact outConf_lt hl O hlt
```

(The structures, `exists_outConf`, `outConf_aux`, `outConf_lt` and the two-line proof of
`saccheri_out_lt` from them were type-checked, R12.) In `outConf_lt` (E2): obtain `E`, then
`⟨d, c, X⟩ := outConf_aux …`; each `SameSide` of (f1)–(f3) is one `sameSide_of_not_meets` (with a
field `n…` of `O` or `X`, possibly after `not_meets_symm`) or one `sameSide_of_between_mem'` /
`opp_of_between_mem`, and each `Interior` membership one `mem_interior_iff` with the lines `b, s`
(f1), `a, s` (f2), `q, d` (f3).

### 4.8b `HilbertFoundations/AngleSumCloseAux8b.lean` — the outside lemma, part 2 (E3–E5), ≈ 300 lines

Imports: `HilbertFoundations.AngleSumCloseAux8`.

```lean
theorem outConf_gt {l s q a b : L} (O : OutConf L A B C D P' Q l s q a b)
    (hgt : SLt Q P' B D) : AngLt (L := L) B D P' A C D                                       -- E3
theorem saccheri_out_gt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hgt : SLt Q P' B D) : AngLt (L := L) B D P' A C D
theorem saccheri_out_eq (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (he : SegCong B D Q P') : AngCong A C D B D P'           -- E4
theorem saccheri_out_type (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') :
    (SLt B D Q P' → LtSupp L C D B) ∧ (SegCong B D Q P' → EqSupp L C D B) ∧
      (SLt Q P' B D → GtSupp L C D B)                                                        -- E5
```

E3's final step (A8, then B1 and A7 by contradiction) is best written as
`rcases angLt_trichotomy hl n1 n2 with h | h | h`, with the two bad cases closed by **one** shared
`have key : AngLt (L := L) A C P' B D P' ∨ AngCong A C P' B D P' → False` (proved once with
`angLt_add` and `angLt_asymm`), after transporting `∠ACD` to `∠ACP'` with `angLt_rays_left` /
`angCong_rays`. E4 uses `outConf_aux` with `E := P'` (allowed: `OutAux` contains no `E ∉ s`).

### 4.9 `HilbertFoundations/AngleSumCloseAux9.lean` — Lambert quadrilaterals: doubling and nesting (F1–F4), ≈ 400 lines

Imports: `HilbertFoundations.AngleSumCloseAux8b`.

```lean
theorem lambert_symm (h : Lambert L M B D N) : Lambert L M N D B                             -- F1
theorem lambert_not_meets (h : Lambert L M B D N) {l s : L} (hM : M ∈ l) (hB : B ∈ l)
    (hN : N ∈ s) (hD : D ∈ s) : ¬Meets (Point := P) l s
theorem lambert_nc (h : Lambert L M B D N) : ¬Collinear (Line := L) B D N
theorem lambert_double (h : Lambert L M B D N) {t : L} (hM : M ∈ t) (hN : N ∈ t) :
    Between B M (Pas.refl t B) ∧ Between D N (Pas.refl t D) ∧
      Saccheri L (Pas.refl t B) B (Pas.refl t D) D ∧
      AngCong B D N (Pas.refl t B) (Pas.refl t D) N                                          -- F2
theorem lambert_cut {B₀ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B) :
    ∃ D₁, Between N D₁ D ∧ Lambert L M B₀ D₁ N                                               -- F3
theorem lambert_nest {B₀ D₁ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B)
    (hD₁ : Between N D₁ D) (h₁ : Lambert L M B₀ D₁ N) : SameType L B D N B₀ D₁ N             -- F4
```

### 4.10 `HilbertFoundations/AngleSumCloseAux10.lean` — uniformity (F5–F9), ≈ 300 lines

Imports: `HilbertFoundations.AngleSumCloseAux9`.

```lean
theorem lambert_shrink {B₀ : P} (h : Lambert L M B D N) (hB₀ : B₀ = B ∨ Between M B₀ B) :
    ∃ D₁, Lambert L M B₀ D₁ N ∧ SameType L B D N B₀ D₁ N                                     -- F5(a)
theorem lambert_shrink2 {B₀ N₀ : P} (h : Lambert L M B D N) (hB₀ : B₀ = B ∨ Between M B₀ B)
    (hN₀ : N₀ = N ∨ Between M N₀ N) :
    ∃ D₀, Lambert L M B₀ D₀ N₀ ∧ SameType L B D N B₀ D₀ N₀                                   -- F5(b)
theorem lambert_unique (h : Lambert L M B D N) (h' : Lambert L M B D' N) : D = D'            -- F6
theorem lambert_transport {M' N' N₁ : P} (h' : Lambert L M' B' D' N')
    (hr : RightAng (L := L) B₁ M N₁) (sB : SegCong M' B' M B₁) (sN : SegCong M' N' M N₁) :
    ∃ D₁, Lambert L M B₁ D₁ N₁ ∧ SameType L B' D' N' B₁ D₁ N₁                                -- F7
theorem exists_common (hB₁ : B₁ ∈ ray M B) :
    ∃ B₀, (B₀ = B ∨ Between M B₀ B) ∧ (B₀ = B₁ ∨ Between M B₀ B₁)
theorem lambert_sameType {M' N' : P} (h : Lambert L M B D N) (h' : Lambert L M' B' D' N') :
    SameType L B D N B' D' N'                                                                -- F8
theorem saccheri_sameType (h : Saccheri L A B C D) (h' : Saccheri L A' B' C' D') :
    SameType L A C D A' C' D'                                                                -- F9
```

### 4.11 `HilbertFoundations/AngleSumCloseAux11.lean` — the midline of a triangle (G1, G2), ≈ 320 lines

Imports: `HilbertFoundations.AngleSumCloseAux10`.

**Caution.** `Pas.ht` is defined only under `[PlaneCongruence P L]`, so `MidConf` must be declared
in a section whose `variable` line **contains the instance** `[PlaneCongruence P L]` (but not `hl`,
and no `include`). In the definitions-only section used elsewhere (without the instance) its four
`Pas.ht` fields fail with "failed to synthesize `PlaneCongruence P L`" (this happened in the first
scratch compile of this revision; the form below compiled).

```lean
-- definition: section with
-- variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
--   [PlaneCongruence P L]
variable (L) in
/-- The data of Lemmas G1, G2 for the triangle `ABC`: `D`, `E` the midpoints of `CA`, `CB`, `e` the
line `DE`, `F`, `G`, `H` the feet of `A`, `B`, `C` on `e`. -/
structure MidConf (A B C D E F G H : P) (e : L) : Prop where
  htA : Pas.ht (L := L) D A = C
  htB : Pas.ht (L := L) E B = C
  bD : Between A D C
  bE : Between B E C
  hD : D ∈ e
  hE : E ∈ e
  hA : A ∉ e
  hB : B ∉ e
  hC : C ∉ e
  sideAB : SameSide e A B
  fA : Foot e A F
  fB : Foot e B G
  fC : Foot e C H
  htF : Pas.ht (L := L) D F = H
  htG : Pas.ht (L := L) E G = H
  sac : Saccheri L F G A B

-- theorems
/-- G1 + G2. -/
theorem tri_midline (h : ¬Collinear (Line := L) A B C) :
    ∃ (D E F G H : P) (e : L), MidConf L A B C D E F G H e
```

(Internally: a lemma `tri_midline_side` for G1, a lemma for `ρ F = H` (C6(c),(d)), and a lemma for
`F ≠ G`; free to split. `MidConf` and `tri_midline` were type-checked, R12. In Aux12/Aux12b take
`M : MidConf L A B C D E F G H e` as hypothesis and use its fields `M.htA`, `M.fC`, … instead of
destructuring.)

### 4.12 `HilbertFoundations/AngleSumCloseAux12.lean` — the configuration at `C`, part 1 (`TriConf`; G3 items 1–5), ≈ 330 lines

Imports: `HilbertFoundations.AngleSumCloseAux11`.

```lean
-- definition (section without `include`)
variable (L) in
/-- The configuration of Lemma G3 (blueprint) attached to a triangle `ABC`. -/
structure TriConf (A B C F G H X Y A₁ B₁ : P) : Prop where
  nc : ¬Collinear (Line := L) A B C
  sac : Saccheri L F G A B
  hX : Between A C X
  hY : Between B₁ C Y
  angA : AngCong C A B X C Y
  sideY : ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B
  intY : Y ∈ Interior (Line := L) X C B
  angB : AngCong C B A B C A₁
  ncA : ¬Collinear (Line := L) A₁ C B
  sideA : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y
  angS : AngCong F A B H C B₁
  ncH : ¬Collinear (Line := L) B₁ C H
  ncH' : ¬Collinear (Line := L) A₁ C H
  angH : AngCong B₁ C H A₁ C H
  sideH : ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y
  sideYH : ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B
```

The item lemmas take (subsets of) the same hypotheses: `{e : L}`,
`(h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)`,
`(hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁)`,
`(hX : Between A C X) (hY : Between B₁ C Y)`. They are written out in full below (add `{e : L}`
to the common variable line of Aux12 and Aux12b).

```lean
theorem tri_B₁_ne (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) : B₁ ≠ C ∧ Between B D B₁ ∧ B₁ ∉ e                     -- setup
theorem tri_angA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    AngCong C A B X C Y                                                                      -- G3.1
theorem tri_sideY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B                                                  -- G3.2
theorem tri_intY (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X) (hY : Between B₁ C Y) :
    Y ∈ Interior (Line := L) X C B                                                           -- G3.3
theorem tri_angB (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) :
    AngCong C B A B C A₁ ∧ ¬Collinear (Line := L) A₁ C B                                     -- G3.4
theorem tri_sideA (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hX : Between A C X)
    (hY : Between B₁ C Y) : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y                        -- G3.5
```

### 4.12b `HilbertFoundations/AngleSumCloseAux12b.lean` — the configuration at `C`, part 2 (G3 items 6–9, assembly), ≈ 300 lines

Imports: `HilbertFoundations.AngleSumCloseAux12`.

```lean
theorem tri_angS (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong F A B H C B₁ ∧ ¬Collinear (Line := L) B₁ C H ∧
      AngCong G B A H C A₁ ∧ ¬Collinear (Line := L) A₁ C H                                   -- G3.6
theorem tri_angH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) :
    AngCong B₁ C H A₁ C H                                                                    -- G3.7
theorem tri_sideH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hA₁ : Pas.ht (L := L) E A = A₁) (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y                                                 -- G3.8
theorem tri_sideYH (h : ¬Collinear (Line := L) A B C) (M : MidConf L A B C D E F G H e)
    (hB₁ : Pas.ht (L := L) D B = B₁) (hY : Between B₁ C Y) :
    ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B                                                  -- G3.9
theorem exists_triConf (h : ¬Collinear (Line := L) A B C) :
    ∃ F G H X Y A₁ B₁ : P, TriConf L A B C F G H X Y A₁ B₁                                   -- G3
```

`exists_triConf`: `obtain ⟨D, E, F, G, H, e, M⟩ := tri_midline hl h`; obtain `A₁`, `B₁` with their
equations by `obtain ⟨A₁, hA₁⟩ : ∃ A₁, Pas.ht (L := L) E A = A₁ := ⟨_, rfl⟩` (and likewise `B₁`);
`X` from `exists_beyond` (`A ≠ C`), `Y` from `exists_beyond` (`B₁ ≠ C`, `tri_B₁_ne`); fill the
sixteen fields from the item lemmas. G3(9) uses `Pas.mem_imLine` with `ρ := Pas.ht (L := L) D`
(see § 3, G3(9)).

### 4.13 `HilbertFoundations/AngleSumCloseAux13.lean` — witnesses and positions (G4–G6), ≈ 330 lines

Imports: `HilbertFoundations.AngleSumCloseAux12b`, `HilbertFoundations.Commentary`.
Write `Conclusion.ExteriorConfig`, `Conclusion.AngleSum…TwoRight` in full (this form was
type-checked from inside `namespace HilbertFoundations.AngSum`), or use `open Conclusion in`.

```lean
theorem triConf_ray {X' Y' : P} (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : Conclusion.ExteriorConfig L A B C X' Y') : X' ∈ ray C X ∧ Y' ∈ ray C Y              -- G4
/-- Replace arbitrary witnesses by the canonical `X`, `Y` once and for all. -/
theorem triConf_canon {X' Y' : P} (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : Conclusion.ExteriorConfig L A B C X' Y') :
    Interior (Line := L) X' C B = Interior (Line := L) X C B ∧
      Interior (Line := L) Y' C B = Interior (Line := L) Y C B ∧
      ¬Collinear (Line := L) Y' C B ∧ AngCong Y' C B Y C B
theorem triConf_eq_iff (T : TriConf L A B C F G H X Y A₁ B₁) :
    Conclusion.AngleSumEqTwoRight L A B C ↔ Collinear (Line := L) C Y A₁                     -- G6
theorem triConf_lt_iff (T : TriConf L A B C F G H X Y A₁ B₁) :
    Conclusion.AngleSumLtTwoRight L A B C ↔ ∀ a : L, C ∈ a → Y ∈ a → SameSide a A₁ B
theorem triConf_gt_iff (T : TriConf L A B C F G H X Y A₁ B₁) :
    Conclusion.AngleSumGtTwoRight L A B C ↔ ∀ a : L, C ∈ a → Y ∈ a → OppositeSides a A₁ B
```

`triConf_canon`: from G4, `interior_rays` (4.1; `B ∈ ray C B` by `mem_ray_self'`) twice — `∠XCB` is
genuine by `not_collinear_of_between` (from `¬Collinear A C B`, a permutation of `T.nc`, and
`T.hX : Between A C X`); `∠YCB` is genuine because `Y ∉` line `CB` (`T.sideA` gives `Y` off every line
through `C`, `B`); then `¬Collinear Y' C B` by `not_collinear_of_mem_rays`, and
`AngCong Y' C B Y C B` by `angCong_rays` from `angCong_refl`. In the three directions "predicate →
position" of G6, first apply `triConf_canon` and rewrite with its two `Interior` equalities; then
the three cases do not repeat the ray book-keeping.

### 4.13b `HilbertFoundations/AngleSumCloseAux14.lean` — types (G7, G8), ≈ 250 lines

Imports: `HilbertFoundations.AngleSumCloseAux13`.

```lean
theorem triConf_type_eq (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : Collinear (Line := L) C Y A₁) : EqSupp L B₁ C H                                     -- G7
theorem triConf_type_lt (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : ∀ a : L, C ∈ a → Y ∈ a → SameSide a A₁ B) : LtSupp L B₁ C H
theorem triConf_type_gt (T : TriConf L A B C F G H X Y A₁ B₁)
    (h : ∀ a : L, C ∈ a → Y ∈ a → OppositeSides a A₁ B) : GtSupp L B₁ C H
theorem tri_saccheri (h : ¬Collinear (Line := L) A B C) :
    ∃ F G : P, Saccheri L F G A B ∧
      (Conclusion.AngleSumLtTwoRight L A B C ↔ LtSupp L F A B) ∧
      (Conclusion.AngleSumEqTwoRight L A B C ↔ EqSupp L F A B) ∧
      (Conclusion.AngleSumGtTwoRight L A B C ↔ GtSupp L F A B)                               -- G8
```

In `triConf_type_gt` the call is `gtSupp_of_copy hl … T.ncH' …` (§ 4.4).

*Optional (compile time).* `Commentary` imports `Analytic` (mathlib analysis), which makes every
compile of Aux13/Aux14 slower (a scratch file importing it took 193 s against about 114 s without).
This is correct, only slow. If it becomes a nuisance, Aux13/Aux14 may state G4/G6/G8 for the
unfolded bodies of the predicates (copied from § 1, e.g. `∃ X' Y' : P, (Between A C X' ∧
AngCong C A B X' C Y' ∧ ∀ a : L, A ∈ a → C ∈ a → SameSide a Y' B) ∧ …`), drop the `Commentary`
import, and let `AngleSumClose.lean` repackage them with `unfold` and `Iff.rfl`. The default
arrangement (import `Commentary`) is the one type-checked.

### 4.14 `HilbertFoundations/AngleSumClose.lean` — the theorem (Stage H), ≈ 90 lines

Imports: `HilbertFoundations.Commentary`, `HilbertFoundations.AngleSumCloseAux14`.
Module docstring in the style of `CommentaryClose.lean` ("This file proves the unit
`concl.angle_sum` of `Commentary.lean`, which is only stated there …", with a short description of
the proof: types of angles by comparison with the supplement, Saccheri and Lambert quadrilaterals,
the outside lemma, the half-turns about the midpoints).

```lean
namespace HilbertFoundations

namespace Conclusion

open AngSum in
/-- **Dehn's theorem on the angle sum** (unit `concl.angle_sum`): in every plane satisfying groups
I, II, IV, if one triangle has angle sum greater than / equal to / less than two right angles, so
has every triangle. -/
theorem angleSumTheorem : AngleSumTheorem := by
  intro P L _ _ _ _ hC A B C A' B' C' hT'
  have key : ∀ hl : (∀ X : P, ∃ l : L, X ∈ l), IsTriangle (Line := L) A B C →
      (AngleSumGtTwoRight L A B C → AngleSumGtTwoRight L A' B' C') ∧
      (AngleSumEqTwoRight L A B C → AngleSumEqTwoRight L A' B' C') ∧
      (AngleSumLtTwoRight L A B C → AngleSumLtTwoRight L A' B' C') := by
    intro hl hT
    obtain ⟨F, G, hS, hLt, hEq, hGt⟩ := tri_saccheri hl hT
    obtain ⟨F', G', hS', hLt', hEq', hGt'⟩ := tri_saccheri hl hT'
    obtain ⟨t1, t2, t3⟩ := saccheri_sameType hl hS hS'
    exact ⟨fun h => hGt'.2 (t3.1 (hGt.1 h)), fun h => hEq'.2 (t2.1 (hEq.1 h)),
      fun h => hLt'.2 (t1.1 (hLt.1 h))⟩
  have hl_of : ∀ {X : P}, Between A C X → ∀ Z : P, ∃ l : L, Z ∈ l := fun hb =>
    line_through_of_ne (L := L) (ne12_of_between (Line := L) hb)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.2 h

end Conclusion

end HilbertFoundations
```

(`hC : PlaneCongruence P L` is a local hypothesis of class type, hence already a local instance; no
`haveI` is needed. `h0` is needed because `obtain … := h` would consume `h`.)

### 4.15 Summary of files

| # | file | stage | content | est. lines |
|---|---|---|---|---|
| 1 | `AngleSumCloseAux1.lean` | 0 | plane wrappers, order of half-rays, isometries, half-turns | 330 |
| 2 | `AngleSumCloseAux2.lean` | A | order of angles | 300 |
| 3 | `AngleSumCloseAux3.lean` | B | `angLt_add`; `LtSupp`/`EqSupp`/`GtSupp`/`SameType`, exclusivity | 260 |
| 4 | `AngleSumCloseAux4.lean` | B | invariance of the type; types from position | 280 |
| 5 | `AngleSumCloseAux5.lean` | C | `SLt`; `Foot`, perpendiculars | 380 |
| 6 | `AngleSumCloseAux6.lean` | D | exterior angle; `BiRight`, `Saccheri`, `Lambert`; midline | 380 |
| 7 | `AngleSumCloseAux7.lean` | D | `biRight_lt`, `biRight_gt` | 200 |
| 8 | `AngleSumCloseAux8.lean` | E | `OutConf`, `OutAux`; E0, E1, E2 | 380 |
| 8b | `AngleSumCloseAux8b.lean` | E | E3, E4, E5 | 300 |
| 9 | `AngleSumCloseAux9.lean` | F | Lambert: doubling, cutting, nesting | 400 |
| 10 | `AngleSumCloseAux10.lean` | F | uniformity | 300 |
| 11 | `AngleSumCloseAux11.lean` | G | `MidConf`; midline of a triangle (G1, G2) | 320 |
| 12 | `AngleSumCloseAux12.lean` | G | `TriConf`; G3 items 1–5 | 330 |
| 12b | `AngleSumCloseAux12b.lean` | G | G3 items 6–9; `exists_triConf` | 300 |
| 13 | `AngleSumCloseAux13.lean` | G | G4, `triConf_canon`, G6 (predicates ↔ positions) | 330 |
| 14 | `AngleSumCloseAux14.lean` | G | G7, G8 (positions → types; `tri_saccheri`) | 250 |
| 15 | `AngleSumClose.lean` | H | `Conclusion.angleSumTheorem` | 90 |
| | | | **total** (17 files) | **≈ 5100** |

The estimates are calibrated on the compiled proofs (about one Lean line per atomic step of § 3:
`ext_angle_aux` 34 lines, `exists_perp_at` 27, `interior_trans` 25, `lambert_cut` 33) and are still
± 30 %; a realistic total is 4800–5400 lines. Files at the limit: Aux5, Aux6, Aux9. If one of them
exceeds about 400 lines, split it at a lemma boundary into `…b.lean` (for Aux9: `lambert_nest`, F4,
into `AngleSumCloseAux9b.lean`), keeping the single chain of imports.

Stages can be implemented one after another in this order; within a stage the lemmas are in
dependency order. Stages 0–C have no geometric risk; the delicate files are 8, 8b, 12, 12b (long
lists of side-of-a-line facts) and 13 (G6).

### 4.16 Implementation notes for the hard spots

1. **Stage E (`outConf_lt`, `outConf_gt`).** Not hard mathematically, but about 25 side-of-a-line
   facts over seven lines. Obtain the lines once with `exists_outConf` / `outConf_aux` (plain `L`
   variables; never `line … h` terms) and use the fields of `OutConf` / `OutAux`. Each `SameSide` is
   one `sameSide_of_not_meets` (field `n…`, possibly through `not_meets_symm`) or one
   `sameSide_of_between_mem'` / `opp_of_between_mem`; each `Interior` membership is one
   `mem_interior_iff` (4.1) with two of these lines. E3's last step: one shared `have key` for the
   two bad cases of `angLt_trichotomy` (§ 4.8b).
2. **`angLt_add` (B1).** The `theorem14` call compiled in exactly this shape (critic's scratch file
   `.lake-local/scratch/anglesum-critic-lean2/K1.lean`, `t14_test`):
   `theorem14 (L := L) hBO hB₁O' h1n h2n h3n h1n' h2n' h3n' h1 h2 (Or.inr ⟨ho, ho'⟩)` with
   `ho : OppositeSides (line (Line := L) O B hBO.symm) A C`; obtain `ho`, `ho'` from
   `opp_of_interior` (4.1) with `mem_line_left _`, `mem_line_right _`.
3. **D3 (`saccheri_refl`).** The case split `sameSide_or_opp'` on `C, W` with 0.8 is fine; get the
   invariance of the base line once from `refl_mem_line_iff` (§ 4.6).
4. **G6, direction "predicate → position".** Use `triConf_canon` (§ 4.13) first.
5. **Rewriting under isometries.** `rw [Pas.refl_fix hG]`, `rw [f1, f2] at a1`,
   `generalize Pas.ht (L := L) M B = B' at …` work. Do **not** introduce a map with
   `set g := Pas.refl m`: a later `rw [hrefl]` with `hrefl : Pas.refl m A = B` no longer finds its
   pattern. Keep `Pas.refl m` explicit (the letter `g` in § 3 is only notation). For transporting
   half-rays use `Pas.isom_ray`, for lines `Pas.mem_imLine` (§ 2.6).
6. **Collinear permutations and degenerate values**: see § 4.0 and § 3.0.

---------------------------------------------------------------------------------------------------

## 5. MATHLIB / DEPENDENCY API

The development is almost entirely inside the repository's own geometry; the declarations it rests
on are those of § 2 (each confirmed by reading the file named there). From mathlib only the
following are needed (all confirmed with `rg` in `.lake/packages/mathlib/Mathlib`):

| declaration | file |
|---|---|
| `Equiv.Perm.mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)` | `Mathlib/Algebra/Group/End.lean` (l. 101) |
| `Equiv.Perm.one_apply (x) : (1 : Perm α) x = x` | `Mathlib/Algebra/Group/End.lean` (l. 104) |
| `Equiv.Perm.inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y` | `Mathlib/Algebra/Group/End.lean` (l. 133) |
| `Equiv.apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x` | `Mathlib/Logic/Equiv/Defs.lean` (l. 247) |
| `Equiv.symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x` | `Mathlib/Logic/Equiv/Defs.lean` (l. 249) |
| `Equiv.injective (e : α ≃ β) : Injective e` | `Mathlib/Logic/Equiv/Defs.lean` (l. 177) |
| `Subgroup.mul_mem`, `Subgroup.inv_mem` | `Mathlib/Algebra/Group/Subgroup/Defs.lean` (l. 436, 441) |

and from the repository, for computing with isometries (instead of the two `Equiv` lemmas above):

| declaration | file |
|---|---|
| `Pas.perm_apply_inv (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x` | `HilbertFoundations/PascalAux2.lean` (l. 60) |
| `Pas.perm_inv_apply (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x` | `HilbertFoundations/PascalAux2.lean` (l. 63) |

Where each repository declaration of § 2 lives:

| declarations | file |
|---|---|
| incidence, order, `line`, `ray`, `SameSide`, `OppositeSides`, `Interior`, `IsTriangle`, axioms, `segCong_refl`, `segCong_swap_left/right`, `angCong_refl`, `angCong_swap_left/right` | `HilbertFoundations/Basic.lean` |
| `collinear_of_mem`, `Collinear.perm231/312`, `eq_of_mem_of_mem`, `mem_of_collinear`, `not_collinear_of_not_mem`, `exists_mem_not_mem`, `exists_not_mem`, `OrderCore.*`, `OrderLin.trans₁/₂` | `HilbertFoundations/OrderAux.lean` |
| `mem_mid/right/left_of_between`, `ne_of_mem_not_mem`, `collinear_iff_mem_line`, ray lemmas, `between_of_mem_rays`, `not_collinear_of_mem_rays`, `not_collinear_of_between`, `not_collinear_swap`, `ne_of_not_collinear`, `sameSide_*'`, `opp_*'`, `sameSide_of_between_mem'`, `opp_of_between_mem`, `sameSide_of_ray`, `mem_ray_of_sameSide`, `interior_iff`, `interior_swap`, `mem_interior_of_between`, `LineIn`, `Frame`, `planeFrame`, `Frame.ne`, `Frame.crossbar`, `Frame.mem_interior_of_ray`, `Frame.interior_or_interior` | `HilbertFoundations/CongruenceAux.lean` |
| `segCong_symm`, `segCong_trans`, `segCong_swap`, `segCong_layoff`, `eq_of_segCong_ray'`, `between_of_segCong_ray`, `nc_of`, `eq_of_collinear_collinear`, `angCong_symm`, `angCong_trans`, `angCong_rays` | `HilbertFoundations/CongruenceAux2.lean` |
| `nc_of_interior`, `Frame.sas`, `Frame.sss` | `HilbertFoundations/CongruenceAux3.lean` |
| `Frame.angLt_congr` | `HilbertFoundations/CongruenceAux5.lean` |
| `mem_interior_of_rays_plane`, `line_through_of_ne` | `HilbertFoundations/CongruenceAux6.lean` |
| `RightAng`, `Frame.rt_side`, `Frame.rt_symm`, `Frame.rt_arm`, `Frame.rt_congr`, `Frame.rt_cong` | `HilbertFoundations/CongruenceAux8.lean` |
| `theorem12`, `vertical_angles`, `theorem13`, `theorem14`, `AngLt` | `HilbertFoundations/Congruence.lean` |
| `Pas.isom`, `Pas.isom_cong`, `Pas.isom_collinear`, `Pas.isom_between`, `Pas.isom_inv`, `Pas.isom_collinear_iff`, `Pas.isom_between_iff`, `Pas.exists_isom_of_tri`, `Pas.refl`, `Pas.refl_isom`, `Pas.refl_fix`, `Pas.refl_refl`, `Pas.refl_fix_iff`, `Pas.refl_opp`, `Pas.exists_eqd` | `HilbertFoundations/PascalAux1.lean` |
| `Pas.mem_ray_of_between_between`, `Pas.ht`, `Pas.ht_isom`, `Pas.ht_ht`, `Pas.ht_self`, `Pas.ht_eq_iff`, `Pas.ht_fix_iff`, `Pas.midp`, `Pas.ht_midp` | `HilbertFoundations/PascalAux2.lean` |
| `Conclusion.ExteriorConfig`, `Conclusion.AngleSumEqTwoRight`, `Conclusion.AngleSumLtTwoRight`, `Conclusion.AngleSumGtTwoRight`, `Conclusion.AngleSumTheorem` | `HilbertFoundations/Commentary.lean` |

Usage notes confirmed by compilation (Appendix A):
* `(fr hl).crossbar (S := Set.univ) rfl trivial trivial trivial trivial h hD`;
  `(fr hl).layoff Set.univ rfl A O B l O' A' D h (fun _ _ => trivial) hO' hA' hne trivial hD`
  (returns `⟨B', _, hside, hcong⟩`);
  `(fr hl).layoff_unique Set.univ rfl A O B l O' A' B' B'' h (fun _ _ => trivial) hO' hA' hne
  trivial trivial hs h1 h2`;
  `(fr hl).interior_or_interior (S := Set.univ) rfl trivial trivial trivial trivial hHL hLO hs hHK`;
  `((fr hl).sss h1 h1' s1 s2 s3).1`.
* `Pas.refl_opp (L := L) hXl : OppositeSides l X (Pas.refl l X)`; `Pas.refl_fix hG : Pas.refl l G = G`
  (rewrite with it inside an `AngCong` produced by `isom_angCong hl (Pas.refl_isom (P := P) l) hn`).
* `isom_angCong` needs no distinctness hypothesis once `hl` is available.
* Half-turns: `(Pas.ht_eq_iff (L := L) h).1 rfl`, `Pas.ht_midp (L := L) A C`,
  `Pas.ht_ht (L := L) M A`, `(Pas.ht_fix_iff (L := L)).2 e`, `Pas.ht_isom (L := L) M`; to get rid
  of the term `Pas.midp (L := L) A C` (or `Pas.ht (L := L) M B`) use
  `generalize Pas.midp (L := L) A C = M at …`.
* `Pas.exists_eqd (L := L) hne` returns `⟨m, hmem, hrefl, hopp⟩`.

---------------------------------------------------------------------------------------------------

## 6. RISKS

**R1. The degenerate geometry (handled).** A single point with no line satisfies `PlaneCongruence`
(every axiom is vacuous or about `AngCong X X X X X X`; the docstrings of `Commentary.lean` mention
this "degenerate geometry of a single point" too), and there `IsTriangle X X X` is true. This
does not falsify the target: each of the three predicates contains `Between A C X`, which is false
there, so the three implications hold vacuously; in the proof, `hl` is obtained from that
`Between`. But it forces the hypothesis `hl` on essentially every lemma (for instance
`angLt_of_interior` is false without it). Do not try to remove `hl`.

**R2. The first alternative of `AngleSumGtTwoRight` (handled).** `Y ∉ Interior X C B` never holds in
a plane with groups I, II, IV (G3.3 together with G4: this is the exterior angle theorem for the
angle at `A`). So `Gt` is equivalent to its second alternative, and the three predicates are
mutually exclusive and exhaustive for every triangle; the target says what it is meant to say.
Nothing in the definitions makes the theorem false or trivially true.

**R3. The outside lemma E2/E3 is the mathematical heart and the place where I am least protected by
existing material.** It was reconstructed from memory of Hartshorne's Proposition 34.4 and then
re-derived from scratch; I could not consult the book, so the *attribution* of individual steps to
Hartshorne is not guaranteed, only the correctness of the argument given here. The proof needs (i)
six interior-of-angle memberships, each a pair of side-of-a-line statements, (ii) the exterior angle
theorem for the triangle `C D E`, (iii) `angLt_add`. I checked every membership by hand; an
independent critic re-derived E2/E3 and found them correct, up to the incidence facts now stated in
E0 (`s ≠ q`, `A ∉ q`, …). In addition the configurations were checked numerically on 3000 random
configurations in the hyperbolic plane (all of (f1)–(f3), (g1)–(g3), the auxiliary inequalities and
the conclusions held). **This numerical evidence covers only the acute branch.** The earlier
"spherical" tests are withdrawn as evidence: the sphere (or elliptic plane) does not satisfy the
order axioms (group II), so it is not a Hilbert plane. The obtuse branch (E3 in its use for
`GtSupp`, `Pos₊`, B8(c)) is therefore justified by the logical proof alone; the proof of E3 does not
depend on the type and was re-derived by the critic. A genuine Hilbert plane in which the obtuse
case occurs is Dehn's non-legendrian geometry (the part of an elliptic plane over a non-archimedean
field infinitely near a point, which does satisfy groups I, II, IV: `CommentaryCloseAux3.lean` –
`CommentaryCloseAux6.lean`; its angle-sum theorem is `angleSumGt`, `CommentaryCloseAux6.lean`
l. 196, used in `Conclusion.nonLegendrianGeometryExists`, `CommentaryClose.lean` l. 201–204); it was
not used for numerical tests.

**R4. The triangle configuration G3 is new (not from a book).** The nine items were proved by hand
(the critic re-derived them; item 9 now states explicitly `H, E ∉ y`, which follow from
`y ∩ e = ∅`) and checked numerically on 4000 random triangles in the hyperbolic plane (no violation;
always `Pos₋`). As for R3, the earlier spherical tests are not evidence (no order axioms), so the
cases `Pos₀`, `Pos₊` rest on the proof alone. The point of the construction is that no case
distinction on the foot `H` is needed; if an implementer finds a configuration where an item
fails, the item is wrong and must be reported — do not patch it with a case split without
understanding why.

**R5. `angLt_add` (B1) uses `theorem14` with ten hypotheses.** The assignment
`(O H K M) := (O A C B)`, `(O' H' K' M') := (O' A' C₁ B₁)` and the "opposite sides" alternative must
be respected exactly; the orientation of every `AngCong` (which arm first) matters and is fixed by
`angCong_swap_left/right`. Expect bookkeeping, not mathematics.

**R6. Orientation conventions.** `AngLt A O B A' O' B'` compares with the sub-angle `∠A'O'X`
adjacent to the *first* arm `O'A'`; `LtSupp A O B` extends the *first* arm (`Between A O C`);
`RightAng A O B` has its supplement along the *second* arm (`Between B O C`). The proofs in § 3 say
"swap" where an arm has to be exchanged (`angLt_swap_left/right`, `sameType_swap`, `rt_symm`).
Mistakes here are the most likely source of friction.

**R7. Lines given by two points.** `interior_iff` is stated with `line O A hA.symm`; `BiRight`,
`TriConf` and `ExteriorConfig` quantify over all lines through two points. Converting between the
two forms is routine (`eq_line`, `line_unique`) but pervasive; the helper `mem_interior_iff` (4.1)
is there for it. Whenever § 3 says "the line `UV`", fix once `set k := line (Line := L) U V h` and
transport.

**R8. Reuse of `Pas` (isometries).** The headers of `PascalAux1.lean` / `PascalAux2.lean` say
"groups I–IV", but the declarations used here are in sections whose variables are
`[hC : PlaneCongruence P L]` only (`PascalAux1.lean`: sections `Isometries` l. 33–, `TriIso`
l. 171–, `Reflections` l. 361–; `PascalAux2.lean`: sections `Signs` l. 30–58 and `HalfTurns`
l. 66–251). This was confirmed by compiling uses of `Pas.refl_opp`, `Pas.refl_isom`, `Pas.refl_fix`,
`Pas.isom_collinear_iff`, `Pas.ht`, `Pas.ht_isom`, `Pas.ht_eq_iff`, `Pas.ht_fix_iff`, `Pas.ht_ht`,
`Pas.midp`, `Pas.ht_midp`, `Pas.exists_eqd` under `PlaneCongruence` alone (Appendix A).
`Pas.exists_isom_of_tri`, `Pas.isom_between_iff`, `Pas.mem_ray_of_between_between`, `Pas.refl_refl`
were read but not compiled in a scratch file. Importing `PascalAux2` makes
the new modules depend on the Pascal helper chain up to that file (no cycle: `Commentary` does not
import the new files).

**R9. `Frame.angLt_congr`, `mem_interior_of_rays_plane`, `theorem13`, `theorem14`** are used with the
argument orders copied in § 2; they were read, not all compiled.

**R10. Size.** The calibrated estimate is ≈ 5100 lines (realistic range 4800–5400) in 17 files
(§ 4.15). The files that the first estimate put at the limit (Stage E, G3, G4–G8) are split in
advance (`Aux8`/`Aux8b`, `Aux12`/`Aux12b`, `Aux13`/`Aux14`). Aux5, Aux6, Aux9 remain at the limit
and may need a further `…b` split. None of the proofs needs heavy automation; all are chains of the
named lemmas.

**R11. Things deliberately not done.** (a) No link with the repository's `IsRightAngle`, `IsAcute`,
`IsObtuse` (`Congruence.lean`): the types `LtSupp`/`EqSupp`/`GtSupp` are compared with the
supplement, not with a right angle; the equivalence with `IsAcute` etc. is true but not needed.
(b) Exhaustiveness `LtSupp ∨ EqSupp ∨ GtSupp` is not needed (it follows from A8). (c) The converse
directions of D6 are not needed. (d) Nothing is proved for space geometry (`Frame` with several
planes); the target is a statement of plane geometry. (e) The wiring (root file
`HilbertFoundations.lean`, status and "Lean reading" of the unit `concl.angle_sum`, which now says
"Not proved here", the summary list in `CommentaryClose.lean`, `LegendreTheorem` remarks) is left to
the integration step.

**R12. What the type-checker has confirmed** (scratch files in `.lake-local/scratch/anglesum/`):
The file `.lake-local/scratch/anglesum/T3.lean` (reproduced in Appendix A; imports
`HilbertFoundations.Commentary` and `HilbertFoundations.PascalAux2`) compiles with
`python .lake-local/leanc.py` (`[OK]`, 193 s), the only warnings being the `sorry` of five
statement stubs. Confirmed:
* all definitions of § 4 elaborate as written: `LtSupp`, `EqSupp`, `GtSupp`, `SameType`, `SLt`,
  `Foot`, `BiRight`, `Saccheri`, `Lambert`, `TriConf`;
* the convention `variable (hl : …)` + `include hC hl`, and `abbrev fr`;
* **complete proofs** of: `ne_of_nc`, the wrappers `crossbar`, `layoff`, `layoff_unique`,
  `interior_or_interior` (0.1), `mem_ray_of_angCong` (0.2), `sameSide_of_not_meets` (0.5),
  `isom_angCong` (0.6), `ht_spec`, `midp_spec` (0.9), `angLt_of_interior` (A1), `angLt_irrefl` (A5),
  `between_refl_of_rightAng` (C4), `no_two_right` (C5), `exists_perp_at` (C10), `ext_angle_aux`
  (the first half of D1);
* the **statements** (with `sorry`) of `saccheri_out_lt` (E2), `lambert_nest` (F4),
  `saccheri_sameType` (F9), `exists_triConf` (G3), `tri_saccheri` (G8);
* the **final theorem**: `Conclusion.angleSumTheorem' : AngleSumTheorem` is proved there from the
  stubs `tri_saccheri` and `saccheri_sameType` exactly as in § 4.14, so the logical shape of the
  last step and the interfaces G8, F9 are right.
An earlier scratch file `T1.lean` also checked `isom_rightAng` and `exists_foot` (C6(a)) in a
version without `hl` (they need only the obvious adaptation).

*Critic's scratch file* `.lake-local/scratch/anglesum-critic-lean2/K1.lean` (imports `PascalAux2`
and `Commentary`; 182 s): **every** definition and **every statement of § 4.1–4.13 of the previous
version** elaborates under the complete variable line of § 4.0; complete proofs of `interior_rays`,
`mem_interior_iff`, `opp_of_interior`, `interior_trans`, the `rt_*` wrappers, `isom_nc`,
`isom_rightAng`, `isom_sameSide_self`, `isom_opp_self`, `ht_mem`, `angLt_congr_right`,
`sLt_trichotomy`, `biRight_mk`, `lambert_symm`, `exists_common`, the corrected `sLt_congr_right`,
and `lambert_transport` / `lambert_cut` up to one small stub each; API-fit tests of `theorem12`,
`theorem13`, `theorem14` (the shape of § 4.16 item 2), `vertical_angles`,
`Pas.mem_ray_of_between_between`. Its single error was a wrong `Collinear` permutation in a test
proof (§ 4.0).

*Revision scratch files* `.lake-local/scratch/anglesum-rev/K2.lean`, `K3.lean` (a copy of `K3` is
kept next to this blueprint as `tested_scratch_K3.lean`). `K3` (imports `PascalAux2`,
`Commentary`) compiles `[OK]` (114 s) with only `sorry` warnings, confirming the **new** interfaces
of this revision: the structures `OutConf`, `OutAux`, `TriConf`, and `MidConf` (in a section with
the `PlaneCongruence` instance — `K2`, without it, failed exactly at the four `Pas.ht` fields, R14);
the statements of `gtSupp_of_copy` (with `hX'`), `tri_midline`, `exists_outConf`, `outConf_aux`,
`outConf_lt`, `outConf_gt`, all G3 item lemmas `tri_B₁_ne` … `tri_sideYH` of § 4.12/4.12b,
`exists_triConf` (up to the final assembly), `triConf_canon`; complete proofs of
`outConf_not_mem_s` and of `saccheri_out_lt` from `exists_outConf` + `outConf_lt`; `K2` also
compiled the full proof of the corrected `sLt_congr_right`.

**Not** compiled: everything else — in particular B1 (`angLt_add`), D3–D6, the bodies of Stages
E, F, G. Those proofs exist only as the mathematics of § 3.

**R13. Possible simplification not taken.** D3 proves `refl m C = D` through the invariance of the
sides of the base under the reflection (0.8 with a fixed point `W` off the base). If this turns out
awkward, D4 alone can be proved without reflections (SAS for `CAB`, `DBA`, then SSS for `ACD`,
`BDC`), but D3 (the midline and the Lambert quadrilateral) is needed for D5, F9 anyway.


**R14. Structures with `Pas.ht` fields need the instance.** `MidConf` mentions `Pas.ht`, which
exists only under `[PlaneCongruence P L]`; it must be declared in a section that has this instance
(§ 4.11). The other structures (`OutConf`, `OutAux`, `TriConf`) and all predicates are declared,
as before, in a section with only the four `Has…` classes.

**R15. `E ∉ s` is not part of `OutAux`.** Lemma E1 is used with `E := P'` in E4, where `E ∈ s`.
Therefore the fact `E ∉ s` (needed in E2, E3, where `E ≠ P'`) is the separate lemma
`outConf_not_mem_s`, not a field.

---------------------------------------------------------------------------------------------------

## REJECTED CRITIQUES

Both critiques were checked point by point against the repository, by re-deriving the mathematics,
and (for the Lean points) by two new scratch compiles (R12). Every point was found correct and has
been incorporated: math critique — `s ≠ q` and `A ∉ q` (E0, E2, E3), the withdrawal of the
spherical tests (status line, R3, R4), `H, E ∉ y` (G3(9)), `M ≠ B` (D3); Lean critique —
`sLt_congr_right` with `hAB` (C2, § 4.5), `gtSupp_of_copy` with `hX'` (B8(c), § 4.4), the variable
line with `P'` (§ 4.0), the `--olean` build procedure (§ 4.0), the file splits (§ 4.8–4.15), the
`Prop`-structures `MidConf`, `OutConf`, `OutAux` (§ 4.8, § 4.11), the survey of the isometry API and
`Frame.parallel_of_alternate` (§ 2.6), and the hard-spot advice (§ 4.16). Only the following parts
were not adopted as proposed:

* **Lean critique, issue 7 (do not import `Commentary` in Aux13).** Correct but optional: the
  import only costs compile time. Kept as an *option* in § 4.13b; the default remains the
  type-checked arrangement with `Commentary` imported, because restating G4/G6/G8 for the unfolded
  predicate bodies duplicates long formulas and risks a mismatch with the definitions of § 1.
* **Lean critique, issue 6 (`MidConf` as written).** The proposed structure does **not** elaborate
  in a definitions section without the `PlaneCongruence` instance (its `Pas.ht` fields fail with
  "failed to synthesize `PlaneCongruence P L`"; first scratch compile of this revision). It is
  adopted with that correction (R14) and with one extra field `sideAB : SameSide e A B` (G1).
  Likewise the critic's `OutConf` sketch is adopted with `E ∉ s` moved out of `OutAux` (R15).
* **Lean critique, issue 2, alternative fix** (a helper `nc_of_mem_interior_left`). Not taken; the
  extra hypothesis `hX'` is cheaper, as the critic also recommends.

---------------------------------------------------------------------------------------------------

## APPENDIX A. Type-checked scratch file (`.lake-local/scratch/anglesum/T3.lean`)

This file compiles (Lean 4 v4.36.0, the repository's mathlib) with five `sorry` stubs. It is a
test, not a file of the project: in the real development the declarations are distributed over the
files of § 4 (each of which imports only what § 4 says; here everything is in one file importing
`Commentary`), and the stubs are replaced by the proofs of § 3. The theorem section shows the
header to use. `P'` is a point (the letter `P` is the type of points).
Its point `variable` line (`{A B C D E O X Y Z A' B' C' D' O' H K M N P' Q : P}`) is the
one of this test file only and lacks `F G A₁ B₁ O₁`; the new files must use the complete line of
§ 4.0, `{A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}`.
A copy of the file is kept next to this blueprint:
`.lake-local/plans/hilbert-angle-sum/tested_scratch_T3.lean` (not a module of the project).

```lean
import HilbertFoundations.Commentary
import HilbertFoundations.PascalAux2

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section Defs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
def LtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) A O B C O B

variable (L) in
def EqSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngCong A O B C O B

variable (L) in
def GtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) C O B A O B

variable (L) in
def SameType (A O B A' O' B' : P) : Prop :=
  (LtSupp L A O B ↔ LtSupp L A' O' B') ∧ (EqSupp L A O B ↔ EqSupp L A' O' B') ∧
    (GtSupp L A O B ↔ GtSupp L A' O' B')

def SLt (A B C D : P) : Prop := ∃ X, Between C X D ∧ SegCong A B C X

def Foot (l : L) (X F : P) : Prop :=
  F ∈ l ∧ X ∉ l ∧ ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F X

variable (L) in
def BiRight (A B C D : P) : Prop :=
  A ≠ B ∧ RightAng (L := L) B A C ∧ RightAng (L := L) A B D ∧
    ∀ l : L, A ∈ l → B ∈ l → SameSide l C D

variable (L) in
def Saccheri (A B C D : P) : Prop := BiRight L A B C D ∧ SegCong A C B D

variable (L) in
def Lambert (M B D N : P) : Prop :=
  RightAng (L := L) B M N ∧ RightAng (L := L) M B D ∧ RightAng (L := L) M N D

variable (L) in
structure TriConf (A B C F G H X Y A₁ B₁ : P) : Prop where
  nc : ¬Collinear (Line := L) A B C
  sac : Saccheri L F G A B
  hX : Between A C X
  hY : Between B₁ C Y
  angA : AngCong C A B X C Y
  sideY : ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B
  intY : Y ∈ Interior (Line := L) X C B
  angB : AngCong C B A B C A₁
  ncA : ¬Collinear (Line := L) A₁ C B
  sideA : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y
  angS : AngCong F A B H C B₁
  ncH : ¬Collinear (Line := L) B₁ C H
  ncH' : ¬Collinear (Line := L) A₁ C H
  angH : AngCong B₁ C H A₁ C H
  sideH : ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y
  sideYH : ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B

end Defs

section Thms

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E O X Y Z A' B' C' D' O' H K M N P' Q : P} {l m : L}
include hC hl

abbrev fr : Frame P L := planeFrame hl

theorem ne_of_nc (h : ¬Collinear (Line := L) A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B :=
  ne_of_not_collinear h (hl O)

theorem crossbar (h : ¬Collinear (Line := L) B A C) (hD : D ∈ Interior (Line := L) B A C) :
    ∃ Y, Between B Y C ∧ Y ∈ ray A D :=
  (fr hl).crossbar (S := Set.univ) rfl trivial trivial trivial trivial h hD

theorem layoff (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l) (hne : A' ≠ O')
    (hD : D ∉ l) : ∃ B', SameSide l B' D ∧ AngCong A O B A' O' B' := by
  obtain ⟨B', -, h1, h2⟩ := (fr hl).layoff Set.univ rfl A O B l O' A' D h (fun _ _ => trivial) hO'
    hA' hne trivial hD
  exact ⟨B', h1, h2⟩

theorem layoff_unique (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l)
    (hne : A' ≠ O') {B' B'' : P} (hs : SameSide l B' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A O B A' O' B'') : ray O' B' = ray O' B'' :=
  (fr hl).layoff_unique Set.univ rfl A O B l O' A' B' B'' h (fun _ _ => trivial) hO' hA' hne
    trivial trivial hs h1 h2

theorem mem_ray_of_angCong (h : ¬Collinear (Line := L) A O B) (hO : O ∈ l) (hA : A ∈ l)
    (hs : SameSide l B B') (hc : AngCong A O B A O B') : B' ∈ ray O B := by
  obtain ⟨hAO, -, -⟩ := ne_of_nc hl h
  have e := layoff_unique hl h hO hA hAO hs (angCong_refl (Line := L) h) hc
  rw [e]
  exact mem_ray_self' (L := L) (fun e' => hs.2.1 (e' ▸ hO))

theorem interior_or_interior {L' : P} (hHL : ¬Collinear (Line := L) H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear (Line := L) H O K) :
    K ∈ Interior (Line := L) H O L' ∨ H ∈ Interior (Line := L) K O L' :=
  (fr hl).interior_or_interior (S := Set.univ) rfl trivial trivial trivial trivial hHL hLO hs hHK

theorem isom_angCong {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : AngCong X Y Z (f X) (f Y) (f Z) := by
  have h1 : ¬Collinear (Line := L) Y X Z := fun hh => h hh.swap12
  have h1' : ¬Collinear (Line := L) (f Y) (f X) (f Z) := fun hh =>
    h1 ((Pas.isom_collinear_iff hf).1 hh)
  obtain ⟨hYX, hZX, hYZ⟩ := ne_of_nc hl h1
  exact ((fr hl).sss h1 h1' (hf Y X hYX) (hf Y Z hYZ) (hf X Z hZX.symm)).1

/-- A5 -/
theorem angLt_irrefl : ¬AngLt (L := L) A O B A O B := by
  rintro ⟨h, -, X, hX, hc⟩
  obtain ⟨hAO, hBO, hAB⟩ := ne_of_nc hl h
  have hOl : O ∈ line (Line := L) O A hAO.symm := mem_line_left _
  have hAl : A ∈ line (Line := L) O A hAO.symm := mem_line_right _
  have hBl : B ∉ line (Line := L) O A hAO.symm := fun hB => h (collinear_of_mem hAl hOl hB)
  have hs : SameSide (line (Line := L) O A hAO.symm) X B := sameSide_of_between_mem' hAl hBl hX
  have hr : X ∈ ray O B := mem_ray_of_angCong hl h hOl hAl (sameSide_symm' hs) hc
  have e : X = B := eq_of_collinear_collinear (L := L) h (collinear_of_between hX).swap23
    (collinear_of_mem_ray hr)
  exact ne23_of_between (Line := L) hX e

/-- C4 -/
theorem between_refl_of_rightAng {G F : P} (hG : G ∈ l) (hF : F ∈ l)
    (h : RightAng (L := L) G F X) : Between X F (Pas.refl l X) := by
  obtain ⟨hn, C, hC', hc⟩ := h
  obtain ⟨hGF, hXF, -⟩ := ne_of_nc hl hn
  have hXl : X ∉ l := fun hX => hn (collinear_of_mem hG hF hX)
  have ho := Pas.refl_opp (L := L) hXl
  have h2 := isom_angCong hl (Pas.refl_isom (P := P) l) hn
  rw [Pas.refl_fix hG, Pas.refl_fix hF] at h2
  have hoC : OppositeSides l X C := opp_of_between_mem hF hXl hC'
  have hs : SameSide l C (Pas.refl l X) := OrderCore.sameSide_of_opp_opp (opp_symm' hoC) ho
  have nC : ¬Collinear (Line := L) G F C := fun hc' => hs.1 (mem_of_collinear hc' hGF hG hF)
  have hr : Pas.refl l X ∈ ray F C := mem_ray_of_angCong hl nC hF hG hs
    (angCong_trans (L := L) nC hn (fun hc' => hs.2.1 (mem_of_collinear hc' hGF hG hF))
      (angCong_symm (L := L) hn nC hc) h2)
  exact between_of_mem_rays hC' (mem_ray_self' (L := L) hXF) hr


/-- C5 -/
theorem no_two_right {F F' : P} (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' X) :
    False := by
  obtain ⟨hF'F, hXF, -⟩ := ne_of_nc hl h1.1
  set t := line (Line := L) F F' hF'F.symm with ht
  have hFt : F ∈ t := mem_line_left _
  have hF't : F' ∈ t := mem_line_right _
  have hXt : X ∉ t := fun hX => h1.1 (collinear_of_mem hF't hFt hX)
  have b1 := between_refl_of_rightAng hl hF't hFt h1
  have b2 := between_refl_of_rightAng hl hFt hF't h2
  have hne : X ≠ Pas.refl t X := ne13_of_between (Line := L) b1
  obtain ⟨g, hXg, hX'g⟩ := exists_line (Line := L) hne
  have hFg : F ∈ g := mem_mid_of_between b1 hXg hX'g
  have hF'g : F' ∈ g := mem_mid_of_between b2 hXg hX'g
  have e : g = t := line_unique hF'F.symm hFg hF'g hFt hF't
  exact hXt (e ▸ hXg)

/-- 0.5 -/
theorem sameSide_of_not_meets {k m : L} (h : ¬Meets (Point := P) m k) (hX : X ∈ m) (hY : Y ∈ m) :
    SameSide k X Y :=
  ⟨fun hk => h ⟨X, hX, hk⟩, fun hk => h ⟨Y, hY, hk⟩,
    fun ⟨Z, hZk, hZ⟩ => h ⟨Z, mem_mid_of_between hZ hX hY, hZk⟩⟩

/-- A1 -/
theorem angLt_of_interior (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hX : X ∈ Interior (Line := L) A' O' B') (hc : AngCong A O B A' O' X) :
    AngLt (L := L) A O B A' O' B' := by
  obtain ⟨hAO, hBO, -⟩ := ne_of_nc hl h
  obtain ⟨hA'O', hB'O', -⟩ := ne_of_nc hl h'
  obtain ⟨Y, hY, hYr⟩ := crossbar hl h' hX
  have nX := (nc_of_interior (L := L) hA'O' hB'O' hX).1
  exact ⟨h, h', Y, hY, angCong_rays (L := L) h nX hc (mem_ray_self' (L := L) hAO)
    (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) hA'O') hYr⟩

/-- 0.9 -/
theorem ht_spec {M : P} (h : X ≠ M) :
    Between X M (Pas.ht (L := L) M X) ∧ SegCong M X M (Pas.ht (L := L) M X) :=
  (Pas.ht_eq_iff (L := L) h).1 rfl

theorem midp_spec (h : A ≠ C) :
    Between A (Pas.midp (L := L) A C) C ∧ Pas.ht (L := L) (Pas.midp (L := L) A C) A = C ∧
      Pas.ht (L := L) (Pas.midp (L := L) A C) C = A := by
  have h1 : Pas.ht (L := L) (Pas.midp (L := L) A C) A = C := Pas.ht_midp (L := L) A C
  have hne : A ≠ Pas.midp (L := L) A C := fun e =>
    h (((Pas.ht_fix_iff (L := L)).2 e).symm.trans h1)
  refine ⟨((Pas.ht_eq_iff (L := L) hne).1 h1).1, h1, ?_⟩
  have h2 := Pas.ht_ht (L := L) (Pas.midp (L := L) A C) A
  rwa [h1] at h2

/-- D1, first half -/
theorem ext_angle_aux (h : ¬Collinear (Line := L) A B C) (hD : Between B C D) :
    AngLt (L := L) B A C A C D := by
  obtain ⟨hAB, hCB, hAC⟩ := ne_of_nc hl h
  obtain ⟨hM, f1, f2⟩ := midp_spec hl hAC
  generalize Pas.midp (L := L) A C = M at hM f1 f2
  have hDC : D ≠ C := (ne23_of_between (Line := L) hD).symm
  obtain ⟨a, hAa, hCa⟩ := exists_line (Line := L) hAC
  have hBa : B ∉ a := fun hB => h (collinear_of_mem hAa hB hCa)
  have hMa : M ∈ a := mem_mid_of_between hM hAa hCa
  have hBM : B ≠ M := fun e => hBa (e ▸ hMa)
  obtain ⟨hb, -⟩ := ht_spec hl hBM
  have nBAC : ¬Collinear (Line := L) B A C := fun hc => h hc.swap12
  have a1 := isom_angCong hl (Pas.ht_isom (L := L) M) nBAC
  have nB'CA : ¬Collinear (Line := L) (Pas.ht (L := L) M B) (Pas.ht (L := L) M A)
      (Pas.ht (L := L) M C) :=
    fun hh => nBAC ((Pas.isom_collinear_iff (Pas.ht_isom (L := L) M)).1 hh)
  rw [f1, f2] at a1 nB'CA
  generalize Pas.ht (L := L) M B = B' at hb a1 nB'CA
  have o1 : OppositeSides a B B' := opp_of_between_mem hMa hBa hb
  have o2 : OppositeSides a B D := opp_of_between_mem hCa hBa hD
  have s1 : SameSide a B' D := OrderCore.sameSide_of_opp_opp (opp_symm' o1) o2
  obtain ⟨n, hBn, hCn⟩ := exists_line (Line := L) hCB.symm
  have hAn : A ∉ n := fun hA => h (collinear_of_mem hA hBn hCn)
  have hDn : D ∈ n := mem_right_of_between hD hBn hCn
  have s2 : SameSide n M A := sameSide_of_between_mem' hCn hAn (between_symm hM)
  have hB'n : B' ∉ n := fun hB'n => s2.1 (mem_mid_of_between hb hBn hB'n)
  have s3 : SameSide n M B' := sameSide_of_between_mem' hBn hB'n hb
  have s4 : SameSide n B' A := OrderCore.sameSide_trans (sameSide_symm' s3) s2
  have hint : B' ∈ Interior (Line := L) A C D := by
    refine (interior_iff (L := L) hAC hDC).2 ⟨?_, ?_⟩
    · rw [← eq_line hAC.symm hCa hAa]; exact s1
    · rw [← eq_line hDC.symm hCn hDn]; exact s4
  have nACD : ¬Collinear (Line := L) A C D := fun hc => s1.2.1 (mem_of_collinear hc hAC hAa hCa)
  exact angLt_of_interior hl nBAC nACD hint (angCong_swap_right (Line := L) nBAC nB'CA a1)

/-- C10 -/
theorem exists_perp_at {F : P} (hF : F ∈ l) :
    ∃ m : L, F ∈ m ∧ ∀ Z : P, Z ∈ m → Z ≠ F → ∀ G : P, G ∈ l → G ≠ F →
      RightAng (L := L) G F Z := by
  obtain ⟨G₀, hG₀l, hG₀F⟩ : ∃ G₀ : P, G₀ ∈ l ∧ G₀ ≠ F := by
    obtain ⟨U, V, hUV, hU, hV⟩ := exists_two_points (Point := P) l
    by_cases hUF : U = F
    · exact ⟨V, hV, fun e => hUV (hUF.trans e.symm)⟩
    · exact ⟨U, hU, hUF⟩
  obtain ⟨hb, hs⟩ := ht_spec hl hG₀F
  generalize Pas.ht (L := L) F G₀ = G₁ at hb hs
  have hG₁F : G₁ ≠ F := (ne23_of_between (Line := L) hb).symm
  obtain ⟨m, hmem, hrefl, hopp⟩ := Pas.exists_eqd (L := L) (ne13_of_between (Line := L) hb)
  have hFm : F ∈ m := (hmem F).2 ⟨hG₀F.symm, hG₁F.symm, hs⟩
  refine ⟨m, hFm, fun Z hZm hZF G hG hGF => ?_⟩
  have hml : m ≠ l := fun e => hopp.1 (e ▸ hG₀l)
  have hZl : Z ∉ l := fun hZl => hZF (eq_of_mem_of_mem hml hZm hZl hFm hF)
  have hn : ¬Collinear (Line := L) G₀ F Z := fun hc => hZl (mem_of_collinear hc hG₀F hG₀l hF)
  have a1 := isom_angCong hl (Pas.refl_isom (P := P) m) hn
  rw [hrefl, Pas.refl_fix hFm, Pas.refl_fix hZm] at a1
  have hn₁ : ¬Collinear (Line := L) G₁ F Z := fun hc =>
    hZl (mem_of_collinear hc hG₁F (mem_right_of_between hb hG₀l hF) hF)
  have r1 : RightAng (L := L) Z F G₀ :=
    ⟨fun hc => hn hc.swap13, G₁, hb,
      angCong_swap_left (Line := L) hn (fun hc => hn₁ hc.swap13)
        (angCong_swap_right (Line := L) hn hn₁ a1)⟩
  exact (fr hl).rt_arm ((fr hl).rt_symm r1) hGF (collinear_of_mem hF hG₀l hG)

/-! statements -/

theorem saccheri_out_lt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by
  sorry

theorem saccheri_sameType (h : Saccheri L A B C D) (h' : Saccheri L A' B' C' D') :
    SameType L A C D A' C' D' := by
  sorry

theorem lambert_nest {B₀ D₁ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B)
    (hD₁ : Between N D₁ D) (h₁ : Lambert L M B₀ D₁ N) : SameType L B D N B₀ D₁ N := by
  sorry

theorem exists_triConf (h : ¬Collinear (Line := L) A B C) :
    ∃ F G H X Y A₁ B₁ : P, TriConf L A B C F G H X Y A₁ B₁ := by
  sorry

open Conclusion in
theorem tri_saccheri (h : ¬Collinear (Line := L) A B C) :
    ∃ F G : P, Saccheri L F G A B ∧ (AngleSumLtTwoRight L A B C ↔ LtSupp L F A B) ∧
      (AngleSumEqTwoRight L A B C ↔ EqSupp L F A B) ∧
      (AngleSumGtTwoRight L A B C ↔ GtSupp L F A B) := by
  sorry

end Thms

end AngSum

namespace Conclusion

open AngSum in
theorem angleSumTheorem' : AngleSumTheorem := by
  intro P L _ _ _ _ hC A B C A' B' C' hT'
  have key : ∀ hl : (∀ X : P, ∃ l : L, X ∈ l), IsTriangle (Line := L) A B C →
      (AngleSumGtTwoRight L A B C → AngleSumGtTwoRight L A' B' C') ∧
      (AngleSumEqTwoRight L A B C → AngleSumEqTwoRight L A' B' C') ∧
      (AngleSumLtTwoRight L A B C → AngleSumLtTwoRight L A' B' C') := by
    intro hl hT
    obtain ⟨F, G, hS, hLt, hEq, hGt⟩ := tri_saccheri hl hT
    obtain ⟨F', G', hS', hLt', hEq', hGt'⟩ := tri_saccheri hl hT'
    obtain ⟨t1, t2, t3⟩ := saccheri_sameType hl hS hS'
    exact ⟨fun h => hGt'.2 (t3.1 (hGt.1 h)), fun h => hEq'.2 (t2.1 (hEq.1 h)),
      fun h => hLt'.2 (t1.1 (hLt.1 h))⟩
  have hl_of : ∀ {X : P}, Between A C X → ∀ Z : P, ∃ l : L, Z ∈ l := fun hb =>
    line_through_of_ne (L := L) (ne12_of_between (Line := L) hb)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.2 h

end Conclusion

end HilbertFoundations
```
