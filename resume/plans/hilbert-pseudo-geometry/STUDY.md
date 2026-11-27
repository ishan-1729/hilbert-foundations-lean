# STUDY: unit `concl.pseudo_geometry` (`Conclusion.PseudoGeometryTheorem`)

Target: `HilbertFoundations/Commentary.lean`, lines 532-573, `HilbertFoundations.Conclusion.PseudoGeometryTheorem`.
Status of this document: architecture and feasibility study, not a line-by-line blueprint.
Scratch check: `.lake-local/scratch/pseudo-study/Final.lean` (final assembly, see section 4, stage S0).

## 0. Verdict in ten lines

* The statement is TRUE for every plane satisfying I, II, IV (it is a corollary of the Hjelmslev-Bachmann-Pejas
  embedding theorem) and it is not degenerate. No defect of the formal statement was found.
* There is NO shortcut. Any `φ` as in the statement makes the points off `t` a sub-configuration of a
  plane with I-IV and parallels, which is the Cartesian plane over a commutative ordered field; so the
  statement contains "every Hilbert plane is locally Pappian and Desarguesian with an orderable
  coordinate field". Routes (B) and (C) of the task collapse into route (A).
* The proof needs the calculus of reflections (three-reflections theorem, pencils, half-rotations).
  The repository has none of it (no reflection as a map, no motion group, no pencils).
* Three genuine simplifications over the textbook route were found and are rigorous (section 3):
  (1) work only in the affine chart `A_O` whose line at infinity is the polar of a real point `O ∉ t`;
  (2) get the ordering of the coordinate field for free: the field is Pythagorean and `-1` is not a
  square, hence semireal, hence orderable by `IsSemireal.exists_linearOrder` (Tau Ceti, already a
  dependency). The order of the Hilbert plane is never transported to ideal points;
  (3) move `t` to infinity at the very end by an explicit projective change of chart in coordinates.
* One block is NOT reconstructed in this study and must be transcribed from the literature (or
  re-derived) at blueprint time: the group-theoretic theorem of Pappus-Brianchon for lines of two
  pencils and the theory of half-rotations (Bachmann, *Aufbau der Geometrie aus dem
  Spiegelungsbegriff*, 2nd ed., § 4 and § 6). I could state these results but not re-prove them from
  memory; they are flagged under RISKS.
* Honest size: about 24 000 lines of Lean (range 18 000 - 32 000), in about 10 stages.

## 1. The statement

```
def PseudoGeometryTheorem : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → ∀ t : L,
      ∃ (P' L' : Type) (_ : HasLines P' L') (_ : HasBetween P') (_ : HasSegCong P') (_ : HasAngCong P'),
        PlaneParallels P' L' ∧ PlaneCongruence P' L' ∧
        ∃ φ : {A : P // A ∉ t} → P', Function.Injective φ ∧
          (∀ A B C, Collinear (A : P) B C ↔ Collinear (φ A) (φ B) (φ C)) ∧
          ∀ A B C D (T : P), T ∈ t → (A : P) ≠ B → (C : P) ≠ D → ¬Collinear (A : P) B C →
            Collinear (A : P) B T → Collinear (C : P) D T →
              ∀ X : P', ¬(Collinear (φ A) (φ B) X ∧ Collinear (φ C) (φ D) X)
```

Reading. `PlaneCongruence P L` is the full Hilbert plane of this edition (I 1-2, I 7 plane clauses,
II 1-5, IV 1-6; no parallels, no Archimedes). `P'` is any plane with I-IV and III. Only collinearity
is transported. Universe: everything is in `Type`, and the construction below stays in `Type`
(the coordinate field is a subtype/quotient built from `P` and `L`).

Truth. By the embedding theorem (Hjelmslev 1907; Bachmann § 6; Pejas, Math. Ann. 143 (1961)), a
Hilbert plane is, as an incidence structure, a set of points of the projective plane over a
Pythagorean formally real field `K`, its lines being traces of projective lines. Remove the
projective line through `t`: the points off `t` lie in the affine plane `K²`, collinearity is
preserved and reflected, and two distinct lines through `T ∈ t` become distinct affine lines with the
same point at infinity, i.e. disjoint. `P' := Coord K 2` with any ordering of `K`.

Degenerate instances checked: `Collinear A A C` holds on both sides (two points always lie on a
line in both planes); points off `t` exist; in the last clause `φ A ≠ φ B` and `φ C ≠ φ D` by
injectivity, so both lines of `P'` are determined and the clause says exactly "the two image lines
are disjoint". No vacuity, no falsity.

## 2. Comparison of the routes

### (B) Shortcuts exploiting the weak statement: none exists

Let `φ` be as in the statement. `P'` satisfies I-IV and III, so (Hilbert Ch. III; in the repository
`Pascal.lean`, `Proportion.lean`) Pascal's and Desargues's theorems hold in `P'`. Because `φ`
preserves and reflects collinearity and sends "meet on `t`" to "parallel", every instance of these
theorems all of whose points are `φ`-images is an incidence theorem about `P \ t`. So the statement
implies the affine Desargues and Pappus theorems for all configurations of points of `P` off `t`
(with "parallel" read as "meeting on `t`"), for every Hilbert plane, including the non-Archimedean
semi-elliptic and semi-hyperbolic ones where two lines need have neither a common point nor a common
perpendicular. These closure theorems are exactly what the theory of ideal elements proves; they are
not consequences of anything already in the repository (all of Chapters III, V, VI there assume the
parallel axiom III: `PlaneParallels`).

"Prove Desargues for the partial plane `P \ t` directly and feed the repository's coordinatization":
the repository's coordinatization (`DesarguesAlgebra*.lean`, Artin-style: translations and central
dilatations built from `DesarguesII`) needs an affine plane, i.e. `PlaneParallels` (existence AND
uniqueness of parallels, every two non-parallel lines meet). `P \ t` is not one: lines that do not
meet in `P` and do not meet on `t` exist. Making it one is precisely the introduction of ideal
points. A coordinatization of "partial planes with local Desargues" exists in the literature but is
longer than the ideal-element construction and not in the repository.

Choosing `P'` large (real closure, Pythagorean closure) does not help: the coordinate field of `P`
has to exist and to be commutative and orderable before anything can be embedded. In fact no
extension is needed: the field itself is Pythagorean (stage S8).

Dehn's own route (make the pseudo-geometry itself the plane `P'`, with a pseudo-congruence and the
cut-open projective order) is strictly more expensive: all of II and IV would have to be verified
for ideal points. Rejected.

### (C) Case split by the type of the plane: no gain

The trichotomy semi-Euclidean / semi-hyperbolic / semi-elliptic does not simplify anything: without
Archimedes's axiom none of the three types has parallels or limiting parallels available, and the
calculus of reflections treats the three uniformly. (In the semi-Euclidean case alone the chart of
section 3 has native translations, but that case is a small part.) Hartshorne §§ 41-43 (ends,
Hilbert's field of ends) needs the limiting-parallel axiom and does not apply.

### (A) The classical route: the only one, with three simplifications

Reflections → three-reflections theorem → pencils → half-rotations → affine plane of ideal
points → Pappus / Desargues → coordinates → field Pythagorean and semireal → Cartesian plane.
Every step is a theorem for ALL Hilbert planes (the only property of order used is that a Hilbert
plane is "non-elliptic": two distinct perpendiculars to a line never meet, and that it has free
mobility: midpoints, perpendiculars, angle bisectors).

## 3. The mathematics of the recommended route (what is new, with proofs)

Notation. `σ_a` is the reflection in the line `a` (a bijection of `P`), products are compositions,
`S` the set of line reflections, `G` the group they generate. `a ⊥ b` : `a`, `b` perpendicular.
For `a ≠ b`, a line `c` *lies in the pencil of* `a, b` if `σ_a σ_b σ_c ∈ S`. A pencil is *proper*
(all lines through a point), a *perpendicular pencil* (all perpendiculars to a line), or neither.
`O` is a fixed point with `O ∉ t`.

### 3.1 The chart `A_O` (replaces the projective ideal plane)

In the ideal plane the polar of `O` is the set of perpendicular pencils of the lines through `O`,
and no real point lies on it. Use it as line at infinity. Concretely, for real lines:

    a ∥_O b   :⇔   the perpendicular from O to a is also perpendicular to b.

`∥_O` is an equivalence relation on real lines, two distinct `∥_O`-parallel lines are disjoint
(non-elliptic), and through every real point there is exactly one `∥_O`-parallel to a given line
(drop `u ⊥ a` from `O`, then the perpendicular to `u` from the point). What fails in `P` is only
"non-parallel lines meet". The affine plane `A_O` is `P` completed by the missing meeting points.
Two equivalent constructions (the blueprint must pick one; see S5):

* (pencils) points = pencils that are not perpendicular pencils of a line through `O`; lines = the
  real lines, plus the ideal lines obtained from real lines by the inverse contractions below;
* (fractions) points = classes `X / D` of a real point `X` and a contraction `D`, lines = classes
  `ℓ / D` of a real line and a contraction, with `X/D ∈ ℓ/D ⇔ X ∈ ℓ`, after reduction to a common
  denominator. This uses only real points and lines; pencils remain a proof tool.

Contractions. For two non-perpendicular lines `u, v` through `O`, the half-rotation of Hjelmslev
sends a point `X` to the foot of the perpendicular from `X` to the image of the line `OX` under the
rotation `σ_u σ_v`; composed with the inverse rotation it is the *contraction* `D_{u,v}` (in a
Klein-Beltrami or Cartesian chart centred at `O`: multiplication by `cos ∠(u,v)`). Facts needed
(Bachmann § 6, theorems on half-rotations; NOT re-proved in this study, see risk R1):

    (C1) D is injective, fixes O, maps every line through O into itself, preserves and reflects collinearity;
    (C2) D maps every line ℓ into a line ∥_O ℓ; it maps lines of a pencil to lines of a pencil;
    (C3) contractions commute with each other and with the motions fixing O;
    (C4) (shrinking) real lines a, b that are not ∥_O-parallel have contracted images that meet in a real point.

Proved here (elementary, synthetic), *transitivity*: for real `X ≠ Y` on one ray from `O` there are
contractions with `D₁ X = D₂ Y`. Proof: let `Y'` be `Y` rotated about `O` by a right angle, `F` the
foot of the perpendicular from `O` to the line `X Y'` (`O ∉ XY'`, and `F` lies strictly inside the
segment `XY'` because the angle `X O Y'` is right and the angles at `X`, `Y'` are acute). Then `F`
is at once the foot of the perpendicular from `X` and from `Y'` to the line `OF`. So the contraction
of angle `∠XOF` sends `X`, and the contraction of angle `∠Y'OF` sends `Y'`, to the points of their
rays at distance `OF` from `O`; rotating back by the right angle, `D₁ X = D₂ Y`. Hence the group `H`
of fractions `D₁⁻¹ D₂` (together with the point reflection in `O`) acts on `A_O` as a commutative
group of dilatations with centre `O`, transitive on `ℓ \ {O}` for every line `ℓ ∋ O`.

Consequences that are immediate (and need no closure theorem):

* Desargues's theorem with centre `O` and Pascal's theorem with carriers through `O` hold in `A_O`
  (the usual dilatation argument; commutativity of `H` is Pascal).
* Every affine point of `A_O` is `η⁻¹(real point)` and every affine line not through `O` is
  `η⁻¹(real line)` for some `η ∈ H`; a finite configuration can be made real simultaneously.
  Lines through `O` are always real.

### 3.2 What still has to be proved about `A_O`: one closure theorem

The repository coordinatizes an affine plane from `DesarguesII` (both cases: joins concurrent, joins
parallel) and identifies commutativity with `PascalTheorem`. With 3.1 this reduces as follows.

LEMMA 3.2 (proved here). Let `A` be an affine plane, `O` a point, `H` a commutative group of
dilatations with centre `O` transitive on `ℓ \ {O}` for all `ℓ ∋ O`, `R` a group of collineations
fixing `O` and transitive on the lines through `O`, and let ONE translation `τ ≠ id` exist. Then
`DesarguesII A` and `PascalTheorem A` hold.
Proof. The conjugates `ρ η τ η⁻¹ ρ⁻¹` are translations taking `O` to any prescribed point `≠ O`
(first `η` moves `τ O` along the line `O τO`, then `ρ` turns the line); a translation is determined
by one image (`tr_eq_of`) and composites of translations are translations (`IsTr.comp`), so the
translations are transitive. Conjugating `H` by translations gives the dilatations with any centre,
transitive on each line through the centre. From transitive translations and central dilatations
`DesarguesII` follows in the classical way (the dilatation with centre `Z` taking `A` to `A'` takes
`B` to `B'` and `C` to `C'`, hence `BC ∥ B'C'`; same with a translation when the joins are parallel),
and `PascalTheorem` follows from the commutativity of the conjugates of `H`. ∎

So everything about `A_O` that is not native is the existence of one non-trivial translation of
`A_O` (equivalently: little Desargues in one direction; equivalently, by shrinking, a Desargues
statement about ten REAL points of `P` with `∥_O`). In the semi-Euclidean case it is native
(`∥_O` does not depend on `O`, so the dilatations with every real centre preserve `∥_O`). In general
it is a true closure theorem. Known proof:

* (P) Bachmann: the group-theoretic theorem of Pappus-Brianchon (§ 4): if `a₁,a₂,a₃` lie in a pencil,
  `b₁,b₂,b₃` lie in a pencil, and `c₃` lies in the pencils `(a₁,b₂)` and `(a₂,b₁)`, `c₁` in `(a₂,b₃)`,
  `(a₃,b₂)`, `c₂` in `(a₃,b₁)`, `(a₁,b₃)`, then `c₁,c₂,c₃` lie in a pencil. It is a statement about
  nine REAL lines; by 3.1 every Brianchon configuration of `A_O` can be made real, so the dual of
  Pappus's theorem, hence Pappus's theorem (self-dual, one application), holds in the projective
  closure of `A_O`. Then either Desargues by Hessenberg's theorem, or more cheaply: affine Pappus
  with parallel carriers gives the translation needed in Lemma 3.2 (little Pappus ⇒ little
  Desargues, about one page on paper).
* I did not find a proof that avoids a Pappus-type group computation. Tried and discarded: an elation
  of axis polar(`O`) as an explicit product of reflections and contractions (exists in coordinates,
  no synthetic verification found); Lenz-Barlotti style bootstrapping from the
  `(O', polar O')`-transitivities (needs control of how contractions move the polars of other points).

### 3.3 The coordinate field is Pythagorean and semireal: no order has to be extended (proved here)

Let `F` be the field coordinatizing `A_O` in a frame `O, E, E'` with `OE ⊥ OE'` and `OE ≅ OE'`.
Every line of `A_O` through `O` is a real line, so every `m ∈ F` is the slope of a real line `u_m`.

1. The reflection `σ_u` in a line `u ∋ O` acts on `A_O` as a collineation fixing `O` and `u`
   pointwise. Such a map is additive (it preserves parallelograms) and commutes with the scalar
   action (`λw` is cut out on `Ow` by the parallel through `λv` to `vw`, for `v ∈ u` fixed), hence
   it is `F`-linear. It maps `u^⊥` (the perpendicular through `O`) to itself and is an involution,
   so it is `-1` on `u^⊥` (`+1` would make it the identity; in particular char `F ≠ 2`).
2. The rotation `J = σ_d σ_g` (`g = OE`, `d` the bisector, which swaps `E` and `E'`) is
   `(x,y) ↦ (-y,x)`, and `J u = u^⊥` for every line `u ∋ O` (a quarter turn). So
   `u_m^⊥ = span(-m,1)`; since `u_m ≠ u_m^⊥`, `1 + m² ≠ 0` for all `m`: `-1` IS NOT A SQUARE.
3. Let `b` be the bisector of `g` and `u_m`, of slope `k`. By 1, `σ_b(E) = ((1-k²)/(1+k²), 2k/(1+k²))
   =: (c,s)` with `c² + s² = 1`, and `σ_b(E) ∈ u_m`, i.e. `s = m c` (`c ≠ 0` unless `u_m` is the
   y-axis). Hence `1 + m² = (1/c)²`: EVERY `1 + m²` IS A SQUARE.
4. So every sum of two squares is a square (`a² + b² = a²(1 + (b/a)²)`), every sum of squares is a
   square, and `-1` is not a sum of squares: `IsSemireal F`. By `IsSemireal.exists_linearOrder`
   `F` has a linear order making it a strict ordered ring, and for that order `IsPythagorean F`
   (the repository's class: `∃ y ≥ 0, y² = 1 + x²`; take `|y|`).

The order of `F` so obtained has nothing to do with the betweenness of `P`, and it need not: `φ`
is not required to preserve order. This removes the hardest part of Pejas's theory (ordering the
ideal plane). Group II of `P` enters only through neutral geometry (existence of perpendiculars,
midpoints, bisectors, "two perpendiculars to a line do not meet").

### 3.4 Moving `t` to infinity (proved here)

After S7 there is an injective `κ : P → F²`, collinear ⇔ collinear, every real line being the trace
of an affine line. `t` has an equation `ax + by + c = 0` with `c ≠ 0` (`O = (0,0) ∉ t`); scale to
`c = 1`. Put `λ(x,y) = ax + by + 1` and

    ψ(x,y) = (x / λ, y / λ)        on {λ ≠ 0}.

`ψ` is injective (`1/λ = 1 - a x' - b y'` recovers `λ` from the image `(x',y')`), and three points
with `λ ≠ 0` are collinear iff their `ψ`-images are (the 3×3 determinant of the images is the
determinant of the points divided by `λ₁λ₂λ₃`). `φ := ψ ∘ κ` on `{A ∉ t}` (there `λ(κA) ≠ 0`
because `κ` reflects collinearity with two points of `t`).
Last clause: let `κT = (p,q)`, `λ(p,q) = 0`, so `(p,q) ≠ 0`. A line through `κT` with direction
`(d₁,d₂)`, not the line `t`, has `δ := a d₁ + b d₂ ≠ 0`, and for `Z = (p,q) + s(d₁,d₂)`, `s ≠ 0`:
`λ(Z) = sδ`, `ψ(Z) = (1/(sδ))·(p,q) + (1/δ)·(d₁,d₂)`. So `ψ` maps every line through `κT` into a
line of direction `(p,q)`: the images of two distinct lines through `T` are two parallel lines of
`F²`, distinct because `φ` reflects collinearity, and no `X` is collinear with both pairs.

### 3.5 Small results of the calculus of reflections that I verified (basis of the estimates)

* Rigidity: a motion (bijection preserving `Between`, `SegCong`, `AngCong`) fixing two points
  `A ≠ B` is the identity or `σ_{AB}` (IV 1 and IV 4 uniqueness).
* Three reflections, concurrent lines `a,b,c ∋ O`: take `X ∈ a`, `X ≠ O`, let `d` be the
  perpendicular bisector of `X` and `X' := σ_c σ_b X` (it passes through `O`; `d := a` if `X' = X`).
  Then `μ = σ_d σ_c σ_b σ_a` fixes `O` and `X`; `μ = σ_a` would give `σ_d σ_c σ_b = 1`, impossible
  (a reflection is not a product of two reflections: for `b ≠ c` the fixed points of `σ_c σ_b` are
  at most `O`). So `μ = 1`. No notion of orientation is needed.
* Three reflections, `a,b,c ⊥ g`: the same with `X` the foot of `a`; `μ` maps `g` to itself,
  preserves the sides of `g` and the order of `g`, fixes `X`, hence is `1`.
* `σ_a σ_b σ_c ∈ S` is invariant under all permutations of `a,b,c` (inverse and conjugation).
* Every pencil has a line through every real point `Q`: with `A, B` the feet of the perpendiculars
  `u, v` from `Q` to `a, b` and `w` the perpendicular from `Q` to `AB` (case `A ≠ B`), put
  `c := σ_u σ_w σ_v ∈ S`. Then `σ_a σ_c σ_b = (σ_a σ_u) σ_w (σ_v σ_b)` is the product point `A` ·
  line `w` · point `B` with `A, B ∈ d := AB`, `w ⊥ d`; it equals `σ_{a'} σ_w σ_{b'}` for the
  perpendiculars `a', b'` to `d` at `A, B`, a reflection by the second three-reflections theorem.
  (This is the Lotensatz in the form used for contractions.)

## 4. Architecture: the chain of intermediate theorems

All new code in new files `HilbertFoundations/PseudoGeometry*.lean` (no new library, no fork),
the closing theorem in a `...Close` file as for the other closed units. Line counts are estimates
of final Lean, proofs included.

### S0. Final assembly (60 lines; scratch-checked)

`pseudoGeometry_of_coord`: if for every Hilbert plane and line `t` there are a field `K : Type`
with `LinearOrder`, `IsStrictOrderedRing`, `IsPythagorean` and an injective
`φ : {A // A ∉ t} → Coord K 2` with the two collinearity clauses, then `PseudoGeometryTheorem`.
Proof: `⟨Coord K 2, CoordLine K 2, inferInstance ×4, planeParallels_coord K,
planeCongruence_of_isPythagorean K, φ, …⟩`. The statement and this proof are in
`.lake-local/scratch/pseudo-study/Final.lean` (see section 8 for the compile status).
Risk: none.

### S1. Motions and reflections of a Hilbert plane (about 2 500 lines)

Setting `[PlaneCongruence P L]`. Repository provides: SAS, ASA, SSS (`CongruenceAux3.lean`: `sas`,
`asa`, `sss`), supplementary and vertical angles, all right angles congruent (`right_angles`),
segment addition/subtraction and laying off (`CongruenceAux2.lean`), a perpendicular to a line
(`Constructions.problem5`, `ConstructionsAux.Perp`), uniqueness of midpoints
(`CongruenceAux4.midpoint_unique`), neutral existence of a parallel (`Commentary.lean`,
`exists_parallel`, `theorem19_converse_alternate`), sides of a line and rays (`Basic.lean`,
`Order.lean`). It does NOT provide: the reflection as a map, motions, feet of perpendiculars from an
arbitrary point in the neutral plane setting, midpoints and angle bisectors as existence theorems
in the plane setting (several exist only relative to a plane of space, `F.IsPl S`; they have to be
re-proved or transferred).
To prove: (a) foot of the perpendicular from a point, uniqueness; two distinct perpendiculars to a
line do not meet; (b) existence of the midpoint and the perpendicular bisector, of the bisector of
two lines through a point; (c) `reflect a : P ≃ P`, involutive, fixes exactly the points of `a`,
preserves `Between`, `SegCong`, `AngCong`, lines, perpendicularity, sides; (d) the structure
`Motion` (bijections preserving `Between` and `SegCong`, then everything), rigidity (3.5);
(e) a motion conjugates reflections to reflections: `g ∘ reflect a ∘ g⁻¹ = reflect (g a)`.
Risk: low (classical neutral geometry), but long; the junk-tolerant `AngCong` on degenerate tuples
needs care.

### S2. The reflection calculus as an abstract interface (about 2 500 lines)

A structure `MetricPlane` in the style of Bachmann: a group `G`, a conjugation-stable generating
set `S` of involutions ("lines"), points = involutory products of two lines, with the axioms
(1) two points lie on a line, (2) uniquely if distinct, (3) `a,b,c | P ⇒ abc ∈ S`,
(4) `a,b,c | g ⇒ abc ∈ S`, (non-elliptic) no involutory `abc` is a point, and the free-mobility
extras used later (midpoint lines, bisectors). Instance from S1 with `G ≤ Equiv.Perm P` (proofs of
(3), (4) as in 3.5). Then the elementary theory (Bachmann § 3): perpendiculars, the characterization
of `abc ∈ S` for `a,b` with a common point or a common perpendicular (converse of the axioms),
every element of `G` is a product of at most three lines, parity (a product of an even number of
lines is not a line), the abelian groups of rotations about a point and of translations along a
line. All proofs are short identities in a group (`group`, `simp` with involution lemmas).
Design choice to settle in the blueprint: abstract structure (clean algebra, one transfer lemma
per notion) versus working directly in `Equiv.Perm P`. Recommended: abstract structure for S2-S4,
because S3-S4 are pure group calculations in the source.
Risk: low-medium (bookkeeping of the dictionary point/line ↔ group element).

### S3. Pencils and the theorem of Pappus-Brianchon (about 4 000 lines)

Definitions: `InPencil a b c := a * b * c ∈ S` (for `a ≠ b`), pencils as sets of lines.
Theorems, in order:
1. symmetry of `InPencil` (3.5);
2. a line of the pencil through every point (3.5), unique unless the pencil is proper at that point;
3. Lotensatz (Hjelmslev): for `a,b ∋ O`, feet `A,B` of a point `Q`, the perpendicular from `O` to
   `AB` is `a·(OQ)·b` (same computation as in 3.5);
4. transitivity: `a ≠ b`, `c ≠ d` in the pencil of `a,b` ⇒ the pencil of `c,d` is the pencil of
   `a,b` (Bachmann § 4, "Transitivitätssatz"; uses the lemma of the nine lines);
5. theorem of Pappus-Brianchon for lines of two pencils (statement in 3.2 (P)).
Items 1-3 are proved in this study. Items 4 and 5 are quoted from Bachmann § 4 and were NOT
re-derived here (risk R1). They are statements inside the group calculus with short proofs in the
source (each about one page); the Lean size is dominated by the degenerate cases (coinciding lines,
lines of both pencils).

### S4. Half-rotations and the contraction group at `O` (about 4 500 lines)

Definitions: half-rotation and contraction `D_{u,v}` on points and on lines (3.1).
Theorems: (C1)-(C4) of 3.1, the transitivity lemma of 3.1 (proved here), the action on pencils, the
group `H` of fractions, its commutativity, compatibility with the motions fixing `O`.
Source for (C1)-(C4): Bachmann § 6 (the theorems on "Halbdrehungen"); not re-derived here (R1).
The core is one theorem: "the half-rotation maps the points of a line into the points of a line and
the lines of a pencil into the lines of a pencil", which rests on the Lotensatz and on S3.4.
Risk: HIGH for the estimate (this is the least reconstructed part), medium for feasibility (it is
textbook mathematics valid for all metric planes, in particular all Hilbert planes).

### S5. The affine plane `A_O` (about 3 000 lines)

Types `AO.Pt`, `AO.Ln` (in `Type`), `HasLines AO.Pt AO.Ln`, the embedding `ι : P → AO.Pt`
(injective, collinear ⇔ collinear, real lines = traces), `PlaneParallels AO.Pt AO.Ln`
(I 1, I 2, I 7, three non-collinear points, existence and uniqueness of parallels), every line has
at least three points, every line through `ι O` is real, parallel = `∥_O` on real lines, the action
of `H` (dilatations with centre `O`, transitive, commutative) and of the motions fixing `O`
(collineations), "every finite configuration can be made real".
Recommended construction: fractions (3.1), because join and meet reduce to common denominators and
no ideal line has to be defined as a set of pencils; the meet of two non-parallel lines is (C4).
Risk: medium (quotient types in Lean; choose `Quotient` over a setoid on `P × Contraction`).

### S6. Desargues and Pascal in `A_O` (about 3 000 lines)

`DesarguesII AO.Pt` and `PascalTheorem AO.Pt` (the repository's definitions,
`DesarguesAlgebraAux.lean`, `NonPascalAux2.lean`).
Route: (i) Brianchon in `A_O` for nine lines: shrink to real lines, apply S3.5, where "concurrent or
parallel" is "in a pencil"; (ii) Pappus from Brianchon (duality, in the projective closure, or
directly in the affine form needed); (iii) one non-trivial translation from Pappus with parallel
carriers; (iv) Lemma 3.2. Fallback for (iii)-(iv): Hessenberg's theorem (Pappus ⇒ Desargues) in
its affine form, estimated 1 500 lines more.
Risk: medium-high. (i) needs the dictionary "three lines of `A_O` concurrent or pairwise parallel
⇔ after shrinking, in a pencil" including the degenerate positions; (iii) is classical but I have
not written out the proof.

### S7. Coordinates (about 1 300 lines, plus a refactor)

Apply `DesarguesAlgebra*.lean` to `A_O`: `DesAlg.Seg F` is a division ring (`instDivisionRing`),
`coords_bijective`, `theorem34` and `theorem34_converse` (lines = solution sets of left-linear
equations), `pascal_iff_commutative` (commutativity from `PascalTheorem`), giving a `Field` and
`κ : P → F × F` with collinear ⇔ the 3×3 determinant vanishes.
OBSTACLE: these theorems are stated under `[HasBetween P] [LineOrder P L] [PlaneParallels P L]
[Nonempty L]`, and `A_O` has no betweenness before it has coordinates. The order is used only for
"a point off two given lines" (`DesAlg.exists_off_two`, `DesarguesAlgebraAux.lean` line 292; the
module docstrings say so). Required refactor: introduce a `Prop` class (say `DesAlg.ThreePoints P L`:
every line has three distinct points), an instance from `LineOrder`, and replace the instance
arguments in `DesarguesAlgebraAux.lean` … `Aux7.lean`, `NonPascalAux2.lean` (the parts used by
`instDivisionRing`, `th34_line`, `th34_converse`, `coords_bijective_nd`, `pascal_iff_law12`).
The house rule "a result assumes exactly the axioms Hilbert uses, or fewer" is respected (fewer).
Alternative without touching existing files: copy the roughly 3 500 lines needed. The refactor is
recommended; it must be planned as its own blueprint step with a compile of all dependants.
Then: collinearity in `Coord F 2` versus the equation `a x + b y + c = 0` (`CoordLine`,
`AnalyticAux.lean`: `mem_line_iff`, `mem_through_iff`, `collinear_of_mathlib`).
Risk: medium (refactor of files that other units import; `Seg F` has left-sided equations, which is
harmless once commutativity is known).

### S8. `F` is Pythagorean and semireal; choice of the order (about 1 200 lines)

Section 3.3. Needs from S5: the reflections in lines through `O` act on `A_O`; from S7: the vector
structure of the repository (`DesarguesAlgebraAux2.lean`: `Vec F`, `basisEE'`, `mem_ln_iff_smul`).
Output: `IsSemireal F`, then `IsSemireal.exists_linearOrder` (Tau Ceti), then `IsPythagorean F`.
Risk: low-medium (linearity of a collineation fixing a line pointwise, in the repository's API).

### S9. Change of chart and the three clauses (about 700 lines)

Section 3.4, in `Coord F 2`: `ψ`, injectivity, determinant identity, parallel images.
Risk: low (field identities; `field_simp`, `linear_combination`).

## 5. Dependency graph

    S1 motions/reflections ──► S2 reflection calculus ──► S3 pencils, Lotensatz, transitivity,
                                                              Pappus-Brianchon
                                   │                               │
                                   └──────────► S4 half-rotations, contractions (C1)-(C4), H ◄──┘
                                                              │
                                                              ▼
                                                  S5 affine plane A_O, ι, actions of H and of
                                                     the motions fixing O
                                                              │
                              S3.5 ──────────────────────────► S6 DesarguesII, PascalTheorem in A_O
                                                              │
        refactor DesAlg (drop LineOrder) ────────────────────► S7 field F, κ : P → F², lines linear
                                                              │
                                      S5 (reflections act) ──► S8 F Pythagorean, semireal, ordered
                                                              │
                                                              ▼
                                         S9 chart change (t to infinity) ──► S0 PseudoGeometryTheorem

## 6. Size

| stage | content | lines | confidence |
|---|---|---|---|
| S0 | assembly | 60 | checked |
| S1 | motions, reflections, feet, midpoints, bisectors | 2 500 | good |
| S2 | reflection calculus, Bachmann § 3 | 2 500 | good |
| S3 | pencils, Lotensatz, transitivity, Pappus-Brianchon | 4 000 | fair |
| S4 | half-rotations, contractions | 4 500 | poor |
| S5 | affine plane `A_O` | 3 000 | fair |
| S6 | Desargues, Pascal in `A_O` | 3 000 | fair |
| S7 | coordinates (+ refactor of about 300 changed lines) | 1 300 | good |
| S8 | Pythagorean, semireal, order | 1 200 | good |
| S9 | chart change | 700 | good |
| | total | about 23 000 | range 18 000 - 32 000 |

For comparison: the whole repository is 71 000 lines; Chapter V (`DesarguesAlgebra*`) is 5 800,
Chapter III (`Pascal*`, `Proportion*`) is 7 800. This unit is the largest single open unit by far.

## 7. Risks and open points

R1 (main). The proofs of S3.4 (transitivity of pencils), S3.5 (Pappus-Brianchon) and S4 (C1)-(C4)
(half-rotations) are known theorems (F. Bachmann, *Aufbau der Geometrie aus dem Spiegelungsbegriff*,
2nd ed. 1973, § 4 and § 6; J. Hjelmslev, Math. Ann. 64 (1907)) but were quoted from memory, not
re-derived, and the source is not in the repository. Their exact statements (in particular which
non-degeneracy hypotheses Pappus-Brianchon carries, and the precise definition of the half-rotation
on lines) must be fixed from the book before the blueprint can be written. If the book cannot be
consulted, these proofs have to be re-derived; this is feasible (they are group identities) but
is research-level reconstruction and may move the estimate by several thousand lines.
R2. S6 (iii): "Pappus with parallel carriers gives a translation" was not written out. Fallback:
affine Hessenberg, +1 500 lines, classical but with many degenerate cases.
R3. S7 refactor touches seven existing files imported by closed units (Chapters V and VI). It is
mechanical, but each file takes minutes to compile on this machine and the chain is long.
R4. S5 quotient construction: collinearity and parallelism after "common denominators" need (C3)
(commutation) everywhere; if (C3) is only available up to a rotation, the fractions design
degrades and the pencil design must be used (+1 500 lines).
R5. The junk values of `AngCong`/`SegCong` on degenerate tuples (repository convention) make the
definition of `Motion` delicate: preserve the relations only on genuine segments and angles.
R6. Size. With R1 unresolved the upper end (32 000) is realistic. This is several weeks of
work at the pace of the closed units; it cannot be shortened by weakening the route, because the
target implies the embedding theorem (section 2).
Not a risk: orderability of the field (3.3), the existence of `P'` (repository), the final clauses
(3.4), universes (`Type` throughout).

## 8. Declarations relied upon (confirmed in the sources)

Repository (`HilbertFoundations/`):
* `Commentary.lean`: `Conclusion.PseudoGeometryTheorem` (namespace `HilbertFoundations.Conclusion`),
  `exists_parallel`, `theorem19_converse_alternate` (section `Neutral`).
* `Basic.lean`: `HasLines`, `Collinear`, `PlaneCongruence`, `PlaneParallels`, `line`, `eq_line`.
* `Analytic.lean`: `planeParallels_coord (K) [DivisionRing K] : PlaneParallels (Coord K 2) (CoordLine K 2)`,
  `planeCongruence_of_isPythagorean (K) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [IsPythagorean K] : PlaneCongruence (Coord K 2) (CoordLine K 2)`.
* `AnalyticAux.lean`: `Coord`, `CoordLine`, `mem_line_iff`, `mem_through_iff`, `collinear_of_mathlib`.
* `AnalyticAux2.lean`: `class IsPythagorean (K) [Field K] [LinearOrder K]`
  (`sqrt_one_add_sq : ∀ x, ∃ y, 0 ≤ y ∧ y ^ 2 = 1 + x ^ 2`), `IsPythagorean.exists_sqrt_sq_add_sq`.
* `DesarguesAlgebraAux.lean`: `DesAlg.ParPts`, `DesarguesII`, `LPar`, `IsDil`, `IsTr`, `tr_eq_of`,
  `IsTr.comp`, `exists_tr`, `exists_cdil`, `exists_off_two` (the only use of the order).
* `DesarguesAlgebraAux2.lean`: `Frame`, `instDivisionRing`; `DesarguesAlgebraAux5.lean`: `th34_line`;
  `DesarguesAlgebraAux7.lean`: `coords_bijective_nd`; `DesarguesAlgebra.lean`: `theorem34`,
  `theorem34_converse`, `coords_bijective`.
* `NonPascalAux2.lean`: `PascalTheorem`; `NonPascal.lean`: `pascal_iff_commutative`.
* `CongruenceAux2.lean`, `CongruenceAux3.lean`: `segCong_add`, `segCong_sub`, `sas`, `asa`, `sss`,
  `supp`, `vertical`, `right_angles`; `CongruenceAux4.lean`: `midpoint_unique`;
  `Constructions.lean`: `problem5`; `ConstructionsAux.lean`: `Perp`.
Tau Ceti (`.lake/packages/TauCeti`, already required by `lakefile.toml`):
* `TauCeti/Algebra/Order/Ring/Ordering/Semireal.lean`:
  `IsSemireal.exists_linearOrder {K} [Field K] [IsSemireal K] : ∃ o : LinearOrder K, letI := o; IsStrictOrderedRing K`.
mathlib (`.lake/packages/mathlib/Mathlib`):
* `Algebra/Ring/Semireal/Defs.lean`: `IsSemireal`, `isSemireal_iff_not_isSumSq_neg_one`.
* No Artin-Schreier theorem and no projective/affine coordinatization in mathlib at this pin
  (searched `Algebra/Order/Ring/Ordering`, `Algebra/Ring`, `FieldTheory/IsRealClosed`).

Compile status of the scratch check: `python .lake-local/leanc.py .lake-local/scratch/pseudo-study/Final.lean` ends with `[OK]`.
The theorem `pseudoGeometry_of_coord` (stage S0) is proved there without `sorry`; the only `sorry` of the file is the
placeholder `IsSemireal K` in the second example, which checks that `IsSemireal.exists_linearOrder` has the form used in S8.
