# Resume notes: the open units

These notes are for whoever continues the formalizations of two books, on any machine. They are
kept on the branch `wip/open-units` of this repository (`hilbert-foundations-lean`), which is not to
be merged into `main`. Paths are relative to the root of this repository unless they say otherwise.

The two repositories:

- `ishan-1729/galois-oeuvres-lean`: Galois, *Œuvres mathématiques* (1897).
- `ishan-1729/hilbert-foundations-lean`: Hilbert, *The Foundations of Geometry* (Townsend, 1902).

Both use Lean `v4.36.0` and mathlib `v4.36.0` (pinned by `lean-toolchain` and `lake-manifest.json`).

## 1. Where things stand

### Galois repository

`main` is at `b1999a7` ("Prove Galois's claim that PSL(2, p) has no subgroup of index p for
p > 11, and refute and correct his converse on primitive equations of degree p^ν"). Its CI run on
the temporary branch with the same commit succeeded (run 46021617995). Nothing is open any more:
229 units, of which 118 `proved`, 54 `proved (reading)`, 34 `proved (corrected)`, 10 `definition`,
13 `remark`; no `sorry`, only the standard axioms (`scripts/AxiomsAudit.lean`: 1,148 declarations
checked). The two units closed last are `lettre.impossible_au_dela` and `nombres.reciproque`
(section 3). The plans that were used for them are in `resume/plans/galois/`, for reference.

### Hilbert repository

`main` is at `3a635a3` ("Prove Theorem 44 for any number of parameters from Artin's theorem for
the finitely generated subfields of the reals"). Its CI run on the temporary branch with the same
commit succeeded (run 46023602071: `lake build`, the axiom audit with 6,147 declarations checked,
`scripts/ClosingProofs.lean`, the unit map). Counts: 430 units, of which 191 `proved`,
41 `proved (reading)`, 22 `proved (corrected)`, 106 `definition`, 60 `remark` and
10 `stated (open here)`. All of Theorems 1–44 are closed. The unit closed last is `th.44`
(section 3).

This branch, `wip/open-units`, is `main` plus the skeleton of the angle-sum proof (section 2.1)
and this directory. It is not to be merged: the skeleton files contain `sorry`.

The ten open units (status `stated (open here)`). Each is a `Prop`-valued definition; none is
assumed anywhere. All are in the namespace `HilbertFoundations`.

| unit | open statement (Lean name) | file |
|---|---|---|
| `concl.angle_sum` | `Conclusion.AngleSumTheorem` | `HilbertFoundations/Commentary.lean` (block at l. 576, def at l. 716) |
| `concl.pseudo_geometry` | `Conclusion.PseudoGeometryTheorem` | `HilbertFoundations/Commentary.lean` (block l. 532, def l. 562) |
| `app.main_theorem` | `Appendix.AppendixMainTheoremNonempty` (the real target) | `HilbertFoundations/CommentaryCloseAux7.lean` l. 71; the printed form `Appendix.AppendixMainTheorem` (`Commentary.lean` l. 1952) is false for the empty plane, `not_appendixMainTheorem` (`CommentaryCloseAux7.lean` l. 62) |
| `app.two_fixed_points` | `Appendix.TwoFixedPointsIdentity` | `Commentary.lean` l. 2242 |
| `app.transitive` | `Appendix.DisplacementsTransitive` | `Commentary.lean` l. 2298 |
| `app.middle` | `Appendix.AtMostOneMiddle` | `Commentary.lean` l. 2339 |
| `app.rotation_group` | `Appendix.RotationsOfTrueCircle` | `Commentary.lean` l. 2124 |
| `app.true_circle_jordan` | `Appendix.TrueCirclesAreJordan` | `Commentary.lean` l. 2048 |
| `app.true_line` | `Appendix.TrueLineIsCurve` and `Appendix.TrueLinesMeetAtMostOnce` | `Commentary.lean` l. 2434, 2439 |
| `app.invariant_subgroup` | `Appendix.AppendixEuclideanTheorem` | `Commentary.lean` l. 1986 |

Line numbers are those of `main` at the time of writing. Reductions already proved (in
`CommentaryCloseAux7.lean`): `steps_of_main` and the `…_of_main` lemmas derive
`TwoFixedPointsIdentity`, `DisplacementsTransitive`, `AtMostOneMiddle` and `RotationsOfTrueCircle`
from `AppendixMainTheoremNonempty`; `atMostOneMiddle_of_twoFixedPoints`. They point the wrong way
for a proof (in Hilbert's memoir these statements are steps towards the main theorem), but they
are correct and may be used as checks.

## 2. The open units, one by one

### 2.1 `concl.angle_sum` (Dehn's theorem on the angle sum)

**Plan.** `resume/plans/hilbert-angle-sum/BLUEPRINT.md` (about 2,500 lines), reviewed by two
critiques next to it (`CRITIQUE-math.md`, `CRITIQUE-lean.md`; all their points were accepted and
worked into the blueprint, see its last section). Route: Saccheri and Lambert quadrilaterals, after
Hartshorne, *Geometry: Euclid and Beyond*, § 34, with one simplification: the passage from a
triangle to its Saccheri quadrilateral uses the half-turns about the midpoints of `CA` and `CB`, so
that no case distinction on the foot of the altitude is needed. No parallels, no Archimedes, no
continuity. The target is true as formalized. Estimate: about 5,100 lines of Lean (4,800–5,400)
in 17 files, `HilbertFoundations/AngleSumCloseAux1.lean` … `AngleSumCloseAux14.lean` with the two
split files `Aux8b`, `Aux12b`, and `AngleSumClose.lean`, which proves
`Conclusion.angleSumTheorem : AngleSumTheorem`. Stages (blueprint § 3 and § 4.15): 0 plane tools
and isometries (Aux1); A order of angles (Aux2); B addition of angles, types of angles (Aux3,
Aux4); C comparison of segments, perpendiculars (Aux5); D exterior angle, quadrilaterals with two
right angles, Saccheri quadrilaterals (Aux6, Aux7); E the outside lemma (Aux8, Aux8b); F Lambert
quadrilaterals, all Saccheri quadrilaterals have the same type (Aux9, Aux10); G triangles (Aux11,
Aux12, Aux12b, Aux13, Aux14); H conclusion (`AngleSumClose.lean`). Two scratch files that were
type-checked while the plan was written are kept next to it (`tested_scratch_T3.lean`,
`tested_scratch_K3.lean`; they refer to their original location `.lake-local/scratch/…`, which
does not exist on another machine).

**Skeleton (on this branch).** Statements with `sorry` proofs, in a single chain of imports
(`Aux1` imports `HilbertFoundations.PascalAux2`, each later file the previous one, `Aux9` imports
`Aux8b`). They are not imported by the root module `HilbertFoundations.lean`, so `lake build` does
not build them. "Compiled" means that an `.olean` newer than the source existed on the machine
where the work was done.

| file | lines | `sorry` | declarations | compiled |
|---|---|---|---|---|
| `AngleSumCloseAux1.lean` | 176 | 11 | 26 | yes |
| `AngleSumCloseAux2.lean` | 105 | 14 | 14 | yes |
| `AngleSumCloseAux3.lean` | 117 | 8 | 15 | yes |
| `AngleSumCloseAux4.lean` | 75 | 8 | 8 | yes |
| `AngleSumCloseAux5.lean` | 122 | 14 | 16 | yes |
| `AngleSumCloseAux6.lean` | 114 | 9 | 13 | yes |
| `AngleSumCloseAux7.lean` | 44 | 2 | 2 | yes |
| `AngleSumCloseAux8.lean` | 154 | 4 | 7 | yes |
| `AngleSumCloseAux8b.lean` | 57 | 3 | 4 | yes |
| `AngleSumCloseAux9.lean` | 66 | 5 | 6 | yes |
| `AngleSumCloseAux10.lean` | 74 | 7 | 7 | yes |
| `AngleSumCloseAux11.lean` | 80 | 3 | 4 | yes |
| `AngleSumCloseAux12.lean` | 98 | 6 | 7 | yes |
| `AngleSumCloseAux12b.lean` | 64 | 5 | 5 | no |

`AngleSumCloseAux12b.lean` was written last and never compiled; `AngleSumCloseAux13.lean`,
`AngleSumCloseAux14.lean` and `AngleSumClose.lean` are not yet created.

**Next steps.**
1. Compile `AngleSumCloseAux12b.lean` and fix its statements against blueprint § 4.12b.
2. Write the statements of `Aux13` (G4, `triConf_canon`, G6), `Aux14` (G7, G8, `tri_saccheri`)
   and `AngleSumClose.lean` (blueprint § 4.13, § 4.13b, § 4.14). The final step was already
   type-checked from the two stubs `tri_saccheri` and `saccheri_sameType` (blueprint R12).
3. Fill the proofs file by file in the order of the imports. Stages 0–C have no geometric risk;
   the delicate files are Aux8, Aux8b, Aux12, Aux12b (long lists of side-of-a-line facts) and
   Aux13 (G6). Split a file at a lemma boundary into `…b.lean` if it exceeds about 400 lines
   (Aux5, Aux6, Aux9 are at the limit).
4. Wire the unit: import `AngleSumClose` in `HilbertFoundations.lean`, rewrite the Lean reading
   and the status of `concl.angle_sum` in `Commentary.lean` (comments only), add the `example` to
   `scripts/ClosingProofs.lean`, update the counts (section 4 below).

**Risks (blueprint § 6, summarized).**
- R1: the one-point geometry satisfies `PlaneCongruence` and has `IsTriangle X X X`; the target is
  still true (each predicate contains a `Between`, false there), but nearly every lemma needs the
  hypothesis `hl : ∀ X : P, ∃ l : L, X ∈ l` (every point lies on a line). Do not try to remove it.
- R2: the first alternative of `AngleSumGtTwoRight` (`Y ∉ Interior X C B`) never holds; the three
  predicates are exclusive and exhaustive, so the target says what it should.
- R3: the outside lemma (Stage E, E2/E3) is the mathematical heart. It was reconstructed from
  memory of Hartshorne, Prop. 34.4, re-derived, checked by hand and independently by a reviewer,
  and tested numerically on 3,000 random hyperbolic configurations; the numerical tests cover the
  acute case only, the obtuse branch rests on the hand proof alone.
- R4: the triangle configuration of Stage G (G3, the structure `TriConf`, nine items) is new, not
  from a book; checked by hand and by a reviewer, tested on 4,000 hyperbolic triangles (acute case
  only). If an item fails in some configuration, the item is wrong: do not patch it with a case
  split without understanding why.
- R5: `angLt_add` (B1) calls `theorem14` with ten hypotheses; the orientation of every `AngCong`
  matters (bookkeeping).
- R6: orientation conventions: `AngLt A O B A' O' B'` compares with the sub-angle adjacent to the
  first arm `O'A'`; `LtSupp A O B` extends the first arm; `RightAng A O B` has its supplement
  along the second arm. The most likely source of friction.
- R7: lines given by two points versus quantified lines (`eq_line`, `line_unique`,
  `mem_interior_iff`).
- R8: the isometries of `PascalAux1.lean`, `PascalAux2.lean` (namespace `Pas`) are usable under
  `PlaneCongruence` alone (checked by compiling).
- R10: size, ±30 %. R12 lists exactly what the type-checker confirmed while planning; everything
  else (in particular B1, D3–D6, the bodies of E, F, G) is design, not checked code.
- R14: structures with `Pas.ht` fields (`MidConf`) must be declared in a section that has the
  instance `[PlaneCongruence P L]`.
- Blueprint § 4.16 has implementation notes for the hard spots (rewriting under isometries: keep
  `Pas.refl m` explicit, do not `set` it).

### 2.2 `concl.pseudo_geometry` (Dehn's pseudo-geometry)

Only a study exists: `resume/plans/hilbert-pseudo-geometry/STUDY.md`. No Lean files.

**Verdict.** The statement is true and not degenerate. There is no cheap route: any `φ` as in the
statement makes the points off `t` part of a plane with parallels over a commutative ordered
field, so the statement contains "every Hilbert plane is locally Pappian and Desarguesian with an
orderable coordinate field" (the Hjelmslev–Bachmann–Pejas embedding theorem). Estimate about
23,000 lines (range 18,000–32,000; the study's first paragraph says 24,000).

**Recommended route** (classical, with three simplifications): reflections → three-reflections
theorem → pencils → half-rotations → affine plane of ideal points → Pappus / Desargues →
coordinates → the field is Pythagorean and semireal → Cartesian plane. The simplifications:
(1) work in the affine chart `A_O` whose line at infinity is the polar of a real point `O ∉ t`;
(2) the coordinate field is Pythagorean with `-1` not a square, hence semireal, hence orderable
(`IsSemireal.exists_linearOrder`, Tau Ceti): the order of the plane is never transported to ideal
points; (3) move `t` to infinity at the end by an explicit change of chart in coordinates.

**Stages** (study § 4, § 6): S0 final assembly (60 lines, scratch-checked); S1 motions and
reflections of a Hilbert plane (2,500); S2 the reflection calculus as an abstract interface,
Bachmann § 3 (2,500); S3 pencils, Lotensatz, transitivity, Pappus–Brianchon (4,000); S4
half-rotations and the contraction group at `O` (4,500, least reconstructed); S5 the affine plane
`A_O` (3,000); S6 Desargues and Pascal in `A_O` (3,000); S7 coordinates through the existing
`DesarguesAlgebra*.lean`, after a refactor that replaces the `LineOrder` assumption by a
three-points class (1,300 + about 300 changed lines); S8 the field is Pythagorean and semireal
(1,200); S9 change of chart and the three clauses (700).

**Open points R1–R6** (study § 7). R1 (main): the transitivity of pencils (S3.4), the theorem of
Pappus–Brianchon (S3.5) and the theory of half-rotations (S4, (C1)–(C4)) were quoted from memory
of Bachmann, *Aufbau der Geometrie aus dem Spiegelungsbegriff*, § 4 and § 6, and Hjelmslev
(1907), not re-derived; their exact statements and non-degeneracy hypotheses must be fixed from a
source. R2: "Pappus with parallel carriers gives a translation" (S6 (iii)) was not written out;
fallback affine Hessenberg, +1,500 lines. R3: the S7 refactor touches seven existing files that
closed units import. R4: if the commutation (C3) holds only up to a rotation, the fractions design
of `A_O` fails and a pencil design is needed (+1,500). R5: the junk values of `AngCong`/`SegCong`
on degenerate tuples make the definition of a motion delicate. R6: size; with R1 unresolved the
upper end is realistic.

**Source.** J. Hjelmslev, "Neue Begründung der ebenen Geometrie", *Math. Ann.* 64 (1907),
is public domain and is the source for the lemmas the study could not reconstruct (R1).
Its OCR text is `resume/sources/Hjelmslev-1907.txt` (section 7 says how to fetch it again). A
section-by-section reconstruction of it was started but not finished: its directory
(`plans/sources/` in the working directory where the work was done) was created but no file was
written into it, so nothing of it is here. The next step is to write that
reconstruction (statements and proofs of the pencil and half-rotation theorems in Hjelmslev's
form), then turn the study into a blueprint.

### 2.3 The Appendix (eight units)

Only a study exists: `resume/plans/hilbert-appendix/STUDY.md`. No Lean files.

**Grouping** (study § 0):
- G1, five units, need only the "circle part" of Hilbert's memoir (§§ 1–22), stages 1–5:
  `TwoFixedPointsIdentity`, `AtMostOneMiddle`, `RotationsOfTrueCircle`, `TrueCirclesAreJordan`,
  `DisplacementsTransitive`; 10,000–15,000 lines.
- G2, two more, need also the line theory (§§ 23–40), stage 6: `TrueLineIsCurve`,
  `TrueLinesMeetAtMostOnce` (the unit `app.true_line`); +5,000–8,000.
- G3, `AppendixMainTheoremNonempty` and `AppendixEuclideanTheorem` (units `app.main_theorem`,
  `app.invariant_subgroup`), need the classification (stages 7, 8) and the simplicity of
  `PSL(2, ℝ)` (stage 9); +12,000–19,000. The hyperbolic branch (stage 8) is not designed.

Total 27,000–42,000 lines, central estimate about 34,000.

**Stages** (study § 14): 9 (do first) `PSL(2, ℝ)` and the disc group, giving
`appendixEuclideanTheorem_of_main` (900–1,300, low risk; mathlib has
`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'`); 1 elementary consequences of I–III
(800–1,100, low); 2 winding numbers (1,600–2,300, low–medium); 3 plane topology toolkit
(2,200–3,200, medium: volume, not depth); 4 one true circle near `M` is a closed Jordan curve
(3,000–4,400, medium–high; a new argument with winding numbers and Haar measure replaces Hilbert's
§§ 4–8 and 13–18); 5 all true circles, `K_M ≅ ℝ/ℤ`, the five units of G1 (2,600–3,900, medium);
6 half-rotations, middles, tangent true circles, true lines (5,000–8,000, high); 7 reduction and
the euclidean branch (2,000–3,000, medium); 8 the hyperbolic branch (9,000–15,000, very high, not
worked out). Recommended order: 9, then 1–5 (closes five units), then decide on 6, then a separate
study of 8.

**Statement audit** (study § 2). Only `AppendixMainTheorem` is false (the empty plane); the target
is `AppendixMainTheoremNonempty`. Traps: `IsPlane` does not ask for simple connectedness
(`ℂ ∖ {0}` is a plane), so never use "the inside of a Jordan curve of `S` lies in `S`" without
proof; until stage 5 every such argument must stay inside a number disc contained in `S`.
`IsEuclideanGeometry` and `IsHyperbolicGeometry` only give a bijection `φ`, not a homeomorphism,
so `TrueCirclesAreJordan` and `TrueLineIsCurve` cannot be derived from the main theorem as a black
box; they must be proved on the way to it. `SensePreserving` is used exactly as stated (it
excludes reflections, without it `TwoFixedPointsIdentity` would be false).

**Main risks** (study § 14): stage 8 is not designed; the tangent true circles of stage 6
(§§ 27–29) are not reconstructed; the new argument of stage 4 was checked by hand only; the source
was read only as a paraphrase, so section numbers and details of §§ 23–42 must be re-checked
against the scan.

**Sources and unfinished work.** Hilbert's memoir is Anhang IV of the 2nd edition of the
*Grundlagen der Geometrie* (Teubner, 1903, public domain), and the hyperbolic case rests on
Anhang III ("Neue Begründung der Bolyai-Lobatschefskyschen Geometrie"). Their OCR texts are
`resume/sources/Anhang-IV.txt` and `resume/sources/Anhang-III.txt`. Plans for stages 1, 2, 3 and 9
and reconstructions of Anhang IV and Anhang III from the scan were started but not finished: in
the working directory where the work was done the directories `plans/appendix-s2-winding/`,
`plans/appendix-s3-topology/`, `plans/appendix-s9-invariant/` and `plans/sources/` were created,
but no file was written into any of them (there was none for stage 1), so nothing of them is here.
Next step: stage 9 (small and independent), then a blueprint for stages 1–3, with the German text
of Anhang IV read directly from `resume/sources/Anhang-IV.txt`.

## 3. How the units closed in this round were proved (models)

**Galois, `lettre.impossible_au_dela`** (`GaloisOeuvres/LettreChevalierClose.lean`, with
`LettreChevalierCloseAux1.lean` (the arithmetic), `…Aux2.lean` (a counting theorem for finite
groups), `…Aux3.lean` (centralizers in `SL(2, F)`); theorem
`GaloisOeuvres.LettreChevalier.abaissement_impossible : AbaissementImpossible`): for a prime
`p > 11`, `PSL(2, p)` has no subgroup of index `p`. No use of Dickson's classification. If `H`
has index `p`, its order `h = (p + 1)(p − 1)/2` is prime to `p` and greater than 60, so no
non-central element of its preimage `K` in `SL(2, p)` has trace `±2`; the centralizers of these
elements partition `K` minus the centre, each has index at most 2 in its normalizer, and counting
the elements of `K` over their conjugacy classes gives an equation in natural numbers with no
solution for `h > 60` (`no_class_equation`, `no_subgroup_index_p`). Plan:
`resume/plans/galois/galois-psl-index/`.

**Galois, `nombres.reciproque`** (`GaloisOeuvres/TheorieNombresClose.lean`, with
`TheorieNombresCloseAux1.lean` and `…Aux2.lean`; status `proved (corrected)`): Galois's converse
(a solvable primitive equation of degree `p^ν`, `p^ν ≠ 9, 25`, has its group among the
substitutions `k ↦ (ak + b)^(p^r)`) is false for every prime `p` (`not_reciproqueGalois`). The
counterexample is `AGL(1, p²) ≀ C₂` acting on the `p⁴` points of `F × F`, `|F| = p²`: primitive
and solvable (`Couronne.couronne_primitif`, `Couronne.couronne_soluble`, Aux2), of order a
multiple of `2(p² − 1)²`, which does not divide `p⁴(p⁴ − 1)·4` (`Couronne.arith`). It is the group
of an equation: Aux1 proves that every transitive permutation group of finitely many letters is
the group of an irreducible equation over the field of rational functions of the letters invariant
under the group (`Realisation.equation`, `Realisation.galActionHom_racine`). The corrected
statement `reciproque_corrigee` (Jordan's form): the group consists of affine substitutions
`k ↦ A k + b` of the `ℤ/p`-vector space of the imaginaries and contains the translations. Plan:
`resume/plans/galois/galois-reciproque/` (with reference copies of the three files).

**Hilbert, `th.44`** (`HilbertFoundations/Theorem44Close.lean`, with `Theorem44CloseAux1.lean`
and `Theorem44CloseAux2.lean`; `theorem44 : Theorem44`). Hilbert's reduction
(`theorem44_of_theorem43For`, `ConstructionsAux10.lean`) applied to
`theorem43For_closure : Theorem43For ℚ(S)` for every finite `S ⊆ ℝ`, Artin's theorem for the
finitely generated subfields of `ℝ`. A number `g` that is not a sum of squares is negative in some
ordering (`Hilbert17.RingPreordering.isSumSq_iff_nonneg_all_orders`, copied library `Hilbert17/`);
in a real closure `L` of that ordering (Tau Ceti, `TauCeti.RealClosure.exists_realClosure`)
`−g = w²`; the field `K` generated by `S` and `w` is finite over `ℚ(t)` for a transcendence basis
`t`; a primitive element gives a polynomial with rational coefficients with a simple zero; the
transfer of sign conditions between real closed fields (`Hilbert17Transfer.exists_matching_signs_eval₂`)
gives a simple real zero, which persists near a point with algebraically independent coordinates
(`exists_root_near`, `exists_algebraicIndependent_near`); this gives an embedding `K → ℝ`
(`nonempty_ringHom_real`) under which `g < 0` (`exists_ringHom_real_neg`). Only the Artin–Lang step
is this project's; `docs/FAITHFULNESS.md` and `docs/SOURCES.md` say what is taken from where. Plan:
`resume/plans/hilbert-th44/` (with reference copies of the three files).

The pattern in all three: the chapter file keeps the unit block and the `Prop`; a separate
`…Close.lean` file (with `…CloseAux*.lean` helpers) proves it; only comments and the status change
in the chapter file.

## 4. Conventions to follow

Read `README.md`, `docs/FAITHFULNESS.md` ("Units", "Statuses", "House rules", "Third-party
code"), `scripts/unit_table.py`, `scripts/ClosingProofs.lean`, `scripts/AxiomsAudit.lean` and
`.github/workflows/ci.yml` of each repository. In short:

- **Units.** Every statement of the book is a unit: a comment block `## [id] Title`, the quotation,
  `**Lean reading.**`, and `**Status.**` followed by exactly one status string and nothing after
  it. Hilbert: `proved`, `proved (reading)`, `proved (corrected)`, `definition`, `remark`,
  `stated (open here)`. Galois uses the same strings (the vocabulary is in
  `GaloisOeuvres/Basic.lean`). The declarations of a unit follow its block.
- **A unit proved in another file.** The chapter file keeps the block and the `Prop` (`def … :
  Prop`); the proof goes into a new `…Close.lean` (helpers `…CloseAux<n>.lean`) imported by the root
  module (`HilbertFoundations.lean` / `GaloisOeuvres.lean`). Then: change the status line and the
  Lean reading of the unit (comments only; check with `resume/tools/strip_cmp.py`, which compares a
  file with `HEAD` after removing comments), and in the Hilbert repository add
  `example : TheProp := theTheorem` to `scripts/ClosingProofs.lean`.
- **No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe` on `main`.**
  `scripts/AxiomsAudit.lean` fails if a declaration of the project's namespace depends on anything
  but `propext`, `Classical.choice`, `Quot.sound`. An open unit is a `def … : Prop`, never a
  theorem with an incomplete proof. `sorry` is allowed only on the `wip/…` branch, in files the
  root module does not import.
- **`docs/UNITS.md` is generated** by `python scripts/unit_table.py`; never edit it by hand.
  `--check` must pass, and CI fails if the file is stale.
- **Counts by hand.** When a status changes, update the status table and the sentences with counts
  in `README.md` and `docs/FAITHFULNESS.md` (Hilbert: the totals, the table by part of the book,
  the number of helper modules and closing files, the section "What is not proved" / "Stated, open
  here", the lists of third-party uses), and the root module's docstring.
- **Lines of at most 100 characters** in new Lean files (quotations of the book in the unit blocks
  are exempt); **every declaration has a docstring**; new files start with a module docstring that
  says what they prove.
- **Commits**: plain, factual messages in the style of `git log`.
- **A change reaches `main` only after CI passed** on a temporary branch with the same commit;
  then fast-forward `main` (`git merge --ff-only`), push, and delete the temporary branch. Never
  force-push.

## 5. Setting up on another machine

```
git clone https://github.com/ishan-1729/hilbert-foundations-lean
git clone https://github.com/ishan-1729/galois-oeuvres-lean
cd hilbert-foundations-lean
git checkout wip/open-units
```

Install `elan`; the toolchain is selected by `lean-toolchain` (`leanprover/lean4:v4.36.0`). Then,
in each repository:

```
lake exe cache get   # mathlib's compiled files
lake build           # the project
```

On a normal machine this is the right way. In the Hilbert repository the first `lake build` also
compiles from source about 1,100 modules of Tau Ceti and the 18 modules of `Hilbert17/`, of the
order of 45 minutes; later builds reuse them. (On the machine where this work was done these two
commands were not used because it is short of memory; that restriction does not apply elsewhere.)

To check one file: `lake env lean HilbertFoundations/File.lean`. The helper scripts used here are in
`resume/tools/`; copy them to `.lake-local/` (git-ignored) to use them:

- `leanc.py <File.lean> [--olean]` runs `lean` on one file with the environment of `lake env`
  (cached in `.lake-local/lake_env.json` for 6 hours) and the project options `autoImplicit=false`,
  `pp.unicode.fun=true`; with `--olean` it also writes `.lake/build/lib/lean/<Module>.olean` and
  `.ilean`, so that later files can import the module without `lake build`. It takes a slot of a
  machine-wide lock (at most 3 Lean processes, through `scripts/check.py`), retries transient
  "failed to read file" errors, and prints `[OK]` or `[FAIL]`. It expects a built `.lake` (mathlib,
  Tau Ceti and the imported project modules already compiled); imports must be compiled first.
- `strip_cmp.py <files…>` compares each file with its version at `HEAD` after removing comments and
  white space: `OK` means that only comments changed.
- `tc_modules.py <TauCeti.Module …>` runs one `lake build` of the given Tau Ceti modules with
  Lake's artifact cache settings (it expects a file `.lake-local/lake-cache.toml`, which is not in
  this directory); on a normal machine `lake build` makes it unnecessary.

**Working on the skeleton.** Compile in the order of the imports: `lake build
HilbertFoundations.PascalAux2 HilbertFoundations.Commentary`, then each `AngleSumCloseAux<n>` in
turn (for instance `lake env lean -o .lake/build/lib/lean/HilbertFoundations/AngleSumCloseAux1.olean
HilbertFoundations/AngleSumCloseAux1.lean`, or `lake build HilbertFoundations.AngleSumCloseAux1`,
which works for any module even though the root does not import it). When a file is free of
`sorry`, it stays on the branch until the whole chain is; only then is `AngleSumClose` imported in
the root module, the unit wired (section 2.1, step 4), and the work moved to `main` through a
temporary branch and CI.

## 6. Pitfalls met so far

- **Degenerate geometries.** The one-point geometry satisfies `PlaneCongruence` (no lines at all),
  so many lemmas need `hl : ∀ X, ∃ l, X ∈ l`; the empty plane makes `AppendixMainTheorem` false.
  Check every new statement against the degenerate models before proving it.
- **Junk values.** `AngCong` and `SegCong` on degenerate tuples (equal points) have unintended
  values; a definition of "motion" must ask for preservation only on genuine segments and angles.
- **Orientation conventions** of the angle predicates (which arm first, which arm is extended); see
  2.1, R6. Use the `…_swap` lemmas instead of re-proving.
- **The Appendix plane need not be simply connected**, and its main theorem only gives a bijection.
- **`import Mathlib`** in a new file is accepted (both `Basic.lean` files do it), but importing
  only what is needed keeps the compile time down.
- **Header comments inside `Hilbert17/*.lean`** are the upstream author's and are not to be
  edited (their status is explained in `Hilbert17/README.md`); the same holds for `JordanPick/`.
- **Line numbers in the plans** refer to the files at the time of writing; check them.
- **Plans reconstructed from memory.** The pseudo-geometry study (R1) and the Appendix study (read
  from a paraphrase) quote results that were not re-derived; read the sources in `resume/sources/`
  before relying on them.

## 7. Contents of `resume/`

- `resume/README.md`: these notes.
- `resume/plans/galois/galois-psl-index/BLUEPRINT.md`: plan used for `lettre.impossible_au_dela` (finished)
- `resume/plans/galois/galois-psl-index/CRITIQUE-lean.md`
- `resume/plans/galois/galois-psl-index/CRITIQUE-math.md`
- `resume/plans/galois/galois-reciproque/BLUEPRINT.md`: plan used for `nombres.reciproque` (finished; `reference/` holds copies of the three files as they were then)
- `resume/plans/galois/galois-reciproque/CRITIQUE-lean.md`
- `resume/plans/galois/galois-reciproque/CRITIQUE-math.md`
- `resume/plans/galois/galois-reciproque/reference/TheorieNombresClose.lean`
- `resume/plans/galois/galois-reciproque/reference/TheorieNombresCloseAux1.lean`
- `resume/plans/galois/galois-reciproque/reference/TheorieNombresCloseAux2.lean`
- `resume/plans/hilbert-angle-sum/BLUEPRINT.md`: plan for `concl.angle_sum`
- `resume/plans/hilbert-angle-sum/CRITIQUE-lean.md`
- `resume/plans/hilbert-angle-sum/CRITIQUE-math.md`
- `resume/plans/hilbert-angle-sum/tested_scratch_K3.lean`
- `resume/plans/hilbert-angle-sum/tested_scratch_T3.lean`
- `resume/plans/hilbert-appendix/STUDY.md`: study for the eight Appendix units
- `resume/plans/hilbert-pseudo-geometry/STUDY.md`: study for `concl.pseudo_geometry`
- `resume/plans/hilbert-th44/BLUEPRINT.md`: plan used for `th.44` (finished; `ref/` holds copies of the three files as they were then, which may differ from those on `main`)
- `resume/plans/hilbert-th44/CRITIQUE-lean.md`
- `resume/plans/hilbert-th44/CRITIQUE-math.md`
- `resume/plans/hilbert-th44/ref/Theorem44Close.lean`
- `resume/plans/hilbert-th44/ref/Theorem44CloseAux1.lean`
- `resume/plans/hilbert-th44/ref/Theorem44CloseAux2.lean`
- `resume/sources/Anhang-III.txt`
- `resume/sources/Anhang-IV.txt`
- `resume/sources/Hjelmslev-1907.txt`
- `resume/tools/leanc.py`
- `resume/tools/strip_cmp.py`
- `resume/tools/tc_modules.py`


**Sources** (OCR text of public-domain works, kept here because they are small):
- `resume/sources/Anhang-III.txt` and `Anhang-IV.txt`: D. Hilbert, *Grundlagen der Geometrie*,
  2nd ed., Teubner, Leipzig, 1903, Anhang III and Anhang IV; lines 6270–7075 and 7076–9212 of
  the full OCR text.
- `resume/sources/Hjelmslev-1907.txt`: J. Hjelmslev, "Neue Begründung der ebenen Geometrie",
  *Math. Ann.* 64 (1907); lines 32115–33900 of the OCR text of the volume.

The two full-volume files are not copied. To fetch them and cut the excerpts again:

```
mkdir -p .lake-local/src/hilbert1903 .lake-local/src/mathann64
curl -L -o .lake-local/src/hilbert1903/grunddergeovon00hilbrich_djvu.txt \
  https://archive.org/download/grunddergeovon00hilbrich/grunddergeovon00hilbrich_djvu.txt
curl -L -o .lake-local/src/mathann64/sim_mathematische-annalen_1907_64_djvu.txt \
  https://archive.org/download/sim_mathematische-annalen_1907_64/sim_mathematische-annalen_1907_64_djvu.txt
sed -n '6270,7075p' .lake-local/src/hilbert1903/grunddergeovon00hilbrich_djvu.txt > Anhang-III.txt
sed -n '7076,9212p' .lake-local/src/hilbert1903/grunddergeovon00hilbrich_djvu.txt > Anhang-IV.txt
sed -n '32115,33900p' .lake-local/src/mathann64/sim_mathematische-annalen_1907_64_djvu.txt \
  > Hjelmslev-1907.txt
```
