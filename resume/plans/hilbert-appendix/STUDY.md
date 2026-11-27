# STUDY — the eight open units of the Appendix (Hilbert, "Ueber die Grundlagen der Geometrie", Math. Ann. 56)

Scope: `app.main_theorem`, `app.two_fixed_points`, `app.transitive`, `app.middle`, `app.rotation_group`,
`app.true_circle_jordan`, `app.true_line`, `app.invariant_subgroup` of `HilbertFoundations/Commentary.lean`
(namespace `HilbertFoundations.Appendix`, lines 1195–2497), with the partial results of
`CommentaryClose.lean` and `CommentaryCloseAux7.lean`.

This is an architecture and feasibility study, not an implementation blueprint. Where an argument is written
out below it has been checked by hand by the author of the study; where it has not been worked out this is
said explicitly (sections 9 and 11, and the list of risks in section 14). Nothing in the repository was
modified.

---------------------------------------------------------------------------------------------------------

## 0. Verdict in one page

* Only one formal statement is false as formalized: `AppendixMainTheorem` (empty plane; already recorded in
  the repository as `not_appendixMainTheorem`). The other seven statements, and `AppendixMainTheoremNonempty`,
  are true, in the sense that I found no degenerate counterexample and each follows from Hilbert's theorem
  (section 2).
* The eight units do **not** all need the classification. They fall into three groups of very different cost:

  | group | units | what is needed | Lean lines (estimate) |
  |---|---|---|---|
  | G1 | `TwoFixedPointsIdentity`, `AtMostOneMiddle`, `RotationsOfTrueCircle`, `TrueCirclesAreJordan`, `DisplacementsTransitive` | the "circle part" of the memoir (§§ 1–22): stages 1–5 below | 10 000 – 15 000 |
  | G2 | `TrueLineIsCurve`, `TrueLinesMeetAtMostOnce` | G1 + the "line part" (§§ 23–40): stage 6 | + 5 000 – 8 000 |
  | G3 | `AppendixMainTheoremNonempty`, `AppendixEuclideanTheorem` | G1 + G2 + classification (stages 7, 8) + simplicity of PSL(2, ℝ) (stage 9) | + 12 000 – 19 000 |

  Total: **27 000 – 42 000 lines** of new Lean (central estimate about 34 000). For comparison the whole
  repository has 71 000 lines in `HilbertFoundations/`. This is not a "close the remaining units" task; it is
  a project of the size of half the existing development, with genuine mathematical design risk in stage 6
  (tangent true circles) and above all in stage 8 (the hyperbolic case).
* `AppendixEuclideanTheorem` reduces to `AppendixMainTheoremNonempty` at small cost (900–1 300 lines, stage 9):
  mathlib v4.36.0 has the simplicity of `PSL(2, F)`
  (`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'`, confirmed by a scratch compile for `F = ℝ`). This
  reduction can be done first and is checkable at once.
* `TrueCirclesAreJordan` and `TrueLineIsCurve` can **not** be derived from `AppendixMainTheoremNonempty` used as
  a black box (its conclusion only gives a bijection `φ`, not a homeomorphism). In the plan below they are not
  derived from the main theorem at all: they are proved on the way to it (G1, G2).
* No modern proof is cheaper on mathlib v4.36.0 (section 13). The plan follows Hilbert's chain of theorems, but
  replaces his §§ 4–8 and 13–18 (cyclic order by Dedekind cuts, dyadic bisection of angles) by an argument with
  winding numbers and Haar measure that is shorter to formalize and uses the hypothesis `SensePreserving`
  exactly in the form in which it is stated (section 7).

---------------------------------------------------------------------------------------------------------

## 1. Sources

* The memoir itself: I used the reprint as Anhang IV of *Grundlagen der Geometrie*, **2nd edition, Teubner
  1903** (public domain), OCR text at
  `https://archive.org/stream/grunddergeovon00hilbrich/grunddergeovon00hilbrich_djvu.txt` (Anhang IV is
  roughly characters 300 000 – 422 000 of that file, pp. 121–162, §§ 1–42). **Caveat:** the page could only be
  read through a web tool that returned only a paraphrase, not the verbatim text; what I have is a
  section-by-section paraphrase (in places visibly garbled, e.g. wrong cross-references). Section numbers
  quoted below (§ n) refer to that edition. Before stages 6 and 8 are blueprinted, the German text of
  §§ 23–42 and of Anhang III must be read directly from the scan by the blueprint author; I mark every place
  where I rely on the paraphrase.
* Structure of the memoir as obtained: §1 stability of rotations near `M`; §2 covered points, the set `kk`;
  §3 the true circle `ϰ` through a point of `kk` is perfect; §4–5 arcs inside and outside, cyclic order of
  `ϰ`, invariance; §6 no neighbouring points (Axiom III); §7–8 `ϰ` is a closed Jordan curve; §9 `ϰ = kk`, `M`
  inside; §10–12 true circles touching a number circle from inside/outside, every true circle through a point
  near `M` is a Jordan curve around `M`; §13–18 group of the true circle, angle; §19–21 a rotation fixing a
  true circle pointwise is the identity, continuity and period of the rotation formulas; §22 two fixed points,
  transitivity; §23–26 half-rotation, middle, smaller segments have middles; §27–29 tangent true circles;
  §30–37 dyadic points, convergence, the true line; §38–40 no double points, two lines meet at most once, a
  line meets every circle about one of its points, any two points lie on a line; §41 congruence theorems for
  triangles of the same sense; §42 conclusion: the plane axioms of the *Grundlagen* hold with the narrower form
  of the congruence axiom IV 6 (III 5/III 6 in other numberings), and Hilbert **cites two other works** for the
  classification: Anhang II (base angles of the isosceles triangle; euclidean case) and Anhang III ("Neue
  Begründung der Bolyai-Lobatschefskyschen Geometrie", calculus of ends; hyperbolic case).
* The modern literature was used from memory only (section 13).

---------------------------------------------------------------------------------------------------------

## 2. Audit of the formal statements

Definitions (all in `Commentary.lean`): `IsClosedJordanCurve`, `IsJordanRegion`, `IsDomainOf`, `IsPlane`,
`WindsAround`, `SensePreserving`, `IsDisplacement`, `Geometry`, `IsRotationAbout`, `AxiomI`, `AxiomIGroup`,
`AxiomII`, `TrueCircle`, `NearlyBrought`, `AxiomIII`, `IsEuclideanGeometry`, `IsHyperbolicGeometry`,
`HasInvariantSubgroup`, `IsSemiRotation`, `IsMiddle`, `TrueLineGen`, `TrueLine`.

### 2.1 The only defect

**D1. `AppendixMainTheorem` is false.** Counterexample: `emptyGeometry` (`S = ∅`). Already proved in the
repository (`not_appendixMainTheorem`). The target is `AppendixMainTheoremNonempty` (hypothesis `G.S.Nonempty`).
The unit `app.main_theorem` can therefore only be closed in the corrected form.

### 2.2 Things that look dangerous but are not defects

* **Plane with one point.** Not a plane: `IsPlane S` gives every `z ∈ S` a Jordan region `U ⊆ S` with `z ∈ U`,
  and Jordan regions are open (`IsJordanRegion.isOpen`) and nonempty; so a nonempty plane is an **open** subset
  of `ℂ`, and it is **connected** (any two points lie in a common Jordan region, which is a connected
  component). No finite plane except `∅`.
* **`IsPlane` does not ask for simple connectedness** (e.g. `ℂ ∖ {0}` is a plane: two points lie in a thin
  Jordan region avoiding `0`). This does not make the theorem false: the proof shows that for a geometry
  satisfying I–III every closed true disc lies in `S` and `S` is the increasing union of them (stage 5, 8.6).
  But the proof must never use "the inside of a Jordan curve of `S` lies in `S`" without proof. This is a
  recurring trap for implementers.
* **Domains.** `IsDomainOf S U z` does not ask that the bounding curve lie in `S`. Harmless: every disc
  `Metric.ball z r ⊆ S` is a domain (`isJordanRegion_ball`) and every domain of `z` contains such a disc, so
  `NearlyBrought G A B C A' B' C'` is equivalent to: for every `ε > 0` there are `A₁ B₁ C₁` and `f ∈ D` with
  `|A₁ − A|, |B₁ − B|, |C₁ − C|, |f A₁ − A'|, |f B₁ − B'|, |f C₁ − C'| < ε`. Hence the **sequence form of III**
  used everywhere below: if `fₙ ∈ D`, `Aₙ → A`, `Bₙ → B`, `Cₙ → C`, `fₙ Aₙ → A'`, `fₙ Bₙ → B'`, `fₙ Cₙ → C'`
  (all six limits in `S`), then some `f ∈ D` has `f A = A'`, `f B = B'`, `f C = C'`.
* **`SensePreserving`.** It is stated for closed Jordan curves `γ : ℝ → S` and points `p ∈ S` off the curve,
  with `WindsAround (γ − p) n ↔ WindsAround (f ∘ γ − f p) n`. (a) It is not vacuous and not contradictory: a
  winding number always exists and is unique (stage 2). (b) It does exclude reflections (a reflection changes
  `n` into `−n`, and `n ≠ 0` for `p` inside), which is exactly what the proof needs; without it
  `TwoFixedPointsIdentity` would be false (full euclidean group). (c) The proof below uses it only for Jordan
  curves lying in a small disc of `S` and for points `p` of `S`, i.e. literally as stated. (d) That the Möbius
  maps of the disc satisfy it is **not** needed for any of the eight units (the hyperbolic plane never has to
  be exhibited as a `Geometry`); the repository's remark that this is unproved stays true and is outside the
  scope.
* **`HasInvariantSubgroup`** (a subgroup `N ⊆ D`, containing a non-identity element, missing an element of
  `D`, normalized by `D`). For the empty plane it is false (no `f ≠ refl`), so `AppendixEuclideanTheorem` is
  vacuous there. In the hyperbolic case `D ≅ PSL(2, ℝ)` is simple, so the statement is true. No defect.
* **`TrueLine G A B` for arbitrary fundamental points `A ≠ B`.** In a geometry satisfying I–III every pair of
  points has a middle and lies on a true line `ℓ` with a parameter `p : ℝ → ℓ` in which the half-rotation about
  `p a` is `x ↦ 2a − x` (stage 6). If `A = p a`, `B = p b`, the generated set `TrueLineGen G A B` is exactly
  `{p (a + q (b − a)) | q dyadic}` (induction; `semi` gives `2x − y`, `middle` gives `(x + y)/2` by uniqueness
  of the middle; the case `X = Y` of `middle` gives `M = X`), whose closure in `S` is `ℓ`. So
  `TrueLine G A B = ℓ` for **all** `A ≠ B`, and both statements of `app.true_line` are true as formalized.
  (`TrueLineIsCurve` asks only for a continuous injective `γ : ℝ → ℂ` with the right range, not for an
  embedding.)
* **`RotationsOfTrueCircle`, `TrueCirclesAreJordan`, `AtMostOneMiddle`, `TwoFixedPointsIdentity`,
  `DisplacementsTransitive`**: quantified over points, hence vacuous for the empty plane; true otherwise.

### 2.3 A weakness that matters for the architecture (not a falsity)

**W1.** `IsEuclideanGeometry` / `IsHyperbolicGeometry` only ask for a *bijection* `φ`. Therefore
`AppendixMainTheoremNonempty` does not imply `TrueCirclesAreJordan` or `TrueLineIsCurve` by model computations
(the header of `CommentaryCloseAux7.lean` already says so). Hilbert's proof gives a homeomorphism. Two
consequences: (i) G1 and G2 must be proved before, not after, the main theorem (they are steps of its proof
anyway); (ii) the classification stage only has to produce an **abstract** isomorphism of `(D, K_M)` with the
model group and its point stabilizer, which is a real simplification (section 10.1).

---------------------------------------------------------------------------------------------------------

## 3. Logical structure

Already in the repository: `steps_of_main : AppendixMainTheoremNonempty → TwoFixedPointsIdentity ∧
DisplacementsTransitive ∧ AtMostOneMiddle ∧ RotationsOfTrueCircle`, and
`atMostOneMiddle_of_twoFixedPoints`. These reductions are correct but point the wrong way for a proof: in every
known proof the four statements are steps towards the main theorem.

Dependency graph of the plan (→ means "is used for"):

```
 stage 1 (I–III: sequence form, stability, equicontinuity, no collapse)
 stage 2 (winding numbers)      stage 3 (plane topology: arcs, θ-curves, nested Jordan curves)
        \________________________/
 stage 4  one true circle near M is a closed Jordan curve; χ : K_M → ℝ/ℤ, Θ : ϰ ≃ₜ ℝ/ℤ
 stage 5  all true circles near M; K_M ≅ ℝ/ℤ acts freely; global continuity
            → TwoFixedPointsIdentity, AtMostOneMiddle, RotationsOfTrueCircle,
              TrueCirclesAreJordan, DisplacementsTransitive                         [G1]
 stage 6  half-rotations, middles, tangent circles, true lines
            → TrueLineIsCurve, TrueLinesMeetAtMostOnce                               [G2]
 stage 7  euclidean branch      stage 8  hyperbolic branch
            → AppendixMainTheoremNonempty                                            [G3]
 stage 9  PSL(2,ℝ) simple  + main theorem → AppendixEuclideanTheorem                 [G3]
```

Stage 9 can be proved first in the conditional form
`appendixEuclideanTheorem_of_main : AppendixMainTheoremNonempty → AppendixEuclideanTheorem`.

Notation used below: `S = G.S` (nonempty, open, connected), `D = G.D` (a group of homeomorphisms of `S`,
by `AxiomIGroup` and `IsDisplacement`), `K_M = {f ∈ D | f M = M}`, `B(M,r)`, `B̄(M,r)`, `c(M,r)` the open and
closed number discs and the number circle.

---------------------------------------------------------------------------------------------------------

## 4. Stage 1 — elementary consequences of the axioms (800–1 100 lines, low risk)

All proofs are complete here.

**1.1 Sequence form of III** and of its three special cases (from 2.2; `specialCase*_of_axiomIII` exist).

**1.2 No collapse (NC).** There are no `fₙ ∈ D` and `X ≠ Y` in `S` with `fₙ X → P`, `fₙ Y → P`, `P ∈ S`.
*Proof.* Apply III to `fₙ⁻¹ ∈ D` and the triads `(fₙX, fₙY, fₙX) → (P, P, P)`, images `(X, Y, X)`: some
`g ∈ D` has `g P = X` and `g P = Y`.

**1.3 Equicontinuity (EQ).** For `A ∈ S`, compact `C ⊆ S`, `ε > 0` there is `δ > 0` with: `f ∈ D`, `f A ∈ C`,
`|X − A| < δ` imply `|f X − f A| < ε`. *Proof.* Else `Xₙ → A`, `fₙ A → Q ∈ C` (subsequence), `|fₙXₙ − fₙA| ≥ ε`.
Let `ε' ≤ ε` be so small that the closed `ε'`-neighbourhood of `C` is a compact subset of `S`. On the segment
`[A, Xₙ]` (inside a small disc of `S`) the continuous function `X ↦ |fₙ X − fₙ A|` goes from `0` to `≥ ε'`, so
some `Yₙ` on it has `|fₙYₙ − fₙA| = ε'`; a subsequence has `fₙ Yₙ → Q'`, `|Q' − Q| = ε'`, `Q' ∈ S`. III with
triads `(A, Yₙ, A) → (A, A, A)` and images `→ (Q, Q', Q)` gives `g` with `g A = Q` and `g A = Q'`.
Contradiction. (Applied to `f⁻¹` it gives the corresponding statement for inverses.)

**1.4 Stability at a fixed point (Hilbert §1).** For `r₀ > 0` with `B̄(M,r₀) ⊆ S` there is `r₁ > 0` with
`f(B(M,r₁)) ⊆ B(M,r₀)` for all `f ∈ K_M`. *Proof.* As 1.3 with `A = M`, using the third special case:
otherwise some rotation about `M` would move `M` to a point of `c(M,r₀)`.

**1.5 Small true circles are compact and perfect (Hilbert §3).** For `A ∈ B(M,r₁) ∖ {M}`:
`Subtype.val '' TrueCircle G M A` is closed in `S` (`trueCircle_closed`), contained in `B(M,r₀)`, hence
compact; infinite by II; so it has an accumulation point, and by transitivity of `K_M` on it
(`trueCircle_transitive`) every point is one.

**1.6 The functions `n, N`.** For `X` near `M`: `n(X) = min_{f ∈ K_M} |f X − M|`,
`N(X) = max_{f ∈ K_M} |f X − M|`; continuous (by 1.3), `K_M`-invariant, `n(X) ≤ |X − M| ≤ N(X)`, zero only at
`M`. `{n < s} = K_M·B(M,s)` (open, connected), `{n ≤ s} = K_M·B̄(M,s)` (compact, connected).

**1.7 Restriction to an orbit is equicontinuous both ways**; pointwise limits of rotations about `M` on a small
true circle are realized on every pair of its points by a rotation about `M` (first special case of III).

---------------------------------------------------------------------------------------------------------

## 5. Stage 2 — winding numbers (1 600 – 2 300 lines, low–medium risk)

mathlib has no planar winding number for curves in `ℂ` (only `windingNumber` on `FundamentalGroup (AddCircle p)`
in `Mathlib/Topology/Covering/FundamentalGroupCircle.lean`). What it has and what will be used:
`Circle.isCoveringMap_exp` (`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`),
`IsCoveringMap.liftPath`, `IsCoveringMap.liftHomotopy`, `IsCoveringMap.exists_path_lifts`
(`Mathlib/Topology/Homotopy/Lifting.lean`), Tietze (`ContinuousMap.exists_restrict_eq`,
`Mathlib/Topology/TietzeExtension.lean`), and from the vendored library `JordanCurve.Brouwer.brouwerFPT`,
`JordanCurve.crossing`, `JordanCurve.arc_not_separates` (`JordanPick/JordanCurve.lean`), and the repository's
`jordanCurveTheorem` (`JordanCurveClose.lean`).

To build (all standard; statements only):

* 2.1 `Δ γ x ∈ ℝ`: variation of a continuous argument of `γ t − x` along a path `γ : [0,1] → ℂ ∖ {x}`
  (existence and uniqueness by path lifting; additivity under concatenation; sign change under reversal;
  invariance under reparametrization; continuity in `x` off the path).
* 2.2 Closed paths: `w γ x = Δ γ x / 2π ∈ ℤ`; locally constant in `x`, hence constant on connected subsets of
  the complement of the path; `0` on the unbounded component. Link with the repository's `WindsAround`:
  for a closed curve `γ` of period 1, `WindsAround (γ − x) n ↔ n = w γ x`; in particular **uniqueness** of `n`.
* 2.3 **Square lemma (duality).** If paths `u : U₀ ⇝ U₁` and `v : x ⇝ y` are disjoint, then
  `Δ u x − Δ u y = Δ v U₀ − Δ v U₁`. (Lift `(s,t) ↦ u s − v t` on the square with `liftHomotopy`; compare the
  four sides.)
* 2.4 Stability: if `|γ₁ t − γ₂ t| < |γ₁ t − x|` for all `t`, then `w γ₁ x = w γ₂ x`.
* 2.5 Reparametrization of a closed curve by an orientation-reversing homeomorphism of `ℝ/ℤ` changes `w` into
  `−w`.
* 2.6 **Inside ⇒ nonzero** (Borsuk-type). For a closed Jordan curve `J` and `p` in its bounded component:
  `w J p ≠ 0`. *Proof.* If `w = 0` the argument descends to a continuous `g` on `J` with `z − p = e^{g z}`;
  extend `g` to `ℂ` (Tietze); `h = e^{g}` on the closed inside, `h z = z − p` elsewhere, is continuous (the
  frontier of the inside is `J`, from `jordanCurveTheorem`) and never zero; on a large disc the map
  `z ↦ p − R·h z/|h z|` has no fixed point, against `brouwerFPT`.
* 2.7 **Jump across a straight piece**: if a closed curve contains a straight segment and is otherwise at
  positive distance from a point `q` of the open segment, then `w` at the two points `q ± εν` (ν normal) differ
  by exactly `±1` for small `ε`.
* 2.8 **`w = ±1` inside a closed Jordan curve.** From 2.6, 2.7 and `jordanCurveTheorem`: through an inside
  point `p` take the horizontal chord `[P,Q]` (first hits of `J` on both sides); `J = a ∪ b` (arcs from `P` to
  `Q`); `Γ_a = a ∪ [P,Q]`, `Γ_b = b ∪ [P,Q]` are closed Jordan curves, `w J = w Γ_a − w Γ_b`; by 2.7 the two
  points `x⁺, x⁻` next to `p` on the two sides of the chord are on different sides of `Γ_a` and of `Γ_b`, with
  the same jump `ε = ±1`; one of them is outside (`w = 0`); the case "both `Γ` have `x⁺` inside" would give
  `w J x⁺ = 0`, excluded by 2.6; hence `w J x⁺ = ±1`. (Checked by hand; about 300 lines of Lean.)

---------------------------------------------------------------------------------------------------------

## 6. Stage 3 — plane topology toolkit (2 200 – 3 200 lines, medium risk: volume, not depth)

* 3.1 Arcs (continuous injective images of `[0,1]`); **two-arc lemma**: from an arc `A ⇝ B` and an arc
  `B ⇝ C` one cuts an arc `A ⇝ C` inside their union (first point of the first arc on the second); finite
  chains; an open connected subset of `ℂ` is polygonally connected, hence arc-connected
  (`IsOpen.isConnected_iff_isPathConnected`, `Mathlib/Topology/Connected/LocallyPathConnected.lean`, gives
  paths; polygonal paths by the usual open–closed argument).
* 3.2 Gluing two arcs with common end points and otherwise disjoint into a curve satisfying
  `IsClosedJordanCurve` (period 1, injective on `[0,1)`).
* 3.3 For a closed Jordan curve `J ⊆ B(M,r₀) ⊆ S`: inside `⊆ B(M,r₀)`; a homeomorphism `f` of `S` maps the
  inside of `J` onto the inside of `f J` whenever `f J ⊆ B(M,r₀)` too (an open connected set with compact
  closure in `S` whose frontier is the Jordan curve is its bounded component).
* 3.4 Two disjoint closed Jordan curves, each with `M` inside, are nested; the closed inside of the inner one
  lies in the open inside of the outer one.
* 3.5 **Outside component is invariant.** If `F ⊆ B(M,r₀)` is compact and `K_M`-invariant and `O` is the
  unbounded component of `ℂ ∖ F`, then `O ∩ S` is connected and `f (O ∩ S) = O ∩ S` for `f ∈ K_M` (it is the
  only component of `S ∖ F` whose closure in `S` is not compact).
* 3.6 Accessibility: a point `P ∈ frontier O` is *accessible from `O`* if an arc ends at `P` and lies otherwise
  in `O`. First points of straight segments are accessible; accessible points are dense in `frontier O`.
* 3.7 **θ-lemma.** If `s₁, s₂, s₃` are arcs from `m` to `z`, pairwise disjoint except for the end points,
  then `ℂ ∖ (s₁ ∪ s₂ ∪ s₃)` has exactly three components, and the component of `ℂ ∖ (s₁ ∪ s₂)` containing the
  open arc `s₃` is cut by `s₃` into two of them, with frontiers `s₁ ∪ s₃` and `s₂ ∪ s₃`. Classical consequence
  of the Jordan curve theorem and `arc_not_separates`; not in mathlib, not in `JordanPick`. I did **not**
  write out a proof in this study; standard proofs are one to two pages (400–700 lines of Lean). Risk: medium.
* 3.8 Tripods: three arcs from `M` to three points can be re-cut (two-arc lemma) into three arcs from a common
  point, pairwise disjoint otherwise.

---------------------------------------------------------------------------------------------------------

## 7. Stage 4 — one true circle near `M` is a closed Jordan curve (3 000 – 4 400 lines, medium–high risk)

This replaces Hilbert's §§ 2–9 and 13–18. The arguments below are my own reconstruction (not Hilbert's text);
they were checked by hand but not by Lean.

### 7.1 Setting ("bi-accessible configuration")

Fix `M`, `r₀`, `r₁` as in 1.4, `K = K_M`. Let `C ⊆ B(M,r₁)` be a finite union of closed number discs with
`M ∈ interior C` and `interior C` connected (basic case: `C = B̄(M,s)`; the general case is needed in 8.2).
Put `F = K·C` (compact, connected, invariant), `I = K·interior C` (open, connected, invariant, `M ∈ I`),
`O` = unbounded component of `ℂ ∖ F` (so `O ∩ S` is invariant by 3.5 and `I ∩ O = ∅`), and
`𝒜 = {P ∈ frontier O | P accessible from O}` (nonempty, invariant).

*Every point `P` of `frontier O` is accessible from `I`*: `P = f Q` with `f ∈ K`, `Q ∈ C`; `Q` is not interior
to `C` (else `P ∈ I ⊆ interior F`), so `Q` lies on the rim of one of the discs, and the `f`-image of the radius
of that disc ending at `Q` is an arc ending at `P` with all other points in `I`. So each `P ∈ 𝒜` has an *inner
arc* (from `M`) and an *outer arc* (from a point of `O ∩ S`). For one point of `𝒜` the outer arc is a straight
segment inside `B̄(M,r₀)`; for the points of its orbit it is the image of that segment under a rotation, which
lies in `O ∩ S` by 3.5 but **need not** stay inside `B̄(M,r₀)`. This is harmless: `σ` below only uses winding
numbers of curves of `S` about points of `S`, never the inside of such a curve.

### 7.2 The integer invariant `σ` and its properties

For distinct `P, Q ∈ 𝒜` choose an inner path `a : P ⇝ Q` (in `I ∪ {P,Q}`) and an outer path `b : P ⇝ Q`
(in `(O ∩ S) ∪ {P,Q}`; it exists because `O ∩ S` is open and connected, 3.5); for
`X, Y ∈ frontier O ∖ {P,Q}` put

`σ(P,Q;X,Y) = (Δ a X − Δ b X − Δ a Y + Δ b Y)/2π = w(a·b⁻¹, X) − w(a·b⁻¹, Y) ∈ ℤ.`

1. *Independent of `a`, `b`.* Two inner paths differ by a loop in `I ∪ {P,Q}`; `X, Y` lie in the closure of
   the connected set `O`, which is disjoint from the loop and unbounded, so `w = 0` at both. Two outer paths
   differ by a loop in `O ∪ {P,Q}`; `X, Y` lie in the closure of the connected set `I`, disjoint from the loop,
   so `w` takes the same value at both; the difference cancels.
2. *Cocycle identities* in each pair, antisymmetry in each pair (additivity of `Δ`).
3. *Duality*: `σ(X,Y;P,Q) = −σ(P,Q;X,Y)` for four distinct points of `𝒜` (square lemma 2.3 applied to
   inner-of-one against outer-of-the-other, which are disjoint because `I ∩ O = ∅`).
4. *Jordan form.* By 3.1, 3.2 the paths can be chosen as arcs, so `J = a ∪ b` is a closed Jordan curve lying
   in `S`. By 2.8 (applied in `ℂ`), `σ(P,Q;X,Y) ∈ {0, ±1}`, and it is `≠ 0` iff `J` separates `X` from `Y`
   in `ℂ`.
5. *Local constancy* in `(X,Y)` for fixed `(P,Q)` (2.2), hence, by duality, in all four variables on
   quadruples of distinct points of `𝒜`.
6. *Invariance*: `σ(fP,fQ;fX,fY) = σ(P,Q;X,Y)` for `f ∈ K`. This is where `SensePreserving` enters, in exactly
   its stated form: `f J` is a Jordan curve of the same kind for `fP, fQ` (`f I = I`, `f (O ∩ S) = O ∩ S`),
   and `w(f J, f X) = w(J, X)` by `SensePreserving` and 2.2.
7. *Both sides are occupied.* For distinct `P, Q ∈ 𝒜` both components of `ℂ ∖ J` contain points of `𝒜`.
   (Each component `U` has all of `J` in its frontier, so meets `I` near the inner arc and `O` near the outer
   arc; a polygonal path in `U` from a point of `O` to a point of `I` has a first point outside `O`; it is in
   `frontier O`, accessible from `O`, and lies in `U`.)
8. *Exactly one pairing separates.* For distinct `A, B, C, E ∈ 𝒜` exactly one of `σ(A,B;C,E)`, `σ(A,C;B,E)`,
   `σ(A,E;B,C)` is nonzero. (Tripods 3.8 inside `I` and inside `O` give a θ-graph through `A, B, C`; apply the
   θ-lemma 3.7 to the face containing `E`.)

### 7.3 The cyclic order

Choose for each `P ∈ 𝒜` a *spoke* (inner arc from `M` to `P`, then outer arc from `P` to a fixed far point
`Z₀`), and let `ω(P,X) = Δ(spoke of P)(X)/2π − c_P`, where the constants `c_P` are chosen (by 2.3) so that
`ω(P,X) = −ω(X,P)`. Then `σ(P,Q;X,Y) = T(P,Q,X) − T(P,Q,Y)` with `T(A,B,C) = ω(A,B) + ω(B,C) + ω(C,A)`;
`T` is totally antisymmetric and satisfies `T(A,B,C) − T(A,B,E) + T(A,C,E) − T(B,C,E) = 0` identically, and
`σ(A,B;C,E) + σ(A,C;B,E) − σ(A,E;B,C) = 2·T(A,E,C)`. With 7.2.8 this forces `T ∈ {+1/2, −1/2}`. So
`o = 2T : 𝒜³ → {±1}` is an alternating map with `o(A,B,C) − o(A,B,E) + o(A,C,E) − o(B,C,E) = 0`, i.e. a total
cyclic order on `𝒜` (it yields a `CircularOrder` in the sense of `Mathlib/Order/Circular.lean`: e.g.
`o(A,B,C) = o(A,C,E) = 1` forces `o(A,B,E) = 1`). It is `K`-invariant and locally constant on triples of
distinct points (from 7.2.5–7), and the two "intervals" of `𝒜 ∖ {P,Q}` are relatively open and nonempty.
(An implementer may prefer to define the cyclic order directly from `σ` and derive the axioms from 7.2.8; the
content is the same.)

### 7.4 No gaps in an orbit

Let `ϰ = K·P₀ ⊆ 𝒜` be an orbit (compact, perfect by 1.5). **Claim:** for `X ≠ X'` in `ϰ` both open intervals
between them contain points of `ϰ`. *Proof.* Suppose the interval `(X,X')` has no point of `ϰ`; it contains a
point `q ∈ 𝒜` (7.2.7). Take `Xₙ ∈ ϰ`, `Xₙ → X`, `Xₙ ≠ X`, `fₙ ∈ K` with `fₙ X = Xₙ`, `Xₙ' = fₙ X'`; the
intervals `(Xₙ,Xₙ')` have no point of `ϰ` (invariance). A limit point `Q` of `Xₙ'` is `≠ X` (NC, 1.2), lies in
`ϰ`, and `(X,Q)` has no point of `ϰ` (local constancy), so `Q = X'` (two gaps starting at `X` are equal).
Fix `U ∈ ϰ ∖ {X,X'}`. By local constancy at the triples `(U,X,q)` and `(q,X',U)`: for large `n`,
`Xₙ ∈ (U,q)` and `Xₙ' ∈ (q,U)`; as `Xₙ ∈ ϰ`, `Xₙ ∉ (X,q)`, so `Xₙ ∈ (U,X)`, i.e. the cyclic order is
`U, Xₙ, X, q, Xₙ'`, and `X ∈ (Xₙ,Xₙ')`, a point of `ϰ` in a gap. Contradiction.

### 7.5 Haar measure and the angle `Θ` (replaces Hilbert's §§ 7, 8, 13–18)

* `E` := closure of `{f|_ϰ : f ∈ K}` in `C(ϰ,ϰ)` (uniform metric). By 1.7 and Arzelà–Ascoli
  (`ArzelaAscoli.isCompact_of_equicontinuous`, `Mathlib/Topology/UniformSpace/Ascoli.lean`, or
  `BoundedContinuousFunction.arzela_ascoli`) `E` is compact; its elements are bijections of `ϰ` (limits of
  `fₙ` and, along a subsequence, of `fₙ⁻¹`), `E` is a compact Hausdorff topological group acting continuously
  and transitively on `ϰ`. mathlib has no ready-made "compact group of homeomorphisms"; the group structure and
  `IsTopologicalGroup` on this subtype must be built by hand (400–600 lines).
* `ν` := image of the normalized Haar measure of `E` (`MeasureTheory.Measure.haarMeasure`,
  `Mathlib/MeasureTheory/Measure/Haar/Basic.lean`) under `g ↦ g P₀`: a `K`-invariant Borel probability measure
  on `ϰ`, positive on nonempty open sets, without atoms (`ϰ` is infinite and homogeneous).
* `θ(P,Q) := ν((P,Q) ∩ ϰ) mod 1` for `P ≠ Q` in `ϰ`, `θ(P,P) = 0`. From the cyclic order:
  `θ(P,Q) + θ(Q,R) = θ(P,R)` in `ℝ/ℤ`; from invariance of `o` and `ν`: `θ(fP,fQ) = θ(P,Q)`.
* `Θ(X) := θ(P₀,X)`, `χ(f) := θ(P₀, f P₀)`. Then **`χ : K → ℝ/ℤ` is a group homomorphism** and
  `Θ(f X) = χ(f) + Θ(X)`.
* `Θ` is continuous: `Θ(X') − Θ(X) = ∫ σ(X,X';Z,Y₀) dν(Z)` (for a fixed `Y₀`, modulo 1), and for each fixed
  `Z ≠ X` the integrand is `−σ(Z,Y₀;X,X') = 0` as soon as `X'` is close to `X` (7.2.3, 7.2.5); dominated
  convergence.
* `Θ` is injective: `θ(X,X') = ν((X,X') ∩ ϰ) ∈ (0,1)` by 7.4 (both intervals are nonempty open subsets of `ϰ`).
* Hence `Θ` is a homeomorphism of `ϰ` onto the compact set `Θ(ϰ) = χ(K)`, an infinite closed subgroup of
  `ℝ/ℤ`, i.e. all of `ℝ/ℤ`.

**Theorem 4 (output of the stage).** `ϰ` is the range of a closed Jordan curve; `χ : K_M → ℝ/ℤ` is a
surjective homomorphism; `Θ : ϰ → ℝ/ℤ` is an equivariant homeomorphism; `ker χ` = the stabilizer of any point
of `ϰ` = the pointwise stabilizer of `ϰ`.

### 7.6 `M` is inside, and `ϰ = frontier O` (Hilbert §9)

Take `P, Q ∈ ϰ` and `J` as in 7.2.4. The two arcs of the Jordan curve `ϰ` between `P` and `Q` are connected,
disjoint from `J`, and both sides of `J` contain points of `ϰ` (7.4), so they lie on different sides of `J`.
If `I` and `O` were in the same component of `ℂ ∖ ϰ`, the other component `U'` would be disjoint from `J`,
hence on one side of `J`, and `ϰ ⊆ closure U'` would put both arcs on that side. So `ϰ` separates `I ∋ M` from
`O`: `M` is inside `ϰ`. Then `F ⊆` closed inside of `ϰ` (every point of `F` is in the closure of `I`), so
`O` = outside of `ϰ` and `frontier O = ϰ = 𝒜`.

---------------------------------------------------------------------------------------------------------

## 8. Stage 5 — all true circles; the rotation group; the five units of G1 (2 600 – 3 900 lines, medium risk)

**8.1 Touching circles.** For `0 < s < r₁` let `ϰ_s` be the Jordan orbit of 7.6 for `C = B̄(M,s)`: it lies
outside `B(M,s)`, meets `c(M,s)`, and has `B(M,s)` inside. *Uniqueness* (Hilbert §11): a Jordan orbit around
`M` outside `B(M,s)` and meeting `c(M,s)` equals `ϰ_s` (two distinct orbits are disjoint, hence nested by 3.4,
and the outer one could not meet `c(M,s) ⊆ closure(B(M,s))`). *Monotonicity*: for `s < s'`, `ϰ_s` lies inside
`ϰ_{s'}` (`{n ≤ s} ⊆ {n < s'}`).

**8.2 Every orbit near `M` is one of the `ϰ_s` (Hilbert §12, with a different proof).** Let `P` lie inside
`ϰ_{s₀}`, `P ≠ M`, `s* = sup{s | P is outside ϰ_s}`.
(a) `P` is not outside `ϰ_{s*}`: else a path from `P` to infinity avoids `F_{s*} = {n ≤ s*} = ⋂_{s>s*} F_s`,
hence avoids `F_s` for `s` slightly larger (compactness), so `P` is outside `ϰ_s` for some `s > s*`.
(b) `P` is not inside `ϰ_{s*}`: else join `M` to `P` by a polygonal path inside the open inside of `ϰ_{s*}`
(an invariant open set), cover it by finitely many small closed discs inside it, apply stage 4 to this `C`:
a Jordan orbit `ϰ_C` with `C` in its closed inside and `ϰ_C ⊆ K·C` inside `ϰ_{s*}`; by uniqueness (8.1)
`ϰ_C = ϰ_{s''}` with `s'' = min_{ϰ_C} |z − M| < s*`; so `P` is not outside `ϰ_{s''}`, against the definition
of `s*`. Hence `P ∈ ϰ_{s*}`.
**Consequence:** inside `ϰ_{s₀}` the orbits of `K_M` other than `{M}` are exactly the nested closed Jordan
curves `ϰ_s`, `{n = s} = ϰ_s`, and each carries the structure of Theorem 4.

**8.3 A rotation fixing a small true circle pointwise is the identity (Hilbert §19).** Let `g ∈ K_M` fix
`ϰ_s` pointwise. For `A ∈ ϰ_s` apply 8.2 at the centre `A`: every small true circle `α` about `A` is a Jordan
curve around `A`, and `ϰ_s` (connected, through `A`, of larger diameter) meets it; `g ∈ K_A` fixes a point of
`α`, hence `α` pointwise (Theorem 4 at `A`). So `g` is the identity near every point of `ϰ_s`. The set of `s`
for which `g` fixes `ϰ_s` pointwise is therefore open, and closed; so `g = id` near `M`. Finally the interior
of the fixed point set of `g` is closed in `S` (same argument at a frontier point `B`, which is a fixed
point), so `g = id` (`S` connected).
**Consequence:** `χ : K_M → ℝ/ℤ` is an isomorphism; write `K_M = {k_t | t ∈ ℝ/ℤ}`; it is abelian and acts
freely on the punctured inside of `ϰ_{s₀}`.

**8.4 Global continuity and properness.** If `tₙ → t` then `k_{tₙ} X → k_t X` for **every** `X ∈ S`:
the set of such `X` contains a neighbourhood of `M`, is open (EQ + III on triads `(M, P, ·)` + uniqueness from
8.3) and closed (the path argument of 1.3) in `S`. So `(t,X) ↦ k_t X` is jointly continuous on
`ℝ/ℤ × S`. Similarly: if `fₙ ∈ D` and `fₙ A` converges in `S`, a subsequence converges pointwise (locally
uniformly) to an element of `D`.

**8.5 The units.**
* *Fixed points are isolated*: a displacement `g ≠ id` fixing `B` acts on the small true circles about `B`
  as `k^B_t` with `t ≠ 0`, without fixed points.
* **`TwoFixedPointsIdentity`**: `g` fixes `A ≠ B`; `g ∈ K_A` commutes with `K_A`, so it fixes the true circle
  `K_A·B` pointwise, an infinite compact set (8.4, II); a non-isolated fixed point; `g = id`.
* **`AtMostOneMiddle`**: `atMostOneMiddle_of_twoFixedPoints` (in the repository).
* **`TrueCirclesAreJordan`** (all true circles, not only small ones): `γ t = k_t A`; continuous (8.4),
  of period 1, injective on `[0,1)` (freeness = two fixed points).
* **`RotationsOfTrueCircle`**: `φ (k_t A) = e^{2πit}`.
* **`DisplacementsTransitive`** (Hilbert §22): for `P ≠ Q` the closed Jordan curves `K_P·Q` and `K_Q·P`
  meet (then `k R = Q`, `k' P = R` give `k k' P = Q`). Indeed the centre is inside each true circle about it:
  `Q ↦ w(K_P·Q, P)` is locally constant on the connected set `S ∖ {P}` (2.4, 8.4) and is `±1` near `P`; and
  two disjoint closed Jordan curves each containing a point of the inside of the other cannot exist (3.4).

**8.6** By the same continuity argument every closed true disc (closed inside of `K_P·Q`) lies in `S`; the
true circles about `P` are totally ordered by inclusion of insides and exhaust `S`.

---------------------------------------------------------------------------------------------------------

## 9. Stage 6 — half-rotations, middles, true lines (5 000 – 8 000 lines, HIGH risk)

Here the study has **not** reconstructed complete proofs; what follows is the list of statements with the
status of each. The blueprint for this stage has to be written from the German text of §§ 23–40.

After stage 5: the semi-rotation about `X` is unique, `σ_X = k^X_{1/2}` (`IsSemiRotation G σ X ↔ σ = σ_X`);
`σ_{gX} = g σ_X g⁻¹`; `(X,Y) ↦ σ_X Y` is continuous (§25: 8.4 and uniqueness); `D` acts simply transitively on
ordered pairs of points of a given congruence class.

* 6.1 (§24) uniqueness of the middle — done (G1).
* 6.2 (§26) *If `AB` has a middle and `C` is inside the true circle about `A` through `B`, then `AC` has a
  middle.* Complete proof: `m_A : X ↦ σ_X A` is continuous and `K_A`-equivariant; along a path from `A` to the
  middle of `AB` its image runs from `A` to `B` and crosses the true circle through `C`; rotate about `A`.
* 6.3 (§§27–29) **Tangent true circles**: two congruent true circles touching from outside in exactly one
  point exist, the point is the middle of the centres; a true circle inside another and touching it touches in
  one point; consequently *for `E` close to `O` the true circle about `O` through `E` contains the true circle
  about the middle `M` of `OE` through `E` and touches it only in `E`* (so the middle is strictly nearer to `O`
  than `E`). **Not reconstructed.** The paraphrase of §27 I obtained has at least two steps that are only
  asserted (choice of a rotation making exactly one contact point; uniqueness of the touching congruent
  circle), §28 uses placements "inside/outside" without argument. Some statement of this kind is unavoidable:
  the purely formal data of stage 5 are also satisfied by elliptic geometry (where a segment of length one
  third of a line is as long as its half's double), so planarity must be used again here. I estimate
  1 500–2 500 lines and regard this as the place in G2 most likely to need new mathematical work.
* 6.4 (§§30–35) dyadic points `p(k/2ⁿ)` from `O, E`; `σ_{p a} p x = p(2a − x)`; `p(2⁻ⁿ) → O` (§33, uses 6.3 and
  §25); `p` is uniformly continuous on bounded sets of dyadic numbers (§35: otherwise two limit points would be
  brought simultaneously near `O`, against NC). The algebra is routine; the convergence statements depend on
  6.3.
* 6.5 (§§36–39) extension `p : ℝ → S`, continuous, `σ_{p a} p x = p(2a − x)`; injective (§38; the paraphrase
  of the final contradiction is unclear — to be re-read); two true lines with two common points coincide (§39,
  by iterated middles and density).
* 6.6 (§40) a true line through `O` meets every true circle about `O`; hence any two points lie on a true
  line, every segment has a middle, and `p` is a closed embedding. (Paraphrase has unproved steps in both
  cases.)
* 6.7 Identification with the repository's definition: `TrueLine G A B = range p` for the line through
  `A, B` (2.2) ⇒ **`TrueLineIsCurve`**, **`TrueLinesMeetAtMostOnce`**. Routine once 6.4–6.6 exist (400–600
  lines).

---------------------------------------------------------------------------------------------------------

## 10. Stage 7 — the classification: reduction and the euclidean branch (2 000 – 3 000 lines, medium risk)

**10.1 Reduction to group theory.** `AppendixMainTheoremNonempty` follows from: *there is a group isomorphism
`Φ` of `D` onto the model group (`{z ↦ az + b}` or `{z ↦ c(z − a)/(1 − ā z)}`) carrying `K_M` onto the
stabilizer of `0`*. Then `φ (g M) := Φ(g)(0)` is a well-defined bijection of `S` (transitivity) onto `ℂ` or the
disc, and `f ∈ D ↔ φ f φ⁻¹` is a model motion. No continuity of `φ` is required by the formal statement (W1).
The closure of the model group under composition is partly in the repository (`mob`, `mobPerm`, `rotPerm`,
`mob_neg_mob`, `norm_mob_lt` in `CommentaryCloseAux7.lean`); the composition law of the disc maps is missing.

**10.2 The dichotomy.** (E): for all `A, B, C` the product `σ_A σ_B σ_C` is a half-rotation. Either (E) holds
or not.

**10.3 Euclidean branch (assuming (E) and stage 6).** Proof sketch, checked in outline only:
`P := {σ_X σ_M}` is then an abelian normal subgroup of `D` acting simply transitively on `S`; transport it to
an abelian group structure on `S` with zero `M`; the true lines through `M` are its one-parameter subgroups
(stage 6), which gives a scalar multiplication by dyadic numbers, extended by continuity; `S` becomes a
Hausdorff topological real vector space, locally compact, hence finite-dimensional
(`FiniteDimensional.of_locallyCompactSpace`, `Mathlib/Topology/Algebra/Module/FiniteDimension.lean`; continuous
additive maps are real-linear: `AddMonoidHom.toRealLinearMap`, `Mathlib/Topology/Instances/RealVectorSpace.lean`);
`K_M` acts linearly, `k_{1/2} = −1`, `J := k_{1/4}` has `J² = −1`, so `S` is a complex vector space on which
`K_M` acts ℂ-linearly; the rays from `0` form one free `K_M`-orbit, which forces complex dimension 1 and
`k_t = e^{±2πit}`. This is much shorter than Hilbert's route through Anhang II and the coordinates of
Chapter III, and it does not need reflections. What the repository has for the euclidean case
(`Pas.exists_real_coord_norm`, `exists_real_correspondence`, `CC.PreEmb`, `exists_metric_coords`,
`CC.exists_bijective_emb`) presupposes the **full** congruence axiom IV 6 (`PlaneCongruence`) and the parallel
axiom (`PlaneParallels`); the displacements only give IV 6 for triangles of the same sense, and the repository
has nothing on the narrower axiom (Anhang II). So those theorems are not directly usable.

---------------------------------------------------------------------------------------------------------

## 11. Stage 8 — the hyperbolic branch (9 000 – 15 000 lines, VERY HIGH risk; not worked out)

When (E) fails one has to produce the isomorphism `D ≅ PSL(2,ℝ)` (10.1). The repository has **nothing** for
the hyperbolic plane: no model satisfying the axioms, no limiting parallels, no calculus of ends (the
occurrences of "hyperbolic" are in `Commentary*.lean`, `Independence*.lean`, `Pascal.lean` only, none of them
a classification). mathlib has `UpperHalfPlane` with the Möbius action of `GL(2,ℝ)` and the metric
(`Mathlib/Analysis/Complex/UpperHalfPlane/{MoebiusAction,Metric}.lean`) and `Complex.UnitDisc`, but no
axiomatic hyperbolic geometry and no characterization of `PSL(2,ℝ)`.

Two candidate routes; neither has been worked out in this study.

* **Route H (Hilbert, §§41–42 + Anhang III).** Verify the plane axioms I 1–3, II (including Pasch: needs that a
  true line separates `S` into two sides), the congruence axioms with IV 6 for equally oriented triangles, and
  continuity; then formalize Anhang III with the narrower IV 6 (Hilbert only asserts that it goes through):
  limiting parallels, ends, addition and multiplication of ends, the field of ends is `ℝ`, the equation of a
  point. Estimate: axioms 4 000–6 000, calculus of ends 6 000–9 000, identification with the disc formulas
  1 500–2 500.
* **Route G (group form of the same idea).** Ends `∂` = classes of asymptotic rays; `D` acts on `∂` (a circle);
  the stabilizer `B` of an end `∞` acts simply transitively on `S`; the elements of `B` without fixed end other
  than `∞` form a subgroup `N` acting freely and transitively on `∂ ∖ {∞}`, order-preservingly, hence
  `N ≅ (ℝ,+)` (Hölder); the translations `T` along a line ending at `∞` normalize `N` and act by positive
  multiplications; so `B ≅ Aff⁺(ℝ)` in its standard action on `ℝ ∪ {∞}`; the half-rotation `σ_M` normalizes
  `T`, hence acts as `x ↦ −c/x`; `D = B ∪ B σ_M B` then equals `PSL(2,ℝ)`; transport to the disc by the Cayley
  transform. The hard steps are the same as in Hilbert: asymptotic rays form an equivalence relation, and `N`
  is a group (Hilbert's addition of ends, his "limit of rotations about points moving to infinity").
  Estimate 9 000–13 000.

Either way this stage is as large as stages 1–5 together, and it is the only part of the plan for which I
cannot name every intermediate lemma today. A separate study, with the text of Anhang III in hand, is needed
before blueprinting.

---------------------------------------------------------------------------------------------------------

## 12. Stage 9 — the invariant subgroup (900 – 1 300 lines, low risk)

`AppendixEuclideanTheorem` from `AppendixMainTheoremNonempty`:

1. `H` := the set of permutations `z ↦ c(z − a)/(1 − ā z)` of `Metric.ball (0:ℂ) 1` is a subgroup of
   `Equiv.Perm` (composition law to be computed; inverses via `mobPerm`, `rotPerm`).
2. A surjective homomorphism `Ψ : SL(2,ℝ) → H` with `Ψ(−1) = 1` (Cayley transform of the action on the upper
   half plane, or directly `SU(1,1)`: `(αz + β)/(β̄z + ᾱ) = (α/ᾱ)(z + β/α)/(1 + (β̄/ᾱ)z)`).
3. `H` is simple: for `N ⊴ H`, `Ψ⁻¹ N ⊴ SL(2,ℝ)` maps to a normal subgroup of `PSL(2,ℝ)`, which is `⊥` or `⊤`
   by `Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` (hypothesis `∃ a ≠ 0, a² ≠ 1`: `a = 2`; **confirmed
   by scratch compile** for `Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ`), giving `N = ⊥` or `N = ⊤`.
4. If `G` has an invariant sub-group and is hyperbolic, `φ` carries it to a proper non-trivial normal subgroup
   of `H`; contradiction; so `G` is euclidean by the main theorem (`G.S` is nonempty because the invariant
   sub-group contains a non-identity permutation).

This yields at once the unconditional theorem
`appendixEuclideanTheorem_of_main : AppendixMainTheoremNonempty → AppendixEuclideanTheorem`.

---------------------------------------------------------------------------------------------------------

## 13. Modern proofs: would any be cheaper?

* **Hilbert's fifth problem for transformation groups** (Montgomery–Zippin: a locally compact group acting
  effectively and transitively on a surface is a Lie group; then Lie/Mostow classification of homogeneous
  surfaces). Needs Gleason–Yamabe, Lie groups and Lie algebras, classification of 3-dimensional Lie groups and
  their homogeneous spaces. None of it is in mathlib v4.36.0. Far more expensive.
* **Tits, Freudenthal (Riemann–Helmholtz–Lie space problem)**, **Salzmann et al. (planar groups)**: start from
  Lie groups or from Brouwer's and Montgomery–Zippin's theorems. Not cheaper.
* **Brouwer (1909–10), Kerékjártó (1930s: compact and "regular" groups of surface homeomorphisms), Süss
  (1926–27, weakening of Hilbert's axioms), R. L. Moore (1919)**: elementary plane topology of the same kind and
  length as Hilbert's §§ 1–22; they do not shorten the classification step. The theorem "a compact group of
  orientation-preserving homeomorphisms of the disc is conjugate to a group of rotations" (Kerékjártó,
  Eilenberg; modern proofs by Constantin–Kolev and Kolev) would give stage 4–5, but its proofs are not shorter
  than section 7 and are not in mathlib.
* **Busemann, Birkhoff (metric characterizations)**: need geodesics and lead to the same classification.
* What does help from mathlib: Haar measure on a compact group (section 7.5), covering-space lifting (stage 2),
  simplicity of `PSL(2,F)` (stage 9), finite-dimensionality of locally compact topological vector spaces
  (stage 7). The Riemann mapping theorem is only partially in mathlib
  (`Mathlib/Analysis/Complex/RiemannMapping.lean` contains private preliminary lemmas), there is no invariance
  of domain, no Schoenflies theorem, no θ-curve lemma, no planar winding number.

Conclusion: the cheapest route on mathlib v4.36.0 is Hilbert's chain of theorems with the modifications of
sections 7, 8.2 and 10.

---------------------------------------------------------------------------------------------------------

## 14. Estimates, risks, staged plan

| stage | content | lines | risk | checkable result at the end |
|---|---|---|---|---|
| 9 (first) | PSL(2,ℝ) and the disc group | 900–1 300 | low | `appendixEuclideanTheorem_of_main` |
| 1 | consequences of I–III | 800–1 100 | low | `nc`, `equicontinuous`, `stable`, compact perfect small circles |
| 2 | winding numbers | 1 600–2 300 | low–medium | `winding_inside_eq_one_or_neg_one`, square lemma |
| 3 | plane topology | 2 200–3 200 | medium | θ-lemma, nested Jordan curves, invariance of the outside |
| 4 | one Jordan true circle | 3 000–4 400 | medium–high | Theorem 4 (7.5), 7.6 |
| 5 | all circles, `K_M ≅ ℝ/ℤ`, G1 | 2 600–3 900 | medium | the five units of G1, with their exact statements |
| 6 | true lines, G2 | 5 000–8 000 | high | `TrueLineIsCurve`, `TrueLinesMeetAtMostOnce` |
| 7 | reduction + euclidean branch | 2 000–3 000 | medium | `(E) → IsEuclideanGeometry G` |
| 8 | hyperbolic branch | 9 000–15 000 | very high | `¬(E) → IsHyperbolicGeometry G`, hence `AppendixMainTheoremNonempty` and `AppendixEuclideanTheorem` |
| | **total** | **27 000–42 000** | | |

Risks, in order of seriousness:

1. **Stage 8 is not designed.** Its cost has the widest error bars and it may reveal that Hilbert's Anhang III
   with the narrower congruence axiom needs arguments he did not write down.
2. **Stage 6, tangent true circles (§§27–29).** Not reconstructed; the available paraphrase shows gaps. If
   Hilbert's argument cannot be completed as written, a new proof is needed that middles are "inside" (see
   6.3).
3. **Section 7 is a new argument.** It was checked by hand, not by Lean. Points to verify first in a blueprint:
   independence of `σ` from the outer path (7.2.1), the normalization making `ω` antisymmetric (7.3), the
   θ-lemma (3.7) and the limit argument 7.4. Fallback: Hilbert's own §§4–8 and 13–18 (order by cuts, bisection
   of angles), which I estimate 2 000–3 000 lines longer.
4. **`S` is not known to be simply connected until 8.6.** Every use of "inside of a Jordan curve" before that
   must stay inside a number disc `B̄(M,r₀) ⊆ S`.
5. **Source.** The memoir was read only through a paraphrasing tool; section numbers and details of §§23–42
   must be re-checked against the scan.
6. Volume: stages 2–3 are standard but long; underestimation by 30 % would not be surprising.
7. Machine: 16 GB RAM, one Lean file at a time; files of the order of 400–500 lines as in the rest of the
   repository mean 60–90 new files.

Recommended order: stage 9 → stages 1–5 (this closes five of the eight units unconditionally, with complete
proofs available in this study) → decision point → stage 6 → separate study of stage 8 → stages 7, 8.

---------------------------------------------------------------------------------------------------------

## 15. Declarations confirmed (by rg in the mathlib sources, or by one scratch compile with `leanc.py`; the scratch file has been removed)

mathlib (`.lake/packages/mathlib/Mathlib/…`):
`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` (LinearAlgebra/Projectivization/PSL/PSL2.lean; compiled
for `ℝ`); `MeasureTheory.Measure.haarMeasure`, `isHaarMeasure_haarMeasure` (MeasureTheory/Measure/Haar/Basic.lean);
`Circle.isCoveringMap_exp` (Analysis/SpecialFunctions/Complex/Circle.lean); `IsCoveringMap.liftPath`,
`IsCoveringMap.liftHomotopy`, `IsCoveringMap.exists_path_lifts` (Topology/Homotopy/Lifting.lean);
`ArzelaAscoli.isCompact_of_equicontinuous` (Topology/UniformSpace/Ascoli.lean);
`BoundedContinuousFunction.arzela_ascoli` (Topology/ContinuousMap/Bounded/ArzelaAscoli.lean);
`ContinuousMap.exists_restrict_eq` (Topology/TietzeExtension.lean); `CircularOrder` (Order/Circular.lean);
`AddMonoidHom.toRealLinearMap` (Topology/Instances/RealVectorSpace.lean);
`FiniteDimensional.of_locallyCompactSpace` (Topology/Algebra/Module/FiniteDimension.lean);
`IsOpen.isConnected_iff_isPathConnected` (Topology/Connected/LocallyPathConnected.lean);
`isConnected_compl_singleton_of_one_lt_rank` (Analysis/Normed/Module/Connected.lean; found by rg, the scratch
file lacked the import); `AddCircle.homeomorphCircle` (Analysis/SpecialFunctions/Complex/Circle.lean);
`UpperHalfPlane.dist_eq`, `UpperHalfPlane.glAction` (Analysis/Complex/UpperHalfPlane/{Metric,MoebiusAction}.lean);
`Order.iso_of_countable_dense` (Order/CountableDenseLinearOrder.lean; only needed for the fallback of risk 3).
Not found / absent: a planar winding number, invariance of domain, a θ-curve lemma, a complete Riemann mapping
theorem, a topological group structure on homeomorphism or isometry groups, any classification of
`PSL(2,ℝ)` or of hyperbolic planes.

Repository: `Appendix.jordanCurveTheorem` (JordanCurveClose.lean); `JordanCurve.Brouwer.brouwerFPT`,
`JordanCurve.crossing`, `JordanCurve.arc_not_separates`, `JordanCurve.jordan_curve` (JordanPick/);
`trueCircle_closed`, `trueCircle_mapsTo`, `trueCircle_transitive`, `specialCaseRotSeg_of_axiomIII`,
`specialCaseSeg_of_axiomIII`, `specialCaseRotPt_of_axiomIII`, `isJordanRegion_ball`, `circleCurve`,
`circleCurve_isClosedJordanCurve`, `range_circleCurve` (Commentary.lean); `not_appendixMainTheorem`,
`AppendixMainTheoremNonempty`, `atMostOneMiddle_of_twoFixedPoints`, `mob`, `mobPerm`, `rotPerm`,
`norm_mob_lt`, `mob_neg_mob` (CommentaryCloseAux7.lean); `steps_of_main` (CommentaryClose.lean).
