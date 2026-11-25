import HilbertFoundations.Analytic
import HilbertFoundations.Order
import HilbertFoundations.IndependenceAux
import HilbertFoundations.IndependenceAux2
import HilbertFoundations.IndependenceAux3

/-!
# Independence of the axioms (§§ 10–12)

Sections of Hilbert's text covered here (full text in `data/foundations.json`):

* § 10. Independence of the axioms of parallels. Non-euclidean geometry
* § 11. Independence of the axioms of congruence
* § 12. Independence of the axiom of continuity. Non-archimedean geometry

## The three models

* **§ 10, the first assertion of III** (helper module `HilbertFoundations/IndependenceAux2.lean`,
  namespace `ParallelExists`): proved from groups I, II, IV, with Theorems 10 and 12 proved there;
  the space version (in every plane of a geometry of space) in the helper module
  `HilbertFoundations/IndependenceAux3.lean`, through the restriction of the congruences of space
  to a plane (`planeCongruence`).
* **§ 10, the non-euclidean geometry** (helper module `HilbertFoundations/IndependenceAux.lean`,
  namespace `Klein`): the interior of the unit sphere of `ℝ³` (the projective model of Beltrami,
  Cayley and Klein). Points `Klein.KPt 3`, lines `Klein.KLine 3`, planes `Klein.KPlane 3` (the
  lines and planes of `ℝ³` meeting the ball), betweenness of `ℝ³`, congruence of segments by the
  projective invariant `Klein.ch` (the hyperbolic cosine of the Cayley–Klein distance), congruence
  of angles by `Klein.kcos` (the cosine of the Cayley–Klein angle). Groups I, II, IV and V hold,
  the second assertion of III fails.
* **§ 11** (`SkewPt K`): ordinary space `K³` with ordinary angles but Hilbert's new lengths
  `√((x₁ - x₂ + y₁ - y₂)² + (y₁ - y₂)² + (z₁ - z₂)²)`. Groups I, II, III, IV 1–5 and V hold, IV 6
  and Theorem 10 fail.
* **§ 12** (`Coord OmegaT 3`): the coordinate geometry of § 9 over Hilbert's non-archimedean field
  `Ω(t)` (`OmegaT`, constructed in `AnalyticAux3.lean`). Groups I–IV hold, V fails.

Each model is an instance of exactly the classes Hilbert lists, and the excluded axiom is refuted
as a Lean statement about the model (`¬AxiomIIIUniqueSpace (Klein.KPt 3)`,
`¬AxiomIV6 (SkewPt K)`, `¬AxiomV (Coord OmegaT 3)`). The independence statements are
`axiomIIIUnique_independent`, `axiomIV6_independent`, `axiomV_independent`.
-/

namespace HilbertFoundations

open Module Coord AffPt Filter

/-! ## § 10. Independence of the axioms of parallels. Non-euclidean geometry -/

/-!
## [s10.mutual_independence] The axioms are mutually independent

*(§ 10)*

> Having shown that the axioms of the above system are not contradictory to one another, it is of interest to investigate the question of their mutual independence. In fact, it may be shown that none of them can be deduced from the remaining ones by any logical process of reasoning. First of all, so far as the particular axioms of groups I, II, and IV are concerned, it is easy to show that the axioms of these groups are each independent of the other of the same group.

**Lean reading.** Two claims: none of the axioms can be deduced from the others, and within each
of the groups I, II, IV each axiom is independent of the other axioms of its group. Both are false
as printed, because of axiom II 4: by E. H. Moore's theorem (1902; Order.lean, unit
`s3.II4_dependent`), II 4 follows from I 1–2, the two clauses of I 7 of plane geometry and II 1–3,
II 5 (with the presupposition `BetweenOnLine`). `axiomII4_dependent` restates it: every plane
geometry satisfying the other axioms of groups I and II satisfies II 4; so II 4 can be "deduced from
the remaining ones" of groups I, II. (In space Order.lean proves the same under the hypothesis that
a plane exists, `axiomII4_of_others_space`.) What remains true is proved for group I of plane
geometry: `groupI_plane_independent` gives, for each of the four plane axioms of group I (I 1, I 2,
the line clause of I 7, the existence of three non-collinear points), a finite incidence structure
(three points, `FinIncidence.Pt`, `FinIncidence.Ln`, given by an incidence table) in which it fails
and the other three hold. The other independence claims within groups I (space axioms I 3–7), II
and IV are not formalized here: Hilbert gives no argument in the text, only a reference to his
unpublished lectures (the translator's note on Schur and Moore makes no mathematical claim). What
§§ 10–12 actually prove is the independence of the second assertion of III, of IV 6 and of V
(units `s10.non_euclidean`, `s11.iv6_fails`, `s12.geometry`).

**Status.** proved (corrected)
-/

/-- **Axiom II 4 is not independent** of the other axioms of groups I and II (E. H. Moore): it
holds in every plane geometry satisfying I 1–2, I 7, II 1–3 and II 5. -/
theorem axiomII4_dependent :
    ∀ (P L : Type) [HasLines P L] [HasBetween P], PlaneConnection P L → BetweenOnLine P →
      AxiomII1 P → AxiomII2 P → AxiomII3 P → AxiomII5 P → AxiomII4 P :=
  fun _ _ _ _ _ hB h1 h2 h3 h5 => axiomII4_of_others hB h1 h2 h3 h5

namespace FinIncidence

/-- The points of a finite incidence structure with `n` points and `k` lines, given by its
incidence table `m` (`m a A`: the point `A` lies on the line `a`). -/
def Pt (n k : ℕ) (_m : Fin k → Fin n → Bool) : Type := Fin n

/-- The lines of the finite incidence structure. -/
def Ln (n k : ℕ) (_m : Fin k → Fin n → Bool) : Type := Fin k

variable {n k : ℕ} {m : Fin k → Fin n → Bool}

instance instHasLines : HasLines (Pt n k m) (Ln n k m) := ⟨fun A a => m a A = true⟩
instance : Fintype (Pt n k m) := inferInstanceAs (Fintype (Fin n))
instance : Fintype (Ln n k m) := inferInstanceAs (Fintype (Fin k))
instance : DecidableEq (Pt n k m) := inferInstanceAs (DecidableEq (Fin n))
instance : DecidableEq (Ln n k m) := inferInstanceAs (DecidableEq (Fin k))
instance (A : Pt n k m) (a : Ln n k m) : Decidable (A ∈ a) :=
  inferInstanceAs (Decidable (m a A = true))

/-- Three points `0, 1, 2`, one line `{0, 1}`. -/
def tblI1 : Fin 1 → Fin 3 → Bool := ![![true, true, false]]

/-- Three points, the lines `{0, 1}`, `{0, 1}` (two different lines), `{1, 2}`, `{0, 2}`. -/
def tblI2 : Fin 4 → Fin 3 → Bool :=
  ![![true, true, false], ![true, true, false], ![false, true, true], ![true, false, true]]

/-- Three points, the lines `{0, 1}`, `{1, 2}`, `{0, 2}`, `{0}`. -/
def tblI7 : Fin 4 → Fin 3 → Bool :=
  ![![true, true, false], ![false, true, true], ![true, false, true], ![true, false, false]]

/-- Three points on one line. -/
def tblNC : Fin 1 → Fin 3 → Bool := ![![true, true, true]]

end FinIncidence

open FinIncidence in
/-- **The four axioms of group I of plane geometry are independent of each other**: in each of the
four structures one of I 1, I 2, I 7 (line clause), I 7 (three non-collinear points) fails and the
other three hold. -/
theorem groupI_plane_independent :
    (¬AxiomI1 (Pt 3 1 tblI1) ∧ AxiomI2 (Pt 3 1 tblI1) ∧ AxiomI7Line (Pt 3 1 tblI1) ∧
      ExistsNoncollinear (Pt 3 1 tblI1)) ∧
    (AxiomI1 (Pt 3 4 tblI2) ∧ ¬AxiomI2 (Pt 3 4 tblI2) ∧ AxiomI7Line (Pt 3 4 tblI2) ∧
      ExistsNoncollinear (Pt 3 4 tblI2)) ∧
    (AxiomI1 (Pt 3 4 tblI7) ∧ AxiomI2 (Pt 3 4 tblI7) ∧ ¬AxiomI7Line (Pt 3 4 tblI7) ∧
      ExistsNoncollinear (Pt 3 4 tblI7)) ∧
    (AxiomI1 (Pt 3 1 tblNC) ∧ AxiomI2 (Pt 3 1 tblNC) ∧ AxiomI7Line (Pt 3 1 tblNC) ∧
      ¬ExistsNoncollinear (Pt 3 1 tblNC)) := by
  unfold AxiomI1 AxiomI2 AxiomI7Line ExistsNoncollinear Collinear
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals decide

/-!
## [s10.groups_III_IV_V] It suffices to treat groups III, IV and V

*(§ 10)*

> According to our presentation, the axioms of groups I and II form the basis of the remaining axioms. It is sufficient, therefore, to show that each of the groups II, IV, and V is independent of the others.

**Lean reading.** "Groups II, IV, and V" is a misprint (also in the LaTeX source) for "III, IV
and V": §§ 10–12 treat III, IV and V, and group II, presupposed by III–V, is never shown
independent. In the formalization the classes of groups III, IV, V extend those of groups I and II
(`PlaneParallels`, `SpaceParallels` extend the connection classes, `SegmentCongruence`,
`AngleCongruence`, `Archimedes` extend `LineOrder`), so only the independence of III, IV, V from
the others can even be formulated. Each is shown by a model in which one axiom (or assertion) of the
group fails and all other groups hold: the second assertion of III (`axiomIIIUnique_independent`),
IV 6 (`axiomIV6_independent`), V (`axiomV_independent`).

**Status.** remark
-/

/-!
## [s10.first_assertion] The first assertion of the axiom of parallels follows from I, II, IV

*(§ 10)*

> The first statement of the axiom of parallels can be demonstrated by aid of the axioms of groups I, II, and IV. In order to do this, join the given point $A$ with any arbitrary point $B$ of the straight line $a$. Let $C$ be any other point of the given straight line. At the point $A$ on $AB$, construct the angle $ABC$ so that it shall lie in the same plane $\alpha$ as the point $C$, but upon the opposite side of $AB$ from it. The straight line thus obtained through $A$ does not meet the give straight line $\alpha$; for, if it should cut it, say in the point $D$, and if we suppose $B$ to be situated between $C$ and $D$, we could then find on $\alpha$ a point $D'$ so situated that $B$ would lie between $D$ and $D'$, and, moreover, so that we should have \[ AD \equiv BD' \] Because of the congruence of the two triangles $ABD$ and $BAD'$, we have also \[ \angle ABD \equiv \angle BAD', \] and since the angles $ABD'$ and $ABD$ are supplementary, it follows from theorem 12 that the angles $BAD$ and $BAD'$ are also supplementary. This, however, cannot be true, as, by theorem 1, two straight lines cannot intersect in more than one point, which would be the case if $BAD$ and $BAD'$ were supplementary.

**Lean reading.** `firstAssertionOfParallels`: in every plane geometry satisfying groups I, II and
IV (`PlaneCongruence`; no axiom of group III or V), through a point `A` off a line `a` there is a
line not meeting `a` (`AxiomIIIExists`, the first assertion of III, unit `s5.two_assertions`). The
proof (`ParallelExists.axiomIIIExists`, helper module `IndependenceAux2.lean`) follows Hilbert: with
`B`, `C` on `a`, the angle `∠ABC` is laid off at `A` on the half-ray `AB` on the side of `AB`
opposite to `C` (IV 4), giving the line `AE`. If `AE` met `a` in `D` on the side of `E`, then `B`
lies between `C` and `D`; `D'` is laid off on the half-ray `BC` with `AD ≡ BD'` (IV 1); IV 6 for the
triangles `ABD`, `BAD'` gives `∠ABD ≡ ∠BAD'`; Theorem 12 (`ParallelExists.supplement`) gives that the
supplement of `∠BAD` is congruent to `∠ABD`, hence to `∠BAD'`, and the uniqueness in IV 4
(`ParallelExists.ray_eq_of_angCong`) puts `D'` on the prolongation of `DA`: the lines `AD` and `a`
would have the two points `D ≠ D'` in common (Theorem 1). Theorems 10 (third side,
`ParallelExists.segCong_of_sas`) and 12 are proved again in the helper module from IV 1–6, because
`Congruence.lean` is not imported. Findings: (1) Hilbert's argument covers only the case where `D`
lies on the half-ray `AE` ("if we suppose `B` to be situated between `C` and `D`"); if `D` lies on
the other half-ray (on the side of `C`), it does not apply as written. The proof here reduces that
case to the first one: with `C₂` beyond `B` on `a`, Theorem 12 gives `∠BAD ≡ ∠ABC₂`, and `C₂`, `D`
lie on different sides of `AB` (`ParallelExists.no_meet_core` is applied to `C₂`, `D`). (2) "The
give straight line `α`" is a misprint for "the given straight line `a`". (3) The congruence of the
triangles `ABD`, `BAD'` is used only for the angles, i.e. IV 6 itself suffices there. Hilbert states
the claim for a plane `α` of a geometry of space. The space version is `firstAssertionOfParallelsSpace`:
in every geometry of space satisfying groups I, II, IV (`SpaceCongruence`), for every plane `α`,
line `a` of `α` and point `A` of `α` off `a`, some line of `α` through `A` does not meet `a`. It is
derived from the plane theorem through the restriction of the space congruences to the plane `α`
(helper module `IndependenceAux3.lean`: `planeCongruence α`, groups I, II, IV of plane geometry
hold in every plane of a geometry of space satisfying I, II, IV; `ParallelExists.axiomIIIExistsSpace`).

**Status.** proved
-/

/-- **The first assertion of the axiom of parallels follows from groups I, II, IV** (plane
geometry). -/
def FirstAssertionOfParallels : Prop :=
  ∀ (P L : Type) [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P],
    PlaneCongruence P L → AxiomIIIExists P

theorem firstAssertionOfParallels : FirstAssertionOfParallels :=
  fun P L _ _ _ _ h => ParallelExists.axiomIIIExists (P := P) (L := L) (hG := h)

/-- **The first assertion of the axiom of parallels follows from groups I, II, IV** (space
geometry, in every plane `α`). -/
def FirstAssertionOfParallelsSpace : Prop :=
  ∀ (P L Pl : Type) [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P] [HasAngCong P],
    SpaceCongruence P L Pl → ∀ (α : Pl) (a : L) (A : P), LiesInPlane (Point := P) a α → A ∈ α →
      A ∉ a → ∃ b : L, LiesInPlane (Point := P) b α ∧ A ∈ b ∧ ¬Meets (Point := P) b a

theorem firstAssertionOfParallelsSpace : FirstAssertionOfParallelsSpace :=
  fun P L _ _ _ _ _ _ h => ParallelExists.axiomIIIExistsSpace (P := P) (L := L) (h := h)

/-!
## [s10.non_euclidean] The non-euclidean geometry: the second assertion of III is independent

*(§ 10)*

> The second statement of the axiom of parallels is independent of all the other axioms. This may be most easily shown in the following well known manner. As the individual elements of a geometry of space, select the points, straight lines, and planes of the ordinary geometry as constructed in § 9, and regard these elements as restricted in extent to the interior of a fixed sphere. Then, define the congruences of this geometry by aid of such linear transformations of the ordinary geometry as transform the fixed sphere into itself. By suitable conventions, we can make this “*non-euclidean geometry*” obey all of the axioms of our system except the axiom of Euclid (group III).

**Lean reading.** The model (helper module `IndependenceAux.lean`, namespace `Klein`) is built over
`ℝ`, the ordinary geometry of `s9.reals`: points `Klein.KPt 3` are the points `p` of `ℝ³` with
`|p|² < 1`, lines and planes are the lines and planes of `ℝ³` having a point inside the sphere,
incidence and betweenness are those of `ℝ³`. Congruence is defined by the two invariants of the
projective transformations that map the sphere onto itself: segments `AB ≡ A'B'` iff
`Klein.ch A B = Klein.ch A' B'`, where `ch p q = (1 - ⟪p, q⟫)/(√(1 - |p|²) √(1 - |q|²))` (the
hyperbolic cosine of the Cayley–Klein distance, a function of the cross-ratio of `p`, `q` and the
ends of their chord); angles `∠AOB ≡ ∠A'O'B'` iff `Klein.kcos A O B = Klein.kcos A' O' B'`, the
cosine of the angle for the Cayley–Klein form `G_O u v = (1 - |O|²) ⟪u, v⟫ + ⟪O, u⟫ ⟪O, v⟫`
(`Klein.kcos_eq_ch`: it is the hyperbolic law of cosines in terms of `ch`). These are Hilbert's
"suitable conventions", and they are exactly congruence "by aid of" the transformations: the
motions `Klein.IsMotion` are the composites of the boosts `Klein.boost s` (the projective maps
`(x : y : z : w) ↦ (c x + s w : y : z : s x + c w)`, `c = √(1 + s²)`, which preserve
`x² + y² + z² - w²` and so map the sphere onto itself) and the reflections `Klein.refl m` in planes
through the centre; they preserve both invariants (`Klein.IsMotion.ch_eq`,
`Klein.IsMotion.kcos_eq`), every point can be moved to the centre
(`Klein.exists_motion_to_centre`), and `Klein.segCong_iff_motion`: `AB ≡ A'B'` iff a motion maps
`A`, `B` to `A'`, `B'`; `Klein.angCong_iff_motion`: `∠AOB ≡ ∠A'O'B'` iff a motion maps `O` to `O'`
and `A`, `B` to points of the sides `O'A'`, `O'B'`. Not formalized: that every projective
transformation of the sphere into itself is such a composite, and that motions preserve
betweenness (both classical; the equivalences above do not need them). Proved
(`nonEuclidean_model`): groups I (`Klein.instSpaceConnection`), II (`Klein.instSpaceOrder`), IV
(`Klein.instSpaceCongruence`: IV 1 by an explicit construction and the monotonicity of `ch` along
rays, IV 3 by the addition formula `Klein.ch_add`, IV 4 by laying off the angle with the form
`G_O` in each plane, IV 6 by the law of cosines) and V (`Klein.instArchimedes`: `ch` grows at least
geometrically along a chain of congruent segments, `Klein.mul_ch_le_of_between`), while the second
assertion of III fails (`Klein.exists_two_parallels`: two lines through `(0, ½, 0)` in the plane
`z = 0` not meeting the line `y = z = 0`), so `¬AxiomIIIUniqueSpace` and `¬AxiomIIISpace`; the
first assertion of III holds, as it must (`nonEuclidean_axiomIIIExists`, from unit
`s10.first_assertion`), so the model obeys "all of the axioms of our system except" the second
assertion of III, and `nonEuclidean_has_plane` checks that it is a genuine geometry of space.
Departure: Hilbert takes "the ordinary geometry as constructed in § 9", i.e. over his countable
field `Ω`. Over `Ω` the model does not work: laying off segments needs square roots that are not
sums of squares (laid off from the centre, a segment congruent to the one joining `(a, 0, 0)` and
`(0, a, 0)` ends at euclidean distance `√(2a² - a⁴)` from the centre, since its invariant is
`ch = 1/(1 - a²)`; for `a = √2 - 1 ∈ Ω` the radicand `2a² - a⁴ = 8√2 - 11` has the negative
conjugate `-8√2 - 11`, so it is not a square in `Ω`, whose elements are totally real). This failure over `Ω` is a remark, not proved here; § 9 itself allows `ℝ` ("we should have
obtained likewise a geometry …"), which is used.

**Status.** proved (reading)
-/

/-- **The non-euclidean geometry** satisfies groups I, II, IV and V of space geometry, and not
the second assertion of the axiom of parallels (nor, hence, axiom III). -/
theorem nonEuclidean_model :
    SpaceOrder (Klein.KPt 3) (Klein.KLine 3) (Klein.KPlane 3) ∧
      SpaceCongruence (Klein.KPt 3) (Klein.KLine 3) (Klein.KPlane 3) ∧
      Archimedes (Klein.KPt 3) (Klein.KLine 3) ∧
      ¬AxiomIIIUniqueSpace (L := Klein.KLine 3) (Pl := Klein.KPlane 3) (Klein.KPt 3) ∧
      ¬AxiomIIISpace (Klein.KPt 3) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, Klein.not_axiomIIISpace⟩
  intro h
  obtain ⟨α, a, A, b₁, b₂, hai, hAα, hAa, hne, hb₁, hb₂⟩ := Klein.exists_two_parallels
  exact hne (h α a A hai hAα hAa b₁ b₂ hb₁.1 hb₁.2.1 hb₁.2.2 hb₂.1 hb₂.2.1 hb₂.2.2)

/-- **The second assertion of the axiom of parallels is independent** of groups I, II, IV, V. -/
theorem axiomIIIUnique_independent :
    ∃ (P L Pl : Type) (_ : HasLines P L) (_ : HasPlanes P Pl) (_ : HasBetween P)
      (_ : HasSegCong P) (_ : HasAngCong P),
      SpaceOrder P L Pl ∧ SpaceCongruence P L Pl ∧ Archimedes P L ∧
        ¬AxiomIIIUniqueSpace (L := L) (Pl := Pl) P :=
  ⟨Klein.KPt 3, Klein.KLine 3, Klein.KPlane 3, _, _, _, _, _, nonEuclidean_model.1,
    nonEuclidean_model.2.1, nonEuclidean_model.2.2.1, nonEuclidean_model.2.2.2.1⟩

/-- The model is a genuine geometry of space: it has a plane with three non-collinear points. -/
theorem nonEuclidean_has_plane :
    ∃ (α : Klein.KPlane 3) (A B C : Klein.KPt 3), A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ ¬Collinear A B C :=
  let ⟨α, _, _, _, _, _, _, _, _, _⟩ := Klein.exists_two_parallels
  ⟨α, SpaceConnection.ax_I7_plane (Point := Klein.KPt 3) (Line := Klein.KLine 3) α⟩

/-- In the non-euclidean geometry **the first assertion of III holds** (by
`firstAssertionOfParallelsSpace`): of the axiom of Euclid only the second assertion fails. -/
theorem nonEuclidean_axiomIIIExists (α : Klein.KPlane 3) (a : Klein.KLine 3) (A : Klein.KPt 3)
    (ha : LiesInPlane (Point := Klein.KPt 3) a α) (hAα : A ∈ α) (hAa : A ∉ a) :
    ∃ b : Klein.KLine 3, LiesInPlane (Point := Klein.KPt 3) b α ∧ A ∈ b ∧
      ¬Meets (Point := Klein.KPt 3) b a :=
  ParallelExists.axiomIIIExistsSpace α a A ha hAα hAa

/-!
## [s10.consistency] The non-euclidean geometry is consistent

*(§ 10)*

> Since the possibility of the ordinary geometry has already been established, that of the non-euclidean geometry is now an immediate consequence of the above considerations.

**Lean reading.** As in unit `s9.consistency`, consistency is read semantically:
`NonEuclideanConsistent` says that not every system satisfying groups I, II, IV, V and the negation
of the second assertion of III (in space) is impossible. `nonEuclidean_consistent` proves it with
the model of `s10.non_euclidean`, built inside the ordinary geometry `ℝ³` (`s9.reals`); the
consistency of `ℝ` (Lean's background) plays the role of "the possibility of the ordinary
geometry".

**Status.** proved (reading)
-/

/-- **Non-euclidean geometry is not contradictory.** -/
def NonEuclideanConsistent : Prop :=
  ¬∀ (P L Pl : Type) [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P], SpaceOrder P L Pl → SpaceCongruence P L Pl → Archimedes P L →
      ¬AxiomIIIUniqueSpace (L := L) (Pl := Pl) P → False

theorem nonEuclidean_consistent : NonEuclideanConsistent :=
  fun h => h (Klein.KPt 3) (Klein.KLine 3) (Klein.KPlane 3) nonEuclidean_model.1
    nonEuclidean_model.2.1 nonEuclidean_model.2.2.1 nonEuclidean_model.2.2.2.1

/-! ## § 11. Independence of the axioms of congruence -/

/-!
## [s11.iv6_or_theorem10] IV 6, or Theorem 10, is not a consequence of the other axioms

*(§ 11)*

> We shall show the independence of the axioms of congruence by demonstrating that axiom IV, 6, or what amounts to the same thing, that the first theorem of congruence for triangles (theorem 10) cannot be deduced from the remaining axioms I, II, III, IV 1–5, V by any logical process of reasoning.

**Lean reading.** `FirstCongruenceTheorem P` is Theorem 10 as a property of a geometry: if
`AB ≡ A'B'`, `AC ≡ A'C'` and `∠A ≡ ∠A'` for two triangles, they are congruent (the third sides and
the two other angles are congruent; § 7 defines congruent triangles by all six congruences).
"What amounts to the same thing": Theorem 10 contains IV 6 (`axiomIV6_of_firstCongruenceTheorem`,
for any structure), and conversely Theorem 10 is derived from IV 1–6 in § 7 (unit `th.10` of
Congruence.lean; re-proved here for plane geometry as `firstCongruenceTheorem_of_planeCongruence`,
from the third-side argument `ParallelExists.segCong_of_sas` of the helper module).
`axiomIV6_iff_firstCongruenceTheorem`: given groups I, II and IV 1–5 of plane geometry, IV 6 and
Theorem 10 are equivalent. (Tacit assumption: the geometry has two distinct points; in a one-point
structure every axiom holds vacuously while the degenerate "triangle" `AAA` can violate Theorem 10,
since `IsTriangle` alone does not make the vertices distinct, cf. `ne_of_isTriangle`.) The independence claims themselves are
`axiomIV6_independent` (unit `s11.iv6_fails`): a geometry of space satisfying I, II, III, IV 1–5
and V in which both IV 6 and Theorem 10 fail.

**Status.** proved (reading)
-/

/-- **The first theorem of congruence for triangles** (Theorem 10) as a property of a geometry. -/
def FirstCongruenceTheorem (P : Type*) {L : Type*} [HasLines P L] [HasSegCong P] [HasAngCong P] :
    Prop :=
  ∀ A B C A' B' C' : P, IsTriangle A B C → IsTriangle A' B' C' →
    SegCong A B A' B' → SegCong A C A' C' → AngCong B A C B' A' C' →
    SegCong B C B' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B'

/-- Theorem 10 contains axiom IV 6. -/
theorem axiomIV6_of_firstCongruenceTheorem {P : Type*} {L : Type*} [HasLines P L] [HasSegCong P]
    [HasAngCong P] (h : FirstCongruenceTheorem P) : AxiomIV6 P :=
  fun A B C A' B' C' h1 h2 h3 h4 h5 => (h A B C A' B' C' h1 h2 h3 h4 h5).2

/-- In a geometry with two distinct points, the vertices of a triangle are distinct (in a
one-point structure without lines `¬Collinear A A A` holds). -/
theorem ne_of_isTriangle {P : Type*} {L : Type*} [HasLines P L] [Connection P L]
    (hP : ∃ X Y : P, X ≠ Y) {A B C : P} (h : IsTriangle A B C) : A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  have hline : ∀ Z : P, ∃ g : L, Z ∈ g := by
    obtain ⟨X, Y, hXY⟩ := hP
    intro Z
    by_cases hZX : Z = X
    · subst hZX; obtain ⟨g, h1, -⟩ := exists_line (Line := L) hXY; exact ⟨g, h1⟩
    · obtain ⟨g, h1, -⟩ := exists_line (Line := L) hZX; exact ⟨g, h1⟩
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · subst e
    by_cases hAC : A = C
    · subst hAC; obtain ⟨g, hg⟩ := hline A; exact h ⟨g, hg, hg, hg⟩
    · obtain ⟨g, h1, h2⟩ := exists_line (Line := L) hAC; exact h ⟨g, h1, h1, h2⟩
  · subst e
    by_cases hAB : A = B
    · subst hAB; obtain ⟨g, hg⟩ := hline A; exact h ⟨g, hg, hg, hg⟩
    · obtain ⟨g, h1, h2⟩ := exists_line (Line := L) hAB; exact h ⟨g, h1, h2, h1⟩
  · subst e
    by_cases hAB : A = B
    · subst hAB; obtain ⟨g, hg⟩ := hline A; exact h ⟨g, hg, hg, hg⟩
    · obtain ⟨g, h1, h2⟩ := exists_line (Line := L) hAB; exact h ⟨g, h1, h2, h2⟩

/-- **Theorem 10 follows from groups I, II, IV** (plane geometry, at least two points), by the
proof of § 7 (`ParallelExists.segCong_of_sas` for the third side, IV 6 for the angles). -/
theorem firstCongruenceTheorem_of_planeCongruence {P : Type*} {L : Type*} [HasLines P L]
    [HasBetween P] [HasSegCong P] [HasAngCong P] [hG : PlaneCongruence P L]
    (hP : ∃ X Y : P, X ≠ Y) : FirstCongruenceTheorem P := by
  intro A B C A' B' C' h h' h1 h2 h3
  obtain ⟨-, -, hBC⟩ := ne_of_isTriangle (L := L) hP h
  obtain ⟨hA'B', -, hB'C'⟩ := ne_of_isTriangle (L := L) hP h'
  exact ⟨ParallelExists.segCong_of_sas (L := L) h h' hBC hA'B' hB'C' h1 h2 h3,
    TriangleCongruence.ax_IV6 (Line := L) A B C A' B' C' h h' h1 h2 h3⟩

/-- **IV 6 "amounts to the same thing" as Theorem 10**: in a plane geometry satisfying groups I,
II and IV 1–5 (with at least two points), IV 6 holds iff Theorem 10 holds. -/
theorem axiomIV6_iff_firstCongruenceTheorem {P : Type*} {L : Type*} [HasLines P L] [HasBetween P]
    [HasSegCong P] [HasAngCong P] [hA : PlaneAngleCongruence P L] [hS : SegmentCongruence P L]
    (hP : ∃ X Y : P, X ≠ Y) : AxiomIV6 P ↔ FirstCongruenceTheorem P := by
  refine ⟨fun h6 => ?_, axiomIV6_of_firstCongruenceTheorem⟩
  have hG : PlaneCongruence P L := { hA, hS with ax_IV6 := h6 }
  exact firstCongruenceTheorem_of_planeCongruence (L := L) hP

/-!
## [s11.model] The geometry of § 11: a new congruence of segments

*(§ 11)*

> Select, as the points, straight lines, and planes of our new geometry of space, the points, straight lines, and planes of ordinary geometry, and define the laying off of an angle as in ordinary geometry, for example, as explained in § 9. We will, however, define the laying off of segments in another manner. Let $A_1$, $A_2$ be two points which, in ordinary geometry, have the co-ordinates $x_1$, $y_1$, $z_1$ and $x_2$, $y_2$, $z_2$, respectively. We will now define the length of the segment $A_1 A_2$ as the positive value of the expression \[ \sqrt{(x_1-x_2+y_1-y_2)^2 + (y_1-y_2)^2 + (z_1-z_2)^2} \] and call the two segments $A_1A_2$ and $A'_1A'_2$ congruent when they have equal lengths in the sense just defined.

**Lean reading.** `SkewPt K` is ordinary space `K³` (a type synonym of `Coord K 3`) with the lines,
planes, betweenness and congruence of angles of the coordinate geometry of § 9
(`Coord.instHasAngCong`: equal cosines), over any ordered field `K`. The new congruence of segments
(`SkewPt.instHasSegCong`) compares Hilbert's squared lengths
`skewQ (A₂ - A₁) = (x₁ - x₂ + y₁ - y₂)² + (y₁ - y₂)² + (z₁ - z₂)²`: positive square roots of
positive numbers are equal iff the numbers are, so this is "equal lengths" without square roots.
Over `ℝ` the lengths themselves are `skewLength`, and `SkewPt.segCong_iff_length` shows that
congruence is equality of lengths, as Hilbert defines it. (`skewQ v = |T v|²` for the linear map
`T (x, y, z) = (x + y, y, z)`, so the new lengths are the euclidean lengths of the images under `T`;
angles are not transformed, which is why IV 6 fails.)

**Status.** definition
-/

/-- Hilbert's **squared length** in the geometry of § 11, for the vector `v = A₁ - A₂`:
`(x + y)² + y² + z²`. -/
def skewQ {K : Type*} [Field K] (v : Coord K 3) : K :=
  (AffPt.toV v 0 + AffPt.toV v 1) ^ 2 + AffPt.toV v 1 ^ 2 + AffPt.toV v 2 ^ 2

@[simp] theorem skewQ_pt3 {K : Type*} [Field K] (x y z : K) :
    skewQ (pt3 x y z) = (x + y) ^ 2 + y ^ 2 + z ^ 2 := rfl

/-- **The points of the geometry of § 11**: the points of ordinary space `K³`. -/
def SkewPt (K : Type*) : Type _ := Coord K 3

namespace SkewPt

variable {K : Type*}

/-- The point of ordinary space. -/
def toC (A : SkewPt K) : Coord K 3 := A

/-- The point `(x, y, z)`. -/
def mk (x y z : K) : SkewPt K := pt3 x y z

@[simp] theorem toC_mk (x y z : K) : toC (mk x y z) = pt3 x y z := rfl

variable [Field K] [LinearOrder K]

instance instHasLines : HasLines (SkewPt K) (CoordLine K 3) :=
  inferInstanceAs (HasLines (Coord K 3) (CoordLine K 3))
instance instHasPlanes : HasPlanes (SkewPt K) (CoordPlane K 3) :=
  inferInstanceAs (HasPlanes (Coord K 3) (CoordPlane K 3))
instance instHasBetween : HasBetween (SkewPt K) := inferInstanceAs (HasBetween (Coord K 3))
/-- Congruence of angles: as in ordinary geometry. -/
instance instHasAngCong : HasAngCong (SkewPt K) := inferInstanceAs (HasAngCong (Coord K 3))
/-- **Hilbert's congruence of segments** (§ 11): equal values of `skewQ`. -/
instance instHasSegCong : HasSegCong (SkewPt K) :=
  ⟨fun A B A' B' => skewQ (toC B - toC A) = skewQ (toC B' - toC A')⟩

omit [LinearOrder K] in
theorem segCong_iff {A B A' B' : SkewPt K} :
    SegCong A B A' B' ↔ skewQ (toC B - toC A) = skewQ (toC B' - toC A') := Iff.rfl

theorem angCong_iff {A O B A' O' B' : SkewPt K} :
    AngCong A O B A' O' B' ↔ AngCong (toC A) (toC O) (toC B) (toC A') (toC O') (toC B') := Iff.rfl

omit [LinearOrder K] in
theorem collinear_iff {A B C : SkewPt K} : Collinear A B C ↔ Collinear (toC A) (toC B) (toC C) :=
  Iff.rfl

end SkewPt

/-- Hilbert's **length** of the segment `A₁A₂` (over `ℝ`):
`√((x₁ - x₂ + y₁ - y₂)² + (y₁ - y₂)² + (z₁ - z₂)²)`. -/
noncomputable def skewLength (A₁ A₂ : Coord ℝ 3) : ℝ := Real.sqrt (skewQ (A₁ - A₂))

section QNorm

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- A **quadratic length** on `K^n`: homogeneous of degree two, positive off `0`, and a sum of
squares (so that it has square roots in a Pythagorean field). -/
structure IsQNorm (Q : Coord K n → K) : Prop where
  smul : ∀ (c : K) (v : Coord K n), Q (c • v) = c ^ 2 * Q v
  pos : ∀ v : Coord K n, v ≠ 0 → 0 < Q v
  sumSq : ∀ v : Coord K n, IsSumSq (Q v)

namespace IsQNorm

variable {Q : Coord K n → K} (hQ : IsQNorm Q)
include hQ

omit [IsStrictOrderedRing K] in
theorem neg (v : Coord K n) : Q (-v) = Q v := by
  have := hQ.smul (-1) v
  rwa [neg_one_smul, neg_one_sq, one_mul] at this

omit [IsStrictOrderedRing K] in
theorem sub_swap (X Y : Coord K n) : Q (X - Y) = Q (Y - X) := by
  rw [← neg_sub Y X, hQ.neg]

end IsQNorm

end QNorm

theorem isQNorm_skewQ {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsQNorm (skewQ (K := K)) where
  smul c v := by simp only [skewQ, AffPt.toV_smul, Pi.smul_apply, smul_eq_mul]; ring
  pos v hv := by
    have hnn : 0 ≤ skewQ v := by unfold skewQ; positivity
    refine lt_of_le_of_ne hnn (fun h => hv ?_)
    unfold skewQ at h
    have h2 : AffPt.toV v 2 = 0 := by
      nlinarith [sq_nonneg (AffPt.toV v 0 + AffPt.toV v 1), sq_nonneg (AffPt.toV v 1),
        sq_nonneg (AffPt.toV v 2)]
    have h1 : AffPt.toV v 1 = 0 := by
      nlinarith [sq_nonneg (AffPt.toV v 0 + AffPt.toV v 1), sq_nonneg (AffPt.toV v 1),
        sq_nonneg (AffPt.toV v 2)]
    have h01 : AffPt.toV v 0 + AffPt.toV v 1 = 0 := by
      nlinarith [sq_nonneg (AffPt.toV v 0 + AffPt.toV v 1), sq_nonneg (AffPt.toV v 1),
        sq_nonneg (AffPt.toV v 2)]
    rw [h1, add_zero] at h01
    exact pt3_ext (by rw [h01]; rfl) (by rw [h1]; rfl) (by rw [h2]; rfl)
  sumSq v := by
    unfold skewQ
    simp only [sq]
    exact ((IsSumSq.mul_self _).add (IsSumSq.mul_self _)).add (IsSumSq.mul_self _)

/-- Two segments are congruent iff they have equal lengths (over `ℝ`). -/
theorem SkewPt.segCong_iff_length {A B A' B' : SkewPt ℝ} :
    SegCong A B A' B' ↔ skewLength (toC A) (toC B) = skewLength (toC A') (toC B') := by
  rw [segCong_iff, skewLength, skewLength, isQNorm_skewQ.sub_swap (toC A),
    isQNorm_skewQ.sub_swap (toC A'), Real.sqrt_inj (isQNorm_skewQ.sumSq _).nonneg
      (isQNorm_skewQ.sumSq _).nonneg]

/-!
## [s11.axioms_hold] Axioms I, II, III, IV 1–2, 4–5 and V hold

*(§ 11)*

> It is at once evident that, in the geometry of space thus defined, the axioms I, II, III, IV 1–2, 4–5, V are all fulfilled.

**Lean reading.** Over a Pythagorean ordered field `K` (an archimedean one for V; Hilbert's
ordinary geometry is over `Ω` or `ℝ`): groups I, II, III and IV 4–5 are those of the coordinate
geometry (`SkewPt.instSpaceOrder`, `SkewPt.instSpaceParallels`, `SkewPt.instSpaceAngleCongruence`,
transferred from § 9 since nothing but the congruence of segments changes). IV 1 (laying off),
IV 2 and V are proved for any quadratic length `Q` (`IsQNorm`: `Q (c v) = c² Q v`, `Q > 0` off `0`,
`Q` a sum of squares) by the arguments of § 9 with `Q` in place of the euclidean square length
(`IsQNorm.layOff`, `IsQNorm.archimedes`), and `skewQ` is such a length (`isQNorm_skewQ`). IV 1 needs
the square root of the sum of squares `Q (B - A) · Q (C' - A')` (Pythagorean field), V the
archimedean property of `K`. "At once evident" is fair for I–III and IV 4–5; IV 1 and V need these
short arguments. The unit `s11.iv3` adds IV 3.

**Status.** proved
-/

namespace IsQNorm

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
  {Q : Coord K n → K} (hQ : IsQNorm Q)
include hQ

/-- **Laying off segments** (IV 1) for the congruence `Q (B - A) = Q (B' - A')`. -/
theorem layOff [IsPythagorean K] (A B A' C' : Coord K n) (hAB : A ≠ B) (hC' : A' ≠ C') :
    ∃! B' : Coord K n, SameSidePt A' C' B' ∧ Q (B - A) = Q (B' - A') := by
  have hd : C' - A' ≠ 0 := sub_ne_zero.2 hC'.symm
  set d := C' - A'
  set s := Q (B - A)
  set E := Q d
  have hs : 0 < s := hQ.pos _ (sub_ne_zero.2 hAB.symm)
  have hE : 0 < E := hQ.pos _ hd
  obtain ⟨r, hr0, hr⟩ :=
    IsPythagorean.exists_sqrt_of_isSumSq ((hQ.sumSq (B - A)).mul (hQ.sumSq d))
  have hrpos : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h] at hr; exfalso
      have : 0 < s * E := mul_pos hs hE
      rw [← hr] at this; simp at this
    · exact h
  set l := r / E
  have hl : 0 < l := div_pos hrpos hE
  have hl2 : l ^ 2 * E = s := by
    simp only [l]; field_simp; rw [hr]; ring
  refine ⟨l • d + A', ⟨(mem_ray_iff hC'.symm).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
  · show s = Q (l • d + A' - A')
    rw [add_sub_cancel_right, hQ.smul, hl2]
  · rintro y ⟨hy, hys⟩
    obtain ⟨m, hm, rfl⟩ := (mem_ray_iff hC'.symm).1 hy
    rw [add_sub_cancel_right, hQ.smul] at hys
    have : m = l := by
      have hsq : m ^ 2 = l ^ 2 := by
        apply mul_right_cancel₀ hE.ne'
        rw [hl2, ← hys]
      exact (pow_left_inj₀ hm.le hl.le two_ne_zero).1 hsq
    rw [this]

/-- **Archimedes's axiom** for the congruence `Q (B - A) = Q (B' - A')`. -/
theorem archimedes [Archimedean K] :
    ArchimedesWith (Coord K n) (fun A B A' B' => Q (B - A) = Q (B' - A')) := by
  intro P B h01 hstep hcong
  have hP01 : P 0 ≠ P 1 := ne12_of_between (Line := CoordLine K n) h01
  set d := P 1 - P 0 with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hP01.symm
  have hdiff : ∀ k : ℕ, P (k + 1) - P k = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show P (k + 2) - P (k + 1) = d
      obtain ⟨hne, t, ht0, ht1, ht⟩ := sbtw_iff_param.1 (hstep k)
      have hc : Q (P (k + 2) - P (k + 1)) = Q (P (k + 1) - P k) := (hcong k (k + 1)).symm
      have hu0 : P (k + 1) - P k ≠ 0 := by rw [ih]; exact hd0
      have hu : P (k + 1) - P k = t • ((P (k + 2) - P (k + 1)) + (P (k + 1) - P k)) := by
        rw [sub_add_sub_cancel]; rw [ht]; abel
      have hw : P (k + 2) - P (k + 1) = ((1 - t) / t) • (P (k + 1) - P k) := by
        have e : t • (P (k + 2) - P (k + 1)) = (1 - t) • (P (k + 1) - P k) := by
          calc t • (P (k + 2) - P (k + 1))
              = t • ((P (k + 2) - P (k + 1)) + (P (k + 1) - P k)) - t • (P (k + 1) - P k) := by
                rw [smul_add]; abel
            _ = (P (k + 1) - P k) - t • (P (k + 1) - P k) := by rw [← hu]
            _ = (1 - t) • (P (k + 1) - P k) := by rw [sub_smul, one_smul]
        rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← e, smul_smul, inv_mul_cancel₀ ht0.ne',
          one_smul]
      rw [hw, hQ.smul] at hc
      have hq : ((1 - t) / t) ^ 2 = 1 := by
        apply mul_right_cancel₀ (hQ.pos _ hu0).ne'
        rw [hc, one_mul]
      have hq1 : (1 - t) / t = 1 :=
        (pow_left_inj₀ (div_pos (sub_pos.2 ht1) ht0).le zero_le_one two_ne_zero).1
          (by rw [hq, one_pow])
      rw [hw, hq1, one_smul, ih]
  have hpos : ∀ k : ℕ, P k = (k : K) • d + P 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show P (k + 1) = (P (k + 1) - P k) + P k by abel, hdiff k, ih, Nat.cast_succ, add_smul,
        one_smul]; abel
  obtain ⟨-, t, ht0, ht1, ht⟩ := sbtw_iff_param.1 h01
  have hB : B = t⁻¹ • d + P 0 := by
    have : d = t • (B - P 0) := by rw [hd, ht, add_sub_cancel_right]
    rw [this, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, sub_add_cancel]
  obtain ⟨N, hN⟩ := exists_nat_gt t⁻¹
  refine ⟨N, ?_⟩
  have key := (sbtw_param_iff hd0 (0 : K) t⁻¹ N (O := P 0)).2 (Or.inl ⟨inv_pos.2 ht0, hN⟩)
  rw [zero_smul, zero_add] at key
  rw [AffPt.between_iff, hB, hpos N]
  exact key

end IsQNorm

namespace SkewPt

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

instance instLineOrder : LineOrder (SkewPt K) (CoordLine K 3) :=
  inferInstanceAs (LineOrder (Coord K 3) (CoordLine K 3))

/-- **Groups I and II** (space). -/
instance instSpaceOrder : SpaceOrder (SkewPt K) (CoordLine K 3) (CoordPlane K 3) :=
  inferInstanceAs (SpaceOrder (Coord K 3) (CoordLine K 3) (CoordPlane K 3))

/-- **Group III** (space). -/
instance instSpaceParallels : SpaceParallels (SkewPt K) (CoordLine K 3) (CoordPlane K 3) :=
  inferInstanceAs (SpaceParallels (Coord K 3) (CoordLine K 3) (CoordPlane K 3))

/-- **Axioms IV 4–5** (congruence of angles as in ordinary geometry). -/
instance instSpaceAngleCongruence [IsPythagorean K] :
    SpaceAngleCongruence (SkewPt K) (CoordLine K 3) (CoordPlane K 3) :=
  inferInstanceAs (SpaceAngleCongruence (Coord K 3) (CoordLine K 3) (CoordPlane K 3))

/-- **Axiom IV 1** (laying off) for the new congruence of segments. -/
theorem axiomIV1LayOff [IsPythagorean K] : AxiomIV1LayOff (SkewPt K) :=
  fun A B A' C' hAB hC' => isQNorm_skewQ.layOff (toC A) (toC B) (toC A') (toC C') hAB hC'

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Axiom IV 2** for the new congruence of segments. -/
theorem axiomIV2 : AxiomIV2 (SkewPt K) :=
  fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2

/-- **Axiom V** holds for the new congruence of segments. -/
instance instArchimedes [Archimedean K] : Archimedes (SkewPt K) (CoordLine K 3) :=
  { instLineOrder with ax_V := isQNorm_skewQ.archimedes }

end SkewPt

/-!
## [s11.iv3] Axiom IV 3 holds

*(§ 11)*

> In order to show that axiom IV, 3 also holds, we select an arbitrary straight line $a$ and upon it three points $A_1$, $A_2$, $A_3$ so that $A_2$ shall lie between $A_1$ and $A_3$. Let the points $x$, $y$, $z$ of the straight line $a$ be given by means of the equations \begin{eqnarray*} x & = & \lambda t + \lambda', \\ y & = & \mu t + \mu', \\ z & = & \nu t + \nu', \end{eqnarray*} where $\lambda$, $\lambda'$, $\mu$, $\mu'$, $\nu$, $\nu'$ represent certain constants and $T$ is a parameter. If $t_1$, $t_2 (<t_1)$, $t_3 (<t_2)$ are the values of the parameter corresponding to the points $A_1$, $A_2$, $A_3$ we have as the lengths of the three segments $A_1A_2$ $A_2A_3$ and $A_1A_3$ respectively, the following values: \[ (t_1-t_2) \left| \sqrt{(\lambda + \mu)^2 + \mu^2 + \nu^2} \right| \] \[ (t_2-t_3) \left| \sqrt{(\lambda + \mu)^2 + \mu^2 + \nu^2} \right| \] \[ (t_1-t_3) \left| \sqrt{(\lambda + \mu)^2 + \mu^2 + \nu^2} \right| \] Consequently, the length of $A_1A_3$ is equal to the sum of the lengths of the segments $A_1A_2$ and $A_2A_3$. But this result is equivalent to the existence of axiom IV, 3.

**Lean reading.** Over `ℝ`, Hilbert's computation is `skewLength_param`: on the line
`x = λt + λ'`, `y = μt + μ'`, `z = νt + ν'` the segment between the parameters `t₂ ≤ t₁` has length
`(t₁ - t₂) √((λ + μ)² + μ² + ν²)`; `skewLength_add`: for `t₃ < t₂ < t₁` the length of `A₁A₃` is the
sum of the lengths of `A₁A₂` and `A₂A₃`. "Equivalent to the existence of axiom IV, 3" (i.e. its
validity): additivity of lengths along every line gives IV 3, since segments with no common point
but `B` are adjacent segments `AB`, `BC` with `B` between `A` and `C`
(`between_of_segmentsMeetOnlyAt`). The proof of IV 3 in Lean (`IsQNorm.iv3`, giving
`SkewPt.instSegmentCongruence`) works over any ordered field with squared lengths: if `B` divides
`AC` in the ratio `t : 1 - t` and `B'` divides `A'C'` in the ratio `t' : 1 - t'`, then
`t² Q = t'² Q'` and `(1 - t)² Q = (1 - t')² Q'` force `Q = Q'` (`iv3_algebra` of § 9). Misprints:
"`T` is a parameter" for `t`; the absolute value bars belong around `t₁ - t₂` (they are harmless
since `t₂ < t₁`).

**Status.** proved
-/

/-- **Axiom IV 3** for the congruence `Q (B - A) = Q (B' - A')`. -/
theorem IsQNorm.iv3 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
    {Q : Coord K n → K} (hQ : IsQNorm Q) (A B C A' B' C' : Coord K n)
    (h : SegmentsMeetOnlyAt A B C) (h' : SegmentsMeetOnlyAt A' B' C')
    (hAB : Q (B - A) = Q (B' - A')) (hBC : Q (C - B) = Q (C' - B')) : Q (C - A) = Q (C' - A') := by
  have hb := between_of_segmentsMeetOnlyAt (L := CoordLine K n) h
  have hb' := between_of_segmentsMeetOnlyAt (L := CoordLine K n) h'
  obtain ⟨hAC, t, ht0, ht1, hB⟩ := sbtw_iff_param.1 hb
  obtain ⟨hAC', t', ht0', ht1', hB'⟩ := sbtw_iff_param.1 hb'
  have e1 : B - A = t • (C - A) := by rw [hB, add_sub_cancel_right]
  have e2 : C - B = (1 - t) • (C - A) := by rw [hB, sub_smul, one_smul]; abel
  have e1' : B' - A' = t' • (C' - A') := by rw [hB', add_sub_cancel_right]
  have e2' : C' - B' = (1 - t') • (C' - A') := by rw [hB', sub_smul, one_smul]; abel
  rw [e1, e1', hQ.smul, hQ.smul] at hAB
  rw [e2, e2', hQ.smul, hQ.smul] at hBC
  have hs' : 0 < Q (C' - A') := hQ.pos _ (sub_ne_zero.2 hAC'.symm)
  exact iv3_algebra ht0 ht1 ht0' ht1' hs' hAB hBC

/-- **Axioms IV 1–3** hold for Hilbert's new congruence of segments. -/
instance SkewPt.instSegmentCongruence {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] : SegmentCongruence (SkewPt K) (CoordLine K 3) :=
  { SkewPt.instLineOrder with
    segCong_swap := fun A B A' B' h =>
      ⟨by rw [SkewPt.segCong_iff, isQNorm_skewQ.sub_swap]; exact h,
        by rw [SkewPt.segCong_iff, isQNorm_skewQ.sub_swap (SkewPt.toC A')]; exact h⟩
    ax_IV1 := SkewPt.axiomIV1LayOff
    ax_IV1_refl := fun _ _ _ => rfl
    ax_IV2 := SkewPt.axiomIV2
    ax_IV3 := fun A B C A' B' C' h h' h1 h2 =>
      isQNorm_skewQ.iv3 (SkewPt.toC A) (SkewPt.toC B) (SkewPt.toC C) (SkewPt.toC A')
        (SkewPt.toC B') (SkewPt.toC C') h h' h1 h2 }

/-- **Lengths along a line** (Hilbert's computation for IV 3). -/
theorem skewLength_param (l l' m m' k k' t₁ t₂ : ℝ) (h : t₂ ≤ t₁) :
    skewLength (t₁ • pt3 l m k + pt3 l' m' k') (t₂ • pt3 l m k + pt3 l' m' k') =
      (t₁ - t₂) * Real.sqrt ((l + m) ^ 2 + m ^ 2 + k ^ 2) := by
  rw [skewLength, add_sub_add_right_eq_sub, ← sub_smul, isQNorm_skewQ.smul, skewQ_pt3,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sub_nonneg.2 h)]

/-- **The length of `A₁A₃` is the sum of the lengths of `A₁A₂` and `A₂A₃`.** -/
theorem skewLength_add (l l' m m' k k' t₁ t₂ t₃ : ℝ) (h12 : t₂ < t₁) (h23 : t₃ < t₂) :
    skewLength (t₁ • pt3 l m k + pt3 l' m' k') (t₃ • pt3 l m k + pt3 l' m' k') =
      skewLength (t₁ • pt3 l m k + pt3 l' m' k') (t₂ • pt3 l m k + pt3 l' m' k') +
        skewLength (t₂ • pt3 l m k + pt3 l' m' k') (t₃ • pt3 l m k + pt3 l' m' k') := by
  rw [skewLength_param _ _ _ _ _ _ _ _ (h23.trans h12).le, skewLength_param _ _ _ _ _ _ _ _ h12.le,
    skewLength_param _ _ _ _ _ _ _ _ h23.le]
  ring

/-!
## [s11.theorem10_fails] Theorem 10 fails: Hilbert's example

*(§ 11)*

> Axiom IV, 6, or rather the first theorem of congruence for triangles, is not always fulfilled in this geometry. Consider, for example, in the plane $z = 0$, the four points \begin{tabular}{cccccc} $O$, & having& the& co-ordinates& $x=0$, & $y = 0$ \\ $A$, & “ & “ & “ & $x=1$, & $y=0$ \\ $B$, & “ & “ & “ & $x=0$, & $y=1$ \\ $C$, & “ & “ & “ & $x=\frac{1}{2}$, & $y=\frac{1}{2}$ \end{tabular} [Fig. 15] Then, in the right triangles $OAC$ and $OBC$, the angles at $C$ as also the adjacent sides $AC$ and $BC$ are respectively congruent; for, the side $OC$ is common to the two triangles and the sides $AC$ and $BC$ have the same length, namely, $\frac{1}{2}$. However, the third sides $OA$ and $OB$ have the lengths $1$ and $\sqrt{2}$, respectively, and are not, therefore, congruent.

**Lean reading.** The points (Fig. 15, reconstructed from the text: the unit square's corners
`O = (0, 0)`, `A = (1, 0)`, `B = (0, 1)` and its centre `C = (½, ½)`, in the plane `z = 0`).
`SkewPt.not_firstCongruenceTheorem`: in the triangles `COA`, `COB` the sides `CO ≡ CO` and
`CA ≡ CB` and the (right) angles at `C` are congruent, but `OA` and `OB` are not, so Theorem 10
fails. `skewLength_fig15` checks Hilbert's lengths `½, ½, 1, √2`. A finding: this example does
**not** refute IV 6 itself, contrary to the first words "Axiom IV, 6, or rather …": the two other
angles of the triangles are congruent (`SkewPt.fig15_iv6_conclusion`: `∠CAO ≡ ∠CBO` and
`∠COA ≡ ∠COB`, all half right angles), which is presumably why Hilbert adds the next sentence
(unit `s11.iv6_fails`). "Right triangles": `SkewPt.fig15_right_angles` (each angle at `C` is
congruent to its supplementary angle).

**Status.** proved
-/

namespace SkewPt

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem not_collinear_mk {x₁ y₁ x₂ y₂ x₃ y₃ : K}
    (h : (x₂ - x₁) * (y₃ - y₁) - (y₂ - y₁) * (x₃ - x₁) ≠ 0) :
    ¬Collinear (mk x₁ y₁ 0) (mk x₂ y₂ 0) (mk x₃ y₃ 0) := by
  rw [collinear_iff]
  apply not_collinear_of_li
  simp only [toC_mk, pt3_sub, sub_zero]
  exact li_pt3 h

omit [IsStrictOrderedRing K] in
theorem angCong_mk_iff {a₁ a₂ o₁ o₂ b₁ b₂ a₁' a₂' o₁' o₂' b₁' b₂' : K} :
    AngCong (mk a₁ a₂ 0) (mk o₁ o₂ 0) (mk b₁ b₂ 0) (mk a₁' a₂' 0) (mk o₁' o₂' 0) (mk b₁' b₂' 0) ↔
      AngleEq (pt3 (a₁ - o₁) (a₂ - o₂) 0) (pt3 (b₁ - o₁) (b₂ - o₂) 0)
        (pt3 (a₁' - o₁') (a₂' - o₂') 0) (pt3 (b₁' - o₁') (b₂' - o₂') 0) := by
  rw [angCong_iff, Coord.angCong_iff]
  simp only [toC_mk, pt3_sub, sub_zero]

/-- **Hilbert's example**: Theorem 10 fails in the geometry of § 11. -/
theorem not_firstCongruenceTheorem : ¬FirstCongruenceTheorem (SkewPt K) := by
  intro h
  have := (h (mk (1/2) (1/2) 0) (mk 1 0 0) (mk 0 0 0) (mk (1/2) (1/2) 0) (mk 0 1 0) (mk 0 0 0)
    (not_collinear_mk (by norm_num)) (not_collinear_mk (by norm_num))
    (by rw [segCong_iff]; simp only [toC_mk, pt3_sub, skewQ_pt3]; norm_num)
    rfl
    (by rw [angCong_mk_iff, AngleEq]; simp only [ip_pt3]; norm_num)).1
  rw [segCong_iff] at this
  simp only [toC_mk, pt3_sub, skewQ_pt3] at this
  norm_num at this

/-- In Hilbert's example the conclusion of IV 6 holds: `∠CAO ≡ ∠CBO` and `∠COA ≡ ∠COB`. -/
theorem fig15_iv6_conclusion :
    AngCong (mk (1/2 : K) (1/2) 0) (mk 1 0 0) (mk 0 0 0) (mk (1/2) (1/2) 0) (mk 0 1 0) (mk 0 0 0) ∧
      AngCong (mk (1/2 : K) (1/2) 0) (mk 0 0 0) (mk 1 0 0) (mk (1/2) (1/2) 0) (mk 0 0 0)
        (mk 0 1 0) := by
  constructor <;> rw [angCong_mk_iff, AngleEq] <;> simp only [ip_pt3] <;> norm_num

/-- The triangles of Fig. 15 are **right triangles**: the angle `∠OCA` is congruent to its
supplementary angle `∠ACD` (`D = (1, 1)` on the prolongation of `OC` beyond `C`), and likewise
`∠OCB ≡ ∠BCD`. -/
theorem fig15_right_angles :
    AngCong (mk (0 : K) 0 0) (mk (1/2) (1/2) 0) (mk 1 0 0) (mk 1 0 0) (mk (1/2) (1/2) 0)
        (mk 1 1 0) ∧
      AngCong (mk (0 : K) 0 0) (mk (1/2) (1/2) 0) (mk 0 1 0) (mk 0 1 0) (mk (1/2) (1/2) 0)
        (mk 1 1 0) := by
  constructor <;> rw [angCong_mk_iff, AngleEq] <;> simp only [ip_pt3] <;> norm_num

end SkewPt

/-- **Hilbert's lengths** in Fig. 15: `AC` and `BC` have length `½`, `OA` length `1`, `OB` length
`√2`. -/
theorem skewLength_fig15 :
    skewLength (pt3 1 0 0) (pt3 (1/2) (1/2) 0) = 1/2 ∧
      skewLength (pt3 0 1 0) (pt3 (1/2) (1/2) 0) = 1/2 ∧
      skewLength (pt3 0 0 0) (pt3 1 0 0) = 1 ∧
      skewLength (pt3 0 0 0) (pt3 0 1 0) = Real.sqrt 2 := by
  simp only [skewLength, pt3_sub, skewQ_pt3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ((1:ℝ) - 1/2 + (0 - 1/2)) ^ 2 + (0 - 1/2) ^ 2 + (0 - 0) ^ 2 = (1/2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  · rw [show ((0:ℝ) - 1/2 + (1 - 1/2)) ^ 2 + (1 - 1/2) ^ 2 + (0 - 0) ^ 2 = (1/2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  · norm_num
  · norm_num

/-!
## [s11.iv6_fails] Axiom IV 6 itself fails

*(§ 11)*

> It is not difficult to find in this geometry two triangles for which axiom IV, 6, itself is not valid.

**Lean reading.** `SkewPt.not_axiomIV6`: the right triangles `OPQ`, `OP'Q'` with `O = 0`,
`P = (17, 0, 0)`, `Q = (0, 5, 0)`, `P' = (7, 8, 0)`, `Q' = (-8, 7, 0)` have `OP ≡ OP'`
(`skewQ = 289`), `OQ ≡ OQ'` (`skewQ = 50`) and right angles at `O`, but their angles at `P`, `P'`
are not congruent (squared cosines `289/314` and `1/2`). Over every ordered field. Hence
`axiomIV6_independent`: Hilbert's geometry over `Ω` (§ 9) satisfies I, II, III, IV 1–5 and V of
space geometry and neither IV 6 nor Theorem 10; `SkewPt.model` states this over any Pythagorean
archimedean ordered field (`ℝ` included).

**Status.** proved
-/

/-- **Axiom IV 6 fails** in the geometry of § 11. -/
theorem SkewPt.not_axiomIV6 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ¬AxiomIV6 (SkewPt K) := by
  intro h
  have := (h (SkewPt.mk 0 0 0) (SkewPt.mk 17 0 0) (SkewPt.mk 0 5 0) (SkewPt.mk 0 0 0)
    (SkewPt.mk 7 8 0) (SkewPt.mk (-8) 7 0)
    (SkewPt.not_collinear_mk (by norm_num)) (SkewPt.not_collinear_mk (by norm_num))
    (by rw [SkewPt.segCong_iff]; simp only [SkewPt.toC_mk, pt3_sub, skewQ_pt3]; norm_num)
    (by rw [SkewPt.segCong_iff]; simp only [SkewPt.toC_mk, pt3_sub, skewQ_pt3]; norm_num)
    (by rw [SkewPt.angCong_mk_iff, AngleEq]; simp only [ip_pt3]; norm_num)).1
  rw [SkewPt.angCong_mk_iff, AngleEq] at this
  simp only [ip_pt3] at this
  norm_num at this

/-- **The geometry of § 11** satisfies I, II, III, IV 1–5 and V, and neither IV 6 nor
Theorem 10. -/
theorem SkewPt.model {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [IsPythagorean K] [Archimedean K] :
    SpaceOrder (SkewPt K) (CoordLine K 3) (CoordPlane K 3) ∧
      SpaceParallels (SkewPt K) (CoordLine K 3) (CoordPlane K 3) ∧
      SegmentCongruence (SkewPt K) (CoordLine K 3) ∧
      SpaceAngleCongruence (SkewPt K) (CoordLine K 3) (CoordPlane K 3) ∧
      Archimedes (SkewPt K) (CoordLine K 3) ∧ ¬AxiomIV6 (SkewPt K) ∧
      ¬FirstCongruenceTheorem (SkewPt K) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, SkewPt.not_axiomIV6,
    SkewPt.not_firstCongruenceTheorem⟩

/-- **Axiom IV 6 (and Theorem 10) is independent** of I, II, III, IV 1–5, V: Hilbert's geometry
of § 11 over `Ω`. -/
theorem axiomIV6_independent :
    ∃ (P L Pl : Type) (_ : HasLines P L) (_ : HasPlanes P Pl) (_ : HasBetween P)
      (_ : HasSegCong P) (_ : HasAngCong P),
      SpaceOrder P L Pl ∧ SpaceParallels P L Pl ∧ SegmentCongruence P L ∧
        SpaceAngleCongruence P L Pl ∧ Archimedes P L ∧ ¬AxiomIV6 P ∧ ¬FirstCongruenceTheorem P :=
  ⟨SkewPt OmegaField, CoordLine OmegaField 3, CoordPlane OmegaField 3, _, _, _, _, _,
    SkewPt.model⟩

/-! ## § 12. Independence of the axiom of continuity. Non-archimedean geometry -/

/-!
## [s12.omega_t] Hilbert's domain `Ω(t)`

*(§ 12)*

> For this purpose, we construct a domain $\Omega(t)$ of all those algebraic functions of $t$ which may be obtained from $t$ by means of the four arithmetical operations of addition, subtraction, multiplication, division, and the fifth operation $\sqrt{1+\omega^2}$, where $\omega$ represents any function arising from the application of these five operations.

**Lean reading.** `OmegaT` (helper module `AnalyticAux3.lean`, from the § 13 group): the germs at
`t = +∞` of the real functions obtained from `t` by the four operations (division by functions not
identically zero for large `t`) and `ω ↦ √(1 + ω²)` (the non-negative root), a subring of the ring
of germs; two functions agreeing for large `t` are the same number of `Ω(t)` (Hilbert compares
functions only "for sufficiently large values of `t`"). `omegaT_generated` (=
`OmegaT.mem_omegaTSubring_iff_isGenT`): the numbers of `OmegaT` are exactly the germs of the
functions built from `t` alone (`OmegaT.IsGenT`). "Algebraic functions of `t`":
`OmegaT.isAlgebraic`: every number of `Ω(t)` is algebraic over the subfield `ℚ(t)` generated by
`t` (`OmegaT.Qt`), i.e. satisfies, for all large `t`, a non-trivial polynomial equation whose
coefficients are rational functions of `t` (the algebraic elements are closed under the field
operations, and `√(1 + ω²)` is a root of `X² - (1 + ω²)`). Hilbert's inference from algebraicity
to the sign property is not valid as stated (unit `s12.sign`), which is proved differently. The
first sentence of § 12 and Veronese's footnote are prose.

**Status.** proved
-/

theorem omegaT_generated {x : GermT} :
    x ∈ omegaTSubring ↔ ∃ f, OmegaT.IsGenT f ∧ (f : GermT) = x :=
  OmegaT.mem_omegaTSubring_iff_isGenT

namespace OmegaT

/-- The number of `Ω(t)` defined by a function of `Ω(t)`. -/
noncomputable def mk {f : ℝ → ℝ} (hf : IsGen f) : OmegaT := ⟨(f : GermT), f, hf, rfl⟩

/-- The subfield `ℚ(t)` of `Ω(t)` generated by `t`: the rational functions of `t` with rational
coefficients. -/
noncomputable abbrev Qt : IntermediateField ℚ OmegaT := IntermediateField.adjoin ℚ {OmegaT.t}

theorem isAlgebraic_mk {f : ℝ → ℝ} (hf : IsGen f) : IsAlgebraic Qt (mk hf) := by
  induction hf with
  | t =>
    have : mk IsGen.t = algebraMap Qt OmegaT ⟨OmegaT.t, IntermediateField.subset_adjoin _ _ rfl⟩ :=
      rfl
    rw [this]; exact isAlgebraic_algebraMap _
  | one =>
    have : mk IsGen.one = 1 := rfl
    rw [this]; exact isAlgebraic_one
  | @add f g hf hg ha hb =>
    have : mk (hf.add hg) = mk hf + mk hg := Subtype.ext (Germ.coe_add f g).symm
    rw [this]; exact ha.add hb
  | @sub f g hf hg ha hb =>
    have : mk (hf.sub hg) = mk hf - mk hg := Subtype.ext (Germ.coe_sub f g).symm
    rw [this]; exact ha.sub hb
  | @mul f g hf hg ha hb =>
    have : mk (hf.mul hg) = mk hf * mk hg := Subtype.ext (Germ.coe_mul f g).symm
    rw [this]; exact ha.mul hb
  | @div f g hf hg hg0 ha hb =>
    have : mk (hf.div hg hg0) = mk hf * (mk hg)⁻¹ := by
      apply Subtype.ext
      show ((f / g : ℝ → ℝ) : GermT) = (f : GermT) * (g : GermT)⁻¹
      rw [div_eq_mul_inv, Germ.coe_mul, Germ.coe_inv]
    rw [this]; exact ha.mul hb.inv
  | @sqrt f hf ha =>
    apply IsAlgebraic.of_pow (n := 2) two_pos
    have : mk hf.sqrt ^ 2 = 1 + mk hf * mk hf := by
      apply Subtype.ext
      show ((fun t => Real.sqrt (1 + f t ^ 2) : ℝ → ℝ) : GermT) ^ 2 =
        (1 : GermT) + (f : GermT) * (f : GermT)
      rw [← Germ.coe_pow, ← Germ.coe_mul, ← Germ.coe_one, ← Germ.coe_add, Germ.coe_eq]
      exact Eventually.of_forall fun t => by
        simp only [Pi.pow_apply, Pi.add_apply, Pi.one_apply, Pi.mul_apply]
        rw [Real.sq_sqrt (by positivity), sq]
    rw [this]; exact isAlgebraic_one.add (ha.mul ha)

/-- **Every number of `Ω(t)` is an algebraic function of `t`**: algebraic over `ℚ(t)`. -/
theorem isAlgebraic (x : OmegaT) : IsAlgebraic Qt x := by
  obtain ⟨f, hf, hfx⟩ := x.2
  have : x = mk hf := Subtype.ext hfx.symm
  rw [this]; exact isAlgebraic_mk hf

end OmegaT

/-!
## [s12.countable] `Ω(t)` is enumerable

*(§ 12)*

> The elements of $\Omega(t)$—just as was previously the case for $\Omega$—constitute an enumerable set.

**Lean reading.** `OmegaT.countable_set`, `OmegaT.instCountable`: every number of `Ω(t)` is the
germ of the value of one of the countably many expressions built from `t` and `1` by the five
operations (`OmegaT.Expr`, `OmegaT.IsGen.exists_expr`).

**Status.** proved
-/

namespace OmegaT

/-- Expressions built from `t` and `1` by Hilbert's five operations. -/
inductive Expr
  | t
  | one
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | sqrt (a : Expr)
  deriving Countable

/-- The function of `t` denoted by an expression. -/
noncomputable def Expr.eval : Expr → ℝ → ℝ
  | t => id
  | one => 1
  | add a b => a.eval + b.eval
  | sub a b => a.eval - b.eval
  | mul a b => a.eval * b.eval
  | div a b => a.eval / b.eval
  | sqrt a => fun x => Real.sqrt (1 + a.eval x ^ 2)

theorem IsGen.exists_expr {f : ℝ → ℝ} (h : IsGen f) : ∃ e : Expr, e.eval = f := by
  induction h with
  | t => exact ⟨.t, rfl⟩
  | one => exact ⟨.one, rfl⟩
  | add _ _ ha hb => obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.add a b, rfl⟩
  | sub _ _ ha hb => obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.sub a b, rfl⟩
  | mul _ _ ha hb => obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.mul a b, rfl⟩
  | div _ _ _ ha hb => obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨.div a b, rfl⟩
  | sqrt _ ha => obtain ⟨a, rfl⟩ := ha; exact ⟨.sqrt a, rfl⟩

/-- **`Ω(t)` is enumerable.** -/
theorem countable_set : (omegaTSubring : Set GermT).Countable :=
  (Set.countable_range fun e : Expr => ((e.eval : ℝ → ℝ) : GermT)).mono fun _ ⟨f, hf, hfx⟩ => by
    obtain ⟨e, rfl⟩ := hf.exists_expr
    exact ⟨e, hfx⟩

instance instCountable : Countable OmegaT := countable_set.to_subtype

end OmegaT

/-!
## [s12.real_single_valued] The operations are real and single-valued

*(§ 12)*

> These five operations may all be performed without introducing imaginaries, and that in only one way. The domain $\Omega(t)$ contains, therefore, only real, single-valued functions of $t$.

**Lean reading.** `OmegaT.sqrt_real_unique`: for every real value `ω`, `1 + ω² > 0`, so
`√(1 + ω²)` is real, and it is the only non-negative number whose square is `1 + ω²` (the
convention "in only one way" is the choice of the non-negative root). The four arithmetic operations
are single-valued; division is only by functions not identically zero for large `t`, which vanish
at no large `t` (unit `s12.sign`), so the quotient is defined for all large `t`. Hence every element
of `OmegaT` is a real function of `t` (`ℝ → ℝ`, taken for large `t`), as the inductive definition
`OmegaT.IsGen` already builds in. Reading: "single-valued" refers to this choice of branch; the
functions are total functions of `ℝ` in Lean (with `x / 0 = 0` at the finitely many poles, which
are irrelevant for germs at `+∞`).

**Status.** proved (reading)
-/

/-- The square root `√(1 + ω²)` is real and is the unique non-negative root of `1 + ω²`. -/
theorem OmegaT.sqrt_real_unique (w : ℝ) :
    0 < 1 + w ^ 2 ∧ ∀ y : ℝ, 0 ≤ y → y ^ 2 = 1 + w ^ 2 → y = Real.sqrt (1 + w ^ 2) := by
  refine ⟨by positivity, fun y hy h => ?_⟩
  rw [← h, Real.sqrt_sq hy]

/-!
## [s12.sign] The sign of a function of `Ω(t)` for large `t`

*(§ 12)*

> Let $c$ be any function of the domain $\Omega(t)$. Since this function $c$ is an algebraic function of $t$, it can in no case vanish for more than a finite number of values of $t$, and, hence, for sufficiently large positive values of $t$, it must remain always positive or always negative.

**Lean reading.** As printed the claim is false, twice. (1) The zero function belongs to `Ω(t)`
(`t - t`) and vanishes everywhere; Hilbert means `c ≠ 0`. (2) Even a function of `Ω(t)` that is not
zero for large `t` can vanish at infinitely many values of `t`, because the convention of taking the
non-negative root (unit `s12.real_single_valued`) makes the functions only piecewise algebraic:
`OmegaT.exists_isGen_infinite_zeros` exhibits `c = 2s √(1 + ω²) - (s² + 1)` with `s = -t` and
`ω = (s² - 1)/(2s)`, which equals `0` for every `t < 0` (there `√(1 + ω²) = (s² + 1)/(2s)`) and
`-2(t² + 1) < 0` for every `t > 0`. The conclusion Hilbert needs is true, with "identically zero"
as a third case: `OmegaT.sign_eventually`: every function of `Ω(t)` is, for all sufficiently large
`t`, identically zero, or always positive, or always negative (`OmegaT.IsGen.trichotomy` of
`AnalyticAux3.lean`, proved there via the meromorphy of `s ↦ c(1/s)` at `s = 0⁺` instead of
algebraicity).

**Status.** proved (corrected)
-/

namespace OmegaT

/-- The function `-t` of `Ω(t)`. -/
noncomputable def negT : ℝ → ℝ := 0 - id

/-- The function `2` of `Ω(t)`. -/
noncomputable def two : ℝ → ℝ := 1 + 1

/-- The function `ω = (s² - 1) / (2 s)` with `s = -t`. -/
noncomputable def omCex : ℝ → ℝ := (negT * negT - 1) / (two * negT)

/-- **The counterexample** `2 s √(1 + ω²) - (s² + 1)` with `s = -t`, `ω = (s² - 1)/(2s)`. -/
noncomputable def zeroCex : ℝ → ℝ :=
  two * negT * (fun x => Real.sqrt (1 + omCex x ^ 2)) - (negT * negT + 1)

theorem isGen_zeroCex : IsGen zeroCex := by
  have hs : IsGen negT := IsGen.zero.sub IsGen.t
  have h2 : IsGen two := IsGen.one.add IsGen.one
  have hden : ¬(two * negT) =ᶠ[atTop] 0 := by
    intro h
    obtain ⟨x, hx, hx1⟩ := (h.and (eventually_gt_atTop (0 : ℝ))).exists
    simp [two, negT] at hx
    linarith
  exact ((h2.mul hs).mul ((((hs.mul hs).sub IsGen.one).div (h2.mul hs) hden).sqrt)).sub
    ((hs.mul hs).add IsGen.one)

theorem zeroCex_apply (x : ℝ) : zeroCex x =
    2 * (-x) * Real.sqrt (1 + ((x * x - 1) / (2 * (-x))) ^ 2) - (x * x + 1) := by
  have h1 : omCex x = (x * x - 1) / (2 * (-x)) := by
    simp only [omCex, negT, two, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.one_apply,
      Pi.div_apply, Pi.zero_apply, id]
    ring
  simp only [zeroCex, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.one_apply, h1]
  simp only [negT, two, Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.zero_apply, id]
  ring

theorem sqrt_aux (x : ℝ) (hx : x ≠ 0) :
    Real.sqrt (1 + ((x * x - 1) / (2 * (-x))) ^ 2) = |(x * x + 1) / (2 * x)| := by
  have e : 1 + ((x * x - 1) / (2 * (-x))) ^ 2 = ((x * x + 1) / (2 * x)) ^ 2 := by
    field_simp; ring
  rw [e, Real.sqrt_sq_eq_abs]

theorem zeroCex_neg {x : ℝ} (hx : x < 0) : zeroCex x = 0 := by
  have hx0 : x ≠ 0 := hx.ne
  have hp : 0 < x * x + 1 := by nlinarith [mul_self_nonneg x]
  rw [zeroCex_apply, sqrt_aux x hx0, abs_of_neg (div_neg_of_pos_of_neg hp (by linarith))]
  field_simp
  ring

theorem zeroCex_pos {x : ℝ} (hx : 0 < x) : zeroCex x < 0 := by
  rw [zeroCex_apply, sqrt_aux x hx.ne', abs_of_pos (by positivity)]
  have : 2 * -x * ((x * x + 1) / (2 * x)) - (x * x + 1) = -2 * (x * x + 1) := by
    field_simp; ring
  rw [this]; nlinarith

/-- **Hilbert's claim on the zeros is false as printed**: some function of `Ω(t)` is negative for
all large `t` but vanishes at infinitely many values of `t`. -/
theorem exists_isGen_infinite_zeros :
    ∃ f : ℝ → ℝ, IsGen f ∧ (∀ᶠ x in atTop, f x < 0) ∧ {x : ℝ | f x = 0}.Infinite := by
  refine ⟨zeroCex, isGen_zeroCex, (eventually_gt_atTop 0).mono fun x hx => zeroCex_pos hx, ?_⟩
  exact (Set.Iio_infinite (0 : ℝ)).mono fun x hx => zeroCex_neg hx

/-- **The corrected claim**: for sufficiently large `t`, a function of `Ω(t)` is identically zero,
or always positive, or always negative. -/
theorem sign_eventually {f : ℝ → ℝ} (h : IsGen f) :
    (∀ᶠ x in atTop, f x = 0) ∨ (∀ᶠ x in atTop, 0 < f x) ∨ (∀ᶠ x in atTop, f x < 0) :=
  h.trichotomy

end OmegaT

/-!
## [s12.ordering] `Ω(t)` as an ordered number system

*(§ 12)*

> Let us now regard the functions of the domain $\Omega(t)$ as a kind of complex numbers. In the system of complex numbers thus defined, all of the ordinary rules of operation evidently hold. Moreover, if $a$, $b$ are any two distinct numbers of this system, then $a$ is said to be greater than, or less than, $b$ (written $a>b$ or $a<b$) according as the difference $c = a-b$ is always positive or always negative for sufficiently large values of $t$. By the adoption of this convention for the numbers of our system, it is possible to arrange them according to their magnitude in a manner analogous to that employed for real numbers. We readily see also that, for this system of complex numbers, the validity of an inequality is not destroyed by adding the same or equal numbers to both members, or by multiplying both members by the same number, providing it is greater than zero.

**Lean reading.** "All of the ordinary rules of operation": `OmegaT` is a field
(`OmegaT.instField`); `OmegaT.rules_of_operation`: it satisfies laws 1–16 of § 13 (from
`omegaT_laws`, which also shows that law 17, Archimedes's, fails). The order: `OmegaT.lt_iff_eventually`
(`a < b` iff `b - a` is positive for all sufficiently large `t`); "it is possible to arrange them
according to their magnitude": it is a linear order (`OmegaT.instLinearOrder`, resting on the sign
property `OmegaT.sign_eventually`). The two monotonicity laws are `OmegaT.add_lt_add_of_lt` and
`OmegaT.mul_lt_mul_of_lt` ("adding the same or equal numbers to both members", "multiplying both
members by the same number, providing it is greater than zero").

**Status.** proved
-/

theorem OmegaT.lt_iff {x y : OmegaT} {f g : ℝ → ℝ} (hf : (f : GermT) = x) (hg : (g : GermT) = y) :
    x < y ↔ ∀ᶠ s in atTop, f s < g s :=
  OmegaT.lt_iff_eventually hf hg

/-- "All of the ordinary rules of operation": laws 1–16 of § 13 (unit `s13` of Analytic.lean). -/
theorem OmegaT.rules_of_operation : Laws1to16 OmegaT ∧ Law13Asymm OmegaT :=
  ⟨omegaT_laws.1, omegaT_laws.2.1⟩

theorem OmegaT.trichotomy (x y : OmegaT) : x < y ∨ x = y ∨ y < x := lt_trichotomy x y

theorem OmegaT.add_lt_add_of_lt {a b : OmegaT} (h : a < b) (c : OmegaT) : a + c < b + c :=
  add_lt_add_left h c

theorem OmegaT.mul_lt_mul_of_lt {a b c : OmegaT} (h : a < b) (hc : 0 < c) : a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

/-!
## [s12.n_lt_t] `n < t`: `Ω(t)` is non-archimedean

*(§ 12)*

> If $n$ is any arbitrary positive integral rational number, then, for the two numbers $n$ and $t$ of the domain $\Omega (t)$, the inequality $n<t$ certainly holds; for, the difference $n-t$, considered as a function of $t$, is always negative for sufficiently large values of $t$. We express this fact in the following manner: The two numbers $l$ and $t$ of the domain $\Omega (t)$, each of which is greater than zero, possess the property that any multiple whatever of the first always remains smaller than the second.

**Lean reading.** `OmegaT.natCast_lt_t`: `n < t` for every natural number `n`.
`OmegaT.nsmul_one_lt_t`: every multiple `n · 1` of the number `1` stays below `t`. "The two
numbers `l` and `t`" is a misprint for "`1` and `t`" (the multiples of `1` are the `n`).

**Status.** proved
-/

theorem OmegaT.nsmul_one_lt_t (n : ℕ) : n • (1 : OmegaT) < OmegaT.t := by
  rw [nsmul_one]; exact OmegaT.natCast_lt_t n

/-!
## [s12.geometry] The non-archimedean geometry

*(§ 12)*

> From the complex numbers of the domain $\Omega (t)$, we now proceed to construct a geometry in exactly the same manner as in § 9, where we took as the basis of our consideration the algebraic numbers of the domain $\Omega$. We will regard a system of three numbers $(x,y,z)$ of the domain $\Omega (t)$ as defining a point, and the ratio of any four such numbers $(u:v:w:r)$, where $u$, $v$, $w$ are not all zero, as defining a plane. Finally, the existence of the equation \[ xu + yv + zw + r = 0 \] shall express the condition that the point $(x, y, z)$ lies in the plane $(u:v:w:r)$. Let the straight line be defined in our geometry as the totality of all the points lying simultaneously in the same two planes. If now we adopt conventions corresponding to those of § 9 concerning the arrangement of elements and the laying off of angles and of segments, we shall obtain a *“non-archimedean” geometry* where, as the properties of the complex number system already investigated show, all of the axioms, with the exception of that of Archimedes, are fulfilled.

**Lean reading.** The geometry is `Coord OmegaT 3` with the lines `CoordLine OmegaT 3` and planes
`CoordPlane OmegaT 3` of § 9 (affine subspaces of dimensions 1 and 2), betweenness and congruence
as in § 9 (unit `s9.space`). Hilbert's description (planes as the solution sets of
`xu + yv + zw + r = 0` with `(u, v, w) ≠ 0`, lines as the common points of two planes) describes
the same subsets of `Ω(t)³`; the correspondence is classical linear algebra and is not
re-proved here, as in `s9.space`. Proved (`omegaT_model`): groups I, II, III, IV of space geometry
hold (`spaceCongruence_of_isPythagorean`: `Ω(t)` is a Pythagorean ordered field,
`OmegaT.instIsPythagorean`), and Archimedes's axiom fails (`omegaT_not_axiomV`, from the general
`not_axiomV_of_infinite`: over any ordered field with an element larger than all natural numbers).
`axiomV_independent`: hence V is not a consequence of I–IV. The plane version holds as well
(`omegaT_plane_model`).

**Status.** proved
-/

/-- In a coordinate geometry over an ordered field containing an element `t` larger than every
natural number, **Archimedes's axiom fails**: the points `0, e, 2e, 3e, …` (`e` a unit vector) are
consecutive and equally spaced, `e` lies between `0` and `t e`, but `t e` never lies between `0`
and `n e`. -/
theorem not_axiomV_of_infinite {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} [NeZero n] (t : K) (ht : ∀ m : ℕ, (m : K) < t) : ¬AxiomV (Coord K n) := by
  intro hV
  set e : Coord K n := AffPt.ofV (Pi.single 0 1) with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun (congrArg AffPt.toV h) 0
    simp [he] at this
  have key : ∀ x y z : K, Between (x • e) (y • e) (z • e) ↔ (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
    intro x y z
    have := sbtw_param_iff he0 x y z (O := 0)
    simp only [add_zero] at this
    exact this
  obtain ⟨m, hm⟩ := hV (fun k => (k : K) • e) (t • e)
    (by simp only [Nat.cast_zero, Nat.cast_one]; exact (key 0 1 t).2 (Or.inl ⟨one_pos, by
      simpa using ht 1⟩))
    (fun k => (key _ _ _).2 (Or.inl ⟨by push_cast; linarith, by push_cast; linarith⟩))
    (fun a b => by
      rw [Coord.segCong_iff, ← sub_smul, ← sub_smul]
      simp)
  rcases (key _ _ _).1 hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact lt_asymm h2 (ht m)
  · simp at h1 h2; linarith

/-- **Archimedes's axiom fails** in the non-archimedean geometry of space. -/
theorem omegaT_not_axiomV : ¬AxiomV (Coord OmegaT 3) :=
  not_axiomV_of_infinite OmegaT.t OmegaT.natCast_lt_t

/-- **The non-archimedean geometry** satisfies groups I–IV of space geometry, not V. -/
theorem omegaT_model :
    SpaceCongruence (Coord OmegaT 3) (CoordLine OmegaT 3) (CoordPlane OmegaT 3) ∧
      SpaceParallels (Coord OmegaT 3) (CoordLine OmegaT 3) (CoordPlane OmegaT 3) ∧
      ¬AxiomV (Coord OmegaT 3) :=
  ⟨(spaceCongruence_of_isPythagorean OmegaT).1, (spaceCongruence_of_isPythagorean OmegaT).2,
    omegaT_not_axiomV⟩

/-- The plane version: groups I–IV of plane geometry hold in `Ω(t)²`, V fails. -/
theorem omegaT_plane_model :
    PlaneCongruence (Coord OmegaT 2) (CoordLine OmegaT 2) ∧
      PlaneParallels (Coord OmegaT 2) (CoordLine OmegaT 2) ∧ ¬AxiomV (Coord OmegaT 2) :=
  ⟨planeCongruence_of_isPythagorean OmegaT, planeParallels_coord OmegaT,
    not_axiomV_of_infinite OmegaT.t OmegaT.natCast_lt_t⟩

/-- **Archimedes's axiom is independent** of groups I–IV. -/
theorem axiomV_independent :
    ∃ (P L Pl : Type) (_ : HasLines P L) (_ : HasPlanes P Pl) (_ : HasBetween P)
      (_ : HasSegCong P) (_ : HasAngCong P),
      SpaceCongruence P L Pl ∧ SpaceParallels P L Pl ∧ ¬AxiomV P :=
  ⟨Coord OmegaT 3, CoordLine OmegaT 3, CoordPlane OmegaT 3, _, _, _, _, _, omegaT_model⟩

/-!
## [s12.lay_off_unit] Laying off the segment `1` on the segment `t`

*(§ 12)*

> In fact, we can lay off successively the segment 1 upon the segment $t$ an arbitrary number of times without reaching the end point of the segment $t$, which is a contradiction to the axiom of Archimedes.

**Lean reading.** On the `x`-axis of `Ω(t)³` with `e = (1, 0, 0)`: `layOff_unit_on_t`: the
segments `(k e)((k + 1) e)` are all congruent to the unit segment `0e`, each `(k + 1) e` lies
between `k e` and `(k + 2) e` (they are laid off successively), and for every `n ≥ 1` the point
`n e` lies between `0` and `t e`, so the end point `t e` is never reached. This is the
counterexample to V used in `not_axiomV_of_infinite`.

**Status.** proved
-/

theorem layOff_unit_on_t :
    let e : Coord OmegaT 3 := pt3 1 0 0
    (∀ k : ℕ, SegCong ((k : OmegaT) • e) (((k + 1 : ℕ) : OmegaT) • e) (0 : Coord OmegaT 3) e) ∧
      (∀ k : ℕ, Between ((k : OmegaT) • e) (((k + 1 : ℕ) : OmegaT) • e)
        (((k + 2 : ℕ) : OmegaT) • e)) ∧
      ∀ n : ℕ, 1 ≤ n → Between (0 : Coord OmegaT 3) ((n : OmegaT) • e) (OmegaT.t • e) := by
  intro e
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun (congrArg AffPt.toV h) 0
    simp [e, pt3] at this
  have key : ∀ x y z : OmegaT, Between (x • e) (y • e) (z • e) ↔
      (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
    intro x y z
    have := sbtw_param_iff he0 x y z (O := 0)
    simp only [add_zero] at this
    exact this
  refine ⟨fun k => ?_, fun k => (key _ _ _).2 (Or.inl ⟨by push_cast; linarith,
    by push_cast; linarith⟩), fun n hn => ?_⟩
  · rw [Coord.segCong_iff, ← sub_smul, sub_zero]
    push_cast
    rw [add_sub_cancel_left, one_smul]
  · have h := (key 0 n OmegaT.t).2 (Or.inl ⟨by exact_mod_cast hn, OmegaT.natCast_lt_t n⟩)
    rwa [zero_smul] at h

end HilbertFoundations
