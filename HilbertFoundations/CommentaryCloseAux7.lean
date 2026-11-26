import HilbertFoundations.Commentary

/-!
# The appendix: the main theorem as stated, and what follows from it (helper for `CommentaryClose.lean`)

Units `app.main_theorem`, `app.two_fixed_points`, `app.transitive`, `app.middle` of
`Commentary.lean`. None of them is closed here; this file records what is proved about them.

* `not_appendixMainTheorem`: the statement `AppendixMainTheorem` is false as stated, for a degenerate
  reason (the empty set of points is a plane in the sense of `IsPlane`). The statement Hilbert
  means is `AppendixMainTheoremNonempty`.
* The three steps of Hilbert's proof `TwoFixedPointsIdentity`, `DisplacementsTransitive`,
  `AtMostOneMiddle` are consequences of `AppendixMainTheoremNonempty`
  (`twoFixedPointsIdentity_of_main`, `displacementsTransitive_of_main`, `atMostOneMiddle_of_main`):
  they hold in every geometry that is euclidean or hyperbolic in the sense of `IsEuclideanGeometry`,
  `IsHyperbolicGeometry` (`twoFixedPoints_of_isEuclidean`, `twoFixedPoints_of_isHyperbolic`,
  `transitive_of_isEuclidean`, `transitive_of_isHyperbolic`). So these formal statements are correct
  if the main theorem is, and they are exactly as deep as it is: in Hilbert's memoir they are steps
  of its proof.
* `atMostOneMiddle_of_twoFixedPoints`: `AtMostOneMiddle` follows from `TwoFixedPointsIdentity`.
* `rotationsOfTrueCircle_of_main`: the proposition on the group of a true circle
  (`RotationsOfTrueCircle`, unit `app.rotation_group`) is also a consequence of
  `AppendixMainTheoremNonempty` (`rotationsOfTrueCircle_of_isEuclidean`,
  `rotationsOfTrueCircle_of_isHyperbolic`).

The units `app.true_circle_jordan` and `app.true_line` are not obtained in this way from the main
theorem as it is stated: they speak of the position of the true circles and true lines in the
number plane, whereas `IsEuclideanGeometry` and `IsHyperbolicGeometry` only ask for a bijection of
the points (not a continuous one) that carries the displacements onto the motions.
-/

namespace HilbertFoundations

namespace Appendix

open Complex Set

/-! ### The main theorem as stated -/

/-- The empty set of points of the number plane is a plane in the sense of `IsPlane`. -/
theorem isPlane_empty : IsPlane (∅ : Set ℂ) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

/-- **The empty geometry**: no point, the identity as only displacement. -/
def emptyGeometry : Geometry where
  S := ∅
  isPlane := isPlane_empty
  D := Set.univ
  isDisplacement _ _ :=
    ⟨continuous_of_discreteTopology, fun γ => ((γ 0).2 : (γ 0 : ℂ) ∈ (∅ : Set ℂ)).elim⟩

theorem emptyGeometry_isEmpty : IsEmpty emptyGeometry.S := ⟨fun x => x.2.elim⟩

/-- The empty geometry satisfies axioms I (group reading), II and III. -/
theorem emptyGeometry_axioms :
    AxiomIGroup emptyGeometry ∧ AxiomII emptyGeometry ∧ AxiomIII emptyGeometry :=
  ⟨⟨fun _ _ _ _ => trivial, trivial, fun _ _ => trivial⟩,
    fun A => (emptyGeometry_isEmpty.false A).elim, fun A => (emptyGeometry_isEmpty.false A).elim⟩

/-- **The main theorem of the appendix is false as stated**: the empty geometry satisfies axioms
I–III and is neither the euclidean nor the Bolyai–Lobachevskian plane. -/
theorem not_appendixMainTheorem : ¬AppendixMainTheorem := by
  intro h
  obtain ⟨h1, h2, h3⟩ := emptyGeometry_axioms
  rcases h emptyGeometry h1 h2 h3 with ⟨φ, -⟩ | ⟨φ, -⟩
  · exact emptyGeometry_isEmpty.false (φ.symm 0)
  · exact emptyGeometry_isEmpty.false (φ.symm ⟨0, Metric.mem_ball_self one_pos⟩)

/-- **Hilbert's theorem** (appendix), for a plane that has a point: a geometry satisfying axioms
I–III is the euclidean or the Bolyai–Lobachevskian geometry. Not proved here. -/
def AppendixMainTheoremNonempty : Prop :=
  ∀ G : Geometry, G.S.Nonempty → AxiomIGroup G → AxiomII G → AxiomIII G →
    IsEuclideanGeometry G ∨ IsHyperbolicGeometry G

/-! ### A segment has at most one middle -/

/-- **A segment has at most one middle**, given that a displacement with two fixed points is the
identity (unit `app.two_fixed_points`): two semi-rotations carrying `A` into `B` coincide (their
composite fixes `A` and `B`), and a semi-rotation, not being the identity, fixes only its centre. -/
theorem atMostOneMiddle_of_twoFixedPoints (h : TwoFixedPointsIdentity) : AtMostOneMiddle := by
  rintro G h1 h2 h3 M M' A B hAB ⟨σ, ⟨⟨hσD, hσM⟩, hσσ, hσne⟩, hσA⟩
    ⟨σ', ⟨⟨hσ'D, hσ'M⟩, hσ'σ', -⟩, hσ'A⟩
  have hσB : σ B = A := by
    have e := congrArg (fun f : Equiv.Perm G.S => f A) hσσ
    simp only [Equiv.trans_apply, Equiv.refl_apply] at e
    rw [hσA] at e; exact e
  have hσ'B : σ' B = A := by
    have e := congrArg (fun f : Equiv.Perm G.S => f A) hσ'σ'
    simp only [Equiv.trans_apply, Equiv.refl_apply] at e
    rw [hσ'A] at e; exact e
  have hτ := h G h1 h2 h3 (σ.trans σ') (h1.1 σ hσD σ' hσ'D) A B hAB
    (by rw [Equiv.trans_apply, hσA, hσ'B]) (by rw [Equiv.trans_apply, hσB, hσ'A])
  have hσeq : ∀ X, σ' X = σ X := fun X => by
    have e1 := congrArg (fun f : Equiv.Perm G.S => f (σ X)) hτ
    have e2 := congrArg (fun f : Equiv.Perm G.S => f X) hσσ
    simp only [Equiv.trans_apply, Equiv.refl_apply] at e1 e2
    rw [e2] at e1; exact e1
  have hM' : σ M' = M' := by rw [← hσeq]; exact hσ'M
  by_contra hne
  exact hσne (h G h1 h2 h3 σ hσD M M' hne hσM hM')

/-! ### Two fixed points -/

/-- In a euclidean geometry a displacement with two fixed points is the identity. -/
theorem twoFixedPoints_of_isEuclidean {G : Geometry} (hE : IsEuclideanGeometry G)
    {f : Equiv.Perm G.S} (hf : f ∈ G.D) {A B : G.S} (hAB : A ≠ B) (hA : f A = A) (hB : f B = B) :
    f = Equiv.refl G.S := by
  obtain ⟨φ, hφ⟩ := hE
  obtain ⟨a, b, -, hab⟩ := (hφ f).1 hf
  have e1 := hab A
  rw [hA] at e1
  have e2 := hab B
  rw [hB] at e2
  have hd : φ A - φ B ≠ 0 := sub_ne_zero.2 (fun e => hAB (φ.injective e))
  have ha : a = 1 := by
    have : (a - 1) * (φ A - φ B) = 0 := by linear_combination e2 - e1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
  have hb : b = 0 := by rw [ha] at e1; linear_combination -e1
  have hX : ∀ X, f X = X := fun X => by
    have := hab X
    rw [ha, hb, one_mul, add_zero] at this
    exact φ.injective this
  exact Equiv.ext hX

/-- The denominator of a conformal automorphism of the unit disc does not vanish in the disc. -/
theorem one_sub_conj_mul_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - starRingEnd ℂ a * z ≠ 0 := by
  intro h0
  have h1 : starRingEnd ℂ a * z = 1 := by linear_combination -h0
  have h2 : ‖a‖ * ‖z‖ = 1 := by rw [← Complex.norm_conj a, ← norm_mul, h1, norm_one]
  have h3 : ‖a‖ * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg _) ha.le
  linarith

/-- In a hyperbolic geometry a displacement with two fixed points is the identity: a conformal
automorphism `z ↦ c (z - a) / (1 - conj a z)` of the disc with two fixed points `z₁ ≠ z₂` has
`conj a z₁ z₂ = -c a`, which forces `a = 0` (as `|z₁ z₂| < 1`), and then `c = 1`. -/
theorem twoFixedPoints_of_isHyperbolic {G : Geometry} (hH : IsHyperbolicGeometry G)
    {f : Equiv.Perm G.S} (hf : f ∈ G.D) {A B : G.S} (hAB : A ≠ B) (hA : f A = A) (hB : f B = B) :
    f = Equiv.refl G.S := by
  obtain ⟨φ, hφ⟩ := hH
  obtain ⟨c, a, hc, ha, hca⟩ := (hφ f).1 hf
  have hball : ∀ X : G.S, ‖(φ X : ℂ)‖ < 1 := fun X => mem_ball_zero_iff.1 (φ X).2
  have hden : ∀ X : G.S, 1 - starRingEnd ℂ a * (φ X : ℂ) ≠ 0 := fun X =>
    one_sub_conj_mul_ne_zero ha (hball X)
  have hz : (φ A : ℂ) - φ B ≠ 0 :=
    sub_ne_zero.2 (fun e => hAB (φ.injective (Subtype.ext e)))
  have e1 : (φ A : ℂ) * (1 - starRingEnd ℂ a * (φ A : ℂ)) = c * ((φ A : ℂ) - a) := by
    have := hca A
    rw [hA, eq_div_iff (hden A)] at this
    exact this
  have e2 : (φ B : ℂ) * (1 - starRingEnd ℂ a * (φ B : ℂ)) = c * ((φ B : ℂ) - a) := by
    have := hca B
    rw [hB, eq_div_iff (hden B)] at this
    exact this
  have hc' : 1 - starRingEnd ℂ a * ((φ A : ℂ) + φ B) = c := by
    have : ((φ A : ℂ) - φ B) * (1 - starRingEnd ℂ a * ((φ A : ℂ) + φ B) - c) = 0 := by
      linear_combination e1 - e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz)
  have hprod : starRingEnd ℂ a * ((φ A : ℂ) * φ B) = -(c * a) := by
    linear_combination e1 - (φ A : ℂ) * hc'
  have ha0 : a = 0 := by
    by_contra hne
    have hn : ‖a‖ * (‖(φ A : ℂ)‖ * ‖(φ B : ℂ)‖) = ‖a‖ := by
      have := congrArg norm hprod
      rwa [norm_mul, norm_mul, Complex.norm_conj, norm_neg, norm_mul, hc, one_mul] at this
    have h1 : ‖(φ A : ℂ)‖ * ‖(φ B : ℂ)‖ = 1 :=
      mul_left_cancel₀ (norm_ne_zero_iff.2 hne) (by rw [hn, mul_one])
    have h2 : ‖(φ A : ℂ)‖ * ‖(φ B : ℂ)‖ ≤ ‖(φ B : ℂ)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (hball A).le
    linarith [hball B]
  have hc1 : c = 1 := by
    rw [ha0] at hc'
    simpa using hc'.symm
  have hX : ∀ X, f X = X := fun X => by
    have := hca X
    rw [ha0, hc1] at this
    simp only [map_zero, zero_mul, sub_zero, one_mul, div_one] at this
    exact φ.injective (Subtype.ext this)
  exact Equiv.ext hX

/-- **`TwoFixedPointsIdentity` follows from the main theorem** (for a plane that has a point). -/
theorem twoFixedPointsIdentity_of_main (h : AppendixMainTheoremNonempty) :
    TwoFixedPointsIdentity := by
  intro G h1 h2 h3 f hf A B hAB hA hB
  rcases h G ⟨A, A.2⟩ h1 h2 h3 with hE | hH
  · exact twoFixedPoints_of_isEuclidean hE hf hAB hA hB
  · exact twoFixedPoints_of_isHyperbolic hH hf hAB hA hB

/-- **`AtMostOneMiddle` follows from the main theorem** (for a plane that has a point). -/
theorem atMostOneMiddle_of_main (h : AppendixMainTheoremNonempty) : AtMostOneMiddle :=
  atMostOneMiddle_of_twoFixedPoints (twoFixedPointsIdentity_of_main h)

/-! ### Transitivity -/

/-- In a euclidean geometry every point can be brought into every other (by a translation). -/
theorem transitive_of_isEuclidean {G : Geometry} (hE : IsEuclideanGeometry G) (A B : G.S) :
    ∃ f ∈ G.D, f A = B := by
  obtain ⟨φ, hφ⟩ := hE
  refine ⟨(φ.trans (Equiv.addRight (φ B - φ A))).trans φ.symm,
    (hφ _).2 ⟨1, φ B - φ A, norm_one, fun X => ?_⟩, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.coe_addRight, one_mul]
  · simp only [Equiv.trans_apply, Equiv.coe_addRight, add_sub_cancel, Equiv.symm_apply_apply]

/-- The conformal map `z ↦ (z - a) / (1 - conj a z)` of the unit disc (`|a| < 1`), which carries `a`
into `0`. -/
noncomputable def mob (a z : ℂ) : ℂ := (z - a) / (1 - starRingEnd ℂ a * z)

theorem normSq_mob_aux (a z : ℂ) :
    normSq (1 - starRingEnd ℂ a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, one_re, one_im, conj_re, conj_im]
  ring

theorem norm_mob_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have hd := one_sub_conj_mul_ne_zero ha hz
  have ha2 : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hlt : normSq (z - a) < normSq (1 - starRingEnd ℂ a * z) := by
    have := normSq_mob_aux a z
    nlinarith [mul_pos (sub_pos.2 ha2) (sub_pos.2 hz2)]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hlt
  have hlt' : ‖z - a‖ < ‖1 - starRingEnd ℂ a * z‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]
  exact hlt'

theorem mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := one_sub_conj_mul_ne_zero ha hz
  have hd' := one_sub_conj_mul_ne_zero (a := -a) (by rwa [norm_neg]) (norm_mob_lt ha hz)
  have hw : mob a z * (1 - starRingEnd ℂ a * z) = z - a := div_mul_cancel₀ _ hd
  rw [mob, div_eq_iff hd']
  apply mul_right_cancel₀ hd
  simp only [map_neg]
  linear_combination (1 - z * starRingEnd ℂ a) * hw

/-- The conformal map `mob a` as a permutation of the unit disc. -/
noncomputable def mobPerm (a : ℂ) (ha : ‖a‖ < 1) : Equiv.Perm (Metric.ball (0 : ℂ) 1) where
  toFun z := ⟨mob a z, mem_ball_zero_iff.2 (norm_mob_lt ha (mem_ball_zero_iff.1 z.2))⟩
  invFun z := ⟨mob (-a) z,
    mem_ball_zero_iff.2 (norm_mob_lt (by rwa [norm_neg]) (mem_ball_zero_iff.1 z.2))⟩
  left_inv z := Subtype.ext (mob_neg_mob ha (mem_ball_zero_iff.1 z.2))
  right_inv z := Subtype.ext (by
    have := mob_neg_mob (a := -a) (by rwa [norm_neg]) (mem_ball_zero_iff.1 z.2)
    rwa [neg_neg] at this)

/-- In a hyperbolic geometry (whose displacements form a group) every point can be brought into
every other: the displacement `z ↦ (z - a) / (1 - conj a z)` carries `a` into the centre. -/
theorem transitive_of_isHyperbolic {G : Geometry} (h1 : AxiomIGroup G)
    (hH : IsHyperbolicGeometry G) (A B : G.S) : ∃ f ∈ G.D, f A = B := by
  obtain ⟨φ, hφ⟩ := hH
  have key : ∀ A : G.S, ∃ f ∈ G.D, f A = φ.symm ⟨0, Metric.mem_ball_self one_pos⟩ := by
    intro A
    have ha : ‖(φ A : ℂ)‖ < 1 := mem_ball_zero_iff.1 (φ A).2
    refine ⟨(φ.trans (mobPerm (φ A) ha)).trans φ.symm,
      (hφ _).2 ⟨1, φ A, norm_one, ha, fun X => ?_⟩, ?_⟩
    · simp only [Equiv.trans_apply, Equiv.apply_symm_apply, one_mul]
      rfl
    · simp only [Equiv.trans_apply]
      congr 1
      exact Subtype.ext (by show mob (φ A) (φ A) = 0; simp [mob])
  obtain ⟨f, hf, hfA⟩ := key A
  obtain ⟨g, hg, hgB⟩ := key B
  refine ⟨f.trans g.symm, h1.1 f hf _ (h1.2.2 g hg), ?_⟩
  rw [Equiv.trans_apply, hfA, ← hgB, Equiv.symm_apply_apply]

/-- **`DisplacementsTransitive` follows from the main theorem** (for a plane that has a point). -/
theorem displacementsTransitive_of_main (h : AppendixMainTheoremNonempty) :
    DisplacementsTransitive := by
  intro G h1 h2 h3 A B
  rcases h G ⟨A, A.2⟩ h1 h2 h3 with hE | hH
  · exact transitive_of_isEuclidean hE A B
  · exact transitive_of_isHyperbolic h1 hH A B

/-! ### The rotations of a true circle -/

/-- In a euclidean geometry the rotations about `M` act on a true circle about `M` as the ordinary
rotations act on the ordinary circle. -/
theorem rotationsOfTrueCircle_of_isEuclidean {G : Geometry} (hE : IsEuclideanGeometry G)
    {M A : G.S} (hAM : A ≠ M) :
    ∃ ψ : G.S → ℂ, BijOn ψ (TrueCircle G M A) (Metric.sphere 0 1) ∧
      (∀ f, IsRotationAbout G f M → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X ∈ TrueCircle G M A, ψ (f X) = c * ψ X) ∧
      ∀ c : ℂ, ‖c‖ = 1 → ∃ f, IsRotationAbout G f M ∧ ∀ X ∈ TrueCircle G M A, ψ (f X) = c * ψ X := by
  obtain ⟨φ, hφ⟩ := hE
  have hd : φ A - φ M ≠ 0 := sub_ne_zero.2 (fun e => hAM (φ.injective e))
  have hrot : ∀ f, IsRotationAbout G f M →
      ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ X, φ (f X) - φ M = a * (φ X - φ M) := by
    rintro f ⟨hfD, hfM⟩
    obtain ⟨a, b, ha, hab⟩ := (hφ f).1 hfD
    have hM := hab M
    rw [hfM] at hM
    exact ⟨a, ha, fun X => by rw [hab X]; linear_combination -hM⟩
  have hrotc : ∀ c : ℂ, ‖c‖ = 1 →
      ∃ f, IsRotationAbout G f M ∧ ∀ X, φ (f X) - φ M = c * (φ X - φ M) := by
    intro c hc
    have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one hc
    have hτ : ∀ z, ((Equiv.mulLeft₀ c hc0).trans (Equiv.addRight (φ M - c * φ M))) z =
        c * z + (φ M - c * φ M) := fun z => rfl
    refine ⟨(φ.trans ((Equiv.mulLeft₀ c hc0).trans (Equiv.addRight (φ M - c * φ M)))).trans φ.symm,
      ⟨(hφ _).2 ⟨c, φ M - c * φ M, hc, fun X => ?_⟩, ?_⟩, fun X => ?_⟩
    · rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply, hτ]
    · rw [Equiv.trans_apply, Equiv.trans_apply, hτ,
        show c * φ M + (φ M - c * φ M) = φ M by ring, Equiv.symm_apply_apply]
    · rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply, hτ]
      ring
  refine ⟨fun X => (φ X - φ M) / (φ A - φ M), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X ⟨f, hf, rfl⟩
    obtain ⟨a, ha, hfa⟩ := hrot f hf
    show (φ (f A) - φ M) / (φ A - φ M) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, hfa, mul_div_assoc, div_self hd, mul_one, ha]
  · intro X _ Y _ e
    exact φ.injective (sub_left_injective ((div_left_inj₀ hd).1 e))
  · intro c hc
    rw [mem_sphere_zero_iff_norm] at hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    refine ⟨f A, ⟨f, hf, rfl⟩, ?_⟩
    show (φ (f A) - φ M) / (φ A - φ M) = c
    rw [hfv, mul_div_assoc, div_self hd, mul_one]
  · intro f hf
    obtain ⟨a, ha, hfa⟩ := hrot f hf
    exact ⟨a, ha, fun X _ => by
      show (φ (f X) - φ M) / (φ A - φ M) = a * ((φ X - φ M) / (φ A - φ M))
      rw [hfa, mul_div_assoc]⟩
  · intro c hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    exact ⟨f, hf, fun X _ => by
      show (φ (f X) - φ M) / (φ A - φ M) = c * ((φ X - φ M) / (φ A - φ M))
      rw [hfv, mul_div_assoc]⟩

/-- The rotation `z ↦ c z` (`|c| = 1`) as a permutation of the unit disc. -/
noncomputable def rotPerm (c : ℂ) (hc : ‖c‖ = 1) : Equiv.Perm (Metric.ball (0 : ℂ) 1) where
  toFun z := ⟨c * z, by
    rw [mem_ball_zero_iff, norm_mul, hc, one_mul]; exact mem_ball_zero_iff.1 z.2⟩
  invFun z := ⟨c⁻¹ * z, by
    rw [mem_ball_zero_iff, norm_mul, norm_inv, hc, inv_one, one_mul]; exact mem_ball_zero_iff.1 z.2⟩
  left_inv z := Subtype.ext (inv_mul_cancel_left₀ (ne_zero_of_norm_eq_one hc) _)
  right_inv z := Subtype.ext (mul_inv_cancel_left₀ (ne_zero_of_norm_eq_one hc) _)

/-- In a hyperbolic geometry (whose displacements form a group) the rotations about `M` act on a
true circle about `M` as the ordinary rotations act on the ordinary circle: after the displacement
`η` carrying `M` into the centre of the disc, the rotations about `M` are the maps `z ↦ c z`. -/
theorem rotationsOfTrueCircle_of_isHyperbolic {G : Geometry} (h1 : AxiomIGroup G)
    (hH : IsHyperbolicGeometry G) {M A : G.S} (hAM : A ≠ M) :
    ∃ ψ : G.S → ℂ, BijOn ψ (TrueCircle G M A) (Metric.sphere 0 1) ∧
      (∀ f, IsRotationAbout G f M → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X ∈ TrueCircle G M A, ψ (f X) = c * ψ X) ∧
      ∀ c : ℂ, ‖c‖ = 1 → ∃ f, IsRotationAbout G f M ∧ ∀ X ∈ TrueCircle G M A, ψ (f X) = c * ψ X := by
  obtain ⟨φ, hφ⟩ := hH
  have hm : ‖(φ M : ℂ)‖ < 1 := mem_ball_zero_iff.1 (φ M).2
  obtain ⟨η, hηv⟩ : ∃ η : Equiv.Perm G.S, ∀ X, (φ (η X) : ℂ) = mob (φ M) (φ X) :=
    ⟨(φ.trans (mobPerm (φ M) hm)).trans φ.symm, fun X => by
      rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply]; rfl⟩
  have hηD : η ∈ G.D := (hφ _).2 ⟨1, φ M, norm_one, hm, fun X => by
    rw [hηv X, one_mul]; rfl⟩
  have hηM : (φ (η M) : ℂ) = 0 := by
    rw [hηv M]; simp [mob]
  have hd : (φ (η A) : ℂ) ≠ 0 := fun e =>
    hAM (η.injective (φ.injective (Subtype.ext (e.trans hηM.symm))))
  -- a displacement fixing `η M` is a rotation `z ↦ c z` in the chart
  have hcen : ∀ g ∈ G.D, g (η M) = η M → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X, (φ (g X) : ℂ) = c * φ X := by
    intro g hg hgM
    obtain ⟨c, a, hc, -, hca⟩ := (hφ g).1 hg
    have e := hca (η M)
    rw [hgM, hηM] at e
    simp only [mul_zero, sub_zero, div_one, zero_sub] at e
    have ha0 : a = 0 := by
      have : c * a = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left (ne_zero_of_norm_eq_one hc)
    refine ⟨c, hc, fun X => ?_⟩
    rw [hca X, ha0]
    simp only [map_zero, zero_mul, sub_zero, div_one]
  have hrot : ∀ f, IsRotationAbout G f M →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ X, (φ (η (f X)) : ℂ) = c * φ (η X) := by
    rintro f ⟨hfD, hfM⟩
    obtain ⟨c, hc, hcX⟩ := hcen ((η.symm.trans f).trans η)
      (h1.1 _ (h1.1 _ (h1.2.2 η hηD) f hfD) η hηD)
      (by simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hfM])
    refine ⟨c, hc, fun X => ?_⟩
    have := hcX (η X)
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using this
  have hrotc : ∀ c : ℂ, ‖c‖ = 1 →
      ∃ f, IsRotationAbout G f M ∧ ∀ X, (φ (η (f X)) : ℂ) = c * φ (η X) := by
    intro c hc
    obtain ⟨r, hrv⟩ : ∃ r : Equiv.Perm G.S, ∀ X, (φ (r X) : ℂ) = c * φ X :=
      ⟨(φ.trans (rotPerm c hc)).trans φ.symm, fun X => by
        rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply]; rfl⟩
    have hrD : r ∈ G.D := (hφ _).2 ⟨c, 0, hc, by rw [norm_zero]; exact one_pos, fun X => by
      rw [hrv X]
      simp only [map_zero, zero_mul, sub_zero, div_one]⟩
    refine ⟨(η.trans r).trans η.symm, ⟨h1.1 _ (h1.1 η hηD r hrD) _ (h1.2.2 η hηD), ?_⟩,
      fun X => ?_⟩
    · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq]
      apply φ.injective
      apply Subtype.ext
      rw [hrv, hηM, mul_zero]
    · rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply]
      exact hrv (η X)
  refine ⟨fun X => (φ (η X) : ℂ) / φ (η A), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro X ⟨f, hf, rfl⟩
    obtain ⟨c, hc, hcX⟩ := hrot f hf
    show (φ (η (f A)) : ℂ) / φ (η A) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, hcX, mul_div_assoc, div_self hd, mul_one, hc]
  · intro X _ Y _ e
    exact η.injective (φ.injective (Subtype.ext ((div_left_inj₀ hd).1 e)))
  · intro c hc
    rw [mem_sphere_zero_iff_norm] at hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    refine ⟨f A, ⟨f, hf, rfl⟩, ?_⟩
    show (φ (η (f A)) : ℂ) / φ (η A) = c
    rw [hfv, mul_div_assoc, div_self hd, mul_one]
  · intro f hf
    obtain ⟨c, hc, hcX⟩ := hrot f hf
    exact ⟨c, hc, fun X _ => by
      show (φ (η (f X)) : ℂ) / φ (η A) = c * ((φ (η X) : ℂ) / φ (η A))
      rw [hcX, mul_div_assoc]⟩
  · intro c hc
    obtain ⟨f, hf, hfv⟩ := hrotc c hc
    exact ⟨f, hf, fun X _ => by
      show (φ (η (f X)) : ℂ) / φ (η A) = c * ((φ (η X) : ℂ) / φ (η A))
      rw [hfv, mul_div_assoc]⟩

/-- **`RotationsOfTrueCircle` follows from the main theorem** (for a plane that has a point). -/
theorem rotationsOfTrueCircle_of_main (h : AppendixMainTheoremNonempty) :
    RotationsOfTrueCircle := by
  intro G h1 h2 h3 M A hAM
  rcases h G ⟨A, A.2⟩ h1 h2 h3 with hE | hH
  · exact rotationsOfTrueCircle_of_isEuclidean hE hAM
  · exact rotationsOfTrueCircle_of_isHyperbolic h1 hH hAM

end Appendix

end HilbertFoundations
