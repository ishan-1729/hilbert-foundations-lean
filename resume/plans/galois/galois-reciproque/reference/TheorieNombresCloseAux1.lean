import GaloisOeuvres.Radicaux

/-!
# Every finite transitive permutation group is the group of an equation

Auxiliary file for the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`).

Let `Γ` be a group of permutations of a finite set `X` of letters, transitive on `X`. The
substitutions of the letters act on the field `Fonctions X` of the rational functions of the
letters (rational coefficients); `Corps Γ` is the field of the functions invariant under `Γ`.
The letters are the roots of an irreducible equation `equation Γ x₀` over `Corps Γ` (the minimal
polynomial of one letter), of degree the number of letters (`natDegree_equation`), and the group
of this equation, acting on its roots in an algebraically closed field `Cloture Γ`, is `Γ` acting
on the letters: `versGal` is an isomorphism from `Γ` onto the group (`versGal_injective`,
`versGal_surjective`) and `racine` a labelling of the roots by the letters compatible with the
actions (`galActionHom_racine`). Hence the group of the equation is primitive if `Γ` is
(`primitif`), and the equation is solvable by radicals if `Γ` is solvable (`soluble`).
-/

open Polynomial

namespace GaloisOeuvres.TheorieNombres.Realisation

section Action

variable (X : Type)

/-- The field of rational functions of the letters. -/
abbrev Fonctions : Type := FractionRing (MvPolynomial X ℚ)

/-- The letter `x_i`. -/
noncomputable def lettre (i : X) : Fonctions X :=
  algebraMap (MvPolynomial X ℚ) (Fonctions X) (MvPolynomial.X i)

theorem lettre_injective : Function.Injective (lettre X) := fun _ _ h =>
  MvPolynomial.X_injective (IsFractionRing.injective (MvPolynomial X ℚ) (Fonctions X) h)

/-- The substitutions of the letters, as automorphisms of the polynomial ring. -/
noncomputable def permRing : Equiv.Perm X →* (MvPolynomial X ℚ ≃+* MvPolynomial X ℚ) where
  toFun σ := (MvPolynomial.renameEquiv ℚ σ).toRingEquiv
  map_one' := by
    apply RingEquiv.ext; intro q
    change MvPolynomial.rename (⇑(1 : Equiv.Perm X)) q = q
    rw [Equiv.Perm.coe_one, MvPolynomial.rename_id]; rfl
  map_mul' σ τ := by
    apply RingEquiv.ext; intro q
    change MvPolynomial.rename (⇑(σ * τ)) q = MvPolynomial.rename σ (MvPolynomial.rename τ q)
    rw [MvPolynomial.rename_rename]; rfl

/-- The substitutions of the letters act on the rational functions. -/
noncomputable instance actionPerm : MulSemiringAction (Equiv.Perm X) (Fonctions X) :=
  MulSemiringAction.compHom (Fonctions X)
    ((IsFractionRing.ringEquivOfRingEquivHom (MvPolynomial X ℚ) (Fonctions X)).comp (permRing X))

theorem smul_lettre (σ : Equiv.Perm X) (i : X) : σ • lettre X i = lettre X (σ i) := by
  change IsFractionRing.ringEquivOfRingEquiv ((MvPolynomial.renameEquiv ℚ σ).toRingEquiv)
    (algebraMap (MvPolynomial X ℚ) (Fonctions X) (MvPolynomial.X i)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change algebraMap _ _ (MvPolynomial.rename σ (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]; rfl

end Action

/-- Solvable group ⇒ solvable by radicals. -/
theorem soluble_of_isSolvable_gal {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] {p : K[X]} (hp : Irreducible p) (h : Group.IsSolvable p.Gal) :
    SolubleParRadicaux p Ω := by
  intro x hx
  have hx' : aeval x p = 0 := (mem_rootSet.1 hx).2
  have hint : IsIntegral K x := IsAlgebraic.isIntegral ⟨p, hp.ne_zero, hx'⟩
  apply mem_solvableByRad_of_isSolvable hint
  exact Group.isSolvable_of_surjective
    (Gal.restrictDvd_surjective (minpoly.dvd K x hx') hp.ne_zero)

section Corps

variable {X : Type} (Γ : Subgroup (Equiv.Perm X))

theorem smul_lettre' (γ : Γ) (i : X) : γ • lettre X i = lettre X (γ • i) :=
  smul_lettre X (γ : Equiv.Perm X) i

instance faithful : FaithfulSMul Γ (Fonctions X) := ⟨fun {a b} h => by
  apply Subtype.ext; apply Equiv.ext; intro i
  apply lettre_injective X
  have := h (lettre X i)
  rwa [smul_lettre', smul_lettre'] at this⟩

/-- The field of the rational functions invariant under `Γ`. -/
abbrev Corps : Type := ↥(FixedPoints.subfield Γ (Fonctions X))

instance : CharZero (Corps Γ) :=
  (algebraMap (Corps Γ) (Fonctions X)).charZero

/-- The equation whose roots are the letters. -/
noncomputable def equation (x₀ : X) : (Corps Γ)[X] := minpoly (Corps Γ) (lettre X x₀)

/-- The algebraically closed field in which the roots are taken. -/
abbrev Cloture : Type := AlgebraicClosure (Corps Γ)

instance splitsΩ (x₀ : X) :
    Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Cloture Γ))).Splits) :=
  ⟨IsAlgClosed.splits _⟩

variable [Finite X] (x₀ : X)

theorem equation_irreducible : Irreducible (equation Γ x₀) :=
  minpoly.irreducible (FixedPoints.isIntegral Γ (Fonctions X) (lettre X x₀))

instance splitsF : Fact (((equation Γ x₀).map (algebraMap (Corps Γ) (Fonctions X))).Splits) :=
  ⟨Normal.splits inferInstance _⟩

/-- The group `Γ` as the group of the equation. -/
noncomputable def versGal : Γ →* (equation Γ x₀).Gal :=
  (Gal.restrict (equation Γ x₀) (Fonctions X)).comp
    (MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X))

theorem versGal_surjective : Function.Surjective (versGal Γ x₀) :=
  (Gal.restrict_surjective (equation Γ x₀) (Fonctions X)).comp
    (FixedPoints.toAlgAut_surjective Γ (Fonctions X))

theorem soluble [Group.IsSolvable Γ] : SolubleParRadicaux (equation Γ x₀) (Cloture Γ) :=
  soluble_of_isSolvable_gal (equation_irreducible Γ x₀)
    (Group.isSolvable_of_surjective (versGal_surjective Γ x₀))

section Transitif

variable [MulAction.IsPretransitive Γ X]

omit [Finite X] in
theorem aeval_lettre (i : X) : aeval (lettre X i) (equation Γ x₀) = 0 := by
  obtain ⟨γ, rfl⟩ := MulAction.exists_smul_eq Γ x₀ i
  have h : lettre X (γ • x₀) =
      MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X) γ (lettre X x₀) :=
    (smul_lettre' Γ γ x₀).symm
  have h0 : aeval (lettre X x₀) (equation Γ x₀) = 0 := minpoly.aeval _ _
  rw [h, aeval_algHom_apply, h0, map_zero]

omit [MulAction.IsPretransitive Γ X] in
theorem exists_lettre_of_root {y : Fonctions X} (hy : aeval y (equation Γ x₀) = 0) :
    ∃ i, y = lettre X i := by
  have h1 : minpoly (Corps Γ) y = minpoly (Corps Γ) (lettre X x₀) :=
    (minpoly.eq_of_irreducible_of_monic (equation_irreducible Γ x₀) hy
      (minpoly.monic (FixedPoints.isIntegral Γ (Fonctions X) (lettre X x₀)))).symm
  obtain ⟨φ, hφ⟩ := (Normal.minpoly_eq_iff_mem_orbit (Fonctions X)).mp h1
  obtain ⟨γ, rfl⟩ := FixedPoints.toAlgAut_surjective Γ (Fonctions X) φ
  exact ⟨γ • x₀, hφ.symm.trans (smul_lettre' Γ γ x₀)⟩

/-- The labelling of the roots (in the field of rational functions) by the letters. -/
noncomputable def racineF : X ≃ (equation Γ x₀).rootSet (Fonctions X) :=
  Equiv.ofBijective
    (fun i => ⟨lettre X i, mem_rootSet.mpr ⟨(equation_irreducible Γ x₀).ne_zero,
      aeval_lettre Γ x₀ i⟩⟩)
    ⟨fun _ _ h => lettre_injective X (congrArg Subtype.val h),
      fun y => by
        obtain ⟨i, hi⟩ := exists_lettre_of_root Γ x₀ (mem_rootSet.mp y.2).2
        exact ⟨i, Subtype.ext hi.symm⟩⟩

theorem versGal_smul (γ : Γ) (i : X) :
    versGal Γ x₀ γ • racineF Γ x₀ i = racineF Γ x₀ (γ • i) := by
  apply Subtype.ext
  exact (Gal.restrict_smul (MulSemiringAction.toAlgAut Γ (Corps Γ) (Fonctions X) γ)
    (racineF Γ x₀ i)).trans (smul_lettre' Γ γ i)

theorem versGal_injective : Function.Injective (versGal Γ x₀) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext; apply Equiv.ext; intro i
  have h := versGal_smul Γ x₀ γ i
  rw [hγ, one_smul] at h
  exact ((racineF Γ x₀).injective h).symm

theorem natDegree_equation : (equation Γ x₀).natDegree = Nat.card X := by
  rw [← card_rootSet_eq_natDegree (equation_irreducible Γ x₀).separable
    (Fact.out : ((equation Γ x₀).map (algebraMap (Corps Γ) (Fonctions X))).Splits),
    ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (racineF Γ x₀)).symm

/-- The labelling of the roots in `Ω` by the letters. -/
noncomputable def racine : X ≃ (equation Γ x₀).rootSet (Cloture Γ) :=
  (racineF Γ x₀).trans (Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ))

theorem galActionHom_racine (γ : Γ) (i : X) :
    Gal.galActionHom (equation Γ x₀) (Cloture Γ) (versGal Γ x₀ γ) (racine Γ x₀ i) =
      racine Γ x₀ (γ • i) := by
  change versGal Γ x₀ γ • Gal.rootsEquivRoots (equation Γ x₀) (Fonctions X) (Cloture Γ)
    (racineF Γ x₀ i) = _
  rw [Gal.smul_rootsEquivRoots, versGal_smul]; rfl

theorem card_gal : Nat.card (equation Γ x₀).Gal = Nat.card Γ :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨versGal_injective Γ x₀, versGal_surjective Γ x₀⟩)).symm

end Transitif

theorem primitif [MulAction.IsPreprimitive Γ X] :
    MulAction.IsPreprimitive (groupe (equation Γ x₀) (Cloture Γ))
      ((equation Γ x₀).rootSet (Cloture Γ)) := by
  let φ : Γ → groupe (equation Γ x₀) (Cloture Γ) := fun γ =>
    (Gal.galActionHom (equation Γ x₀) (Cloture Γ)).rangeRestrict (versGal Γ x₀ γ)
  let j : X →ₑ[φ] (equation Γ x₀).rootSet (Cloture Γ) :=
    { toFun := racine Γ x₀
      map_smul' := fun γ i => (galActionHom_racine Γ x₀ γ i).symm }
  exact MulAction.IsPreprimitive.of_surjective (f := j) (racine Γ x₀).surjective

end Corps

end GaloisOeuvres.TheorieNombres.Realisation
