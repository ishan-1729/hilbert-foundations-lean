import GaloisOeuvres.TheorieNombres
import GaloisOeuvres.EquationsPrimitives
import GaloisOeuvres.TheorieNombresCloseAux1
import GaloisOeuvres.TheorieNombresCloseAux2

/-!
# The converse for primitive equations of degree `p^ν`: refutation and correction

This file closes the unit `nombres.reciproque` of *Sur la théorie des nombres*
(`GaloisOeuvres/TheorieNombres.lean`), where Galois's claim is stated as `ReciproqueGalois`.

* `not_reciproqueGalois`: the claim is false for every prime `ℓ`, already in degree `ℓ⁴`. The
  group `AGL(1, ℓ²) ≀ C₂` of substitutions of `ℓ⁴` letters (`Couronne.couronne`) is primitive and
  solvable, it is the group of an equation (`Realisation.equation`), and its order does not divide
  the number `ℓ⁴ (ℓ⁴ - 1) · 4` of Galois's substitutions.
* `reciproque_corrigee`: what is true. The roots of a primitive equation of degree `p^ν` solvable
  by radicals can be labelled by the `p^ν` imaginaries so that its group consists of linear
  substitutions `k ↦ A k + b`, `A` an invertible linear map of the `ℤ/p`-vector space of the
  imaginaries (`AGL`), and contains all the translations. Galois's substitutions
  `k ↦ (a k + b)^(p^r)` are of this kind (`AGammaL_le_AGL`).
-/

open Polynomial

namespace GaloisOeuvres.TheorieNombres

/-- **The linear substitutions** `k ↦ A k + b` of the points of a vector space over `ℤ/p`
(`A` an invertible linear map): the affine group. -/
def AGL (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∃ A : V ≃ₗ[ZMod p] V, ∃ b : V, ∀ k, σ k = A k + b}
  one_mem' := ⟨LinearEquiv.refl _ _, 0, fun k => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨A, b, hσ⟩ ⟨A', b', hτ⟩
    exact ⟨A'.trans A, A b' + b, fun k => by
      rw [Equiv.Perm.mul_apply, hτ, hσ, map_add, LinearEquiv.trans_apply, add_assoc]⟩
  inv_mem' := by
    rintro σ ⟨A, b, hσ⟩
    refine ⟨A.symm, -(A.symm b), fun k => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hσ, map_add, map_neg, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    abel

theorem mem_AGL_of_linearMap {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {σ : Equiv.Perm V} (A : V →ₗ[ZMod p] V) (b : V) (h : ∀ k, σ k = A k + b) : σ ∈ AGL p V := by
  have hA : ∀ k, A k = σ k - b := fun k => by rw [h]; abel
  have hbij : Function.Bijective A := by
    constructor
    · intro k k' hk
      apply σ.injective
      rw [h, h, hk]
    · intro y
      refine ⟨σ.symm (y + b), ?_⟩
      rw [hA, Equiv.apply_symm_apply]; abel
  exact ⟨LinearEquiv.ofBijective A hbij, b, fun k => by rw [LinearEquiv.ofBijective_apply, h]⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-- Galois's substitutions are linear substitutions: `AΓL(1, p^ν) ≤ AGL(ν, p)`. -/
theorem AGammaL_le_AGL (K : Type*) [Field K] [Finite K] [Algebra (ZMod p) K] :
    AGammaL (p := p) K ≤ AGL p K := by
  rintro σ ⟨r, A, -, B, h⟩
  refine mem_AGL_of_linearMap
    ((LinearMap.mulLeft (ZMod p) A).comp
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K ^ r).toLinearMap) B fun k => ?_
  rw [h, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgEquiv.toLinearMap_apply,
    frob_pow_apply]

/-- **The corrected converse** (Galois, Jordan). -/
theorem reciproque_corrigee {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)] {ν : ℕ} (hν : ν ≠ 0)
    (hirr : Irreducible f) (hdeg : f.natDegree = p ^ ν)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ e : GaloisField p ν ≃ f.rootSet Ω,
      (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL p (GaloisField p ν)) ∧
      ∀ b : GaloisField p ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b := by
  classical
  have hdeg0 : (f.map (algebraMap K Ω)).degree ≠ 0 := by
    rw [degree_map]; exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap K Ω)) hdeg0
  have hxr : x ∈ f.rootSet Ω := by
    rw [mem_rootSet]; exact ⟨hirr.ne_zero, by rwa [aeval_def, eval₂_eq_eval_map]⟩
  have hG : Group.IsSolvable f.Gal :=
    isSolvable_gal_of_irreducible (hsol x hxr) hirr (mem_rootSet.mp hxr).2
  have : Group.IsSolvable (groupe f Ω) :=
    Group.isSolvable_of_surjective (Gal.galActionHom f Ω).rangeRestrict_surjective
  have hcard : Nat.card (f.rootSet Ω) = p ^ ν := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hirr.separable
      (Fact.out : (f.map (algebraMap K Ω)).Splits), hdeg]
  have hp2 := hp.out.two_le
  have : Nontrivial (f.rootSet Ω) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]; exact Nat.one_lt_pow hν hp.out.one_lt)
  obtain ⟨q, μ, hq, e₀, hlin, htr⟩ :=
    EquationsPrimitives.exists_affine_indexing (G := groupe f Ω) (X := f.rootSet Ω)
  have hcard' : q ^ μ = p ^ ν := by
    rw [← hcard, Nat.card_congr e₀, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard'
    exact (Nat.one_lt_pow hν hp.out.one_lt).ne hcard'
  have hpq : p = q := by
    have h1 : q ∣ p ^ ν := by rw [← hcard']; exact dvd_pow_self q hμ
    exact ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow h1)).symm
  subst hpq
  have hνμ : ν = μ := (Nat.pow_right_injective hp2 hcard').symm
  subst hνμ
  let B : GaloisField p ν ≃ₗ[ZMod p] (Fin ν → ZMod p) :=
    (Module.finBasisOfFinrankEq (ZMod p) (GaloisField p ν) (GaloisField.finrank p hν)).equivFun
  refine ⟨B.toEquiv.trans e₀.symm, fun σ => ?_, fun b => ?_⟩
  · obtain ⟨M, -, c, hM⟩ := hlin ⟨Gal.galActionHom f Ω σ, ⟨σ, rfl⟩⟩
    refine mem_AGL_of_linearMap ((B.symm.toLinearMap.comp M.mulVecLin).comp B.toLinearMap)
      (B.symm c) fun k => ?_
    change B.symm (e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k)))) = _
    have := hM (e₀.symm (B k))
    rw [Equiv.apply_symm_apply] at this
    change e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k))) = _ at this
    rw [this, map_add]
    rfl
  · obtain ⟨g, hg⟩ := htr (B b)
    obtain ⟨σ, hσ⟩ := g.2
    refine ⟨σ, fun k => ?_⟩
    change B.symm (e₀ (Gal.galActionHom f Ω σ (e₀.symm (B k)))) = _
    have := hg (e₀.symm (B k))
    rw [Equiv.apply_symm_apply] at this
    rw [hσ]
    change e₀ ((g : Equiv.Perm (f.rootSet Ω)) (e₀.symm (B k))) = _ at this
    rw [this, map_add, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- **The corrected converse, with the degree.** -/
theorem reciproque_corrigee_degre {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (f : K[X]) [Fact ((f.map (algebraMap K Ω)).Splits)]
    (hirr : Irreducible f) (hdeg : f.natDegree ≠ 1)
    (hprim : MulAction.IsPreprimitive (groupe f Ω) (f.rootSet Ω))
    (hsol : SolubleParRadicaux f Ω) :
    ∃ (ℓ ν : ℕ) (_ : Fact ℓ.Prime), ν ≠ 0 ∧ f.natDegree = ℓ ^ ν ∧
      ∃ e : GaloisField ℓ ν ≃ f.rootSet Ω,
        (∀ σ : f.Gal, groupeIndice f e σ ∈ AGL ℓ (GaloisField ℓ ν)) ∧
        ∀ b : GaloisField ℓ ν, ∃ σ : f.Gal, ∀ k, groupeIndice f e σ k = k + b := by
  obtain ⟨q, k, hq, hk⟩ := degre_primitive f hirr hprim hsol
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hdeg (by rw [hk, pow_zero])
  have := Fact.mk hq
  exact ⟨q, k, ⟨hq⟩, hk0, hk, reciproque_corrigee f hk0 hirr hk hprim hsol⟩

/-- What the printed claim would give for a solvable primitive group of degree `ℓ ^ ν`. -/
theorem card_dvd_of_reciproque (ℓ : ℕ) [Fact ℓ.Prime] (H : ReciproqueGalois ℓ) {X : Type}
    [Finite X] (Γ : Subgroup (Equiv.Perm X)) [MulAction.IsPreprimitive Γ X] [Group.IsSolvable Γ]
    (ν : ℕ) (hν : ν ≠ 0) (h9 : ℓ ^ ν ≠ 9) (h25 : ℓ ^ ν ≠ 25) (hX : Nat.card X = ℓ ^ ν) :
    Nat.card Γ ∣ ℓ ^ ν * (ℓ ^ ν - 1) * ν := by
  obtain ⟨x₀⟩ : Nonempty X :=
    (Nat.card_pos_iff.mp (by rw [hX]; exact pow_pos (Fact.out : ℓ.Prime).pos ν)).1
  rw [← Realisation.card_gal Γ x₀]
  exact reciproque_borne ℓ H (Realisation.Corps Γ) (Realisation.Cloture Γ)
    (Realisation.equation Γ x₀) ν hν h9 h25 (Realisation.equation_irreducible Γ x₀)
    ((Realisation.natDegree_equation Γ x₀).trans hX) (Realisation.primitif Γ x₀)
    (Realisation.soluble Γ x₀)

/-- **Galois's converse claim, read literally, is false for every prime `ℓ`.** -/
theorem not_reciproqueGalois (ℓ : ℕ) [Fact ℓ.Prime] : ¬ ReciproqueGalois ℓ := by
  intro H
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hF : Nat.card (GaloisField ℓ 2) = ℓ ^ 2 := GaloisField.card ℓ 2 two_ne_zero
  have h4le : 4 ≤ ℓ ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
  have h3 : ∃ c : GaloisField ℓ 2, c ≠ 0 ∧ c ≠ 1 :=
    Couronne.exists_ne_zero_ne_one (by rw [hF]; omega)
  have := Couronne.couronne_primitif h3
  have := Couronne.couronne_soluble (F := GaloisField ℓ 2)
  have hX : Nat.card (GaloisField ℓ 2 × GaloisField ℓ 2) = ℓ ^ 4 := by
    rw [Nat.card_prod, hF]; ring
  have hpow : ℓ ^ 4 = 16 ∨ 81 ≤ ℓ ^ 4 := by
    rcases hℓ.eq_or_lt with h | h
    · left; rw [← h]; norm_num
    · right
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ ℓ ^ 4 := Nat.pow_le_pow_left h 4
  have h := card_dvd_of_reciproque ℓ H (Couronne.couronne (GaloisField ℓ 2)) 4 (by norm_num)
    (by omega) (by omega) hX
  have h2 := (Couronne.two_mul_dvd_card (F := GaloisField ℓ 2)).trans h
  rw [hF] at h2
  exact Couronne.arith ℓ hℓ h2

end GaloisOeuvres.TheorieNombres
