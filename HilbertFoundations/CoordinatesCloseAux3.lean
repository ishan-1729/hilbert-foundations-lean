import HilbertFoundations.CoordinatesCloseAux2
import HilbertFoundations.DesarguesAlgebra
import HilbertFoundations.Proportion

/-!
# Helper for the co-ordinates of space (§ 17, § 30): the two co-ordinatizations of a plane

Helper module of `CoordinatesClose.lean` (units `s17.space`, `s30.any_dimension`). The general
theorem `SpaceCoord.exists_space_coords` (CoordinatesCloseAux2.lean) extends co-ordinates of a plane
`α` of a geometry of space with I–III to co-ordinates of space. It is applied here to

* the co-ordinates of a desarguesian plane over its segments (`DesAlg.Vec F` over `(Seg F)ᵐᵒᵖ`,
  DesarguesAlgebra.lean): `any_dimension` (§ 30);
* the rectangular co-ordinates of a plane with I–IV over its field of segments (`Pas.G ax`,
  Proportion.lean): `space_coordinates` (§ 17).
-/

namespace HilbertFoundations

namespace SpaceCoord

open Module

universe u v w

/-! ## Linear images of a co-ordinatized space -/

section Embed

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsStrictOrderedRing K]
variable {W : Type*} [AddCommGroup W] [Module K W] {W' : Type*} [AddCommGroup W'] [Module K W']

omit [IsStrictOrderedRing K] in
/-- A co-ordinatized space, followed by an injective linear map: lines and planes go onto the
points of affine subspaces of dimension 1 and 2, betweenness is preserved and reflected. -/
theorem embed_linear (f : P ≃ AffPt K W)
    (hl : ∀ ℓ : L, ∃ m : AffLine K W, ∀ X : P, X ∈ ℓ ↔ f X ∈ m)
    (hp : ∀ π : Pl, ∃ S : AffPlane K W, ∀ X : P, X ∈ π ↔ f X ∈ S)
    (hb : ∀ X Y Z : P, Between (f X) (f Y) (f Z) ↔ Between X Y Z)
    (ψ : AffPt K W →ₗ[K] AffPt K W') (hψ : Function.Injective ψ) :
    Function.Injective (fun X : P => ψ (f X)) ∧
      (∀ A B C : P, Between A B C ↔ Sbtw K (ψ (f A)) (ψ (f B)) (ψ (f C))) ∧
      (∀ l : L, ∃ S : AffineSubspace K (AffPt K W'),
        finrank K S.direction = 1 ∧ ∀ X : P, X ∈ l ↔ ψ (f X) ∈ S) ∧
      (∀ π : Pl, ∃ S : AffineSubspace K (AffPt K W'),
        finrank K S.direction = 2 ∧ ∀ X : P, X ∈ π ↔ ψ (f X) ∈ S) := by
  have hinj' : Function.Injective ψ.toAffineMap := hψ
  have hfr : ∀ S : AffineSubspace K (AffPt K W),
      finrank K (S.map ψ.toAffineMap).direction = finrank K S.direction := fun S => by
    rw [AffineSubspace.map_direction, LinearMap.toAffineMap_linear]
    exact (Submodule.equivMapOfInjective _ hψ S.direction).finrank_eq.symm
  have hmem : ∀ (S : AffineSubspace K (AffPt K W)) (X : AffPt K W),
      X ∈ S ↔ ψ X ∈ S.map ψ.toAffineMap := fun S X => by
    rw [AffineSubspace.mem_map]
    constructor
    · intro h; exact ⟨X, h, rfl⟩
    · rintro ⟨Y, hY, e⟩
      have : Y = X := hψ e
      rw [← this]; exact hY
  refine ⟨fun X Y h => f.injective (hψ h), fun A B C => ?_, fun l => ?_, fun π => ?_⟩
  · rw [← hb A B C]
    exact (hinj'.sbtw_map_iff (x := f A) (y := f B) (z := f C)).symm
  · obtain ⟨m, hm⟩ := hl l
    exact ⟨m.carrier.map ψ.toAffineMap, by rw [hfr]; exact m.finrank_direction,
      fun X => (hm X).trans (hmem m.carrier (f X))⟩
  · obtain ⟨S, hS⟩ := hp π
    exact ⟨S.carrier.map ψ.toAffineMap, by rw [hfr]; exact S.finrank_direction,
      fun X => (hS X).trans (hmem S.carrier (f X))⟩

end Embed

/-! ## The co-ordinates of a desarguesian plane -/

section DesPlane

open DesAlg MulOpposite

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [PlaneOrder P L]
  [PlaneParallels P L] [Nonempty L] [hDF : Fact (DesarguesII P)] (F : DesAlg.Frame P)

/-- The lines of a desarguesian plane are the lines of the vector space of its points. -/
theorem desAlg_line (a : L) : ∃ O d : DesAlg.Vec F, d ≠ 0 ∧
    ∀ Z : P, Z ∈ a ↔ (DesAlg.Vec.ofP Z : DesAlg.Vec F) ∈ PLine (DesAlg.Seg F)ᵐᵒᵖ O d := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
  refine ⟨DesAlg.Vec.ofP A, DesAlg.Vec.ofP B - DesAlg.Vec.ofP A,
    sub_ne_zero.2 fun h => hAB (DesAlg.Vec.ofP_injective (F := F) h).symm, fun Z => ?_⟩
  rw [← DesAlg.ln_eq hAB hA hB, DesAlg.mem_ln_iff_smul (F := F) hAB]
  rfl

/-- Betweenness in a desarguesian plane is betweenness in the vector space of its points. -/
theorem desAlg_between (X Y Z : P) :
    Sbtw (DesAlg.Seg F)ᵐᵒᵖ (DesAlg.Vec.ofP X : DesAlg.Vec F) (DesAlg.Vec.ofP Y)
      (DesAlg.Vec.ofP Z) ↔ Between X Y Z := by
  by_cases hXZ : X = Z
  · subst hXZ
    exact ⟨fun h => absurd rfl h.left_ne_right,
      fun h => absurd rfl (ne13_of_between (Line := L) h)⟩
  rw [DesAlg.between_iff_param (F := F) hXZ]
  constructor
  · intro h
    obtain ⟨-, t, h0, h1, e⟩ := (AffPt.sbtw_iff_param (K := (DesAlg.Seg F)ᵐᵒᵖ)
      (V := DesAlg.Vec F) (A := DesAlg.Vec.ofP X) (B := DesAlg.Vec.ofP Y)
      (C := DesAlg.Vec.ofP Z)).1 h
    exact ⟨unop t, h0, h1, by rw [op_unop]; exact e⟩
  · rintro ⟨t, h0, h1, e⟩
    exact (AffPt.sbtw_iff_param (K := (DesAlg.Seg F)ᵐᵒᵖ)
      (V := DesAlg.Vec F) (A := DesAlg.Vec.ofP X) (B := DesAlg.Vec.ofP Y)
      (C := DesAlg.Vec.ofP Z)).2
      ⟨fun h => hXZ (DesAlg.Vec.ofP_injective (F := F) h), op t, h0, h1, e⟩

end DesPlane

/-! ## § 30: a geometry of space with I–III is part of a geometry of any dimension -/

section AnyDim

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [hO : SpaceOrder P L Pl] [hS : SpaceParallels P L Pl]

include hO hS

/-- **Every geometry of space with I, II, III having a plane has co-ordinates** in a vector space
of dimension 3 over an ordered skew field, in which its lines and planes are exactly the lines and
planes of the coordinate space, and betweenness is that of the coordinate space. -/
theorem exists_skew_coords (α : Pl) :
    ∃ (K : Type u) (_ : DivisionRing K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (W : Type u) (_ : AddCommGroup W) (_ : Module K W) (_ : finrank K W = 3)
      (f : P ≃ AffPt K W),
      (∀ ℓ : L, ∃ m : AffLine K W, ∀ X : P, X ∈ ℓ ↔ f X ∈ m) ∧
      (∀ m : AffLine K W, ∃ ℓ : L, ∀ X : P, X ∈ ℓ ↔ f X ∈ m) ∧
      (∀ π : Pl, ∃ S : AffPlane K W, ∀ X : P, X ∈ π ↔ f X ∈ S) ∧
      (∀ S : AffPlane K W, ∃ π : Pl, ∀ X : P, X ∈ π ↔ f X ∈ S) ∧
      ∀ X Y Z : P, Between (f X) (f Y) (f Z) ↔ Between X Y Z := by
  have := DesAlg.nonempty_lines_of_plane (P := P) (L := L) α
  have : Fact (DesAlg.DesarguesII {A : P // A ∈ α}) :=
    ⟨(planes_of_space_desarguesian (L := L) α).2⟩
  obtain ⟨F⟩ := DesAlg.exists_frame (P := {A : P // A ∈ α})
    (L := {a : L // LiesInPlane (Point := P) a α})
  let e : {A : P // A ∈ α} ≃ DesAlg.Vec F :=
    ⟨DesAlg.Vec.ofP, DesAlg.Vec.toP, fun _ => rfl, fun _ => rfl⟩
  have he : LineHyp (DesAlg.Seg F)ᵐᵒᵖ e := fun a ha => desAlg_line F ⟨a, ha⟩
  obtain ⟨f, -, h1, h2, h3, h4, h5⟩ :=
    exists_space_coords (K := (DesAlg.Seg F)ᵐᵒᵖ) (DesAlg.Vec.finrank_eq_two (F := F)) α e he
  refine ⟨(DesAlg.Seg F)ᵐᵒᵖ, inferInstance, inferInstance, inferInstance,
    DesAlg.Vec F × (DesAlg.Seg F)ᵐᵒᵖ, inferInstance, inferInstance, DesAlg.finrank_space F, f,
    h1, h2, h3, h4, h5 fun X Y Z => desAlg_between F X Y Z⟩

/-- **A geometry of space with I, II, III having a plane is a part of the coordinate geometry of
any dimension `n ≥ 3`** over an ordered skew field. -/
theorem any_dimension (α : Pl) {n : ℕ} (hn : 3 ≤ n) :
    ∃ (K : Type u) (_ : DivisionRing K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (f : P → AffPt K (Fin n → K)), Function.Injective f ∧
      (∀ A B C : P, Between A B C ↔ Sbtw K (f A) (f B) (f C)) ∧
      (∀ l : L, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        finrank K S.direction = 1 ∧ ∀ X : P, X ∈ l ↔ f X ∈ S) ∧
      (∀ π : Pl, ∃ S : AffineSubspace K (AffPt K (Fin n → K)),
        finrank K S.direction = 2 ∧ ∀ X : P, X ∈ π ↔ f X ∈ S) := by
  obtain ⟨K, iD, iL, iS, W, iA, iM, hW, f, h1, -, h3, -, h5⟩ :=
    exists_skew_coords (P := P) (L := L) α
  have : Module.Finite K W := Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  let b : Basis (Fin 3) K W := Module.finBasisOfFinrankEq K W hW
  let ψ : AffPt K W →ₗ[K] AffPt K (Fin n → K) :=
    (DesAlg.ext3 (K := K) n).comp (b.equivFun : W →ₗ[K] (Fin 3 → K))
  have hψ : Function.Injective ψ :=
    (DesAlg.ext3_injective (K := K) hn).comp b.equivFun.injective
  exact ⟨K, iD, iL, iS, fun X => ψ (f X), embed_linear f h1 h3 h5 ψ hψ⟩

end AnyDim

/-! ## § 17: the rectangular co-ordinates of a plane and the co-ordinates of space -/

section Alg

variable {K : Type*} [Field K]

/-- The solutions of a linear equation in `x`, `y` form a line of `K × K`. -/
theorem linEq_pline {p q : K} (h : p ≠ 0 ∨ q ≠ 0) (r : K) :
    ∃ O d : K × K, d ≠ 0 ∧ ∀ v : K × K, p * v.1 + q * v.2 + r = 0 ↔ v ∈ PLine K O d := by
  by_cases hp : p = 0
  · have hq : q ≠ 0 := h.resolve_left (not_not.2 hp)
    refine ⟨(0, -r / q), (1, 0), fun e => one_ne_zero (congrArg Prod.fst e), fun v => ?_⟩
    constructor
    · intro hv
      have hv2 : v.2 = -r / q := by
        rw [eq_div_iff hq]
        rw [hp] at hv
        linear_combination hv
      refine ⟨v.1, Prod.ext ?_ ?_⟩
      · show v.1 = v.1 * 1 + 0
        ring
      · show v.2 = v.1 * 0 + -r / q
        rw [hv2]; ring
    · rintro ⟨t, rfl⟩
      show p * (t * 1 + 0) + q * (t * 0 + -r / q) + r = 0
      have e : q * (-r / q) = -r := by rw [mul_comm, div_mul_cancel₀ _ hq]
      rw [hp]
      linear_combination e
  · refine ⟨(-r / p, 0), (q, -p), fun e => hp (neg_eq_zero.1 (congrArg Prod.snd e)),
      fun v => ?_⟩
    constructor
    · intro hv
      refine ⟨-v.2 / p, Prod.ext ?_ ?_⟩
      · show v.1 = -v.2 / p * q + -r / p
        rw [div_mul_eq_mul_div, ← add_div, eq_div_iff hp]
        linear_combination hv
      · show v.2 = -v.2 / p * -p + 0
        rw [add_zero, div_mul_eq_mul_div, eq_div_iff hp]
        ring
    · rintro ⟨t, rfl⟩
      show p * (t * q + -r / p) + q * (t * -p + 0) + r = 0
      have e : p * (-r / p) = -r := by rw [mul_comm, div_mul_cancel₀ _ hp]
      linear_combination e

/-- The linear form `a x + b y + c z` on `(K × K) × K`. -/
def lin3 (a b c : K) : AffPt K ((K × K) × K) →ₗ[K] K where
  toFun X := a * (AffPt.toV X).1.1 + b * (AffPt.toV X).1.2 + c * (AffPt.toV X).2
  map_add' X Y := by
    simp only [AffPt.toV_add, Prod.fst_add, Prod.snd_add]; ring
  map_smul' t X := by
    simp only [AffPt.toV_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

theorem lin3_apply (a b c : K) (X : AffPt K ((K × K) × K)) :
    lin3 a b c X = a * (AffPt.toV X).1.1 + b * (AffPt.toV X).1.2 + c * (AffPt.toV X).2 := rfl

theorem finrank_KKK : finrank K ((K × K) × K) = 3 := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]

/-- Every linear form on `(K × K) × K` is some `a x + b y + c z`. -/
theorem eq_lin3 (φ : AffPt K ((K × K) × K) →ₗ[K] K) :
    φ = lin3 (φ (AffPt.ofV ((1, 0), 0))) (φ (AffPt.ofV ((0, 1), 0))) (φ (AffPt.ofV ((0, 0), 1))) := by
  apply LinearMap.ext
  intro X
  have hX : X = (AffPt.toV X).1.1 • (AffPt.ofV ((1, 0), 0) : AffPt K ((K × K) × K)) +
      (AffPt.toV X).1.2 • (AffPt.ofV ((0, 1), 0) : AffPt K ((K × K) × K)) +
      (AffPt.toV X).2 • (AffPt.ofV ((0, 0), 1) : AffPt K ((K × K) × K)) := by
    apply AffPt.toV_injective
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
  conv_lhs => rw [hX]
  rw [map_add, map_add, map_smul, map_smul, map_smul, lin3_apply]
  simp only [smul_eq_mul]
  ring

/-- **Every plane of `(K × K) × K` is the solution set of a linear equation.** -/
theorem affPlane_eq (S : AffPlane K ((K × K) × K)) :
    ∃ a b c d : K, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      ∀ X : AffPt K ((K × K) × K), X ∈ S ↔ lin3 a b c X + d = 0 := by
  have : Module.Finite K (AffPt K ((K × K) × K)) :=
    inferInstanceAs (Module.Finite K ((K × K) × K))
  have hdim : finrank K (AffPt K ((K × K) × K)) = 3 := finrank_KKK
  have hW : finrank K S.carrier.direction = 2 := S.finrank_direction
  have hlt : S.carrier.direction < ⊤ := lt_top_iff_ne_top.2 fun h => by
    rw [h, finrank_top, hdim] at hW; omega
  obtain ⟨φ, hφ0, hWφ⟩ := S.carrier.direction.exists_le_ker_of_lt_top hlt
  have hk : finrank K (LinearMap.ker φ) < 3 := by
    have := Submodule.finrank_lt (s := LinearMap.ker φ) fun h => hφ0 (LinearMap.ker_eq_top.1 h)
    rwa [hdim] at this
  have hWeq : S.carrier.direction = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_le hWφ (by omega)
  obtain ⟨X0, hX0⟩ := AffPt.nonempty_plane S
  have hφ := eq_lin3 φ
  refine ⟨φ (AffPt.ofV ((1, 0), 0)), φ (AffPt.ofV ((0, 1), 0)), φ (AffPt.ofV ((0, 0), 1)),
    -φ X0, ?_, fun X => ?_⟩
  · by_contra hall
    simp only [not_or, not_not] at hall
    apply hφ0
    rw [hφ, hall.1, hall.2.1, hall.2.2]
    apply LinearMap.ext
    intro X
    simp [lin3_apply]
  · rw [← hφ]
    show X ∈ S.carrier ↔ _
    rw [AffPt.mem_iff_sub_mem_direction hX0, hWeq, LinearMap.mem_ker, map_sub, sub_eq_add_neg]

/-- **The zeros of a non-constant affine function on a space of dimension 3 form a plane.** -/
theorem exists_affPlane_of_functional {W : Type*} [AddCommGroup W] [Module K W]
    (hW : finrank K W = 3) (φ : AffPt K W →ₗ[K] K) {v : AffPt K W} (hv : φ v ≠ 0) (d : K) :
    ∃ S : AffPlane K W, ∀ X : AffPt K W, X ∈ S ↔ φ X + d = 0 := by
  have hdim : finrank K (AffPt K W) = 3 := hW
  have : Module.Finite K (AffPt K W) := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have hsurj : Function.Surjective φ := fun y =>
    ⟨(y / φ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
  have hker : finrank K (LinearMap.ker φ) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hdim] at h1
    omega
  obtain ⟨X0, hX0⟩ := hsurj (-d)
  refine ⟨⟨AffineSubspace.mk' X0 (LinearMap.ker φ), by
    rw [AffineSubspace.direction_mk']; exact hker⟩, fun X => ?_⟩
  show X ∈ AffineSubspace.mk' X0 (LinearMap.ker φ) ↔ _
  rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hX0, sub_neg_eq_add]

theorem lin3_e₁ (a b c : K) : lin3 a b c (AffPt.ofV ((1, 0), 0)) = a := by
  show a * 1 + b * 0 + c * 0 = a
  ring

theorem lin3_e₂ (a b c : K) : lin3 a b c (AffPt.ofV ((0, 1), 0)) = b := by
  show a * 0 + b * 1 + c * 0 = b
  ring

theorem lin3_e₃ (a b c : K) : lin3 a b c (AffPt.ofV ((0, 0), 1)) = c := by
  show a * 0 + b * 0 + c * 1 = c
  ring

/-- **Every linear equation in `(K × K) × K` represents a plane.** -/
theorem exists_affPlane_of_eq {a b c : K} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (d : K) :
    ∃ S : AffPlane K ((K × K) × K),
      ∀ X : AffPt K ((K × K) × K), X ∈ S ↔ lin3 a b c X + d = 0 := by
  have hv : ∃ v : AffPt K ((K × K) × K), lin3 a b c v ≠ 0 := by
    rcases h with h | h | h
    · exact ⟨AffPt.ofV ((1, 0), 0), by rw [lin3_e₁]; exact h⟩
    · exact ⟨AffPt.ofV ((0, 1), 0), by rw [lin3_e₂]; exact h⟩
    · exact ⟨AffPt.ofV ((0, 0), 1), by rw [lin3_e₃]; exact h⟩
  obtain ⟨v, hv⟩ := hv
  exact exists_affPlane_of_functional (W := (K × K) × K) finrank_KKK (lin3 a b c) hv d

end Alg

/-- A plane of a geometry of space with I, II, IV satisfies I, II, IV of plane geometry
(`planeCongruence`); an instance inside this namespace. -/
scoped instance instPlaneCongruence {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [HasSegCong P] [HasAngCong P] [SpaceCongruence P L Pl]
    (α : Pl) : PlaneCongruence {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  planeCongruence α

/-- A plane of a geometry of space with I, II, V satisfies V (`planeArchimedes`); an instance
inside this namespace. -/
scoped instance instPlaneArchimedes {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L]
    [HasPlanes P Pl] [HasBetween P] [HasSegCong P] [HasAngCong P] [SpaceOrder P L Pl]
    [Archimedes P L] (α : Pl) :
    Archimedes {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  planeArchimedes α

section Rect

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl] [hS : SpaceParallels P L Pl]

local notation "𝒫[" π "]" => {A : P // A ∈ π}
local notation "ℒ[" π "]" => {a : L // LiesInPlane (Point := P) a π}

/-- The rectangular co-ordinates of a plane of a geometry of space with I–IV. -/
noncomputable def rectEquiv (α : Pl) (ax : Pas.Axes 𝒫[α] ℒ[α]) : 𝒫[α] ≃ Pas.G ax × Pas.G ax :=
  Equiv.ofBijective _ (Pas.coords_bijective ax)

theorem rectEquiv_apply (α : Pl) (ax : Pas.Axes 𝒫[α] ℒ[α]) (Z : 𝒫[α]) :
    rectEquiv α ax Z = (Pas.px ax Z, Pas.py ax Z) := rfl

/-- In rectangular co-ordinates the lines of the plane are the lines of `K × K`. -/
theorem rect_lineHyp (α : Pl) (ax : Pas.Axes 𝒫[α] ℒ[α]) :
    LineHyp (Pas.G ax) (rectEquiv α ax) := by
  intro a ha
  obtain ⟨p, q, r, hpq, h⟩ := Pas.exists_line_eq ax ⟨a, ha⟩
  obtain ⟨O, d, hd, hOd⟩ := linEq_pline hpq r
  exact ⟨O, d, hd, fun Z => (h Z).trans (hOd (rectEquiv α ax Z))⟩

/-- In rectangular co-ordinates betweenness is that of `K × K`. -/
theorem rect_between (α : Pl) (ax : Pas.Axes 𝒫[α] ℒ[α]) (X Y Z : 𝒫[α]) :
    Sbtw (Pas.G ax) (rectEquiv α ax X) (rectEquiv α ax Y) (rectEquiv α ax Z) ↔
      Between (X : P) Y Z := by
  constructor
  · intro h
    obtain ⟨hne, t, h0, h1, e⟩ := (AffPt.sbtw_iff_param (K := Pas.G ax)
      (V := Pas.G ax × Pas.G ax) (A := rectEquiv α ax X) (B := rectEquiv α ax Y)
      (C := rectEquiv α ax Z)).1 h
    have hXZ : X ≠ Z := fun e => hne (by rw [e])
    have e1 : Pas.px ax Y = t * (Pas.px ax Z - Pas.px ax X) + Pas.px ax X := congrArg Prod.fst e
    have e2 : Pas.py ax Y = t * (Pas.py ax Z - Pas.py ax X) + Pas.py ax X := congrArg Prod.snd e
    exact Pas.between_of_coords ax hXZ h0 h1 (by rw [e1]; ring) (by rw [e2]; ring)
  · intro h
    have h' : Between X Y Z := h
    obtain ⟨t, h0, h1, e1, e2⟩ := Pas.between_coords ax h'
    refine (AffPt.sbtw_iff_param (K := Pas.G ax)
      (V := Pas.G ax × Pas.G ax) (A := rectEquiv α ax X) (B := rectEquiv α ax Y)
      (C := rectEquiv α ax Z)).2 ⟨fun e => ne13_of_between (Line := L) h
        (congrArg Subtype.val ((rectEquiv α ax).injective e)), t, h0, h1, ?_⟩
    refine Prod.ext ?_ ?_
    · show Pas.px ax Y = t * (Pas.px ax Z - Pas.px ax X) + Pas.px ax X
      rw [← e1]; ring
    · show Pas.py ax Y = t * (Pas.py ax Z - Pas.py ax X) + Pas.py ax X
      rw [← e2]; ring

/-- A plane of a geometry of space with I–IV has axes. -/
theorem exists_axes_in (α : Pl) : Nonempty (Pas.Axes 𝒫[α] ℒ[α]) := by
  obtain ⟨X, Y, Z, hX, hY, -, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  have hXY : X ≠ Y := (ne_of_not_collinear (L := L) hn (exists_line_through_of_mem (L := L) hY)).1
  obtain ⟨ax, -, -⟩ := Pas.exists_axes (P := 𝒫[α]) (L := ℒ[α]) (O := ⟨X, hX⟩) (E := ⟨Y, hY⟩)
    (fun e => hXY (congrArg Subtype.val e))
  exact ⟨ax⟩

include hC hS in
/-- **The co-ordinates of space** (§ 17): a geometry of space with I–IV having a plane has
co-ordinates `x, y, z` in an ordered field in which the planes are exactly the solution sets of the
linear equations `a x + b y + c z + d = 0`, `(a, b, c) ≠ 0`. -/
theorem space_coordinates (α : Pl) :
    ∃ (K : Type u) (_ : Field K) (_ : LinearOrder K) (_ : IsStrictOrderedRing K)
      (f : P ≃ K × K × K),
      (∀ α : Pl, ∃ a b c d : K, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        ∀ Z : P, Z ∈ α ↔ a * (f Z).1 + b * (f Z).2.1 + c * (f Z).2.2 + d = 0) ∧
      (∀ a b c d : K, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) → ∃ α : Pl,
        ∀ Z : P, Z ∈ α ↔ a * (f Z).1 + b * (f Z).2.1 + c * (f Z).2.2 + d = 0) := by
  obtain ⟨ax⟩ := exists_axes_in (P := P) (L := L) α
  have hV : finrank (Pas.G ax) (Pas.G ax × Pas.G ax) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  obtain ⟨f, -, -, -, hp1, hp2, -⟩ :=
    exists_space_coords (K := Pas.G ax) hV α (rectEquiv α ax) (rect_lineHyp α ax)
  refine ⟨Pas.G ax, inferInstance, inferInstance, inferInstance,
    f.trans (Equiv.prodAssoc _ _ _), fun π => ?_, fun a b c d h => ?_⟩
  · obtain ⟨S, hS⟩ := hp1 π
    obtain ⟨a, b, c, d, h, hS'⟩ := affPlane_eq S
    exact ⟨a, b, c, d, h, fun Z => (hS Z).trans (hS' (f Z))⟩
  · obtain ⟨S, hS⟩ := exists_affPlane_of_eq h d
    obtain ⟨π, hπ⟩ := hp2 S
    exact ⟨π, fun Z => (hπ Z).trans (hS (f Z))⟩

end Rect

end SpaceCoord

end HilbertFoundations
