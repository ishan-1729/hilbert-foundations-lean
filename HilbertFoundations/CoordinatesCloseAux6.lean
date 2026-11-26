import HilbertFoundations.CoordinatesCloseAux5

/-!
# Helper for § 17 (ideal elements): angles, and the embedding into the real space

Helper module of `CoordinatesClose.lean` (unit `s17.ideal`).

* `angCong_iff_exists`: in a geometry of space with I, II, IV, two angles are congruent iff
  congruent segments laid off on their sides have congruent joins (Theorems 10 and 16). Hence a
  bijection onto the coordinate space over a Pythagorean field that preserves and reflects
  collinearity, betweenness and the congruence of segments also preserves and reflects the
  congruence of angles (`psi_angCong_iff`).
* `jmap ι`: the embedding of `K³` into `ℝ³` for an embedding `ι` of the ordered field `K` into `ℝ`;
  it preserves and reflects lines, betweenness and the two congruences.
* `ideal_elements`: every geometry of space with I–V having a plane extends to the analytic
  geometry of space over `ℝ` (§ 17).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace SpaceCoord

open Module

universe u v w

/-! ## Congruence of angles in terms of congruence of segments -/

section AngleChar

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl]

include hC

/-- **Two angles are congruent iff** the segments `OA`, `OB` can be laid off on the sides of the
second angle so that the joins are congruent (Theorems 10 and 16). -/
theorem angCong_iff_exists {A O B A' O' B' : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') :
    AngCong A O B A' O' B' ↔ ∃ A₁ B₁ : P, A₁ ∈ ray O' A' ∧ B₁ ∈ ray O' B' ∧
      SegCong O A O' A₁ ∧ SegCong O B O' B₁ ∧ SegCong A B A₁ B₁ := by
  obtain ⟨hAO, hBO, hAB⟩ := ne_of_not_collinear (L := L) h (line_through_space (Pl := Pl) O)
  obtain ⟨hA'O', hB'O', -⟩ :=
    ne_of_not_collinear (L := L) h' (line_through_space (Pl := Pl) O')
  have hT : IsTriangle (Line := L) O A B := fun hc => h hc.swap12
  constructor
  · intro hang
    obtain ⟨A₁, hA₁, sA⟩ := segCong_layoff (L := L) hAO.symm hA'O'.symm
    obtain ⟨B₁, hB₁, sB⟩ := segCong_layoff (L := L) hBO.symm hB'O'.symm
    have h₁ : ¬Collinear (Line := L) A₁ O' B₁ := not_collinear_of_mem_rays (L := L) h' hA₁ hB₁
    have hang₁ : AngCong A O B A₁ O' B₁ :=
      angCong_of_sameAngle (Line := L) h h' (sameAngle_refl A O B)
        (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hA₁).symm
          (ray_eq_of_mem (L := L) hB₁).symm) hang
    have hT₁ : IsTriangle (Line := L) O' A₁ B₁ := fun hc => h₁ hc.swap12
    obtain ⟨-, -, s3, -⟩ := theorem10_space (L := L) (Pl := Pl) hT hT₁ sA sB hang₁
    exact ⟨A₁, B₁, hA₁, hB₁, sA, sB, s3⟩
  · rintro ⟨A₁, B₁, hA₁, hB₁, sA, sB, s3⟩
    have h₁ : ¬Collinear (Line := L) A₁ O' B₁ := not_collinear_of_mem_rays (L := L) h' hA₁ hB₁
    have hT₁ : IsTriangle (Line := L) O' A₁ B₁ := fun hc => h₁ hc.swap12
    obtain ⟨-, -, -, hang₁, -⟩ := theorem16_space (L := L) (Pl := Pl) hT hT₁ sA sB s3
    exact angCong_of_sameAngle (Line := L) h h₁ (sameAngle_refl A O B)
      (sameAngle_of_ray_eq (L := L) (ray_eq_of_mem (L := L) hA₁) (ray_eq_of_mem (L := L) hB₁))
      hang₁

end AngleChar

/-! ## Bijections onto a coordinate space -/

/-- Collinearity in a coordinate space. -/
theorem coord_collinear_iff {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V]
    [Module K V] {U V' X : AffPt K V} (h : U ≠ V') :
    Collinear U V' X ↔ ∃ r : K, X = r • (V' - U) + U := by
  constructor
  · rintro ⟨m, hU, hV, hX⟩
    rw [m.eq_through h hU hV] at hX
    exact (AffLine.mem_through_iff h).1 hX
  · intro hX
    exact ⟨AffLine.through U V' h, AffLine.left_mem_through h, AffLine.right_mem_through h,
      (AffLine.mem_through_iff h).2 hX⟩

section Transfer

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P] [hC : SpaceCongruence P L Pl]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsPythagorean K]
variable (Ψ : P → Coord K 3) (hbij : Function.Bijective Ψ)
  (hline : ∀ (ℓ : L) (A B : P), A ≠ B → A ∈ ℓ → B ∈ ℓ →
    ∀ X : P, X ∈ ℓ ↔ ∃ r : K, Ψ X = r • (Ψ B - Ψ A) + Ψ A)
  (hbtw : ∀ X Y Z : P, Sbtw K (Ψ X) (Ψ Y) (Ψ Z) ↔ Between X Y Z)
  (hseg : ∀ A B C D : P, A ≠ B → C ≠ D → (SegCong (Ψ A) (Ψ B) (Ψ C) (Ψ D) ↔ SegCong A B C D))

include hC hbij hline

theorem psi_collinear_iff {A B X : P} (hAB : A ≠ B) :
    Collinear (Ψ A) (Ψ B) (Ψ X) ↔ Collinear (Line := L) A B X := by
  rw [coord_collinear_iff (hbij.1.ne hAB)]
  constructor
  · intro h
    obtain ⟨ℓ, hA, hB⟩ := exists_line (Line := L) hAB
    exact ⟨ℓ, hA, hB, (hline ℓ A B hAB hA hB X).2 h⟩
  · rintro ⟨ℓ, hA, hB, hX⟩
    exact (hline ℓ A B hAB hA hB X).1 hX

theorem psi_not_collinear_iff {A O B : P} :
    ¬Collinear (Ψ A) (Ψ O) (Ψ B) ↔ ¬Collinear (Line := L) A O B := by
  by_cases hAO : A = O
  · subst hAO
    have h1 : Collinear (Line := L) A A B := by
      by_cases hAB : A = B
      · subst hAB
        obtain ⟨l, hl⟩ := line_through_space (L := L) (Pl := Pl) A
        exact ⟨l, hl, hl, hl⟩
      · obtain ⟨l, h1, h2⟩ := exists_line (Line := L) hAB
        exact ⟨l, h1, h1, h2⟩
    have h2 : Collinear (Ψ A) (Ψ A) (Ψ B) := by
      by_cases hAB : Ψ A = Ψ B
      · rw [← hAB]
        obtain ⟨l, hl⟩ := line_through_space (L := CoordLine K 3) (Pl := CoordPlane K 3) (Ψ A)
        exact ⟨l, hl, hl, hl⟩
      · obtain ⟨l, h1, h2⟩ := exists_line (Line := CoordLine K 3) hAB
        exact ⟨l, h1, h1, h2⟩
    exact ⟨fun h => absurd h2 h, fun h => absurd h1 h⟩
  · rw [psi_collinear_iff Ψ hbij hline hAO]

include hbtw

theorem psi_ray_iff {O A X : P} : Ψ X ∈ ray (Ψ O) (Ψ A) ↔ X ∈ ray O A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hAO : A ≠ O := fun e => h1 (by rw [e])
    exact ⟨hAO, fun e => h2 (by rw [e]), (psi_collinear_iff Ψ hbij hline hAO).1 h3,
      fun hb => h4 ((hbtw A O X).2 hb)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hbij.1.ne h1, hbij.1.ne h2, (psi_collinear_iff Ψ hbij hline h1).2 h3,
      fun hb => h4 ((hbtw A O X).1 hb)⟩

include hseg

/-- **The congruence of angles is that of the coordinate space.** -/
theorem psi_angCong_iff {A O B A' O' B' : P} (h : ¬Collinear (Line := L) A O B)
    (h' : ¬Collinear (Line := L) A' O' B') :
    AngCong (Ψ A) (Ψ O) (Ψ B) (Ψ A') (Ψ O') (Ψ B') ↔ AngCong A O B A' O' B' := by
  have hΨ : ¬Collinear (Ψ A) (Ψ O) (Ψ B) := (psi_not_collinear_iff Ψ hbij hline).2 h
  have hΨ' : ¬Collinear (Ψ A') (Ψ O') (Ψ B') := (psi_not_collinear_iff Ψ hbij hline).2 h'
  obtain ⟨hAO, hBO, hAB⟩ := ne_of_not_collinear (L := L) h (line_through_space (Pl := Pl) O)
  have key : ∀ A₁ B₁ : P, A₁ ∈ ray O' A' → B₁ ∈ ray O' B' →
      ((SegCong (Ψ O) (Ψ A) (Ψ O') (Ψ A₁) ∧ SegCong (Ψ O) (Ψ B) (Ψ O') (Ψ B₁) ∧
        SegCong (Ψ A) (Ψ B) (Ψ A₁) (Ψ B₁)) ↔
      (SegCong O A O' A₁ ∧ SegCong O B O' B₁ ∧ SegCong A B A₁ B₁)) := by
    intro A₁ B₁ hA₁ hB₁
    have hn₁ := not_collinear_of_mem_rays (L := L) h' hA₁ hB₁
    obtain ⟨hA₁O, hB₁O, hA₁B₁⟩ :=
      ne_of_not_collinear (L := L) hn₁ (line_through_space (Pl := Pl) O')
    rw [hseg O A O' A₁ hAO.symm hA₁O.symm, hseg O B O' B₁ hBO.symm hB₁O.symm,
      hseg A B A₁ B₁ hAB hA₁B₁]
  rw [angCong_iff_exists (L := L) (Pl := Pl) h h',
    angCong_iff_exists (L := CoordLine K 3) (Pl := CoordPlane K 3) hΨ hΨ']
  constructor
  · rintro ⟨Y₁, Y₂, r1, r2, s⟩
    obtain ⟨A₁, rfl⟩ := hbij.2 Y₁
    obtain ⟨B₁, rfl⟩ := hbij.2 Y₂
    have hA₁ := (psi_ray_iff Ψ hbij hline hbtw).1 r1
    have hB₁ := (psi_ray_iff Ψ hbij hline hbtw).1 r2
    exact ⟨A₁, B₁, hA₁, hB₁, (key A₁ B₁ hA₁ hB₁).1 s⟩
  · rintro ⟨A₁, B₁, hA₁, hB₁, s⟩
    exact ⟨Ψ A₁, Ψ B₁, (psi_ray_iff Ψ hbij hline hbtw).2 hA₁,
      (psi_ray_iff Ψ hbij hline hbtw).2 hB₁, (key A₁ B₁ hA₁ hB₁).2 s⟩

end Transfer

/-! ## The embedding of `K³` into `ℝ³` -/

section RealEmb

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ι : K →+*o ℝ)

/-- The embedding of `K³` into `ℝ³`, co-ordinate by co-ordinate. -/
def jmap (X : Coord K 3) : Coord ℝ 3 := AffPt.ofV (fun i => ι (AffPt.toV X i))

theorem jmap_apply (X : Coord K 3) (i : Fin 3) : AffPt.toV (jmap ι X) i = ι (AffPt.toV X i) := rfl

theorem jmap_sub (X Y : Coord K 3) : jmap ι (X - Y) = jmap ι X - jmap ι Y := by
  apply AffPt.toV_injective; funext i; exact map_sub ι _ _

theorem jmap_add (X Y : Coord K 3) : jmap ι (X + Y) = jmap ι X + jmap ι Y := by
  apply AffPt.toV_injective; funext i; exact map_add ι _ _

theorem jmap_smul (t : K) (X : Coord K 3) : jmap ι (t • X) = ι t • jmap ι X := by
  apply AffPt.toV_injective; funext i; exact map_mul ι _ _

theorem jmap_injective : Function.Injective (jmap ι) := fun X Y h => by
  apply AffPt.toV_injective; funext i
  exact ι.toRingHom.injective (congrFun (congrArg AffPt.toV h) i)

theorem ip_jmap (X Y : Coord K 3) : Coord.ip (jmap ι X) (jmap ι Y) = ι (Coord.ip X Y) := by
  rw [ip_three, ip_three, map_add, map_add, map_mul, map_mul, map_mul]; rfl

theorem jmap_segCong_iff {A B C D : Coord K 3} :
    SegCong (jmap ι A) (jmap ι B) (jmap ι C) (jmap ι D) ↔ SegCong A B C D := by
  rw [Coord.segCong_iff, Coord.segCong_iff, ← jmap_sub, ← jmap_sub, ip_jmap, ip_jmap]
  exact ι.toRingHom.injective.eq_iff

theorem sign_orderRingHom (x : K) : SignType.sign (ι x) = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · have h' : ι x < 0 := by
      have := orderRingHom_strictMono ι h
      rwa [map_zero] at this
    rw [sign_neg h, sign_neg h']
  · subst h; rw [map_zero, sign_zero, sign_zero]
  · rw [sign_pos h, sign_pos (orderRingHom_pos ι h)]

theorem jmap_angleEq_iff (a b a' b' : Coord K 3) :
    Coord.AngleEq (jmap ι a) (jmap ι b) (jmap ι a') (jmap ι b') ↔ Coord.AngleEq a b a' b' := by
  unfold Coord.AngleEq
  simp only [ip_jmap, sign_orderRingHom]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · apply ι.toRingHom.injective
    show ι _ = ι _
    simp only [map_mul, map_pow]
    exact h
  · have h1 := congrArg ι h
    simp only [map_mul, map_pow] at h1
    exact h1

theorem jmap_angCong_iff {A O B A' O' B' : Coord K 3} :
    AngCong (jmap ι A) (jmap ι O) (jmap ι B) (jmap ι A') (jmap ι O') (jmap ι B') ↔
      AngCong A O B A' O' B' := by
  rw [Coord.angCong_iff, Coord.angCong_iff, ← jmap_sub, ← jmap_sub, ← jmap_sub, ← jmap_sub]
  exact jmap_angleEq_iff ι _ _ _ _

/-- A point of `K³` whose image lies on the real line through the images of two points lies on
their line. -/
theorem jmap_param_iff {U V X : Coord K 3} (hUV : U ≠ V) :
    (∃ ρ : ℝ, jmap ι X = ρ • (jmap ι V - jmap ι U) + jmap ι U) ↔
      ∃ r : K, X = r • (V - U) + U := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have hd : V - U ≠ 0 := sub_ne_zero.2 (Ne.symm hUV)
    obtain ⟨i, hi⟩ : ∃ i, AffPt.toV (V - U) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hd
      apply AffPt.toV_injective
      funext i
      exact hcon i
    have hιi : ι (AffPt.toV (V - U) i) ≠ 0 := fun h =>
      hi (ι.toRingHom.injective (h.trans (map_zero ι).symm))
    have hi' : ι (AffPt.toV X i) =
        ρ * (ι (AffPt.toV V i) - ι (AffPt.toV U i)) + ι (AffPt.toV U i) :=
      congrFun (congrArg AffPt.toV hρ) i
    have hsub : ι (AffPt.toV (V - U) i) = ι (AffPt.toV V i) - ι (AffPt.toV U i) :=
      map_sub ι _ _
    have hρr : ρ = ι ((AffPt.toV X i - AffPt.toV U i) / AffPt.toV (V - U) i) := by
      rw [map_div₀, map_sub, eq_div_iff hιi, hsub]
      linear_combination (-1 : ℝ) * hi'
    refine ⟨(AffPt.toV X i - AffPt.toV U i) / AffPt.toV (V - U) i, jmap_injective ι ?_⟩
    rw [jmap_add, jmap_smul, jmap_sub, ← hρr]
    exact hρ
  · rintro ⟨r, rfl⟩
    exact ⟨ι r, by rw [jmap_add, jmap_smul, jmap_sub]⟩

theorem jmap_sbtw_iff {U X V : Coord K 3} :
    Sbtw ℝ (jmap ι U) (jmap ι X) (jmap ι V) ↔ Sbtw K U X V := by
  rw [AffPt.sbtw_iff_param (K := ℝ), AffPt.sbtw_iff_param (K := K)]
  constructor
  · rintro ⟨hne, τ, h0, h1, hτ⟩
    have hUV : U ≠ V := fun e => hne (by rw [e])
    obtain ⟨r, hr⟩ := (jmap_param_iff ι hUV).1 ⟨τ, hτ⟩
    have hd : jmap ι V - jmap ι U ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have h2 : jmap ι X = ι r • (jmap ι V - jmap ι U) + jmap ι U := by
      rw [hr, jmap_add, jmap_smul, jmap_sub]
    have e : τ = ι r := (smul_add_inj hd).1 (hτ.symm.trans h2)
    rw [e] at h0 h1
    refine ⟨hUV, r, ?_, ?_, hr⟩
    · exact (orderRingHom_strictMono ι).lt_iff_lt.1 (by rwa [map_zero])
    · exact (orderRingHom_strictMono ι).lt_iff_lt.1 (by rwa [map_one])
  · rintro ⟨hUV, r, h0, h1, rfl⟩
    refine ⟨(jmap_injective ι).ne hUV, ι r, orderRingHom_pos ι h0, ?_,
      by rw [jmap_add, jmap_smul, jmap_sub]⟩
    have h := orderRingHom_strictMono ι h1
    rwa [map_one] at h

end RealEmb

/-- **Every linear equation in `F³` represents a plane** (`F` an ordered field). -/
theorem exists_coordPlane {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : Coord F 3} (hn : n ≠ 0) (d : F) :
    ∃ S : CoordPlane F 3, ∀ Y : Coord F 3, Y ∈ S ↔ Coord.ip n Y + d = 0 := by
  let φ : Coord F 3 →ₗ[F] F :=
    { toFun := fun Y => Coord.ip n Y
      map_add' := fun X Y => Coord.ip_add_right n X Y
      map_smul' := fun t X => Coord.ip_smul_right t n X }
  have hv : φ n ≠ 0 := fun h => hn (Coord.ip_self_eq_zero.1 h)
  exact exists_affPlane_of_functional (Module.finrank_fin_fun F) φ hv d

/-! ## § 17: ideal elements -/

section Ideal

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P]

/-- **Every geometry of space with I–V having a plane extends to the analytic geometry of space
over `ℝ`** (§ 17): there are injective maps of its points, lines and planes into those of `ℝ³`
preserving and reflecting incidence, betweenness, the congruence of segments and the congruence of
angles. -/
theorem ideal_elements (hG : SpaceGeometry P L Pl) (α : Pl) :
    ∃ (pt : P → Coord ℝ 3) (line : L → CoordLine ℝ 3) (plane : Pl → CoordPlane ℝ 3),
      Function.Injective pt ∧ Function.Injective line ∧ Function.Injective plane ∧
      (∀ (A : P) (a : L), pt A ∈ line a ↔ A ∈ a) ∧
      (∀ (A : P) (α : Pl), pt A ∈ plane α ↔ A ∈ α) ∧
      (∀ A B C : P, Between (pt A) (pt B) (pt C) ↔ Between A B C) ∧
      (∀ A B C D : P, A ≠ B → C ≠ D →
        (SegCong (pt A) (pt B) (pt C) (pt D) ↔ SegCong A B C D)) ∧
      (∀ A O B A' O' B' : P, ¬Collinear (Line := L) A O B → ¬Collinear (Line := L) A' O' B' →
        (AngCong (pt A) (pt O) (pt B) (pt A') (pt O') (pt B') ↔ AngCong A O B A' O' B')) := by
  have := hG
  obtain ⟨K, iF, iL, iS, iA, iP, Ψ, hbij, hline, hplane, hbtw, hseg⟩ :=
    exists_metric_coords (P := P) (L := L) α
  obtain ⟨ι⟩ := Real.nonemptyOrderRingHom K
  have hptinj : Function.Injective (fun X : P => jmap ι (Ψ X)) := fun X Y h =>
    hbij.1 (jmap_injective ι h)
  have hpts : ∀ a : L, ∃ AB : P × P, AB.1 ≠ AB.2 ∧ AB.1 ∈ a ∧ AB.2 ∈ a := fun a => by
    obtain ⟨A, B, h, hA, hB⟩ := exists_two_points (Point := P) a
    exact ⟨(A, B), h, hA, hB⟩
  choose pts hpts using hpts
  have hln : ∀ a : L, ∃ m : CoordLine ℝ 3, ∀ X : P, jmap ι (Ψ X) ∈ m ↔ X ∈ a := by
    intro a
    obtain ⟨h1, h2, h3⟩ := hpts a
    refine ⟨AffLine.through (jmap ι (Ψ (pts a).1)) (jmap ι (Ψ (pts a).2)) (hptinj.ne h1),
      fun X => ?_⟩
    rw [hline a _ _ h1 h2 h3 X, AffLine.mem_through_iff]
    exact jmap_param_iff ι (hbij.1.ne h1)
  choose line hline' using hln
  have hpl : ∀ π : Pl, ∃ S : CoordPlane ℝ 3, ∀ X : P, jmap ι (Ψ X) ∈ S ↔ X ∈ π := by
    intro π
    obtain ⟨n, d, hn, hπ⟩ := hplane π
    have hjn : jmap ι n ≠ 0 := fun h => hn (jmap_injective ι (h.trans (by
      apply AffPt.toV_injective; funext i; exact (map_zero ι).symm)))
    obtain ⟨S, hS⟩ := exists_coordPlane hjn (ι d)
    refine ⟨S, fun X => ?_⟩
    rw [hS, hπ X, ip_jmap, ← map_add]
    constructor
    · intro h; exact ι.toRingHom.injective (h.trans (map_zero ι).symm)
    · intro h; rw [h, map_zero]
  choose plane hplane' using hpl
  refine ⟨fun X => jmap ι (Ψ X), line, plane, hptinj, ?_, ?_, fun A a => hline' a A,
    fun A π => hplane' π A, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨h1, h2, h3⟩ := hpts a
    have hA : (pts a).1 ∈ b := (hline' b _).1 (h ▸ (hline' a _).2 h2)
    have hB : (pts a).2 ∈ b := (hline' b _).1 (h ▸ (hline' a _).2 h3)
    exact line_unique h1 h2 h3 hA hB
  · intro π ρ h
    obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) π
    have tr : ∀ W : P, W ∈ π → W ∈ ρ := fun W hW => (hplane' ρ W).1 (h ▸ (hplane' π W).2 hW)
    exact plane_unique hn hX hY hZ (tr X hX) (tr Y hY) (tr Z hZ)
  · intro A B C
    rw [← hbtw A B C]
    exact jmap_sbtw_iff ι
  · intro A B C D hAB hCD
    rw [← hseg A B C D hAB hCD]
    exact jmap_segCong_iff ι
  · intro A O B A' O' B' h h'
    rw [← psi_angCong_iff Ψ hbij hline hbtw hseg h h']
    exact jmap_angCong_iff ι

end Ideal

end SpaceCoord

end HilbertFoundations
