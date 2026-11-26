import HilbertFoundations.CommentaryCloseAux4

/-!
# The non-legendrian geometry satisfies groups I, II, IV (helper for `CommentaryClose.lean`)

For the infinitesimal part `EPt K`, `ELn K` of the elliptic plane over a euclidean non-archimedean
ordered field (CommentaryCloseAux4.lean), with the elliptic congruences:

* `planeCongruence : PlaneCongruence (EPt K) (ELn K)`: groups I, II, IV hold;
* `infinitelyManyParallels`: through a point outside a line pass infinitely many lines that do not
  meet it (they meet it outside the infinitesimal part).
-/

namespace HilbertFoundations

namespace Elliptic

open Coord Conclusion

universe u

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [HasInfinitesimal K]

theorem E_inf (A : EPt K) : InfPt A.1 := A.2

/-! ### Infinitely many parallels -/

/-- **Infinitely many parallels** in the infinitesimal part of the plane. -/
theorem infinitelyManyParallels : InfinitelyManyParallels (EPt K) (ELn K) := by
  intro a A hA
  obtain ⟨u, v, w, huv, ha⟩ := exists_eq_of_line a.1
  have hc0 : lin u v w A.1 ≠ 0 := fun h0 => hA (by
    show A.1 ∈ a.1
    rw [ha, mem_lineOfEq]; exact h0)
  have hN : 0 < u ^ 2 + v ^ 2 := by
    rcases huv with h | h
    · have := lt_of_le_of_ne (sq_nonneg u) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg v]
    · have := lt_of_le_of_ne (sq_nonneg v) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg u]
  have h1N : (1 : K) + (u ^ 2 + v ^ 2) ≠ 0 := by positivity
  -- the family of lines
  let μ : ℕ → K := fun k => ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2)) / lin u v w A.1
  have hμ : ∀ k, μ k * lin u v w A.1 = ((k : K) + 1) * (1 + (u ^ 2 + v ^ 2)) := fun k =>
    div_mul_cancel₀ _ hc0
  let f : ℕ → ELn K := fun k =>
    ⟨FinitePart.tilted u v huv A.1 (μ k), A.1, A.2,
      (FinitePart.mem_tilted huv A.1 A.1 (μ k)).2 (by ring)⟩
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ ?_
  · intro j k hjk
    have hl : FinitePart.tilted u v huv A.1 (μ j) = FinitePart.tilted u v huv A.1 (μ k) :=
      congrArg Subtype.val hjk
    have hZ : pt2 (xc A.1 + (μ k * v + u)) (yc A.1 - (μ k * u - v)) ∈
        FinitePart.tilted u v huv A.1 (μ k) := by
      rw [FinitePart.mem_tilted]; simp only [xc_pt2, yc_pt2]; ring
    rw [← hl, FinitePart.mem_tilted] at hZ
    simp only [xc_pt2, yc_pt2] at hZ
    have h2 : (μ j - μ k) * (u ^ 2 + v ^ 2) = 0 := by linear_combination hZ
    have h3 : μ j = μ k := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hN.ne')
    have h4 := (div_left_inj₀ hc0).1 h3
    have h5 := mul_right_cancel₀ h1N h4
    exact Nat.cast_injective (add_right_cancel h5)
  · intro k
    refine ⟨(FinitePart.mem_tilted huv A.1 A.1 (μ k)).2 (by ring), ?_⟩
    rintro ⟨X, hXb, hXa⟩
    have hXb' := (FinitePart.mem_tilted huv A.1 X.1 (μ k)).1 hXb
    have hXa' : lin u v w X.1 = 0 := by
      have : X.1 ∈ a.1 := hXa
      rwa [ha, mem_lineOfEq] at this
    have hd := FinitePart.lin_sub_lin u v w X.1 A.1
    rw [hXa', zero_sub] at hd
    have hp : |xc X.1 - xc A.1| ≤ 1 / 2 := ((E_inf X).1.sub (E_inf A).1).abs_le_half
    have hq : |yc X.1 - yc A.1| ≤ 1 / 2 := ((E_inf X).2.sub (E_inf A).2).abs_le_half
    set p := xc X.1 - xc A.1
    set q := yc X.1 - yc A.1
    set c := lin u v w A.1
    have hcross : q * u - p * v = μ k * c := by linear_combination hXb' + μ k * hd
    have e1 : (u ^ 2 + v ^ 2) * (p ^ 2 + q ^ 2) =
        c ^ 2 + (((k : K) + 1) * (1 + (u ^ 2 + v ^ 2))) ^ 2 := by
      rw [← hμ k]
      linear_combination (-(p * u + q * v) + c) * hd + (q * u - p * v + μ k * c) * hcross
    have hp2 := (abs_mul_le_quarter hp hp).2
    have hq2 := (abs_mul_le_quarter hq hq).2
    have hk1 : (1 : K) ≤ ((k : K) + 1) ^ 2 := by
      have := Nat.cast_nonneg (α := K) k
      nlinarith
    have h6 : (u ^ 2 + v ^ 2) * (p ^ 2 + q ^ 2) ≤ (u ^ 2 + v ^ 2) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hN.le
    have h7 : (1 + (u ^ 2 + v ^ 2)) ^ 2 ≤ (((k : K) + 1) * (1 + (u ^ 2 + v ^ 2))) ^ 2 := by
      rw [mul_pow]; exact le_mul_of_one_le_left (sq_nonneg _) hk1
    have h8 : (u ^ 2 + v ^ 2) * (1 / 2) < (1 + (u ^ 2 + v ^ 2)) ^ 2 := by nlinarith
    linarith [sq_nonneg c]

/-! ### The congruences -/

variable [IsEuclidean K]

/-- Congruence of segments: equal elliptic lengths. -/
noncomputable instance instHasSegCong : HasSegCong (EPt K) :=
  ⟨fun A B C D => cs A.1 B.1 = cs C.1 D.1⟩

/-- Congruence of angles: equal elliptic measures. -/
noncomputable instance instHasAngCong : HasAngCong (EPt K) :=
  ⟨fun A O B A' O' B' =>
    kc O.1 (A.1 - O.1) (B.1 - O.1) = kc O'.1 (A'.1 - O'.1) (B'.1 - O'.1)⟩

theorem E_segCong_iff {A B C D : EPt K} : SegCong A B C D ↔ cs A.1 B.1 = cs C.1 D.1 := Iff.rfl

theorem E_angCong_iff {A O B A' O' B' : EPt K} :
    AngCong A O B A' O' B' ↔
      kc O.1 (A.1 - O.1) (B.1 - O.1) = kc O'.1 (A'.1 - O'.1) (B'.1 - O'.1) := Iff.rfl

omit [IsEuclidean K] in
theorem E_cr_ne_zero {A O B : EPt K} (h : ¬Collinear (Line := ELn K) A O B) :
    crossProd2 (A.1 - O.1) (B.1 - O.1) ≠ 0 :=
  cr_ne_zero_of_not_collinear (fun hc => h (E_collinear_iff.2 hc))

/-- **Axiom IV 1** (laying off segments) in the non-legendrian geometry. -/
theorem axiomIV1LayOff : AxiomIV1LayOff (EPt K) := by
  intro A B A' C' hAB hA'C'
  have hC'A' : C'.1 ≠ A'.1 := (E_ne_iff.1 hA'C').symm
  obtain ⟨s, hs, hInf, hcs⟩ := layoff_exists (E_inf A) (E_inf B) (E_inf A') (E_ne_iff.1 hAB) hC'A'
  refine ⟨⟨s • (C'.1 - A'.1) + A'.1, hInf⟩, ⟨?_, hcs.symm⟩, ?_⟩
  · exact E_mem_ray_iff.2 ((AffPt.mem_ray_iff hC'A').2 ⟨s, hs, rfl⟩)
  · rintro Y ⟨hs', hc'⟩
    obtain ⟨s', hs'pos, hYe⟩ := (AffPt.mem_ray_iff hC'A').1 (E_mem_ray_iff.1 hs')
    have hYinf : InfPt (s' • (C'.1 - A'.1) + A'.1) := by rw [← hYe]; exact E_inf Y
    have hc'' : cs A.1 B.1 = cs A'.1 (s' • (C'.1 - A'.1) + A'.1) := by rw [← hYe]; exact hc'
    have hss := layoff_unique (sub_ne_zero.2 hC'A') hs'pos hs (Sf_pos (E_inf A') hYinf)
      (Sf_pos (E_inf A') hInf) (hc''.symm.trans hcs.symm)
    apply Subtype.ext
    show Y.1 = s • (C'.1 - A'.1) + A'.1
    rw [hYe, hss]

/-- **Axiom IV 4** (laying off angles) in the non-legendrian geometry. -/
theorem axiomIV4LayOff : AxiomIV4LayOff (EPt K) := by
  intro A O B a' O' A' D' h hO' hA' hA'O' hD'
  have hab := E_cr_ne_zero h
  have hAO' := E_ne_iff.1 hA'O'
  have hu : A'.1 - O'.1 ≠ 0 := sub_ne_zero.2 hAO'
  have hd : crossProd2 (A'.1 - O'.1) (D'.1 - O'.1) ≠ 0 := fun e =>
    hD' ((E_mem_iff_cr hO' hA' hA'O' D').2 e)
  obtain ⟨y, hy, hk⟩ := ang_layoff (O := O.1) hab (O' := O'.1) hu hd
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : crossProd2 (A'.1 - O'.1) (0 : Coord K 2) = 0 := by cring
    rw [this, zero_mul] at hy; exact lt_irrefl _ hy
  obtain ⟨B₁, c, hc, hB₁⟩ := exists_on_ray O' hy0
  have hcr : crossProd2 (A'.1 - O'.1) (B₁.1 - O'.1) = c * crossProd2 (A'.1 - O'.1) y := by
    rw [hB₁, cr_smul_right]
  have hss : SameSide a' B₁ D' := by
    rw [E_sameSide_iff_cr hO' hA' hA'O', hcr, mul_assoc]
    exact mul_pos hc hy
  have hB₁a : B₁ ∉ a' := hss.1
  have hAng : AngCong A O B A' O' B₁ := by
    rw [E_angCong_iff, hB₁, kc_smul_right _ _ _ hc, hk]
  have key : ∀ Q : EPt K, Q ∉ a' →
      ((∀ X : EPt K, X ∈ Interior (Line := ELn K) A' O' Q → SameSide a' X D') ↔
        SameSide a' Q D') := fun Q hQ => by
    have := interior_cond_iff (L := ELn K) (S := Set.univ) (l := a') (O' := O') (A' := A')
      (B' := Q) (D' := D') (fun _ _ _ _ _ _ h1 h2 => OrderCore.sameSide_trans h1 h2)
      (fun _ _ => trivial) hO' hA' hA'O' hQ trivial trivial
    exact ⟨fun h => this.1 (fun X _ hX => h X hX), fun h X hX => this.2 h X trivial hX⟩
  refine ⟨B₁, hB₁a, hAng, (key _ hB₁a).2 hss, ?_⟩
  intro B'' hB'' hc'' hint
  have h1 : SameSide a' B'' D' := (key _ hB'').1 hint
  have h2 : SameSide a' B'' B₁ := OrderCore.sameSide_trans h1 (sameSide_symm' hss)
  have h3 := (E_sameSide_iff_cr hO' hA' hA'O' B'' B₁).1 h2
  have hk'' : kc O'.1 (A'.1 - O'.1) (B''.1 - O'.1) = kc O'.1 (A'.1 - O'.1) (B₁.1 - O'.1) :=
    (E_angCong_iff.1 hc'').symm.trans (E_angCong_iff.1 hAng)
  obtain ⟨c', hc', e⟩ := ang_unique hu h3 hk''
  have hB₁O : B₁.1 ≠ O'.1 := by
    intro e0
    rw [e0, sub_self] at hB₁
    exact hy0 ((smul_eq_zero.1 hB₁.symm).resolve_left hc.ne')
  exact E_ray_eq_of_plane (AffPt.ray_eq_of_pos_smul hB₁O hc' e)

/-- **Groups I, II, IV hold in the non-legendrian geometry.** -/
theorem planeCongruence : PlaneCongruence (EPt K) (ELn K) :=
  { (inferInstance : PlaneOrder (EPt K) (ELn K)) with
    angCong_wd := fun A O B C D A' O' B' C' D' h h' hs hs' hc => by
      rw [E_angCong_iff] at hc ⊢
      rw [kc_of_sameAngle (fun hc => h (E_collinear_iff.2 hc)) (E_sameAngle hs),
        kc_of_sameAngle (fun hc => h' (E_collinear_iff.2 hc)) (E_sameAngle hs')]
      exact hc
    ax_IV4_refl := fun _ _ _ _ => rfl
    ax_IV5 := fun _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
    ax_IV4 := axiomIV4LayOff
    segCong_swap := fun A B A' B' h =>
      ⟨by rw [E_segCong_iff] at h ⊢; rw [cs_comm]; exact h,
        by rw [E_segCong_iff] at h ⊢; rw [cs_comm B'.1]; exact h⟩
    ax_IV1 := axiomIV1LayOff
    ax_IV1_refl := fun _ _ _ => rfl
    ax_IV2 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
    ax_IV3 := fun A B C A' B' C' h h' h1 h2 => by
      have hb : Sbtw K A.1 B.1 C.1 :=
        AffPt.between_iff.1 ((IV3_reading (P := EPt K) (L := ELn K)).1 h)
      have hb' : Sbtw K A'.1 B'.1 C'.1 :=
        AffPt.between_iff.1 ((IV3_reading (P := EPt K) (L := ELn K)).1 h')
      rw [E_segCong_iff] at h1 h2 ⊢
      rw [cs_add hb, cs_add hb', h1, h2, sn_eq_of_cs_eq h1, sn_eq_of_cs_eq h2]
    ax_IV6 := fun A B C A' B' C' h h' h1 h2 h3 => by
      obtain ⟨hab, hac, hbc⟩ := AffPt.not_collinear_of_eq (fun hc => h (E_collinear_iff.2 hc))
      obtain ⟨hab', hac', hbc'⟩ :=
        AffPt.not_collinear_of_eq (fun hc => h' (E_collinear_iff.2 hc))
      rw [E_segCong_iff] at h1 h2
      rw [E_angCong_iff] at h3
      have hBC := cs_eq_of_kc_eq hab.symm hac.symm hab'.symm hac'.symm h1 h2 h3
      constructor
      · rw [E_angCong_iff]
        exact kc_eq_of_cs_eq hab hbc.symm hab' hbc'.symm (by rw [cs_comm, h1, cs_comm]) hBC h2
      · rw [E_angCong_iff]
        exact kc_eq_of_cs_eq hac hbc hac' hbc' (by rw [cs_comm, h2, cs_comm])
          (by rw [cs_comm, hBC, cs_comm]) h1 }

end Elliptic

end HilbertFoundations
