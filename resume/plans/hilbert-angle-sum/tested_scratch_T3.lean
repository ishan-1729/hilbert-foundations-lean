import HilbertFoundations.Commentary
import HilbertFoundations.PascalAux2

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace AngSum

universe u v

section Defs

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]

variable (L) in
def LtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) A O B C O B

variable (L) in
def EqSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngCong A O B C O B

variable (L) in
def GtSupp (A O B : P) : Prop :=
  ¬Collinear (Line := L) A O B ∧ ∃ C, Between A O C ∧ AngLt (L := L) C O B A O B

variable (L) in
def SameType (A O B A' O' B' : P) : Prop :=
  (LtSupp L A O B ↔ LtSupp L A' O' B') ∧ (EqSupp L A O B ↔ EqSupp L A' O' B') ∧
    (GtSupp L A O B ↔ GtSupp L A' O' B')

def SLt (A B C D : P) : Prop := ∃ X, Between C X D ∧ SegCong A B C X

def Foot (l : L) (X F : P) : Prop :=
  F ∈ l ∧ X ∉ l ∧ ∀ G : P, G ∈ l → G ≠ F → RightAng (L := L) G F X

variable (L) in
def BiRight (A B C D : P) : Prop :=
  A ≠ B ∧ RightAng (L := L) B A C ∧ RightAng (L := L) A B D ∧
    ∀ l : L, A ∈ l → B ∈ l → SameSide l C D

variable (L) in
def Saccheri (A B C D : P) : Prop := BiRight L A B C D ∧ SegCong A C B D

variable (L) in
def Lambert (M B D N : P) : Prop :=
  RightAng (L := L) B M N ∧ RightAng (L := L) M B D ∧ RightAng (L := L) M N D

variable (L) in
structure TriConf (A B C F G H X Y A₁ B₁ : P) : Prop where
  nc : ¬Collinear (Line := L) A B C
  sac : Saccheri L F G A B
  hX : Between A C X
  hY : Between B₁ C Y
  angA : AngCong C A B X C Y
  sideY : ∀ a : L, A ∈ a → C ∈ a → SameSide a Y B
  intY : Y ∈ Interior (Line := L) X C B
  angB : AngCong C B A B C A₁
  ncA : ¬Collinear (Line := L) A₁ C B
  sideA : ∀ a : L, C ∈ a → B ∈ a → SameSide a A₁ Y
  angS : AngCong F A B H C B₁
  ncH : ¬Collinear (Line := L) B₁ C H
  ncH' : ¬Collinear (Line := L) A₁ C H
  angH : AngCong B₁ C H A₁ C H
  sideH : ∀ a : L, C ∈ a → H ∈ a → SameSide a A₁ Y
  sideYH : ∀ a : L, C ∈ a → Y ∈ a → SameSide a H B

end Defs

section Thms

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L] (hl : ∀ X : P, ∃ l : L, X ∈ l)
  {A B C D E O X Y Z A' B' C' D' O' H K M N P' Q : P} {l m : L}
include hC hl

abbrev fr : Frame P L := planeFrame hl

theorem ne_of_nc (h : ¬Collinear (Line := L) A O B) : A ≠ O ∧ B ≠ O ∧ A ≠ B :=
  ne_of_not_collinear h (hl O)

theorem crossbar (h : ¬Collinear (Line := L) B A C) (hD : D ∈ Interior (Line := L) B A C) :
    ∃ Y, Between B Y C ∧ Y ∈ ray A D :=
  (fr hl).crossbar (S := Set.univ) rfl trivial trivial trivial trivial h hD

theorem layoff (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l) (hne : A' ≠ O')
    (hD : D ∉ l) : ∃ B', SameSide l B' D ∧ AngCong A O B A' O' B' := by
  obtain ⟨B', -, h1, h2⟩ := (fr hl).layoff Set.univ rfl A O B l O' A' D h (fun _ _ => trivial) hO'
    hA' hne trivial hD
  exact ⟨B', h1, h2⟩

theorem layoff_unique (h : ¬Collinear (Line := L) A O B) (hO' : O' ∈ l) (hA' : A' ∈ l)
    (hne : A' ≠ O') {B' B'' : P} (hs : SameSide l B' B'') (h1 : AngCong A O B A' O' B')
    (h2 : AngCong A O B A' O' B'') : ray O' B' = ray O' B'' :=
  (fr hl).layoff_unique Set.univ rfl A O B l O' A' B' B'' h (fun _ _ => trivial) hO' hA' hne
    trivial trivial hs h1 h2

theorem mem_ray_of_angCong (h : ¬Collinear (Line := L) A O B) (hO : O ∈ l) (hA : A ∈ l)
    (hs : SameSide l B B') (hc : AngCong A O B A O B') : B' ∈ ray O B := by
  obtain ⟨hAO, -, -⟩ := ne_of_nc hl h
  have e := layoff_unique hl h hO hA hAO hs (angCong_refl (Line := L) h) hc
  rw [e]
  exact mem_ray_self' (L := L) (fun e' => hs.2.1 (e' ▸ hO))

theorem interior_or_interior {L' : P} (hHL : ¬Collinear (Line := L) H O L') (hLO : L' ≠ O)
    (hs : SameSide (line (Line := L) O L' hLO.symm) H K) (hHK : ¬Collinear (Line := L) H O K) :
    K ∈ Interior (Line := L) H O L' ∨ H ∈ Interior (Line := L) K O L' :=
  (fr hl).interior_or_interior (S := Set.univ) rfl trivial trivial trivial trivial hHL hLO hs hHK

theorem isom_angCong {f : Equiv.Perm P} (hf : f ∈ Pas.isom (L := L))
    (h : ¬Collinear (Line := L) X Y Z) : AngCong X Y Z (f X) (f Y) (f Z) := by
  have h1 : ¬Collinear (Line := L) Y X Z := fun hh => h hh.swap12
  have h1' : ¬Collinear (Line := L) (f Y) (f X) (f Z) := fun hh =>
    h1 ((Pas.isom_collinear_iff hf).1 hh)
  obtain ⟨hYX, hZX, hYZ⟩ := ne_of_nc hl h1
  exact ((fr hl).sss h1 h1' (hf Y X hYX) (hf Y Z hYZ) (hf X Z hZX.symm)).1

/-- A5 -/
theorem angLt_irrefl : ¬AngLt (L := L) A O B A O B := by
  rintro ⟨h, -, X, hX, hc⟩
  obtain ⟨hAO, hBO, hAB⟩ := ne_of_nc hl h
  have hOl : O ∈ line (Line := L) O A hAO.symm := mem_line_left _
  have hAl : A ∈ line (Line := L) O A hAO.symm := mem_line_right _
  have hBl : B ∉ line (Line := L) O A hAO.symm := fun hB => h (collinear_of_mem hAl hOl hB)
  have hs : SameSide (line (Line := L) O A hAO.symm) X B := sameSide_of_between_mem' hAl hBl hX
  have hr : X ∈ ray O B := mem_ray_of_angCong hl h hOl hAl (sameSide_symm' hs) hc
  have e : X = B := eq_of_collinear_collinear (L := L) h (collinear_of_between hX).swap23
    (collinear_of_mem_ray hr)
  exact ne23_of_between (Line := L) hX e

/-- C4 -/
theorem between_refl_of_rightAng {G F : P} (hG : G ∈ l) (hF : F ∈ l)
    (h : RightAng (L := L) G F X) : Between X F (Pas.refl l X) := by
  obtain ⟨hn, C, hC', hc⟩ := h
  obtain ⟨hGF, hXF, -⟩ := ne_of_nc hl hn
  have hXl : X ∉ l := fun hX => hn (collinear_of_mem hG hF hX)
  have ho := Pas.refl_opp (L := L) hXl
  have h2 := isom_angCong hl (Pas.refl_isom (P := P) l) hn
  rw [Pas.refl_fix hG, Pas.refl_fix hF] at h2
  have hoC : OppositeSides l X C := opp_of_between_mem hF hXl hC'
  have hs : SameSide l C (Pas.refl l X) := OrderCore.sameSide_of_opp_opp (opp_symm' hoC) ho
  have nC : ¬Collinear (Line := L) G F C := fun hc' => hs.1 (mem_of_collinear hc' hGF hG hF)
  have hr : Pas.refl l X ∈ ray F C := mem_ray_of_angCong hl nC hF hG hs
    (angCong_trans (L := L) nC hn (fun hc' => hs.2.1 (mem_of_collinear hc' hGF hG hF))
      (angCong_symm (L := L) hn nC hc) h2)
  exact between_of_mem_rays hC' (mem_ray_self' (L := L) hXF) hr


/-- C5 -/
theorem no_two_right {F F' : P} (h1 : RightAng (L := L) F' F X) (h2 : RightAng (L := L) F F' X) :
    False := by
  obtain ⟨hF'F, hXF, -⟩ := ne_of_nc hl h1.1
  set t := line (Line := L) F F' hF'F.symm with ht
  have hFt : F ∈ t := mem_line_left _
  have hF't : F' ∈ t := mem_line_right _
  have hXt : X ∉ t := fun hX => h1.1 (collinear_of_mem hF't hFt hX)
  have b1 := between_refl_of_rightAng hl hF't hFt h1
  have b2 := between_refl_of_rightAng hl hFt hF't h2
  have hne : X ≠ Pas.refl t X := ne13_of_between (Line := L) b1
  obtain ⟨g, hXg, hX'g⟩ := exists_line (Line := L) hne
  have hFg : F ∈ g := mem_mid_of_between b1 hXg hX'g
  have hF'g : F' ∈ g := mem_mid_of_between b2 hXg hX'g
  have e : g = t := line_unique hF'F.symm hFg hF'g hFt hF't
  exact hXt (e ▸ hXg)

/-- 0.5 -/
theorem sameSide_of_not_meets {k m : L} (h : ¬Meets (Point := P) m k) (hX : X ∈ m) (hY : Y ∈ m) :
    SameSide k X Y :=
  ⟨fun hk => h ⟨X, hX, hk⟩, fun hk => h ⟨Y, hY, hk⟩,
    fun ⟨Z, hZk, hZ⟩ => h ⟨Z, mem_mid_of_between hZ hX hY, hZk⟩⟩

/-- A1 -/
theorem angLt_of_interior (h : ¬Collinear (Line := L) A O B) (h' : ¬Collinear (Line := L) A' O' B')
    (hX : X ∈ Interior (Line := L) A' O' B') (hc : AngCong A O B A' O' X) :
    AngLt (L := L) A O B A' O' B' := by
  obtain ⟨hAO, hBO, -⟩ := ne_of_nc hl h
  obtain ⟨hA'O', hB'O', -⟩ := ne_of_nc hl h'
  obtain ⟨Y, hY, hYr⟩ := crossbar hl h' hX
  have nX := (nc_of_interior (L := L) hA'O' hB'O' hX).1
  exact ⟨h, h', Y, hY, angCong_rays (L := L) h nX hc (mem_ray_self' (L := L) hAO)
    (mem_ray_self' (L := L) hBO) (mem_ray_self' (L := L) hA'O') hYr⟩

/-- 0.9 -/
theorem ht_spec {M : P} (h : X ≠ M) :
    Between X M (Pas.ht (L := L) M X) ∧ SegCong M X M (Pas.ht (L := L) M X) :=
  (Pas.ht_eq_iff (L := L) h).1 rfl

theorem midp_spec (h : A ≠ C) :
    Between A (Pas.midp (L := L) A C) C ∧ Pas.ht (L := L) (Pas.midp (L := L) A C) A = C ∧
      Pas.ht (L := L) (Pas.midp (L := L) A C) C = A := by
  have h1 : Pas.ht (L := L) (Pas.midp (L := L) A C) A = C := Pas.ht_midp (L := L) A C
  have hne : A ≠ Pas.midp (L := L) A C := fun e =>
    h (((Pas.ht_fix_iff (L := L)).2 e).symm.trans h1)
  refine ⟨((Pas.ht_eq_iff (L := L) hne).1 h1).1, h1, ?_⟩
  have h2 := Pas.ht_ht (L := L) (Pas.midp (L := L) A C) A
  rwa [h1] at h2

/-- D1, first half -/
theorem ext_angle_aux (h : ¬Collinear (Line := L) A B C) (hD : Between B C D) :
    AngLt (L := L) B A C A C D := by
  obtain ⟨hAB, hCB, hAC⟩ := ne_of_nc hl h
  obtain ⟨hM, f1, f2⟩ := midp_spec hl hAC
  generalize Pas.midp (L := L) A C = M at hM f1 f2
  have hDC : D ≠ C := (ne23_of_between (Line := L) hD).symm
  obtain ⟨a, hAa, hCa⟩ := exists_line (Line := L) hAC
  have hBa : B ∉ a := fun hB => h (collinear_of_mem hAa hB hCa)
  have hMa : M ∈ a := mem_mid_of_between hM hAa hCa
  have hBM : B ≠ M := fun e => hBa (e ▸ hMa)
  obtain ⟨hb, -⟩ := ht_spec hl hBM
  have nBAC : ¬Collinear (Line := L) B A C := fun hc => h hc.swap12
  have a1 := isom_angCong hl (Pas.ht_isom (L := L) M) nBAC
  have nB'CA : ¬Collinear (Line := L) (Pas.ht (L := L) M B) (Pas.ht (L := L) M A)
      (Pas.ht (L := L) M C) :=
    fun hh => nBAC ((Pas.isom_collinear_iff (Pas.ht_isom (L := L) M)).1 hh)
  rw [f1, f2] at a1 nB'CA
  generalize Pas.ht (L := L) M B = B' at hb a1 nB'CA
  have o1 : OppositeSides a B B' := opp_of_between_mem hMa hBa hb
  have o2 : OppositeSides a B D := opp_of_between_mem hCa hBa hD
  have s1 : SameSide a B' D := OrderCore.sameSide_of_opp_opp (opp_symm' o1) o2
  obtain ⟨n, hBn, hCn⟩ := exists_line (Line := L) hCB.symm
  have hAn : A ∉ n := fun hA => h (collinear_of_mem hA hBn hCn)
  have hDn : D ∈ n := mem_right_of_between hD hBn hCn
  have s2 : SameSide n M A := sameSide_of_between_mem' hCn hAn (between_symm hM)
  have hB'n : B' ∉ n := fun hB'n => s2.1 (mem_mid_of_between hb hBn hB'n)
  have s3 : SameSide n M B' := sameSide_of_between_mem' hBn hB'n hb
  have s4 : SameSide n B' A := OrderCore.sameSide_trans (sameSide_symm' s3) s2
  have hint : B' ∈ Interior (Line := L) A C D := by
    refine (interior_iff (L := L) hAC hDC).2 ⟨?_, ?_⟩
    · rw [← eq_line hAC.symm hCa hAa]; exact s1
    · rw [← eq_line hDC.symm hCn hDn]; exact s4
  have nACD : ¬Collinear (Line := L) A C D := fun hc => s1.2.1 (mem_of_collinear hc hAC hAa hCa)
  exact angLt_of_interior hl nBAC nACD hint (angCong_swap_right (Line := L) nBAC nB'CA a1)

/-- C10 -/
theorem exists_perp_at {F : P} (hF : F ∈ l) :
    ∃ m : L, F ∈ m ∧ ∀ Z : P, Z ∈ m → Z ≠ F → ∀ G : P, G ∈ l → G ≠ F →
      RightAng (L := L) G F Z := by
  obtain ⟨G₀, hG₀l, hG₀F⟩ : ∃ G₀ : P, G₀ ∈ l ∧ G₀ ≠ F := by
    obtain ⟨U, V, hUV, hU, hV⟩ := exists_two_points (Point := P) l
    by_cases hUF : U = F
    · exact ⟨V, hV, fun e => hUV (hUF.trans e.symm)⟩
    · exact ⟨U, hU, hUF⟩
  obtain ⟨hb, hs⟩ := ht_spec hl hG₀F
  generalize Pas.ht (L := L) F G₀ = G₁ at hb hs
  have hG₁F : G₁ ≠ F := (ne23_of_between (Line := L) hb).symm
  obtain ⟨m, hmem, hrefl, hopp⟩ := Pas.exists_eqd (L := L) (ne13_of_between (Line := L) hb)
  have hFm : F ∈ m := (hmem F).2 ⟨hG₀F.symm, hG₁F.symm, hs⟩
  refine ⟨m, hFm, fun Z hZm hZF G hG hGF => ?_⟩
  have hml : m ≠ l := fun e => hopp.1 (e ▸ hG₀l)
  have hZl : Z ∉ l := fun hZl => hZF (eq_of_mem_of_mem hml hZm hZl hFm hF)
  have hn : ¬Collinear (Line := L) G₀ F Z := fun hc => hZl (mem_of_collinear hc hG₀F hG₀l hF)
  have a1 := isom_angCong hl (Pas.refl_isom (P := P) m) hn
  rw [hrefl, Pas.refl_fix hFm, Pas.refl_fix hZm] at a1
  have hn₁ : ¬Collinear (Line := L) G₁ F Z := fun hc =>
    hZl (mem_of_collinear hc hG₁F (mem_right_of_between hb hG₀l hF) hF)
  have r1 : RightAng (L := L) Z F G₀ :=
    ⟨fun hc => hn hc.swap13, G₁, hb,
      angCong_swap_left (Line := L) hn (fun hc => hn₁ hc.swap13)
        (angCong_swap_right (Line := L) hn hn₁ a1)⟩
  exact (fr hl).rt_arm ((fr hl).rt_symm r1) hGF (collinear_of_mem hF hG₀l hG)

/-! statements -/

theorem saccheri_out_lt (h : Saccheri L A B C D) (hP : Between C D P') (hQ : Between A B Q)
    (hr : RightAng (L := L) B Q P') (hlt : SLt B D Q P') : AngLt (L := L) A C D B D P' := by
  sorry

theorem saccheri_sameType (h : Saccheri L A B C D) (h' : Saccheri L A' B' C' D') :
    SameType L A C D A' C' D' := by
  sorry

theorem lambert_nest {B₀ D₁ : P} (h : Lambert L M B D N) (hB₀ : Between M B₀ B)
    (hD₁ : Between N D₁ D) (h₁ : Lambert L M B₀ D₁ N) : SameType L B D N B₀ D₁ N := by
  sorry

theorem exists_triConf (h : ¬Collinear (Line := L) A B C) :
    ∃ F G H X Y A₁ B₁ : P, TriConf L A B C F G H X Y A₁ B₁ := by
  sorry

open Conclusion in
theorem tri_saccheri (h : ¬Collinear (Line := L) A B C) :
    ∃ F G : P, Saccheri L F G A B ∧ (AngleSumLtTwoRight L A B C ↔ LtSupp L F A B) ∧
      (AngleSumEqTwoRight L A B C ↔ EqSupp L F A B) ∧
      (AngleSumGtTwoRight L A B C ↔ GtSupp L F A B) := by
  sorry

end Thms

end AngSum

namespace Conclusion

open AngSum in
theorem angleSumTheorem' : AngleSumTheorem := by
  intro P L _ _ _ _ hC A B C A' B' C' hT'
  have key : ∀ hl : (∀ X : P, ∃ l : L, X ∈ l), IsTriangle (Line := L) A B C →
      (AngleSumGtTwoRight L A B C → AngleSumGtTwoRight L A' B' C') ∧
      (AngleSumEqTwoRight L A B C → AngleSumEqTwoRight L A' B' C') ∧
      (AngleSumLtTwoRight L A B C → AngleSumLtTwoRight L A' B' C') := by
    intro hl hT
    obtain ⟨F, G, hS, hLt, hEq, hGt⟩ := tri_saccheri hl hT
    obtain ⟨F', G', hS', hLt', hEq', hGt'⟩ := tri_saccheri hl hT'
    obtain ⟨t1, t2, t3⟩ := saccheri_sameType hl hS hS'
    exact ⟨fun h => hGt'.2 (t3.1 (hGt.1 h)), fun h => hEq'.2 (t2.1 (hEq.1 h)),
      fun h => hLt'.2 (t1.1 (hLt.1 h))⟩
  have hl_of : ∀ {X : P}, Between A C X → ∀ Z : P, ∃ l : L, Z ∈ l := fun hb =>
    line_through_of_ne (L := L) (ne12_of_between (Line := L) hb)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.1 h
  · have h0 := h
    obtain ⟨hT, X, Y, ⟨hb, -, -⟩, -⟩ := h0
    exact (key (hl_of hb) hT).2.2 h

end Conclusion

end HilbertFoundations
