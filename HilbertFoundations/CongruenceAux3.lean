import HilbertFoundations.CongruenceAux2

/-!
# Helper module for `Congruence.lean`: the congruence theorems of § 7 in a plane frame

This module contains no unit of Hilbert's text. It proves Theorems 10–16 of § 7 for an arbitrary
plane frame `F : Frame P L` (see `CongruenceAux.lean`), with the axioms of congruence IV 1–3,
the plane-free part of IV 4–5 and IV 6 (`TriangleCongruence`); the units of `Congruence.lean`
specialise them to plane geometry (`planeFrame`) and to space geometry (`spaceFrame`).

* `Frame.sas` (Theorem 10), `Frame.asa` (Theorem 11), `Frame.supp` (Theorem 12),
  `Frame.vertical` (vertical angles), `Frame.interior_transfer` (Theorem 13),
  `Frame.angle_addition` (Theorem 14, corrected), `Frame.right_angles` (Theorem 15),
  `Frame.sss` (Theorem 16), and `base_angles` (the isosceles triangle, IV 6 only).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v

section Interior

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  {A B O X : P}
include hO

/-- An interior point is on neither side line. -/
theorem nc_of_interior (hA : A ≠ O) (hB : B ≠ O) (hX : X ∈ Interior (Line := L) A O B) :
    ¬Collinear A O X ∧ ¬Collinear B O X := by
  have hi := (interior_iff (L := L) hA hB).1 hX
  exact ⟨fun hc => hi.1.1 (mem_of_collinear hc.swap12 hA.symm (mem_line_left _)
      (mem_line_right _)),
    fun hc => hi.2.1 (mem_of_collinear hc.swap12 hB.symm (mem_line_left _) (mem_line_right _))⟩

end Interior

/-- **The base angles of an isosceles triangle are congruent** (IV 6 applied to the triangles `CAB`
and `CBA`; with IV 1–2 for the symmetry of `CA ≡ CB`). -/
theorem base_angles {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
    [HasAngCong P] [TriangleCongruence P L] {A B C : P} (h : ¬Collinear C A B) (hCA : C ≠ A)
    (hCB : C ≠ B) (hc : SegCong C A C B) : AngCong C A B C B A := by
  have h' : ¬Collinear C B A := fun hh => h hh.swap23
  have hACB : ¬Collinear A C B := fun hh => h hh.swap12
  exact (angCong_of_sas h h' hc (segCong_symm (L := L) hCA hCB hc)
    (angCong_swap_right hACB hACB (angCong_refl hACB))).1

namespace Frame

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hT : TriangleCongruence P L] (F : Frame P L) {S S' : Set P}
  {A B C D O H K M A' B' C' D' O' H' K' M' X : P}
include hT F

/-- **Theorem 10** in a plane frame (first theorem of congruence for triangles). -/
theorem sas (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hA : AngCong B A C B' A' C') :
    SegCong B C B' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B' := by
  obtain ⟨hB, hC⟩ := angCong_of_sas h h' hAB hAC hA
  refine ⟨?_, hB, hC⟩
  obtain ⟨hAB0, hCB0, -⟩ := F.ne h
  obtain ⟨hAB', hCB', -⟩ := F.ne h'
  obtain ⟨D', hD'r, hD'c⟩ := segCong_layoff (L := L) hCB0.symm hCB'.symm
  have hn' : ¬Collinear A' B' D' :=
    not_collinear_of_mem_rays h' (mem_ray_self' (L := L) hAB') hD'r
  have hBAC : ¬Collinear B A C := fun hh => h hh.swap12
  have hB'A'D' : ¬Collinear B' A' D' := fun hh => hn' hh.swap12
  have hBc : AngCong A B C A' B' D' := angCong_rays h h' hB (mem_ray_self' (L := L) hAB0)
    (mem_ray_self' (L := L) hCB0) (mem_ray_self' (L := L) hAB') hD'r
  have h6 := angCong_of_sas hBAC hB'A'D' (segCong_swap hAB) hD'c hBc
  obtain ⟨S, hS, hA'S, hB'S, hC'S⟩ := F.exists_pl A' B' C' h'
  have hD'S := F.memS_of_ray hS hB'S hC'S hD'r
  have hC'l : C' ∉ line (Line := L) A' B' hAB' := fun hh =>
    h' (collinear_of_mem (mem_line_left _) (mem_line_right _) hh)
  have hss : SameSide (line (Line := L) A' B' hAB') C' D' :=
    sameSide_of_ray (mem_line_right _) hC'l hD'r
  have e := F.layoff_unique S hS B A C _ A' B' C' D' hBAC (F.lineIn hS hA'S hB'S hAB')
    (mem_line_left _) (mem_line_right _) hAB'.symm hC'S hD'S hss hA h6.1
  have hD'A' : D' ≠ A' := (F.ne hn').2.2.symm
  have hD'r2 : D' ∈ ray A' C' := by rw [e]; exact mem_ray_self' (L := L) hD'A'
  have e2 : D' = C' := eq_of_collinear_collinear h' (collinear_of_mem_ray hD'r2)
    (collinear_of_mem_ray hD'r)
  rw [← e2]; exact hD'c

/-- **Theorem 11** in a plane frame (second theorem of congruence for triangles). -/
theorem asa (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hAB : SegCong A B A' B')
    (hA : AngCong B A C B' A' C') (hB : AngCong A B C A' B' C') :
    SegCong A C A' C' ∧ SegCong B C B' C' ∧ AngCong A C B A' C' B' := by
  obtain ⟨hAB0, hCB0, hAC0⟩ := F.ne h
  obtain ⟨hAB', hCB', hAC'⟩ := F.ne h'
  obtain ⟨C2, hC2r, hC2c⟩ := segCong_layoff (L := L) hAC0 hAC'
  have hn2 : ¬Collinear A' B' C2 := fun hh => not_collinear_of_mem_rays
    (fun hh' => h' hh'.swap12) (mem_ray_self' (L := L) hAB'.symm) hC2r hh.swap12
  have hA2 : AngCong B A C B' A' C2 := angCong_rays (fun hh => h hh.swap12)
    (fun hh => h' hh.swap12) hA (mem_ray_self' (L := L) hAB0.symm)
    (mem_ray_self' (L := L) hAC0.symm) (mem_ray_self' (L := L) hAB'.symm) hC2r
  obtain ⟨s1, a1, a2⟩ := F.sas h hn2 hAB hC2c hA2
  obtain ⟨S, hS, hA'S, hB'S, hC'S⟩ := F.exists_pl A' B' C' h'
  have hC2S := F.memS_of_ray hS hA'S hC'S hC2r
  have hC'l : C' ∉ line (Line := L) B' A' hAB'.symm := fun hh =>
    h' (collinear_of_mem (mem_line_right _) (mem_line_left _) hh)
  have hss : SameSide (line (Line := L) B' A' hAB'.symm) C' C2 :=
    sameSide_of_ray (mem_line_right _) hC'l hC2r
  have e := F.layoff_unique S hS A B C _ B' A' C' C2 h (F.lineIn hS hB'S hA'S hAB'.symm)
    (mem_line_left _) (mem_line_right _) hAB' hC'S hC2S hss hB a1
  have hC2B' : C2 ≠ B' := (F.ne hn2).2.1
  have hC2r' : C2 ∈ ray B' C' := by rw [e]; exact mem_ray_self' (L := L) hC2B'
  have e2 : C2 = C' := eq_of_collinear_collinear h' (collinear_of_mem_ray hC2r)
    (collinear_of_mem_ray hC2r')
  subst e2
  exact ⟨hC2c, s1, a2⟩

/-- **Theorem 12** in a plane frame: supplementary angles of congruent angles are congruent. -/
theorem supp (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hc : AngCong A B C A' B' C')
    (hD : Between A B D) (hD' : Between A' B' D') : AngCong C B D C' B' D' := by
  obtain ⟨hAB, hCB, -⟩ := F.ne h
  obtain ⟨hAB', hCB', -⟩ := F.ne h'
  have hDB := (ne23_of_between hD).symm
  have hDB' := (ne23_of_between hD').symm
  obtain ⟨A2, hA2r, hA2c⟩ := segCong_layoff (L := L) hAB.symm hAB'.symm
  obtain ⟨C2, hC2r, hC2c⟩ := segCong_layoff (L := L) hCB.symm hCB'.symm
  obtain ⟨D2, hD2r, hD2c⟩ := segCong_layoff (L := L) hDB.symm hDB'.symm
  have hn2 : ¬Collinear A2 B' C2 := not_collinear_of_mem_rays h' hA2r hC2r
  have hb2 : Between A2 B' D2 := between_of_mem_rays hD' hA2r hD2r
  have hc2 : AngCong A B C A2 B' C2 := angCong_rays h h' hc (mem_ray_self' (L := L) hAB)
    (mem_ray_self' (L := L) hCB) hA2r hC2r
  have hBAC : ¬Collinear B A C := fun hh => h hh.swap12
  have hB'A2C2 : ¬Collinear B' A2 C2 := fun hh => hn2 hh.swap12
  obtain ⟨s1, a1, -⟩ := F.sas (A := B) (B := A) (C := C) (A' := B') (B' := A2) (C' := C2) hBAC
    hB'A2C2 hA2c hC2c hc2
  have sAD : SegCong A D A2 D2 := segCong_add hD hb2 (segCong_swap hA2c) hD2c
  -- the lines `AB` and `A2B'`
  have hAB2 : A2 ≠ B' := (F.ne hn2).1
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hDl : D ∈ line (Line := L) A B hAB := mem_right_of_between hD hAl hBl
  have hCl : C ∉ line (Line := L) A B hAB := fun hh => h (collinear_of_mem hAl hBl hh)
  have hA2l : A2 ∈ line (Line := L) A2 B' hAB2 := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A2 B' hAB2 := mem_line_right _
  have hD2l : D2 ∈ line (Line := L) A2 B' hAB2 := mem_right_of_between hb2 hA2l hB'l
  have hC2l : C2 ∉ line (Line := L) A2 B' hAB2 := fun hh => hn2 (collinear_of_mem hA2l hB'l hh)
  have hAD : A ≠ D := ne13_of_between hD
  have hAD2 : A2 ≠ D2 := ne13_of_between hb2
  have nACD := nc_of hAl hDl hAD hCl
  have nACD2 := nc_of hA2l hD2l hAD2 hC2l
  have nCAB := nc_of hAl hBl hAB hCl
  have nCAB2 := nc_of hA2l hB'l hAB2 hC2l
  have a1' : AngCong C A B C2 A2 B' :=
    angCong_swap_right nCAB.2.2.1 hB'A2C2 (angCong_swap_left hBAC hB'A2C2 a1)
  have aCAD : AngCong C A D C2 A2 D2 := angCong_rays nCAB.2.2.1 nCAB2.2.2.1 a1'
    (mem_ray_self' (L := L) (F.ne nCAB.2.2.1).1) (mem_ray_of_between' hD)
    (mem_ray_self' (L := L) (F.ne nCAB2.2.2.1).1) (mem_ray_of_between' hb2)
  obtain ⟨s2, -, a2⟩ := F.sas (A := A) (B := C) (C := D) (A' := A2) (B' := C2) (C' := D2)
    nACD.2.1 nACD2.2.1 s1 sAD aCAD
  have aBDC : AngCong B D C B' D2 C2 := angCong_rays nACD.1 nACD2.1 a2
    (mem_ray_of_between (between_symm hD)) (mem_ray_self' (L := L) (F.ne nACD.1).2.1)
    (mem_ray_of_between (between_symm hb2)) (mem_ray_self' (L := L) (F.ne nACD2.1).2.1)
  have nDBC := nc_of hDl hBl hDB hCl
  have nDBC2 := nc_of hD2l hB'l (ne23_of_between hb2).symm hC2l
  obtain ⟨a3, -⟩ := angCong_of_sas nDBC.1 nDBC2.1 (segCong_swap hD2c) (segCong_swap s2) aBDC
  have a3' : AngCong C B D C2 B' D2 := angCong_swap_right nDBC.2.2.2.2.2 nDBC2.1
    (angCong_swap_left nDBC.1 nDBC2.1 a3)
  exact angCong_rays nDBC.2.2.2.2.2 nDBC2.2.2.2.2.2 a3'
    (mem_ray_self' (L := L) hCB) (mem_ray_self' (L := L) hDB) (mem_ray_comm hC2r)
    (mem_ray_comm hD2r)

/-- **Vertical angles are congruent** (consequence of Theorem 12). -/
theorem vertical (h : ¬Collinear A O B) (h1 : Between A O C) (h2 : Between B O D) :
    AngCong A O B C O D := by
  have hCOB : ¬Collinear C O B := not_collinear_of_between h h1
  have hBOC : ¬Collinear B O C := not_collinear_swap hCOB
  have hDOC : ¬Collinear D O C := not_collinear_of_between hBOC h2
  have := F.supp (A := C) (B := O) (C := B) (D := A) (A' := B) (B' := O) (C' := C) (D' := D)
    hCOB hBOC (angCong_swap_right hCOB hCOB (angCong_refl hCOB)) (between_symm h1) h2
  exact angCong_swap_left (not_collinear_swap h) (not_collinear_swap hDOC) this

/-- **Theorem 13** in a plane frame: a half-ray within an angle is carried to a half-ray within a
congruent angle. -/
theorem interior_transfer (hS : F.IsPl S) (hOS : O ∈ S) (hAS : A ∈ S) (hBS : B ∈ S)
    (hXS : X ∈ S) (h : ¬Collinear A O B) (h' : ¬Collinear A' O' B')
    (hc : AngCong A O B A' O' B') (hX : X ∈ Interior A O B) :
    ∃ Y, (∀ S', F.IsPl S' → O' ∈ S' → A' ∈ S' → B' ∈ S' → Y ∈ S') ∧
      Y ∈ Interior A' O' B' ∧ AngCong A O X A' O' Y ∧ AngCong B O X B' O' Y := by
  obtain ⟨hAO, hBO, hAB⟩ := F.ne h
  obtain ⟨hAO', hBO', hAB'⟩ := F.ne h'
  obtain ⟨A2, hA2r, hA2c⟩ := segCong_layoff (L := L) hAO.symm hAO'.symm
  obtain ⟨B2, hB2r, hB2c⟩ := segCong_layoff (L := L) hBO.symm hBO'.symm
  have hn2 : ¬Collinear A2 O' B2 := not_collinear_of_mem_rays h' hA2r hB2r
  have hc2 : AngCong A O B A2 O' B2 := angCong_rays h h' hc (mem_ray_self' (L := L) hAO)
    (mem_ray_self' (L := L) hBO) hA2r hB2r
  have hOAB : ¬Collinear O A B := fun hh => h hh.swap12
  have hO'A2B2 : ¬Collinear O' A2 B2 := fun hh => hn2 hh.swap12
  obtain ⟨s1, a1, a2⟩ := F.sas (A := O) (B := A) (C := B) (A' := O') (B' := A2) (C' := B2) hOAB
    hO'A2B2 hA2c hB2c hc2
  obtain ⟨C, hC, hCr⟩ := F.crossbar hS hOS hAS hBS hXS h hX
  have hAB2 : A2 ≠ B2 := (F.ne hn2).2.2
  obtain ⟨C2, hC2r, hC2c⟩ := segCong_layoff (L := L) (ne12_of_between hC) hAB2
  have hb2 : Between A2 C2 B2 := between_of_segCong_ray hC hC2r hC2c s1
  have s2 : SegCong C B C2 B2 := segCong_sub hC hb2 hC2c s1
  have hAl : A ∈ line (Line := L) A B hAB := mem_line_left _
  have hBl : B ∈ line (Line := L) A B hAB := mem_line_right _
  have hCl : C ∈ line (Line := L) A B hAB := mem_mid_of_between hC hAl hBl
  have hOl : O ∉ line (Line := L) A B hAB := fun hh => h (collinear_of_mem hAl hh hBl)
  have hA2l : A2 ∈ line (Line := L) A2 B2 hAB2 := mem_line_left _
  have hB2l : B2 ∈ line (Line := L) A2 B2 hAB2 := mem_line_right _
  have hC2l : C2 ∈ line (Line := L) A2 B2 hAB2 := mem_mid_of_between hb2 hA2l hB2l
  have hO'l : O' ∉ line (Line := L) A2 B2 hAB2 := fun hh => hn2 (collinear_of_mem hA2l hh hB2l)
  have nAC := nc_of hAl hCl (ne12_of_between hC) hOl
  have nBC := nc_of hBl hCl (ne23_of_between hC).symm hOl
  have nAC2 := nc_of hA2l hC2l (ne12_of_between hb2) hO'l
  have nBC2 := nc_of hB2l hC2l (ne23_of_between hb2).symm hO'l
  have nAB := nc_of hAl hBl hAB hOl
  have nAB2 := nc_of hA2l hB2l hAB2 hO'l
  have aOAC : AngCong O A C O' A2 C2 := angCong_rays nAB.2.2.1 nAB2.2.2.1 a1
    (mem_ray_self' (L := L) (F.ne nAB.2.2.1).1) (mem_ray_of_between hC)
    (mem_ray_self' (L := L) (F.ne nAB2.2.2.1).1) hC2r
  obtain ⟨-, b1, -⟩ := F.sas (A := A) (B := O) (C := C) (A' := A2) (B' := O') (C' := C2)
    nAC.2.1 nAC2.2.1 (segCong_swap hA2c) hC2c aOAC
  have aOBC : AngCong O B C O' B2 C2 := angCong_rays nAB.2.2.2.2.2 nAB2.2.2.2.2.2 a2
    (mem_ray_self' (L := L) (F.ne nAB.2.2.2.2.2).1) (mem_ray_of_between (between_symm hC))
    (mem_ray_self' (L := L) (F.ne nAB2.2.2.2.2.2).1) (mem_ray_of_between (between_symm hb2))
  obtain ⟨-, b2, -⟩ := F.sas (A := B) (B := O) (C := C) (A' := B2) (B' := O') (C' := C2)
    nBC.2.1 nBC2.2.1 (segCong_swap hB2c) (segCong_swap s2) aOBC
  have hC2r' : C2 ∈ ray O' C2 := mem_ray_self' (L := L) (F.ne nAC2.2.1).2.1
  refine ⟨C2, ?_, ?_, ?_, ?_⟩
  · intro S' hS' hO' hA' hB'
    exact F.memS_of_between hS' (F.memS_of_ray hS' hO' hA' hA2r) (F.memS_of_ray hS' hO' hB' hB2r)
      hb2
  · obtain ⟨S', hS', hA'S, hO'S, hB'S⟩ := F.exists_pl A' O' B' h'
    have hA2S := F.memS_of_ray hS' hO'S hA'S hA2r
    have hB2S := F.memS_of_ray hS' hO'S hB'S hB2r
    exact F.mem_interior_of_rays hS' hO'S hA2S hB2S (F.memS_of_between hS' hA2S hB2S hb2) hn2
      (mem_interior_of_between hn2 hb2) (mem_ray_comm hA2r) (mem_ray_comm hB2r)
  · exact angCong_rays nAC.2.1 nAC2.2.1 b1 (mem_ray_self' (L := L) hAO) (mem_ray_comm hCr)
      (mem_ray_comm hA2r) hC2r'
  · exact angCong_rays nBC.2.1 nBC2.2.1 b2 (mem_ray_self' (L := L) hBO) (mem_ray_comm hCr)
      (mem_ray_comm hB2r) hC2r'

/-- The case of Theorem 14 in which `k` lies within the angle `(h, l)` (the half-rays `h'`, `k'`
lying on the same side of `l'`). -/
theorem addition_aux (hS : F.IsPl S) (hS' : F.IsPl S') (hO : O ∈ S) (hH : H ∈ S) (hK : K ∈ S)
    (hM : M ∈ S) (hO' : O' ∈ S') (hH' : H' ∈ S') (hK' : K' ∈ S') (hM' : M' ∈ S')
    (hHM : ¬Collinear H O M) (hKM : ¬Collinear K O M) (hH'M' : ¬Collinear H' O' M')
    (hK'M' : ¬Collinear K' O' M') (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M')
    (hKi : K ∈ Interior H O M) (hMO' : M' ≠ O')
    (hs' : SameSide (line (Line := L) O' M' hMO'.symm) H' K') : AngCong H O K H' O' K' := by
  obtain ⟨hHO, hMO, -⟩ := F.ne hHM
  obtain ⟨hHO', -, -⟩ := F.ne hH'M'
  obtain ⟨K2, hK2S, hK2i, a1, a2⟩ := F.interior_transfer hS hO hH hM hK hHM hH'M' h1 hKi
  have hK2S' := hK2S S' hS' hO' hH' hM'
  have i2 := (interior_iff (L := L) hHO' hMO').1 hK2i
  have hl := F.lineIn hS' hO' hM' hMO'.symm
  have hss : SameSide (line (Line := L) O' M' hMO'.symm) K' K2 :=
    F.ss_trans hS' hl hK' hH' hK2S' (sameSide_symm' hs') (sameSide_symm' i2.2)
  have hMOK : ¬Collinear M O K := fun hh => hKM hh.swap13
  have hM'O'K' : ¬Collinear M' O' K' := fun hh => hK'M' hh.swap13
  have a2' : AngCong M O K M' O' K' :=
    angCong_swap_right (not_collinear_swap hKM) hK'M' (angCong_swap_left hKM hK'M' h2)
  have e := F.layoff_unique S' hS' M O K _ O' M' K' K2 hMOK hl (mem_line_left _)
    (mem_line_right _) hMO' hK' hK2S' hss a2' a2
  have nHK := (nc_of_interior (L := L) hHO hMO hKi).1
  have nHK2 := (nc_of_interior (L := L) hHO' hMO' hK2i).1
  have hK'O' : K' ≠ O' := (F.ne hK'M').1
  exact angCong_rays nHK nHK2 a1 (mem_ray_self' (L := L) hHO)
    (mem_ray_self' (L := L) (F.ne nHK).2.1) (mem_ray_self' (L := L) hHO')
    (by rw [← e]; exact mem_ray_self' (L := L) hK'O')

/-- Theorem 14 when `h`, `k` lie on the same side of `l` and `h'`, `k'` on the same side of `l'`. -/
theorem addition_same (hS : F.IsPl S) (hS' : F.IsPl S') (hO : O ∈ S) (hH : H ∈ S) (hK : K ∈ S)
    (hM : M ∈ S) (hO' : O' ∈ S') (hH' : H' ∈ S') (hK' : K' ∈ S') (hM' : M' ∈ S')
    (hHM : ¬Collinear H O M) (hKM : ¬Collinear K O M) (hHK : ¬Collinear H O K)
    (hH'M' : ¬Collinear H' O' M') (hK'M' : ¬Collinear K' O' M') (hH'K' : ¬Collinear H' O' K')
    (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M') (hMO : M ≠ O) (hMO' : M' ≠ O')
    (hs : SameSide (line (Line := L) O M hMO.symm) H K)
    (hs' : SameSide (line (Line := L) O' M' hMO'.symm) H' K') : AngCong H O K H' O' K' := by
  rcases F.interior_or_interior hS hO hH hK hM hHM hMO hs hHK with hi | hi
  · exact F.addition_aux hS hS' hO hH hK hM hO' hH' hK' hM' hHM hKM hH'M' hK'M' h1 h2 hi hMO' hs'
  · have := F.addition_aux hS hS' hO hK hH hM hO' hK' hH' hM' hKM hHM hK'M' hH'M' h2 h1 hi hMO'
      (sameSide_symm' hs')
    exact angCong_swap_right hHK (not_collinear_swap hH'K')
      (angCong_swap_left (not_collinear_swap hHK) (not_collinear_swap hH'K') this)

/-- **Theorem 14** in a plane frame, **corrected**: the half-rays `h`, `k` must lie on the same
side of `l` exactly when `h'`, `k'` lie on the same side of `l'`. -/
theorem angle_addition (hS : F.IsPl S) (hS' : F.IsPl S') (hO : O ∈ S) (hH : H ∈ S)
    (hK : K ∈ S) (hM : M ∈ S) (hO' : O' ∈ S') (hH' : H' ∈ S') (hK' : K' ∈ S') (hM' : M' ∈ S')
    (hHM : ¬Collinear H O M) (hKM : ¬Collinear K O M) (hHK : ¬Collinear H O K)
    (hH'M' : ¬Collinear H' O' M') (hK'M' : ¬Collinear K' O' M') (hH'K' : ¬Collinear H' O' K')
    (h1 : AngCong H O M H' O' M') (h2 : AngCong K O M K' O' M') (hMO : M ≠ O) (hMO' : M' ≠ O')
    (hside : (SameSide (line (Line := L) O M hMO.symm) H K ∧
        SameSide (line (Line := L) O' M' hMO'.symm) H' K') ∨
      (OppositeSides (line (Line := L) O M hMO.symm) H K ∧
        OppositeSides (line (Line := L) O' M' hMO'.symm) H' K')) :
    AngCong H O K H' O' K' := by
  rcases hside with ⟨hs, hs'⟩ | ⟨hs, hs'⟩
  · exact F.addition_same hS hS' hO hH hK hM hO' hH' hK' hM' hHM hKM hHK hH'M' hK'M' hH'K' h1 h2
      hMO hMO' hs hs'
  · obtain ⟨hHO, -, -⟩ := F.ne hHM
    obtain ⟨hHO', -, -⟩ := F.ne hH'M'
    obtain ⟨H2, hH2⟩ := exists_beyond (Line := L) hHO
    obtain ⟨H2', hH2'⟩ := exists_beyond (Line := L) hHO'
    have hH2S := F.memS_of_between' hS hH hO hH2
    have hH2S' := F.memS_of_between' hS' hH' hO' hH2'
    have nH2M := not_collinear_of_between hHM hH2
    have nH2M' := not_collinear_of_between hH'M' hH2'
    have nH2K := not_collinear_of_between hHK hH2
    have nH2K' := not_collinear_of_between hH'K' hH2'
    have c1 : AngCong M O H2 M' O' H2' := F.supp hHM hH'M' h1 hH2 hH2'
    have c1' : AngCong H2 O M H2' O' M' := angCong_swap_right nH2M (not_collinear_swap nH2M')
      (angCong_swap_left (not_collinear_swap nH2M) (not_collinear_swap nH2M') c1)
    have hl := F.lineIn hS hO hM hMO.symm
    have hl' := F.lineIn hS' hO' hM' hMO'.symm
    have s1 : SameSide (line (Line := L) O M hMO.symm) H2 K := F.ss_of_opp_opp hS hl hH2S hH hK
      (opp_symm' (opp_of_between_mem (mem_line_left _) hs.1 hH2)) hs
    have s1' : SameSide (line (Line := L) O' M' hMO'.symm) H2' K' := F.ss_of_opp_opp hS' hl' hH2S'
      hH' hK' (opp_symm' (opp_of_between_mem (mem_line_left _) hs'.1 hH2')) hs'
    have c2 := F.addition_same hS hS' hO hH2S hK hM hO' hH2S' hK' hM' nH2M hKM nH2K nH2M' hK'M'
      nH2K' c1' h2 hMO hMO' s1 s1'
    have c3 : AngCong K O H K' O' H' := F.supp nH2K nH2K' c2 (between_symm hH2)
      (between_symm hH2')
    exact angCong_swap_right hHK (not_collinear_swap hH'K')
      (angCong_swap_left (not_collinear_swap hHK) (not_collinear_swap hH'K') c3)


/-- The contradiction in Hilbert's proof of Theorem 15: a right angle `B'A'D'` laid off on `AB`
within the right angle `BAD`. -/
theorem right_angles_aux (hS : F.IsPl S) (hA : A ∈ S) (hB : B ∈ S) (hD : D ∈ S)
    (hb : Between B A C) (h : ¬Collinear B A D) (hr : AngCong B A D C A D)
    (hb' : Between B' A' C') (h' : ¬Collinear B' A' D') (hr' : AngCong B' A' D' C' A' D')
    {D2 : P} (hD2S : D2 ∈ S) (hD2i : D2 ∈ Interior B A D) (hc : AngCong B' A' D' B A D2) :
    False := by
  obtain ⟨hBA, hDA, -⟩ := F.ne h
  have hCA : C ≠ A := (ne23_of_between hb).symm
  have hCS := F.memS_of_between' hS hB hA hb
  have hnBAD2 : ¬Collinear B A D2 := (nc_of_interior (L := L) hBA hDA hD2i).1
  have hnCAD : ¬Collinear C A D := not_collinear_of_between h hb
  have hnCAD2 : ¬Collinear C A D2 := not_collinear_of_between hnBAD2 hb
  have hnCAD' : ¬Collinear C' A' D' := not_collinear_of_between h' hb'
  have s1 : AngCong D' A' C' D2 A C := F.supp h' hnBAD2 hc hb' hb
  have s2 : AngCong C' A' D' C A D2 := angCong_swap_right hnCAD' (not_collinear_swap hnCAD2)
    (angCong_swap_left (not_collinear_swap hnCAD') (not_collinear_swap hnCAD2) s1)
  have t : AngCong B A D2 C A D2 := angCong_trans hnBAD2 hnCAD' hnCAD2
    (angCong_trans hnBAD2 h' hnCAD' (angCong_symm h' hnBAD2 hc) hr') s2
  obtain ⟨D3, hD3S, hD3i, a1, -⟩ := F.interior_transfer hS hA hB hD hD2S h hnCAD hr hD2i
  have hD3S' := hD3S S hS hA hCS hD
  have hnCAD3 : ¬Collinear C A D3 := (nc_of_interior (L := L) hCA hDA hD3i).1
  have u : AngCong C A D2 C A D3 := angCong_trans_left hnBAD2 hnCAD2 hnCAD3 t a1
  have hCl : C ∈ line (Line := L) A B hBA.symm :=
    mem_right_of_between hb (mem_line_right _) (mem_line_left _)
  have el : line (Line := L) A B hBA.symm = line A C hCA.symm :=
    eq_line hCA.symm (mem_line_left _) hCl
  have i2 := (interior_iff (L := L) hBA hDA).1 hD2i
  have i3 := (interior_iff (L := L) hCA hDA).1 hD3i
  have hl := F.lineIn hS hA hCS hCA.symm
  have i2' : SameSide (line (Line := L) A C hCA.symm) D2 D := by rw [← el]; exact i2.1
  have hss : SameSide (line (Line := L) A C hCA.symm) D2 D3 :=
    F.ss_trans hS hl hD2S hD hD3S' i2' (sameSide_symm' i3.1)
  have e := F.layoff_unique S hS C A D2 _ A C D2 D3 hnCAD2 hl (mem_line_left _) (mem_line_right _)
    hCA hD2S hD3S' hss (angCong_refl hnCAD2) u
  have hD2A : D2 ≠ A := (F.ne hnBAD2).2.1
  have hD2i' : D2 ∈ Interior C A D := F.mem_interior_of_ray hS hA hCS hD hD3S' hnCAD hD3i
    (by rw [← e]; exact mem_ray_self' (L := L) hD2A)
  exact F.interior_disjoint hS hA hB hD hD2S h hb hD2i hD2i'

/-- **Theorem 15** in a plane frame: all right angles are congruent. The right angle `BAD` is
congruent to its supplementary angle `CAD` (`A` between `B` and `C`), and likewise `B'A'D'`. -/
theorem right_angles (hb : Between B A C) (h : ¬Collinear B A D) (hr : AngCong B A D C A D)
    (hb' : Between B' A' C') (h' : ¬Collinear B' A' D') (hr' : AngCong B' A' D' C' A' D') :
    AngCong B A D B' A' D' := by
  by_contra hne
  obtain ⟨hBA, hDA, -⟩ := F.ne h
  have hCA : C ≠ A := (ne23_of_between hb).symm
  obtain ⟨S, hS, hBS, hAS, hDS⟩ := F.exists_pl B A D h
  have hCS := F.memS_of_between' hS hBS hAS hb
  have hDl : D ∉ line (Line := L) A B hBA.symm := fun hh =>
    h (collinear_of_mem (mem_line_right _) (mem_line_left _) hh)
  obtain ⟨D2, hD2S, hss, hc⟩ := F.layoff S hS B' A' D' _ A B D h'
    (F.lineIn hS hAS hBS hBA.symm) (mem_line_left _) (mem_line_right _) hBA hDS hDl
  have hD2A : D2 ≠ A := ne_of_mem_not_mem (mem_line_left _) hss.1
  have hnCAD : ¬Collinear C A D := not_collinear_of_between h hb
  have hnCAD' : ¬Collinear C' A' D' := not_collinear_of_between h' hb'
  have hnBAD2 : ¬Collinear B A D2 := fun hh =>
    hss.1 (mem_of_collinear (a := line (Line := L) A B hBA.symm) (hh.swap12 : Collinear A B D2)
      hBA.symm (mem_line_left _) (mem_line_right _))
  by_cases hcol : Collinear A D D2
  · have hr2 : D2 ∈ ray A D := mem_ray_of_sameSide (mem_line_left (Line := L) hBA.symm) hcol hD2A
      (sameSide_symm' hss)
    exact hne (angCong_symm h' h (angCong_rays h' hnBAD2 hc
      (mem_ray_self' (L := L) (F.ne h').1) (mem_ray_self' (L := L) (F.ne h').2.1)
      (mem_ray_self' (L := L) hBA) (mem_ray_comm hr2)))
  · have hD2m : D2 ∉ line (Line := L) A D hDA.symm := fun hh =>
      hcol (collinear_of_mem (mem_line_left _) (mem_line_right _) hh)
    have hBm : B ∉ line (Line := L) A D hDA.symm := fun hh =>
      h (collinear_of_mem hh (mem_line_left _) (mem_line_right _))
    rcases sameSide_or_opp' hD2m hBm with h1 | h1
    · exact F.right_angles_aux hS hAS hBS hDS hb h hr hb' h' hr' hD2S
        ((interior_iff (L := L) hBA hDA).2 ⟨hss, h1⟩) hc
    · have h2 : SameSide (line (Line := L) A D hDA.symm) D2 C := F.ss_of_opp_opp hS
        (F.lineIn hS hAS hDS hDA.symm) hD2S hBS hCS h1
        (opp_of_between_mem (mem_line_left _) hBm hb)
      have hCl : C ∈ line (Line := L) A B hBA.symm :=
        mem_right_of_between hb (mem_line_right _) (mem_line_left _)
      have el : line (Line := L) A B hBA.symm = line A C hCA.symm :=
        eq_line hCA.symm (mem_line_left _) hCl
      have hss' : SameSide (line (Line := L) A C hCA.symm) D2 D := by rw [← el]; exact hss
      have hi : D2 ∈ Interior C A D := (interior_iff (L := L) hCA hDA).2 ⟨hss', h2⟩
      have hnCAD2 : ¬Collinear C A D2 := not_collinear_of_between hnBAD2 hb
      have s1 : AngCong D' A' C' D2 A C := F.supp h' hnBAD2 hc hb' hb
      have hc2 : AngCong C' A' D' C A D2 := angCong_swap_right hnCAD'
        (not_collinear_swap hnCAD2)
        (angCong_swap_left (not_collinear_swap hnCAD') (not_collinear_swap hnCAD2) s1)
      exact F.right_angles_aux hS hAS hCS hDS (between_symm hb) hnCAD (angCong_symm h hnCAD hr)
        (between_symm hb') hnCAD' (angCong_symm h' hnCAD' hr') hD2S hi hc2

/-- **Theorem 16** in a plane frame (third theorem of congruence for triangles). -/
theorem sss (h : ¬Collinear A B C) (h' : ¬Collinear A' B' C') (hAB : SegCong A B A' B')
    (hAC : SegCong A C A' C') (hBC : SegCong B C B' C') :
    AngCong B A C B' A' C' ∧ AngCong A B C A' B' C' ∧ AngCong A C B A' C' B' := by
  obtain ⟨hAB0, hCB0, hAC0⟩ := F.ne h
  obtain ⟨hAB', hCB', hAC'⟩ := F.ne h'
  suffices key : AngCong B A C B' A' C' by
    obtain ⟨-, x, y⟩ := F.sas h h' hAB hAC key
    exact ⟨key, x, y⟩
  obtain ⟨S, hS, hA'S, hB'S, hC'S⟩ := F.exists_pl A' B' C' h'
  have hl := F.lineIn hS hA'S hB'S hAB'
  have hA'l : A' ∈ line (Line := L) A' B' hAB' := mem_line_left _
  have hB'l : B' ∈ line (Line := L) A' B' hAB' := mem_line_right _
  have hC'l : C' ∉ line (Line := L) A' B' hAB' := fun hh => h' (collinear_of_mem hA'l hB'l hh)
  obtain ⟨C0, hC0⟩ := exists_beyond (Line := L) hAC'.symm
  have hC0S := F.memS_of_between' hS hC'S hA'S hC0
  have hopp0 : OppositeSides (line (Line := L) A' B' hAB') C' C0 :=
    opp_of_between_mem hA'l hC'l hC0
  have hBAC : ¬Collinear B A C := fun hh => h hh.swap12
  obtain ⟨X, hXS, hXs, hXc⟩ := F.layoff S hS B A C _ A' B' C0 hBAC hl hA'l hB'l hAB'.symm hC0S
    hopp0.2.1
  have hXA' : X ≠ A' := ne_of_mem_not_mem hA'l hXs.1
  obtain ⟨C2, hC2r, hC2c⟩ := segCong_layoff (L := L) hAC0 hXA'.symm
  have hC2S := F.memS_of_ray hS hA'S hXS hC2r
  have hss2 : SameSide (line (Line := L) A' B' hAB') X C2 := sameSide_of_ray hA'l hXs.1 hC2r
  have hopp : OppositeSides (line (Line := L) A' B' hAB') C' C2 := opp_symm'
    (F.opp_of_ss_opp hS hl hC2S hC0S hC'S
      (F.ss_trans hS hl hC2S hXS hC0S (sameSide_symm' hss2) hXs) (opp_symm' hopp0))
  have nC2 := nc_of hA'l hB'l hAB' hopp.2.1
  have nC' := nc_of hA'l hB'l hAB' hC'l
  have nX := nc_of hA'l hB'l hAB' hXs.1
  have hc2 : AngCong B A C B' A' C2 := angCong_rays hBAC nX.2.2.2.1 hXc
    (mem_ray_self' (L := L) hAB0.symm) (mem_ray_self' (L := L) hAC0.symm)
    (mem_ray_self' (L := L) hAB'.symm) hC2r
  obtain ⟨s1, -, -⟩ := F.sas h nC2.1 hAB hC2c hc2
  have hC2A' : A' ≠ C2 := (ne_of_mem_not_mem hA'l hopp.2.1).symm
  have hC2B' : B' ≠ C2 := (ne_of_mem_not_mem hB'l hopp.2.1).symm
  have e1 : SegCong A' C' A' C2 := segCong_trans (L := L) hAC' hAC0 hC2A'
    (segCong_symm (L := L) hAC0 hAC' hAC) hC2c
  have e2 : SegCong B' C' B' C2 := segCong_trans (L := L) hCB'.symm hCB0.symm hC2B'
    (segCong_symm (L := L) hCB0.symm hCB'.symm hBC) s1
  have hC'C2 : C' ≠ C2 := by
    obtain ⟨Y, -, hY⟩ := hopp.2.2; exact ne13_of_between hY
  obtain ⟨Y, hYl, hY⟩ := hopp.2.2
  have hC'm : C' ∈ line (Line := L) C' C2 hC'C2 := mem_line_left _
  have hC2m : C2 ∈ line (Line := L) C' C2 hC'C2 := mem_line_right _
  have hYm : Y ∈ line (Line := L) C' C2 hC'C2 := mem_mid_of_between hY hC'm hC2m
  have hlm : line (Line := L) A' B' hAB' ≠ line C' C2 hC'C2 := fun e => hC'l (by rw [e]; exact hC'm)
  -- `∠A'C'B' ≡ ∠A'C2B'`, from the isosceles triangles `A'C'C2`, `B'C'C2`
  have key2 : AngCong A' C' B' A' C2 B' := by
    by_cases hAm : A' ∈ line (Line := L) C' C2 hC'C2
    · have hYA : Y = A' := eq_of_mem_of_mem hlm hYl hYm hA'l hAm
      rw [hYA] at hY
      have hB'm : B' ∉ line (Line := L) C' C2 hC'C2 := fun hh =>
        hlm (line_unique hAB' hA'l hB'l hAm hh)
      have nB := nc_of hC'm hC2m hC'C2 hB'm
      have iso := base_angles (L := L) nB.2.2.1 (ne_of_mem_not_mem hC'm hB'm)
        (ne_of_mem_not_mem hC2m hB'm) e2
      have iso' : AngCong C2 C' B' C' C2 B' := angCong_swap_right nB.2.2.2.1 nB.2.2.2.2.2
        (angCong_swap_left nB.2.2.1 nB.2.2.2.2.2 iso)
      exact angCong_rays nB.2.2.2.1 nB.1 iso' (mem_ray_of_between hY)
        (mem_ray_self' (L := L) (ne_of_mem_not_mem hC'm hB'm))
        (mem_ray_of_between (between_symm hY)) (mem_ray_self' (L := L) (ne_of_mem_not_mem hC2m hB'm))
    · by_cases hBm : B' ∈ line (Line := L) C' C2 hC'C2
      · have hYB : Y = B' := eq_of_mem_of_mem hlm hYl hYm hB'l hBm
        rw [hYB] at hY
        have nA := nc_of hC'm hC2m hC'C2 hAm
        have iso := base_angles (L := L) nA.2.2.1 (ne_of_mem_not_mem hC'm hAm)
          (ne_of_mem_not_mem hC2m hAm) e1
        exact angCong_rays nA.2.2.1 nA.2.2.2.2.2 iso
          (mem_ray_self' (L := L) (ne_of_mem_not_mem hC'm hAm)) (mem_ray_of_between hY)
          (mem_ray_self' (L := L) (ne_of_mem_not_mem hC2m hAm)) (mem_ray_of_between (between_symm hY))
      · have nA := nc_of hC'm hC2m hC'C2 hAm
        have nB := nc_of hC'm hC2m hC'C2 hBm
        have isoA := base_angles (L := L) nA.2.2.1 (ne_of_mem_not_mem hC'm hAm)
          (ne_of_mem_not_mem hC2m hAm) e1
        have isoB := base_angles (L := L) nB.2.2.1 (ne_of_mem_not_mem hC'm hBm)
          (ne_of_mem_not_mem hC2m hBm) e2
        have em : line (Line := L) C2 C' hC'C2.symm = line C' C2 hC'C2 := line_comm hC'C2
        have hside : (SameSide (line (Line := L) C' C2 hC'C2) A' B' ∧
              SameSide (line (Line := L) C2 C' hC'C2.symm) A' B') ∨
            (OppositeSides (line (Line := L) C' C2 hC'C2) A' B' ∧
              OppositeSides (line (Line := L) C2 C' hC'C2.symm) A' B') := by
          rw [em]
          rcases sameSide_or_opp' hAm hBm with hs | hs
          · exact Or.inl ⟨hs, hs⟩
          · exact Or.inr ⟨hs, hs⟩
        exact F.angle_addition (O := C') (H := A') (K := B') (M := C2) (O' := C2) (H' := A')
          (K' := B') (M' := C') hS hS hC'S hA'S hB'S hC2S hC2S hA'S hB'S hC'S nA.2.2.1 nB.2.2.1
          (fun hh => h' hh.swap23) nA.2.2.2.2.2 nB.2.2.2.2.2 nC2.2.1 isoA isoB hC'C2.symm hC'C2
          hside
  obtain ⟨-, k, -⟩ := F.sas (A := C') (B := A') (C := B') (A' := C2) (B' := A') (C' := B')
    nC'.2.2.1 nC2.2.2.1 (segCong_swap e1) (segCong_swap e2) key2
  have k' : AngCong B' A' C' B' A' C2 := angCong_swap_right nC'.2.2.2.1 nC2.2.2.1
    (angCong_swap_left nC'.2.2.1 nC2.2.2.1 k)
  exact angCong_trans hBAC nC2.2.2.2.1 nC'.2.2.2.1 hc2 (angCong_symm nC'.2.2.2.1 nC2.2.2.2.1 k')

end Frame

end HilbertFoundations
