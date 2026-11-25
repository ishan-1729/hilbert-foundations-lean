import HilbertFoundations.DesarguesAlgebraAux3

/-!
# Helper for § 22 / § 30: Desargues's theorem in the planes of space; the first part from the second

Helper module of `DesarguesAlgebra.lean`.

* **Desargues's theorem in space** (`space_desargues`): in a space geometry satisfying I and III
  (`SpaceParallels`), the second part of Desargues's theorem holds for triangles of any plane `α`.
  The proof lifts the figure out of `α` through a point `S ∉ α` (which exists by I 7): two triangles
  `XYZ`, `X'Y'Z'` in distinct planes with `XY ∥ X'Y'`, `XZ ∥ X'Z'` lie in planes without a common
  point (`planes_disjoint`); for the case of parallel joins, two lines parallel to a third are
  parallel (`spar_trans`).
* **The first part from the second** (`desarguesI_of_II`): in a plane geometry satisfying I 1–2,
  III, the second part of Desargues's theorem implies the first.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace DesAlg

/-! ## Distinct vertices of a triangle -/

section Gen

variable {P : Type u} {L : Type v} [HasLines P L] [Connection P L]

theorem nc_ne12 {A B C : P} {l : L} (hn : ¬Collinear A B C) (hl : A ∈ l) : A ≠ B := by
  rintro rfl
  by_cases hAC : A = C
  · subst hAC; exact hn ⟨l, hl, hl, hl⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hAC; exact hn ⟨m, h1, h1, h2⟩

theorem nc_ne13 {A B C : P} {l : L} (hn : ¬Collinear A B C) (hl : A ∈ l) : A ≠ C := by
  rintro rfl
  by_cases hAB : A = B
  · subst hAB; exact hn ⟨l, hl, hl, hl⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hAB; exact hn ⟨m, h1, h2, h1⟩

theorem nc_ne23 {A B C : P} {l : L} (hn : ¬Collinear A B C) (hl : B ∈ l) : B ≠ C := by
  rintro rfl
  by_cases hAB : A = B
  · subst hAB; exact hn ⟨l, hl, hl, hl⟩
  · obtain ⟨m, h1, h2⟩ := exists_line (Line := L) hAB; exact hn ⟨m, h1, h2, h2⟩

end Gen

/-! ## Space -/

section Space

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
  [hS : SpaceParallels P L Pl]

/-- Two lines are **parallel in space**: they lie in a common plane and have no common point. -/
def SPar (P : Type u) {L : Type v} (Pl : Type w) [HasLines P L] [HasPlanes P Pl] (a b : L) :
    Prop :=
  (∃ σ : Pl, LiesInPlane (Point := P) a σ ∧ LiesInPlane (Point := P) b σ) ∧
    ¬Meets (Point := P) a b

theorem SPar.symm {a b : L} (h : SPar P Pl a b) : SPar P Pl b a :=
  ⟨let ⟨σ, h1, h2⟩ := h.1; ⟨σ, h2, h1⟩, fun ⟨X, h1, h2⟩ => h.2 ⟨X, h2, h1⟩⟩

/-- Axiom III in the plane `π` (uniqueness). -/
theorem iii_unique {π : Pl} {g a b : L} {X : P} (hg : LiesInPlane g π) (ha : LiesInPlane a π)
    (hb : LiesInPlane b π) (hX : X ∈ π) (hXg : X ∉ g) (hXa : X ∈ a) (hXb : X ∈ b)
    (hag : ¬Meets (Point := P) a g) (hbg : ¬Meets (Point := P) b g) : a = b :=
  (SpaceParallels.ax_III (Point := P) (Line := L) (Plane := Pl) π g X hg hX hXg).unique
    ⟨ha, hXa, hag⟩ ⟨hb, hXb, hbg⟩

/-- Axiom III in the plane `π` (existence). -/
theorem iii_exists {π : Pl} {g : L} {X : P} (hg : LiesInPlane g π) (hX : X ∈ π) (hXg : X ∉ g) :
    ∃ b : L, LiesInPlane b π ∧ X ∈ b ∧ ¬Meets (Point := P) b g :=
  (SpaceParallels.ax_III (Point := P) (Line := L) (Plane := Pl) π g X hg hX hXg).exists

/-- A line lying in two distinct planes is their common line. -/
theorem eq_of_lies_both {π π' : Pl} {g a : L} (hg : ∀ X : P, X ∈ g ↔ X ∈ π ∧ X ∈ π')
    (ha : LiesInPlane (Point := P) a π) (ha' : LiesInPlane (Point := P) a π') : a = g := by
  obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) a
  exact line_unique hXY hX hY ((hg X).2 ⟨ha X hX, ha' X hX⟩) ((hg Y).2 ⟨ha Y hY, ha' Y hY⟩)

/-- If two distinct planes meet in the line `g`, and parallel lines `a ⊆ π`, `a' ⊆ π'` are given,
then `g = a` or `g` does not meet `a`. -/
theorem lpp {π π' : Pl} {g a a' : L} (_hππ' : π ≠ π') (hg : ∀ X : P, X ∈ g ↔ X ∈ π ∧ X ∈ π')
    (ha : LiesInPlane (Point := P) a π) (ha' : LiesInPlane (Point := P) a' π')
    (hp : SPar P Pl a a') : g = a ∨ ¬Meets (Point := P) g a := by
  by_contra hc
  rw [not_or, not_not] at hc
  obtain ⟨hga, W, hWg, hWa⟩ := hc
  by_cases hap : LiesInPlane (Point := P) a π'
  · exact hga (eq_of_lies_both hg ha hap).symm
  · obtain ⟨σ, hσa, hσa'⟩ := hp.1
    have hσ : σ ≠ π' := fun e => hap (e ▸ hσa)
    obtain ⟨h, hh⟩ := planes_meet_in_line hσ (hσa W hWa) ((hg W).1 hWg).2
    have e : a' = h := eq_of_lies_both hh hσa' ha'
    have hWh := (hh W).2 ⟨hσa W hWa, ((hg W).1 hWg).2⟩
    exact hp.2 ⟨W, hWa, e ▸ hWh⟩

/-- **Planes through triangles with two pairs of parallel sides do not meet.** -/
theorem planes_disjoint {π π' : Pl} {X Y Z X' Y' Z' : P} (hπ : π ≠ π') (hn : ¬Collinear X Y Z)
    (hX : X ∈ π) (hY : Y ∈ π) (hZ : Z ∈ π) (hX' : X' ∈ π') (hY' : Y' ∈ π') (hZ' : Z' ∈ π')
    (hX'Y' : X' ≠ Y') (hX'Z' : X' ≠ Z') {xy x'y' xz x'z' : L} (h1 : X ∈ xy) (h2 : Y ∈ xy)
    (h3 : X' ∈ x'y') (h4 : Y' ∈ x'y') (h5 : X ∈ xz) (h6 : Z ∈ xz) (h7 : X' ∈ x'z')
    (h8 : Z' ∈ x'z') (p1 : SPar P Pl xy x'y') (p2 : SPar P Pl xz x'z') :
    ¬∃ W : P, W ∈ π ∧ W ∈ π' := by
  rintro ⟨W, hWπ, hWπ'⟩
  obtain ⟨g, hg⟩ := planes_meet_in_line hπ hWπ hWπ'
  have hXY : X ≠ Y := nc_ne12 hn h1
  have hXZ : X ≠ Z := nc_ne13 hn h1
  have lxy := liesInPlane_of_mem hXY h1 h2 hX hY
  have lxz := liesInPlane_of_mem hXZ h5 h6 hX hZ
  have lx'y' := liesInPlane_of_mem hX'Y' h3 h4 hX' hY'
  have lx'z' := liesInPlane_of_mem hX'Z' h7 h8 hX' hZ'
  have hne : xy ≠ xz := fun e => hn ⟨xy, h1, h2, e ▸ h6⟩
  have lg : LiesInPlane (Point := P) g π := fun V hV => ((hg V).1 hV).1
  rcases lpp hπ hg lxy lx'y' p1 with r1 | r1 <;> rcases lpp hπ hg lxz lx'z' p2 with r2 | r2
  · exact hne (r1.symm.trans r2)
  · exact r2 ⟨X, r1 ▸ h1, h5⟩
  · exact r1 ⟨X, r2 ▸ h5, h1⟩
  · have hXg : X ∉ g := fun h => r1 ⟨X, h, h1⟩
    exact hne (iii_unique lg lxy lxz hX hXg h1 h5 (fun ⟨V, a, b⟩ => r1 ⟨V, b, a⟩)
      (fun ⟨V, a, b⟩ => r2 ⟨V, b, a⟩))

/-- Two planes containing two distinct lines without common point are equal. -/
theorem plane_eq_of_two_lines {a b : L} {σ τ : Pl} (hn : ¬Meets (Point := P) a b)
    (hσa : LiesInPlane (Point := P) a σ) (hσb : LiesInPlane (Point := P) b σ)
    (hτa : LiesInPlane (Point := P) a τ) (hτb : LiesInPlane (Point := P) b τ) : σ = τ := by
  obtain ⟨X, Y, hXY, hX, hY⟩ := exists_two_points (Point := P) a
  obtain ⟨Z, -, -, hZ, -⟩ := exists_two_points (Point := P) b
  have hZa : Z ∉ a := fun h => hn ⟨Z, h, hZ⟩
  have hnc : ¬Collinear X Y Z := not_collinear_of_not_mem hX hY hXY hZa
  exact plane_unique hnc (hσa X hX) (hσa Y hY) (hσb Z hZ) (hτa X hX) (hτa Y hY) (hτb Z hZ)

/-- **Two lines parallel to a third are parallel** (in space). -/
theorem spar_trans {a b c : L} (hab : SPar P Pl a b) (hac : SPar P Pl a c) (hbc : b ≠ c) :
    SPar P Pl b c := by
  obtain ⟨σ, hσa, hσb⟩ := hab.1
  obtain ⟨τ, hτa, hτc⟩ := hac.1
  by_cases hστ : σ = τ
  · subst hστ
    refine ⟨⟨σ, hσb, hτc⟩, fun ⟨W, hWb, hWc⟩ => hbc ?_⟩
    have hWa : W ∉ a := fun h => hab.2 ⟨W, h, hWb⟩
    exact iii_unique hσa hσb hτc (hσb W hWb) hWa hWb hWc
      (fun ⟨V, h1, h2⟩ => hab.2 ⟨V, h2, h1⟩) (fun ⟨V, h1, h2⟩ => hac.2 ⟨V, h2, h1⟩)
  · obtain ⟨C, -, -, hC, -⟩ := exists_two_points (Point := P) c
    have hCa : C ∉ a := fun h => hac.2 ⟨C, h, hC⟩
    have hCb : C ∉ b := by
      intro h
      obtain ⟨g, hg⟩ := planes_meet_in_line hστ (hσb C h) (hτc C hC)
      have e := eq_of_lies_both hg hσa hτa
      exact hCa (e ▸ (hg C).2 ⟨hσb C h, hτc C hC⟩)
    obtain ⟨ρ, hρb, hρC⟩ := exists_plane_line_point (Pl := Pl) hCb
    have hρτ : ρ ≠ τ := by
      intro e; subst e
      exact hστ (plane_eq_of_two_lines hab.2 hσa hσb hτa hρb)
    obtain ⟨c', hc'⟩ := planes_meet_in_line hρτ hρC (hτc C hC)
    rcases lpp hρτ hc' hρb hτa hab.symm with r1 | r1
    · exfalso
      have : LiesInPlane (Point := P) b τ := fun V hV => ((hc' V).1 (r1 ▸ hV)).2
      exact hστ (plane_eq_of_two_lines hab.2 hσa hσb hτa this)
    · have hg' : ∀ X : P, X ∈ c' ↔ X ∈ τ ∧ X ∈ ρ := fun X => by rw [hc' X, and_comm]
      rcases lpp (Ne.symm hρτ) hg' hτa hρb hab with r2 | r2
      · exact absurd (r2 ▸ (hc' C).2 ⟨hρC, hτc C hC⟩) hCa
      · have lc' : LiesInPlane (Point := P) c' τ := fun V hV => ((hc' V).1 hV).2
        have e : c' = c := iii_unique hτa lc' hτc (hτc C hC) hCa ((hc' C).2 ⟨hρC, hτc C hC⟩) hC
          (fun ⟨V, h1, h2⟩ => r2 ⟨V, h1, h2⟩) (fun ⟨V, h1, h2⟩ => hac.2 ⟨V, h2, h1⟩)
        refine ⟨⟨ρ, hρb, fun V hV => ((hc' V).1 (e ▸ hV)).1⟩, fun ⟨W, hWb, hWc⟩ => r1 ⟨W, e ▸ hWc, hWb⟩⟩

/-- The plane through three non-collinear points. -/
theorem exists_plane3 {A B C : P} (h : ¬Collinear A B C) : ∃ π : Pl, A ∈ π ∧ B ∈ π ∧ C ∈ π :=
  exists_plane h

include hS in
theorem exists_point_off (α : Pl) : ∃ S : P, S ∉ α := by
  obtain ⟨A, B, C, D, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  by_contra hall
  simp only [not_exists, not_not] at hall
  exact h ⟨α, hall A, hall B, hall C, hall D⟩


/-- The core of the spatial proof of Desargues's theorem: lifting through `S ∉ α` and `S' ∉ α`. -/
theorem desargues_core {α : Pl} {A B C A' B' C' S S' : P} (hA : A ∈ α) (hB : B ∈ α)
    (hC : C ∈ α) (hA' : A' ∈ α) (hB' : B' ∈ α) (hC' : C' ∈ α) (hS : S ∉ α) (hS' : S' ∉ α)
    (hn : ¬Collinear A B C) (hn' : ¬Collinear A' B' C') (hBCB' : ¬Collinear B C B')
    {ab a'b' ac a'c' as a's' : L} (k1 : A ∈ ab) (k2 : B ∈ ab) (k3 : A' ∈ a'b') (k4 : B' ∈ a'b')
    (k5 : A ∈ ac) (k6 : C ∈ ac) (k7 : A' ∈ a'c') (k8 : C' ∈ a'c') (k9 : A ∈ as) (k10 : S ∈ as)
    (k11 : A' ∈ a's') (k12 : S' ∈ a's') (pab : ¬Meets (Point := P) ab a'b')
    (pac : ¬Meets (Point := P) ac a'c') (pas : SPar P Pl as a's')
    (copB : ∃ σ : Pl, B ∈ σ ∧ B' ∈ σ ∧ S ∈ σ ∧ S' ∈ σ)
    (copC : ∃ σ : Pl, C ∈ σ ∧ C' ∈ σ ∧ S ∈ σ ∧ S' ∈ σ) :
    ∃ bc b'c' : L, B ∈ bc ∧ C ∈ bc ∧ B' ∈ b'c' ∧ C' ∈ b'c' ∧ ¬Meets (Point := P) bc b'c' := by
  have ne_off : ∀ X : P, X ∈ α → ∀ Y : P, Y ∉ α → X ≠ Y := fun X hX Y hY e => hY (e ▸ hX)
  have ncS : ∀ X Y : P, X ∈ α → Y ∈ α → X ≠ Y → ∀ T : P, T ∉ α → ¬Collinear X Y T := by
    intro X Y hX hY hXY T hT hc
    obtain ⟨m, h1, h2, h3⟩ := hc
    exact hT (liesInPlane_of_mem hXY h1 h2 hX hY T h3)
  have hAB := nc_ne12 hn k1
  have hAC := nc_ne13 hn k1
  have hBC := nc_ne23 hn k2
  have hA'B' := nc_ne12 hn' k3
  have hA'C' := nc_ne13 hn' k3
  have hB'C' := nc_ne23 hn' k4
  have hSB : S ≠ B := (ne_off B hB S hS).symm
  have hS'B' : S' ≠ B' := (ne_off B' hB' S' hS').symm
  have hS'C' : S' ≠ C' := (ne_off C' hC' S' hS').symm
  have hSC : S ≠ C := (ne_off C hC S hS).symm
  have lab : LiesInPlane (Point := P) ab α := liesInPlane_of_mem hAB k1 k2 hA hB
  have la'b' : LiesInPlane (Point := P) a'b' α := liesInPlane_of_mem hA'B' k3 k4 hA' hB'
  have lac : LiesInPlane (Point := P) ac α := liesInPlane_of_mem hAC k5 k6 hA hC
  have la'c' : LiesInPlane (Point := P) a'c' α := liesInPlane_of_mem hA'C' k7 k8 hA' hC'
  -- the planes through the lifted triangles
  have claim : ∀ (X X' : P) (ax a'x' : L) (hX : X ∈ α) (hX' : X' ∈ α), X ≠ A → X' ≠ A' →
      (∃ σ : Pl, X ∈ σ ∧ X' ∈ σ ∧ S ∈ σ ∧ S' ∈ σ) → A ∈ ax → X ∈ ax → A' ∈ a'x' →
      X' ∈ a'x' → ¬Meets (Point := P) ax a'x' → A' ∉ ax →
      SPar P Pl (line X S (ne_off X hX S hS) : L) (line X' S' (ne_off X' hX' S' hS')) := by
    intro X X' ax a'x' hX hX' hXA hX'A' hcop m1 m2 m3 m4 hm hA'n
    obtain ⟨π, hπA, hπX, hπS⟩ := exists_plane3 (Pl := Pl) (ncS A X hA hX hXA.symm S hS)
    obtain ⟨π', hπA', hπX', hπS'⟩ := exists_plane3 (Pl := Pl) (ncS A' X' hA' hX' hX'A'.symm S' hS')
    have hππ' : π ≠ π' := by
      intro e; subst e
      have hnc : ¬Collinear A X A' := fun h => hA'n (mem_of_collinear h hXA.symm m1 m2)
      have := plane_unique hnc hA hX hA' hπA hπX hπA'
      exact hS (this ▸ hπS)
    have dis := planes_disjoint (X := A) (Y := X) (Z := S) hππ' (ncS A X hA hX hXA.symm S hS)
      hπA hπX hπS hπA' hπX' hπS' hX'A'.symm (ne_off A' hA' S' hS') m1 m2 m3 m4 k9 k10 k11 k12
      ⟨⟨α, liesInPlane_of_mem hXA.symm m1 m2 hA hX, liesInPlane_of_mem hX'A'.symm m3 m4 hA' hX'⟩,
        hm⟩ pas
    obtain ⟨σ, hσX, hσX', hσS, hσS'⟩ := hcop
    refine ⟨⟨σ, liesInPlane_of_mem (ne_off X hX S hS) ((mem_line_left _)) ((mem_line_right _))
      hσX hσS, liesInPlane_of_mem (ne_off X' hX' S' hS') ((mem_line_left _))
      ((mem_line_right _)) hσX' hσS'⟩, ?_⟩
    rintro ⟨W, hW1, hW2⟩
    refine dis ⟨W, liesInPlane_of_mem (ne_off X hX S hS) ((mem_line_left _))
      ((mem_line_right _)) hπX hπS W hW1, liesInPlane_of_mem (ne_off X' hX' S' hS')
      ((mem_line_left _)) ((mem_line_right _)) hπX' hπS' W hW2⟩
  have hA'ab : A' ∉ ab := fun h => pab ⟨A', h, k3⟩
  have hA'ac : A' ∉ ac := fun h => pac ⟨A', h, k7⟩
  have c1 := claim B B' ab a'b' hB hB' hAB.symm hA'B'.symm copB k1 k2 k3 k4 pab hA'ab
  have c2 := claim C C' ac a'c' hC hC' hAC.symm hA'C'.symm copC k5 k6 k7 k8 pac hA'ac
  -- the planes `SBC`, `S'B'C'`
  have hnSBC : ¬Collinear S B C := fun h => ncS B C hB hC hBC S hS h.perm231
  have hnSBC' : ¬Collinear S' B' C' := fun h => ncS B' C' hB' hC' hB'C' S' hS' h.perm231
  obtain ⟨π, hπS, hπB, hπC⟩ := exists_plane3 (Pl := Pl) hnSBC
  obtain ⟨π', hπS', hπB', hπC'⟩ := exists_plane3 (Pl := Pl) hnSBC'
  have hππ' : π ≠ π' := by
    intro e; subst e
    have := plane_unique hBCB' hB hC hB' hπB hπC hπB'
    exact hS (this ▸ hπS)
  have dis := planes_disjoint (X := S) (Y := B) (Z := C) hππ' hnSBC hπS hπB hπC hπS' hπB' hπC'
    hS'B' hS'C' ((mem_line_right _)) ((mem_line_left _)) ((mem_line_right _))
    ((mem_line_left _)) ((mem_line_right _)) ((mem_line_left _)) ((mem_line_right _))
    ((mem_line_left _)) c1 c2
  refine ⟨line B C hBC, line B' C' hB'C', (mem_line_left _), (mem_line_right _),
    (mem_line_left _), (mem_line_right _), ?_⟩
  rintro ⟨W, hW1, hW2⟩
  exact dis ⟨W, liesInPlane_of_mem hBC ((mem_line_left _)) ((mem_line_right _)) hπB hπC W hW1,
    liesInPlane_of_mem hB'C' ((mem_line_left _)) ((mem_line_right _)) hπB' hπC' W hW2⟩

/-- **Desargues's theorem (second part) in a plane of space** (I, III). -/
theorem space_desargues (α : Pl) {A B C A' B' C' : P} {a b c : L} (hA : A ∈ α) (hB : B ∈ α)
    (hC : C ∈ α) (hA' : A' ∈ α) (hB' : B' ∈ α) (hC' : C' ∈ α)
    (hn : ¬Collinear A B C) (hn' : ¬Collinear A' B' C')
    (hAa : A ∈ a) (hA'a : A' ∈ a) (hBb : B ∈ b) (hB'b : B' ∈ b) (hCc : C ∈ c) (hC'c : C' ∈ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcp : ConcurrentOrParallel P a b c)
    (h1 : ∃ ab a'b' : L, A ∈ ab ∧ B ∈ ab ∧ A' ∈ a'b' ∧ B' ∈ a'b' ∧ ¬Meets (Point := P) ab a'b')
    (h2 : ∃ ac a'c' : L, A ∈ ac ∧ C ∈ ac ∧ A' ∈ a'c' ∧ C' ∈ a'c' ∧ ¬Meets (Point := P) ac a'c') :
    ∃ bc b'c' : L, B ∈ bc ∧ C ∈ bc ∧ B' ∈ b'c' ∧ C' ∈ b'c' ∧ ¬Meets (Point := P) bc b'c' := by
  obtain ⟨ab, a'b', k1, k2, k3, k4, pab⟩ := h1
  obtain ⟨ac, a'c', k5, k6, k7, k8, pac⟩ := h2
  have hAA' : A ≠ A' := fun e => pab ⟨A, k1, e ▸ k3⟩
  have hBB' : B ≠ B' := fun e => pab ⟨B, k2, e ▸ k4⟩
  have hCC' : C ≠ C' := fun e => pac ⟨C, k6, e ▸ k8⟩
  have hAB := nc_ne12 hn k1
  have hAC := nc_ne13 hn k1
  have la : LiesInPlane (Point := P) a α := liesInPlane_of_mem hAA' hAa hA'a hA hA'
  have lb : LiesInPlane (Point := P) b α := liesInPlane_of_mem hBB' hBb hB'b hB hB'
  have lc : LiesInPlane (Point := P) c α := liesInPlane_of_mem hCC' hCc hC'c hC hC'
  obtain ⟨S, hS⟩ := exists_point_off (P := P) (L := L) α
  have ne_off : ∀ X : P, X ∈ α → ∀ Y : P, Y ∉ α → X ≠ Y := fun X hX Y hY e => hY (e ▸ hX)
  have ncS : ∀ X Y : P, X ∈ α → Y ∈ α → X ≠ Y → ∀ T : P, T ∉ α → ¬Collinear X Y T := by
    intro X Y hX hY hXY T hT hc
    obtain ⟨m, h1, h2, h3⟩ := hc
    exact hT (liesInPlane_of_mem hXY h1 h2 hX hY T h3)
  have hAS := ne_off A hA S hS
  have hA'sa : A' ∉ (line A S hAS : L) := by
    intro h
    have e : (line A S hAS : L) = a :=
      line_unique hAA' ((mem_line_left _)) h hAa hA'a
    exact hS (la S (e ▸ (mem_line_right _)))
  have hBCB'_of : ∀ (hCb : C ∉ b), ¬Collinear B C B' := by
    intro hCb h
    obtain ⟨m, m1, m2, m3⟩ := h
    have e : m = b := line_unique hBB' m1 m3 hBb hB'b
    exact hCb (e ▸ m2)
  rcases hcp with ⟨O, hOa, hOb, hOc⟩ | ⟨pab', pac', pbc'⟩
  · -- concurrent joins
    have hO : O ∈ α := la O hOa
    have hOA : O ≠ A := by
      rintro rfl
      have e : ab = b := line_unique hAB k1 k2 hOb hBb
      exact pab ⟨B', e ▸ hB'b, k4⟩
    have hOA' : O ≠ A' := by
      rintro rfl
      have e : a'b' = b := line_unique (nc_ne12 hn' k3) k3 k4 hOb hB'b
      exact pab ⟨B, k2, e ▸ hBb⟩
    have hOB : O ≠ B := by
      rintro rfl
      have e : ab = a := line_unique hAB k1 k2 hAa hOa
      exact pab ⟨A', e ▸ hA'a, k3⟩
    have hOC : O ≠ C := by
      rintro rfl
      have e : ac = a := line_unique hAC k5 k6 hAa hOa
      exact pac ⟨A', e ▸ hA'a, k7⟩
    obtain ⟨π0, hπO, hπA, hπS⟩ := exists_plane3 (Pl := Pl) (ncS O A hO hA hOA S hS)
    have hOS := ne_off O hO S hS
    set s : L := line O S hOS
    set sa : L := line A S hAS
    have la0 : LiesInPlane (Point := P) a π0 := liesInPlane_of_mem hOA hOa hAa hπO hπA
    have ls0 : LiesInPlane (Point := P) s π0 :=
      liesInPlane_of_mem hOS ((mem_line_left _)) ((mem_line_right _)) hπO hπS
    have lsa0 : LiesInPlane (Point := P) sa π0 :=
      liesInPlane_of_mem hAS ((mem_line_left _)) ((mem_line_right _)) hπA hπS
    obtain ⟨k, lk, hA'k, hk⟩ := iii_exists lsa0 (la0 A' hA'a) hA'sa
    have hSk : S ∉ k := fun h => hk ⟨S, h, (mem_line_right _)⟩
    have hmeet : ∃ W : P, W ∈ s ∧ W ∈ k := by
      by_contra hc
      have e : s = sa := iii_unique lk ls0 lsa0 hπS hSk ((mem_line_right _))
        ((mem_line_right _)) (fun ⟨V, h1, h2⟩ => hc ⟨V, h1, h2⟩)
        (fun ⟨V, h1, h2⟩ => hk ⟨V, h2, h1⟩)
      have hAs : A ∈ s := e ▸ (mem_line_left hAS)
      have e2 : s = a := line_unique hOA ((mem_line_left _)) hAs hOa hAa
      exact hS (la S (e2 ▸ (mem_line_right hOS)))
    obtain ⟨S', hS's, hS'k⟩ := hmeet
    have hS'α : S' ∉ α := by
      intro h
      by_cases hS'O : S' = O
      · rw [hS'O] at hS'k
        have e : k = a := line_unique hOA' hS'k hA'k hOa hA'a
        exact hk ⟨A, e ▸ hAa, (mem_line_left _)⟩
      · have := liesInPlane_of_mem (Ne.symm hS'O) ((mem_line_left hOS)) hS's hO h
        exact hS (this S ((mem_line_right _)))
    have pas : SPar P Pl sa k := ⟨⟨π0, lsa0, lk⟩, fun ⟨W, h1, h2⟩ => hk ⟨W, h2, h1⟩⟩
    have cop : ∀ X X' : P, X ∈ α → X ≠ O → ∀ x : L, O ∈ x → X ∈ x → X' ∈ x →
        ∃ σ : Pl, X ∈ σ ∧ X' ∈ σ ∧ S ∈ σ ∧ S' ∈ σ := by
      intro X X' hX hXO x h1 h2 h3
      obtain ⟨σ, hσO, hσX, hσS⟩ := exists_plane3 (Pl := Pl) (ncS O X hO hX hXO.symm S hS)
      exact ⟨σ, hσX, liesInPlane_of_mem hXO.symm h1 h2 hσO hσX X' h3, hσS,
        liesInPlane_of_mem hOS ((mem_line_left _)) ((mem_line_right _)) hσO hσS S' hS's⟩
    have hCb : C ∉ b := fun h => hOC (eq_of_mem_of_mem hbc hOb hOc h hCc)
    exact desargues_core hA hB hC hA' hB' hC' hS hS'α hn hn' (hBCB'_of hCb) k1 k2 k3 k4 k5 k6
      k7 k8 ((mem_line_left _)) ((mem_line_right _)) hA'k hS'k pab pac pas
      (cop B B' hB hOB.symm b hOb hBb hB'b) (cop C C' hC hOC.symm c hOc hCc hC'c)
  · -- parallel joins
    obtain ⟨π0, hπA, hπA', hπS⟩ := exists_plane3 (Pl := Pl) (ncS A A' hA hA' hAA' S hS)
    set sa : L := line A S hAS
    have la0 : LiesInPlane (Point := P) a π0 := liesInPlane_of_mem hAA' hAa hA'a hπA hπA'
    have lsa0 : LiesInPlane (Point := P) sa π0 :=
      liesInPlane_of_mem hAS ((mem_line_left _)) ((mem_line_right _)) hπA hπS
    have hSa : S ∉ a := fun h => hS (la S h)
    obtain ⟨k1', lk1, hSk1, hk1⟩ := iii_exists la0 hπS hSa
    obtain ⟨k2', lk2, hA'k2, hk2⟩ := iii_exists lsa0 hπA' hA'sa
    have hSk2 : S ∉ k2' := fun h => hk2 ⟨S, h, (mem_line_right _)⟩
    have hmeet : ∃ W : P, W ∈ k1' ∧ W ∈ k2' := by
      by_contra hc
      have e : k1' = sa := iii_unique lk2 lk1 lsa0 hπS hSk2 hSk1 ((mem_line_right _))
        (fun ⟨V, h1, h2⟩ => hc ⟨V, h1, h2⟩) (fun ⟨V, h1, h2⟩ => hk2 ⟨V, h2, h1⟩)
      exact hk1 ⟨A, e ▸ (mem_line_left hAS), hAa⟩
    obtain ⟨S', hS'1, hS'2⟩ := hmeet
    have hπα : π0 ≠ α := fun e => hS (e ▸ hπS)
    have hS'α : S' ∉ α := by
      intro h
      obtain ⟨g, hg⟩ := planes_meet_in_line hπα hπA hA
      have e : a = g := eq_of_lies_both hg la0 la
      exact hk1 ⟨S', hS'1, e ▸ (hg S').2 ⟨lk1 S' hS'1, h⟩⟩
    have pas : SPar P Pl sa k2' := ⟨⟨π0, lsa0, lk2⟩, fun ⟨W, h1, h2⟩ => hk2 ⟨W, h2, h1⟩⟩
    have pak : SPar P Pl a k1' := ⟨⟨π0, la0, lk1⟩, fun ⟨W, h1, h2⟩ => hk1 ⟨W, h2, h1⟩⟩
    have cop : ∀ (X X' : P) (x : L), LiesInPlane (Point := P) x α → ¬Meets (Point := P) a x →
        a ≠ x → X ∈ x → X' ∈ x → ∃ σ : Pl, X ∈ σ ∧ X' ∈ σ ∧ S ∈ σ ∧ S' ∈ σ := by
      intro X X' x lx hax _ h1 h2
      have hxk : x ≠ k1' := fun e => hS (lx S (e ▸ hSk1))
      obtain ⟨⟨σ, hσx, hσk⟩, -⟩ := spar_trans ⟨⟨α, la, lx⟩, hax⟩ pak hxk
      exact ⟨σ, hσx X h1, hσx X' h2, hσk S hSk1, hσk S' hS'1⟩
    have hCb : C ∉ b := fun h => pbc' ⟨C, h, hCc⟩
    exact desargues_core hA hB hC hA' hB' hC' hS hS'α hn hn' (hBCB'_of hCb) k1 k2 k3 k4 k5 k6
      k7 k8 ((mem_line_left _)) ((mem_line_right _)) hA'k2 hS'2 pab pac pas
      (cop B B' b lb pab' hab hBb hB'b) (cop C C' c lc pac' hac hCc hC'c)

end Space

/-! ## The first part of Desargues's theorem from the second -/

section FirstPart

variable {P : Type u} {L : Type v} [HasLines P L] [PlaneParallels P L] [Nonempty L]

/-- **The first part of Desargues's theorem follows from the second** (in a plane geometry with
I 1–2 and III). -/
theorem desarguesI_of_II (hD : DesarguesII P) : DesarguesI P := by
  intro A B C A' B' C' hn hn' h1 h2 h3
  have hAA' := ne_of_parPts h1
  have hBB' := ne_of_parPts' h1
  have hCC' := ne_of_parPts' h2
  obtain ⟨l1, l1', m1, m2, m3, m4, p1⟩ := h1
  obtain ⟨l2, l2', n1, n2, n3, n4, p2⟩ := h2
  obtain ⟨l3, l3', o1, o2, o3, o4, p3⟩ := h3
  have hAB := nc_ne12 hn m1
  have hAC := nc_ne13 hn m1
  have hBC := nc_ne23 hn m2
  have hA'B' := nc_ne12 hn' m3
  have hA'C' := nc_ne13 hn' m3
  have hB'C' := nc_ne23 hn' m4
  -- the sides as lines
  have e1 : l1 = ln A B := (ln_eq hAB m1 m2).symm
  have e1' : l1' = ln A' B' := (ln_eq hA'B' m3 m4).symm
  have e2 : l2 = ln A C := (ln_eq hAC n1 n2).symm
  have e2' : l2' = ln A' C' := (ln_eq hA'C' n3 n4).symm
  have e3 : l3 = ln B C := (ln_eq hBC o1 o2).symm
  have e3' : l3' = ln B' C' := (ln_eq hB'C' o3 o4).symm
  subst e1 e1' e2 e2' e3 e3'
  have hA'l1 : A' ∉ (ln A B : L) := fun h => p1 ⟨A', h, m3⟩
  have hB'l1 : B' ∉ (ln A B : L) := fun h => p1 ⟨B', h, m4⟩
  have hBl1' : B ∉ (ln A' B' : L) := fun h => p1 ⟨B, m2, h⟩
  have hA'l2 : A' ∉ (ln A C : L) := fun h => p2 ⟨A', h, n3⟩
  have hB'l3 : B' ∉ (ln B C : L) := fun h => p3 ⟨B', h, o3⟩
  have par2 : LPar P (ln A' C' : L) (ln A C) := lpar_of_not_meets fun ⟨X, h, h'⟩ => p2 ⟨X, h', h⟩
  have par3 : LPar P (ln B' C' : L) (ln B C) := lpar_of_not_meets fun ⟨X, h, h'⟩ => p3 ⟨X, h', h⟩
  have nl23 : ¬LPar P (ln A C : L) (ln B C) := not_lpar_of (mem_ln_right A C) (mem_ln_right B C)
    fun e => hn ((collinear_iff_mem_ln hAC).2 (e ▸ mem_ln_left B C) |>.swap23)
  -- the sides `A'C'` and `B'C'` are not parallel
  have nl23' : ¬LPar P (ln A' C' : L) (ln B' C') := fun h =>
    nl23 ((par2.symm.trans h).trans par3)
  set a : L := ln A A'
  set b : L := ln B B'
  have hBa : B ∉ a := fun h => hA'l1 (by
    rw [ln_eq hAB (mem_ln_left A A') h]; exact mem_ln_right A A')
  have hCa : C ∉ a := fun h => hA'l2 (by
    rw [ln_eq hAC (mem_ln_left A A') h]; exact mem_ln_right A A')
  have hCb : C ∉ b := fun h => hB'l3 (by
    rw [ln_eq hBC (mem_ln_left B B') h]; exact mem_ln_right B B')
  have hab : a ≠ b := fun e => hBa (e ▸ mem_ln_left B B')
  -- the common step: a point `C''` of `A'C'` on a line `c` through `C` with `BC ∥ B'C''` is `C'`
  have step : ∀ (c : L) (C'' : P), C ∈ c → C'' ∈ c → C'' ∈ (ln A' C' : L) → a ≠ c → b ≠ c →
      C'' ≠ A' → ConcurrentOrParallel P a b c → C'' = C' := by
    intro c C'' hCc hC''c hC''l hac hbc hC''A' hcp
    have hn'' : ¬Collinear A' B' C'' := by
      intro h
      have k : C'' ∈ (ln A' B' : L) := (collinear_iff_mem_ln hA'B').1 h
      have e : (ln A' B' : L) = ln A' C' :=
        (ln_eq hC''A'.symm (mem_ln_left A' B') k).symm.trans (ln_eq hC''A'.symm (mem_ln_left A' C') hC''l)
      exact hn' ((collinear_iff_mem_ln hA'B').2 (e ▸ mem_ln_right A' C'))
    have q1 : ParPts A B A' B' := ⟨_, _, mem_ln_left A B, mem_ln_right A B, m3, m4, p1⟩
    have q2 : ParPts A C A' C'' := ⟨ln A C, ln A' C', mem_ln_left A C, mem_ln_right A C,
      mem_ln_left A' C', hC''l, p2⟩
    have r := hD A B C A' B' C'' a b c hn hn'' (mem_ln_left A A') (mem_ln_right A A')
      (mem_ln_left B B') (mem_ln_right B B') hCc hC''c hab hac hbc hcp q1 q2
    have k1 : C'' ∈ pline (ln B C : L) B' := mem_pline_of_parPts r hBC
    have k2 : C' ∈ pline (ln B C : L) B' := by
      rw [← eq_pline (mem_ln_left B' C') par3]; exact mem_ln_right B' C'
    have k3 : (ln B' C' : L) = pline (ln B C) B' := eq_pline (mem_ln_left B' C') par3
    rw [← k3] at k1 k2
    exact eq_of_mem_not_lpar nl23' hC''l k1 (mem_ln_right A' C') k2
  by_cases hpab : LPar P a b
  · -- parallel joins
    set c : L := pline a C
    have nlc : ¬LPar P c (ln A' C') := fun h => by
      have h' : LPar P a (ln A C) := ((pline_lpar a C).symm.trans h).trans par2
      exact (not_lpar_of (mem_ln_left A A') (mem_ln_left A C) fun e => hCa
        (by have k := mem_ln_right (L := L) A C; rw [← e] at k; exact k)) h'
    set C'' : P := meet c (ln A' C' : L)
    have hC''c : C'' ∈ c := meet_mem_left nlc
    have hC''l : C'' ∈ (ln A' C' : L) := meet_mem_right nlc
    have hac : a ≠ c := fun e => hCa (by rw [e]; exact mem_pline a C)
    have hbc : b ≠ c := fun e => hCb (by rw [e]; exact mem_pline a C)
    have pc : LPar P c a := pline_lpar a C
    have hC''A' : C'' ≠ A' := fun e => hac (by
      rw [e] at hC''c
      exact (eq_pline (mem_ln_right A A') (lpar_refl a)).trans
        (pline_eq_of_mem hC''c) |>.trans (by rfl))
    have hcp : ConcurrentOrParallel P a b c := Or.inr
      ⟨not_meets_of_lpar hpab hab, not_meets_of_lpar pc.symm hac,
        not_meets_of_lpar (hpab.symm.trans pc.symm) hbc⟩
    have e := step c C'' (mem_pline a C) hC''c hC''l hac hbc hC''A' hcp
    rw [e] at hC''c
    have ec : (ln C C' : L) = c := ln_eq hCC' (mem_pline a C) hC''c
    refine Or.inr ⟨⟨a, b, mem_ln_left _ _, mem_ln_right _ _, mem_ln_left _ _, mem_ln_right _ _,
      not_meets_of_lpar hpab hab⟩, ⟨a, c, mem_ln_left _ _, mem_ln_right _ _, mem_pline a C,
      hC''c, not_meets_of_lpar pc.symm hac⟩, ⟨b, c, mem_ln_left _ _, mem_ln_right _ _,
      mem_pline a C, hC''c, not_meets_of_lpar (hpab.symm.trans pc.symm) hbc⟩⟩
  · -- concurrent joins
    set O : P := meet a b
    have hOa : O ∈ a := meet_mem_left hpab
    have hOb : O ∈ b := meet_mem_right hpab
    have hOA : O ≠ A := fun e => hB'l1 (by
      rw [e] at hOb
      rw [ln_eq hAB hOb (mem_ln_left B B')]; exact mem_ln_right B B')
    have hOA' : O ≠ A' := fun e => hBl1' (by
      rw [e] at hOb
      rw [ln_eq hA'B' hOb (mem_ln_right B B')]; exact mem_ln_left B B')
    have hOC : O ≠ C := fun e => hCa (e ▸ hOa)
    set c : L := ln O C
    have nl0 : ¬LPar P c (ln A C) := by
      refine not_lpar_of (mem_ln_right O C) (mem_ln_right A C) fun e => hOA ?_
      have hOl : O ∈ (ln A C : L) := e ▸ mem_ln_left O C
      have hne : a ≠ ln A C := fun e' => hA'l2 (e' ▸ mem_ln_right A A')
      exact eq_of_mem_of_mem hne hOa hOl (mem_ln_left A A') (mem_ln_left A C)
    have nlc : ¬LPar P c (ln A' C') := fun h => nl0 (h.trans par2)
    set C'' : P := meet c (ln A' C' : L)
    have hC''c : C'' ∈ c := meet_mem_left nlc
    have hC''l : C'' ∈ (ln A' C' : L) := meet_mem_right nlc
    have hac : a ≠ c := fun e => hCa (by rw [e]; exact mem_ln_right O C)
    have hbc : b ≠ c := fun e => hCb (by rw [e]; exact mem_ln_right O C)
    have hC''A' : C'' ≠ A' := fun e => by
      rw [e] at hC''c
      exact hac (line_unique hOA' hOa (mem_ln_right A A') (mem_ln_left O C) hC''c)
    have e := step c C'' (mem_ln_right O C) hC''c hC''l hac hbc hC''A'
      (Or.inl ⟨O, hOa, hOb, mem_ln_left O C⟩)
    rw [e] at hC''c
    exact Or.inl ⟨O, ⟨a, mem_ln_left _ _, mem_ln_right _ _, hOa⟩,
      ⟨b, mem_ln_left _ _, mem_ln_right _ _, hOb⟩, ⟨c, mem_ln_right O C, hC''c, mem_ln_left O C⟩⟩

end FirstPart

end DesAlg

end HilbertFoundations
