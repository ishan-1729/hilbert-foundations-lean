import HilbertFoundations.Basic

/-!
# Helper module for `Order.lean`: plane order without axiom II 4

This module contains no unit of Hilbert's text; its results are stated as units in `Order.lean`.

It develops the plane theory of order from the axioms of connection of plane geometry
(`PlaneConnection`), the presupposition `BetweenOnLine` and the axioms II 1, II 2, II 3 and II 5,
**without** axiom II 4. These hypotheses are bundled in the class `PlaneOrderCore` (a bundle of
axioms of Basic.lean, not a new axiom); every `PlaneOrder` is a `PlaneOrderCore`.

* Elementary consequences of II 1–3 (namespace `OrderCore`).
* Pasch's axiom and the fact that a line cannot meet all three sides of a triangle (`pasch_excl`).
* The plane separation properties of the relations `SameSide a` / `OppositeSides a` of Basic.lean
  (`sameSide_trans`, `opp_of_sameSide_opp`, `sameSide_of_opp_opp`), first for non-collinear
  points by Pasch's axiom and then for collinear points with an auxiliary point off their line.
* The two four-point lemmas `between_of_between_between₁/₂` (E. H. Moore), from which axiom II 4
  follows (`axiomII4_core`).
-/

namespace HilbertFoundations

universe u v w

/-- **Plane order without II 4**: the axioms of connection of plane geometry, the presupposition
`BetweenOnLine` and the axioms II 1, II 2, II 3, II 5 (Pasch). A bundle of axioms of Basic.lean
used to prove that II 4 is a consequence of the others. -/
class PlaneOrderCore (Point : Type u) (Line : Type v) [HasLines Point Line] [HasBetween Point] :
    Prop extends PlaneConnection Point Line where
  between_onLine : BetweenOnLine Point
  ax_II1 : AxiomII1 Point
  ax_II2 : AxiomII2 Point
  ax_II3 : AxiomII3 Point
  ax_II5 : AxiomII5 Point

instance (priority := 100) PlaneOrder.toPlaneOrderCore {Point : Type u} {Line : Type v}
    [HasLines Point Line] [HasBetween Point] [h : PlaneOrder Point Line] :
    PlaneOrderCore Point Line where
  between_onLine := h.between_onLine
  ax_II1 := h.ax_II1
  ax_II2 := h.ax_II2
  ax_II3 := h.ax_II3
  ax_II5 := h.ax_II5

/-! ### Incidence lemmas (group I only) -/

section Incidence

variable {P : Type u} {L : Type v} [HasLines P L]

/-- Three points of one line are collinear. -/
theorem collinear_of_mem {A B C : P} {a : L} (hA : A ∈ a) (hB : B ∈ a) (hC : C ∈ a) :
    Collinear A B C := ⟨a, hA, hB, hC⟩

theorem Collinear.perm231 {A B C : P} (h : Collinear A B C) : Collinear B C A := by
  obtain ⟨a, hA, hB, hC⟩ := h; exact ⟨a, hB, hC, hA⟩

theorem Collinear.perm312 {A B C : P} (h : Collinear A B C) : Collinear C A B := by
  obtain ⟨a, hA, hB, hC⟩ := h; exact ⟨a, hC, hA, hB⟩

variable [hI : Connection P L]
include hI

/-- Two distinct lines have at most one common point. -/
theorem eq_of_mem_of_mem {a b : L} {X Y : P} (hab : a ≠ b) (hXa : X ∈ a) (hXb : X ∈ b)
    (hYa : Y ∈ a) (hYb : Y ∈ b) : X = Y := by
  by_contra h
  exact hab (line_unique h hXa hYa hXb hYb)

/-- If `A ≠ B` lie on `a` and `A`, `B`, `C` are collinear, then `C` lies on `a`. -/
theorem mem_of_collinear {A B C : P} {a : L} (h : Collinear A B C) (hAB : A ≠ B) (hA : A ∈ a)
    (hB : B ∈ a) : C ∈ a := by
  obtain ⟨c, hAc, hBc, hCc⟩ := h
  rwa [line_unique hAB hA hB hAc hBc]

/-- A point off a line through two distinct points is not collinear with them. -/
theorem not_collinear_of_not_mem {A B C : P} {a : L} (hA : A ∈ a) (hB : B ∈ a) (hAB : A ≠ B)
    (hC : C ∉ a) : ¬Collinear A B C := fun h => hC (mem_of_collinear h hAB hA hB)

/-- Of two distinct lines, the first has a point not on the second. -/
theorem exists_mem_not_mem {a b : L} (h : a ≠ b) : ∃ X : P, X ∈ a ∧ X ∉ b := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
  by_cases hA' : A ∈ b
  · by_cases hB' : B ∈ b
    · exact absurd (line_unique hAB hA hB hA' hB') h
    · exact ⟨B, hB, hB'⟩
  · exact ⟨A, hA, hA'⟩

end Incidence

section PlaneIncidence

variable {P : Type u} {L : Type v} [HasLines P L] [hI : PlaneConnection P L]
include hI

/-- In plane geometry, every line misses some point (I 7). -/
theorem exists_not_mem (a : L) : ∃ X : P, X ∉ a := by
  obtain ⟨A, B, C, h⟩ := exists_noncollinear (Point := P) (Line := L)
  by_contra hall
  simp only [not_exists, not_not] at hall
  exact h ⟨a, hall A, hall B, hall C⟩

end PlaneIncidence

/-! ### Elementary consequences of II 1–3 (without II 4) -/

namespace OrderCore

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hC : PlaneOrderCore P L]
  {A B C D X Y Z : P}
include hC

theorem ne12 (h : Between A B C) : A ≠ B :=
  (PlaneOrderCore.between_onLine (Line := L) A B C h).1

theorem ne13 (h : Between A B C) : A ≠ C :=
  (PlaneOrderCore.between_onLine (Line := L) A B C h).2.1

theorem ne23 (h : Between A B C) : B ≠ C :=
  (PlaneOrderCore.between_onLine (Line := L) A B C h).2.2.1

theorem col (h : Between A B C) : Collinear A B C :=
  (PlaneOrderCore.between_onLine (Line := L) A B C h).2.2.2

theorem symm (h : Between A B C) : Between C B A :=
  PlaneOrderCore.ax_II1 (Line := L) A B C (col h) h

theorem comm : Between A B C ↔ Between C B A := ⟨symm, symm⟩

theorem not12 (h : Between A B C) : ¬Between B A C := fun h' =>
  (PlaneOrderCore.ax_II3 (Line := L) A B C (col h) (ne12 h) (ne13 h) (ne23 h)).2.1 ⟨h', h⟩

theorem not23 (h : Between A B C) : ¬Between A C B := fun h' =>
  (PlaneOrderCore.ax_II3 (Line := L) A B C (col h) (ne12 h) (ne13 h) (ne23 h)).2.2.2 ⟨h, h'⟩

theorem trich (h : Collinear A B C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    Between B A C ∨ Between A B C ∨ Between A C B :=
  (PlaneOrderCore.ax_II3 (Line := L) A B C h hAB hAC hBC).1

theorem exists_between (h : A ≠ C) : ∃ B, Between A B C := by
  obtain ⟨a, hA, hC⟩ := exists_line (Line := L) h
  exact (PlaneOrderCore.ax_II2 A C a hA hC h).1

theorem exists_beyond (h : A ≠ C) : ∃ D, Between A C D := by
  obtain ⟨a, hA, hC⟩ := exists_line (Line := L) h
  exact (PlaneOrderCore.ax_II2 A C a hA hC h).2

/-- A point between two points of a line lies on the line. -/
theorem mem_of_between {a : L} (h : Between A B C) (hA : A ∈ a) (hC : C ∈ a) : B ∈ a :=
  mem_of_collinear (col h).swap23 (ne13 h) hA hC

theorem mem_of_between' {a : L} (h : Between A B C) (hA : A ∈ a) (hB : B ∈ a) : C ∈ a :=
  mem_of_collinear (col h) (ne12 h) hA hB

theorem mem_of_between'' {a : L} (h : Between A B C) (hB : B ∈ a) (hC : C ∈ a) : A ∈ a :=
  mem_of_collinear (col h).perm231 (ne23 h) hB hC

/-- Pasch's axiom II 5. -/
theorem pasch {a : L} (h : ¬Collinear A B C) (hA : A ∉ a) (hB : B ∉ a) (hCa : C ∉ a)
    (hX : X ∈ a) (hAXB : Between A X B) :
    (∃ Y, Y ∈ a ∧ Between B Y C) ∨ ∃ Y, Y ∈ a ∧ Between A Y C :=
  PlaneOrderCore.ax_II5 A B C a h hA hB hCa ⟨X, hX, hAXB⟩

/-! ### A line does not meet all three sides of a triangle -/

/-- Auxiliary configuration for `pasch_excl`. -/
theorem pasch_excl_aux {V U W P1 P2 Q : P} (h : ¬Collinear V U W) (h1 : Between V P1 U)
    (h2 : Between V P2 W) (hQ : Between U Q W) (hPQ : Between P1 Q P2) : False := by
  have hVU : V ≠ U := ne13 h1
  have hVW : V ≠ W := ne13 h2
  have hUW : U ≠ W := ne13 hQ
  set m : L := line U W hUW
  set g : L := line V U hVU
  set k : L := line V W hVW
  have hUm : U ∈ m := mem_line_left hUW
  have hWm : W ∈ m := mem_line_right hUW
  have hVg : V ∈ g := mem_line_left hVU
  have hUg : U ∈ g := mem_line_right hVU
  have hVk : V ∈ k := mem_line_left hVW
  have hWk : W ∈ k := mem_line_right hVW
  have hP1g : P1 ∈ g := mem_of_between h1 hVg hUg
  have hP2k : P2 ∈ k := mem_of_between h2 hVk hWk
  have hQm : Q ∈ m := mem_of_between hQ hUm hWm
  have hVm : V ∉ m := fun hV => h ⟨m, hV, hUm, hWm⟩
  have hmg : m ≠ g := fun e => hVm (e ▸ hVg)
  have hmk : m ≠ k := fun e => hVm (e ▸ hVk)
  have hP1m : P1 ∉ m := fun hP => ne23 h1 (eq_of_mem_of_mem hmg hP hP1g hUm hUg)
  have hP2m : P2 ∉ m := fun hP => ne23 h2 (eq_of_mem_of_mem hmk hP hP2k hWm hWk)
  have hgk : g ≠ k := fun e => h ⟨g, hVg, hUg, e ▸ hWk⟩
  have hVP1 : V ≠ P1 := ne12 h1
  have hnc : ¬Collinear P1 P2 V := by
    intro hc
    have hP2g : P2 ∈ g := mem_of_collinear hc.swap23 hVP1.symm hP1g hVg
    exact ne12 h2 (eq_of_mem_of_mem hgk hVg hVk hP2g hP2k)
  rcases pasch hnc hP1m hP2m hVm hQm hPQ with ⟨Y, hYm, hY⟩ | ⟨Y, hYm, hY⟩
  · have hYk : Y ∈ k := mem_of_between hY hP2k hVk
    have := eq_of_mem_of_mem hmk hYm hYk hWm hWk
    subst this
    exact not23 h2 (symm hY)
  · have hYg : Y ∈ g := mem_of_between hY hP1g hVg
    have := eq_of_mem_of_mem hmg hYm hYg hUm hUg
    subst this
    exact not23 h1 (symm hY)

/-- **A line does not meet all three sides of a triangle** (II 1–3, II 5). -/
theorem pasch_excl {a : L} (h : ¬Collinear A B C) (hX : X ∈ a) (hAXB : Between A X B) (hY : Y ∈ a) (hBYC : Between B Y C) (hZ : Z ∈ a)
    (hAZC : Between A Z C) : False := by
  have hAB : A ≠ B := ne13 hAXB
  have hBC : B ≠ C := ne13 hBYC
  have hAC : A ≠ C := ne13 hAZC
  set g : L := line A B hAB
  set k : L := line B C hBC
  set n : L := line A C hAC
  have hXg : X ∈ g := mem_of_between hAXB (mem_line_left hAB) (mem_line_right hAB)
  have hYk : Y ∈ k := mem_of_between hBYC (mem_line_left hBC) (mem_line_right hBC)
  have hZn : Z ∈ n := mem_of_between hAZC (mem_line_left hAC) (mem_line_right hAC)
  have hgk : g ≠ k := fun e => h ⟨g, mem_line_left hAB, mem_line_right hAB,
    e ▸ mem_line_right hBC⟩
  have hgn : g ≠ n := fun e => h ⟨g, mem_line_left hAB, mem_line_right hAB,
    e ▸ mem_line_right hAC⟩
  have hkn : k ≠ n := fun e => h ⟨k, e ▸ mem_line_left hAC, mem_line_left hBC,
    mem_line_right hBC⟩
  have hXY : X ≠ Y := by
    rintro rfl
    exact ne23 hAXB (eq_of_mem_of_mem hgk hXg hYk (mem_line_right hAB) (mem_line_left hBC))
  have hXZ : X ≠ Z := by
    rintro rfl
    exact ne12 hAXB (eq_of_mem_of_mem hgn hXg hZn (mem_line_left hAB) (mem_line_left hAC)).symm
  have hYZ : Y ≠ Z := by
    rintro rfl
    exact ne23 hBYC (eq_of_mem_of_mem hkn hYk hZn (mem_line_right hBC) (mem_line_right hAC))
  rcases trich (collinear_of_mem hX hY hZ) hXY hXZ hYZ with h1 | h1 | h1
  · exact pasch_excl_aux (V := C) (U := B) (W := A) (fun hc => h hc.swap13) (symm hBYC)
      (symm hAZC) (symm hAXB) h1
  · exact pasch_excl_aux (V := A) (U := B) (W := C) h hAXB hAZC hBYC h1
  · exact pasch_excl_aux (V := B) (U := A) (W := C) (fun hc => h hc.swap12) (symm hAXB) hBYC
      hAZC h1

/-! ### The sides of a line -/

theorem sameSide_symm {a : L} (h : SameSide a A B) : SameSide a B A :=
  ⟨h.2.1, h.1, fun ⟨X, hX, hB⟩ => h.2.2 ⟨X, hX, symm hB⟩⟩

theorem opp_symm {a : L} (h : OppositeSides a A B) : OppositeSides a B A := by
  obtain ⟨hA, hB, X, hX, hAXB⟩ := h
  exact ⟨hB, hA, X, hX, symm hAXB⟩

theorem sameSide_refl {a : L} (h : A ∉ a) : SameSide a A A :=
  ⟨h, h, fun ⟨_, _, hX⟩ => ne13 hX rfl⟩

omit hC in
theorem sameSide_or_opp {a : L} (hA : A ∉ a) (hB : B ∉ a) :
    SameSide a A B ∨ OppositeSides a A B := by
  by_cases h : ∃ X, X ∈ a ∧ Between A X B
  · exact Or.inr ⟨hA, hB, h⟩
  · exact Or.inl ⟨hA, hB, h⟩

omit hC in
theorem not_sameSide_of_opp {a : L} (h : OppositeSides a A B) : ¬SameSide a A B :=
  fun h' => h'.2.2 h.2.2

theorem ne_of_opp {a : L} (h : OppositeSides a A B) : A ≠ B := by
  obtain ⟨_, _, X, _, hX⟩ := h
  exact ne13 hX

theorem not_collinear_left {a : L} (hA : A ∈ a) (hB : B ∈ a) (hAB : A ≠ B) (hX : X ∉ a) :
    ¬Collinear X A B := fun h => hX (mem_of_collinear h.perm231 hAB hA hB)

theorem not_collinear_mid {a : L} (hA : A ∈ a) (hB : B ∈ a) (hAB : A ≠ B) (hX : X ∉ a) :
    ¬Collinear A X B := fun h => hX (mem_of_collinear h.swap23 hAB hA hB)

theorem sameSide_trans_nc {a : L} (h : ¬Collinear A B C) (h1 : SameSide a A B)
    (h2 : SameSide a B C) : SameSide a A C := by
  refine ⟨h1.1, h2.2.1, ?_⟩
  rintro ⟨X, hX, hAXC⟩
  rcases pasch (B := C) (C := B) (fun hc => h hc.swap23) h1.1 h2.2.1 h1.2.1 hX hAXC with
    ⟨Y, hY, hCYB⟩ | ⟨Y, hY, hAYB⟩
  · exact h2.2.2 ⟨Y, hY, symm hCYB⟩
  · exact h1.2.2 ⟨Y, hY, hAYB⟩

theorem opp_of_sameSide_opp_nc {a : L} (h : ¬Collinear A B C) (h1 : SameSide a A B)
    (h2 : OppositeSides a B C) : OppositeSides a A C := by
  obtain ⟨hB, hCa, X, hX, hBXC⟩ := h2
  refine ⟨h1.1, hCa, ?_⟩
  rcases pasch (A := B) (B := C) (C := A) (fun hc => h hc.perm312) hB hCa h1.1 hX hBXC with
    ⟨Y, hY, hCYA⟩ | ⟨Y, hY, hBYA⟩
  · exact ⟨Y, hY, symm hCYA⟩
  · exact absurd ⟨Y, hY, symm hBYA⟩ h1.2.2

theorem sameSide_of_opp_opp_nc {a : L} (h : ¬Collinear A B C) (h1 : OppositeSides a A B)
    (h2 : OppositeSides a B C) : SameSide a A C := by
  obtain ⟨hA, _, X, hX, hAXB⟩ := h1
  obtain ⟨_, hCa, Y, hY, hBYC⟩ := h2
  exact ⟨hA, hCa, fun ⟨Z, hZ, hAZC⟩ => pasch_excl h hX hAXB hY hBYC hZ hAZC⟩

/-- An auxiliary point: for `A ∉ a` on a line `m ≠ a`, a point `E` off `m` on the same side of `a`
as `A` (on the line joining a point `D` of `a` to `A`, beyond `A`). -/
theorem exists_aux_point {a m : L} (hAm : A ∈ m) (hAa : A ∉ a) (hma : m ≠ a) :
    ∃ E : P, E ∉ m ∧ SameSide a E A := by
  obtain ⟨D, hDa, hDm⟩ := exists_mem_not_mem (P := P) hma.symm
  have hDA : D ≠ A := fun e => hAa (e ▸ hDa)
  obtain ⟨E, hDAE⟩ := exists_beyond (L := L) hDA
  have hDg : D ∈ line (Line := L) D A hDA := mem_line_left hDA
  have hAg : A ∈ line (Line := L) D A hDA := mem_line_right hDA
  have hEg : E ∈ line (Line := L) D A hDA := mem_of_between' hDAE hDg hAg
  have hga : line (Line := L) D A hDA ≠ a := fun e => hAa (e ▸ hAg)
  have hgm : line (Line := L) D A hDA ≠ m := fun e => hDm (e ▸ hDg)
  have hEm : E ∉ m := fun hE => ne23 hDAE (eq_of_mem_of_mem hgm hAg hAm hEg hE)
  have hEa : E ∉ a := fun hE => ne13 hDAE (eq_of_mem_of_mem hga hDg hDa hEg hE)
  refine ⟨E, hEm, hEa, hAa, ?_⟩
  rintro ⟨X, hXa, hEXA⟩
  have hXg : X ∈ line (Line := L) D A hDA := mem_of_between hEXA hEg hAg
  have : X = D := eq_of_mem_of_mem hga hXg hXa hDg hDa
  rw [this] at hEXA
  exact not12 hDAE (symm hEXA)

/-- **Same side is transitive** (II 1–3, II 5). -/
theorem sameSide_trans {a : L} (h1 : SameSide a A B) (h2 : SameSide a B C) : SameSide a A C := by
  by_cases hc : Collinear A B C
  swap
  · exact sameSide_trans_nc hc h1 h2
  by_cases hAB : A = B
  · subst hAB; exact h2
  by_cases hBC : B = C
  · subst hBC; exact h1
  by_cases hAC : A = C
  · subst hAC; exact sameSide_refl h1.1
  have hAm : A ∈ line (Line := L) A B hAB := mem_line_left hAB
  have hBm : B ∈ line (Line := L) A B hAB := mem_line_right hAB
  have hCm : C ∈ line (Line := L) A B hAB := mem_of_collinear hc hAB hAm hBm
  have hma : line (Line := L) A B hAB ≠ a := fun e => h1.1 (e ▸ hAm)
  obtain ⟨E, hEm, hEA⟩ := exists_aux_point hAm h1.1 hma
  have hEB := sameSide_trans_nc (not_collinear_left hAm hBm hAB hEm) hEA h1
  have hEC := sameSide_trans_nc (not_collinear_left hBm hCm hBC hEm) hEB h2
  exact sameSide_trans_nc (not_collinear_mid hAm hCm hAC hEm) (sameSide_symm hEA) hEC

/-- **Same side and opposite sides give opposite sides** (II 1–3, II 5). -/
theorem opp_of_sameSide_opp {a : L} (h1 : SameSide a A B) (h2 : OppositeSides a B C) :
    OppositeSides a A C := by
  by_cases hc : Collinear A B C
  swap
  · exact opp_of_sameSide_opp_nc hc h1 h2
  by_cases hAB : A = B
  · subst hAB; exact h2
  have hBC : B ≠ C := ne_of_opp h2
  by_cases hAC : A = C
  · subst hAC; exact absurd h1 (not_sameSide_of_opp (opp_symm h2))
  have hAm : A ∈ line (Line := L) A B hAB := mem_line_left hAB
  have hBm : B ∈ line (Line := L) A B hAB := mem_line_right hAB
  have hCm : C ∈ line (Line := L) A B hAB := mem_of_collinear hc hAB hAm hBm
  have hma : line (Line := L) A B hAB ≠ a := fun e => h1.1 (e ▸ hAm)
  obtain ⟨E, hEm, hEA⟩ := exists_aux_point hAm h1.1 hma
  have hEB := sameSide_trans_nc (not_collinear_left hAm hBm hAB hEm) hEA h1
  have hEC := opp_of_sameSide_opp_nc (not_collinear_left hBm hCm hBC hEm) hEB h2
  exact opp_of_sameSide_opp_nc (not_collinear_mid hAm hCm hAC hEm) (sameSide_symm hEA) hEC

/-- **Opposite sides twice give the same side** (II 1–3, II 5). -/
theorem sameSide_of_opp_opp {a : L} (h1 : OppositeSides a A B) (h2 : OppositeSides a B C) :
    SameSide a A C := by
  by_cases hc : Collinear A B C
  swap
  · exact sameSide_of_opp_opp_nc hc h1 h2
  have hAB : A ≠ B := ne_of_opp h1
  have hBC : B ≠ C := ne_of_opp h2
  by_cases hAC : A = C
  · subst hAC; exact sameSide_refl h1.1
  have hAm : A ∈ line (Line := L) A B hAB := mem_line_left hAB
  have hBm : B ∈ line (Line := L) A B hAB := mem_line_right hAB
  have hCm : C ∈ line (Line := L) A B hAB := mem_of_collinear hc hAB hAm hBm
  have hma : line (Line := L) A B hAB ≠ a := fun e => h1.1 (e ▸ hAm)
  obtain ⟨E, hEm, hEA⟩ := exists_aux_point hAm h1.1 hma
  have hEB := opp_of_sameSide_opp_nc (not_collinear_left hAm hBm hAB hEm) hEA h1
  have hEC := sameSide_of_opp_opp_nc (not_collinear_left hBm hCm hBC hEm) hEB h2
  exact sameSide_trans_nc (not_collinear_mid hAm hCm hAC hEm) (sameSide_symm hEA) hEC

/-! ### The four-point lemmas and axiom II 4 (E. H. Moore) -/

/-- If `B` is between `A` and `C` and `C` between `B` and `D`, then `C` is between `A` and `D`
(II 1–3, II 5, without II 4). -/
theorem between_of_between_between₁ (h1 : Between A B C) (h2 : Between B C D) :
    Between A C D := by
  have hBC : B ≠ C := ne12 h2
  have hBg : B ∈ line (Line := L) B C hBC := mem_line_left hBC
  have hCg : C ∈ line (Line := L) B C hBC := mem_line_right hBC
  have hAg := mem_of_between'' h1 hBg hCg
  have hDg := mem_of_between' h2 hBg hCg
  obtain ⟨G, hG⟩ := exists_not_mem (P := P) (line (Line := L) B C hBC)
  have hCG : C ≠ G := fun e => hG (e ▸ hCg)
  have hCl : C ∈ line (Line := L) C G hCG := mem_line_left hCG
  have hGl : G ∈ line (Line := L) C G hCG := mem_line_right hCG
  have hlg : line (Line := L) C G hCG ≠ line B C hBC := fun e => hG (e ▸ hGl)
  have key : ∀ X, X ∈ line (Line := L) B C hBC → X ∈ line (Line := L) C G hCG → X = C :=
    fun X hXg hXl => eq_of_mem_of_mem hlg hXl hXg hCl hCg
  have hAl : A ∉ line (Line := L) C G hCG := fun h => ne13 h1 (key A hAg h)
  have hBl : B ∉ line (Line := L) C G hCG := fun h => hBC (key B hBg h)
  have hDl : D ∉ line (Line := L) C G hCG := fun h => ne23 h2 (key D hDg h).symm
  have hAB : SameSide (line (Line := L) C G hCG) A B := ⟨hAl, hBl, fun ⟨X, hXl, hAXB⟩ => by
    rw [key X (mem_of_between hAXB hAg hBg) hXl] at hAXB
    exact not23 h1 hAXB⟩
  have hBD : OppositeSides (line (Line := L) C G hCG) B D := ⟨hBl, hDl, C, hCl, h2⟩
  obtain ⟨_, _, X, hXl, hAXD⟩ := opp_of_sameSide_opp hAB hBD
  rwa [key X (mem_of_between hAXD hAg hDg) hXl] at hAXD

theorem between_of_between_between₁' (h1 : Between A B C) (h2 : Between B C D) :
    Between A B D :=
  symm (between_of_between_between₁ (symm h2) (symm h1))

/-- If `B` is between `A` and `C` and `C` between `A` and `D`, then `C` is between `B` and `D`
(II 1–3, II 5, without II 4). -/
theorem between_of_between_between₂ (h1 : Between A B C) (h2 : Between A C D) :
    Between B C D := by
  have hAC : A ≠ C := ne13 h1
  have hAg : A ∈ line (Line := L) A C hAC := mem_line_left hAC
  have hCg : C ∈ line (Line := L) A C hAC := mem_line_right hAC
  have hBg := mem_of_between h1 hAg hCg
  have hDg := mem_of_between' h2 hAg hCg
  obtain ⟨G, hG⟩ := exists_not_mem (P := P) (line (Line := L) A C hAC)
  have hCG : C ≠ G := fun e => hG (e ▸ hCg)
  have hCl : C ∈ line (Line := L) C G hCG := mem_line_left hCG
  have hGl : G ∈ line (Line := L) C G hCG := mem_line_right hCG
  have hlg : line (Line := L) C G hCG ≠ line A C hAC := fun e => hG (e ▸ hGl)
  have key : ∀ X, X ∈ line (Line := L) A C hAC → X ∈ line (Line := L) C G hCG → X = C :=
    fun X hXg hXl => eq_of_mem_of_mem hlg hXl hXg hCl hCg
  have hAl : A ∉ line (Line := L) C G hCG := fun h => hAC (key A hAg h)
  have hBl : B ∉ line (Line := L) C G hCG := fun h => ne23 h1 (key B hBg h)
  have hDl : D ∉ line (Line := L) C G hCG := fun h => ne23 h2 (key D hDg h).symm
  have hBA : SameSide (line (Line := L) C G hCG) B A := ⟨hBl, hAl, fun ⟨X, hXl, hBXA⟩ => by
    rw [key X (mem_of_between hBXA hBg hAg) hXl] at hBXA
    exact not23 h1 (symm hBXA)⟩
  have hAD : OppositeSides (line (Line := L) C G hCG) A D := ⟨hAl, hDl, C, hCl, h2⟩
  obtain ⟨_, _, X, hXl, hBXD⟩ := opp_of_sameSide_opp hBA hAD
  rwa [key X (mem_of_between hBXD hBg hDg) hXl] at hBXD

theorem between_of_between_between₂' (h1 : Between A B C) (h2 : Between A C D) :
    Between A B D :=
  between_of_between_between₁' h1 (between_of_between_between₂ h1 h2)

end OrderCore

/-- Four points `W, X, Y, Z` in the arrangement of axiom II 4. -/
def II4Arrangement {P : Type u} [HasBetween P] (W X Y Z : P) : Prop :=
  Between W X Y ∧ Between W X Z ∧ Between W Y Z ∧ Between X Y Z

theorem exists_perm_of_arr {P : Type u} [HasBetween P] (Q : Fin 4 → P) (f : Fin 4 → Fin 4)
    (hf : Function.Bijective f) (h : II4Arrangement (Q (f 0)) (Q (f 1)) (Q (f 2)) (Q (f 3))) :
    ∃ σ : Equiv.Perm (Fin 4), II4Arrangement (Q (σ 0)) (Q (σ 1)) (Q (σ 2)) (Q (σ 3)) :=
  ⟨Equiv.ofBijective f hf, h⟩

namespace OrderCore

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hC : PlaneOrderCore P L]
include hC

/-- Placing a fourth point `D` relative to `E₁`, `M`, `E₂` with `M` between `E₁` and `E₂`. -/
theorem arr_of_between {E₁ M E₂ D : P} {a : L} (h : Between E₁ M E₂) (hE₁ : E₁ ∈ a)
    (hE₂ : E₂ ∈ a) (hD : D ∈ a) (h1 : E₁ ≠ D) (h2 : M ≠ D) (h3 : E₂ ≠ D) :
    II4Arrangement D E₁ M E₂ ∨ II4Arrangement E₁ M E₂ D ∨ II4Arrangement E₁ M D E₂ ∨ II4Arrangement E₁ D M E₂ := by
  have hM : M ∈ a := mem_of_between h hE₁ hE₂
  rcases trich (L := L) (collinear_of_mem hE₁ hE₂ hD) (ne13 h) h1 h3 with h4 | h4 | h4
  · left
    exact ⟨symm (between_of_between_between₂ (symm h) h4), symm h4,
      symm (between_of_between_between₂' (symm h) h4), h⟩
  · right; left
    exact ⟨h, between_of_between_between₂' h h4, h4, between_of_between_between₂ h h4⟩
  · rcases trich (L := L) (collinear_of_mem hE₁ hM hD) (ne12 h) h1 h2 with h5 | h5 | h5
    · exact absurd (between_of_between_between₁' h5 h4) (not12 h)
    · right; right; left
      exact ⟨h5, h, h4, between_of_between_between₂ h5 h4⟩
    · right; right; right
      exact ⟨h5, h4, h, between_of_between_between₂ h5 h⟩

/-- **Axiom II 4 follows from I 1–2, I 7, II 1–3 and II 5** (plane geometry; E. H. Moore). -/
theorem axiomII4 : AxiomII4 P := by
  intro A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD
  show ∃ σ : Equiv.Perm (Fin 4), II4Arrangement (![A, B, C, D] (σ 0)) (![A, B, C, D] (σ 1))
    (![A, B, C, D] (σ 2)) (![A, B, C, D] (σ 3))
  rcases trich (L := L) (collinear_of_mem hA hB hC) hAB hAC hBC with h | h | h
  · rcases arr_of_between h hB hC hD hBD hAD hCD with h' | h' | h' | h'
    · exact exists_perm_of_arr _ ![3, 1, 0, 2] (by decide) h'
    · exact exists_perm_of_arr _ ![1, 0, 2, 3] (by decide) h'
    · exact exists_perm_of_arr _ ![1, 0, 3, 2] (by decide) h'
    · exact exists_perm_of_arr _ ![1, 3, 0, 2] (by decide) h'
  · rcases arr_of_between h hA hC hD hAD hBD hCD with h' | h' | h' | h'
    · exact exists_perm_of_arr _ ![3, 0, 1, 2] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 1, 2, 3] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 1, 3, 2] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 3, 1, 2] (by decide) h'
  · rcases arr_of_between h hA hB hD hAD hCD hBD with h' | h' | h' | h'
    · exact exists_perm_of_arr _ ![3, 0, 2, 1] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 2, 1, 3] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 2, 3, 1] (by decide) h'
    · exact exists_perm_of_arr _ ![0, 3, 2, 1] (by decide) h'

end OrderCore

/-! ## The linear axioms II 1–4: positions of three and four points of a line -/

/-- `y` lies strictly between `x` and `z` (integers). -/
def IBtw (x y z : ℤ) : Prop := (x < y ∧ y < z) ∨ (z < y ∧ y < x)

namespace OrderLin

section Positions

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  {A B C D O U X Y Z : P}
include hO

/-- The six arrangements of three points when `Y` is between `X` and `Z` (II 1, II 3). -/
theorem between_six (h : Between X Y Z) :
    Between X Y Z ∧ Between Z Y X ∧ ¬Between Y X Z ∧ ¬Between Z X Y ∧ ¬Between X Z Y ∧
      ¬Between Y Z X :=
  ⟨h, between_symm h, not_between_swap12 h, fun h' => not_between_swap12 h (between_symm h'),
    not_between_swap23 h, fun h' => not_between_swap23 h (between_symm h')⟩

/-- **Three points of a line have integer positions** describing their betweenness (II 1, II 3). -/
theorem three_points (h : Collinear A B C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∃ a b c : ℤ, (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      ((Between A B C ↔ IBtw a b c) ∧ (Between A C B ↔ IBtw a c b) ∧
      (Between B A C ↔ IBtw b a c) ∧ (Between B C A ↔ IBtw b c a) ∧
      (Between C A B ↔ IBtw c a b) ∧ (Between C B A ↔ IBtw c b a)) := by
  rcases between_trichotomy (Line := L) h hAB hAC hBC with h1 | h1 | h1
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := between_six h1
    refine ⟨1, 0, 2, by decide, ?_⟩
    simp [IBtw, e1, e2, e3, e4, e5, e6]
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := between_six h1
    refine ⟨0, 1, 2, by decide, ?_⟩
    simp [IBtw, e1, e2, e3, e4, e5, e6]
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := between_six h1
    refine ⟨0, 2, 1, by decide, ?_⟩
    simp [IBtw, e1, e2, e3, e4, e5, e6]

theorem four_aux {R : Fin 4 → P} (h0 : Between (R 0) (R 1) (R 2))
    (h1 : Between (R 0) (R 1) (R 3)) (h2 : Between (R 0) (R 2) (R 3))
    (h3 : Between (R 1) (R 2) (R 3)) (i j k : Fin 4) :
    Between (R i) (R j) (R k) ↔ IBtw (i : ℕ) (j : ℕ) (k : ℕ) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := between_six h0
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := between_six h1
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := between_six h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := between_six h3
  have n : ∀ i k : Fin 4, ¬Between (R i) (R i) (R k) := fun i k h => ne12_of_between h rfl
  have n' : ∀ i k : Fin 4, ¬Between (R k) (R i) (R i) := fun i k h => ne23_of_between h rfl
  have n'' : ∀ i k : Fin 4, ¬Between (R i) (R k) (R i) := fun i k h => ne13_of_between h rfl
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [IBtw, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, c1, c2, c3, c4, c5, c6, d1, d2,
      d3, d4, d5, d6, n, n', n'']

/-- Positions of four points of a line, from II 4. -/
theorem four_pos {a : L} (hA : A ∈ a) (hB : B ∈ a) (hC : C ∈ a) (hD : D ∈ a) (hAB : A ≠ B)
    (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ∃ p : Fin 4 → ℤ, Function.Injective p ∧ ∀ i j k : Fin 4,
      (Between (![A, B, C, D] i) (![A, B, C, D] j) (![A, B, C, D] k) ↔
        IBtw (p i) (p j) (p k)) := by
  obtain ⟨σ, h0, h1, h2, h3⟩ :=
    LineOrder.ax_II4 (Line := L) A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD
  refine ⟨fun i => ((σ.symm i : ℕ) : ℤ), ?_, ?_⟩
  · intro i j h
    simp only [Nat.cast_inj] at h
    exact σ.symm.injective (Fin.ext h)
  · intro i j k
    have := four_aux (R := fun i => ![A, B, C, D] (σ i)) h0 h1 h2 h3 (σ.symm i) (σ.symm j)
      (σ.symm k)
    simpa using this

/-- **Four distinct points of a line have integer positions** describing their betweenness
(II 1–4). -/
theorem four_points {a : L} (hA : A ∈ a) (hB : B ∈ a) (hC : C ∈ a) (hD : D ∈ a) (hAB : A ≠ B)
    (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    ∃ a b c d : ℤ, (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧
      ((Between A B C ↔ IBtw a b c) ∧
      (Between A B D ↔ IBtw a b d) ∧
      (Between A C B ↔ IBtw a c b) ∧
      (Between A C D ↔ IBtw a c d) ∧
      (Between A D B ↔ IBtw a d b) ∧
      (Between A D C ↔ IBtw a d c) ∧
      (Between B A C ↔ IBtw b a c) ∧
      (Between B A D ↔ IBtw b a d) ∧
      (Between B C A ↔ IBtw b c a) ∧
      (Between B C D ↔ IBtw b c d) ∧
      (Between B D A ↔ IBtw b d a) ∧
      (Between B D C ↔ IBtw b d c) ∧
      (Between C A B ↔ IBtw c a b) ∧
      (Between C A D ↔ IBtw c a d) ∧
      (Between C B A ↔ IBtw c b a) ∧
      (Between C B D ↔ IBtw c b d) ∧
      (Between C D A ↔ IBtw c d a) ∧
      (Between C D B ↔ IBtw c d b) ∧
      (Between D A B ↔ IBtw d a b) ∧
      (Between D A C ↔ IBtw d a c) ∧
      (Between D B A ↔ IBtw d b a) ∧
      (Between D B C ↔ IBtw d b c) ∧
      (Between D C A ↔ IBtw d c a) ∧
      (Between D C B ↔ IBtw d c b)) := by
  obtain ⟨p, hpi, hp⟩ := four_pos hA hB hC hD hAB hAC hAD hBC hBD hCD
  refine ⟨p 0, p 1, p 2, p 3, ⟨fun h => absurd (hpi h) (by decide),
    fun h => absurd (hpi h) (by decide), fun h => absurd (hpi h) (by decide),
    fun h => absurd (hpi h) (by decide), fun h => absurd (hpi h) (by decide),
    fun h => absurd (hpi h) (by decide)⟩, ⟨hp 0 1 2,
    hp 0 1 3,
    hp 0 2 1,
    hp 0 2 3,
    hp 0 3 1,
    hp 0 3 2,
    hp 1 0 2,
    hp 1 0 3,
    hp 1 2 0,
    hp 1 2 3,
    hp 1 3 0,
    hp 1 3 2,
    hp 2 0 1,
    hp 2 0 3,
    hp 2 1 0,
    hp 2 1 3,
    hp 2 3 0,
    hp 2 3 1,
    hp 3 0 1,
    hp 3 0 2,
    hp 3 1 0,
    hp 3 1 2,
    hp 3 2 0,
    hp 3 2 1⟩⟩

/-- II 1–4: if `B` is between `A` and `C` and `C` between `A` and `D`, then `B` is between
`A` and `D` and `C` between `B` and `D`. -/
theorem trans₂ (h1 : Between A B C) (h2 : Between A C D) : Between A B D ∧ Between B C D := by
  obtain ⟨g, hAg, hBg, hCg⟩ := collinear_of_between h1
  have hDg : D ∈ g := mem_of_collinear (collinear_of_between h2) (ne13_of_between h1) hAg hCg
  have hBD : B ≠ D := by rintro rfl; exact not_between_swap23 h1 h2
  obtain ⟨a, b, c, d, hd, hp⟩ := four_points hAg hBg hCg hDg (ne12_of_between h1)
    (ne13_of_between h1) (ne13_of_between h2) (ne23_of_between h1) hBD (ne23_of_between h2)
  simp only [hp, IBtw] at h1 h2 ⊢
  omega

/-- II 1–4: if `B` is between `A` and `C` and `C` between `B` and `D`, then `B` is between
`A` and `D` and `C` between `A` and `D`. -/
theorem trans₁ (h1 : Between A B C) (h2 : Between B C D) : Between A B D ∧ Between A C D := by
  obtain ⟨g, hAg, hBg, hCg⟩ := collinear_of_between h1
  have hDg : D ∈ g := mem_of_collinear (collinear_of_between h2) (ne12_of_between h2) hBg hCg
  have hAD : A ≠ D := by rintro rfl; exact not_between_swap23 h1 (between_symm h2)
  obtain ⟨a, b, c, d, hd, hp⟩ := four_points hAg hBg hCg hDg (ne12_of_between h1)
    (ne13_of_between h1) hAD (ne23_of_between h1) (ne13_of_between h2) (ne23_of_between h2)
  simp only [hp, IBtw] at h1 h2 ⊢
  omega

end Positions

end OrderLin

namespace OrderLin

/-! ### The order of sequence of the points of a line (II 1–4) -/

/-- Sign of the point `X` of a line relative to the reference points `O ≠ U` of the line: `0` for
`X = O`, `-1` if `O` lies between `U` and `X`, and `1` otherwise. -/
noncomputable def sgn {P : Type u} [HasBetween P] (O U X : P) : ℤ := by
  classical exact if X = O then 0 else if Between U O X then -1 else 1

/-- The **order of sequence** of the points of a line determined by the reference points `O`, `U`:
`X` precedes `Y`. -/
def lineLt {P : Type u} [HasBetween P] (O U X Y : P) : Prop :=
  sgn O U X < sgn O U Y ∨ (sgn O U X = 1 ∧ sgn O U Y = 1 ∧ Between O X Y) ∨
    (sgn O U X = -1 ∧ sgn O U Y = -1 ∧ Between X Y O)

theorem sgn_self {P : Type u} [HasBetween P] (O U : P) : sgn O U O = 0 := by
  unfold sgn; simp

theorem sgn_of_ne {P : Type u} [HasBetween P] {O U X : P} (hX : X ≠ O) :
    (sgn O U X = -1 ∧ Between U O X) ∨ (sgn O U X = 1 ∧ ¬Between U O X) := by
  unfold sgn
  by_cases h : Between U O X <;> simp [hX, h]

theorem sgn_bounds {P : Type u} [HasBetween P] (O U X : P) : -1 ≤ sgn O U X ∧ sgn O U X ≤ 1 := by
  by_cases hX : X = O
  · subst hX; rw [sgn_self]; omega
  · rcases sgn_of_ne (U := U) hX with h | h <;> omega

theorem sgn_ne_zero {P : Type u} [HasBetween P] {O U X : P} (hX : X ≠ O) : sgn O U X ≠ 0 := by
  rcases sgn_of_ne (U := U) hX with h | h <;> omega

theorem lineLt_irrefl {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [LineOrder P L]
    (O U X : P) : ¬lineLt O U X X := by
  unfold lineLt
  rintro (h | ⟨-, -, h⟩ | ⟨-, -, h⟩)
  · exact lt_irrefl _ h
  · exact ne23_of_between h rfl
  · exact ne12_of_between h rfl

theorem lineLt_simp {P : Type u} [HasBetween P] {O U X Y : P} (s t : ℤ) (hs : sgn O U X = s)
    (ht : sgn O U Y = t) :
    lineLt O U X Y ↔ s < t ∨ (s = 1 ∧ t = 1 ∧ Between O X Y) ∨ (s = -1 ∧ t = -1 ∧ Between X Y O) := by
  unfold lineLt; rw [hs, ht]

section LineOrderSec

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  {O U X Y Z : P} {a : L}
include hO

/-- The sign rule: `O` lies between two points `X`, `Y ≠ O` of the line iff their signs differ. -/
theorem sign_rule (hOa : O ∈ a) (hUa : U ∈ a) (hOU : O ≠ U) (hX : X ∈ a) (hY : Y ∈ a)
    (hXO : X ≠ O) (hYO : Y ≠ O) (hXY : X ≠ Y) : Between X O Y ↔ sgn O U X ≠ sgn O U Y := by
  by_cases hXU : X = U
  · subst hXU
    have hs : sgn O X X = 1 := by
      rcases sgn_of_ne (U := X) hXO with h | h
      · exact absurd h.2 not_between_self
      · exact h.1
    rw [hs]
    rcases sgn_of_ne (U := X) hYO with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> simp [h2]
  by_cases hYU : Y = U
  · subst hYU
    have hs : sgn O Y Y = 1 := by
      rcases sgn_of_ne (U := Y) hYO with h | h
      · exact absurd h.2 not_between_self
      · exact h.1
    rw [hs, between_comm]
    rcases sgn_of_ne (U := Y) hXO with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> simp [h2]
  obtain ⟨u, o, x, y, hd, hp⟩ := OrderLin.four_points hUa hOa hX hY hOU.symm (Ne.symm hXU)
    (Ne.symm hYU) hXO.symm hYO.symm hXY
  rcases sgn_of_ne (U := U) hXO with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases sgn_of_ne (U := U) hYO with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rw [h1, h3] <;> simp only [hp, IBtw] at h2 h4 ⊢ <;> constructor <;> intro <;> omega

/-- **Betweenness is described by the order of sequence**: for three distinct points `X`, `Y`, `Z`
of the line, `Y` lies between `X` and `Z` iff `X, Y, Z` or `Z, Y, X` are in increasing order. -/
theorem between_iff_lineLt (hOa : O ∈ a) (hUa : U ∈ a) (hOU : O ≠ U) (hX : X ∈ a) (hY : Y ∈ a)
    (hZ : Z ∈ a) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) :
    Between X Y Z ↔ (lineLt O U X Y ∧ lineLt O U Y Z) ∨ (lineLt O U Z Y ∧ lineLt O U Y X) := by
  by_cases hXO : X = O
  · subst hXO
    obtain ⟨o, y, z, hd, hp⟩ := OrderLin.three_points (collinear_of_mem hX hY hZ) hXY hXZ hYZ
    have hs := sign_rule hX hUa hOU hY hZ hXY.symm hXZ.symm hYZ
    rcases sgn_of_ne (U := U) hXY.symm with ⟨h2, -⟩ | ⟨h2, -⟩ <;>
    rcases sgn_of_ne (U := U) hXZ.symm with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
    simp only [lineLt_simp _ _ (sgn_self X U) h2, lineLt_simp _ _ h2 (sgn_self X U),
      lineLt_simp _ _ h2 h3, lineLt_simp _ _ h3 h2, h2, h3] at hs ⊢ <;>
    norm_num at hs ⊢ <;>
    simp only [hp, IBtw] at hs ⊢ <;> omega
  by_cases hYO : Y = O
  · subst hYO
    obtain ⟨x, o, z, hd, hp⟩ := OrderLin.three_points (collinear_of_mem hX hY hZ) hXY hXZ hYZ
    have hs := sign_rule hY hUa hOU hX hZ hXY hYZ.symm hXZ
    rcases sgn_of_ne (U := U) hXY with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases sgn_of_ne (U := U) hYZ.symm with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
    simp only [lineLt_simp _ _ (sgn_self Y U) h1, lineLt_simp _ _ h1 (sgn_self Y U),
      lineLt_simp _ _ (sgn_self Y U) h3, lineLt_simp _ _ h3 (sgn_self Y U), h1, h3] at hs ⊢ <;>
    norm_num at hs ⊢ <;>
    simp only [hp, IBtw] at hs ⊢ <;> omega
  by_cases hZO : Z = O
  · subst hZO
    obtain ⟨x, y, o, hd, hp⟩ := OrderLin.three_points (collinear_of_mem hX hY hZ) hXY hXZ hYZ
    have hs := sign_rule hZ hUa hOU hX hY hXZ hYZ hXY
    rcases sgn_of_ne (U := U) hXZ with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases sgn_of_ne (U := U) hYZ with ⟨h2, -⟩ | ⟨h2, -⟩ <;>
    simp only [lineLt_simp _ _ h1 h2, lineLt_simp _ _ h2 h1,
      lineLt_simp _ _ (sgn_self Z U) h2, lineLt_simp _ _ h2 (sgn_self Z U), h1, h2] at hs ⊢ <;>
    norm_num at hs ⊢ <;>
    simp only [hp, IBtw] at hs ⊢ <;> omega
  obtain ⟨o, x, y, z, hd, hp⟩ := OrderLin.four_points hOa hX hY hZ (Ne.symm hXO) (Ne.symm hYO)
    (Ne.symm hZO) hXY hXZ hYZ
  have s1 := sign_rule hOa hUa hOU hX hY hXO hYO hXY
  have s2 := sign_rule hOa hUa hOU hX hZ hXO hZO hXZ
  have s3 := sign_rule hOa hUa hOU hY hZ hYO hZO hYZ
  rcases sgn_of_ne (U := U) hXO with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
  rcases sgn_of_ne (U := U) hYO with ⟨h2, -⟩ | ⟨h2, -⟩ <;>
  rcases sgn_of_ne (U := U) hZO with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
  simp only [lineLt_simp _ _ h1 h2, lineLt_simp _ _ h2 h1, lineLt_simp _ _ h2 h3,
    lineLt_simp _ _ h3 h2, h1, h2, h3] at s1 s2 s3 ⊢ <;>
  norm_num at s1 s2 s3 ⊢ <;>
  simp only [hp, IBtw] at s1 s2 s3 ⊢ <;> omega

theorem lineLt_trichotomous (hOa : O ∈ a) (hUa : U ∈ a) (hOU : O ≠ U) (hX : X ∈ a) (hY : Y ∈ a)
    (hXY : X ≠ Y) : lineLt O U X Y ∨ lineLt O U Y X := by
  have bX := sgn_bounds O U X
  have bY := sgn_bounds O U Y
  unfold lineLt
  by_cases hXO : X = O
  · subst hXO
    have := sgn_ne_zero (U := U) hXY.symm
    rw [sgn_self]; omega
  by_cases hYO : Y = O
  · subst hYO
    have := sgn_ne_zero (U := U) hXY
    rw [sgn_self]; omega
  have hXn := sgn_ne_zero (U := U) hXO
  have hYn := sgn_ne_zero (U := U) hYO
  have hs := sign_rule hOa hUa hOU hX hY hXO hYO hXY
  by_cases he : sgn O U X = sgn O U Y
  · have hn : ¬Between X O Y := fun h => hs.1 h he
    rcases between_trichotomy (collinear_of_mem hOa hX hY) (Ne.symm hXO) (Ne.symm hYO) hXY with
      h | h | h
    · exact absurd h hn
    · by_cases h1 : sgn O U X = 1
      · left; right; left; exact ⟨h1, he ▸ h1, h⟩
      · right; right; right; exact ⟨by omega, by omega, between_symm h⟩
    · by_cases h1 : sgn O U X = 1
      · right; right; left; exact ⟨he ▸ h1, h1, h⟩
      · left; right; right; exact ⟨by omega, by omega, between_symm h⟩
  · omega

theorem lineLt_trans (h1 : lineLt O U X Y) (h2 : lineLt O U Y Z) : lineLt O U X Z := by
  have bX := sgn_bounds O U X
  have bY := sgn_bounds O U Y
  have bZ := sgn_bounds O U Z
  unfold lineLt at *
  rcases h1 with h1 | ⟨h1, h1', h1''⟩ | ⟨h1, h1', h1''⟩ <;>
    rcases h2 with h2 | ⟨h2, h2', h2''⟩ | ⟨h2, h2', h2''⟩
  all_goals first
    | (left; omega)
    | omega
    | (right; left; exact ⟨h1, h2', (OrderLin.trans₂ h1'' h2'').1⟩)
    | (right; right; exact ⟨h1, h2',
        between_symm (OrderLin.trans₂ (between_symm h2'') (between_symm h1'')).1⟩)

/-- The order of sequence on the points of a line is a strict total order. -/
theorem lineLt_isStrictTotalOrder (hOa : O ∈ a) (hUa : U ∈ a) (hOU : O ≠ U) :
    IsStrictTotalOrder {X : P // X ∈ a} (fun X Y => lineLt O U (X : P) Y) :=
  @IsStrictTotalOrder.mk _ _
    ⟨fun X Y h1 h2 => by
      by_contra h
      rcases lineLt_trichotomous hOa hUa hOU X.2 Y.2 (fun e => h (Subtype.ext e)) with h3 | h3
      · exact h1 h3
      · exact h2 h3⟩
    (@IsStrictOrder.mk _ _ ⟨fun X => lineLt_irrefl O U (X : P)⟩
      ⟨fun _ _ _ h1 h2 => lineLt_trans h1 h2⟩)

/-- The linear order of the points of a line given by the reference points `O ≠ U`. -/
@[instance_reducible] noncomputable def lineOrder (hOa : O ∈ a) (hUa : U ∈ a) (hOU : O ≠ U) :
    LinearOrder {X : P // X ∈ a} :=
  @linearOrderOfSTO _ (fun X Y => lineLt O U (X : P) Y)
    (lineLt_isStrictTotalOrder hOa hUa hOU) (Classical.decRel _)

end LineOrderSec

/-- In a linear order, a "betweenness-monotone" sequence whose first two terms increase is strictly
monotone. -/
theorem strictMono_of_btw {α : Type*} [LinearOrder α] {n : ℕ} (g : Fin n → α)
    (hg : ∀ i j k : Fin n, i < j → j < k → (g i < g j ∧ g j < g k) ∨ (g k < g j ∧ g j < g i))
    (h01 : ∀ h : 1 < n, g ⟨0, by omega⟩ < g ⟨1, h⟩) : StrictMono g := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  have hn : 1 < n := by have := j.2; omega
  have hzo := h01 hn
  have hA : ∀ k : Fin n, (0 : ℕ) < k → g ⟨0, by omega⟩ < g k := by
    intro k hk
    by_cases hko : (k : ℕ) = 1
    · have : k = ⟨1, hn⟩ := Fin.ext hko
      rw [this]; exact hzo
    · rcases hg ⟨0, by omega⟩ ⟨1, hn⟩ k (by rw [Fin.lt_def]; simp)
        (by rw [Fin.lt_def]; simp only; omega) with h | h
      · exact lt_trans hzo h.2
      · exact absurd (lt_trans h.2 hzo) (lt_irrefl _)
  by_cases hi : (i : ℕ) = 0
  · have : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [this]; exact hA j (by omega)
  · rcases hg ⟨0, by omega⟩ i j (by rw [Fin.lt_def]; simp only; omega) hij with h | h
    · exact h.2
    · exact absurd (lt_trans (hA i (by omega)) h.2) (lt_irrefl _)

/-- In a linear order, an injective "betweenness-monotone" sequence is strictly monotone or
strictly antitone. -/
theorem strictMono_or_strictAnti_of_btw {α : Type*} [LinearOrder α] {n : ℕ} (g : Fin n → α)
    (hinj : Function.Injective g)
    (hg : ∀ i j k : Fin n, i < j → j < k → (g i < g j ∧ g j < g k) ∨ (g k < g j ∧ g j < g i)) :
    StrictMono g ∨ StrictAnti g := by
  by_cases hn : 1 < n
  · have hne : g ⟨0, by omega⟩ ≠ g ⟨1, hn⟩ := hinj.ne (by simp [Fin.ext_iff])
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (strictMono_of_btw g hg fun _ => h)
    · right
      have := strictMono_of_btw (α := αᵒᵈ) (fun i => OrderDual.toDual (g i))
        (fun i j k hij hjk => by
          rcases hg i j k hij hjk with h' | h'
          · exact Or.inr ⟨h'.2, h'.1⟩
          · exact Or.inl ⟨h'.2, h'.1⟩) (fun _ => h)
      exact fun i j hij => this hij
  · left
    intro i j hij
    have := j.2; have : (i : ℕ) < j := hij
    omega

end OrderLin

/-! ## The restriction of a space geometry to one of its planes -/

section PlaneRestriction

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]

/-- The points and lines of the plane `α`: the subtypes `{A // A ∈ α}` and
`{a // LiesInPlane a α}`, with the incidence of space. -/
instance planeHasLines (α : Pl) :
    HasLines {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} :=
  ⟨fun A a => (A : P) ∈ (a : L)⟩

/-- Betweenness of the points of the plane `α`: betweenness in space. -/
instance planeHasBetween [HasBetween P] (α : Pl) : HasBetween {A : P // A ∈ α} :=
  ⟨fun A B C => Between (A : P) B C⟩

theorem restrict_mem_iff {α : Pl} {A : {A : P // A ∈ α}}
    {a : {a : L // LiesInPlane (Point := P) a α}} : A ∈ a ↔ (A : P) ∈ (a : L) := Iff.rfl

theorem restrict_between_iff [HasBetween P] {α : Pl} {A B C : {A : P // A ∈ α}} :
    Between A B C ↔ Between (A : P) B C := Iff.rfl

theorem collinear_of_restrict {α : Pl} {A B C : {A : P // A ∈ α}} (h : Collinear A B C) :
    Collinear (A : P) B C := by
  obtain ⟨a, hA, hB, hC⟩ := h
  exact ⟨a, hA, hB, hC⟩

theorem restrict_vec_apply {α : Pl} (A B C D : {A : P // A ∈ α}) (i : Fin 4) :
    ((![A, B, C, D] i : {A : P // A ∈ α}) : P) = ![(A : P), B, C, D] i := by
  fin_cases i <;> rfl

/-- Crossing a line of the plane `α`, read in the plane or in space. -/
theorem restrict_cross_iff [HasBetween P] {α : Pl} {A B : {A : P // A ∈ α}}
    {a : {a : L // LiesInPlane (Point := P) a α}} :
    (∃ X : {A : P // A ∈ α}, X ∈ a ∧ Between A X B) ↔ ∃ X : P, X ∈ (a : L) ∧ Between (A : P) X B :=
  ⟨fun ⟨X, hX, hb⟩ => ⟨X, hX, hb⟩, fun ⟨X, hX, hb⟩ => ⟨⟨X, a.2 X hX⟩, hX, hb⟩⟩

theorem restrict_sameSide_iff [HasBetween P] {α : Pl} {A B : {A : P // A ∈ α}}
    {a : {a : L // LiesInPlane (Point := P) a α}} :
    SameSide a A B ↔ SameSide (a : L) (A : P) B := by
  unfold SameSide
  rw [restrict_cross_iff]
  rfl

theorem restrict_opp_iff [HasBetween P] {α : Pl} {A B : {A : P // A ∈ α}}
    {a : {a : L // LiesInPlane (Point := P) a α}} :
    OppositeSides a A B ↔ OppositeSides (a : L) (A : P) B := by
  unfold OppositeSides
  rw [restrict_cross_iff]
  rfl

variable [hS : SpaceConnection P L Pl]
include hS

theorem restrict_collinear_iff {α : Pl} {A B C : {A : P // A ∈ α}} :
    Collinear A B C ↔ Collinear (A : P) B C := by
  refine ⟨collinear_of_restrict, fun ⟨g, hA, hB, hC⟩ => ?_⟩
  by_cases hAB : (A : P) = B
  · by_cases hAC : (A : P) = C
    · obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
      have hD : ∃ D : P, D ∈ α ∧ D ≠ (A : P) := by
        by_contra hno
        simp only [not_exists, not_and, not_not] at hno
        exact hn ⟨g, by rw [hno X hX]; exact hA, by rw [hno Y hY]; exact hA,
          by rw [hno Z hZ]; exact hA⟩
      obtain ⟨D, hDα, hDA⟩ := hD
      obtain ⟨d, hAd, hDd⟩ := exists_line (Line := L) (Ne.symm hDA)
      exact ⟨⟨d, liesInPlane_of_mem (Ne.symm hDA) hAd hDd A.2 hDα⟩, hAd,
        by show (B : P) ∈ d; rw [← hAB]; exact hAd, by show (C : P) ∈ d; rw [← hAC]; exact hAd⟩
    · exact ⟨⟨g, liesInPlane_of_mem hAC hA hC A.2 C.2⟩, hA, hB, hC⟩
  · exact ⟨⟨g, liesInPlane_of_mem hAB hA hB A.2 B.2⟩, hA, hB, hC⟩

/-- **The points and lines of a plane of space satisfy group I of plane geometry**. -/
instance planeConnection (α : Pl) :
    PlaneConnection {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} where
  ax_I1 A B h := by
    have h' : (A : P) ≠ B := fun e => h (Subtype.ext e)
    obtain ⟨g, hA, hB⟩ := exists_line (Line := L) h'
    exact ⟨⟨g, liesInPlane_of_mem h' hA hB A.2 B.2⟩, hA, hB⟩
  ax_I2 A B a b h hA hB hA' hB' :=
    Subtype.ext (line_unique (fun e => h (Subtype.ext e)) hA hB hA' hB')
  ax_I7_line a := by
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) (a : L)
    exact ⟨⟨A, a.2 A hA⟩, ⟨B, a.2 B hB⟩, fun e => hAB (congrArg Subtype.val e), hA, hB⟩
  ax_I7_noncollinear := by
    obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
    exact ⟨⟨X, hX⟩, ⟨Y, hY⟩, ⟨Z, hZ⟩, fun h => hn (collinear_of_restrict h)⟩

omit hS in
theorem restrict_axiomIII {α : Pl} (h : AxiomIIISpace P) : AxiomIII {A : P // A ∈ α} := by
  intro a A hA
  have meets_iff : ∀ b c : {a : L // LiesInPlane (Point := P) a α},
      Meets (Point := {A : P // A ∈ α}) b c ↔ Meets (Point := P) (b : L) (c : L) := fun b c =>
    ⟨fun ⟨X, h1, h2⟩ => ⟨X, h1, h2⟩, fun ⟨X, h1, h2⟩ => ⟨⟨X, b.2 X h1⟩, h1, h2⟩⟩
  obtain ⟨b, ⟨hbα, hAb, hb⟩, hu⟩ := h α a A a.2 A.2 hA
  refine ⟨⟨b, hbα⟩, ⟨hAb, (meets_iff _ _).not.2 hb⟩, fun c ⟨hAc, hc⟩ => ?_⟩
  exact Subtype.ext (hu c ⟨c.2, hAc, (meets_iff _ _).not.1 hc⟩)

variable [HasBetween P] {α : Pl}

theorem restrict_betweenOnLine (h : BetweenOnLine P) : BetweenOnLine {A : P // A ∈ α} := by
  intro A B C hb
  obtain ⟨h1, h2, h3, h4⟩ := h A B C hb
  exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e),
    fun e => h3 (congrArg Subtype.val e), (restrict_collinear_iff (L := L)).2 h4⟩

omit hS in
theorem restrict_axiomII1 (h : AxiomII1 P) : AxiomII1 {A : P // A ∈ α} :=
  fun A B C hc hb => h A B C (collinear_of_restrict hc) hb

theorem restrict_axiomII2 (hB : BetweenOnLine P) (h : AxiomII2 P) :
    AxiomII2 {A : P // A ∈ α} := by
  intro A C a hA hC hAC
  have hAC' : (A : P) ≠ C := fun e => hAC (Subtype.ext e)
  obtain ⟨⟨B, hb⟩, ⟨D, hd⟩⟩ := h A C a hA hC hAC'
  have hBa : B ∈ (a : L) :=
    mem_of_collinear (hB _ _ _ hb).2.2.2.swap23 (hB _ _ _ hb).2.1 hA hC
  have hDa : D ∈ (a : L) :=
    mem_of_collinear (hB _ _ _ hd).2.2.2 (hB _ _ _ hd).1 hA hC
  exact ⟨⟨⟨B, a.2 B hBa⟩, hb⟩, ⟨⟨D, a.2 D hDa⟩, hd⟩⟩

omit hS in
theorem restrict_axiomII3 (h : AxiomII3 P) : AxiomII3 {A : P // A ∈ α} := by
  intro A B C hc hAB hAC hBC
  exact h A B C (collinear_of_restrict hc) (fun e => hAB (Subtype.ext e))
    (fun e => hAC (Subtype.ext e)) (fun e => hBC (Subtype.ext e))

omit hS in
theorem restrict_axiomII4 (h : AxiomII4 P) : AxiomII4 {A : P // A ∈ α} := by
  intro A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD
  obtain ⟨σ, h1⟩ := h A B C D a hA hB hC hD (fun e => hAB (Subtype.ext e))
    (fun e => hAC (Subtype.ext e)) (fun e => hAD (Subtype.ext e)) (fun e => hBC (Subtype.ext e))
    (fun e => hBD (Subtype.ext e)) (fun e => hCD (Subtype.ext e))
  refine ⟨σ, ?_⟩
  simp only [restrict_between_iff, restrict_vec_apply]
  exact h1

theorem restrict_axiomII5 (h : AxiomII5Space P) : AxiomII5 {A : P // A ∈ α} := by
  intro A B C a hn hA hB hC hX
  have hn' : ¬Collinear (A : P) B C := fun hc => hn ((restrict_collinear_iff (L := L)).2 hc)
  rcases h A B C α a hn' A.2 B.2 C.2 a.2 hA hB hC (restrict_cross_iff.1 hX) with h' | h'
  · exact Or.inl (restrict_cross_iff.2 h')
  · exact Or.inr (restrict_cross_iff.2 h')

/-- The plane axioms of order without II 4, for the points of a plane of space. -/
theorem restrict_planeOrderCore (hB : BetweenOnLine P) (h1 : AxiomII1 P) (h2 : AxiomII2 P)
    (h3 : AxiomII3 P) (h5 : AxiomII5Space P) :
    PlaneOrderCore {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} where
  between_onLine := restrict_betweenOnLine hB
  ax_II1 := restrict_axiomII1 h1
  ax_II2 := restrict_axiomII2 hB h2
  ax_II3 := restrict_axiomII3 h3
  ax_II5 := restrict_axiomII5 h5

end PlaneRestriction

/-- **The points and lines of a plane of space satisfy groups I and II of plane geometry**. -/
instance planeOrder {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [HasBetween P] [h : SpaceOrder P L Pl] (α : Pl) :
    PlaneOrder {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} where
  between_onLine := restrict_betweenOnLine h.between_onLine
  ax_II1 := restrict_axiomII1 h.ax_II1
  ax_II2 := restrict_axiomII2 h.between_onLine h.ax_II2
  ax_II3 := restrict_axiomII3 h.ax_II3
  ax_II4 := restrict_axiomII4 h.ax_II4
  ax_II5 := restrict_axiomII5 h.ax_II5

/-- **The points and lines of a plane of space satisfy groups I and III of plane geometry**. -/
instance planeParallels {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
    [h : SpaceParallels P L Pl] (α : Pl) :
    PlaneParallels {A : P // A ∈ α} {a : L // LiesInPlane (Point := P) a α} where
  ax_III := restrict_axiomIII h.ax_III

/-! ## Incidence in space (I 1–7) -/

section SpaceIncidence

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]
  [hS : SpaceConnection P L Pl]
include hS

/-- A line and a point off it lie in a common plane (I 3, I 5, I 7). -/
theorem exists_plane_line_point {a : L} {A : P} (hA : A ∉ a) :
    ∃ α : Pl, LiesInPlane a α ∧ A ∈ α := by
  obtain ⟨B, C, hBC, hB, hC⟩ := exists_two_points (Point := P) a
  have hn : ¬Collinear A B C := fun h => hA (mem_of_collinear h.perm231 hBC hB hC)
  obtain ⟨α, hAα, hBα, hCα⟩ := exists_plane (Plane := Pl) hn
  exact ⟨α, liesInPlane_of_mem hBC hB hC hBα hCα, hAα⟩

/-- Every plane contains a point off any given line (I 7). -/
theorem exists_mem_plane_not_mem (α : Pl) (a : L) : ∃ Q : P, Q ∈ α ∧ Q ∉ a := by
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  by_cases hXa : X ∈ a
  · by_cases hYa : Y ∈ a
    · exact ⟨Z, hZ, fun hZa => hn ⟨a, hXa, hYa, hZa⟩⟩
    · exact ⟨Y, hY, hYa⟩
  · exact ⟨X, hX, hXa⟩

/-- If there is a plane at all, every line lies in a plane. -/
theorem exists_plane_of_line [Nonempty Pl] (a : L) : ∃ α : Pl, LiesInPlane a α := by
  obtain ⟨Q, -, hQ⟩ := exists_mem_plane_not_mem (P := P) (Classical.arbitrary Pl) a
  obtain ⟨α, ha, -⟩ := exists_plane_line_point hQ
  exact ⟨α, ha⟩

/-- Two distinct planes with a common point meet exactly in the points of a line (I 1, I 2, I 4,
I 5, I 6). -/
theorem planes_meet_in_line {α β : Pl} {A : P} (hαβ : α ≠ β) (hA : A ∈ α) (hA' : A ∈ β) :
    ∃ m : L, ∀ X : P, X ∈ m ↔ X ∈ α ∧ X ∈ β := by
  obtain ⟨B, hBA, hBα, hBβ⟩ := SpaceConnection.ax_I6 (Point := P) (Line := L) α β A hαβ hA hA'
  obtain ⟨m, hAm, hBm⟩ := exists_line (Line := L) hBA.symm
  refine ⟨m, fun X => ⟨fun hX => ⟨liesInPlane_of_mem hBA.symm hAm hBm hA hBα X hX,
    liesInPlane_of_mem hBA.symm hAm hBm hA' hBβ X hX⟩, fun ⟨hXα, hXβ⟩ => ?_⟩⟩
  by_contra hX
  exact hαβ (plane_unique (not_collinear_of_not_mem hAm hBm hBA.symm hX) hA hBα hXα hA' hBβ hXβ)

/-- Through three points `A`, `B`, `C`, two of which (`A ≠ C`) are distinct, passes a plane
(provided some plane `γ` exists). -/
theorem exists_plane_three (γ : Pl) {A B C : P} (hAC : A ≠ C) :
    ∃ β : Pl, A ∈ β ∧ B ∈ β ∧ C ∈ β := by
  by_cases hc : Collinear A B C
  · obtain ⟨g, hAg, hCg⟩ := exists_line (Line := L) hAC
    have hBg : B ∈ g := mem_of_collinear hc.swap23 hAC hAg hCg
    obtain ⟨Q, -, hQ⟩ := exists_mem_plane_not_mem (P := P) γ g
    obtain ⟨β, hg, -⟩ := exists_plane_line_point hQ
    exact ⟨β, hg A hAg, hg B hBg, hg C hCg⟩
  · exact exists_plane (Line := L) hc

end SpaceIncidence

/-! ## The sides of a line in a plane of space -/

namespace OrderSpace

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [hO : SpaceOrder P L Pl] {β : Pl} {m : L} {A B C : P}
include hO

theorem sameSide_trans (hm : LiesInPlane (Point := P) m β) (hA : A ∈ β) (hB : B ∈ β)
    (hC : C ∈ β) (h1 : SameSide m A B) (h2 : SameSide m B C) : SameSide m A C := by
  have := OrderCore.sameSide_trans (L := {a : L // LiesInPlane (Point := P) a β})
    (a := ⟨m, hm⟩) (A := ⟨A, hA⟩) (B := ⟨B, hB⟩) (C := ⟨C, hC⟩)
    (restrict_sameSide_iff.2 h1) (restrict_sameSide_iff.2 h2)
  exact restrict_sameSide_iff.1 this

theorem opp_of_sameSide_opp (hm : LiesInPlane (Point := P) m β) (hA : A ∈ β) (hB : B ∈ β)
    (hC : C ∈ β) (h1 : SameSide m A B) (h2 : OppositeSides m B C) : OppositeSides m A C := by
  have := OrderCore.opp_of_sameSide_opp (L := {a : L // LiesInPlane (Point := P) a β})
    (a := ⟨m, hm⟩) (A := ⟨A, hA⟩) (B := ⟨B, hB⟩) (C := ⟨C, hC⟩)
    (restrict_sameSide_iff.2 h1) (restrict_opp_iff.2 h2)
  exact restrict_opp_iff.1 this

theorem sameSide_of_opp_opp (hm : LiesInPlane (Point := P) m β) (hA : A ∈ β) (hB : B ∈ β)
    (hC : C ∈ β) (h1 : OppositeSides m A B) (h2 : OppositeSides m B C) : SameSide m A C := by
  have := OrderCore.sameSide_of_opp_opp (L := {a : L // LiesInPlane (Point := P) a β})
    (a := ⟨m, hm⟩) (A := ⟨A, hA⟩) (B := ⟨B, hB⟩) (C := ⟨C, hC⟩)
    (restrict_opp_iff.2 h1) (restrict_opp_iff.2 h2)
  exact restrict_sameSide_iff.1 this

end OrderSpace

end HilbertFoundations
