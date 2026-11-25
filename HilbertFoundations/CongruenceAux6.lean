import HilbertFoundations.CongruenceAux5

/-!
# Helper module for `Congruence.lean`: the regions of an angle (§ 6) and Axiom IV 3

This module contains no unit of Hilbert's text. With groups I and II of plane geometry
(`PlaneOrder`):

* `angle_exit`: the segment from an interior point of an angle to a point that is not interior
  meets the vertex or a side;
* `exterior_eq`: the exterior of an angle is the union of two open half-planes, each convex;
* `angle_regions_aux`: the two regions of § 6 with all their properties.

With the linear axioms (`LineOrder`): `segmentsMeetOnlyAt_iff_between` and its variant for the
points within the segments (the two readings of Axiom IV 3).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

section Regions

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : PlaneOrder P L]
  {A B O X Y Z : P}
include hO

/-- The vertex and the two sides of the angle `AOB`. -/
def AngleBoundary (A O B : P) : Set P := {X | X = O ∨ X ∈ ray O A ∨ X ∈ ray O B}

/-- One half of the exit lemma: `Y` on the line `OA` or beyond it. -/
theorem angle_exit_aux (hAO : A ≠ O) (hBO : B ≠ O) (_h : ¬Collinear A O B)
    (hX : X ∈ Interior (Line := L) A O B) (hYa : Y ∈ line (Line := L) O A hAO.symm ∨
      OppositeSides (line (Line := L) O A hAO.symm) Y B) (hYO : Y ≠ O) (hYA : Y ∉ ray O A) :
    ∃ Z, Z ∈ AngleBoundary A O B ∧ (Z = Y ∨ Between X Z Y) := by
  set a := line (Line := L) O A hAO.symm
  set b := line (Line := L) O B hBO.symm
  have hOa : O ∈ a := mem_line_left _
  have hAa : A ∈ a := mem_line_right _
  have hOb : O ∈ b := mem_line_left _
  have hBb : B ∈ b := mem_line_right _
  have hi := (interior_iff (L := L) hAO hBO).1 hX
  have hBa : B ∉ a := hi.1.2.1
  have hAb : A ∉ b := hi.2.2.1
  -- a point of `b` between `X` and a point `W` of `a` lies on the side `OB`
  have onk : ∀ W Z : P, W ∈ a → Z ∈ b → Between X Z W → Z ∈ ray O B := fun W Z hW hZ hb =>
    mem_ray_of_sameSide hOa (collinear_of_mem hOb hBb hZ)
      (fun e => hi.1.1 (by rw [e] at hb; exact mem_left_of_between hb hOa hW))
      (OrderCore.sameSide_trans (OrderCore.sameSide_symm hi.1)
        (OrderCore.sameSide_symm (sameSide_of_between_mem' hW hi.1.1 (between_symm hb))))
  -- from a point `W` of `a` opposite to `A`, the segment `XW` crosses `b` on the side `OB`
  have cross : ∀ W : P, W ∈ a → Between A O W → ∃ Z, Z ∈ ray O B ∧ Between X Z W := by
    intro W hW hAOW
    have o1 : OppositeSides b A W := opp_of_between_mem hOb hAb hAOW
    have o2 : OppositeSides b X W := OrderCore.opp_of_sameSide_opp hi.2 o1
    obtain ⟨-, -, Z, hZb, hZ⟩ := o2
    exact ⟨Z, onk W Z hW hZb hZ, hZ⟩
  rcases hYa with hYa | hYo
  · have hc : Collinear O A Y := collinear_of_mem hOa hAa hYa
    rcases mem_ray_or_between (L := L) hc hAO hYO with hr | hb
    · exact absurd hr hYA
    · obtain ⟨Z, hZr, hZ⟩ := cross Y hYa hb
      exact ⟨Z, Or.inr (Or.inr hZr), Or.inr hZ⟩
  · have o : OppositeSides a X Y :=
      OrderCore.opp_of_sameSide_opp hi.1 (OrderCore.opp_symm hYo)
    obtain ⟨-, -, W, hWa, hW⟩ := o
    by_cases hWO : W = O
    · exact ⟨W, Or.inl hWO, Or.inr hW⟩
    rcases mem_ray_or_between (L := L) (collinear_of_mem hOa hAa hWa) hAO hWO with hr | hb
    · exact ⟨W, Or.inr (Or.inl hr), Or.inr hW⟩
    · obtain ⟨Z, hZr, hZ⟩ := cross W hWa hb
      exact ⟨Z, Or.inr (Or.inr hZr), Or.inr (OrderLin.trans₂ hZ hW).1⟩

theorem angleBoundary_swap (A O B : P) : AngleBoundary A O B = AngleBoundary B O A := by
  ext X
  simp only [AngleBoundary, Set.mem_ofPred_eq]
  tauto

/-- **Exit lemma**: the segment from an interior point `X` of the angle `AOB` to a point `Y` that is
not interior contains a point of the vertex or of the sides (`Y` itself, or a point between). -/
theorem angle_exit (hAO : A ≠ O) (hBO : B ≠ O) (h : ¬Collinear A O B)
    (hX : X ∈ Interior (Line := L) A O B) (hY : Y ∉ Interior (Line := L) A O B) :
    ∃ Z, Z ∈ AngleBoundary A O B ∧ (Z = Y ∨ Between X Z Y) := by
  by_cases hYT : Y ∈ AngleBoundary A O B
  · exact ⟨Y, hYT, Or.inl rfl⟩
  simp only [AngleBoundary, Set.mem_ofPred_eq, not_or] at hYT
  obtain ⟨hYO, hYA, hYB⟩ := hYT
  by_cases c1 : Y ∈ line (Line := L) O A hAO.symm ∨
      OppositeSides (line (Line := L) O A hAO.symm) Y B
  · exact angle_exit_aux hAO hBO h hX c1 hYO hYA
  by_cases c2 : Y ∈ line (Line := L) O B hBO.symm ∨
      OppositeSides (line (Line := L) O B hBO.symm) Y A
  · have hX' : X ∈ Interior (Line := L) B O A := by rw [← interior_swap]; exact hX
    obtain ⟨Z, hZ, hZ'⟩ := angle_exit_aux hBO hAO (not_collinear_swap h) hX' c2 hYO hYB
    exact ⟨Z, by rw [angleBoundary_swap]; exact hZ, hZ'⟩
  push Not at c1 c2
  exfalso
  apply hY
  refine (interior_iff (L := L) hAO hBO).2 ⟨?_, ?_⟩
  · rcases sameSide_or_opp' c1.1 (interior_iff (L := L) hAO hBO |>.1 hX).1.2.1 with hs | ho
    · exact hs
    · exact absurd ho c1.2
  · rcases sameSide_or_opp' c2.1 (interior_iff (L := L) hAO hBO |>.1 hX).2.2.1 with hs | ho
    · exact hs
    · exact absurd ho c2.2

/-- A broken line joining a point of the interior of the angle with a point that is not interior,
in either order, has a point in common with the vertex or the sides. -/
theorem angle_brokenLine_meets (hAO : A ≠ O) (hBO : B ≠ O) (h : ¬Collinear A O B) {n : ℕ}
    (w : Fin (n + 1) → P)
    (hw : (w 0 ∈ Interior (Line := L) A O B ∧ w (Fin.last n) ∉ Interior (Line := L) A O B) ∨
      (w 0 ∉ Interior (Line := L) A O B ∧ w (Fin.last n) ∈ Interior (Line := L) A O B)) :
    (BrokenLinePoints w ∩ AngleBoundary A O B).Nonempty := by
  classical
  -- the first index at which membership in the interior differs from that of `w 0`
  set I := Interior (Line := L) A O B
  have hex : ∃ m : ℕ, ∃ h : m < n + 1, (w ⟨m, h⟩ ∈ I ↔ ¬(w 0 ∈ I)) := by
    refine ⟨n, by omega, ?_⟩
    have : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [this]
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun x => absurd x h2, fun x => absurd h1 x⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
  obtain ⟨hm, hwm⟩ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro e
    have : (⟨Nat.find hex, hm⟩ : Fin (n + 1)) = 0 := Fin.ext e
    rw [this] at hwm
    exact iff_not_self hwm
  have hprev : (w ⟨Nat.find hex - 1, by omega⟩ ∈ I ↔ w 0 ∈ I) := by
    by_contra hc
    refine Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨by omega, ?_⟩
    constructor
    · intro hu hw0; exact hc ⟨fun _ => hw0, fun _ => hu⟩
    · intro hw0; by_contra hu; exact hc ⟨fun x => absurd x hu, fun x => absurd x hw0⟩
  set U := w ⟨Nat.find hex - 1, by omega⟩
  set V := w ⟨Nat.find hex, hm⟩
  have e2 : (⟨Nat.find hex - 1, by omega⟩ : Fin n).succ = ⟨Nat.find hex, hm⟩ :=
    Fin.ext (by simp only [Fin.val_succ]; omega)
  have e1 : (⟨Nat.find hex - 1, by omega⟩ : Fin n).castSucc = ⟨Nat.find hex - 1, by omega⟩ :=
    Fin.ext (by simp)
  by_cases hU : U ∈ I
  · have hV : V ∉ I := fun hv => hwm.1 hv (hprev.1 hU)
    obtain ⟨Z, hZ, hZs⟩ := angle_exit hAO hBO h hU hV
    refine ⟨Z, ?_, hZ⟩
    rcases hZs with rfl | hb
    · exact Or.inl ⟨_, rfl⟩
    · refine Or.inr ⟨⟨Nat.find hex - 1, by omega⟩, ?_⟩
      rw [e1, e2]; exact hb
  · have hV : V ∈ I := hwm.2 (fun h0 => hU (hprev.2 h0))
    obtain ⟨Z, hZ, hZs⟩ := angle_exit hAO hBO h hV hU
    refine ⟨Z, ?_, hZ⟩
    rcases hZs with rfl | hb
    · exact Or.inl ⟨_, rfl⟩
    · refine Or.inr ⟨⟨Nat.find hex - 1, by omega⟩, ?_⟩
      rw [e1, e2]; exact between_symm hb

/-- The interior of an angle is convex. -/
theorem interior_convex (hAO : A ≠ O) (hBO : B ≠ O) (hX : X ∈ Interior (Line := L) A O B)
    (hY : Y ∈ Interior (Line := L) A O B) (h : Between X Z Y) : Z ∈ Interior (Line := L) A O B := by
  have i1 := (interior_iff (L := L) hAO hBO).1 hX
  have i2 := (interior_iff (L := L) hAO hBO).1 hY
  refine (interior_iff (L := L) hAO hBO).2 ⟨?_, ?_⟩
  · exact OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between
      (OrderCore.sameSide_trans i1.1 (OrderCore.sameSide_symm i2.1)) h)) i1.1
  · exact OrderCore.sameSide_trans (OrderCore.sameSide_symm (sameSide_of_between
      (OrderCore.sameSide_trans i1.2 (OrderCore.sameSide_symm i2.2)) h)) i1.2

/-- The open half-plane beyond the line `OA` (opposite to `B`). -/
def HalfBeyond (A O B : P) (hAO : A ≠ O) : Set P :=
  {X | OppositeSides (line (Line := L) O A hAO.symm) B X}

theorem halfBeyond_convex (hAO : A ≠ O) (hX : X ∈ HalfBeyond (L := L) A O B hAO)
    (hY : Y ∈ HalfBeyond (L := L) A O B hAO) (h : Between X Z Y) :
    Z ∈ HalfBeyond (L := L) A O B hAO := by
  have hXY := OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm hX) hY
  have hXZ := sameSide_of_between hXY h
  exact OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hXZ)
    (OrderCore.opp_symm hX))

/-- **The exterior is the union of two half-planes**: the points beyond `OA` (opposite to `B`) and
the points beyond `OB` (opposite to `A`). -/
theorem exterior_eq (hAO : A ≠ O) (hBO : B ≠ O) (h : ¬Collinear A O B) :
    Exterior (Line := L) A O B = HalfBeyond (L := L) A O B hAO ∪ HalfBeyond (L := L) B O A hBO := by
  set a := line (Line := L) O A hAO.symm
  set b := line (Line := L) O B hBO.symm
  have hOa : O ∈ a := mem_line_left _
  have hAa : A ∈ a := mem_line_right _
  have hOb : O ∈ b := mem_line_left _
  have hBb : B ∈ b := mem_line_right _
  have hBa : B ∉ a := fun hh => h (collinear_of_mem hAa hOa hh)
  have hAb : A ∉ b := fun hh => h (collinear_of_mem hh hOb hBb)
  ext X
  simp only [Exterior, HalfBeyond, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hXO, hXA, hXB, hXI⟩
    by_cases hXa : X ∈ a
    · rcases mem_ray_or_between (L := L) (collinear_of_mem hOa hAa hXa) hAO hXO with hr | hb
      · exact absurd hr hXA
      · exact Or.inr (opp_of_between_mem hOb hAb hb)
    by_cases hXb : X ∈ b
    · rcases mem_ray_or_between (L := L) (collinear_of_mem hOb hBb hXb) hBO hXO with hr | hb
      · exact absurd hr hXB
      · exact Or.inl (opp_of_between_mem hOa hBa hb)
    by_contra hc
    push Not at hc
    apply hXI
    refine (interior_iff (L := L) hAO hBO).2 ⟨?_, ?_⟩
    · rcases sameSide_or_opp' hXa hBa with hs | ho
      · exact hs
      · exact absurd (OrderCore.opp_symm ho) hc.1
    · rcases sameSide_or_opp' hXb hAb with hs | ho
      · exact hs
      · exact absurd (OrderCore.opp_symm ho) hc.2
  · rintro (ho | ho)
    · refine ⟨ne_of_mem_not_mem hOa ho.2.1, fun hr => ho.2.1 (mem_of_collinear
        (collinear_of_mem_ray hr) hAO.symm hOa hAa), fun hr => ?_, fun hi => ?_⟩
      · exact OrderCore.not_sameSide_of_opp ho (sameSide_of_ray hOa hBa hr)
      · exact OrderCore.not_sameSide_of_opp ho (OrderCore.sameSide_symm
          ((interior_iff (L := L) hAO hBO).1 hi).1)
    · refine ⟨ne_of_mem_not_mem hOb ho.2.1, fun hr => ?_, fun hr => ho.2.1 (mem_of_collinear
        (collinear_of_mem_ray hr) hBO.symm hOb hBb), fun hi => ?_⟩
      · exact OrderCore.not_sameSide_of_opp ho (sameSide_of_ray hOb hAb hr)
      · exact OrderCore.not_sameSide_of_opp ho (OrderCore.sameSide_symm
          ((interior_iff (L := L) hAO hBO).1 hi).2)
/-- **The two regions of an angle** (§ 6), with all the properties Hilbert lists. -/
theorem angle_regions_aux (hAO : A ≠ O) (hBO : B ≠ O) (h : ¬Collinear A O B) :
    let I := Interior (Line := L) A O B
    let E := Exterior (Line := L) A O B
    let T := AngleBoundary A O B
    I.Nonempty ∧ E.Nonempty ∧ Disjoint I E ∧ I ∪ E = Tᶜ ∧
    (∀ X ∈ I, ∀ Y ∈ E, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = X → w (Fin.last n) = Y →
      (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ E, ∀ Y ∈ I, ∀ (n : ℕ) (w : Fin (n + 1) → P), w 0 = X → w (Fin.last n) = Y →
      (BrokenLinePoints w ∩ T).Nonempty) ∧
    (∀ X ∈ I, ∀ X' ∈ I, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = X ∧
      w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X ∈ E, ∀ X' ∈ E, ∃ (n : ℕ) (w : Fin (n + 1) → P), IsBrokenLine w ∧ w 0 = X ∧
      w (Fin.last n) = X' ∧ Disjoint (BrokenLinePoints w) T) ∧
    (∀ X Y Z, X ∈ I → Y ∈ I → Between X Z Y → Z ∈ I) ∧
    ¬(∀ X Y Z, X ∈ E → Y ∈ E → Between X Z Y → Z ∈ E) := by
  intro I E T
  set a := line (Line := L) O A hAO.symm
  set b := line (Line := L) O B hBO.symm
  have hOa : O ∈ a := mem_line_left _
  have hAa : A ∈ a := mem_line_right _
  have hOb : O ∈ b := mem_line_left _
  have hBb : B ∈ b := mem_line_right _
  have hBa : B ∉ a := fun hh => h (collinear_of_mem hAa hOa hh)
  have hAb : A ∉ b := fun hh => h (collinear_of_mem hh hOb hBb)
  have hAB : A ≠ B := fun e => hBa (e ▸ hAa)
  have hE := exterior_eq (L := L) hAO hBO h
  -- the boundary is disjoint from the interior and from the exterior
  have hIT : Disjoint I T := by
    refine Set.disjoint_left.2 fun X hX hXT => ?_
    have hi := (interior_iff (L := L) hAO hBO).1 hX
    rcases hXT with rfl | hr | hr
    · exact hi.1.1 hOa
    · exact hi.1.1 (mem_of_collinear (collinear_of_mem_ray hr) hAO.symm hOa hAa)
    · exact hi.2.1 (mem_of_collinear (collinear_of_mem_ray hr) hBO.symm hOb hBb)
  have hET : Disjoint E T := by
    refine Set.disjoint_left.2 fun X hX hXT => ?_
    obtain ⟨hXO, hXA, hXB, -⟩ := hX
    rcases hXT with rfl | hr | hr
    · exact hXO rfl
    · exact hXA hr
    · exact hXB hr
  have hIE : Disjoint I E := Set.disjoint_left.2 fun X hX hXE => hXE.2.2.2 hX
  have convI : ∀ X Y Z, X ∈ I → Y ∈ I → Between X Z Y → Z ∈ I := fun X Y Z hX hY hb =>
    interior_convex hAO hBO hX hY hb
  -- the two half-planes making up the exterior
  set H1 := HalfBeyond (L := L) A O B hAO
  set H2 := HalfBeyond (L := L) B O A hBO
  have convH1 : ∀ X Y Z, X ∈ H1 → Y ∈ H1 → Between X Z Y → Z ∈ H1 :=
    fun X Y Z hX hY hb => halfBeyond_convex hAO hX hY hb
  have convH2 : ∀ X Y Z, X ∈ H2 → Y ∈ H2 → Between X Z Y → Z ∈ H2 :=
    fun X Y Z hX hY hb => halfBeyond_convex hBO hX hY hb
  have hH1E : H1 ⊆ E := fun X hX => by rw [show E = H1 ∪ H2 from hE]; exact Or.inl hX
  have hH2E : H2 ⊆ E := fun X hX => by rw [show E = H1 ∪ H2 from hE]; exact Or.inr hX
  have hH1T : Disjoint H1 T := Set.disjoint_of_subset_left hH1E hET
  have hH2T : Disjoint H2 T := Set.disjoint_of_subset_left hH2E hET
  -- a point beyond both lines
  obtain ⟨As, hAs⟩ := exists_beyond (Line := L) hAO
  obtain ⟨Bs, hBs⟩ := exists_beyond (Line := L) hBO
  have hAsa : As ∈ a := mem_right_of_between hAs hAa hOa
  have hBsb : Bs ∈ b := mem_right_of_between hBs hBb hOb
  have hAsBs : As ≠ Bs := by
    intro e
    have hAsO : As ≠ O := (ne23_of_between hAs).symm
    have hab : a ≠ b := fun e' => hBa (by rw [e']; exact hBb)
    exact hAsO (eq_of_mem_of_mem hab hAsa (by rw [e]; exact hBsb) hOa hOb)
  obtain ⟨Q, hQ⟩ := exists_between (Line := L) hAsBs
  have oBBs : OppositeSides a B Bs := opp_of_between_mem hOa hBa hBs
  have oAAs : OppositeSides b A As := opp_of_between_mem hOb hAb hAs
  have s1 : SameSide a Q Bs := sameSide_of_between_mem' hAsa oBBs.2.1 hQ
  have hQ1 : Q ∈ H1 := OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp s1 (OrderCore.opp_symm oBBs))
  have s2 : SameSide b Q As := sameSide_of_between_mem' hBsb oAAs.2.1 (between_symm hQ)
  have hQ2 : Q ∈ H2 := OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp s2 (OrderCore.opp_symm oAAs))
  -- points beyond the sides
  obtain ⟨X0, hX0⟩ := exists_beyond (Line := L) (Ne.symm hAB)
  obtain ⟨Y0, hY0⟩ := exists_beyond (Line := L) hAB
  have hX0E : X0 ∈ E := hH1E (opp_of_between_mem hAa hBa hX0)
  have hY0E : Y0 ∈ E := hH2E (opp_of_between_mem hBb hAb hY0)
  refine ⟨⟨_, mem_interior_of_between (L := L) h (exists_between (Line := L) hAB).choose_spec⟩,
    ⟨X0, hX0E⟩, hIE, ?_, ?_, ?_, ?_, ?_, convI, ?_⟩
  · ext X
    simp only [Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro (hX | hX)
      · exact Set.disjoint_left.1 hIT hX
      · exact Set.disjoint_left.1 hET hX
    · intro hXT
      by_cases hXI : X ∈ I
      · exact Or.inl hXI
      · right
        refine ⟨fun e => hXT (Or.inl e), fun hr => hXT (Or.inr (Or.inl hr)),
          fun hr => hXT (Or.inr (Or.inr hr)), hXI⟩
  · intro X hX Y hY n w h0 hn
    exact angle_brokenLine_meets hAO hBO h w (Or.inl ⟨h0 ▸ hX, hn ▸ hY.2.2.2⟩)
  · intro X hX Y hY n w h0 hn
    exact angle_brokenLine_meets hAO hBO h w (Or.inr ⟨h0 ▸ hX.2.2.2, hn ▸ hY⟩)
  · intro X hX X' hX'
    exact join_of_convex convI hIT hX hX'
  · intro X hX X' hX'
    have hX1 : X ∈ H1 ∪ H2 := by rw [← show E = H1 ∪ H2 from hE]; exact hX
    have hX'1 : X' ∈ H1 ∪ H2 := by rw [← show E = H1 ∪ H2 from hE]; exact hX'
    rcases hX1 with h1 | h2 <;> rcases hX'1 with h1' | h2'
    · exact join_of_convex convH1 hH1T h1 h1'
    · by_cases hX2 : X ∈ H2
      · exact join_of_convex convH2 hH2T hX2 h2'
      by_cases hX'1 : X' ∈ H1
      · exact join_of_convex convH1 hH1T h1 hX'1
      exact join_of_convex₂ convH1 convH2 hH1T hH2T h1 hQ1 hQ2 h2'
        (fun e => hX2 (e ▸ hQ2)) (fun e => hX'1 (e ▸ hQ1))
    · by_cases hX1 : X ∈ H1
      · exact join_of_convex convH1 hH1T hX1 h1'
      by_cases hX'2 : X' ∈ H2
      · exact join_of_convex convH2 hH2T h2 hX'2
      exact join_of_convex₂ convH2 convH1 hH2T hH1T h2 hQ2 hQ1 h1'
        (fun e => hX1 (e ▸ hQ1)) (fun e => hX'2 (e ▸ hQ2))
    · exact join_of_convex convH2 hH2T h2 h2'
  · intro hconv
    have hXAY : Between X0 A Y0 := (OrderLin.trans₁ (between_symm hX0) hY0).1
    have := hconv X0 Y0 A hX0E hY0E hXAY
    exact Set.disjoint_left.1 hET this (Or.inr (Or.inl (mem_ray_self' (L := L) hAO)))

/-- **The angle of a triangle contains the interior of the triangle** (§ 6): the interior points of
the triangle `V 0 V 1 V 2` (with side lines `ℓ`, Theorem 6) are interior points of each of its
angles. -/
theorem triInside_subset_interior {V : Fin 3 → P} {ℓ : Fin 3 → L} (hT : TriangleLines V ℓ)
    (i : Fin 3) : TriInside V ℓ ⊆ Interior (Line := L) (V (i + 1)) (V i) (V (i + 2)) := by
  intro X hX a b hOa hAa hOb hBb
  have hne1 : V i ≠ V (i + 1) := hT.vertex_ne (fin3_ne1 i).symm
  have hne2 : V i ≠ V (i + 2) := hT.vertex_ne (fin3_ne2 i).symm
  have e1 : a = ℓ (i + 2) := line_unique hne1 hOa hAa
    (by have := hT.mem₁ (i + 2); rwa [fin3_add21] at this)
    (by have := hT.mem₂ (i + 2); rwa [fin3_add22] at this)
  have e2 : b = ℓ (i + 1) := line_unique hne2 hOb hBb
    (by have := hT.mem₂ (i + 1); rwa [fin3_add12] at this)
    (by have := hT.mem₁ (i + 1); rwa [fin3_add11] at this)
  subst e1 e2
  exact ⟨hX (i + 2), hX (i + 1)⟩
/-- The interior of an angle only depends on its sides (plane geometry, groups I and II). -/
theorem mem_interior_of_rays_plane {A' B' : P} (hAO : A ≠ O) (hBO : B ≠ O)
    (hX : X ∈ Interior (Line := L) A O B) (hA' : A' ∈ ray O A) (hB' : B' ∈ ray O B) :
    X ∈ Interior (Line := L) A' O B' := by
  have hA'O := ne_of_mem_ray hA'
  have hB'O := ne_of_mem_ray hB'
  have hi := (interior_iff (L := L) hAO hBO).1 hX
  have e1 : line (Line := L) O A' hA'O.symm = line O A hAO.symm :=
    (eq_line hA'O.symm (mem_line_left (Line := L) hAO.symm)
      (mem_of_collinear (collinear_of_mem_ray hA') hAO.symm (mem_line_left _)
        (mem_line_right _))).symm
  have e2 : line (Line := L) O B' hB'O.symm = line O B hBO.symm :=
    (eq_line hB'O.symm (mem_line_left (Line := L) hBO.symm)
      (mem_of_collinear (collinear_of_mem_ray hB') hBO.symm (mem_line_left _)
        (mem_line_right _))).symm
  refine (interior_iff (L := L) hA'O hB'O).2 ⟨?_, ?_⟩
  · rw [e1]
    exact OrderCore.sameSide_trans hi.1 (sameSide_of_ray (mem_line_left _) hi.1.2.1 hB')
  · rw [e2]
    exact OrderCore.sameSide_trans hi.2 (sameSide_of_ray (mem_line_left _) hi.2.2.1 hA')

/-- **The interior is well defined on angles** (plane geometry): if `∠AOB` and `∠COD` are the same
angle, they have the same interior. -/
theorem interior_eq_of_sameAngle {C D : P} (hAO : A ≠ O) (hBO : B ≠ O)
    (hs : SameAngle (Line := L) A O B C D) :
    Interior (Line := L) A O B = Interior (Line := L) C O D := by
  have hA : A ∈ ray O A := mem_ray_self' (L := L) hAO
  have hB : B ∈ ray O B := mem_ray_self' (L := L) hBO
  rcases Set.pair_eq_pair_iff.1 hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hC : A ∈ ray O C := e1 ▸ hA
    have hD : B ∈ ray O D := e2 ▸ hB
    ext X
    exact ⟨fun h => mem_interior_of_rays_plane hAO hBO h (mem_ray_comm hC) (mem_ray_comm hD),
      fun h => mem_interior_of_rays_plane hC.1 hD.1 h hC hD⟩
  · have hD : A ∈ ray O D := e1 ▸ hA
    have hC : B ∈ ray O C := e2 ▸ hB
    rw [interior_swap (A := C)]
    ext X
    exact ⟨fun h => mem_interior_of_rays_plane hAO hBO h (mem_ray_comm hD) (mem_ray_comm hC),
      fun h => mem_interior_of_rays_plane hD.1 hC.1 h hD hC⟩

end Regions

section RegionsSpace

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [hO : SpaceOrder P L Pl] {A B O X : P}
include hO

/-- The interior of an angle only depends on its sides (a plane `α` of space). -/
theorem mem_interior_of_rays_space {α : Pl} {A' B' : P} (hO : O ∈ α) (hA : A ∈ α) (hB : B ∈ α)
    (hXα : X ∈ α) (hAO : A ≠ O) (hBO : B ≠ O) (hX : X ∈ Interior (Line := L) A O B)
    (hA' : A' ∈ ray O A) (hB' : B' ∈ ray O B) : X ∈ Interior (Line := L) A' O B' := by
  have hA'O := ne_of_mem_ray hA'
  have hB'O := ne_of_mem_ray hB'
  have hi := (interior_iff (L := L) hAO hBO).1 hX
  have la := liesInPlane_of_mem hAO.symm (mem_line_left (Line := L) hAO.symm) (mem_line_right _)
    hO hA
  have lb := liesInPlane_of_mem hBO.symm (mem_line_left (Line := L) hBO.symm) (mem_line_right _)
    hO hB
  have hA'α : A' ∈ α := la A' (mem_of_collinear (collinear_of_mem_ray hA') hAO.symm
    (mem_line_left _) (mem_line_right _))
  have hB'α : B' ∈ α := lb B' (mem_of_collinear (collinear_of_mem_ray hB') hBO.symm
    (mem_line_left _) (mem_line_right _))
  have e1 : line (Line := L) O A' hA'O.symm = line O A hAO.symm :=
    (eq_line hA'O.symm (mem_line_left (Line := L) hAO.symm)
      (mem_of_collinear (collinear_of_mem_ray hA') hAO.symm (mem_line_left _)
        (mem_line_right _))).symm
  have e2 : line (Line := L) O B' hB'O.symm = line O B hBO.symm :=
    (eq_line hB'O.symm (mem_line_left (Line := L) hBO.symm)
      (mem_of_collinear (collinear_of_mem_ray hB') hBO.symm (mem_line_left _)
        (mem_line_right _))).symm
  refine (interior_iff (L := L) hA'O hB'O).2 ⟨?_, ?_⟩
  · rw [e1]
    exact OrderSpace.sameSide_trans (Pl := Pl) la hXα hB hB'α hi.1
      (sameSide_of_ray (mem_line_left _) hi.1.2.1 hB')
  · rw [e2]
    exact OrderSpace.sameSide_trans (Pl := Pl) lb hXα hA hA'α hi.2
      (sameSide_of_ray (mem_line_left _) hi.2.2.1 hA')

/-- **The interior is well defined on angles** (a plane `α` of space). -/
theorem interior_eq_of_sameAngle_space {α : Pl} {C D : P} (hO : O ∈ α) (hA : A ∈ α)
    (hB : B ∈ α) (hAO : A ≠ O) (hBO : B ≠ O) (hs : SameAngle (Line := L) A O B C D) :
    {X | X ∈ α ∧ X ∈ Interior (Line := L) A O B} = {X | X ∈ α ∧ X ∈ Interior (Line := L) C O D} := by
  have hAr : A ∈ ray O A := mem_ray_self' (L := L) hAO
  have hBr : B ∈ ray O B := mem_ray_self' (L := L) hBO
  have la := liesInPlane_of_mem hAO.symm (mem_line_left (Line := L) hAO.symm) (mem_line_right _)
    hO hA
  have lb := liesInPlane_of_mem hBO.symm (mem_line_left (Line := L) hBO.symm) (mem_line_right _)
    hO hB
  have onA : ∀ Y, Y ∈ ray O A → Y ∈ α := fun Y hY => la Y (mem_of_collinear
    (collinear_of_mem_ray hY) hAO.symm (mem_line_left _) (mem_line_right _))
  have onB : ∀ Y, Y ∈ ray O B → Y ∈ α := fun Y hY => lb Y (mem_of_collinear
    (collinear_of_mem_ray hY) hBO.symm (mem_line_left _) (mem_line_right _))
  rcases Set.pair_eq_pair_iff.1 hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hC : A ∈ ray O C := e1 ▸ hAr
    have hD : B ∈ ray O D := e2 ▸ hBr
    have hCα := onA C (mem_ray_comm hC)
    have hDα := onB D (mem_ray_comm hD)
    ext X
    exact ⟨fun ⟨hX, h⟩ => ⟨hX, mem_interior_of_rays_space hO hA hB hX hAO hBO h (mem_ray_comm hC)
        (mem_ray_comm hD)⟩,
      fun ⟨hX, h⟩ => ⟨hX, mem_interior_of_rays_space hO hCα hDα hX hC.1 hD.1 h hC hD⟩⟩
  · have hD : A ∈ ray O D := e1 ▸ hAr
    have hC : B ∈ ray O C := e2 ▸ hBr
    have hCα := onB C (mem_ray_comm hC)
    have hDα := onA D (mem_ray_comm hD)
    rw [interior_swap (A := C)]
    ext X
    exact ⟨fun ⟨hX, h⟩ => ⟨hX, mem_interior_of_rays_space hO hA hB hX hAO hBO h (mem_ray_comm hD)
        (mem_ray_comm hC)⟩,
      fun ⟨hX, h⟩ => ⟨hX, mem_interior_of_rays_space hO hDα hCα hX hD.1 hC.1 h hD hC⟩⟩

end RegionsSpace

section IV3

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L] {A B C : P}
include hO

/-- **The reading of Axiom IV 3**: two segments `AB`, `BC` of a line have no common point but `B`
(extremities included) iff `B` lies between `A` and `C`. -/
theorem segmentsMeetOnlyAt_iff_between : SegmentsMeetOnlyAt (Line := L) A B C ↔ Between A B C := by
  constructor
  · rintro ⟨hc, hAB, hBC, hX⟩
    by_cases hAC : A = C
    · subst hAC
      exact absurd (hX A (Or.inl rfl) (Or.inr (Or.inl rfl))) hAB
    rcases between_trichotomy (Line := L) hc hAB hAC hBC with h | h | h
    · exact absurd (hX A (Or.inl rfl) (Or.inr (Or.inr h))) hAB
    · exact h
    · exact absurd (hX C (Or.inr (Or.inr h)) (Or.inr (Or.inl rfl))) hBC.symm
  · intro hb
    refine ⟨collinear_of_between hb, ne12_of_between hb, ne23_of_between hb, ?_⟩
    intro W hW1 hW2
    rcases hW1 with e | e | hW
    · rcases hW2 with e2 | e2 | h3
      · exact absurd (e.symm.trans e2) (ne12_of_between hb)
      · exact absurd (e.symm.trans e2) (ne13_of_between hb)
      · subst e; exact absurd h3 (not_between_swap12 hb)
    · exact e
    · rcases hW2 with e2 | e2 | h3
      · exact e2
      · subst e2; exact absurd hW (not_between_swap23 hb)
      · exact absurd h3 (not_between_swap12 (OrderLin.trans₂ hW hb).2)

/-- The same with the points *within* the segments (Hilbert's "points of a segment"): `AB` and `BC`
have no point in common iff `B` lies between `A` and `C`. -/
theorem segments_disjoint_iff_between :
    (Collinear A B C ∧ A ≠ B ∧ B ≠ C ∧ ∀ X, X ∈ Seg A B → X ∉ Seg B C) ↔ Between A B C := by
  constructor
  · rintro ⟨hc, hAB, hBC, hX⟩
    by_cases hAC : A = C
    · subst hAC
      obtain ⟨X, hX'⟩ := exists_between (Line := L) hAB
      exact absurd (between_symm hX') (hX X hX')
    rcases between_trichotomy (Line := L) hc hAB hAC hBC with h | h | h
    · obtain ⟨X, hX'⟩ := exists_between (Line := L) (Ne.symm hAB)
      exact absurd (OrderLin.trans₂ hX' h).1 (hX X (between_symm hX'))
    · exact h
    · obtain ⟨X, hX'⟩ := exists_between (Line := L) (Ne.symm hBC)
      exact absurd (between_symm hX')
        (hX X (between_symm (OrderLin.trans₂ (between_symm hX') (between_symm h)).1))
  · intro hb
    refine ⟨collinear_of_between hb, ne12_of_between hb, ne23_of_between hb, fun X h1 h2 => ?_⟩
    exact not_between_swap12 (OrderLin.trans₂ h1 hb).2 h2

end IV3


/-- In plane geometry (group I) every point lies on a line, unless all points coincide. -/
theorem plane_cases {P : Type u} {L : Type v} [HasLines P L] [PlaneConnection P L] :
    (∀ X : P, ∃ l : L, X ∈ l) ∨ ∀ X Y : P, X = Y := by
  by_cases h : ∃ X Y : P, X ≠ Y
  · left
    obtain ⟨X, Y, hXY⟩ := h
    intro Z
    by_cases hZX : Z = X
    · subst hZX
      obtain ⟨l, hl, -⟩ := exists_line (Line := L) hXY
      exact ⟨l, hl⟩
    · obtain ⟨l, hl, -⟩ := exists_line (Line := L) hZX
      exact ⟨l, hl⟩
  · right
    push Not at h
    exact h

/-- In plane geometry, two distinct points give a line through every point. -/
theorem line_through_of_ne {P : Type u} {L : Type v} [HasLines P L] [PlaneConnection P L]
    {X Y : P} (h : X ≠ Y) : ∀ Z : P, ∃ l : L, Z ∈ l := by
  rcases plane_cases (P := P) (L := L) with hl | e
  · exact hl
  · exact absurd (e X Y) h

end HilbertFoundations
