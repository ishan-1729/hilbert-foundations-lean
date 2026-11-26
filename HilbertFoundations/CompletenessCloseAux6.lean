import HilbertFoundations.CompletenessCloseAux5

/-!
# Helper module for `CompletenessClose.lean` (6): the extension by the real co-ordinate space

This module contains no unit of Hilbert's text.

* `CC.GIso`: an isomorphism of two systems of points, lines and planes, the congruences being
  compared on genuine segments and genuine angles only (and the congruence of segments of the first
  system being a relation between unordered pairs, `SegCongSwap`). `CC.GIso.spaceGeometry`: all
  axioms I–V are carried over by such an isomorphism — the axioms do not constrain the congruences
  on degenerate tuples beyond `SegCongSwap`.
* `CC.XPt e`, `CC.XLine e`, `CC.XPlane e`: for an embedding `e : CC.PreEmb P L Pl` into
  `Coord ℝ 3`, a copy of the real co-ordinate space in the universes of `P`, `L`, `Pl`, whose
  congruences are those of `Coord ℝ 3` on genuine segments and angles and those of `P` (through
  `e`) on the degenerate tuples. It is a geometry of space with I–V (`CC.xIso`), and `e` is a
  `SpaceEmbedding` into it (`CC.xEmb`).
* `CC.PreEmb.surjective_of_complete`: by the Axiom of Completeness, every point of `Coord ℝ 3` is
  the image of a point.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v w u' v' w'

/-- Two half-rays from `O` forming the same angle as a genuine angle form a genuine angle. -/
theorem not_collinear_of_sameAngle {P : Type u} {L : Type v} [HasLines P L] [HasBetween P]
    [LineOrder P L] {A O B C D : P} (h : ¬Collinear (Line := L) A O B) (hl : ∃ l : L, O ∈ l)
    (s : SameAngle (Line := L) A O B C D) : ¬Collinear (Line := L) C O D := by
  obtain ⟨hAO, hBO, -⟩ := ne_of_not_collinear (L := L) h hl
  have s' : ({ray (Line := L) O A, ray (Line := L) O B} : Set (Set P)) =
      {ray (Line := L) O C, ray (Line := L) O D} := s
  have hA : ray (Line := L) O A = ray (Line := L) O C ∨
      ray (Line := L) O A = ray (Line := L) O D := by
    have h1 : ray (Line := L) O A ∈
        ({ray (Line := L) O C, ray (Line := L) O D} : Set (Set P)) := by
      rw [← s']; exact Set.mem_insert _ _
    exact (Set.mem_insert_iff.1 h1).imp id Set.mem_singleton_iff.1
  have hB : ray (Line := L) O B = ray (Line := L) O C ∨
      ray (Line := L) O B = ray (Line := L) O D := by
    have h1 : ray (Line := L) O B ∈
        ({ray (Line := L) O C, ray (Line := L) O D} : Set (Set P)) := by
      rw [← s']; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact (Set.mem_insert_iff.1 h1).imp id Set.mem_singleton_iff.1
  have mA : A ∈ ray (Line := L) O A := mem_ray_self' (L := L) hAO
  have mB : B ∈ ray (Line := L) O B := mem_ray_self' (L := L) hBO
  have same : ∀ Z : P, A ∈ ray (Line := L) O Z → B ∈ ray (Line := L) O Z → False := by
    intro Z h1 h2
    have h3 : B ∈ ray (Line := L) O A := by rw [ray_eq_of_mem h1]; exact h2
    exact h (collinear_of_mem_ray h3).swap12
  rcases hA with eA | eA <;> rcases hB with eB | eB
  · rw [eA] at mA; rw [eB] at mB
    exact (same C mA mB).elim
  · rw [eA] at mA; rw [eB] at mB
    exact not_collinear_of_mem_rays h (mem_ray_comm mA) (mem_ray_comm mB)
  · rw [eA] at mA; rw [eB] at mB
    exact fun hc => not_collinear_of_mem_rays h (mem_ray_comm mA) (mem_ray_comm mB) hc.swap13
  · rw [eA] at mA; rw [eB] at mB
    exact (same D mA mB).elim

/-- An **isomorphism of systems** of points, lines and planes, the congruences being compared on
genuine segments and genuine angles only. -/
structure GIso (P' : Type u') (L' : Type v') (Pl' : Type w') (P : Type u) (L : Type v)
    (Pl : Type w) [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P'] [HasSegCong P']
    [HasAngCong P'] [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P]
    [HasAngCong P] where
  φ : P' ≃ P
  ψ : L' ≃ L
  χ : Pl' ≃ Pl
  mem : ∀ (A : P') (a : L'), A ∈ a ↔ φ A ∈ ψ a
  memP : ∀ (A : P') (α : Pl'), A ∈ α ↔ φ A ∈ χ α
  btw : ∀ A B C : P', Between A B C ↔ Between (φ A) (φ B) (φ C)
  seg : ∀ A B C D : P', A ≠ B → C ≠ D →
    (SegCong A B C D ↔ SegCong (φ A) (φ B) (φ C) (φ D))
  swap : SegCongSwap P'
  ang : ∀ A O B A' O' B' : P', ¬Collinear (Line := L) (φ A) (φ O) (φ B) →
    ¬Collinear (Line := L) (φ A') (φ O') (φ B') →
    (AngCong A O B A' O' B' ↔ AngCong (φ A) (φ O) (φ B) (φ A') (φ O') (φ B'))

namespace GIso

variable {P' : Type u'} {L' : Type v'} {Pl' : Type w'} {P : Type u} {L : Type v} {Pl : Type w}
  [HasLines P' L'] [HasPlanes P' Pl'] [HasBetween P'] [HasSegCong P'] [HasAngCong P']
  [HasLines P L] [HasPlanes P Pl] [HasBetween P] [HasSegCong P] [HasAngCong P]
  (g : GIso P' L' Pl' P L Pl)

theorem mem_symm (A : P') (a : L) : A ∈ g.ψ.symm a ↔ g.φ A ∈ a := by
  rw [g.mem, Equiv.apply_symm_apply]

theorem symm_mem (A : P) (a : L') : g.φ.symm A ∈ a ↔ A ∈ g.ψ a := by
  rw [g.mem, Equiv.apply_symm_apply]

theorem memP_symm (A : P') (α : Pl) : A ∈ g.χ.symm α ↔ g.φ A ∈ α := by
  rw [g.memP, Equiv.apply_symm_apply]

theorem symm_memP (A : P) (α : Pl') : g.φ.symm A ∈ α ↔ A ∈ g.χ α := by
  rw [g.memP, Equiv.apply_symm_apply]

theorem ne_iff {A B : P'} : g.φ A ≠ g.φ B ↔ A ≠ B := g.φ.injective.ne_iff

theorem collinear {A B C : P'} :
    Collinear (Line := L') A B C ↔ Collinear (Line := L) (g.φ A) (g.φ B) (g.φ C) :=
  ⟨fun ⟨a, h1, h2, h3⟩ => ⟨g.ψ a, (g.mem _ _).1 h1, (g.mem _ _).1 h2, (g.mem _ _).1 h3⟩,
    fun ⟨a, h1, h2, h3⟩ =>
      ⟨g.ψ.symm a, (g.mem_symm _ _).2 h1, (g.mem_symm _ _).2 h2, (g.mem_symm _ _).2 h3⟩⟩

theorem coplanar {A B C D : P'} :
    Coplanar (Plane := Pl') A B C D ↔ Coplanar (Plane := Pl) (g.φ A) (g.φ B) (g.φ C) (g.φ D) :=
  ⟨fun ⟨α, h1, h2, h3, h4⟩ =>
      ⟨g.χ α, (g.memP _ _).1 h1, (g.memP _ _).1 h2, (g.memP _ _).1 h3, (g.memP _ _).1 h4⟩,
    fun ⟨α, h1, h2, h3, h4⟩ =>
      ⟨g.χ.symm α, (g.memP_symm _ _).2 h1, (g.memP_symm _ _).2 h2, (g.memP_symm _ _).2 h3,
        (g.memP_symm _ _).2 h4⟩⟩

theorem meets {a b : L'} : Meets (Point := P') a b ↔ Meets (Point := P) (g.ψ a) (g.ψ b) :=
  ⟨fun ⟨X, h1, h2⟩ => ⟨g.φ X, (g.mem _ _).1 h1, (g.mem _ _).1 h2⟩,
    fun ⟨X, h1, h2⟩ => ⟨g.φ.symm X, (g.symm_mem _ _).2 h1, (g.symm_mem _ _).2 h2⟩⟩

theorem liesInPlane {a : L'} {α : Pl'} :
    LiesInPlane (Point := P') a α ↔ LiesInPlane (Point := P) (g.ψ a) (g.χ α) :=
  ⟨fun h _ hX => (g.symm_memP _ _).1 (h _ ((g.symm_mem _ _).2 hX)),
    fun h _ hX => (g.memP _ _).2 (h _ ((g.mem _ _).1 hX))⟩

theorem sameSidePt {O A B : P'} :
    SameSidePt (Line := L') O A B ↔ SameSidePt (Line := L) (g.φ O) (g.φ A) (g.φ B) :=
  ⟨fun ⟨h1, h2, h3, h4⟩ =>
      ⟨g.ne_iff.2 h1, g.ne_iff.2 h2, g.collinear.1 h3, fun h => h4 ((g.btw _ _ _).2 h)⟩,
    fun ⟨h1, h2, h3, h4⟩ =>
      ⟨g.ne_iff.1 h1, g.ne_iff.1 h2, g.collinear.2 h3, fun h => h4 ((g.btw _ _ _).1 h)⟩⟩

theorem mem_ray {O A X : P'} :
    X ∈ ray (Line := L') O A ↔ g.φ X ∈ ray (Line := L) (g.φ O) (g.φ A) :=
  g.sameSidePt

theorem ray_image (O A : P') :
    ray (Line := L) (g.φ O) (g.φ A) = g.φ '' ray (Line := L') O A := by
  ext Y
  constructor
  · intro h
    refine ⟨g.φ.symm Y, ?_, g.φ.apply_symm_apply Y⟩
    rw [g.mem_ray, Equiv.apply_symm_apply]
    exact h
  · rintro ⟨X, hX, rfl⟩
    exact g.mem_ray.1 hX

theorem sameAngle {A O B C D : P'} (h : SameAngle (Line := L') A O B C D) :
    SameAngle (Line := L) (g.φ A) (g.φ O) (g.φ B) (g.φ C) (g.φ D) := by
  have h' : ({ray (Line := L') O A, ray (Line := L') O B} : Set (Set P')) =
      {ray (Line := L') O C, ray (Line := L') O D} := h
  show ({ray (Line := L) (g.φ O) (g.φ A), ray (Line := L) (g.φ O) (g.φ B)} : Set (Set P)) =
    {ray (Line := L) (g.φ O) (g.φ C), ray (Line := L) (g.φ O) (g.φ D)}
  rw [g.ray_image, g.ray_image, g.ray_image, g.ray_image, ← Set.image_pair (Set.image g.φ),
    ← Set.image_pair (Set.image g.φ), h']

theorem segWithEnds {A B X : P'} :
    X ∈ SegWithEnds A B ↔ g.φ X ∈ SegWithEnds (g.φ A) (g.φ B) := by
  show (X = A ∨ X = B ∨ Between A X B) ↔
    (g.φ X = g.φ A ∨ g.φ X = g.φ B ∨ Between (g.φ A) (g.φ X) (g.φ B))
  rw [g.φ.injective.eq_iff, g.φ.injective.eq_iff, ← g.btw]

theorem segmentsMeetOnlyAt {A B C : P'} (h : SegmentsMeetOnlyAt (Line := L') A B C) :
    SegmentsMeetOnlyAt (Line := L) (g.φ A) (g.φ B) (g.φ C) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨g.collinear.1 h1, g.ne_iff.2 h2, g.ne_iff.2 h3, fun X hX hX' => ?_⟩
  have e := h4 (g.φ.symm X) (by rw [g.segWithEnds, Equiv.apply_symm_apply]; exact hX)
    (by rw [g.segWithEnds, Equiv.apply_symm_apply]; exact hX')
  rw [← e, Equiv.apply_symm_apply]

theorem sameSide {a : L'} {A B : P'} :
    SameSide a A B ↔ SameSide (g.ψ a) (g.φ A) (g.φ B) :=
  ⟨fun ⟨h1, h2, h3⟩ =>
      ⟨fun h => h1 ((g.mem _ _).2 h), fun h => h2 ((g.mem _ _).2 h), fun ⟨X, hX, hb⟩ =>
        h3 ⟨g.φ.symm X, (g.symm_mem _ _).2 hX, by
          rw [g.btw, Equiv.apply_symm_apply]; exact hb⟩⟩,
    fun ⟨h1, h2, h3⟩ =>
      ⟨fun h => h1 ((g.mem _ _).1 h), fun h => h2 ((g.mem _ _).1 h), fun ⟨X, hX, hb⟩ =>
        h3 ⟨g.φ X, (g.mem _ _).1 hX, (g.btw _ _ _).1 hb⟩⟩⟩

theorem interior {A O B X : P'} :
    X ∈ Interior (Line := L') A O B ↔ g.φ X ∈ Interior (Line := L) (g.φ A) (g.φ O) (g.φ B) := by
  constructor
  · intro h a b hO hA hO' hB
    have h1 := h (g.ψ.symm a) (g.ψ.symm b) ((g.mem_symm _ _).2 hO) ((g.mem_symm _ _).2 hA)
      ((g.mem_symm _ _).2 hO') ((g.mem_symm _ _).2 hB)
    have h2 := g.sameSide.1 h1.1
    have h3 := g.sameSide.1 h1.2
    rw [Equiv.apply_symm_apply] at h2 h3
    exact ⟨h2, h3⟩
  · intro h a b hO hA hO' hB
    have h1 := h (g.ψ a) (g.ψ b) ((g.mem _ _).1 hO) ((g.mem _ _).1 hA) ((g.mem _ _).1 hO')
      ((g.mem _ _).1 hB)
    exact ⟨g.sameSide.2 h1.1, g.sameSide.2 h1.2⟩

include g in
/-- **All axioms I–V are carried over by an isomorphism of systems.** -/
theorem spaceGeometry [hG : SpaceGeometry P L Pl] : SpaceGeometry P' L' Pl' := by
  -- group I
  have I1 : AxiomI1 P' := fun A B h => by
    obtain ⟨a, h1, h2⟩ := exists_line (Line := L) (g.ne_iff.2 h)
    exact ⟨g.ψ.symm a, (g.mem_symm _ _).2 h1, (g.mem_symm _ _).2 h2⟩
  have I2 : AxiomI2 P' := fun A B a b h hAa hBa hAb hBb =>
    g.ψ.injective (line_unique (g.ne_iff.2 h) ((g.mem _ _).1 hAa) ((g.mem _ _).1 hBa)
      ((g.mem _ _).1 hAb) ((g.mem _ _).1 hBb))
  have I7l : AxiomI7Line P' := fun a => by
    obtain ⟨A, B, h, hA, hB⟩ := exists_two_points (Point := P) (g.ψ a)
    exact ⟨g.φ.symm A, g.φ.symm B, g.φ.symm.injective.ne h, (g.symm_mem _ _).2 hA,
      (g.symm_mem _ _).2 hB⟩
  have hConn : Connection P' L' := ⟨I1, I2, I7l⟩
  have ncol : ∀ {A O B : P'}, ¬Collinear (Line := L') A O B →
      ¬Collinear (Line := L) (g.φ A) (g.φ O) (g.φ B) := fun h hc => h (g.collinear.2 hc)
  have I3 : AxiomI3 P' := fun A B C h => by
    obtain ⟨α, h1, h2, h3⟩ := exists_plane (Plane := Pl) (ncol h)
    exact ⟨g.χ.symm α, (g.memP_symm _ _).2 h1, (g.memP_symm _ _).2 h2, (g.memP_symm _ _).2 h3⟩
  have I4 : AxiomI4 P' := fun A B C α β h hA hB hC hA' hB' hC' =>
    g.χ.injective (plane_unique (ncol h) ((g.memP _ _).1 hA) ((g.memP _ _).1 hB)
      ((g.memP _ _).1 hC) ((g.memP _ _).1 hA') ((g.memP _ _).1 hB') ((g.memP _ _).1 hC'))
  have I5 : AxiomI5 P' := fun A B a α h hA hB hA' hB' X hX =>
    (g.memP _ _).2 (liesInPlane_of_mem (g.ne_iff.2 h) ((g.mem _ _).1 hA) ((g.mem _ _).1 hB)
      ((g.memP _ _).1 hA') ((g.memP _ _).1 hB') (g.φ X) ((g.mem _ _).1 hX))
  have I6 : AxiomI6 P' := fun α β A h hA hA' => by
    obtain ⟨B, hB, h1, h2⟩ := SpaceConnection.ax_I6 (Point := P) (Line := L) (Plane := Pl)
      (g.χ α) (g.χ β) (g.φ A) (g.χ.injective.ne h) ((g.memP _ _).1 hA) ((g.memP _ _).1 hA')
    exact ⟨g.φ.symm B, fun e => hB (by rw [← e, Equiv.apply_symm_apply]),
      (g.symm_memP _ _).2 h1, (g.symm_memP _ _).2 h2⟩
  have I7p : AxiomI7Plane P' := fun α => by
    obtain ⟨A, B, C, hA, hB, hC, hn⟩ :=
      SpaceConnection.ax_I7_plane (Point := P) (Line := L) (g.χ α)
    refine ⟨g.φ.symm A, g.φ.symm B, g.φ.symm C, (g.symm_memP _ _).2 hA, (g.symm_memP _ _).2 hB,
      (g.symm_memP _ _).2 hC, fun hc => hn ?_⟩
    have h1 := g.collinear.1 hc
    simpa only [Equiv.apply_symm_apply] using h1
  have I7s : AxiomI7Space P' := by
    obtain ⟨A, B, C, D, hn⟩ :=
      SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
    refine ⟨g.φ.symm A, g.φ.symm B, g.φ.symm C, g.φ.symm D, fun hc => hn ?_⟩
    have h1 := g.coplanar.1 hc
    simpa only [Equiv.apply_symm_apply] using h1
  have hSC : SpaceConnection P' L' Pl' :=
    { hConn with
      ax_I3 := I3, ax_I4 := I4, ax_I5 := I5, ax_I6 := I6, ax_I7_plane := I7p, ax_I7_space := I7s }
  -- group II
  have BL : BetweenOnLine P' := fun A B C h => by
    have h' := (g.btw _ _ _).1 h
    exact ⟨g.ne_iff.1 (ne12_of_between (Line := L) h'), g.ne_iff.1 (ne13_of_between (Line := L) h'),
      g.ne_iff.1 (ne23_of_between (Line := L) h'),
      g.collinear.2 (collinear_of_between (Line := L) h')⟩
  have II1 : AxiomII1 P' := fun A B C _ h =>
    (g.btw _ _ _).2 (between_symm (Line := L) ((g.btw _ _ _).1 h))
  have II2 : AxiomII2 P' := fun A C a _ _ h => by
    obtain ⟨B, hB⟩ := exists_between (Line := L) (g.ne_iff.2 h)
    obtain ⟨D, hD⟩ := exists_beyond (Line := L) (g.ne_iff.2 h)
    exact ⟨⟨g.φ.symm B, by rw [g.btw, Equiv.apply_symm_apply]; exact hB⟩,
      ⟨g.φ.symm D, by rw [g.btw, Equiv.apply_symm_apply]; exact hD⟩⟩
  have II3 : AxiomII3 P' := fun A B C hc hAB hAC hBC => by
    have h1 := LineOrder.ax_II3 (Line := L) (g.φ A) (g.φ B) (g.φ C) (g.collinear.1 hc)
      (g.ne_iff.2 hAB) (g.ne_iff.2 hAC) (g.ne_iff.2 hBC)
    simpa only [← g.btw] using h1
  have II4 : AxiomII4 P' := fun A B C D a hA hB hC hD hAB hAC hAD hBC hBD hCD => by
    obtain ⟨σ, h1, h2, h3, h4⟩ := LineOrder.ax_II4 (Line := L) (g.φ A) (g.φ B) (g.φ C) (g.φ D)
      (g.ψ a) ((g.mem _ _).1 hA) ((g.mem _ _).1 hB) ((g.mem _ _).1 hC) ((g.mem _ _).1 hD)
      (g.ne_iff.2 hAB) (g.ne_iff.2 hAC) (g.ne_iff.2 hAD) (g.ne_iff.2 hBC) (g.ne_iff.2 hBD)
      (g.ne_iff.2 hCD)
    have hv : ∀ i : Fin 4, ![g.φ A, g.φ B, g.φ C, g.φ D] i = g.φ (![A, B, C, D] i) := fun i => by
      fin_cases i <;> rfl
    simp only [hv] at h1 h2 h3 h4
    exact ⟨σ, (g.btw _ _ _).2 h1, (g.btw _ _ _).2 h2, (g.btw _ _ _).2 h3, (g.btw _ _ _).2 h4⟩
  have II5 : AxiomII5Space P' := fun A B C α a hn hA hB hC ha hAa hBa hCa hX => by
    obtain ⟨X, hX, hb⟩ := hX
    have h1 := SpaceOrder.ax_II5 (Line := L) (Plane := Pl) (g.φ A) (g.φ B) (g.φ C) (g.χ α) (g.ψ a)
      (ncol hn) ((g.memP _ _).1 hA) ((g.memP _ _).1 hB) ((g.memP _ _).1 hC) (g.liesInPlane.1 ha)
      (fun h => hAa ((g.mem _ _).2 h)) (fun h => hBa ((g.mem _ _).2 h))
      (fun h => hCa ((g.mem _ _).2 h)) ⟨g.φ X, (g.mem _ _).1 hX, (g.btw _ _ _).1 hb⟩
    rcases h1 with ⟨Y, hY, hb'⟩ | ⟨Y, hY, hb'⟩
    · exact Or.inl ⟨g.φ.symm Y, (g.symm_mem _ _).2 hY, by
        rw [g.btw, Equiv.apply_symm_apply]; exact hb'⟩
    · exact Or.inr ⟨g.φ.symm Y, (g.symm_mem _ _).2 hY, by
        rw [g.btw, Equiv.apply_symm_apply]; exact hb'⟩
  have hLO : LineOrder P' L' :=
    { hConn with
      between_onLine := BL, ax_II1 := II1, ax_II2 := II2, ax_II3 := II3, ax_II4 := II4 }
  have hSO : SpaceOrder P' L' Pl' := { hSC, hLO with ax_II5 := II5 }
  -- group III
  have III : AxiomIIISpace P' := fun α a A ha hA hAa => by
    obtain ⟨b, ⟨h1, h2, h3⟩, hu⟩ := SpaceParallels.ax_III (Line := L) (Plane := Pl) (g.χ α)
      (g.ψ a) (g.φ A) (g.liesInPlane.1 ha) ((g.memP _ _).1 hA) (fun h => hAa ((g.mem _ _).2 h))
    refine ⟨g.ψ.symm b, ⟨?_, (g.mem_symm _ _).2 h2, ?_⟩, ?_⟩
    · rw [g.liesInPlane, Equiv.apply_symm_apply]; exact h1
    · rw [g.meets, Equiv.apply_symm_apply]; exact h3
    · rintro c ⟨c1, c2, c3⟩
      rw [Equiv.eq_symm_apply]
      exact hu (g.ψ c) ⟨g.liesInPlane.1 c1, (g.mem _ _).1 c2, fun h => c3 (g.meets.2 h)⟩
  have hSP : SpaceParallels P' L' Pl' := { hSC with ax_III := III }
  -- group IV, segments
  have IV1 : AxiomIV1LayOff P' := fun A B A' C' hAB hAC => by
    obtain ⟨B', ⟨hs, hc⟩, hu⟩ := SegmentCongruence.ax_IV1 (Line := L) (g.φ A) (g.φ B) (g.φ A')
      (g.φ C') (g.ne_iff.2 hAB) (g.ne_iff.2 hAC)
    have hs' : SameSidePt (Line := L') A' C' (g.φ.symm B') := by
      rw [g.sameSidePt, Equiv.apply_symm_apply]; exact hs
    refine ⟨g.φ.symm B', ⟨hs', ?_⟩, ?_⟩
    · rw [g.seg A B A' (g.φ.symm B') hAB (Ne.symm hs'.2.1), Equiv.apply_symm_apply]; exact hc
    · rintro Y ⟨y1, y2⟩
      rw [Equiv.eq_symm_apply]
      exact hu (g.φ Y) ⟨g.sameSidePt.1 y1, (g.seg A B A' Y hAB (Ne.symm y1.2.1)).1 y2⟩
  have IV1r : AxiomIV1Refl P' := fun A B h =>
    (g.seg A B A B h h).2 (segCong_refl (Line := L) (g.ne_iff.2 h))
  have IV2 : AxiomIV2 P' := fun A B A' B' A'' B'' h h' h'' c1 c2 =>
    (g.seg A' B' A'' B'' h' h'').2 (SegmentCongruence.ax_IV2 (Line := L) (g.φ A) (g.φ B) (g.φ A')
      (g.φ B') (g.φ A'') (g.φ B'') (g.ne_iff.2 h) (g.ne_iff.2 h') (g.ne_iff.2 h'')
      ((g.seg A B A' B' h h').1 c1) ((g.seg A B A'' B'' h h'').1 c2))
  have n13 : ∀ X Y Z : P', SegmentsMeetOnlyAt (Line := L') X Y Z → X ≠ Z := by
    intro X Y Z m e
    subst e
    exact m.2.1 (m.2.2.2 X (Or.inl rfl) (Or.inr (Or.inl rfl)))
  have IV3 : AxiomIV3 P' := fun A B C A' B' C' m m' c1 c2 =>
    (g.seg A C A' C' (n13 _ _ _ m) (n13 _ _ _ m')).2 (SegmentCongruence.ax_IV3 (Line := L) (g.φ A)
      (g.φ B) (g.φ C) (g.φ A') (g.φ B') (g.φ C') (g.segmentsMeetOnlyAt m) (g.segmentsMeetOnlyAt m')
      ((g.seg A B A' B' m.2.1 m'.2.1).1 c1) ((g.seg B C B' C' m.2.2.1 m'.2.2.1).1 c2))
  have hSeg : SegmentCongruence P' L' :=
    { hLO with
      segCong_swap := g.swap, ax_IV1 := IV1, ax_IV1_refl := IV1r, ax_IV2 := IV2, ax_IV3 := IV3 }
  -- group IV, angles
  have hline : ∀ X : P, ∃ l : L, X ∈ l := fun X => line_through_space (Pl := Pl) X
  have wd : AngCongWellDefined P' := fun A O B C D A' O' B' C' D' h h' s s' c => by
    have h1 := ncol h
    have h1' := ncol h'
    have s1 := g.sameAngle s
    have s1' := g.sameAngle s'
    have h2 := not_collinear_of_sameAngle (L := L) h1 (hline _) s1
    have h2' := not_collinear_of_sameAngle (L := L) h1' (hline _) s1'
    exact (g.ang C O D C' O' D' h2 h2').2 (AngleCongruence.angCong_wd (Line := L) (g.φ A) (g.φ O)
      (g.φ B) (g.φ C) (g.φ D) (g.φ A') (g.φ O') (g.φ B') (g.φ C') (g.φ D') h1 h1' s1 s1'
      ((g.ang A O B A' O' B' h1 h1').1 c))
  have IV4r : AxiomIV4Refl P' := fun A O B h =>
    (g.ang A O B A O B (ncol h) (ncol h)).2 (angCong_refl (Line := L) (ncol h))
  have IV5 : AxiomIV5 P' := fun A O B A' O' B' A'' O'' B'' h h' h'' c1 c2 =>
    (g.ang A' O' B' A'' O'' B'' (ncol h') (ncol h'')).2 (AngleCongruence.ax_IV5 (Line := L)
      (g.φ A) (g.φ O) (g.φ B) (g.φ A') (g.φ O') (g.φ B') (g.φ A'') (g.φ O'') (g.φ B'') (ncol h)
      (ncol h') (ncol h'') ((g.ang A O B A' O' B' (ncol h) (ncol h')).1 c1)
      ((g.ang A O B A'' O'' B'' (ncol h) (ncol h'')).1 c2))
  have hAC : AngleCongruence P' L' :=
    { hLO with angCong_wd := wd, ax_IV4_refl := IV4r, ax_IV5 := IV5 }
  have IV4 : AxiomIV4LayOffSpace P' := fun A O B α' a' O' A' D' h ha hO' hA' hne hD hDa => by
    obtain ⟨B', hB', hB'a, hc, hint, hu⟩ := SpaceAngleCongruence.ax_IV4 (Line := L) (Plane := Pl)
      (g.φ A) (g.φ O) (g.φ B) (g.χ α') (g.ψ a') (g.φ O') (g.φ A') (g.φ D') (ncol h)
      (g.liesInPlane.1 ha) ((g.mem _ _).1 hO') ((g.mem _ _).1 hA') (g.ne_iff.2 hne)
      ((g.memP _ _).1 hD) (fun h => hDa ((g.mem _ _).2 h))
    have nB : ∀ Y : P, Y ∉ g.ψ a' → ¬Collinear (Line := L) (g.φ A') (g.φ O') Y := fun Y hY =>
      not_collinear_of_not_mem ((g.mem _ _).1 hA') ((g.mem _ _).1 hO') (g.ne_iff.2 hne) hY
    have nB' : ¬Collinear (Line := L) (g.φ A') (g.φ O') (g.φ (g.φ.symm B')) := by
      rw [Equiv.apply_symm_apply]; exact nB B' hB'a
    refine ⟨g.φ.symm B', (g.symm_memP _ _).2 hB', fun h => hB'a ((g.symm_mem _ _).1 h), ?_, ?_, ?_⟩
    · rw [g.ang A O B A' O' (g.φ.symm B') (ncol h) nB', Equiv.apply_symm_apply]; exact hc
    · intro X hX hXi
      rw [g.sameSide]
      refine hint (g.φ X) ((g.memP _ _).1 hX) ?_
      have h1 := g.interior.1 hXi
      rwa [Equiv.apply_symm_apply] at h1
    · intro B'' hB'' hB''a hc'' hint''
      have hB''a' : g.φ B'' ∉ g.ψ a' := fun h => hB''a ((g.mem _ _).2 h)
      have e := hu (g.φ B'') ((g.memP _ _).1 hB'') hB''a'
        ((g.ang A O B A' O' B'' (ncol h) (nB _ hB''a')).1 hc'') (fun Y hY hYi => by
          have hYi' : g.φ.symm Y ∈ Interior (Line := L') A' O' B'' := by
            rw [g.interior, Equiv.apply_symm_apply]; exact hYi
          have h1 := hint'' (g.φ.symm Y) ((g.symm_memP _ _).2 hY) hYi'
          have h2 := g.sameSide.1 h1
          rwa [Equiv.apply_symm_apply] at h2)
      ext X
      rw [g.mem_ray, g.mem_ray, e, Equiv.apply_symm_apply]
  have hSAC : SpaceAngleCongruence P' L' Pl' := { hSO, hAC with ax_IV4 := IV4 }
  have IV6 : AxiomIV6 P' := fun A B C A' B' C' t t' s1 s2 a => by
    have t1 : ¬Collinear (Line := L) (g.φ A) (g.φ B) (g.φ C) := ncol t
    have t1' : ¬Collinear (Line := L) (g.φ A') (g.φ B') (g.φ C') := ncol t'
    obtain ⟨nAB, nCB, nAC⟩ := ne_of_not_collinear (L := L) t1 (hline _)
    obtain ⟨nAB', nCB', nAC'⟩ := ne_of_not_collinear (L := L) t1' (hline _)
    have r := TriangleCongruence.ax_IV6 (Line := L) (g.φ A) (g.φ B) (g.φ C) (g.φ A') (g.φ B')
      (g.φ C') t1 t1' ((g.seg A B A' B' (g.ne_iff.1 nAB) (g.ne_iff.1 nAB')).1 s1)
      ((g.seg A C A' C' (g.ne_iff.1 nAC) (g.ne_iff.1 nAC')).1 s2)
      ((g.ang B A C B' A' C' (fun h => t1 h.swap12) (fun h => t1' h.swap12)).1 a)
    exact ⟨(g.ang A B C A' B' C' t1 t1').2 r.1,
      (g.ang A C B A' C' B' (fun h => t1 h.swap23) (fun h => t1' h.swap23)).2 r.2⟩
  have hTC : TriangleCongruence P' L' := { hSeg, hAC with ax_IV6 := IV6 }
  have hSCg : SpaceCongruence P' L' Pl' := { hSAC, hTC with }
  -- group V
  have V : AxiomV P' := fun A B h0 hs hc => by
    obtain ⟨n, hn⟩ := Archimedes.ax_V (Line := L) (fun n => g.φ (A n)) (g.φ B)
      ((g.btw _ _ _).1 h0) (fun n => (g.btw _ _ _).1 (hs n))
      (fun m n => (g.seg _ _ _ _ (BL _ _ _ (hs m)).1 (BL _ _ _ (hs n)).1).1 (hc m n))
    exact ⟨n, (g.btw _ _ _).2 hn⟩
  have hAr : Archimedes P' L' := { hLO with ax_V := V }
  exact { hSP, hSCg, hAr with }

end GIso

/-! ### The extension of a system by the real co-ordinate space -/

section Extension

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl] [HasBetween P]
  [HasSegCong P] [HasAngCong P]

/-- Collinearity is preserved and reflected by an embedding into `Coord ℝ 3`. -/
theorem PreEmb.collinear_iff [hG : SpaceGeometry P L Pl] (e : PreEmb P L Pl) (A B C : P) :
    Collinear (Line := CoordLine ℝ 3) (e.pt A) (e.pt B) (e.pt C) ↔ Collinear (Line := L) A B C := by
  constructor
  · intro hc
    have two : ∀ X Y : P, ∃ l : L, X ∈ l ∧ Y ∈ l := by
      intro X Y
      by_cases h : X = Y
      · subst h
        obtain ⟨l, hl⟩ := line_through_space (L := L) (Pl := Pl) X
        exact ⟨l, hl, hl⟩
      · exact exists_line (Line := L) h
    by_cases hAB : A = B
    · subst hAB
      obtain ⟨l, h1, h2⟩ := two A C
      exact ⟨l, h1, h1, h2⟩
    by_cases hAC : A = C
    · subst hAC
      obtain ⟨l, h1, h2⟩ := two A B
      exact ⟨l, h1, h2, h1⟩
    by_cases hBC : B = C
    · subst hBC
      obtain ⟨l, h1, h2⟩ := two A B
      exact ⟨l, h1, h2, h2⟩
    rcases between_trichotomy (Line := CoordLine ℝ 3) hc (e.pt_injective.ne hAB)
      (e.pt_injective.ne hAC) (e.pt_injective.ne hBC) with h | h | h
    · exact (collinear_of_between (Line := L) ((e.between_iff _ _ _).1 h)).swap12
    · exact collinear_of_between (Line := L) ((e.between_iff _ _ _).1 h)
    · exact (collinear_of_between (Line := L) ((e.between_iff _ _ _).1 h)).swap23
  · rintro ⟨a, h1, h2, h3⟩
    exact ⟨e.line a, (e.mem_iff _ _).2 h1, (e.mem_iff _ _).2 h2, (e.mem_iff _ _).2 h3⟩

/-- The points of the extension: the points of `Coord ℝ 3`, in the universe of `P`. -/
structure XPt (e : PreEmb P L Pl) : Type u where
  p : Coord ℝ 3

/-- The lines of the extension. -/
structure XLine (e : PreEmb P L Pl) : Type v where
  l : CoordLine ℝ 3

/-- The planes of the extension. -/
structure XPlane (e : PreEmb P L Pl) : Type w where
  pl : CoordPlane ℝ 3

variable (e : PreEmb P L Pl)

instance XPt.instHasLines : HasLines (XPt e) (XLine e) := ⟨fun A a => A.p ∈ a.l⟩

instance XPt.instHasPlanes : HasPlanes (XPt e) (XPlane e) := ⟨fun A α => A.p ∈ α.pl⟩

instance XPt.instHasBetween : HasBetween (XPt e) := ⟨fun A B C => Between A.p B.p C.p⟩

/-- Congruence of segments in the extension: that of `Coord ℝ 3` on genuine segments, that of the
original system on the degenerate tuples. -/
instance XPt.instHasSegCong : HasSegCong (XPt e) :=
  ⟨fun A B C D => (A ≠ B ∧ C ≠ D ∧ SegCong A.p B.p C.p D.p) ∨
    ((A = B ∨ C = D) ∧ ∃ a b c d : P, e.pt a = A.p ∧ e.pt b = B.p ∧ e.pt c = C.p ∧
      e.pt d = D.p ∧ SegCong a b c d)⟩

/-- Congruence of angles in the extension: that of `Coord ℝ 3` on genuine angles, that of the
original system on the degenerate tuples. -/
instance XPt.instHasAngCong : HasAngCong (XPt e) :=
  ⟨fun A O B A' O' B' =>
    (¬Collinear (Line := CoordLine ℝ 3) A.p O.p B.p ∧
      ¬Collinear (Line := CoordLine ℝ 3) A'.p O'.p B'.p ∧ AngCong A.p O.p B.p A'.p O'.p B'.p) ∨
    ((Collinear (Line := CoordLine ℝ 3) A.p O.p B.p ∨
        Collinear (Line := CoordLine ℝ 3) A'.p O'.p B'.p) ∧
      ∃ a o b a' o' b' : P, e.pt a = A.p ∧ e.pt o = O.p ∧ e.pt b = B.p ∧ e.pt a' = A'.p ∧
        e.pt o' = O'.p ∧ e.pt b' = B'.p ∧ AngCong a o b a' o' b')⟩

theorem xSeg_def (A B C D : XPt e) : SegCong A B C D ↔
    (A ≠ B ∧ C ≠ D ∧ SegCong A.p B.p C.p D.p) ∨
    ((A = B ∨ C = D) ∧ ∃ a b c d : P, e.pt a = A.p ∧ e.pt b = B.p ∧ e.pt c = C.p ∧
      e.pt d = D.p ∧ SegCong a b c d) := Iff.rfl

theorem xAng_def (A O B A' O' B' : XPt e) : AngCong A O B A' O' B' ↔
    (¬Collinear (Line := CoordLine ℝ 3) A.p O.p B.p ∧
      ¬Collinear (Line := CoordLine ℝ 3) A'.p O'.p B'.p ∧ AngCong A.p O.p B.p A'.p O'.p B'.p) ∨
    ((Collinear (Line := CoordLine ℝ 3) A.p O.p B.p ∨
        Collinear (Line := CoordLine ℝ 3) A'.p O'.p B'.p) ∧
      ∃ a o b a' o' b' : P, e.pt a = A.p ∧ e.pt o = O.p ∧ e.pt b = B.p ∧ e.pt a' = A'.p ∧
        e.pt o' = O'.p ∧ e.pt b' = B'.p ∧ AngCong a o b a' o' b') := Iff.rfl

theorem xPt_eq_iff (X Y : P) : (⟨e.pt X⟩ : XPt e) = ⟨e.pt Y⟩ ↔ X = Y :=
  ⟨fun h => e.pt_injective (congrArg XPt.p h), fun h => by rw [h]⟩

/-- The extension is isomorphic to `Coord ℝ 3` (on genuine segments and angles). -/
def xIso (hswap : SegCongSwap P) :
    GIso (XPt e) (XLine e) (XPlane e) (Coord ℝ 3) (CoordLine ℝ 3) (CoordPlane ℝ 3) where
  φ := ⟨XPt.p, XPt.mk, fun _ => rfl, fun _ => rfl⟩
  ψ := ⟨XLine.l, XLine.mk, fun _ => rfl, fun _ => rfl⟩
  χ := ⟨XPlane.pl, XPlane.mk, fun _ => rfl, fun _ => rfl⟩
  mem := fun _ _ => Iff.rfl
  memP := fun _ _ => Iff.rfl
  btw := fun _ _ _ => Iff.rfl
  seg := fun A B C D hAB hCD => by
    rw [xSeg_def]
    exact ⟨fun h => h.elim (fun h => h.2.2)
      (fun h => h.1.elim (fun k => absurd k hAB) (fun k => absurd k hCD)),
      fun h => Or.inl ⟨hAB, hCD, h⟩⟩
  swap := by
    intro A B A' B' h
    rw [xSeg_def] at h
    rw [xSeg_def, xSeg_def]
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, a, b, c, d, ea, eb, ec, ed, hs⟩
    · exact ⟨Or.inl ⟨h1.symm, h2, segCong_swap_left (Line := CoordLine ℝ 3) h3⟩,
        Or.inl ⟨h1, h2.symm, segCong_swap_right (Line := CoordLine ℝ 3) h3⟩⟩
    · have hs' := hswap a b c d hs
      exact ⟨Or.inr ⟨h1.imp Eq.symm id, b, a, c, d, eb, ea, ec, ed, hs'.1⟩,
        Or.inr ⟨h1.imp id Eq.symm, a, b, d, c, ea, eb, ed, ec, hs'.2⟩⟩
  ang := fun A O B A' O' B' h h' => by
    rw [xAng_def]
    exact ⟨fun c => c.elim (fun c => c.2.2)
      (fun c => c.1.elim (fun k => absurd k h) (fun k => absurd k h')),
      fun c => Or.inl ⟨h, h', c⟩⟩

/-- **The original system is embedded into the extension.** -/
def xEmb [hG : SpaceGeometry P L Pl] :
    SpaceEmbedding P L Pl (XPt e) (XLine e) (XPlane e) where
  pt := fun A => ⟨e.pt A⟩
  line := fun a => ⟨e.line a⟩
  plane := fun α => ⟨e.plane α⟩
  pt_injective := fun A B h => e.pt_injective (congrArg XPt.p h)
  line_injective := fun a b h => e.line_injective (congrArg XLine.l h)
  plane_injective := fun a b h => e.plane_injective (congrArg XPlane.pl h)
  mem_iff := fun A a => e.mem_iff A a
  memPlane_iff := fun A α => e.memPlane_iff A α
  between_iff := fun A B C => e.between_iff A B C
  segCong_iff := fun A B C D => by
    rw [xSeg_def]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨-, a, b, c, d, ea, eb, ec, ed, hs⟩)
      · exact (e.segCong_iff A B C D (fun h => h1 ((xPt_eq_iff e _ _).2 h))
          (fun h => h2 ((xPt_eq_iff e _ _).2 h))).1 h3
      · have e1 : a = A := e.pt_injective ea
        have e2 : b = B := e.pt_injective eb
        have e3 : c = C := e.pt_injective ec
        have e4 : d = D := e.pt_injective ed
        rw [e1, e2, e3, e4] at hs
        exact hs
    · intro h
      by_cases hd : A ≠ B ∧ C ≠ D
      · exact Or.inl ⟨fun k => hd.1 ((xPt_eq_iff e _ _).1 k), fun k => hd.2 ((xPt_eq_iff e _ _).1 k),
          (e.segCong_iff A B C D hd.1 hd.2).2 h⟩
      · refine Or.inr ⟨?_, A, B, C, D, rfl, rfl, rfl, rfl, h⟩
        by_cases hAB : A = B
        · exact Or.inl ((xPt_eq_iff e _ _).2 hAB)
        · refine Or.inr ((xPt_eq_iff e _ _).2 ?_)
          by_contra hCD
          exact hd ⟨hAB, hCD⟩
  angCong_iff := fun A O B A' O' B' => by
    rw [xAng_def]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨-, a, o, b, a', o', b', ea, eo, eb, ea', eo', eb', hs⟩)
      · exact (e.angCong_iff A O B A' O' B' (fun h => h1 ((e.collinear_iff A O B).2 h))
          (fun h => h2 ((e.collinear_iff A' O' B').2 h))).1 h3
      · have e1 : a = A := e.pt_injective ea
        have e2 : o = O := e.pt_injective eo
        have e3 : b = B := e.pt_injective eb
        have e4 : a' = A' := e.pt_injective ea'
        have e5 : o' = O' := e.pt_injective eo'
        have e6 : b' = B' := e.pt_injective eb'
        rw [e1, e2, e3, e4, e5, e6] at hs
        exact hs
    · intro h
      by_cases hd : ¬Collinear (Line := L) A O B ∧ ¬Collinear (Line := L) A' O' B'
      · exact Or.inl ⟨fun k => hd.1 ((e.collinear_iff A O B).1 k),
          fun k => hd.2 ((e.collinear_iff A' O' B').1 k),
          (e.angCong_iff A O B A' O' B' hd.1 hd.2).2 h⟩
      · refine Or.inr ⟨?_, A, O, B, A', O', B', rfl, rfl, rfl, rfl, rfl, rfl, h⟩
        by_cases hc : Collinear (Line := L) A O B
        · exact Or.inl ((e.collinear_iff A O B).2 hc)
        · refine Or.inr ((e.collinear_iff A' O' B').2 ?_)
          by_contra hc'
          exact hd ⟨hc, hc'⟩

/-- **Completeness: every point of `Coord ℝ 3` is the image of a point.** -/
theorem PreEmb.surjective_of_complete [hG : SpaceGeometry P L Pl] (hc : SpaceComplete P L Pl) :
    Function.Surjective e.pt := by
  have hX : SpaceGeometry (XPt e) (XLine e) (XPlane e) :=
    (xIso e (SegmentCongruence.segCong_swap (Line := L))).spaceGeometry
  intro Q
  obtain ⟨X, hX'⟩ := (hc (XPt e) (XLine e) (XPlane e) hX (xEmb e)).1 ⟨Q⟩
  exact ⟨X, congrArg XPt.p hX'⟩

end Extension

end CC

end HilbertFoundations
