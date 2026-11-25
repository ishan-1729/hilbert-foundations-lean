import HilbertFoundations.Congruence

/-!
# Helper module for `Pascal.lean`: isometries of a plane geometry with groups I–IV

This module contains no unit of Hilbert's text. It works in a plane geometry with the axioms
I 1–2, II, III, IV (`PlaneCongruence`, `PlaneParallels`); group III is only used from
`PascalAux2.lean` on.

* **Isometries** (`isom`): the permutations of the points that preserve the congruence of segments,
  a subgroup of `Equiv.Perm P`. They preserve collinearity, betweenness, lines, sides, half-rays and
  parallelism.
* **The isometry of a congruence of triangles** (`exists_isom_of_tri`): two triangles with
  congruent sides are related by an isometry; it is built point by point with Theorem 17 (existence
  of the corresponding point, `Frame.theorem17_exists`) and the uniqueness of a point with given
  distances from three non-collinear points (`Frame.eq_of_equidistant`).
* **Rigidity**: an isometry fixing three non-collinear points is the identity; an isometry fixing
  two points fixes their line.
* **Equidistant points** (`eqd_line`): the points equidistant from two distinct points form a line.
* **Reflections in lines** (`refl`): for each line `l` the unique isometry other than the identity
  fixing all points of `l`; it is an involution, its fixed points are the points of `l`, it
  exchanges the sides of `l`, and every isometry fixing two points of `l` is the identity or `refl l`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace Pas

universe u v

section Isometries

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L]
include hC

/-- `f` **preserves the congruence of segments**. -/
def PresCong (f : P → P) : Prop := ∀ X Y : P, X ≠ Y → SegCong X Y (f X) (f Y)

/-- The **isometries**: permutations of the points preserving the congruence of segments. -/
def isom : Subgroup (Equiv.Perm P) where
  carrier := {f | PresCong (f : P → P)}
  mul_mem' {f g} hf hg X Y h := by
    have h1 := hg X Y h
    have h2 := hf (g X) (g Y) (g.injective.ne h)
    exact segCong_trans (L := L) h (g.injective.ne h) (f.injective.ne (g.injective.ne h)) h1 h2
  one_mem' X Y h := segCong_refl (Line := L) h
  inv_mem' {f} hf X Y h := by
    have h1 := hf (f⁻¹ X) (f⁻¹ Y) ((f⁻¹).injective.ne h)
    rw [show f (f⁻¹ X) = X from f.apply_symm_apply X,
      show f (f⁻¹ Y) = Y from f.apply_symm_apply Y] at h1
    exact segCong_symm (L := L) ((f⁻¹).injective.ne h) h h1

theorem mem_isom {f : Equiv.Perm P} : f ∈ isom (L := L) ↔ PresCong (f : P → P) := Iff.rfl

theorem isom_cong {f : Equiv.Perm P} (hf : f ∈ isom (L := L)) {X Y : P} (h : X ≠ Y) :
    SegCong X Y (f X) (f Y) := hf X Y h

/-- A plane with two distinct points has a line through every point. -/
theorem hl_of_ne {X Y : P} (h : X ≠ Y) : ∀ Z : P, ∃ l : L, Z ∈ l := line_through_of_ne h

/-- The plane frame (all points form the plane). -/
noncomputable abbrev pf {X Y : P} (h : X ≠ Y) : Frame P L := planeFrame (hl_of_ne (L := L) h)

theorem pf_univ {X Y : P} (h : X ≠ Y) : (pf (L := L) h).IsPl Set.univ := rfl

variable {f : Equiv.Perm P}

/-- Isometries preserve collinearity. -/
theorem isom_collinear (hf : f ∈ isom (L := L)) {X Y Z : P} (h : Collinear (Line := L) X Y Z) :
    Collinear (Line := L) (f X) (f Y) (f Z) := by
  by_cases hXY : X = Y
  · subst hXY
    by_cases hXZ : X = Z
    · subst hXZ
      by_cases hall : ∃ W : P, W ≠ f X
      · obtain ⟨W, hW⟩ := hall
        obtain ⟨l, h1, -⟩ := exists_line (Line := L) hW.symm
        exact ⟨l, h1, h1, h1⟩
      · push Not at hall
        rw [← hall X]; exact h
    · exact (collinear_of_ne (Line := L) (f.injective.ne hXZ)).swap23
  by_cases hXZ : X = Z
  · subst hXZ; exact collinear_of_ne (Line := L) (f.injective.ne hXY)
  by_cases hYZ : Y = Z
  · subst hYZ; exact (collinear_of_ne (Line := L) (f.injective.ne hXY).symm).swap12
  exact (pf (L := L) hXY).collinear_of_segCong' h hXY hYZ hXZ (f.injective.ne hXY)
    (f.injective.ne hYZ) (f.injective.ne hXZ) (hf X Y hXY) (hf Y Z hYZ) (hf X Z hXZ)

/-- Isometries preserve betweenness. -/
theorem isom_between (hf : f ∈ isom (L := L)) {X Y Z : P} (h : Between X Y Z) :
    Between (f X) (f Y) (f Z) := by
  have hXY := ne12_of_between (Line := L) h
  have hYZ := ne23_of_between (Line := L) h
  have hXZ := ne13_of_between (Line := L) h
  exact between_of_segCong h (isom_collinear hf (collinear_of_between (Line := L) h))
    (f.injective.ne hXY) (f.injective.ne hYZ) (f.injective.ne hXZ) (hf X Y hXY) (hf Y Z hYZ)
    (hf X Z hXZ)

theorem isom_inv (hf : f ∈ isom (L := L)) : f⁻¹ ∈ isom (L := L) := (isom (L := L)).inv_mem hf

theorem isom_collinear_iff (hf : f ∈ isom (L := L)) {X Y Z : P} :
    Collinear (Line := L) (f X) (f Y) (f Z) ↔ Collinear (Line := L) X Y Z := by
  refine ⟨fun h => ?_, isom_collinear hf⟩
  have := isom_collinear (isom_inv hf) h
  simpa using this

theorem isom_between_iff (hf : f ∈ isom (L := L)) {X Y Z : P} :
    Between (f X) (f Y) (f Z) ↔ Between X Y Z := by
  refine ⟨fun h => ?_, isom_between hf⟩
  have := isom_between (isom_inv hf) h
  simpa using this

/-- Isometries map each line onto a line. -/
theorem isom_line (hf : f ∈ isom (L := L)) (l : L) : ∃ l' : L, ∀ Z : P, f Z ∈ l' ↔ Z ∈ l := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  refine ⟨line (f A) (f B) (f.injective.ne hAB), fun Z => ?_⟩
  rw [← collinear_iff_mem_line (L := L) (f.injective.ne hAB), isom_collinear_iff hf,
    collinear_iff_mem_line (L := L) hAB, ← eq_line hAB hA hB]

/-- The image of a line under an isometry (a chosen line through the images). -/
noncomputable def imLine (f : Equiv.Perm P) (hf : f ∈ isom (L := L)) (l : L) : L :=
  Classical.choose (isom_line hf l)

theorem mem_imLine (hf : f ∈ isom (L := L)) (l : L) (Z : P) : f Z ∈ imLine f hf l ↔ Z ∈ l :=
  Classical.choose_spec (isom_line hf l) Z

theorem mem_imLine' (hf : f ∈ isom (L := L)) (l : L) (Z : P) :
    Z ∈ imLine f hf l ↔ f⁻¹ Z ∈ l := by
  rw [← mem_imLine hf l (f⁻¹ Z)]; simp

/-- Isometries preserve the sides of a line. -/
theorem isom_sameSide (hf : f ∈ isom (L := L)) {l : L} {X Y : P} (h : SameSide l X Y) :
    SameSide (imLine f hf l) (f X) (f Y) := by
  refine ⟨fun h' => h.1 ((mem_imLine hf l X).1 h'), fun h' => h.2.1 ((mem_imLine hf l Y).1 h'),
    ?_⟩
  rintro ⟨Z, hZ, hb⟩
  rw [mem_imLine'] at hZ
  have : Between X (f⁻¹ Z) Y := by
    have := isom_between (isom_inv hf) hb
    simpa using this
  exact h.2.2 ⟨_, hZ, this⟩

theorem isom_opp (hf : f ∈ isom (L := L)) {l : L} {X Y : P} (h : OppositeSides l X Y) :
    OppositeSides (imLine f hf l) (f X) (f Y) := by
  obtain ⟨hX, hY, Z, hZ, hb⟩ := h
  exact ⟨fun h' => hX ((mem_imLine hf l X).1 h'), fun h' => hY ((mem_imLine hf l Y).1 h'),
    f Z, (mem_imLine hf l Z).2 hZ, isom_between hf hb⟩

/-- Isometries preserve half-rays. -/
theorem isom_ray (hf : f ∈ isom (L := L)) {O A X : P} (h : X ∈ ray O A) :
    f X ∈ ray (f O) (f A) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨f.injective.ne h1, f.injective.ne h2, isom_collinear hf h3,
    fun hb => h4 ((isom_between_iff hf).1 hb)⟩

/-- Isometries preserve parallelism (lines without common point). -/
theorem isom_meets_iff (hf : f ∈ isom (L := L)) {l m : L} :
    Meets (Point := P) (imLine f hf l) (imLine f hf m) ↔ Meets (Point := P) l m := by
  constructor
  · rintro ⟨Z, h1, h2⟩
    rw [mem_imLine'] at h1 h2
    exact ⟨_, h1, h2⟩
  · rintro ⟨Z, h1, h2⟩
    exact ⟨f Z, (mem_imLine hf l Z).2 h1, (mem_imLine hf m Z).2 h2⟩

end Isometries

section TriIso

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L]
include hC

theorem lineIn_univ (l : L) : LineIn (P := P) l Set.univ := fun _ _ => trivial

theorem not_mem_line_of_nc {A B X : P} (hAB : A ≠ B) (h : ¬Collinear (Line := L) A B X) :
    X ∉ line (Line := L) A B hAB :=
  fun hX => h (collinear_of_mem (mem_line_left hAB) (mem_line_right hAB) hX)

theorem nc_of_not_mem_line {A B X : P} (hAB : A ≠ B) (h : X ∉ line (Line := L) A B hAB) :
    ¬Collinear (Line := L) A B X :=
  fun hc => h ((collinear_iff_mem_line (L := L) hAB).1 hc)

/-- Two points on the same side of the line `AB` with the same distances from `A` and from `B`
coincide. -/
theorem eq_of_sameSide_equidistant {A B X Y : P} (hAB : A ≠ B)
    (hs : SameSide (line (Line := L) A B hAB) X Y) (hA : SegCong A X A Y) (hB : SegCong B X B Y) :
    X = Y := by
  let F := pf (L := L) hAB
  have nX := nc_of_not_mem_line hAB hs.1
  have nY := nc_of_not_mem_line hAB hs.2.1
  obtain ⟨a, -, -⟩ := F.sss nX nY (segCong_refl (Line := L) hAB) hA hB
  have hXA : X ≠ A := fun e => hs.1 (e ▸ mem_line_left hAB)
  have hYA : Y ≠ A := fun e => hs.2.1 (e ▸ mem_line_left hAB)
  have nX' : ¬Collinear (Line := L) B A X := fun h => nX h.swap12
  have nY' : ¬Collinear (Line := L) B A Y := fun h => nY h.swap12
  have r := F.layoff_unique Set.univ rfl B A X (line (Line := L) A B hAB) A B X Y nX'
    (lineIn_univ _) (mem_line_left hAB) (mem_line_right hAB) hAB.symm trivial trivial hs
    (angCong_refl (Line := L) nX') a
  have hX : X ∈ ray A Y := by rw [← r]; exact mem_ray_self' (L := L) hXA
  exact eq_of_segCong_ray' (L := L) hX (mem_ray_self' (L := L) hYA) hA

/-- **The isometry of a congruence of triangles**: two triangles whose corresponding sides are
congruent are related by an isometry. -/
theorem exists_isom_of_tri {A B C A' B' C' : P} (h : ¬Collinear (Line := L) A B C)
    (h' : ¬Collinear (Line := L) A' B' C') (hAB0 : A ≠ B) (sAB : SegCong A B A' B')
    (sAC : SegCong A C A' C') (sBC : SegCong B C B' C') :
    ∃ f ∈ isom (L := L), f A = A' ∧ f B = B' ∧ f C = C' := by
  let F := pf (L := L) hAB0
  obtain ⟨hAB, hCB, hAC⟩ := F.ne h
  obtain ⟨hAB', hCB', hAC'⟩ := F.ne h'
  let t : Fin 3 → P := ![A, B, C]
  let t' : Fin 3 → P := ![A', B', C']
  have ht : Function.Injective t := injective_fin3 hAB hAC hCB.symm
  have ht' : Function.Injective t' := injective_fin3 hAB' hAC' hCB'.symm
  have hseg : ∀ i j, i ≠ j → SegCong (t i) (t j) (t' i) (t' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [t, t'] at hij ⊢ <;>
      first
        | exact sAB
        | exact sAC
        | exact sBC
        | exact segCong_swap (L := L) sAB
        | exact segCong_swap (L := L) sAC
        | exact segCong_swap (L := L) sBC
  have tnc : ¬Collinear (Line := L) (t 0) (t 1) (t 2) := h
  have tnc' : ¬Collinear (Line := L) (t' 0) (t' 1) (t' 2) := h'
  have key : ∀ Q : P, (∀ i, Q ≠ t i) → ∃ Q', (∀ i, Q' ≠ t' i) ∧ ∀ i, SegCong (t i) Q (t' i) Q' := by
    intro Q hQ
    obtain ⟨Q', -, h1, h2⟩ := F.theorem17_exists (S := Set.univ) (S' := Set.univ) rfl rfl
      (fun _ => trivial) (fun _ => trivial) ht ht' hseg trivial hQ
    exact ⟨Q', h1, h2⟩
  -- uniqueness of a point with given distances from the three vertices
  have uniq : ∀ {Q Q1 Q2 : P}, (∀ i, Q ≠ t i) → (∀ i, Q1 ≠ t' i) → (∀ i, Q2 ≠ t' i) →
      (∀ i, SegCong (t i) Q (t' i) Q1) → (∀ i, SegCong (t i) Q (t' i) Q2) → Q1 = Q2 := by
    intro Q Q1 Q2 hQ h1 h2 s1 s2
    have s : ∀ i, SegCong (t' i) Q1 (t' i) Q2 := fun i =>
      SegmentCongruence.ax_IV2 (Line := L) (t i) Q (t' i) Q1 (t' i) Q2 (hQ i).symm (h1 i).symm
        (h2 i).symm (s1 i) (s2 i)
    exact F.eq_of_equidistant (S := Set.univ) rfl trivial trivial trivial trivial trivial tnc'
      (h1 0) (h1 1) (h1 2) (h2 0) (h2 1) (h2 2) (s 0) (s 1) (s 2)
  classical
  let g : P → P := fun Q =>
    if hQ : ∃ i, Q = t i then t' (Classical.choose hQ) else Classical.choose (key Q (by
      push Not at hQ; exact hQ))
  have g_t : ∀ i, g (t i) = t' i := by
    intro i
    have hQ : ∃ j, t i = t j := ⟨i, rfl⟩
    simp only [g, hQ, ↓reduceDIte]
    rw [ht (Classical.choose_spec hQ).symm]
  have g_off : ∀ Q, (∀ i, Q ≠ t i) → (∀ i, g Q ≠ t' i) ∧ ∀ i, SegCong (t i) Q (t' i) (g Q) := by
    intro Q hQ
    have hQ' : ¬∃ i, Q = t i := fun ⟨i, e⟩ => hQ i e
    simp only [g, hQ', ↓reduceDIte]
    exact Classical.choose_spec (key Q hQ)
  have g_eq : ∀ {Q Q' : P}, (∀ i, Q ≠ t i) → (∀ i, Q' ≠ t' i) →
      (∀ i, SegCong (t i) Q (t' i) Q') → g Q = Q' := fun hQ hQ' s =>
    uniq hQ (g_off _ hQ).1 hQ' (g_off _ hQ).2 s
  -- congruence of all segments
  have cong : ∀ Q R : P, Q ≠ R → SegCong Q R (g Q) (g R) := by
    intro Q R hQR
    by_cases hQ : ∃ i, Q = t i
    · obtain ⟨i, rfl⟩ := hQ
      by_cases hR : ∃ j, R = t j
      · obtain ⟨j, rfl⟩ := hR
        rw [g_t, g_t]
        exact hseg i j (fun e => hQR (by rw [e]))
      · push Not at hR
        rw [g_t]
        exact (g_off R hR).2 i
    · push Not at hQ
      by_cases hR : ∃ j, R = t j
      · obtain ⟨j, rfl⟩ := hR
        rw [g_t]
        exact segCong_swap (L := L) ((g_off Q hQ).2 j)
      · push Not at hR
        obtain ⟨gQt, sQ⟩ := g_off Q hQ
        set f4 : Fin 4 → P := ![t 0, t 1, t 2, Q]
        set g4 : Fin 4 → P := ![t' 0, t' 1, t' 2, g Q]
        have hf4 : Function.Injective f4 := by
          intro x y e
          fin_cases x <;> fin_cases y <;> simp [f4] at e ⊢ <;>
            first
              | exact absurd e (ht.ne (by decide))
              | exact absurd e (hQ _).symm
              | exact absurd e (hQ _)
        have hg4 : Function.Injective g4 := by
          intro x y e
          fin_cases x <;> fin_cases y <;> simp [g4] at e ⊢ <;>
            first
              | exact absurd e (ht'.ne (by decide))
              | exact absurd e (gQt _).symm
              | exact absurd e (gQt _)
        have hseg4 : ∀ i j, i ≠ j → SegCong (f4 i) (f4 j) (g4 i) (g4 j) := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp [f4, g4] at hij ⊢ <;>
            first
              | exact hseg _ _ (by decide)
              | exact sQ _
              | exact segCong_swap (L := L) (sQ _)
        have hRf : ∀ i, R ≠ f4 i := by
          intro i; fin_cases i <;> simp [f4]
          · exact hR 0
          · exact hR 1
          · exact hR 2
          · exact fun e => hQR e.symm
        obtain ⟨R', -, hR'g, sR⟩ := F.theorem17_exists (S := Set.univ) (S' := Set.univ) rfl rfl
          (fun _ => trivial) (fun _ => trivial) hf4 hg4 hseg4 trivial hRf
        have e : g R = R' := g_eq hR (fun i => by
            have := hR'g (Fin.castSucc i)
            fin_cases i <;> simpa [g4] using this)
          (fun i => by
            have := sR (Fin.castSucc i)
            fin_cases i <;> simpa [f4, g4] using this)
        rw [e]
        simpa [f4, g4] using sR 3
  have g_inj : Function.Injective g := by
    intro Q R e
    by_contra hQR
    by_cases hQ : ∃ i, Q = t i
    · obtain ⟨i, rfl⟩ := hQ
      by_cases hR : ∃ j, R = t j
      · obtain ⟨j, rfl⟩ := hR
        rw [g_t, g_t] at e
        exact hQR (congrArg t (ht' e))
      · push Not at hR
        rw [g_t] at e
        exact (g_off R hR).1 i e.symm
    · push Not at hQ
      by_cases hR : ∃ j, R = t j
      · obtain ⟨j, rfl⟩ := hR
        rw [g_t] at e
        exact (g_off Q hQ).1 j e
      · push Not at hR
        obtain ⟨gQt, sQ⟩ := g_off Q hQ
        obtain ⟨-, sR⟩ := g_off R hR
        have s : ∀ i, SegCong (t i) Q (t i) R := fun i =>
          segCong_trans (L := L) (hQ i).symm (gQt i).symm (hR i).symm (sQ i)
            (segCong_symm (L := L) (hR i).symm (gQt i).symm (e ▸ sR i))
        exact hQR (F.eq_of_equidistant (S := Set.univ) rfl trivial trivial trivial trivial trivial
          tnc (hQ 0) (hQ 1) (hQ 2) (hR 0) (hR 1) (hR 2) (s 0) (s 1) (s 2))
  have g_surj : Function.Surjective g := by
    intro Q'
    by_cases hQ' : ∃ i, Q' = t' i
    · obtain ⟨i, rfl⟩ := hQ'
      exact ⟨t i, g_t i⟩
    · push Not at hQ'
      have hseg' : ∀ i j, i ≠ j → SegCong (t' i) (t' j) (t i) (t j) := fun i j hij =>
        segCong_symm (L := L) (ht.ne hij) (ht'.ne hij) (hseg i j hij)
      obtain ⟨Q, -, hQt, sQ⟩ := F.theorem17_exists (S := Set.univ) (S' := Set.univ) rfl rfl
        (fun _ => trivial) (fun _ => trivial) ht' ht hseg' trivial hQ'
      refine ⟨Q, g_eq hQt hQ' (fun i => segCong_symm (L := L) (hQ' i).symm (hQt i).symm (sQ i))⟩
  refine ⟨Equiv.ofBijective g ⟨g_inj, g_surj⟩, fun X Y hXY => cong X Y hXY, g_t 0, g_t 1, g_t 2⟩

end TriIso


section Reflections

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P] [HasAngCong P]
  [hC : PlaneCongruence P L]
include hC

variable {f g : Equiv.Perm P}

/-- **Rigidity**: an isometry fixing three non-collinear points is the identity. -/
theorem isom_eq_one (hf : f ∈ isom (L := L)) {A B C : P} (h : ¬Collinear (Line := L) A B C)
    (hAB : A ≠ B) (hA : f A = A) (hB : f B = B) (hC : f C = C) : f = 1 := by
  let F := pf (L := L) hAB
  ext Q
  simp only [Equiv.Perm.coe_one, id_eq]
  by_cases eA : Q = A
  · subst eA; exact hA
  by_cases eB : Q = B
  · subst eB; exact hB
  by_cases eC : Q = C
  · subst eC; exact hC
  have n : ∀ {Z : P}, f Z = Z → Q ≠ Z → f Q ≠ Z := fun hZ hQZ e =>
    hQZ (f.injective (e.trans hZ.symm))
  have s : ∀ {Z : P}, f Z = Z → Q ≠ Z → SegCong Z Q Z (f Q) := fun {Z} hZ hQZ => by
    have := hf Z Q (Ne.symm hQZ); rwa [hZ] at this
  exact (F.eq_of_equidistant (S := Set.univ) rfl trivial trivial trivial trivial trivial h eA eB eC
    (n hA eA) (n hB eB) (n hC eC) (s hA eA) (s hB eB) (s hC eC)).symm

/-- An isometry fixing two points fixes every point of their line. -/
theorem isom_fix_line (hf : f ∈ isom (L := L)) {A B : P} (hAB : A ≠ B) (hA : f A = A)
    (hB : f B = B) {X : P} (hX : Collinear (Line := L) A B X) : f X = X := by
  let F := pf (L := L) hAB
  by_cases eA : X = A
  · subst eA; exact hA
  by_cases eB : X = B
  · subst eB; exact hB
  have n : ∀ {Z : P}, f Z = Z → X ≠ Z → f X ≠ Z := fun hZ hXZ e =>
    hXZ (f.injective (e.trans hZ.symm))
  have s : ∀ {Z : P}, f Z = Z → X ≠ Z → SegCong Z X Z (f X) := fun {Z} hZ hXZ => by
    have := hf Z X (Ne.symm hXZ); rwa [hZ] at this
  exact (F.eq_of_equidistant_line hAB hX eA eB (n hA eA) (n hB eB) (s hA eA) (s hB eB)).symm

/-- The mirror image of a point in a line through `A`, `B`. -/
theorem exists_mirror {A B C : P} (hAB : A ≠ B) (hC : C ∉ line (Line := L) A B hAB) :
    ∃ C', OppositeSides (line (Line := L) A B hAB) C C' ∧ SegCong A C A C' ∧ SegCong B C B C' := by
  let F := pf (L := L) hAB
  set l := line (Line := L) A B hAB
  have hAl : A ∈ l := mem_line_left hAB
  have hBl : B ∈ l := mem_line_right hAB
  have hCA : C ≠ A := fun e => hC (e ▸ hAl)
  obtain ⟨D, hD⟩ := exists_beyond (Line := L) hCA
  have hDl : D ∉ l := fun h => hC (mem_left_of_between hD hAl h)
  have nBAC : ¬Collinear (Line := L) B A C := fun hc => hC
    ((collinear_iff_mem_line (L := L) hAB).1 hc.swap12)
  obtain ⟨C1, -, hC1D, a1⟩ := F.layoff Set.univ rfl B A C l A B D nBAC (lineIn_univ _) hAl hBl
    hAB.symm trivial hDl
  have hC1A : C1 ≠ A := fun e => hC1D.1 (e ▸ hAl)
  obtain ⟨C', hC'r, sC'⟩ := segCong_layoff (L := L) hCA.symm hC1A.symm
  have hC'l : SameSide l C1 C' := sameSide_of_ray hAl hC1D.1 hC'r
  have hopp : OppositeSides l C D := opp_of_between_mem hAl hC hD
  have o1 : OppositeSides l C C1 :=
    OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp hC1D (OrderCore.opp_symm hopp))
  have o2 : OppositeSides l C C' :=
    OrderCore.opp_symm (OrderCore.opp_of_sameSide_opp (OrderCore.sameSide_symm hC'l)
      (OrderCore.opp_symm o1))
  have nBAC1 : ¬Collinear (Line := L) B A C1 := fun hc => hC1D.1
    ((collinear_iff_mem_line (L := L) hAB).1 hc.swap12)
  have nBAC' : ¬Collinear (Line := L) B A C' := fun hc => hC'l.2.1
    ((collinear_iff_mem_line (L := L) hAB).1 hc.swap12)
  have a2 : AngCong B A C B A C' := angCong_rays nBAC nBAC1 a1 (mem_ray_self' (L := L) hAB.symm)
    (mem_ray_self' (L := L) hCA) (mem_ray_self' (L := L) hAB.symm) hC'r
  have nABC : ¬Collinear (Line := L) A B C := fun hc => nBAC hc.swap12
  have nABC' : ¬Collinear (Line := L) A B C' := fun hc => nBAC' hc.swap12
  obtain ⟨s, -, -⟩ := F.sas nABC nABC' (segCong_refl (Line := L) hAB) sC' a2
  exact ⟨C', o2, sC', s⟩

/-- Existence of the reflection in a line. -/
theorem exists_refl (l : L) : ∃ f ∈ isom (L := L), f ≠ 1 ∧ ∀ X : P, X ∈ l → f X = X := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have el := eq_line hAB hA hB
  obtain ⟨C, hC⟩ := exists_not_mem (P := P) l
  rw [el] at hC
  obtain ⟨C', ho, s1, s2⟩ := exists_mirror (L := L) hAB hC
  have nC := nc_of_not_mem_line hAB hC
  have nC' := nc_of_not_mem_line hAB ho.2.1
  obtain ⟨f, hf, fA, fB, fC⟩ := exists_isom_of_tri nC nC' hAB (segCong_refl (Line := L) hAB) s1 s2
  refine ⟨f, hf, fun e => ?_, fun X hX => isom_fix_line hf hAB fA fB ?_⟩
  · rw [e] at fC
    exact OrderCore.ne_of_opp ho fC
  · rw [el] at hX; exact (collinear_iff_mem_line (L := L) hAB).2 hX

/-- The **reflection in the line `l`**. -/
noncomputable def refl (l : L) : Equiv.Perm P := Classical.choose (exists_refl (P := P) l)

theorem refl_isom (l : L) : refl (P := P) l ∈ isom (L := L) :=
  (Classical.choose_spec (exists_refl (P := P) l)).1

theorem refl_ne_one (l : L) : refl (P := P) l ≠ 1 :=
  (Classical.choose_spec (exists_refl (P := P) l)).2.1

theorem refl_fix {l : L} {X : P} (hX : X ∈ l) : refl l X = X :=
  (Classical.choose_spec (exists_refl (P := P) l)).2.2 X hX

/-- An isometry fixing two distinct points `A`, `B` is the identity or the reflection in `AB`. -/
theorem isom_fix2 (hf : f ∈ isom (L := L)) {A B : P} (hAB : A ≠ B) (hA : f A = A)
    (hB : f B = B) : f = 1 ∨ f = refl (line (Line := L) A B hAB) := by
  set l := line (Line := L) A B hAB
  obtain ⟨C, hC⟩ := exists_not_mem (P := P) l
  have nC := nc_of_not_mem_line hAB hC
  by_cases hfC : f C = C
  · exact Or.inl (isom_eq_one hf nC hAB hA hB hfC)
  right
  set σ := refl (P := P) l
  have hσ := refl_isom (P := P) l
  have σA : σ A = A := refl_fix (mem_line_left hAB)
  have σB : σ B = B := refl_fix (mem_line_right hAB)
  have hσC : σ C ≠ C := fun e => refl_ne_one (P := P) l (isom_eq_one hσ nC hAB σA σB e)
  have off : ∀ {g : Equiv.Perm P}, g ∈ isom (L := L) → g A = A → g B = B → g C ≠ C → g C ∉ l :=
    fun {g} hg gA gB hgC hl => hgC (g.injective (isom_fix_line hg hAB gA gB
      ((collinear_iff_mem_line (L := L) hAB).2 hl)))
  have hCA : C ≠ A := fun e => hC (e ▸ mem_line_left hAB)
  have hCB : C ≠ B := fun e => hC (e ▸ mem_line_right hAB)
  have dist : ∀ {g : Equiv.Perm P}, g ∈ isom (L := L) → g A = A → g B = B →
      SegCong A C A (g C) ∧ SegCong B C B (g C) := fun {g} hg gA gB => by
    have h1 := hg A C hCA.symm
    have h2 := hg B C hCB.symm
    rw [gA] at h1; rw [gB] at h2
    exact ⟨h1, h2⟩
  have opp : ∀ {g : Equiv.Perm P}, g ∈ isom (L := L) → g A = A → g B = B → g C ≠ C →
      OppositeSides l C (g C) := fun {g} hg gA gB hgC => by
    rcases OrderCore.sameSide_or_opp hC (off hg gA gB hgC) with hs | ho
    · exact absurd (eq_of_sameSide_equidistant hAB hs (dist hg gA gB).1
        (dist hg gA gB).2).symm hgC
    · exact ho
  have ss : SameSide l (f C) (σ C) :=
    OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm (opp hf hA hB hfC)) (opp hσ σA σB hσC)
  have hfCA : f C ≠ A := fun e => off hf hA hB hfC (e ▸ mem_line_left hAB)
  have hfCB : f C ≠ B := fun e => off hf hA hB hfC (e ▸ mem_line_right hAB)
  have hσCA : σ C ≠ A := fun e => off hσ σA σB hσC (e ▸ mem_line_left hAB)
  have hσCB : σ C ≠ B := fun e => off hσ σA σB hσC (e ▸ mem_line_right hAB)
  have e := eq_of_sameSide_equidistant hAB ss
    (SegmentCongruence.ax_IV2 (Line := L) A C A (f C) A (σ C) hCA.symm hfCA.symm
        hσCA.symm (dist hf hA hB).1 (dist hσ σA σB).1)
    (SegmentCongruence.ax_IV2 (Line := L) B C B (f C) B (σ C) hCB.symm hfCB.symm hσCB.symm
        (dist hf hA hB).2 (dist hσ σA σB).2)
  have h1 : σ⁻¹ * f = 1 := by
    refine isom_eq_one ((isom (L := L)).mul_mem (isom_inv hσ) hf) nC hAB ?_ ?_ ?_
    · rw [Equiv.Perm.mul_apply, hA, Equiv.Perm.inv_eq_iff_eq, σA]
    · rw [Equiv.Perm.mul_apply, hB, Equiv.Perm.inv_eq_iff_eq, σB]
    · rw [Equiv.Perm.mul_apply, e, Equiv.Perm.inv_eq_iff_eq]
  rw [← mul_inv_cancel_left σ f, h1, mul_one]

theorem refl_unique {l : L} (hf : f ∈ isom (L := L)) (hf1 : f ≠ 1)
    (hfix : ∀ X : P, X ∈ l → f X = X) : f = refl l := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have el := eq_line hAB hA hB
  rcases isom_fix2 hf hAB (hfix A hA) (hfix B hB) with h | h
  · exact absurd h hf1
  · rw [h, ← el]

/-- The reflection in a line is an involution. -/
theorem refl_mul_self (l : L) : refl (P := P) l * refl l = 1 := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have el := eq_line hAB hA hB
  have h2 := (isom (L := L)).mul_mem (refl_isom (P := P) l) (refl_isom (P := P) l)
  rcases isom_fix2 h2 hAB (by rw [Equiv.Perm.mul_apply, refl_fix hA, refl_fix hA])
    (by rw [Equiv.Perm.mul_apply, refl_fix hB, refl_fix hB]) with h | h
  · exact h
  · rw [← el] at h
    have : refl (P := P) l = 1 := by
      have := congrArg ((refl (P := P) l)⁻¹ * ·) h
      simpa using this
    exact absurd this (refl_ne_one l)

theorem refl_refl (l : L) (X : P) : refl l (refl l X) = X := by
  have := congrArg (fun g : Equiv.Perm P => g X) (refl_mul_self (L := L) l)
  simpa using this

/-- The fixed points of the reflection in `l` are the points of `l`. -/
theorem refl_fix_iff {l : L} {X : P} : refl l X = X ↔ X ∈ l := by
  refine ⟨fun h => ?_, refl_fix⟩
  by_contra hX
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have el := eq_line hAB hA hB
  rw [el] at hX
  exact refl_ne_one (P := P) l (isom_eq_one (refl_isom (P := P) l) (nc_of_not_mem_line hAB hX) hAB
    (refl_fix hA) (refl_fix hB) h)

/-- The reflection in `l` exchanges the sides of `l`. -/
theorem refl_opp {l : L} {X : P} (hX : X ∉ l) : OppositeSides l X (refl l X) := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) l
  have el := eq_line hAB hA hB
  have hσ := refl_isom (P := P) l
  have hσX : refl l X ≠ X := fun e => hX (refl_fix_iff.1 e)
  have hσXl : refl l X ∉ l := fun h => hσX (by
    have := refl_fix h; rw [refl_refl] at this; exact this.symm)
  rcases OrderCore.sameSide_or_opp hX hσXl with hs | ho
  · exfalso
    have hs' : SameSide (line (Line := L) A B hAB) X (refl l X) := by rw [← el]; exact hs
    have h1 := hσ A X (fun e => hX (e ▸ hA))
    have h2 := hσ B X (fun e => hX (e ▸ hB))
    rw [refl_fix hA] at h1; rw [refl_fix hB] at h2
    exact hσX (eq_of_sameSide_equidistant hAB hs' h1 h2).symm
  · exact ho

/-- The points equidistant from two distinct points form a line, and the reflection in this line
exchanges the two points. -/
theorem exists_eqd {X Y : P} (h : X ≠ Y) :
    ∃ m : L, (∀ Z : P, Z ∈ m ↔ Z ≠ X ∧ Z ≠ Y ∧ SegCong Z X Z Y) ∧ refl m X = Y ∧
      OppositeSides m X Y := by
  let F := pf (L := L) h
  obtain ⟨Q, R, -, -, hQR, sQ, sR⟩ := F.bisector (S := Set.univ) rfl trivial trivial h
  have hQR' : Q ≠ R := OrderCore.ne_of_opp hQR
  obtain ⟨nX, nY⟩ := F.not_mem_bisector h hQR sQ sR hQR'
  set m := line (Line := L) Q R hQR'
  have hQX : Q ≠ X := fun e => hQR.1 (e ▸ mem_line_left h)
  have hQY : Q ≠ Y := fun e => hQR.1 (e ▸ mem_line_right h)
  have hRX : R ≠ X := fun e => hQR.2.1 (e ▸ mem_line_left h)
  have hRY : R ≠ Y := fun e => hQR.2.1 (e ▸ mem_line_right h)
  have mem : ∀ Z : P, Z ∈ m ↔ Z ≠ X ∧ Z ≠ Y ∧ SegCong Z X Z Y := by
    intro Z
    constructor
    · intro hZ
      exact ⟨fun e => nX (e ▸ hZ), fun e => nY (e ▸ hZ), F.equidistant_of_mem hQR' nX nY sQ sR hZ⟩
    · rintro ⟨hZX, hZY, sZ⟩
      by_contra hZ
      have nc := nc_of_not_mem_line hQR' hZ
      exact h (F.eq_of_equidistant (S := Set.univ) rfl trivial trivial trivial trivial trivial nc
        hQX.symm hRX.symm hZX.symm hQY.symm hRY.symm hZY.symm sQ sR sZ)
  obtain ⟨M, hMm, hM, -⟩ := F.midpoint_of_equidistant (S := Set.univ) rfl trivial trivial trivial
    trivial hQR' h nX nY sQ sR
  have hopp : OppositeSides m X Y := ⟨nX, nY, M, hMm, hM⟩
  refine ⟨m, mem, ?_, hopp⟩
  have hσ := refl_isom (P := P) m
  have o1 := refl_opp (L := L) nX
  have ss : SameSide m (refl m X) Y := OrderCore.sameSide_of_opp_opp (OrderCore.opp_symm o1) hopp
  have hσXQ : refl m X ≠ Q := fun e => ss.1 (e ▸ mem_line_left hQR')
  have hσXR : refl m X ≠ R := fun e => ss.1 (e ▸ mem_line_right hQR')
  have h1 := hσ Q X hQX
  have h2 := hσ R X hRX
  rw [refl_fix (mem_line_left hQR')] at h1
  rw [refl_fix (mem_line_right hQR')] at h2
  exact eq_of_sameSide_equidistant hQR' ss
    (SegmentCongruence.ax_IV2 (Line := L) Q X Q (refl m X) Q Y hQX hσXQ.symm hQY h1 sQ)
    (SegmentCongruence.ax_IV2 (Line := L) R X R (refl m X) R Y hRX hσXR.symm hRY h2 sR)

end Reflections

end Pas

end HilbertFoundations
