import HilbertFoundations.Order
import HilbertFoundations.Analytic

/-!
# Helper for §§ 24–30: affine planes, Desargues's theorem, dilatations and translations

Helper module of `DesarguesAlgebra.lean` (the units are stated there). Contents:

* **Affine incidence** in a plane geometry satisfying I 1–2 and III (`PlaneParallels`): the
  relation `LPar P a b` ("`a` and `b` are parallel or equal"), the parallel `pline l X` to `l`
  through `X`, the line `ln A B` through two points, the common point `meet a b` of two
  non-parallel lines.
* **Desargues's theorem** as a proposition about a plane geometry: `DesarguesI` (Hilbert's first
  part: homologous sides parallel ⇒ joins concurrent or parallel), `DesarguesII` (the converse,
  "the second part of Desargues's theorem"), `DesarguesTheorem` (both).
* **Dilatations** (`IsDil`: maps sending every line into a parallel line) and **translations**
  (`IsTr`: dilatations without fixed point, or the identity), following E. Artin, *Geometric
  Algebra*, ch. II. A dilatation is determined by the images of two points.
* **The pencil construction** (`pencilMap`): from the second part of Desargues's theorem, for every
  pencil of lines (all lines parallel to a given one, or all lines through a point `O`) and every
  pair `A`, `B` of points of one line of the pencil there is a dilatation mapping `A` to `B` and every
  line of the pencil into itself. For a parallel pencil this is a translation (`exists_tr`), for the
  pencil through `O` a dilatation with centre `O` (`exists_cdil`).
* **The group of translations**: composition, inverses, commutativity.

The order axioms are used only through "every line has at least three points" (II 2), so that a
point off two given lines exists (`exists_off_two`).
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

universe u v w

namespace DesAlg

variable {P : Type u} {L : Type v} [HasLines P L]

/-! ## Desargues's theorem as a proposition -/

/-- **The line `AB` is parallel to the line `CD`**: there are lines through `A, B` and through
`C, D` without a common point (Hilbert's "parallel": lines that do not intersect). -/
def ParPts (A B C D : P) : Prop :=
  ∃ a b : L, A ∈ a ∧ B ∈ a ∧ C ∈ b ∧ D ∈ b ∧ ¬Meets (Point := P) a b

/-- Three lines **pass through one point or are parallel to one another**. -/
def ConcurrentOrParallel (P : Type u) {L : Type v} [HasLines P L] (a b c : L) : Prop :=
  (∃ O : P, O ∈ a ∧ O ∈ b ∧ O ∈ c) ∨
    (¬Meets (Point := P) a b ∧ ¬Meets (Point := P) a c ∧ ¬Meets (Point := P) b c)

/-- **Desargues's theorem, first part** (Theorem 32): if the homologous sides of two triangles
`ABC`, `A'B'C'` are parallel, the lines `AA'`, `BB'`, `CC'` pass through one point or are parallel
to one another. -/
def DesarguesI (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ A B C A' B' C' : P, ¬Collinear A B C → ¬Collinear A' B' C' →
    ParPts A B A' B' → ParPts A C A' C' → ParPts B C B' C' →
      (∃ O : P, Collinear A A' O ∧ Collinear B B' O ∧ Collinear C C' O) ∨
        (ParPts A A' B B' ∧ ParPts A A' C C' ∧ ParPts B B' C C')

/-- **Desargues's theorem, second part** (the converse in Theorem 32): if the (three distinct)
lines `a ∋ A, A'`, `b ∋ B, B'`, `c ∋ C, C'` joining the homologous vertices of two triangles pass
through one point or are parallel, and `AB ∥ A'B'`, `AC ∥ A'C'`, then `BC ∥ B'C'`. -/
def DesarguesII (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  ∀ (A B C A' B' C' : P) (a b c : L), ¬Collinear A B C → ¬Collinear A' B' C' →
    A ∈ a → A' ∈ a → B ∈ b → B' ∈ b → C ∈ c → C' ∈ c → a ≠ b → a ≠ c → b ≠ c →
    ConcurrentOrParallel P a b c → ParPts A B A' B' → ParPts A C A' C' → ParPts B C B' C'

/-- **Desargues's theorem** (Theorem 32, both parts). -/
def DesarguesTheorem (P : Type u) {L : Type v} [HasLines P L] : Prop :=
  DesarguesI P ∧ DesarguesII P

/-! ## Affine incidence -/

/-- The lines `a` and `b` are **parallel or equal**. -/
def LPar (P : Type u) {L : Type v} [HasLines P L] (a b : L) : Prop :=
  ∀ X : P, X ∈ a → X ∈ b → a = b

theorem lpar_refl (a : L) : LPar P a a := fun _ _ _ => rfl

theorem LPar.symm {a b : L} (h : LPar P a b) : LPar P b a := fun X hb ha => (h X ha hb).symm

theorem not_meets_of_lpar {a b : L} (h : LPar P a b) (hab : a ≠ b) : ¬Meets (Point := P) a b :=
  fun ⟨X, ha, hb⟩ => hab (h X ha hb)

theorem lpar_of_not_meets {a b : L} (h : ¬Meets (Point := P) a b) : LPar P a b :=
  fun X ha hb => (h ⟨X, ha, hb⟩).elim

theorem not_lpar_iff {a b : L} : ¬LPar P a b ↔ ∃ X : P, X ∈ a ∧ X ∈ b ∧ a ≠ b := by
  unfold LPar
  constructor
  · intro h
    by_contra h'
    exact h fun X ha hb => by_contra fun hab => h' ⟨X, ha, hb, hab⟩
  · rintro ⟨X, ha, hb, hab⟩ h
    exact hab (h X ha hb)

theorem not_lpar_of {a b : L} {X : P} (ha : X ∈ a) (hb : X ∈ b) (hab : a ≠ b) : ¬LPar P a b :=
  not_lpar_iff.2 ⟨X, ha, hb, hab⟩

section Affine

variable [hPP : PlaneParallels P L] [hL : Nonempty L]
include hPP hL

theorem exists_two_ne_points : ∃ A B : P, A ≠ B := by
  obtain ⟨l⟩ := hL
  obtain ⟨A, B, h, -⟩ := exists_two_points (Point := P) l
  exact ⟨A, B, h⟩

theorem nonempty_point : Nonempty P := by
  obtain ⟨A, -, -⟩ := exists_two_ne_points (P := P) (L := L)
  exact ⟨A⟩

theorem exists_other (A : P) : ∃ B : P, B ≠ A := by
  obtain ⟨X, Y, h⟩ := exists_two_ne_points (P := P) (L := L)
  by_cases hX : X = A
  · exact ⟨Y, fun e => h (hX.trans e.symm)⟩
  · exact ⟨X, hX⟩

theorem exists_line_two (A B : P) : ∃ l : L, A ∈ l ∧ B ∈ l := by
  by_cases h : A = B
  · subst h
    obtain ⟨C, hC⟩ := exists_other (L := L) A
    obtain ⟨l, hA, -⟩ := exists_line (Line := L) hC.symm
    exact ⟨l, hA, hA⟩
  · exact exists_line h

/-- A line through `A` and `B` (the line `AB` when `A ≠ B`). -/
noncomputable def ln (A B : P) : L := (exists_line_two (L := L) A B).choose

theorem mem_ln_left (A B : P) : A ∈ (ln A B : L) := (exists_line_two (L := L) A B).choose_spec.1

theorem mem_ln_right (A B : P) : B ∈ (ln A B : L) := (exists_line_two (L := L) A B).choose_spec.2

theorem ln_eq {A B : P} {l : L} (h : A ≠ B) (hA : A ∈ l) (hB : B ∈ l) : ln A B = l :=
  line_unique h (mem_ln_left A B) (mem_ln_right A B) hA hB

theorem ln_comm {A B : P} (h : A ≠ B) : (ln A B : L) = ln B A :=
  (ln_eq h.symm (mem_ln_right A B) (mem_ln_left A B)).symm

theorem collinear_iff_mem_ln {A B C : P} (h : A ≠ B) : Collinear A B C ↔ C ∈ (ln A B : L) := by
  constructor
  · rintro ⟨l, hA, hB, hC⟩; rw [ln_eq h hA hB]; exact hC
  · intro hC; exact ⟨ln A B, mem_ln_left A B, mem_ln_right A B, hC⟩

theorem exists_not_mem' (l : L) : ∃ X : P, X ∉ l := exists_not_mem (P := P) l

/-! ### Parallels -/

theorem exists_lpar (l : L) (X : P) : ∃ m : L, X ∈ m ∧ LPar P m l := by
  by_cases h : X ∈ l
  · exact ⟨l, h, lpar_refl l⟩
  · obtain ⟨b, ⟨hXb, hb⟩, -⟩ := exists_unique_parallel (Line := L) h
    exact ⟨b, hXb, lpar_of_not_meets hb⟩

/-- **The parallel to `l` through `X`** (`l` itself when `X ∈ l`). -/
noncomputable def pline (l : L) (X : P) : L := (exists_lpar (P := P) l X).choose

theorem mem_pline (l : L) (X : P) : X ∈ pline l X := (exists_lpar (P := P) l X).choose_spec.1

theorem pline_lpar (l : L) (X : P) : LPar P (pline l X) l := (exists_lpar (P := P) l X).choose_spec.2

/-- Uniqueness of the parallel (axiom III). -/
theorem lpar_unique {l m m' : L} {X : P} (hm : X ∈ m) (hm' : X ∈ m') (h : LPar P m l)
    (h' : LPar P m' l) : m = m' := by
  by_cases hXl : X ∈ l
  · rw [h X hm hXl, h' X hm' hXl]
  · have h1 : ¬Meets (Point := P) m l := fun ⟨Y, hY, hY'⟩ => hXl (by rw [← h Y hY hY']; exact hm)
    have h2 : ¬Meets (Point := P) m' l :=
      fun ⟨Y, hY, hY'⟩ => hXl (by rw [← h' Y hY hY']; exact hm')
    exact (exists_unique_parallel (Line := L) hXl).unique ⟨hm, h1⟩ ⟨hm', h2⟩

theorem eq_pline {l m : L} {X : P} (hX : X ∈ m) (h : LPar P m l) : m = pline l X :=
  lpar_unique hX (mem_pline l X) h (pline_lpar l X)

theorem LPar.trans {a b c : L} (h1 : LPar P a b) (h2 : LPar P b c) : LPar P a c :=
  fun _ ha hc => lpar_unique ha hc h1 h2.symm

theorem pline_of_mem {l : L} {X : P} (h : X ∈ l) : pline l X = l :=
  (eq_pline h (lpar_refl l)).symm

theorem pline_eq_of_mem {l : L} {X Y : P} (h : Y ∈ pline l X) : pline l Y = pline l X :=
  (eq_pline h (pline_lpar l X)).symm

theorem pline_congr {l l' : L} (h : LPar P l l') (X : P) : pline l X = pline l' X :=
  eq_pline (mem_pline l X) ((pline_lpar l X).trans h)

theorem pline_pline (l : L) (X Y : P) : pline (pline l Y) X = pline l X :=
  pline_congr (pline_lpar l Y) X

theorem pline_symm {l : L} {X Y : P} (h : Y ∈ pline l X) : X ∈ pline l Y := by
  rw [pline_eq_of_mem h]; exact mem_pline l X

theorem not_lpar_pline {a b : L} (h : ¬LPar P a b) (X Y : P) :
    ¬LPar P (pline a X) (pline b Y) :=
  fun h' => h (((pline_lpar a X).symm.trans h').trans (pline_lpar b Y))

theorem not_lpar_pline_left {a b : L} (h : ¬LPar P a b) (X : P) : ¬LPar P (pline a X) b :=
  fun h' => h ((pline_lpar a X).symm.trans h')

theorem not_lpar_pline_right {a b : L} (h : ¬LPar P a b) (Y : P) : ¬LPar P a (pline b Y) :=
  fun h' => h (h'.trans (pline_lpar b Y))

theorem lpar_of_pline_eq {a b : L} {X : P} (h : pline a X = pline b X) : LPar P a b := by
  have h1 := (pline_lpar a X).symm
  rw [h] at h1
  exact h1.trans (pline_lpar b X)

/-! ### The common point of two lines -/

/-- The **common point** of two lines (if they have one). -/
noncomputable def meet (a b : L) : P := by
  classical
  exact if h : ∃ X : P, X ∈ a ∧ X ∈ b then h.choose else (nonempty_point (L := L)).some

theorem meet_mem_of_meets {a b : L} (h : ∃ X : P, X ∈ a ∧ X ∈ b) :
    meet a b ∈ a ∧ meet a b ∈ b := by
  unfold meet
  split
  · rename_i h'; exact h'.choose_spec
  · exact absurd h ‹_›

theorem meet_mem {a b : L} (h : ¬LPar P a b) : meet (P := P) a b ∈ a ∧ meet (P := P) a b ∈ b := by
  obtain ⟨X, ha, hb, -⟩ := not_lpar_iff.1 h
  exact meet_mem_of_meets ⟨X, ha, hb⟩

theorem meet_mem_left {a b : L} (h : ¬LPar P a b) : meet (P := P) a b ∈ a := (meet_mem h).1

theorem meet_mem_right {a b : L} (h : ¬LPar P a b) : meet (P := P) a b ∈ b := (meet_mem h).2

theorem eq_meet {a b : L} {X : P} (h : ¬LPar P a b) (ha : X ∈ a) (hb : X ∈ b) : X = meet a b := by
  obtain ⟨-, -, -, hab⟩ := not_lpar_iff.1 h
  exact eq_of_mem_of_mem hab ha hb (meet_mem_left h) (meet_mem_right h)

theorem eq_of_mem_not_lpar {a b : L} {X Y : P} (h : ¬LPar P a b) (ha : X ∈ a) (hb : X ∈ b)
    (ha' : Y ∈ a) (hb' : Y ∈ b) : X = Y :=
  (eq_meet h ha hb).trans (eq_meet h ha' hb').symm

/-- Two lines through `Z` and two different points `X`, `Y`, with `Z` off `XY`, are not parallel. -/
theorem not_lpar_ln_ln {X Y Z : P} (hXY : X ≠ Y) (hZ : Z ∉ (ln X Y : L)) :
    ¬LPar P (ln X Z : L) (ln Y Z) := by
  refine not_lpar_of (mem_ln_right X Z) (mem_ln_right Y Z) fun e => hZ ?_
  have hXZ : X ≠ Z := fun h => hZ (h ▸ mem_ln_left X Y)
  have hY : Y ∈ (ln X Z : L) := by rw [e]; exact mem_ln_left Y Z
  rw [ln_eq hXY (mem_ln_left X Z) hY]; exact mem_ln_right X Z

theorem mem_ln_of_lpar {A B : P} {l : L} (_hAB : A ≠ B) (hA : A ∈ l) (h : LPar P (ln A B) l) :
    B ∈ l := by
  rw [← h A (mem_ln_left A B) hA]; exact mem_ln_right A B

theorem ln_eq_pline {A B : P} {l : L} (hAB : A ≠ B) (hB : B ∈ pline l A) : (ln A B : L) = pline l A :=
  ln_eq hAB (mem_pline l A) hB

/-- Lines through a common point are parallel only if equal. -/
theorem eq_of_lpar_of_mem {a b : L} {X : P} (h : LPar P a b) (ha : X ∈ a) (hb : X ∈ b) : a = b :=
  h X ha hb

/-! ### Parallelism between pairs of points -/

theorem parPts_of {A B A' B' : P} (_hAB : A ≠ B) (hA' : A' ∉ (ln A B : L))
    (hB' : B' ∈ pline (ln A B : L) A') : ParPts A B A' B' :=
by
  refine ⟨ln A B, pline (ln A B) A', mem_ln_left A B, mem_ln_right A B, mem_pline _ A', hB', ?_⟩
  rintro ⟨X, h1, h2⟩
  have e : pline (ln A B : L) A' = ln A B := (pline_lpar (ln A B : L) A') X h2 h1
  exact hA' (e ▸ mem_pline (ln A B : L) A')

theorem mem_pline_of_parPts {A B A' B' : P} (h : ParPts A B A' B') (hAB : A ≠ B) :
    B' ∈ pline (ln A B : L) A' := by
  obtain ⟨a, b, hA, hB, hA', hB', hn⟩ := h
  rw [ln_eq hAB hA hB, ← eq_pline hA' (lpar_of_not_meets hn).symm]; exact hB'

theorem ne_of_parPts {A B A' B' : P} (h : ParPts A B A' B') : A ≠ A' := by
  obtain ⟨a, b, hA, -, hA', -, hn⟩ := h
  rintro rfl; exact hn ⟨A, hA, hA'⟩

theorem ne_of_parPts' {A B A' B' : P} (h : ParPts A B A' B') : B ≠ B' := by
  obtain ⟨a, b, -, hB, -, hB', hn⟩ := h
  rintro rfl; exact hn ⟨B, hB, hB'⟩

end Affine

/-! ## Points off lines (II 2: every line has a third point) -/

section ThreePoints

variable [HasBetween P] [hLO : LineOrder P L] [hPP : PlaneParallels P L] [hL : Nonempty L]
include hLO hPP hL

/-- A point off two given lines. -/
theorem exists_off_two (a b : L) : ∃ Z : P, Z ∉ a ∧ Z ∉ b := by
  obtain ⟨Q, hQ⟩ := exists_not_mem' (P := P) a
  by_cases hQb : Q ∈ b
  · obtain ⟨T, hT⟩ := exists_not_mem' (P := P) b
    have hQT : Q ≠ T := fun e => hT (e ▸ hQb)
    obtain ⟨M, hM⟩ := exists_between (Line := L) hQT
    have hMg : M ∈ (ln Q T : L) := by
      rw [← collinear_iff_mem_ln hQT]
      exact (collinear_of_between hM).swap23
    have hQM : Q ≠ M := ne12_of_between hM
    have hMT : M ≠ T := ne23_of_between hM
    have hgb : (ln Q T : L) ≠ b := fun e => hT (e ▸ mem_ln_right Q T)
    have offb : ∀ X : P, X ∈ (ln Q T : L) → X ≠ Q → X ∉ b := fun X hX hXQ hXb =>
      hXQ (eq_of_mem_of_mem hgb hX hXb (mem_ln_left Q T) hQb)
    by_cases hTa : T ∈ a
    · refine ⟨M, fun hMa => ?_, offb M hMg hQM.symm⟩
      have : (ln Q T : L) = a := (ln_eq hMT hMg (mem_ln_right Q T)).symm.trans (ln_eq hMT hMa hTa)
      exact hQ (this ▸ mem_ln_left Q T)
    · exact ⟨T, hTa, hT⟩
  · exact ⟨Q, hQ, hQb⟩

end ThreePoints

/-! ## Dilatations and translations -/

section Dilatations

variable [hPP : PlaneParallels P L] [hL : Nonempty L]
include hPP hL

/-- A **dilatation**: a map sending every line into a parallel line (Artin): for `X ≠ Y`, `f Y`
lies on the parallel to `XY` through `f X`. Constant maps are (degenerate) dilatations. -/
def IsDil (f : P → P) : Prop := ∀ X Y : P, X ≠ Y → f Y ∈ pline (ln X Y : L) (f X)

/-- A **translation**: a dilatation which is the identity as soon as it has a fixed point. -/
def IsTr (f : P → P) : Prop := IsDil (L := L) f ∧ ∀ X : P, f X = X → f = id

theorem isDil_id : IsDil (L := L) (id : P → P) := fun X Y h => by
  show Y ∈ pline (ln X Y : L) X
  rw [pline_of_mem (mem_ln_left X Y)]; exact mem_ln_right X Y

theorem isDil_const (c : P) : IsDil (L := L) (fun _ : P => c) := fun _ _ _ => mem_pline _ c

/-- A dilatation maps a line `l` into the parallel to `l` through the image of one of its points. -/
theorem IsDil.map_line {f : P → P} (hf : IsDil (L := L) f) {l : L} {X Y : P} (hX : X ∈ l)
    (hY : Y ∈ l) : f Y ∈ pline l (f X) := by
  by_cases h : X = Y
  · subst h; exact mem_pline l (f X)
  · have := hf X Y h; rwa [ln_eq h hX hY] at this

theorem IsDil.comp {f g : P → P} (hf : IsDil (L := L) f) (hg : IsDil (L := L) g) :
    IsDil (L := L) (f ∘ g) := by
  intro X Y hXY
  simp only [Function.comp]
  by_cases h : g X = g Y
  · rw [← h]; exact mem_pline _ _
  · have h1 := hg X Y hXY
    have := hf (g X) (g Y) h
    rwa [ln_eq_pline h h1, pline_pline] at this

/-- **A dilatation is determined by the images of two points** (off the line of the two points). -/
theorem dil_eq_of_off {f g : P → P} (hf : IsDil (L := L) f) (hg : IsDil (L := L) g) {X Y Z : P}
    (hXY : X ≠ Y) (h1 : f X = g X) (h2 : f Y = g Y) (hZ : Z ∉ (ln X Y : L)) : f Z = g Z := by
  have hXZ : X ≠ Z := fun e => hZ (e ▸ mem_ln_left X Y)
  have hYZ : Y ≠ Z := fun e => hZ (e ▸ mem_ln_right X Y)
  have hn := not_lpar_pline (not_lpar_ln_ln hXY hZ) (f X) (f Y)
  have a1 := hf X Z hXZ
  have a2 := hf Y Z hYZ
  have b1 := hg X Z hXZ
  have b2 := hg Y Z hYZ
  rw [← h1] at b1; rw [← h2] at b2
  exact eq_of_mem_not_lpar hn a1 a2 b1 b2

/-- **A dilatation is determined by the images of two distinct points.** -/
theorem dil_eq_of_two {f g : P → P} (hf : IsDil (L := L) f) (hg : IsDil (L := L) g) {X Y : P}
    (hXY : X ≠ Y) (h1 : f X = g X) (h2 : f Y = g Y) : f = g := by
  funext Z
  by_cases hZ : Z ∈ (ln X Y : L)
  · obtain ⟨W, hW⟩ := exists_not_mem' (P := P) (ln X Y : L)
    have hXW : X ≠ W := fun e => hW (e ▸ mem_ln_left X Y)
    have hW' : f W = g W := dil_eq_of_off hf hg hXY h1 h2 hW
    by_cases hZX : Z = X
    · rw [hZX]; exact h1
    · refine dil_eq_of_off hf hg hXW h1 hW' fun hZ' => hW ?_
      have e1 : (ln X W : L) = ln X Y := by
        rw [← ln_eq (Ne.symm hZX) (mem_ln_left X W) hZ', ln_eq (Ne.symm hZX) (mem_ln_left X Y) hZ]
      rw [← e1]; exact mem_ln_right X W
  · exact dil_eq_of_off hf hg hXY h1 h2 hZ

/-- A dilatation identifying two distinct points is constant. -/
theorem IsDil.eq_const {f : P → P} (hf : IsDil (L := L) f) {X Y : P} (hXY : X ≠ Y) (h : f X = f Y) :
    f = fun _ => f X :=
  dil_eq_of_two hf (isDil_const (L := L) (f X)) hXY rfl h.symm

/-- A dilatation fixing two distinct points is the identity. -/
theorem IsDil.eq_id {f : P → P} (hf : IsDil (L := L) f) {X Y : P} (hXY : X ≠ Y) (h1 : f X = X)
    (h2 : f Y = Y) : f = id :=
  dil_eq_of_two hf (isDil_id (L := L)) hXY h1 h2

/-- A dilatation fixing `O` maps every line through `O` into itself. -/
theorem IsDil.mem_of_fix {f : P → P} (hf : IsDil (L := L) f) {O Y : P} {l : L} (hO : f O = O)
    (hOl : O ∈ l) (hY : Y ∈ l) : f Y ∈ l := by
  have := hf.map_line hOl hY; rwa [hO, pline_of_mem hOl] at this

theorem isTr_id : IsTr (L := L) (id : P → P) := ⟨isDil_id, fun _ _ => rfl⟩

/-- A translation maps the line joining a point to its image into itself. -/
theorem IsDil.trace_invariant {f : P → P} (hf : IsDil (L := L) f) {X W : P}
    (hW : W ∈ (ln X (f X) : L)) : f W ∈ (ln X (f X) : L) := by
  have := hf.map_line (mem_ln_left X (f X)) hW
  rwa [pline_of_mem (mem_ln_right X (f X))] at this

/-- **The traces of a translation are parallel**: every `f Y` lies on the parallel through `Y` to
the line joining `X` and `f X ≠ X`. -/
theorem IsTr.trace {f : P → P} (hf : IsTr (L := L) f) {X : P} (hX : f X ≠ X) (Y : P) :
    f Y ∈ pline (ln X (f X) : L) Y := by
  have hY : f Y ≠ Y := fun e => hX (by rw [hf.2 Y e]; rfl)
  by_cases hd : LPar P (ln Y (f Y) : L) (ln X (f X))
  · rw [← eq_pline (mem_ln_left Y (f Y)) hd]; exact mem_ln_right Y (f Y)
  · exfalso
    obtain ⟨Z, h1, h2, hne⟩ := not_lpar_iff.1 hd
    have k1 := hf.1.trace_invariant h1
    have k2 := hf.1.trace_invariant h2
    have hZ : f Z = Z := eq_of_mem_of_mem hne k1 k2 h1 h2
    exact hX (by rw [hf.2 Z hZ]; rfl)

/-- A translation different from the identity moves every point. -/
theorem IsTr.ne_of_ne {f : P → P} (hf : IsTr (L := L) f) {X : P} (hX : f X ≠ X) (Y : P) :
    f Y ≠ Y := fun e => hX (by rw [hf.2 Y e]; rfl)

/-- **A translation is determined by the image of one point.** -/
theorem tr_eq_of {f g : P → P} (hf : IsTr (L := L) f) (hg : IsTr (L := L) g) {X : P}
    (h : f X = g X) : f = g := by
  by_cases hX : f X = X
  · rw [hf.2 X hX, hg.2 X (h ▸ hX)]
  · obtain ⟨Y, hY⟩ := exists_not_mem' (P := P) (ln X (f X) : L)
    have hXY : X ≠ Y := fun e => hY (e ▸ mem_ln_left X (f X))
    have hgX : g X ≠ X := h ▸ hX
    have e1 := hf.trace hX Y
    have e2 := hg.trace hgX Y
    rw [← h] at e2
    have a1 := hf.1 X Y hXY
    have a2 := hg.1 X Y hXY
    rw [← h] at a2
    have hn : ¬LPar P (pline (ln X (f X) : L) Y) (pline (ln X Y) (f X)) := by
      refine not_lpar_pline (not_lpar_of (mem_ln_left X (f X)) (mem_ln_left X Y) fun e => hY ?_) _ _
      rw [e]; exact mem_ln_right X Y
    have hYY : f Y = g Y := eq_of_mem_not_lpar hn e1 a1 e2 a2
    exact dil_eq_of_two hf.1 hg.1 hXY h hYY

/-- A translation which is not the identity is injective. -/
theorem IsTr.injective {f : P → P} (hf : IsTr (L := L) f) : Function.Injective f := by
  intro X Y h
  by_contra hXY
  have hc := hf.1.eq_const hXY h
  have : f = id := hf.2 (f X) (by rw [hc])
  rw [this] at h; exact hXY h

/-- **The composite of two translations is a translation.** -/
theorem IsTr.comp {f g : P → P} (hf : IsTr (L := L) f) (hg : IsTr (L := L) g) :
    IsTr (L := L) (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun Z hZ => ?_⟩
  simp only [Function.comp] at hZ
  by_cases hQ : g Z = Z
  · rw [hQ] at hZ; rw [hf.2 Z hZ, hg.2 Z hQ]; rfl
  · -- `f (g Z) = Z` with `g Z ≠ Z`
    have hfQ : f (g Z) ≠ g Z := fun e => hQ (e.symm.trans hZ)
    obtain ⟨X, hX⟩ := exists_not_mem' (P := P) (ln Z (g Z) : L)
    have hZX : Z ≠ X := fun e => hX (e ▸ mem_ln_left Z (g Z))
    -- the trace of `g` through `X` and the dilatation property
    have t1 : g X ∈ pline (ln Z (g Z) : L) X := hg.trace hQ X
    have t2 : g X ∈ pline (ln Z X : L) (g Z) := hg.1 Z X hZX
    have hgXQ : g X ≠ g Z := fun e => hZX (hg.injective e.symm)
    have t3 : f (g X) ∈ pline (ln (g Z) (f (g Z)) : L) (g X) := hf.trace hfQ (g X)
    have hl : (ln (g Z) (f (g Z)) : L) = ln Z (g Z) := by
      rw [hZ, ln_comm hQ]
    rw [hl, pline_eq_of_mem t1] at t3
    have t4 : f (g X) ∈ pline (ln (g Z) (g X) : L) (f (g Z)) := hf.1 (g Z) (g X) hgXQ.symm
    rw [ln_eq_pline hgXQ.symm t2, pline_pline, hZ, pline_of_mem (mem_ln_left Z X)] at t4
    have hn : ¬LPar P (pline (ln Z (g Z) : L) X) (ln Z X) := by
      refine not_lpar_of (mem_pline _ X) (mem_ln_right Z X) fun e => hX ?_
      have : Z ∈ pline (ln Z (g Z) : L) X := e ▸ mem_ln_left Z X
      have h1 := pline_eq_of_mem this
      rw [pline_of_mem (mem_ln_left Z (g Z))] at h1
      rw [h1]; exact mem_pline _ X
    have hfix : f (g X) = X := eq_of_mem_not_lpar hn t3 t4 (mem_pline _ X) (mem_ln_right Z X)
    exact (hf.1.comp hg.1).eq_id hZX hZ hfix

end Dilatations


/-! ## The pencil construction (second part of Desargues's theorem) -/

section Pencil

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L]

/-- A **pencil of lines**: `pen X` is the line of the pencil through `X` (for `X` not excluded);
the excluded points `S` (at most one: the centre, which lies on every line of the pencil). Any
three distinct lines of the pencil pass through one point or are parallel. -/
structure IsPencil (pen : P → L) (S : P → Prop) : Prop where
  mem : ∀ X, ¬S X → X ∈ pen X
  eq : ∀ X Y, ¬S X → ¬S Y → Y ∈ pen X → pen Y = pen X
  joins : ∀ X Y Z, ¬S X → ¬S Y → ¬S Z → pen X ≠ pen Y → pen X ≠ pen Z → pen Y ≠ pen Z →
    ConcurrentOrParallel P (pen X) (pen Y) (pen Z)
  ctr : ∀ c X, S c → ¬S X → c ∈ pen X
  sub : ∀ c c', S c → S c' → c = c'

/-- The data of the pencil construction: a pencil and two distinct points `A`, `B` of one of its
lines. -/
structure PData (pen : P → L) (S : P → Prop) (A B : P) : Prop where
  hp : IsPencil pen S
  hA : ¬S A
  hB : ¬S B
  hBA : B ∈ pen A
  hAB : A ≠ B

/-- The image of a point `X` off the line `pen A`: the common point of the line of the pencil
through `X` and of the parallel to `AX` through `B`. -/
noncomputable def pmap0 (pen : P → L) (A B X : P) : P := meet (pen X) (pline (ln A X : L) B)

/-- The image of a point `X` of the line `pen A`, constructed with the auxiliary point `R`. -/
noncomputable def pmapL (pen : P → L) (A B R X : P) : P :=
  meet (pen A) (pline (ln R X : L) (pmap0 pen A B R))

/-- **The map of the pencil construction.** -/
noncomputable def pencilMap (pen : P → L) (S : P → Prop) (A B R : P) (X : P) : P := by
  classical
  exact if S X then X else if X ∈ pen A then pmapL pen A B R X else pmap0 pen A B X

namespace PData

variable {pen : P → L} {S : P → Prop} {A B : P} (d : PData pen S A B)
include d

theorem mem_p0 {c : P} (hc : S c) : c ∈ pen A := d.hp.ctr c A hc d.hA

theorem A_mem : A ∈ pen A := d.hp.mem A d.hA

theorem pen_eq {X : P} (hX : ¬S X) (h : X ∈ pen A) : pen X = pen A := d.hp.eq A X d.hA hX h

theorem ln_AB : (ln A B : L) = pen A := ln_eq d.hAB d.A_mem d.hBA

theorem A_not_mem {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : A ∉ pen X := fun h =>
  hX0 (by rw [d.hp.eq X A hX d.hA h]; exact d.hp.mem X hX)

theorem pen_ne {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : pen X ≠ pen A := fun e =>
  hX0 (by rw [← e]; exact d.hp.mem X hX)

theorem B_not_ln {X : P} (hX0 : X ∉ pen A) : B ∉ (ln A X : L) := fun h => hX0 (by
  have e : (ln A B : L) = ln A X := ln_eq d.hAB (mem_ln_left A X) h
  rw [← d.ln_AB, e]; exact mem_ln_right A X)

theorem nl {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : ¬LPar P (pen X) (pline (ln A X : L) B) :=
  not_lpar_pline_right (not_lpar_of (d.hp.mem X hX) (mem_ln_right A X) fun e =>
    d.A_not_mem hX hX0 (by rw [e]; exact mem_ln_left A X)) B

theorem pm0_mem {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : pmap0 pen A B X ∈ pen X :=
  meet_mem_left (d.nl hX hX0)

theorem pm0_par {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) :
    pmap0 pen A B X ∈ pline (ln A X : L) B :=
  meet_mem_right (d.nl hX hX0)

theorem pm0_ne {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : pmap0 pen A B X ≠ X := by
  intro e
  have h1 := d.pm0_par hX hX0
  rw [e] at h1
  have h2 : pline (ln A X : L) B = ln A X := by
    rw [← pline_eq_of_mem h1, pline_of_mem (mem_ln_right A X)]
  exact d.B_not_ln hX0 (h2 ▸ mem_pline (ln A X : L) B)

theorem pm0_notS {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : ¬S (pmap0 pen A B X) := by
  intro hc
  have hcB : pmap0 pen A B X ≠ B := fun e => d.hB (e ▸ hc)
  have e1 : (ln (pmap0 pen A B X) B : L) = pline (ln A X : L) B :=
    ln_eq hcB (d.pm0_par hX hX0) (mem_pline _ B)
  have e2 : (ln (pmap0 pen A B X) B : L) = pen A := ln_eq hcB (d.mem_p0 hc) d.hBA
  have h3 : LPar P (pen A) (ln A X : L) := by rw [← e2, e1]; exact pline_lpar _ _
  have h4 : pen A = ln A X := h3 A d.A_mem (mem_ln_left A X)
  exact hX0 (h4 ▸ mem_ln_right A X)

theorem pen_pm0 {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : pen (pmap0 pen A B X) = pen X :=
  d.hp.eq X _ hX (d.pm0_notS hX hX0) (d.pm0_mem hX hX0)

theorem pm0_off {X : P} (hX : ¬S X) (hX0 : X ∉ pen A) : pmap0 pen A B X ∉ pen A := fun h =>
  d.pen_ne hX hX0 ((d.pen_pm0 hX hX0).symm.trans (d.pen_eq (d.pm0_notS hX hX0) h))

/-- The image of `R` does not lie on a line through `R` other than its pencil line. -/
theorem pm0_not_ln {R Y : P} (hR : ¬S R) (hR0 : R ∉ pen A) (hY : Y ∉ pen R) :
    pmap0 pen A B R ∉ (ln R Y : L) := by
  intro h
  have hne : pen R ≠ (ln R Y : L) := fun e => hY (e ▸ mem_ln_right R Y)
  exact d.pm0_ne hR hR0 (eq_of_mem_of_mem hne (d.pm0_mem hR hR0) h (d.hp.mem R hR)
    (mem_ln_left R Y))

/-- **First Desargues step**: the construction maps two points off `pen A` on different lines of
the pencil to points on a parallel to their join. -/
theorem m1 (hD : DesarguesII P) {X Y : P} (hX : ¬S X) (hX0 : X ∉ pen A) (hY : ¬S Y)
    (hY0 : Y ∉ pen A) (hXY : X ≠ Y) (hpXY : pen X ≠ pen Y) :
    pmap0 pen A B Y ∈ pline (ln X Y : L) (pmap0 pen A B X) := by
  have hAX : A ≠ X := fun e => hX0 (e ▸ d.A_mem)
  have hAY : A ≠ Y := fun e => hY0 (e ▸ d.A_mem)
  by_cases hc : Collinear A X Y
  · have hYl : Y ∈ (ln A X : L) := (collinear_iff_mem_ln hAX).1 hc
    have e1 : (ln A Y : L) = ln A X := ln_eq hAY (mem_ln_left A X) hYl
    have e2 : (ln X Y : L) = ln A X := ln_eq hXY (mem_ln_right A X) hYl
    rw [e2, pline_eq_of_mem (d.pm0_par hX hX0)]
    have := d.pm0_par hY hY0; rwa [e1] at this
  · have hBX : B ≠ pmap0 pen A B X := fun e => d.pm0_off hX hX0 (e ▸ d.hBA)
    have hBY : B ≠ pmap0 pen A B Y := fun e => d.pm0_off hY hY0 (e ▸ d.hBA)
    have nc : ¬Collinear B (pmap0 pen A B X) (pmap0 pen A B Y) := by
      intro hcol
      have hX'Y : pmap0 pen A B X ∈ pline (ln A Y : L) B := by
        have := (collinear_iff_mem_ln hBY).1 hcol.swap23
        rwa [ln_eq hBY (mem_pline (ln A Y : L) B) (d.pm0_par hY hY0)] at this
      have k : pline (ln A X : L) B = pline (ln A Y : L) B := by
        rw [← ln_eq hBX (mem_pline _ B) (d.pm0_par hX hX0), ← ln_eq hBX (mem_pline _ B) hX'Y]
      have k2 : (ln A X : L) = ln A Y := lpar_of_pline_eq k A (mem_ln_left A X) (mem_ln_left A Y)
      exact hc ((collinear_iff_mem_ln hAX).2 (k2 ▸ mem_ln_right A Y))
    have hpar := hD A X Y B (pmap0 pen A B X) (pmap0 pen A B Y) (pen A) (pen X) (pen Y) hc nc
      d.A_mem d.hBA (d.hp.mem X hX) (d.pm0_mem hX hX0) (d.hp.mem Y hY) (d.pm0_mem hY hY0)
      (d.pen_ne hX hX0).symm (d.pen_ne hY hY0).symm hpXY
      (d.hp.joins A X Y d.hA hX hY (d.pen_ne hX hX0).symm (d.pen_ne hY hY0).symm hpXY)
      (parPts_of hAX (d.B_not_ln hX0) (d.pm0_par hX hX0))
      (parPts_of hAY (d.B_not_ln hY0) (d.pm0_par hY hY0))
    exact mem_pline_of_parPts hpar hXY

theorem psi_nl {R X : P} (hR0 : R ∉ pen A) (hX0 : X ∈ pen A) :
    ¬LPar P (pen A) (pline (ln R X : L) (pmap0 pen A B R)) :=
  not_lpar_pline_right (not_lpar_of hX0 (mem_ln_right R X) fun e =>
    hR0 (by rw [e]; exact mem_ln_left R X)) _

theorem psi_mem {R X : P} (hR0 : R ∉ pen A) (hX0 : X ∈ pen A) : pmapL pen A B R X ∈ pen A :=
  meet_mem_left (d.psi_nl hR0 hX0)

theorem psi_par {R X : P} (hR0 : R ∉ pen A) (hX0 : X ∈ pen A) :
    pmapL pen A B R X ∈ pline (ln R X : L) (pmap0 pen A B R) :=
  meet_mem_right (d.psi_nl hR0 hX0)

/-- **Second Desargues step**: the image of a point of `pen A` does not depend on the auxiliary
point (first for auxiliary points on different lines of the pencil). -/
theorem m3a (hD : DesarguesII P) {R1 R2 X : P} (h1 : ¬S R1) (h10 : R1 ∉ pen A) (h2 : ¬S R2)
    (h20 : R2 ∉ pen A) (hp12 : pen R1 ≠ pen R2) (hX : ¬S X) (hX0 : X ∈ pen A) :
    pmapL pen A B R1 X = pmapL pen A B R2 X := by
  have hR12 : R1 ≠ R2 := fun e => hp12 (e ▸ rfl)
  have hR1X : R1 ≠ X := fun e => h10 (e ▸ hX0)
  have hR2X : R2 ≠ X := fun e => h20 (e ▸ hX0)
  have hpX : pen X = pen A := d.pen_eq hX hX0
  have hX1 := d.psi_mem (B := B) (R := R1) h10 hX0
  have hX1' := d.psi_par (B := B) (R := R1) h10 hX0
  have hM := d.m1 hD h1 h10 h2 h20 hR12 hp12
  suffices hs : pmapL pen A B R1 X ∈ pline (ln R2 X : L) (pmap0 pen A B R2) from
    eq_meet (d.psi_nl h20 hX0) hX1 hs
  by_cases hc : Collinear R1 R2 X
  · have hXh : X ∈ (ln R1 R2 : L) := (collinear_iff_mem_ln hR12).1 hc
    have e1 : (ln R1 X : L) = ln R1 R2 := ln_eq hR1X (mem_ln_left R1 R2) hXh
    have e2 : (ln R2 X : L) = ln R1 R2 := ln_eq hR2X (mem_ln_right R1 R2) hXh
    rw [e2, pline_eq_of_mem hM, ← e1]; exact hX1'
  · have hR2n : R2 ∉ pen R1 := fun h => hp12 (d.hp.eq R1 R2 h1 h2 h).symm
    have hXn : X ∉ pen R1 := fun h => d.pen_ne h1 h10 ((d.hp.eq R1 X h1 hX h).symm.trans hpX)
    have hp1X : pen R1 ≠ pen X := fun e => d.pen_ne h1 h10 (e.trans hpX)
    have hp2X : pen R2 ≠ pen X := fun e => d.pen_ne h2 h20 (e.trans hpX)
    have hne12 : pmap0 pen A B R1 ≠ pmap0 pen A B R2 := fun e =>
      hp12 ((d.pen_pm0 h1 h10).symm.trans (e ▸ d.pen_pm0 h2 h20))
    have hne1X : pmap0 pen A B R1 ≠ pmapL pen A B R1 X := fun e => d.pm0_off h1 h10 (e ▸ hX1)
    have nc : ¬Collinear (pmap0 pen A B R1) (pmap0 pen A B R2) (pmapL pen A B R1 X) := by
      intro hcol
      have g1 : (ln (pmap0 pen A B R1) (pmap0 pen A B R2) : L) =
          pline (ln R1 R2 : L) (pmap0 pen A B R1) := ln_eq hne12 (mem_pline _ _) hM
      have hX1g := (collinear_iff_mem_ln hne12).1 hcol
      have g2 : (ln (pmap0 pen A B R1) (pmap0 pen A B R2) : L) =
          pline (ln R1 X : L) (pmap0 pen A B R1) :=
        (ln_eq hne1X (mem_ln_left _ _) hX1g).symm.trans (ln_eq hne1X (mem_pline _ _) hX1')
      have k : (ln R1 R2 : L) = ln R1 X :=
        lpar_of_pline_eq (g1.symm.trans g2) R1 (mem_ln_left R1 R2) (mem_ln_left R1 X)
      exact hc ((collinear_iff_mem_ln hR12).2 (k ▸ mem_ln_right R1 X))
    have hpar := hD R1 R2 X (pmap0 pen A B R1) (pmap0 pen A B R2) (pmapL pen A B R1 X)
      (pen R1) (pen R2) (pen X) hc nc (d.hp.mem R1 h1) (d.pm0_mem h1 h10) (d.hp.mem R2 h2)
      (d.pm0_mem h2 h20) (d.hp.mem X hX) (hpX ▸ hX1) hp12 hp1X hp2X
      (d.hp.joins R1 R2 X h1 h2 hX hp12 hp1X hp2X)
      (parPts_of hR12 (d.pm0_not_ln h1 h10 hR2n) hM)
      (parPts_of hR1X (d.pm0_not_ln h1 h10 hXn) hX1')
    exact mem_pline_of_parPts hpar hR2X

theorem m3 (hD : DesarguesII P) {R1 R2 X : P} (h1 : ¬S R1) (h10 : R1 ∉ pen A) (h2 : ¬S R2)
    (h20 : R2 ∉ pen A) (hX : ¬S X) (hX0 : X ∈ pen A) :
    pmapL pen A B R1 X = pmapL pen A B R2 X := by
  by_cases hp12 : pen R1 = pen R2
  · obtain ⟨R3, h3a, h3b⟩ := exists_off_two (P := P) (pen A) (pen R1)
    have h3S : ¬S R3 := fun hc => h3a (d.mem_p0 hc)
    have hp13 : pen R1 ≠ pen R3 := fun e => h3b (by rw [e]; exact d.hp.mem R3 h3S)
    rw [d.m3a hD h1 h10 h3S h3a hp13 hX hX0,
      d.m3a hD h3S h3a h2 h20 (fun e => hp13 (hp12.trans e.symm)) hX hX0]
  · exact d.m3a hD h1 h10 h2 h20 hp12 hX hX0

omit d in
theorem pencilMap_S {R X : P} (hX : S X) : pencilMap pen S A B R X = X := by
  simp [pencilMap, hX]

omit d in
theorem pencilMap_p0 {R X : P} (hX : ¬S X) (h : X ∈ pen A) :
    pencilMap pen S A B R X = pmapL pen A B R X := by
  simp [pencilMap, hX, h]

omit d in
theorem pencilMap_off {R X : P} (hX : ¬S X) (h : X ∉ pen A) :
    pencilMap pen S A B R X = pmap0 pen A B X := by
  simp [pencilMap, hX, h]

/-- **The pencil construction** gives a dilatation mapping `A` to `B`, fixing the centre and
mapping every line of the pencil into itself. -/
theorem pencilMap_spec (hD : DesarguesII P) {R : P} (hR : ¬S R) (hR0 : R ∉ pen A) :
    IsDil (L := L) (pencilMap pen S A B R) ∧ pencilMap pen S A B R A = B ∧
      (∀ c, S c → pencilMap pen S A B R c = c) ∧
      ∀ X, ¬S X → pencilMap pen S A B R X ∈ pen X := by
  have hmem : ∀ X, ¬S X → pencilMap pen S A B R X ∈ pen X := by
    intro X hX
    by_cases h : X ∈ pen A
    · rw [pencilMap_p0 hX h, d.pen_eq hX h]; exact d.psi_mem hR0 h
    · rw [pencilMap_off hX h]; exact d.pm0_mem hX h
  refine ⟨?_, ?_, fun c hc => pencilMap_S hc, hmem⟩
  · intro X Y hXY
    by_cases hSX : S X
    · have hSY : ¬S Y := fun h => hXY (d.hp.sub X Y hSX h)
      rw [pencilMap_S hSX, pline_of_mem (mem_ln_left X Y),
        ln_eq hXY (d.hp.ctr X Y hSX hSY) (d.hp.mem Y hSY)]
      exact hmem Y hSY
    by_cases hSY : S Y
    · rw [pencilMap_S hSY, ln_eq hXY (d.hp.mem X hSX) (d.hp.ctr Y X hSY hSX),
        pline_of_mem (hmem X hSX)]
      exact d.hp.ctr Y X hSY hSX
    by_cases hpp : pen X = pen Y
    · have hYX : Y ∈ pen X := hpp ▸ d.hp.mem Y hSY
      rw [ln_eq hXY (d.hp.mem X hSX) hYX, pline_of_mem (hmem X hSX)]
      exact hpp ▸ hmem Y hSY
    by_cases hX0 : X ∈ pen A
    · have hY0 : Y ∉ pen A := fun h => hpp ((d.pen_eq hSX hX0).trans (d.pen_eq hSY h).symm)
      rw [pencilMap_p0 hSX hX0, pencilMap_off hSY hY0, d.m3 hD hR hR0 hSY hY0 hSX hX0]
      have := d.psi_par (B := B) hY0 hX0
      rw [ln_comm (Ne.symm hXY)] at this
      exact pline_symm this
    · rw [pencilMap_off hSX hX0]
      by_cases hY0 : Y ∈ pen A
      · rw [pencilMap_p0 hSY hY0, d.m3 hD hR hR0 hSX hX0 hSY hY0]
        exact d.psi_par hX0 hY0
      · rw [pencilMap_off hSY hY0]
        exact d.m1 hD hSX hX0 hSY hY0 hXY hpp
  · rw [pencilMap_p0 d.hA d.A_mem]
    have h1 : pline (ln R A : L) (pmap0 pen A B R) = pline (ln A R : L) B := by
      rw [ln_comm (fun e => hR0 (by rw [e]; exact d.A_mem))]
      exact pline_eq_of_mem (d.pm0_par hR hR0)
    exact (eq_meet (d.psi_nl hR0 d.A_mem) d.hBA (h1 ▸ mem_pline _ B)).symm

theorem exists_dil (hD : DesarguesII P) :
    ∃ f : P → P, IsDil (L := L) f ∧ f A = B ∧ (∀ c, S c → f c = c) ∧ ∀ X, ¬S X → f X ∈ pen X := by
  obtain ⟨R, hR0⟩ := exists_not_mem' (P := P) (pen A)
  have hR : ¬S R := fun hc => hR0 (d.mem_p0 hc)
  exact ⟨_, d.pencilMap_spec hD hR hR0⟩

end PData

/-- **Existence of translations** (from the second part of Desargues's theorem, parallel case):
for any two points `A`, `B` there is a translation mapping `A` to `B`. -/
theorem exists_tr (hD : DesarguesII P) (A B : P) : ∃ f : P → P, IsTr (L := L) f ∧ f A = B := by
  by_cases hAB : A = B
  · exact ⟨id, isTr_id, hAB⟩
  set l : L := ln A B
  have hp : IsPencil (fun X : P => pline l X) (fun _ => False) :=
    { mem := fun X _ => mem_pline l X
      eq := fun X Y _ _ h => pline_eq_of_mem h
      joins := fun X Y Z _ _ _ h1 h2 h3 => by
        have k : ∀ U V : P, pline l U ≠ pline l V → ¬Meets (Point := P) (pline l U) (pline l V) :=
          fun U V h => not_meets_of_lpar ((pline_lpar l U).trans (pline_lpar l V).symm) h
        exact Or.inr ⟨k X Y h1, k X Z h2, k Y Z h3⟩
      ctr := fun _ _ h _ => h.elim
      sub := fun _ _ h _ => h.elim }
  have hBA : B ∈ pline l A := by rw [pline_of_mem (mem_ln_left A B)]; exact mem_ln_right A B
  have d : PData (fun X : P => pline l X) (fun _ => False) A B := ⟨hp, id, id, hBA, hAB⟩
  obtain ⟨f, hf, hfA, -, hfm⟩ := d.exists_dil hD
  refine ⟨f, ⟨hf, fun Z hZ => ?_⟩, hfA⟩
  obtain ⟨Y, hY⟩ := exists_not_mem' (P := P) (pline l Z)
  have hZY : Z ≠ Y := fun e => hY (e ▸ mem_pline l Z)
  have h1 := hf Z Y hZY
  rw [hZ, pline_of_mem (mem_ln_left Z Y)] at h1
  have h2 : f Y ∈ pline l Y := hfm Y id
  have hn : ¬LPar P (ln Z Y : L) (pline l Y) := not_lpar_of (mem_ln_right Z Y) (mem_pline l Y)
    fun e => hY (pline_symm (e ▸ mem_ln_left Z Y))
  have hfY : f Y = Y := eq_of_mem_not_lpar hn h1 h2 (mem_ln_right Z Y) (mem_pline l Y)
  exact hf.eq_id hZY hZ hfY

/-- **Existence of dilatations with a given centre** (from the second part of Desargues's theorem,
concurrent case): for points `A`, `B ≠ O` on a line through `O` there is a dilatation fixing `O`
and mapping `A` to `B`. -/
theorem exists_cdil (hD : DesarguesII P) {O A B : P} (hA : A ≠ O) (hB : B ≠ O)
    (hAB : B ∈ (ln O A : L)) : ∃ f : P → P, IsDil (L := L) f ∧ f O = O ∧ f A = B := by
  by_cases hAB' : A = B
  · exact ⟨id, isDil_id, rfl, hAB'⟩
  have hp : IsPencil (fun X : P => (ln O X : L)) (fun X => X = O) :=
    { mem := fun X _ => mem_ln_right O X
      eq := fun X Y _ hY h => ln_eq (Ne.symm hY) (mem_ln_left O X) h
      joins := fun X Y Z _ _ _ _ _ _ =>
        Or.inl ⟨O, mem_ln_left O X, mem_ln_left O Y, mem_ln_left O Z⟩
      ctr := fun c X hc _ => hc ▸ mem_ln_left O X
      sub := fun c c' h h' => h.trans h'.symm }
  have d : PData (fun X : P => (ln O X : L)) (fun X => X = O) A B := ⟨hp, hA, hB, hAB, hAB'⟩
  obtain ⟨f, hf, hfA, hfO, -⟩ := d.exists_dil hD
  exact ⟨f, hf, hfO O rfl, hfA⟩

end Pencil

/-! ## The group of translations -/

section TranslationGroup

variable [HasBetween P] [LineOrder P L] [PlaneParallels P L] [Nonempty L]

/-- Translations with different directions commute. -/
theorem tr_comm_of_not_lpar {f g : P → P} (hf : IsTr (L := L) f) (hg : IsTr (L := L) g) {X : P}
    (hfX : f X ≠ X) (hgX : g X ≠ X) (h : ¬LPar P (ln X (f X) : L) (ln X (g X))) :
    f ∘ g = g ∘ f := by
  refine tr_eq_of (hf.comp hg) (hg.comp hf) (X := X) ?_
  simp only [Function.comp]
  have a1 : f (g X) ∈ pline (ln X (f X) : L) (g X) := hf.trace hfX (g X)
  have a2 : f (g X) ∈ pline (ln X (g X) : L) (f X) := hf.1 X (g X) hgX.symm
  have b1 : g (f X) ∈ pline (ln X (g X) : L) (f X) := hg.trace hgX (f X)
  have b2 : g (f X) ∈ pline (ln X (f X) : L) (g X) := hg.1 X (f X) hfX.symm
  exact eq_of_mem_not_lpar (not_lpar_pline h _ _) a1 a2 b2 b1

/-- **The group of translations is commutative** (uses the existence of translations). -/
theorem tr_comm (hD : DesarguesII P) {f g : P → P} (hf : IsTr (L := L) f)
    (hg : IsTr (L := L) g) : f ∘ g = g ∘ f := by
  obtain ⟨X⟩ := nonempty_point (P := P) (L := L)
  by_cases hfX : f X = X
  · rw [hf.2 X hfX]; rfl
  by_cases hgX : g X = X
  · rw [hg.2 X hgX]; rfl
  by_cases hd : LPar P (ln X (f X) : L) (ln X (g X))
  · obtain ⟨Z, hZ⟩ := exists_not_mem' (P := P) (ln X (f X) : L)
    obtain ⟨h, hh, hhX⟩ := exists_tr (L := L) hD X Z
    have hXZ : X ≠ Z := fun e => hZ (e ▸ mem_ln_left X (f X))
    have hhX' : h X ≠ X := by rw [hhX]; exact hXZ.symm
    have hdh : ¬LPar P (ln X (f X) : L) (ln X (h X)) := by
      rw [hhX]; exact not_lpar_of (mem_ln_left X (f X)) (mem_ln_left X Z) fun e =>
        hZ (e ▸ mem_ln_right X Z)
    have c1 := tr_comm_of_not_lpar hf hh hfX hhX' hdh
    have hgZ : g Z ∈ pline (ln X (f X) : L) Z := by
      rw [pline_congr hd]; exact hg.trace hgX Z
    have hgZn : g Z ∉ (ln X (f X) : L) := fun hm => hZ (by
      have e1 := pline_eq_of_mem hgZ
      rw [pline_of_mem hm] at e1
      rw [e1]; exact mem_pline _ Z)
    have hghX : (g ∘ h) X ≠ X := by
      simp only [Function.comp, hhX]; exact fun e => hgZn (e ▸ mem_ln_left X (f X))
    have hdgh : ¬LPar P (ln X (f X) : L) (ln X ((g ∘ h) X)) := by
      simp only [Function.comp, hhX]
      exact not_lpar_of (mem_ln_left X (f X)) (mem_ln_left X (g Z)) fun e =>
        hgZn (e ▸ mem_ln_right X (g Z))
    have c2 := tr_comm_of_not_lpar hf (hg.comp hh) hfX hghX hdgh
    refine tr_eq_of (hf.comp hg) (hg.comp hf) (X := h X) ?_
    have e2 := congrFun c2 X
    have e1 := congrFun c1 X
    simp only [Function.comp] at e1 e2 ⊢
    rw [e2, ← e1]
  · exact tr_comm_of_not_lpar hf hg hfX hgX hd

/-- **Inverse translations.** -/
theorem tr_inv (hD : DesarguesII P) {f : P → P} (hf : IsTr (L := L) f) :
    ∃ g : P → P, IsTr (L := L) g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨X⟩ := nonempty_point (P := P) (L := L)
  obtain ⟨g, hg, hgX⟩ := exists_tr (L := L) hD (f X) X
  exact ⟨g, hg, (hg.comp hf).2 X (by simp [hgX]), (hf.comp hg).2 (f X) (by simp [hgX])⟩

/-- **Inverse of a dilatation with centre `O`.** -/
theorem cdil_inv (hD : DesarguesII P) {f : P → P} (hf : IsDil (L := L) f) {O A : P}
    (hO : f O = O) (hA : A ≠ O) (hfA : f A ≠ O) :
    ∃ g : P → P, IsDil (L := L) g ∧ g O = O ∧ g ∘ f = id ∧ f ∘ g = id := by
  have hmem : f A ∈ (ln O A : L) := hf.mem_of_fix hO (mem_ln_left O A) (mem_ln_right O A)
  have hmem' : A ∈ (ln O (f A) : L) := by
    rw [ln_eq (Ne.symm hfA) (mem_ln_left O A) hmem]; exact mem_ln_right O A
  obtain ⟨g, hg, hgO, hgA⟩ := exists_cdil (L := L) hD hfA hA hmem'
  exact ⟨g, hg, hgO, (hg.comp hf).eq_id hA.symm (by simp [hO, hgO]) (by simp [hgA]),
    (hf.comp hg).eq_id hfA.symm (by simp [hO, hgO]) (by simp [hgA])⟩

/-- A left-invertible dilatation is a bijection with inverse its left inverse. -/
theorem IsDil.right_inv {f g : P → P} (hg : IsDil (L := L) g) (hgf : g ∘ f = id) :
    f ∘ g = id := by
  have k := congrFun hgf
  simp only [Function.comp, id] at k
  have ginj : Function.Injective g := fun a b hab => by
    by_contra hne
    have hc := hg.eq_const hne hab
    have : g (f a) = g (f b) := by rw [hc]
    rw [k a, k b] at this
    exact hne this
  funext X
  exact ginj (k (g X))

/-- **The conjugate of a translation by an invertible dilatation is a translation.** -/
theorem IsTr.conj {f g τ : P → P} (hf : IsDil (L := L) f) (hg : IsDil (L := L) g)
    (hgf : g ∘ f = id) (hτ : IsTr (L := L) τ) : IsTr (L := L) (f ∘ τ ∘ g) := by
  refine ⟨hf.comp (hτ.1.comp hg), fun Z hZ => ?_⟩
  simp only [Function.comp] at hZ
  have k := congrFun hgf
  simp only [Function.comp, id] at k
  have h1 : τ (g Z) = g Z := by
    have := congrArg g hZ
    rw [k] at this; exact this
  rw [hτ.2 _ h1]
  exact hg.right_inv hgf

end TranslationGroup

end DesAlg

end HilbertFoundations
