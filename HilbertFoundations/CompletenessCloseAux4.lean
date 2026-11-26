import HilbertFoundations.CompletenessCloseAux3
import HilbertFoundations.DesarguesAlgebraAux3

/-!
# Helper module for `CompletenessClose.lean` (4): the co-ordinate of a line (linear axioms only)

This module contains no unit of Hilbert's text. A geometry of space without planes consists of the
points of one line (I 3), and the co-ordinates of `CompletenessCloseAux.lean` (which use a plane) are
not available. Here a real co-ordinate is constructed from the *linear* axioms alone (I 1–2, II 1–4,
IV 1–3, V), for a system all of whose points lie on one line (`CC.LFrame`):

* the order of sequence of the points (`CC.LFrame.linOrd`, from `OrderLin.lineLt`);
* the **translations** of the line: the strictly increasing maps preserving the congruence of
  segments (`CC.LFrame.IsTr`). A translation is determined by the image of one point
  (`IsTr.unique`), and there is one carrying any point to any point (`exists_tr`);
* hence the points form a group (`X + Y` is the image of `Y` under the translation carrying `O` to
  `X`), which is commutative (`add_comm'`, by IV 3 in the form `seg_on_line`), ordered and, by
  Axiom V, archimedean;
* by Hölder's theorem (mathlib: `Archimedean.exists_orderAddMonoidHom_real_injective`) the group
  embeds into `ℝ`: `CC.exists_line_coord` gives a strictly increasing `f : P → ℝ` with
  `AB ≡ CD ↔ |f B - f A| = |f D - f C|`.
-/

set_option linter.unusedSectionVars false

namespace HilbertFoundations

namespace CC

universe u v

/-- A system of points all lying on one line `a`, with two distinct reference points `O`, `E`. -/
class LFrame (P : Type u) (L : Type v) [HasLines P L] where
  a : L
  O : P
  E : P
  hOE : O ≠ E
  hall : ∀ X : P, X ∈ a

namespace LFrame

section Order

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [hO : LineOrder P L]
  [F : LFrame P L]

include hO F

/-- The order of sequence of the points in which `O` precedes `E`. -/
@[instance_reducible] noncomputable def linOrd : LinearOrder P :=
  @LinearOrder.lift' _ _ (OrderLin.lineOrder (F.hall F.O) (F.hall F.E) F.hOE)
    (fun X => (⟨X, F.hall X⟩ : {X : P // X ∈ F.a})) (fun _ _ h => congrArg Subtype.val h)

attribute [local instance] linOrd

theorem col (X Y Z : P) : Collinear (Line := L) X Y Z := ⟨F.a, F.hall X, F.hall Y, F.hall Z⟩

theorem lt_iff (X Y : P) : X < Y ↔ OrderLin.lineLt F.O F.E X Y := Iff.rfl

theorem between_iff {X Y Z : P} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) :
    Between X Y Z ↔ (X < Y ∧ Y < Z) ∨ (Z < Y ∧ Y < X) := by
  simp only [lt_iff (L := L)]
  exact OrderLin.between_iff_lineLt (F.hall F.O) (F.hall F.E) F.hOE (F.hall X) (F.hall Y)
    (F.hall Z) hXY hXZ hYZ

theorem between_of_lt {X Y Z : P} (h1 : X < Y) (h2 : Y < Z) : Between X Y Z :=
  (between_iff (L := L) h1.ne (h1.trans h2).ne h2.ne).2 (Or.inl ⟨h1, h2⟩)

theorem lt_of_between {X Y Z : P} (h : Between X Y Z) : (X < Y ∧ Y < Z) ∨ (Z < Y ∧ Y < X) :=
  (between_iff (L := L) (ne12_of_between (Line := L) h) (ne13_of_between (Line := L) h)
    (ne23_of_between (Line := L) h)).1 h

theorem between_iff' {X M Y : P} (hX : X ≠ M) (hY : Y ≠ M) :
    Between X M Y ↔ (X < M ∧ M < Y) ∨ (Y < M ∧ M < X) := by
  by_cases hXY : X = Y
  · subst hXY
    constructor
    · intro h; exact absurd h (not_between_self (Line := L))
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact absurd h1 (lt_asymm h2)
  · exact between_iff (L := L) hX hXY (Ne.symm hY)

/-- Half-rays in terms of the order of sequence. -/
theorem mem_ray_iff {M X Y : P} (hX : X ≠ M) (hY : Y ≠ M) :
    Y ∈ ray (Line := L) M X ↔ (M < X ↔ M < Y) := by
  have hb := between_iff' (L := L) hX hY
  constructor
  · rintro ⟨-, -, -, hn⟩
    rw [hb] at hn
    constructor
    · intro h1; by_contra h2; exact hn (Or.inr ⟨lt_of_le_of_ne (not_lt.1 h2) hY, h1⟩)
    · intro h1; by_contra h2; exact hn (Or.inl ⟨lt_of_le_of_ne (not_lt.1 h2) hX, h1⟩)
  · intro h
    refine ⟨hX, hY, col _ _ _, ?_⟩
    rw [hb]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact lt_asymm h1 (h.2 h2)
    · exact lt_asymm h1 (h.1 h2)

theorem exists_ne' (X : P) : ∃ W : P, W ≠ X := by
  by_cases h : X = F.O
  · exact ⟨F.E, fun e => F.hOE (h.symm.trans e.symm)⟩
  · exact ⟨F.O, Ne.symm h⟩

theorem exists_gt' (X : P) : ∃ Y : P, X < Y := by
  obtain ⟨W, hW⟩ := exists_ne' (L := L) X
  rcases lt_or_gt_of_ne hW with h | h
  · obtain ⟨D, hD⟩ := exists_beyond (Line := L) hW
    rcases lt_of_between (L := L) hD with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact ⟨D, h2⟩
    · exact absurd h (lt_asymm h2)
  · exact ⟨W, h⟩

theorem exists_lt' (X : P) : ∃ Y : P, Y < X := by
  obtain ⟨W, hW⟩ := exists_ne' (L := L) X
  rcases lt_or_gt_of_ne hW with h | h
  · exact ⟨W, h⟩
  · obtain ⟨D, hD⟩ := exists_beyond (Line := L) hW
    rcases lt_of_between (L := L) hD with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h (lt_asymm h1)
    · exact ⟨D, h1⟩

end Order

section Translations

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] [F : LFrame P L]

include hS F

attribute [local instance] linOrd

/-- A **translation** of the line: a strictly increasing map preserving congruence. -/
def IsTr (f : P → P) : Prop := StrictMono f ∧ ∀ X Y : P, X ≠ Y → SegCong X Y (f X) (f Y)

theorem isTr_id : IsTr (L := L) (id : P → P) :=
  ⟨strictMono_id, fun _ _ h => segCong_refl (Line := L) h⟩

theorem IsTr.comp {f g : P → P} (hf : IsTr (L := L) f) (hg : IsTr (L := L) g) :
    IsTr (L := L) (f ∘ g) :=
  ⟨hf.1.comp hg.1, fun X Y h =>
    segCong_trans (L := L) h (hg.1.injective.ne h) (hf.1.injective.ne (hg.1.injective.ne h))
      (hg.2 X Y h) (hf.2 _ _ (hg.1.injective.ne h))⟩

/-- A translation is determined by the image of one point. -/
theorem IsTr.unique {f g : P → P} (hf : IsTr (L := L) f) (hg : IsTr (L := L) g) {A : P}
    (h : f A = g A) : f = g := by
  funext Y
  by_cases hY : Y = A
  · rw [hY, h]
  have h1 := hf.2 A Y (Ne.symm hY)
  have h2 := hg.2 A Y (Ne.symm hY)
  rw [← h] at h2
  have n1 : f Y ≠ f A := hf.1.injective.ne hY
  have n2 : g Y ≠ f A := by rw [h]; exact hg.1.injective.ne hY
  have hr : g Y ∈ ray (Line := L) (f A) (f Y) := by
    rw [mem_ray_iff (L := L) n1 n2]
    constructor
    · intro h3
      have h4 := hf.1.lt_iff_lt.1 h3
      rw [h]; exact hg.1 h4
    · intro h3
      rw [h] at h3
      exact hf.1 (hg.1.lt_iff_lt.1 h3)
  exact eq_of_segCong_ray (L := L) (Ne.symm hY) (mem_ray_self' (L := L) n1) hr h1 h2

/-- A map of the line preserving congruence and injective is strictly monotone or antitone. -/
theorem mono_or_anti {f : P → P} (hinj : Function.Injective f)
    (hiso : ∀ X Y : P, X ≠ Y → SegCong X Y (f X) (f Y)) : StrictMono f ∨ StrictAnti f := by
  refine DesAlg.strictMono_or_strictAnti f hinj fun x y z h1 h2 => ?_
  have hb := between_of_lt (L := L) h1 h2
  have hb' : Between (f x) (f y) (f z) :=
    between_of_segCong (L := L) hb (col _ _ _) (hinj.ne h1.ne) (hinj.ne h2.ne)
      (hinj.ne (h1.trans h2).ne) (hiso _ _ h1.ne) (hiso _ _ h2.ne) (hiso _ _ (h1.trans h2).ne)
  exact lt_of_between (L := L) hb'

/-- **There is a translation carrying any point to any point.** -/
theorem exists_tr (A B : P) : ∃ f : P → P, IsTr (L := L) f ∧ f A = B := by
  classical
  obtain ⟨Cp, hCp⟩ := exists_gt' (L := L) B
  obtain ⟨Cm, hCm⟩ := exists_lt' (L := L) B
  have hlay : ∀ Y : P, Y ≠ A → ∃ Z : P, Z ≠ B ∧ (B < Z ↔ A < Y) ∧ SegCong A Y B Z := by
    intro Y hY
    by_cases hAY : A < Y
    · obtain ⟨Z, hZ, hc⟩ := segCong_layoff (L := L) (Ne.symm hY) hCp.ne
      have hZB := ne_of_mem_ray (L := L) hZ
      have h1 := (mem_ray_iff (L := L) hCp.ne' hZB).1 hZ
      exact ⟨Z, hZB, ⟨fun _ => hAY, fun _ => h1.1 hCp⟩, hc⟩
    · obtain ⟨Z, hZ, hc⟩ := segCong_layoff (L := L) (Ne.symm hY) hCm.ne'
      have hZB := ne_of_mem_ray (L := L) hZ
      have h1 := (mem_ray_iff (L := L) hCm.ne hZB).1 hZ
      exact ⟨Z, hZB, ⟨fun h => absurd (h1.2 h) (lt_asymm hCm), fun h => absurd h hAY⟩, hc⟩
  let f : P → P := fun Y => if h : Y = A then B else Classical.choose (hlay Y h)
  have fA : f A = B := by simp [f]
  have fspec : ∀ Y, Y ≠ A → f Y ≠ B ∧ (B < f Y ↔ A < Y) ∧ SegCong A Y B (f Y) := by
    intro Y h
    simp only [f, h, ↓reduceDIte]
    exact Classical.choose_spec (hlay Y h)
  have hiso : ∀ X Y : P, X ≠ Y → SegCong X Y (f X) (f Y) := by
    intro X Y hXY
    by_cases hX : X = A
    · have hYA : Y ≠ A := fun e => hXY (hX.trans e.symm)
      rw [hX, fA]; exact (fspec Y hYA).2.2
    by_cases hY : Y = A
    · rw [hY, fA]; exact segCong_swap (L := L) (fspec X hX).2.2
    obtain ⟨x1, x2, x3⟩ := fspec X hX
    obtain ⟨y1, y2, y3⟩ := fspec Y hY
    refine seg_on_line (L := L) x3 y3 hX hY x1 y1 (col _ _ _) (col _ _ _) hXY ?_
    rw [mem_ray_iff (L := L) hY hX, mem_ray_iff (L := L) y1 x1, y2, x2]
  have hinj : Function.Injective f := by
    intro X Y e
    by_contra hXY
    by_cases hX : X = A
    · have hYA : Y ≠ A := fun e' => hXY (hX.trans e'.symm)
      rw [hX, fA] at e
      exact (fspec Y hYA).1 e.symm
    by_cases hY : Y = A
    · rw [hY, fA] at e
      exact (fspec X hX).1 e
    obtain ⟨x1, x2, x3⟩ := fspec X hX
    obtain ⟨y1, y2, y3⟩ := fspec Y hY
    rw [← e] at y1 y2 y3
    have hc : SegCong A X A Y :=
      segCong_trans (L := L) (Ne.symm hX) (Ne.symm x1) (Ne.symm hY) x3
        (segCong_symm (L := L) (Ne.symm hY) (Ne.symm x1) y3)
    have hr : Y ∈ ray (Line := L) A X := (mem_ray_iff (L := L) hX hY).2 (x2.symm.trans y2)
    exact hXY (eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hX) hr hc)
  refine ⟨f, ⟨?_, hiso⟩, fA⟩
  rcases mono_or_anti (L := L) hinj hiso with h | h
  · exact h
  · exfalso
    obtain ⟨Y, hY⟩ := exists_gt' (L := L) A
    have h1 := (fspec Y hY.ne').2.1.2 hY
    have h2 := h hY
    rw [fA] at h2
    exact lt_asymm h1 h2

/-- The translation carrying `O` to `X`. -/
noncomputable def tr (X : P) : P → P := Classical.choose (exists_tr (L := L) F.O X)

theorem tr_isTr (X : P) : IsTr (L := L) (tr (L := L) X) :=
  (Classical.choose_spec (exists_tr (L := L) F.O X)).1

theorem tr_O (X : P) : tr (L := L) X F.O = X :=
  (Classical.choose_spec (exists_tr (L := L) F.O X)).2

theorem tr_zero : tr (L := L) (F.O : P) = id :=
  IsTr.unique (L := L) (tr_isTr _) isTr_id (A := F.O) (tr_O _)

theorem tr_tr (X Y : P) : tr (L := L) X ∘ tr (L := L) Y = tr (L := L) (tr (L := L) X Y) :=
  IsTr.unique (L := L) ((tr_isTr X).comp (tr_isTr Y)) (tr_isTr _) (A := F.O)
    (by simp only [Function.comp_apply, tr_O])

/-- The point carried to `O` by the translation carrying `O` to `X`. -/
noncomputable def ng (X : P) : P := Classical.choose (exists_tr (L := L) X F.O) F.O

theorem tr_ng (X : P) : tr (L := L) (ng (L := L) X) X = F.O := by
  have h := Classical.choose_spec (exists_tr (L := L) X F.O)
  have e : tr (L := L) (ng (L := L) X) = Classical.choose (exists_tr (L := L) X F.O) :=
    IsTr.unique (L := L) (tr_isTr _) h.1 (A := F.O) (tr_O _)
  rw [e]; exact h.2

/-- **The group of the points of the line** (`O` is the zero). -/
@[instance_reducible] noncomputable def addGroup : AddGroup P :=
  letI : Add P := ⟨fun X Y => tr (L := L) X Y⟩
  letI : Neg P := ⟨ng (L := L)⟩
  letI : Zero P := ⟨F.O⟩
  AddGroup.ofLeftAxioms
    (fun X Y Z => (congrFun (tr_tr (L := L) X Y) Z).symm)
    (fun X => congrFun (tr_zero (L := L)) X)
    (fun X => tr_ng (L := L) X)

end Translations

section Group

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] [F : LFrame P L]

include hS F

attribute [local instance] linOrd addGroup

theorem add_def (X Y : P) : X + Y = tr (L := L) X Y := rfl

theorem zero_def : (0 : P) = F.O := rfl

theorem add_lt_add_iff' (X : P) {Y Z : P} : X + Y < X + Z ↔ Y < Z :=
  (tr_isTr (L := L) X).1.lt_iff_lt

theorem add_cong (X : P) {Y Z : P} (h : Y ≠ Z) : SegCong Y Z (X + Y) (X + Z) :=
  (tr_isTr (L := L) X).2 Y Z h

theorem lt_add_iff' (X Y : P) : X < X + Y ↔ 0 < Y := by
  have h := add_lt_add_iff' (L := L) X (Y := 0) (Z := Y)
  rwa [add_zero] at h

theorem lt_zero_iff_not {X : P} (hX : X ≠ 0) : X < 0 ↔ ¬(0 : P) < X :=
  ⟨fun h => lt_asymm h, fun h => lt_of_le_of_ne (not_lt.1 h) hX⟩

theorem neg_pos_iff' {X : P} (hX : X ≠ 0) : 0 < -X ↔ ¬(0 : P) < X := by
  have h := add_lt_add_iff' (L := L) X (Y := 0) (Z := -X)
  rw [add_zero, add_neg_cancel] at h
  rw [← h, lt_zero_iff_not (L := L) hX]

theorem segCong_neg {X : P} (hX : X ≠ 0) : SegCong (0 : P) X 0 (-X) := by
  have h := add_cong (L := L) (-X) (Ne.symm hX)
  rw [add_zero, neg_add_cancel] at h
  exact segCong_swap_right (Line := L) h

theorem neg_cong {X Y : P} (hXY : X ≠ Y) : SegCong X Y (-X) (-Y) := by
  by_cases hX : X = 0
  · subst hX; rw [neg_zero]; exact segCong_neg (L := L) (Ne.symm hXY)
  by_cases hY : Y = 0
  · subst hY; rw [neg_zero]; exact segCong_swap (L := L) (segCong_neg (L := L) hXY)
  refine seg_on_line (L := L) (segCong_neg (L := L) hX) (segCong_neg (L := L) hY) hX hY
    (neg_ne_zero.2 hX) (neg_ne_zero.2 hY) (col _ _ _) (col _ _ _) hXY ?_
  rw [mem_ray_iff (L := L) hY hX, mem_ray_iff (L := L) (neg_ne_zero.2 hY) (neg_ne_zero.2 hX),
    neg_pos_iff' (L := L) hX, neg_pos_iff' (L := L) hY, not_iff_not]

theorem neg_anti : StrictAnti (fun X : P => -X) := by
  rcases mono_or_anti (L := L) (f := fun X : P => -X) neg_injective
    (fun X Y h => neg_cong (L := L) h) with h | h
  · exfalso
    obtain ⟨Y, hY⟩ := exists_gt' (L := L) (0 : P)
    have h1 : -(0 : P) < -Y := h hY
    rw [neg_zero, neg_pos_iff' (L := L) hY.ne'] at h1
    exact h1 hY
  · exact h

/-- **The group of the points of a line is commutative.** -/
theorem add_comm' (X Y : P) : X + Y = Y + X := by
  by_cases hX : X = 0
  · subst hX; rw [zero_add, add_zero]
  by_cases hY : Y = 0
  · subst hY; rw [zero_add, add_zero]
  by_cases hZ : X + Y = 0
  · rw [hZ, eq_neg_of_add_eq_zero_right hZ, neg_add_cancel]
  by_cases hZ' : Y + X = 0
  · rw [hZ', eq_neg_of_add_eq_zero_right hZ', neg_add_cancel]
  have c1 : SegCong X 0 Y (Y + X) := by
    have h := add_cong (L := L) Y (Ne.symm hX)
    rw [add_zero] at h
    exact segCong_swap_left (Line := L) h
  have nXY : X + Y ≠ X := fun e => hY (by simpa using e)
  have nYX : Y + X ≠ Y := fun e => hX (by simpa using e)
  have c2 : SegCong X (X + Y) Y 0 := by
    have h := add_cong (L := L) X (Ne.symm hY)
    rw [add_zero] at h
    exact segCong_swap_right (Line := L) (segCong_symm (L := L) (Ne.symm hY) (Ne.symm nXY) h)
  have c3 : SegCong (0 : P) (X + Y) (Y + X) 0 := by
    refine seg_on_line (L := L) c1 c2 (Ne.symm hX) nXY nYX (Ne.symm hY) (col _ _ _) (col _ _ _)
      (Ne.symm hZ) ?_
    rw [mem_ray_iff (L := L) nXY (Ne.symm hX), mem_ray_iff (L := L) (Ne.symm hY) nYX,
      lt_add_iff' (L := L), lt_add_iff' (L := L), lt_zero_iff_not (L := L) hX,
      lt_zero_iff_not (L := L) hY]
    by_cases ha : (0 : P) < X <;> by_cases hb : (0 : P) < Y <;> simp [ha, hb]
  have hs : (0 : P) < X + Y ↔ 0 < Y + X := by
    have h1 : (0 : P) < X + Y ↔ -X < Y := by
      have h := add_lt_add_iff' (L := L) X (Y := -X) (Z := Y)
      rw [add_neg_cancel] at h
      exact h
    have h2 : (0 : P) < Y + X ↔ -Y < X := by
      have h := add_lt_add_iff' (L := L) Y (Y := -Y) (Z := X)
      rw [add_neg_cancel] at h
      exact h
    rw [h1, h2]
    constructor
    · intro h
      have := neg_anti (L := L) h
      simpa using this
    · intro h
      have := neg_anti (L := L) h
      simpa using this
  have hr : Y + X ∈ ray (Line := L) (0 : P) (X + Y) := (mem_ray_iff (L := L) hZ hZ').2 hs
  exact eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hZ) hr
    (segCong_swap_right (Line := L) c3)

end Group

section CommGroup

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] [F : LFrame P L]

include hS F

/-- The commutative group of the points of the line. -/
@[instance_reducible] noncomputable def addCommGroup : AddCommGroup P :=
  { addGroup (L := L) with add_comm := add_comm' (L := L) }

attribute [local instance] linOrd addCommGroup

theorem add_cong_c (X : P) {Y Z : P} (h : Y ≠ Z) : SegCong Y Z (X + Y) (X + Z) :=
  add_cong (L := L) X h

theorem segCong_neg_c {X : P} (hX : X ≠ 0) : SegCong (0 : P) X 0 (-X) := segCong_neg (L := L) hX

theorem neg_pos_iff_c {X : P} (hX : X ≠ 0) : 0 < -X ↔ ¬(0 : P) < X := neg_pos_iff' (L := L) hX

theorem lt_add_iff_c (X Y : P) : X < X + Y ↔ 0 < Y := lt_add_iff' (L := L) X Y

theorem isOrderedAddMonoid : IsOrderedAddMonoid P where
  add_le_add_left a b h c := by
    rw [add_comm a c, add_comm b c]
    exact (tr_isTr (L := L) c).1.monotone h

theorem archimedean [hV : Archimedes P L] : Archimedean P := by
  haveI := isOrderedAddMonoid (P := P) (L := L)
  constructor
  intro x y hy
  by_cases hxy : x ≤ y
  · exact ⟨1, by rwa [one_nsmul]⟩
  have hyx : y < x := not_le.1 hxy
  have hstep : ∀ n : ℕ, n • y < (n + 1) • y := by
    intro n
    rw [succ_nsmul]
    exact (lt_add_iff_c (L := L) _ _).2 hy
  have hc0 : ∀ n : ℕ, SegCong (0 : P) y (n • y) ((n + 1) • y) := by
    intro n
    have h := add_cong_c (L := L) (n • y) hy.ne
    rwa [add_zero, ← succ_nsmul] at h
  obtain ⟨n, hn⟩ := Archimedes.ax_V (Line := L) (fun n : ℕ => n • y) x
    (by
      show Between ((0 : ℕ) • y) ((1 : ℕ) • y) x
      rw [zero_nsmul, one_nsmul]
      exact between_of_lt (L := L) hy hyx)
    (fun n => between_of_lt (L := L) (hstep n) (hstep (n + 1)))
    (fun m n => segCong_trans (L := L) (hstep m).ne hy.ne (hstep n).ne
      (segCong_symm (L := L) hy.ne (hstep m).ne (hc0 m)) (hc0 n))
  refine ⟨n, ?_⟩
  have hn' : Between ((0 : ℕ) • y) x (n • y) := hn
  rw [zero_nsmul] at hn'
  rcases lt_of_between (L := L) hn' with ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h2.le
  · exact absurd (hy.trans hyx) (lt_asymm h2)

/-- **The real co-ordinate of a line** (Hölder's theorem). -/
theorem exists_coord [hV : Archimedes P L] : ∃ f : P → ℝ, StrictMono f ∧
    ∀ A B C D : P, A ≠ B → C ≠ D → (SegCong A B C D ↔ |f B - f A| = |f D - f C|) := by
  haveI := isOrderedAddMonoid (P := P) (L := L)
  haveI := archimedean (P := P) (L := L)
  obtain ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective P
  have hmono : StrictMono f := (OrderHomClass.mono f).strictMono_of_injective hf
  refine ⟨f, hmono, ?_⟩
  intro A B C D hAB hCD
  have hu : -A + B ≠ 0 := fun e => hAB (neg_add_eq_zero.1 e)
  have hv : -C + D ≠ 0 := fun e => hCD (neg_add_eq_zero.1 e)
  have cA : SegCong A B 0 (-A + B) := by
    have h := add_cong_c (L := L) (-A) hAB
    rwa [neg_add_cancel] at h
  have cC : SegCong C D 0 (-C + D) := by
    have h := add_cong_c (L := L) (-C) hCD
    rwa [neg_add_cancel] at h
  have fu : f (-A + B) = f B - f A := by rw [map_add, map_neg]; ring
  have fv : f (-C + D) = f D - f C := by rw [map_add, map_neg]; ring
  rw [← fu, ← fv]
  constructor
  · intro h
    have h0 : SegCong (0 : P) (-A + B) 0 (-C + D) :=
      segCong_trans (L := L) (Ne.symm hu) hAB (Ne.symm hv)
        (segCong_symm (L := L) hAB (Ne.symm hu) cA)
        (segCong_trans (L := L) hAB hCD (Ne.symm hv) h cC)
    by_cases hs : ((0 : P) < -A + B ↔ 0 < -C + D)
    · have hr : -C + D ∈ ray (Line := L) (0 : P) (-A + B) := (mem_ray_iff (L := L) hu hv).2 hs
      rw [eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hu) hr h0]
    · have hr : -(-C + D) ∈ ray (Line := L) (0 : P) (-A + B) := by
        rw [mem_ray_iff (L := L) hu (neg_ne_zero.2 hv), neg_pos_iff_c (L := L) hv]
        by_cases ha : (0 : P) < -A + B <;> by_cases hb : (0 : P) < -C + D <;> simp [ha, hb] at hs ⊢
      have h1 : SegCong (0 : P) (-A + B) 0 (-(-C + D)) :=
        segCong_trans (L := L) (Ne.symm hu) (Ne.symm hv) (Ne.symm (neg_ne_zero.2 hv)) h0
          (segCong_neg_c (L := L) hv)
      rw [eq_of_segCong_ray' (L := L) (mem_ray_self' (L := L) hu) hr h1, map_neg, abs_neg]
  · intro h
    have h0 : SegCong (0 : P) (-A + B) 0 (-C + D) := by
      rcases abs_eq_abs.1 h with e | e
      · rw [hf e]; exact segCong_refl (Line := L) (Ne.symm hv)
      · have e' : -A + B = -(-C + D) := hf (by rw [e, map_neg])
        rw [e']
        exact segCong_symm (L := L) (Ne.symm hv) (Ne.symm (neg_ne_zero.2 hv))
          (segCong_neg_c (L := L) hv)
    exact segCong_trans (L := L) hAB (Ne.symm hu) hCD cA
      (segCong_trans (L := L) (Ne.symm hu) (Ne.symm hv) hCD h0
        (segCong_symm (L := L) hCD (Ne.symm hv) cC))

end CommGroup

end LFrame

section LineCoord

variable {P : Type u} {L : Type v} [HasLines P L] [HasBetween P] [HasSegCong P]
  [hS : SegmentCongruence P L] [hV : Archimedes P L]

include hS hV

/-- **A system of points of one line satisfying the linear axioms I 1–2, II 1–4, IV 1–3, V has a
real co-ordinate**: an injective `f : P → ℝ` carrying betweenness to betweenness of real numbers
and congruence of segments to equality of distances. -/
theorem exists_line_coord (a : L) (hall : ∀ X : P, X ∈ a) {O E : P} (hOE : O ≠ E) :
    ∃ f : P → ℝ, Function.Injective f ∧
      (∀ A B C : P, Between A B C → (f A < f B ∧ f B < f C) ∨ (f C < f B ∧ f B < f A)) ∧
      ∀ A B C D : P, A ≠ B → C ≠ D → (SegCong A B C D ↔ |f B - f A| = |f D - f C|) := by
  letI F : LFrame P L := ⟨a, O, E, hOE, hall⟩
  letI := LFrame.linOrd (P := P) (L := L)
  obtain ⟨f, hmono, hc⟩ := LFrame.exists_coord (P := P) (L := L)
  refine ⟨f, hmono.injective, ?_, hc⟩
  intro A B C h
  rcases LFrame.lt_of_between (L := L) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hmono h1, hmono h2⟩
  · exact Or.inr ⟨hmono h1, hmono h2⟩

end LineCoord

end CC

end HilbertFoundations
