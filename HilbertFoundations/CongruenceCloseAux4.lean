import HilbertFoundations.CongruenceCloseAux3

/-!
# Helper module for `CongruenceClose.lean`: the space geometry without planes

This module contains no unit of Hilbert's text. With the literal reading of Axiom I 7 (Basic.lean,
unit `ax.I7`), a single line without any plane satisfies groups I, II, IV of space geometry: the
rational line `LinePt` with one line (`PUnit`), no plane (`PEmpty`), the usual betweenness, the
congruence of segments `|a - b| = |c - d|` and no genuine angle (`LinePt.instSpaceCongruence`).
There four points are "not in a plane" because there is no plane, and the uniqueness clause of
Theorem 18 fails: the figure consisting of the point `0` extends by `1` to a figure congruent to
itself and to its extension by `-1` (`linePt_not_theorem18`).
-/

namespace HilbertFoundations

universe u v w

/-- A list of four distinct elements of a linear order can be arranged increasingly. -/
theorem exists_perm_strictMono_fin4 {α : Type*} [LinearOrder α] (f : Fin 4 → α)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 4), f (σ 0) < f (σ 1) ∧ f (σ 1) < f (σ 2) ∧ f (σ 2) < f (σ 3) := by
  have hs : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  exact ⟨Tuple.sort f, hs (by decide), hs (by decide), hs (by decide)⟩

/-- The points of the **rational line**, the only line of a space geometry without planes. -/
@[ext]
structure LinePt : Type u where
  /-- The coordinate of the point. -/
  val : ℚ

namespace LinePt

instance : HasLines LinePt.{u} PUnit.{v + 1} := ⟨fun _ _ => True⟩
instance : HasPlanes LinePt.{u} PEmpty.{w + 1} := ⟨fun _ e => e.elim⟩
instance : HasBetween LinePt.{u} := ⟨fun x y z => ratBetween x.val y.val z.val⟩
instance : HasSegCong LinePt.{u} := ⟨fun a b c d => |a.val - b.val| = |c.val - d.val|⟩
instance : HasAngCong LinePt.{u} := ⟨fun _ _ _ _ _ _ => True⟩

theorem between_iff {x y z : LinePt} : Between x y z ↔ ratBetween x.val y.val z.val := Iff.rfl

theorem segCong_iff {a b c d : LinePt} :
    SegCong a b c d ↔ |a.val - b.val| = |c.val - d.val| := Iff.rfl

theorem ne_iff {x y : LinePt} : x ≠ y ↔ x.val ≠ y.val := not_congr LinePt.ext_iff

theorem collinear (A B C : LinePt.{u}) : Collinear (Line := PUnit.{v + 1}) A B C :=
  ⟨⟨⟩, trivial, trivial, trivial⟩

instance instConnection : Connection LinePt.{u} PUnit.{v + 1} where
  ax_I1 _ _ _ := ⟨⟨⟩, trivial, trivial⟩
  ax_I2 _ _ _ _ _ _ _ _ _ := rfl
  ax_I7_line _ := ⟨⟨0⟩, ⟨1⟩, ne_iff.2 (by norm_num), trivial, trivial⟩

instance instSpaceConnection : SpaceConnection LinePt.{u} PUnit.{v + 1} PEmpty.{w + 1} :=
  { instConnection with
    ax_I3 := fun A B C h => absurd (collinear A B C) h
    ax_I4 := fun _ _ _ α => α.elim
    ax_I5 := fun _ _ _ α => α.elim
    ax_I6 := fun α => α.elim
    ax_I7_plane := fun α => α.elim
    ax_I7_space := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, fun ⟨α, _⟩ => α.elim⟩ }

instance instLineOrder : LineOrder LinePt.{u} PUnit.{v + 1} :=
  { instConnection with
    between_onLine := fun A B C h => by
      rw [between_iff] at h
      refine ⟨ne_iff.2 ?_, ne_iff.2 ?_, ne_iff.2 ?_, collinear A B C⟩ <;>
        rcases h with h | h <;> intro e <;> linarith [h.1, h.2]
    ax_II1 := fun A B C _ h => Or.symm h
    ax_II2 := fun A C _ _ _ hAC => by
      rcases lt_or_gt_of_ne (ne_iff.1 hAC) with h | h
      · exact ⟨⟨⟨(A.val + C.val) / 2⟩, Or.inl ⟨by show A.val < (A.val + C.val) / 2; linarith,
          by show (A.val + C.val) / 2 < C.val; linarith⟩⟩,
          ⟨⟨2 * C.val - A.val⟩, Or.inl ⟨h, by show C.val < 2 * C.val - A.val; linarith⟩⟩⟩
      · exact ⟨⟨⟨(A.val + C.val) / 2⟩, Or.inr ⟨by show C.val < (A.val + C.val) / 2; linarith,
          by show (A.val + C.val) / 2 < A.val; linarith⟩⟩,
          ⟨⟨2 * C.val - A.val⟩, Or.inr ⟨by show 2 * C.val - A.val < C.val; linarith, h⟩⟩⟩
    ax_II3 := fun A B C _ hAB hAC hBC =>
      ratBetween_axiomII3 (ne_iff.1 hAB) (ne_iff.1 hAC) (ne_iff.1 hBC)
    ax_II4 := fun A B C D _ _ _ _ _ hAB hAC hAD hBC hBD hCD => by
      have hpts : ∀ i, (![A, B, C, D] i).val = ![A.val, B.val, C.val, D.val] i := by
        intro i; fin_cases i <;> rfl
      have hinj : Function.Injective ![A.val, B.val, C.val, D.val] := by
        have h1 := ne_iff.1 hAB
        have h2 := ne_iff.1 hAC
        have h3 := ne_iff.1 hAD
        have h4 := ne_iff.1 hBC
        have h5 := ne_iff.1 hBD
        have h6 := ne_iff.1 hCD
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      obtain ⟨σ, h01, h12, h23⟩ := exists_perm_strictMono_fin4 _ hinj
      refine ⟨σ, ?_, ?_, ?_, ?_⟩ <;> simp only [between_iff, hpts] <;>
        exact Or.inl ⟨by linarith, by linarith⟩ }

instance instSpaceOrder : SpaceOrder LinePt.{u} PUnit.{v + 1} PEmpty.{w + 1} :=
  { instSpaceConnection, instLineOrder with ax_II5 := fun _ _ _ α => α.elim }

/-- On the rational line, the distance is additive along betweenness. -/
theorem abs_add_of_ratBetween {a b c : ℚ} (h : ratBetween a b c) :
    |a - c| = |a - b| + |b - c| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]; ring

/-- Laying off a distance `d > 0` from `a'` on the side of `c'`, on the rational line. -/
theorem layoff_iff {a' c' b' d : ℚ} (hc : a' ≠ c') (hd : 0 < d) :
    (b' ≠ a' ∧ ¬ratBetween c' a' b' ∧ d = |a' - b'|) ↔
      b' = if a' < c' then a' + d else a' - d := by
  rcases lt_or_gt_of_ne hc with h | h
  · simp only [h, ↓reduceIte]
    constructor
    · rintro ⟨hb, hnb, hdb⟩
      have hlt : a' < b' := by
        rcases lt_or_gt_of_ne hb with h' | h'
        · exact absurd (Or.inr ⟨h', h⟩) hnb
        · exact h'
      rw [abs_of_neg (by linarith)] at hdb
      linarith
    · rintro rfl
      refine ⟨by linarith, ?_, ?_⟩
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> linarith
      · rw [abs_of_neg (by linarith)]; ring
  · simp only [not_lt.2 h.le, ↓reduceIte]
    constructor
    · rintro ⟨hb, hnb, hdb⟩
      have hlt : b' < a' := by
        rcases lt_or_gt_of_ne hb with h' | h'
        · exact h'
        · exact absurd (Or.inl ⟨h, h'⟩) hnb
      rw [abs_of_pos (by linarith)] at hdb
      linarith
    · rintro rfl
      refine ⟨by linarith, ?_, ?_⟩
      · rintro (⟨-, h1⟩ | ⟨-, h1⟩) <;> linarith
      · rw [abs_of_pos (by linarith)]; ring

instance instSegmentCongruence : SegmentCongruence LinePt.{u} PUnit.{v + 1} :=
  { instLineOrder with
    segCong_swap := fun A B A' B' h => by
      rw [segCong_iff] at h
      exact ⟨by rw [segCong_iff, abs_sub_comm]; exact h,
        by rw [segCong_iff, abs_sub_comm B'.val]; exact h⟩
    ax_IV1 := fun A B A' C' hAB hC' => by
      have hd : 0 < |A.val - B.val| := abs_pos.2 (sub_ne_zero.2 (ne_iff.1 hAB))
      have key := fun b' : ℚ => layoff_iff (b' := b') (ne_iff.1 hC') hd
      refine ⟨⟨if A'.val < C'.val then A'.val + |A.val - B.val| else A'.val - |A.val - B.val|⟩,
        ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := (key _).2 rfl
        exact ⟨⟨hC'.symm, ne_iff.2 h1, collinear _ _ _, h2⟩, h3⟩
      · rintro Y ⟨⟨-, h1, -, h2⟩, h3⟩
        exact LinePt.ext ((key Y.val).1 ⟨ne_iff.1 h1, h2, h3⟩)
    ax_IV1_refl := fun _ _ _ => rfl
    ax_IV2 := fun _ _ _ _ _ _ _ _ _ h1 h2 => by
      rw [segCong_iff] at h1 h2 ⊢
      exact h1.symm.trans h2
    ax_IV3 := fun A B C A' B' C' h h' h1 h2 => by
      rw [segmentsMeetOnlyAt_iff_between, between_iff] at h h'
      rw [segCong_iff] at h1 h2 ⊢
      rw [abs_add_of_ratBetween h, abs_add_of_ratBetween h', h1, h2] }

instance instAngleCongruence : AngleCongruence LinePt.{u} PUnit.{v + 1} :=
  { instLineOrder with
    angCong_wd := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
    ax_IV4_refl := fun _ _ _ _ => trivial
    ax_IV5 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial }

instance instTriangleCongruence : TriangleCongruence LinePt.{u} PUnit.{v + 1} :=
  { instSegmentCongruence, instAngleCongruence with
    ax_IV6 := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩ }

instance instSpaceAngleCongruence : SpaceAngleCongruence LinePt.{u} PUnit.{v + 1} PEmpty.{w + 1} :=
  { instSpaceOrder, instAngleCongruence with ax_IV4 := fun _ _ _ α' => α'.elim }

/-- **The rational line without planes is a space geometry with groups I, II, IV** (with the
literal reading of I 7). -/
instance instSpaceCongruence : SpaceCongruence LinePt.{u} PUnit.{v + 1} PEmpty.{w + 1} :=
  { instSpaceAngleCongruence, instTriangleCongruence with }

end LinePt

/-- **The uniqueness clause of Theorem 18 fails on the rational line without planes**: the figure
`(0)` is congruent to itself, has "four points not in a plane" (there is no plane), and extends by
the point `1` both to `(0, 1)` and to `(0, -1)`. -/
theorem linePt_not_theorem18 :
    ¬Theorem18Statement (L := PUnit.{v + 1}) (Pl := PEmpty.{w + 1}) LinePt.{u} := by
  intro hT
  let f : Fin 1 → LinePt.{u} := fun _ => ⟨0⟩
  have hfi : Function.Injective f := fun i j _ => Subsingleton.elim i j
  have hc : CongruentFigures (L := PUnit.{v + 1}) f f :=
    ⟨hfi, hfi, fun i j hij => absurd (Subsingleton.elim i j) hij,
      fun i j k h _ => absurd (LinePt.collinear _ _ _) h⟩
  have hr : ∀ q : ℚ, q ≠ 0 → (⟨q⟩ : LinePt.{u}) ∉ Set.range f := by
    rintro q hq ⟨i, hi⟩
    exact hq (congrArg LinePt.val hi).symm
  have c1 := congruentFigures_snoc
    (spaceFrame (P := LinePt.{u}) (L := PUnit.{v + 1}) (Pl := PEmpty.{w + 1})) hc
    (hr 1 one_ne_zero) (hr 1 one_ne_zero) (fun _ => rfl)
  have c2 := congruentFigures_snoc
    (spaceFrame (P := LinePt.{u}) (L := PUnit.{v + 1}) (Pl := PEmpty.{w + 1})) hc
    (hr 1 one_ne_zero) (hr (-1) (by norm_num))
    (fun _ => by show |(0 : ℚ) - 1| = |(0 : ℚ) - -1|; norm_num)
  have e := (hT 1 f f hc ⟨1⟩ (hr 1 one_ne_zero)).2 ⟨0, 0, 0, 0, fun ⟨α, _⟩ => α.elim⟩ ⟨1⟩ ⟨-1⟩
    c1 c2
  have : (1 : ℚ) = -1 := congrArg LinePt.val e
  norm_num at this

end HilbertFoundations
