import HilbertFoundations.Order
import HilbertFoundations.NonDesarguesAux6

/-!
# Helper for the co-ordinates of space (§ 17, § 30): parallels and parallel projections in space

Helper module of `CoordinatesClose.lean` (units `s17.space`, `s30.any_dimension`). Synthetic part,
from groups I and III of a geometry of space (and II for the last section):

* `SpaceCoord.Par`: parallel lines of space (equal, or in one plane without a common point);
  through every point there is exactly one parallel to a line (`exists_par`, `par_unique`), and
  parallelism is transitive (`par_trans`, the classical argument with three planes).
* `SpaceCoord.proj`: the parallel projection of space onto a plane `α` along a line `d` that cuts
  `α`. A line not parallel to `d` is mapped one-to-one onto a line of `α` (`proj_line`), a line
  parallel to `d` to a point (`proj_const`).
* `proj_pair`: for two directions `d₁`, `d₂` through a point `O` of `α`, the two projections of a
  point are equal or lie on a line of `α` that is the trace `m₀` of the plane `d₁d₂` or does not
  meet it.
* `exists_three_directions`: three lines through a point of `α`, not in `α` and not in one plane.
* `proj_between`: parallel projection preserves and reflects betweenness on a line (II 5).
-/

namespace HilbertFoundations

namespace SpaceCoord

open SpaceDesargues

universe u v w

variable {P : Type u} {L : Type v} {Pl : Type w} [HasLines P L] [HasPlanes P Pl]

section Incidence

variable [hS : SpaceConnection P L Pl]
include hS

omit [HasPlanes P Pl] hS in
/-- A line all of whose points lie on another line is that line. -/
theorem line_eq_of_subset [Connection P L] {a b : L} (h : ∀ X : P, X ∈ a → X ∈ b) : a = b := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_points (Point := P) a
  exact line_unique hAB hA hB (h A hA) (h B hB)

/-- The plane through a line and a point off it is unique. -/
theorem plane_eq_of_line_point {a : L} {A : P} (hA : A ∉ a) {γ γ' : Pl}
    (h : LiesInPlane (Point := P) a γ) (hAγ : A ∈ γ) (h' : LiesInPlane (Point := P) a γ')
    (hAγ' : A ∈ γ') : γ = γ' :=
  (theorem2_line_point hA).unique ⟨h, hAγ⟩ ⟨h', hAγ'⟩

/-- The plane through two distinct lines with a common point is unique. -/
theorem plane_eq_of_two_lines {a b : L} (hab : a ≠ b) {A : P} (hAa : A ∈ a) (hAb : A ∈ b)
    {γ γ' : Pl} (ha : LiesInPlane (Point := P) a γ) (hb : LiesInPlane (Point := P) b γ)
    (ha' : LiesInPlane (Point := P) a γ') (hb' : LiesInPlane (Point := P) b γ') : γ = γ' :=
  (theorem2_two_lines hab hAa hAb).unique ⟨ha, hb⟩ ⟨ha', hb'⟩

end Incidence

section Parallel

variable [hS : SpaceParallels P L Pl]
include hS

omit hS in
/-- **Parallel lines of space**: equal, or lying in one plane without a common point. -/
def Par (a b : L) : Prop :=
  a = b ∨ ((∃ γ : Pl, LiesInPlane (Point := P) a γ ∧ LiesInPlane (Point := P) b γ) ∧
    ¬Meets (Point := P) a b)

omit hS in
theorem par_refl (a : L) : Par (P := P) (Pl := Pl) a a := Or.inl rfl

omit hS in
theorem par_symm {a b : L} (h : Par (P := P) (Pl := Pl) a b) : Par (P := P) (Pl := Pl) b a := by
  rcases h with h | ⟨⟨γ, ha, hb⟩, hm⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨⟨γ, hb, ha⟩, fun ⟨Z, h1, h2⟩ => hm ⟨Z, h2, h1⟩⟩

omit hS in
theorem par_eq_of_meets {a b : L} (h : Par (P := P) (Pl := Pl) a b) {X : P} (hXa : X ∈ a)
    (hXb : X ∈ b) : a = b := by
  rcases h with h | ⟨-, hm⟩
  · exact h
  · exact absurd ⟨X, hXa, hXb⟩ hm

omit hS in
theorem par_not_meets {a b : L} (h : Par (P := P) (Pl := Pl) a b) (hab : a ≠ b) :
    ¬Meets (Point := P) a b := by
  rcases h with h | ⟨-, hm⟩
  · exact absurd h hab
  · exact hm

/-- A parallel to a line of a plane through a point of the plane lies in the plane. -/
theorem par_in_plane {a b : L} (h : Par (P := P) (Pl := Pl) a b) {γ : Pl}
    (ha : LiesInPlane (Point := P) a γ) {Y : P} (hY : Y ∈ b) (hYγ : Y ∈ γ) :
    LiesInPlane (Point := P) b γ := by
  rcases h with rfl | ⟨⟨γ', ha', hb'⟩, hm⟩
  · exact ha
  · have hYa : Y ∉ a := fun h => hm ⟨Y, h, hY⟩
    have : γ' = γ := plane_eq_of_line_point hYa ha' (hb' Y hY) ha hYγ
    subst this
    exact hb'

/-- Through every point there is a parallel to a given line. -/
theorem exists_par (a : L) (X : P) : ∃ b : L, Par (P := P) (Pl := Pl) a b ∧ X ∈ b := by
  by_cases hX : X ∈ a
  · exact ⟨a, Or.inl rfl, hX⟩
  · obtain ⟨γ, ha, hXγ⟩ := exists_plane_line_point (Pl := Pl) hX
    obtain ⟨m, hm, hXm, hmn⟩ := exists_parallel ha hXγ hX
    exact ⟨m, Or.inr ⟨⟨γ, ha, hm⟩, fun ⟨Z, h1, h2⟩ => hmn ⟨Z, h2, h1⟩⟩, hXm⟩

/-- The parallel to a line through a point is unique. -/
theorem par_unique {a b b' : L} (h : Par (P := P) (Pl := Pl) a b)
    (h' : Par (P := P) (Pl := Pl) a b') {X : P} (hX : X ∈ b) (hX' : X ∈ b') : b = b' := by
  by_cases hXa : X ∈ a
  · exact (par_eq_of_meets h hXa hX).symm.trans (par_eq_of_meets h' hXa hX')
  · obtain ⟨γ, ha, hXγ⟩ := exists_plane_line_point (Pl := Pl) hXa
    have hb := par_in_plane h ha hX hXγ
    have hb' := par_in_plane h' ha hX' hXγ
    have hab : a ≠ b := fun e => hXa (e ▸ hX)
    have hab' : a ≠ b' := fun e => hXa (e ▸ hX')
    have m1 : ¬Meets (Point := P) b a := fun ⟨Z, h1, h2⟩ => par_not_meets h hab ⟨Z, h2, h1⟩
    have m2 : ¬Meets (Point := P) b' a := fun ⟨Z, h1, h2⟩ => par_not_meets h' hab' ⟨Z, h2, h1⟩
    exact parallel_unique ha hXγ hXa hb hX m1 hb' hX' m2

/-- **Parallelism of lines of space is transitive.** -/
theorem par_trans {a b c : L} (hab : Par (P := P) (Pl := Pl) a b)
    (hbc : Par (P := P) (Pl := Pl) b c) : Par (P := P) (Pl := Pl) a c := by
  by_cases h1 : a = b
  · subst h1; exact hbc
  by_cases h2 : b = c
  · subst h2; exact hab
  by_cases h3 : a = c
  · exact Or.inl h3
  obtain ⟨⟨γ₁, ha1, hb1⟩, hmab⟩ := hab.resolve_left h1
  obtain ⟨⟨γ₂, hb2, hc2⟩, hmbc⟩ := hbc.resolve_left h2
  have hmac : ¬Meets (Point := P) a c := fun ⟨X, hXa, hXc⟩ =>
    h3 (par_unique (par_symm hab) hbc hXa hXc)
  refine Or.inr ⟨?_, hmac⟩
  by_cases hγ : γ₁ = γ₂
  · subst hγ; exact ⟨γ₁, ha1, hc2⟩
  obtain ⟨C, C', -, hC, -⟩ := exists_two_points (Point := P) c
  have hCa : C ∉ a := fun h => hmac ⟨C, h, hC⟩
  obtain ⟨δ, haδ, hCδ⟩ := exists_plane_line_point (Pl := Pl) hCa
  obtain ⟨B1, B2, hB, hB1, hB2⟩ := exists_two_points (Point := P) b
  have hcommon : ∀ Z : P, Z ∈ γ₁ → Z ∈ γ₂ → Z ∈ b := fun Z h1 h2 =>
    mem_of_planes hγ hB hB1 hB2 (hb1 _ hB1) (hb1 _ hB2) (hb2 _ hB1) (hb2 _ hB2) h1 h2
  have hCγ₁ : C ∉ γ₁ := fun h => hmbc ⟨C, hcommon C h (hc2 C hC), hC⟩
  obtain ⟨A, A', hAA', hA, hA'⟩ := exists_two_points (Point := P) a
  have hδγ₂ : δ ≠ γ₂ := by
    rintro rfl
    exact hmab ⟨A, hA, hcommon A (ha1 A hA) (haδ A hA)⟩
  have hδγ₁ : δ ≠ γ₁ := by
    rintro rfl
    exact hCγ₁ hCδ
  obtain ⟨c', hc'⟩ := planes_meet_in_line (L := L) hδγ₂ hCδ (hc2 C hC)
  have hc'γ₂ : LiesInPlane (Point := P) c' γ₂ := fun X hX => ((hc' X).1 hX).2
  have hc'b : ¬Meets (Point := P) c' b := by
    rintro ⟨Y, hY, hYb⟩
    exact hmab ⟨Y, mem_of_planes hδγ₁ hAA' hA hA' (haδ _ hA) (haδ _ hA') (ha1 _ hA) (ha1 _ hA')
      ((hc' Y).1 hY).1 (hb1 Y hYb), hYb⟩
  have hCb : C ∉ b := fun h => hmbc ⟨C, h, hC⟩
  have hcb : ¬Meets (Point := P) c b := fun ⟨Z, h1, h2⟩ => hmbc ⟨Z, h2, h1⟩
  have : c' = c := parallel_unique hb2 (hc2 C hC) hCb hc'γ₂ ((hc' C).2 ⟨hCδ, hc2 C hC⟩) hc'b
    hc2 hC hcb
  subst this
  exact ⟨δ, haδ, fun X hX => ((hc' X).1 hX).1⟩

omit hS in
/-- The line `d` **cuts** the plane `α`: it has a point in `α` and does not lie in `α`. -/
def Cuts (d : L) (α : Pl) : Prop :=
  ¬LiesInPlane (Point := P) d α ∧ ∃ O : P, O ∈ d ∧ O ∈ α

/-- A parallel to a line cutting `α` cuts `α`. -/
theorem cuts_of_par {d b : L} {α : Pl} (hd : Cuts (P := P) d α)
    (h : Par (P := P) (Pl := Pl) d b) : Cuts (P := P) b α := by
  rcases h with rfl | ⟨⟨γ, hdγ, hbγ⟩, hm⟩
  · exact hd
  obtain ⟨hdα, O, hOd, hOα⟩ := hd
  have hγα : γ ≠ α := by rintro rfl; exact hdα hdγ
  obtain ⟨m, hm'⟩ := planes_meet_in_line (L := L) hγα (hdγ O hOd) hOα
  have hmγ : LiesInPlane (Point := P) m γ := fun X hX => ((hm' X).1 hX).1
  have hmd : m ≠ d := by
    rintro rfl
    exact hdα fun X hX => ((hm' X).1 hX).2
  have hbd : ¬Meets (Point := P) b d := fun ⟨Z, h1, h2⟩ => hm ⟨Z, h2, h1⟩
  obtain ⟨Z, hZm, hZb⟩ := meets_of_parallel hmγ hdγ hbγ ((hm' O).2 ⟨hdγ O hOd, hOα⟩) hOd hmd hbd
  refine ⟨fun hbα => ?_, Z, hZb, ((hm' Z).1 hZm).2⟩
  have : b = m := line_eq_of_subset fun X hX => (hm' X).2 ⟨hbγ X hX, hbα X hX⟩
  subst this
  exact hm ⟨O, hOd, (hm' O).2 ⟨hdγ O hOd, hOα⟩⟩

/-- The parallel to `d` through `X` meets `α` in exactly one point. -/
theorem exists_unique_proj {d : L} {α : Pl} (hd : Cuts (P := P) d α) (X : P) :
    ∃! Z : P, Z ∈ α ∧ ∃ b : L, Par (P := P) (Pl := Pl) d b ∧ X ∈ b ∧ Z ∈ b := by
  obtain ⟨b, hb, hXb⟩ := exists_par (Pl := Pl) d X
  obtain ⟨hbα, Z, hZb, hZα⟩ := cuts_of_par hd hb
  refine ⟨Z, ⟨hZα, b, hb, hXb, hZb⟩, ?_⟩
  rintro Z' ⟨hZ'α, b', hb', hXb', hZ'b'⟩
  have : b' = b := par_unique hb' hb hXb' hXb
  subst this
  exact theorem1_line_plane hbα hZ'b' hZ'α hZb hZα

/-- **The parallel projection** of space onto the plane `α` along the line `d`. -/
noncomputable def proj {d : L} {α : Pl} (hd : Cuts (P := P) d α) (X : P) : P :=
  (exists_unique_proj hd X).exists.choose

theorem proj_mem {d : L} {α : Pl} (hd : Cuts (P := P) d α) (X : P) : proj hd X ∈ α :=
  (exists_unique_proj hd X).exists.choose_spec.1

theorem proj_spec {d : L} {α : Pl} (hd : Cuts (P := P) d α) (X : P) :
    ∃ b : L, Par (P := P) (Pl := Pl) d b ∧ X ∈ b ∧ proj hd X ∈ b :=
  (exists_unique_proj hd X).exists.choose_spec.2

theorem proj_eq {d : L} {α : Pl} (hd : Cuts (P := P) d α) {X Z : P} {b : L} (hZα : Z ∈ α)
    (hb : Par (P := P) (Pl := Pl) d b) (hXb : X ∈ b) (hZb : Z ∈ b) : proj hd X = Z :=
  (exists_unique_proj hd X).unique ⟨proj_mem hd X, proj_spec hd X⟩ ⟨hZα, b, hb, hXb, hZb⟩

theorem proj_of_mem {d : L} {α : Pl} (hd : Cuts (P := P) d α) {X : P} (hX : X ∈ α) :
    proj hd X = X := by
  obtain ⟨b, hb, hXb⟩ := exists_par (Pl := Pl) d X
  exact proj_eq hd hX hb hXb hXb

/-- The plane through a line `ℓ` not parallel to `d` that contains the parallels to `d` through
its points, and its trace `m` in `α`. -/
theorem proj_plane {d : L} {α : Pl} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : ¬Par (P := P) (Pl := Pl) d ℓ) :
    ∃ (γ : Pl) (m : L), LiesInPlane (Point := P) ℓ γ ∧
      (∀ (Y : P) (b : L), Y ∈ γ → Par (P := P) (Pl := Pl) d b → Y ∈ b →
        LiesInPlane (Point := P) b γ) ∧ ∀ X : P, X ∈ m ↔ X ∈ γ ∧ X ∈ α := by
  obtain ⟨X₀, -, -, hX₀, -⟩ := exists_two_points (Point := P) ℓ
  obtain ⟨b₀, hb₀, hX₀b⟩ := exists_par (Pl := Pl) d X₀
  have hne : b₀ ≠ ℓ := by rintro rfl; exact hℓ hb₀
  obtain ⟨γ, ⟨hb₀γ, hℓγ⟩, -⟩ := theorem2_two_lines (Pl := Pl) hne hX₀b hX₀
  obtain ⟨hb₀α, Z₀, hZ₀b, hZ₀α⟩ := cuts_of_par hd hb₀
  have hγα : γ ≠ α := by rintro rfl; exact hb₀α hb₀γ
  obtain ⟨m, hm⟩ := planes_meet_in_line (L := L) hγα (hb₀γ Z₀ hZ₀b) hZ₀α
  exact ⟨γ, m, hℓγ, fun Y b hY hb hYb => par_in_plane (par_trans (par_symm hb₀) hb) hb₀γ hYb hY,
    hm⟩

/-- **A line not parallel to `d` is projected one-to-one onto a line of `α`.** -/
theorem proj_line {d : L} {α : Pl} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : ¬Par (P := P) (Pl := Pl) d ℓ) :
    ∃ m : L, LiesInPlane (Point := P) m α ∧ (∀ X : P, X ∈ ℓ → proj hd X ∈ m) ∧
      (∀ Z : P, Z ∈ m → ∃ X : P, X ∈ ℓ ∧ proj hd X = Z) ∧
      ∀ X X' : P, X ∈ ℓ → X' ∈ ℓ → proj hd X = proj hd X' → X = X' := by
  obtain ⟨γ, m, hℓγ, hγ, hm⟩ := proj_plane hd hℓ
  refine ⟨m, fun X hX => ((hm X).1 hX).2, fun X hX => ?_, fun Z hZ => ?_, fun X X' hX hX' e => ?_⟩
  · obtain ⟨b, hb, hXb, hZb⟩ := proj_spec hd X
    exact (hm _).2 ⟨hγ X b (hℓγ X hX) hb hXb _ hZb, proj_mem hd X⟩
  · obtain ⟨hZγ, hZα⟩ := (hm Z).1 hZ
    obtain ⟨b, hb, hZb⟩ := exists_par (Pl := Pl) d Z
    have hbγ := hγ Z b hZγ hb hZb
    by_cases hmeet : Meets (Point := P) ℓ b
    · obtain ⟨X, hXℓ, hXb⟩ := hmeet
      exact ⟨X, hXℓ, proj_eq hd hZα hb hXb hZb⟩
    · exact absurd (par_trans hb (par_symm (Or.inr ⟨⟨γ, hℓγ, hbγ⟩, hmeet⟩))) hℓ
  · by_contra hne
    obtain ⟨b, hb, hXb, hZb⟩ := proj_spec hd X
    obtain ⟨b', hb', hXb', hZb'⟩ := proj_spec hd X'
    rw [← e] at hZb'
    have : b' = b := par_unique hb' hb hZb' hZb
    subst this
    have : b' = ℓ := line_unique hne hXb hXb' hX hX'
    subst this
    exact hℓ hb

/-- A line parallel to `d` is projected to a point. -/
theorem proj_const {d : L} {α : Pl} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : Par (P := P) (Pl := Pl) d ℓ) {X X' : P} (hX : X ∈ ℓ) (hX' : X' ∈ ℓ) :
    proj hd X = proj hd X' := by
  obtain ⟨b', hb', hXb', hZb'⟩ := proj_spec hd X'
  have : b' = ℓ := par_unique hb' hℓ hXb' hX'
  subst this
  exact proj_eq hd (proj_mem hd X') hℓ hX hZb'

/-- **Two projections.** For two distinct lines `d₁`, `d₂` through a point and cutting `α`, with
`m₀` the trace in `α` of their plane `γ₀`: the two projections of a point coincide or lie on a line
of `α` which is `m₀` or does not meet `m₀`. -/
theorem proj_pair {d₁ d₂ : L} {α : Pl} (hd₁ : Cuts (P := P) d₁ α) (hd₂ : Cuts (P := P) d₂ α)
    {O : P} (hO₁ : O ∈ d₁) (hO₂ : O ∈ d₂) (h12 : d₁ ≠ d₂) {γ₀ : Pl}
    (h1γ : LiesInPlane (Point := P) d₁ γ₀) (h2γ : LiesInPlane (Point := P) d₂ γ₀) {m₀ : L}
    (hm₀ : ∀ X : P, X ∈ m₀ ↔ X ∈ γ₀ ∧ X ∈ α) (X : P) :
    proj hd₁ X = proj hd₂ X ∨ ∃ m : L, LiesInPlane (Point := P) m α ∧ proj hd₁ X ∈ m ∧
      proj hd₂ X ∈ m ∧ (m = m₀ ∨ ¬Meets (Point := P) m m₀) := by
  by_cases hX : X ∈ α
  · exact Or.inl ((proj_of_mem hd₁ hX).trans (proj_of_mem hd₂ hX).symm)
  have hnp : ¬Par (P := P) (Pl := Pl) d₁ d₂ := fun h => h12 (par_eq_of_meets h hO₁ hO₂)
  obtain ⟨b₁, hb₁, hXb₁, hZb₁⟩ := proj_spec hd₁ X
  obtain ⟨b₂, hb₂, hXb₂, hZb₂⟩ := proj_spec hd₂ X
  have hb12 : b₁ ≠ b₂ := by
    rintro rfl
    exact hnp (par_trans hb₁ (par_symm hb₂))
  obtain ⟨γ, ⟨hb₁γ, hb₂γ⟩, -⟩ := theorem2_two_lines (Pl := Pl) hb12 hXb₁ hXb₂
  have hγα : γ ≠ α := by rintro rfl; exact hX (hb₁γ X hXb₁)
  obtain ⟨m, hm⟩ := planes_meet_in_line (L := L) hγα (hb₁γ _ hZb₁) (proj_mem hd₁ X)
  refine Or.inr ⟨m, fun Y hY => ((hm Y).1 hY).2, (hm _).2 ⟨hb₁γ _ hZb₁, proj_mem hd₁ X⟩,
    (hm _).2 ⟨hb₂γ _ hZb₂, proj_mem hd₂ X⟩, ?_⟩
  by_cases hmeet : Meets (Point := P) m m₀
  · left
    obtain ⟨Z, hZm, hZm₀⟩ := hmeet
    obtain ⟨hZγ, -⟩ := (hm Z).1 hZm
    obtain ⟨hZγ₀, -⟩ := (hm₀ Z).1 hZm₀
    obtain ⟨c₁, hc₁, hZc₁⟩ := exists_par (Pl := Pl) d₁ Z
    obtain ⟨c₂, hc₂, hZc₂⟩ := exists_par (Pl := Pl) d₂ Z
    have hc12 : c₁ ≠ c₂ := by
      rintro rfl
      exact hnp (par_trans hc₁ (par_symm hc₂))
    have e : γ = γ₀ := plane_eq_of_two_lines hc12 hZc₁ hZc₂
      (par_in_plane (par_trans (par_symm hb₁) hc₁) hb₁γ hZc₁ hZγ)
      (par_in_plane (par_trans (par_symm hb₂) hc₂) hb₂γ hZc₂ hZγ)
      (par_in_plane hc₁ h1γ hZc₁ hZγ₀) (par_in_plane hc₂ h2γ hZc₂ hZγ₀)
    subst e
    exact line_eq_of_subset fun Y hY => (hm₀ Y).2 ((hm Y).1 hY)
  · exact Or.inr hmeet

/-- Two projections along distinct directions through a point determine the point. -/
theorem proj_inj_pair {d₁ d₂ : L} {α : Pl} (hd₁ : Cuts (P := P) d₁ α) (hd₂ : Cuts (P := P) d₂ α)
    {O : P} (hO₁ : O ∈ d₁) (hO₂ : O ∈ d₂) (h12 : d₁ ≠ d₂) {X Y : P}
    (h1 : proj hd₁ X = proj hd₁ Y) (h2 : proj hd₂ X = proj hd₂ Y) : X = Y := by
  have hnp : ¬Par (P := P) (Pl := Pl) d₁ d₂ := fun h => h12 (par_eq_of_meets h hO₁ hO₂)
  obtain ⟨b₁, hb₁, hXb₁, hZb₁⟩ := proj_spec hd₁ X
  obtain ⟨b₁', hb₁', hYb₁, hZb₁'⟩ := proj_spec hd₁ Y
  obtain ⟨b₂, hb₂, hXb₂, hZb₂⟩ := proj_spec hd₂ X
  obtain ⟨b₂', hb₂', hYb₂, hZb₂'⟩ := proj_spec hd₂ Y
  rw [← h1] at hZb₁'
  rw [← h2] at hZb₂'
  have e1 : b₁' = b₁ := par_unique hb₁' hb₁ hZb₁' hZb₁
  have e2 : b₂' = b₂ := par_unique hb₂' hb₂ hZb₂' hZb₂
  subst e1 e2
  have hb12 : b₁' ≠ b₂' := by
    rintro rfl
    exact hnp (par_trans hb₁ (par_symm hb₂))
  exact eq_of_mem_of_mem hb12 hXb₁ hXb₂ hYb₁ hYb₂

/-- In every plane there are two distinct points and a third point off their line. -/
theorem exists_triangle_in_plane (α : Pl) :
    ∃ (A B C : P) (a : L), A ∈ α ∧ B ∈ α ∧ C ∈ α ∧ A ≠ B ∧ A ∈ a ∧ B ∈ a ∧ C ∉ a := by
  obtain ⟨W, hW⟩ := SpaceDesargues.exists_not_mem (P := P) L α
  obtain ⟨X, Y, Z, hX, hY, hZ, hn⟩ := SpaceConnection.ax_I7_plane (Point := P) (Line := L) α
  have hXW : X ≠ W := fun e => hW (e ▸ hX)
  obtain ⟨g, hXg, -⟩ := exists_line (Line := L) hXW
  have hA : ∃ A : P, A ∈ α ∧ X ≠ A := by
    by_cases hYX : X = Y
    · by_cases hZX : X = Z
      · exact absurd ⟨g, hXg, hYX ▸ hXg, hZX ▸ hXg⟩ hn
      · exact ⟨Z, hZ, hZX⟩
    · exact ⟨Y, hY, hYX⟩
  obtain ⟨A, hAα, hXA⟩ := hA
  obtain ⟨a, hXa, hAa⟩ := exists_line (Line := L) hXA
  obtain ⟨B, hBα, hBa⟩ := exists_mem_plane_not_mem (P := P) α a
  exact ⟨X, A, B, a, hX, hAα, hBα, hXA, hXa, hAa, hBa⟩

end Parallel

section Order

variable [HasBetween P] [hO : SpaceOrder P L Pl] [hS : SpaceParallels P L Pl]
include hO hS

/-- **Three directions**: a point `O` of `α` and three lines through it that do not lie in `α`
and do not lie in one plane. -/
theorem exists_three_directions (α : Pl) :
    ∃ (O : P) (d₁ d₂ d₃ : L), O ∈ α ∧ O ∈ d₁ ∧ O ∈ d₂ ∧ O ∈ d₃ ∧
      ¬LiesInPlane (Point := P) d₁ α ∧ ¬LiesInPlane (Point := P) d₂ α ∧
      ¬LiesInPlane (Point := P) d₃ α ∧
      ¬∃ γ : Pl, LiesInPlane (Point := P) d₁ γ ∧ LiesInPlane (Point := P) d₂ γ ∧
        LiesInPlane (Point := P) d₃ γ := by
  obtain ⟨O, A, B, a, hO, hA, hB, hOA, hOa, hAa, hBa⟩ := exists_triangle_in_plane (P := P) (L := L) α
  obtain ⟨W, hW⟩ := SpaceDesargues.exists_not_mem (P := P) L α
  have hAW : A ≠ W := fun e => hW (e ▸ hA)
  have hBW : B ≠ W := fun e => hW (e ▸ hB)
  have hOW : O ≠ W := fun e => hW (e ▸ hO)
  obtain ⟨W₂, hW₂⟩ := exists_between (Line := L) hAW
  obtain ⟨W₃, hW₃⟩ := exists_between (Line := L) hBW
  obtain ⟨gA, hAgA, hWgA⟩ := exists_line (Line := L) hAW
  obtain ⟨gB, hBgB, hWgB⟩ := exists_line (Line := L) hBW
  have hW₂g : W₂ ∈ gA := mem_of_collinear (collinear_of_between hW₂).swap23 hAW hAgA hWgA
  have hW₃g : W₃ ∈ gB := mem_of_collinear (collinear_of_between hW₃).swap23 hBW hBgB hWgB
  have hW₂α : W₂ ∉ α := fun h =>
    hW (liesInPlane_of_mem (ne12_of_between (Line := L) hW₂) hAgA hW₂g hA h W hWgA)
  have hW₃α : W₃ ∉ α := fun h =>
    hW (liesInPlane_of_mem (ne12_of_between (Line := L) hW₃) hBgB hW₃g hB h W hWgB)
  have hOW₂ : O ≠ W₂ := fun e => hW₂α (e ▸ hO)
  have hOW₃ : O ≠ W₃ := fun e => hW₃α (e ▸ hO)
  obtain ⟨d₁, hOd₁, hWd₁⟩ := exists_line (Line := L) hOW
  obtain ⟨d₂, hOd₂, hWd₂⟩ := exists_line (Line := L) hOW₂
  obtain ⟨d₃, hOd₃, hWd₃⟩ := exists_line (Line := L) hOW₃
  refine ⟨O, d₁, d₂, d₃, hO, hOd₁, hOd₂, hOd₃, fun h => hW (h W hWd₁), fun h => hW₂α (h W₂ hWd₂),
    fun h => hW₃α (h W₃ hWd₃), ?_⟩
  rintro ⟨γ, h1, h2, h3⟩
  have hAγ : A ∈ γ := liesInPlane_of_mem (ne23_of_between (Line := L) hW₂) hW₂g hWgA
    (h2 W₂ hWd₂) (h1 W hWd₁) A hAgA
  have hBγ : B ∈ γ := liesInPlane_of_mem (ne23_of_between (Line := L) hW₃) hW₃g hWgB
    (h3 W₃ hWd₃) (h1 W hWd₁) B hBgB
  have hn : ¬Collinear O A B := not_collinear_of_not_mem hOa hAa hOA hBa
  have : γ = α := plane_unique hn (h1 O hOd₁) hAγ hBγ hO hA hB
  exact hW (this ▸ h1 W hWd₁)

omit hS in
/-- Three lines `b_X`, `b_Y`, `b_Z` of a plane, the outer ones not meeting the middle one: if
`Y` lies between `X` and `Z` (points of the three lines), the same holds for any three collinear
points of the three lines. -/
theorem between_parallels {γ : Pl} {bX bY bZ m : L} (hbX : LiesInPlane (Point := P) bX γ)
    (hbY : LiesInPlane (Point := P) bY γ) (hbZ : LiesInPlane (Point := P) bZ γ)
    (hXY : ¬Meets (Point := P) bX bY) (hZY : ¬Meets (Point := P) bZ bY) {X Y Z X' Y' Z' : P}
    (hX : X ∈ bX) (hX' : X' ∈ bX) (hY : Y ∈ bY) (hY' : Y' ∈ bY) (hZ : Z ∈ bZ) (hZ' : Z' ∈ bZ)
    (hXm : X' ∈ m) (hYm : Y' ∈ m) (hZm : Z' ∈ m) (h : Between X Y Z) : Between X' Y' Z' := by
  have hXn : X ∉ bY := fun h => hXY ⟨X, hX, h⟩
  have hX'n : X' ∉ bY := fun h => hXY ⟨X', hX', h⟩
  have hZn : Z ∉ bY := fun h => hZY ⟨Z, hZ, h⟩
  have hZ'n : Z' ∉ bY := fun h => hZY ⟨Z', hZ', h⟩
  have opp : OppositeSides bY X Z := ⟨hXn, hZn, Y, hY, h⟩
  have sX : SameSide bY X' X := ⟨hX'n, hXn, fun ⟨T, hT, hb⟩ => hXY ⟨T,
    mem_of_collinear (collinear_of_between hb).swap23 (ne13_of_between (Line := L) hb) hX' hX,
    hT⟩⟩
  have sZ : SameSide bY Z' Z := ⟨hZ'n, hZn, fun ⟨T, hT, hb⟩ => hZY ⟨T,
    mem_of_collinear (collinear_of_between hb).swap23 (ne13_of_between (Line := L) hb) hZ' hZ,
    hT⟩⟩
  have opp1 : OppositeSides bY X' Z :=
    OrderSpace.opp_of_sameSide_opp hbY (hbX X' hX') (hbX X hX) (hbZ Z hZ) sX opp
  have opp1' : OppositeSides bY Z X' := by
    obtain ⟨h1, h2, T, hT, hb⟩ := opp1
    exact ⟨h2, h1, T, hT, between_symm (Line := L) hb⟩
  obtain ⟨-, -, T, hT, hb⟩ :=
    OrderSpace.opp_of_sameSide_opp hbY (hbZ Z' hZ') (hbZ Z hZ) (hbX X' hX') sZ opp1'
  have hTm : T ∈ m :=
    mem_of_collinear (collinear_of_between hb).swap23 (ne13_of_between (Line := L) hb) hZm hXm
  have hmb : m ≠ bY := by rintro rfl; exact hX'n hXm
  have : T = Y' := eq_of_mem_of_mem hmb hTm hT hYm hY'
  subst this
  exact between_symm (Line := L) hb

/-- **Parallel projection preserves and reflects betweenness** on a line not parallel to the
direction of projection. -/
theorem proj_between {d : L} {α : Pl} (hd : Cuts (P := P) d α) {ℓ : L}
    (hℓ : ¬Par (P := P) (Pl := Pl) d ℓ) {X Y Z : P} (hX : X ∈ ℓ) (hY : Y ∈ ℓ) (hZ : Z ∈ ℓ) :
    Between (proj hd X) (proj hd Y) (proj hd Z) ↔ Between X Y Z := by
  obtain ⟨γ, m, hℓγ, hγ, hm⟩ := proj_plane hd hℓ
  obtain ⟨bX, hbX, hXb, hX'b⟩ := proj_spec hd X
  obtain ⟨bY, hbY, hYb, hY'b⟩ := proj_spec hd Y
  obtain ⟨bZ, hbZ, hZb, hZ'b⟩ := proj_spec hd Z
  have hbXγ := hγ X bX (hℓγ X hX) hbX hXb
  have hbYγ := hγ Y bY (hℓγ Y hY) hbY hYb
  have hbZγ := hγ Z bZ (hℓγ Z hZ) hbZ hZb
  have key : ∀ {U V : P} {bU bV : L}, Par (P := P) (Pl := Pl) d bU →
      Par (P := P) (Pl := Pl) d bV → U ∈ ℓ → V ∈ ℓ → U ∈ bU → V ∈ bV → U ≠ V →
      ¬Meets (Point := P) bU bV := by
    intro U V bU bV hbU hbV hU hV hUb hVb hUV
    refine par_not_meets (par_trans (par_symm hbU) hbV) ?_
    rintro rfl
    exact hℓ ((line_unique hUV hUb hVb hU hV) ▸ hbU)
  have hXm : proj hd X ∈ m := (hm _).2 ⟨hbXγ _ hX'b, proj_mem hd X⟩
  have hYm : proj hd Y ∈ m := (hm _).2 ⟨hbYγ _ hY'b, proj_mem hd Y⟩
  have hZm : proj hd Z ∈ m := (hm _).2 ⟨hbZγ _ hZ'b, proj_mem hd Z⟩
  constructor
  · intro h
    have hXY : X ≠ Y := fun e => ne12_of_between (Line := L) h (by rw [e])
    have hZY : Z ≠ Y := fun e => ne23_of_between (Line := L) h (by rw [e])
    exact between_parallels hbXγ hbYγ hbZγ (key hbX hbY hX hY hXb hYb hXY)
      (key hbZ hbY hZ hY hZb hYb hZY) hX'b hXb hY'b hYb hZ'b hZb hX hY hZ h
  · intro h
    exact between_parallels hbXγ hbYγ hbZγ
      (key hbX hbY hX hY hXb hYb (ne12_of_between (Line := L) h))
      (key hbZ hbY hZ hY hZb hYb (ne23_of_between (Line := L) h).symm) hXb hX'b hYb hY'b hZb hZ'b
      hXm hYm hZm h

end Order

section Transfer

variable {P' : Type*} {L' : Type*} {Pl' : Type*} [HasLines P' L'] [HasPlanes P' Pl']

/-- **Planes go to planes.** An injective map between geometries of space that maps collinear
points to collinear points maps a plane `π` into any plane `S` containing the images of two points
of `π` and of a third point of `π` off their line. -/
theorem plane_transfer [HasBetween P] [SpaceOrder P L Pl] [SpaceParallels P L Pl]
    [SpaceConnection P' L' Pl'] (f : P → P') (hinj : Function.Injective f)
    (hcol : ∀ ℓ : L, ∃ ℓ' : L', ∀ X : P, X ∈ ℓ → f X ∈ ℓ') {π : Pl} {S : Pl'} {A B C : P} {a : L}
    (hA : A ∈ π) (hB : B ∈ π) (hC : C ∈ π) (hAB : A ≠ B) (hAa : A ∈ a) (hBa : B ∈ a)
    (hCa : C ∉ a) (hfA : f A ∈ S) (hfB : f B ∈ S) (hfC : f C ∈ S) :
    ∀ X : P, X ∈ π → f X ∈ S := by
  have hfline : ∀ {U V W : P} {ℓ : L}, U ≠ V → U ∈ ℓ → V ∈ ℓ → W ∈ ℓ → f U ∈ S → f V ∈ S →
      f W ∈ S := by
    intro U V W ℓ hUV hU hV hW hfU hfV
    obtain ⟨ℓ', h⟩ := hcol ℓ
    exact liesInPlane_of_mem (hinj.ne hUV) (h U hU) (h V hV) hfU hfV _ (h W hW)
  obtain ⟨A', hA'⟩ := exists_between (Line := L) hAB
  have hA'a : A' ∈ a := mem_of_collinear (collinear_of_between hA').swap23 hAB hAa hBa
  have hAA' : A ≠ A' := ne12_of_between (Line := L) hA'
  have hA'B : A' ≠ B := ne23_of_between (Line := L) hA'
  have hfA' : f A' ∈ S := hfline hAB hAa hBa hA'a hfA hfB
  have hBC : B ≠ C := fun e => hCa (e ▸ hBa)
  obtain ⟨c, hBc, hCc⟩ := exists_line (Line := L) hBC
  have hcπ : LiesInPlane (Point := P) c π := liesInPlane_of_mem hBC hBc hCc hB hC
  have haπ : LiesInPlane (Point := P) a π := liesInPlane_of_mem hAB hAa hBa hA hB
  have hac : a ≠ c := by rintro rfl; exact hCa hCc
  have hAc : A ∉ c := fun h => hac (line_unique hAB hAa hBa h hBc)
  have hA'c : A' ∉ c := fun h => hac (line_unique hA'B hA'a hBa h hBc)
  intro X hX
  by_cases hXa : X ∈ a
  · exact hfline hAB hAa hBa hXa hfA hfB
  by_cases hXc : X ∈ c
  · exact hfline hBC hBc hCc hXc hfB hfC
  have hXA : X ≠ A := fun e => hXa (e ▸ hAa)
  have hXA' : X ≠ A' := fun e => hXa (e ▸ hA'a)
  obtain ⟨g, hXg, hAg⟩ := exists_line (Line := L) hXA
  obtain ⟨g', hXg', hA'g'⟩ := exists_line (Line := L) hXA'
  have hgπ : LiesInPlane (Point := P) g π := liesInPlane_of_mem hXA hXg hAg hX hA
  have hg'π : LiesInPlane (Point := P) g' π :=
    liesInPlane_of_mem hXA' hXg' hA'g' hX (haπ A' hA'a)
  by_cases hm : Meets (Point := P) g c
  · obtain ⟨D, hDg, hDc⟩ := hm
    have hAD : A ≠ D := fun e => hAc (e ▸ hDc)
    exact hfline hAD hAg hDg hXg hfA (hfline hBC hBc hCc hDc hfB hfC)
  by_cases hm' : Meets (Point := P) g' c
  · obtain ⟨D, hDg, hDc⟩ := hm'
    have hAD : A' ≠ D := fun e => hA'c (e ▸ hDc)
    exact hfline hAD hA'g' hDg hXg' hfA' (hfline hBC hBc hCc hDc hfB hfC)
  have : g = g' := parallel_unique hcπ hX hXc hgπ hXg hm hg'π hXg' hm'
  subst this
  exact absurd ((line_unique hAA' hAg hA'g' hAa hA'a) ▸ hXg) hXa

end Transfer

end SpaceCoord

end HilbertFoundations
