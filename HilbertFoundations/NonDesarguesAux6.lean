import HilbertFoundations.Analytic

/-!
# Desargues's theorem in space from the axioms I and III (helper for `NonDesargues.lean`)

§ 22: "Upon the basis of the axioms of groups I–III, it is well known that the so-called theorem of
Desargues may be easily demonstrated", and § 23 concludes from this that the plane geometry built
there "cannot be considered as a part of a geometry of space". This module proves the case of
Theorem 32 needed for that conclusion, in any space geometry satisfying the axioms of
connection I 1–7 and Euclid's axiom III in each plane (`SpaceParallels`; no order, no congruence):

*if two triangles `ABC`, `A'B'C'` of a plane `α` have their homologous sides on lines without
common point, and the lines `BB'` and `CC'` meet in a point `O` (distinct from the vertices `A`,
`B`, `C`, `B'`, `C'`), then `O` lies on `AA'`* (`SpaceDesargues.concurrent`; the
non-degeneracy conditions follow from the hypotheses, `concurrent'`). By relabelling the triangles
this gives the whole direct part of Theorem 32 in a plane of such a space
(`SpaceDesargues.direct`: the joining lines are concurrent or pairwise without common point).

The proof is the classical one by leaving the plane: take `S ∉ α` (I 7), on `OS` the point `S'`
with `S'B' ∥ SB` (in the plane `OBS`), on `OA` the point `A''` with `S'A'' ∥ SA` (in the plane
`OAS`); two planes containing two intersecting lines each of which misses the other plane have no
common point (`planes_disjoint`, from I 6 and III), which gives `S'C' ∥ SC`, then `A''B' ∥ AB`
and `A''C' ∥ AC`, so that `A''` lies on the parallels `A'B'` and `A'C'` through `B'` and `C'`,
i.e. `A'' = A'`.
-/

namespace HilbertFoundations

namespace SpaceDesargues

variable {P : Type*} {L : Type*} {Pl : Type*} [HasLines P L] [HasPlanes P Pl]

section Connection

variable [SpaceConnection P L Pl]

/-- A point of a line through two distinct points of `α` lies in `α` (I 5). -/
theorem mem_plane_of {X Y Z : P} {l : L} {α : Pl} (h : X ≠ Y) (hX : X ∈ l) (hY : Y ∈ l)
    (hXα : X ∈ α) (hYα : Y ∈ α) (hZ : Z ∈ l) : Z ∈ α :=
  liesInPlane_of_mem h hX hY hXα hYα Z hZ

/-- Two distinct points of `α` and a point outside `α` are not collinear. -/
theorem not_collinear_of_out {X Y Z : P} {α : Pl} (h : X ≠ Y) (hX : X ∈ α) (hY : Y ∈ α)
    (hZ : Z ∉ α) : ¬Collinear (Line := L) X Y Z := by
  rintro ⟨l, h1, h2, h3⟩
  exact hZ (mem_plane_of h h1 h2 hX hY h3)

/-- Two distinct planes through the distinct points `X`, `Y` of `l` have no common point off `l`
(I 4). -/
theorem mem_of_planes {α β : Pl} {X Y Z : P} {l : L} (hαβ : α ≠ β) (hXY : X ≠ Y) (hX : X ∈ l)
    (hY : Y ∈ l) (hXα : X ∈ α) (hYα : Y ∈ α) (hXβ : X ∈ β) (hYβ : Y ∈ β) (hZα : Z ∈ α)
    (hZβ : Z ∈ β) : Z ∈ l := by
  by_contra hZ
  have hn : ¬Collinear (Line := L) X Y Z := by
    rintro ⟨m, h1, h2, h3⟩
    exact hZ (line_unique hXY h1 h2 hX hY ▸ h3)
  exact hαβ (plane_unique hn hXα hYα hZα hXβ hYβ hZβ)

/-- A line `l` of a plane `ρ` misses a plane `π ≠ ρ` if it misses a line `m` through two distinct
common points of `ρ` and `π`. -/
theorem not_mem_plane_of {ρ π : Pl} {l m : L} {X Y : P} (hρπ : ρ ≠ π)
    (hl : LiesInPlane (Point := P) l ρ) (hXY : X ≠ Y) (hX : X ∈ m) (hY : Y ∈ m) (hXρ : X ∈ ρ)
    (hYρ : Y ∈ ρ) (hXπ : X ∈ π) (hYπ : Y ∈ π) (hlm : ¬Meets (Point := P) l m) :
    ∀ U : P, U ∈ l → U ∉ π := fun U hU hUπ =>
  hlm ⟨U, hU, mem_of_planes hρπ hXY hX hY hXρ hYρ hXπ hYπ (hl U hU) hUπ⟩

omit [SpaceConnection P L Pl] in
/-- There is a point outside any given plane (third clause of I 7). -/
theorem exists_not_mem (L : Type*) [HasLines P L] [SpaceConnection P L Pl] (α : Pl) :
    ∃ S : P, S ∉ α := by
  obtain ⟨W1, W2, W3, W4, h⟩ := SpaceConnection.ax_I7_space (Point := P) (Line := L) (Plane := Pl)
  by_contra hne
  simp only [not_exists, not_not] at hne
  exact h ⟨α, hne W1, hne W2, hne W3, hne W4⟩

end Connection

section Parallels

variable [SpaceParallels P L Pl]

/-- III in the plane `β`: the parallel to `n` through `Y`. -/
theorem exists_parallel {β : Pl} {n : L} {Y : P} (hn : LiesInPlane (Point := P) n β) (hY : Y ∈ β)
    (hYn : Y ∉ n) : ∃ m : L, LiesInPlane (Point := P) m β ∧ Y ∈ m ∧ ¬Meets (Point := P) m n :=
  (SpaceParallels.ax_III (Point := P) (Line := L) (Plane := Pl) β n Y hn hY hYn).exists

/-- III in the plane `β`: two lines of `β` through `X ∉ t` missing `t` coincide. -/
theorem parallel_unique {β : Pl} {t l₁ l₂ : L} {X : P} (ht : LiesInPlane (Point := P) t β)
    (hX : X ∈ β) (hXt : X ∉ t) (h1 : LiesInPlane (Point := P) l₁ β) (hX1 : X ∈ l₁)
    (m1 : ¬Meets (Point := P) l₁ t) (h2 : LiesInPlane (Point := P) l₂ β) (hX2 : X ∈ l₂)
    (m2 : ¬Meets (Point := P) l₂ t) : l₁ = l₂ :=
  (SpaceParallels.ax_III (Point := P) (Line := L) (Plane := Pl) β t X ht hX hXt).unique
    ⟨h1, hX1, m1⟩ ⟨h2, hX2, m2⟩

/-- In a plane, a parallel `m` to a line `n` meets every other line `s` through a point of `n`. -/
theorem meets_of_parallel {β : Pl} {s n m : L} {X : P} (hs : LiesInPlane (Point := P) s β)
    (hn : LiesInPlane (Point := P) n β) (hm : LiesInPlane (Point := P) m β) (hXs : X ∈ s)
    (hXn : X ∈ n) (hsn : s ≠ n) (hmn : ¬Meets (Point := P) m n) : ∃ Z : P, Z ∈ s ∧ Z ∈ m := by
  by_contra hsm
  have hXm : X ∉ m := fun h => hmn ⟨X, h, hXn⟩
  have hnm : ¬Meets (Point := P) n m := fun ⟨Z, h1, h2⟩ => hmn ⟨Z, h2, h1⟩
  exact hsn (parallel_unique hm (hs X hXs) hXm hs hXs hsm hn hXn hnm)

/-- **Parallel planes.** If two distinct lines `l₁`, `l₂` of `π` through a point `X` both miss the
plane `π' ≠ π`, then `π` and `π'` have no common point (I 5, I 6, III). -/
theorem planes_disjoint {π π' : Pl} {l₁ l₂ : L} {X : P} (hππ' : π ≠ π')
    (h1 : LiesInPlane (Point := P) l₁ π) (h2 : LiesInPlane (Point := P) l₂ π) (hX1 : X ∈ l₁)
    (hX2 : X ∈ l₂) (h12 : l₁ ≠ l₂) (n1 : ∀ U : P, U ∈ l₁ → U ∉ π')
    (n2 : ∀ U : P, U ∈ l₂ → U ∉ π') : ∀ U : P, U ∈ π → U ∉ π' := by
  intro U hU hU'
  obtain ⟨V, hVU, hV, hV'⟩ :=
    SpaceConnection.ax_I6 (Point := P) (Line := L) (Plane := Pl) π π' U hππ' hU hU'
  obtain ⟨t, hUt, hVt⟩ := exists_line (Line := L) hVU.symm
  have htπ : LiesInPlane (Point := P) t π := liesInPlane_of_mem hVU.symm hUt hVt hU hV
  have htπ' : LiesInPlane (Point := P) t π' := liesInPlane_of_mem hVU.symm hUt hVt hU' hV'
  have m1 : ¬Meets (Point := P) l₁ t := fun ⟨Z, hZ1, hZt⟩ => n1 Z hZ1 (htπ' Z hZt)
  have m2 : ¬Meets (Point := P) l₂ t := fun ⟨Z, hZ2, hZt⟩ => n2 Z hZ2 (htπ' Z hZt)
  have hXt : X ∉ t := fun h => m1 ⟨X, hX1, h⟩
  exact h12 (parallel_unique htπ (h1 X hX1) hXt h1 hX1 m1 h2 hX2 m2)

/-- **Desargues's theorem (Theorem 32), case of concurrent joining lines, in space from I and III.**
Two triangles `ABC`, `A'B'C'` of a plane `α` with homologous sides on lines without common point
(`a = BC ∥ a' = B'C'`, `b = CA ∥ b'`, `c = AB ∥ c'`); if the lines `q = BB'` and `r = CC'` meet in
a point `O` distinct from `A`, `B`, `C`, `B'`, `C'`, then `O` lies on `p = AA'`. -/
theorem concurrent {α : Pl} {A B C A' B' C' O : P} {a b c a' b' c' p q r : L}
    (hA : A ∈ α) (hB : B ∈ α) (hC : C ∈ α) (hA' : A' ∈ α) (hB' : B' ∈ α) (hC' : C' ∈ α)
    (hO : O ∈ α) (nABC : ¬Collinear A B C) (nABC' : ¬Collinear A' B' C')
    (hBa : B ∈ a) (hCa : C ∈ a) (hCb : C ∈ b) (hAb : A ∈ b) (hAc : A ∈ c) (hBc : B ∈ c)
    (hBa' : B' ∈ a') (hCa' : C' ∈ a') (hCb' : C' ∈ b') (hAb' : A' ∈ b') (hAc' : A' ∈ c')
    (hBc' : B' ∈ c')
    (pa : ¬Meets (Point := P) a a') (pb : ¬Meets (Point := P) b b')
    (pc : ¬Meets (Point := P) c c')
    (hAp : A ∈ p) (hA'p : A' ∈ p) (hBq : B ∈ q) (hB'q : B' ∈ q) (hCr : C ∈ r) (hC'r : C' ∈ r)
    (hOq : O ∈ q) (hOr : O ∈ r)
    (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C) (hOB' : O ≠ B') (hOC' : O ≠ C') : O ∈ p := by
  -- distinctness of the vertices
  have hAB : A ≠ B := fun e => nABC ⟨a, e ▸ hBa, hBa, hCa⟩
  have hBC : B ≠ C := fun e => nABC ⟨c, hAc, hBc, e ▸ hBc⟩
  have hAC : A ≠ C := fun e => nABC ⟨c, hAc, hBc, e ▸ hAc⟩
  have hA'B' : A' ≠ B' := fun e => nABC' ⟨a', e ▸ hBa', hBa', hCa'⟩
  have hB'C' : B' ≠ C' := fun e => nABC' ⟨c', hAc', hBc', e ▸ hBc'⟩
  have hA'C' : A' ≠ C' := fun e => nABC' ⟨c', hAc', hBc', e ▸ hAc'⟩
  have hAA' : A ≠ A' := fun e => pb ⟨A, hAb, e ▸ hAb'⟩
  have hB'c : B' ∉ c := fun h => pc ⟨B', h, hBc'⟩
  have hC'b : C' ∉ b := fun h => pb ⟨C', h, hCb'⟩
  have hB'a : B' ∉ a := fun h => pa ⟨B', h, hBa'⟩
  have hBB' : B ≠ B' := fun e => hB'c (e ▸ hBc)
  -- `B'C'` lies in no line through two points of `ABC`'s plane other than `a'`
  have hC'q : C' ∉ q := by
    intro h
    have hqr : q = r := line_unique hOC' hOq h hOr hC'r
    have : a' = q := line_unique hB'C' hBa' hCa' hB'q h
    exact pa ⟨C, hCa, this ▸ hqr ▸ hCr⟩
  -- `A ∉ q`, `A ∉ r`
  have hAq : A ∉ q := fun h => hB'c (line_unique hAB h hBq hAc hBc ▸ hB'q)
  have hAr : A ∉ r := fun h => hC'b (line_unique hAC h hCr hAb hCb ▸ hC'r)
  -- the lines of `α`
  have aα : LiesInPlane (Point := P) a α := liesInPlane_of_mem hBC hBa hCa hB hC
  have bα : LiesInPlane (Point := P) b α := liesInPlane_of_mem hAC hAb hCb hA hC
  have cα : LiesInPlane (Point := P) c α := liesInPlane_of_mem hAB hAc hBc hA hB
  have b'α : LiesInPlane (Point := P) b' α := liesInPlane_of_mem hA'C' hAb' hCb' hA' hC'
  have c'α : LiesInPlane (Point := P) c' α := liesInPlane_of_mem hA'B' hAc' hBc' hA' hB'
  -- a point `S` outside `α`
  obtain ⟨S, hS⟩ := exists_not_mem (P := P) L α
  have neα : ∀ X : P, X ∈ α → X ≠ S := fun X hX e => hS (e ▸ hX)
  -- the lines `OS`, `AS`, `BS`, `CS`, `OA`
  obtain ⟨s, hOs, hSs⟩ := exists_line (Line := L) (neα O hO)
  obtain ⟨nA, hAnA, hSnA⟩ := exists_line (Line := L) (neα A hA)
  obtain ⟨nB, hBnB, hSnB⟩ := exists_line (Line := L) (neα B hB)
  obtain ⟨nC, hCnC, hSnC⟩ := exists_line (Line := L) (neα C hC)
  obtain ⟨oA, hOoA, hAoA⟩ := exists_line (Line := L) hOA
  -- a line through two distinct points of `α` and through `S` is impossible
  have offα : ∀ {X Y : P} {l : L}, X ≠ Y → X ∈ α → Y ∈ α → X ∈ l → Y ∈ l → S ∉ l :=
    fun hXY hX hY h1 h2 hSl => hS (mem_plane_of hXY h1 h2 hX hY hSl)
  -- the plane `β₁ = OBS`
  obtain ⟨β₁, hOβ₁, hBβ₁, hSβ₁⟩ := exists_plane (not_collinear_of_out (L := L) hOB hO hB hS)
  have sβ₁ : LiesInPlane (Point := P) s β₁ := liesInPlane_of_mem (neα O hO) hOs hSs hOβ₁ hSβ₁
  have nBβ₁ : LiesInPlane (Point := P) nB β₁ :=
    liesInPlane_of_mem (neα B hB) hBnB hSnB hBβ₁ hSβ₁
  have qβ₁ : LiesInPlane (Point := P) q β₁ := liesInPlane_of_mem hOB hOq hBq hOβ₁ hBβ₁
  have hB'β₁ : B' ∈ β₁ := qβ₁ B' hB'q
  have hsnB : s ≠ nB := fun e => offα hOB hO hB hOs (e ▸ hBnB) hSs
  have hB'nB : B' ∉ nB := fun h => offα hBB' hB hB' hBnB h hSnB
  -- `S'` on `OS` with `S'B' ∥ SB`
  obtain ⟨mB, mBβ₁, hB'mB, hmBn⟩ := exists_parallel nBβ₁ hB'β₁ hB'nB
  obtain ⟨S', hS's, hS'mB⟩ := meets_of_parallel sβ₁ nBβ₁ mBβ₁ hSs hSnB hsnB hmBn
  have hS' : S' ∉ α := by
    intro hS'α
    by_cases hS'O : S' = O
    · subst hS'O
      have : mB = q := line_unique hOB' hS'mB hB'mB hOq hB'q
      exact hmBn ⟨B, this ▸ hBq, hBnB⟩
    · exact offα hS'O hS'α hO hS's hOs hSs
  have neα' : ∀ X : P, X ∈ α → X ≠ S' := fun X hX e => hS' (e ▸ hX)
  have hS'S : S' ≠ S := fun e => hmBn ⟨S, e ▸ hS'mB, hSnB⟩
  -- step 1: `S'C' ∥ SC`, through the planes `SBC` and `S'B'C'`
  obtain ⟨π₁, hBπ₁, hCπ₁, hSπ₁⟩ := exists_plane (not_collinear_of_out (L := L) hBC hB hC hS)
  obtain ⟨π₁', hB'π₁', hC'π₁', hS'π₁'⟩ :=
    exists_plane (not_collinear_of_out (L := L) hB'C' hB' hC' hS')
  have hπ₁α : π₁ ≠ α := fun e => hS (e ▸ hSπ₁)
  have hπ₁ : π₁ ≠ π₁' := by
    intro e
    exact hB'a (mem_of_planes hπ₁α hBC hBa hCa hBπ₁ hCπ₁ hB hC (e ▸ hB'π₁') hB')
  have nBπ₁ : LiesInPlane (Point := P) nB π₁ := liesInPlane_of_mem (neα B hB) hBnB hSnB hBπ₁ hSπ₁
  have aπ₁ : LiesInPlane (Point := P) a π₁ := liesInPlane_of_mem hBC hBa hCa hBπ₁ hCπ₁
  have hnBa : nB ≠ a := fun e => offα hBC hB hC hBa hCa (e ▸ hSnB)
  have hβ₁π₁' : β₁ ≠ π₁' := by
    intro e
    have hβ₁α : β₁ ≠ α := fun e' => hS (e' ▸ hSβ₁)
    exact hC'q (mem_of_planes hβ₁α hOB hOq hBq hOβ₁ hBβ₁ hO hB (e ▸ hC'π₁') hC')
  have hS'β₁ : S' ∈ β₁ := sβ₁ S' hS's
  have n1 : ∀ U : P, U ∈ nB → U ∉ π₁' :=
    not_mem_plane_of hβ₁π₁' nBβ₁ (neα' B' hB') hB'mB hS'mB hB'β₁ hS'β₁ hB'π₁' hS'π₁'
      (fun ⟨Z, h1, h2⟩ => hmBn ⟨Z, h2, h1⟩)
  have hαπ₁' : α ≠ π₁' := fun e => hS' (e ▸ hS'π₁')
  have n2 : ∀ U : P, U ∈ a → U ∉ π₁' :=
    not_mem_plane_of hαπ₁' aα hB'C' hBa' hCa' hB' hC' hB'π₁' hC'π₁' pa
  have disj₁ := planes_disjoint hπ₁ nBπ₁ aπ₁ hBnB hBa hnBa n1 n2
  obtain ⟨mC, hC'mC, hS'mC⟩ := exists_line (Line := L) (neα' C' hC')
  have mCπ₁' : LiesInPlane (Point := P) mC π₁' :=
    liesInPlane_of_mem (neα' C' hC') hC'mC hS'mC hC'π₁' hS'π₁'
  have hnCmC : ¬Meets (Point := P) nC mC := fun ⟨Z, h1, h2⟩ =>
    disj₁ Z (liesInPlane_of_mem (neα C hC) hCnC hSnC hCπ₁ hSπ₁ Z h1) (mCπ₁' Z h2)
  -- the plane `β₂ = OAS` and `A''` on `OA` with `S'A'' ∥ SA`
  obtain ⟨β₂, hOβ₂, hAβ₂, hSβ₂⟩ := exists_plane (not_collinear_of_out (L := L) hOA hO hA hS)
  have hβ₂α : β₂ ≠ α := fun e => hS (e ▸ hSβ₂)
  have sβ₂ : LiesInPlane (Point := P) s β₂ := liesInPlane_of_mem (neα O hO) hOs hSs hOβ₂ hSβ₂
  have nAβ₂ : LiesInPlane (Point := P) nA β₂ :=
    liesInPlane_of_mem (neα A hA) hAnA hSnA hAβ₂ hSβ₂
  have oAβ₂ : LiesInPlane (Point := P) oA β₂ := liesInPlane_of_mem hOA hOoA hAoA hOβ₂ hAβ₂
  have hS'β₂ : S' ∈ β₂ := sβ₂ S' hS's
  have hS'nA : S' ∉ nA := by
    intro h
    have : nA = s := line_unique hS'S h hSnA hS's hSs
    exact offα hOA hO hA hOs (this ▸ hAnA) hSs
  obtain ⟨kA, kAβ₂, hS'kA, hkAn⟩ := exists_parallel nAβ₂ hS'β₂ hS'nA
  have hoAnA : oA ≠ nA := fun e => offα hOA hO hA hOoA hAoA (e ▸ hSnA)
  obtain ⟨A'', hA''oA, hA''kA⟩ := meets_of_parallel oAβ₂ nAβ₂ kAβ₂ hAoA hAnA hoAnA hkAn
  have hA''α : A'' ∈ α := mem_plane_of hOA hOoA hAoA hO hA hA''oA
  have hA''β₂ : A'' ∈ β₂ := oAβ₂ A'' hA''oA
  have hA''O : A'' ≠ O := by
    intro e
    subst e
    have : kA = s := line_unique (neα' A'' hA''α) hA''kA hS'kA hOs hS's
    exact hkAn ⟨S, this ▸ hSs, hSnA⟩
  have hA''q : A'' ∉ q := by
    intro h
    have : oA = q := line_unique hA''O.symm hOoA hA''oA hOq h
    exact hAq (this ▸ hAoA)
  have hA''r : A'' ∉ r := by
    intro h
    have : oA = r := line_unique hA''O.symm hOoA hA''oA hOr h
    exact hAr (this ▸ hAoA)
  have hA''B' : A'' ≠ B' := fun e => hA''q (e ▸ hB'q)
  have hA''C' : A'' ≠ C' := fun e => hA''r (e ▸ hC'r)
  have hβ₁α : β₁ ≠ α := fun e => hS (e ▸ hSβ₁)
  -- step 2: `A''B' ∥ AB`, through the planes `SAB` and `S'A''B'`
  have hA''c' : A'' ∈ c' := by
    obtain ⟨π₂, hAπ₂, hBπ₂, hSπ₂⟩ := exists_plane (not_collinear_of_out (L := L) hAB hA hB hS)
    obtain ⟨π₂', hA''π₂', hB'π₂', hS'π₂'⟩ :=
      exists_plane (not_collinear_of_out (L := L) hA''B' hA''α hB' hS')
    have hπ₂α : π₂ ≠ α := fun e => hS (e ▸ hSπ₂)
    have hπ₂ : π₂ ≠ π₂' := fun e =>
      hB'c (mem_of_planes hπ₂α hAB hAc hBc hAπ₂ hBπ₂ hA hB (e ▸ hB'π₂') hB')
    have nAπ₂ : LiesInPlane (Point := P) nA π₂ :=
      liesInPlane_of_mem (neα A hA) hAnA hSnA hAπ₂ hSπ₂
    have nBπ₂ : LiesInPlane (Point := P) nB π₂ :=
      liesInPlane_of_mem (neα B hB) hBnB hSnB hBπ₂ hSπ₂
    have hnAnB : nA ≠ nB := fun e => offα hAB hA hB hAnA (e ▸ hBnB) hSnA
    have hβ₂π₂' : β₂ ≠ π₂' := by
      intro e
      have hB'oA : B' ∈ oA :=
        mem_of_planes hβ₂α hOA hOoA hAoA hOβ₂ hAβ₂ hO hA (e ▸ hB'π₂') hB'
      have : oA = q := line_unique hOB' hOoA hB'oA hOq hB'q
      exact hAq (this ▸ hAoA)
    have m1 : ∀ U : P, U ∈ nA → U ∉ π₂' :=
      not_mem_plane_of hβ₂π₂' nAβ₂ (neα' A'' hA''α).symm hS'kA hA''kA hS'β₂ hA''β₂ hS'π₂'
        hA''π₂' (fun ⟨Z, h1, h2⟩ => hkAn ⟨Z, h2, h1⟩)
    have hβ₁π₂' : β₁ ≠ π₂' := fun e =>
      hA''q (mem_of_planes hβ₁α hOB hOq hBq hOβ₁ hBβ₁ hO hB (e ▸ hA''π₂') hA''α)
    have m2 : ∀ U : P, U ∈ nB → U ∉ π₂' :=
      not_mem_plane_of hβ₁π₂' nBβ₁ (neα' B' hB').symm hS'mB hB'mB hS'β₁ hB'β₁ hS'π₂' hB'π₂'
        (fun ⟨Z, h1, h2⟩ => hmBn ⟨Z, h2, h1⟩)
    have disj₂ := planes_disjoint hπ₂ nAπ₂ nBπ₂ hSnA hSnB hnAnB m1 m2
    obtain ⟨k, hA''k, hB'k⟩ := exists_line (Line := L) hA''B'
    have hck : ¬Meets (Point := P) k c := fun ⟨Z, h1, h2⟩ =>
      disj₂ Z (liesInPlane_of_mem hAB hAc hBc hAπ₂ hBπ₂ Z h2)
        (liesInPlane_of_mem hA''B' hA''k hB'k hA''π₂' hB'π₂' Z h1)
    have : k = c' := parallel_unique cα hB' hB'c
      (liesInPlane_of_mem hA''B' hA''k hB'k hA''α hB') hB'k hck c'α hBc'
      (fun ⟨Z, h1, h2⟩ => pc ⟨Z, h2, h1⟩)
    exact this ▸ hA''k
  -- step 3: `A''C' ∥ AC`, through the planes `SAC` and `S'A''C'`
  have hA''b' : A'' ∈ b' := by
    obtain ⟨π₃, hAπ₃, hCπ₃, hSπ₃⟩ := exists_plane (not_collinear_of_out (L := L) hAC hA hC hS)
    obtain ⟨π₃', hA''π₃', hC'π₃', hS'π₃'⟩ :=
      exists_plane (not_collinear_of_out (L := L) hA''C' hA''α hC' hS')
    have hπ₃α : π₃ ≠ α := fun e => hS (e ▸ hSπ₃)
    have hπ₃ : π₃ ≠ π₃' := fun e =>
      hC'b (mem_of_planes hπ₃α hAC hAb hCb hAπ₃ hCπ₃ hA hC (e ▸ hC'π₃') hC')
    have nAπ₃ : LiesInPlane (Point := P) nA π₃ :=
      liesInPlane_of_mem (neα A hA) hAnA hSnA hAπ₃ hSπ₃
    have nCπ₃ : LiesInPlane (Point := P) nC π₃ :=
      liesInPlane_of_mem (neα C hC) hCnC hSnC hCπ₃ hSπ₃
    have hnAnC : nA ≠ nC := fun e => offα hAC hA hC hAnA (e ▸ hCnC) hSnA
    have hβ₂π₃' : β₂ ≠ π₃' := by
      intro e
      have hC'oA : C' ∈ oA :=
        mem_of_planes hβ₂α hOA hOoA hAoA hOβ₂ hAβ₂ hO hA (e ▸ hC'π₃') hC'
      have : oA = r := line_unique hOC' hOoA hC'oA hOr hC'r
      exact hAr (this ▸ hAoA)
    have m1 : ∀ U : P, U ∈ nA → U ∉ π₃' :=
      not_mem_plane_of hβ₂π₃' nAβ₂ (neα' A'' hA''α).symm hS'kA hA''kA hS'β₂ hA''β₂ hS'π₃'
        hA''π₃' (fun ⟨Z, h1, h2⟩ => hkAn ⟨Z, h2, h1⟩)
    -- the plane `β₃ = OCS` contains `SC` and `S'C'`
    obtain ⟨β₃, hOβ₃, hCβ₃, hSβ₃⟩ := exists_plane (not_collinear_of_out (L := L) hOC hO hC hS)
    have hβ₃α : β₃ ≠ α := fun e => hS (e ▸ hSβ₃)
    have nCβ₃ : LiesInPlane (Point := P) nC β₃ :=
      liesInPlane_of_mem (neα C hC) hCnC hSnC hCβ₃ hSβ₃
    have hS'β₃ : S' ∈ β₃ := liesInPlane_of_mem (neα O hO) hOs hSs hOβ₃ hSβ₃ S' hS's
    have hC'β₃ : C' ∈ β₃ := liesInPlane_of_mem hOC hOr hCr hOβ₃ hCβ₃ C' hC'r
    have hβ₃π₃' : β₃ ≠ π₃' := fun e =>
      hA''r (mem_of_planes hβ₃α hOC hOr hCr hOβ₃ hCβ₃ hO hC (e ▸ hA''π₃') hA''α)
    have m2 : ∀ U : P, U ∈ nC → U ∉ π₃' :=
      not_mem_plane_of hβ₃π₃' nCβ₃ (neα' C' hC') hC'mC hS'mC hC'β₃ hS'β₃ hC'π₃' hS'π₃' hnCmC
    have disj₃ := planes_disjoint hπ₃ nAπ₃ nCπ₃ hSnA hSnC hnAnC m1 m2
    obtain ⟨k, hA''k, hC'k⟩ := exists_line (Line := L) hA''C'
    have hbk : ¬Meets (Point := P) k b := fun ⟨Z, h1, h2⟩ =>
      disj₃ Z (liesInPlane_of_mem hAC hAb hCb hAπ₃ hCπ₃ Z h2)
        (liesInPlane_of_mem hA''C' hA''k hC'k hA''π₃' hC'π₃' Z h1)
    have : k = b' := parallel_unique bα hC' hC'b
      (liesInPlane_of_mem hA''C' hA''k hC'k hA''α hC') hC'k hbk b'α hCb'
      (fun ⟨Z, h1, h2⟩ => pb ⟨Z, h2, h1⟩)
    exact this ▸ hA''k
  -- conclusion: `A'' = A'`, so `p = OA` passes through `O`
  have hA''A' : A'' = A' := by
    by_contra hne
    have : b' = c' := line_unique hne hA''b' hAb' hA''c' hAc'
    exact nABC' ⟨c', hAc', hBc', this ▸ hCb'⟩
  have : oA = p := line_unique hAA' hAoA (hA''A' ▸ hA''oA) hAp hA'p
  exact this ▸ hOoA

/-- `concurrent` without the non-degeneracy hypotheses: they follow from the parallelism of the
sides (and `O ∈ α` from `O ∈ BB'`). -/
theorem concurrent' {α : Pl} {A B C A' B' C' O : P} {a b c a' b' c' p q r : L}
    (hA : A ∈ α) (hB : B ∈ α) (hC : C ∈ α) (hA' : A' ∈ α) (hB' : B' ∈ α) (hC' : C' ∈ α)
    (nABC : ¬Collinear A B C) (nABC' : ¬Collinear A' B' C')
    (hBa : B ∈ a) (hCa : C ∈ a) (hCb : C ∈ b) (hAb : A ∈ b) (hAc : A ∈ c) (hBc : B ∈ c)
    (hBa' : B' ∈ a') (hCa' : C' ∈ a') (hCb' : C' ∈ b') (hAb' : A' ∈ b') (hAc' : A' ∈ c')
    (hBc' : B' ∈ c')
    (pa : ¬Meets (Point := P) a a') (pb : ¬Meets (Point := P) b b')
    (pc : ¬Meets (Point := P) c c')
    (hAp : A ∈ p) (hA'p : A' ∈ p) (hBq : B ∈ q) (hB'q : B' ∈ q) (hCr : C ∈ r) (hC'r : C' ∈ r)
    (hOq : O ∈ q) (hOr : O ∈ r) : O ∈ p := by
  have hAB : A ≠ B := fun e => nABC ⟨a, e ▸ hBa, hBa, hCa⟩
  have hBC : B ≠ C := fun e => nABC ⟨c, hAc, hBc, e ▸ hBc⟩
  have hB'C' : B' ≠ C' := fun e => nABC' ⟨c', hAc', hBc', e ▸ hBc'⟩
  have hB'c : B' ∉ c := fun h => pc ⟨B', h, hBc'⟩
  have hBB' : B ≠ B' := fun e => hB'c (e ▸ hBc)
  have hOB : O ≠ B := by
    rintro rfl
    have : r = a := line_unique hBC hOr hCr hBa hCa
    exact pa ⟨C', this ▸ hC'r, hCa'⟩
  have hOC : O ≠ C := by
    rintro rfl
    have : q = a := line_unique hBC hBq hOq hBa hCa
    exact pa ⟨B', this ▸ hB'q, hBa'⟩
  have hOB' : O ≠ B' := by
    rintro rfl
    have : r = a' := line_unique hB'C' hOr hC'r hBa' hCa'
    exact pa ⟨C, hCa, this ▸ hCr⟩
  have hOC' : O ≠ C' := by
    rintro rfl
    have : q = a' := line_unique hB'C' hB'q hOq hBa' hCa'
    exact pa ⟨B, hBa, this ▸ hBq⟩
  have hOA : O ≠ A := by
    rintro rfl
    have : q = c := line_unique hAB hOq hBq hAc hBc
    exact hB'c (this ▸ hB'q)
  exact concurrent hA hB hC hA' hB' hC' (mem_plane_of hBB' hBq hB'q hB hB' hOq) nABC nABC'
    hBa hCa hCb hAb hAc hBc hBa' hCa' hCb' hAb' hAc' hBc' pa pb pc hAp hA'p hBq hB'q hCr hC'r
    hOq hOr hOA hOB hOC hOB' hOC'

/-- **Desargues's theorem (Theorem 32, direct part) in a plane of a space satisfying I and III.**
Two triangles of a plane `α` whose homologous sides lie on lines without common point: the lines
`AA'`, `BB'`, `CC'` pass through one point or are pairwise without common point. The second case
reduces to the first by relabelling the triangles. -/
theorem direct {α : Pl} {A B C A' B' C' : P} {a b c a' b' c' p q r : L}
    (hA : A ∈ α) (hB : B ∈ α) (hC : C ∈ α) (hA' : A' ∈ α) (hB' : B' ∈ α) (hC' : C' ∈ α)
    (nABC : ¬Collinear A B C) (nABC' : ¬Collinear A' B' C')
    (hBa : B ∈ a) (hCa : C ∈ a) (hCb : C ∈ b) (hAb : A ∈ b) (hAc : A ∈ c) (hBc : B ∈ c)
    (hBa' : B' ∈ a') (hCa' : C' ∈ a') (hCb' : C' ∈ b') (hAb' : A' ∈ b') (hAc' : A' ∈ c')
    (hBc' : B' ∈ c')
    (pa : ¬Meets (Point := P) a a') (pb : ¬Meets (Point := P) b b')
    (pc : ¬Meets (Point := P) c c')
    (hAp : A ∈ p) (hA'p : A' ∈ p) (hBq : B ∈ q) (hB'q : B' ∈ q) (hCr : C ∈ r) (hC'r : C' ∈ r) :
    (∃ O : P, O ∈ p ∧ O ∈ q ∧ O ∈ r) ∨
      (¬Meets (Point := P) p q ∧ ¬Meets (Point := P) q r ∧ ¬Meets (Point := P) p r) := by
  by_cases hqr : Meets (Point := P) q r
  · obtain ⟨O, hOq, hOr⟩ := hqr
    exact Or.inl ⟨O, concurrent' hA hB hC hA' hB' hC' nABC nABC' hBa hCa hCb hAb hAc hBc hBa' hCa'
      hCb' hAb' hAc' hBc' pa pb pc hAp hA'p hBq hB'q hCr hC'r hOq hOr, hOq, hOr⟩
  · refine Or.inr ⟨?_, hqr, ?_⟩
    · -- `p`, `q` meet: relabel `(A, B, C) ↦ (C, A, B)`
      rintro ⟨O, hOp, hOq⟩
      have := concurrent' hC hA hB hC' hA' hB' (fun h => nABC h.swap12.swap23)
        (fun h => nABC' h.swap12.swap23) hAc hBc hBa hCa hCb hAb hAc' hBc' hBa' hCa' hCb' hAb'
        pc pa pb hCr hC'r hAp hA'p hBq hB'q hOp hOq
      exact hqr ⟨O, hOq, this⟩
    · -- `p`, `r` meet: relabel `(A, B, C) ↦ (B, C, A)`
      rintro ⟨O, hOp, hOr⟩
      have := concurrent' hB hC hA hB' hC' hA' (fun h => nABC h.swap23.swap12)
        (fun h => nABC' h.swap23.swap12) hCb hAb hAc hBc hBa hCa hCb' hAb' hAc' hBc' hBa' hCa'
        pb pc pa hBq hB'q hCr hC'r hAp hA'p hOr hOp
      exact hqr ⟨O, this, hOr⟩

end Parallels

end SpaceDesargues

end HilbertFoundations
