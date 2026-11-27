# CRITIQUE (mathematics lens) — BLUEPRINT `concl.angle_sum`

Verdict: **sound**. I re-derived every lemma of § 3 on my own, and I found no false statement, no
circular argument and no missing case. The issues below are small: justifications that are left
implicit, and one remark about the numerical evidence. None of them changes a statement or the
architecture.

## 1. Target versus the formalization (checked binder by binder against Commentary.lean 608–721)

- `ExteriorConfig`, `AngleSumEq/Lt/GtTwoRight` and `AngleSumTheorem` are copied exactly.
- The second triangle comes with `IsTriangle A' B' C'`, which is what G8 needs. The first triangle
  gets `IsTriangle` from the predicate. `hl` comes from `Between A C X` through
  `line_through_of_ne`, and that is available under `PlaneCongruence` (the existing proof
  `angleSumEqTwoRight_of_parallels` does the same).
- Meaning of the predicates (§ 1 of the blueprint). `A₁ := ht_E A` gives `∠BCA₁ ≅ ∠CBA`, with `A₁`
  on the side of the line `CB` where `X` is. `B₁ := ht_D B` and `Y` beyond `C` on the line `B₁C`
  give the canonical half-ray `CY` (vertical angles plus the side of `B`). By G4 this half-ray does
  not depend on the witnesses. Eq ⇔ `A₁ ∈ CY`; Lt ⇔ `A₁` inside `∠YCB`; Gt (second disjunct) ⇔ `CY`
  inside `∠A₁CB`. The first disjunct of Gt never holds: G3.3 together with G4. All three are
  correct in a Euclidean sanity check: exterior angle = A + B, versus > A + B, versus < A + B.
- Stage H uses only G8 (an "iff" for each triangle) and F9. The logic is exact.

## 2. Lemma-by-lemma re-derivation (all verified)

- **Stage 0**
  - 0.2: layoff uniqueness.
  - 0.3: crossbar plus `opp_of_between_mem`.
  - 0.4: I checked the `OrderLin.trans₂` instance `(C,Y₀,X₀,A)`. It gives `Between C Y₀ A` and
    `Between Y₀ X₀ A`.
  - 0.6: SSS on `Y X Z`, first conjunct.
  - 0.8, 0.9: verified.
- **Stage A**
  - A5: `eq_of_collinear_collinear` with `(A B C) := (A O B)` gives `X = B`.
  - A8: both branches of `interior_or_interior` checked.
  - A9: `B' ∈ Interior C'O'X` follows from the two side facts as written.
- **Stage B**
  - B1: Step 1 uses 0.4 on `∠C'O'A'` with `(X,Y) = (B',B₁)`. Step 4 uses 0.4 on `∠A'O'C'`. The
    `theorem14` hypotheses are correct, and the opposite-sides alternative holds by 0.3 on both
    sides. The non-collinearity of `A'O'C₁` comes from `C₁ ∈ Interior A'O'C'`.
  - B2–B8: verified, including the arm orders in B5 (`vertical_angles` with `(C O B)`, giving
    `∠COB ≅ ∠AOD`) and in B8(a, c).
- **Stage C**
  - C1–C3: correct instances of `between_of_segCong_ray`.
  - C4 / C5: correct.
  - C6(d): only needs `f(l) ⊆ l`, because `X ∉ l` comes back from the genuine right angle at the
    image.
  - C7–C10: verified. In C8, `Z ≠ F` uses `¬Collinear F F' Y`.
- **Stage D**
  - D1: both side facts are correct. The second claim follows from the first plus
    `vertical_angles (B C E)`.
  - D3: the invariance of `l`, the same-side argument through the fixed point `W`, `C' = D`, and the
    three right angles are all verified.
  - D5: C8 with `(F,X,F',Y) = (M,B,N,D)`.
  - D6(a): the excluded alternative of `interior_or_interior` is correctly refuted by D5 for
    `Saccheri A B C E`. The exterior angle step uses D1 on `(C,D,E)` with `Between D E B`. The
    conclusion "larger side → smaller opposite summit angle" has the correct direction.
- **Stage E** (heart)
  - E1: both auxiliary Saccheri quadrilaterals are correct (`AC ≅ BD ≅ QE`).
  - E2: the memberships (f1)–(f3) and (f4) are all correct, and so is the instance of B1. Sanity
    check: in the hyperbolic plane the summit line diverges, so `QP > BD`, and acute < obtuse.
  - E3: the memberships (g1)–(g3) and the contradiction through B1 with `h1` in its "≤" form are
    correct.
  - E4, E5: correct, with `P` the supplement point of `∠CDB`.
- **Stage F**
  - F2: right angle at `gB` by `rt_arm`, then the image under `g`.
  - F3: two applications of C9 and Pasch through opposite sides.
  - F4: E5 is applied to `Σ = B₀*B₀D₁*D₁` with `(P,Q) = (D,B)`, which needs `Between D₁* D₁ D`,
    `Between B₀* B₀ B` and `RightAng B₀ B D` (all supplied). The comparison quadrilateral
    `B₀* B D₁* D` is a valid BiRight. Its summit angles are converted correctly through
    `D ∈ ray D₁* N` and `D₁* ∈ ray D N`. The three cases are consistent with B6.
  - F5–F9: verified. In F6, C7 is used twice. In F8, `mem_ray_cases` supplies the common smaller
    point.
- **Stage G**
  - G1: verified.
  - G2: verified, including `F ≠ G` through C7 and `eq_of_segCong_ray'`.
  - G3: items 1–9 all verified. Item 8: `CB₁ ≅ AB ≅ CA₁`, and `A₁ ≠ B₁` by the sides of `CB`.
    Item 9: `y ∩ e = ∅` because `ρ` maps `y` into the line `AB` and `e` into `e`, then D5.
  - G4–G8: verified. The ← direction of G8 uses G5 (exhaustive) together with B3 (exclusive).
  - The half-turn construction does avoid every case split on the position of `H`. I could not find
    a configuration it misses.

## 3. Issues (most severe first; all minor)

1. **minor — E2/E3 setting: two incidence facts are used without justification.**
   - `E ∉ s` is justified as "`s` meets `q` only in `P`". This needs `s ≠ q`: `Q ∈ q ∩ l`, and `s`
     does not meet `l` (D5).
   - (f3) uses `A ∉ q`: otherwise `q = l` (it contains `Q` and `A`), but `P ∈ q \ l`.
   - Fix: add these two one-liners to the shared private lemma that 4.8 recommends.
2. **minor — R4/R3 evidence.**
   - The "spherical plane" is not a model of group II, so the numerical tests never exercise the
     obtuse branch (`Pos₊`, `GtSupp`, E3) in a genuine Hilbert plane.
   - The logical proof covers that branch, and I re-derived it. Say this explicitly, and do not
     cite the spherical tests as evidence.
   - Optional: point to Dehn's non-Legendrian plane (`CommentaryClose*`) as the model where `Gt`
     really occurs.
3. **minor — G3(9): `H ∉ y` and `E ∉ y` are used implicitly** (both follow from `y ∩ e = ∅`). State
   them, because `sameSide_of_not_meets` produces them anyway.
4. **minor — D3: `M ≠ B` for `rt_arm`** is implicit (it follows from `Between A M B`). State it.

No fatal or major issue.
