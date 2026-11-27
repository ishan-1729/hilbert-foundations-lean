# CRITIQUE (lens: Lean feasibility) of `BLUEPRINT.md` — `concl.angle_sum`

Scope: whether the blueprint can be turned into Lean 4 (v4.36.0, the repository's mathlib) as
written — names and types of the declarations relied on, well-typedness of the planned statements
of § 4, import order, file sizes, the hard spots. The mathematics was read only as far as needed to
check that each cited lemma is applied with arguments of the right shape (every role assignment of
E2/E3/E5/F4/G6/G7/G8 against the § 4 signatures was checked by hand and matches).

(This file replaces an earlier, unfinished version of the same critique whose scratch compile had
never been run; its findings were re-checked independently and are kept where they still hold.)

## Verdict

**Fixable.** No wrong name, no wrong type, no import cycle. One planned statement is not provable as
stated (`sLt_congr_right`, issue 1). Everything else is engineering: a missing variable name, one
hidden hypothesis, three files that will overflow 400 lines, the missing `--olean` build step,
and long anonymous conjunctions.

## What was checked

* **Repository declarations of § 2 / § 5**: looked up with `grep` in the file the blueprint names.
  All exist with the stated names, argument orders and conclusions, including those the blueprint
  says were "read, not compiled": `Frame.angLt_congr` (CongruenceAux5 l. 317),
  `mem_interior_of_rays_plane` (CongruenceAux6 l. 366), `Pas.exists_isom_of_tri` (PascalAux1 l. 208),
  `segCong_trans`/`segCong_symm` (CongruenceAux2 l. 35/30), `exists_not_mem` (OrderAux l. 98),
  `Collinear.perm231/312` (OrderAux l. 56/59), `OrderLin.trans₁` (OrderAux l. 637),
  `OrderCore.between_of_between_between₂'` (l. 435), `OrderCore.ne_of_opp` (l. 263),
  `sameSide_or_opp'`, `not_sameSide_of_opp'`, `sameSide_of_ray`, `mem_ray_of_sameSide`,
  `interior_swap`, `mem_ray_or_between`, `not_mem_ray_of_between` (CongruenceAux l. 189–255),
  `nc_of`, `eq_of_collinear_collinear` (CongruenceAux2 l. 149/158), `line_comm` (Basic l. 579),
  `Pas.isom_inv`, `Pas.isom_cong` (PascalAux1 l. 102/58), `Pas.perm_apply_inv/perm_inv_apply`
  (PascalAux2 l. 60/63).
* **mathlib declarations of § 5** (`rg` in `.lake/packages/mathlib/Mathlib`):
  `Equiv.Perm.mul_apply` / `one_apply` / `inv_eq_iff_eq` (`Algebra/Group/End.lean` l. 101/104/133),
  `Equiv.injective` / `apply_symm_apply` / `symm_apply_apply` (`Logic/Equiv/Defs.lean`
  l. 177/247/249), `Subgroup.mul_mem` / `inv_mem` (`Algebra/Group/Subgroup/Defs.lean` l. 436/441).
  All as stated.
* **Target block** (`Commentary.lean` l. 608–638, 715–721) copied correctly; the definitions live in
  `section AngleSum` with `{P L : Type*} [HasLines P L] [HasBetween P] [HasAngCong P]`, `L` explicit.
  `Commentary` imports only `Analytic`, `Order`, `Congruence`: no cycle with the new chain.
* **Name clashes**: no `HilbertFoundations.AngSum.*`, no `tri_saccheri`, `saccheri_sameType`,
  `angleSumTheorem` anywhere in `HilbertFoundations/`. Wrappers named like `Frame` fields
  (`crossbar`, `layoff`, …) live in `AngSum` and shadow nothing outside it.
* **Scratch compile** `.lake-local/scratch/anglesum-critic-lean2/K1.lean`, importing
  `PascalAux2` and `Commentary`, containing **every** definition and **every** statement of
  § 4.1–4.13 (with `sorry` where no proof is given), complete proofs of ~25 lemmas
  (wrappers, `interior_rays`, `mem_interior_iff`, `opp_of_interior`, `interior_trans`,
  `isom_rightAng`, `isom_sameSide_self`, `isom_opp_self`, `ht_mem`, `angLt_congr_right`,
  `sLt_trichotomy`, `biRight_mk`, `lambert_symm`, `exists_common`, `sLt_congr_right` *with the fix
  of issue 1*, `lambert_cut` and `lambert_transport` up to one small `sorry` each), API-fit tests of
  `theorem12`, `theorem13`, `theorem14` (exactly in the shape of B1 step 5), `vertical_angles`,
  `Pas.mem_ray_of_between_between`, and `#check`s of the remaining uncompiled names.
  Result: see the last section.

## Issues (most severe first)

### 1. (major, statement) `sLt_congr_right` is not provable as stated — § 4.5, C2

```lean
theorem sLt_congr_right (h : SLt A B C D) (hC'D' : C' ≠ D') (hc : SegCong C D C' D') : SLt A B C' D'
```

The proof needs `SegCong A B C' X'` from `SegCong A B C X` and `SegCong C X C' X'`, i.e.
`segCong_trans (hAB : A ≠ B) …`. Axiom IV 2 is stated for genuine segments only (`AxiomIV2`,
`Basic.lean` l. 1197–1199), so `SegCong A A _ _` is unconstrained and `A ≠ B` is neither assumed
nor derivable.
**Fix.** Add `(hAB : A ≠ B)`:

```lean
theorem sLt_congr_right (h : SLt A B C D) (hAB : A ≠ B) (hC'D' : C' ≠ D')
    (hc : SegCong C D C' D') : SLt A B C' D' := by
  obtain ⟨W, hW, hcW⟩ := h
  have hCW : C ≠ W := ne12_of_between (Line := L) hW
  obtain ⟨W', hW'r, hcW'⟩ := segCong_layoff (L := L) hCW hC'D'
  have b := between_of_segCong_ray (L := L) hW hW'r hcW' hc
  exact ⟨W', b, segCong_trans (L := L) hAB hCW (ne12_of_between (Line := L) b) hcW hcW'⟩
```

(compiled in `K1.lean`). In Stages D–F every compared segment is a side of a right angle, so
`A ≠ B` is always available from `ne_of_nc hl` of that `RightAng`. General rule to state in § 3.0: **every
lemma that transports `SegCong`/`SLt` needs both `≠`, every `AngCong` transport both
non-collinearities.**

### 2. (minor, statement) `gtSupp_of_copy` hides a non-collinearity — § 4.4, B8(c)

The proof ("A1 with `angCong_refl`: `∠BOC < ∠BOX`") needs `¬Collinear X O B` (and `X ≠ O` for
`nc_of_interior`). They follow from `C ∈ Interior X O B` only by unfolding `Interior` with a line
through `O, X` — no named lemma.
**Fix.** Add `(hX' : ¬Collinear (Line := L) X O B)`; at the only use (G7, `Pos₊`, `X := A₁`,
`O := C`, `B := H`) it is the field `TriConf.ncH'`. Or prove once a helper
`nc_of_mem_interior_left : X ∈ Interior A O B → ¬Collinear A O B → …` — but the extra hypothesis is
cheaper.

### 3. (minor, statement) the common `variable` line of § 4.0 lacks `P'`

`saccheri_out_aux/lt/gt/eq/type` (§ 4.8) use `P'`; with `autoImplicit = false` they do not
elaborate. Appendix A has `P'` but lacks `F G A₁ B₁ O₁`.
**Fix.** `{A B C D E F G H K M N O Q X Y Z A' B' C' D' O' A₁ B₁ O₁ P' : P} {l m : L}`
(compiled in `K1.lean`; all other identifiers of § 4 are bound there or locally).

### 4. (minor, process) the chain cannot be checked without writing `.olean`s — § 4.0

`AuxN` imports `Aux(N-1)`; `python .lake-local/leanc.py File.lean` without `--olean` only
type-checks. Each finished file must be compiled once with
`python .lake-local/leanc.py HilbertFoundations/AngleSumCloseAuxN.lean --olean` before the next can
be checked (docstring of `leanc.py`, l. 4–7). The blueprint never says so.
**Fix.** Add this sentence to § 4.0, and the advice to finish (and `--olean`) each file before
starting the next; one compile can wait minutes for a slot (this critique's compile queued behind
three others).

### 5. (minor, size) files 8, 12, 13 will exceed 400 lines

Calibration from compiled proofs: about one Lean line per atomic step of § 3 (`ext_angle_aux` 34
lines, `exists_perp_at` 27, `interior_trans` 25, `lambert_cut` 33). Stage E: ≈ 450–500
(E2 and E3 each ≈ 110–130: ~12 side-of-line facts over 7 lines, each 2–4 lines);
G3: ≈ 420–480 (nine items, each 30–60); G4–G8: ≈ 430–480 (G6 has six directions).
**Fix.** Plan the splits now: `Aux8` = shared setting + E1 + E2, `Aux8b` = E3–E5;
`Aux12` = G3 items 1–5, `Aux12b` = items 6–9 + `exists_triConf`; `Aux13` = G4–G6,
`Aux14` = G7–G8. Realistic total ≈ 4800–5200 lines rather than 4400.

### 6. (minor, interface) long anonymous conjunctions

`tri_midline` returns 15 conjuncts under 6 binders; E2/E3/E4 share ~15 incidence facts that § 4.8
leaves to "a private lemma". `obtain ⟨…15 names…⟩` works but is fragile and must be repeated.
**Fix.** `Prop`-structures, as already done for `TriConf`, e.g.

```lean
variable (L) in
structure MidConf (A B C D E F G H : P) (e : L) : Prop where
  htA : Pas.ht (L := L) D A = C
  htB : Pas.ht (L := L) E B = C
  bD : Between A D C
  bE : Between B E C
  hD : D ∈ e
  hE : E ∈ e
  hA : A ∉ e
  hB : B ∉ e
  hC : C ∉ e
  fA : Foot e A F
  fB : Foot e B G
  fC : Foot e C H
  htF : Pas.ht (L := L) D F = H
  htG : Pas.ht (L := L) E G = H
  sac : Saccheri L F G A B
```

and an `OutConf` for Stage E holding the seven lines `l s q a b` (+ `d c` after E1) as **fields**
(plain `L` variables, not `line … h` terms), the memberships, the `¬Meets` facts and the two
auxiliary Saccheri quadrilaterals. Then each `SameSide` in (f1)–(g3) is one
`sameSide_of_not_meets` / `sameSide_of_between_mem'` and each `Interior` one `mem_interior_iff`.

### 7. (minor, engineering, optional) `Aux13` imports `Commentary`

`Commentary` drags `Analytic` (mathlib analysis) into every compile of the most delicate file of
Stage G (the appendix file took 193 s with it). The predicates are only needed to *state* G4/G6/G8.
**Fix (optional).** State G4/G6/G8 for the unfolded bodies (e.g. for
`∃ X' Y' : P, (Between A C X' ∧ AngCong C A B X' C Y' ∧ ∀ a : L, A ∈ a → C ∈ a → SameSide a Y' B) ∧ …`)
and repackage in `AngleSumClose.lean` by `Iff.rfl` after `unfold`. If not adopted, the blueprint's
arrangement is correct (`K1.lean` elaborates the G statements with `Commentary` imported).

### 8. (minor, survey) existing isometry API not listed in § 2.6

`PascalAux1.lean` (section `Isometries`, `[PlaneCongruence]` only) also has `Pas.isom_line`
(l. 117), `Pas.imLine`, `Pas.mem_imLine`, `Pas.mem_imLine'` (l. 124–130), `Pas.isom_sameSide`
(l. 135), `Pas.isom_opp` (l. 146), `Pas.isom_ray` (l. 153), `Pas.isom_meets_iff` (l. 160),
`Pas.isom_fix_line` (l. 389), `Pas.hl_of_ne` (l. 62); `CongruenceAux5.lean` has
`Frame.parallel_of_alternate` (l. 117: alternate angles congruent ⟹ lines do not meet, Euclid I 27).
Nothing is wrong because of this, but G3(9) ("the image under `ρ` of the line `CB₁` is the line
`AB`") is exactly `Pas.mem_imLine`, and `Pas.isom_ray` removes several `angCong_rays`
book-keeping steps when transporting rays by `ρ`, `ρ'`.

## Hardest steps for the formalization, with concrete suggestions

1. **Stage E (E2, E3).** Not hard mathematically, but ~25 side-of-a-line facts over seven lines.
   Fix the lines once by `obtain ⟨q, hQq, hPq⟩ := exists_line …` (never `line … h` terms), bundle
   them in `OutConf` (issue 6), and use `mem_interior_iff` so no `line`-term is ever rewritten.
   E3's final step (A8 + B1 + A7 by contradiction) is best written as
   `rcases angLt_trichotomy hl n1 n2 with h | h | h` with the two bad cases closed by one shared
   `have key : AngLt … ∨ AngCong … → False`.
2. **`angLt_add` (B1).** The `theorem14` call compiles in the exact shape of step 5
   (`theorem14 (L := L) hBO hB₁O' h1n h2n h3n h1n' h2n' h3n' h1 h2 (Or.inr ⟨ho, ho'⟩)` with
   `ho : OppositeSides (line (Line := L) O B hBO.symm) A C`); get `ho`, `ho'` from `opp_of_interior`
   with `mem_line_left _`, `mem_line_right _`.
3. **D3 (`saccheri_refl`).** The case split `sameSide_or_opp'` on `C, W` with 0.8 is fine; get
   `∀ Z, Z ∈ l ↔ g Z ∈ l` from `Pas.isom_collinear` and `Pas.refl_refl` once as a lemma
   `refl_mem_line_iff (hA : A ∈ l) (hB : B ∈ l) (hAB : A ≠ B) (e : Pas.refl m A = B)`.
4. **G6, direction "predicate → position".** Replace the witnesses `X' Y'` by `X Y` once, in a
   lemma `triConf_canon` returning `Interior X' C B = Interior X C B`,
   `Interior Y' C B = Interior Y C B` (`interior_rays`) and the `angCong_rays` transport of
   `∠Y'CB`; then the three cases do not repeat the ray book-keeping.
5. **Rewriting under isometries.** `rw [Pas.refl_fix hG]`, `rw [f1, f2] at a1`,
   `generalize Pas.ht (L := L) M B = B' at …` work (appendix, `K1.lean`). Do **not** introduce the
   map with `set g := Pas.refl m`: a later `rw [hrefl]` with `hrefl : Pas.refl m A = B` no longer
   finds its pattern. Keep `Pas.refl m` explicit.
6. **Degenerate values.** `SegCong`/`AngCong` are junk on degenerate arguments. Get the needed `≠`
   from `ne_of_nc hl` of the relevant `RightAng`/non-collinearity (e.g. `RightAng B A C` gives
   `B ≠ A`, `C ≠ A`); worth one sentence in § 3.0 (see issue 1).

## Result of the scratch compile

`python .lake-local/leanc.py .lake-local/scratch/anglesum-critic-lean2/K1.lean` (182 s once it had a
slot) reported **exactly one error**. Everything else elaborated, and Lean keeps checking after an
error, so the rest of the file was checked too. The error is in one of the critic's own test proofs,
not in a blueprint statement: in `lambert_cut` (final `rt_side` step) the term
`(collinear_of_between (between_symm hb)).perm231.swap23` has type `Collinear D₁ D N` where
`Collinear N D D₁` is needed. The right permutation is `(collinear_of_between hb).swap23`, or
`.swap13` of what was written. (F3's informal step "`rt_side`" is correct; it only takes the
`Collinear O B B'` argument in the order vertex, old point, new point.)

So the following were confirmed:
* every definition of § 4 (`LtSupp`, `EqSupp`, `GtSupp`, `SameType`, `SLt`, `Foot`, `BiRight`,
  `Saccheri`, `Lambert`, `TriConf`) and **every statement of § 4.1–4.13** elaborates under the
  corrected variable line (issue 3), with `Commentary` imported for the G statements
  (`Conclusion.ExteriorConfig`, `Conclusion.AngleSum…TwoRight` resolve from inside
  `namespace HilbertFoundations.AngSum`);
* the fixed `sLt_congr_right` (issue 1) compiles with a complete proof;
* complete proofs of `interior_rays`, `mem_interior_iff`, `opp_of_interior`, `interior_trans`,
  `rt_*` wrappers, `isom_nc`, `isom_rightAng`, `isom_sameSide_self`, `isom_opp_self`, `ht_mem`,
  `angLt_congr_right` (via `Frame.angLt_congr`), `sLt_trichotomy`, `biRight_mk`, `lambert_symm`,
  `exists_common`, and `lambert_transport` (up to the `lambert_nc` stub, through
  `Frame.sas` + `Pas.exists_isom_of_tri` + `isom_rightAng`);
* API-fit tests of `theorem12`, `theorem13`, `theorem14` (B1 step 5 shape), `vertical_angles`,
  `Pas.mem_ray_of_between_between` all pass; `#check` confirms the signatures of
  `Pas.isom_line`, `OrderLin.trans₁/₂`, `OrderCore.between_of_between_between₂'`,
  `OrderCore.sameSide_trans`, `OrderCore.opp_of_sameSide_opp`, `Pas.isom_inv`, `exists_not_mem`
  (needs `[PlaneConnection]`, available from `PlaneCongruence`), `Pas.mem_imLine`,
  `Frame.parallel_of_alternate`.

Implementer advice from this: `Collinear` permutations (`swap12/23/13`, `perm231/312`) are the
most frequent small type errors; write the target `Collinear` explicitly with `have … : Collinear
(Line := L) N D D₁ := …` before passing it.
