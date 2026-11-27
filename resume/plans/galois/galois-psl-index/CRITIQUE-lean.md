# CRITIQUE (Lean feasibility lens) of BLUEPRINT.md — `lettre.impossible_au_dela`

Verdict: **sound** for Lean feasibility. The blueprint does not just plan the Lean code: §7 holds
the complete text of the four files, and I re-checked it on my own. The issues below are
documentation, wiring and robustness points. None of them blocks the implementation.

## What I checked independently

1. **§7 text = compiled text.** Script `.lake-local/scratch/psl-index-lean-critic/extract.py`
   pulls the four ```lean blocks out of BLUEPRINT.md §7. All four are byte-identical to
   `scratch/psl-index/final_{Aux1,Aux2,Aux3,Close}.lean.txt`. Rebuilt the same way the generator
   does it, they match `scratch/psl-index/T9.lean` exactly, except for the trailing
   `#print axioms` line.
   (Caveat: `T9.lean` has a modification time 25 s *later* than `T9.out`, because
   `gen_blueprint.py` rewrites it. The rewritten text is the same as the compiled text, which is
   why I recompiled it: see 3.)
2. **Files 1–3 compile standalone under `import Mathlib` only.** This answers the "environment
   difference" risk of §6.3. I compiled `scratch/psl-index-lean-critic/Aux123.lean`, which is
   Aux1+Aux2+Aux3 in sections, with no `GaloisOeuvres` import: `[OK]` in 187 s. Only the linter
   warnings listed in §6.3 appeared (`haveI`, `push_neg` deprecated, one unused simp arg).
   The fallback of §6.3 (importing LettreChevalier) is therefore unnecessary.
3. **Full re-run of T9.** The `T9copy.lean` compile result is recorded at the end of this file.
4. **Imports / build.** `.lake/build/lib/lean/GaloisOeuvres/LettreChevalier.olean` exists and is
   newer than its source (olean 2026-11-25 07:35, source 07:23). `leanc.py --olean` writes
   `.lake/build/lib/lean/<module>.olean`, so file 4 can import Aux1–3 after they are compiled
   with `--olean`. The import order is acyclic: Aux1–3 import only Mathlib; Close imports
   LettreChevalier and Aux1–3.
5. **File sizes:** 154 / 264 / 307 / 236 lines. These are realistic; nothing needs splitting.
6. **Mathlib names.** Every declaration used in §7 is exercised by the compile. I also checked
   with rg the names listed in §5 that §7 does *not* use: `Subgroup.instNormalCenter`
   (GroupTheory/Subgroup/Center.lean:131), `Subgroup.center_le_centralizer` (Centralizer.lean:72),
   `Matrix.SpecialLinearGroup.mem_center_iff` (SpecialLinearGroup.lean:369),
   `ConjAct.toConjAct_ofConjAct` (ConjAct.lean:96), `Nat.card_coe_set_eq` (Data/Set/Card.lean:662),
   `ZMod.charP` (Data/ZMod/Basic.lean:110), `pow_eq_one_iff_of_coprime` (Data/Int/GCD.lean:277),
   `Finset.card_le_card_of_injOn` (Data/Finset/Card.lean:430),
   `Subgroup.conjAct_pointwise_smul_iff` (Pointwise.lean:573), `MulAction.index_stabilizer`
   (Index.lean:949). All exist with the stated shapes.
7. **Axiom audit / CI.** CI runs `scripts/AxiomsAudit.lean`, which imports the root
   `GaloisOeuvres`. The axioms reported, `[propext, Classical.choice, Quot.sound]`, pass it. The
   module doc-comments of the new files begin with `/-!\n# …` and not with `/-!\n## [unit]`,
   so `scripts/unit_table.py` will not see them as duplicate units. Good.

## Issues (most severe first)

### M1 (minor, factual error in the blueprint) — `Subgroup.mem_centralizer_singleton_iff` exists
§4.3, Notes, says: "This mathlib has no `Subgroup.mem_centralizer_singleton_iff`". This is wrong.
`Mathlib/GroupTheory/Subgroup/Centralizer.lean:53`:
```lean
lemma mem_centralizer_singleton_iff {g k : G} :
    k ∈ Subgroup.centralizer {g} ↔ Commute k g
```
The §7 code does not use it, so nothing breaks. The sentence should be corrected, because an
implementer repairing a proof might otherwise rebuild it by hand. It is also the simpler tool
for `hmemD`, D2, D3 and D4 if one of those needs repair (`Commute k g` unfolds to
`k * g = g * k` by `Commute`/`SemiconjBy` defeq).

### M2 (minor, wiring) — `docs/UNITS.md` is generated, not hand-edited
§1 and §6.3 tell whoever does the wiring to update "`docs/UNITS.md` line 123" by hand. CI
(`.github/workflows/ci.yml`) runs `python3 scripts/unit_table.py --check` and then
`git diff --exit-code docs/UNITS.md`. So that file must be **regenerated** with
`python scripts/unit_table.py` after the `**Status.**` line of the unit in
`LettreChevalier.lean` is changed (for example to `proved`, or `proved (in LettreChevalierClose)`).
`unit_table.py` lists only the declarations that follow the unit block *in the same file*. The
theorem `abaissement_impossible` sits in `LettreChevalierClose.lean`, so the table will still list
only `AbaissementImpossible`. Mention the theorem's file in the Status line or the
"Lean reading" text.
Also, the new modules must be added to `GaloisOeuvres.lean`. The `lean_lib` in `lakefile.toml`
has no `globs`, so files that the root does not import are neither built nor axiom-audited by CI.
§1 says this, but it should be flagged as mandatory for CI coverage.

### M3 (minor, documentation inconsistency) — compile time
§4 and §6.3 say a run "took 30–60 minutes", but the recorded runs took 181 s (T9) and 187 s (my
Aux123). Say "3–4 minutes when a slot is free; much longer while waiting for a slot or under
memory pressure", so that implementers do not kill healthy runs or plan around a false figure.

### M4 (minor, robustness) — fragile tactic spots, if the files ever need repair
These spots compile today, but they are the ones most likely to break on a mathlib bump or
after a small edit:
* `matrix_pow_succ_of_sq`: `push_cast; module`. `module` is sensitive to the shape of the goal.
  Fallback: `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply, Matrix.smul_apply] <;> ring`.
* `pow_char_scalar`: the `first | ring1 | linear_combination -hdet` combinator after `simp`.
  Fallback: name each of the four entry goals and close each with a `linear_combination` whose
  coefficient is stated explicitly.
* `no_class_equation`: `simpa using Finset.card_nsmul_le_sum …` (it relies on `smul_eq_mul`
  normal forms) and `interval_cases hs : s.card`.
* `no_subgroup_index_p`, `hbound`: the double `Subtype.ext` injectivity trick (see §6.3 (v)).
  A cleaner reformulation:
  `Nat.card (D (x i)) = Nat.card (centralizer {↑(x i)} ⊓ K)` via `Subgroup.subgroupOfEquivOfLe`
  or `Subgroup.card_subgroupOf`-type lemmas, then `Subgroup.card_le_of_le inf_le_left`.
  Not needed now.
* The deprecated `push_neg` (two uses) is only a warning in this pin. If warnings are ever made
  errors, replace it with `push Not` or with `not_or`/`not_not` rewrites.

### M5 (nit) — `haveI := hp` in `abaissement_impossible`
The linter suggests `have`. Under `have`, the instance would still be found, because local
hypotheses of class type are instances in Lean 4. `haveI` is harmless. Optional cleanup:
`exact @LettreChevalierClose.no_subgroup_index_p p hp h11 H hH`.

## Assessment of the "hardest steps" (the lens question)
The steps the original sketch feared most are already discharged by compiled code, with good
reformulations:
* The counting in (d) is done in `K ≤ SL(2,p)` instead of `H ≤ PSL(2,p)`. This avoids lifts and
  sign ambiguity entirely, and is the right call. It uses an abstract theorem (`partition_count`)
  over any finite group with a subgroup `Z` and a map `D : Γ → Subgroup Γ`, proved once with
  `MulAction.orbitRel.Quotient (ConjAct Γ) (Subgroup Γ)`, `Finset.sum_fiberwise` and
  `MulAction.index_stabilizer`.
* The 2×2 algebra is done entry-wise with explicit `linear_combination` certificates (C1, C4,
  C6). Only the crude bound `|cen| ≤ 2q` is needed, not the torus orders `p ∓ 1`.
* The arithmetic works in ℕ with `q * c` as an `omega` atom, after `Nat.mul_sub_one` and
  re-association. A 4-term case is excluded by `card_nsmul_le_sum`.
* Coercions `K → SL` are isolated in `hmemZ` and `hmemD`.

No universe problems: `partition_count` quantifies `ι : Type u` with `Γ : Type u`, and `ι` is a
subtype of a quotient of `Subgroup Γ : Type u`. No binder or instance problems were found:
`Fintype` instances come from `Fintype.ofFinite` under `classical`, and the
`Finite (ConjAct Γ)` instance is supplied by hand.

## Recompile record
* `scratch/psl-index-lean-critic/Aux123.lean` (files 1–3, `import Mathlib` only): `[OK]` in 187 s,
  warnings only.
* `scratch/psl-index-lean-critic/T9copy.lean` (an exact copy of T9 = all four §7 texts plus
  `#print axioms`): `[OK]` in 126 s. Axioms reported:
  `abaissement_impossible` depends on `[propext, Classical.choice, Quot.sound]`.
* Not run: the four files as separate modules (`--olean`). That would write into `.lake/build`,
  which is outside the write scope of this review. Point 2 above and the T9 run together cover
  every difference that compiling them separately could make.
