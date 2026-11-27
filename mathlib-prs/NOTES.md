# Two small mathlib PRs: notes for the submitter

Both branches are in `D:\Projects\mathlib4`, a clone of `leanprover-community/mathlib4` master at commit 643371581c (25 Nov 2026). Each branch is one commit on top of that commit. Nothing has been pushed or opened yet.

| Branch | Files | Size |
|---|---|---|
| `analyticAt-sqrt` | `Mathlib/Analysis/SpecialFunctions/Sqrt.lean` | +44 / −3 |
| `mulOpposite-linearOrder` | `Mathlib/Algebra/Order/Group/Opposite.lean`, `Mathlib/Algebra/Order/Ring/Opposite.lean` | +57 / −3 |

See the diffs with `git diff master...<branch>` from inside `D:\Projects\mathlib4`.

## Mathlib's AI policy

From the "Use of AI" section of https://leanprover-community.github.io/contribute/index.html (mid-2026):

- **Disclose in the PR description** which tools you used and how.
- **Add the `LLM-generated` label** when a substantial amount of the code is LLM-generated, by posting a comment containing `LLM-generated`. Both PRs qualify.
- **Understand everything** and be able to justify every design decision to reviewers without an AI.
- **Write your own GitHub and Zulip comments.** Using an LLM to write them is not allowed. So write the PR descriptions and every review reply yourself. The facts below are notes to write from, not text to paste.
- **Low-effort LLM PRs are closed without comment**, especially from authors who haven't engaged with the community. Repeated low-effort PRs can lead to a ban.

Suggested order:

1. Read this file and the diffs until you could defend each line.
2. Join the Lean Zulip and introduce yourself; add your GitHub username to your Zulip profile.
3. Open the sqrt PR first, because it is the simplest.

---

## PR 1: `Real.sqrt` is analytic away from 0

**Suggested title:** `feat(Analysis/SpecialFunctions/Sqrt): Real.sqrt is analytic away from 0`

**What it adds.** In namespace `Real`:
- `analyticAt_sqrt (hx : x ≠ 0) : AnalyticAt ℝ (√·) x`, tagged `@[fun_prop]`;
- `analyticWithinAt_sqrt (hx : x ≠ 0) : AnalyticWithinAt ℝ (√·) s x`;
- `analyticOnNhd_sqrt : AnalyticOnNhd ℝ (√·) {0}ᶜ`;
- `analyticOn_sqrt : AnalyticOn ℝ (√·) {0}ᶜ`.

In a new `section Analytic`, the composition ("dot notation") lemmas for `f : E → ℝ` on a real normed space `E`:
- `AnalyticAt.sqrt` and `AnalyticOnNhd.sqrt`, both tagged `@[fun_prop]`;
- `AnalyticWithinAt.sqrt` and `AnalyticOn.sqrt`.

**Why it is true.**
- The existing `contDiffAt_sqrt` gives `ContDiffAt ℝ n (√·) x` for every `n : WithTop ℕ∞`, including `n = ω`.
- `ContDiffAt.analyticAt` turns `ContDiffAt ℝ ω` into `AnalyticAt`.
- Everything else is composition: `AnalyticAt.comp`, `AnalyticAt.comp_analyticWithinAt`, and `AnalyticOnNhd.analyticOn`.

**Why `x ≠ 0` and not `0 < x`.**
- For `x < 0`, `√` is locally the constant 0, so it is analytic there too.
- At 0 it is not even differentiable, so `x ≠ 0` is exactly the right condition.
- It matches `contDiffAt_sqrt`, and `{0}ᶜ` is the set used by `contDiffOn_inv` and `differentiableOn_log`.

**Why these attributes.**
- `AnalyticAt` and `AnalyticOnNhd` are `fun_prop` predicates, so `analyticAt_sqrt`, `AnalyticAt.sqrt` and `AnalyticOnNhd.sqrt` get `@[fun_prop]`.
- `AnalyticWithinAt` and `AnalyticOn` are not `fun_prop` predicates; tagging those lemmas would make `fun_prop` complain.

**Precedent.** `Real.analyticAt_arsinh` (Arsinh.lean) and `Real.analyticAt_log` / `AnalyticAt.log` (SpecialFunctions/Complex/Analytic.lean) have the same shapes.

**Checked locally.**
- `lake build Mathlib.Analysis.SpecialFunctions.Sqrt` succeeds with no warnings.
- `lake exe lint-style` passes.
- In a scratch file, `fun_prop` proves:
  - `AnalyticAt ℝ (fun y ↦ √(y^2+1)) x`, with discharger `positivity`;
  - `AnalyticOnNhd ℝ (fun x ↦ √(x^2+1)) univ`;
  - `AnalyticOnNhd ℝ (fun x ↦ √(f x)) s` from `hf : AnalyticOnNhd ℝ f s` and `f ≠ 0` on `s`.
- I searched master for an existing analytic lemma for `sqrt` or `rpow` and found none.

**Questions a reviewer may ask.**
- *Why not an iff (`AnalyticAt ℝ (√·) x ↔ x ≠ 0`)?* Mathlib has no lemma saying `√` is not differentiable at 0, so that needs its own PR.
- *Why `(√·)` and not `Real.sqrt`?* The rest of the file states things with `(√·)`.

---

## PR 2: more order structure on `MulOpposite` / `AddOpposite`

**Suggested title:** `feat(Algebra/Order): linear order and strict ordered ring structures on opposites`

**What it adds.** For `αᵐᵒᵖ` (each also for `αᵃᵒᵖ` through `@[to_additive]`, unless noted otherwise):
- **Strict order lemmas.** `unop_lt_unop` and `op_lt_op` (simp): the `<` versions of the existing `unop_le_unop` and `op_le_op`.
- **`Max`, `Min` and `Ord` instances.** These are defined pointwise: `max a b := op (a.unop ⊔ b.unop)`, and similarly for the others. They come with the simp lemmas `op_sup`, `unop_sup`, `op_inf`, `unop_inf`, `op_compare` and `unop_compare`, all proved by `rfl`.
- **`LinearOrder` instance.** Built with `unop_injective.linearOrder`, reusing the existing `≤`, `<`, `DecidableEq` and the new `Max`/`Min`/`Ord`.
- **Ordered cancellative monoid instances.** `IsOrderedCancelMonoid` (for `αᵐᵒᵖ` and `αᵃᵒᵖ`) and `IsOrderedCancelAddMonoid` (for `αᵐᵒᵖ`).
- **Strict lemmas next to the existing ones.**
  - `unop_lt_one`, `one_lt_unop`, `op_lt_one`, `one_lt_op` (simp), next to the existing `unop_le_one` etc.
  - Their additive versions are named explicitly: `unop_lt_zero`, `unop_pos`, `op_lt_zero`, `op_pos`. The default `to_additive` names would clash with the existing `AddOpposite.unop_neg`.
  - The same four `< 0` lemmas for `αᵐᵒᵖ` with its additive structure, and the `< 1` lemmas for `αᵃᵒᵖ`.
- **Generalized existing instances.** `IsOrderedMonoid` and `IsOrderedAddMonoid` now need only `[Preorder α]`, not `[PartialOrder α]`, and so do the new cancellative instances. This matches the `OrderDual` and `Prod` instances.
- **Strict ordered rings.** In `Ring/Opposite.lean`: `IsStrictOrderedRing Rᵐᵒᵖ` and `IsStrictOrderedRing Rᵃᵒᵖ`, next to the existing `IsOrderedRing` instances.

**Why it is right.**
- In `Rᵐᵒᵖ`, `a * b = op (b.unop * a.unop)`. So "multiplying on the left by a positive element is strictly monotone" in `Rᵐᵒᵖ` is "multiplying on the right" in `R`. That is why the `MulOpposite` ring instance swaps `mul_lt_mul_of_pos_left` and `_right`, and the `AddOpposite` one (where multiplication is unchanged) does not.
- The cancellative instances have to be in the same PR, because `IsStrictOrderedRing` extends `IsOrderedCancelAddMonoid`.
- Together with the existing `Field αᵐᵒᵖ` instance, `αᵐᵒᵖ` is now a linearly ordered field whenever `α` is one.

**The design point a reviewer will look at: instance diamonds.**
- **Why not `LinearOrder.lift'`.** The quick way to define the linear order would generate its own `max`, `min` and `DecidableEq`. Those would not be reducibly equal to `MulOpposite.instDecidableEq`, and `op (max a b) = max (op a) (op b)` would not hold by `rfl`. `Mathlib/Order/Basic.lean` warns against exactly this.
- **What the branch does instead.** It defines `Max`/`Min`/`Ord` first and then uses `Function.Injective.linearOrder`, which takes the existing instances as arguments. This is the same pattern as `ULift` in `Mathlib/Order/Lattice.lean`.
- **Checked in Lean**, with `with_reducible_and_instances rfl`, for both `ᵐᵒᵖ` and `ᵃᵒᵖ`:
  - the old `PartialOrder` equals `LinearOrder.toPartialOrder`;
  - `instDecidableEq` equals `LinearOrder.toDecidableEq`;
  - the new `Max`/`Ord` equal the ones inside the linear order.

**Checked locally.**
- These modules build with no warnings: `Mathlib.Algebra.Order.Group.Opposite`, `Mathlib.Algebra.Order.Ring.Opposite`, and the downstream `Mathlib.Algebra.Group.UniqueProds.Basic` and `Mathlib.Algebra.Order.Star.Basic`.
- `lake exe lint-style` passes.
- In a scratch file:
  - the diamonds above;
  - `inferInstance` finds every new instance;
  - `mul_pos` and `inv_pos` work in `Rᵐᵒᵖ` for a linearly ordered field `R`;
  - `simp` proves `op a < 1 ↔ a < 1` and `0 < op a ↔ 0 < a`.
- Only these modules were built locally, not the whole of mathlib. Mathlib's CI builds everything; watch it for breakage elsewhere.

**Questions a reviewer may ask.**
- *`Mathlib/Algebra/Group/UniqueProds/Basic.lean` line ~614 builds this linear order by hand. Why not use the new instance there?*
  - I tried. That file is not allowed to import order theory: mathlib's directory-import check fails with "Declaration IsOrderedMonoid is not allowed to be imported by this file". So it is left alone.
  - Mention this in the PR description.
- *Lattice instances (`SemilatticeSup` etc.)?* A natural follow-up, not done here.
- *The generated name `AddOpposite.instIsOrderedAddCancelMonoid` differs from `MulOpposite.instIsOrderedCancelAddMonoid`.* This is a known `to_additive` naming quirk, and `Prod` and `OrderDual` have the same mismatch.

---

## Before pushing

- **Commit e-mail.** The commits are authored with your personal Gmail address, which becomes public once pushed. Your GitHub no-reply address is `60109638+ishan-1729@users.noreply.github.com`. To switch the two commits to it, inside `D:\Projects\mathlib4` run:
  ```
  git config user.email 60109638+ishan-1729@users.noreply.github.com
  git switch analyticAt-sqrt && git commit --amend --reset-author --no-edit
  git switch mulOpposite-linearOrder && git commit --amend --reset-author --no-edit
  ```
- **Fork and push:**
  ```
  gh repo fork leanprover-community/mathlib4 --remote --remote-name fork
  git push fork analyticAt-sqrt mulOpposite-linearOrder
  ```
  Then open each PR against `leanprover-community/mathlib4` `master`, with a description you write yourself. It must include the AI disclosure: you used Claude Code to draft the code and to check it against mathlib's conventions, and you reviewed and understand every line. Then comment `LLM-generated` to add the label.
