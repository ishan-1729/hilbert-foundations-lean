# PR 2: linear order and strict ordered ring structures on opposites

Open at: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:mulOpposite-linearOrder?expand=1

After opening, post a comment containing only the line `LLM-generated` to add the label. Topic labels are added automatically from the files changed.

## Title

```text
feat(Algebra/Order): linear order and strict ordered ring structures on opposites
```

## Description

```text
Add `LinearOrder`, `IsOrderedCancelMonoid` / `IsOrderedCancelAddMonoid` and `IsStrictOrderedRing` instances on `αᵐᵒᵖ` and `αᵃᵒᵖ`, the `Max`, `Min` and `Ord` instances they are built from, and the simp lemmas `op_lt_op`, `unop_lt_unop`, `op_sup`, `unop_sup`, `op_inf`, `unop_inf`, `op_compare`, `unop_compare` and the strict versions of `unop_le_one`, `unop_nonneg` etc. (`unop_lt_one`, `op_pos`, ...). Also generalize the existing `IsOrderedMonoid` / `IsOrderedAddMonoid` instances from `PartialOrder` to `Preorder`.

With the existing `Field αᵐᵒᵖ` instance, `αᵐᵒᵖ` is now a linearly ordered field whenever `α` is.

---

Design: the `LinearOrder` is built with `Function.Injective.linearOrder` from pointwise `Max`/`Min`/`Ord` instances (as for `ULift`), not with `LinearOrder.lift'`, so that `max`/`min`/`compare` commute with `op`/`unop` by `rfl` and the `PartialOrder` and `DecidableEq` fields agree with the existing instances at instance-reducible transparency (checked with `with_reducible_and_instances rfl` for both opposites).

The cancellative instances are included because `IsStrictOrderedRing` extends `IsOrderedCancelAddMonoid`. In `Rᵐᵒᵖ` the left and right strict monotonicity of multiplication swap, since `op a * op b = op (b * a)`.

`TwoUniqueProds.of_covariant_left` in `Mathlib/Algebra/Group/UniqueProds/Basic.lean` still builds this order locally with `LinearOrder.lift'`; using the new instance there would need an import of `Mathlib.Algebra.Order.Group.Opposite`, which the directory import check does not allow for that file, so it is left unchanged.

The additive names of the new `< 1` lemmas are given explicitly (`unop_lt_zero`, `unop_pos`, `op_lt_zero`, `op_pos`) because the default `to_additive` names would clash with `AddOpposite.unop_neg`.

AI use: I used Claude Code (Anthropic) to draft these instances and lemmas and to check them against mathlib's conventions; an initial version used `LinearOrder.lift'` and was changed to the construction above after checking the instance diamonds. I reviewed every line and can explain each choice. Checked locally: the changed modules and `Mathlib.Algebra.Group.UniqueProds.Basic` and `Mathlib.Algebra.Order.Star.Basic` build, `lake exe lint-style` passes, and the diamond and instance-synthesis tests described above.
```
