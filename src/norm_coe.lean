/-
Normalizing coercions in arithmetic expressions
-/

import tactic.basic

namespace tactic

/-
instances such as has_lift_t ℤ ℕ time out instead of failing
we assume that the instances should be solved instantly
and we use mk_instance_bis to work around the timeout problem
-/
meta def mk_instance_bis (x : expr) : tactic expr :=
    try_for 1000 (mk_instance x)

end tactic

open tactic

namespace norm_coe

meta def eq_lemma (α β : expr) : tactic expr :=
do
    h ← to_expr ``(∀ (x y : %%α), (↑x : %%β) = ↑y = (x = y)),
    ((), eh) ← solve_aux h `[simp, done],
    pr ← instantiate_mvars eh,
    return pr

meta def aux_eq (x y : expr) : tactic (expr × option expr) :=
match x, y with
| `(@coe %%α %%δ1 %%coe_1 %%a), `(@coe %%β %%δ2 %%coe_2 %%b) :=
do
    is_def_eq δ1 δ2,
    let δ := δ1,
    (do
        -- α = β
        is_def_eq α β,

        let new_x := a,
        let new_y := b,
        new_e ← to_expr ``(%%new_x = %%new_y),

        h ← eq_lemma α δ,
        let pr := expr.app (expr.app h a) b,

        return (new_e, some pr)

    ) <|> ( do
        -- has_lift_t α β
        coe_a_b ← to_expr ``(has_lift_t %%α %%β) >>= mk_instance_bis,

        new_x ← to_expr ``(@coe %%α %%β %%coe_a_b %%a),
        let new_y := b,
        new_e ← to_expr ``(%%new_x = %%new_y),

        h ← eq_lemma β δ,
        let bar := expr.app (expr.app h new_x) new_y,

        t ← to_expr ``(%%x = %%y = (↑%%new_x = (↑%%new_y : %%δ))),
        ((), foo) ← solve_aux t `[simp, done],
        foo ← instantiate_mvars foo,

        pr ← mk_eq_trans foo bar,
        return (new_e, some pr)

    ) <|> ( do
        -- has_lift_t β α
        coe_b_a ← to_expr ``(has_lift_t %%β %%α) >>= mk_instance_bis,

        let new_x := a,
        new_y ← to_expr ``(@coe %%β %%α %%coe_b_a %%b),
        new_e ← to_expr ``(%%new_x = %%new_y),
        
        h ← eq_lemma α δ,
        let bar := expr.app (expr.app h new_x) new_y,

        t ← to_expr ``(%%x = %%y = ((↑%%new_x : %%δ) = ↑%%new_y)),
        ((), foo) ← solve_aux t `[simp, done],
        foo ← instantiate_mvars foo,

        pr ← mk_eq_trans foo bar,
        return (new_e, some pr)

    ) <|> ( do
        new_e ← to_expr ``(%%x = %%y),
        return (new_e, none)
    )
| new_x, new_y :=
do
    new_e ← to_expr ``(%%new_x = %%new_y),
    return (new_e, none)
end

meta def aux_addition (x y : expr) : tactic (expr × option expr) :=
match x, y with
| `(@coe %%α %%δ1 %%coe_1 %%a), `(@coe %%β %%δ2 %%coe_2 %%b) :=
do
    is_def_eq δ1 δ2,
    let δ := δ1,
    e ← to_expr ``(%%x + %%y),
    (do
        -- α = β
        is_def_eq α β,

        let new_x := a,
        let new_y := b,
        new_e ← to_expr ``(↑(%%new_x + %%new_y) : %%δ),

        h ← to_expr ``(%%e = %%new_e),
        ((), pr) ← solve_aux h `[simp, done],
        pr ← instantiate_mvars pr,

        return (new_e, some pr)

    ) <|> ( do
        -- has_lift_t α β
        coe_a_b ← to_expr ``(has_lift_t %%α %%β) >>= mk_instance_bis,

        new_x ← to_expr ``(@coe %%α %%β %%coe_a_b %%a),
        let new_y := b,
        new_e ← to_expr ``(↑(%%new_x + %%new_y) : %%δ),

        h ← to_expr ``(%%e = %%new_e),
        ((), pr) ← solve_aux h `[simp, done],
        pr ← instantiate_mvars pr,

        return (new_e, some pr)

    ) <|> ( do
        -- has_lift_t β α
        coe_b_a ← to_expr ``(has_lift_t %%β %%α) >>= mk_instance_bis,

        let new_x := a,
        new_y ← to_expr ``(@coe %%β %%α %%coe_b_a %%b),
        new_e ← to_expr ``(@coe %%α %%δ %%coe_1 (%%new_x + %%new_y)),

        h ← to_expr ``(%%e = %%new_e),
        ((), pr) ← solve_aux h `[simp, done],
        pr ← instantiate_mvars pr,

        return (new_e, some pr)

    ) <|> ( do
        new_e ← to_expr ``(%%x + %%y),
        return (new_e, none)
    )
| _, _ :=
do
    new_e ← to_expr ``(%%x + %%y),
    return (new_e, none)
end

meta def derive1 (f : expr → tactic (expr × expr)) : expr → tactic (expr × option expr)
| `(%%a + %%b) := aux_addition a b
| `(%%a = %%b) := aux_eq a b
| a            := return (a, none)

/-
the core tactic is the same as for norm_num
-/
meta def derive : expr → tactic (expr × expr) | e :=
do
    e ← instantiate_mvars e,
    (_, e', pr) ←
        ext_simplify_core () {} simp_lemmas.mk (λ _, failed)
            (λ _ _ _ _ _, failed)
            (λ _ _ _ _ e,
            do (new_e, pr) ← derive1 derive e,
                guard (¬ new_e =ₐ e),
                return ((), new_e, pr, tt))
            `eq e,
    return (e', pr)

end norm_coe

namespace tactic.interactive

open norm_coe
open interactive
open interactive.types

/-
the interactive tactics are the same as for norm_num
-/

meta def norm_coe1 (loc : parse location) : tactic unit :=
do
    ns ← loc.get_locals,
    tt ← replace_at derive ns loc.include_goal
        | fail "norm_coe failed to simplify",
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction

meta def norm_coe (hs : parse simp_arg_list) (l : parse location) : tactic unit :=
    repeat1 $ orelse' (norm_coe1 l) $
    simp_core {} (norm_coe1 (loc.ns [none])) ff hs [] l

end tactic.interactive
