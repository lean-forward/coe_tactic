/-
Normalizing coercions in arithmetic expressions
-/

import tactic.basic

namespace tactic

meta def mk_instance_bis (e : expr) : tactic expr :=
    try_for 1000 (mk_instance e)

end tactic


namespace norm_coe
open tactic

meta def is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := (expr.is_eq e).is_some

meta def flip_equation : expr → expr
| (expr.pi n bi d b)           := expr.pi n bi d (flip_equation b)
| (expr.app (expr.app op x) y) := expr.app (expr.app op y) x
| e                            := e

meta def mk_local_lams_whnf : expr → tactic (list expr × expr) | e := do
(expr.lam n bi d b) ← whnf e | return ([], e),
p ← mk_local' n bi d,
(ps, r) ← mk_local_lams_whnf (expr.instantiate_var b p),
return ((p :: ps), r)

meta def lam_from_locals : expr → list expr → expr
| e ((expr.local_const n m bi t)::locals) :=
    let e' := lam_from_locals e locals in
    expr.lam m bi t (e'.abstract_local n)
| e _ := e

private meta def new_name : name → name
| name.anonymous        := name.mk_string "norm_coe" name.anonymous
| (name.mk_string s n)  := name.mk_string s (new_name n)
| (name.mk_numeral i n) := name.mk_numeral i (new_name n)

private meta def after_set (decl : name) (prio : ℕ) (pers : bool) : tactic unit :=
do
    (declaration.thm n l ty task_e) ← get_decl decl | failed,
    let new_n := new_name n,
    (do
        guard (is_equation ty),
        let new_ty := flip_equation ty,
        let e := task_e.get,

        (locals, e') ← mk_local_lams_whnf e,
        e'' ← mk_eq_symm e',
        let new_e := expr.lambdas locals e'',

        let task_new_e := task.pure new_e,
        add_decl (declaration.thm new_n l new_ty task_new_e)
    ) <|> add_decl (declaration.thm new_n l ty task_e)

private meta def mk_cache : list name → tactic simp_lemmas :=
monad.foldl (λ s, s.add_simp ∘ new_name) simp_lemmas.mk

@[user_attribute]
meta def norm_coe_attr : user_attribute simp_lemmas :=
{
    name      := `norm_coe,
    descr     := "attribute for coercion normalization",
    after_set := some after_set,
    cache_cfg := {
        mk_cache     := mk_cache,
        dependencies := [],
    }
}

@[user_attribute]
meta def simp_coe_attr : user_attribute simp_lemmas :=
{
    name      := `simp_coe,
    descr     := "attribute for coercion simplification",
    cache_cfg := {
        mk_cache     := monad.foldl simp_lemmas.add_simp simp_lemmas.mk,
        dependencies := [],
    }
}

--meta def aux2 (e : expr) : tactic (expr × expr) :=
meta def aux2 : expr → tactic (expr × expr)
| e@(expr.app (expr.app op x) y) :=
do
    `(@coe %%α %%δ %%coe1 %%xx) ← return x | failed,
    `(@coe %%β %%γ %%coe2 %%yy) ← return y | failed,
    is_def_eq δ γ,

    (do
        is_def_eq α β,
        pr ← mk_eq_refl e,
        return (e, pr)
    ) <|> (do
        coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance_bis,
        new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
        let new_e := expr.app (expr.app op new_x) y,

        s ← simp_coe_attr.get_cache,
        (x', eq_x) ← s.rewrite new_x,
        eq_x ← mk_eq_symm eq_x,

        pr ← mk_congr_arg op eq_x,
        pr ← mk_congr_fun pr y,
        return (new_e, pr)
    ) <|> (do
        coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance_bis,
        new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
        let new_e := expr.app (expr.app op x) new_y,

        s ← simp_coe_attr.get_cache,
        (y', eq_y) ← s.rewrite new_y,
        eq_y ← mk_eq_symm eq_y,

        pr ← mk_congr_arg (expr.app op x) eq_y,
        return (new_e, pr)
    ) <|> (do
        pr ← mk_eq_refl e,
        return (e, pr)
    )
| _ := failed

meta def aux1 (e : expr) : tactic (expr × expr) :=
do
    (tmp_e, pr1) ← aux2 e <|> prod.mk e <$> mk_eq_refl e,

    ty ← infer_type e,
    let r := match ty with
    | (expr.sort zero) := `iff
    | _                := `eq
    end,

    s ← norm_coe_attr.get_cache,
    (new_e, pr2) ← s.rewrite tmp_e failed r,

    pr2 ← match r with
    |`iff := mk_app `propext [pr2]
    |_    := return pr2
    end,

    pr ← mk_eq_trans pr1 pr2,
    return (new_e, pr)

meta def derive1 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
    (new_e, pr) ← aux1 e,
    return ((), new_e, pr)

meta def derive (e : expr) : tactic (expr × expr) :=
do
    ((), new_e, pr) ← simplify_bottom_up () derive1 e,
    return (new_e, pr)

end norm_coe


namespace tactic.interactive
open tactic interactive interactive.types
open norm_coe

meta def norm_coe1 (loc : parse location) : tactic unit :=
do
    ns ← loc.get_locals,
    tt ← replace_at derive ns loc.include_goal
        | fail "norm_coe failed to simplify",
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction

meta def simp_coe1 (loc : parse location) : tactic unit :=
do
    s ← simp_coe_attr.get_cache,
    ns ← loc.get_locals,
    tt ← replace_at (simplify s []) ns loc.include_goal
        | fail "simp_coe failed to simplify",
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction

end tactic.interactive