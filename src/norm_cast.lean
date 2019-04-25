/-
Normalizing casts in arithmetic expressions
-/

import tactic.basic tactic.interactive tactic.converter.interactive

namespace tactic

meta def mk_instance_bis (e : expr) : tactic expr :=
    try_for 1000 (mk_instance e)

end tactic


namespace norm_cast
open tactic

private meta def new_name : name → name
| name.anonymous        := name.mk_string "norm_cast" name.anonymous
| (name.mk_string s n)  := name.mk_string s (new_name n)
| (name.mk_numeral i n) := name.mk_numeral i (new_name n)

private meta def flip_equation : expr → tactic (expr × (expr → expr))
| (expr.pi n bi d b) := do
    (ty, f) ← flip_equation $ expr.instantiate_var b (expr.local_const n n bi d),
    return $ (
        expr.pi n bi d $ expr.abstract_local ty n,
        λ e, expr.lam n bi d $ expr.abstract_local ( f $ e (expr.local_const n n bi d) ) n
    )
| ty := do
    `(%%a = %%b) ← return ty | failure,
    α ← infer_type a,
    symm ← to_expr ``(@eq.symm %%α %%a %%b),
    new_ty ← to_expr ``(%%b = %%a),
    return (new_ty, symm)

private meta def after_set (decl : name) (prio : ℕ) (pers : bool) : tactic unit :=
do
    (declaration.thm n l ty task_e) ← get_decl decl | failed,
    let new_n := new_name n,
    ( do
        (new_ty, f) ← flip_equation ty,
        trace new_ty, -- debug
        let task_new_e := task.map f task_e,
        add_decl (declaration.thm new_n l new_ty task_new_e)
    ) <|> ( do
        trace ty, -- debug
        add_decl (declaration.thm new_n l ty task_e)
    )

private meta def mk_cache : list name → tactic simp_lemmas :=
monad.foldl (λ s, s.add_simp ∘ new_name) simp_lemmas.mk

@[user_attribute]
meta def norm_cast_attr : user_attribute simp_lemmas :=
{
    name      := `norm_cast,
    descr     := "attribute for cast normalization",
    after_set := some after_set,
    cache_cfg := {
        mk_cache     := mk_cache,
        dependencies := [],
    }
}

@[user_attribute]
meta def simp_cast_attr : user_attribute simp_lemmas :=
{
    name      := `simp_cast,
    descr     := "attribute for cast simplification",
    after_set := some (λ n _ _, get_decl n >>= trace ∘ declaration.type), -- debug
    cache_cfg := {
        mk_cache     := monad.foldl simp_lemmas.add_simp simp_lemmas.mk,
        dependencies := [],
    }
}

private meta def aux1 (e new_e : expr) : tactic expr :=
do
    s ← simp_cast_attr.get_cache,
    (e', pr) ← s.rewrite new_e,
    is_def_eq e e',
    mk_eq_symm pr

private meta def heur (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
match e with
| (expr.app (expr.app op x) y) :=
do
    `(@coe %%α %%δ %%coe1 %%xx) ← return x,
    `(@coe %%β %%γ %%coe2 %%yy) ← return y,
    is_def_eq δ γ,

    b ← (is_def_eq α β >> return ff) <|> return tt,
    guard b,

    (do
        coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance_bis,
        new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
        let new_e := expr.app (expr.app op new_x) y,

        eq_x ← aux1 x new_x,

        pr ← mk_congr_arg op eq_x,
        pr ← mk_congr_fun pr y,
        return ((), new_e, pr)
    ) <|> (do
        coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance_bis,
        new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
        let new_e := expr.app (expr.app op x) new_y,

        eq_y ← aux1 y new_y,

        pr ← mk_congr_arg (expr.app op x) eq_y,
        return ((), new_e, pr)
    )
| _ := failed
end

private meta def post (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
    s ← norm_cast_attr.get_cache,
    r ← mcond (is_prop e) (return `iff) (return `eq),

    let prove : tactic unit := do {
        t ← target,
        tactic.interactive.simpa none ff [] [] none
    },
    (new_e, pr) ← s.rewrite e prove r,
    -- (new_e, pr) ← s.rewrite e r,

    pr ← match r with
    |`iff := mk_app `propext [pr]
    |_    := return pr
    end,

    return ((), new_e, pr)

private meta def aux_num (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
match e with
| `(0 : ℕ) := failed
| `(1 : ℕ) := failed
| `(@has_zero.zero %%α %%h) := do
    coe_nat ← to_expr ``(has_lift_t ℕ %%α) >>= mk_instance_bis,
    new_e ← to_expr ``(@coe ℕ %%α %%coe_nat 0),
    pr ← aux1 e new_e,
    return ((), new_e, pr)
| `(@has_one.one %%α %%h) := do
    coe_nat ← to_expr ``(has_lift_t ℕ %%α) >>= mk_instance_bis,
    new_e ← to_expr ``(@coe ℕ %%α %%coe_nat 1),
    pr ← aux1 e new_e,
    return ((), new_e, pr)
| _ := failed
end

meta def derive (cfg : simp_config := {}) (e : expr) : tactic (expr × expr) :=
do
    ((), new_e, pr1) ← ext_simplify_core () {fail_if_unchanged := ff} simp_lemmas.mk (λ _, failed)
        (λ a _ _ _ e, failed)
        (λ a _ _ _ e, do (new_a, new_e, pr) ← aux_num a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
        `eq e,

    ((), new_e, pr2) ← ext_simplify_core () {fail_if_unchanged := ff, ..cfg} simp_lemmas.mk (λ _, failed)
        (λ a _ _ _ e, failed)
        (λ a _ _ _ e, do (new_a, new_e, pr) ← post a e <|> heur a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
        `eq new_e,

    s ← simp_cast_attr.get_cache,
    (new_e, pr3) ← simplify s [] new_e {fail_if_unchanged := ff},

    guard (¬ new_e =ₐ e),
    pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,

    return (new_e, pr)

end norm_cast


namespace tactic
open tactic expr
open norm_cast

private meta def aux_mod_cast (e : expr) : tactic expr :=
match e with
| local_const _ lc _ _ := do
    e ← get_local lc,
    replace_at (derive {}) [e] tt,
    get_local lc
| e := do
    t ← infer_type e,
    e ← assertv `this t e,
    replace_at (derive {}) [e] tt,
    get_local `this
end -- TODO: error message

meta def exact_mod_cast (e : expr) : tactic unit :=
(aux_mod_cast e >>= exact) <|> fail "exact_mod_cast failed"

meta def apply_mod_cast (e : expr) : tactic (list (name × expr)) :=
(aux_mod_cast e >>= apply) <|> fail "apply_mod_cast failed"
-- TODO: normalize the new goals

meta def assumption_mod_cast : tactic unit :=
do {
    let cfg : simp_config := {
        fail_if_unchanged := ff,
        canonize_instances := ff,
        canonize_proofs := ff,
        proj := ff
    },
    ctx ← local_context,
    _ ← replace_at (derive cfg) ctx tt,
    assumption
} <|> fail "assumption_mod_cast failed"

end tactic


namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast

local postfix `?`:9001 := optional

meta def assumption_mod_cast : tactic unit :=
tactic.assumption_mod_cast

meta def norm_cast (loc : parse location) : tactic unit :=
do
    ns ← loc.get_locals,
    tt ← replace_at (derive {}) ns loc.include_goal
        | fail "norm_cast failed to simplify",
    when loc.include_goal $ try tactic.reflexivity,
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction

/-
meta def simp_cast1 (loc : parse location) : tactic unit :=
do
    s ← simp_cast_attr.get_cache,
    ns ← loc.get_locals,
    tt ← replace_at (simplify s []) ns loc.include_goal
        | fail "simp_cast failed to simplify",
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction
-/

meta def rw_mod_cast (rs : parse rw_rules) (loc : parse location) : tactic unit :=
do
    let cfg_norm : simp_config := {},
    let cfg_rw : rewrite_cfg := {},
    ns ← loc.get_locals,
    _ ← replace_at (derive cfg_norm) ns loc.include_goal,
    monad.mapm' (λ r, do
        rw ⟨[r], none⟩ loc cfg_rw,
        _ ← replace_at (derive cfg_norm) ns loc.include_goal,
        skip
    ) rs.rules

meta def exact_mod_cast (e : parse texpr) : tactic unit :=
do
    e ← i_to_expr e <|> do {
        ty ← target,
        e ← i_to_expr_strict ``(%%e : %%ty),
        pty ← pp ty, ptgt ← pp e,
        fail ("exact_mod_cast failed, expression type not directly " ++
        "inferrable. Try:\n\nexact_mod_cast ...\nshow " ++
        to_fmt pty ++ ",\nfrom " ++ ptgt : format)
    },
    tactic.exact_mod_cast e

meta def apply_mod_cast (e : parse texpr) : tactic unit :=
do
    e ← i_to_expr_for_apply e,
    concat_tags $ tactic.apply_mod_cast e

end tactic.interactive

namespace conv.interactive
open conv tactic tactic.interactive interactive interactive.types
open norm_cast (derive)

meta def norm_cast : conv unit := replace_lhs (derive {})

end conv.interactive