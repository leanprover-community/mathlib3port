prelude
import Leanbin.Init.Meta.Tactic
import Leanbin.Init.Meta.MatchTactic
import Leanbin.Init.Meta.MkDecEqInstance
import Leanbin.Init.Data.List.Instances
import Mathbin.Logic.Relator

open Tactic Expr List Monadₓ

namespace Transfer

private unsafe structure rel_data where
  in_type : expr
  out_type : expr
  relation : expr

unsafe instance has_to_tactic_format_rel_data : has_to_tactic_format rel_data :=
  ⟨fun r => do
    let R ← pp r.relation
    let α ← pp r.in_type
    let β ← pp r.out_type
    return f! "({R }: rel ({α }) ({β}))"⟩

private unsafe structure rule_data where
  pr : expr
  uparams : List Name
  params : List (expr × Bool)
  uargs : List Name
  args : List (expr × rel_data)
  pat : pattern
  output : expr

unsafe instance has_to_tactic_format_rule_data : has_to_tactic_format rule_data :=
  ⟨fun r => do
    let pr ← pp r.pr
    let up ← pp r.uparams
    let mp ← pp r.params
    let ua ← pp r.uargs
    let ma ← pp r.args
    let pat ← pp r.pat.target
    let output ← pp r.output
    return f! "\{ ⟨{pat }⟩ pr: {pr } → {output }, {up } {mp } {ua } {ma} }}"⟩

private unsafe def get_lift_fun : expr → tactic (List rel_data × expr)
  | e =>
    (do
        guardb (is_constant_of (get_app_fn e) `` Relator.LiftFun)
        let [α, β, γ, δ, R, S] ← return <| get_app_args e
        let (ps, r) ← get_lift_fun S
        return (rel_data.mk α β R :: ps, r)) <|>
      return ([], e)

private unsafe def mark_occurences (e : expr) : List expr → List (expr × Bool)
  | [] => []
  | h :: t =>
    let xs := mark_occurences t
    (h, occurs h e || any xs fun ⟨e, oc⟩ => oc && occurs h e) :: xs

private unsafe def analyse_rule (u' : List Name) (pr : expr) : tactic rule_data := do
  let t ← infer_type pr
  let (params, app (app r f) g) ← mk_local_pis t
  let (arg_rels, R) ← get_lift_fun r
  let args ←
    (enum arg_rels).mmap fun ⟨n, a⟩ => Prod.mk <$> mk_local_def (mkSimpleName ("a_" ++ reprₓ n)) a.in_type <*> pure a
  let a_vars ← return <| Prod.fst <$> args
  let p ← head_beta (app_of_list f a_vars)
  let p_data ← return <| mark_occurences (app R p) params
  let p_vars ← return <| List.map Prod.fst (p_data.filter fun x => ↑x.2)
  let u ← return <| collect_univ_params (app R p) ∩ u'
  let pat ← mk_pattern (level.param <$> u) (p_vars ++ a_vars) (app R p) (level.param <$> u) (p_vars ++ a_vars)
  return <| rule_data.mk pr (u'.remove_all u) p_data u args pat g

unsafe def analyse_decls : List Name → tactic (List rule_data) :=
  mmap fun n => do
    let d ← get_decl n
    let c ← return d.univ_params.length
    let ls ← (repeat () c).mmap fun _ => mk_fresh_name
    analyse_rule ls (const n (ls.map level.param))

private unsafe def split_params_args : List (expr × Bool) → List expr → List (expr × Option expr) × List expr
  | (lc, tt) :: ps, e :: es =>
    let (ps', es') := split_params_args ps es
    ((lc, some e) :: ps', es')
  | (lc, ff) :: ps, es =>
    let (ps', es') := split_params_args ps es
    ((lc, none) :: ps', es')
  | _, es => ([], es)

private unsafe def param_substitutions (ctxt : List expr) :
    List (expr × Option expr) → tactic (List (Name × expr) × List expr)
  | (local_const n _ bi t, s) :: ps => do
    let (e, m) ←
      match s with
        | some e => return (e, [])
        | none =>
          let ctxt' := List.filterₓ (fun v => occurs v t) ctxt
          let ty := pis ctxt' t
          if bi = BinderInfo.inst_implicit then do
            guardₓ (bi = BinderInfo.inst_implicit)
            let e ← instantiate_mvars ty >>= mk_instance
            return (e, [])
          else do
            let mv ← mk_meta_var ty
            return (app_of_list mv ctxt', [mv])
    let sb ← return <| instantiate_local n e
    let ps ← return <| Prod.map sb ((· <$> ·) sb) <$> ps
    let (ms, vs) ← param_substitutions ps
    return ((n, e) :: ms, m ++ vs)
  | _ => return ([], [])

unsafe def compute_transfer : List rule_data → List expr → expr → tactic (expr × expr × List expr)
  | rds, ctxt, e => do
    let (i, ps, args, ms, rd) ←
      first
            (rds.map fun rd => do
              let (l, m) ← match_pattern rd.pat e semireducible
              let level_map ← rd.uparams.mmap fun l => Prod.mk l <$> mk_meta_univ
              let inst_univ ← return fun e => instantiate_univ_params e (level_map ++ zip rd.uargs l)
              let (ps, args) ← return <| split_params_args (rd.params.map (Prod.map inst_univ id)) m
              let (ps, ms) ← param_substitutions ctxt ps
              return (instantiate_locals ps ∘ inst_univ, ps, args, ms, rd)) <|>
          do
          trace e
          fail "no matching rule"
    let (bs, hs, mss) ←
      ((zip rd.args args).mmap fun ⟨⟨_, d⟩, e⟩ => do
            let (args, r) ← get_lift_fun (i d.relation)
            let ((a_vars, b_vars), (R_vars, bnds)) ←
              ((enum args).mmap fun ⟨n, arg⟩ => do
                    let a ← mk_local_def (s! "a{n}") arg.in_type
                    let b ← mk_local_def (s! "b{n}") arg.out_type
                    let R ← mk_local_def (s! "R{n}") (arg.relation a b)
                    return ((a, b), (R, [a, b, R]))) >>=
                  return ∘ Prod.map unzip unzip ∘ unzip
            let rds' ← R_vars.mmap (analyse_rule [])
            let a ← return <| i e
            let a' ← head_beta (app_of_list a a_vars)
            let (b, pr, ms) ← compute_transfer (rds ++ rds') (ctxt ++ a_vars) (app r a')
            let b' ← head_eta (lambdas b_vars b)
            return (b', [a, b', lambdas (List.join bnds) pr], ms)) >>=
          return ∘ Prod.map id unzip ∘ unzip
    let b ← head_beta (app_of_list (i rd.output) bs)
    let pr ← return <| app_of_list (i rd.pr) (Prod.snd <$> ps ++ List.join hs)
    return (b, pr, ms ++ mss.join)

end Transfer

open Transfer

unsafe def tactic.transfer (ds : List Name) : tactic Unit := do
  let rds ← analyse_decls ds
  let tgt ← target
  guardₓ ¬tgt.has_meta_var <|> fail "Target contains (universe) meta variables. This is not supported by transfer."
  let (new_tgt, pr, ms) ← compute_transfer rds [] ((const `iff [] : expr) tgt)
  let new_pr ← mk_meta_var new_tgt
  exact ((const `iff.mpr [] : expr) tgt new_tgt pr new_pr)
  let ms ← ms.mmap fun m => get_assignment m >> return [] <|> return [m]
  let gs ← get_goals
  set_goals (ms.join ++ new_pr :: gs)

