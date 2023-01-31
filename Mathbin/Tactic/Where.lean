/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek

! This file was ported from Lean 3 source module tactic.where
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# The `where` command

When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/


open Lean.Parser Tactic

namespace Where

/-- Assigns a priority to each binder for determining the order in which variables are traced. -/
unsafe def binder_priority : BinderInfo → ℕ
  | BinderInfo.implicit => 1
  | BinderInfo.strict_implicit => 2
  | BinderInfo.default => 3
  | BinderInfo.inst_implicit => 4
  | BinderInfo.aux_decl => 5
#align where.binder_priority where.binder_priority

/-- The relation on binder priorities. -/
unsafe def binder_less_important (u v : BinderInfo) : Bool :=
  binder_priority u < binder_priority v
#align where.binder_less_important where.binder_less_important

/-- Selects the elements of the given `list α` which under the image of `p : α → β × γ` have `β`
component equal to `b'`. Returns the `γ` components of the selected elements under the image of `p`,
and the elements of the original `list α` which were not selected. -/
def selectForWhich {α β γ : Type} (p : α → β × γ) [DecidableEq β] (b' : β) :
    List α → List γ × List α
  | [] => ([], [])
  | a :: rest =>
    let (cs, others) := select_for_which rest
    let (b, c) := p a
    if b = b' then (c :: cs, others) else (cs, a :: others)
#align where.select_for_which Where.selectForWhich

/-- Helper function for `collect_by`. -/
private unsafe def collect_by_aux {α β γ : Type} (p : α → β × γ) [DecidableEq β] :
    List β → List α → List (β × List γ)
  | [], [] => []
  | [], _ => undefined_core "didn't find every key entry!"
  | b :: rest, as =>
    let (cs, as) := selectForWhich p b as
    (b, cs) :: collect_by_aux rest as
#align where.collect_by_aux where.collect_by_aux

/-- Returns the elements of `l` under the image of `p`, collecting together elements with the same
`β` component, deleting duplicates. -/
unsafe def collect_by {α β γ : Type} (l : List α) (p : α → β × γ) [DecidableEq β] :
    List (β × List γ) :=
  collect_by_aux p (l.map <| Prod.fst ∘ p).dedup l
#align where.collect_by where.collect_by

/-- Sort the variables by their priority as defined by `where.binder_priority`. -/
unsafe def sort_variable_list (l : List (Name × BinderInfo × expr)) :
    List (expr × BinderInfo × List Name) :=
  let l := collect_by l fun v => (v.2.2, (v.1, v.2.1))
  let l := l.map fun el => (el.1, collect_by el.2 fun v => (v.2, v.1))
  (List.join <| l.map fun e => Prod.mk e.1 <$> e.2).qsort fun v u =>
    binder_less_important v.2.1 u.2.1
#align where.sort_variable_list where.sort_variable_list

/-- Separate out the names of implicit variables (commonly instances with no name). -/
unsafe def collect_implicit_names : List Name → List String × List String
  | [] => ([], [])
  | n :: ns =>
    let n := toString n
    let (ns, ins) := collect_implicit_names ns
    if n.front = '_' then (ns, n :: ins) else (n :: ns, ins)
#align where.collect_implicit_names where.collect_implicit_names

/-- Format an individual variable definition for printing. -/
unsafe def format_variable : expr × BinderInfo × List Name → tactic String
  | (e, bi, ns) => do
    let (l, r) := bi.brackets
    let e ← pp e
    let (ns, ins) := collect_implicit_names ns
    let ns := " ".intercalate <| ns.map toString
    let ns := if ns.length = 0 then [] else [s! "{l }{ns } : {e }{r}"]
    let ins := ins.map fun _ => s! "{l }{e }{r}"
    return <| " ".intercalate <| ns ++ ins
#align where.format_variable where.format_variable

/-- Turn a list of triples of variable names, binder info, and types, into a pretty list. -/
unsafe def compile_variable_list (l : List (Name × BinderInfo × expr)) : tactic String :=
  " ".intercalate <$> (sort_variable_list l).mmap format_variable
#align where.compile_variable_list where.compile_variable_list

/-- Strips the namespace prefix `ns` from `n`. -/
private unsafe def strip_namespace (ns n : Name) : Name :=
  n.replace_prefix ns Name.anonymous
#align where.strip_namespace where.strip_namespace

/-- `get_open_namespaces ns` returns a list of the open namespaces, given that we are currently in
the namespace `ns` (which we do not include). -/
unsafe def get_open_namespaces (ns : Name) : tactic (List Name) := do
  let opens ← List.dedup <$> tactic.open_namespaces
  return <| (opens ns).map <| strip_namespace ns
#align where.get_open_namespaces where.get_open_namespaces

/-- Give a slightly friendlier name for `name.anonymous` in the context of your current namespace.
-/
private unsafe def explain_anonymous_name : Name → String
  | Name.anonymous => "[root namespace]"
  | ns => toString ns
#align where.explain_anonymous_name where.explain_anonymous_name

/-- `#where` output helper which traces the current namespace. -/
unsafe def build_str_namespace (ns : Name) : lean.parser String :=
  return s! "namespace {explain_anonymous_name ns}"
#align where.build_str_namespace where.build_str_namespace

/-- `#where` output helper which traces the open namespaces. -/
unsafe def build_str_open_namespaces (ns : Name) : tactic String := do
  let l ← get_open_namespaces ns
  let str := " ".intercalate <| l.map toString
  if l then return "" else return s! "open {str}"
#align where.build_str_open_namespaces where.build_str_open_namespaces

/-- `#where` output helper which traces the variables. -/
unsafe def build_str_variables : lean.parser String := do
  let l ← get_variables
  let str ← compile_variable_list l
  if l then return "" else return s! "variables {str}"
#align where.build_str_variables where.build_str_variables

/-- `#where` output helper which traces the includes. -/
unsafe def build_str_includes : lean.parser String := do
  let l ← get_included_variables
  let str := " ".intercalate <| l.map fun n => toString n.1
  if l then return "" else return s! "include {str}"
#align where.build_str_includes where.build_str_includes

/-- `#where` output helper which traces the namespace end. -/
unsafe def build_str_end (ns : Name) : tactic String :=
  return s! "end {explain_anonymous_name ns}"
#align where.build_str_end where.build_str_end

/-- `#where` output helper which traces newlines. -/
private unsafe def append_nl (s : String) (n : ℕ) : tactic String :=
  return <| s ++ (List.asString <| (List.range n).map fun _ => '\n')
#align where.append_nl where.append_nl

/-- `#where` output helper which traces lines, adding a newline if nonempty. -/
private unsafe def append_line (s : String) (t : lean.parser String) : lean.parser String := do
  let v ← t
  return <| s ++ v ++ if v = 0 then "" else "\n"
#align where.append_line where.append_line

/-- `#where` output main function. -/
unsafe def build_msg : lean.parser String := do
  let msg := ""
  let ns ← get_current_namespace
  let msg ← append_line msg <| build_str_namespace ns
  let msg ← append_nl msg 1
  let msg ← append_line msg <| build_str_open_namespaces ns
  let msg ← append_line msg <| build_str_variables
  let msg ← append_line msg <| build_str_includes
  let msg ← append_nl msg 3
  let msg ← append_line msg <| build_str_end ns
  return msg
#align where.build_msg where.build_msg

open Interactive

/-- When working in a Lean file with namespaces, parameters, and variables, it can be confusing to
identify what the current "parser context" is. The command `#where` identifies and prints
information about the current location, including the active namespace, open namespaces, and
declared variables.

It is a bug for `#where` to incorrectly report this information (this was not formerly the case);
please file an issue on GitHub if you observe a failure.
-/
@[user_command]
unsafe def where_cmd (_ : parse <| tk "#where") : lean.parser Unit := do
  let msg ← build_msg
  trace msg
#align where.where_cmd where.where_cmd

add_tactic_doc
  { Name := "#where"
    category := DocCategory.cmd
    declNames := [`where.where_cmd]
    tags := ["environment"] }

end Where

