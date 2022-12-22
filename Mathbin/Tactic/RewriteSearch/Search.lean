/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison

! This file was ported from Lean 3 source module tactic.rewrite_search.search
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Buffer.Basic
import Mathbin.Tactic.RewriteSearch.Discovery
import Mathbin.Tactic.RewriteSearch.Types

/-!
# The graph algorithm part of rewrite search

`search.lean` contains the logic to do a graph search. The search algorithm
starts with an equation to prove, treats the left hand side and right hand side as
two vertices in a graph, and uses rewrite rules to find a path that connects the two sides.
-/


open Tactic

namespace Tactic.RewriteSearch

/-- An edge represents a proof that can get from one expression to another.
It represents the fact that, starting from the vertex `fr`, the expression in `proof`
can prove the vertex `to`.
`how` contains information that the explainer will use to generate Lean code for the
proof.
-/
unsafe structure edge where
  (from_id to_id : ℕ)
  Proof : tactic expr
  how : how
#align tactic.rewrite_search.edge tactic.rewrite_search.edge

/-- Converting an edge to a human-readable string. -/
unsafe def edge.to_string : edge → format
  | e => f! "{e.from_id } → {e.to_id}"
#align tactic.rewrite_search.edge.to_string tactic.rewrite_search.edge.to_string

unsafe instance edge.has_to_format : has_to_format edge :=
  ⟨edge.to_string⟩
#align tactic.rewrite_search.edge.has_to_format tactic.rewrite_search.edge.has_to_format

/-- A vertex represents an expression that is equivalent to either the left or right side
of our initial equation.
* `id` is a numerical id used to refer to this vertex in the context of a single graph.
* `exp` is the expression this vertex represents.
* `pp` is the string format of the expression; we store this in the vertex to avoid
recalculating it.
* `side` is whether this vertex descends from the left or right side of the equation.
* `parent` is the edge that originally added this vertex to the graph.
-/
unsafe structure vertex where
  id : ℕ
  exp : expr
  pp : String
  Side : Side
  parent : Option edge
#align tactic.rewrite_search.vertex tactic.rewrite_search.vertex

/-- The graph represents two trees, one descending from each of the left and right sides
of our initial equation.
* `conf` and `rules` determine what rewrites are used to generate new graph vertices.
  Here, the format of a rewrite rule is an expression for rewriting, plus a flag for the
  direction to apply it in.
* `vertices` maps vertex.id to vertex.
* `vmap` maps vertex.pp to a list of vertex.id with that pp, so we can quickly find collisions.
* `solving_edge` represents a solution that will prove our target equation.
  It is an edge that would connect the two trees, so `solving_edge.fr` and `solving_edge.to`
  are vertices in different trees.
* `lhs` and `rhs` are the left and right expressions we are trying to prove are equal.
-/
unsafe structure graph where
  conf : config
  rules : List (expr × Bool)
  vertices : Buffer vertex
  vmap : native.rb_map String (List ℕ)
  solving_edge : Option edge
  lhs : expr
  rhs : expr
#align tactic.rewrite_search.graph tactic.rewrite_search.graph

/-- Construct a graph to search for a proof of a given equation.

This graph initially contains only two disconnected vertices corresponding to the two
sides of the equation. When `find_proof` is called, we will run a search and add
new vertices and edges.
-/
unsafe def mk_graph (conf : config) (rules : List (expr × Bool)) (eq : expr) : tactic graph := do
  let (lhs, rhs) ← tactic.match_eq Eq <|> tactic.match_iff Eq
  let lhs_pp ← toString <$> tactic.pp lhs
  let rhs_pp ← toString <$> tactic.pp rhs
  let lhs_vertex : vertex := ⟨0, lhs, lhs_pp, Side.L, none⟩
  let rhs_vertex : vertex := ⟨1, rhs, rhs_pp, Side.R, none⟩
  return
      ⟨conf, rules, [lhs_vertex, rhs_vertex].toBuffer,
        native.rb_map.of_list [(lhs_pp, [0]), (rhs_pp, [1])], none, lhs, rhs⟩
#align tactic.rewrite_search.mk_graph tactic.rewrite_search.mk_graph

variable (g : graph)

namespace Graph

/-- Find a list of edges that connect the given edge to the root of its tree.
The edges are returned in leaf-to-root order, while they are in root-to-leaf direction,
so if you want them in the logical order you must reverse the returned list.
-/
private unsafe def walk_up_parents : Option edge → tactic (List edge)
  | none => return []
  | some e => do
    let v ← g.vertices.read_t e.from_id
    let edges ← walk_up_parents v.parent
    return (e :: edges)
#align tactic.rewrite_search.graph.walk_up_parents tactic.rewrite_search.graph.walk_up_parents

/-- Returns two lists that represent a solution. The first list is a path from LHS to some
interior vertex, the second is a path from the RHS to that interior vertex.
-/
private unsafe def solution_paths : tactic (List edge × List edge) := do
  let e ← g.solving_edge
  let v ← g.vertices.read_t e.to_id
  let path1 ← walk_up_parents g e
  let path2 ← walk_up_parents g v.parent
  match v with
    | side.L => return (path2, path1)
    | side.R => return (path1, path2)
#align tactic.rewrite_search.graph.solution_paths tactic.rewrite_search.graph.solution_paths

/-- Finds the id of a vertex in a list whose expression is defeq to the provided expression.
Returns none if there is none.
-/
private unsafe def find_defeq : expr → List ℕ → tactic (Option ℕ)
  | exp, [] => return none
  | exp, id :: rest => do
    let v ← g.vertices.read_t id
    (do
          tactic.is_def_eq v exp
          return (some id)) <|>
        find_defeq exp rest
#align tactic.rewrite_search.graph.find_defeq tactic.rewrite_search.graph.find_defeq

/-- Add the new vertex and edge to the graph, that can be proved in one step starting
at a given vertex, with a given rewrite expression.
For efficiency, it's important that this is the only way the graph is mutated,
and it only appends to the end of the `vertices` buffer.
-/
private unsafe def add_rewrite (v : vertex) (rw : rewrite) : tactic graph := do
  let pp ← toString <$> tactic.pp rw.exp
  let existing_ids :=
    match g.vmap.find pp with
    | some ids => ids
    | none => []
  let maybe_id ← find_defeq g rw.exp existing_ids
  match maybe_id with
    | some id => do
      let existing_vertex ← g id
      if v = existing_vertex then return g
        else return { g with solving_edge := some ⟨v, existing_vertex, rw, rw⟩ }
    | none => do
      let new_vertex_id := g
      let new_edge : edge := ⟨v, new_vertex_id, rw, rw⟩
      let new_vertex : vertex := ⟨new_vertex_id, rw, pp, v, some new_edge⟩
      trace_if_enabled `rewrite_search f! "new edge: {v } → {new_vertex}"
      return
          { g with 
            vertices := g new_vertex
            vmap := g pp (new_vertex_id :: existing_ids) }
#align tactic.rewrite_search.graph.add_rewrite tactic.rewrite_search.graph.add_rewrite

/-- Add all single-step rewrites starting at a particular vertex to the graph.
-/
private unsafe def expand_vertex (v : vertex) : tactic graph := do
  let rws ← get_rewrites g.rules v.exp g.conf
  List.foldlM (fun g rw => add_rewrite g v rw) g rws
#align tactic.rewrite_search.graph.expand_vertex tactic.rewrite_search.graph.expand_vertex

/-- Repeatedly expand edges, starting at a given vertex id, until a solution is found.
-/
private unsafe def find_solving_edge : graph → ℕ → tactic graph
  | g, vertex_id =>
    if vertex_id ≥ g.conf.max_iterations then fail "search failed: max iterations reached"
    else
      if h : vertex_id < g.vertices.size then do
        let v := g.vertices.read (Fin.mk vertex_id h)
        let g ← expand_vertex g v
        match g with
          | some _ => return g
          | none => find_solving_edge g (vertex_id + 1)
      else fail "search failed: all vertices explored"
#align tactic.rewrite_search.graph.find_solving_edge tactic.rewrite_search.graph.find_solving_edge

/-- Use `mk_eq_trans` to combine a list of proof expressions into a single proof expression.
-/
private unsafe def combine_proofs (proofs : List expr) : tactic expr :=
  match proofs with
  | [] => fail "cannot combine empty proof list"
  | proof :: rest => List.foldlM mk_eq_trans proof rest
#align tactic.rewrite_search.graph.combine_proofs tactic.rewrite_search.graph.combine_proofs

/-- Construct a proof unit, given a path through the graph.
This reverses the direction of the proof on the right hand side, with `mk_eq_symm`.
-/
private unsafe def proof_for_edges : side × List edge → tactic (Option proof_unit)
  | (s, []) => return none
  | (s, edges) => do
    let proofs ←
      match s with
        | side.L => edges.mmap fun e => e.Proof
        | side.R => edges.reverse.mmap fun e => e.Proof >>= mk_eq_symm
    let proof ← combine_proofs proofs
    let hows := edges.map fun e => e.how
    return <| some ⟨proof, s, hows⟩
#align tactic.rewrite_search.graph.proof_for_edges tactic.rewrite_search.graph.proof_for_edges

/-- Checks to see if an empty series of rewrites will solve this, because it's an expression
of the form a = a.
-/
private unsafe def find_trivial_proof : tactic (graph × expr × List proof_unit) := do
  is_def_eq g g
  let exp ← mk_eq_refl g.lhs
  return (g, exp, [])
#align tactic.rewrite_search.graph.find_trivial_proof tactic.rewrite_search.graph.find_trivial_proof

/-- Run the search to find a proof for the provided graph.
Normally, this is the only external method needed to run the graph search.
-/
unsafe def find_proof : tactic (graph × expr × List proof_unit) :=
  find_trivial_proof g <|> do
    let g ← find_solving_edge g 0
    let (left_edges, right_edges) ← solution_paths g
    let units ← [(Side.L, left_edges), (Side.R, right_edges)].mmapFilter proof_for_edges
    let proof ← combine_proofs <| Units.map fun u => u.Proof
    return (g, proof, Units)
#align tactic.rewrite_search.graph.find_proof tactic.rewrite_search.graph.find_proof

end Graph

end Tactic.RewriteSearch

