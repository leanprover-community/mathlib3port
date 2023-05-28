/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.connectivity
! leanprover-community/mathlib commit b99e2d58a5e6861833fa8de11e51a81144258db4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Combinatorics.SimpleGraph.Subgraph
import Mathbin.Data.List.Rotate

/-!

# Graph connectivity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk` (with accompanying pattern definitions
  `simple_graph.walk.nil'` and `simple_graph.walk.cons'`)

* `simple_graph.walk.is_trail`, `simple_graph.walk.is_path`, and `simple_graph.walk.is_cycle`.

* `simple_graph.path`

* `simple_graph.walk.map` and `simple_graph.path.map` for the induced map on walks,
  given an (injective) graph homomorphism.

* `simple_graph.reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `simple_graph.preconnected` and `simple_graph.connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

* `simple_graph.connected_component` is the type of connected components of
  a given graph.

* `simple_graph.is_bridge` for whether an edge is a bridge edge

## Main statements

* `simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
walks, trails, paths, circuits, cycles, bridge edges

-/


open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}

variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

#print SimpleGraph.Walk /-
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`.

See `simple_graph.walk.nil'` and `simple_graph.walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : walk v w) : walk u w
  deriving DecidableEq
#align simple_graph.walk SimpleGraph.Walk
-/

attribute [refl] walk.nil

#print SimpleGraph.Walk.instInhabited /-
@[simps]
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) :=
  ⟨Walk.nil⟩
#align simple_graph.walk.inhabited SimpleGraph.Walk.instInhabited
-/

#print SimpleGraph.Adj.toWalk /-
/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil
#align simple_graph.adj.to_walk SimpleGraph.Adj.toWalk
-/

namespace Walk

variable {G}

#print SimpleGraph.Walk.nil' /-
/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : G.Walk u u :=
  Walk.nil
#align simple_graph.walk.nil' SimpleGraph.Walk.nil'
-/

#print SimpleGraph.Walk.cons' /-
/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w :=
  Walk.cons h p
#align simple_graph.walk.cons' SimpleGraph.Walk.cons'
-/

#print SimpleGraph.Walk.copy /-
/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  Eq.ndrec (Eq.ndrec p hv) hu
#align simple_graph.walk.copy SimpleGraph.Walk.copy
-/

#print SimpleGraph.Walk.copy_rfl_rfl /-
@[simp]
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p :=
  rfl
#align simple_graph.walk.copy_rfl_rfl SimpleGraph.Walk.copy_rfl_rfl
-/

#print SimpleGraph.Walk.copy_copy /-
@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v) (hu : u = u') (hv : v = v') (hu' : u' = u'')
    (hv' : v' = v'') : (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') :=
  by
  subst_vars
  rfl
#align simple_graph.walk.copy_copy SimpleGraph.Walk.copy_copy
-/

#print SimpleGraph.Walk.copy_nil /-
@[simp]
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = Walk.nil :=
  by
  subst_vars
  rfl
#align simple_graph.walk.copy_nil SimpleGraph.Walk.copy_nil
-/

#print SimpleGraph.Walk.copy_cons /-
theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (by rwa [← hu]) (p.copy rfl hw) :=
  by
  subst_vars
  rfl
#align simple_graph.walk.copy_cons SimpleGraph.Walk.copy_cons
-/

#print SimpleGraph.Walk.cons_copy /-
@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    Walk.cons h (p.copy hv hw) = (Walk.cons (by rwa [hv]) p).copy rfl hw :=
  by
  subst_vars
  rfl
#align simple_graph.walk.cons_copy SimpleGraph.Walk.cons_copy
-/

#print SimpleGraph.Walk.exists_eq_cons_of_ne /-
theorem exists_eq_cons_of_ne :
    ∀ {u v : V} (hne : u ≠ v) (p : G.Walk u v),
      ∃ (w : V)(h : G.Adj u w)(p' : G.Walk w v), p = cons h p'
  | _, _, hne, nil => (hne rfl).elim
  | _, _, _, cons h p' => ⟨_, h, p', rfl⟩
#align simple_graph.walk.exists_eq_cons_of_ne SimpleGraph.Walk.exists_eq_cons_of_ne
-/

#print SimpleGraph.Walk.length /-
/-- The length of a walk is the number of edges/darts along it. -/
def length : ∀ {u v : V}, G.Walk u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ q => q.length.succ
#align simple_graph.walk.length SimpleGraph.Walk.length
-/

#print SimpleGraph.Walk.append /-
/-- The concatenation of two compatible walks. -/
@[trans]
def append : ∀ {u v w : V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)
#align simple_graph.walk.append SimpleGraph.Walk.append
-/

#print SimpleGraph.Walk.concat /-
/-- The reversed version of `simple_graph.walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w :=
  p.append (cons h nil)
#align simple_graph.walk.concat SimpleGraph.Walk.concat
-/

#print SimpleGraph.Walk.concat_eq_append /-
theorem concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) :=
  rfl
#align simple_graph.walk.concat_eq_append SimpleGraph.Walk.concat_eq_append
-/

#print SimpleGraph.Walk.reverseAux /-
/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux : ∀ {u v w : V}, G.Walk u v → G.Walk u w → G.Walk v w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => reverse_aux p (cons (G.symm h) q)
#align simple_graph.walk.reverse_aux SimpleGraph.Walk.reverseAux
-/

#print SimpleGraph.Walk.reverse /-
/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u :=
  w.reverseAux nil
#align simple_graph.walk.reverse SimpleGraph.Walk.reverse
-/

#print SimpleGraph.Walk.getVert /-
/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def getVert : ∀ {u v : V} (p : G.Walk u v) (n : ℕ), V
  | u, v, nil, _ => u
  | u, v, cons _ _, 0 => u
  | u, v, cons _ q, n + 1 => q.getVert n
#align simple_graph.walk.get_vert SimpleGraph.Walk.getVert
-/

#print SimpleGraph.Walk.getVert_zero /-
@[simp]
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl
#align simple_graph.walk.get_vert_zero SimpleGraph.Walk.getVert_zero
-/

#print SimpleGraph.Walk.getVert_of_length_le /-
theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) : w.getVert i = v :=
  by
  induction' w with _ x y z hxy wyz IH generalizing i
  · rfl
  · cases i
    · cases hi
    · exact IH (Nat.succ_le_succ_iff.1 hi)
#align simple_graph.walk.get_vert_of_length_le SimpleGraph.Walk.getVert_of_length_le
-/

#print SimpleGraph.Walk.getVert_length /-
@[simp]
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le
#align simple_graph.walk.get_vert_length SimpleGraph.Walk.getVert_length
-/

#print SimpleGraph.Walk.adj_getVert_succ /-
theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) :=
  by
  induction' w with _ x y z hxy wyz IH generalizing i
  · cases hi
  · cases i
    · simp [get_vert, hxy]
    · exact IH (Nat.succ_lt_succ_iff.1 hi)
#align simple_graph.walk.adj_get_vert_succ SimpleGraph.Walk.adj_getVert_succ
-/

#print SimpleGraph.Walk.cons_append /-
@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) :=
  rfl
#align simple_graph.walk.cons_append SimpleGraph.Walk.cons_append
-/

#print SimpleGraph.Walk.cons_nil_append /-
@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p :=
  rfl
#align simple_graph.walk.cons_nil_append SimpleGraph.Walk.cons_nil_append
-/

#print SimpleGraph.Walk.append_nil /-
@[simp]
theorem append_nil : ∀ {u v : V} (p : G.Walk u v), p.append nil = p
  | _, _, nil => rfl
  | _, _, cons h p => by rw [cons_append, append_nil]
#align simple_graph.walk.append_nil SimpleGraph.Walk.append_nil
-/

#print SimpleGraph.Walk.nil_append /-
@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl
#align simple_graph.walk.nil_append SimpleGraph.Walk.nil_append
-/

#print SimpleGraph.Walk.append_assoc /-
theorem append_assoc :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x),
      p.append (q.append r) = (p.append q).append r
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    dsimp only [append]
    rw [append_assoc]
#align simple_graph.walk.append_assoc SimpleGraph.Walk.append_assoc
-/

#print SimpleGraph.Walk.append_copy_copy /-
@[simp]
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w) (hu : u = u')
    (hv : v = v') (hw : w = w') : (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw :=
  by
  subst_vars
  rfl
#align simple_graph.walk.append_copy_copy SimpleGraph.Walk.append_copy_copy
-/

#print SimpleGraph.Walk.concat_nil /-
theorem concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil :=
  rfl
#align simple_graph.walk.concat_nil SimpleGraph.Walk.concat_nil
-/

#print SimpleGraph.Walk.concat_cons /-
@[simp]
theorem concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x) :
    (cons h p).concat h' = cons h (p.concat h') :=
  rfl
#align simple_graph.walk.concat_cons SimpleGraph.Walk.concat_cons
-/

#print SimpleGraph.Walk.append_concat /-
theorem append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x) :
    p.append (q.concat h) = (p.append q).concat h :=
  append_assoc _ _ _
#align simple_graph.walk.append_concat SimpleGraph.Walk.append_concat
-/

#print SimpleGraph.Walk.concat_append /-
theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append, ← append_assoc, cons_nil_append]
#align simple_graph.walk.concat_append SimpleGraph.Walk.concat_append
-/

#print SimpleGraph.Walk.exists_cons_eq_concat /-
/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
theorem exists_cons_eq_concat :
    ∀ {u v w : V} (h : G.Adj u v) (p : G.Walk v w),
      ∃ (x : V)(q : G.Walk u x)(h' : G.Adj x w), cons h p = q.concat h'
  | _, _, _, h, nil => ⟨_, nil, h, rfl⟩
  | _, _, _, h, cons h' p =>
    by
    obtain ⟨y, q, h'', hc⟩ := exists_cons_eq_concat h' p
    refine' ⟨y, cons h q, h'', _⟩
    rw [concat_cons, hc]
#align simple_graph.walk.exists_cons_eq_concat SimpleGraph.Walk.exists_cons_eq_concat
-/

#print SimpleGraph.Walk.exists_concat_eq_cons /-
/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
theorem exists_concat_eq_cons :
    ∀ {u v w : V} (p : G.Walk u v) (h : G.Adj v w),
      ∃ (x : V)(h' : G.Adj u x)(q : G.Walk x w), p.concat h = cons h' q
  | _, _, _, nil, h => ⟨_, h, nil, rfl⟩
  | _, _, _, cons h' p, h => ⟨_, h', Walk.concat p h, concat_cons _ _ _⟩
#align simple_graph.walk.exists_concat_eq_cons SimpleGraph.Walk.exists_concat_eq_cons
-/

#print SimpleGraph.Walk.reverse_nil /-
@[simp]
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil :=
  rfl
#align simple_graph.walk.reverse_nil SimpleGraph.Walk.reverse_nil
-/

#print SimpleGraph.Walk.reverse_singleton /-
theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl
#align simple_graph.walk.reverse_singleton SimpleGraph.Walk.reverse_singleton
-/

#print SimpleGraph.Walk.cons_reverseAux /-
@[simp]
theorem cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q) :=
  rfl
#align simple_graph.walk.cons_reverse_aux SimpleGraph.Walk.cons_reverseAux
-/

#print SimpleGraph.Walk.append_reverseAux /-
@[simp]
protected theorem append_reverseAux :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x),
      (p.append q).reverseAux r = q.reverseAux (p.reverseAux r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => append_reverse_aux p' q (cons (G.symm h) r)
#align simple_graph.walk.append_reverse_aux SimpleGraph.Walk.append_reverseAux
-/

#print SimpleGraph.Walk.reverseAux_append /-
@[simp]
protected theorem reverseAux_append :
    ∀ {u v w x : V} (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x),
      (p.reverseAux q).append r = p.reverseAux (q.append r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by simp [reverse_aux_append p' (cons (G.symm h) q) r]
#align simple_graph.walk.reverse_aux_append SimpleGraph.Walk.reverseAux_append
-/

#print SimpleGraph.Walk.reverseAux_eq_reverse_append /-
protected theorem reverseAux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]
#align simple_graph.walk.reverse_aux_eq_reverse_append SimpleGraph.Walk.reverseAux_eq_reverse_append
-/

#print SimpleGraph.Walk.reverse_cons /-
@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by simp [reverse]
#align simple_graph.walk.reverse_cons SimpleGraph.Walk.reverse_cons
-/

#print SimpleGraph.Walk.reverse_copy /-
@[simp]
theorem reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu :=
  by
  subst_vars
  rfl
#align simple_graph.walk.reverse_copy SimpleGraph.Walk.reverse_copy
-/

#print SimpleGraph.Walk.reverse_append /-
@[simp]
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]
#align simple_graph.walk.reverse_append SimpleGraph.Walk.reverse_append
-/

#print SimpleGraph.Walk.reverse_concat /-
@[simp]
theorem reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).reverse = cons (G.symm h) p.reverse := by simp [concat_eq_append]
#align simple_graph.walk.reverse_concat SimpleGraph.Walk.reverse_concat
-/

#print SimpleGraph.Walk.reverse_reverse /-
@[simp]
theorem reverse_reverse : ∀ {u v : V} (p : G.Walk u v), p.reverse.reverse = p
  | _, _, nil => rfl
  | _, _, cons h p => by simp [reverse_reverse]
#align simple_graph.walk.reverse_reverse SimpleGraph.Walk.reverse_reverse
-/

#print SimpleGraph.Walk.length_nil /-
@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 :=
  rfl
#align simple_graph.walk.length_nil SimpleGraph.Walk.length_nil
-/

#print SimpleGraph.Walk.length_cons /-
@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 :=
  rfl
#align simple_graph.walk.length_cons SimpleGraph.Walk.length_cons
-/

#print SimpleGraph.Walk.length_copy /-
@[simp]
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl
#align simple_graph.walk.length_copy SimpleGraph.Walk.length_copy
-/

#print SimpleGraph.Walk.length_append /-
@[simp]
theorem length_append :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk v w), (p.append q).length = p.length + q.length
  | _, _, _, nil, _ => by simp
  | _, _, _, cons _ _, _ => by simp [length_append, add_left_comm, add_comm]
#align simple_graph.walk.length_append SimpleGraph.Walk.length_append
-/

#print SimpleGraph.Walk.length_concat /-
@[simp]
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 :=
  length_append _ _
#align simple_graph.walk.length_concat SimpleGraph.Walk.length_concat
-/

#print SimpleGraph.Walk.length_reverseAux /-
@[simp]
protected theorem length_reverseAux :
    ∀ {u v w : V} (p : G.Walk u v) (q : G.Walk u w), (p.reverseAux q).length = p.length + q.length
  | _, _, _, nil, _ => by simp!
  | _, _, _, cons _ _, _ => by simp [length_reverse_aux, Nat.add_succ, Nat.succ_add]
#align simple_graph.walk.length_reverse_aux SimpleGraph.Walk.length_reverseAux
-/

#print SimpleGraph.Walk.length_reverse /-
@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]
#align simple_graph.walk.length_reverse SimpleGraph.Walk.length_reverse
-/

#print SimpleGraph.Walk.eq_of_length_eq_zero /-
theorem eq_of_length_eq_zero : ∀ {u v : V} {p : G.Walk u v}, p.length = 0 → u = v
  | _, _, nil, _ => rfl
#align simple_graph.walk.eq_of_length_eq_zero SimpleGraph.Walk.eq_of_length_eq_zero
-/

#print SimpleGraph.Walk.exists_length_eq_zero_iff /-
@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v :=
  by
  constructor
  · rintro ⟨p, hp⟩
    exact eq_of_length_eq_zero hp
  · rintro rfl
    exact ⟨nil, rfl⟩
#align simple_graph.walk.exists_length_eq_zero_iff SimpleGraph.Walk.exists_length_eq_zero_iff
-/

#print SimpleGraph.Walk.length_eq_zero_iff /-
@[simp]
theorem length_eq_zero_iff {u : V} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by cases p <;> simp
#align simple_graph.walk.length_eq_zero_iff SimpleGraph.Walk.length_eq_zero_iff
-/

section ConcatRec

variable {motive : ∀ u v : V, G.Walk u v → Sort _} (Hnil : ∀ {u : V}, motive u u nil)
  (Hconcat : ∀ {u v w : V} (p : G.Walk u v) (h : G.Adj v w), motive u v p → motive u w (p.concat h))

#print SimpleGraph.Walk.concatRecAux /-
/-- Auxiliary definition for `simple_graph.walk.concat_rec` -/
def concatRecAux : ∀ {u v : V} (p : G.Walk u v), motive v u p.reverse
  | _, _, nil => Hnil
  | _, _, cons h p =>
    Eq.ndrec (Hconcat p.reverse (G.symm h) (concat_rec_aux p)) (reverse_cons h p).symm
#align simple_graph.walk.concat_rec_aux SimpleGraph.Walk.concatRecAux
-/

#print SimpleGraph.Walk.concatRec /-
/-- Recursor on walks by inducting on `simple_graph.walk.concat`.

This is inducting from the opposite end of the walk compared
to `simple_graph.walk.rec`, which inducts on `simple_graph.walk.cons`. -/
@[elab_as_elim]
def concatRec {u v : V} (p : G.Walk u v) : motive u v p :=
  Eq.ndrec (concatRecAux (@Hnil) (@Hconcat) p.reverse) (reverse_reverse p)
#align simple_graph.walk.concat_rec SimpleGraph.Walk.concatRec
-/

/- warning: simple_graph.walk.concat_rec_nil -> SimpleGraph.Walk.concatRec_nil is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {motive : forall (u : V) (v : V), (SimpleGraph.Walk.{u1} V G u v) -> Sort.{u2}} (Hnil : forall {u : V}, motive u u (SimpleGraph.Walk.nil.{u1} V G u)) (Hconcat : forall {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u1} V G u v) (h : SimpleGraph.Adj.{u1} V G v w), (motive u v p) -> (motive u w (SimpleGraph.Walk.concat.{u1} V G u v w p h))) (u : V), Eq.{u2} (motive u u (SimpleGraph.Walk.nil.{u1} V G u)) (SimpleGraph.Walk.concatRec.{u1, u2} V G motive Hnil Hconcat u u (SimpleGraph.Walk.nil.{u1} V G u)) (Hnil u)
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {motive : forall (u : V) (v : V), (SimpleGraph.Walk.{u2} V G u v) -> Sort.{u1}} (Hnil : forall {u : V}, motive u u (SimpleGraph.Walk.nil.{u2} V G u)) (Hconcat : forall {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u2} V G u v) (h : SimpleGraph.Adj.{u2} V G v w), (motive u v p) -> (motive u w (SimpleGraph.Walk.concat.{u2} V G u v w p h))) (u : V), Eq.{u1} (motive u u (SimpleGraph.Walk.nil.{u2} V G u)) (SimpleGraph.Walk.concatRec.{u2, u1} V G motive Hnil Hconcat u u (SimpleGraph.Walk.nil.{u2} V G u)) (Hnil u)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.concat_rec_nil SimpleGraph.Walk.concatRec_nilₓ'. -/
@[simp]
theorem concatRec_nil (u : V) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.Walk u u) = Hnil :=
  rfl
#align simple_graph.walk.concat_rec_nil SimpleGraph.Walk.concatRec_nil

/- warning: simple_graph.walk.concat_rec_concat -> SimpleGraph.Walk.concatRec_concat is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {motive : forall (u : V) (v : V), (SimpleGraph.Walk.{u1} V G u v) -> Sort.{u2}} (Hnil : forall {u : V}, motive u u (SimpleGraph.Walk.nil.{u1} V G u)) (Hconcat : forall {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u1} V G u v) (h : SimpleGraph.Adj.{u1} V G v w), (motive u v p) -> (motive u w (SimpleGraph.Walk.concat.{u1} V G u v w p h))) {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u1} V G u v) (h : SimpleGraph.Adj.{u1} V G v w), Eq.{u2} (motive u w (SimpleGraph.Walk.concat.{u1} V G u v w p h)) (SimpleGraph.Walk.concatRec.{u1, u2} V G motive Hnil Hconcat u w (SimpleGraph.Walk.concat.{u1} V G u v w p h)) (Hconcat u v w p h (SimpleGraph.Walk.concatRec.{u1, u2} V G (fun (_x : V) (_x_1 : V) (_x_2 : SimpleGraph.Walk.{u1} V G _x _x_1) => motive _x _x_1 _x_2) Hnil Hconcat u v p))
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {motive : forall (u : V) (v : V), (SimpleGraph.Walk.{u2} V G u v) -> Sort.{u1}} (Hnil : forall {u : V}, motive u u (SimpleGraph.Walk.nil.{u2} V G u)) (Hconcat : forall {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u2} V G u v) (h : SimpleGraph.Adj.{u2} V G v w), (motive u v p) -> (motive u w (SimpleGraph.Walk.concat.{u2} V G u v w p h))) {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u2} V G u v) (h : SimpleGraph.Adj.{u2} V G v w), Eq.{u1} (motive u w (SimpleGraph.Walk.concat.{u2} V G u v w p h)) (SimpleGraph.Walk.concatRec.{u2, u1} V G motive Hnil Hconcat u w (SimpleGraph.Walk.concat.{u2} V G u v w p h)) (Hconcat u v w p h (SimpleGraph.Walk.concatRec.{u2, u1} V G (fun (_x : V) (_x_1 : V) (_x_2 : SimpleGraph.Walk.{u2} V G _x _x_1) => motive _x _x_1 _x_2) Hnil Hconcat u v p))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.concat_rec_concat SimpleGraph.Walk.concatRec_concatₓ'. -/
@[simp]
theorem concatRec_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (p.concat h) =
      Hconcat p h (concatRec (@Hnil) (@Hconcat) p) :=
  by
  simp only [concat_rec]
  apply eq_of_hEq
  apply rec_heq_of_heq
  trans concat_rec_aux (@Hnil) (@Hconcat) (cons h.symm p.reverse)
  · congr
    simp
  · rw [concat_rec_aux, rec_heq_iff_heq]
    congr <;> simp [heq_rec_iff_heq]
#align simple_graph.walk.concat_rec_concat SimpleGraph.Walk.concatRec_concat

end ConcatRec

#print SimpleGraph.Walk.concat_ne_nil /-
theorem concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h ≠ nil := by
  cases p <;> simp [concat]
#align simple_graph.walk.concat_ne_nil SimpleGraph.Walk.concat_ne_nil
-/

#print SimpleGraph.Walk.concat_inj /-
theorem concat_inj {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
    {h' : G.Adj v' w} (he : p.concat h = p'.concat h') : ∃ hv : v = v', p.copy rfl hv = p' :=
  by
  induction p
  · cases p'
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [concat_nil, concat_cons] at he
      obtain ⟨rfl, he⟩ := he
      simp only [heq_iff_eq] at he
      exact concat_ne_nil _ _ he.symm
  · rw [concat_cons] at he
    cases p'
    · exfalso
      simp only [concat_nil] at he
      obtain ⟨rfl, he⟩ := he
      rw [heq_iff_eq] at he
      exact concat_ne_nil _ _ he
    · rw [concat_cons] at he
      simp only at he
      obtain ⟨rfl, he⟩ := he
      rw [heq_iff_eq] at he
      obtain ⟨rfl, rfl⟩ := p_ih he
      exact ⟨rfl, rfl⟩
#align simple_graph.walk.concat_inj SimpleGraph.Walk.concat_inj
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.support /-
/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : ∀ {u v : V}, G.Walk u v → List V
  | u, v, nil => [u]
  | u, v, cons h p => u::p.support
#align simple_graph.walk.support SimpleGraph.Walk.support
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.darts /-
/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts : ∀ {u v : V}, G.Walk u v → List G.Dart
  | u, v, nil => []
  | u, v, cons h p => ⟨(u, _), h⟩::p.darts
#align simple_graph.walk.darts SimpleGraph.Walk.darts
-/

#print SimpleGraph.Walk.edges /-
/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_graph.walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) :=
  p.darts.map Dart.edge
#align simple_graph.walk.edges SimpleGraph.Walk.edges
-/

#print SimpleGraph.Walk.support_nil /-
@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] :=
  rfl
#align simple_graph.walk.support_nil SimpleGraph.Walk.support_nil
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.support_cons /-
@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u::p.support :=
  rfl
#align simple_graph.walk.support_cons SimpleGraph.Walk.support_cons
-/

#print SimpleGraph.Walk.support_concat /-
@[simp]
theorem support_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).support = p.support.concat w := by induction p <;> simp [*, concat_nil]
#align simple_graph.walk.support_concat SimpleGraph.Walk.support_concat
-/

#print SimpleGraph.Walk.support_copy /-
@[simp]
theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst_vars
  rfl
#align simple_graph.walk.support_copy SimpleGraph.Walk.support_copy
-/

#print SimpleGraph.Walk.support_append /-
theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support ++ p'.support.tail := by induction p <;> cases p' <;> simp [*]
#align simple_graph.walk.support_append SimpleGraph.Walk.support_append
-/

#print SimpleGraph.Walk.support_reverse /-
@[simp]
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]
#align simple_graph.walk.support_reverse SimpleGraph.Walk.support_reverse
-/

#print SimpleGraph.Walk.support_ne_nil /-
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp
#align simple_graph.walk.support_ne_nil SimpleGraph.Walk.support_ne_nil
-/

#print SimpleGraph.Walk.tail_support_append /-
theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]
#align simple_graph.walk.tail_support_append SimpleGraph.Walk.tail_support_append
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.support_eq_cons /-
theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u::p.support.tail := by
  cases p <;> simp
#align simple_graph.walk.support_eq_cons SimpleGraph.Walk.support_eq_cons
-/

#print SimpleGraph.Walk.start_mem_support /-
@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp
#align simple_graph.walk.start_mem_support SimpleGraph.Walk.start_mem_support
-/

#print SimpleGraph.Walk.end_mem_support /-
@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]
#align simple_graph.walk.end_mem_support SimpleGraph.Walk.end_mem_support
-/

#print SimpleGraph.Walk.support_nonempty /-
@[simp]
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩
#align simple_graph.walk.support_nonempty SimpleGraph.Walk.support_nonempty
-/

#print SimpleGraph.Walk.mem_support_iff /-
theorem mem_support_iff {u v w : V} (p : G.Walk u v) : w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
  by cases p <;> simp
#align simple_graph.walk.mem_support_iff SimpleGraph.Walk.mem_support_iff
-/

#print SimpleGraph.Walk.mem_support_nil_iff /-
theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp
#align simple_graph.walk.mem_support_nil_iff SimpleGraph.Walk.mem_support_nil_iff
-/

#print SimpleGraph.Walk.mem_tail_support_append_iff /-
@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_append]
#align simple_graph.walk.mem_tail_support_append_iff SimpleGraph.Walk.mem_tail_support_append_iff
-/

#print SimpleGraph.Walk.end_mem_tail_support_of_ne /-
@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail :=
  by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp
#align simple_graph.walk.end_mem_tail_support_of_ne SimpleGraph.Walk.end_mem_tail_support_of_ne
-/

#print SimpleGraph.Walk.mem_support_append_iff /-
@[simp]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support :=
  by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  by_cases h : t = v <;> by_cases h' : t = u <;> subst_vars <;> try have := Ne.symm h' <;> simp [*]
#align simple_graph.walk.mem_support_append_iff SimpleGraph.Walk.mem_support_append_iff
-/

#print SimpleGraph.Walk.subset_support_append_left /-
@[simp]
theorem subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v)
    (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp only [walk.support_append, List.subset_append_left]
#align simple_graph.walk.subset_support_append_left SimpleGraph.Walk.subset_support_append_left
-/

#print SimpleGraph.Walk.subset_support_append_right /-
@[simp]
theorem subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V} (p : G.Walk u v)
    (q : G.Walk v w) : q.support ⊆ (p.append q).support :=
  by
  intro h
  simp (config := { contextual := true }) only [mem_support_append_iff, or_true_iff, imp_true_iff]
#align simple_graph.walk.subset_support_append_right SimpleGraph.Walk.subset_support_append_right
-/

#print SimpleGraph.Walk.coe_support /-
theorem coe_support {u v : V} (p : G.Walk u v) : (p.support : Multiset V) = {u} + p.support.tail :=
  by cases p <;> rfl
#align simple_graph.walk.coe_support SimpleGraph.Walk.coe_support
-/

#print SimpleGraph.Walk.coe_support_append /-
theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]
#align simple_graph.walk.coe_support_append SimpleGraph.Walk.coe_support_append
-/

#print SimpleGraph.Walk.coe_support_append' /-
theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} :=
  by
  rw [support_append, ← Multiset.coe_add]
  simp only [coe_support]
  rw [add_comm {v}]
  simp only [← add_assoc, add_tsub_cancel_right]
#align simple_graph.walk.coe_support_append' SimpleGraph.Walk.coe_support_append'
-/

#print SimpleGraph.Walk.chain_adj_support /-
theorem chain_adj_support :
    ∀ {u v w : V} (h : G.Adj u v) (p : G.Walk v w), List.Chain G.Adj u p.support
  | _, _, _, h, nil => List.Chain.cons h List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_adj_support h' p)
#align simple_graph.walk.chain_adj_support SimpleGraph.Walk.chain_adj_support
-/

#print SimpleGraph.Walk.chain'_adj_support /-
theorem chain'_adj_support : ∀ {u v : V} (p : G.Walk u v), List.Chain' G.Adj p.support
  | _, _, nil => List.Chain.nil
  | _, _, cons h p => chain_adj_support h p
#align simple_graph.walk.chain'_adj_support SimpleGraph.Walk.chain'_adj_support
-/

#print SimpleGraph.Walk.chain_dartAdj_darts /-
theorem chain_dartAdj_darts :
    ∀ {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w), List.Chain G.DartAdj d p.darts
  | _, _, _, h, nil => List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_dart_adj_darts rfl p)
#align simple_graph.walk.chain_dart_adj_darts SimpleGraph.Walk.chain_dartAdj_darts
-/

#print SimpleGraph.Walk.chain'_dartAdj_darts /-
theorem chain'_dartAdj_darts : ∀ {u v : V} (p : G.Walk u v), List.Chain' G.DartAdj p.darts
  | _, _, nil => trivial
  | _, _, cons h p => chain_dartAdj_darts rfl p
#align simple_graph.walk.chain'_dart_adj_darts SimpleGraph.Walk.chain'_dartAdj_darts
-/

/- warning: simple_graph.walk.edges_subset_edge_set -> SimpleGraph.Walk.edges_subset_edgeSet is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {{e : Sym2.{u1} V}}, (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) G))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {{e : Sym2.{u1} V}}, (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V G))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.edges_subset_edge_set SimpleGraph.Walk.edges_subset_edgeSetₓ'. -/
/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edgeSet :
    ∀ {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄ (h : e ∈ p.edges), e ∈ G.edgeSetEmbedding
  | _, _, cons h' p', e, h => by rcases h with ⟨rfl, h⟩ <;> solve_by_elim
#align simple_graph.walk.edges_subset_edge_set SimpleGraph.Walk.edges_subset_edgeSet

#print SimpleGraph.Walk.adj_of_mem_edges /-
theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : ⟦(x, y)⟧ ∈ p.edges) : G.Adj x y :=
  edges_subset_edgeSet p h
#align simple_graph.walk.adj_of_mem_edges SimpleGraph.Walk.adj_of_mem_edges
-/

#print SimpleGraph.Walk.darts_nil /-
@[simp]
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] :=
  rfl
#align simple_graph.walk.darts_nil SimpleGraph.Walk.darts_nil
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.darts_cons /-
@[simp]
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩::p.darts :=
  rfl
#align simple_graph.walk.darts_cons SimpleGraph.Walk.darts_cons
-/

#print SimpleGraph.Walk.darts_concat /-
@[simp]
theorem darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by induction p <;> simp [*, concat_nil]
#align simple_graph.walk.darts_concat SimpleGraph.Walk.darts_concat
-/

#print SimpleGraph.Walk.darts_copy /-
@[simp]
theorem darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).darts = p.darts := by
  subst_vars
  rfl
#align simple_graph.walk.darts_copy SimpleGraph.Walk.darts_copy
-/

#print SimpleGraph.Walk.darts_append /-
@[simp]
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').darts = p.darts ++ p'.darts := by induction p <;> simp [*]
#align simple_graph.walk.darts_append SimpleGraph.Walk.darts_append
-/

#print SimpleGraph.Walk.darts_reverse /-
@[simp]
theorem darts_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.darts = (p.darts.map Dart.symm).reverse := by induction p <;> simp [*, Sym2.eq_swap]
#align simple_graph.walk.darts_reverse SimpleGraph.Walk.darts_reverse
-/

#print SimpleGraph.Walk.mem_darts_reverse /-
theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} :
    d ∈ p.reverse.darts ↔ d.symm ∈ p.darts := by simp
#align simple_graph.walk.mem_darts_reverse SimpleGraph.Walk.mem_darts_reverse
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.cons_map_snd_darts /-
theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u::p.darts.map Dart.snd) = p.support := by
  induction p <;> simp! [*]
#align simple_graph.walk.cons_map_snd_darts SimpleGraph.Walk.cons_map_snd_darts
-/

#print SimpleGraph.Walk.map_snd_darts /-
theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map Dart.snd = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)
#align simple_graph.walk.map_snd_darts SimpleGraph.Walk.map_snd_darts
-/

#print SimpleGraph.Walk.map_fst_darts_append /-
theorem map_fst_darts_append {u v : V} (p : G.Walk u v) : p.darts.map Dart.fst ++ [v] = p.support :=
  by induction p <;> simp! [*]
#align simple_graph.walk.map_fst_darts_append SimpleGraph.Walk.map_fst_darts_append
-/

#print SimpleGraph.Walk.map_fst_darts /-
theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map Dart.fst = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)
#align simple_graph.walk.map_fst_darts SimpleGraph.Walk.map_fst_darts
-/

#print SimpleGraph.Walk.edges_nil /-
@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] :=
  rfl
#align simple_graph.walk.edges_nil SimpleGraph.Walk.edges_nil
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.Walk.edges_cons /-
@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = ⟦(u, v)⟧::p.edges :=
  rfl
#align simple_graph.walk.edges_cons SimpleGraph.Walk.edges_cons
-/

#print SimpleGraph.Walk.edges_concat /-
@[simp]
theorem edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edges = p.edges.concat ⟦(v, w)⟧ := by simp [edges]
#align simple_graph.walk.edges_concat SimpleGraph.Walk.edges_concat
-/

#print SimpleGraph.Walk.edges_copy /-
@[simp]
theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst_vars
  rfl
#align simple_graph.walk.edges_copy SimpleGraph.Walk.edges_copy
-/

#print SimpleGraph.Walk.edges_append /-
@[simp]
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').edges = p.edges ++ p'.edges := by simp [edges]
#align simple_graph.walk.edges_append SimpleGraph.Walk.edges_append
-/

#print SimpleGraph.Walk.edges_reverse /-
@[simp]
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [edges]
#align simple_graph.walk.edges_reverse SimpleGraph.Walk.edges_reverse
-/

#print SimpleGraph.Walk.length_support /-
@[simp]
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]
#align simple_graph.walk.length_support SimpleGraph.Walk.length_support
-/

#print SimpleGraph.Walk.length_darts /-
@[simp]
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]
#align simple_graph.walk.length_darts SimpleGraph.Walk.length_darts
-/

#print SimpleGraph.Walk.length_edges /-
@[simp]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]
#align simple_graph.walk.length_edges SimpleGraph.Walk.length_edges
-/

#print SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts /-
theorem dart_fst_mem_support_of_mem_darts :
    ∀ {u v : V} (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.support
  | u, v, cons h p', d, hd =>
    by
    simp only [support_cons, darts_cons, List.mem_cons] at hd⊢
    rcases hd with (rfl | hd)
    · exact Or.inl rfl
    · exact Or.inr (dart_fst_mem_support_of_mem_darts _ hd)
#align simple_graph.walk.dart_fst_mem_support_of_mem_darts SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts
-/

#print SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts /-
theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d ∈ p.darts) : d.snd ∈ p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)
#align simple_graph.walk.dart_snd_mem_support_of_mem_darts SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts
-/

#print SimpleGraph.Walk.fst_mem_support_of_mem_edges /-
theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
    t ∈ p.support := by
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he
  rw [dart_edge_eq_mk_iff'] at he
  rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd
#align simple_graph.walk.fst_mem_support_of_mem_edges SimpleGraph.Walk.fst_mem_support_of_mem_edges
-/

#print SimpleGraph.Walk.snd_mem_support_of_mem_edges /-
theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
    u ∈ p.support := by
  rw [Sym2.eq_swap] at he
  exact p.fst_mem_support_of_mem_edges he
#align simple_graph.walk.snd_mem_support_of_mem_edges SimpleGraph.Walk.snd_mem_support_of_mem_edges
-/

#print SimpleGraph.Walk.darts_nodup_of_support_nodup /-
theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p
  · simp
  · simp only [darts_cons, support_cons, List.nodup_cons] at h⊢
    refine' ⟨fun h' => h.1 (dart_fst_mem_support_of_mem_darts p_p h'), p_ih h.2⟩
#align simple_graph.walk.darts_nodup_of_support_nodup SimpleGraph.Walk.darts_nodup_of_support_nodup
-/

#print SimpleGraph.Walk.edges_nodup_of_support_nodup /-
theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p
  · simp
  · simp only [edges_cons, support_cons, List.nodup_cons] at h⊢
    exact ⟨fun h' => h.1 (fst_mem_support_of_mem_edges p_p h'), p_ih h.2⟩
#align simple_graph.walk.edges_nodup_of_support_nodup SimpleGraph.Walk.edges_nodup_of_support_nodup
-/

/-! ### Trails, paths, circuits, cycles -/


#print SimpleGraph.Walk.IsTrail /-
/-- A *trail* is a walk with no repeating edges. -/
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup
#align simple_graph.walk.is_trail SimpleGraph.Walk.IsTrail
-/

#print SimpleGraph.Walk.IsPath /-
/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) extends
  "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure" :
  Prop where
  support_nodup : p.support.Nodup
#align simple_graph.walk.is_path SimpleGraph.Walk.IsPath
-/

#print SimpleGraph.Walk.IsCircuit /-
/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure IsCircuit {u : V} (p : G.Walk u u) extends
  "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure" :
  Prop where
  ne_nil : p ≠ nil
#align simple_graph.walk.is_circuit SimpleGraph.Walk.IsCircuit
-/

#print SimpleGraph.Walk.IsCycle /-
/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) extends
  "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure" :
  Prop where
  support_nodup : p.support.tail.Nodup
#align simple_graph.walk.is_cycle SimpleGraph.Walk.IsCycle
-/

#print SimpleGraph.Walk.isTrail_def /-
theorem isTrail_def {u v : V} (p : G.Walk u v) : p.IsTrail ↔ p.edges.Nodup :=
  ⟨IsTrail.edges_nodup, fun h => ⟨h⟩⟩
#align simple_graph.walk.is_trail_def SimpleGraph.Walk.isTrail_def
-/

#print SimpleGraph.Walk.isTrail_copy /-
@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl
#align simple_graph.walk.is_trail_copy SimpleGraph.Walk.isTrail_copy
-/

#print SimpleGraph.Walk.IsPath.mk' /-
theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : IsPath p :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩
#align simple_graph.walk.is_path.mk' SimpleGraph.Walk.IsPath.mk'
-/

#print SimpleGraph.Walk.isPath_def /-
theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩
#align simple_graph.walk.is_path_def SimpleGraph.Walk.isPath_def
-/

#print SimpleGraph.Walk.isPath_copy /-
@[simp]
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl
#align simple_graph.walk.is_path_copy SimpleGraph.Walk.isPath_copy
-/

#print SimpleGraph.Walk.isCircuit_def /-
theorem isCircuit_def {u : V} (p : G.Walk u u) : p.IsCircuit ↔ IsTrail p ∧ p ≠ nil :=
  Iff.intro (fun h => ⟨h.1, h.2⟩) fun h => ⟨h.1, h.2⟩
#align simple_graph.walk.is_circuit_def SimpleGraph.Walk.isCircuit_def
-/

#print SimpleGraph.Walk.isCircuit_copy /-
@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit :=
  by
  subst_vars
  rfl
#align simple_graph.walk.is_circuit_copy SimpleGraph.Walk.isCircuit_copy
-/

#print SimpleGraph.Walk.isCycle_def /-
theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ IsTrail p ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
#align simple_graph.walk.is_cycle_def SimpleGraph.Walk.isCycle_def
-/

#print SimpleGraph.Walk.isCycle_copy /-
@[simp]
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') : (p.copy hu hu).IsCycle ↔ p.IsCycle :=
  by
  subst_vars
  rfl
#align simple_graph.walk.is_cycle_copy SimpleGraph.Walk.isCycle_copy
-/

#print SimpleGraph.Walk.IsTrail.nil /-
@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩
#align simple_graph.walk.is_trail.nil SimpleGraph.Walk.IsTrail.nil
-/

#print SimpleGraph.Walk.IsTrail.of_cons /-
theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [is_trail_def]
#align simple_graph.walk.is_trail.of_cons SimpleGraph.Walk.IsTrail.of_cons
-/

#print SimpleGraph.Walk.cons_isTrail_iff /-
@[simp]
theorem cons_isTrail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ ⟦(u, v)⟧ ∉ p.edges := by simp [is_trail_def, and_comm']
#align simple_graph.walk.cons_is_trail_iff SimpleGraph.Walk.cons_isTrail_iff
-/

#print SimpleGraph.Walk.IsTrail.reverse /-
theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [is_trail_def] using h
#align simple_graph.walk.is_trail.reverse SimpleGraph.Walk.IsTrail.reverse
-/

#print SimpleGraph.Walk.reverse_isTrail_iff /-
@[simp]
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try rw [reverse_reverse]
#align simple_graph.walk.reverse_is_trail_iff SimpleGraph.Walk.reverse_isTrail_iff
-/

#print SimpleGraph.Walk.IsTrail.of_append_left /-
theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩
#align simple_graph.walk.is_trail.of_append_left SimpleGraph.Walk.IsTrail.of_append_left
-/

#print SimpleGraph.Walk.IsTrail.of_append_right /-
theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩
#align simple_graph.walk.is_trail.of_append_right SimpleGraph.Walk.IsTrail.of_append_right
-/

#print SimpleGraph.Walk.IsTrail.count_edges_le_one /-
theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e
#align simple_graph.walk.is_trail.count_edges_le_one SimpleGraph.Walk.IsTrail.count_edges_le_one
-/

#print SimpleGraph.Walk.IsTrail.count_edges_eq_one /-
theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he
#align simple_graph.walk.is_trail.count_edges_eq_one SimpleGraph.Walk.IsTrail.count_edges_eq_one
-/

#print SimpleGraph.Walk.IsPath.nil /-
theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by fconstructor <;> simp
#align simple_graph.walk.is_path.nil SimpleGraph.Walk.IsPath.nil
-/

#print SimpleGraph.Walk.IsPath.of_cons /-
theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [is_path_def]
#align simple_graph.walk.is_path.of_cons SimpleGraph.Walk.IsPath.of_cons
-/

#print SimpleGraph.Walk.cons_isPath_iff /-
@[simp]
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp (config := { contextual := true }) [is_path_def]
#align simple_graph.walk.cons_is_path_iff SimpleGraph.Walk.cons_isPath_iff
-/

#print SimpleGraph.Walk.isPath_iff_eq_nil /-
@[simp]
theorem isPath_iff_eq_nil {u : V} (p : G.Walk u u) : p.IsPath ↔ p = nil := by
  cases p <;> simp [is_path.nil]
#align simple_graph.walk.is_path_iff_eq_nil SimpleGraph.Walk.isPath_iff_eq_nil
-/

#print SimpleGraph.Walk.IsPath.reverse /-
theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [is_path_def] using h
#align simple_graph.walk.is_path.reverse SimpleGraph.Walk.IsPath.reverse
-/

#print SimpleGraph.Walk.isPath_reverse_iff /-
@[simp]
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse <;> simp
#align simple_graph.walk.is_path_reverse_iff SimpleGraph.Walk.isPath_reverse_iff
-/

#print SimpleGraph.Walk.IsPath.of_append_left /-
theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath :=
  by
  simp only [is_path_def, support_append]
  exact List.Nodup.of_append_left
#align simple_graph.walk.is_path.of_append_left SimpleGraph.Walk.IsPath.of_append_left
-/

#print SimpleGraph.Walk.IsPath.of_append_right /-
theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath :=
  by
  rw [← is_path_reverse_iff] at h⊢
  rw [reverse_append] at h
  apply h.of_append_left
#align simple_graph.walk.is_path.of_append_right SimpleGraph.Walk.IsPath.of_append_right
-/

#print SimpleGraph.Walk.IsCycle.not_of_nil /-
@[simp]
theorem IsCycle.not_of_nil {u : V} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl
#align simple_graph.walk.is_cycle.not_of_nil SimpleGraph.Walk.IsCycle.not_of_nil
-/

#print SimpleGraph.Walk.cons_isCycle_iff /-
theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ ¬⟦(u, v)⟧ ∈ p.edges :=
  by
  simp only [walk.is_cycle_def, walk.is_path_def, walk.is_trail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.nodup → p.edges.nodup := edges_nodup_of_support_nodup
  tauto
#align simple_graph.walk.cons_is_cycle_iff SimpleGraph.Walk.cons_isCycle_iff
-/

/-! ### About paths -/


instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath :=
  by
  rw [is_path_def]
  infer_instance

#print SimpleGraph.Walk.IsPath.length_lt /-
theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V :=
  by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card
#align simple_graph.walk.is_path.length_lt SimpleGraph.Walk.IsPath.length_lt
-/

/-! ### Walk decompositions -/


section WalkDecomp

variable [DecidableEq V]

#print SimpleGraph.Walk.takeUntil /-
/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil : ∀ {v w : V} (p : G.Walk v w) (u : V) (h : u ∈ p.support), G.Walk v u
  | v, w, nil, u, h => by rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by subst u
    else cons r (take_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id)
#align simple_graph.walk.take_until SimpleGraph.Walk.takeUntil
-/

#print SimpleGraph.Walk.dropUntil /-
/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil : ∀ {v w : V} (p : G.Walk v w) (u : V) (h : u ∈ p.support), G.Walk u w
  | v, w, nil, u, h => by rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else drop_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id
#align simple_graph.walk.drop_until SimpleGraph.Walk.dropUntil
-/

#print SimpleGraph.Walk.take_spec /-
/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p :=
  by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · obtain rfl | h := h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]
#align simple_graph.walk.take_spec SimpleGraph.Walk.take_spec
-/

#print SimpleGraph.Walk.mem_support_iff_exists_append /-
theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w)(r : G.Walk w v), p = q.append r := by
  classical
    constructor
    · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
    · rintro ⟨q, r, rfl⟩
      simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]
#align simple_graph.walk.mem_support_iff_exists_append SimpleGraph.Walk.mem_support_iff_exists_append
-/

#print SimpleGraph.Walk.count_support_takeUntil_eq_one /-
@[simp]
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support.count u = 1 :=
  by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · obtain rfl | h := h
    · simp!
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]
#align simple_graph.walk.count_support_take_until_eq_one SimpleGraph.Walk.count_support_takeUntil_eq_one
-/

#print SimpleGraph.Walk.count_edges_takeUntil_le_one /-
theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count ⟦(u, x)⟧ ≤ 1 :=
  by
  induction' p with u' u' v' w' ha p' ih
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · obtain rfl | h := h
    · simp!
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · rw [Sym2.eq_iff] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih
#align simple_graph.walk.count_edges_take_until_le_one SimpleGraph.Walk.count_edges_takeUntil_le_one
-/

#print SimpleGraph.Walk.takeUntil_copy /-
@[simp]
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h =
      (p.takeUntil u
            (by
              subst_vars
              exact h)).copy
        hv rfl :=
  by
  subst_vars
  rfl
#align simple_graph.walk.take_until_copy SimpleGraph.Walk.takeUntil_copy
-/

#print SimpleGraph.Walk.dropUntil_copy /-
@[simp]
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h =
      (p.dropUntil u
            (by
              subst_vars
              exact h)).copy
        rfl hw :=
  by
  subst_vars
  rfl
#align simple_graph.walk.drop_until_copy SimpleGraph.Walk.dropUntil_copy
-/

#print SimpleGraph.Walk.support_takeUntil_subset /-
theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx =>
  by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx
#align simple_graph.walk.support_take_until_subset SimpleGraph.Walk.support_takeUntil_subset
-/

#print SimpleGraph.Walk.support_dropUntil_subset /-
theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx =>
  by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx
#align simple_graph.walk.support_drop_until_subset SimpleGraph.Walk.support_dropUntil_subset
-/

#print SimpleGraph.Walk.darts_takeUntil_subset /-
theorem darts_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts := fun x hx =>
  by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inl hx
#align simple_graph.walk.darts_take_until_subset SimpleGraph.Walk.darts_takeUntil_subset
-/

#print SimpleGraph.Walk.darts_dropUntil_subset /-
theorem darts_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts := fun x hx =>
  by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inr hx
#align simple_graph.walk.darts_drop_until_subset SimpleGraph.Walk.darts_dropUntil_subset
-/

#print SimpleGraph.Walk.edges_takeUntil_subset /-
theorem edges_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_takeUntil_subset h)
#align simple_graph.walk.edges_take_until_subset SimpleGraph.Walk.edges_takeUntil_subset
-/

#print SimpleGraph.Walk.edges_dropUntil_subset /-
theorem edges_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_dropUntil_subset h)
#align simple_graph.walk.edges_drop_until_subset SimpleGraph.Walk.edges_dropUntil_subset
-/

#print SimpleGraph.Walk.length_takeUntil_le /-
theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length :=
  by
  have := congr_arg walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.le.intro this
#align simple_graph.walk.length_take_until_le SimpleGraph.Walk.length_takeUntil_le
-/

#print SimpleGraph.Walk.length_dropUntil_le /-
theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length :=
  by
  have := congr_arg walk.length (p.take_spec h)
  rw [length_append, add_comm] at this
  exact Nat.le.intro this
#align simple_graph.walk.length_drop_until_le SimpleGraph.Walk.length_dropUntil_le
-/

#print SimpleGraph.Walk.IsTrail.takeUntil /-
protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.take_until SimpleGraph.Walk.IsTrail.takeUntil
-/

#print SimpleGraph.Walk.IsTrail.dropUntil /-
protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.drop_until SimpleGraph.Walk.IsTrail.dropUntil
-/

#print SimpleGraph.Walk.IsPath.takeUntil /-
protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.take_until SimpleGraph.Walk.IsPath.takeUntil
-/

#print SimpleGraph.Walk.IsPath.dropUntil /-
protected theorem IsPath.dropUntil {u v w : V} (p : G.Walk v w) (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.drop_until SimpleGraph.Walk.IsPath.dropUntil
-/

#print SimpleGraph.Walk.rotate /-
/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)
#align simple_graph.walk.rotate SimpleGraph.Walk.rotate
-/

#print SimpleGraph.Walk.support_rotate /-
@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).support.tail ~r c.support.tail :=
  by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]
#align simple_graph.walk.support_rotate SimpleGraph.Walk.support_rotate
-/

#print SimpleGraph.Walk.rotate_darts /-
theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).darts ~r c.darts :=
  by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]
#align simple_graph.walk.rotate_darts SimpleGraph.Walk.rotate_darts
-/

#print SimpleGraph.Walk.rotate_edges /-
theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _
#align simple_graph.walk.rotate_edges SimpleGraph.Walk.rotate_edges
-/

#print SimpleGraph.Walk.IsTrail.rotate /-
protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail :=
  by
  rw [is_trail_def, (c.rotate_edges h).Perm.nodup_iff]
  exact hc.edges_nodup
#align simple_graph.walk.is_trail.rotate SimpleGraph.Walk.IsTrail.rotate
-/

#print SimpleGraph.Walk.IsCircuit.rotate /-
protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit :=
  by
  refine' ⟨hc.to_trail.rotate _, _⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simpa using hn'
#align simple_graph.walk.is_circuit.rotate SimpleGraph.Walk.IsCircuit.rotate
-/

#print SimpleGraph.Walk.IsCycle.rotate /-
protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.support) :
    (c.rotate h).IsCycle := by
  refine' ⟨hc.to_circuit.rotate _, _⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup
#align simple_graph.walk.is_cycle.rotate SimpleGraph.Walk.IsCycle.rotate
-/

end WalkDecomp

#print SimpleGraph.Walk.exists_boundary_dart /-
/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not.
-/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S :=
  by
  induction' p with _ x y w a p' ih
  · exact absurd uS vS
  · by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, Or.inr hd, hcd⟩
    · exact ⟨⟨(x, y), a⟩, Or.inl rfl, uS, h⟩
#align simple_graph.walk.exists_boundary_dart SimpleGraph.Walk.exists_boundary_dart
-/

end Walk

/-! ### Type of paths -/


#print SimpleGraph.Path /-
/-- The type for paths between two vertices. -/
abbrev Path (u v : V) :=
  { p : G.Walk u v // p.IsPath }
#align simple_graph.path SimpleGraph.Path
-/

namespace Path

variable {G G'}

#print SimpleGraph.Path.isPath /-
@[simp]
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath :=
  p.property
#align simple_graph.path.is_path SimpleGraph.Path.isPath
-/

#print SimpleGraph.Path.isTrail /-
@[simp]
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail
#align simple_graph.path.is_trail SimpleGraph.Path.isTrail
-/

#print SimpleGraph.Path.nil /-
/-- The length-0 path at a vertex. -/
@[refl, simps]
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩
#align simple_graph.path.nil SimpleGraph.Path.nil
-/

#print SimpleGraph.Path.singleton /-
/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩
#align simple_graph.path.singleton SimpleGraph.Path.singleton
-/

#print SimpleGraph.Path.mk'_mem_edges_singleton /-
theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    ⟦(u, v)⟧ ∈ (singleton h : G.Walk u v).edges := by simp [singleton]
#align simple_graph.path.mk_mem_edges_singleton SimpleGraph.Path.mk'_mem_edges_singleton
-/

#print SimpleGraph.Path.reverse /-
/-- The reverse of a path is another path.  See also `simple_graph.walk.reverse`. -/
@[symm, simps]
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩
#align simple_graph.path.reverse SimpleGraph.Path.reverse
-/

#print SimpleGraph.Path.count_support_eq_one /-
theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw
#align simple_graph.path.count_support_eq_one SimpleGraph.Path.count_support_eq_one
-/

#print SimpleGraph.Path.count_edges_eq_one /-
theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw
#align simple_graph.path.count_edges_eq_one SimpleGraph.Path.count_edges_eq_one
-/

#print SimpleGraph.Path.nodup_support /-
@[simp]
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property
#align simple_graph.path.nodup_support SimpleGraph.Path.nodup_support
-/

#print SimpleGraph.Path.loop_eq /-
theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil :=
  by
  obtain ⟨_ | _, this⟩ := p
  · rfl
  · simpa
#align simple_graph.path.loop_eq SimpleGraph.Path.loop_eq
-/

#print SimpleGraph.Path.not_mem_edges_of_loop /-
theorem not_mem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} : ¬e ∈ (p : G.Walk v v).edges :=
  by simp [p.loop_eq]
#align simple_graph.path.not_mem_edges_of_loop SimpleGraph.Path.not_mem_edges_of_loop
-/

#print SimpleGraph.Path.cons_isCycle /-
theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : ¬⟦(u, v)⟧ ∈ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [walk.is_cycle_def, walk.cons_is_trail_iff, he]
#align simple_graph.path.cons_is_cycle SimpleGraph.Path.cons_isCycle
-/

end Path

/-! ### Walks to paths -/


namespace Walk

variable {G} [DecidableEq V]

#print SimpleGraph.Walk.bypass /-
/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `simple_graph.walk.bypass_is_path`.
This is packaged up in `simple_graph.walk.to_path`. -/
def bypass : ∀ {u v : V}, G.Walk u v → G.Walk u v
  | u, v, nil => nil
  | u, v, cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then p'.dropUntil u hs else cons ha p'
#align simple_graph.walk.bypass SimpleGraph.Walk.bypass
-/

#print SimpleGraph.Walk.bypass_copy /-
@[simp]
theorem bypass_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv :=
  by
  subst_vars
  rfl
#align simple_graph.walk.bypass_copy SimpleGraph.Walk.bypass_copy
-/

#print SimpleGraph.Walk.bypass_isPath /-
theorem bypass_isPath {u v : V} (p : G.Walk u v) : p.bypass.IsPath :=
  by
  induction p
  · simp!
  · simp only [bypass]
    split_ifs
    · apply is_path.drop_until
      assumption
    · simp [*, cons_is_path_iff]
#align simple_graph.walk.bypass_is_path SimpleGraph.Walk.bypass_isPath
-/

#print SimpleGraph.Walk.length_bypass_le /-
theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length :=
  by
  induction p
  · rfl
  · simp only [bypass]
    split_ifs
    · trans
      apply length_drop_until_le
      rw [length_cons]
      exact le_add_right p_ih
    · rw [length_cons, length_cons]
      exact add_le_add_right p_ih 1
#align simple_graph.walk.length_bypass_le SimpleGraph.Walk.length_bypass_le
-/

#print SimpleGraph.Walk.toPath /-
/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩
#align simple_graph.walk.to_path SimpleGraph.Walk.toPath
-/

#print SimpleGraph.Walk.support_bypass_subset /-
theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.support ⊆ p.support :=
  by
  induction p
  · simp!
  · simp! only
    split_ifs
    · apply List.Subset.trans (support_drop_until_subset _ _)
      apply List.subset_cons_of_subset
      assumption
    · rw [support_cons]
      apply List.cons_subset_cons
      assumption
#align simple_graph.walk.support_bypass_subset SimpleGraph.Walk.support_bypass_subset
-/

#print SimpleGraph.Walk.support_toPath_subset /-
theorem support_toPath_subset {u v : V} (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  support_bypass_subset _
#align simple_graph.walk.support_to_path_subset SimpleGraph.Walk.support_toPath_subset
-/

#print SimpleGraph.Walk.darts_bypass_subset /-
theorem darts_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.darts ⊆ p.darts :=
  by
  induction p
  · simp!
  · simp! only
    split_ifs
    · apply List.Subset.trans (darts_drop_until_subset _ _)
      apply List.subset_cons_of_subset _ p_ih
    · rw [darts_cons]
      exact List.cons_subset_cons _ p_ih
#align simple_graph.walk.darts_bypass_subset SimpleGraph.Walk.darts_bypass_subset
-/

#print SimpleGraph.Walk.edges_bypass_subset /-
theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subset _ p.darts_bypass_subset
#align simple_graph.walk.edges_bypass_subset SimpleGraph.Walk.edges_bypass_subset
-/

#print SimpleGraph.Walk.darts_toPath_subset /-
theorem darts_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _
#align simple_graph.walk.darts_to_path_subset SimpleGraph.Walk.darts_toPath_subset
-/

#print SimpleGraph.Walk.edges_toPath_subset /-
theorem edges_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _
#align simple_graph.walk.edges_to_path_subset SimpleGraph.Walk.edges_toPath_subset
-/

end Walk

/-! ### Mapping paths -/


namespace Walk

variable {G G' G''}

#print SimpleGraph.Walk.map /-
/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') : ∀ {u v : V}, G.Walk u v → G'.Walk (f u) (f v)
  | _, _, nil => nil
  | _, _, cons h p => cons (f.map_adj h) (map p)
#align simple_graph.walk.map SimpleGraph.Walk.map
-/

variable (f : G →g G') (f' : G' →g G'') {u v u' v' : V} (p : G.Walk u v)

#print SimpleGraph.Walk.map_nil /-
@[simp]
theorem map_nil : (nil : G.Walk u u).map f = nil :=
  rfl
#align simple_graph.walk.map_nil SimpleGraph.Walk.map_nil
-/

#print SimpleGraph.Walk.map_cons /-
@[simp]
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) :=
  rfl
#align simple_graph.walk.map_cons SimpleGraph.Walk.map_cons
-/

#print SimpleGraph.Walk.map_copy /-
@[simp]
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (by rw [hu]) (by rw [hv]) :=
  by
  subst_vars
  rfl
#align simple_graph.walk.map_copy SimpleGraph.Walk.map_copy
-/

/- warning: simple_graph.walk.map_id -> SimpleGraph.Walk.map_id is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v), Eq.{succ u1} (SimpleGraph.Walk.{u1} V G (coeFn.{succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V G G) (fun (_x : RelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G)) => V -> V) (RelHom.hasCoeToFun.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Hom.id.{u1} V G) u) (coeFn.{succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V G G) (fun (_x : RelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G)) => V -> V) (RelHom.hasCoeToFun.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Hom.id.{u1} V G) v)) (SimpleGraph.Walk.map.{u1, u1} V V G G (SimpleGraph.Hom.id.{u1} V G) u v p) p
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V}, (SimpleGraph.Walk.{u1} V G u v) -> (forall (p : SimpleGraph.Walk.{u1} V G u v), Eq.{succ u1} (SimpleGraph.Walk.{u1} V G (FunLike.coe.{succ u1, succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V G G) V (fun (a : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V) a) (RelHomClass.toFunLike.{u1, u1, u1} (SimpleGraph.Hom.{u1, u1} V V G G) V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G) (RelHom.instRelHomClassRelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Hom.id.{u1} V G) u) (FunLike.coe.{succ u1, succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V G G) V (fun (a : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V) a) (RelHomClass.toFunLike.{u1, u1, u1} (SimpleGraph.Hom.{u1, u1} V V G G) V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G) (RelHom.instRelHomClassRelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Hom.id.{u1} V G) v)) (SimpleGraph.Walk.map.{u1, u1} V V G G (SimpleGraph.Hom.id.{u1} V G) u v p) p)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.map_id SimpleGraph.Walk.map_idₓ'. -/
@[simp]
theorem map_id (p : G.Walk u v) : p.map Hom.id = p := by induction p <;> simp [*]
#align simple_graph.walk.map_id SimpleGraph.Walk.map_id

#print SimpleGraph.Walk.map_map /-
@[simp]
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by induction p <;> simp [*]
#align simple_graph.walk.map_map SimpleGraph.Walk.map_map
-/

#print SimpleGraph.Walk.map_eq_of_eq /-
/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
to work with equality of graph homomorphisms is a necessary evil. -/
theorem map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
    p.map f = (p.map f').copy (by rw [h]) (by rw [h]) :=
  by
  subst_vars
  rfl
#align simple_graph.walk.map_eq_of_eq SimpleGraph.Walk.map_eq_of_eq
-/

#print SimpleGraph.Walk.map_eq_nil_iff /-
@[simp]
theorem map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil := by cases p <;> simp
#align simple_graph.walk.map_eq_nil_iff SimpleGraph.Walk.map_eq_nil_iff
-/

#print SimpleGraph.Walk.length_map /-
@[simp]
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]
#align simple_graph.walk.length_map SimpleGraph.Walk.length_map
-/

#print SimpleGraph.Walk.map_append /-
theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]
#align simple_graph.walk.map_append SimpleGraph.Walk.map_append
-/

#print SimpleGraph.Walk.reverse_map /-
@[simp]
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]
#align simple_graph.walk.reverse_map SimpleGraph.Walk.reverse_map
-/

#print SimpleGraph.Walk.support_map /-
@[simp]
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]
#align simple_graph.walk.support_map SimpleGraph.Walk.support_map
-/

#print SimpleGraph.Walk.darts_map /-
@[simp]
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]
#align simple_graph.walk.darts_map SimpleGraph.Walk.darts_map
-/

#print SimpleGraph.Walk.edges_map /-
@[simp]
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by induction p <;> simp [*]
#align simple_graph.walk.edges_map SimpleGraph.Walk.edges_map
-/

variable {p f}

#print SimpleGraph.Walk.map_isPath_of_injective /-
theorem map_isPath_of_injective (hinj : Function.Injective f) (hp : p.IsPath) : (p.map f).IsPath :=
  by
  induction' p with w u v w huv hvw ih
  · simp
  · rw [walk.cons_is_path_iff] at hp
    simp [ih hp.1]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx
#align simple_graph.walk.map_is_path_of_injective SimpleGraph.Walk.map_isPath_of_injective
-/

#print SimpleGraph.Walk.IsPath.of_map /-
protected theorem IsPath.of_map {f : G →g G'} (hp : (p.map f).IsPath) : p.IsPath :=
  by
  induction' p with w u v w huv hvw ih
  · simp
  · rw [map_cons, walk.cons_is_path_iff, support_map] at hp
    rw [walk.cons_is_path_iff]
    cases' hp with hp1 hp2
    refine' ⟨ih hp1, _⟩
    contrapose! hp2
    exact List.mem_map_of_mem f hp2
#align simple_graph.walk.is_path.of_map SimpleGraph.Walk.IsPath.of_map
-/

#print SimpleGraph.Walk.map_isPath_iff_of_injective /-
theorem map_isPath_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_isPath_of_injective hinj⟩
#align simple_graph.walk.map_is_path_iff_of_injective SimpleGraph.Walk.map_isPath_iff_of_injective
-/

#print SimpleGraph.Walk.map_isTrail_iff_of_injective /-
theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail :=
  by
  induction' p with w u v w huv hvw ih
  · simp
  · rw [map_cons, cons_is_trail_iff, cons_is_trail_iff, edges_map]
    change _ ∧ Sym2.map f ⟦(u, v)⟧ ∉ _ ↔ _
    rw [List.mem_map_of_injective (Sym2.map.injective hinj)]
    exact and_congr_left' ih
#align simple_graph.walk.map_is_trail_iff_of_injective SimpleGraph.Walk.map_isTrail_iff_of_injective
-/

alias map_is_trail_iff_of_injective ↔ _ map_is_trail_of_injective
#align simple_graph.walk.map_is_trail_of_injective SimpleGraph.Walk.map_isTrail_of_injective

#print SimpleGraph.Walk.map_isCycle_iff_of_injective /-
theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [is_cycle_def, is_cycle_def, map_is_trail_iff_of_injective hinj, Ne.def, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]
#align simple_graph.walk.map_is_cycle_iff_of_injective SimpleGraph.Walk.map_isCycle_iff_of_injective
-/

alias map_is_cycle_iff_of_injective ↔ _ map_is_cycle_of_injective
#align simple_graph.walk.map_is_cycle_of_injective SimpleGraph.Walk.map_isCycle_of_injective

variable (p f)

#print SimpleGraph.Walk.map_injective_of_injective /-
theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : G.Walk u v → G'.Walk (f u) (f v)) :=
  by
  intro p p' h
  induction' p with _ _ _ _ _ _ ih generalizing p'
  · cases p'
    · rfl
    simpa using h
  · induction p'
    · simpa using h
    · simp only [map_cons] at h
      cases hinj h.1
      simp only [eq_self_iff_true, heq_iff_eq, true_and_iff]
      apply ih
      simpa using h.2
#align simple_graph.walk.map_injective_of_injective SimpleGraph.Walk.map_injective_of_injective
-/

#print SimpleGraph.Walk.mapLe /-
/-- The specialization of `simple_graph.walk.map` for mapping walks to supergraphs. -/
@[reducible]
def mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v) : G'.Walk u v :=
  p.map (Hom.mapSpanningSubgraphs h)
#align simple_graph.walk.map_le SimpleGraph.Walk.mapLe
-/

#print SimpleGraph.Walk.mapLe_isTrail /-
@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_trail SimpleGraph.Walk.mapLe_isTrail
-/

alias map_le_is_trail ↔ is_trail.of_map_le is_trail.map_le
#align simple_graph.walk.is_trail.of_map_le SimpleGraph.Walk.IsTrail.of_mapLe
#align simple_graph.walk.is_trail.map_le SimpleGraph.Walk.IsTrail.mapLe

#print SimpleGraph.Walk.mapLe_isPath /-
@[simp]
theorem mapLe_isPath {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  map_isPath_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_path SimpleGraph.Walk.mapLe_isPath
-/

alias map_le_is_path ↔ is_path.of_map_le is_path.map_le
#align simple_graph.walk.is_path.of_map_le SimpleGraph.Walk.IsPath.of_mapLe
#align simple_graph.walk.is_path.map_le SimpleGraph.Walk.IsPath.mapLe

#print SimpleGraph.Walk.mapLe_isCycle /-
@[simp]
theorem mapLe_isCycle {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_cycle SimpleGraph.Walk.mapLe_isCycle
-/

alias map_le_is_cycle ↔ is_cycle.of_map_le is_cycle.map_le
#align simple_graph.walk.is_cycle.of_map_le SimpleGraph.Walk.IsCycle.of_mapLe
#align simple_graph.walk.is_cycle.map_le SimpleGraph.Walk.IsCycle.mapLe

end Walk

namespace Path

variable {G G'}

#print SimpleGraph.Path.map /-
/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_isPath_of_injective hinj p.2⟩
#align simple_graph.path.map SimpleGraph.Path.map
-/

#print SimpleGraph.Path.map_injective /-
theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) :=
  by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.coe_mk] at h
  simp [walk.map_injective_of_injective hinj u v h]
#align simple_graph.path.map_injective SimpleGraph.Path.map_injective
-/

/- warning: simple_graph.path.map_embedding -> SimpleGraph.Path.mapEmbedding is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} (f : SimpleGraph.Embedding.{u1, u2} V V' G G') {u : V} {v : V}, (SimpleGraph.Path.{u1} V G u v) -> (SimpleGraph.Path.{u2} V' G' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (fun (_x : RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelEmbedding.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f u) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (fun (_x : RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelEmbedding.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f v))
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} (f : SimpleGraph.Embedding.{u1, u2} V V' G G') {u : V} {v : V}, (SimpleGraph.Path.{u1} V G u v) -> (SimpleGraph.Path.{u2} V' G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelEmbedding.instRelHomClassRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) f u) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelEmbedding.instRelHomClassRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) f v))
Case conversion may be inaccurate. Consider using '#align simple_graph.path.map_embedding SimpleGraph.Path.mapEmbeddingₓ'. -/
/-- Given a graph embedding, map paths to paths. -/
@[simps]
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.Injective p
#align simple_graph.path.map_embedding SimpleGraph.Path.mapEmbedding

/- warning: simple_graph.path.map_embedding_injective -> SimpleGraph.Path.mapEmbedding_injective is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} (f : SimpleGraph.Embedding.{u1, u2} V V' G G') (u : V) (v : V), Function.Injective.{succ u1, succ u2} (SimpleGraph.Path.{u1} V G u v) (SimpleGraph.Path.{u2} V' G' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (fun (_x : RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelEmbedding.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f u) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (fun (_x : RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelEmbedding.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f v)) (SimpleGraph.Path.mapEmbedding.{u1, u2} V V' G G' f u v)
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} (f : SimpleGraph.Embedding.{u1, u2} V V' G G') (u : V) (v : V), Function.Injective.{succ u1, succ u2} (SimpleGraph.Path.{u1} V G u v) (SimpleGraph.Path.{u2} V' G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelEmbedding.instRelHomClassRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) f u) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Embedding.{u1, u2} V V' G G') V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelEmbedding.instRelHomClassRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) f v)) (SimpleGraph.Path.mapEmbedding.{u1, u2} V V' G G' f u v)
Case conversion may be inaccurate. Consider using '#align simple_graph.path.map_embedding_injective SimpleGraph.Path.mapEmbedding_injectiveₓ'. -/
theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.Injective u v
#align simple_graph.path.map_embedding_injective SimpleGraph.Path.mapEmbedding_injective

end Path

/-! ### Transferring between graphs -/


namespace Walk

variable {G}

/- warning: simple_graph.walk.transfer -> SimpleGraph.Walk.transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) (H : SimpleGraph.{u1} V), (forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))) -> (SimpleGraph.Walk.{u1} V H u v)
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) (H : SimpleGraph.{u1} V), (forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))) -> (SimpleGraph.Walk.{u1} V H u v)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.transfer SimpleGraph.Walk.transferₓ'. -/
/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[protected, simp]
def transfer :
    ∀ {u v : V} (p : G.Walk u v) (H : SimpleGraph V)
      (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSetEmbedding), H.Walk u v
  | _, _, walk.nil, H, h => Walk.nil
  | _, _, walk.cons' u v w a p, H, h =>
    Walk.cons (h (⟦(u, v)⟧ : Sym2 V) (by simp)) (p.transfer H fun e he => h e (by simp [he]))
#align simple_graph.walk.transfer SimpleGraph.Walk.transfer

variable {u v w : V} (p : G.Walk u v) (q : G.Walk v w) {H : SimpleGraph V}
  (hp : ∀ e, e ∈ p.edges → e ∈ H.edgeSetEmbedding) (hq : ∀ e, e ∈ q.edges → e ∈ H.edgeSetEmbedding)

#print SimpleGraph.Walk.transfer_self /-
theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp only [*, transfer, eq_self_iff_true, heq_iff_eq, and_self_iff]
#align simple_graph.walk.transfer_self SimpleGraph.Walk.transfer_self
-/

/- warning: simple_graph.walk.transfer_eq_map_of_le -> SimpleGraph.Walk.transfer_eq_map_of_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))) (GH : LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V) G H), Eq.{succ u1} (SimpleGraph.Walk.{u1} V H u v) (SimpleGraph.Walk.transfer.{u1} V G u v p H hp) (SimpleGraph.Walk.map.{u1, u1} V V G H (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V G H GH) u v p)
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))) (GH : LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.instLESimpleGraph.{u1} V) G H), Eq.{succ u1} (SimpleGraph.Walk.{u1} V H u v) (SimpleGraph.Walk.transfer.{u1} V G u v p H hp) (SimpleGraph.Walk.map.{u1, u1} V V G H (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V G H GH) u v p)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.transfer_eq_map_of_le SimpleGraph.Walk.transfer_eq_map_of_leₓ'. -/
theorem transfer_eq_map_of_le (GH : G ≤ H) :
    p.transfer H hp = p.map (SimpleGraph.Hom.mapSpanningSubgraphs GH) := by
  induction p <;>
    simp only [*, transfer, map_cons, hom.map_spanning_subgraphs_apply, eq_self_iff_true,
      heq_iff_eq, and_self_iff, map_nil]
#align simple_graph.walk.transfer_eq_map_of_le SimpleGraph.Walk.transfer_eq_map_of_le

/- warning: simple_graph.walk.edges_transfer -> SimpleGraph.Walk.edges_transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))), Eq.{succ u1} (List.{u1} (Sym2.{u1} V)) (SimpleGraph.Walk.edges.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.edges.{u1} V G u v p)
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))), Eq.{succ u1} (List.{u1} (Sym2.{u1} V)) (SimpleGraph.Walk.edges.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.edges.{u1} V G u v p)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.edges_transfer SimpleGraph.Walk.edges_transferₓ'. -/
@[simp]
theorem edges_transfer : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp only [*, transfer, edges_nil, edges_cons, eq_self_iff_true, and_self_iff]
#align simple_graph.walk.edges_transfer SimpleGraph.Walk.edges_transfer

/- warning: simple_graph.walk.support_transfer -> SimpleGraph.Walk.support_transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))), Eq.{succ u1} (List.{u1} V) (SimpleGraph.Walk.support.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.support.{u1} V G u v p)
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))), Eq.{succ u1} (List.{u1} V) (SimpleGraph.Walk.support.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.support.{u1} V G u v p)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.support_transfer SimpleGraph.Walk.support_transferₓ'. -/
@[simp]
theorem support_transfer : (p.transfer H hp).support = p.support := by
  induction p <;> simp only [*, transfer, eq_self_iff_true, and_self_iff, support_nil, support_cons]
#align simple_graph.walk.support_transfer SimpleGraph.Walk.support_transfer

/- warning: simple_graph.walk.length_transfer -> SimpleGraph.Walk.length_transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))), Eq.{1} Nat (SimpleGraph.Walk.length.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.length.{u1} V G u v p)
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} (p : SimpleGraph.Walk.{u1} V G u v) {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))), Eq.{1} Nat (SimpleGraph.Walk.length.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp)) (SimpleGraph.Walk.length.{u1} V G u v p)
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.length_transfer SimpleGraph.Walk.length_transferₓ'. -/
@[simp]
theorem length_transfer : (p.transfer H hp).length = p.length := by induction p <;> simp [*]
#align simple_graph.walk.length_transfer SimpleGraph.Walk.length_transfer

variable {p}

/- warning: simple_graph.walk.is_path.transfer -> SimpleGraph.Walk.IsPath.transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} {p : SimpleGraph.Walk.{u1} V G u v} {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))), (SimpleGraph.Walk.IsPath.{u1} V G u v p) -> (SimpleGraph.Walk.IsPath.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} {p : SimpleGraph.Walk.{u1} V G u v} {H : SimpleGraph.{u1} V} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u v p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))), (SimpleGraph.Walk.IsPath.{u1} V G u v p) -> (SimpleGraph.Walk.IsPath.{u1} V H u v (SimpleGraph.Walk.transfer.{u1} V G u v p H hp))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.is_path.transfer SimpleGraph.Walk.IsPath.transferₓ'. -/
protected theorem IsPath.transfer (pp : p.IsPath) : (p.transfer H hp).IsPath :=
  by
  induction p <;> simp only [transfer, is_path.nil, cons_is_path_iff, support_transfer] at pp⊢
  · tauto
#align simple_graph.walk.is_path.transfer SimpleGraph.Walk.IsPath.transfer

/- warning: simple_graph.walk.is_cycle.transfer -> SimpleGraph.Walk.IsCycle.transfer is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {H : SimpleGraph.{u1} V} {p : SimpleGraph.Walk.{u1} V G u u}, (SimpleGraph.Walk.IsCycle.{u1} V G u p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u u p)) -> (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) H))), SimpleGraph.Walk.IsCycle.{u1} V H u (SimpleGraph.Walk.transfer.{u1} V G u u p H hp))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {H : SimpleGraph.{u1} V} {p : SimpleGraph.Walk.{u1} V G u u}, (SimpleGraph.Walk.IsCycle.{u1} V G u p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u u p)) -> (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V H))), SimpleGraph.Walk.IsCycle.{u1} V H u (SimpleGraph.Walk.transfer.{u1} V G u u p H hp))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.is_cycle.transfer SimpleGraph.Walk.IsCycle.transferₓ'. -/
protected theorem IsCycle.transfer {p : G.Walk u u} (pc : p.IsCycle) (hp) :
    (p.transfer H hp).IsCycle :=
  by
  cases p <;>
    simp only [transfer, is_cycle.not_of_nil, cons_is_cycle_iff, transfer, edges_transfer] at pc⊢
  · exact pc
  · exact ⟨pc.left.transfer _, pc.right⟩
#align simple_graph.walk.is_cycle.transfer SimpleGraph.Walk.IsCycle.transfer

variable (p)

/- warning: simple_graph.walk.transfer_transfer -> SimpleGraph.Walk.transfer_transfer is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.transfer_transfer SimpleGraph.Walk.transfer_transferₓ'. -/
@[simp]
theorem transfer_transfer {K : SimpleGraph V} (hp' : ∀ e, e ∈ p.edges → e ∈ K.edgeSetEmbedding) :
    (p.transfer H hp).transfer K
        (by
          rw [p.edges_transfer hp]
          exact hp') =
      p.transfer K hp' :=
  by
  induction p <;> simp only [transfer, eq_self_iff_true, heq_iff_eq, true_and_iff]
  apply p_ih
#align simple_graph.walk.transfer_transfer SimpleGraph.Walk.transfer_transfer

/- warning: simple_graph.walk.transfer_append -> SimpleGraph.Walk.transfer_append is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.transfer_append SimpleGraph.Walk.transfer_appendₓ'. -/
@[simp]
theorem transfer_append (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => by
            apply hpq
            simp [he]).append
        (q.transfer H fun e he => by
          apply hpq
          simp [he]) :=
  by
  induction p <;>
    simp only [transfer, nil_append, cons_append, eq_self_iff_true, heq_iff_eq, true_and_iff]
  apply p_ih
#align simple_graph.walk.transfer_append SimpleGraph.Walk.transfer_append

/- warning: simple_graph.walk.reverse_transfer -> SimpleGraph.Walk.reverse_transfer is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.reverse_transfer SimpleGraph.Walk.reverse_transferₓ'. -/
@[simp]
theorem reverse_transfer :
    (p.transfer H hp).reverse =
      p.reverse.transfer H
        (by
          simp only [edges_reverse, List.mem_reverse']
          exact hp) :=
  by
  induction p <;> simp only [*, transfer_append, transfer, reverse_nil, reverse_cons]
  rfl
#align simple_graph.walk.reverse_transfer SimpleGraph.Walk.reverse_transfer

end Walk

/-! ## Deleting edges -/


namespace Walk

variable {G}

#print SimpleGraph.Walk.toDeleteEdges /-
/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
@[reducible]
def toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w) (hp : ∀ e, e ∈ p.edges → ¬e ∈ s) :
    (G.deleteEdges s).Walk v w :=
  p.transfer _
    (by
      simp only [edge_set_delete_edges, Set.mem_diff]
      exact fun e ep => ⟨edges_subset_edge_set p ep, hp e ep⟩)
#align simple_graph.walk.to_delete_edges SimpleGraph.Walk.toDeleteEdges
-/

#print SimpleGraph.Walk.toDeleteEdges_nil /-
@[simp]
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : G.Walk v v).toDeleteEdges s hp = Walk.nil :=
  rfl
#align simple_graph.walk.to_delete_edges_nil SimpleGraph.Walk.toDeleteEdges_nil
-/

#print SimpleGraph.Walk.toDeleteEdges_cons /-
@[simp]
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons ⟨h, hp _ (Or.inl rfl)⟩ (p.toDeleteEdges s fun _ he => hp _ <| Or.inr he) :=
  rfl
#align simple_graph.walk.to_delete_edges_cons SimpleGraph.Walk.toDeleteEdges_cons
-/

#print SimpleGraph.Walk.toDeleteEdge /-
/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `simple_graph.walk.to_delete_edges`. -/
abbrev toDeleteEdge {v w : V} (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) :
    (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} fun e' => by
    contrapose!
    simp (config := { contextual := true }) [hp]
#align simple_graph.walk.to_delete_edge SimpleGraph.Walk.toDeleteEdge
-/

/- warning: simple_graph.walk.map_to_delete_edges_eq -> SimpleGraph.Walk.map_toDeleteEdges_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} (s : Set.{u1} (Sym2.{u1} V)) {v : V} {w : V} {p : SimpleGraph.Walk.{u1} V G v w} (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G v w p)) -> (Not (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e s))), Eq.{succ u1} (SimpleGraph.Walk.{u1} V G (coeFn.{succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G s) G) (fun (_x : RelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G s)) (SimpleGraph.Adj.{u1} V G)) => V -> V) (RelHom.hasCoeToFun.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G s)) (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G s) G (SimpleGraph.deleteEdges_le.{u1} V G s)) v) (coeFn.{succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G s) G) (fun (_x : RelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G s)) (SimpleGraph.Adj.{u1} V G)) => V -> V) (RelHom.hasCoeToFun.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G s)) (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G s) G (SimpleGraph.deleteEdges_le.{u1} V G s)) w)) (SimpleGraph.Walk.map.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G s) G (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G s) G (SimpleGraph.deleteEdges_le.{u1} V G s)) v w (SimpleGraph.Walk.toDeleteEdges.{u1} V G s v w p hp)) p
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {s : V} {v : V} (w : Set.{u1} (Sym2.{u1} V)) {p : SimpleGraph.Walk.{u1} V G s v} (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G s v p)) -> (Not (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e w))), Eq.{succ u1} (SimpleGraph.Walk.{u1} V G (FunLike.coe.{succ u1, succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G w) G) V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V) _x) (RelHomClass.toFunLike.{u1, u1, u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G w) G) V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G w)) (SimpleGraph.Adj.{u1} V G) (RelHom.instRelHomClassRelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G w)) (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G w) G (SimpleGraph.deleteEdges_le.{u1} V G w)) s) (FunLike.coe.{succ u1, succ u1, succ u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G w) G) V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V) _x) (RelHomClass.toFunLike.{u1, u1, u1} (SimpleGraph.Hom.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G w) G) V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G w)) (SimpleGraph.Adj.{u1} V G) (RelHom.instRelHomClassRelHom.{u1, u1} V V (SimpleGraph.Adj.{u1} V (SimpleGraph.deleteEdges.{u1} V G w)) (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G w) G (SimpleGraph.deleteEdges_le.{u1} V G w)) v)) (SimpleGraph.Walk.map.{u1, u1} V V (SimpleGraph.deleteEdges.{u1} V G w) G (SimpleGraph.Hom.mapSpanningSubgraphs.{u1} V (SimpleGraph.deleteEdges.{u1} V G w) G (SimpleGraph.deleteEdges_le.{u1} V G w)) s v (SimpleGraph.Walk.toDeleteEdges.{u1} V G w s v p hp)) p
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.map_to_delete_edges_eq SimpleGraph.Walk.map_toDeleteEdges_eqₓ'. -/
@[simp]
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {v w : V} {p : G.Walk v w} (hp) :
    Walk.map (Hom.mapSpanningSubgraphs (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_of_le, transfer_transfer, transfer_self]
#align simple_graph.walk.map_to_delete_edges_eq SimpleGraph.Walk.map_toDeleteEdges_eq

/- warning: simple_graph.walk.is_path.to_delete_edges -> SimpleGraph.Walk.IsPath.toDeleteEdges is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} (s : Set.{u1} (Sym2.{u1} V)) {v : V} {w : V} {p : SimpleGraph.Walk.{u1} V G v w}, (SimpleGraph.Walk.IsPath.{u1} V G v w p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G v w p)) -> (Not (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e s))), SimpleGraph.Walk.IsPath.{u1} V (SimpleGraph.deleteEdges.{u1} V G s) v w (SimpleGraph.Walk.toDeleteEdges.{u1} V G s v w p hp))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {s : V} {v : V} (w : Set.{u1} (Sym2.{u1} V)) {p : SimpleGraph.Walk.{u1} V G s v}, (SimpleGraph.Walk.IsPath.{u1} V G s v p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G s v p)) -> (Not (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e w))), SimpleGraph.Walk.IsPath.{u1} V (SimpleGraph.deleteEdges.{u1} V G w) s v (SimpleGraph.Walk.toDeleteEdges.{u1} V G w s v p hp))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.is_path.to_delete_edges SimpleGraph.Walk.IsPath.toDeleteEdgesₓ'. -/
protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V)) {v w : V} {p : G.Walk v w} (h : p.IsPath)
    (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _
#align simple_graph.walk.is_path.to_delete_edges SimpleGraph.Walk.IsPath.toDeleteEdges

/- warning: simple_graph.walk.is_cycle.to_delete_edges -> SimpleGraph.Walk.IsCycle.toDeleteEdges is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} (s : Set.{u1} (Sym2.{u1} V)) {v : V} {p : SimpleGraph.Walk.{u1} V G v v}, (SimpleGraph.Walk.IsCycle.{u1} V G v p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G v v p)) -> (Not (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e s))), SimpleGraph.Walk.IsCycle.{u1} V (SimpleGraph.deleteEdges.{u1} V G s) v (SimpleGraph.Walk.toDeleteEdges.{u1} V G s v v p hp))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {s : V} (v : Set.{u1} (Sym2.{u1} V)) {p : SimpleGraph.Walk.{u1} V G s s}, (SimpleGraph.Walk.IsCycle.{u1} V G s p) -> (forall (hp : forall (e : Sym2.{u1} V), (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G s s p)) -> (Not (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e v))), SimpleGraph.Walk.IsCycle.{u1} V (SimpleGraph.deleteEdges.{u1} V G v) s (SimpleGraph.Walk.toDeleteEdges.{u1} V G v s s p hp))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.is_cycle.to_delete_edges SimpleGraph.Walk.IsCycle.toDeleteEdgesₓ'. -/
protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V)) {v : V} {p : G.Walk v v} (h : p.IsCycle)
    (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _
#align simple_graph.walk.is_cycle.to_delete_edges SimpleGraph.Walk.IsCycle.toDeleteEdges

/- warning: simple_graph.walk.to_delete_edges_copy -> SimpleGraph.Walk.toDeleteEdges_copy is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.to_delete_edges_copy SimpleGraph.Walk.toDeleteEdges_copyₓ'. -/
@[simp]
theorem toDeleteEdges_copy (s : Set (Sym2 V)) {u v u' v'} (p : G.Walk u v) (hu : u = u')
    (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s
            (by
              subst_vars
              exact h)).copy
        hu hv :=
  by
  subst_vars
  rfl
#align simple_graph.walk.to_delete_edges_copy SimpleGraph.Walk.toDeleteEdges_copy

end Walk

/-! ## `reachable` and `connected` -/


#print SimpleGraph.Reachable /-
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `relation.refl_trans_gen` of `G.adj`.
See `simple_graph.reachable_iff_refl_trans_gen`. -/
def Reachable (u v : V) : Prop :=
  Nonempty (G.Walk u v)
#align simple_graph.reachable SimpleGraph.Reachable
-/

variable {G}

#print SimpleGraph.reachable_iff_nonempty_univ /-
theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty
#align simple_graph.reachable_iff_nonempty_univ SimpleGraph.reachable_iff_nonempty_univ
-/

#print SimpleGraph.Reachable.elim /-
protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v) (hp : G.Walk u v → p) :
    p :=
  Nonempty.elim h hp
#align simple_graph.reachable.elim SimpleGraph.Reachable.elim
-/

#print SimpleGraph.Reachable.elim_path /-
protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath
#align simple_graph.reachable.elim_path SimpleGraph.Reachable.elim_path
-/

#print SimpleGraph.Walk.reachable /-
protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩
#align simple_graph.walk.reachable SimpleGraph.Walk.reachable
-/

#print SimpleGraph.Adj.reachable /-
protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.Reachable
#align simple_graph.adj.reachable SimpleGraph.Adj.reachable
-/

#print SimpleGraph.Reachable.refl /-
@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u :=
  by
  fconstructor
  rfl
#align simple_graph.reachable.refl SimpleGraph.Reachable.refl
-/

#print SimpleGraph.Reachable.rfl /-
protected theorem Reachable.rfl {u : V} : G.Reachable u u :=
  Reachable.refl _
#align simple_graph.reachable.rfl SimpleGraph.Reachable.rfl
-/

#print SimpleGraph.Reachable.symm /-
@[symm]
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩
#align simple_graph.reachable.symm SimpleGraph.Reachable.symm
-/

#print SimpleGraph.reachable_comm /-
theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩
#align simple_graph.reachable_comm SimpleGraph.reachable_comm
-/

#print SimpleGraph.Reachable.trans /-
@[trans]
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
#align simple_graph.reachable.trans SimpleGraph.Reachable.trans
-/

#print SimpleGraph.reachable_iff_reflTransGen /-
theorem reachable_iff_reflTransGen (u v : V) : G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v :=
  by
  constructor
  · rintro ⟨h⟩
    induction h
    · rfl
    · exact (Relation.ReflTransGen.single h_h).trans h_ih
  · intro h
    induction' h with _ _ _ ha hr
    · rfl
    · exact reachable.trans hr ⟨walk.cons ha walk.nil⟩
#align simple_graph.reachable_iff_refl_trans_gen SimpleGraph.reachable_iff_reflTransGen
-/

/- warning: simple_graph.reachable.map -> SimpleGraph.Reachable.map is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} (f : SimpleGraph.Hom.{u1, u2} V V' G G') {u : V} {v : V}, (SimpleGraph.Reachable.{u1} V G u v) -> (SimpleGraph.Reachable.{u2} V' G' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Hom.{u1, u2} V V' G G') (fun (_x : RelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelHom.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f u) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Hom.{u1, u2} V V' G G') (fun (_x : RelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelHom.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) f v))
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : V} {G' : V} {f : SimpleGraph.{u1} V} {u : SimpleGraph.{u2} V'} (v : SimpleGraph.Hom.{u1, u2} V V' f u), (SimpleGraph.Reachable.{u1} V f G G') -> (SimpleGraph.Reachable.{u2} V' u (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Hom.{u1, u2} V V' f u) V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Hom.{u1, u2} V V' f u) V V' (SimpleGraph.Adj.{u1} V f) (SimpleGraph.Adj.{u2} V' u) (RelHom.instRelHomClassRelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V f) (SimpleGraph.Adj.{u2} V' u))) v G) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SimpleGraph.Hom.{u1, u2} V V' f u) V (fun (_x : V) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : V) => V') _x) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (SimpleGraph.Hom.{u1, u2} V V' f u) V V' (SimpleGraph.Adj.{u1} V f) (SimpleGraph.Adj.{u2} V' u) (RelHom.instRelHomClassRelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V f) (SimpleGraph.Adj.{u2} V' u))) v G'))
Case conversion may be inaccurate. Consider using '#align simple_graph.reachable.map SimpleGraph.Reachable.mapₓ'. -/
protected theorem Reachable.map {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G') {u v : V}
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩
#align simple_graph.reachable.map SimpleGraph.Reachable.map

/- warning: simple_graph.iso.reachable_iff -> SimpleGraph.Iso.reachable_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {u : V} {v : V}, Iff (SimpleGraph.Reachable.{u2} V' G' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (fun (_x : RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelIso.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) φ u) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (fun (_x : RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelIso.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) φ v)) (SimpleGraph.Reachable.{u1} V G u v)
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {u : V} {v : V}, Iff (SimpleGraph.Reachable.{u2} V' G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V (fun (_x : V) => V') (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.instRelHomClassRelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) φ u) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V (fun (_x : V) => V') (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.instRelHomClassRelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) φ v)) (SimpleGraph.Reachable.{u1} V G u v)
Case conversion may be inaccurate. Consider using '#align simple_graph.iso.reachable_iff SimpleGraph.Iso.reachable_iffₓ'. -/
theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩
#align simple_graph.iso.reachable_iff SimpleGraph.Iso.reachable_iff

/- warning: simple_graph.iso.symm_apply_reachable -> SimpleGraph.Iso.symm_apply_reachable is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {u : V} {v : V'}, Iff (SimpleGraph.Reachable.{u1} V G (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SimpleGraph.Iso.{u2, u1} V' V G' G) (fun (_x : RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) => V' -> V) (RelIso.hasCoeToFun.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Iso.symm.{u1, u2} V V' G G' φ) v) u) (SimpleGraph.Reachable.{u2} V' G' v (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (fun (_x : RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelIso.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) φ u))
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {u : V} {v : V'}, Iff (SimpleGraph.Reachable.{u1} V G (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) V' (fun (_x : V') => V) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G) (RelIso.instRelHomClassRelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Iso.symm.{u1, u2} V V' G G' φ) v) u) (SimpleGraph.Reachable.{u2} V' G' v (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V (fun (_x : V) => V') (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.instRelHomClassRelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) φ u))
Case conversion may be inaccurate. Consider using '#align simple_graph.iso.symm_apply_reachable SimpleGraph.Iso.symm_apply_reachableₓ'. -/
theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← iso.reachable_iff, RelIso.apply_symm_apply]
#align simple_graph.iso.symm_apply_reachable SimpleGraph.Iso.symm_apply_reachable

variable (G)

#print SimpleGraph.reachable_is_equivalence /-
theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk _ (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)
#align simple_graph.reachable_is_equivalence SimpleGraph.reachable_is_equivalence
-/

#print SimpleGraph.reachableSetoid /-
/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachableSetoid : Setoid V :=
  Setoid.mk _ G.reachable_is_equivalence
#align simple_graph.reachable_setoid SimpleGraph.reachableSetoid
-/

#print SimpleGraph.Preconnected /-
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop :=
  ∀ u v : V, G.Reachable u v
#align simple_graph.preconnected SimpleGraph.Preconnected
-/

#print SimpleGraph.Preconnected.map /-
theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun a b => Nonempty.map (Walk.map _) <| hG _ _
#align simple_graph.preconnected.map SimpleGraph.Preconnected.map
-/

#print SimpleGraph.Iso.preconnected_iff /-
theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.Surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.Surjective⟩
#align simple_graph.iso.preconnected_iff SimpleGraph.Iso.preconnected_iff
-/

#print SimpleGraph.Connected /-
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj, mk_iff]
structure Connected : Prop where
  Preconnected : G.Preconnected
  [Nonempty : Nonempty V]
#align simple_graph.connected SimpleGraph.Connected
-/

instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v :=
  ⟨fun h => h.Preconnected⟩

#print SimpleGraph.Connected.map /-
theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩
#align simple_graph.connected.map SimpleGraph.Connected.map
-/

#print SimpleGraph.Iso.connected_iff /-
theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.Surjective, Connected.map e.symm.toHom e.symm.toEquiv.Surjective⟩
#align simple_graph.iso.connected_iff SimpleGraph.Iso.connected_iff
-/

#print SimpleGraph.ConnectedComponent /-
/-- The quotient of `V` by the `simple_graph.reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent :=
  Quot G.Reachable
#align simple_graph.connected_component SimpleGraph.ConnectedComponent
-/

#print SimpleGraph.connectedComponentMk /-
/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent :=
  Quot.mk G.Reachable v
#align simple_graph.connected_component_mk SimpleGraph.connectedComponentMk
-/

variable {V' G G' G''}

namespace connectedComponent

#print SimpleGraph.ConnectedComponent.inhabited /-
@[simps]
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩
#align simple_graph.connected_component.inhabited SimpleGraph.ConnectedComponent.inhabited
-/

#print SimpleGraph.ConnectedComponent.ind /-
@[elab_as_elim]
protected theorem ind {β : G.ConnectedComponent → Prop} (h : ∀ v : V, β (G.connectedComponentMk v))
    (c : G.ConnectedComponent) : β c :=
  Quot.ind h c
#align simple_graph.connected_component.ind SimpleGraph.ConnectedComponent.ind
-/

#print SimpleGraph.ConnectedComponent.ind₂ /-
@[elab_as_elim]
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h
#align simple_graph.connected_component.ind₂ SimpleGraph.ConnectedComponent.ind₂
-/

#print SimpleGraph.ConnectedComponent.sound /-
protected theorem sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound
#align simple_graph.connected_component.sound SimpleGraph.ConnectedComponent.sound
-/

#print SimpleGraph.ConnectedComponent.exact /-
protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _
#align simple_graph.connected_component.exact SimpleGraph.ConnectedComponent.exact
-/

#print SimpleGraph.ConnectedComponent.eq /-
@[simp]
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _
#align simple_graph.connected_component.eq SimpleGraph.ConnectedComponent.eq
-/

#print SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj /-
theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.Reachable
#align simple_graph.connected_component.connected_component_mk_eq_of_adj SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
-/

#print SimpleGraph.ConnectedComponent.lift /-
/-- The `connected_component` specialization of `quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort _} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2
#align simple_graph.connected_component.lift SimpleGraph.ConnectedComponent.lift
-/

/- warning: simple_graph.connected_component.lift_mk -> SimpleGraph.ConnectedComponent.lift_mk is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {β : Sort.{u2}} {f : V -> β} {h : forall (v : V) (w : V) (p : SimpleGraph.Walk.{u1} V G v w), (SimpleGraph.Walk.IsPath.{u1} V G v w p) -> (Eq.{u2} β (f v) (f w))} {v : V}, Eq.{u2} β (SimpleGraph.ConnectedComponent.lift.{u1, u2} V G β f h (SimpleGraph.connectedComponentMk.{u1} V G v)) (f v)
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {β : Sort.{u1}} {f : V -> β} {h : forall (v : V) (w : V) (p : SimpleGraph.Walk.{u2} V G v w), (SimpleGraph.Walk.IsPath.{u2} V G v w p) -> (Eq.{u1} β (f v) (f w))} {v : V}, Eq.{u1} β (SimpleGraph.ConnectedComponent.lift.{u2, u1} V G β f h (SimpleGraph.connectedComponentMk.{u2} V G v)) (f v)
Case conversion may be inaccurate. Consider using '#align simple_graph.connected_component.lift_mk SimpleGraph.ConnectedComponent.lift_mkₓ'. -/
@[simp]
protected theorem lift_mk {β : Sort _} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl
#align simple_graph.connected_component.lift_mk SimpleGraph.ConnectedComponent.lift_mk

#print SimpleGraph.ConnectedComponent.exists /-
protected theorem exists {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).exists
#align simple_graph.connected_component.exists SimpleGraph.ConnectedComponent.exists
-/

#print SimpleGraph.ConnectedComponent.forall /-
protected theorem forall {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).forall
#align simple_graph.connected_component.forall SimpleGraph.ConnectedComponent.forall
-/

#print SimpleGraph.Preconnected.subsingleton_connectedComponent /-
theorem SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩
#align simple_graph.preconnected.subsingleton_connected_component SimpleGraph.Preconnected.subsingleton_connectedComponent
-/

#print SimpleGraph.ConnectedComponent.map /-
/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun v w p _ =>
    ConnectedComponent.eq.mpr (p.map φ).Reachable
#align simple_graph.connected_component.map SimpleGraph.ConnectedComponent.map
-/

#print SimpleGraph.ConnectedComponent.map_mk /-
@[simp]
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl
#align simple_graph.connected_component.map_mk SimpleGraph.ConnectedComponent.map_mk
-/

#print SimpleGraph.ConnectedComponent.map_id /-
@[simp]
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C :=
  by
  refine' C.ind _
  exact fun _ => rfl
#align simple_graph.connected_component.map_id SimpleGraph.ConnectedComponent.map_id
-/

#print SimpleGraph.ConnectedComponent.map_comp /-
@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) := by
  refine' C.ind _
  exact fun _ => rfl
#align simple_graph.connected_component.map_comp SimpleGraph.ConnectedComponent.map_comp
-/

variable {φ : G ≃g G'} {v : V} {v' : V'}

/- warning: simple_graph.connected_component.iso_image_comp_eq_map_iff_eq_comp -> SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {v : V} {C : SimpleGraph.ConnectedComponent.{u1} V G}, Iff (Eq.{succ u2} (SimpleGraph.ConnectedComponent.{u2} V' G') (SimpleGraph.connectedComponentMk.{u2} V' G' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (fun (_x : RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) => V -> V') (RelIso.hasCoeToFun.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) φ v)) (SimpleGraph.ConnectedComponent.map.{u1, u2} V V' G G' ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (SimpleGraph.Embedding.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Embedding.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (RelEmbedding.RelHom.hasCoe.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))))) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Embedding.{u1, u2} V V' G G') (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Embedding.{u1, u2} V V' G G') (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Embedding.{u1, u2} V V' G G') (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Embedding.{u1, u2} V V' G G') (RelIso.RelEmbedding.hasCoe.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))))) φ)) C)) (Eq.{succ u1} (SimpleGraph.ConnectedComponent.{u1} V G) (SimpleGraph.connectedComponentMk.{u1} V G v) C)
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {v : V} {C : SimpleGraph.ConnectedComponent.{u1} V G}, Iff (Eq.{succ u2} (SimpleGraph.ConnectedComponent.{u2} V' G') (SimpleGraph.connectedComponentMk.{u2} V' G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V (fun (_x : V) => V') (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.instRelHomClassRelIso.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) φ v)) (SimpleGraph.ConnectedComponent.map.{u1, u2} V V' G G' (RelEmbedding.toRelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.toRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') φ)) C)) (Eq.{succ u1} (SimpleGraph.ConnectedComponent.{u1} V G) (SimpleGraph.connectedComponentMk.{u1} V G v) C)
Case conversion may be inaccurate. Consider using '#align simple_graph.connected_component.iso_image_comp_eq_map_iff_eq_comp SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_compₓ'. -/
@[simp]
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C :=
  by
  refine' C.ind fun u => _
  simp only [iso.reachable_iff, connected_component.map_mk, RelEmbedding.coe_coeFn,
    RelIso.coe_coeFn, connected_component.eq]
#align simple_graph.connected_component.iso_image_comp_eq_map_iff_eq_comp SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp

/- warning: simple_graph.connected_component.iso_inv_image_comp_eq_iff_eq_map -> SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {v' : V'} {C : SimpleGraph.ConnectedComponent.{u1} V G}, Iff (Eq.{succ u1} (SimpleGraph.ConnectedComponent.{u1} V G) (SimpleGraph.connectedComponentMk.{u1} V G (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SimpleGraph.Iso.{u2, u1} V' V G' G) (fun (_x : RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) => V' -> V) (RelIso.hasCoeToFun.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) (SimpleGraph.Iso.symm.{u1, u2} V V' G G' φ) v')) C) (Eq.{succ u2} (SimpleGraph.ConnectedComponent.{u2} V' G') (SimpleGraph.connectedComponentMk.{u2} V' G' v') (SimpleGraph.ConnectedComponent.map.{u1, u2} V V' G G' ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (SimpleGraph.Hom.{u1, u2} V V' G G') (coeTrans.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (SimpleGraph.Iso.{u1, u2} V V' G G') (RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) (SimpleGraph.Hom.{u1, u2} V V' G G') (coeBase.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G')) (SimpleGraph.Hom.{u1, u2} V V' G G') (RelEmbedding.RelHom.hasCoe.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))) (RelIso.RelEmbedding.hasCoe.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G'))))) φ) C))
but is expected to have type
  forall {V : Type.{u1}} {V' : Type.{u2}} {G : SimpleGraph.{u1} V} {G' : SimpleGraph.{u2} V'} {φ : SimpleGraph.Iso.{u1, u2} V V' G G'} {v' : V'} {C : SimpleGraph.ConnectedComponent.{u1} V G}, Iff (Eq.{succ u1} (SimpleGraph.ConnectedComponent.{u1} V G) (SimpleGraph.connectedComponentMk.{u1} V G (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) V' (fun (_x : V') => V) (RelHomClass.toFunLike.{max u2 u1, u2, u1} (RelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G)) V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G) (RelIso.instRelHomClassRelIso.{u2, u1} V' V (SimpleGraph.Adj.{u2} V' G') (SimpleGraph.Adj.{u1} V G))) (SimpleGraph.Iso.symm.{u1, u2} V V' G G' φ) v')) C) (Eq.{succ u2} (SimpleGraph.ConnectedComponent.{u2} V' G') (SimpleGraph.connectedComponentMk.{u2} V' G' v') (SimpleGraph.ConnectedComponent.map.{u1, u2} V V' G G' (RelEmbedding.toRelHom.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') (RelIso.toRelEmbedding.{u1, u2} V V' (SimpleGraph.Adj.{u1} V G) (SimpleGraph.Adj.{u2} V' G') φ)) C))
Case conversion may be inaccurate. Consider using '#align simple_graph.connected_component.iso_inv_image_comp_eq_iff_eq_map SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_mapₓ'. -/
@[simp]
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ :=
  by
  refine' C.ind fun u => _
  simp only [iso.symm_apply_reachable, connected_component.eq, coe_coe, connected_component.map_mk,
    RelEmbedding.coe_coeFn, RelIso.coe_coeFn]
#align simple_graph.connected_component.iso_inv_image_comp_eq_iff_eq_map SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map

end connectedComponent

namespace Iso

#print SimpleGraph.Iso.connectedComponentEquiv /-
/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent
    where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C :=
    ConnectedComponent.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
      C
  right_inv C :=
    ConnectedComponent.ind
      (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v)) C
#align simple_graph.iso.connected_component_equiv SimpleGraph.Iso.connectedComponentEquiv
-/

#print SimpleGraph.Iso.connectedComponentEquiv_refl /-
@[simp]
theorem connectedComponentEquiv_refl : (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ :=
  by
  ext ⟨v⟩
  rfl
#align simple_graph.iso.connected_component_equiv_refl SimpleGraph.Iso.connectedComponentEquiv_refl
-/

#print SimpleGraph.Iso.connectedComponentEquiv_symm /-
@[simp]
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm :=
  by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_symm SimpleGraph.Iso.connectedComponentEquiv_symm
-/

#print SimpleGraph.Iso.connectedComponentEquiv_trans /-
@[simp]
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
      φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv :=
  by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_trans SimpleGraph.Iso.connectedComponentEquiv_trans
-/

end Iso

namespace connectedComponent

#print SimpleGraph.ConnectedComponent.supp /-
/-- The set of vertices in a connected component of a graph. -/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }
#align simple_graph.connected_component.supp SimpleGraph.ConnectedComponent.supp
-/

#print SimpleGraph.ConnectedComponent.supp_injective /-
@[ext]
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) :=
  by
  refine' connected_component.ind₂ _
  intro v w
  simp only [connected_component.supp, Set.ext_iff, connected_component.eq, Set.mem_setOf_eq]
  intro h
  rw [reachable_comm, h]
#align simple_graph.connected_component.supp_injective SimpleGraph.ConnectedComponent.supp_injective
-/

#print SimpleGraph.ConnectedComponent.supp_inj /-
@[simp]
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff
#align simple_graph.connected_component.supp_inj SimpleGraph.ConnectedComponent.supp_inj
-/

instance : SetLike G.ConnectedComponent V
    where
  coe := ConnectedComponent.supp
  coe_injective' := ConnectedComponent.supp_injective

#print SimpleGraph.ConnectedComponent.mem_supp_iff /-
@[simp]
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl
#align simple_graph.connected_component.mem_supp_iff SimpleGraph.ConnectedComponent.mem_supp_iff
-/

#print SimpleGraph.ConnectedComponent.connectedComponentMk_mem /-
theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl
#align simple_graph.connected_component.connected_component_mk_mem SimpleGraph.ConnectedComponent.connectedComponentMk_mem
-/

#print SimpleGraph.ConnectedComponent.isoEquivSupp /-
/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp
    where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.Prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.Prop⟩
  left_inv v := Subtype.ext_val (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext_val (φ.toEquiv.right_inv ↑v)
#align simple_graph.connected_component.iso_equiv_supp SimpleGraph.ConnectedComponent.isoEquivSupp
-/

end connectedComponent

#print SimpleGraph.Subgraph.Connected /-
/-- A subgraph is connected if it is connected as a simple graph. -/
abbrev Subgraph.Connected (H : G.Subgraph) : Prop :=
  H.coe.Connected
#align simple_graph.subgraph.connected SimpleGraph.Subgraph.Connected
-/

#print SimpleGraph.singletonSubgraph_connected /-
theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected :=
  by
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [singleton_subgraph_verts, Set.mem_singleton_iff] at ha hb
  subst_vars
#align simple_graph.singleton_subgraph_connected SimpleGraph.singletonSubgraph_connected
-/

#print SimpleGraph.subgraphOfAdj_connected /-
@[simp]
theorem subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected :=
  by
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraph_of_adj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first
      |rfl|·
        apply adj.reachable
        simp
#align simple_graph.subgraph_of_adj_connected SimpleGraph.subgraphOfAdj_connected
-/

#print SimpleGraph.Preconnected.set_univ_walk_nonempty /-
theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v
#align simple_graph.preconnected.set_univ_walk_nonempty SimpleGraph.Preconnected.set_univ_walk_nonempty
-/

#print SimpleGraph.Connected.set_univ_walk_nonempty /-
theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.Preconnected.set_univ_walk_nonempty u v
#align simple_graph.connected.set_univ_walk_nonempty SimpleGraph.Connected.set_univ_walk_nonempty
-/

/-! ### Walks as subgraphs -/


namespace Walk

variable {G G'} {u v w : V}

#print SimpleGraph.Walk.toSubgraph /-
/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp]
protected def toSubgraph : ∀ {u v : V}, G.Walk u v → G.Subgraph
  | u, _, nil => G.singletonSubgraph u
  | _, _, cons h p => G.subgraphOfAdj h ⊔ p.toSubgraph
#align simple_graph.walk.to_subgraph SimpleGraph.Walk.toSubgraph
-/

#print SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj /-
theorem toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) :
    (cons h nil).toSubgraph = G.subgraphOfAdj h := by simp
#align simple_graph.walk.to_subgraph_cons_nil_eq_subgraph_of_adj SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj
-/

#print SimpleGraph.Walk.mem_verts_toSubgraph /-
theorem mem_verts_toSubgraph (p : G.Walk u v) : w ∈ p.toSubgraph.verts ↔ w ∈ p.support :=
  by
  induction' p with _ x y z h p' ih
  · simp
  · have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp (config := { contextual := true })⟩
    simp [ih, or_assoc', this]
#align simple_graph.walk.mem_verts_to_subgraph SimpleGraph.Walk.mem_verts_toSubgraph
-/

#print SimpleGraph.Walk.verts_toSubgraph /-
@[simp]
theorem verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w ∈ p.support } :=
  Set.ext fun _ => p.mem_verts_toSubgraph
#align simple_graph.walk.verts_to_subgraph SimpleGraph.Walk.verts_toSubgraph
-/

#print SimpleGraph.Walk.mem_edges_toSubgraph /-
theorem mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} :
    e ∈ p.toSubgraph.edgeSetEmbedding ↔ e ∈ p.edges := by induction p <;> simp [*]
#align simple_graph.walk.mem_edges_to_subgraph SimpleGraph.Walk.mem_edges_toSubgraph
-/

#print SimpleGraph.Walk.edgeSet_toSubgraph /-
@[simp]
theorem edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSetEmbedding = { e | e ∈ p.edges } :=
  Set.ext fun _ => p.mem_edges_toSubgraph
#align simple_graph.walk.edge_set_to_subgraph SimpleGraph.Walk.edgeSet_toSubgraph
-/

/- warning: simple_graph.walk.to_subgraph_append -> SimpleGraph.Walk.toSubgraph_append is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u1} V G u v) (q : SimpleGraph.Walk.{u1} V G v w), Eq.{succ u1} (SimpleGraph.Subgraph.{u1} V G) (SimpleGraph.Walk.toSubgraph.{u1} V G u w (SimpleGraph.Walk.append.{u1} V G u v w p q)) (Sup.sup.{u1} (SimpleGraph.Subgraph.{u1} V G) (SimpleGraph.Subgraph.hasSup.{u1} V G) (SimpleGraph.Walk.toSubgraph.{u1} V G u v p) (SimpleGraph.Walk.toSubgraph.{u1} V G v w q))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V} {w : V} (p : SimpleGraph.Walk.{u1} V G u v) (q : SimpleGraph.Walk.{u1} V G v w), Eq.{succ u1} (SimpleGraph.Subgraph.{u1} V G) (SimpleGraph.Walk.toSubgraph.{u1} V G u w (SimpleGraph.Walk.append.{u1} V G u v w p q)) (Sup.sup.{u1} (SimpleGraph.Subgraph.{u1} V G) (SimpleGraph.Subgraph.instSupSubgraph.{u1} V G) (SimpleGraph.Walk.toSubgraph.{u1} V G u v p) (SimpleGraph.Walk.toSubgraph.{u1} V G v w q))
Case conversion may be inaccurate. Consider using '#align simple_graph.walk.to_subgraph_append SimpleGraph.Walk.toSubgraph_appendₓ'. -/
@[simp]
theorem toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := by induction p <;> simp [*, sup_assoc]
#align simple_graph.walk.to_subgraph_append SimpleGraph.Walk.toSubgraph_append

#print SimpleGraph.Walk.toSubgraph_reverse /-
@[simp]
theorem toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph :=
  by
  induction p
  · simp
  · simp only [*, walk.to_subgraph, reverse_cons, to_subgraph_append, subgraph_of_adj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]
#align simple_graph.walk.to_subgraph_reverse SimpleGraph.Walk.toSubgraph_reverse
-/

#print SimpleGraph.Walk.toSubgraph_rotate /-
@[simp]
theorem toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).toSubgraph = c.toSubgraph := by
  rw [rotate, to_subgraph_append, sup_comm, ← to_subgraph_append, take_spec]
#align simple_graph.walk.to_subgraph_rotate SimpleGraph.Walk.toSubgraph_rotate
-/

#print SimpleGraph.Walk.toSubgraph_map /-
@[simp]
theorem toSubgraph_map (f : G →g G') (p : G.Walk u v) : (p.map f).toSubgraph = p.toSubgraph.map f :=
  by induction p <;> simp [*, subgraph.map_sup]
#align simple_graph.walk.to_subgraph_map SimpleGraph.Walk.toSubgraph_map
-/

#print SimpleGraph.Walk.finite_neighborSet_toSubgraph /-
@[simp]
theorem finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet w).Finite :=
  by
  induction p
  · rw [walk.to_subgraph, neighbor_set_singleton_subgraph]
    apply Set.toFinite
  · rw [walk.to_subgraph, subgraph.neighbor_set_sup]
    refine' Set.Finite.union _ p_ih
    refine' Set.Finite.subset _ (neighbor_set_subgraph_of_adj_subset p_h)
    apply Set.toFinite
#align simple_graph.walk.finite_neighbor_set_to_subgraph SimpleGraph.Walk.finite_neighborSet_toSubgraph
-/

end Walk

/-! ### Walks of a given length -/


section WalkCounting

#print SimpleGraph.set_walk_self_length_zero_eq /-
theorem set_walk_self_length_zero_eq (u : V) : { p : G.Walk u u | p.length = 0 } = {Walk.nil} :=
  by
  ext p
  simp
#align simple_graph.set_walk_self_length_zero_eq SimpleGraph.set_walk_self_length_zero_eq
-/

#print SimpleGraph.set_walk_length_zero_eq_of_ne /-
theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    { p : G.Walk u v | p.length = 0 } = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
  exact fun h' => absurd (walk.eq_of_length_eq_zero h') h
#align simple_graph.set_walk_length_zero_eq_of_ne SimpleGraph.set_walk_length_zero_eq_of_ne
-/

#print SimpleGraph.set_walk_length_succ_eq /-
theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    { p : G.Walk u v | p.length = n.succ } =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' { p' : G.Walk w v | p'.length = n } :=
  by
  ext p
  cases' p with _ _ w _ huw pwv
  · simp [eq_comm]
  · simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro rfl
      exact ⟨w, huw, pwv, rfl, rfl, HEq.rfl⟩
    · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
      rfl
#align simple_graph.set_walk_length_succ_eq SimpleGraph.set_walk_length_succ_eq
-/

variable (G) [DecidableEq V]

section LocallyFinite

variable [LocallyFinite G]

#print SimpleGraph.finsetWalkLength /-
/-- The `finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `simple_graph.coe_finset_walk_length_eq` for the relationship between this `finset` and
the set of length-`n` walks. -/
def finsetWalkLength : ∀ (n : ℕ) (u v : V), Finset (G.Walk u v)
  | 0, u, v =>
    if h : u = v then by
      subst u
      exact {walk.nil}
    else ∅
  | n + 1, u, v =>
    Finset.univ.biUnion fun w : G.neighborSet u =>
      (finset_walk_length n w v).map ⟨fun p => Walk.cons w.property p, fun p q => by simp⟩
#align simple_graph.finset_walk_length SimpleGraph.finsetWalkLength
-/

#print SimpleGraph.coe_finsetWalkLength_eq /-
theorem coe_finsetWalkLength_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = { p : G.Walk u v | p.length = n } :=
  by
  induction' n with n ih generalizing u v
  · obtain rfl | huv := eq_or_ne u v <;> simp [finset_walk_length, set_walk_length_zero_eq_of_ne, *]
  · simp only [finset_walk_length, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_univ, Set.iUnion_true]
    ext p
    simp only [mem_neighbor_set, Finset.coe_map, embedding.coe_fn_mk, Set.iUnion_coe_set,
      Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    congr with w
    congr with h
    congr with q
    have := set.ext_iff.mp (ih w v) q
    simp only [Finset.mem_coe, Set.mem_setOf_eq] at this
    rw [← this]
    rfl
#align simple_graph.coe_finset_walk_length_eq SimpleGraph.coe_finsetWalkLength_eq
-/

variable {G}

#print SimpleGraph.Walk.mem_finsetWalkLength_iff_length_eq /-
theorem Walk.mem_finsetWalkLength_iff_length_eq {n : ℕ} {u v : V} (p : G.Walk u v) :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p
#align simple_graph.walk.mem_finset_walk_length_iff_length_eq SimpleGraph.Walk.mem_finsetWalkLength_iff_length_eq
-/

variable (G)

#print SimpleGraph.fintypeSetWalkLength /-
instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype { p : G.Walk u v | p.length = n } :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finset_walk_length_eq]
#align simple_graph.fintype_set_walk_length SimpleGraph.fintypeSetWalkLength
-/

#print SimpleGraph.set_walk_length_toFinset_eq /-
theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    { p : G.Walk u v | p.length = n }.toFinset = G.finsetWalkLength n u v :=
  by
  ext p
  simp [← coe_finset_walk_length_eq]
#align simple_graph.set_walk_length_to_finset_eq SimpleGraph.set_walk_length_toFinset_eq
-/

#print SimpleGraph.card_set_walk_length_eq /-
/- See `simple_graph.adj_matrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card { p : G.Walk u v | p.length = n } = (G.finsetWalkLength n u v).card :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finset_walk_length_eq]
#align simple_graph.card_set_walk_length_eq SimpleGraph.card_set_walk_length_eq
-/

#print SimpleGraph.fintypeSetPathLength /-
instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype { p : G.Walk u v | p.IsPath ∧ p.length = n } :=
  Fintype.ofFinset ((G.finsetWalkLength n u v).filterₓ Walk.IsPath) <| by
    simp [walk.mem_finset_walk_length_iff_length_eq, and_comm']
#align simple_graph.fintype_set_path_length SimpleGraph.fintypeSetPathLength
-/

end LocallyFinite

section Finite

variable [Fintype V] [DecidableRel G.Adj]

#print SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty /-
theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty :=
  by
  constructor
  · intro r
    refine' r.elim_path fun p => _
    refine' ⟨⟨_, p.is_path.length_lt⟩, p, _⟩
    simp [walk.mem_finset_walk_length_iff_length_eq]
  · rintro ⟨_, p, _⟩
    use p
#align simple_graph.reachable_iff_exists_finset_walk_length_nonempty SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty
-/

instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

instance : Fintype G.ConnectedComponent :=
  @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance : Decidable G.Preconnected := by
  unfold preconnected
  infer_instance

instance : Decidable G.Connected :=
  by
  rw [connected_iff, ← Finset.univ_nonempty_iff]
  exact And.decidable

end Finite

end WalkCounting

section BridgeEdges

/-! ### Bridge edges -/


#print SimpleGraph.IsBridge /-
/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSetEmbedding ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, by simp [reachable_comm]⟩ e
#align simple_graph.is_bridge SimpleGraph.IsBridge
-/

/- warning: simple_graph.is_bridge_iff -> SimpleGraph.isBridge_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V}, Iff (SimpleGraph.IsBridge.{u1} V G (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V u v))) (And (SimpleGraph.Adj.{u1} V G u v) (Not (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasSdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasSingleton.{u1} (Sym2.{u1} V)) (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V u v))))) u v)))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {u : V} {v : V}, Iff (SimpleGraph.IsBridge.{u1} V G (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V u v))) (And (SimpleGraph.Adj.{u1} V G u v) (Not (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.sdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (Set.{u1} (Sym2.{u1} V)) (Set.instSingletonSet.{u1} (Sym2.{u1} V)) (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V u v))))) u v)))
Case conversion may be inaccurate. Consider using '#align simple_graph.is_bridge_iff SimpleGraph.isBridge_iffₓ'. -/
theorem isBridge_iff {u v : V} :
    G.IsBridge ⟦(u, v)⟧ ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {⟦(u, v)⟧}).Reachable u v :=
  Iff.rfl
#align simple_graph.is_bridge_iff SimpleGraph.isBridge_iff

/- warning: simple_graph.reachable_delete_edges_iff_exists_walk -> SimpleGraph.reachable_delete_edges_iff_exists_walk is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {v : V} {w : V}, Iff (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasSdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasSingleton.{u1} (Sym2.{u1} V)) (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w))))) v w) (Exists.{succ u1} (SimpleGraph.Walk.{u1} V G v w) (fun (p : SimpleGraph.Walk.{u1} V G v w) => Not (Membership.Mem.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w)) (SimpleGraph.Walk.edges.{u1} V G v w p))))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {v : V} {w : V}, Iff (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.sdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (Set.{u1} (Sym2.{u1} V)) (Set.instSingletonSet.{u1} (Sym2.{u1} V)) (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w))))) v w) (Exists.{succ u1} (SimpleGraph.Walk.{u1} V G v w) (fun (p : SimpleGraph.Walk.{u1} V G v w) => Not (Membership.mem.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w)) (SimpleGraph.Walk.edges.{u1} V G v w p))))
Case conversion may be inaccurate. Consider using '#align simple_graph.reachable_delete_edges_iff_exists_walk SimpleGraph.reachable_delete_edges_iff_exists_walkₓ'. -/
theorem reachable_delete_edges_iff_exists_walk {v w : V} :
    (G \ fromEdgeSet {⟦(v, w)⟧}).Reachable v w ↔ ∃ p : G.Walk v w, ¬⟦(v, w)⟧ ∈ p.edges :=
  by
  constructor
  · rintro ⟨p⟩
    use p.map (hom.map_spanning_subgraphs (by simp))
    simp_rw [walk.edges_map, List.mem_map, hom.map_spanning_subgraphs_apply, Sym2.map_id', id.def]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edge_set h
  · rintro ⟨p, h⟩
    refine' ⟨p.transfer _ fun e ep => _⟩
    simp only [edge_set_sdiff, edge_set_from_edge_set, edge_set_sdiff_sdiff_is_diag, Set.mem_diff,
      Set.mem_singleton_iff]
    exact ⟨p.edges_subset_edge_set ep, fun h' => h (h' ▸ ep)⟩
#align simple_graph.reachable_delete_edges_iff_exists_walk SimpleGraph.reachable_delete_edges_iff_exists_walk

#print SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges /-
theorem isBridge_iff_adj_and_forall_walk_mem_edges {v w : V} :
    G.IsBridge ⟦(v, w)⟧ ↔ G.Adj v w ∧ ∀ p : G.Walk v w, ⟦(v, w)⟧ ∈ p.edges :=
  by
  rw [is_bridge_iff, and_congr_right']
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not]
#align simple_graph.is_bridge_iff_adj_and_forall_walk_mem_edges SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges
-/

#print SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux /-
theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : ∀ p : G.Walk v w, ⟦(v, w)⟧ ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : ⟦(v, w)⟧ ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False :=
  by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.take_until v hv).takeUntil w hw
  let pwv := (c.take_until v hv).dropUntil w hw
  let pvu := c.drop_until v hv
  have : c = (puw.append pwv).append pvu := by simp
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge ⟦(v, w)⟧, but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [walk.edges_reverse, List.mem_reverse'] at hpq'
  rw [walk.is_trail_def, this, walk.edges_append, walk.edges_append, List.nodup_append_comm, ←
    List.append_assoc, ← walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'
#align simple_graph.reachable_delete_edges_iff_exists_cycle.aux SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux
-/

/- warning: simple_graph.adj_and_reachable_delete_edges_iff_exists_cycle -> SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {v : V} {w : V}, Iff (And (SimpleGraph.Adj.{u1} V G v w) (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasSdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasSingleton.{u1} (Sym2.{u1} V)) (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w))))) v w)) (Exists.{succ u1} V (fun (u : V) => Exists.{succ u1} (SimpleGraph.Walk.{u1} V G u u) (fun (p : SimpleGraph.Walk.{u1} V G u u) => And (SimpleGraph.Walk.IsCycle.{u1} V G u p) (Membership.Mem.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) (Quotient.mk'.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w)) (SimpleGraph.Walk.edges.{u1} V G u u p)))))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {v : V} {w : V}, Iff (And (SimpleGraph.Adj.{u1} V G v w) (SimpleGraph.Reachable.{u1} V (SDiff.sdiff.{u1} (SimpleGraph.{u1} V) (SimpleGraph.sdiff.{u1} V) G (SimpleGraph.fromEdgeSet.{u1} V (Singleton.singleton.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (Set.{u1} (Sym2.{u1} V)) (Set.instSingletonSet.{u1} (Sym2.{u1} V)) (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w))))) v w)) (Exists.{succ u1} V (fun (u : V) => Exists.{succ u1} (SimpleGraph.Walk.{u1} V G u u) (fun (p : SimpleGraph.Walk.{u1} V G u u) => And (SimpleGraph.Walk.IsCycle.{u1} V G u p) (Membership.mem.{u1, u1} (Quotient.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V)) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) (Quotient.mk.{succ u1} (Prod.{u1, u1} V V) (Sym2.Rel.setoid.{u1} V) (Prod.mk.{u1, u1} V V v w)) (SimpleGraph.Walk.edges.{u1} V G u u p)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_and_reachable_delete_edges_iff_exists_cycle SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycleₓ'. -/
theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G \ fromEdgeSet {⟦(v, w)⟧}).Reachable v w ↔
      ∃ (u : V)(p : G.Walk u u), p.IsCycle ∧ ⟦(v, w)⟧ ∈ p.edges :=
  by
  classical
    rw [reachable_delete_edges_iff_exists_walk]
    constructor
    · rintro ⟨h, p, hp⟩
      refine' ⟨w, walk.cons h.symm p.to_path, _, _⟩
      · apply path.cons_is_cycle
        rw [Sym2.eq_swap]
        intro h
        exact absurd (walk.edges_to_path_subset p h) hp
      simp only [Sym2.eq_swap, walk.edges_cons, List.mem_cons, eq_self_iff_true, true_or_iff]
    · rintro ⟨u, c, hc, he⟩
      have hvc : v ∈ c.support := walk.fst_mem_support_of_mem_edges c he
      have hwc : w ∈ c.support := walk.snd_mem_support_of_mem_edges c he
      let puv := c.take_until v hvc
      let pvu := c.drop_until v hvc
      obtain hw | hw' : w ∈ puv.support ∨ w ∈ pvu.support := by
        rwa [← walk.mem_support_append_iff, walk.take_spec]
      · by_contra' h
        specialize h (c.adj_of_mem_edges he)
        exact reachable_delete_edges_iff_exists_cycle.aux h c hc.to_trail he hw
      · by_contra' hb
        specialize hb (c.adj_of_mem_edges he)
        have hb' : ∀ p : G.walk w v, ⟦(w, v)⟧ ∈ p.edges :=
          by
          intro p
          simpa [Sym2.eq_swap] using hb p.reverse
        apply
          reachable_delete_edges_iff_exists_cycle.aux hb' (pvu.append puv) (hc.to_trail.rotate hvc)
            _ (walk.start_mem_support _)
        rwa [walk.edges_append, List.mem_append, or_comm', ← List.mem_append, ← walk.edges_append,
          walk.take_spec, Sym2.eq_swap]
#align simple_graph.adj_and_reachable_delete_edges_iff_exists_cycle SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle

#print SimpleGraph.isBridge_iff_adj_and_forall_cycle_not_mem /-
theorem isBridge_iff_adj_and_forall_cycle_not_mem {v w : V} :
    G.IsBridge ⟦(v, w)⟧ ↔ G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → ⟦(v, w)⟧ ∉ p.edges :=
  by
  rw [is_bridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and_iff]
#align simple_graph.is_bridge_iff_adj_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_adj_and_forall_cycle_not_mem
-/

/- warning: simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem -> SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {e : Sym2.{u1} V}, Iff (SimpleGraph.IsBridge.{u1} V G e) (And (Membership.Mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.hasMem.{u1} (Sym2.{u1} V)) e (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (SimpleGraph.hasLe.{u1} V) (Set.hasLe.{u1} (Sym2.{u1} V))) (fun (_x : RelEmbedding.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) => (SimpleGraph.{u1} V) -> (Set.{u1} (Sym2.{u1} V))) (RelEmbedding.hasCoeToFun.{u1, u1} (SimpleGraph.{u1} V) (Set.{u1} (Sym2.{u1} V)) (LE.le.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasLe.{u1} V)) (LE.le.{u1} (Set.{u1} (Sym2.{u1} V)) (Set.hasLe.{u1} (Sym2.{u1} V)))) (SimpleGraph.edgeSetEmbedding.{u1} V) G)) (forall {{u : V}} (p : SimpleGraph.Walk.{u1} V G u u), (SimpleGraph.Walk.IsCycle.{u1} V G u p) -> (Not (Membership.Mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.hasMem.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u u p)))))
but is expected to have type
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {e : Sym2.{u1} V}, Iff (SimpleGraph.IsBridge.{u1} V G e) (And (Membership.mem.{u1, u1} (Sym2.{u1} V) (Set.{u1} (Sym2.{u1} V)) (Set.instMembershipSet.{u1} (Sym2.{u1} V)) e (SimpleGraph.edgeSet.{u1} V G)) (forall {{u : V}} (p : SimpleGraph.Walk.{u1} V G u u), (SimpleGraph.Walk.IsCycle.{u1} V G u p) -> (Not (Membership.mem.{u1, u1} (Sym2.{u1} V) (List.{u1} (Sym2.{u1} V)) (List.instMembershipList.{u1} (Sym2.{u1} V)) e (SimpleGraph.Walk.edges.{u1} V G u u p)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_memₓ'. -/
theorem isBridge_iff_mem_and_forall_cycle_not_mem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSetEmbedding ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun v w => isBridge_iff_adj_and_forall_cycle_not_mem) e
#align simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem

end BridgeEdges

end SimpleGraph

