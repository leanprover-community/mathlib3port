/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.List.Default

/-!

# Graph connectivity

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

* `simple_graph.walk`

* `simple_graph.walk.is_trail`, `simple_graph.walk.is_path`, and `simple_graph.walk.is_cycle`.

* `simple_graph.path`

## Tags
walks, trails, paths, circuits, cycles

-/


universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`. -/
inductive Walk : V → V → Type u
  | nil {u : V} : walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : walk v w) : walk u w
  deriving DecidableEq

attribute [refl] walk.nil

instance Walk.inhabited (v : V) : Inhabited (G.Walk v v) :=
  ⟨by
    rfl⟩

namespace Walk

variable {G}

theorem exists_eq_cons_of_ne :
    ∀ {u v : V} hne : u ≠ v p : G.Walk u v, ∃ (w : V)(h : G.Adj u w)(p' : G.Walk w v), p = cons h p'
  | _, _, hne, nil => (hne rfl).elim
  | _, _, _, cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges along it. -/
def length : ∀ {u v : V}, G.Walk u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ q => q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : ∀ {u v w : V}, G.Walk u v → G.Walk v w → G.Walk u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux : ∀ {u v w : V}, G.Walk u v → G.Walk u w → G.Walk v w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => reverse_aux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u :=
  w.reverseAux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def getVert : ∀ {u v : V} p : G.Walk u v n : ℕ, V
  | u, v, nil, _ => u
  | u, v, cons _ _, 0 => u
  | u, v, cons _ q, n + 1 => q.getVert n

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) :=
  rfl

@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h nil).append p = cons h p :=
  rfl

@[simp]
theorem append_nil : ∀ {u v : V} p : G.Walk u v, p.append nil = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    rw [cons_append, append_nil]

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

theorem append_assoc :
    ∀ {u v w x : V} p : G.Walk u v q : G.Walk v w r : G.Walk w x, p.append (q.append r) = (p.append q).append r
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    dunfold append
    rw [append_assoc]

@[simp]
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil :=
  rfl

theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl

@[simp]
theorem cons_reverse_aux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q) :=
  rfl

@[simp]
protected theorem append_reverse_aux :
    ∀ {u v w x : V} p : G.Walk u v q : G.Walk v w r : G.Walk u x,
      (p.append q).reverseAux r = q.reverseAux (p.reverseAux r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => append_reverse_aux p' q (cons (G.symm h) r)

@[simp]
protected theorem reverse_aux_append :
    ∀ {u v w x : V} p : G.Walk u v q : G.Walk u w r : G.Walk w x, (p.reverseAux q).append r = p.reverseAux (q.append r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    simp [reverse_aux_append p' (cons (G.symm h) q) r]

protected theorem reverse_aux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by
  simp [reverse]

@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by
  simp [reverse]

@[simp]
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  simp [reverse]

@[simp]
theorem reverse_reverse : ∀ {u v : V} p : G.Walk u v, p.reverse.reverse = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    simp [reverse_reverse]

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 :=
  rfl

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).length = p.length + 1 :=
  rfl

@[simp]
theorem length_append : ∀ {u v w : V} p : G.Walk u v q : G.Walk v w, (p.append q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [length_append, add_left_commₓ, add_commₓ]

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
@[simp]
protected theorem length_reverse_aux :
    ∀ {u v w : V} p : G.Walk u v q : G.Walk u w, (p.reverseAux q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [length_reverse_aux, Nat.add_succ, Nat.succ_add]

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by
  simp [reverse]

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : ∀ {u v : V}, G.Walk u v → List V
  | u, v, nil => [u]
  | u, v, cons h p => u :: p.Support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges : ∀ {u v : V}, G.Walk u v → List (Sym2 V)
  | u, v, nil => []
  | u, v, @cons _ _ _ x _ h p => ⟦(u, x)⟧ :: p.edges

@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).Support = [u] :=
  rfl

@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).Support = u :: p.Support :=
  rfl

theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').Support = p.Support ++ p'.Support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.Support = p.Support.reverse := by
  induction p <;> simp [support_append, *]

theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.Support ≠ [] := by
  cases p <;> simp

theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').Support.tail = p.Support.tail ++ p'.Support.tail := by
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.Support = u :: p.Support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.Support := by
  cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.Support := by
  induction p <;> simp [*]

theorem mem_support_iff {u v w : V} (p : G.Walk u v) : w ∈ p.Support ↔ w = u ∨ w ∈ p.Support.tail := by
  cases p <;> simp

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).Support ↔ u = v := by
  simp

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').Support.tail ↔ t ∈ p.Support.tail ∨ t ∈ p'.Support.tail := by
  rw [tail_support_append, List.mem_appendₓ]

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.Support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

@[simp]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').Support ↔ t ∈ p.Support ∨ t ∈ p'.Support := by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  by_cases' h : t = v <;>
    by_cases' h' : t = u <;>
      subst_vars <;>
        try
            have := Ne.symm h' <;>
          simp [*]

theorem coe_support {u v : V} (p : G.Walk u v) : (p.Support : Multiset V) = {u} + p.Support.tail := by
  cases p <;> rfl

theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').Support : Multiset V) = {u} + p.Support.tail + p'.Support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').Support : Multiset V) = p.Support + p'.Support - {v} := by
  rw [support_append, ← Multiset.coe_add]
  simp only [coe_support]
  rw [add_commₓ {v}]
  simp only [← add_assocₓ, add_tsub_cancel_right]

theorem chain_adj_support_aux : ∀ {u v w : V} h : G.Adj u v p : G.Walk v w, List.Chain G.Adj u p.Support
  | _, _, _, h, nil => List.Chain.cons h List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_adj_support_aux h' p)

theorem chain_adj_support : ∀ {u v : V} p : G.Walk u v, List.Chain' G.Adj p.Support
  | _, _, nil => List.Chain.nil
  | _, _, cons h p => chain_adj_support_aux h p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form to avoid unsightly coercions. -/
theorem edges_subset_edge_set : ∀ {u v : V} p : G.Walk u v {e : Sym2 V} h : e ∈ p.edges, e ∈ G.EdgeSet
  | _, _, cons h' p', e, h => by
    rcases h with ⟨rfl, h⟩ <;> solve_by_elim

@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] :=
  rfl

@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).edges = ⟦(u, v)⟧ :: p.edges :=
  rfl

@[simp]
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) : (p.append p').edges = p.edges ++ p'.edges := by
  induction p <;> simp [*]

@[simp]
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  induction p <;> simp [*, Sym2.eq_swap]

@[simp]
theorem length_support {u v : V} (p : G.Walk u v) : p.Support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by
  induction p <;> simp [*]

theorem mem_support_of_mem_edges : ∀ {t u v w : V} p : G.Walk v w he : ⟦(t, u)⟧ ∈ p.edges, t ∈ p.Support
  | t, u, v, w, cons h p', he => by
    simp only [support_cons, edges_cons, List.mem_cons_iff, Quotientₓ.eq] at he⊢
    rcases he with ((he | he) | he)
    · exact Or.inl rfl
      
    · exact Or.inr (start_mem_support _)
      
    · exact Or.inr (mem_support_of_mem_edges _ he)
      

theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.Support.Nodup) : p.edges.Nodup := by
  induction p
  · simp
    
  · simp only [edges_cons, support_cons, List.nodup_cons] at h⊢
    exact ⟨fun h' => h.1 (mem_support_of_mem_edges p_p h'), p_ih h.2⟩
    

/-! ### Trails, paths, circuits, cycles -/


/-- A *trail* is a walk with no repeating edges. -/
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) extends
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.Support.Nodup

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure IsCircuit {u : V} (p : G.Walk u u) extends
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure" : Prop where
  ne_nil : p ≠ nil

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle [DecidableEq V] {u : V} (p : G.Walk u u) extends
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.Support.tail.Nodup

theorem is_trail_def {u v : V} (p : G.Walk u v) : p.IsTrail ↔ p.edges.Nodup :=
  ⟨IsTrail.edges_nodup, fun h => ⟨h⟩⟩

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.Support.Nodup) : IsPath p :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

theorem is_path_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.Support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

theorem is_cycle_def [DecidableEq V] {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ IsTrail p ∧ p ≠ nil ∧ p.Support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by
    simp [edges]⟩

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} : (cons h p).IsTrail → p.IsTrail := by
  simp [is_trail_def]

@[simp]
theorem cons_is_trail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ ⟦(u, v)⟧ ∉ p.edges := by
  simp [is_trail_def, and_comm]

theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [is_trail_def] using h

@[simp]
theorem reverse_is_trail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try
        rw [reverse_reverse]
      

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsTrail) : p.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsTrail) : q.IsTrail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩

theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail) (e : Sym2 V) :
    p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail) {e : Sym2 V}
    (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

@[simp]
theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by
  fconstructor <;> simp

theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} : (cons h p).IsPath → p.IsPath := by
  simp [is_path_def]

@[simp]
theorem cons_is_path_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.Support :=
  by
  constructor <;> simp (config := { contextual := true })[is_path_def]

theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [is_path_def] using h

@[simp]
theorem is_path_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse <;> simp

theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} : (p.append q).IsPath → p.IsPath := by
  simp only [is_path_def, support_append]
  exact List.nodup_of_nodup_append_left

theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w} (h : (p.append q).IsPath) : q.IsPath := by
  rw [← is_path_reverse_iff] at h⊢
  rw [reverse_append] at h
  apply h.of_append_left

/-! ### Walk decompositions -/


section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil : ∀ {v w : V} p : G.Walk v w u : V h : u ∈ p.Support, G.Walk v u
  | v, w, nil, u, h => by
    rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by
      subst u
    else cons r (take_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil : ∀ {v w : V} p : G.Walk v w u : V h : u ∈ p.Support, G.Walk u w
  | v, w, nil, u, h => by
    rw [mem_support_nil_iff.mp h]
  | v, w, cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else drop_until p _ <| h.casesOn (fun h' => (hx h'.symm).elim) id

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).append (p.dropUntil u h) = p :=
  by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h' <;> subst_vars <;> simp [*]
      
    

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
@[simp]
theorem count_support_take_until_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.takeUntil u h).Support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp [*, List.count_cons]
      
    

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
theorem count_edges_take_until_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) (x : V) :
    (p.takeUntil u h).edges.count ⟦(u, x)⟧ ≤ 1 := by
  induction' p with u' u' v' w' ha p' ih
  · rw [mem_support_nil_iff] at h
    subst u
    simp
    
  · obtain rfl | h := h
    · simp
      
    · simp only
      split_ifs with h'
      · subst h'
        simp
        
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · rw [Sym2.eq_iff] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
            
          · cases p' <;> simp
            
          
        · apply ih
          
        
      
    

theorem support_take_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.takeUntil u h).Support ⊆ p.Support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_drop_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) :
    (p.dropUntil u h).Support ⊆ p.Support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

theorem edges_take_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).edges ⊆ p.edges :=
  fun x hx => by
  rw [← take_spec p h, edges_append, List.mem_appendₓ]
  exact Or.inl hx

theorem edges_drop_until_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.dropUntil u h).edges ⊆ p.edges :=
  fun x hx => by
  rw [← take_spec p h, edges_append, List.mem_appendₓ]
  exact Or.inr hx

theorem length_take_until_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.takeUntil u h).length ≤ p.length :=
  by
  have := congr_argₓ walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.Le.intro this

theorem length_drop_until_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.Support) : (p.dropUntil u h).length ≤ p.length :=
  by
  have := congr_argₓ walk.length (p.take_spec h)
  rw [length_append, add_commₓ] at this
  exact Nat.Le.intro this

protected theorem IsTrail.take_until {u v w : V} {p : G.Walk v w} (hc : p.IsTrail) (h : u ∈ p.Support) :
    (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsTrail.drop_until {u v w : V} {p : G.Walk v w} (hc : p.IsTrail) (h : u ∈ p.Support) :
    (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsPath.take_until {u v w : V} {p : G.Walk v w} (hc : p.IsPath) (h : u ∈ p.Support) :
    (p.takeUntil u h).IsPath :=
  IsPath.of_append_left
    (by
      rwa [← take_spec _ h] at hc)

protected theorem IsPath.drop_until {u v w : V} (p : G.Walk v w) (hc : p.IsPath) (h : u ∈ p.Support) :
    (p.dropUntil u h).IsPath :=
  IsPath.of_append_right
    (by
      rwa [← take_spec _ h] at hc)

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : (c.rotate h).Support.tail ~r c.Support.tail :=
  by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.is_rotated_append
  rw [← tail_support_append, take_spec]

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.Support) : (c.rotate h).edges ~r c.edges := by
  simp only [rotate, edges_append]
  apply List.IsRotated.trans List.is_rotated_append
  rw [← edges_append, take_spec]

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.Support) :
    (c.rotate h).IsTrail := by
  rw [is_trail_def, (c.rotate_edges h).Perm.nodup_iff]
  exact hc.edges_nodup

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit) (h : u ∈ c.Support) :
    (c.rotate h).IsCircuit := by
  refine' ⟨hc.to_trail.rotate _, _⟩
  cases c
  · exact (hc.ne_nil rfl).elim
    
  · intro hn
    have hn' := congr_argₓ length hn
    rw [rotate, length_append, add_commₓ, ← length_append, take_spec] at hn'
    simpa using hn'
    

protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.Support) :
    (c.rotate h).IsCycle := by
  refine' ⟨hc.to_circuit.rotate _, _⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup

end WalkDecomp

end Walk

/-! ### Walks to paths -/


/-- The type for paths between two vertices. -/
abbrev Path (u v : V) :=
  { p : G.Walk u v // p.IsPath }

namespace Walk

variable {G} [DecidableEq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `simple_graph.walk.bypass_is_path`.
This is packaged up in `simple_graph.walk.to_path`. -/
def bypass : ∀ {u v : V}, G.Walk u v → G.Walk u v
  | u, v, nil => nil
  | u, v, cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.Support then p'.dropUntil u hs else cons ha p'

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
theorem bypass_is_path {u v : V} (p : G.Walk u v) : p.bypass.IsPath := by
  induction p
  · simp
    
  · simp only [bypass]
    split_ifs
    · apply is_path.drop_until
      assumption
      
    · simp [*, cons_is_path_iff]
      
    

theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length := by
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
      
    

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_is_path⟩

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.Support ⊆ p.Support := by
  induction p
  · simp
    
  · simp only
    split_ifs
    · apply List.Subset.trans (support_drop_until_subset _ _)
      apply List.subset_cons_of_subsetₓ
      assumption
      
    · rw [support_cons]
      apply List.cons_subset_consₓ
      assumption
      
    

theorem support_to_path_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).Support ⊆ p.Support :=
  support_bypass_subset _

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges := by
  induction p
  · simp
    
  · simp only
    split_ifs
    · apply List.Subset.trans (edges_drop_until_subset _ _)
      apply List.subset_cons_of_subsetₓ _ p_ih
      
    · rw [edges_cons]
      exact List.cons_subset_consₓ _ p_ih
      
    

theorem edges_to_path_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _

end Walk

end SimpleGraph

