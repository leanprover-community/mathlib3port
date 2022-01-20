import Mathbin.Combinatorics.SimpleGraph.Basic

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

* `simple_graph.is_trail`, `simple_graph.is_path`, and `simple_graph.is_cycle`.

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
inductive walk : V → V → Type u
  | nil {u : V} : walk u u
  | cons {u v w : V} (h : G.adj u v) (p : walk v w) : walk u w
  deriving DecidableEq

attribute [refl] walk.nil

instance walk.inhabited (v : V) : Inhabited (G.walk v v) :=
  ⟨by
    rfl⟩

namespace Walk

variable {G}

theorem exists_eq_cons_of_ne :
    ∀ {u v : V} hne : u ≠ v p : G.walk u v, ∃ (w : V)(h : G.adj u w)(p' : G.walk w v), p = cons h p'
  | _, _, hne, nil => (hne rfl).elim
  | _, _, _, cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges along it. -/
def length : ∀ {u v : V}, G.walk u v → ℕ
  | _, _, nil => 0
  | _, _, cons _ q => q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : ∀ {u v w : V}, G.walk u v → G.walk v w → G.walk u w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverse_aux : ∀ {u v w : V}, G.walk u v → G.walk u w → G.walk v w
  | _, _, _, nil, q => q
  | _, _, _, cons h p, q => reverse_aux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u :=
  w.reverse_aux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def get_vert : ∀ {u v : V} p : G.walk u v n : ℕ, V
  | u, v, nil, _ => u
  | u, v, cons _ _, 0 => u
  | u, v, cons _ q, n + 1 => q.get_vert n

@[simp]
theorem cons_append {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
    (cons h p).append q = cons h (p.append q) :=
  rfl

@[simp]
theorem cons_nil_append {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h nil).append p = cons h p :=
  rfl

@[simp]
theorem append_nil : ∀ {u v : V} p : G.walk u v, p.append nil = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    rw [cons_append, append_nil]

@[simp]
theorem nil_append {u v : V} (p : G.walk u v) : nil.append p = p :=
  rfl

theorem append_assoc :
    ∀ {u v w x : V} p : G.walk u v q : G.walk v w r : G.walk w x, p.append (q.append r) = (p.append q).append r
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    dunfold append
    rw [append_assoc]

@[simp]
theorem reverse_nil {u : V} : (nil : G.walk u u).reverse = nil :=
  rfl

theorem reverse_singleton {u v : V} (h : G.adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl

@[simp]
theorem cons_reverse_aux {u v w x : V} (p : G.walk u v) (q : G.walk w x) (h : G.adj w u) :
    (cons h p).reverseAux q = p.reverse_aux (cons (G.symm h) q) :=
  rfl

@[simp]
protected theorem append_reverse_aux :
    ∀ {u v w x : V} p : G.walk u v q : G.walk v w r : G.walk u x,
      (p.append q).reverseAux r = q.reverse_aux (p.reverse_aux r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => append_reverse_aux p' q (cons (G.symm h) r)

@[simp]
protected theorem reverse_aux_append :
    ∀ {u v w x : V} p : G.walk u v q : G.walk u w r : G.walk w x,
      (p.reverse_aux q).append r = p.reverse_aux (q.append r)
  | _, _, _, _, nil, _, _ => rfl
  | _, _, _, _, cons h p', q, r => by
    simp [reverse_aux_append p' (cons (G.symm h) q) r]

protected theorem reverse_aux_eq_reverse_append {u v w : V} (p : G.walk u v) (q : G.walk u w) :
    p.reverse_aux q = p.reverse.append q := by
  simp [reverse]

@[simp]
theorem reverse_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by
  simp [reverse]

@[simp]
theorem reverse_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  simp [reverse]

@[simp]
theorem reverse_reverse : ∀ {u v : V} p : G.walk u v, p.reverse.reverse = p
  | _, _, nil => rfl
  | _, _, cons h p => by
    simp [reverse_reverse]

@[simp]
theorem length_nil {u : V} : (nil : G.walk u u).length = 0 :=
  rfl

@[simp]
theorem length_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).length = p.length + 1 :=
  rfl

@[simp]
theorem length_append : ∀ {u v w : V} p : G.walk u v q : G.walk v w, (p.append q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [length_append, add_left_commₓ, add_commₓ]

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:377:22: warning: unsupported simp config option: iota_eqn
@[simp]
protected theorem length_reverse_aux :
    ∀ {u v w : V} p : G.walk u v q : G.walk u w, (p.reverse_aux q).length = p.length + q.length
  | _, _, _, nil, _ => by
    simp
  | _, _, _, cons _ _, _ => by
    simp [length_reverse_aux, Nat.add_succ, Nat.succ_add]

@[simp]
theorem length_reverse {u v : V} (p : G.walk u v) : p.reverse.length = p.length := by
  simp [reverse]

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : ∀ {u v : V}, G.walk u v → List V
  | u, v, nil => [u]
  | u, v, cons h p => u :: p.support

/-- The `edges` of a walk is the list of edges it visits in order. -/
def edges : ∀ {u v : V}, G.walk u v → List (Sym2 V)
  | u, v, nil => []
  | u, v, @cons _ _ _ x _ h p => ⟦(u, x)⟧ :: p.edges

@[simp]
theorem support_nil {u : V} : (nil : G.walk u u).Support = [u] :=
  rfl

@[simp]
theorem support_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).Support = u :: p.support :=
  rfl

theorem support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    (p.append p').Support = p.support ++ p'.support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
theorem support_reverse {u v : V} (p : G.walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]

theorem support_ne_nil {u v : V} (p : G.walk u v) : p.support ≠ [] := by
  cases p <;> simp

theorem tail_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    (p.append p').Support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]

theorem support_eq_cons {u v : V} (p : G.walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support := by
  cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support := by
  induction p <;> simp [*]

theorem mem_support_iff {u v w : V} (p : G.walk u v) : w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by
  cases p <;> simp

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    t ∈ (p.append p').Support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_appendₓ]

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.walk u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

@[simp]
theorem mem_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    t ∈ (p.append p').Support ↔ t ∈ p.support ∨ t ∈ p'.support := by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  by_cases' h : t = v <;>
    by_cases' h' : t = u <;>
      subst_vars <;>
        try
            have := Ne.symm h' <;>
          simp [*]

theorem coe_support {u v : V} (p : G.walk u v) : (p.support : Multiset V) = {u} + p.support.tail := by
  cases p <;> rfl

theorem coe_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    ((p.append p').Support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
    ((p.append p').Support : Multiset V) = p.support + p'.support - {v} := by
  rw [support_append, ← Multiset.coe_add]
  simp only [coe_support]
  rw [add_commₓ {v}]
  simp only [← add_assocₓ, add_tsub_cancel_right]

theorem chain_adj_support_aux : ∀ {u v w : V} h : G.adj u v p : G.walk v w, List.Chain G.adj u p.support
  | _, _, _, h, nil => List.Chain.cons h List.Chain.nil
  | _, _, _, h, cons h' p => List.Chain.cons h (chain_adj_support_aux h' p)

theorem chain_adj_support : ∀ {u v : V} p : G.walk u v, List.Chain' G.adj p.support
  | _, _, nil => List.Chain.nil
  | _, _, cons h p => chain_adj_support_aux h p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form to avoid unsightly coercions. -/
theorem edges_subset_edge_set : ∀ {u v : V} p : G.walk u v {e : Sym2 V} h : e ∈ p.edges, e ∈ G.edge_set
  | _, _, cons h' p', e, h => by
    rcases h with ⟨rfl, h⟩ <;> solve_by_elim

@[simp]
theorem edges_nil {u : V} : (nil : G.walk u u).edges = [] :=
  rfl

@[simp]
theorem edges_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).edges = ⟦(u, v)⟧ :: p.edges :=
  rfl

@[simp]
theorem edges_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) : (p.append p').edges = p.edges ++ p'.edges := by
  induction p <;> simp [*]

@[simp]
theorem edges_reverse {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse := by
  induction p <;> simp [*, Sym2.eq_swap]

@[simp]
theorem length_support {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp]
theorem length_edges {u v : V} (p : G.walk u v) : p.edges.length = p.length := by
  induction p <;> simp [*]

theorem mem_support_of_mem_edges : ∀ {t u v w : V} p : G.walk v w he : ⟦(t, u)⟧ ∈ p.edges, t ∈ p.support
  | t, u, v, w, cons h p', he => by
    simp only [support_cons, edges_cons, List.mem_cons_iff, Quotientₓ.eq] at he⊢
    rcases he with ((he | he) | he)
    · exact Or.inl rfl
      
    · exact Or.inr (start_mem_support _)
      
    · exact Or.inr (mem_support_of_mem_edges _ he)
      

theorem edges_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) : p.edges.nodup := by
  induction p
  · simp
    
  · simp only [edges_cons, support_cons, List.nodup_cons] at h⊢
    exact ⟨fun h' => h.1 (mem_support_of_mem_edges p_p h'), p_ih h.2⟩
    

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {u v : V} (p : G.walk u v) : Prop where
  edges_nodup : p.edges.nodup

-- ././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure
/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure is_path {u v : V} (p : G.walk u v) extends
  "././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.support.nodup

-- ././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure is_circuit {u : V} (p : G.walk u u) extends
  "././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure" : Prop where
  ne_nil : p ≠ nil

-- ././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle [DecidableEq V] {u : V} (p : G.walk u u) extends
  "././Mathport/Syntax/Translate/Basic.lean:1165:11: unsupported: advanced extends in structure" : Prop where
  support_nodup : p.support.tail.nodup

theorem is_trail_def {u v : V} (p : G.walk u v) : p.is_trail ↔ p.edges.nodup :=
  ⟨is_trail.edges_nodup, fun h => ⟨h⟩⟩

theorem is_path.mk' {u v : V} {p : G.walk u v} (h : p.support.nodup) : is_path p :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

theorem is_path_def {u v : V} (p : G.walk u v) : p.is_path ↔ p.support.nodup :=
  ⟨is_path.support_nodup, is_path.mk'⟩

theorem is_cycle_def [DecidableEq V] {u : V} (p : G.walk u u) :
    p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem is_trail.nil {u : V} : (nil : G.walk u u).IsTrail :=
  ⟨by
    simp [edges]⟩

theorem is_trail.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} : (cons h p).IsTrail → p.is_trail := by
  simp [is_trail_def]

@[simp]
theorem cons_is_trail_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
    (cons h p).IsTrail ↔ p.is_trail ∧ ⟦(u, v)⟧ ∉ p.edges := by
  simp [is_trail_def, and_comm]

theorem is_trail.reverse {u v : V} (p : G.walk u v) (h : p.is_trail) : p.reverse.is_trail := by
  simpa [is_trail_def] using h

@[simp]
theorem reverse_is_trail_iff {u v : V} (p : G.walk u v) : p.reverse.is_trail ↔ p.is_trail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try
        rw [reverse_reverse]
      

theorem is_trail.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w} (h : (p.append q).IsTrail) : p.is_trail :=
  by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩

theorem is_trail.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w} (h : (p.append q).IsTrail) :
    q.is_trail := by
  rw [is_trail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩

theorem is_trail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.walk u v} (h : p.is_trail) (e : Sym2 V) :
    p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e

theorem is_trail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.walk u v} (h : p.is_trail) {e : Sym2 V}
    (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he

@[simp]
theorem is_path.nil {u : V} : (nil : G.walk u u).IsPath := by
  fconstructor <;> simp

theorem is_path.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} : (cons h p).IsPath → p.is_path := by
  simp [is_path_def]

@[simp]
theorem cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) : (cons h p).IsPath ↔ p.is_path ∧ u ∉ p.support :=
  by
  constructor <;> simp (config := { contextual := true })[is_path_def]

theorem is_path.reverse {u v : V} {p : G.walk u v} (h : p.is_path) : p.reverse.is_path := by
  simpa [is_path_def] using h

@[simp]
theorem is_path_reverse_iff {u v : V} (p : G.walk u v) : p.reverse.is_path ↔ p.is_path := by
  constructor <;> intro h <;> convert h.reverse <;> simp

theorem is_path.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w} : (p.append q).IsPath → p.is_path := by
  simp only [is_path_def, support_append]
  exact List.nodup_of_nodup_append_left

theorem is_path.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w} (h : (p.append q).IsPath) : q.is_path :=
  by
  rw [← is_path_reverse_iff] at h⊢
  rw [reverse_append] at h
  apply h.of_append_left

end Walk

end SimpleGraph

