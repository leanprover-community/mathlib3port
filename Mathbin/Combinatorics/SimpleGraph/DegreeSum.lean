import Mathbin.Combinatorics.SimpleGraph.Basic 
import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Nat.Parity 
import Mathbin.Data.Zmod.Parity

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- A `dart` is a directed edge, consisting of an ordered pair of adjacent vertices,
  thought of as being a directed edge.
- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.even_card_odd_degree_vertices` is the handshaking lemma.
- `simple_graph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/


open Finset

open_locale BigOperators

namespace SimpleGraph

universe u

variable{V : Type u}(G : SimpleGraph V)

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
/-- A dart is a directed edge, consisting of an ordered pair of adjacent vertices. -/
@[ext #[], derive #[expr decidable_eq]]
structure dart := (fst snd : V) (is_adj : G.adj fst snd)

instance dart.fintype [Fintype V] [DecidableRel G.adj] : Fintype G.dart :=
  Fintype.ofEquiv (Σv, G.neighbor_set v)
    { toFun := fun s => ⟨s.fst, s.snd, s.snd.property⟩, invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩,
      left_inv :=
        fun s =>
          by 
            ext <;> simp ,
      right_inv :=
        fun d =>
          by 
            ext <;> simp  }

variable{G}

/-- The edge associated to the dart. -/
def dart.edge (d : G.dart) : Sym2 V :=
  «expr⟦ ⟧» (d.fst, d.snd)

@[simp]
theorem dart.edge_mem (d : G.dart) : d.edge ∈ G.edge_set :=
  d.is_adj

/-- The dart with reversed orientation from a given dart. -/
def dart.rev (d : G.dart) : G.dart :=
  ⟨d.snd, d.fst, G.symm d.is_adj⟩

@[simp]
theorem dart.rev_edge (d : G.dart) : d.rev.edge = d.edge :=
  Sym2.eq_swap

@[simp]
theorem dart.rev_rev (d : G.dart) : d.rev.rev = d :=
  dart.ext _ _ rfl rfl

@[simp]
theorem dart.rev_involutive : Function.Involutive (dart.rev : G.dart → G.dart) :=
  dart.rev_rev

theorem dart.rev_ne (d : G.dart) : d.rev ≠ d :=
  by 
    cases' d with f s h 
    simp only [dart.rev, not_and, Ne.def]
    rintro rfl 
    exact False.elim (G.loopless _ h)

theorem dart_edge_eq_iff (d₁ d₂ : G.dart) : d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.rev :=
  by 
    cases' d₁ with s₁ t₁ h₁ 
    cases' d₂ with s₂ t₂ h₂ 
    simp only [dart.edge, dart.rev_edge, dart.rev]
    rw [Sym2.eq_iff]

variable(G)

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. --/
def dart_of_neighbor_set (v : V) (w : G.neighbor_set v) : G.dart :=
  ⟨v, w, w.property⟩

theorem dart_of_neighbor_set_injective (v : V) : Function.Injective (G.dart_of_neighbor_set v) :=
  fun e₁ e₂ h =>
    by 
      injection h with h₁ h₂ 
      exact Subtype.ext h₂

instance dart.inhabited [Inhabited V] [Inhabited (G.neighbor_set (default _))] : Inhabited G.dart :=
  ⟨G.dart_of_neighbor_set (default _) (default _)⟩

section DegreeSum

variable[Fintype V][DecidableRel G.adj]

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dart_fst_fiber
[decidable_eq V]
(v : V) : «expr = »(univ.filter (λ d : G.dart, «expr = »(d.fst, v)), univ.image (G.dart_of_neighbor_set v)) :=
begin
  ext [] [ident d] [],
  simp [] [] ["only"] ["[", expr mem_image, ",", expr true_and, ",", expr mem_filter, ",", expr set_coe.exists, ",", expr mem_univ, ",", expr exists_prop_of_true, "]"] [] [],
  split,
  { rintro [ident rfl],
    exact [expr ⟨_, d.is_adj, dart.ext _ _ rfl rfl⟩] },
  { rintro ["⟨", ident e, ",", ident he, ",", ident rfl, "⟩"],
    refl }
end

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dart_fst_fiber_card_eq_degree
[decidable_eq V]
(v : V) : «expr = »((univ.filter (λ d : G.dart, «expr = »(d.fst, v))).card, G.degree v) :=
begin
  have [ident hh] [] [":=", expr card_image_of_injective univ (G.dart_of_neighbor_set_injective v)],
  rw ["[", expr finset.card_univ, ",", expr card_neighbor_set_eq_degree, "]"] ["at", ident hh],
  rwa [expr dart_fst_fiber] []
end

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dart_card_eq_sum_degrees : «expr = »(fintype.card G.dart, «expr∑ , »((v), G.degree v)) :=
begin
  haveI [ident h] [":", expr decidable_eq V] [],
  { classical,
    apply_instance },
  simp [] [] ["only"] ["[", "<-", expr card_univ, ",", "<-", expr dart_fst_fiber_card_eq_degree, "]"] [] [],
  exact [expr card_eq_sum_card_fiberwise (by simp [] [] [] [] [] [])]
end

variable{G}[DecidableEq V]

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dart.edge_fiber (d : G.dart) : «expr = »(univ.filter (λ d' : G.dart, «expr = »(d'.edge, d.edge)), {d, d.rev}) :=
finset.ext (λ d', by simpa [] [] [] [] [] ["using", expr dart_edge_eq_iff d' d])

variable(G)

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dart_edge_fiber_card
(e : sym2 V)
(h : «expr ∈ »(e, G.edge_set)) : «expr = »((univ.filter (λ d : G.dart, «expr = »(d.edge, e))).card, 2) :=
begin
  refine [expr quotient.ind (λ p h, _) e h],
  cases [expr p] ["with", ident v, ident w],
  let [ident d] [":", expr G.dart] [":=", expr ⟨v, w, h⟩],
  convert [] [expr congr_arg card d.edge_fiber] [],
  rw ["[", expr card_insert_of_not_mem, ",", expr card_singleton, "]"] [],
  rw ["[", expr mem_singleton, "]"] [],
  exact [expr d.rev_ne.symm]
end

theorem dart_card_eq_twice_card_edges : Fintype.card G.dart = 2*G.edge_finset.card :=
  by 
    rw [←card_univ]
    rw
      [@card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset
        fun d h =>
          by 
            rw [mem_edge_finset]
            apply dart.edge_mem]
    rw [←mul_commₓ, sum_const_nat]
    intro e h 
    apply G.dart_edge_fiber_card e 
    rwa [←mem_edge_finset]

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : (∑v, G.degree v) = 2*G.edge_finset.card :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

end DegreeSum

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices
[fintype V]
[decidable_rel G.adj] : even (univ.filter (λ v, odd (G.degree v))).card :=
begin
  classical,
  have [ident h] [] [":=", expr congr_arg (λ n, «expr↑ »(n) : exprℕ() → zmod 2) G.sum_degrees_eq_twice_card_edges],
  simp [] [] ["only"] ["[", expr zmod.nat_cast_self, ",", expr zero_mul, ",", expr nat.cast_mul, "]"] [] ["at", ident h],
  rw ["[", expr nat.cast_sum, ",", "<-", expr sum_filter_ne_zero, "]"] ["at", ident h],
  rw [expr @sum_congr _ _ _ _ (λ v, (G.degree v : zmod 2)) (λ v, (1 : zmod 2)) _ rfl] ["at", ident h],
  { simp [] [] ["only"] ["[", expr filter_congr_decidable, ",", expr mul_one, ",", expr nsmul_eq_mul, ",", expr sum_const, ",", expr ne.def, "]"] [] ["at", ident h],
    rw ["<-", expr zmod.eq_zero_iff_even] [],
    convert [] [expr h] [],
    ext [] [ident v] [],
    rw ["<-", expr zmod.ne_zero_iff_odd] [],
    congr' [] [] },
  { intros [ident v],
    simp [] [] ["only"] ["[", expr true_and, ",", expr mem_filter, ",", expr mem_univ, ",", expr ne.def, "]"] [] [],
    rw ["[", expr zmod.eq_zero_iff_even, ",", expr zmod.eq_one_iff_odd, ",", expr nat.odd_iff_not_even, ",", expr imp_self, "]"] [],
    trivial }
end

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem odd_card_odd_degree_vertices_ne
[fintype V]
[decidable_eq V]
[decidable_rel G.adj]
(v : V)
(h : odd (G.degree v)) : odd (univ.filter (λ w, «expr ∧ »(«expr ≠ »(w, v), odd (G.degree w)))).card :=
begin
  rcases [expr G.even_card_odd_degree_vertices, "with", "⟨", ident k, ",", ident hg, "⟩"],
  have [ident hk] [":", expr «expr < »(0, k)] [],
  { have [ident hh] [":", expr (filter (λ v : V, odd (G.degree v)) univ).nonempty] [],
    { use [expr v],
      simp [] [] ["only"] ["[", expr true_and, ",", expr mem_filter, ",", expr mem_univ, "]"] [] [],
      use [expr h] },
    rwa ["[", "<-", expr card_pos, ",", expr hg, ",", expr zero_lt_mul_left, "]"] ["at", ident hh],
    exact [expr zero_lt_two] },
  have [ident hc] [":", expr «expr = »(λ
    w : V, «expr ∧ »(«expr ≠ »(w, v), odd (G.degree w)), λ w : V, «expr ∧ »(odd (G.degree w), «expr ≠ »(w, v)))] [],
  { ext [] [ident w] [],
    rw [expr and_comm] [] },
  simp [] [] ["only"] ["[", expr hc, ",", expr filter_congr_decidable, "]"] [] [],
  rw ["[", "<-", expr filter_filter, ",", expr filter_ne', ",", expr card_erase_of_mem, "]"] [],
  { use [expr «expr - »(k, 1)],
    rw ["[", expr nat.pred_eq_succ_iff, ",", expr hg, ",", expr mul_tsub, ",", expr tsub_add_eq_add_tsub, ",", expr eq_comm, ",", expr tsub_eq_iff_eq_add_of_le, "]"] [],
    { ring [] },
    { exact [expr add_le_add_right (zero_le _) 2] },
    { exact [expr nat.mul_le_mul_left _ hk] } },
  { simpa [] [] ["only"] ["[", expr true_and, ",", expr mem_filter, ",", expr mem_univ, "]"] [] [] }
end

-- error in Combinatorics.SimpleGraph.DegreeSum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_ne_odd_degree_of_exists_odd_degree
[fintype V]
[decidable_rel G.adj]
(v : V)
(h : odd (G.degree v)) : «expr∃ , »((w : V), «expr ∧ »(«expr ≠ »(w, v), odd (G.degree w))) :=
begin
  haveI [] [":", expr decidable_eq V] [],
  { classical,
    apply_instance },
  rcases [expr G.odd_card_odd_degree_vertices_ne v h, "with", "⟨", ident k, ",", ident hg, "⟩"],
  have [ident hg'] [":", expr «expr > »((filter (λ
      w : V, «expr ∧ »(«expr ≠ »(w, v), odd (G.degree w))) univ).card, 0)] [],
  { rw [expr hg] [],
    apply [expr nat.succ_pos] },
  rcases [expr card_pos.mp hg', "with", "⟨", ident w, ",", ident hw, "⟩"],
  simp [] [] ["only"] ["[", expr true_and, ",", expr mem_filter, ",", expr mem_univ, ",", expr ne.def, "]"] [] ["at", ident hw],
  exact [expr ⟨w, hw⟩]
end

end SimpleGraph

