/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
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

variable {V : Type u} (G : SimpleGraph V)

/-- A dart is a directed edge, consisting of an ordered pair of adjacent vertices. -/
@[ext]
structure Dart where
  (fst snd : V)
  is_adj : G.Adj fst snd
  deriving DecidableEq

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σv, G.NeighborSet v)
    { toFun := fun s => ⟨s.fst, s.snd, s.snd.property⟩, invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩,
      left_inv := fun s => by
        ext <;> simp ,
      right_inv := fun d => by
        ext <;> simp }

variable {G}

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  ⟦(d.fst, d.snd)⟧

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.EdgeSet :=
  d.is_adj

/-- The dart with reversed orientation from a given dart. -/
def Dart.rev (d : G.Dart) : G.Dart :=
  ⟨d.snd, d.fst, G.symm d.is_adj⟩

@[simp]
theorem Dart.rev_edge (d : G.Dart) : d.rev.edge = d.edge :=
  Sym2.eq_swap

@[simp]
theorem Dart.rev_rev (d : G.Dart) : d.rev.rev = d :=
  Dart.ext _ _ rfl rfl

@[simp]
theorem Dart.rev_involutive : Function.Involutive (Dart.rev : G.Dart → G.Dart) :=
  dart.rev_rev

theorem Dart.rev_ne (d : G.Dart) : d.rev ≠ d := by
  cases' d with f s h
  simp only [dart.rev, not_and, Ne.def]
  rintro rfl
  exact False.elim (G.loopless _ h)

theorem dart_edge_eq_iff (d₁ d₂ : G.Dart) : d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.rev := by
  cases' d₁ with s₁ t₁ h₁
  cases' d₂ with s₂ t₂ h₂
  simp only [dart.edge, dart.rev_edge, dart.rev]
  rw [Sym2.eq_iff]

variable (G)

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. --/
def dartOfNeighborSet (v : V) (w : G.NeighborSet v) : G.Dart :=
  ⟨v, w, w.property⟩

theorem dart_of_neighbor_set_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) := fun e₁ e₂ h => by
  injection h with h₁ h₂
  exact Subtype.ext h₂

instance Dart.inhabited [Inhabited V] [Inhabited (G.NeighborSet default)] : Inhabited G.Dart :=
  ⟨G.dartOfNeighborSet default default⟩

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v) = univ.Image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_andₓ, mem_filter, SetCoe.exists, mem_univ, exists_prop_of_true]
  constructor
  · rintro rfl
    exact ⟨_, d.is_adj, dart.ext _ _ rfl rfl⟩
    
  · rintro ⟨e, he, rfl⟩
    rfl
    

theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v).card = G.degree v := by
  have hh := card_image_of_injective univ (G.dart_of_neighbor_set_injective v)
  rw [Finset.card_univ, card_neighbor_set_eq_degree] at hh
  rwa [dart_fst_fiber]

theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  have h : DecidableEq V := by
    classical
    infer_instance
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact
    card_eq_sum_card_fiberwise
      (by
        simp )

variable {G} [DecidableEq V]

theorem Dart.edge_fiber (d : G.Dart) : (univ.filter fun d' : G.Dart => d'.edge = d.edge) = {d, d.rev} :=
  Finset.ext fun d' => by
    simpa using dart_edge_eq_iff d' d

variable (G)

theorem dart_edge_fiber_card (e : Sym2 V) (h : e ∈ G.EdgeSet) : (univ.filter fun d : G.Dart => d.edge = e).card = 2 :=
  by
  refine' Quotientₓ.ind (fun p h => _) e h
  cases' p with v w
  let d : G.dart := ⟨v, w, h⟩
  convert congr_argₓ card d.edge_fiber
  rw [card_insert_of_not_mem, card_singleton]
  rw [mem_singleton]
  exact d.rev_ne.symm

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
  rw [← card_univ]
  rw
    [@card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset fun d h => by
      rw [mem_edge_finset]
      apply dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edge_finset]

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : (∑ v, G.degree v) = 2 * G.edgeFinset.card :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

end DegreeSum

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even (univ.filter fun v => Odd (G.degree v)).card := by
  classical
  have h := congr_argₓ (fun n => ↑n : ℕ → Zmod 2) G.sum_degrees_eq_twice_card_edges
  simp only [Zmod.nat_cast_self, zero_mul, Nat.cast_mulₓ] at h
  rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
  rw [@sum_congr _ _ _ _ (fun v => (G.degree v : Zmod 2)) (fun v => (1 : Zmod 2)) _ rfl] at h
  · simp only [filter_congr_decidable, mul_oneₓ, nsmul_eq_mul, sum_const, Ne.def] at h
    rw [← Zmod.eq_zero_iff_even]
    convert h
    ext v
    rw [← Zmod.ne_zero_iff_odd]
    congr
    
  · intro v
    simp only [true_andₓ, mem_filter, mem_univ, Ne.def]
    rw [Zmod.eq_zero_iff_even, Zmod.eq_one_iff_odd, Nat.odd_iff_not_even, imp_self]
    trivial
    

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd (univ.filter fun w => w ≠ v ∧ Odd (G.degree w)).card := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : (filter (fun v : V => Odd (G.degree v)) univ).Nonempty := by
      use v
      simp only [true_andₓ, mem_filter, mem_univ]
      use h
    rwa [← card_pos, hg, zero_lt_mul_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [hc, filter_congr_decidable]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine' ⟨k - 1, tsub_eq_of_eq_add <| hg.trans _⟩
    rw [add_assocₓ, one_add_one_eq_two, ← Nat.mul_succ]
    congr
    exact (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 hk).symm
    
  · simpa only [true_andₓ, mem_filter, mem_univ]
    

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V) (h : Odd (G.degree v)) :
    ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  have : DecidableEq V := by
    classical
    infer_instance
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : (filter (fun w : V => w ≠ v ∧ Odd (G.degree w)) univ).card > 0 := by
    rw [hg]
    apply Nat.succ_posₓ
  rcases card_pos.mp hg' with ⟨w, hw⟩
  simp only [true_andₓ, mem_filter, mem_univ, Ne.def] at hw
  exact ⟨w, hw⟩

end SimpleGraph

