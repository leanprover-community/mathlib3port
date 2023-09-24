/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import Combinatorics.SimpleGraph.Connectivity
import Data.Nat.Lattice

#align_import combinatorics.simple_graph.metric from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# Graph metric

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines the `simple_graph.dist` function, which takes
pairs of vertices to the length of the shortest walk between them.

## Main definitions

- `simple_graph.dist` is the graph metric.

## Todo

- Provide an additional computable version of `simple_graph.dist`
  for when `G` is connected.

- Evaluate `nat` vs `enat` for the codomain of `dist`, or potentially
  having an additional `edist` when the objects under consideration are
  disconnected graphs.

- When directed graphs exist, a directed notion of distance,
  likely `enat`-valued.

## Tags

graph metric, distance

-/


namespace SimpleGraph

variable {V : Type _} (G : SimpleGraph V)

/-! ## Metric -/


#print SimpleGraph.dist /-
/-- The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`. -/
noncomputable def dist (u v : V) : ℕ :=
  sInf (Set.range (Walk.length : G.Walk u v → ℕ))
#align simple_graph.dist SimpleGraph.dist
-/

variable {G}

#print SimpleGraph.Reachable.exists_walk_of_dist /-
protected theorem Reachable.exists_walk_of_dist {u v : V} (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)
#align simple_graph.reachable.exists_walk_of_dist SimpleGraph.Reachable.exists_walk_of_dist
-/

#print SimpleGraph.Connected.exists_walk_of_dist /-
protected theorem Connected.exists_walk_of_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (hconn u v).exists_walk_of_dist
#align simple_graph.connected.exists_walk_of_dist SimpleGraph.Connected.exists_walk_of_dist
-/

#print SimpleGraph.dist_le /-
theorem dist_le {u v : V} (p : G.Walk u v) : G.dist u v ≤ p.length :=
  Nat.sInf_le ⟨p, rfl⟩
#align simple_graph.dist_le SimpleGraph.dist_le
-/

#print SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable /-
@[simp]
theorem dist_eq_zero_iff_eq_or_not_reachable {u v : V} :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist, Nat.sInf_eq_zero, reachable]
#align simple_graph.dist_eq_zero_iff_eq_or_not_reachable SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable
-/

#print SimpleGraph.dist_self /-
theorem dist_self {v : V} : dist G v v = 0 := by simp
#align simple_graph.dist_self SimpleGraph.dist_self
-/

#print SimpleGraph.Reachable.dist_eq_zero_iff /-
protected theorem Reachable.dist_eq_zero_iff {u v : V} (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]
#align simple_graph.reachable.dist_eq_zero_iff SimpleGraph.Reachable.dist_eq_zero_iff
-/

#print SimpleGraph.Reachable.pos_dist_of_ne /-
protected theorem Reachable.pos_dist_of_ne {u v : V} (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])
#align simple_graph.reachable.pos_dist_of_ne SimpleGraph.Reachable.pos_dist_of_ne
-/

#print SimpleGraph.Connected.dist_eq_zero_iff /-
protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) {u v : V} :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]
#align simple_graph.connected.dist_eq_zero_iff SimpleGraph.Connected.dist_eq_zero_iff
-/

#print SimpleGraph.Connected.pos_dist_of_ne /-
protected theorem Connected.pos_dist_of_ne {u v : V} (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [hconn.dist_eq_zero_iff, hne])
#align simple_graph.connected.pos_dist_of_ne SimpleGraph.Connected.pos_dist_of_ne
-/

#print SimpleGraph.dist_eq_zero_of_not_reachable /-
theorem dist_eq_zero_of_not_reachable {u v : V} (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]
#align simple_graph.dist_eq_zero_of_not_reachable SimpleGraph.dist_eq_zero_of_not_reachable
-/

#print SimpleGraph.nonempty_of_pos_dist /-
theorem nonempty_of_pos_dist {u v : V} (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h
#align simple_graph.nonempty_of_pos_dist SimpleGraph.nonempty_of_pos_dist
-/

#print SimpleGraph.Connected.dist_triangle /-
protected theorem Connected.dist_triangle (hconn : G.Connected) {u v w : V} :
    G.dist u w ≤ G.dist u v + G.dist v w :=
  by
  obtain ⟨p, hp⟩ := hconn.exists_walk_of_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_of_dist v w
  rw [← hp, ← hq, ← walk.length_append]
  apply dist_le
#align simple_graph.connected.dist_triangle SimpleGraph.Connected.dist_triangle
-/

private theorem dist_comm_aux {u v : V} (h : G.Reachable u v) : G.dist u v ≤ G.dist v u :=
  by
  obtain ⟨p, hp⟩ := h.symm.exists_walk_of_dist
  rw [← hp, ← walk.length_reverse]
  apply dist_le

#print SimpleGraph.dist_comm /-
theorem dist_comm {u v : V} : G.dist u v = G.dist v u :=
  by
  by_cases h : G.reachable u v
  · apply le_antisymm (dist_comm_aux h) (dist_comm_aux h.symm)
  · have h' : ¬G.reachable v u := fun h' => absurd h'.symm h
    simp [h, h', dist_eq_zero_of_not_reachable]
#align simple_graph.dist_comm SimpleGraph.dist_comm
-/

end SimpleGraph

