/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Coloring

/-!
# Graph partitions

This module provides an interface for dealing with partitions on simple graphs. A partition of
a graph `G`, with vertices `V`, is a set `P` of disjoint nonempty subsets of `V` such that:

* The union of the subsets in `P` is `V`.

* Each element of `P` is an independent set. (Each subset contains no pair of adjacent vertices.)

Graph partitions are graph colorings that do not name their colors.  They are adjoint in the
following sense. Given a graph coloring, there is an associated partition from the set of color
classes, and given a partition, there is an associated graph coloring from using the partition's
subsets as colors.  Going from graph colorings to partitions and back makes a coloring "canonical":
all colors are given a canonical name and unused colors are removed.  Going from partitions to
graph colorings and back is the identity.

## Main definitions

* `simple_graph.partition` is a structure to represent a partition of a simple graph

* `simple_graph.partition.parts_card_le` is whether a given partition is an `n`-partition.
  (a partition with at most `n` parts).

* `simple_graph.partitionable n` is whether a given graph is `n`-partite

* `simple_graph.partition.to_coloring` creates colorings from partitions

* `simple_graph.coloring.to_partition` creates partitions from colorings

## Main statements

* `simple_graph.partitionable_iff_colorable` is that `n`-partitionability and
  `n`-colorability are equivalent.

-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- A `partition` of a simple graph `G` is a structure constituted by
* `parts`: a set of subsets of the vertices `V` of `G`
* `is_partition`: a proof that `parts` is a proper partition of `V`
* `independent`: a proof that each element of `parts` doesn't have a pair of adjacent vertices
-/
structure Partition where
  parts : Set (Set V)
  IsPartition : Setoidₓ.IsPartition parts
  Independent : ∀ s ∈ parts, IsAntichain G.Adj s

/-- Whether a partition `P` has at most `n` parts. A graph with a partition
satisfying this predicate called `n`-partite. (See `simple_graph.partitionable`.) -/
def Partition.PartsCardLe {G : SimpleGraph V} (P : G.partition) (n : ℕ) : Prop :=
  ∃ h : P.parts.Finite, h.toFinset.card ≤ n

/-- Whether a graph is `n`-partite, which is whether its vertex set
can be partitioned in at most `n` independent sets. -/
def Partitionable (n : ℕ) : Prop :=
  ∃ P : G.partition, P.PartsCardLe n

namespace Partition

variable {G} (P : G.partition)

/-- The part in the partition that `v` belongs to -/
def PartOfVertex (v : V) : Set V :=
  Classical.some (P.IsPartition.2 v)

theorem part_of_vertex_mem (v : V) : P.PartOfVertex v ∈ P.parts := by
  obtain ⟨h, -⟩ := (P.is_partition.2 v).some_spec.1
  exact h

theorem mem_part_of_vertex (v : V) : v ∈ P.PartOfVertex v := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := (P.is_partition.2 v).some_spec
  exact h2.1

theorem part_of_vertex_ne_of_adj {v w : V} (h : G.Adj v w) : P.PartOfVertex v ≠ P.PartOfVertex w := by
  intro hn
  have hw := P.mem_part_of_vertex w
  rw [← hn] at hw
  exact P.independent _ (P.part_of_vertex_mem v) (P.mem_part_of_vertex v) hw (G.ne_of_adj h) h

/-- Create a coloring using the parts themselves as the colors.
Each vertex is colored by the part it's contained in. -/
def toColoring : G.Coloring P.parts :=
  (Coloring.mk fun v => ⟨P.PartOfVertex v, P.part_of_vertex_mem v⟩) fun _ _ hvw => by
    rw [Ne.def, Subtype.mk_eq_mk]
    exact P.part_of_vertex_ne_of_adj hvw

/-- Like `simple_graph.partition.to_coloring` but uses `set V` as the coloring type. -/
def toColoring' : G.Coloring (Set V) :=
  (Coloring.mk P.PartOfVertex) fun _ _ hvw => P.part_of_vertex_ne_of_adj hvw

theorem to_colorable [Fintype P.parts] : G.Colorable (Fintype.card P.parts) :=
  P.toColoring.to_colorable

end Partition

variable {G}

/-- Creates a partition from a coloring. -/
@[simps]
def Coloring.toPartition {α : Type v} (C : G.Coloring α) : G.partition where
  parts := C.ColorClasses
  IsPartition := C.color_classes_is_partition
  Independent := by
    rintro s ⟨c, rfl⟩
    apply C.color_classes_independent

/-- The partition where every vertex is in its own part. -/
@[simps]
instance : Inhabited (Partition G) :=
  ⟨G.selfColoring.toPartition⟩

theorem partitionable_iff_colorable {n : ℕ} : G.Partitionable n ↔ G.Colorable n := by
  constructor
  · rintro ⟨P, hf, h⟩
    haveI : Fintype P.parts := hf.fintype
    rw [Set.Finite.card_to_finset] at h
    apply P.to_colorable.mono h
    
  · rintro ⟨C⟩
    refine' ⟨C.to_partition, C.color_classes_finite, le_transₓ _ (Fintype.card_fin n).le⟩
    generalize_proofs h
    haveI : Fintype C.color_classes := C.color_classes_finite.fintype
    rw [h.card_to_finset]
    exact C.card_color_classes_le
    

end SimpleGraph

