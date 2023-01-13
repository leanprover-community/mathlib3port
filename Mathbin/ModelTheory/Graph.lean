/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.graph
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Satisfiability
import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# First-Ordered Structures in Graph Theory
This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions
* `first_order.language.graph` is the language consisting of a single relation representing
adjacency.
* `simple_graph.Structure` is the first-order structure corresponding to a given simple graph.
* `first_order.language.Theory.simple_graph` is the theory of simple graphs.
* `first_order.language.simple_graph_of_structure` gives the simple graph corresponding to a model
of the theory of simple graphs.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open StructureCat

variable {L : Language.{u, v}} {α : Type w} {V : Type w'} {n : ℕ}

/-! ### Simple Graphs -/


/-- The language consisting of a single relation representing adjacency. -/
protected def graph : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit
#align first_order.language.graph FirstOrder.Language.graph

/-- The symbol representing the adjacency relation. -/
def adj : Language.graph.Relations 2 :=
  Unit.unit
#align first_order.language.adj FirstOrder.Language.adj

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
def SimpleGraph.structure (G : SimpleGraph V) : Language.graph.StructureCat V :=
  StructureCat.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => G.Adj
#align simple_graph.Structure SimpleGraph.structure

namespace Graph

instance : IsRelational Language.graph :=
  language.is_relational_mk₂

instance : Subsingleton (Language.graph.Relations n) :=
  language.subsingleton_mk₂_relations

end Graph

/-- The theory of simple graphs. -/
protected def TheoryCat.simpleGraph : Language.graph.TheoryCat :=
  {adj.Irreflexive, adj.Symmetric}
#align first_order.language.Theory.simple_graph FirstOrder.Language.TheoryCat.simpleGraph

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem TheoryCat.simple_graph_model_iff [Language.graph.StructureCat V] :
    V ⊨ Theory.simple_graph ↔
      (Irreflexive fun x y : V => RelMap adj ![x, y]) ∧
        Symmetric fun x y : V => RelMap adj ![x, y] :=
  by simp [Theory.simple_graph]
#align
  first_order.language.Theory.simple_graph_model_iff FirstOrder.Language.TheoryCat.simple_graph_model_iff

instance simple_graph_model (G : SimpleGraph V) :
    @TheoryCat.Model _ V G.StructureCat TheoryCat.simpleGraph :=
  by
  simp only [Theory.simple_graph_model_iff, rel_map_apply₂]
  exact ⟨G.loopless, G.symm⟩
#align first_order.language.simple_graph_model FirstOrder.Language.simple_graph_model

variable (V)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
def simpleGraphOfStructure [Language.graph.StructureCat V] [V ⊨ Theory.simple_graph] : SimpleGraph V
    where
  Adj x y := RelMap adj ![x, y]
  symm :=
    Relations.realize_symmetric.1
      (TheoryCat.realize_sentence_of_mem TheoryCat.simpleGraph
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  loopless :=
    Relations.realize_irreflexive.1
      (TheoryCat.realize_sentence_of_mem TheoryCat.simpleGraph (Set.mem_insert _ _))
#align first_order.language.simple_graph_of_structure FirstOrder.Language.simpleGraphOfStructure

variable {V}

@[simp]
theorem SimpleGraph.simple_graph_of_structure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.StructureCat _ = G :=
  by
  ext
  rfl
#align simple_graph.simple_graph_of_structure SimpleGraph.simple_graph_of_structure

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Structure_simple_graph_of_structure [S : Language.graph.StructureCat V]
    [V ⊨ Theory.simple_graph] : (simpleGraphOfStructure V).StructureCat = S :=
  by
  ext (n f xs)
  · exact (is_relational.empty_functions n).elim f
  · ext (n r xs)
    rw [iff_eq_eq]
    cases n
    · exact r.elim
    · cases n
      · exact r.elim
      · cases n
        · cases r
          change rel_map adj ![xs 0, xs 1] = _
          refine' congr rfl (funext _)
          simp [Fin.forall_fin_two]
        · exact r.elim
#align
  first_order.language.Structure_simple_graph_of_structure FirstOrder.Language.Structure_simple_graph_of_structure

theorem TheoryCat.simple_graph_is_satisfiable : TheoryCat.IsSatisfiable TheoryCat.simpleGraph :=
  ⟨@TheoryCat.ModelCat.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩
#align
  first_order.language.Theory.simple_graph_is_satisfiable FirstOrder.Language.TheoryCat.simple_graph_is_satisfiable

end Language

end FirstOrder

