/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Topology.Algebra.Order.Basic
import Mathbin.Topology.Constructions

/-!
# Topological lattices

In this file we define mixin classes `has_continuous_inf` and `has_continuous_sup`. We define the
class `topological_lattice` as a topological space and lattice `L` extending `has_continuous_inf`
and `has_continuous_sup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/


open Filter

open TopologicalSpace

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimum* if the map
`⊓:L×L → L` is continuous.
-/
class HasContinuousInf (L : Type _) [TopologicalSpace L] [HasInf L] : Prop where
  continuous_inf : Continuous fun p : L × L => p.1⊓p.2

/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous supremum* if the map
`⊓:L×L → L` is continuous.
-/
class HasContinuousSup (L : Type _) [TopologicalSpace L] [HasSup L] : Prop where
  continuous_sup : Continuous fun p : L × L => p.1⊔p.2

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.has_continuous_sup (L : Type _) [TopologicalSpace L] [HasInf L]
    [HasContinuousInf L] : HasContinuousSup (OrderDual L) where
  continuous_sup := @HasContinuousInf.continuous_inf L _ _ _

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.has_continuous_inf (L : Type _) [TopologicalSpace L] [HasSup L]
    [HasContinuousSup L] : HasContinuousInf (OrderDual L) where
  continuous_inf := @HasContinuousSup.continuous_sup L _ _ _

/-- Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
class TopologicalLattice (L : Type _) [TopologicalSpace L] [Lattice L] extends HasContinuousInf L, HasContinuousSup L

-- see Note [lower instance priority]
instance (priority := 100) OrderDual.topologicalLattice (L : Type _) [TopologicalSpace L] [Lattice L]
    [TopologicalLattice L] : TopologicalLattice (OrderDual L) :=
  {  }

variable {L : Type _} [TopologicalSpace L]

variable {X : Type _} [TopologicalSpace X]

@[continuity]
theorem continuous_inf [HasInf L] [HasContinuousInf L] : Continuous fun p : L × L => p.1⊓p.2 :=
  HasContinuousInf.continuous_inf

@[continuity]
theorem Continuous.inf [HasInf L] [HasContinuousInf L] {f g : X → L} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x⊓g x :=
  continuous_inf.comp (hf.prod_mk hg : _)

@[continuity]
theorem continuous_sup [HasSup L] [HasContinuousSup L] : Continuous fun p : L × L => p.1⊔p.2 :=
  HasContinuousSup.continuous_sup

@[continuity]
theorem Continuous.sup [HasSup L] [HasContinuousSup L] {f g : X → L} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x⊔g x :=
  continuous_sup.comp (hf.prod_mk hg : _)

theorem Filter.Tendsto.sup_right_nhds' {ι β} [TopologicalSpace β] [HasSup β] [HasContinuousSup β] {l : Filter ι}
    {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f⊔g) l (𝓝 (x⊔y)) :=
  (continuous_sup.Tendsto _).comp (Tendsto.prod_mk_nhds hf hg)

theorem Filter.Tendsto.sup_right_nhds {ι β} [TopologicalSpace β] [HasSup β] [HasContinuousSup β] {l : Filter ι}
    {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i⊔g i) l (𝓝 (x⊔y)) :=
  hf.sup_right_nhds' hg

theorem Filter.Tendsto.inf_right_nhds' {ι β} [TopologicalSpace β] [HasInf β] [HasContinuousInf β] {l : Filter ι}
    {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (f⊓g) l (𝓝 (x⊓y)) :=
  (continuous_inf.Tendsto _).comp (Tendsto.prod_mk_nhds hf hg)

theorem Filter.Tendsto.inf_right_nhds {ι β} [TopologicalSpace β] [HasInf β] [HasContinuousInf β] {l : Filter ι}
    {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i⊓g i) l (𝓝 (x⊓y)) :=
  hf.inf_right_nhds' hg

