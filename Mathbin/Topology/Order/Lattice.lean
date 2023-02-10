/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module topology.order.lattice
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.Constructions

/-!
# Topological lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define mixin classes `has_continuous_inf` and `has_continuous_sup`. We define the
class `topological_lattice` as a topological space and lattice `L` extending `has_continuous_inf`
and `has_continuous_sup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/


open Filter

open Topology

#print ContinuousInf /-
/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be an infimum. Then `L` is said to have *(jointly) continuous infimum* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousInf (L : Type _) [TopologicalSpace L] [HasInf L] : Prop where
  continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2
#align has_continuous_inf ContinuousInf
-/

#print ContinuousSup /-
/-- Let `L` be a topological space and let `L×L` be equipped with the product topology and let
`⊓:L×L → L` be a supremum. Then `L` is said to have *(jointly) continuous supremum* if the map
`⊓:L×L → L` is continuous.
-/
class ContinuousSup (L : Type _) [TopologicalSpace L] [HasSup L] : Prop where
  continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2
#align has_continuous_sup ContinuousSup
-/

#print OrderDual.continuousSup /-
-- see Note [lower instance priority]
instance (priority := 100) OrderDual.continuousSup (L : Type _) [TopologicalSpace L] [HasInf L]
    [ContinuousInf L] : ContinuousSup Lᵒᵈ
    where continuous_sup := @ContinuousInf.continuous_inf L _ _ _
#align order_dual.has_continuous_sup OrderDual.continuousSup
-/

#print OrderDual.continuousInf /-
-- see Note [lower instance priority]
instance (priority := 100) OrderDual.continuousInf (L : Type _) [TopologicalSpace L] [HasSup L]
    [ContinuousSup L] : ContinuousInf Lᵒᵈ
    where continuous_inf := @ContinuousSup.continuous_sup L _ _ _
#align order_dual.has_continuous_inf OrderDual.continuousInf
-/

#print TopologicalLattice /-
/-- Let `L` be a lattice equipped with a topology such that `L` has continuous infimum and supremum.
Then `L` is said to be a *topological lattice*.
-/
class TopologicalLattice (L : Type _) [TopologicalSpace L] [Lattice L] extends ContinuousInf L,
  ContinuousSup L
#align topological_lattice TopologicalLattice
-/

#print OrderDual.topologicalLattice /-
-- see Note [lower instance priority]
instance (priority := 100) OrderDual.topologicalLattice (L : Type _) [TopologicalSpace L]
    [Lattice L] [TopologicalLattice L] : TopologicalLattice Lᵒᵈ where
#align order_dual.topological_lattice OrderDual.topologicalLattice
-/

#print LinearOrder.topologicalLattice /-
-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.topologicalLattice {L : Type _} [TopologicalSpace L]
    [LinearOrder L] [OrderClosedTopology L] : TopologicalLattice L
    where
  continuous_inf := continuous_min
  continuous_sup := continuous_max
#align linear_order.topological_lattice LinearOrder.topologicalLattice
-/

variable {L : Type _} [TopologicalSpace L]

variable {X : Type _} [TopologicalSpace X]

/- warning: continuous_inf -> continuous_inf is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] [_inst_3 : HasInf.{u1} L] [_inst_4 : ContinuousInf.{u1} L _inst_1 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} L L) L (Prod.topologicalSpace.{u1, u1} L L _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} L L) => HasInf.inf.{u1} L _inst_3 (Prod.fst.{u1, u1} L L p) (Prod.snd.{u1, u1} L L p))
but is expected to have type
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] [_inst_3 : HasInf.{u1} L] [_inst_4 : ContinuousInf.{u1} L _inst_1 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} L L) L (instTopologicalSpaceProd.{u1, u1} L L _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} L L) => HasInf.inf.{u1} L _inst_3 (Prod.fst.{u1, u1} L L p) (Prod.snd.{u1, u1} L L p))
Case conversion may be inaccurate. Consider using '#align continuous_inf continuous_infₓ'. -/
@[continuity]
theorem continuous_inf [HasInf L] [ContinuousInf L] : Continuous fun p : L × L => p.1 ⊓ p.2 :=
  ContinuousInf.continuous_inf
#align continuous_inf continuous_inf

/- warning: continuous.inf -> Continuous.inf is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] {X : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : HasInf.{u1} L] [_inst_4 : ContinuousInf.{u1} L _inst_1 _inst_3] {f : X -> L} {g : X -> L}, (Continuous.{u2, u1} X L _inst_2 _inst_1 f) -> (Continuous.{u2, u1} X L _inst_2 _inst_1 g) -> (Continuous.{u2, u1} X L _inst_2 _inst_1 (fun (x : X) => HasInf.inf.{u1} L _inst_3 (f x) (g x)))
but is expected to have type
  forall {L : Type.{u2}} {_inst_1 : Type.{u1}} [X : TopologicalSpace.{u2} L] [_inst_2 : TopologicalSpace.{u1} _inst_1] [_inst_3 : HasInf.{u2} L] [_inst_4 : ContinuousInf.{u2} L X _inst_3] {f : _inst_1 -> L} {g : _inst_1 -> L}, (Continuous.{u1, u2} _inst_1 L _inst_2 X f) -> (Continuous.{u1, u2} _inst_1 L _inst_2 X g) -> (Continuous.{u1, u2} _inst_1 L _inst_2 X (fun (x : _inst_1) => HasInf.inf.{u2} L _inst_3 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.inf Continuous.infₓ'. -/
@[continuity]
theorem Continuous.inf [HasInf L] [ContinuousInf L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊓ g x :=
  continuous_inf.comp (hf.prod_mk hg : _)
#align continuous.inf Continuous.inf

/- warning: continuous_sup -> continuous_sup is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] [_inst_3 : HasSup.{u1} L] [_inst_4 : ContinuousSup.{u1} L _inst_1 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} L L) L (Prod.topologicalSpace.{u1, u1} L L _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} L L) => HasSup.sup.{u1} L _inst_3 (Prod.fst.{u1, u1} L L p) (Prod.snd.{u1, u1} L L p))
but is expected to have type
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] [_inst_3 : HasSup.{u1} L] [_inst_4 : ContinuousSup.{u1} L _inst_1 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} L L) L (instTopologicalSpaceProd.{u1, u1} L L _inst_1 _inst_1) _inst_1 (fun (p : Prod.{u1, u1} L L) => HasSup.sup.{u1} L _inst_3 (Prod.fst.{u1, u1} L L p) (Prod.snd.{u1, u1} L L p))
Case conversion may be inaccurate. Consider using '#align continuous_sup continuous_supₓ'. -/
@[continuity]
theorem continuous_sup [HasSup L] [ContinuousSup L] : Continuous fun p : L × L => p.1 ⊔ p.2 :=
  ContinuousSup.continuous_sup
#align continuous_sup continuous_sup

/- warning: continuous.sup -> Continuous.sup is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} L] {X : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : HasSup.{u1} L] [_inst_4 : ContinuousSup.{u1} L _inst_1 _inst_3] {f : X -> L} {g : X -> L}, (Continuous.{u2, u1} X L _inst_2 _inst_1 f) -> (Continuous.{u2, u1} X L _inst_2 _inst_1 g) -> (Continuous.{u2, u1} X L _inst_2 _inst_1 (fun (x : X) => HasSup.sup.{u1} L _inst_3 (f x) (g x)))
but is expected to have type
  forall {L : Type.{u2}} {_inst_1 : Type.{u1}} [X : TopologicalSpace.{u2} L] [_inst_2 : TopologicalSpace.{u1} _inst_1] [_inst_3 : HasSup.{u2} L] [_inst_4 : ContinuousSup.{u2} L X _inst_3] {f : _inst_1 -> L} {g : _inst_1 -> L}, (Continuous.{u1, u2} _inst_1 L _inst_2 X f) -> (Continuous.{u1, u2} _inst_1 L _inst_2 X g) -> (Continuous.{u1, u2} _inst_1 L _inst_2 X (fun (x : _inst_1) => HasSup.sup.{u2} L _inst_3 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.sup Continuous.supₓ'. -/
@[continuity]
theorem Continuous.sup [HasSup L] [ContinuousSup L] {f g : X → L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊔ g x :=
  continuous_sup.comp (hf.prod_mk hg : _)
#align continuous.sup Continuous.sup

/- warning: filter.tendsto.sup_right_nhds' -> Filter.Tendsto.sup_right_nhds' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : HasSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_3 _inst_4] {l : Filter.{u1} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u1, u2} ι β f l (nhds.{u2} β _inst_3 x)) -> (Filter.Tendsto.{u1, u2} ι β g l (nhds.{u2} β _inst_3 y)) -> (Filter.Tendsto.{u1, u2} ι β (HasSup.sup.{max u1 u2} (ι -> β) (Pi.hasSup.{u1, u2} ι (fun (ᾰ : ι) => β) (fun (i : ι) => _inst_4)) f g) l (nhds.{u2} β _inst_3 (HasSup.sup.{u2} β _inst_4 x y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : HasSup.{u1} β] [_inst_5 : ContinuousSup.{u1} β _inst_3 _inst_4] {l : Filter.{u2} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u2, u1} ι β f l (nhds.{u1} β _inst_3 x)) -> (Filter.Tendsto.{u2, u1} ι β g l (nhds.{u1} β _inst_3 y)) -> (Filter.Tendsto.{u2, u1} ι β (HasSup.sup.{max u1 u2} (ι -> β) (Pi.instHasSupForAll.{u2, u1} ι (fun (ᾰ : ι) => β) (fun (i : ι) => _inst_4)) f g) l (nhds.{u1} β _inst_3 (HasSup.sup.{u1} β _inst_4 x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.sup_right_nhds' Filter.Tendsto.sup_right_nhds'ₓ'. -/
theorem Filter.Tendsto.sup_right_nhds' {ι β} [TopologicalSpace β] [HasSup β] [ContinuousSup β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
  (continuous_sup.Tendsto _).comp (Tendsto.prod_mk_nhds hf hg)
#align filter.tendsto.sup_right_nhds' Filter.Tendsto.sup_right_nhds'

/- warning: filter.tendsto.sup_right_nhds -> Filter.Tendsto.sup_right_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : HasSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_3 _inst_4] {l : Filter.{u1} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u1, u2} ι β f l (nhds.{u2} β _inst_3 x)) -> (Filter.Tendsto.{u1, u2} ι β g l (nhds.{u2} β _inst_3 y)) -> (Filter.Tendsto.{u1, u2} ι β (fun (i : ι) => HasSup.sup.{u2} β _inst_4 (f i) (g i)) l (nhds.{u2} β _inst_3 (HasSup.sup.{u2} β _inst_4 x y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : HasSup.{u1} β] [_inst_5 : ContinuousSup.{u1} β _inst_3 _inst_4] {l : Filter.{u2} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u2, u1} ι β f l (nhds.{u1} β _inst_3 x)) -> (Filter.Tendsto.{u2, u1} ι β g l (nhds.{u1} β _inst_3 y)) -> (Filter.Tendsto.{u2, u1} ι β (fun (i : ι) => HasSup.sup.{u1} β _inst_4 (f i) (g i)) l (nhds.{u1} β _inst_3 (HasSup.sup.{u1} β _inst_4 x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.sup_right_nhds Filter.Tendsto.sup_right_nhdsₓ'. -/
theorem Filter.Tendsto.sup_right_nhds {ι β} [TopologicalSpace β] [HasSup β] [ContinuousSup β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y)) :=
  hf.sup_right_nhds' hg
#align filter.tendsto.sup_right_nhds Filter.Tendsto.sup_right_nhds

/- warning: filter.tendsto.inf_right_nhds' -> Filter.Tendsto.inf_right_nhds' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : HasInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_3 _inst_4] {l : Filter.{u1} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u1, u2} ι β f l (nhds.{u2} β _inst_3 x)) -> (Filter.Tendsto.{u1, u2} ι β g l (nhds.{u2} β _inst_3 y)) -> (Filter.Tendsto.{u1, u2} ι β (HasInf.inf.{max u1 u2} (ι -> β) (Pi.hasInf.{u1, u2} ι (fun (ᾰ : ι) => β) (fun (i : ι) => _inst_4)) f g) l (nhds.{u2} β _inst_3 (HasInf.inf.{u2} β _inst_4 x y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : HasInf.{u1} β] [_inst_5 : ContinuousInf.{u1} β _inst_3 _inst_4] {l : Filter.{u2} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u2, u1} ι β f l (nhds.{u1} β _inst_3 x)) -> (Filter.Tendsto.{u2, u1} ι β g l (nhds.{u1} β _inst_3 y)) -> (Filter.Tendsto.{u2, u1} ι β (HasInf.inf.{max u1 u2} (ι -> β) (Pi.instHasInfForAll.{u2, u1} ι (fun (ᾰ : ι) => β) (fun (i : ι) => _inst_4)) f g) l (nhds.{u1} β _inst_3 (HasInf.inf.{u1} β _inst_4 x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.inf_right_nhds' Filter.Tendsto.inf_right_nhds'ₓ'. -/
theorem Filter.Tendsto.inf_right_nhds' {ι β} [TopologicalSpace β] [HasInf β] [ContinuousInf β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
  (continuous_inf.Tendsto _).comp (Tendsto.prod_mk_nhds hf hg)
#align filter.tendsto.inf_right_nhds' Filter.Tendsto.inf_right_nhds'

/- warning: filter.tendsto.inf_right_nhds -> Filter.Tendsto.inf_right_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : HasInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_3 _inst_4] {l : Filter.{u1} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u1, u2} ι β f l (nhds.{u2} β _inst_3 x)) -> (Filter.Tendsto.{u1, u2} ι β g l (nhds.{u2} β _inst_3 y)) -> (Filter.Tendsto.{u1, u2} ι β (fun (i : ι) => HasInf.inf.{u2} β _inst_4 (f i) (g i)) l (nhds.{u2} β _inst_3 (HasInf.inf.{u2} β _inst_4 x y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : HasInf.{u1} β] [_inst_5 : ContinuousInf.{u1} β _inst_3 _inst_4] {l : Filter.{u2} ι} {f : ι -> β} {g : ι -> β} {x : β} {y : β}, (Filter.Tendsto.{u2, u1} ι β f l (nhds.{u1} β _inst_3 x)) -> (Filter.Tendsto.{u2, u1} ι β g l (nhds.{u1} β _inst_3 y)) -> (Filter.Tendsto.{u2, u1} ι β (fun (i : ι) => HasInf.inf.{u1} β _inst_4 (f i) (g i)) l (nhds.{u1} β _inst_3 (HasInf.inf.{u1} β _inst_4 x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.inf_right_nhds Filter.Tendsto.inf_right_nhdsₓ'. -/
theorem Filter.Tendsto.inf_right_nhds {ι β} [TopologicalSpace β] [HasInf β] [ContinuousInf β]
    {l : Filter ι} {f g : ι → β} {x y : β} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y)) :=
  hf.inf_right_nhds' hg
#align filter.tendsto.inf_right_nhds Filter.Tendsto.inf_right_nhds

