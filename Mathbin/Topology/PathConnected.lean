/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.path_connected
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Order.ProjIcc
import Mathbin.Topology.CompactOpen
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.UnitInterval

/-!
# Path connectedness

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `path.map` is the image of a path under a continuous map.
* `joined (x y : X)` means there is a path between `x` and `y`.
* `joined.some_path (h : joined x y)` selects some path between two points `x` and `y`.
* `path_component (x : X)` is the set of points joined to `x`.
* `path_connected_space X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : set X`.

* `joined_in F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `joined_in.some_path (h : joined_in F x y)` selects a path from `x` to `y` inside `F`.
* `path_component_in F (x : X)` is the set of points joined to `x` in `F`.
* `is_path_connected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `loc_path_connected_space X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `joined` and `joined_in F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : set X)` or the
subtype `↥F`.

* `path_connected_space_iff_univ : path_connected_space X ↔ is_path_connected (univ : set X)`
* `is_path_connected_iff_path_connected_space : is_path_connected F ↔ path_connected_space ↥F`

For locally path connected spaces, we have
* `path_connected_space_iff_connected_space : path_connected_space X ↔ connected_space X`
* `is_connected_iff_is_path_connected (U_op : is_open U) : is_path_connected U ↔ is_connected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `set.Icc_extend` that will extend any continuous map `γ : I → X` into a continuous map
`Icc_extend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `path.extend` that turns `γ : path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/


noncomputable section

open Classical Topology Filter unitInterval

open Filter Set Function unitInterval

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type _}

/-! ### Paths -/


#print Path /-
/-- Continuous path connecting two points `x` and `y` in a topological space -/
@[nolint has_nonempty_instance]
structure Path (x y : X) extends C(I, X) where
  source' : to_fun 0 = x
  target' : to_fun 1 = y
#align path Path
-/

instance : CoeFun (Path x y) fun _ => I → X :=
  ⟨fun p => p.toFun⟩

#print Path.ext /-
@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂
  | ⟨⟨x, h11⟩, h12, h13⟩, ⟨⟨x, h21⟩, h22, h23⟩, rfl => rfl
#align path.ext Path.ext
-/

namespace Path

#print Path.coe_mk_mk /-
@[simp]
theorem coe_mk_mk (f : I → X) (h₁ h₂ h₃) : ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl
#align path.coe_mk Path.coe_mk_mk
-/

variable (γ : Path x y)

#print Path.continuous /-
@[continuity]
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun
#align path.continuous Path.continuous
-/

#print Path.source /-
@[simp]
protected theorem source : γ 0 = x :=
  γ.source'
#align path.source Path.source
-/

#print Path.target /-
@[simp]
protected theorem target : γ 1 = y :=
  γ.target'
#align path.target Path.target
-/

#print Path.simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply : I → X :=
  γ
#align path.simps.apply Path.simps.apply
-/

initialize_simps_projections Path (to_continuous_map_to_fun → simps.apply, -toContinuousMap)

/- warning: path.coe_to_continuous_map -> Path.coe_toContinuousMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} ((coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (coeFn.{succ u1, succ u1} (ContinuousMap.{0, u1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) X (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1) (fun (_x : ContinuousMap.{0, u1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) X (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (ContinuousMap.hasCoeToFun.{0, u1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) X (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1) (Path.toContinuousMap.{u1} X _inst_1 x y γ)) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x y) (fun (_x : Path.{u1} X _inst_1 x y) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x y) γ)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} (forall (ᾰ : Set.Elem.{0} Real unitInterval), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (ContinuousMap.{0, u1} (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (ContinuousMap.{0, u1} (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (ContinuousMap.instContinuousMapClassContinuousMap.{0, u1} (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1)) (Path.toContinuousMap.{u1} X _inst_1 x y γ)) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 x y)) γ)
Case conversion may be inaccurate. Consider using '#align path.coe_to_continuous_map Path.coe_toContinuousMapₓ'. -/
@[simp]
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl
#align path.coe_to_continuous_map Path.coe_toContinuousMap

#print Path.hasUncurryPath /-
/-- Any function `φ : Π (a : α), path (x a) (y a)` can be seen as a function `α × I → X`. -/
instance hasUncurryPath {X α : Type _} [TopologicalSpace X] {x y : α → X} :
    HasUncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩
#align path.has_uncurry_path Path.hasUncurryPath
-/

#print Path.refl /-
/-- The constant path from a point to itself -/
@[refl, simps]
def refl (x : X) : Path x x where
  toFun t := x
  continuous_toFun := continuous_const
  source' := rfl
  target' := rfl
#align path.refl Path.refl
-/

#print Path.refl_range /-
@[simp]
theorem refl_range {a : X} : range (Path.refl a) = {a} := by simp [Path.refl, CoeFun.coe, coeFn]
#align path.refl_range Path.refl_range
-/

#print Path.symm /-
/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps]
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by continuity
  source' := by simpa [-Path.target] using γ.target
  target' := by simpa [-Path.source] using γ.source
#align path.symm Path.symm
-/

#print Path.symm_symm /-
@[simp]
theorem symm_symm {γ : Path x y} : γ.symm.symm = γ :=
  by
  ext
  simp
#align path.symm_symm Path.symm_symm
-/

#print Path.refl_symm /-
@[simp]
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a :=
  by
  ext
  rfl
#align path.refl_symm Path.refl_symm
-/

#print Path.symm_range /-
@[simp]
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ :=
  by
  ext x
  simp only [mem_range, Path.symm, CoeFun.coe, coeFn, unitInterval.symm, SetCoe.exists, comp_app,
    Subtype.coe_mk, Subtype.val_eq_coe]
  constructor <;> rintro ⟨y, hy, hxy⟩ <;> refine' ⟨1 - y, mem_iff_one_sub_mem.mp hy, _⟩ <;>
    convert hxy
  simp
#align path.symm_range Path.symm_range
-/

/-! #### Space of paths -/


open ContinuousMap

instance : Coe (Path x y) C(I, X) :=
  ⟨fun γ => γ.1⟩

/-- The following instance defines the topology on the path space to be induced from the
compact-open topology on the space `C(I,X)` of continuous maps from `I` to `X`.
-/
instance : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced (coe : _ → C(I, X)) ContinuousMap.compactOpen

/- warning: path.continuous_eval -> Path.continuous_eval is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Continuous.{u1, u1} (Prod.{u1, 0} (Path.{u1} X _inst_1 x y) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u1, 0} (Path.{u1} X _inst_1 x y) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Path.topologicalSpace.{u1} X _inst_1 x y) (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (fun (p : Prod.{u1, 0} (Path.{u1} X _inst_1 x y) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) => coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x y) (fun (_x : Path.{u1} X _inst_1 x y) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x y) (Prod.fst.{u1, 0} (Path.{u1} X _inst_1 x y) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) p) (Prod.snd.{u1, 0} (Path.{u1} X _inst_1 x y) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) p))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Continuous.{u1, u1} (Prod.{u1, 0} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (Path.topologicalSpace.{u1} X _inst_1 x y) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (fun (p : Prod.{u1, 0} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval)) => FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 x y)) (Prod.fst.{u1, 0} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) p) (Prod.snd.{u1, 0} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) p))
Case conversion may be inaccurate. Consider using '#align path.continuous_eval Path.continuous_evalₓ'. -/
theorem continuous_eval : Continuous fun p : Path x y × I => p.1 p.2 :=
  continuous_eval'.comp <| continuous_induced_dom.Prod_map continuous_id
#align path.continuous_eval Path.continuous_eval

#print Continuous.path_eval /-
@[continuity]
theorem Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y => f y (g y) :=
  Continuous.comp continuous_eval (hf.prod_mk hg)
#align continuous.path_eval Continuous.path_eval
-/

/- warning: path.continuous_uncurry_iff -> Path.continuous_uncurry_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {g : Y -> (Path.{u1} X _inst_1 x y)}, Iff (Continuous.{u2, u1} (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_3 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (Y -> (Path.{u1} X _inst_1 x y)) (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X Y _inst_1 (fun (ᾰ : Y) => x) (fun (ᾰ : Y) => y)) g)) (Continuous.{u2, u1} Y (Path.{u1} X _inst_1 x y) _inst_3 (Path.topologicalSpace.{u1} X _inst_1 x y) g)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {g : Y -> (Path.{u1} X _inst_1 x y)}, Iff (Continuous.{u2, u1} (Prod.{u2, 0} Y (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u2, 0} Y (Set.Elem.{0} Real unitInterval) _inst_3 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u1 u2, u2, u1} (Y -> (Path.{u1} X _inst_1 x y)) (Prod.{u2, 0} Y (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u1, u2} X Y _inst_1 (fun (ᾰ : Y) => x) (fun (ᾰ : Y) => y)) g)) (Continuous.{u2, u1} Y (Path.{u1} X _inst_1 x y) _inst_3 (Path.topologicalSpace.{u1} X _inst_1 x y) g)
Case conversion may be inaccurate. Consider using '#align path.continuous_uncurry_iff Path.continuous_uncurry_iffₓ'. -/
theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y → Path x y} :
    Continuous ↿g ↔ Continuous g :=
  Iff.symm <|
    continuous_induced_rng.trans
      ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩, continuous_of_continuous_uncurry ↑g⟩
#align path.continuous_uncurry_iff Path.continuous_uncurry_iff

#print Path.extend /-
/-- A continuous map extending a path to `ℝ`, constant before `0` and after `1`. -/
def extend : ℝ → X :=
  IccExtend zero_le_one γ
#align path.extend Path.extend
-/

/- warning: continuous.path_extend -> Continuous.path_extend is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {γ : Y -> (Path.{u1} X _inst_1 x y)} {f : Y -> Real}, (Continuous.{u2, u1} (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_2 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (Y -> (Path.{u1} X _inst_1 x y)) (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X Y _inst_1 (fun (ᾰ : Y) => x) (fun (ᾰ : Y) => y)) γ)) -> (Continuous.{u2, 0} Y Real _inst_2 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Continuous.{u2, u1} Y X _inst_2 _inst_1 (fun (t : Y) => Path.extend.{u1} X _inst_1 x y (γ t) (f t)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {γ : Y -> (Path.{u2} X _inst_1 x y)} {f : Y -> Real}, (Continuous.{u1, u2} (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} Y (Set.Elem.{0} Real unitInterval) _inst_2 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (Y -> (Path.{u2} X _inst_1 x y)) (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X Y _inst_1 (fun (ᾰ : Y) => x) (fun (ᾰ : Y) => y)) γ)) -> (Continuous.{u1, 0} Y Real _inst_2 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Continuous.{u1, u2} Y X _inst_2 _inst_1 (fun (t : Y) => Path.extend.{u2} X _inst_1 x y (γ t) (f t)))
Case conversion may be inaccurate. Consider using '#align continuous.path_extend Continuous.path_extendₓ'. -/
/-- See Note [continuity lemma statement]. -/
theorem Continuous.path_extend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf
#align continuous.path_extend Continuous.path_extend

#print Path.continuous_extend /-
/-- A useful special case of `continuous.path_extend`. -/
@[continuity]
theorem continuous_extend : Continuous γ.extend :=
  γ.Continuous.Icc_extend'
#align path.continuous_extend Path.continuous_extend
-/

/- warning: filter.tendsto.path_extend -> Filter.Tendsto.path_extend is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} X] [_inst_4 : TopologicalSpace.{u2} Y] {l : Y -> X} {r : Y -> X} {y : Y} {l₁ : Filter.{0} Real} {l₂ : Filter.{u1} X} {γ : forall (y : Y), Path.{u1} X _inst_3 (l y) (r y)}, (Filter.Tendsto.{u2, u1} (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) X (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (y : Y), Path.{u1} X _inst_3 (l y) (r y)) (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) X (Path.hasUncurryPath.{u1, u2} X Y _inst_3 (fun (y : Y) => l y) (fun (y : Y) => r y)) γ) (Filter.prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (nhds.{u2} Y _inst_4 y) (Filter.map.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Set.projIcc.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (zero_le_one.{0} Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) l₁)) l₂) -> (Filter.Tendsto.{u2, u1} (Prod.{u2, 0} Y Real) X (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (Y -> Real -> X) (Prod.{u2, 0} Y Real) X (Function.hasUncurryInduction.{u2, u1, 0, u1} Y (Real -> X) Real X (Function.hasUncurryBase.{0, u1} Real X)) (fun (x : Y) => Path.extend.{u1} X _inst_3 (l x) (r x) (γ x))) (Filter.prod.{u2, 0} Y Real (nhds.{u2} Y _inst_4 y) l₁) l₂)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} X] [_inst_4 : TopologicalSpace.{u1} Y] {l : Y -> X} {r : Y -> X} {y : Y} {l₁ : Filter.{0} Real} {l₂ : Filter.{u2} X} {γ : forall (y : Y), Path.{u2} X _inst_3 (l y) (r y)}, (Filter.Tendsto.{u1, u2} (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (y : Y), Path.{u2} X _inst_3 (l y) (r y)) (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X Y _inst_3 (fun (y : Y) => l y) (fun (y : Y) => r y)) γ) (Filter.prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval) (nhds.{u1} Y _inst_4 y) (Filter.map.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Set.projIcc.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (zero_le_one.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder)))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) l₁)) l₂) -> (Filter.Tendsto.{u1, u2} (Prod.{u1, 0} Y Real) X (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (Y -> Real -> X) (Prod.{u1, 0} Y Real) X (Function.hasUncurryInduction.{u1, u2, 0, u2} Y (Real -> X) Real X (Function.hasUncurryBase.{0, u2} Real X)) (fun (x : Y) => Path.extend.{u2} X _inst_3 (l x) (r x) (γ x))) (Filter.prod.{u1, 0} Y Real (nhds.{u1} Y _inst_4 y) l₁) l₂)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.path_extend Filter.Tendsto.path_extendₓ'. -/
theorem Filter.Tendsto.path_extend {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
    {l r : Y → X} {y : Y} {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
    (hγ : Tendsto (↿γ) (𝓝 y ×ᶠ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => (γ x).extend) (𝓝 y ×ᶠ l₁) l₂ :=
  Filter.Tendsto.IccExtend' _ hγ
#align filter.tendsto.path_extend Filter.Tendsto.path_extend

/- warning: continuous_at.path_extend -> ContinuousAt.path_extend is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {g : Y -> Real} {l : Y -> X} {r : Y -> X} (γ : forall (y : Y), Path.{u1} X _inst_1 (l y) (r y)) {y : Y}, (ContinuousAt.{u2, u1} (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) X (Prod.topologicalSpace.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) _inst_2 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (y : Y), Path.{u1} X _inst_1 (l y) (r y)) (Prod.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) X (Path.hasUncurryPath.{u1, u2} X Y _inst_1 (fun (y : Y) => l y) (fun (y : Y) => r y)) γ) (Prod.mk.{u2, 0} Y (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) y (Set.projIcc.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (zero_le_one.{0} Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)) (g y)))) -> (ContinuousAt.{u2, 0} Y Real _inst_2 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g y) -> (ContinuousAt.{u2, u1} Y X _inst_2 _inst_1 (fun (i : Y) => Path.extend.{u1} X _inst_1 (l i) (r i) (γ i) (g i)) y)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {g : Y -> Real} {l : Y -> X} {r : Y -> X} (γ : forall (y : Y), Path.{u2} X _inst_1 (l y) (r y)) {y : Y}, (ContinuousAt.{u1, u2} (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} Y (Set.Elem.{0} Real unitInterval) _inst_2 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_1 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (y : Y), Path.{u2} X _inst_1 (l y) (r y)) (Prod.{u1, 0} Y (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X Y _inst_1 (fun (y : Y) => l y) (fun (y : Y) => r y)) γ) (Prod.mk.{u1, 0} Y (Set.Elem.{0} Real unitInterval) y (Set.projIcc.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (zero_le_one.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder)))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)) (g y)))) -> (ContinuousAt.{u1, 0} Y Real _inst_2 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g y) -> (ContinuousAt.{u1, u2} Y X _inst_2 _inst_1 (fun (i : Y) => Path.extend.{u2} X _inst_1 (l i) (r i) (γ i) (g i)) y)
Case conversion may be inaccurate. Consider using '#align continuous_at.path_extend ContinuousAt.path_extendₓ'. -/
theorem ContinuousAt.path_extend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y)) {y : Y}
    (hγ : ContinuousAt (↿γ) (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg
#align continuous_at.path_extend ContinuousAt.path_extend

/- warning: path.extend_extends -> Path.extend_extends is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real} (ht : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) t (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))), Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t ht))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real} (ht : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) t (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))), Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t ht))
Case conversion may be inaccurate. Consider using '#align path.extend_extends Path.extend_extendsₓ'. -/
@[simp]
theorem extend_extends {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ∈ (Icc 0 1 : Set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht
#align path.extend_extends Path.extend_extends

/- warning: path.extend_zero -> Path.extend_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} X (Path.extend.{u1} X _inst_1 x y γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) x
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} X (Path.extend.{u1} X _inst_1 x y γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) x
Case conversion may be inaccurate. Consider using '#align path.extend_zero Path.extend_zeroₓ'. -/
theorem extend_zero : γ.extend 0 = x := by simp
#align path.extend_zero Path.extend_zero

/- warning: path.extend_one -> Path.extend_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} X (Path.extend.{u1} X _inst_1 x y γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y), Eq.{succ u1} X (Path.extend.{u1} X _inst_1 x y γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y
Case conversion may be inaccurate. Consider using '#align path.extend_one Path.extend_oneₓ'. -/
theorem extend_one : γ.extend 1 = y := by simp
#align path.extend_one Path.extend_one

/- warning: path.extend_extends' -> Path.extend_extends' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))), Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))))) t)) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ t)
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))), Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) t)) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ t)
Case conversion may be inaccurate. Consider using '#align path.extend_extends' Path.extend_extends'ₓ'. -/
@[simp]
theorem extend_extends' {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : (Icc 0 1 : Set ℝ)) : γ.extend t = γ t :=
  Icc_extend_coe _ γ t
#align path.extend_extends' Path.extend_extends'

#print Path.extend_range /-
@[simp]
theorem extend_range {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ
#align path.extend_range Path.extend_range
-/

/- warning: path.extend_of_le_zero -> Path.extend_of_le_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real}, (LE.le.{0} Real Real.hasLe t (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) a)
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real}, (LE.le.{0} Real Real.instLEReal t (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) a)
Case conversion may be inaccurate. Consider using '#align path.extend_of_le_zero Path.extend_of_le_zeroₓ'. -/
theorem extend_of_le_zero {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ≤ 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source
#align path.extend_of_le_zero Path.extend_of_le_zero

/- warning: path.extend_of_one_le -> Path.extend_of_one_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) t) -> (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) b)
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) t) -> (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) b)
Case conversion may be inaccurate. Consider using '#align path.extend_of_one_le Path.extend_of_one_leₓ'. -/
theorem extend_of_one_le {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t : ℝ}
    (ht : 1 ≤ t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target
#align path.extend_of_one_le Path.extend_of_one_le

#print Path.refl_extend /-
@[simp]
theorem refl_extend {X : Type _} [TopologicalSpace X] {a : X} : (Path.refl a).extend = fun _ => a :=
  rfl
#align path.refl_extend Path.refl_extend
-/

/- warning: path.of_line -> Path.ofLine is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {f : Real -> X}, (ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) x) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y) -> (Path.{u1} X _inst_1 x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {f : Real -> X}, (ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) x) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y) -> (Path.{u1} X _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align path.of_line Path.ofLineₓ'. -/
/-- The path obtained from a map defined on `ℝ` by restriction to the unit interval. -/
def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y
    where
  toFun := f ∘ coe
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁
#align path.of_line Path.ofLine

/- warning: path.of_line_mem -> Path.ofLine_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {f : Real -> X} (hf : ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) (h₀ : Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) x) (h₁ : Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y) (t : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x y) (fun (_x : Path.{u1} X _inst_1 x y) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x y) (Path.ofLine.{u1} X _inst_1 x y f hf h₀ h₁) t) (Set.image.{0, u1} Real X f unitInterval)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {f : Real -> X} (hf : ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) (h₀ : Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) x) (h₁ : Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y) (t : Set.Elem.{0} Real unitInterval), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) t) (Set.{u1} X) (Set.instMembershipSet.{u1} X) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 x y)) (Path.ofLine.{u1} X _inst_1 x y f hf h₀ h₁) t) (Set.image.{0, u1} Real X f unitInterval)
Case conversion may be inaccurate. Consider using '#align path.of_line_mem Path.ofLine_memₓ'. -/
theorem ofLine_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    ∀ t, ofLine hf h₀ h₁ t ∈ f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩
#align path.of_line_mem Path.ofLine_mem

attribute [local simp] Iic_def

#print Path.trans /-
/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z
    where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ coe
  continuous_toFun :=
    by
    refine'
      (Continuous.if_le _ _ continuous_id continuous_const (by norm_num)).comp
        continuous_subtype_val
    -- TODO: the following are provable by `continuity` but it is too slow
    exacts[γ.continuous_extend.comp (continuous_const.mul continuous_id),
      γ'.continuous_extend.comp ((continuous_const.mul continuous_id).sub continuous_const)]
  source' := by norm_num
  target' := by norm_num
#align path.trans Path.trans
-/

/- warning: path.trans_apply -> Path.trans_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {z : X} (γ : Path.{u1} X _inst_1 x y) (γ' : Path.{u1} X _inst_1 y z) (t : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval), Eq.{succ u1} X (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x z) (fun (_x : Path.{u1} X _inst_1 x z) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x z) (Path.trans.{u1} X _inst_1 x y z γ γ') t) (dite.{succ u1} X (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.decidableLE ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (fun (h : LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) => coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x y) (fun (_x : Path.{u1} X _inst_1 x y) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x y) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real (AddZeroClass.toHasAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddMonoidWithOne.toAddMonoid.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) unitInterval) (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real (AddZeroClass.toHasAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddMonoidWithOne.toAddMonoid.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))))))))))) (unitInterval.mul_pos_mem_iff (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real (AddZeroClass.toHasAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddMonoidWithOne.toAddMonoid.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (zero_lt_two.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) Real.partialOrder (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring) (NeZero.one.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) Real.nontrivial) (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup))) (And.intro (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real (AddZeroClass.toHasAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddMonoidWithOne.toAddMonoid.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (NonAssocRing.toAddGroupWithOne.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring)))))))))) (And.left (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Subtype.val.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (Subtype.val.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Subtype.property.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t)) h)))) (fun (h : Not (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) => coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 y z) (fun (_x : Path.{u1} X _inst_1 y z) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 y z) γ' (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) unitInterval) (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (Set.Icc.{0} Real Real.preorder (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (unitInterval.two_mul_sub_one_mem_iff ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (And.intro (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (LT.lt.le.{0} Real Real.preorder (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (Iff.mp (Not (LE.le.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (LT.lt.{0} Real (Preorder.toLT.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t)) (not_le.{0} Real Real.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval))))) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) h)) (And.right (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Subtype.val.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (Subtype.val.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Subtype.property.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) t)))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {z : X} (γ : Path.{u1} X _inst_1 x y) (γ' : Path.{u1} X _inst_1 y z) (t : Set.Elem.{0} Real unitInterval), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) t) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 x z) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 x z) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 x z)) (Path.trans.{u1} X _inst_1 x y z γ γ') t) (dite.{succ u1} X (LE.le.{0} Real Real.instLEReal (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Real.decidableLE (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (fun (h : LE.le.{0} Real Real.instLEReal (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) => FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 x y)) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 (AddMonoidWithOne.toNatCast.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (Iff.mpr (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 (AddMonoidWithOne.toNatCast.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) unitInterval) (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 (AddMonoidWithOne.toNatCast.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (unitInterval.mul_pos_mem_iff (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 (AddMonoidWithOne.toNatCast.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (zero_lt_two.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal)) Real.partialOrder (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring) (NeZero.one.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) Real.nontrivial) (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup))) (And.intro (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 (AddMonoidWithOne.toNatCast.{0} Real (AddGroupWithOne.toAddMonoidWithOne.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (And.left (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Subtype.property.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) h)))) (fun (h : Not (LE.le.{0} Real Real.instLEReal (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 y z) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 y z) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 y z)) γ' (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Iff.mpr (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) unitInterval) (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (Set.Icc.{0} Real Real.instPreorderReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (unitInterval.two_mul_sub_one_mem_iff (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (And.intro (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LT.lt.le.{0} Real Real.instPreorderReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (Iff.mp (Not (LE.le.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (LT.lt.{0} Real (Preorder.toLT.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (not_le.{0} Real Real.linearOrder (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) h)) (And.right (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Subtype.property.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) t)))))))
Case conversion may be inaccurate. Consider using '#align path.trans_apply Path.trans_applyₓ'. -/
theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_extends]
#align path.trans_apply Path.trans_apply

#print Path.trans_symm /-
@[simp]
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm :=
  by
  ext t
  simp only [trans_apply, ← one_div, symm_apply, not_le, comp_app]
  split_ifs with h h₁ h₂ h₃ h₄ <;> rw [coe_symm_eq] at h
  · have ht : (t : ℝ) = 1 / 2 := by linarith [unitInterval.nonneg t, unitInterval.le_one t]
    norm_num [ht]
  · refine' congr_arg _ (Subtype.ext _)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine' congr_arg _ (Subtype.ext _)
    have h : 2 - 2 * (t : ℝ) - 1 = 1 - 2 * t := by linarith
    norm_num [mul_sub, h]
  · exfalso
    linarith [unitInterval.nonneg t, unitInterval.le_one t]
#align path.trans_symm Path.trans_symm
-/

#print Path.refl_trans_refl /-
@[simp]
theorem refl_trans_refl {X : Type _} [TopologicalSpace X] {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a :=
  by
  ext
  simp only [Path.trans, if_t_t, one_div, Path.refl_extend]
  rfl
#align path.refl_trans_refl Path.refl_trans_refl
-/

/- warning: path.trans_range -> Path.trans_range is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} {c : X} (γ₁ : Path.{u1} X _inst_3 a b) (γ₂ : Path.{u1} X _inst_3 b c), Eq.{succ u1} (Set.{u1} X) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a c) (fun (_x : Path.{u1} X _inst_3 a c) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a c) (Path.trans.{u1} X _inst_3 a b c γ₁ γ₂))) (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ₁)) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 b c) (fun (_x : Path.{u1} X _inst_3 b c) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 b c) γ₂)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} {c : X} (γ₁ : Path.{u1} X _inst_3 a b) (γ₂ : Path.{u1} X _inst_3 b c), Eq.{succ u1} (Set.{u1} X) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a c) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a c) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a c)) (Path.trans.{u1} X _inst_3 a b c γ₁ γ₂))) (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ₁)) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 b c) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 b c) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 b c)) γ₂)))
Case conversion may be inaccurate. Consider using '#align path.trans_range Path.trans_rangeₓ'. -/
theorem trans_range {X : Type _} [TopologicalSpace X] {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ :=
  by
  rw [Path.trans]
  apply eq_of_subset_of_subset
  · rintro x ⟨⟨t, ht0, ht1⟩, hxt⟩
    by_cases h : t ≤ 1 / 2
    · left
      use 2 * t, ⟨by linarith, by linarith⟩
      rw [← γ₁.extend_extends]
      unfold_coes  at hxt
      simp only [h, comp_app, if_true] at hxt
      exact hxt
    · right
      use 2 * t - 1, ⟨by linarith, by linarith⟩
      rw [← γ₂.extend_extends]
      unfold_coes  at hxt
      simp only [h, comp_app, if_false] at hxt
      exact hxt
  · rintro x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩)
    · use ⟨t / 2, ⟨by linarith, by linarith⟩⟩
      unfold_coes
      have : t / 2 ≤ 1 / 2 := by linarith
      simp only [this, comp_app, if_true]
      ring_nf
      rwa [γ₁.extend_extends]
    · by_cases h : t = 0
      · use ⟨1 / 2, ⟨by linarith, by linarith⟩⟩
        unfold_coes
        simp only [h, comp_app, if_true, le_refl, mul_one_div_cancel (two_ne_zero' ℝ)]
        rw [γ₁.extend_one]
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt
      · use ⟨(t + 1) / 2, ⟨by linarith, by linarith⟩⟩
        unfold_coes
        change t ≠ 0 at h
        have ht0 := lt_of_le_of_ne ht0 h.symm
        have : ¬(t + 1) / 2 ≤ 1 / 2 := by
          rw [not_le]
          linarith
        simp only [comp_app, if_false, this]
        ring_nf
        rwa [γ₂.extend_extends]
#align path.trans_range Path.trans_range

#print Path.map /-
/-- Image of a path from `x` to `y` by a continuous map -/
def map (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := by continuity
  source' := by simp
  target' := by simp
#align path.map Path.map
-/

/- warning: path.map_coe -> Path.map_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y) {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {f : X -> Y} (h : Continuous.{u1, u2} X Y _inst_1 _inst_3 f), Eq.{succ u2} ((fun (_x : Path.{u2} Y _inst_3 (f x) (f y)) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> Y) (Path.map.{u1, u2} X _inst_1 x y γ Y _inst_3 f h)) (coeFn.{succ u2, succ u2} (Path.{u2} Y _inst_3 (f x) (f y)) (fun (_x : Path.{u2} Y _inst_3 (f x) (f y)) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> Y) (Path.hasCoeToFun.{u2} Y _inst_3 (f x) (f y)) (Path.map.{u1, u2} X _inst_1 x y γ Y _inst_3 f h)) (Function.comp.{1, succ u1, succ u2} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) X Y f (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 x y) (fun (_x : Path.{u1} X _inst_1 x y) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 x y) γ))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {x : X} {y : X} (γ : Path.{u2} X _inst_1 x y) {Y : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} Y] {f : X -> Y} (h : Continuous.{u2, u1} X Y _inst_1 _inst_3 f), Eq.{succ u1} (forall (a : Set.Elem.{0} Real unitInterval), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Y) a) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} Y _inst_3 (f x) (f y)) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Y) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} Y _inst_3 (f x) (f y)) (Set.Elem.{0} Real unitInterval) Y (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} Y _inst_3 (f x) (f y))) (Path.map.{u2, u1} X _inst_1 x y γ Y _inst_3 f h)) (Function.comp.{1, succ u2, succ u1} (Set.Elem.{0} Real unitInterval) X Y f (FunLike.coe.{succ u2, 1, succ u2} (Path.{u2} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u2, 0, u2} (Path.{u2} X _inst_1 x y) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u2} X _inst_1 x y)) γ))
Case conversion may be inaccurate. Consider using '#align path.map_coe Path.map_coeₓ'. -/
@[simp]
theorem map_coe (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  rfl
#align path.map_coe Path.map_coe

/- warning: path.map_symm -> Path.map_symm is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y) {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {f : X -> Y} (h : Continuous.{u1, u2} X Y _inst_1 _inst_3 f), Eq.{succ u2} (Path.{u2} Y _inst_3 (f y) (f x)) (Path.symm.{u2} Y _inst_3 (f x) (f y) (Path.map.{u1, u2} X _inst_1 x y γ Y _inst_3 f h)) (Path.map.{u1, u2} X _inst_1 y x (Path.symm.{u1} X _inst_1 x y γ) Y _inst_3 (fun {y : X} => f y) h)
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {x : X} {y : X} (γ : Path.{u2} X _inst_1 x y) {Y : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} Y] {f : X -> Y} (h : Continuous.{u2, u1} X Y _inst_1 _inst_3 f), Eq.{succ u1} (Path.{u1} Y _inst_3 (f y) (f x)) (Path.symm.{u1} Y _inst_3 (f x) (f y) (Path.map.{u2, u1} X _inst_1 x y γ Y _inst_3 f h)) (Path.map.{u2, u1} X _inst_1 y x (Path.symm.{u2} X _inst_1 x y γ) Y _inst_3 f h)
Case conversion may be inaccurate. Consider using '#align path.map_symm Path.map_symmₓ'. -/
@[simp]
theorem map_symm (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl
#align path.map_symm Path.map_symm

/- warning: path.map_trans -> Path.map_trans is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {z : X} (γ : Path.{u1} X _inst_1 x y) (γ' : Path.{u1} X _inst_1 y z) {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {f : X -> Y} (h : Continuous.{u1, u2} X Y _inst_1 _inst_3 f), Eq.{succ u2} (Path.{u2} Y _inst_3 (f x) (f z)) (Path.map.{u1, u2} X _inst_1 x z (Path.trans.{u1} X _inst_1 x y z γ γ') Y _inst_3 f h) (Path.trans.{u2} Y _inst_3 (f x) (f y) (f z) (Path.map.{u1, u2} X _inst_1 x y γ Y _inst_3 f h) (Path.map.{u1, u2} X _inst_1 y z γ' Y _inst_3 (fun {y : X} => f y) h))
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {x : X} {y : X} {z : X} (γ : Path.{u2} X _inst_1 x y) (γ' : Path.{u2} X _inst_1 y z) {Y : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} Y] {f : X -> Y} (h : Continuous.{u2, u1} X Y _inst_1 _inst_3 f), Eq.{succ u1} (Path.{u1} Y _inst_3 (f x) (f z)) (Path.map.{u2, u1} X _inst_1 x z (Path.trans.{u2} X _inst_1 x y z γ γ') Y _inst_3 f h) (Path.trans.{u1} Y _inst_3 (f x) (f y) (f z) (Path.map.{u2, u1} X _inst_1 x y γ Y _inst_3 f h) (Path.map.{u2, u1} X _inst_1 y z γ' Y _inst_3 f h))
Case conversion may be inaccurate. Consider using '#align path.map_trans Path.map_transₓ'. -/
@[simp]
theorem map_trans (γ : Path x y) (γ' : Path y z) {Y : Type _} [TopologicalSpace Y] {f : X → Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) :=
  by
  ext t
  rw [trans_apply, map_coe, comp_app, trans_apply]
  split_ifs <;> rfl
#align path.map_trans Path.map_trans

#print Path.map_id /-
@[simp]
theorem map_id (γ : Path x y) : γ.map continuous_id = γ :=
  by
  ext
  rfl
#align path.map_id Path.map_id
-/

/- warning: path.map_map -> Path.map_map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} (γ : Path.{u1} X _inst_1 x y) {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {Z : Type.{u3}} [_inst_4 : TopologicalSpace.{u3} Z] {f : X -> Y} (hf : Continuous.{u1, u2} X Y _inst_1 _inst_3 f) {g : Y -> Z} (hg : Continuous.{u2, u3} Y Z _inst_3 _inst_4 g), Eq.{succ u3} (Path.{u3} Z _inst_4 (g (f x)) (g (f y))) (Path.map.{u2, u3} Y _inst_3 (f x) (f y) (Path.map.{u1, u2} X _inst_1 x y γ Y _inst_3 f hf) Z _inst_4 g hg) (Path.map.{u1, u3} X _inst_1 x y γ Z _inst_4 (fun {x : X} => g (f x)) (Continuous.comp.{u1, u2, u3} X Y Z _inst_1 _inst_3 _inst_4 g (fun (x : X) => f x) hg hf))
but is expected to have type
  forall {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] {x : X} {y : X} (γ : Path.{u3} X _inst_1 x y) {Y : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} Y] {Z : Type.{u1}} [_inst_4 : TopologicalSpace.{u1} Z] {f : X -> Y} (hf : Continuous.{u3, u2} X Y _inst_1 _inst_3 f) {g : Y -> Z} (hg : Continuous.{u2, u1} Y Z _inst_3 _inst_4 g), Eq.{succ u1} (Path.{u1} Z _inst_4 (g (f x)) (g (f y))) (Path.map.{u2, u1} Y _inst_3 (f x) (f y) (Path.map.{u3, u2} X _inst_1 x y γ Y _inst_3 f hf) Z _inst_4 g hg) (Path.map.{u3, u1} X _inst_1 x y γ Z _inst_4 (Function.comp.{succ u3, succ u2, succ u1} X Y Z g f) (Continuous.comp.{u3, u1, u2} X Y Z _inst_1 _inst_3 _inst_4 g f hg hf))
Case conversion may be inaccurate. Consider using '#align path.map_map Path.map_mapₓ'. -/
@[simp]
theorem map_map (γ : Path x y) {Y : Type _} [TopologicalSpace Y] {Z : Type _} [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f) {g : Y → Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  rfl
#align path.map_map Path.map_map

#print Path.cast /-
/-- Casting a path from `x` to `y` to a path from `x'` to `y'` when `x' = x` and `y' = y` -/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y'
    where
  toFun := γ
  continuous_toFun := γ.Continuous
  source' := by simp [hx]
  target' := by simp [hy]
#align path.cast Path.cast
-/

#print Path.symm_cast /-
@[simp]
theorem symm_cast {X : Type _} [TopologicalSpace X] {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) : (γ.cast ha hb).symm = γ.symm.cast hb ha :=
  rfl
#align path.symm_cast Path.symm_cast
-/

#print Path.trans_cast /-
@[simp]
theorem trans_cast {X : Type _} [TopologicalSpace X] {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc :=
  rfl
#align path.trans_cast Path.trans_cast
-/

#print Path.cast_coe /-
@[simp]
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl
#align path.cast_coe Path.cast_coe
-/

/- warning: path.symm_continuous_family -> Path.symm_continuous_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {ι : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} X] [_inst_4 : TopologicalSpace.{u2} ι] {a : ι -> X} {b : ι -> X} (γ : forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)), (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ)) -> (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (b t) (a t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => b t) (fun (t : ι) => a t)) (fun (t : ι) => Path.symm.{u1} X _inst_3 (a t) (b t) (γ t))))
but is expected to have type
  forall {X : Type.{u2}} {ι : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} X] [_inst_4 : TopologicalSpace.{u1} ι] {a : ι -> X} {b : ι -> X} (γ : forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)), (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ)) -> (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (b t) (a t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => b t) (fun (t : ι) => a t)) (fun (t : ι) => Path.symm.{u2} X _inst_3 (a t) (b t) (γ t))))
Case conversion may be inaccurate. Consider using '#align path.symm_continuous_family Path.symm_continuous_familyₓ'. -/
@[continuity]
theorem symm_continuous_family {X ι : Type _} [TopologicalSpace X] [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.Prod_map continuous_symm)
#align path.symm_continuous_family Path.symm_continuous_family

#print Path.continuous_symm /-
@[continuity]
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (continuous_fst.path_eval continuous_snd)
#align path.continuous_symm Path.continuous_symm
-/

/- warning: path.continuous_uncurry_extend_of_continuous_family -> Path.continuous_uncurry_extend_of_continuous_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {ι : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} X] [_inst_4 : TopologicalSpace.{u2} ι] {a : ι -> X} {b : ι -> X} (γ : forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)), (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ)) -> (Continuous.{u2, u1} (Prod.{u2, 0} ι Real) X (Prod.topologicalSpace.{u2, 0} ι Real _inst_4 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (ι -> Real -> X) (Prod.{u2, 0} ι Real) X (Function.hasUncurryInduction.{u2, u1, 0, u1} ι (Real -> X) Real X (Function.hasUncurryBase.{0, u1} Real X)) (fun (t : ι) => Path.extend.{u1} X _inst_3 (a t) (b t) (γ t))))
but is expected to have type
  forall {X : Type.{u2}} {ι : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} X] [_inst_4 : TopologicalSpace.{u1} ι] {a : ι -> X} {b : ι -> X} (γ : forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)), (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ)) -> (Continuous.{u1, u2} (Prod.{u1, 0} ι Real) X (instTopologicalSpaceProd.{u1, 0} ι Real _inst_4 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (ι -> Real -> X) (Prod.{u1, 0} ι Real) X (Function.hasUncurryInduction.{u1, u2, 0, u2} ι (Real -> X) Real X (Function.hasUncurryBase.{0, u2} Real X)) (fun (t : ι) => Path.extend.{u2} X _inst_3 (a t) (b t) (γ t))))
Case conversion may be inaccurate. Consider using '#align path.continuous_uncurry_extend_of_continuous_family Path.continuous_uncurry_extend_of_continuous_familyₓ'. -/
@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {X ι : Type _} [TopologicalSpace X]
    [TopologicalSpace ι] {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).extend :=
  h.comp (continuous_id.Prod_map continuous_projIcc)
#align path.continuous_uncurry_extend_of_continuous_family Path.continuous_uncurry_extend_of_continuous_family

/- warning: path.trans_continuous_family -> Path.trans_continuous_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {ι : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} X] [_inst_4 : TopologicalSpace.{u2} ι] {a : ι -> X} {b : ι -> X} {c : ι -> X} (γ₁ : forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)), (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (a t) (b t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ₁)) -> (forall (γ₂ : forall (t : ι), Path.{u1} X _inst_3 (b t) (c t)), (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (b t) (c t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => b t) (fun (t : ι) => c t)) γ₂)) -> (Continuous.{u2, u1} (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) _inst_4 (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u2, u1} (forall (t : ι), Path.{u1} X _inst_3 (a t) (c t)) (Prod.{u2, 0} ι (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, u2} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => c t)) (fun (t : ι) => Path.trans.{u1} X _inst_3 (a t) (b t) (c t) (γ₁ t) (γ₂ t)))))
but is expected to have type
  forall {X : Type.{u2}} {ι : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} X] [_inst_4 : TopologicalSpace.{u1} ι] {a : ι -> X} {b : ι -> X} {c : ι -> X} (γ₁ : forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)), (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (a t) (b t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => b t)) γ₁)) -> (forall (γ₂ : forall (t : ι), Path.{u2} X _inst_3 (b t) (c t)), (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (b t) (c t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => b t) (fun (t : ι) => c t)) γ₂)) -> (Continuous.{u1, u2} (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{u1, 0} ι (Set.Elem.{0} Real unitInterval) _inst_4 (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{max u2 u1, u1, u2} (forall (t : ι), Path.{u2} X _inst_3 (a t) (c t)) (Prod.{u1, 0} ι (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u2, u1} X ι _inst_3 (fun (t : ι) => a t) (fun (t : ι) => c t)) (fun (t : ι) => Path.trans.{u2} X _inst_3 (a t) (b t) (c t) (γ₁ t) (γ₂ t)))))
Case conversion may be inaccurate. Consider using '#align path.trans_continuous_family Path.trans_continuous_familyₓ'. -/
@[continuity]
theorem trans_continuous_family {X ι : Type _} [TopologicalSpace X] [TopologicalSpace ι]
    {a b c : ι → X} (γ₁ : ∀ t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : ∀ t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) :=
  by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [has_uncurry.uncurry, CoeFun.coe, coeFn, Path.trans, (· ∘ ·)]
  refine' Continuous.if_le _ _ (continuous_subtype_coe.comp continuous_snd) continuous_const _
  · change
      Continuous ((fun p : ι × ℝ => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I → ℝ))
    exact h₁'.comp (continuous_id.prod_map <| continuous_const.mul continuous_subtype_val)
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact
      h₂'.comp
        (continuous_id.prod_map <|
          (continuous_const.mul continuous_subtype_val).sub continuous_const)
  · rintro st hst
    simp [hst, mul_inv_cancel (two_ne_zero' ℝ)]
#align path.trans_continuous_family Path.trans_continuous_family

/- warning: continuous.path_trans -> Continuous.path_trans is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {z : X} {f : Y -> (Path.{u1} X _inst_1 x y)} {g : Y -> (Path.{u1} X _inst_1 y z)}, (Continuous.{u2, u1} Y (Path.{u1} X _inst_1 x y) _inst_2 (Path.topologicalSpace.{u1} X _inst_1 x y) f) -> (Continuous.{u2, u1} Y (Path.{u1} X _inst_1 y z) _inst_2 (Path.topologicalSpace.{u1} X _inst_1 y z) g) -> (Continuous.{u2, u1} Y (Path.{u1} X _inst_1 x z) _inst_2 (Path.topologicalSpace.{u1} X _inst_1 x z) (fun (t : Y) => Path.trans.{u1} X _inst_1 x y z (f t) (g t)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {z : X} {f : Y -> (Path.{u2} X _inst_1 x y)} {g : Y -> (Path.{u2} X _inst_1 y z)}, (Continuous.{u1, u2} Y (Path.{u2} X _inst_1 x y) _inst_2 (Path.topologicalSpace.{u2} X _inst_1 x y) f) -> (Continuous.{u1, u2} Y (Path.{u2} X _inst_1 y z) _inst_2 (Path.topologicalSpace.{u2} X _inst_1 y z) g) -> (Continuous.{u1, u2} Y (Path.{u2} X _inst_1 x z) _inst_2 (Path.topologicalSpace.{u2} X _inst_1 x z) (fun (t : Y) => Path.trans.{u2} X _inst_1 x y z (f t) (g t)))
Case conversion may be inaccurate. Consider using '#align continuous.path_trans Continuous.path_transₓ'. -/
@[continuity]
theorem Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) :=
  by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)
#align continuous.path_trans Continuous.path_trans

/- warning: path.continuous_trans -> Path.continuous_trans is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {z : X}, Continuous.{u1, u1} (Prod.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z)) (Path.{u1} X _inst_1 x z) (Prod.topologicalSpace.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) (Path.topologicalSpace.{u1} X _inst_1 x y) (Path.topologicalSpace.{u1} X _inst_1 y z)) (Path.topologicalSpace.{u1} X _inst_1 x z) (fun (ρ : Prod.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z)) => Path.trans.{u1} X _inst_1 x y z (Prod.fst.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) ρ) (Prod.snd.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) ρ))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {z : X}, Continuous.{u1, u1} (Prod.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z)) (Path.{u1} X _inst_1 x z) (instTopologicalSpaceProd.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) (Path.topologicalSpace.{u1} X _inst_1 x y) (Path.topologicalSpace.{u1} X _inst_1 y z)) (Path.topologicalSpace.{u1} X _inst_1 x z) (fun (ρ : Prod.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z)) => Path.trans.{u1} X _inst_1 x y z (Prod.fst.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) ρ) (Prod.snd.{u1, u1} (Path.{u1} X _inst_1 x y) (Path.{u1} X _inst_1 y z) ρ))
Case conversion may be inaccurate. Consider using '#align path.continuous_trans Path.continuous_transₓ'. -/
@[continuity]
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 :=
  continuous_fst.path_trans continuous_snd
#align path.continuous_trans Path.continuous_trans

/-! #### Product of paths -/


section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

/- warning: path.prod -> Path.prod is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {a₁ : X} {a₂ : X} {b₁ : Y} {b₂ : Y}, (Path.{u1} X _inst_1 a₁ a₂) -> (Path.{u2} Y _inst_2 b₁ b₂) -> (Path.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {a₁ : X} {a₂ : X} {b₁ : Y} {b₂ : Y}, (Path.{u1} X _inst_1 a₁ a₂) -> (Path.{u2} Y _inst_2 b₁ b₂) -> (Path.{max u2 u1} (Prod.{u1, u2} X Y) (instTopologicalSpaceProd.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂))
Case conversion may be inaccurate. Consider using '#align path.prod Path.prodₓ'. -/
/-- Given a path in `X` and a path in `Y`, we can take their pointwise product to get a path in
`X × Y`. -/
protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂)
    where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp
#align path.prod Path.prod

/- warning: path.prod_coe_fn -> Path.prod_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {a₁ : X} {a₂ : X} {b₁ : Y} {b₂ : Y} (γ₁ : Path.{u1} X _inst_1 a₁ a₂) (γ₂ : Path.{u2} Y _inst_2 b₁ b₂), Eq.{succ (max u1 u2)} ((coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> (Prod.{u1, u2} X Y)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Path.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂)) (fun (_x : Path.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂)) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> (Prod.{u1, u2} X Y)) (Path.hasCoeToFun.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂)) (Path.prod.{u1, u2} X Y _inst_1 _inst_2 a₁ a₂ b₁ b₂ γ₁ γ₂)) (fun (t : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) => Prod.mk.{u1, u2} X Y (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 a₁ a₂) (fun (_x : Path.{u1} X _inst_1 a₁ a₂) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 a₁ a₂) γ₁ t) (coeFn.{succ u2, succ u2} (Path.{u2} Y _inst_2 b₁ b₂) (fun (_x : Path.{u2} Y _inst_2 b₁ b₂) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> Y) (Path.hasCoeToFun.{u2} Y _inst_2 b₁ b₂) γ₂ t))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {a₁ : X} {a₂ : X} {b₁ : Y} {b₂ : Y} (γ₁ : Path.{u2} X _inst_1 a₁ a₂) (γ₂ : Path.{u1} Y _inst_2 b₁ b₂), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Set.Elem.{0} Real unitInterval), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Prod.{u2, u1} X Y) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), 1, max (succ u2) (succ u1)} (Path.{max u1 u2} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y a₁ b₁) (Prod.mk.{u2, u1} X Y a₂ b₂)) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Prod.{u2, u1} X Y) _x) (ContinuousMapClass.toFunLike.{max u2 u1, 0, max u2 u1} (Path.{max u1 u2} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y a₁ b₁) (Prod.mk.{u2, u1} X Y a₂ b₂)) (Set.Elem.{0} Real unitInterval) (Prod.{u2, u1} X Y) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Path.continuousMapClass.{max u2 u1} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y a₁ b₁) (Prod.mk.{u2, u1} X Y a₂ b₂))) (Path.prod.{u2, u1} X Y _inst_1 _inst_2 a₁ a₂ b₁ b₂ γ₁ γ₂)) (fun (t : Set.Elem.{0} Real unitInterval) => Prod.mk.{u2, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) t) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Y) t) (FunLike.coe.{succ u2, 1, succ u2} (Path.{u2} X _inst_1 a₁ a₂) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u2, 0, u2} (Path.{u2} X _inst_1 a₁ a₂) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u2} X _inst_1 a₁ a₂)) γ₁ t) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} Y _inst_2 b₁ b₂) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => Y) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} Y _inst_2 b₁ b₂) (Set.Elem.{0} Real unitInterval) Y (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_2 (Path.continuousMapClass.{u1} Y _inst_2 b₁ b₂)) γ₂ t))
Case conversion may be inaccurate. Consider using '#align path.prod_coe_fn Path.prod_coeₓ'. -/
@[simp]
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : coeFn (γ₁.Prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl
#align path.prod_coe_fn Path.prod_coe

/- warning: path.trans_prod_eq_prod_trans -> Path.trans_prod_eq_prod_trans is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {a₁ : X} {a₂ : X} {a₃ : X} {b₁ : Y} {b₂ : Y} {b₃ : Y} (γ₁ : Path.{u1} X _inst_1 a₁ a₂) (δ₁ : Path.{u1} X _inst_1 a₂ a₃) (γ₂ : Path.{u2} Y _inst_2 b₁ b₂) (δ₂ : Path.{u2} Y _inst_2 b₂ b₃), Eq.{succ (max u1 u2)} (Path.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₃ b₃)) (Path.trans.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y a₁ b₁) (Prod.mk.{u1, u2} X Y a₂ b₂) (Prod.mk.{u1, u2} X Y a₃ b₃) (Path.prod.{u1, u2} X Y _inst_1 _inst_2 a₁ a₂ b₁ b₂ γ₁ γ₂) (Path.prod.{u1, u2} X Y _inst_1 _inst_2 a₂ a₃ b₂ b₃ δ₁ δ₂)) (Path.prod.{u1, u2} X Y _inst_1 _inst_2 a₁ a₃ b₁ b₃ (Path.trans.{u1} X _inst_1 a₁ a₂ a₃ γ₁ δ₁) (Path.trans.{u2} Y _inst_2 b₁ b₂ b₃ γ₂ δ₂))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {a₁ : X} {a₂ : X} {a₃ : X} {b₁ : Y} {b₂ : Y} {b₃ : Y} (γ₁ : Path.{u2} X _inst_1 a₁ a₂) (δ₁ : Path.{u2} X _inst_1 a₂ a₃) (γ₂ : Path.{u1} Y _inst_2 b₁ b₂) (δ₂ : Path.{u1} Y _inst_2 b₂ b₃), Eq.{max (succ u2) (succ u1)} (Path.{max u2 u1} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y a₁ b₁) (Prod.mk.{u2, u1} X Y a₃ b₃)) (Path.trans.{max u2 u1} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y a₁ b₁) (Prod.mk.{u2, u1} X Y a₂ b₂) (Prod.mk.{u2, u1} X Y a₃ b₃) (Path.prod.{u2, u1} X Y _inst_1 _inst_2 a₁ a₂ b₁ b₂ γ₁ γ₂) (Path.prod.{u2, u1} X Y _inst_1 _inst_2 a₂ a₃ b₂ b₃ δ₁ δ₂)) (Path.prod.{u2, u1} X Y _inst_1 _inst_2 a₁ a₃ b₁ b₃ (Path.trans.{u2} X _inst_1 a₁ a₂ a₃ γ₁ δ₁) (Path.trans.{u1} Y _inst_2 b₁ b₂ b₃ γ₂ δ₂))
Case conversion may be inaccurate. Consider using '#align path.trans_prod_eq_prod_trans Path.trans_prod_eq_prod_transₓ'. -/
/-- Path composition commutes with products -/
theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.Prod γ₂).trans (δ₁.Prod δ₂) = (γ₁.trans δ₁).Prod (γ₂.trans δ₂) := by
  ext t <;> unfold Path.trans <;> simp only [Path.coe_mk_mk, Path.prod_coe, Function.comp_apply] <;>
      split_ifs <;>
    rfl
#align path.trans_prod_eq_prod_trans Path.trans_prod_eq_prod_trans

end Prod

section Pi

variable {χ : ι → Type _} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}

#print Path.pi /-
/-- Given a family of paths, one in each Xᵢ, we take their pointwise product to get a path in
Π i, Xᵢ. -/
protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs
    where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp
#align path.pi Path.pi
-/

#print Path.pi_coe /-
@[simp]
theorem pi_coe (γ : ∀ i, Path (as i) (bs i)) : coeFn (Path.pi γ) = fun t i => γ i t :=
  rfl
#align path.pi_coe_fn Path.pi_coe
-/

#print Path.trans_pi_eq_pi_trans /-
/-- Path composition commutes with products -/
theorem trans_pi_eq_pi_trans (γ₀ : ∀ i, Path (as i) (bs i)) (γ₁ : ∀ i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) :=
  by
  ext (t i)
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe_fn]
  split_ifs <;> rfl
#align path.trans_pi_eq_pi_trans Path.trans_pi_eq_pi_trans
-/

end Pi

/-! #### Pointwise multiplication/addition of two paths in a topological (additive) group -/


#print Path.mul /-
/-- Pointwise multiplication of paths in a topological group. The additive version is probably more
useful. -/
@[to_additive "Pointwise addition of paths in a topological additive group."]
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.Prod γ₂).map continuous_mul
#align path.mul Path.mul
#align path.add Path.add
-/

#print Path.mul_apply /-
@[to_additive]
protected theorem mul_apply [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁)
    (γ₂ : Path a₂ b₂) (t : unitInterval) : (γ₁.mul γ₂) t = γ₁ t * γ₂ t :=
  rfl
#align path.mul_apply Path.mul_apply
#align path.add_apply Path.add_apply
-/

/-! #### Truncating a path -/


/- warning: path.truncate -> Path.truncate is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t₀ : Real) (t₁ : Real), Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t₀ t₁)) (Path.extend.{u1} X _inst_3 a b γ t₁)
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t₀ : Real) (t₁ : Real), Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t₀ t₁)) (Path.extend.{u1} X _inst_3 a b γ t₁)
Case conversion may be inaccurate. Consider using '#align path.truncate Path.truncateₓ'. -/
/-- `γ.truncate t₀ t₁` is the path which follows the path `γ` on the
  time interval `[t₀, t₁]` and stays still otherwise. -/
def truncate {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁)
    where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun :=
    γ.continuous_extend.comp ((continuous_subtype_val.max continuous_const).min continuous_const)
  source' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl
#align path.truncate Path.truncate

/- warning: path.truncate_of_le -> Path.truncateOfLe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t₀ : Real} {t₁ : Real}, (LE.le.{0} Real Real.hasLe t₀ t₁) -> (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t₀) (Path.extend.{u1} X _inst_3 a b γ t₁))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) {t₀ : Real} {t₁ : Real}, (LE.le.{0} Real Real.instLEReal t₀ t₁) -> (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t₀) (Path.extend.{u1} X _inst_3 a b γ t₁))
Case conversion may be inaccurate. Consider using '#align path.truncate_of_le Path.truncateOfLeₓ'. -/
/-- `γ.truncate_of_le t₀ t₁ h`, where `h : t₀ ≤ t₁` is `γ.truncate t₀ t₁`
  casted as a path from `γ.extend t₀` to `γ.extend t₁`. -/
def truncateOfLe {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl
#align path.truncate_of_le Path.truncateOfLe

#print Path.truncate_range /-
theorem truncate_range {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
    range (γ.truncate t₀ t₁) ⊆ range γ :=
  by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.exists, SetCoe.forall]
  intro x hx
  simp only [CoeFun.coe, coeFn, Path.truncate, mem_range_self]
#align path.truncate_range Path.truncate_range
-/

/- warning: path.truncate_continuous_family -> Path.truncate_continuous_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Continuous.{0, u1} (Prod.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval))) X (Prod.topologicalSpace.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Prod.topologicalSpace.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))))) _inst_3 (fun (x : Prod.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval))) => coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x) (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) (fun (_x : Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x) (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x) (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))) (Path.truncate.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x) (Prod.fst.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x))) (Prod.snd.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) x)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Continuous.{0, u1} (Prod.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval))) X (instTopologicalSpaceProd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (instTopologicalSpaceProd.{0, 0} Real (Set.Elem.{0} Real unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))))) _inst_3 (fun (x : Prod.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval))) => FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x) (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x) (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x) (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))) (Path.extend.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x))))) (Path.truncate.{u1} X _inst_3 a b γ (Prod.fst.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x) (Prod.fst.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x))) (Prod.snd.{0, 0} Real (Set.Elem.{0} Real unitInterval) (Prod.snd.{0, 0} Real (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) x)))
Case conversion may be inaccurate. Consider using '#align path.truncate_continuous_family Path.truncate_continuous_familyₓ'. -/
/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we
  mean the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
theorem truncate_continuous_family {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))
#align path.truncate_continuous_family Path.truncate_continuous_family

/- warning: path.truncate_const_continuous_family -> Path.truncate_const_continuous_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : Real), Continuous.{0, u1} (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Prod.topologicalSpace.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{u1, 0, u1} (forall (t₁ : Real), Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t₁)) (Path.extend.{u1} X _inst_3 a b γ t₁)) (Prod.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) X (Path.hasUncurryPath.{u1, 0} X Real _inst_3 (fun (t₁ : Real) => Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t₁)) (fun (t₁ : Real) => Path.extend.{u1} X _inst_3 a b γ t₁)) (Path.truncate.{u1} X _inst_3 a b γ t))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : Real), Continuous.{0, u1} (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) X (instTopologicalSpaceProd.{0, 0} Real (Set.Elem.{0} Real unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))) _inst_3 (Function.HasUncurry.uncurry.{u1, 0, u1} (forall (t₁ : Real), Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t₁)) (Path.extend.{u1} X _inst_3 a b γ t₁)) (Prod.{0, 0} Real (Set.Elem.{0} Real unitInterval)) X (Path.hasUncurryPath.{u1, 0} X Real _inst_3 (fun (t₁ : Real) => Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t₁)) (fun (t₁ : Real) => Path.extend.{u1} X _inst_3 a b γ t₁)) (Path.truncate.{u1} X _inst_3 a b γ t))
Case conversion may be inaccurate. Consider using '#align path.truncate_const_continuous_family Path.truncate_const_continuous_familyₓ'. -/
/- TODO : When `continuity` gets quicker, change the proof back to :
    `begin`
      `simp only [has_coe_to_fun.coe, coe_fn, path.truncate],`
      `continuity,`
      `exact continuous_subtype_coe`
    `end` -/
@[continuity]
theorem truncate_const_continuous_family {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (t : ℝ) : Continuous ↿(γ.truncate t) :=
  by
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) :=
    continuous_const.prod_mk continuous_id
  convert γ.truncate_continuous_family.comp key
#align path.truncate_const_continuous_family Path.truncate_const_continuous_family

/- warning: path.truncate_self -> Path.truncate_self is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : Real), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Path.truncate.{u1} X _inst_3 a b γ t t) (Path.cast.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t) (Path.refl.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t)) (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t)) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t))) (Eq.ndrec.{0, 1} Real (LinearOrder.min.{0} Real Real.linearOrder t t) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) (Path.extend.{u1} X _inst_3 a b γ t))) (rfl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder t t)) (Path.extend.{u1} X _inst_3 a b γ t))) t (min_self.{0} Real Real.linearOrder t))) (rfl.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t))) (rfl.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b) (t : Real), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Path.truncate.{u1} X _inst_3 a b γ t t) (Path.cast.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t) (Path.refl.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ t)) (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t)) (id.{0} (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t) (Path.extend.{u1} X _inst_3 a b γ t))) (Eq.ndrec.{0, 1} Real (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) t t) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t)) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) (Path.extend.{u1} X _inst_3 a b γ t))) (Eq.refl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) t t)) (Path.extend.{u1} X _inst_3 a b γ t))) t (min_self.{0} Real Real.linearOrder t))) (Eq.refl.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t))) (rfl.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ t)))
Case conversion may be inaccurate. Consider using '#align path.truncate_self Path.truncate_selfₓ'. -/
@[simp]
theorem truncate_self {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t : ℝ) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl :=
  by
  ext x
  rw [cast_coe]
  simp only [truncate, CoeFun.coe, coeFn, refl, min_def, max_def]
  split_ifs with h₁ h₂ <;> congr
#align path.truncate_self Path.truncate_self

/- warning: path.truncate_zero_zero -> Path.truncate_zero_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Path.cast.{u1} X _inst_3 a a (Path.refl.{u1} X _inst_3 a) (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a)) (Eq.ndrec.{0, 1} Real (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) a)) (rfl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) a)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (min_self.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a) (Eq.{succ u1} X a a) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a) (Eq.{succ u1} X a a)) (Eq.ndrec.{0, succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (_a : X) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a) (Eq.{succ u1} X _a a)) (rfl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a)) a (Path.extend_zero.{u1} X _inst_3 a b γ))) (rfl.{succ u1} X a))) (Path.extend_zero.{u1} X _inst_3 a b γ))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Path.cast.{u1} X _inst_3 a a (Path.refl.{u1} X _inst_3 a) (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a) (id.{0} (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a)) (Eq.ndrec.{0, 1} Real (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) a) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) a)) (Eq.refl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) a)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (min_self.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a) (Eq.{succ u1} X a a) (id.{0} (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a) (Eq.{succ u1} X a a)) (Eq.ndrec.{0, succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (fun (_a : X) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a) (Eq.{succ u1} X _a a)) (Eq.refl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) a)) a (Path.extend_zero.{u1} X _inst_3 a b γ))) (Eq.refl.{succ u1} X a))) (Path.extend_zero.{u1} X _inst_3 a b γ))
Case conversion may be inaccurate. Consider using '#align path.truncate_zero_zero Path.truncate_zero_zeroₓ'. -/
@[simp]
theorem truncate_zero_zero {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert γ.truncate_self 0 <;> exact γ.extend_zero.symm
#align path.truncate_zero_zero Path.truncate_zero_zero

/- warning: path.truncate_one_one -> Path.truncate_one_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Path.cast.{u1} X _inst_3 b b (Path.refl.{u1} X _inst_3 b) (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b)) (Eq.ndrec.{0, 1} Real (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) b)) (rfl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) b)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (min_self.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) (Eq.{succ u1} X b b) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) (Eq.{succ u1} X b b)) (Eq.ndrec.{0, succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (fun (_a : X) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) (Eq.{succ u1} X _a b)) (rfl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b)) b (Path.extend_one.{u1} X _inst_3 a b γ))) (rfl.{succ u1} X b))) (Path.extend_one.{u1} X _inst_3 a b γ))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Path.cast.{u1} X _inst_3 b b (Path.refl.{u1} X _inst_3 b) (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (id.{0} (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b)) (Eq.ndrec.{0, 1} Real (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (fun (_a : Real) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) b) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ _a) b)) (Eq.refl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) b)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (min_self.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (Eq.{succ u1} X b b) (id.{0} (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (Eq.{succ u1} X b b)) (Eq.ndrec.{0, succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (fun (_a : X) => Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (Eq.{succ u1} X _a b)) (Eq.refl.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b)) b (Path.extend_one.{u1} X _inst_3 a b γ))) (Eq.refl.{succ u1} X b))) (Path.extend_one.{u1} X _inst_3 a b γ))
Case conversion may be inaccurate. Consider using '#align path.truncate_one_one Path.truncate_one_oneₓ'. -/
@[simp]
theorem truncate_one_one {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 1 1 = (Path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one := by
  convert γ.truncate_self 1 <;> exact γ.extend_one.symm
#align path.truncate_one_one Path.truncate_one_one

/- warning: path.truncate_zero_one -> Path.truncate_zero_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Path.cast.{u1} X _inst_3 a b γ (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) a) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) a) True) (Eq.trans.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) a) (Eq.{succ u1} X a a) True ((fun (a : X) (a_1 : X) (e_1 : Eq.{succ u1} X a a_1) (ᾰ : X) (ᾰ_1 : X) (e_2 : Eq.{succ u1} X ᾰ ᾰ_1) => congr.{succ u1, 1} X Prop (Eq.{succ u1} X a) (Eq.{succ u1} X a_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} X (X -> Prop) a a_1 (Eq.{succ u1} X) e_1) e_2) (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) a (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) a ((fun (γ : Path.{u1} X _inst_3 a b) (γ_1 : Path.{u1} X _inst_3 a b) (e_1 : Eq.{succ u1} (Path.{u1} X _inst_3 a b) γ γ_1) (ᾰ : Real) (ᾰ_1 : Real) (e_2 : Eq.{1} Real ᾰ ᾰ_1) => congr.{1, succ u1} Real X (Path.extend.{u1} X _inst_3 a b γ) (Path.extend.{u1} X _inst_3 a b γ_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (Real -> X) γ γ_1 (Path.extend.{u1} X _inst_3 a b) e_1) e_2) γ γ (rfl.{succ u1} (Path.{u1} X _inst_3 a b) γ) (LinearOrder.min.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (min_eq_left.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Iff.mpr (LE.le.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) True ((fun {α : Type} [_inst_1 : Zero.{0} α] [_inst_2 : One.{0} α] [_inst_3 : LE.{0} α] [_inst_4 : ZeroLEOneClass.{0} α _inst_1 _inst_2 _inst_3] => iff_true_intro (LE.le.{0} α _inst_3 (OfNat.ofNat.{0} α 0 (OfNat.mk.{0} α 0 (Zero.zero.{0} α _inst_1))) (OfNat.ofNat.{0} α 1 (OfNat.mk.{0} α 1 (One.one.{0} α _inst_2)))) (zero_le_one.{0} α _inst_1 _inst_2 _inst_3 _inst_4)) Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)) True.intro))) (Path.extend_zero.{u1} X _inst_3 a b γ)) a a (rfl.{succ u1} X a)) (propext (Eq.{succ u1} X a a) True (eq_self_iff_true.{succ u1} X a)))) trivial) (Eq.mpr.{0} (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) True) (Eq.trans.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b) (Eq.{succ u1} X b b) True ((fun (a : X) (a_1 : X) (e_1 : Eq.{succ u1} X a a_1) (ᾰ : X) (ᾰ_1 : X) (e_2 : Eq.{succ u1} X ᾰ ᾰ_1) => congr.{succ u1, 1} X Prop (Eq.{succ u1} X a) (Eq.{succ u1} X a_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} X (X -> Prop) a a_1 (Eq.{succ u1} X) e_1) e_2) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) b (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ (OfNat.ofNat.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (OfNat.mk.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (One.one.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) (Set.Icc.one.{0} Real Real.orderedSemiring))))) b (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) True (Iff.trans (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) True (Set.right_mem_Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun {α : Type} [_inst_1 : Zero.{0} α] [_inst_2 : One.{0} α] [_inst_3 : LE.{0} α] [_inst_4 : ZeroLEOneClass.{0} α _inst_1 _inst_2 _inst_3] => iff_true_intro (LE.le.{0} α _inst_3 (OfNat.ofNat.{0} α 0 (OfNat.mk.{0} α 0 (Zero.zero.{0} α _inst_1))) (OfNat.ofNat.{0} α 1 (OfNat.mk.{0} α 1 (One.one.{0} α _inst_2)))) (zero_le_one.{0} α _inst_1 _inst_2 _inst_3 _inst_4)) Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real Real.preorder) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) True.intro))) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ (OfNat.ofNat.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (OfNat.mk.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (One.one.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) (Set.Icc.one.{0} Real Real.orderedSemiring))))) (Path.extend_extends.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) True (Iff.trans (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) True (Set.right_mem_Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun {α : Type} [_inst_1 : Zero.{0} α] [_inst_2 : One.{0} α] [_inst_3 : LE.{0} α] [_inst_4 : ZeroLEOneClass.{0} α _inst_1 _inst_2 _inst_3] => iff_true_intro (LE.le.{0} α _inst_3 (OfNat.ofNat.{0} α 0 (OfNat.mk.{0} α 0 (Zero.zero.{0} α _inst_1))) (OfNat.ofNat.{0} α 1 (OfNat.mk.{0} α 1 (One.one.{0} α _inst_2)))) (zero_le_one.{0} α _inst_1 _inst_2 _inst_3 _inst_4)) Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real Real.preorder) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) True.intro)) ((fun [_inst_1 : CoeFun.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X)] (x : Path.{u1} X _inst_3 a b) (x_1 : Path.{u1} X _inst_3 a b) (e_2 : Eq.{succ u1} (Path.{u1} X _inst_3 a b) x x_1) (ᾰ : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (ᾰ_1 : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (e_3 : Eq.{1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) ᾰ ᾰ_1) => congr.{1, succ u1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) X (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) _inst_1 x) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) _inst_1 x_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) ((fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) x) x x_1 (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 a b) (fun (_x : Path.{u1} X _inst_3 a b) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) _inst_1) e_2) e_3) (Path.hasCoeToFun.{u1} X _inst_3 a b) γ γ (rfl.{succ u1} (Path.{u1} X _inst_3 a b) γ) (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x unitInterval) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) True (Iff.trans (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) True (Set.right_mem_Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun {α : Type} [_inst_1 : Zero.{0} α] [_inst_2 : One.{0} α] [_inst_3 : LE.{0} α] [_inst_4 : ZeroLEOneClass.{0} α _inst_1 _inst_2 _inst_3] => iff_true_intro (LE.le.{0} α _inst_3 (OfNat.ofNat.{0} α 0 (OfNat.mk.{0} α 0 (Zero.zero.{0} α _inst_1))) (OfNat.ofNat.{0} α 1 (OfNat.mk.{0} α 1 (One.one.{0} α _inst_2)))) (zero_le_one.{0} α _inst_1 _inst_2 _inst_3 _inst_4)) Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real Real.preorder) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) True.intro)) (OfNat.ofNat.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (OfNat.mk.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) 1 (One.one.{0} (Subtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real (OrderedSemiring.toOrderedAddCommMonoid.{0} Real Real.orderedSemiring))) (Zero.zero.{0} Real (MulZeroClass.toHasZero.{0} Real (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))))) (One.one.{0} Real (AddMonoidWithOne.toOne.{0} Real (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Real (NonAssocSemiring.toAddCommMonoidWithOne.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))))))) (Set.Icc.one.{0} Real Real.orderedSemiring)))) (Set.Icc.mk_one.{0} Real Real.orderedSemiring (Iff.mpr (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) True (Iff.trans (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.preorder) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) True (Set.right_mem_Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) ((fun {α : Type} [_inst_1 : Zero.{0} α] [_inst_2 : One.{0} α] [_inst_3 : LE.{0} α] [_inst_4 : ZeroLEOneClass.{0} α _inst_1 _inst_2 _inst_3] => iff_true_intro (LE.le.{0} α _inst_3 (OfNat.ofNat.{0} α 0 (OfNat.mk.{0} α 0 (Zero.zero.{0} α _inst_1))) (OfNat.ofNat.{0} α 1 (OfNat.mk.{0} α 1 (One.one.{0} α _inst_2)))) (zero_le_one.{0} α _inst_1 _inst_2 _inst_3 _inst_4)) Real Real.hasZero Real.hasOne (Preorder.toLE.{0} Real Real.preorder) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) True.intro)))) (Path.target.{u1} X _inst_3 a b γ)) b b (rfl.{succ u1} X b)) (propext (Eq.{succ u1} X b b) True (eq_self_iff_true.{succ u1} X b)))) trivial))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {a : X} {b : X} (γ : Path.{u1} X _inst_3 a b), Eq.{succ u1} (Path.{u1} X _inst_3 (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.truncate.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Path.cast.{u1} X _inst_3 a b γ (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (of_eq_true (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) a) (Eq.trans.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) a) (Eq.{succ u1} X a a) True (congrFun.{succ u1, 1} X (fun (a._@.Init.Prelude._hyg.170 : X) => Prop) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (Eq.{succ u1} X a) (congrArg.{succ u1, succ u1} X (X -> Prop) (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) a (Eq.{succ u1} X) (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (a : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) a) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (of_eq_true (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) (Mathlib.Data.Set.Intervals.Basic._auxLemma.4.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (congr.{1, 1} Prop Prop (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And True) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (congrArg.{1, 1} Prop (Prop -> Prop) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) True And (Mathlib.Init.Algebra.Order._auxLemma.1.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real Real.instPreorderReal) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)))) (and_self True))))) a (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (a : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) a) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (of_eq_true (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) (Mathlib.Data.Set.Intervals.Basic._auxLemma.4.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (congr.{1, 1} Prop Prop (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And True) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (congrArg.{1, 1} Prop (Prop -> Prop) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) True And (Mathlib.Init.Algebra.Order._auxLemma.1.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real Real.instPreorderReal) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)))) (and_self True))))) (congrArg.{1, succ u1} Real X (Min.min.{0} Real (LinearOrder.toMin.{0} Real Real.linearOrder) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Path.extend.{u1} X _inst_3 a b γ) (min_eq_left.{0} Real Real.linearOrder (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (of_eq_true (GE.ge.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.trans.{1} Prop (GE.ge.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (Mathlib.Order.Basic._auxLemma.3.{0} Real (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (LinearOrder.toPartialOrder.{0} Real Real.linearOrder))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)))))) (Path.extend_extends.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (of_eq_true (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) (Mathlib.Data.Set.Intervals.Basic._auxLemma.4.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (congr.{1, 1} Prop Prop (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (And True) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (congrArg.{1, 1} Prop (Prop -> Prop) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) True And (Mathlib.Init.Algebra.Order._auxLemma.1.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real Real.instPreorderReal) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring)))) (and_self True))))) (Path.source.{u1} X _inst_3 a b γ))) a) (eq_self.{succ u1} X a))) (of_eq_true (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (Eq.trans.{1} Prop (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b) (Eq.{succ u1} X b b) True (congrFun.{succ u1, 1} X (fun (a._@.Init.Prelude._hyg.170 : X) => Prop) (Eq.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.{succ u1} X b) (congrArg.{succ u1, succ u1} X (X -> Prop) (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) b (Eq.{succ u1} X) (Eq.trans.{succ u1} X (Path.extend.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) (fun (a : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) a) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 a b) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 a b)) γ (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (of_eq_true (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) (Mathlib.Data.Set.Intervals.Basic._auxLemma.4.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (congr.{1, 1} Prop Prop (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (congrArg.{1, 1} Prop (Prop -> Prop) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True And (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real Real.instPreorderReal) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) (Mathlib.Init.Algebra.Order._auxLemma.1.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (and_self True))))) b (Path.extend_extends.{u1} X _inst_3 a b γ (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (of_eq_true (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True True) (Mathlib.Data.Set.Intervals.Basic._auxLemma.4.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (congr.{1, 1} Prop Prop (And (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And True) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True (congrArg.{1, 1} Prop (Prop -> Prop) (LE.le.{0} Real (Preorder.toLE.{0} Real Real.instPreorderReal) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) True And (Mathlib.Algebra.Order.ZeroLEOne._auxLemma.1.{0} Real Real.instZeroReal Real.instOneReal (Preorder.toLE.{0} Real Real.instPreorderReal) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) (Mathlib.Init.Algebra.Order._auxLemma.1.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (and_self True)))) (Path.target.{u1} X _inst_3 a b γ))) b) (eq_self.{succ u1} X b))))
Case conversion may be inaccurate. Consider using '#align path.truncate_zero_one Path.truncate_zero_oneₓ'. -/
@[simp]
theorem truncate_zero_one {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp [zero_le_one, extend_zero]) (by simp) :=
  by
  ext x
  rw [cast_coe]
  have : ↑x ∈ (Icc 0 1 : Set ℝ) := x.2
  rw [truncate, coe_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']
#align path.truncate_zero_one Path.truncate_zero_one

/-! #### Reparametrising a path -/


#print Path.reparam /-
/-- Given a path `γ` and a function `f : I → I` where `f 0 = 0` and `f 1 = 1`, `γ.reparam f` is the
path defined by `γ ∘ f`.
-/
def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by continuity
  source' := by simp [hf₀]
  target' := by simp [hf₁]
#align path.reparam Path.reparam
-/

#print Path.coe_reparam /-
@[simp]
theorem coe_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl
#align path.coe_to_fun Path.coe_reparam
-/

#print Path.reparam_id /-
@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ :=
  by
  ext
  rfl
#align path.reparam_id Path.reparam_id
-/

#print Path.range_reparam /-
theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range ⇑(γ.reparam f hfcont hf₀ hf₁) = range γ :=
  by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_iff_surjective]
    intro t
    have h₁ : Continuous (Icc_extend (zero_le_one' ℝ) f) := by continuity
    have := intermediate_value_Icc (zero_le_one' ℝ) h₁.continuous_on
    · rw [Icc_extend_left, Icc_extend_right] at this
      change Icc (f 0) (f 1) ⊆ _ at this
      rw [hf₀, hf₁] at this
      rcases this t.2 with ⟨w, hw₁, hw₂⟩
      rw [Icc_extend_of_mem _ _ hw₁] at hw₂
      use ⟨w, hw₁⟩, hw₂
  rw [range_comp, this, image_univ]
#align path.range_reparam Path.range_reparam
-/

#print Path.refl_reparam /-
theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x :=
  by
  ext
  simp
#align path.refl_reparam Path.refl_reparam
-/

end Path

/-! ### Being joined by a path -/


#print Joined /-
/-- The relation "being joined by a path". This is an equivalence relation. -/
def Joined (x y : X) : Prop :=
  Nonempty (Path x y)
#align joined Joined
-/

#print Joined.refl /-
@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩
#align joined.refl Joined.refl
-/

#print Joined.somePath /-
/-- When two points are joined, choose some path from `x` to `y`. -/
def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h
#align joined.some_path Joined.somePath
-/

#print Joined.symm /-
@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩
#align joined.symm Joined.symm
-/

#print Joined.trans /-
@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩
#align joined.trans Joined.trans
-/

variable (X)

#print pathSetoid /-
/-- The setoid corresponding the equivalence relation of being joined by a continuous path. -/
def pathSetoid : Setoid X where
  R := Joined
  iseqv := Equivalence.mk _ Joined.refl (fun x y => Joined.symm) fun x y z => Joined.trans
#align path_setoid pathSetoid
-/

#print ZerothHomotopy /-
/-- The quotient type of points of a topological space modulo being joined by a continuous path. -/
def ZerothHomotopy :=
  Quotient (pathSetoid X)
#align zeroth_homotopy ZerothHomotopy
-/

instance : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩

variable {X}

/-! ### Being joined by a path inside a set -/


#print JoinedIn /-
/-- The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not
reflexive for points that do not belong to `F`. -/
def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F
#align joined_in JoinedIn
-/

variable {F : Set X}

#print JoinedIn.mem /-
theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F :=
  by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this
#align joined_in.mem JoinedIn.mem
-/

#print JoinedIn.source_mem /-
theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.Mem.1
#align joined_in.source_mem JoinedIn.source_mem
-/

#print JoinedIn.target_mem /-
theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.Mem.2
#align joined_in.target_mem JoinedIn.target_mem
-/

#print JoinedIn.somePath /-
/-- When `x` and `y` are joined in `F`, choose a path from `x` to `y` inside `F` -/
def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h
#align joined_in.some_path JoinedIn.somePath
-/

#print JoinedIn.somePath_mem /-
theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t
#align joined_in.some_path_mem JoinedIn.somePath_mem
-/

#print JoinedIn.joined_subtype /-
/-- If `x` and `y` are joined in the set `F`, then they are joined in the subtype `F`. -/
theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by continuity
      source' := by simp
      target' := by simp }⟩
#align joined_in.joined_subtype JoinedIn.joined_subtype
-/

/- warning: joined_in.of_line -> JoinedIn.ofLine is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {F : Set.{u1} X} {f : Real -> X}, (ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) x) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (Set.image.{0, u1} Real X f unitInterval) F) -> (JoinedIn.{u1} X _inst_1 F x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {F : Set.{u1} X} {f : Real -> X}, (ContinuousOn.{0, u1} Real X (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_1 f unitInterval) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) x) -> (Eq.{succ u1} X (f (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (Set.image.{0, u1} Real X f unitInterval) F) -> (JoinedIn.{u1} X _inst_1 F x y)
Case conversion may be inaccurate. Consider using '#align joined_in.of_line JoinedIn.ofLineₓ'. -/
theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩
#align joined_in.of_line JoinedIn.ofLine

#print JoinedIn.joined /-
theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩
#align joined_in.joined JoinedIn.joined
-/

#print joinedIn_iff_joined /-
theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩
#align joined_in_iff_joined joinedIn_iff_joined
-/

#print joinedIn_univ /-
@[simp]
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]
#align joined_in_univ joinedIn_univ
-/

#print JoinedIn.mono /-
theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩
#align joined_in.mono JoinedIn.mono
-/

#print JoinedIn.refl /-
theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun t => h⟩
#align joined_in.refl JoinedIn.refl
-/

#print JoinedIn.symm /-
@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x :=
  by
  cases' h.mem with hx hy
  simp_all [joinedIn_iff_joined]
  exact h.symm
#align joined_in.symm JoinedIn.symm
-/

#print JoinedIn.trans /-
theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z :=
  by
  cases' hxy.mem with hx hy
  cases' hyz.mem with hx hy
  simp_all [joinedIn_iff_joined]
  exact hxy.trans hyz
#align joined_in.trans JoinedIn.trans
-/

/-! ### Path component -/


#print pathComponent /-
/-- The path component of `x` is the set of points that can be joined to `x`. -/
def pathComponent (x : X) :=
  { y | Joined x y }
#align path_component pathComponent
-/

#print mem_pathComponent_self /-
@[simp]
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x
#align mem_path_component_self mem_pathComponent_self
-/

#print pathComponent.nonempty /-
@[simp]
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩
#align path_component.nonempty pathComponent.nonempty
-/

#print mem_pathComponent_of_mem /-
theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h
#align mem_path_component_of_mem mem_pathComponent_of_mem
-/

#print pathComponent_symm /-
theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩
#align path_component_symm pathComponent_symm
-/

#print pathComponent_congr /-
theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y :=
  by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h'⊢
    exact h'.trans h
#align path_component_congr pathComponent_congr
-/

#print pathComponent_subset_component /-
theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.Continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩
#align path_component_subset_component pathComponent_subset_component
-/

#print pathComponentIn /-
/-- The path component of `x` in `F` is the set of points that can be joined to `x` in `F`. -/
def pathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }
#align path_component_in pathComponentIn
-/

#print pathComponentIn_univ /-
@[simp]
theorem pathComponentIn_univ (x : X) : pathComponentIn x univ = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]
#align path_component_in_univ pathComponentIn_univ
-/

#print Joined.mem_pathComponent /-
theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz
#align joined.mem_path_component Joined.mem_pathComponent
-/

/-! ### Path connected sets -/


#print IsPathConnected /-
/-- A set `F` is path connected if it contains a point that can be joined to all other in `F`. -/
def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
#align is_path_connected IsPathConnected
-/

/- warning: is_path_connected_iff_eq -> isPathConnected_iff_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {F : Set.{u1} X}, Iff (IsPathConnected.{u1} X _inst_1 F) (Exists.{succ u1} X (fun (x : X) => Exists.{0} (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x F) (fun (H : Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x F) => Eq.{succ u1} (Set.{u1} X) (pathComponentIn.{u1} X _inst_1 x F) F)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {F : Set.{u1} X}, Iff (IsPathConnected.{u1} X _inst_1 F) (Exists.{succ u1} X (fun (x : X) => And (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x F) (Eq.{succ u1} (Set.{u1} X) (pathComponentIn.{u1} X _inst_1 x F) F)))
Case conversion may be inaccurate. Consider using '#align is_path_connected_iff_eq isPathConnected_iff_eqₓ'. -/
theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn x F = F :=
  by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.Mem.2, h⟩
  · intro y y_in
    rwa [← h] at y_in
#align is_path_connected_iff_eq isPathConnected_iff_eq

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » F) -/
#print IsPathConnected.joinedIn /-
theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ (x) (_ : x ∈ F) (y) (_ : y ∈ F), JoinedIn F x y := fun x x_in x y_in =>
  let ⟨b, b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)
#align is_path_connected.joined_in IsPathConnected.joinedIn
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » F) -/
#print isPathConnected_iff /-
theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ (x) (_ : x ∈ F) (y) (_ : y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, hb⟩ := h
      ⟨b, b_in⟩,
      h.JoinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, fun x x_in => h b b_in x x_in⟩⟩
#align is_path_connected_iff isPathConnected_iff
-/

#print IsPathConnected.image /-
theorem IsPathConnected.image {Y : Type _} [TopologicalSpace Y] (hF : IsPathConnected F) {f : X → Y}
    (hf : Continuous f) : IsPathConnected (f '' F) :=
  by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  exact ⟨(hx y_in).somePath.map hf, fun t => ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
#align is_path_connected.image IsPathConnected.image
-/

#print IsPathConnected.mem_pathComponent /-
theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.JoinedIn x x_in y y_in).Joined
#align is_path_connected.mem_path_component IsPathConnected.mem_pathComponent
-/

#print IsPathConnected.subset_pathComponent /-
theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun y y_in => h.mem_pathComponent x_in y_in
#align is_path_connected.subset_path_component IsPathConnected.subset_pathComponent
-/

/- warning: is_path_connected.union -> IsPathConnected.union is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {U : Set.{u1} X} {V : Set.{u1} X}, (IsPathConnected.{u1} X _inst_1 U) -> (IsPathConnected.{u1} X _inst_1 V) -> (Set.Nonempty.{u1} X (Inter.inter.{u1} (Set.{u1} X) (Set.hasInter.{u1} X) U V)) -> (IsPathConnected.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.hasUnion.{u1} X) U V))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {U : Set.{u1} X} {V : Set.{u1} X}, (IsPathConnected.{u1} X _inst_1 U) -> (IsPathConnected.{u1} X _inst_1 V) -> (Set.Nonempty.{u1} X (Inter.inter.{u1} (Set.{u1} X) (Set.instInterSet.{u1} X) U V)) -> (IsPathConnected.{u1} X _inst_1 (Union.union.{u1} (Set.{u1} X) (Set.instUnionSet.{u1} X) U V))
Case conversion may be inaccurate. Consider using '#align is_path_connected.union IsPathConnected.unionₓ'. -/
theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) :=
  by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joined_in x xU y yU).mono (subset_union_left U V)
  · exact (hV.joined_in x xV y yV).mono (subset_union_right U V)
#align is_path_connected.union IsPathConnected.union

#print IsPathConnected.preimage_coe /-
/-- If a set `W` is path-connected, then it is also path-connected when seen as a set in a smaller
ambient type `U` (when `U` contains `W`). -/
theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected ((coe : U → X) ⁻¹' W) :=
  by
  rcases hW with ⟨x, x_in, hx⟩
  use ⟨x, hWU x_in⟩, by simp [x_in]
  rintro ⟨y, hyU⟩ hyW
  exact ⟨(hx hyW).joined_subtype.somePath.map (continuous_inclusion hWU), by simp⟩
#align is_path_connected.preimage_coe IsPathConnected.preimage_coe
-/

/- warning: is_path_connected.exists_path_through_family -> IsPathConnected.exists_path_through_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {n : Nat} {s : Set.{u1} X}, (IsPathConnected.{u1} X _inst_3 s) -> (forall (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> X), (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (p i) s) -> (Exists.{succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (γ : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => And (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ)) s) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (p i) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {n : Nat} {s : Set.{u1} X}, (IsPathConnected.{u1} X _inst_3 s) -> (forall (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> X), (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) (p i) s) -> (Exists.{succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (fun (γ : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) => And (HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ)) s) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) (p i) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ))))))
Case conversion may be inaccurate. Consider using '#align is_path_connected.exists_path_through_family IsPathConnected.exists_path_through_familyₓ'. -/
theorem IsPathConnected.exists_path_through_family {X : Type _} [TopologicalSpace X] {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p n), range γ ⊆ s ∧ ∀ i, p i ∈ range γ :=
  by
  let p' : ℕ → X := fun k => if h : k < n + 1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (p' 0) (p' n), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s :=
    by
    have hp' : ∀ i ≤ n, p' i ∈ s := by
      intro i hi
      simp [p', Nat.lt_succ_of_le hi, hp]
    clear_value p'
    clear hp p
    induction' n with n hn
    · use Path.refl (p' 0)
      · constructor
        · rintro i hi
          rw [le_zero_iff.mp hi]
          exact ⟨0, rfl⟩
        · rw [range_subset_iff]
          rintro x
          exact hp' 0 le_rfl
    · rcases hn fun i hi => hp' i <| Nat.le_succ_of_le hi with ⟨γ₀, hγ₀⟩
      rcases h.joined_in (p' n) (hp' n n.le_succ) (p' <| n + 1) (hp' (n + 1) <| le_rfl) with
        ⟨γ₁, hγ₁⟩
      let γ : Path (p' 0) (p' <| n + 1) := γ₀.trans γ₁
      use γ
      have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁
      constructor
      · rintro i hi
        by_cases hi' : i ≤ n
        · rw [range_eq]
          left
          exact hγ₀.1 i hi'
        · rw [not_le, ← Nat.succ_le_iff] at hi'
          have : i = n.succ := by linarith
          rw [this]
          use 1
          exact γ.target
      · rw [range_eq]
        apply union_subset hγ₀.2
        rw [range_subset_iff]
        exact hγ₁
  have hpp' : ∀ k < n + 1, p k = p' k := by
    intro k hk
    simp only [p', hk, dif_pos]
    congr
    ext
    rw [Fin.val_cast_of_lt hk]
    norm_cast
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)
  simp only [γ.cast_coe]
  refine' And.intro hγ.2 _
  rintro ⟨i, hi⟩
  suffices p ⟨i, hi⟩ = p' i by convert hγ.1 i (Nat.le_of_lt_succ hi)
  rw [← hpp' i hi]
  suffices i = i % n.succ by
    congr
    assumption
  rw [Nat.mod_eq_of_lt hi]
#align is_path_connected.exists_path_through_family IsPathConnected.exists_path_through_family

/- warning: is_path_connected.exists_path_through_family' -> IsPathConnected.exists_path_through_family' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {n : Nat} {s : Set.{u1} X}, (IsPathConnected.{u1} X _inst_3 s) -> (forall (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> X), (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (p i) s) -> (Exists.{succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (γ : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => Exists.{1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) (fun (t : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) => And (forall (t : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ t) s) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{succ u1} X (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ (t i)) (p i))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} X] {n : Nat} {s : Set.{u1} X}, (IsPathConnected.{u1} X _inst_3 s) -> (forall (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> X), (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) (p i) s) -> (Exists.{succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (fun (γ : Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) => Exists.{1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Set.Elem.{0} Real unitInterval)) (fun (t : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Set.Elem.{0} Real unitInterval)) => And (forall (t : Set.Elem.{0} Real unitInterval), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) t) (Set.{u1} X) (Set.instMembershipSet.{u1} X) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ t) s) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) (t i)) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_3 (Path.continuousMapClass.{u1} X _inst_3 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ (t i)) (p i))))))
Case conversion may be inaccurate. Consider using '#align is_path_connected.exists_path_through_family' IsPathConnected.exists_path_through_family'ₓ'. -/
theorem IsPathConnected.exists_path_through_family' {X : Type _} [TopologicalSpace X] {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p n))(t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i :=
  by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_set_of_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩
#align is_path_connected.exists_path_through_family' IsPathConnected.exists_path_through_family'

/-! ### Path connected spaces -/


#print PathConnectedSpace /-
/-- A topological space is path-connected if it is non-empty and every two points can be
joined by a continuous path. -/
class PathConnectedSpace (X : Type _) [TopologicalSpace X] : Prop where
  Nonempty : Nonempty X
  Joined : ∀ x y : X, Joined x y
#align path_connected_space PathConnectedSpace
-/

#print pathConnectedSpace_iff_zerothHomotopy /-
theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) :=
  by
  letI := pathSetoid X
  constructor
  · intro h
    refine' ⟨(nonempty_quotient_iff _).mpr h.1, ⟨_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
    skip
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩
#align path_connected_space_iff_zeroth_homotopy pathConnectedSpace_iff_zerothHomotopy
-/

namespace PathConnectedSpace

variable [PathConnectedSpace X]

#print PathConnectedSpace.somePath /-
/-- Use path-connectedness to build a path between two points. -/
def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)
#align path_connected_space.some_path PathConnectedSpace.somePath
-/

end PathConnectedSpace

#print isPathConnected_iff_pathConnectedSpace /-
theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F :=
  by
  rw [isPathConnected_iff]
  constructor
  · rintro ⟨⟨x, x_in⟩, h⟩
    refine' ⟨⟨⟨x, x_in⟩⟩, _⟩
    rintro ⟨y, y_in⟩ ⟨z, z_in⟩
    have H := h y y_in z z_in
    rwa [joinedIn_iff_joined y_in z_in] at H
  · rintro ⟨⟨x, x_in⟩, H⟩
    refine' ⟨⟨x, x_in⟩, fun y y_in z z_in => _⟩
    rw [joinedIn_iff_joined y_in z_in]
    apply H
#align is_path_connected_iff_path_connected_space isPathConnected_iff_pathConnectedSpace
-/

#print pathConnectedSpace_iff_univ /-
theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) :=
  by
  constructor
  · intro h
    haveI := @PathConnectedSpace.nonempty X _ _
    inhabit X
    refine' ⟨default, mem_univ _, _⟩
    simpa using PathConnectedSpace.joined default
  · intro h
    have h' := h.joined_in
    cases' h with x h
    exact ⟨⟨x⟩, by simpa using h'⟩
#align path_connected_space_iff_univ pathConnectedSpace_iff_univ
-/

#print pathConnectedSpace_iff_eq /-
theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]
#align path_connected_space_iff_eq pathConnectedSpace_iff_eq
-/

#print PathConnectedSpace.connectedSpace /-
-- see Note [lower instance priority]
instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases is_path_connected_iff_eq.mp (path_connected_space_iff_univ.mp ‹_›) with ⟨x, x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x
#align path_connected_space.connected_space PathConnectedSpace.connectedSpace
-/

#print IsPathConnected.isConnected /-
theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F :=
  by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF
#align is_path_connected.is_connected IsPathConnected.isConnected
-/

namespace PathConnectedSpace

variable [PathConnectedSpace X]

/- warning: path_connected_space.exists_path_through_family -> PathConnectedSpace.exists_path_through_family is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_3 : PathConnectedSpace.{u1} X _inst_1] {n : Nat} (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> X), Exists.{succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (γ : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) (p i) (Set.range.{u1, 1} X (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_3 : PathConnectedSpace.{u1} X _inst_1] {n : Nat} (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> X), Exists.{succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (fun (γ : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) => forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) (p i) (Set.range.{u1, 1} X (Set.Elem.{0} Real unitInterval) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ)))
Case conversion may be inaccurate. Consider using '#align path_connected_space.exists_path_through_family PathConnectedSpace.exists_path_through_familyₓ'. -/
theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p n), ∀ i, p i ∈ range γ :=
  by
  have : IsPathConnected (univ : Set X) := path_connected_space_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩
#align path_connected_space.exists_path_through_family PathConnectedSpace.exists_path_through_family

/- warning: path_connected_space.exists_path_through_family' -> PathConnectedSpace.exists_path_through_family' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_3 : PathConnectedSpace.{u1} X _inst_1] {n : Nat} (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> X), Exists.{succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (γ : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => Exists.{1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) (fun (t : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval)) => forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{succ u1} X (coeFn.{succ u1, succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) (fun (_x : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) unitInterval) -> X) (Path.hasCoeToFun.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HasLiftT.mk.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (CoeTCₓ.coe.{1, 1} Nat (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Nat.castCoe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.addMonoidWithOne (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (NeZero.succ n)))))) n))) γ (t i)) (p i)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_3 : PathConnectedSpace.{u1} X _inst_1] {n : Nat} (p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> X), Exists.{succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (fun (γ : Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) => Exists.{1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Set.Elem.{0} Real unitInterval)) (fun (t : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Set.Elem.{0} Real unitInterval)) => forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) (t i)) (FunLike.coe.{succ u1, 1, succ u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) (fun (_x : Set.Elem.{0} Real unitInterval) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : Set.Elem.{0} Real unitInterval) => X) _x) (ContinuousMapClass.toFunLike.{u1, 0, u1} (Path.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n))) (Set.Elem.{0} Real unitInterval) X (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x unitInterval) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) _inst_1 (Path.continuousMapClass.{u1} X _inst_1 (p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p (Nat.cast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (AddMonoidWithOne.toNatCast.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instAddMonoidWithOneFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (NeZero.succ n))) n)))) γ (t i)) (p i)))
Case conversion may be inaccurate. Consider using '#align path_connected_space.exists_path_through_family' PathConnectedSpace.exists_path_through_family'ₓ'. -/
theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p n))(t : Fin (n + 1) → I), ∀ i, γ (t i) = p i :=
  by
  have : IsPathConnected (univ : Set X) := path_connected_space_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩
#align path_connected_space.exists_path_through_family' PathConnectedSpace.exists_path_through_family'

end PathConnectedSpace

/-! ### Locally path connected spaces -/


#print LocPathConnectedSpace /-
/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class LocPathConnectedSpace (X : Type _) [TopologicalSpace X] : Prop where
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id
#align loc_path_connected_space LocPathConnectedSpace
-/

export LocPathConnectedSpace (path_connected_basis)

/- warning: loc_path_connected_of_bases -> locPathConnected_of_bases is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {ι : Type.{u2}} {p : ι -> Prop} {s : X -> ι -> (Set.{u1} X)}, (forall (x : X), Filter.HasBasis.{u1, succ u2} X ι (nhds.{u1} X _inst_1 x) p (s x)) -> (forall (x : X) (i : ι), (p i) -> (IsPathConnected.{u1} X _inst_1 (s x i))) -> (LocPathConnectedSpace.{u1} X _inst_1)
but is expected to have type
  forall {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {ι : Type.{u1}} {p : ι -> Prop} {s : X -> ι -> (Set.{u2} X)}, (forall (x : X), Filter.HasBasis.{u2, succ u1} X ι (nhds.{u2} X _inst_1 x) p (s x)) -> (forall (x : X) (i : ι), (p i) -> (IsPathConnected.{u2} X _inst_1 (s x i))) -> (LocPathConnectedSpace.{u2} X _inst_1)
Case conversion may be inaccurate. Consider using '#align loc_path_connected_of_bases locPathConnected_of_basesₓ'. -/
theorem locPathConnected_of_bases {p : ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis p (s x)) (h' : ∀ x i, p i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X := by
  constructor
  intro x
  apply (h x).to_hasBasis
  · intro i pi
    exact ⟨s x i, ⟨(h x).mem_of_mem pi, h' x i pi⟩, by rfl⟩
  · rintro U ⟨U_in, hU⟩
    rcases(h x).mem_iff.mp U_in with ⟨i, pi, hi⟩
    tauto
#align loc_path_connected_of_bases locPathConnected_of_bases

#print pathConnectedSpace_iff_connectedSpace /-
theorem pathConnectedSpace_iff_connectedSpace [LocPathConnectedSpace X] :
    PathConnectedSpace X ↔ ConnectedSpace X :=
  by
  constructor
  · intro h
    infer_instance
  · intro hX
    rw [pathConnectedSpace_iff_eq]
    use Classical.arbitrary X
    refine' IsClopen.eq_univ ⟨_, _⟩ (by simp)
    · rw [isOpen_iff_mem_nhds]
      intro y y_in
      rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      apply mem_of_superset U_in
      rw [← pathComponent_congr y_in]
      exact hU.subset_path_component (mem_of_mem_nhds U_in)
    · rw [isClosed_iff_nhds]
      intro y H
      rcases(path_connected_basis y).ex_mem with ⟨U, ⟨U_in, hU⟩⟩
      rcases H U U_in with ⟨z, hz, hz'⟩
      exact (hU.joined_in z hz y <| mem_of_mem_nhds U_in).Joined.mem_pathComponent hz'
#align path_connected_space_iff_connected_space pathConnectedSpace_iff_connectedSpace
-/

#print pathConnected_subset_basis /-
theorem pathConnected_subset_basis [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U)
    (hx : x ∈ U) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)
#align path_connected_subset_basis pathConnected_subset_basis
-/

#print locPathConnected_of_isOpen /-
theorem locPathConnected_of_isOpen [LocPathConnectedSpace X] {U : Set X} (h : IsOpen U) :
    LocPathConnectedSpace U :=
  ⟨by
    rintro ⟨x, x_in⟩
    rw [nhds_subtype_eq_comap]
    constructor
    intro V
    rw [(has_basis.comap (coe : U → X) (pathConnected_subset_basis h x_in)).mem_iff]
    constructor
    · rintro ⟨W, ⟨W_in, hW, hWU⟩, hWV⟩
      exact ⟨coe ⁻¹' W, ⟨⟨preimage_mem_comap W_in, hW.preimage_coe hWU⟩, hWV⟩⟩
    · rintro ⟨W, ⟨W_in, hW⟩, hWV⟩
      refine'
        ⟨coe '' W,
          ⟨Filter.image_coe_mem_of_mem_comap (IsOpen.mem_nhds h x_in) W_in,
            hW.image continuous_subtype_val, Subtype.coe_image_subset U W⟩,
          _⟩
      rintro x ⟨y, ⟨y_in, hy⟩⟩
      rw [← Subtype.coe_injective hy]
      tauto⟩
#align loc_path_connected_of_is_open locPathConnected_of_isOpen
-/

#print IsOpen.isConnected_iff_isPathConnected /-
theorem IsOpen.isConnected_iff_isPathConnected [LocPathConnectedSpace X] {U : Set X}
    (U_op : IsOpen U) : IsPathConnected U ↔ IsConnected U :=
  by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  haveI := locPathConnected_of_isOpen U_op
  exact pathConnectedSpace_iff_connectedSpace
#align is_open.is_connected_iff_is_path_connected IsOpen.isConnected_iff_isPathConnected
-/

