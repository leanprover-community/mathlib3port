/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
import AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import GroupTheory.EckmannHilton
import Logic.Equiv.TransferInstance
import Algebra.Group.Ext

#align_import topology.homotopy.homotopy_group from "leanprover-community/mathlib"@"4c3e1721c58ef9087bbc2c8c38b540f70eda2e53"

/-!
# `n`th homotopy group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the `n`th homotopy group at `x : X`, `π_n X x`, as the equivalence classes
of functions from the `n`-dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop (fin n) x`; in particular
`gen_loop (fin 1) x ≃ path x x`.

We show that `π_0 X x` is equivalent to the path-connected components, and
that `π_1 X x` is equivalent to the fundamental group at `x`.
We provide a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `gen_loop N x` is the type of continuous fuctions `I^N → X` that send the boundary to `x`,
* `homotopy_group.pi n X x` denoted `π_ n X x` is the quotient of `gen_loop (fin n) x` by
  homotopy relative to the boundary,
* group instance `group (π_(n+1) X x)`,
* commutative group instance `comm_group (π_(n+2) X x)`.

TODO:
* `Ω^M (Ω^N X) ≃ₜ Ω^(M⊕N) X`, and `Ω^M X ≃ₜ Ω^N X` when `M ≃ N`. Similarly for `π_`.
* Path-induced homomorphisms. Show that `homotopy_group.pi_1_equiv_fundamental_group`
  is a group isomorphism.
* Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/


open scoped unitInterval Topology

open Homeomorph

noncomputable section

scoped[Topology] notation "I^" N => N → I

namespace Cube

#print Cube.boundary /-
/-- The points in a cube with at least one projection equal to 0 or 1. -/
def boundary (N : Type _) : Set (I^N) :=
  {y | ∃ i, y i = 0 ∨ y i = 1}
#align cube.boundary Cube.boundary
-/

variable {N : Type _} [DecidableEq N]

#print Cube.splitAt /-
/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible]
def splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j ≠ i } :=
  funSplitAt I i
#align cube.split_at Cube.splitAt
-/

#print Cube.insertAt /-
/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible]
def insertAt (i : N) : (I × I^{ j // j ≠ i }) ≃ₜ I^N :=
  (funSplitAt I i).symm
#align cube.insert_at Cube.insertAt
-/

#print Cube.insertAt_boundary /-
theorem insertAt_boundary (i : N) {t₀ : I} {t}
    (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary { j // j ≠ i }) : insertAt i ⟨t₀, t⟩ ∈ boundary N :=
  by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [fun_split_at_symm_apply, dif_pos rfl]
  · use j; rwa [fun_split_at_symm_apply, dif_neg j.prop, Subtype.coe_eta]
#align cube.insert_at_boundary Cube.insertAt_boundary
-/

end Cube

variable (N X : Type _) [TopologicalSpace X] (x : X)

#print LoopSpace /-
/-- The space of paths with both endpoints equal to a specified point `x : X`. -/
@[reducible]
def LoopSpace :=
  Path x x
#align loop_space LoopSpace
-/

scoped[Topology] notation "Ω" => LoopSpace

#print LoopSpace.inhabited /-
instance LoopSpace.inhabited : Inhabited (Path x x) :=
  ⟨Path.refl x⟩
#align loop_space.inhabited LoopSpace.inhabited
-/

#print GenLoop /-
/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
def GenLoop : Set C(I^N, X) :=
  {p | ∀ y ∈ Cube.boundary N, p y = x}
#align gen_loop GenLoop
-/

scoped[Topology] notation "Ω^" => GenLoop

variable {N X x}

namespace GenLoop

#print GenLoop.copy /-
/-- Copy of a `gen_loop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
def copy (f : Ω^ N X x) (g : (I^N) → X) (h : g = f) : Ω^ N X x :=
  ⟨⟨g, h.symm ▸ f.1.2⟩, by convert f.2; ext1; simp_rw [h]; rfl⟩
#align gen_loop.copy GenLoop.copy
-/

#print GenLoop.coe_copy /-
theorem coe_copy (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : ⇑(copy f g h) = g :=
  rfl
#align gen_loop.coe_copy GenLoop.coe_copy
-/

#print GenLoop.copy_eq /-
theorem copy_eq (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : copy f g h = f := by ext x;
  exact congr_fun h x
#align gen_loop.copy_eq GenLoop.copy_eq
-/

#print GenLoop.boundary /-
theorem boundary (f : Ω^ N X x) : ∀ y ∈ Cube.boundary N, f y = x :=
  f.2
#align gen_loop.boundary GenLoop.boundary
-/

#print GenLoop.funLike /-
instance funLike : FunLike (Ω^ N X x) (I^N) fun _ => X
    where
  coe f := f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h => by congr; exact h
#align gen_loop.fun_like GenLoop.funLike
-/

#print GenLoop.ext /-
@[ext]
theorem ext (f g : Ω^ N X x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.coe_injective' (funext H)
#align gen_loop.ext GenLoop.ext
-/

#print GenLoop.mk_apply /-
@[simp]
theorem mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y :=
  rfl
#align gen_loop.mk_apply GenLoop.mk_apply
-/

#print GenLoop.const /-
/-- The constant `gen_loop` at `x`. -/
def const : Ω^ N X x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩
#align gen_loop.const GenLoop.const
-/

#print GenLoop.const_apply /-
@[simp]
theorem const_apply {t} : (@const N X _ x) t = x :=
  rfl
#align gen_loop.const_apply GenLoop.const_apply
-/

#print GenLoop.inhabited /-
instance inhabited : Inhabited (Ω^ N X x) :=
  ⟨const⟩
#align gen_loop.inhabited GenLoop.inhabited
-/

#print GenLoop.Homotopic /-
/-- The "homotopic relative to boundary" relation between `gen_loop`s. -/
def Homotopic (f g : Ω^ N X x) : Prop :=
  f.1.HomotopicRel g.1 (Cube.boundary N)
#align gen_loop.homotopic GenLoop.Homotopic
-/

namespace homotopic

variable {f g h : Ω^ N X x}

#print GenLoop.Homotopic.refl /-
@[refl]
theorem refl (f : Ω^ N X x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _
#align gen_loop.homotopic.refl GenLoop.Homotopic.refl
-/

#print GenLoop.Homotopic.symm /-
@[symm]
theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm
#align gen_loop.homotopic.symm GenLoop.Homotopic.symm
-/

#print GenLoop.Homotopic.trans /-
@[trans]
theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1
#align gen_loop.homotopic.trans GenLoop.Homotopic.trans
-/

#print GenLoop.Homotopic.equiv /-
theorem equiv : Equivalence (@Homotopic N X _ x) :=
  ⟨Homotopic.refl, fun _ _ => Homotopic.symm, fun _ _ _ => Homotopic.trans⟩
#align gen_loop.homotopic.equiv GenLoop.Homotopic.equiv
-/

#print GenLoop.Homotopic.setoid /-
instance setoid (N) (x : X) : Setoid (Ω^ N X x) :=
  ⟨Homotopic, equiv⟩
#align gen_loop.homotopic.setoid GenLoop.Homotopic.setoid
-/

end homotopic

section LoopHomeo

variable [DecidableEq N]

#print GenLoop.toLoop /-
/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) const
    where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i).toContinuousMap).curry t, fun y yH =>
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine' p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl _⟩; simp
  target' := by ext t; refine' p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr _⟩; simp
#align gen_loop.to_loop GenLoop.toLoop
-/

#print GenLoop.continuous_toLoop /-
theorem continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i) :=
  Path.continuous_uncurry_iff.1 <|
    Continuous.subtype_mk
      (ContinuousMap.continuous_eval'.comp <|
        Continuous.prod_map
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_comp_left _).comp continuous_subtype_val)
          continuous_id)
      _
#align gen_loop.continuous_to_loop GenLoop.continuous_toLoop
-/

#print GenLoop.fromLoop /-
/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps]
def fromLoop (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : Ω^ N X x :=
  ⟨(ContinuousMap.comp ⟨coe⟩ p.toContinuousMap).uncurry.comp (Cube.splitAt i).toContinuousMap,
    by
    rintro y ⟨j, Hj⟩
    simp only [Subtype.val_eq_coe, ContinuousMap.comp_apply, to_continuous_map_apply,
      fun_split_at_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hne := eq_or_ne j i
    · cases Hj <;> simpa only [Hj, p.coe_to_continuous_map, p.source, p.target]
    · exact GenLoop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩⟩
#align gen_loop.from_loop GenLoop.fromLoop
-/

#print GenLoop.continuous_fromLoop /-
theorem continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i) :=
  ((ContinuousMap.continuous_comp_left _).comp <|
        ContinuousMap.continuous_uncurry.comp <|
          (ContinuousMap.continuous_comp _).comp continuous_induced_dom).subtype_mk
    _
#align gen_loop.continuous_from_loop GenLoop.continuous_fromLoop
-/

#print GenLoop.to_from /-
theorem to_from (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : toLoop i (fromLoop i p) = p :=
  by
  simp_rw [to_loop, from_loop, ContinuousMap.comp_assoc, to_continuous_map_as_coe,
    to_continuous_map_comp_symm, ContinuousMap.comp_id]
  ext; rfl
#align gen_loop.to_from GenLoop.to_from
-/

#print GenLoop.loopHomeo /-
/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
@[simps]
def loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j ≠ i } X x) const
    where
  toFun := toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i
#align gen_loop.loop_homeo GenLoop.loopHomeo
-/

#print GenLoop.toLoop_apply /-
theorem toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} :
    toLoop i p t tn = p (Cube.insertAt i ⟨t, tn⟩) :=
  rfl
#align gen_loop.to_loop_apply GenLoop.toLoop_apply
-/

#print GenLoop.fromLoop_apply /-
theorem fromLoop_apply (i : N) {p : Ω (Ω^ { j // j ≠ i } X x) const} {t : I^N} :
    fromLoop i p t = p (t i) (Cube.splitAt i t).snd :=
  rfl
#align gen_loop.from_loop_apply GenLoop.fromLoop_apply
-/

#print GenLoop.cCompInsert /-
/-- Composition with `cube.insert_at` as a continuous map. -/
@[reducible]
def cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j ≠ i }, X)) :=
  ⟨fun f => f.comp (Cube.insertAt i).toContinuousMap,
    (Cube.insertAt i).toContinuousMap.continuous_comp_left⟩
#align gen_loop.c_comp_insert GenLoop.cCompInsert
-/

#print GenLoop.homotopyTo /-
/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
def homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N)) :
    C(I × I, C(I^{ j // j ≠ i }, X)) :=
  ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry
#align gen_loop.homotopy_to GenLoop.homotopyTo
-/

#print GenLoop.homotopyTo_apply /-
-- Should be generated with `@[simps]` but it times out.
theorem homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
    (t : I × I) (tₙ : I^{ j // j ≠ i }) :
    homotopyTo i H t tₙ = H (t.fst, Cube.insertAt i (t.snd, tₙ)) :=
  rfl
#align gen_loop.homotopy_to_apply GenLoop.homotopyTo_apply
-/

#print GenLoop.homotopicTo /-
theorem homotopicTo (i : N) {p q : Ω^ N X x} :
    Homotopic p q → (toLoop i p).Homotopic (toLoop i q) :=
  by
  refine' Nonempty.map fun H => ⟨⟨⟨fun t => ⟨homotopy_to i H t, _⟩, _⟩, _, _⟩, _⟩
  · rintro y ⟨i, iH⟩
    rw [homotopy_to_apply, H.eq_fst, p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · continuity
  show ∀ _ _ _, _
  · intro t y yH
    constructor <;> ext <;> erw [homotopy_to_apply]
    apply H.eq_fst; on_goal 2 => apply H.eq_snd
    all_goals use i; rw [fun_split_at_symm_apply, dif_pos rfl]; exact yH
  all_goals intro; ext; erw [homotopy_to_apply, to_loop_apply]
  exacts [H.apply_zero _, H.apply_one _]
#align gen_loop.homotopic_to GenLoop.homotopicTo
-/

#print GenLoop.homotopyFrom /-
/-- The converse to `gen_loop.homotopy_to`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
def homotopyFrom (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q)) :
    C(I × I^N, X) :=
  (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨coe⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).Prod_map (Cube.splitAt i).toContinuousMap
#align gen_loop.homotopy_from GenLoop.homotopyFrom
-/

#print GenLoop.homotopyFrom_apply /-
-- Should be generated with `@[simps]` but it times out.
theorem homotopyFrom_apply (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q))
    (t : I × I^N) : homotopyFrom i H t = H (t.fst, t.snd i) fun j => t.snd ↑j :=
  rfl
#align gen_loop.homotopy_from_apply GenLoop.homotopyFrom_apply
-/

#print GenLoop.homotopicFrom /-
theorem homotopicFrom (i : N) {p q : Ω^ N X x} :
    (toLoop i p).Homotopic (toLoop i q) → Homotopic p q :=
  by
  refine' Nonempty.map fun H => ⟨⟨homotopy_from i H, _, _⟩, _⟩
  show ∀ _ _ _, _
  · rintro t y ⟨j, jH⟩
    erw [homotopy_from_apply]
    obtain rfl | h := eq_or_ne j i
    · constructor
      · rw [H.eq_fst]; exacts [congr_arg p (Equiv.right_inv _ _), jH]
      · rw [H.eq_snd]; exacts [congr_arg q (Equiv.right_inv _ _), jH]
    · rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩]; constructor <;> · apply boundary; exact ⟨⟨j, h⟩, jH⟩
  all_goals
    intro
    convert homotopy_from_apply _ _ _
    first
    | rw [H.apply_zero]
    | rw [H.apply_one]
    first
    | apply congr_arg p
    | apply congr_arg q
    exact (Equiv.right_inv _ _).symm
#align gen_loop.homotopic_from GenLoop.homotopicFrom
-/

#print GenLoop.transAt /-
/-- Concatenation of two `gen_loop`s along the `i`th coordinate. -/
def transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x :=
  copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t =>
      if (t i : ℝ) ≤ 1 / 2 then f (t.update i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (t.update i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.trans, from_loop, Path.coe_mk_mk, Function.comp_apply, mk_apply,
        ContinuousMap.comp_apply, to_continuous_map_apply, fun_split_at_apply,
        ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry_apply_pair]
      split_ifs; change f _ = _; swap; change g _ = _
      all_goals congr 1)
#align gen_loop.trans_at GenLoop.transAt
-/

#print GenLoop.symmAt /-
/-- Reversal of a `gen_loop` along the `i`th coordinate. -/
def symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x :=
  (copy (fromLoop i (toLoop i f).symm) fun t => f fun j => if j = i then σ (t i) else t j) <| by
    ext1; change _ = f _; congr; ext1; simp
#align gen_loop.symm_at GenLoop.symmAt
-/

#print GenLoop.transAt_distrib /-
theorem transAt_distrib {i j : N} (h : i ≠ j) (a b c d : Ω^ N X x) :
    transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d) :=
  by
  ext; simp_rw [trans_at, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm
#align gen_loop.trans_at_distrib GenLoop.transAt_distrib
-/

#print GenLoop.fromLoop_trans_toLoop /-
theorem fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} :
    fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q :=
  (copy_eq _ _).symm
#align gen_loop.from_loop_trans_to_loop GenLoop.fromLoop_trans_toLoop
-/

#print GenLoop.fromLoop_symm_toLoop /-
theorem fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm = symmAt i p :=
  (copy_eq _ _).symm
#align gen_loop.from_loop_symm_to_loop GenLoop.fromLoop_symm_toLoop
-/

end LoopHomeo

end GenLoop

#print HomotopyGroup /-
/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `gen_loop.homotopic` relation. -/
def HomotopyGroup (N) (X : Type _) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)
deriving Inhabited
#align homotopy_group HomotopyGroup
-/

variable [DecidableEq N]

open GenLoop

#print homotopyGroupEquivFundamentalGroup /-
/-- Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`. -/
def homotopyGroupEquivFundamentalGroup (i : N) :
    HomotopyGroup N X x ≃ FundamentalGroup (Ω^ { j // j ≠ i } X x) const :=
  by
  refine' Equiv.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  apply Quotient.congr (loop_homeo i).toEquiv
  exact fun p q => ⟨homotopic_to i, homotopic_from i⟩
#align homotopy_group_equiv_fundamental_group homotopyGroupEquivFundamentalGroup
-/

#print HomotopyGroup.Pi /-
/-- Homotopy group of finite index. -/
@[reducible]
def HomotopyGroup.Pi (n) (X : Type _) [TopologicalSpace X] (x : X) :=
  HomotopyGroup (Fin n) _ x
#align homotopy_group.pi HomotopyGroup.Pi
-/

scoped[Topology] notation "π_" => HomotopyGroup.Pi

#print genLoopHomeoOfIsEmpty /-
/-- The 0-dimensional generalized loops based at `x` are in bijection with `X`. -/
def genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X
    where
  toFun f := f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ => isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  continuous_toFun := (ContinuousMap.continuous_eval_const (0 : N → I)).comp continuous_induced_dom
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _
#align gen_loop_homeo_of_is_empty genLoopHomeoOfIsEmpty
-/

#print homotopyGroupEquivZerothHomotopyOfIsEmpty /-
/-- The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `zeroth_homotopy`. -/
def homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] :
    HomotopyGroup N X x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intros;
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t => H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            target' := (H.apply_one _).trans (congr_arg a₂ <| Subsingleton.elim _ _) }⟩,
        ⟨{  toFun := fun t0 => H t0.fst
            map_zero_left' := fun _ => by convert H.source
            map_one_left' := fun _ => by convert H.target
            prop' := fun _ _ ⟨i, _⟩ => isEmptyElim i }⟩])
#align homotopy_group_equiv_zeroth_homotopy_of_is_empty homotopyGroupEquivZerothHomotopyOfIsEmpty
-/

#print HomotopyGroup.pi0EquivZerothHomotopy /-
/-- The 0th homotopy "group" is in bijection with `zeroth_homotopy`. -/
def HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X :=
  homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x
#align homotopy_group.pi_0_equiv_zeroth_homotopy HomotopyGroup.pi0EquivZerothHomotopy
-/

#print genLoopEquivOfUnique /-
/-- The 1-dimensional generalized loops based at `x` are in bijection with loops at `x`. -/
@[simps]
def genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x
    where
  toFun p :=
    Path.mk ⟨fun t => p fun _ => t, by continuity⟩
      (GenLoop.boundary _ (fun _ => 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ => 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c => p (c default), by continuity⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
      exacts [p.source, p.target]⟩
  left_inv p := by ext; exact congr_arg p (eq_const_of_unique y).symm
  right_inv p := by ext; rfl
#align gen_loop_equiv_of_unique genLoopEquivOfUnique
-/

#print homotopyGroupEquivFundamentalGroupOfUnique /-
/- TODO (?): deducing this from `homotopy_group_equiv_fundamental_group` would require
  combination of `category_theory.functor.map_Aut` and
  `fundamental_groupoid.fundamental_groupoid_functor` applied to `gen_loop_homeo_of_is_empty`,
  with possibly worse defeq. -/
/-- The homotopy group at `x` indexed by a singleton is in bijection with the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
def homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] :
    HomotopyGroup N X x ≃ FundamentalGroup X x :=
  by
  refine' Equiv.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  refine' Quotient.congr (genLoopEquivOfUnique N) _
  intros; constructor <;> rintro ⟨H⟩
  ·
    exact
      ⟨{  toFun := fun tx => H (tx.fst, fun _ => tx.snd)
          map_zero_left' := fun _ => H.apply_zero _
          map_one_left' := fun _ => H.apply_one _
          prop' := fun t y iH => H.prop' _ _ ⟨default, iH⟩ }⟩
  refine'
    ⟨⟨⟨⟨fun tx => H (tx.fst, tx.snd default), H.continuous.comp _⟩, fun y => _, fun y => _⟩, _⟩⟩
  · exact continuous_fst.prod_mk ((continuous_apply _).comp continuous_snd)
  · convert H.apply_zero _; exact eq_const_of_unique y
  · convert H.apply_one _; exact eq_const_of_unique y
  · rintro t y ⟨i, iH⟩
    cases Unique.eq_default i; constructor
    · convert H.eq_fst _ _; exacts [eq_const_of_unique y, iH]
    · convert H.eq_snd _ _; exacts [eq_const_of_unique y, iH]
#align homotopy_group_equiv_fundamental_group_of_unique homotopyGroupEquivFundamentalGroupOfUnique
-/

#print HomotopyGroup.pi1EquivFundamentalGroup /-
/-- The first homotopy group at `x` is in bijection with the fundamental group. -/
def HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x :=
  homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)
#align homotopy_group.pi_1_equiv_fundamental_group HomotopyGroup.pi1EquivFundamentalGroup
-/

namespace HomotopyGroup

#print HomotopyGroup.group /-
/-- Group structure on `homotopy_group N X x` for nonempty `N` (in particular `π_(n+1) X x`). -/
instance group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).Group
#align homotopy_group.group HomotopyGroup.group
-/

#print HomotopyGroup.auxGroup /-
/-- Group structure on `homotopy_group` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. -/
@[reducible]
def auxGroup (i : N) : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup i).Group
#align homotopy_group.aux_group HomotopyGroup.auxGroup
-/

#print HomotopyGroup.isUnital_auxGroup /-
theorem isUnital_auxGroup (i : N) :
    EckmannHilton.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) :=
  ⟨⟨(auxGroup i).one_mul⟩, ⟨(auxGroup i).mul_one⟩⟩
#align homotopy_group.is_unital_aux_group HomotopyGroup.isUnital_auxGroup
-/

#print HomotopyGroup.auxGroup_indep /-
theorem auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j :=
  by
  by_cases h : i = j; · rw [h]
  refine' Group.ext (EckmannHilton.mul (is_unital_aux_group i) (is_unital_aux_group j) _)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [from_loop_trans_to_loop, trans_at_distrib h, coe_to_equiv, loop_homeo_apply,
    coe_symm_to_equiv, loop_homeo_symm_apply]
#align homotopy_group.aux_group_indep HomotopyGroup.auxGroup_indep
-/

#print HomotopyGroup.transAt_indep /-
theorem transAt_indep {i} (j) (f g : Ω^ N X x) : ⟦transAt i f g⟧ = ⟦transAt j f g⟧ :=
  by
  simp_rw [← from_loop_trans_to_loop]
  have := congr_arg (@Group.mul _) (aux_group_indep i j)
  exact congr_fun₂ this ⟦g⟧ ⟦f⟧
#align homotopy_group.trans_at_indep HomotopyGroup.transAt_indep
-/

#print HomotopyGroup.symmAt_indep /-
theorem symmAt_indep {i} (j) (f : Ω^ N X x) : ⟦symmAt i f⟧ = ⟦symmAt j f⟧ :=
  by
  simp_rw [← from_loop_symm_to_loop]
  have := congr_arg (@Group.inv _) (aux_group_indep i j)
  exact congr_fun this ⟦f⟧
#align homotopy_group.symm_at_indep HomotopyGroup.symmAt_indep
-/

#print HomotopyGroup.one_def /-
/-- Characterization of multiplicative identity -/
theorem one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧ :=
  rfl
#align homotopy_group.one_def HomotopyGroup.one_def
-/

#print HomotopyGroup.mul_spec /-
/-- Characterization of multiplication -/
theorem mul_spec [Nonempty N] {i} {p q : Ω^ N X x} :
    (⟦p⟧ * ⟦q⟧ : HomotopyGroup N X x) = ⟦transAt i q p⟧ := by
  rw [trans_at_indep _ q, ← from_loop_trans_to_loop]; apply Quotient.sound; rfl
#align homotopy_group.mul_spec HomotopyGroup.mul_spec
-/

#print HomotopyGroup.inv_spec /-
/-- Characterization of multiplicative inverse -/
theorem inv_spec [Nonempty N] {i} {p : Ω^ N X x} : ((⟦p⟧)⁻¹ : HomotopyGroup N X x) = ⟦symmAt i p⟧ :=
  by rw [symm_at_indep _ p, ← from_loop_symm_to_loop]; apply Quotient.sound; rfl
#align homotopy_group.inv_spec HomotopyGroup.inv_spec
-/

#print HomotopyGroup.commGroup /-
/-- Multiplication on `homotopy_group N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative. -/
instance commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x) :=
  let h := exists_ne (Classical.arbitrary N)
  @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1 (isUnital_auxGroup h.some) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [from_loop_trans_to_loop, trans_at_distrib h.some_spec, coe_to_equiv,
        loop_homeo_apply, coe_symm_to_equiv, loop_homeo_symm_apply])
#align homotopy_group.comm_group HomotopyGroup.commGroup
-/

end HomotopyGroup

