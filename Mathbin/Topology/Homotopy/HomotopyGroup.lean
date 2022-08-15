/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
import Mathbin.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental group at `x`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`
* `homotopy_group n x` denoted `π n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary

TODO: show that `π n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups.

-/


open UnitInterval TopologicalSpace

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

variable {n : ℕ} {x : X}

/-- The `n`-dimensional cube.
-/
def Cube (n : ℕ) : Type :=
  Finₓ n → I deriving Zero, One, TopologicalSpace

-- mathport name: «exprI^»
local notation "I^" => Cube

namespace Cube

@[continuity]
theorem proj_continuous (i : Finₓ n) : Continuous fun f : I^ n => f i :=
  continuous_apply i

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
-/
def Boundary (n : ℕ) : Set (I^ n) :=
  { y | ∃ i, y i = 0 ∨ y i = 1 }

/-- The first projection of a positive-dimensional cube.
-/
@[simp]
def head {n} : I^ (n + 1) → I := fun c => c 0

@[continuity]
theorem head.continuous {n} : Continuous (@head n) :=
  proj_continuous 0

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube.
-/
@[simp]
def tail {n} : I^ (n + 1) → I^ n := fun c => Finₓ.tail c

instance uniqueCube0 : Unique (I^ 0) :=
  Pi.uniqueOfIsEmpty _

theorem one_char (f : I^ 1) : f = fun _ => f 0 := by
  convert eq_const_of_unique f

end Cube

/-- The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
-/
structure GenLoop (n : ℕ) (x : X) extends C(I^ n, X) where
  Boundary : ∀, ∀ y ∈ Cube.Boundary n, ∀, to_fun y = x

namespace GenLoop

instance funLike : FunLike (GenLoop n x) (I^ n) fun _ => X where
  coe := fun f => f.1
  coe_injective' := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h => by
    congr
    exact h

@[ext]
theorem ext (f g : GenLoop n x) (H : ∀ y, f y = g y) : f = g :=
  FunLike.ext f g H

@[simp]
theorem mk_apply (f : C(I^ n, X)) (H y) : (⟨f, H⟩ : GenLoop n x) y = f y :=
  rfl

/-- The constant `gen_loop` at `x`.
-/
def const : GenLoop n x :=
  ⟨ContinuousMap.const _ x, fun _ _ => rfl⟩

instance inhabited : Inhabited (GenLoop n x) where default := const

/-- The "homotopy relative to boundary" relation between `gen_loop`s.
-/
def Homotopic (f g : GenLoop n x) : Prop :=
  f.toContinuousMap.HomotopicRel g.toContinuousMap (Cube.Boundary n)

namespace Homotopic

section

variable {f g h : GenLoop n x}

@[refl]
theorem refl (f : GenLoop n x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _

@[symm]
theorem symm (H : f.Homotopic g) : g.Homotopic f :=
  H.symm

@[trans]
theorem trans (H0 : f.Homotopic g) (H1 : g.Homotopic h) : f.Homotopic h :=
  H0.trans H1

theorem equiv : Equivalenceₓ (@Homotopic X _ n x) :=
  ⟨Homotopic.refl, fun _ _ => Homotopic.symm, fun _ _ _ => Homotopic.trans⟩

instance setoid (n : ℕ) (x : X) : Setoidₓ (GenLoop n x) :=
  ⟨Homotopic, equiv⟩

end

end Homotopic

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
`homotopic` relation.
-/
def HomotopyGroup (n : ℕ) (x : X) : Type _ :=
  Quotientₓ (GenLoop.Homotopic.setoid n x)deriving Inhabited

-- mathport name: «exprπ»
local notation "π" => HomotopyGroup

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def genLoopZeroEquiv : GenLoop 0 x ≃ X where
  toFun := fun f => f 0
  invFun := fun x => ⟨ContinuousMap.const _ x, fun _ ⟨f0, _⟩ => f0.elim0⟩
  left_inv := fun f => by
    ext1
    exact congr_arg f (Subsingleton.elimₓ _ _)
  right_inv := fun _ => rfl

/-- The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.
-/
def pi0EquivPathComponents : π 0 x ≃ ZerothHomotopy X :=
  Quotientₓ.congr genLoopZeroEquiv
    (by
      -- joined iff homotopic
      intros
      constructor <;> rintro ⟨H⟩
      exacts[⟨{ toFun := fun t => H ⟨t, Finₓ.elim0⟩,
            source' := (H.apply_zero _).trans (congr_arg a₁ matrix.zero_empty.symm),
            target' := (H.apply_one _).trans (congr_arg a₂ matrix.zero_empty.symm) }⟩,
        ⟨{ toFun := fun t0 => H t0.fst,
            map_zero_left' := fun _ => by
              convert H.source,
            map_one_left' := fun _ => by
              convert H.target,
            prop' := fun _ _ ⟨i, _⟩ => i.elim0 }⟩])

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with
  paths from `x` to itself. -/
@[simps]
def genLoopOneEquivPathSelf : GenLoop 1 x ≃ Path x x where
  toFun := fun p =>
    Path.mk
      ⟨fun t => p fun _ => t, by
        continuity
        exact p.1.2⟩
      (p.Boundary (fun _ => 0) ⟨0, Or.inl rfl⟩) (p.Boundary (fun _ => 1) ⟨1, Or.inr rfl⟩)
  invFun := fun p =>
    { toFun := fun c => p c.head,
      Boundary := by
        rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
        exacts[p.source, p.target] }
  left_inv := fun p => by
    ext1
    exact congr_arg p y.one_char.symm
  right_inv := fun p => by
    ext
    rfl

/-- The first homotopy group at `x` is equivalent to the fundamental group,
i.e. the loops based at `x` up to homotopy.
-/
def pi1EquivFundamentalGroup : π 1 x ≃ FundamentalGroup X x := by
  refine' Equivₓ.trans _ (CategoryTheory.Groupoid.isoEquivHom _ _).symm
  refine' Quotientₓ.congr genLoopOneEquivPathSelf _
  -- homotopic iff homotopic
  intros
  constructor <;> rintro ⟨H⟩
  exacts[⟨{ toFun := fun tx => H (tx.fst, fun _ => tx.snd),
        map_zero_left' := fun _ => by
          convert H.apply_zero _,
        map_one_left' := fun _ => by
          convert H.apply_one _,
        prop' := fun t y iH => H.prop' _ _ ⟨0, iH⟩ }⟩,
    ⟨{ toFun := fun tx => H (tx.fst, tx.snd.head),
        map_zero_left' := fun y => by
          convert H.apply_zero _
          exact y.one_char,
        map_one_left' := fun y => by
          convert H.apply_one _
          exact y.one_char,
        prop' := fun t y ⟨i, iH⟩ => by
          cases Unique.eq_default i
          constructor
          · convert H.eq_fst _ _
            exacts[y.one_char, iH]
            
          · convert H.eq_snd _ _
            exacts[y.one_char, iH]
             }⟩]

