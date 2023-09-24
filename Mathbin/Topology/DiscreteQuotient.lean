/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
import Topology.Separation
import Topology.SubsetProperties
import Topology.LocallyConstant.Basic

#align_import topology.discrete_quotient from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

/-!

# Discrete quotients of a topological space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the type of discrete quotients of a topological space,
denoted `discrete_quotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `discrete_quotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : discrete_quotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : discrete_quotient X`, the space `S` is
  endowed with a `fintype` instance.

## Order structure

The type `discrete_quotient X` is endowed with an instance of a `semilattice_inf` with `order_top`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `discrete_quotient.of_le h`.

Whenever `X` is a locally connected space, the type `discrete_quotient X` is also endowed with an
instance of a `order_bot`, where the bot element `⊥` is given by the `connectedComponentSetoid`,
i.e., `x ~ y` means that `x` and `y` belong to the same connected component. In particular, if `X`
is a discrete topological space, then `x ~ y` is equivalent (propositionally, not definitionally) to
`x = y`.

Given `f : C(X, Y)`, we define a predicate `discrete_quotient.le_comap f A B` for `A :
discrete_quotient X` and `B : discrete_quotient Y`, asserting that `f` descends to `A → B`.  If
`cond : discrete_quotient.le_comap h A B`, the function `A → B` is obtained by
`discrete_quotient.map f cond`.

## Theorems

The two main results proved in this file are:

1. `discrete_quotient.eq_of_forall_proj_eq` which states that when `X` is compact, T₂, and totally
  disconnected, any two elements of `X` are equal if their projections in `Q` agree for all
  `Q : discrete_quotient X`.

2. `discrete_quotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : discrete_quotient X` varies, which is compatible with
  respect to `discrete_quotient.of_le`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/


open Set Function

variable {α X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

#print DiscreteQuotient /-
/-- The type of discrete quotients of a topological space. -/
@[ext]
structure DiscreteQuotient (X : Type _) [TopologicalSpace X] extends Setoid X where
  isOpen_setOf_rel : ∀ x, IsOpen (setOf (to_setoid.Rel x))
#align discrete_quotient DiscreteQuotient
-/

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

#print DiscreteQuotient.ofClopen /-
/-- Construct a discrete quotient from a clopen set. -/
def ofClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X
    where
  toSetoid :=
    ⟨fun x y => x ∈ A ↔ y ∈ A, fun _ => Iff.rfl, fun _ _ => Iff.symm, fun _ _ _ => Iff.trans⟩
  isOpen_setOf_rel x := by by_cases hx : x ∈ A <;> simp [Setoid.Rel, hx, h.1, h.2, ← compl_set_of]
#align discrete_quotient.of_clopen DiscreteQuotient.ofClopen
-/

#print DiscreteQuotient.refl /-
theorem refl : ∀ x, S.Rel x x :=
  S.refl'
#align discrete_quotient.refl DiscreteQuotient.refl
-/

#print DiscreteQuotient.symm /-
theorem symm {x y : X} : S.Rel x y → S.Rel y x :=
  S.symm'
#align discrete_quotient.symm DiscreteQuotient.symm
-/

#print DiscreteQuotient.trans /-
theorem trans {x y z} : S.Rel x y → S.Rel y z → S.Rel x z :=
  S.trans'
#align discrete_quotient.trans DiscreteQuotient.trans
-/

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc to_setoid

instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.toSetoid⟩

instance : TopologicalSpace S :=
  Quotient.topologicalSpace

#print DiscreteQuotient.proj /-
/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S :=
  Quotient.mk''
#align discrete_quotient.proj DiscreteQuotient.proj
-/

#print DiscreteQuotient.fiber_eq /-
theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = setOf (S.Rel x) :=
  Set.ext fun y => eq_comm.trans Quotient.eq''
#align discrete_quotient.fiber_eq DiscreteQuotient.fiber_eq
-/

#print DiscreteQuotient.proj_surjective /-
theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.surjective_Quotient_mk''
#align discrete_quotient.proj_surjective DiscreteQuotient.proj_surjective
-/

#print DiscreteQuotient.proj_quotientMap /-
theorem proj_quotientMap : QuotientMap S.proj :=
  quotientMap_quot_mk
#align discrete_quotient.proj_quotient_map DiscreteQuotient.proj_quotientMap
-/

#print DiscreteQuotient.proj_continuous /-
theorem proj_continuous : Continuous S.proj :=
  S.proj_quotientMap.Continuous
#align discrete_quotient.proj_continuous DiscreteQuotient.proj_continuous
-/

instance : DiscreteTopology S :=
  singletons_open_iff_discrete.1 <|
    S.proj_surjective.forall.2 fun x => by rw [← S.proj_quotient_map.is_open_preimage, fiber_eq];
      exact S.is_open_set_of_rel _

#print DiscreteQuotient.proj_isLocallyConstant /-
theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous
#align discrete_quotient.proj_is_locally_constant DiscreteQuotient.proj_isLocallyConstant
-/

#print DiscreteQuotient.isClopen_preimage /-
theorem isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  (isClopen_discrete A).Preimage S.proj_continuous
#align discrete_quotient.is_clopen_preimage DiscreteQuotient.isClopen_preimage
-/

#print DiscreteQuotient.isOpen_preimage /-
theorem isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).1
#align discrete_quotient.is_open_preimage DiscreteQuotient.isOpen_preimage
-/

#print DiscreteQuotient.isClosed_preimage /-
theorem isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).2
#align discrete_quotient.is_closed_preimage DiscreteQuotient.isClosed_preimage
-/

#print DiscreteQuotient.isClopen_setOf_rel /-
theorem isClopen_setOf_rel (x : X) : IsClopen (setOf (S.Rel x)) := by rw [← fiber_eq];
  apply is_clopen_preimage
#align discrete_quotient.is_clopen_set_of_rel DiscreteQuotient.isClopen_setOf_rel
-/

instance : Inf (DiscreteQuotient X) :=
  ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩

instance : SemilatticeInf (DiscreteQuotient X) :=
  Injective.semilatticeInf toSetoid ext fun _ _ => rfl

instance : OrderTop (DiscreteQuotient X)
    where
  top := ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

instance : Inhabited (DiscreteQuotient X) :=
  ⟨⊤⟩

#print DiscreteQuotient.inhabitedQuotient /-
instance inhabitedQuotient [Inhabited X] : Inhabited S :=
  ⟨S.proj default⟩
#align discrete_quotient.inhabited_quotient DiscreteQuotient.inhabitedQuotient
-/

instance [Nonempty X] : Nonempty S :=
  Nonempty.map S.proj ‹_›

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

#print DiscreteQuotient.comap /-
/-- Comap a discrete quotient along a continuous map. -/
def comap (S : DiscreteQuotient Y) : DiscreteQuotient X
    where
  toSetoid := Setoid.comap f S.1
  isOpen_setOf_rel y := (S.2 _).Preimage f.Continuous
#align discrete_quotient.comap DiscreteQuotient.comap
-/

#print DiscreteQuotient.comap_id /-
@[simp]
theorem comap_id : S.comap (ContinuousMap.id X) = S := by ext; rfl
#align discrete_quotient.comap_id DiscreteQuotient.comap_id
-/

#print DiscreteQuotient.comap_comp /-
@[simp]
theorem comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).comap f :=
  rfl
#align discrete_quotient.comap_comp DiscreteQuotient.comap_comp
-/

#print DiscreteQuotient.comap_mono /-
@[mono]
theorem comap_mono {A B : DiscreteQuotient Y} (h : A ≤ B) : A.comap f ≤ B.comap f := by tauto
#align discrete_quotient.comap_mono DiscreteQuotient.comap_mono
-/

end Comap

section OfLe

variable {A B C : DiscreteQuotient X}

#print DiscreteQuotient.ofLE /-
/-- The map induced by a refinement of a discrete quotient. -/
def ofLE (h : A ≤ B) : A → B :=
  Quotient.map' (fun x => x) h
#align discrete_quotient.of_le DiscreteQuotient.ofLE
-/

#print DiscreteQuotient.ofLE_refl /-
@[simp]
theorem ofLE_refl : ofLE (le_refl A) = id := by ext ⟨⟩; rfl
#align discrete_quotient.of_le_refl DiscreteQuotient.ofLE_refl
-/

#print DiscreteQuotient.ofLE_refl_apply /-
theorem ofLE_refl_apply (a : A) : ofLE (le_refl A) a = a := by simp
#align discrete_quotient.of_le_refl_apply DiscreteQuotient.ofLE_refl_apply
-/

#print DiscreteQuotient.ofLE_ofLE /-
@[simp]
theorem ofLE_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) (x : A) : ofLE h₂ (ofLE h₁ x) = ofLE (h₁.trans h₂) x :=
  by rcases x with ⟨⟩; rfl
#align discrete_quotient.of_le_of_le DiscreteQuotient.ofLE_ofLE
-/

#print DiscreteQuotient.ofLE_comp_ofLE /-
@[simp]
theorem ofLE_comp_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂) :=
  funext <| ofLE_ofLE _ _
#align discrete_quotient.of_le_comp_of_le DiscreteQuotient.ofLE_comp_ofLE
-/

#print DiscreteQuotient.ofLE_continuous /-
theorem ofLE_continuous (h : A ≤ B) : Continuous (ofLE h) :=
  continuous_of_discreteTopology
#align discrete_quotient.of_le_continuous DiscreteQuotient.ofLE_continuous
-/

#print DiscreteQuotient.ofLE_proj /-
@[simp]
theorem ofLE_proj (h : A ≤ B) (x : X) : ofLE h (A.proj x) = B.proj x :=
  Quotient.sound' (B.refl _)
#align discrete_quotient.of_le_proj DiscreteQuotient.ofLE_proj
-/

#print DiscreteQuotient.ofLE_comp_proj /-
@[simp]
theorem ofLE_comp_proj (h : A ≤ B) : ofLE h ∘ A.proj = B.proj :=
  funext <| ofLE_proj _
#align discrete_quotient.of_le_comp_proj DiscreteQuotient.ofLE_comp_proj
-/

end OfLe

/-- When `X` is a locally connected space, there is an `order_bot` instance on
`discrete_quotient X`. The bottom element is given by `connected_component_setoid X`
-/
instance [LocallyConnectedSpace X] : OrderBot (DiscreteQuotient X)
    where
  bot :=
    { toSetoid := connectedComponentSetoid X
      isOpen_setOf_rel := fun x =>
        by
        have : connectedComponent x = {y | (connectedComponentSetoid X).Rel x y} :=
          by
          ext y
          simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using eq_comm
        rw [← this]
        exact isOpen_connectedComponent }
  bot_le S x y (h : connectedComponent x = connectedComponent y) :=
    (S.isClopen_setOf_rel x).connectedComponent_subset (S.refl _) <| h.symm ▸ mem_connectedComponent

#print DiscreteQuotient.proj_bot_eq /-
@[simp]
theorem proj_bot_eq [LocallyConnectedSpace X] {x y : X} :
    proj ⊥ x = proj ⊥ y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
#align discrete_quotient.proj_bot_eq DiscreteQuotient.proj_bot_eq
-/

#print DiscreteQuotient.proj_bot_inj /-
theorem proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y := by simp
#align discrete_quotient.proj_bot_inj DiscreteQuotient.proj_bot_inj
-/

#print DiscreteQuotient.proj_bot_injective /-
theorem proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient X).proj :=
  fun _ _ => proj_bot_inj.1
#align discrete_quotient.proj_bot_injective DiscreteQuotient.proj_bot_injective
-/

#print DiscreteQuotient.proj_bot_bijective /-
theorem proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩
#align discrete_quotient.proj_bot_bijective DiscreteQuotient.proj_bot_bijective
-/

section Map

variable (f : C(X, Y)) (A A' : DiscreteQuotient X) (B B' : DiscreteQuotient Y)

#print DiscreteQuotient.LEComap /-
/-- Given `f : C(X, Y)`, `le_comap cont A B` is defined as `A ≤ B.comap f`. Mathematically this
means that `f` descends to a morphism `A → B`. -/
def LEComap : Prop :=
  A ≤ B.comap f
#align discrete_quotient.le_comap DiscreteQuotient.LEComap
-/

#print DiscreteQuotient.leComap_id /-
theorem leComap_id : LEComap (ContinuousMap.id X) A A := fun _ _ => id
#align discrete_quotient.le_comap_id DiscreteQuotient.leComap_id
-/

variable {A A' B B'} {f} {g : C(Y, Z)} {C : DiscreteQuotient Z}

#print DiscreteQuotient.leComap_id_iff /-
@[simp]
theorem leComap_id_iff : LEComap (ContinuousMap.id X) A A' ↔ A ≤ A' :=
  Iff.rfl
#align discrete_quotient.le_comap_id_iff DiscreteQuotient.leComap_id_iff
-/

#print DiscreteQuotient.LEComap.comp /-
theorem LEComap.comp : LEComap g B C → LEComap f A B → LEComap (g.comp f) A C := by tauto
#align discrete_quotient.le_comap.comp DiscreteQuotient.LEComap.comp
-/

#print DiscreteQuotient.LEComap.mono /-
theorem LEComap.mono (h : LEComap f A B) (hA : A' ≤ A) (hB : B ≤ B') : LEComap f A' B' :=
  hA.trans <| le_trans h <| comap_mono _ hB
#align discrete_quotient.le_comap.mono DiscreteQuotient.LEComap.mono
-/

#print DiscreteQuotient.map /-
/-- Map a discrete quotient along a continuous map. -/
def map (f : C(X, Y)) (cond : LEComap f A B) : A → B :=
  Quotient.map' f cond
#align discrete_quotient.map DiscreteQuotient.map
-/

#print DiscreteQuotient.map_continuous /-
theorem map_continuous (cond : LEComap f A B) : Continuous (map f cond) :=
  continuous_of_discreteTopology
#align discrete_quotient.map_continuous DiscreteQuotient.map_continuous
-/

#print DiscreteQuotient.map_comp_proj /-
@[simp]
theorem map_comp_proj (cond : LEComap f A B) : map f cond ∘ A.proj = B.proj ∘ f :=
  rfl
#align discrete_quotient.map_comp_proj DiscreteQuotient.map_comp_proj
-/

#print DiscreteQuotient.map_proj /-
@[simp]
theorem map_proj (cond : LEComap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) :=
  rfl
#align discrete_quotient.map_proj DiscreteQuotient.map_proj
-/

#print DiscreteQuotient.map_id /-
@[simp]
theorem map_id : map _ (leComap_id A) = id := by ext ⟨⟩ <;> rfl
#align discrete_quotient.map_id DiscreteQuotient.map_id
-/

#print DiscreteQuotient.map_comp /-
@[simp]
theorem map_comp (h1 : LEComap g B C) (h2 : LEComap f A B) :
    map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 := by ext ⟨⟩; rfl
#align discrete_quotient.map_comp DiscreteQuotient.map_comp
-/

#print DiscreteQuotient.ofLE_map /-
@[simp]
theorem ofLE_map (cond : LEComap f A B) (h : B ≤ B') (a : A) :
    ofLE h (map f cond a) = map f (cond.mono le_rfl h) a := by rcases a with ⟨⟩; rfl
#align discrete_quotient.of_le_map DiscreteQuotient.ofLE_map
-/

#print DiscreteQuotient.ofLE_comp_map /-
@[simp]
theorem ofLE_comp_map (cond : LEComap f A B) (h : B ≤ B') :
    ofLE h ∘ map f cond = map f (cond.mono le_rfl h) :=
  funext <| ofLE_map cond h
#align discrete_quotient.of_le_comp_map DiscreteQuotient.ofLE_comp_map
-/

#print DiscreteQuotient.map_ofLE /-
@[simp]
theorem map_ofLE (cond : LEComap f A B) (h : A' ≤ A) (c : A') :
    map f cond (ofLE h c) = map f (cond.mono h le_rfl) c := by rcases c with ⟨⟩; rfl
#align discrete_quotient.map_of_le DiscreteQuotient.map_ofLE
-/

#print DiscreteQuotient.map_comp_ofLE /-
@[simp]
theorem map_comp_ofLE (cond : LEComap f A B) (h : A' ≤ A) :
    map f cond ∘ ofLE h = map f (cond.mono h le_rfl) :=
  funext <| map_ofLE cond h
#align discrete_quotient.map_comp_of_le DiscreteQuotient.map_comp_ofLE
-/

end Map

#print DiscreteQuotient.eq_of_forall_proj_eq /-
theorem eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
    {x y : X} (h : ∀ Q : DiscreteQuotient X, Q.proj x = Q.proj y) : x = y :=
  by
  rw [← mem_singleton_iff, ← connectedComponent_eq_singleton, connectedComponent_eq_iInter_clopen,
    mem_Inter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (of_clopen hU1))).mpr hU2
#align discrete_quotient.eq_of_forall_proj_eq DiscreteQuotient.eq_of_forall_proj_eq
-/

#print DiscreteQuotient.fiber_subset_ofLE /-
theorem fiber_subset_ofLE {A B : DiscreteQuotient X} (h : A ≤ B) (a : A) :
    A.proj ⁻¹' {a} ⊆ B.proj ⁻¹' {ofLE h a} :=
  by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq, of_le_proj, fiber_eq]
  exact fun _ h' => h h'
#align discrete_quotient.fiber_subset_of_le DiscreteQuotient.fiber_subset_ofLE
-/

#print DiscreteQuotient.exists_of_compat /-
theorem exists_of_compat [CompactSpace X] (Qs : ∀ Q : DiscreteQuotient X, Q)
    (compat : ∀ (A B : DiscreteQuotient X) (h : A ≤ B), ofLE h (Qs _) = Qs _) :
    ∃ x : X, ∀ Q : DiscreteQuotient X, Q.proj x = Qs _ :=
  by
  obtain ⟨x, hx⟩ : (⋂ Q, proj Q ⁻¹' {Qs Q}).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_inf fun A B h => _)
      (fun Q => (singleton_nonempty _).Preimage Q.proj_surjective)
      (fun i => (is_closed_preimage _ _).IsCompact) fun i => is_closed_preimage _ _
  · refine' ⟨x, fun Q => _⟩
    exact hx _ ⟨Q, rfl⟩
  · rw [← compat _ _ h]
    exact fiber_subset_of_le _ _
#align discrete_quotient.exists_of_compat DiscreteQuotient.exists_of_compat
-/

instance [CompactSpace X] : Finite S :=
  by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this 

end DiscreteQuotient

namespace LocallyConstant

variable {X} (f : LocallyConstant X α)

#print LocallyConstant.discreteQuotient /-
/-- Any locally constant function induces a discrete quotient. -/
def discreteQuotient : DiscreteQuotient X
    where
  toSetoid := Setoid.comap f ⊥
  isOpen_setOf_rel x := f.IsLocallyConstant _
#align locally_constant.discrete_quotient LocallyConstant.discreteQuotient
-/

#print LocallyConstant.lift /-
/-- The (locally constant) function from the discrete quotient associated to a locally constant
function. -/
def lift : LocallyConstant f.DiscreteQuotient α :=
  ⟨fun a => Quotient.liftOn' a f fun a b => id, fun A => isOpen_discrete _⟩
#align locally_constant.lift LocallyConstant.lift
-/

#print LocallyConstant.lift_comp_proj /-
@[simp]
theorem lift_comp_proj : f.lift ∘ f.DiscreteQuotient.proj = f := by ext; rfl
#align locally_constant.lift_comp_proj LocallyConstant.lift_comp_proj
-/

end LocallyConstant

