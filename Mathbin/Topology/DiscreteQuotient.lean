/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz

! This file was ported from Lean 3 source module topology.discrete_quotient
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.LocallyConstant.Basic

/-!

# Discrete quotients of a topological space.

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
Whenever `X` is discrete, the type `discrete_quotient X` is also endowed with an instance of a
`semilattice_inf` with `order_bot`, where the bot element `⊥` is `X` itself.

Given `f : X → Y` and `h : continuous f`, we define a predicate `le_comap h A B` for
`A : discrete_quotient X` and `B : discrete_quotient Y`, asserting that `f` descends to `A → B`.
If `cond : le_comap h A B`, the function `A → B` is obtained by `discrete_quotient.map cond`.

## Theorems
The two main results proved in this file are:
1. `discrete_quotient.eq_of_proj_eq` which states that when `X` is compact, t2 and totally
  disconnected, any two elements of `X` agree if their projections in `Q` agree for all
  `Q : discrete_quotient X`.
2. `discrete_quotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : discrete_quotient X` varies, which is compatible with
  respect to `discrete_quotient.of_le`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/


variable (X : Type _) [TopologicalSpace X]

/-- The type of discrete quotients of a topological space. -/
@[ext]
structure DiscreteQuotient where
  Rel : X → X → Prop
  Equiv : Equivalence Rel
  clopen : ∀ x, IsClopen (setOf (Rel x))
#align discrete_quotient DiscreteQuotient

namespace DiscreteQuotient

variable {X} (S : DiscreteQuotient X)

/-- Construct a discrete quotient from a clopen set. -/
def ofClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X
    where
  Rel x y := x ∈ A ∧ y ∈ A ∨ x ∉ A ∧ y ∉ A
  Equiv := ⟨by tauto, by tauto, by tauto⟩
  clopen := by
    intro x
    by_cases hx : x ∈ A
    · apply IsClopen.union
      · convert h
        ext
        exact ⟨fun i => i.2, fun i => ⟨hx, i⟩⟩
      · convert isClopen_empty
        tidy
    · apply IsClopen.union
      · convert isClopen_empty
        tidy
      · convert IsClopen.compl h
        ext
        exact ⟨fun i => i.2, fun i => ⟨hx, i⟩⟩
#align discrete_quotient.of_clopen DiscreteQuotient.ofClopen

theorem refl : ∀ x : X, S.Rel x x :=
  S.Equiv.1
#align discrete_quotient.refl DiscreteQuotient.refl

theorem symm : ∀ x y : X, S.Rel x y → S.Rel y x :=
  S.Equiv.2.1
#align discrete_quotient.symm DiscreteQuotient.symm

theorem trans : ∀ x y z : X, S.Rel x y → S.Rel y z → S.Rel x z :=
  S.Equiv.2.2
#align discrete_quotient.trans DiscreteQuotient.trans

/-- The setoid whose quotient yields the discrete quotient. -/
def setoid : Setoid X :=
  ⟨S.Rel, S.Equiv⟩
#align discrete_quotient.setoid DiscreteQuotient.setoid

instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.Setoid⟩

instance : TopologicalSpace S :=
  ⊥

/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S :=
  Quotient.mk'
#align discrete_quotient.proj DiscreteQuotient.proj

theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.surjective_Quotient_mk''
#align discrete_quotient.proj_surjective DiscreteQuotient.proj_surjective

theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = setOf (S.Rel x) :=
  by
  ext1 y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq',
    DiscreteQuotient.proj.equations._eqn_1, Set.mem_setOf_eq]
  exact ⟨fun h => S.symm _ _ h, fun h => S.symm _ _ h⟩
#align discrete_quotient.fiber_eq DiscreteQuotient.fiber_eq

theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  by
  rw [(IsLocallyConstant.tFAE S.proj).out 0 3]
  intro x
  rcases S.proj_surjective x with ⟨x, rfl⟩
  simp [fiber_eq, (S.clopen x).1]
#align discrete_quotient.proj_is_locally_constant DiscreteQuotient.proj_isLocallyConstant

theorem proj_continuous : Continuous S.proj :=
  IsLocallyConstant.continuous <| proj_isLocallyConstant _
#align discrete_quotient.proj_continuous DiscreteQuotient.proj_continuous

theorem fiber_closed (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  IsClosed.preimage S.proj_continuous ⟨trivial⟩
#align discrete_quotient.fiber_closed DiscreteQuotient.fiber_closed

theorem fiber_open (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  IsOpen.preimage S.proj_continuous trivial
#align discrete_quotient.fiber_open DiscreteQuotient.fiber_open

theorem fiber_clopen (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  ⟨fiber_open _ _, fiber_closed _ _⟩
#align discrete_quotient.fiber_clopen DiscreteQuotient.fiber_clopen

instance : PartialOrder (DiscreteQuotient X)
    where
  le A B := ∀ x y : X, A.Rel x y → B.Rel x y
  le_refl a := by tauto
  le_trans a b c h1 h2 := by tauto
  le_antisymm a b h1 h2 := by
    ext
    tauto

instance : OrderTop (DiscreteQuotient X)
    where
  top := ⟨fun a b => True, ⟨by tauto, by tauto, by tauto⟩, fun _ => isClopen_univ⟩
  le_top a := by tauto

instance : SemilatticeInf (DiscreteQuotient X) :=
  {
    DiscreteQuotient.partialOrder with
    inf := fun A B =>
      { Rel := fun x y => A.Rel x y ∧ B.Rel x y
        Equiv :=
          ⟨fun a => ⟨A.refl _, B.refl _⟩, fun a b h => ⟨A.symm _ _ h.1, B.symm _ _ h.2⟩,
            fun a b c h1 h2 => ⟨A.trans _ _ _ h1.1 h2.1, B.trans _ _ _ h1.2 h2.2⟩⟩
        clopen := fun x => IsClopen.inter (A.clopen _) (B.clopen _) }
    inf_le_left := fun a b => by tauto
    inf_le_right := fun a b => by tauto
    le_inf := fun a b c h1 h2 => by tauto }

instance : Inhabited (DiscreteQuotient X) :=
  ⟨⊤⟩

section Comap

variable {Y : Type _} [TopologicalSpace Y] {f : Y → X} (cont : Continuous f)

/-- Comap a discrete quotient along a continuous map. -/
def comap : DiscreteQuotient Y where
  Rel a b := S.Rel (f a) (f b)
  Equiv := ⟨fun a => S.refl _, fun a b h => S.symm _ _ h, fun a b c h1 h2 => S.trans _ _ _ h1 h2⟩
  clopen y := ⟨IsOpen.preimage cont (S.clopen _).1, IsClosed.preimage cont (S.clopen _).2⟩
#align discrete_quotient.comap DiscreteQuotient.comap

@[simp]
theorem comap_id : S.comap (continuous_id : Continuous (id : X → X)) = S :=
  by
  ext
  rfl
#align discrete_quotient.comap_id DiscreteQuotient.comap_id

@[simp]
theorem comap_comp {Z : Type _} [TopologicalSpace Z] {g : Z → Y} (cont' : Continuous g) :
    S.comap (Continuous.comp cont cont') = (S.comap cont).comap cont' :=
  by
  ext
  rfl
#align discrete_quotient.comap_comp DiscreteQuotient.comap_comp

theorem comap_mono {A B : DiscreteQuotient X} (h : A ≤ B) : A.comap cont ≤ B.comap cont := by tauto
#align discrete_quotient.comap_mono DiscreteQuotient.comap_mono

end Comap

section OfLe

/-- The map induced by a refinement of a discrete quotient. -/
def ofLe {A B : DiscreteQuotient X} (h : A ≤ B) : A → B := fun a =>
  Quotient.liftOn' a (fun x => B.proj x) fun a b i => Quotient.sound' (h _ _ i)
#align discrete_quotient.of_le DiscreteQuotient.ofLe

@[simp]
theorem ofLe_refl {A : DiscreteQuotient X} : ofLe (le_refl A) = id :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.of_le_refl DiscreteQuotient.ofLe_refl

theorem ofLe_refl_apply {A : DiscreteQuotient X} (a : A) : ofLe (le_refl A) a = a := by simp
#align discrete_quotient.of_le_refl_apply DiscreteQuotient.ofLe_refl_apply

@[simp]
theorem ofLe_comp {A B C : DiscreteQuotient X} (h1 : A ≤ B) (h2 : B ≤ C) :
    ofLe (le_trans h1 h2) = ofLe h2 ∘ ofLe h1 :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.of_le_comp DiscreteQuotient.ofLe_comp

theorem ofLe_comp_apply {A B C : DiscreteQuotient X} (h1 : A ≤ B) (h2 : B ≤ C) (a : A) :
    ofLe (le_trans h1 h2) a = ofLe h2 (ofLe h1 a) := by simp
#align discrete_quotient.of_le_comp_apply DiscreteQuotient.ofLe_comp_apply

theorem ofLe_continuous {A B : DiscreteQuotient X} (h : A ≤ B) : Continuous (ofLe h) :=
  continuous_of_discreteTopology
#align discrete_quotient.of_le_continuous DiscreteQuotient.ofLe_continuous

@[simp]
theorem ofLe_proj {A B : DiscreteQuotient X} (h : A ≤ B) : ofLe h ∘ A.proj = B.proj :=
  by
  ext
  exact Quotient.sound' (B.refl _)
#align discrete_quotient.of_le_proj DiscreteQuotient.ofLe_proj

@[simp]
theorem ofLe_proj_apply {A B : DiscreteQuotient X} (h : A ≤ B) (x : X) :
    ofLe h (A.proj x) = B.proj x :=
  by
  change (of_le h ∘ A.proj) x = _
  simp
#align discrete_quotient.of_le_proj_apply DiscreteQuotient.ofLe_proj_apply

end OfLe

/-- When X is discrete, there is a `order_bot` instance on `discrete_quotient X`
-/
instance [DiscreteTopology X] : OrderBot (DiscreteQuotient X)
    where
  bot :=
    { Rel := (· = ·)
      Equiv := eq_equivalence
      clopen := fun x => isClopen_discrete _ }
  bot_le := by
    rintro S a b (h : a = b)
    rw [h]
    exact S.refl _

theorem proj_bot_injective [DiscreteTopology X] :
    Function.Injective (⊥ : DiscreteQuotient X).proj := fun a b h => Quotient.exact' h
#align discrete_quotient.proj_bot_injective DiscreteQuotient.proj_bot_injective

theorem proj_bot_bijective [DiscreteTopology X] :
    Function.Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩
#align discrete_quotient.proj_bot_bijective DiscreteQuotient.proj_bot_bijective

section Map

variable {Y : Type _} [TopologicalSpace Y] {f : Y → X} (cont : Continuous f)
  (A : DiscreteQuotient Y) (B : DiscreteQuotient X)

/-- Given `cont : continuous f`, `le_comap cont A B` is defined as `A ≤ B.comap f`.
Mathematically this means that `f` descends to a morphism `A → B`.
-/
def LeComap : Prop :=
  A ≤ B.comap cont
#align discrete_quotient.le_comap DiscreteQuotient.LeComap

variable {cont A B}

theorem leComap_id (A : DiscreteQuotient X) : LeComap continuous_id A A := by tauto
#align discrete_quotient.le_comap_id DiscreteQuotient.leComap_id

theorem leComap_comp {Z : Type _} [TopologicalSpace Z] {g : Z → Y} {cont' : Continuous g}
    {C : DiscreteQuotient Z} :
    LeComap cont' C A → LeComap cont A B → LeComap (Continuous.comp cont cont') C B := by tauto
#align discrete_quotient.le_comap_comp DiscreteQuotient.leComap_comp

theorem leComap_trans {C : DiscreteQuotient X} : LeComap cont A B → B ≤ C → LeComap cont A C :=
  fun h1 h2 => le_trans h1 <| comap_mono _ h2
#align discrete_quotient.le_comap_trans DiscreteQuotient.leComap_trans

/-- Map a discrete quotient along a continuous map. -/
def map (cond : LeComap cont A B) : A → B :=
  Quotient.map' f cond
#align discrete_quotient.map DiscreteQuotient.map

theorem map_continuous (cond : LeComap cont A B) : Continuous (map cond) :=
  continuous_of_discreteTopology
#align discrete_quotient.map_continuous DiscreteQuotient.map_continuous

@[simp]
theorem map_proj (cond : LeComap cont A B) : map cond ∘ A.proj = B.proj ∘ f :=
  rfl
#align discrete_quotient.map_proj DiscreteQuotient.map_proj

@[simp]
theorem map_proj_apply (cond : LeComap cont A B) (y : Y) : map cond (A.proj y) = B.proj (f y) :=
  rfl
#align discrete_quotient.map_proj_apply DiscreteQuotient.map_proj_apply

@[simp]
theorem map_id : map (leComap_id A) = id := by
  ext ⟨⟩
  rfl
#align discrete_quotient.map_id DiscreteQuotient.map_id

@[simp]
theorem map_comp {Z : Type _} [TopologicalSpace Z] {g : Z → Y} {cont' : Continuous g}
    {C : DiscreteQuotient Z} (h1 : LeComap cont' C A) (h2 : LeComap cont A B) :
    map (leComap_comp h1 h2) = map h2 ∘ map h1 :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.map_comp DiscreteQuotient.map_comp

@[simp]
theorem ofLe_map {C : DiscreteQuotient X} (cond : LeComap cont A B) (h : B ≤ C) :
    map (leComap_trans cond h) = ofLe h ∘ map cond :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.of_le_map DiscreteQuotient.ofLe_map

@[simp]
theorem ofLe_map_apply {C : DiscreteQuotient X} (cond : LeComap cont A B) (h : B ≤ C) (a : A) :
    map (leComap_trans cond h) a = ofLe h (map cond a) :=
  by
  rcases a with ⟨⟩
  rfl
#align discrete_quotient.of_le_map_apply DiscreteQuotient.ofLe_map_apply

@[simp]
theorem map_ofLe {C : DiscreteQuotient Y} (cond : LeComap cont A B) (h : C ≤ A) :
    map (le_trans h cond) = map cond ∘ ofLe h :=
  by
  ext ⟨⟩
  rfl
#align discrete_quotient.map_of_le DiscreteQuotient.map_ofLe

@[simp]
theorem map_ofLe_apply {C : DiscreteQuotient Y} (cond : LeComap cont A B) (h : C ≤ A) (c : C) :
    map (le_trans h cond) c = map cond (ofLe h c) :=
  by
  rcases c with ⟨⟩
  rfl
#align discrete_quotient.map_of_le_apply DiscreteQuotient.map_ofLe_apply

end Map

theorem eq_of_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X] {x y : X} :
    (∀ Q : DiscreteQuotient X, Q.proj x = Q.proj y) → x = y :=
  by
  intro h
  change x ∈ ({y} : Set X)
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton] at disc
  rw [← disc y, connectedComponent_eq_interᵢ_clopen]
  rintro U ⟨⟨U, hU1, hU2⟩, rfl⟩
  replace h : _ ∨ _ := Quotient.exact' (h (of_clopen hU1))
  tauto
#align discrete_quotient.eq_of_proj_eq DiscreteQuotient.eq_of_proj_eq

theorem fiber_le_ofLe {A B : DiscreteQuotient X} (h : A ≤ B) (a : A) :
    A.proj ⁻¹' {a} ≤ B.proj ⁻¹' {ofLe h a} :=
  by
  induction a
  erw [fiber_eq, fiber_eq]
  tidy
#align discrete_quotient.fiber_le_of_le DiscreteQuotient.fiber_le_ofLe

theorem exists_of_compat [CompactSpace X] (Qs : ∀ Q : DiscreteQuotient X, Q)
    (compat : ∀ (A B : DiscreteQuotient X) (h : A ≤ B), ofLe h (Qs _) = Qs _) :
    ∃ x : X, ∀ Q : DiscreteQuotient X, Q.proj x = Qs _ :=
  by
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_interᵢ_of_directed_nonempty_compact_closed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (fun A B => _) (fun i => _)
      (fun i => (fiber_closed _ _).IsCompact) fun i => fiber_closed _ _
  · refine' ⟨x, fun Q => _⟩
    exact hx _ ⟨Q, rfl⟩
  · refine' ⟨A ⊓ B, fun a ha => _, fun a ha => _⟩
    · dsimp only
      erw [← compat (A ⊓ B) A inf_le_left]
      exact fiber_le_of_le _ _ ha
    · dsimp only
      erw [← compat (A ⊓ B) B inf_le_right]
      exact fiber_le_of_le _ _ ha
  · obtain ⟨x, hx⟩ := i.proj_surjective (Qs i)
    refine' ⟨x, _⟩
    dsimp only
    rw [← hx, fiber_eq]
    apply i.refl
#align discrete_quotient.exists_of_compat DiscreteQuotient.exists_of_compat

noncomputable instance [CompactSpace X] : Fintype S :=
  by
  have cond : IsCompact (⊤ : Set X) := isCompact_univ
  rw [isCompact_iff_finite_subcover] at cond
  have h :=
    @cond S (fun s => S.proj ⁻¹' {s}) (fun s => fiber_open _ _) fun x hx =>
      ⟨S.proj ⁻¹' {S.proj x}, ⟨S.proj x, rfl⟩, rfl⟩
  let T := Classical.choose h
  have hT := Classical.choose_spec h
  refine' ⟨T, fun s => _⟩
  rcases S.proj_surjective s with ⟨x, rfl⟩
  rcases hT (by tauto : x ∈ ⊤) with ⟨j, ⟨j, rfl⟩, h1, ⟨hj, rfl⟩, h2⟩
  dsimp only at h2
  suffices S.proj x = j by rwa [this]
  rcases j with ⟨j⟩
  apply Quotient.sound'
  erw [fiber_eq] at h2
  exact S.symm _ _ h2

end DiscreteQuotient

namespace LocallyConstant

variable {X} {α : Type _} (f : LocallyConstant X α)

/-- Any locally constant function induces a discrete quotient. -/
def discreteQuotient : DiscreteQuotient X
    where
  Rel a b := f b = f a
  Equiv := ⟨by tauto, by tauto, fun a b c h1 h2 => by rw [h2, h1]⟩
  clopen x := f.IsLocallyConstant.is_clopen_fiber _
#align locally_constant.discrete_quotient LocallyConstant.discreteQuotient

/-- The function from the discrete quotient associated to a locally constant function. -/
def lift : f.DiscreteQuotient → α := fun a => Quotient.liftOn' a f fun a b h => h.symm
#align locally_constant.lift LocallyConstant.lift

theorem lift_isLocallyConstant : IsLocallyConstant f.lift := fun A => trivial
#align locally_constant.lift_is_locally_constant LocallyConstant.lift_isLocallyConstant

/-- A locally constant version of `locally_constant.lift`. -/
def locallyConstantLift : LocallyConstant f.DiscreteQuotient α :=
  ⟨f.lift, f.lift_is_locally_constant⟩
#align locally_constant.locally_constant_lift LocallyConstant.locallyConstantLift

@[simp]
theorem lift_eq_coe : f.lift = f.locallyConstantLift :=
  rfl
#align locally_constant.lift_eq_coe LocallyConstant.lift_eq_coe

@[simp]
theorem factors : f.locallyConstantLift ∘ f.DiscreteQuotient.proj = f :=
  by
  ext
  rfl
#align locally_constant.factors LocallyConstant.factors

end LocallyConstant

