/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Data.Set.UnionLift
import Mathbin.Topology.Homeomorph

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/


/-- Bundled continuous maps. -/
@[protect_proj]
structure ContinuousMap (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  continuous_to_fun : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'

-- mathport name: «exprC( , )»
notation "C(" α ", " β ")" => ContinuousMap α β

namespace ContinuousMap

attribute [continuity] ContinuousMap.continuous_to_fun

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

instance : CoeFun C(α, β) fun _ => α → β :=
  ⟨ContinuousMap.toFun⟩

@[simp]
theorem to_fun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl

variable {α β} {f g : ContinuousMap α β}

@[continuity]
protected theorem continuous (f : C(α, β)) : Continuous f :=
  f.continuous_to_fun

@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous f := by
  cases f
  rw [@coe_fn_coe_base']
  continuity

protected theorem continuous_at (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.Continuous.ContinuousAt

protected theorem continuous_within_at (f : C(α, β)) (s : Set α) (x : α) : ContinuousWithinAt f s x :=
  f.Continuous.ContinuousWithinAt

protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl

protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g := by
  cases f <;> cases g <;> congr <;> exact funext H

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨ContinuousMap.congr_fun, ext⟩

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨{ toFun := fun _ => default }⟩

theorem coe_injective : @Function.Injective C(α, β) (α → β) coeFn := fun f g h => by
  cases f <;> cases g <;> congr

@[simp]
theorem coe_mk (f : α → β) (h : Continuous f) : ⇑(⟨f, h⟩ : ContinuousMap α β) = f :=
  rfl

section

variable (α β)

/-- The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f, fun f => ⟨f, continuous_of_discrete_topology⟩, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

end

/-- The identity as a continuous map. -/
def id : C(α, α) :=
  ⟨id⟩

@[simp]
theorem id_coe : (id : α → α) = _root_.id :=
  rfl

theorem id_apply (a : α) : id a = a :=
  rfl

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) :=
  ⟨f ∘ g⟩

@[simp]
theorem comp_coe (f : C(β, γ)) (g : C(α, β)) : (comp f g : α → γ) = f ∘ g :=
  rfl

theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem id_comp (f : C(β, γ)) : id.comp f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : C(α, β)) : f.comp id = f := by
  ext
  rfl

/-- Constant map as a continuous map -/
def const (b : β) : C(α, β) :=
  ⟨fun x => b⟩

@[simp]
theorem const_coe (b : β) : (const b : α → β) = fun x => b :=
  rfl

theorem const_apply (b : β) (a : α) : const b a = b :=
  rfl

instance [h : Nonempty α] [Nontrivial β] : Nontrivial C(α, β) where
  exists_pair_ne := by
    obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne β
    refine' ⟨const b₁, const b₂, _⟩
    contrapose! hb
    change const b₁ h.some = const b₂ h.some
    simp [hb]

section Prod

variable {α₁ α₂ β₁ β₂ : Type _} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁] [TopologicalSpace β₂]

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun := fun x => (f x, g x)
  continuous_to_fun := Continuous.prod_mk f.Continuous g.Continuous

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g
  continuous_to_fun := Continuous.prod_map f.Continuous g.Continuous

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl

end Prod

section Pi

variable {I A : Type _} {X : I → Type _} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun := fun i : I => f i a

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) :=
  ⟨f ∘ coe⟩

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ coe :=
  rfl

end Restrict

section Gluing

variable {ι : Type _} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ i j x : α hxi : x ∈ S i hxj : x ∈ S j, φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩) (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

include hφ hS

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) := by
  have H : (⋃ i, S i) = Set.Univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_Union]
    obtain ⟨i, hi⟩ := hS x
    exact ⟨i, mem_of_mem_nhds hi⟩
  refine' ⟨Set.liftCover S (fun i => φ i) hφ H, continuous_subtype_nhds_cover hS _⟩
  intro i
  convert (φ i).Continuous
  ext x
  exact Set.lift_cover_coe x

variable {S φ hφ hS}

@[simp]
theorem lift_cover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x :=
  Set.lift_cover_coe _

@[simp]
theorem lift_cover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i :=
  ext <| lift_cover_coe

omit hφ hS

variable (A : Set (Set α)) (F : ∀ s : Set α hi : s ∈ A, C(s, β))
  (hF : ∀ s hs : s ∈ A t ht : t ∈ A x : α hxi : x ∈ s hxj : x ∈ t, F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

include hF hA

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := coe
  let F : ∀ i : A, C(i, β) := fun i => F i i.Prop
  refine' lift_cover S F (fun i j => hF i i.Prop j j.Prop) _
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩

variable {A F hF hA}

@[simp]
theorem lift_cover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : (coe : A → Set α) ⟨s, hs⟩ := x
  lift_cover_coe x'

@[simp]
theorem lift_cover_restrict' {s : Set α} {hs : s ∈ A} : (liftCover' A F hF hA).restrict s = F s hs :=
  ext <| lift_cover_coe'

end Gluing

end ContinuousMap

/-- The forward direction of a homeomorphism, as a bundled continuous map.
-/
@[simps]
def Homeomorph.toContinuousMap {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) :=
  ⟨e⟩

