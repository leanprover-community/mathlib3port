/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.group.basic
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.ConjAct
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Order.Filter.Pointwise
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Topology.Algebra.Constructions

/-!
# Topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/


open Classical Set Filter TopologicalSpace Function

open Classical TopologicalSpace Filter Pointwise

universe u v w x

variable {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/


variable [TopologicalSpace G] [Group G] [HasContinuousMul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulLeft (a : G) : G ≃ₜ G :=
  { Equiv.mulLeft a with 
    continuous_to_fun := continuous_const.mul continuous_id
    continuous_inv_fun := continuous_const.mul continuous_id }
#align homeomorph.mul_left Homeomorph.mulLeft

@[simp, to_additive]
theorem Homeomorph.coe_mul_left (a : G) : ⇑(Homeomorph.mulLeft a) = (· * ·) a :=
  rfl
#align homeomorph.coe_mul_left Homeomorph.coe_mul_left

@[to_additive]
theorem Homeomorph.mul_left_symm (a : G) : (Homeomorph.mulLeft a).symm = Homeomorph.mulLeft a⁻¹ :=
  by 
  ext
  rfl
#align homeomorph.mul_left_symm Homeomorph.mul_left_symm

@[to_additive]
theorem is_open_map_mul_left (a : G) : IsOpenMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsOpenMap
#align is_open_map_mul_left is_open_map_mul_left

@[to_additive IsOpen.left_add_coset]
theorem IsOpen.left_coset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (leftCoset x U) :=
  is_open_map_mul_left x _ h
#align is_open.left_coset IsOpen.left_coset

@[to_additive]
theorem is_closed_map_mul_left (a : G) : IsClosedMap fun x => a * x :=
  (Homeomorph.mulLeft a).IsClosedMap
#align is_closed_map_mul_left is_closed_map_mul_left

@[to_additive IsClosed.left_add_coset]
theorem IsClosed.left_coset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (leftCoset x U) :=
  is_closed_map_mul_left x _ h
#align is_closed.left_coset IsClosed.left_coset

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def Homeomorph.mulRight (a : G) : G ≃ₜ G :=
  { Equiv.mulRight a with
    continuous_to_fun := continuous_id.mul continuous_const
    continuous_inv_fun := continuous_id.mul continuous_const }
#align homeomorph.mul_right Homeomorph.mulRight

@[simp, to_additive]
theorem Homeomorph.coe_mul_right (a : G) : ⇑(Homeomorph.mulRight a) = fun g => g * a :=
  rfl
#align homeomorph.coe_mul_right Homeomorph.coe_mul_right

@[to_additive]
theorem Homeomorph.mul_right_symm (a : G) :
    (Homeomorph.mulRight a).symm = Homeomorph.mulRight a⁻¹ := by
  ext
  rfl
#align homeomorph.mul_right_symm Homeomorph.mul_right_symm

@[to_additive]
theorem is_open_map_mul_right (a : G) : IsOpenMap fun x => x * a :=
  (Homeomorph.mulRight a).IsOpenMap
#align is_open_map_mul_right is_open_map_mul_right

@[to_additive IsOpen.right_add_coset]
theorem IsOpen.right_coset {U : Set G} (h : IsOpen U) (x : G) : IsOpen (rightCoset U x) :=
  is_open_map_mul_right x _ h
#align is_open.right_coset IsOpen.right_coset

@[to_additive]
theorem is_closed_map_mul_right (a : G) : IsClosedMap fun x => x * a :=
  (Homeomorph.mulRight a).IsClosedMap
#align is_closed_map_mul_right is_closed_map_mul_right

@[to_additive IsClosed.right_add_coset]
theorem IsClosed.right_coset {U : Set G} (h : IsClosed U) (x : G) : IsClosed (rightCoset U x) :=
  is_closed_map_mul_right x _ h
#align is_closed.right_coset IsClosed.right_coset

@[to_additive]
theorem discreteTopologyOfOpenSingletonOne (h : IsOpen ({1} : Set G)) : DiscreteTopology G := by
  rw [← singletons_open_iff_discrete]
  intro g
  suffices {g} = (fun x : G => g⁻¹ * x) ⁻¹' {1} by
    rw [this]
    exact (continuous_mul_left g⁻¹).is_open_preimage _ h
  simp only [mul_one, Set.preimage_mul_left_singleton, eq_self_iff_true, inv_inv,
    Set.singleton_eq_singleton_iff]
#align discrete_topology_of_open_singleton_one discreteTopologyOfOpenSingletonOne

@[to_additive]
theorem discrete_topology_iff_open_singleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G) :=
  ⟨fun h => forall_open_iff_discrete.mpr h {1}, discreteTopologyOfOpenSingletonOne⟩
#align discrete_topology_iff_open_singleton_one discrete_topology_iff_open_singleton_one

end ContinuousMulGroup

/-!
### `has_continuous_inv` and `has_continuous_neg`
-/


/-- Basic hypothesis to talk about a topological additive group. A topological additive group
over `M`, for example, is obtained by requiring the instances `add_group M` and
`has_continuous_add M` and `has_continuous_neg M`. -/
class HasContinuousNeg (G : Type u) [TopologicalSpace G] [Neg G] : Prop where
  continuous_neg : Continuous fun a : G => -a
#align has_continuous_neg HasContinuousNeg

/-- Basic hypothesis to talk about a topological group. A topological group over `M`, for example,
is obtained by requiring the instances `group M` and `has_continuous_mul M` and
`has_continuous_inv M`. -/
@[to_additive]
class HasContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where
  continuous_inv : Continuous fun a : G => a⁻¹
#align has_continuous_inv HasContinuousInv

export HasContinuousInv (continuous_inv)

export HasContinuousNeg (continuous_neg)

section ContinuousInv

variable [TopologicalSpace G] [Inv G] [HasContinuousInv G]

@[to_additive]
theorem continuous_on_inv {s : Set G} : ContinuousOn Inv.inv s :=
  continuous_inv.ContinuousOn
#align continuous_on_inv continuous_on_inv

@[to_additive]
theorem continuous_within_at_inv {s : Set G} {x : G} : ContinuousWithinAt Inv.inv s x :=
  continuous_inv.ContinuousWithinAt
#align continuous_within_at_inv continuous_within_at_inv

@[to_additive]
theorem continuous_at_inv {x : G} : ContinuousAt Inv.inv x :=
  continuous_inv.ContinuousAt
#align continuous_at_inv continuous_at_inv

@[to_additive]
theorem tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹) :=
  continuous_at_inv
#align tendsto_inv tendsto_inv

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive
      "If a function converges to a value in an additive topological group, then its\nnegation converges to the negation of this value."]
theorem Filter.Tendsto.inv {f : α → G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹) :=
  (continuous_inv.Tendsto y).comp h
#align filter.tendsto.inv Filter.Tendsto.inv

variable [TopologicalSpace α] {f : α → G} {s : Set α} {x : α}

@[continuity, to_additive]
theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ :=
  continuous_inv.comp hf
#align continuous.inv Continuous.inv

@[to_additive]
theorem ContinuousAt.inv (hf : ContinuousAt f x) : ContinuousAt (fun x => (f x)⁻¹) x :=
  continuous_at_inv.comp hf
#align continuous_at.inv ContinuousAt.inv

@[to_additive]
theorem ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn (fun x => (f x)⁻¹) s :=
  continuous_inv.comp_continuous_on hf
#align continuous_on.inv ContinuousOn.inv

@[to_additive]
theorem ContinuousWithinAt.inv (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x)⁻¹) s x :=
  hf.inv
#align continuous_within_at.inv ContinuousWithinAt.inv

@[to_additive]
instance [TopologicalSpace H] [Inv H] [HasContinuousInv H] : HasContinuousInv (G × H) :=
  ⟨continuous_inv.fst'.prod_mk continuous_inv.snd'⟩

variable {ι : Type _}

@[to_additive]
instance Pi.has_continuous_inv {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Inv (C i)]
    [∀ i, HasContinuousInv (C i)] :
    HasContinuousInv
      (∀ i, C i) where continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.has_continuous_inv Pi.has_continuous_inv

/-- A version of `pi.has_continuous_inv` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_inv` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_neg` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_neg` for non-dependent functions."]
instance Pi.has_continuous_inv' : HasContinuousInv (ι → G) :=
  Pi.has_continuous_inv
#align pi.has_continuous_inv' Pi.has_continuous_inv'

@[to_additive]
instance (priority := 100) has_continuous_inv_of_discrete_topology [TopologicalSpace H] [Inv H]
    [DiscreteTopology H] : HasContinuousInv H :=
  ⟨continuous_of_discrete_topology⟩
#align has_continuous_inv_of_discrete_topology has_continuous_inv_of_discrete_topology

section PointwiseLimits

variable (G₁ G₂ : Type _) [TopologicalSpace G₂] [T2Space G₂]

@[to_additive]
theorem is_closed_set_of_map_inv [Inv G₁] [Inv G₂] [HasContinuousInv G₂] :
    IsClosed { f : G₁ → G₂ | ∀ x, f x⁻¹ = (f x)⁻¹ } := by
  simp only [set_of_forall]
  refine' is_closed_Inter fun i => is_closed_eq (continuous_apply _) (continuous_apply _).inv
#align is_closed_set_of_map_inv is_closed_set_of_map_inv

end PointwiseLimits

instance [TopologicalSpace H] [Inv H] [HasContinuousInv H] :
    HasContinuousNeg (Additive H) where continuous_neg := @continuous_inv H _ _ _

instance [TopologicalSpace H] [Neg H] [HasContinuousNeg H] :
    HasContinuousInv (Multiplicative H) where continuous_inv := @continuous_neg H _ _ _

end ContinuousInv

section ContinuousInvolutiveInv

variable [TopologicalSpace G] [InvolutiveInv G] [HasContinuousInv G] {s : Set G}

@[to_additive]
theorem IsCompact.inv (hs : IsCompact s) : IsCompact s⁻¹ := by
  rw [← image_inv]
  exact hs.image continuous_inv
#align is_compact.inv IsCompact.inv

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def Homeomorph.inv (G : Type _) [TopologicalSpace G] [InvolutiveInv G]
    [HasContinuousInv G] : G ≃ₜ G :=
  { Equiv.inv G with 
    continuous_to_fun := continuous_inv
    continuous_inv_fun := continuous_inv }
#align homeomorph.inv Homeomorph.inv

@[to_additive]
theorem is_open_map_inv : IsOpenMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsOpenMap
#align is_open_map_inv is_open_map_inv

@[to_additive]
theorem is_closed_map_inv : IsClosedMap (Inv.inv : G → G) :=
  (Homeomorph.inv _).IsClosedMap
#align is_closed_map_inv is_closed_map_inv

variable {G}

@[to_additive]
theorem IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹ :=
  hs.Preimage continuous_inv
#align is_open.inv IsOpen.inv

@[to_additive]
theorem IsClosed.inv (hs : IsClosed s) : IsClosed s⁻¹ :=
  hs.Preimage continuous_inv
#align is_closed.inv IsClosed.inv

@[to_additive]
theorem inv_closure : ∀ s : Set G, (closure s)⁻¹ = closure s⁻¹ :=
  (Homeomorph.inv G).preimage_closure
#align inv_closure inv_closure

end ContinuousInvolutiveInv

section LatticeOps

variable {ι' : Sort _} [Inv G]

@[to_additive]
theorem has_continuous_inv_Inf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @HasContinuousInv G t _) : @HasContinuousInv G (inf ts) _ :=
  { continuous_inv :=
      continuous_Inf_rng.2 fun t ht =>
        continuous_Inf_dom ht (@HasContinuousInv.continuous_inv G t _ (h t ht)) }
#align has_continuous_inv_Inf has_continuous_inv_Inf

@[to_additive]
theorem has_continuous_inv_infi {ts' : ι' → TopologicalSpace G}
    (h' : ∀ i, @HasContinuousInv G (ts' i) _) : @HasContinuousInv G (⨅ i, ts' i) _ := by
  rw [← Inf_range]
  exact has_continuous_inv_Inf (set.forall_range_iff.mpr h')
#align has_continuous_inv_infi has_continuous_inv_infi

@[to_additive]
theorem has_continuous_inv_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @HasContinuousInv G t₁ _)
    (h₂ : @HasContinuousInv G t₂ _) : @HasContinuousInv G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_infi]
  refine' has_continuous_inv_infi fun b => _
  cases b <;> assumption
#align has_continuous_inv_inf has_continuous_inv_inf

end LatticeOps

@[to_additive]
theorem Inducing.has_continuous_inv {G H : Type _} [Inv G] [Inv H] [TopologicalSpace G]
    [TopologicalSpace H] [HasContinuousInv H] {f : G → H} (hf : Inducing f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : HasContinuousInv G :=
  ⟨hf.continuous_iff.2 <| by simpa only [(· ∘ ·), hf_inv] using hf.continuous.inv⟩
#align inducing.has_continuous_inv Inducing.has_continuous_inv

section TopologicalGroup

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/


/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class TopologicalAddGroup (G : Type u) [TopologicalSpace G] [AddGroup G] extends HasContinuousAdd G,
  HasContinuousNeg G : Prop
#align topological_add_group TopologicalAddGroup

/-- A topological group is a group in which the multiplication and inversion operations are
continuous.

When you declare an instance that does not already have a `uniform_space` instance,
you should also provide an instance of `uniform_space` and `uniform_group` using
`topological_group.to_uniform_space` and `topological_comm_group_is_uniform`. -/
@[to_additive]
class TopologicalGroup (G : Type _) [TopologicalSpace G] [Group G] extends HasContinuousMul G,
  HasContinuousInv G : Prop
#align topological_group TopologicalGroup

section Conj

instance ConjAct.units_has_continuous_const_smul {M} [Monoid M] [TopologicalSpace M]
    [HasContinuousMul M] : HasContinuousConstSmul (ConjAct Mˣ) M :=
  ⟨fun m => (continuous_const.mul continuous_id).mul continuous_const⟩
#align conj_act.units_has_continuous_const_smul ConjAct.units_has_continuous_const_smul

variable [TopologicalSpace G] [Inv G] [Mul G] [HasContinuousMul G]

/-- Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are continuous. -/
@[to_additive
      "Conjugation is jointly continuous on `G × G` when both `mul` and `inv` are\ncontinuous."]
theorem TopologicalGroup.continuous_conj_prod [HasContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)
#align topological_group.continuous_conj_prod TopologicalGroup.continuous_conj_prod

/-- Conjugation by a fixed element is continuous when `mul` is continuous. -/
@[to_additive "Conjugation by a fixed element is continuous when `add` is continuous."]
theorem TopologicalGroup.continuous_conj (g : G) : Continuous fun h : G => g * h * g⁻¹ :=
  (continuous_mul_right g⁻¹).comp (continuous_mul_left g)
#align topological_group.continuous_conj TopologicalGroup.continuous_conj

/-- Conjugation acting on fixed element of the group is continuous when both `mul` and
`inv` are continuous. -/
@[to_additive
      "Conjugation acting on fixed element of the additive group is continuous when both\n  `add` and `neg` are continuous."]
theorem TopologicalGroup.continuous_conj' [HasContinuousInv G] (h : G) :
    Continuous fun g : G => g * h * g⁻¹ :=
  (continuous_mul_right h).mul continuous_inv
#align topological_group.continuous_conj' TopologicalGroup.continuous_conj'

end Conj

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [TopologicalSpace α] {f : α → G}
  {s : Set α} {x : α}

section Zpow

@[continuity, to_additive]
theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z
  | Int.ofNat n => by simpa using continuous_pow n
  | -[n+1] => by simpa using (continuous_pow (n + 1)).inv
#align continuous_zpow continuous_zpow

instance AddGroup.has_continuous_const_smul_int {A} [AddGroup A] [TopologicalSpace A]
    [TopologicalAddGroup A] : HasContinuousConstSmul ℤ A :=
  ⟨continuous_zsmul⟩
#align add_group.has_continuous_const_smul_int AddGroup.has_continuous_const_smul_int

instance AddGroup.has_continuous_smul_int {A} [AddGroup A] [TopologicalSpace A]
    [TopologicalAddGroup A] : HasContinuousSmul ℤ A :=
  ⟨continuous_uncurry_of_discrete_topology continuous_zsmul⟩
#align add_group.has_continuous_smul_int AddGroup.has_continuous_smul_int

@[continuity, to_additive]
theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z :=
  (continuous_zpow z).comp h
#align continuous.zpow Continuous.zpow

@[to_additive]
theorem continuous_on_zpow {s : Set G} (z : ℤ) : ContinuousOn (fun x => x ^ z) s :=
  (continuous_zpow z).ContinuousOn
#align continuous_on_zpow continuous_on_zpow

@[to_additive]
theorem continuous_at_zpow (x : G) (z : ℤ) : ContinuousAt (fun x => x ^ z) x :=
  (continuous_zpow z).ContinuousAt
#align continuous_at_zpow continuous_at_zpow

@[to_additive]
theorem Filter.Tendsto.zpow {α} {l : Filter α} {f : α → G} {x : G} (hf : Tendsto f l (𝓝 x))
    (z : ℤ) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z)) :=
  (continuous_at_zpow _ _).Tendsto.comp hf
#align filter.tendsto.zpow Filter.Tendsto.zpow

@[to_additive]
theorem ContinuousWithinAt.zpow {f : α → G} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (z : ℤ) : ContinuousWithinAt (fun x => f x ^ z) s x :=
  hf.zpow z
#align continuous_within_at.zpow ContinuousWithinAt.zpow

@[to_additive]
theorem ContinuousAt.zpow {f : α → G} {x : α} (hf : ContinuousAt f x) (z : ℤ) :
    ContinuousAt (fun x => f x ^ z) x :=
  hf.zpow z
#align continuous_at.zpow ContinuousAt.zpow

@[to_additive ContinuousOn.zsmul]
theorem ContinuousOn.zpow {f : α → G} {s : Set α} (hf : ContinuousOn f s) (z : ℤ) :
    ContinuousOn (fun x => f x ^ z) s := fun x hx => (hf x hx).zpow z
#align continuous_on.zpow ContinuousOn.zpow

end Zpow

section OrderedCommGroup

variable [TopologicalSpace H] [OrderedCommGroup H] [TopologicalGroup H]

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi {a : H} : Tendsto Inv.inv (𝓝[>] a) (𝓝[<] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ioi tendsto_inv_nhds_within_Ioi

@[to_additive]
theorem tendsto_inv_nhds_within_Iio {a : H} : Tendsto Inv.inv (𝓝[<] a) (𝓝[>] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iio tendsto_inv_nhds_within_Iio

@[to_additive]
theorem tendsto_inv_nhds_within_Ioi_inv {a : H} : Tendsto Inv.inv (𝓝[>] a⁻¹) (𝓝[<] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhds_within_Ioi _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ioi_inv tendsto_inv_nhds_within_Ioi_inv

@[to_additive]
theorem tendsto_inv_nhds_within_Iio_inv {a : H} : Tendsto Inv.inv (𝓝[<] a⁻¹) (𝓝[>] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhds_within_Iio _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iio_inv tendsto_inv_nhds_within_Iio_inv

@[to_additive]
theorem tendsto_inv_nhds_within_Ici {a : H} : Tendsto Inv.inv (𝓝[≥] a) (𝓝[≤] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Ici tendsto_inv_nhds_within_Ici

@[to_additive]
theorem tendsto_inv_nhds_within_Iic {a : H} : Tendsto Inv.inv (𝓝[≤] a) (𝓝[≥] a⁻¹) :=
  (continuous_inv.Tendsto a).inf <| by simp [tendsto_principal_principal]
#align tendsto_inv_nhds_within_Iic tendsto_inv_nhds_within_Iic

@[to_additive]
theorem tendsto_inv_nhds_within_Ici_inv {a : H} : Tendsto Inv.inv (𝓝[≥] a⁻¹) (𝓝[≤] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhds_within_Ici _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Ici_inv tendsto_inv_nhds_within_Ici_inv

@[to_additive]
theorem tendsto_inv_nhds_within_Iic_inv {a : H} : Tendsto Inv.inv (𝓝[≤] a⁻¹) (𝓝[≥] a) := by
  simpa only [inv_inv] using @tendsto_inv_nhds_within_Iic _ _ _ _ a⁻¹
#align tendsto_inv_nhds_within_Iic_inv tendsto_inv_nhds_within_Iic_inv

end OrderedCommGroup

@[instance, to_additive]
instance [TopologicalSpace H] [Group H] [TopologicalGroup H] :
    TopologicalGroup (G × H) where continuous_inv := continuous_inv.prod_map continuous_inv

@[to_additive]
instance Pi.topological_group {C : β → Type _} [∀ b, TopologicalSpace (C b)] [∀ b, Group (C b)]
    [∀ b, TopologicalGroup (C b)] :
    TopologicalGroup
      (∀ b, C b) where continuous_inv := continuous_pi fun i => (continuous_apply i).inv
#align pi.topological_group Pi.topological_group

open MulOpposite

@[to_additive]
instance [Group α] [HasContinuousInv α] : HasContinuousInv αᵐᵒᵖ :=
  opHomeomorph.symm.Inducing.HasContinuousInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [Group α] [TopologicalGroup α] : TopologicalGroup αᵐᵒᵖ where

variable (G)

@[to_additive]
theorem nhds_one_symm : comap Inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
  ((Homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds inv_one)
#align nhds_one_symm nhds_one_symm

/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.\nThis is a shear mapping."]
protected def Homeomorph.shearMulRight : G × G ≃ₜ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    continuous_to_fun := continuous_fst.prod_mk continuous_mul
    continuous_inv_fun := continuous_fst.prod_mk <| continuous_fst.inv.mul continuous_snd }
#align homeomorph.shear_mul_right Homeomorph.shearMulRight

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_coe :
    ⇑(Homeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl
#align homeomorph.shear_mul_right_coe Homeomorph.shear_mul_right_coe

@[simp, to_additive]
theorem Homeomorph.shear_mul_right_symm_coe :
    ⇑(Homeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl
#align homeomorph.shear_mul_right_symm_coe Homeomorph.shear_mul_right_symm_coe

variable {G}

@[to_additive]
protected theorem Inducing.topological_group {F : Type _} [Group H] [TopologicalSpace H]
    [MonoidHomClass F H G] (f : F) (hf : Inducing f) : TopologicalGroup H :=
  { to_has_continuous_mul := hf.HasContinuousMul _
    to_has_continuous_inv := hf.HasContinuousInv (map_inv f) }
#align inducing.topological_group Inducing.topological_group

@[to_additive]
protected theorem topological_group_induced {F : Type _} [Group H] [MonoidHomClass F H G] (f : F) :
    @TopologicalGroup H (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.topological_group f ⟨rfl⟩
#align topological_group_induced topological_group_induced

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : TopologicalGroup S :=
  Inducing.topological_group S.Subtype inducing_coe

end Subgroup

/-- The (topological-space) closure of a subgroup of a space `M` with `has_continuous_mul` is
itself a subgroup. -/
@[to_additive
      "The (topological-space) closure of an additive subgroup of a space `M` with\n`has_continuous_add` is itself an additive subgroup."]
def Subgroup.topologicalClosure (s : Subgroup G) : Subgroup G :=
  { s.toSubmonoid.topologicalClosure with
    carrier := closure (s : Set G)
    inv_mem' := fun g m => by simpa [← Set.mem_inv, inv_closure] using m }
#align subgroup.topological_closure Subgroup.topologicalClosure

@[simp, to_additive]
theorem Subgroup.topological_closure_coe {s : Subgroup G} :
    (s.topologicalClosure : Set G) = closure s :=
  rfl
#align subgroup.topological_closure_coe Subgroup.topological_closure_coe

@[to_additive]
theorem Subgroup.le_topological_closure (s : Subgroup G) : s ≤ s.topologicalClosure :=
  subset_closure
#align subgroup.le_topological_closure Subgroup.le_topological_closure

@[to_additive]
theorem Subgroup.is_closed_topological_closure (s : Subgroup G) :
    IsClosed (s.topologicalClosure : Set G) := by convert is_closed_closure
#align subgroup.is_closed_topological_closure Subgroup.is_closed_topological_closure

@[to_additive]
theorem Subgroup.topological_closure_minimal (s : Subgroup G) {t : Subgroup G} (h : s ≤ t)
    (ht : IsClosed (t : Set G)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subgroup.topological_closure_minimal Subgroup.topological_closure_minimal

@[to_additive]
theorem DenseRange.topological_closure_map_subgroup [Group H] [TopologicalSpace H]
    [TopologicalGroup H] {f : G →* H} (hf : Continuous f) (hf' : DenseRange f) {s : Subgroup G}
    (hs : s.topologicalClosure = ⊤) : (s.map f).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [Subgroup.topological_closure_coe, Subgroup.coe_top, ← dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image hf hs
#align dense_range.topological_closure_map_subgroup DenseRange.topological_closure_map_subgroup

/-- The topological closure of a normal subgroup is normal.-/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
theorem Subgroup.is_normal_topological_closure {G : Type _} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] (N : Subgroup G) [N.Normal] : (Subgroup.topologicalClosure N).Normal :=
  { conj_mem := fun n hn g => by
      apply map_mem_closure (TopologicalGroup.continuous_conj g) hn
      exact fun m hm => Subgroup.Normal.conj_mem inferInstance m hm g }
#align subgroup.is_normal_topological_closure Subgroup.is_normal_topological_closure

@[to_additive]
theorem mul_mem_connected_component_one {G : Type _} [TopologicalSpace G] [MulOneClass G]
    [HasContinuousMul G] {g h : G} (hg : g ∈ connectedComponent (1 : G))
    (hh : h ∈ connectedComponent (1 : G)) : g * h ∈ connectedComponent (1 : G) := by
  rw [connected_component_eq hg]
  have hmul : g ∈ connectedComponent (g * h) := by
    apply Continuous.image_connected_component_subset (continuous_mul_left g)
    rw [← connected_component_eq hh]
    exact ⟨(1 : G), mem_connected_component, by simp only [mul_one]⟩
  simpa [← connected_component_eq hmul] using mem_connected_component
#align mul_mem_connected_component_one mul_mem_connected_component_one

@[to_additive]
theorem inv_mem_connected_component_one {G : Type _} [TopologicalSpace G] [Group G]
    [TopologicalGroup G] {g : G} (hg : g ∈ connectedComponent (1 : G)) :
    g⁻¹ ∈ connectedComponent (1 : G) := by 
  rw [← inv_one]
  exact
    Continuous.image_connected_component_subset continuous_inv _
      ((Set.mem_image _ _ _).mp ⟨g, hg, rfl⟩)
#align inv_mem_connected_component_one inv_mem_connected_component_one

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."]
def Subgroup.connectedComponentOfOne (G : Type _) [TopologicalSpace G] [Group G]
    [TopologicalGroup G] :
    Subgroup G where 
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connected_component
  mul_mem' g h hg hh := mul_mem_connected_component_one hg hh
  inv_mem' g hg := inv_mem_connected_component_one hg
#align subgroup.connected_component_of_one Subgroup.connectedComponentOfOne

/-- If a subgroup of a topological group is commutative, then so is its topological closure. -/
@[to_additive
      "If a subgroup of an additive topological group is commutative, then so is its\ntopological closure."]
def Subgroup.commGroupTopologicalClosure [T2Space G] (s : Subgroup G)
    (hs : ∀ x y : s, x * y = y * x) : CommGroup s.topologicalClosure :=
  { s.topologicalClosure.toGroup, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subgroup.comm_group_topological_closure Subgroup.commGroupTopologicalClosure

@[to_additive exists_nhds_half_neg]
theorem exists_nhds_split_inv {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v / w ∈ s := by
  have : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' s ∈ 𝓝 ((1, 1) : G × G) :=
    continuous_at_fst.mul continuous_at_snd.inv (by simpa)
  simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage] using
    this
#align exists_nhds_split_inv exists_nhds_split_inv

@[to_additive]
theorem nhds_translation_mul_inv (x : G) : comap (fun y : G => y * x⁻¹) (𝓝 1) = 𝓝 x :=
  ((Homeomorph.mulRight x⁻¹).comap_nhds_eq 1).trans <| show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x by simp
#align nhds_translation_mul_inv nhds_translation_mul_inv

@[simp, to_additive]
theorem map_mul_left_nhds (x y : G) : map ((· * ·) x) (𝓝 y) = 𝓝 (x * y) :=
  (Homeomorph.mulLeft x).map_nhds_eq y
#align map_mul_left_nhds map_mul_left_nhds

@[to_additive]
theorem map_mul_left_nhds_one (x : G) : map ((· * ·) x) (𝓝 1) = 𝓝 x := by simp
#align map_mul_left_nhds_one map_mul_left_nhds_one

/-- A monoid homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) from a
topological group to a topological monoid is continuous provided that it is continuous at one. See
also `uniform_continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive monoid homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) from an additive topological group to an additive topological monoid is\ncontinuous provided that it is continuous at zero. See also\n`uniform_continuous_of_continuous_at_zero`."]
theorem continuous_of_continuous_at_one {M hom : Type _} [MulOneClass M] [TopologicalSpace M]
    [HasContinuousMul M] [MonoidHomClass hom G M] (f : hom) (hf : ContinuousAt f 1) :
    Continuous f :=
  continuous_iff_continuous_at.2 fun x => by
    simpa only [ContinuousAt, ← map_mul_left_nhds_one x, tendsto_map'_iff, (· ∘ ·), map_mul,
      map_one, mul_one] using hf.tendsto.const_mul (f x)
#align continuous_of_continuous_at_one continuous_of_continuous_at_one

@[to_additive]
theorem TopologicalGroup.ext {G : Type _} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _)
    (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
  eq_of_nhds_eq_nhds fun x => by
    rw [← @nhds_translation_mul_inv G t _ _ x, ← @nhds_translation_mul_inv G t' _ _ x, ← h]
#align topological_group.ext TopologicalGroup.ext

@[to_additive]
theorem TopologicalGroup.ext_iff {G : Type _} [Group G] {t t' : TopologicalSpace G}
    (tg : @TopologicalGroup G t _) (tg' : @TopologicalGroup G t' _) :
    t = t' ↔ @nhds G t 1 = @nhds G t' 1 :=
  ⟨fun h => h ▸ rfl, tg.ext tg'⟩
#align topological_group.ext_iff TopologicalGroup.ext_iff

@[to_additive]
theorem TopologicalGroup.of_nhds_aux {G : Type _} [Group G] [TopologicalSpace G]
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x : G => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, map (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) ≤ 𝓝 1) :
    Continuous fun x : G => x⁻¹ := by
  rw [continuous_iff_continuous_at]
  rintro x₀
  have key :
    (fun x => (x₀ * x)⁻¹) = (fun x => x₀⁻¹ * x) ∘ (fun x => x₀ * x * x₀⁻¹) ∘ fun x => x⁻¹ := by
    ext <;> simp [mul_assoc]
  calc
    map (fun x => x⁻¹) (𝓝 x₀) = map (fun x => x⁻¹) ((map fun x => x₀ * x) <| 𝓝 1) := by rw [hleft]
    _ = map (fun x => (x₀ * x)⁻¹) (𝓝 1) := by rw [Filter.map_map]
    _ = map (((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) ∘ fun x => x⁻¹) (𝓝 1) := by rw [key]
    _ = map ((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) _ := by rw [← Filter.map_map]
    _ ≤ map ((fun x => x₀⁻¹ * x) ∘ fun x => x₀ * x * x₀⁻¹) (𝓝 1) := map_mono hinv
    _ = map (fun x => x₀⁻¹ * x) (map (fun x => x₀ * x * x₀⁻¹) (𝓝 1)) := Filter.map_map
    _ ≤ map (fun x => x₀⁻¹ * x) (𝓝 1) := map_mono (hconj x₀)
    _ = 𝓝 x₀⁻¹ := (hleft _).symm
    
#align topological_group.of_nhds_aux TopologicalGroup.of_nhds_aux

@[to_additive]
theorem TopologicalGroup.of_nhds_one' {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : TopologicalGroup G := by
  refine'
    { continuous_mul := (HasContinuousMul.of_nhds_one hmul hleft hright).continuous_mul
      continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft _ }
  intro x₀
  suffices map (fun x : G => x₀ * x * x₀⁻¹) (𝓝 1) = 𝓝 1 by simp [this, le_refl]
  rw [show (fun x => x₀ * x * x₀⁻¹) = (fun x => x₀ * x) ∘ fun x => x * x₀⁻¹ by
      ext
      simp [mul_assoc],
    ← Filter.map_map, ← hright, hleft x₀⁻¹, Filter.map_map]
  convert map_id
  ext
  simp
#align topological_group.of_nhds_one' TopologicalGroup.of_nhds_one'

@[to_additive]
theorem TopologicalGroup.of_nhds_one {G : Type u} [Group G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hconj : ∀ x₀ : G, Tendsto (fun x => x₀ * x * x₀⁻¹) (𝓝 1) (𝓝 1)) : TopologicalGroup G :=
  { continuous_mul := by 
      rw [continuous_iff_continuous_at]
      rintro ⟨x₀, y₀⟩
      have key :
        (fun p : G × G => x₀ * p.1 * (y₀ * p.2)) =
          (fun x => x₀ * y₀ * x) ∘ uncurry (· * ·) ∘ Prod.map (fun x => y₀⁻¹ * x * y₀) id :=
        by 
        ext
        simp [uncurry, Prod.map, mul_assoc]
      specialize hconj y₀⁻¹
      rw [inv_inv] at hconj
      calc
        map (fun p : G × G => p.1 * p.2) (𝓝 (x₀, y₀)) =
            map (fun p : G × G => p.1 * p.2) (𝓝 x₀ ×ᶠ 𝓝 y₀) :=
          by rw [nhds_prod_eq]
        _ = map (fun p : G × G => x₀ * p.1 * (y₀ * p.2)) (𝓝 1 ×ᶠ 𝓝 1) := by
          rw [hleft x₀, hleft y₀, prod_map_map_eq, Filter.map_map]
        _ =
            map (((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·)) ∘ Prod.map (fun x => y₀⁻¹ * x * y₀) id)
              (𝓝 1 ×ᶠ 𝓝 1) :=
          by rw [key]
        _ =
            map ((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·))
              (((map fun x => y₀⁻¹ * x * y₀) <| 𝓝 1) ×ᶠ 𝓝 1) :=
          by rw [← Filter.map_map, ← prod_map_map_eq', map_id]
        _ ≤ map ((fun x => x₀ * y₀ * x) ∘ uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1) :=
          map_mono (Filter.prod_mono hconj <| le_rfl)
        _ = map (fun x => x₀ * y₀ * x) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) := by
          rw [Filter.map_map]
        _ ≤ map (fun x => x₀ * y₀ * x) (𝓝 1) := map_mono hmul
        _ = 𝓝 (x₀ * y₀) := (hleft _).symm
        
    continuous_inv := TopologicalGroup.of_nhds_aux hinv hleft hconj }
#align topological_group.of_nhds_one TopologicalGroup.of_nhds_one

@[to_additive]
theorem TopologicalGroup.of_comm_of_nhds_one {G : Type u} [CommGroup G] [TopologicalSpace G]
    (hmul : Tendsto (uncurry ((· * ·) : G → G → G)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hinv : Tendsto (fun x : G => x⁻¹) (𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : G, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : TopologicalGroup G :=
  TopologicalGroup.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)
#align topological_group.of_comm_of_nhds_one TopologicalGroup.of_comm_of_nhds_one

end TopologicalGroup

section QuotientTopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] (N : Subgroup G) (n : N.Normal)

@[to_additive]
instance QuotientGroup.Quotient.topologicalSpace {G : Type _} [Group G] [TopologicalSpace G]
    (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  Quotient.topologicalSpace
#align quotient_group.quotient.topological_space QuotientGroup.Quotient.topologicalSpace

open QuotientGroup

@[to_additive]
theorem QuotientGroup.is_open_map_coe : IsOpenMap (coe : G → G ⧸ N) := by
  intro s s_op
  change IsOpen ((coe : G → G ⧸ N) ⁻¹' (coe '' s))
  rw [QuotientGroup.preimage_image_coe N s]
  exact is_open_Union fun n => (continuous_mul_right _).is_open_preimage s s_op
#align quotient_group.is_open_map_coe QuotientGroup.is_open_map_coe

@[to_additive]
instance topological_group_quotient [N.Normal] :
    TopologicalGroup
      (G ⧸
        N) where 
  continuous_mul := by
    have cont : Continuous ((coe : G → G ⧸ N) ∘ fun p : G × G => p.fst * p.snd) :=
      continuous_quot_mk.comp continuous_mul
    have quot : QuotientMap fun p : G × G => ((p.1 : G ⧸ N), (p.2 : G ⧸ N)) := by
      apply IsOpenMap.to_quotient_map
      · exact (QuotientGroup.is_open_map_coe N).Prod (QuotientGroup.is_open_map_coe N)
      · exact continuous_quot_mk.prod_map continuous_quot_mk
      · exact (surjective_quot_mk _).prod_map (surjective_quot_mk _)
    exact (QuotientMap.continuous_iff Quot).2 cont
  continuous_inv := by convert (@continuous_inv G _ _ _).quotient_map' _
#align topological_group_quotient topological_group_quotient

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
      "Neighborhoods in the quotient are precisely the map of neighborhoods in\nthe prequotient."]
theorem QuotientGroup.nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = map coe (𝓝 x) :=
  le_antisymm ((QuotientGroup.is_open_map_coe N).nhds_le x) continuous_quot_mk.ContinuousAt
#align quotient_group.nhds_eq QuotientGroup.nhds_eq

variable (G) [FirstCountableTopology G]

/-- Any first countable topological group has an antitone neighborhood basis `u : ℕ → set G` for
which `(u (n + 1)) ^ 2 ⊆ u n`. The existence of such a neighborhood basis is a key tool for
`quotient_group.complete_space` -/
@[to_additive
      "Any first countable topological additive group has an antitone neighborhood basis\n`u : ℕ → set G` for which `u (n + 1) + u (n + 1) ⊆ u n`. The existence of such a neighborhood basis\nis a key tool for `quotient_add_group.complete_space`"]
theorem TopologicalGroup.exists_antitone_basis_nhds_one :
    ∃ u : ℕ → Set G, (𝓝 1).HasAntitoneBasis u ∧ ∀ n, u (n + 1) * u (n + 1) ⊆ u n := by
  rcases(𝓝 (1 : G)).exists_antitone_basis with ⟨u, hu, u_anti⟩
  have :=
    ((hu.prod_nhds hu).tendsto_iff hu).mp
      (by simpa only [mul_one] using continuous_mul.tendsto ((1, 1) : G × G))
  simp only [and_self_iff, mem_prod, and_imp, Prod.forall, exists_true_left, Prod.exists,
    forall_true_left] at this
  have event_mul : ∀ n : ℕ, ∀ᶠ m in at_top, u m * u m ⊆ u n := by
    intro n
    rcases this n with ⟨j, k, h⟩
    refine' at_top_basis.eventually_iff.mpr ⟨max j k, True.intro, fun m hm => _⟩
    rintro - ⟨a, b, ha, hb, rfl⟩
    exact h a b (u_anti ((le_max_left _ _).trans hm) ha) (u_anti ((le_max_right _ _).trans hm) hb)
  obtain ⟨φ, -, hφ, φ_anti_basis⟩ := has_antitone_basis.subbasis_with_rel ⟨hu, u_anti⟩ event_mul
  exact ⟨u ∘ φ, φ_anti_basis, fun n => hφ n.lt_succ_self⟩
#align
  topological_group.exists_antitone_basis_nhds_one TopologicalGroup.exists_antitone_basis_nhds_one

include n

/-- In a first countable topological group `G` with normal subgroup `N`, `1 : G ⧸ N` has a
countable neighborhood basis. -/
@[to_additive
      "In a first countable topological additive group `G` with normal additive subgroup\n`N`, `0 : G ⧸ N` has a countable neighborhood basis."]
instance QuotientGroup.nhds_one_is_countably_generated : (𝓝 (1 : G ⧸ N)).IsCountablyGenerated :=
  (QuotientGroup.nhds_eq N 1).symm ▸ map.is_countably_generated _ _
#align quotient_group.nhds_one_is_countably_generated QuotientGroup.nhds_one_is_countably_generated

end QuotientTopologicalGroup

/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class HasContinuousSub (G : Type _) [TopologicalSpace G] [Sub G] : Prop where
  continuous_sub : Continuous fun p : G × G => p.1 - p.2
#align has_continuous_sub HasContinuousSub

/-- A typeclass saying that `λ p : G × G, p.1 / p.2` is a continuous function. This property
automatically holds for topological groups. Lemmas using this class have primes.
The unprimed version is for `group_with_zero`. -/
@[to_additive]
class HasContinuousDiv (G : Type _) [TopologicalSpace G] [Div G] : Prop where
  continuous_div' : Continuous fun p : G × G => p.1 / p.2
#align has_continuous_div HasContinuousDiv

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) TopologicalGroup.to_has_continuous_div [TopologicalSpace G] [Group G]
    [TopologicalGroup G] : HasContinuousDiv G :=
  ⟨by 
    simp only [div_eq_mul_inv]
    exact continuous_fst.mul continuous_snd.inv⟩
#align topological_group.to_has_continuous_div TopologicalGroup.to_has_continuous_div

export HasContinuousSub (continuous_sub)

export HasContinuousDiv (continuous_div')

section HasContinuousDiv

variable [TopologicalSpace G] [Div G] [HasContinuousDiv G]

@[to_additive sub]
theorem Filter.Tendsto.div' {f g : α → G} {l : Filter α} {a b : G} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f x / g x) l (𝓝 (a / b)) :=
  (continuous_div'.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.div' Filter.Tendsto.div'

@[to_additive const_sub]
theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (fun k : α => b / f k) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h
#align filter.tendsto.const_div' Filter.Tendsto.const_div'

@[to_additive sub_const]
theorem Filter.Tendsto.div_const' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (fun k : α => f k / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds
#align filter.tendsto.div_const' Filter.Tendsto.div_const'

variable [TopologicalSpace α] {f g : α → G} {s : Set α} {x : α}

@[continuity, to_additive sub]
theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x :=
  continuous_div'.comp (hf.prod_mk hg : _)
#align continuous.div' Continuous.div'

@[to_additive continuous_sub_left]
theorem continuous_div_left' (a : G) : Continuous fun b : G => a / b :=
  continuous_const.div' continuous_id
#align continuous_div_left' continuous_div_left'

@[to_additive continuous_sub_right]
theorem continuous_div_right' (a : G) : Continuous fun b : G => b / a :=
  continuous_id.div' continuous_const
#align continuous_div_right' continuous_div_right'

@[to_additive sub]
theorem ContinuousAt.div' {f g : α → G} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x / g x) x :=
  hf.div' hg
#align continuous_at.div' ContinuousAt.div'

@[to_additive sub]
theorem ContinuousWithinAt.div' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x / g x) s x :=
  hf.div' hg
#align continuous_within_at.div' ContinuousWithinAt.div'

@[to_additive sub]
theorem ContinuousOn.div' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x / g x) s := fun x hx => (hf x hx).div' (hg x hx)
#align continuous_on.div' ContinuousOn.div'

end HasContinuousDiv

section DivInTopologicalGroup

variable [Group G] [TopologicalSpace G] [TopologicalGroup G]

/-- A version of `homeomorph.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `homeomorph.add_left a (-b)` that is defeq to `a - b`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with
    continuous_to_fun := continuous_const.div' continuous_id
    continuous_inv_fun := continuous_inv.mul continuous_const }
#align homeomorph.div_left Homeomorph.divLeft

@[to_additive]
theorem is_open_map_div_left (a : G) : IsOpenMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsOpenMap
#align is_open_map_div_left is_open_map_div_left

@[to_additive]
theorem is_closed_map_div_left (a : G) : IsClosedMap ((· / ·) a) :=
  (Homeomorph.divLeft _).IsClosedMap
#align is_closed_map_div_left is_closed_map_div_left

/-- A version of `homeomorph.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `homeomorph.add_right (-a) b` that is defeq to `b - a`. ",
  simps (config := { simpRhs := true })]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with
    continuous_to_fun := continuous_id.div' continuous_const
    continuous_inv_fun := continuous_id.mul continuous_const }
#align homeomorph.div_right Homeomorph.divRight

@[to_additive]
theorem is_open_map_div_right (a : G) : IsOpenMap fun x => x / a :=
  (Homeomorph.divRight a).IsOpenMap
#align is_open_map_div_right is_open_map_div_right

@[to_additive]
theorem is_closed_map_div_right (a : G) : IsClosedMap fun x => x / a :=
  (Homeomorph.divRight a).IsClosedMap
#align is_closed_map_div_right is_closed_map_div_right

@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type _} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (fun n => u n / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : tendsto (fun n : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa using h.div' A⟩
#align tendsto_div_nhds_one_iff tendsto_div_nhds_one_iff

@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x
#align nhds_translation_div nhds_translation_div

end DivInTopologicalGroup

/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `submonoid.top_closure_mul_self_eq` in
`topology.algebra.monoid`.
-/


section HasContinuousConstSmul

variable [TopologicalSpace β] [Group α] [MulAction α β] [HasContinuousConstSmul α β] {s : Set α}
  {t : Set β}

@[to_additive]
theorem IsOpen.smul_left (ht : IsOpen t) : IsOpen (s • t) := by
  rw [← bUnion_smul_set]
  exact is_open_bUnion fun a _ => ht.smul _
#align is_open.smul_left IsOpen.smul_left

@[to_additive]
theorem subset_interior_smul_right : s • interior t ⊆ interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) is_open_interior.smul_left
#align subset_interior_smul_right subset_interior_smul_right

variable [TopologicalSpace α]

@[to_additive]
theorem subset_interior_smul : interior s • interior t ⊆ interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right
#align subset_interior_smul subset_interior_smul

end HasContinuousConstSmul

section HasContinuousConstSmul

variable [TopologicalSpace α] [Group α] [HasContinuousConstSmul α α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_left : IsOpen t → IsOpen (s * t) :=
  IsOpen.smul_left
#align is_open.mul_left IsOpen.mul_left

@[to_additive]
theorem subset_interior_mul_right : s * interior t ⊆ interior (s * t) :=
  subset_interior_smul_right
#align subset_interior_mul_right subset_interior_mul_right

@[to_additive]
theorem subset_interior_mul : interior s * interior t ⊆ interior (s * t) :=
  subset_interior_smul
#align subset_interior_mul subset_interior_mul

end HasContinuousConstSmul

section HasContinuousConstSmulOp

variable [TopologicalSpace α] [Group α] [HasContinuousConstSmul αᵐᵒᵖ α] {s t : Set α}

@[to_additive]
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← bUnion_op_smul_set]
  exact is_open_bUnion fun a _ => hs.smul _
#align is_open.mul_right IsOpen.mul_right

@[to_additive]
theorem subset_interior_mul_left : interior s * t ⊆ interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) is_open_interior.mul_right
#align subset_interior_mul_left subset_interior_mul_left

@[to_additive]
theorem subset_interior_mul' : interior s * interior t ⊆ interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left
#align subset_interior_mul' subset_interior_mul'

end HasContinuousConstSmulOp

section TopologicalGroup

variable [TopologicalSpace α] [Group α] [TopologicalGroup α] {s t : Set α}

@[to_additive]
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← Union_div_left_image]
  exact is_open_bUnion fun a ha => is_open_map_div_left a t ht
#align is_open.div_left IsOpen.div_left

@[to_additive]
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← Union_div_right_image]
  exact is_open_bUnion fun a ha => is_open_map_div_right a s hs
#align is_open.div_right IsOpen.div_right

@[to_additive]
theorem subset_interior_div_left : interior s / t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) is_open_interior.div_right
#align subset_interior_div_left subset_interior_div_left

@[to_additive]
theorem subset_interior_div_right : s / interior t ⊆ interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) is_open_interior.div_left
#align subset_interior_div_right subset_interior_div_right

@[to_additive]
theorem subset_interior_div : interior s / interior t ⊆ interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left
#align subset_interior_div subset_interior_div

@[to_additive]
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set α) : s * closure t = s * t := by
  refine' (mul_subset_iff.2 fun a ha b hb => _).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b ∈ s⁻¹ * {a * b} := ⟨a⁻¹, a * b, Set.inv_mem_inv.2 ha, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, d, hc, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, _, hc, hcs, inv_mul_cancel_left _ _⟩
#align is_open.mul_closure IsOpen.mul_closure

@[to_additive]
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set α) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t), mul_inv_rev, inv_closure, ht.inv.mul_closure, mul_inv_rev, inv_inv,
    inv_inv]
#align is_open.closure_mul IsOpen.closure_mul

@[to_additive]
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set α) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]
#align is_open.div_closure IsOpen.div_closure

@[to_additive]
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set α) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]
#align is_open.closure_div IsOpen.closure_div

end TopologicalGroup

/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`z] [] -/
/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class AddGroupWithZeroNhd (G : Type u) extends AddCommGroup G where
  z : Filter G
  zero_Z : pure 0 ≤ Z
  sub_Z : Tendsto (fun p : G × G => p.1 - p.2) (Z ×ᶠ Z) Z
#align add_group_with_zero_nhd AddGroupWithZeroNhd

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [TopologicalGroup G]

@[to_additive]
theorem TopologicalGroup.t1_space (h : @IsClosed G _ {1}) : T1Space G :=
  ⟨fun x => by 
    convert is_closed_map_mul_right x _ h
    simp⟩
#align topological_group.t1_space TopologicalGroup.t1_space

@[to_additive]
instance (priority := 100) TopologicalGroup.regularSpace : RegularSpace G := by
  refine' RegularSpace.ofExistsMemNhdsIsClosedSubset fun a s hs => _
  have : tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff, image_prod] at hUV
  refine' ⟨closure U, mem_of_superset hU subset_closure, is_closed_closure, _⟩
  calc
    closure U ⊆ closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := is_open_interior.closure_mul U
    _ ⊆ U * V := mul_subset_mul_left interior_subset
    _ ⊆ s := hUV
    
#align topological_group.regular_space TopologicalGroup.regularSpace

@[to_additive]
theorem TopologicalGroup.t3Space [T1Space G] : T3Space G :=
  ⟨⟩
#align topological_group.t3_space TopologicalGroup.t3Space

@[to_additive]
theorem TopologicalGroup.t2Space [T1Space G] : T2Space G := by
  haveI := TopologicalGroup.t3Space G
  infer_instance
#align topological_group.t2_space TopologicalGroup.t2Space

variable {G} (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)]

@[to_additive]
instance Subgroup.t3QuotientOfIsClosed (S : Subgroup G) [Subgroup.Normal S] [IsClosed (S : Set G)] :
    T3Space (G ⧸ S) := by
  suffices T1Space (G ⧸ S) by exact @TopologicalGroup.t3Space _ _ _ _ this
  have hS : IsClosed (S : Set G) := inferInstance
  rw [← QuotientGroup.ker_mk S] at hS
  exact TopologicalGroup.t1_space (G ⧸ S) (quotient_map_quotient_mk.is_closed_preimage.mp hS)
#align subgroup.t3_quotient_of_is_closed Subgroup.t3QuotientOfIsClosed

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the left, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`discrete_topology`.) -/
@[to_additive
      "A subgroup `S` of an additive topological group `G` acts on `G` properly\ndiscontinuously on the left, if it is discrete in the sense that `S ∩ K` is finite for all compact\n`K`. (See also `discrete_topology`."]
theorem Subgroup.properly_discontinuous_smul_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.Subtype cofinite (cocompact G)) : ProperlyDiscontinuousSmul S G :=
  { finite_disjoint_inter_image := by 
      intro K L hK hL
      have H : Set.Finite _ := hS ((hL.prod hK).image continuous_div').compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simpa only [image_smul, mem_image, Prod.exists] using Set.smul_inter_ne_empty_iff' }
#align
  subgroup.properly_discontinuous_smul_of_tendsto_cofinite Subgroup.properly_discontinuous_smul_of_tendsto_cofinite

attribute [local semireducible] MulOpposite

/-- A subgroup `S` of a topological group `G` acts on `G` properly discontinuously on the right, if
it is discrete in the sense that `S ∩ K` is finite for all compact `K`. (See also
`discrete_topology`.)

If `G` is Hausdorff, this can be combined with `t2_space_of_properly_discontinuous_smul_of_t2_space`
to show that the quotient group `G ⧸ S` is Hausdorff. -/
@[to_additive
      "A subgroup `S` of an additive topological group `G` acts on `G` properly\ndiscontinuously on the right, if it is discrete in the sense that `S ∩ K` is finite for all compact\n`K`. (See also `discrete_topology`.)\n\nIf `G` is Hausdorff, this can be combined with `t2_space_of_properly_discontinuous_vadd_of_t2_space`\nto show that the quotient group `G ⧸ S` is Hausdorff."]
theorem Subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite (S : Subgroup G)
    (hS : Tendsto S.Subtype cofinite (cocompact G)) : ProperlyDiscontinuousSmul S.opposite G :=
  { finite_disjoint_inter_image := by 
      intro K L hK hL
      have : Continuous fun p : G × G => (p.1⁻¹, p.2) := continuous_inv.prod_map continuous_id
      have H : Set.Finite _ :=
        hS ((hK.prod hL).image (continuous_mul.comp this)).compl_mem_cocompact
      rw [preimage_compl, compl_compl] at H
      convert H
      ext x
      simpa only [image_smul, mem_image, Prod.exists] using Set.op_smul_inter_ne_empty_iff }
#align
  subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite Subgroup.properly_discontinuous_smul_opposite_of_tendsto_cofinite

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/


variable [TopologicalSpace G] [Group G] [TopologicalGroup G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `K * V ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `K + V ⊆ U`."]
theorem compact_open_separated_mul_right {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), K * V ⊆ U := by
  apply hK.induction_on
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left (V.inter_subset_left W)).trans hV')
        ((mul_subset_mul_left (V.inter_subset_right W)).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 1) by simpa using hU.mem_nhds (hKU hx))
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhds_within_of_mem_nhds ht, s, hs, h⟩
#align compact_open_separated_mul_right compact_open_separated_mul_right

open MulOpposite

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `V * K ⊆ U`. -/
@[to_additive
      "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of\n`0` such that `V + K ⊆ U`."]
theorem compact_open_separated_mul_left {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ V ∈ 𝓝 (1 : G), V * K ⊆ U := by
  rcases compact_open_separated_mul_right (hK.image continuous_op) (op_homeomorph.is_open_map U hU)
      (image_subset op hKU) with
    ⟨V, hV : V ∈ 𝓝 (op (1 : G)), hV' : op '' K * V ⊆ op '' U⟩
  refine' ⟨op ⁻¹' V, continuous_op.continuous_at hV, _⟩
  rwa [← image_preimage_eq V op_surjective, ← image_op_mul, image_subset_iff,
    preimage_image_eq _ op_injective] at hV'
#align compact_open_separated_mul_left compact_open_separated_mul_left

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive
      "A compact set is covered by finitely many left additive translates of a set\n  with non-empty interior."]
theorem compact_covered_by_mul_left_translates {K V : Set G} (hK : IsCompact K)
    (hV : (interior V).Nonempty) : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V := by
  obtain ⟨t, ht⟩ : ∃ t : Finset G, K ⊆ ⋃ x ∈ t, interior ((· * ·) x ⁻¹' V) := by
    refine'
      hK.elim_finite_subcover (fun x => interior <| (· * ·) x ⁻¹' V) (fun x => is_open_interior) _
    cases' hV with g₀ hg₀
    refine' fun g hg => mem_Union.2 ⟨g₀ * g⁻¹, _⟩
    refine' preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) _
    rwa [mem_preimage, inv_mul_cancel_right]
  exact ⟨t, subset.trans ht <| Union₂_mono fun g hg => interior_subset⟩
#align compact_covered_by_mul_left_translates compact_covered_by_mul_left_translates

/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[to_additive SeparableLocallyCompactAddGroup.sigmaCompactSpace
      "Every locally\ncompact separable topological group is σ-compact.\nNote: this is not true if we drop the topological group hypothesis."]
instance (priority := 100) SeparableLocallyCompactGroup.sigmaCompactSpace [SeparableSpace G]
    [LocallyCompactSpace G] : SigmaCompactSpace G := by
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G)
  refine' ⟨⟨fun n => (fun x => x * dense_seq G n) ⁻¹' L, _, _⟩⟩
  · intro n
    exact (Homeomorph.mulRight _).is_compact_preimage.mpr hLc
  · refine' Union_eq_univ_iff.2 fun x => _
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (fun y => x * y) ⁻¹' L).Nonempty := by
      rw [← (Homeomorph.mulLeft x).apply_symm_apply 1] at hL1
      exact
        (dense_range_dense_seq G).inter_nhds_nonempty
          ((Homeomorph.mulLeft x).Continuous.ContinuousAt <| hL1)
    exact ⟨n, hn⟩
#align
  separable_locally_compact_group.sigma_compact_space SeparableLocallyCompactGroup.sigmaCompactSpace

/-- Given two compact sets in a noncompact topological group, there is a translate of the second
one that is disjoint from the first one. -/
@[to_additive
      "Given two compact sets in a noncompact additive topological group, there is a\ntranslate of the second one that is disjoint from the first one."]
theorem exists_disjoint_smul_of_is_compact [NoncompactSpace G] {K L : Set G} (hK : IsCompact K)
    (hL : IsCompact L) : ∃ g : G, Disjoint K (g • L) := by
  have A : ¬K * L⁻¹ = univ := (hK.mul hL.inv).ne_univ
  obtain ⟨g, hg⟩ : ∃ g, g ∉ K * L⁻¹ := by 
    contrapose! A
    exact eq_univ_iff_forall.2 A
  refine' ⟨g, _⟩
  apply disjoint_left.2 fun a ha h'a => hg _
  rcases h'a with ⟨b, bL, rfl⟩
  refine' ⟨g * b, b⁻¹, ha, by simpa only [Set.mem_inv, inv_inv] using bL, _⟩
  simp only [smul_eq_mul, mul_inv_cancel_right]
#align exists_disjoint_smul_of_is_compact exists_disjoint_smul_of_is_compact

/-- In a locally compact group, any neighborhood of the identity contains a compact closed
neighborhood of the identity, even without separation assumptions on the space. -/
@[to_additive
      "In a locally compact additive group, any neighborhood of the identity contains a\ncompact closed neighborhood of the identity, even without separation assumptions on the space."]
theorem local_is_compact_is_closed_nhds_of_group [LocallyCompactSpace G] {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) : ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ K ⊆ U ∧ (1 : G) ∈ interior K :=
  by 
  obtain ⟨L, Lint, LU, Lcomp⟩ : ∃ (L : Set G)(H : L ∈ 𝓝 (1 : G)), L ⊆ U ∧ IsCompact L
  exact local_compact_nhds hU
  obtain ⟨V, Vnhds, hV⟩ : ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ L := by
    have : (fun p : G × G => p.1 * p.2) ⁻¹' L ∈ 𝓝 ((1, 1) : G × G) := by
      refine' continuous_at_fst.mul continuous_at_snd _
      simpa only [mul_one] using Lint
    simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage]
  have VL : closure V ⊆ L :=
    calc
      closure V = {(1 : G)} * closure V := by simp only [singleton_mul, one_mul, image_id']
      _ ⊆ interior V * closure V :=
        mul_subset_mul_right
          (by simpa only [singleton_subset_iff] using mem_interior_iff_mem_nhds.2 Vnhds)
      _ = interior V * V := is_open_interior.mul_closure _
      _ ⊆ V * V := mul_subset_mul_right interior_subset
      _ ⊆ L := by 
        rintro x ⟨y, z, yv, zv, rfl⟩
        exact hV _ yv _ zv
      
  exact
    ⟨closure V, is_compact_of_is_closed_subset Lcomp is_closed_closure VL, is_closed_closure,
      VL.trans LU, interior_mono subset_closure (mem_interior_iff_mem_nhds.2 Vnhds)⟩
#align local_is_compact_is_closed_nhds_of_group local_is_compact_is_closed_nhds_of_group

end

section

variable [TopologicalSpace G] [CommGroup G] [TopologicalGroup G]

@[to_additive]
theorem nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
  filter_eq <|
    Set.ext fun s => by
      rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ←
        nhds_translation_mul_inv (x * y)]
      constructor
      · rintro ⟨t, ht, ts⟩
        rcases exists_nhds_one_split ht with ⟨V, V1, h⟩
        refine'
          ⟨(fun a => a * x⁻¹) ⁻¹' V, (fun a => a * y⁻¹) ⁻¹' V, ⟨V, V1, subset.refl _⟩,
            ⟨V, V1, subset.refl _⟩, _⟩
        rintro a ⟨v, w, v_mem, w_mem, rfl⟩
        apply ts
        simpa [mul_comm, mul_assoc, mul_left_comm] using h (v * x⁻¹) v_mem (w * y⁻¹) w_mem
      · rintro ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩
        refine' ⟨b ∩ d, inter_mem hb hd, fun v => _⟩
        simp only [preimage_subset_iff, mul_inv_rev, mem_preimage] at *
        rintro ⟨vb, vd⟩
        refine' ac ⟨v * y⁻¹, y, _, _, _⟩
        · rw [← mul_assoc _ _ _] at vb
          exact ba _ vb
        · apply dc y
          rw [mul_right_inv]
          exact mem_of_mem_nhds hd
        · simp only [inv_mul_cancel_right]
#align nhds_mul nhds_mul

/-- On a topological group, `𝓝 : G → filter G` can be promoted to a `mul_hom`. -/
@[to_additive
      "On an additive topological group, `𝓝 : G → filter G` can be promoted to an\n`add_hom`.",
  simps]
def nhdsMulHom : G →ₙ* Filter G where 
  toFun := 𝓝
  map_mul' _ _ := nhds_mul _ _
#align nhds_mul_hom nhdsMulHom

end

end FilterMul

instance {G} [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    TopologicalAddGroup (Additive G) where continuous_neg := @continuous_inv G _ _ _

instance {G} [TopologicalSpace G] [AddGroup G] [TopologicalAddGroup G] :
    TopologicalGroup (Multiplicative G) where continuous_inv := @continuous_neg G _ _ _

section Quotient

variable [Group G] [TopologicalSpace G] [TopologicalGroup G] {Γ : Subgroup G}

@[to_additive]
instance QuotientGroup.has_continuous_const_smul :
    HasContinuousConstSmul G
      (G ⧸
        Γ) where continuous_const_smul g := by
    convert ((@continuous_const _ _ _ _ g).mul continuous_id).quotient_map' _
#align quotient_group.has_continuous_const_smul QuotientGroup.has_continuous_const_smul

@[to_additive]
theorem QuotientGroup.continuous_smul₁ (x : G ⧸ Γ) : Continuous fun g : G => g • x := by
  induction x using QuotientGroup.induction_on
  exact continuous_quotient_mk.comp (continuous_mul_right x)
#align quotient_group.continuous_smul₁ QuotientGroup.continuous_smul₁

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
      "The quotient of a second countable additive topological group by a subgroup is second\ncountable."]
instance QuotientGroup.second_countable_topology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ Γ) :=
  HasContinuousConstSmul.second_countable_topology
#align quotient_group.second_countable_topology QuotientGroup.second_countable_topology

end Quotient

namespace Units

open MulOpposite (continuous_op continuous_unop)

variable [Monoid α] [TopologicalSpace α] [Monoid β] [TopologicalSpace β]

@[to_additive]
instance [HasContinuousMul α] :
    TopologicalGroup
      αˣ where continuous_inv := Units.continuous_iff.2 <| ⟨continuous_coe_inv, continuous_coe⟩

/-- The topological group isomorphism between the units of a product of two monoids, and the product
of the units of each monoid. -/
@[to_additive
      "The topological group isomorphism between the additive units of a product of two\nadditive monoids, and the product of the additive units of each additive monoid."]
def Homeomorph.prodUnits :
    (α × β)ˣ ≃ₜ
      αˣ ×
        βˣ where 
  continuous_to_fun :=
    (continuous_fst.units_map (MonoidHom.fst α β)).prod_mk
      (continuous_snd.units_map (MonoidHom.snd α β))
  continuous_inv_fun :=
    Units.continuous_iff.2
      ⟨continuous_coe.fst'.prod_mk continuous_coe.snd',
        continuous_coe_inv.fst'.prod_mk continuous_coe_inv.snd'⟩
  toEquiv := MulEquiv.prodUnits.toEquiv
#align units.homeomorph.prod_units Units.Homeomorph.prodUnits

end Units

section LatticeOps

variable {ι : Sort _} [Group G]

@[to_additive]
theorem topological_group_Inf {ts : Set (TopologicalSpace G)}
    (h : ∀ t ∈ ts, @TopologicalGroup G t _) : @TopologicalGroup G (inf ts) _ :=
  { to_has_continuous_inv :=
      (@has_continuous_inv_Inf _ _ _) fun t ht =>
        @TopologicalGroup.to_has_continuous_inv G t _ <| h t ht
    to_has_continuous_mul :=
      (@has_continuous_mul_Inf _ _ _) fun t ht =>
        @TopologicalGroup.to_has_continuous_mul G t _ <| h t ht }
#align topological_group_Inf topological_group_Inf

@[to_additive]
theorem topological_group_infi {ts' : ι → TopologicalSpace G}
    (h' : ∀ i, @TopologicalGroup G (ts' i) _) : @TopologicalGroup G (⨅ i, ts' i) _ := by
  rw [← Inf_range]
  exact topological_group_Inf (set.forall_range_iff.mpr h')
#align topological_group_infi topological_group_infi

@[to_additive]
theorem topological_group_inf {t₁ t₂ : TopologicalSpace G} (h₁ : @TopologicalGroup G t₁ _)
    (h₂ : @TopologicalGroup G t₂ _) : @TopologicalGroup G (t₁ ⊓ t₂) _ := by
  rw [inf_eq_infi]
  refine' topological_group_infi fun b => _
  cases b <;> assumption
#align topological_group_inf topological_group_inf

end LatticeOps

/-!
### Lattice of group topologies

We define a type class `group_topology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → group_topology β`.

The additive version `add_group_topology α` and corresponding results are provided as well.
-/


/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
structure GroupTopology (α : Type u) [Group α] extends TopologicalSpace α, TopologicalGroup α :
  Type u
#align group_topology GroupTopology

/-- An additive group topology on an additive group `α` is a topology for which addition and
  negation are continuous. -/
structure AddGroupTopology (α : Type u) [AddGroup α] extends TopologicalSpace α,
  TopologicalAddGroup α : Type u
#align add_group_topology AddGroupTopology

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_add` suitable for dot notation."]
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.to_topological_space
    Continuous fun p : α × α => p.1 * p.2 :=
  by 
  letI := g.to_topological_space
  haveI := g.to_topological_group
  exact continuous_mul
#align group_topology.continuous_mul' GroupTopology.continuous_mul'

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive "A version of the global `continuous_neg` suitable for dot notation."]
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.to_topological_space
    Continuous (Inv.inv : α → α) :=
  by 
  letI := g.to_topological_space
  haveI := g.to_topological_group
  exact continuous_inv
#align group_topology.continuous_inv' GroupTopology.continuous_inv'

@[to_additive]
theorem to_topological_space_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) := fun f g h =>
  by 
  cases f
  cases g
  congr
#align group_topology.to_topological_space_injective GroupTopology.to_topological_space_injective

@[ext, to_additive]
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  to_topological_space_injective <| topological_space_eq h
#align group_topology.ext' GroupTopology.ext'

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
      "The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`\nis also open in `t` (`t` is finer than `s`)."]
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace to_topological_space_injective

@[simp, to_additive]
theorem to_topological_space_le {x y : GroupTopology α} :
    x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl
#align group_topology.to_topological_space_le GroupTopology.to_topological_space_le

@[to_additive]
instance : Top (GroupTopology α) :=
  ⟨{  toTopologicalSpace := ⊤
      continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[simp, to_additive]
theorem to_topological_space_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl
#align group_topology.to_topological_space_top GroupTopology.to_topological_space_top

@[to_additive]
instance : Bot (GroupTopology α) :=
  ⟨{  toTopologicalSpace := ⊥
      continuous_mul := by continuity
      continuous_inv := continuous_bot }⟩

@[simp, to_additive]
theorem to_topological_space_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl
#align group_topology.to_topological_space_bot GroupTopology.to_topological_space_bot

@[to_additive]
instance : BoundedOrder (GroupTopology α) where 
  top := ⊤
  le_top x := show x.toTopologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le x := show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
instance : HasInf (GroupTopology α) where inf x y := ⟨x.1 ⊓ y.1, topological_group_inf x.2 y.2⟩

@[simp, to_additive]
theorem to_topological_space_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl
#align group_topology.to_topological_space_inf GroupTopology.to_topological_space_inf

@[to_additive]
instance : SemilatticeInf (GroupTopology α) :=
  to_topological_space_injective.SemilatticeInf _ to_topological_space_inf

@[to_additive]
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

/-- Infimum of a collection of group topologies. -/
@[to_additive "Infimum of a collection of additive group topologies"]
instance :
    HasInf
      (GroupTopology
        α) where inf S :=
    ⟨inf (to_topological_space '' S), topological_group_Inf <| ball_image_iff.2 fun t ht => t.2⟩

@[simp, to_additive]
theorem to_topological_space_Inf (s : Set (GroupTopology α)) :
    (inf s).toTopologicalSpace = inf (to_topological_space '' s) :=
  rfl
#align group_topology.to_topological_space_Inf GroupTopology.to_topological_space_Inf

@[simp, to_additive]
theorem to_topological_space_infi {ι} (s : ι → GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg inf (range_comp _ _).symm
#align group_topology.to_topological_space_infi GroupTopology.to_topological_space_infi

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive
      "Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and\n`⊤` the indiscrete topology.\n\nThe infimum of a collection of group topologies is the topology generated by all their open sets\n(which is a group topology).\n\nThe supremum of two group topologies `s` and `t` is the infimum of the family of all group\ntopologies contained in the intersection of `s` and `t`."]
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { GroupTopology.hasInf, GroupTopology.partialOrder with
    Inf_le := fun S a haS => to_topological_space_le.1 <| Inf_le ⟨a, haS, rfl⟩
    le_Inf := by 
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupTopology α) :=
  { GroupTopology.boundedOrder, GroupTopology.semilatticeInf,
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥ }

/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
      "Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`\nis the finest topology such that `f` is continuous and `β` is a topological additive group."]
def coinduced {α β : Type _} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  inf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align group_topology.coinduced GroupTopology.coinduced

@[to_additive]
theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Group β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f := by
  rw [continuous_Inf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'
#align group_topology.coinduced_continuous GroupTopology.coinduced_continuous

end GroupTopology

