/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.ring
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Prod
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.Subring.Basic
import Mathbin.Topology.Algebra.Group.Basic

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `subring.topological_closure`/`subsemiring.topological_closure`: the topological closure of a
  `subring`/`subsemiring` is itself a `sub(semi)ring`.
- `prod.topological_semiring`/`prod.topological_ring`: The product of two topological
  (semi)rings.
- `pi.topological_semiring`/`pi.topological_ring`: The arbitrary product of topological
  (semi)rings.
- `ideal.closure`: The closure of an ideal is an ideal.
- `topological_ring_quotient`: The quotient of a topological semiring by an ideal is a
  topological ring.

-/


open Classical Set Filter TopologicalSpace Function

open Classical TopologicalSpace Filter

section TopologicalSemiring

variable (α : Type _)

/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `topological_semiring` class should *only* be instantiated in the presence of a
`non_unital_non_assoc_semiring` instance; if there is an instance of `non_unital_non_assoc_ring`,
then `topological_ring` should be used. Note: in the presence of `non_assoc_ring`, these classes are
mathematically equivalent (see `topological_semiring.has_continuous_neg_of_mul` or
`topological_semiring.to_topological_ring`).  -/
class TopologicalSemiring [TopologicalSpace α] [NonUnitalNonAssocSemiring α] extends
  HasContinuousAdd α, HasContinuousMul α : Prop
#align topological_semiring TopologicalSemiring

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`topological_semiring.has_continuous_neg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class TopologicalRing [TopologicalSpace α] [NonUnitalNonAssocRing α] extends TopologicalSemiring α,
  HasContinuousNeg α : Prop
#align topological_ring TopologicalRing

variable {α}

/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
theorem TopologicalSemiring.has_continuous_neg_of_mul [TopologicalSpace α] [NonAssocRing α]
    [HasContinuousMul α] : HasContinuousNeg α :=
  {
    continuous_neg := by
      simpa using (continuous_const.mul continuous_id : Continuous fun x : α => -1 * x) }
#align topological_semiring.has_continuous_neg_of_mul TopologicalSemiring.has_continuous_neg_of_mul

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
theorem TopologicalSemiring.to_topological_ring [TopologicalSpace α] [NonAssocRing α]
    (h : TopologicalSemiring α) : TopologicalRing α :=
  { h,
    (haveI := h.to_has_continuous_mul
      TopologicalSemiring.has_continuous_neg_of_mul :
      HasContinuousNeg α) with }
#align topological_semiring.to_topological_ring TopologicalSemiring.to_topological_ring

-- See note [lower instance priority]
instance (priority := 100) TopologicalRing.to_topological_add_group [NonUnitalNonAssocRing α]
    [TopologicalSpace α] [TopologicalRing α] : TopologicalAddGroup α :=
  { TopologicalRing.to_topological_semiring.to_has_continuous_add,
    TopologicalRing.to_has_continuous_neg with }
#align topological_ring.to_topological_add_group TopologicalRing.to_topological_add_group

instance (priority := 50) DiscreteTopology.topological_semiring [TopologicalSpace α]
    [NonUnitalNonAssocSemiring α] [DiscreteTopology α] : TopologicalSemiring α :=
  ⟨⟩
#align discrete_topology.topological_semiring DiscreteTopology.topological_semiring

instance (priority := 50) DiscreteTopology.topological_ring [TopologicalSpace α]
    [NonUnitalNonAssocRing α] [DiscreteTopology α] : TopologicalRing α :=
  ⟨⟩
#align discrete_topology.topological_ring DiscreteTopology.topological_ring

section

variable [TopologicalSpace α] [Semiring α] [TopologicalSemiring α]

namespace Subsemiring

instance (S : Subsemiring α) : TopologicalSemiring S :=
  { S.toSubmonoid.HasContinuousMul, S.toAddSubmonoid.HasContinuousAdd with }

end Subsemiring

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := closure (s : Set α) }
#align subsemiring.topological_closure Subsemiring.topologicalClosure

@[simp]
theorem Subsemiring.topological_closure_coe (s : Subsemiring α) :
    (s.topologicalClosure : Set α) = closure (s : Set α) :=
  rfl
#align subsemiring.topological_closure_coe Subsemiring.topological_closure_coe

theorem Subsemiring.le_topological_closure (s : Subsemiring α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subsemiring.le_topological_closure Subsemiring.le_topological_closure

theorem Subsemiring.is_closed_topological_closure (s : Subsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := by convert is_closed_closure
#align subsemiring.is_closed_topological_closure Subsemiring.is_closed_topological_closure

theorem Subsemiring.topological_closure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subsemiring.topological_closure_minimal Subsemiring.topological_closure_minimal

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure. -/
def Subsemiring.commSemiringTopologicalClosure [T2Space α] (s : Subsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subsemiring.comm_semiring_topological_closure Subsemiring.commSemiringTopologicalClosure

end

section

variable {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [TopologicalSemiring α]
    [TopologicalSemiring β] : TopologicalSemiring (α × β) where

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [NonUnitalNonAssocRing α] [NonUnitalNonAssocRing β] [TopologicalRing α]
    [TopologicalRing β] : TopologicalRing (α × β) where

end

instance {β : Type _} {C : β → Type _} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    TopologicalSemiring (∀ b, C b) where

instance {β : Type _} {C : β → Type _} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocRing (C b)] [∀ b, TopologicalRing (C b)] : TopologicalRing (∀ b, C b)
    where

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [HasContinuousAdd α] :
    HasContinuousAdd αᵐᵒᵖ
    where continuous_add :=
    continuous_induced_rng.2 <|
      (@continuous_add α _ _ _).comp (continuous_unop.prod_map continuous_unop)

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵐᵒᵖ where

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [HasContinuousNeg α] : HasContinuousNeg αᵐᵒᵖ
    where continuous_neg :=
    continuous_induced_rng.2 <| (@continuous_neg α _ _ _).comp continuous_unop

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] : TopologicalRing αᵐᵒᵖ
    where

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [HasContinuousMul α] :
    HasContinuousMul αᵃᵒᵖ
    where continuous_mul := by
    convert
      continuous_op.comp <|
        (@continuous_mul α _ _ _).comp <| continuous_unop.prod_map continuous_unop

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵃᵒᵖ where

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] : TopologicalRing αᵃᵒᵖ
    where

end AddOpposite

section

variable {R : Type _} [NonUnitalNonAssocRing R] [TopologicalSpace R]

theorem TopologicalRing.of_add_group_of_nhds_zero [TopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : TopologicalRing R :=
  by
  refine' { ‹TopologicalAddGroup R› with .. }
  have hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0) := by simp
  have hadd : tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) (𝓝 0) :=
    by
    rw [← nhds_prod_eq]
    convert continuous_add.tendsto ((0 : R), (0 : R))
    rw [zero_add]
  rw [continuous_iff_continuous_at]
  rintro ⟨x₀, y₀⟩
  rw [ContinuousAt, nhds_prod_eq, hleft x₀, hleft y₀, hleft (x₀ * y₀), Filter.prod_map_map_eq,
    tendsto_map'_iff]
  suffices
    tendsto
      ((fun x : R => x + x₀ * y₀) ∘
        (fun p : R × R => p.1 + p.2) ∘ fun p : R × R => (p.1 * y₀ + x₀ * p.2, p.1 * p.2))
      (𝓝 0 ×ᶠ 𝓝 0) ((map fun x : R => x + x₀ * y₀) <| 𝓝 0)
    by
    convert this using 1
    · ext
      simp only [comp_app, mul_add, add_mul]
      abel
    · simp only [add_comm]
  refine' tendsto_map.comp (hadd.comp (tendsto.prod_mk _ hmul))
  exact hadd.comp (((hmul_right y₀).comp tendsto_fst).prod_mk ((hmul_left x₀).comp tendsto_snd))
#align topological_ring.of_add_group_of_nhds_zero TopologicalRing.of_add_group_of_nhds_zero

theorem TopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : TopologicalRing R :=
  haveI := TopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  TopologicalRing.of_add_group_of_nhds_zero hmul hmul_left hmul_right
#align topological_ring.of_nhds_zero TopologicalRing.of_nhds_zero

end

variable {α} [TopologicalSpace α]

section

variable [NonUnitalNonAssocRing α] [TopologicalRing α]

/-- In a topological semiring, the left-multiplication `add_monoid_hom` is continuous. -/
theorem mul_left_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id
#align mul_left_continuous mul_left_continuous

/-- In a topological semiring, the right-multiplication `add_monoid_hom` is continuous. -/
theorem mul_right_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const
#align mul_right_continuous mul_right_continuous

end

variable [Ring α] [TopologicalRing α]

namespace Subring

instance (S : Subring α) : TopologicalRing S :=
  TopologicalSemiring.to_topological_ring S.toSubsemiring.TopologicalSemiring

end Subring

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := closure (S : Set α) }
#align subring.topological_closure Subring.topologicalClosure

theorem Subring.le_topological_closure (s : Subring α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subring.le_topological_closure Subring.le_topological_closure

theorem Subring.is_closed_topological_closure (s : Subring α) :
    IsClosed (s.topologicalClosure : Set α) := by convert is_closed_closure
#align subring.is_closed_topological_closure Subring.is_closed_topological_closure

theorem Subring.topological_closure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subring.topological_closure_minimal Subring.topological_closure_minimal

/-- If a subring of a topological ring is commutative, then so is its topological closure. -/
def Subring.commRingTopologicalClosure [T2Space α] (s : Subring α) (hs : ∀ x y : s, x * y = y * x) :
    CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subring.comm_ring_topological_closure Subring.commRingTopologicalClosure

end TopologicalSemiring

section TopologicalRing

variable {α : Type _} [TopologicalSpace α] [Ring α] [TopologicalRing α]

/-- The closure of an ideal in a topological ring as an ideal. -/
def Ideal.closure (S : Ideal α) : Ideal α :=
  {
    AddSubmonoid.topologicalClosure
      S.toAddSubmonoid with
    carrier := closure S
    smul_mem' := fun c x hx =>
      map_mem_closure (mul_left_continuous _) hx fun a => S.mul_mem_left c }
#align ideal.closure Ideal.closure

@[simp]
theorem Ideal.coe_closure (S : Ideal α) : (S.closure : Set α) = closure S :=
  rfl
#align ideal.coe_closure Ideal.coe_closure

@[simp]
theorem Ideal.closure_eq_of_is_closed (S : Ideal α) [hS : IsClosed (S : Set α)] : S.closure = S :=
  Ideal.ext <| Set.ext_iff.mp hS.closure_eq
#align ideal.closure_eq_of_is_closed Ideal.closure_eq_of_is_closed

end TopologicalRing

section TopologicalRing

variable {α : Type _} [TopologicalSpace α] [CommRing α] (N : Ideal α)

open Ideal.Quotient

instance topologicalRingQuotientTopology : TopologicalSpace (α ⧸ N) :=
  show TopologicalSpace (Quotient _) by infer_instance
#align topological_ring_quotient_topology topologicalRingQuotientTopology

-- note for the reader: in the following, `mk` is `ideal.quotient.mk`, the canonical map `R → R/I`.
variable [TopologicalRing α]

theorem QuotientRing.is_open_map_coe : IsOpenMap (mk N) :=
  by
  intro s s_op
  change IsOpen (mk N ⁻¹' (mk N '' s))
  rw [quotient_ring_saturate]
  exact is_open_Union fun ⟨n, _⟩ => is_open_map_add_left n s s_op
#align quotient_ring.is_open_map_coe QuotientRing.is_open_map_coe

theorem QuotientRing.quotient_map_coe_coe : QuotientMap fun p : α × α => (mk N p.1, mk N p.2) :=
  IsOpenMap.to_quotient_map ((QuotientRing.is_open_map_coe N).Prod (QuotientRing.is_open_map_coe N))
    ((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
    (by rintro ⟨⟨x⟩, ⟨y⟩⟩ <;> exact ⟨(x, y), rfl⟩)
#align quotient_ring.quotient_map_coe_coe QuotientRing.quotient_map_coe_coe

instance topological_ring_quotient : TopologicalRing (α ⧸ N) :=
  TopologicalSemiring.to_topological_ring
    { continuous_add :=
        have cont : Continuous (mk N ∘ fun p : α × α => p.fst + p.snd) :=
          continuous_quot_mk.comp continuous_add
        (QuotientMap.continuous_iff (QuotientRing.quotient_map_coe_coe N)).mpr cont
      continuous_mul :=
        have cont : Continuous (mk N ∘ fun p : α × α => p.fst * p.snd) :=
          continuous_quot_mk.comp continuous_mul
        (QuotientMap.continuous_iff (QuotientRing.quotient_map_coe_coe N)).mpr cont }
#align topological_ring_quotient topological_ring_quotient

end TopologicalRing

/-!
### Lattice of ring topologies
We define a type class `ring_topology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → ring_topology β`. -/


universe u v

/-- A ring topology on a ring `α` is a topology for which addition, negation and multiplication
are continuous. -/
@[ext]
structure RingTopology (α : Type u) [Ring α] extends TopologicalSpace α, TopologicalRing α : Type u
#align ring_topology RingTopology

namespace RingTopology

variable {α : Type _} [Ring α]

instance inhabited {α : Type u} [Ring α] : Inhabited (RingTopology α) :=
  ⟨{  toTopologicalSpace := ⊤
      continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩
#align ring_topology.inhabited RingTopology.inhabited

@[ext]
theorem ext' {f g : RingTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  by
  ext
  rw [h]
#align ring_topology.ext' RingTopology.ext'

/-- The ordering on ring topologies on the ring `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrder (RingTopology α) :=
  PartialOrder.lift RingTopology.toTopologicalSpace <| ext

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

private def def_Inf (S : Set (RingTopology α)) : RingTopology α :=
  let Inf_S' := infₛ (to_topological_space '' S)
  { toTopologicalSpace := Inf_S'
    continuous_add := by
      apply continuous_Inf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      have h_continuous_id := @Continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_add h_continuous_id
    continuous_mul := by
      apply continuous_Inf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      have h_continuous_id := @Continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_mul h_continuous_id
    continuous_neg := by
      apply continuous_Inf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_Inf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_neg h }
#align ring_topology.def_Inf ring_topology.def_Inf

/-- Ring topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance : CompleteSemilatticeInf (RingTopology α) :=
  { RingTopology.partialOrder with
    inf := defInf
    Inf_le := fun S a haS =>
      by
      apply topological_space.complete_lattice.Inf_le
      use a, ⟨haS, rfl⟩
    le_Inf := by
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

instance : CompleteLattice (RingTopology α) :=
  completeLatticeOfCompleteSemilatticeInf _

/-- Given `f : α → β` and a topology on `α`, the coinduced ring topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological ring. -/
def coinduced {α β : Type _} [t : TopologicalSpace α] [Ring β] (f : α → β) : RingTopology β :=
  infₛ { b : RingTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align ring_topology.coinduced RingTopology.coinduced

theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Ring β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f :=
  by
  rw [continuous_iff_coinduced_le]
  refine' le_infₛ _
  rintro _ ⟨t', ht', rfl⟩
  exact ht'
#align ring_topology.coinduced_continuous RingTopology.coinduced_continuous

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology (t : RingTopology α) : AddGroupTopology α
    where
  toTopologicalSpace := t.toTopologicalSpace
  to_topological_add_group :=
    @TopologicalRing.to_topological_add_group _ _ t.toTopologicalSpace t.to_topological_ring
#align ring_topology.to_add_group_topology RingTopology.toAddGroupTopology

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology α) (AddGroupTopology α)
    where
  toFun t := t.toAddGroupTopology
  inj' := by
    intro t₁ t₂ h_eq
    dsimp only at h_eq
    ext
    have h_t₁ : t₁.to_topological_space = t₁.to_add_group_topology.to_topological_space := rfl
    rw [h_t₁, h_eq]
    rfl
  map_rel_iff' := by
    intro t₁ t₂
    rw [embedding.coe_fn_mk]
    have h_le : t₁ ≤ t₂ ↔ t₁.to_topological_space ≤ t₂.to_topological_space := by rfl
    rw [h_le]
    rfl
#align
  ring_topology.to_add_group_topology.order_embedding RingTopology.toAddGroupTopology.orderEmbedding

end RingTopology

section AbsoluteValue

/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
def AbsoluteValue.comp {R S T : Type _} [Semiring T] [Semiring R] [OrderedSemiring S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S
    where
  toFun := v ∘ f
  map_mul' := by simp only [Function.comp_apply, map_mul, eq_self_iff_true, forall_const]
  nonneg' := by simp only [v.nonneg, forall_const]
  eq_zero' := by simp only [map_eq_zero_iff f hf, v.eq_zero, forall_const, iff_self_iff]
  add_le' := by simp only [Function.comp_apply, map_add, v.add_le, forall_const]
#align absolute_value.comp AbsoluteValue.comp

end AbsoluteValue

