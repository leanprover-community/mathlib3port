/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.Data.Setoid.Basic
import Mathbin.Data.Fintype.Card

/-!
# Basic properties of group actions
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open_locale BigOperators Pointwise

open Function

namespace MulAction

variable (α) [Monoidₓ α] [MulAction α β]

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def Orbit (b : β) :=
  Set.Range fun x : α => x • b

variable {α}

@[to_additive]
theorem mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ Orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
  Iff.rfl

@[simp, to_additive]
theorem mem_orbit (b : β) (x : α) : x • b ∈ Orbit α b :=
  ⟨x, rfl⟩

@[simp, to_additive]
theorem mem_orbit_self (b : β) : b ∈ Orbit α b :=
  ⟨1, by
    simp [MulAction.one_smul]⟩

@[to_additive]
theorem orbit_nonempty (b : β) : Set.Nonempty (Orbit α b) :=
  Set.range_nonempty _

@[to_additive]
theorem maps_to_smul_orbit (a : α) (b : β) : Set.MapsTo ((· • ·) a) (Orbit α b) (Orbit α b) :=
  Set.range_subset_iff.2 fun a' => ⟨a * a', mul_smul _ _ _⟩

@[to_additive]
theorem smul_orbit_subset (a : α) (b : β) : a • Orbit α b ⊆ Orbit α b :=
  (maps_to_smul_orbit a b).image_subset

@[to_additive]
theorem orbit_smul_subset (a : α) (b : β) : Orbit α (a • b) ⊆ Orbit α b :=
  Set.range_subset_iff.2 fun a' => mul_smul a' a b ▸ mem_orbit _ _

@[to_additive]
instance {b : β} : MulAction α (Orbit α b) where
  smul := fun a => (maps_to_smul_orbit a b).restrict _ _ _
  one_smul := fun a => Subtype.ext (one_smul α a)
  mul_smul := fun a a' b' => Subtype.ext (mul_smul a a' b')

@[simp, to_additive]
theorem Orbit.coe_smul {b : β} {a : α} {b' : Orbit α b} : ↑(a • b') = a • (b' : β) :=
  rfl

variable (α) (β)

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def FixedPoints : Set β :=
  { b : β | ∀ x : α, x • b = b }

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixed_by g` is the subfield of elements fixed by `g`."]
def FixedBy (g : α) : Set β :=
  { x | g • x = x }

@[to_additive]
theorem fixed_eq_Inter_fixed_by : FixedPoints α β = ⋂ g : α, FixedBy α β g :=
  Set.ext fun x => ⟨fun hx => Set.mem_Inter.2 fun g => hx g, fun hx g => (Set.mem_Inter.1 hx g : _)⟩

variable {α} (β)

@[simp, to_additive]
theorem mem_fixed_points {b : β} : b ∈ FixedPoints α β ↔ ∀ x : α, x • b = b :=
  Iff.rfl

@[simp, to_additive]
theorem mem_fixed_by {g : α} {b : β} : b ∈ FixedBy α β g ↔ g • b = b :=
  Iff.rfl

@[to_additive]
theorem mem_fixed_points' {b : β} : b ∈ FixedPoints α β ↔ ∀ b', b' ∈ Orbit α b → b' = b :=
  ⟨fun h b h₁ =>
    let ⟨x, hx⟩ := mem_orbit_iff.1 h₁
    hx ▸ h x,
    fun h b => h _ (mem_orbit _ _)⟩

variable (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def Stabilizer.submonoid (b : β) : Submonoid α where
  Carrier := { a | a • b = b }
  one_mem' := one_smul _ b
  mul_mem' := fun hb : a' • b = b =>
    show (a * a') • b = b by
      rw [← smul_smul, hb, ha]

@[simp, to_additive]
theorem mem_stabilizer_submonoid_iff {b : β} {a : α} : a ∈ Stabilizer.submonoid α b ↔ a • b = b :=
  Iff.rfl

@[to_additive]
theorem orbit_eq_univ [IsPretransitive α β] (x : β) : Orbit α x = Set.Univ :=
  (surjective_smul α x).range_eq

end MulAction

namespace MulAction

variable (α)

variable [Groupₓ α] [MulAction α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.\nAn additive subgroup."]
def stabilizer (b : β) : Subgroup α :=
  { Stabilizer.submonoid α b with
    inv_mem' := fun ha : a • b = b =>
      show a⁻¹ • b = b by
        rw [inv_smul_eq_iff, ha] }

variable {α} {β}

@[simp, to_additive]
theorem mem_stabilizer_iff {b : β} {a : α} : a ∈ stabilizer α b ↔ a • b = b :=
  Iff.rfl

@[simp, to_additive]
theorem smul_orbit (a : α) (b : β) : a • Orbit α b = Orbit α b :=
  (smul_orbit_subset a b).antisymm <|
    calc
      Orbit α b = a • a⁻¹ • Orbit α b := (smul_inv_smul _ _).symm
      _ ⊆ a • Orbit α b := Set.image_subset _ (smul_orbit_subset _ _)
      

@[simp, to_additive]
theorem orbit_smul (a : α) (b : β) : Orbit α (a • b) = Orbit α b :=
  (orbit_smul_subset a b).antisymm <|
    calc
      Orbit α b = Orbit α (a⁻¹ • a • b) := by
        rw [inv_smul_smul]
      _ ⊆ Orbit α (a • b) := orbit_smul_subset _ _
      

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (x : β) : IsPretransitive α (Orbit α x) :=
  ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    use b * a⁻¹
    ext1
    simp [mul_smul]⟩

@[to_additive]
theorem orbit_eq_iff {a b : β} : Orbit α a = Orbit α b ↔ a ∈ Orbit α b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨c, hc⟩ => hc ▸ orbit_smul _ _⟩

@[to_additive]
theorem mem_fixed_points_iff_card_orbit_eq_one {a : β} [Fintype (Orbit α a)] :
    a ∈ FixedPoints α β ↔ Fintype.card (Orbit α a) = 1 := by
  rw [Fintype.card_eq_one_iff, mem_fixed_points]
  constructor
  · exact fun h =>
      ⟨⟨a, mem_orbit_self _⟩, fun ⟨b, ⟨x, hx⟩⟩ =>
        Subtype.eq <| by
          simp [h x, hx.symm]⟩
    
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc x • a = z := Subtype.mk.injₓ (hz₁ ⟨x • a, mem_orbit _ _⟩)_ = a :=
        (Subtype.mk.injₓ (hz₁ ⟨a, mem_orbit_self _⟩)).symm
    

variable (α) {β}

@[to_additive]
theorem mem_orbit_smul (g : α) (a : β) : a ∈ Orbit α (g • a) := by
  simp only [orbit_smul, mem_orbit_self]

@[to_additive]
theorem smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ Orbit α (h • a) := by
  simp only [orbit_smul, mem_orbit]

variable (α) (β)

/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbitRel : Setoidₓ β where
  R := fun a b => a ∈ Orbit α b
  iseqv :=
    ⟨mem_orbit_self, fun a b => by
      simp [orbit_eq_iff.symm, eq_comm], fun a b => by
      simp (config := { contextual := true })[orbit_eq_iff.symm, eq_comm]⟩

attribute [local instance] orbit_rel

variable {α} {β}

/-- When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `α`.
-/
@[to_additive]
theorem quotient_preimage_image_eq_union_mul (U : Set β) :
    Quotientₓ.mk ⁻¹' (Quotientₓ.mk '' U) = ⋃ a : α, (· • ·) a '' U := by
  set f : β → Quotientₓ (MulAction.orbitRel α β) := Quotientₓ.mk
  ext
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨a, rfl⟩ := Quotientₓ.exact hxy
    rw [Set.mem_Union]
    exact ⟨a⁻¹, a • x, hy, inv_smul_smul a x⟩
    
  · intro hx
    rw [Set.mem_Union] at hx
    obtain ⟨a, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image_iff_bex]
    refine'
      ⟨a⁻¹ • x, _, by
        simp only [Quotientₓ.eq] <;> use a⁻¹⟩
    rw [← hu₂]
    convert hu₁
    simp only [inv_smul_smul]
    

@[to_additive]
theorem image_inter_image_iff (U V : Set β) :
    Quotientₓ.mk '' U ∩ Quotientₓ.mk '' V = ∅ ↔ ∀, ∀ x ∈ U, ∀, ∀ a : α, a • x ∉ V := by
  set f : β → Quotientₓ (MulAction.orbitRel α β) := Quotientₓ.mk
  rw [Set.eq_empty_iff_forall_not_mem]
  constructor
  · intro h x x_in_U a a_in_V
    refine' h (f (a • x)) ⟨⟨x, x_in_U, _⟩, ⟨a • x, a_in_V, rfl⟩⟩
    rw [Quotientₓ.eq]
    use a⁻¹
    simp
    
  · rintro h x ⟨⟨y, hy₁, hy₂⟩, ⟨z, hz₁, hz₂⟩⟩
    obtain ⟨a, ha⟩ := Quotientₓ.exact (hz₂.trans hy₂.symm)
    apply h y hy₁ a
    convert hz₁
    

variable (α) (β)

-- mathport name: «exprΩ»
local notation "Ω" => Quotientₓ <| orbitRel α β

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
This version works with any right inverse to `quotient.mk'` in order to stay computable. In most
cases you'll want to use `quotient.out'`, so we provide `mul_action.self_equiv_sigma_orbits` as
a special case. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction. This version works with any right inverse to `quotient.mk'` in order to stay computable.\nIn most cases you'll want to use `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits`\nas a special case."]
def selfEquivSigmaOrbits' {φ : Ω → β} (hφ : RightInverse φ Quotientₓ.mk') : β ≃ Σω : Ω, Orbit α (φ ω) :=
  calc
    β ≃ Σω : Ω, { b // Quotientₓ.mk' b = ω } := (Equivₓ.sigmaPreimageEquiv Quotientₓ.mk').symm
    _ ≃ Σω : Ω, Orbit α (φ ω) :=
      Equivₓ.sigmaCongrRight fun ω =>
        Equivₓ.subtypeEquivRight fun x => by
          rw [← hφ ω, Quotientₓ.eq', hφ ω]
          rfl
    

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction."]
noncomputable def selfEquivSigmaOrbits : β ≃ Σω : Ω, Orbit α ω.out' :=
  selfEquivSigmaOrbits' α β Quotientₓ.out_eq'

variable {α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g • x) = (stabilizer α x).map (MulAut.conj g).toMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_invₓ, one_smul, ←
    mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃* stabilizer α y :=
  let g : α := Classical.some h
  have hg : g • y = x := Classical.some_spec h
  have this : stabilizer α x = (stabilizer α y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer α y).symm

end MulAction

namespace AddAction

variable [AddGroupₓ α] [AddAction α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g +ᵥ x) = (stabilizer α x).map (AddAut.conj g).toAddMonoidHom := by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd, add_left_negₓ, zero_vadd, ←
    mem_stabilizer_iff, AddSubgroup.mem_map_equiv, AddAut.conj_symm_apply]

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃+ stabilizer α y :=
  let g : α := Classical.some h
  have hg : g +ᵥ y = x := Classical.some_spec h
  have this : stabilizer α x = (stabilizer α y).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer α y).symm

end AddAction

namespace MulAction

variable [Groupₓ α] [MulAction α β]

open QuotientGroup

/-- Action on left cosets. -/
@[to_additive "Action on left cosets."]
def mulLeftCosets (H : Subgroup α) (x : α) (y : α ⧸ H) : α ⧸ H :=
  Quotientₓ.liftOn' y (fun y => QuotientGroup.mk ((x : α) * y)) fun hab : _ ∈ H =>
    QuotientGroup.eq.2
      (by
        rwa [mul_inv_rev, ← mul_assoc, mul_assoc a⁻¹, inv_mul_selfₓ, mul_oneₓ])

@[to_additive]
instance quotient (H : Subgroup α) : MulAction α (α ⧸ H) where
  smul := mulLeftCosets H
  one_smul := fun a =>
    Quotientₓ.induction_on' a fun a =>
      QuotientGroup.eq.2
        (by
          simp [Subgroup.one_mem])
  mul_smul := fun x y a =>
    Quotientₓ.induction_on' a fun a =>
      QuotientGroup.eq.2
        (by
          simp [mul_inv_rev, Subgroup.one_mem, mul_assoc])

@[simp, to_additive]
theorem quotient.smul_mk (H : Subgroup α) (a x : α) : (a • QuotientGroup.mk x : α ⧸ H) = QuotientGroup.mk (a * x) :=
  rfl

@[simp, to_additive]
theorem quotient.smul_coe (H : Subgroup α) (a x : α) : (a • x : α ⧸ H) = ↑(a * x) :=
  rfl

@[to_additive]
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup α) : MulAction I (α ⧸ H) :=
  MulAction.compHom (α ⧸ H) (Subgroup.subtype I)

variable (α) {β} (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def ofQuotientStabilizer (g : α ⧸ MulAction.stabilizer α x) : β :=
  (Quotientₓ.liftOn' g (· • x)) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_argₓ _ H.symm
      _ = g2 • x := by
        rw [smul_smul, mul_inv_cancel_left]
      

@[simp, to_additive]
theorem of_quotient_stabilizer_mk (g : α) : ofQuotientStabilizer α x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive]
theorem of_quotient_stabilizer_mem_orbit g : ofQuotientStabilizer α x g ∈ Orbit α x :=
  (Quotientₓ.induction_on' g) fun g => ⟨g, rfl⟩

@[to_additive]
theorem of_quotient_stabilizer_smul (g : α) (g' : α ⧸ MulAction.stabilizer α x) :
    ofQuotientStabilizer α x (g • g') = g • ofQuotientStabilizer α x g' :=
  (Quotientₓ.induction_on' g') fun _ => mul_smul _ _ _

@[to_additive]
theorem injective_of_quotient_stabilizer : Function.Injective (ofQuotientStabilizer α x) := fun y₁ y₂ =>
  (Quotientₓ.induction_on₂' y₁ y₂) fun H : g₁ • x = g₂ • x =>
    Quotientₓ.sound' <|
      show (g₁⁻¹ * g₂) • x = x by
        rw [mul_smul, ← H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitEquivQuotientStabilizer (b : β) : Orbit α b ≃ α ⧸ stabilizer α b :=
  Equivₓ.symm <|
    Equivₓ.ofBijective (fun g => ⟨ofQuotientStabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
      ⟨fun x y hxy =>
        injective_of_quotient_stabilizer α b
          (by
            convert congr_argₓ Subtype.val hxy),
        fun ⟨b, ⟨g, hgb⟩⟩ => ⟨g, Subtype.eq hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbitProdStabilizerEquivGroup (b : β) : Orbit α b × stabilizer α b ≃ α :=
  (Equivₓ.prodCongr (orbitEquivQuotientStabilizer α _) (Equivₓ.refl _)).trans
    Subgroup.groupEquivQuotientTimesSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α] [Fintype <| Orbit α b]
    [Fintype <| stabilizer α b] : Fintype.card (Orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbit_prod_stabilizer_equiv_group α b)]

@[simp, to_additive]
theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
    ((orbitEquivQuotientStabilizer α b).symm a : β) = a • b :=
  rfl

@[simp, to_additive]
theorem stabilizer_quotient {G} [Groupₓ G] (H : Subgroup G) : MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [QuotientGroup.eq]

variable (β)

-- mathport name: «exprΩ»
local notation "Ω" => Quotientₓ <| orbitRel α β

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we
provide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/
@[to_additive
      "**Class formula** : given `G` an additive group acting on `X` and `φ` a function\nmapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the\nrelation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection\nbetween `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want\n`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`\nas a special case. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → β} (hφ : LeftInverse Quotientₓ.mk' φ) :
    β ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) :=
  calc
    β ≃ Σω : Ω, Orbit α (φ ω) := selfEquivSigmaOrbits' α β hφ
    _ ≃ Σω : Ω, α ⧸ stabilizer α (φ ω) := Equivₓ.sigmaCongrRight fun ω => orbitEquivQuotientStabilizer α (φ ω)
    

/-- **Class formula** for a finite group acting on a finite type. See
`mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`quotient.out'`. -/
@[to_additive
      "**Class formula** for a finite group acting on a finite type. See\n`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using\n`quotient.out'`."]
theorem card_eq_sum_card_group_div_card_stabilizer' [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] {φ : Ω → β} (hφ : LeftInverse Quotientₓ.mk' φ) :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α (φ ω)) := by
  classical
  have : ∀ ω : Ω, Fintype.card α / Fintype.card ↥(stabilizer α (φ ω)) = Fintype.card (α ⧸ stabilizer α (φ ω)) := by
    intro ω
    rw [Fintype.card_congr (@Subgroup.groupEquivQuotientTimesSubgroup α _ (stabilizer α <| φ ω)), Fintype.card_prod,
      Nat.mul_div_cancelₓ]
    exact
      fintype.card_pos_iff.mpr
        (by
          infer_instance)
  simp_rw [this, ← Fintype.card_sigma, Fintype.card_congr (self_equiv_sigma_orbits_quotient_stabilizer' α β hφ)]

/-- **Class formula**. This is a special case of
`mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/
@[to_additive
      "**Class formula**. This is a special case of\n`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. "]
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : β ≃ Σω : Ω, α ⧸ stabilizer α ω.out' :=
  selfEquivSigmaOrbitsQuotientStabilizer' α β Quotientₓ.out_eq'

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive "**Class formula** for a finite group acting on a finite type."]
theorem card_eq_sum_card_group_div_card_stabilizer [Fintype α] [Fintype β] [Fintype Ω]
    [∀ b : β, Fintype <| stabilizer α b] :
    Fintype.card β = ∑ ω : Ω, Fintype.card α / Fintype.card (stabilizer α ω.out') :=
  card_eq_sum_card_group_div_card_stabilizer' α β Quotientₓ.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/
@[to_additive
      "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all\n`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting\non `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. "]
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σa : α, FixedBy α β a) ≃ Ω × α :=
  calc
    (Σa : α, FixedBy α β a) ≃ { ab : α × β // ab.1 • ab.2 = ab.2 } := (Equivₓ.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : β × α // ba.2 • ba.1 = ba.1 } := (Equivₓ.prodComm α β).subtypeEquiv fun ab => Iff.rfl
    _ ≃ Σb : β, stabilizer α b := Equivₓ.subtypeProdEquivSigmaSubtype fun a => a ∈ stabilizer α b
    _ ≃ Σωb : Σω : Ω, Orbit α ω.out', stabilizer α (ωb.2 : β) := (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σω : Ω, Σb : Orbit α ω.out', stabilizer α (b : β) :=
      Equivₓ.sigmaAssoc fun b : Orbit α ω.out' => stabilizer α (b : β)
    _ ≃ Σω : Ω, Σb : Orbit α ω.out', stabilizer α ω.out' :=
      Equivₓ.sigmaCongrRight fun ω =>
        Equivₓ.sigmaCongrRight fun ⟨b, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σω : Ω, Orbit α ω.out' × stabilizer α ω.out' := Equivₓ.sigmaCongrRight fun ω => Equivₓ.sigmaEquivProd _ _
    _ ≃ Σω : Ω, α := Equivₓ.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out'
    _ ≃ Ω × α := Equivₓ.sigmaEquivProd Ω α
    

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[to_additive
      "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,\nthe average number of elements fixed by each `g ∈ G` is the number of orbits. "]
theorem sum_card_fixed_by_eq_card_orbits_mul_card_group [Fintype α] [∀ a, Fintype <| FixedBy α β a] [Fintype Ω] :
    (∑ a : α, Fintype.card (FixedBy α β a)) = Fintype.card Ω * Fintype.card α := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma, Fintype.card_congr (sigma_fixed_by_equiv_orbits_prod_group α β)]

@[to_additive]
instance is_pretransitive_quotient G [Groupₓ G] (H : Subgroup G) : IsPretransitive G (G ⧸ H) where
  exists_smul_eq := by
    rintro ⟨x⟩ ⟨y⟩
    refine' ⟨y * x⁻¹, quotient_group.eq.mpr _⟩
    simp only [H.one_mem, mul_left_invₓ, inv_mul_cancel_right]

end MulAction

section

variable [Monoidₓ α] [AddMonoidₓ β] [DistribMulAction α β]

theorem List.smul_sum {r : α} {l : List β} : r • l.Sum = (l.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_list_sum l

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type _} [Monoidₓ M] [Ringₓ R] [DistribMulAction M R] (k : M)
    (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) : a = b := by
  rw [← sub_eq_zero]
  refine' h _ _
  rw [smul_sub, h', sub_self]

end

section

variable [Monoidₓ α] [Monoidₓ β] [MulDistribMulAction α β]

theorem List.smul_prod {r : α} {l : List β} : r • l.Prod = (l.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_list_prod l

end

section

variable [Monoidₓ α] [AddCommMonoidₓ β] [DistribMulAction α β]

theorem Multiset.smul_sum {r : α} {s : Multiset β} : r • s.Sum = (s.map ((· • ·) r)).Sum :=
  (DistribMulAction.toAddMonoidHom β r).map_multiset_sum s

theorem Finset.smul_sum {r : α} {f : γ → β} {s : Finset γ} : (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  (DistribMulAction.toAddMonoidHom β r).map_sum f s

end

section

variable [Monoidₓ α] [CommMonoidₓ β] [MulDistribMulAction α β]

theorem Multiset.smul_prod {r : α} {s : Multiset β} : r • s.Prod = (s.map ((· • ·) r)).Prod :=
  (MulDistribMulAction.toMonoidHom β r).map_multiset_prod s

theorem Finset.smul_prod {r : α} {f : γ → β} {s : Finset γ} : (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  (MulDistribMulAction.toMonoidHom β r).map_prod f s

end

namespace Subgroup

variable {G : Type _} [Groupₓ G] (H : Subgroup G)

theorem normal_core_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker := by
  refine'
    le_antisymmₓ
      (fun g hg =>
        Equivₓ.Perm.ext fun q =>
          QuotientGroup.induction_on q fun g' => (MulAction.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))
      (subgroup.normal_le_normal_core.mpr fun g hg => _)
  · rw [mul_inv_rev, ← inv_invₓ g', inv_invₓ]
    exact H.normal_core.inv_mem hg g'⁻¹
    
  · rw [← H.inv_mem_iff, ← mul_oneₓ g⁻¹, ← QuotientGroup.eq, ← mul_oneₓ g]
    exact (MulAction.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G))
    

noncomputable instance fintypeQuotientNormalCore [Fintype (G ⧸ H)] : Fintype (G ⧸ H.normalCore) := by
  rw [H.normal_core_eq_ker]
  classical
  exact Fintype.ofEquiv _ (QuotientGroup.quotientKerEquivRange _).symm.toEquiv

end Subgroup

