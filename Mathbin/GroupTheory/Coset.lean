import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

## TODO

Add `to_additive` to `preimage_mk_equiv_subgroup_times_set`.
-/


open Set Function

variable{α : Type _}

/-- The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[toAdditive LeftAddCoset "The left coset `a+s` for an element `a : α`\nand a subset `s : set α`"]
def LeftCoset [Mul α] (a : α) (s : Set α) : Set α :=
  (fun x => a*x) '' s

/-- The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[toAdditive RightAddCoset "The right coset `s+a` for an element `a : α`\nand a subset `s : set α`"]
def RightCoset [Mul α] (s : Set α) (a : α) : Set α :=
  (fun x => x*a) '' s

localized [Coset] infixl:70 " *l " => LeftCoset

localized [Coset] infixl:70 " +l " => LeftAddCoset

localized [Coset] infixl:70 " *r " => RightCoset

localized [Coset] infixl:70 " +r " => RightAddCoset

section CosetMul

variable[Mul α]

@[toAdditive mem_left_add_coset]
theorem mem_left_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : (a*x) ∈ a *l s :=
  mem_image_of_mem (fun b : α => a*b) hxS

@[toAdditive mem_right_add_coset]
theorem mem_right_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : (x*a) ∈ s *r a :=
  mem_image_of_mem (fun b : α => b*a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[toAdditive LeftAddCosetEquivalence "Equality of two left cosets `a + s` and `b + s`."]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a *l s = b *l s

@[toAdditive left_add_coset_equivalence_rel]
theorem left_coset_equivalence_rel (s : Set α) : Equivalenceₓ (LeftCosetEquivalence s) :=
  mk_equivalence (LeftCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[toAdditive RightAddCosetEquivalence "Equality of two right cosets `s + a` and `s + b`."]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  s *r a = s *r b

@[toAdditive right_add_coset_equivalence_rel]
theorem right_coset_equivalence_rel (s : Set α) : Equivalenceₓ (RightCosetEquivalence s) :=
  mk_equivalence (RightCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

end CosetMul

section CosetSemigroup

variable[Semigroupₓ α]

@[simp, toAdditive left_add_coset_assoc]
theorem left_coset_assoc (s : Set α) (a b : α) : a *l (b *l s) = (a*b) *l s :=
  by 
    simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

@[simp, toAdditive right_add_coset_assoc]
theorem right_coset_assoc (s : Set α) (a b : α) : s *r a *r b = s *r a*b :=
  by 
    simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

@[toAdditive left_add_coset_right_add_coset]
theorem left_coset_right_coset (s : Set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
  by 
    simp [LeftCoset, RightCoset, (image_comp _ _ _).symm, Function.comp, mul_assocₓ]

end CosetSemigroup

section CosetMonoid

variable[Monoidₓ α](s : Set α)

@[simp, toAdditive zero_left_add_coset]
theorem one_left_coset : 1 *l s = s :=
  Set.ext$
    by 
      simp [LeftCoset]

@[simp, toAdditive right_add_coset_zero]
theorem right_coset_one : s *r 1 = s :=
  Set.ext$
    by 
      simp [RightCoset]

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable[Monoidₓ α](s : Submonoid α)

@[toAdditive mem_own_left_add_coset]
theorem mem_own_left_coset (a : α) : a ∈ a *l s :=
  suffices (a*1) ∈ a *l s by 
    simpa 
  mem_left_coset a (one_mem s)

@[toAdditive mem_own_right_add_coset]
theorem mem_own_right_coset (a : α) : a ∈ (s : Set α) *r a :=
  suffices (1*a) ∈ (s : Set α) *r a by 
    simpa 
  mem_right_coset a (one_mem s)

@[toAdditive mem_left_add_coset_left_add_coset]
theorem mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
  by 
    rw [←SetLike.mem_coe, ←ha] <;> exact mem_own_left_coset s a

@[toAdditive mem_right_add_coset_right_add_coset]
theorem mem_right_coset_right_coset {a : α} (ha : (s : Set α) *r a = s) : a ∈ s :=
  by 
    rw [←SetLike.mem_coe, ←ha] <;> exact mem_own_right_coset s a

end CosetSubmonoid

section CosetGroup

variable[Groupₓ α]{s : Set α}{x : α}

@[toAdditive mem_left_add_coset_iff]
theorem mem_left_coset_iff (a : α) : x ∈ a *l s ↔ (a⁻¹*x) ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ =>
      by 
        simp [Eq.symm, hb])
    fun h =>
      ⟨a⁻¹*x, h,
        by 
          simp ⟩

@[toAdditive mem_right_add_coset_iff]
theorem mem_right_coset_iff (a : α) : x ∈ s *r a ↔ (x*a⁻¹) ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ =>
      by 
        simp [Eq.symm, hb])
    fun h =>
      ⟨x*a⁻¹, h,
        by 
          simp ⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable[Groupₓ α](s : Subgroup α)

@[toAdditive left_add_coset_mem_left_add_coset]
theorem left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
  Set.ext$
    by 
      simp [mem_left_coset_iff, mul_mem_cancel_left s (s.inv_mem ha)]

@[toAdditive right_add_coset_mem_right_add_coset]
theorem right_coset_mem_right_coset {a : α} (ha : a ∈ s) : (s : Set α) *r a = s :=
  Set.ext$
    fun b =>
      by 
        simp [mem_right_coset_iff, mul_mem_cancel_right s (s.inv_mem ha)]

@[toAdditive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.normal) (g : α) : g *l s = s *r g :=
  Set.ext$
    fun a =>
      by 
        simp [mem_left_coset_iff, mem_right_coset_iff] <;> rw [N.mem_comm_iff]

@[toAdditive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.normal :=
  ⟨fun a ha g =>
      show ((g*a)*g⁻¹) ∈ (s : Set α)by 
        rw [←mem_right_coset_iff, ←h] <;> exact mem_left_coset g ha⟩

@[toAdditive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.normal ↔ ∀ g : α, g *l s = s *r g :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[toAdditive left_add_coset_eq_iff]
theorem left_coset_eq_iff {x y : α} : LeftCoset x s = LeftCoset y s ↔ (x⁻¹*y) ∈ s :=
  by 
    rw [Set.ext_iff]
    simpRw [mem_left_coset_iff, SetLike.mem_coe]
    split 
    ·
      intro h 
      apply (h y).mpr 
      rw [mul_left_invₓ]
      exact s.one_mem
    ·
      intro h z 
      rw [←mul_inv_cancel_rightₓ (x⁻¹) y]
      rw [mul_assocₓ]
      exact s.mul_mem_cancel_left h

@[toAdditive right_add_coset_eq_iff]
theorem right_coset_eq_iff {x y : α} : RightCoset («expr↑ » s) x = RightCoset s y ↔ (y*x⁻¹) ∈ s :=
  by 
    rw [Set.ext_iff]
    simpRw [mem_right_coset_iff, SetLike.mem_coe]
    split 
    ·
      intro h 
      apply (h y).mpr 
      rw [mul_right_invₓ]
      exact s.one_mem
    ·
      intro h z 
      rw [←inv_mul_cancel_leftₓ y (x⁻¹)]
      rw [←mul_assocₓ]
      exact s.mul_mem_cancel_right h

end CosetSubgroup

run_cmd 
  to_additive.map_namespace `quotient_group `quotient_add_group

namespace QuotientGroup

variable[Groupₓ α](s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[toAdditive "The equivalence relation corresponding to the partition of a group by left cosets\nof a subgroup."]
def left_rel : Setoidₓ α :=
  ⟨fun x y => (x⁻¹*y) ∈ s,
    by 
      simpRw [←left_coset_eq_iff]
      exact left_coset_equivalence_rel s⟩

theorem left_rel_r_eq_left_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.leftRel s) = LeftCosetEquivalence s :=
  by 
    ext 
    exact (left_coset_eq_iff s).symm

@[toAdditive]
instance left_rel_decidable [DecidablePred (· ∈ s)] : DecidableRel (left_rel s).R :=
  fun x y => ‹DecidablePred (· ∈ s)› _

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
@[toAdditive
      "`quotient s` is the quotient type representing the left cosets of `s`.  If `s` is a\nnormal subgroup, `quotient s` is a group"]
def Quotientₓ : Type _ :=
  Quotientₓ (left_rel s)

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[toAdditive "The equivalence relation corresponding to the partition of a group by right cosets of\na subgroup."]
def right_rel : Setoidₓ α :=
  ⟨fun x y => (y*x⁻¹) ∈ s,
    by 
      simpRw [←right_coset_eq_iff]
      exact right_coset_equivalence_rel s⟩

theorem right_rel_r_eq_right_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.rightRel s) = RightCosetEquivalence s :=
  by 
    ext 
    exact (right_coset_eq_iff s).symm

@[toAdditive]
instance right_rel_decidable [DecidablePred (· ∈ s)] : DecidableRel (right_rel s).R :=
  fun x y => ‹DecidablePred (· ∈ s)› _

end QuotientGroup

namespace QuotientGroup

variable[Groupₓ α]{s : Subgroup α}

@[toAdditive]
instance Fintype [Fintype α] (s : Subgroup α) [DecidableRel (left_rel s).R] : Fintype (QuotientGroup.Quotient s) :=
  Quotientₓ.fintype (left_rel s)

/-- The canonical map from a group `α` to the quotient `α/s`. -/
@[toAdditive "The canonical map from an `add_group` `α` to the quotient `α/s`."]
abbrev mk (a : α) : Quotientₓ s :=
  Quotientₓ.mk' a

@[elab_as_eliminator, toAdditive]
theorem induction_on {C : Quotientₓ s → Prop} (x : Quotientₓ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotientₓ.induction_on' x H

@[toAdditive]
instance  : CoeTₓ α (Quotientₓ s) :=
  ⟨mk⟩

@[elab_as_eliminator, toAdditive]
theorem induction_on' {C : Quotientₓ s → Prop} (x : Quotientₓ s) (H : ∀ z : α, C z) : C x :=
  Quotientₓ.induction_on' x H

@[toAdditive]
theorem forall_coe {C : Quotientₓ s → Prop} : (∀ x : Quotientₓ s, C x) ↔ ∀ x : α, C x :=
  ⟨fun hx x => hx _, Quot.ind⟩

@[toAdditive]
instance  (s : Subgroup α) : Inhabited (Quotientₓ s) :=
  ⟨((1 : α) : Quotientₓ s)⟩

@[toAdditive QuotientAddGroup.eq]
protected theorem Eq {a b : α} : (a : Quotientₓ s) = b ↔ (a⁻¹*b) ∈ s :=
  Quotientₓ.eq'

@[toAdditive QuotientAddGroup.eq']
theorem eq' {a b : α} : (mk a : Quotientₓ s) = mk b ↔ (a⁻¹*b) ∈ s :=
  QuotientGroup.eq

@[toAdditive QuotientAddGroup.out_eq']
theorem out_eq' (a : Quotientₓ s) : mk a.out' = a :=
  Quotientₓ.out_eq' a

variable(s)

@[toAdditive QuotientAddGroup.mk_out'_eq_mul]
theorem mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : Quotientₓ s).out' = g*h :=
  ⟨⟨g⁻¹*(mk g).out', eq'.mp (mk g).out_eq'.symm⟩,
    by 
      rw [s.coe_mk, mul_inv_cancel_left]⟩

variable{s}

@[toAdditive QuotientAddGroup.mk_mul_of_mem]
theorem mk_mul_of_mem (g₁ g₂ : α) (hg₂ : g₂ ∈ s) : (mk (g₁*g₂) : Quotientₓ s) = mk g₁ :=
  by 
    rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[toAdditive]
theorem eq_class_eq_left_coset (s : Subgroup α) (g : α) : { x : α | (x : Quotientₓ s) = g } = LeftCoset g s :=
  Set.ext$
    fun z =>
      by 
        rw [mem_left_coset_iff, Set.mem_set_of_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]

@[toAdditive]
theorem preimage_image_coe (N : Subgroup α) (s : Set α) :
  coeₓ ⁻¹' ((coeₓ : α → Quotientₓ N) '' s) = ⋃x : N, (fun y : α => y*x) ⁻¹' s :=
  by 
    ext x 
    simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_Union, Set.mem_image,
      Subgroup.coe_mk, ←eq_inv_mul_iff_mul_eq]
    exact
      ⟨fun ⟨y, hs, hN⟩ =>
          ⟨_, N.inv_mem hN,
            by 
              simpa using hs⟩,
        fun ⟨z, hz, hxz⟩ =>
          ⟨x*z, hxz,
            by 
              simpa using hz⟩⟩

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable[Groupₓ α]{s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[toAdditive "The natural bijection between the cosets `g + s` and `s`."]
def left_coset_equiv_subgroup (g : α) : LeftCoset g s ≃ s :=
  ⟨fun x => ⟨g⁻¹*x.1, (mem_left_coset_iff _).1 x.2⟩, fun x => ⟨g*x.1, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ =>
      Subtype.eq$
        by 
          simp ,
    fun ⟨g, hg⟩ =>
      Subtype.eq$
        by 
          simp ⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[toAdditive "The natural bijection between the cosets `s + g` and `s`."]
def right_coset_equiv_subgroup (g : α) : RightCoset («expr↑ » s) g ≃ s :=
  ⟨fun x => ⟨x.1*g⁻¹, (mem_right_coset_iff _).1 x.2⟩, fun x => ⟨x.1*g, x.1, x.2, rfl⟩,
    fun ⟨x, hx⟩ =>
      Subtype.eq$
        by 
          simp ,
    fun ⟨g, hg⟩ =>
      Subtype.eq$
        by 
          simp ⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[toAdditive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def group_equiv_quotient_times_subgroup : α ≃ Quotientₓ s × s :=
  calc α ≃ ΣL : Quotientₓ s, { x : α // (x : Quotientₓ s) = L } := (Equiv.sigmaPreimageEquiv QuotientGroup.mk).symm 
    _ ≃ ΣL : Quotientₓ s, LeftCoset (Quotientₓ.out' L) s :=
    Equiv.sigmaCongrRight
      fun L =>
        by 
          rw [←eq_class_eq_left_coset]
          show
            (_root_.subtype fun x : α => Quotientₓ.mk' x = L) ≃
              _root_.subtype fun x : α => Quotientₓ.mk' x = Quotientₓ.mk' _ 
          simp [-Quotientₓ.eq']
    _ ≃ ΣL : Quotientₓ s, s := Equiv.sigmaCongrRight fun L => left_coset_equiv_subgroup _ 
    _ ≃ Quotientₓ s × s := Equiv.sigmaEquivProd _ _
    

variable{t : Subgroup α}

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`. -/
@[toAdditive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse\nof the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`.",
  simps]
def quotient_equiv_prod_of_le' (h_le : s ≤ t) (f : Quotientₓ t → α) (hf : Function.RightInverse f QuotientGroup.mk) :
  Quotientₓ s ≃ Quotientₓ t × Quotientₓ (s.subgroup_of t) :=
  { toFun :=
      fun a =>
        ⟨a.map' id fun b c h => h_le h,
          a.map' (fun g : α => ⟨f (Quotientₓ.mk' g)⁻¹*g, Quotientₓ.exact' (hf g)⟩)
            fun b c h =>
              by 
                change ((f b⁻¹*b)⁻¹*f c⁻¹*c) ∈ s 
                have key : f b = f c := congr_argₓ f (Quotientₓ.sound' (h_le h))
                rwa [key, mul_inv_rev, inv_invₓ, mul_assocₓ, mul_inv_cancel_left]⟩,
    invFun :=
      fun a =>
        a.2.map' (fun b => f a.1*b)
          fun b c h =>
            by 
              change ((f a.1*b)⁻¹*f a.1*c) ∈ s 
              rwa [mul_inv_rev, mul_assocₓ, inv_mul_cancel_leftₓ],
    left_inv :=
      by 
        refine' Quotientₓ.ind' fun a => _ 
        simpRw [Quotientₓ.map'_mk', id.def, t.coe_mk, mul_inv_cancel_left],
    right_inv :=
      by 
        refine' Prod.rec _ 
        refine' Quotientₓ.ind' fun a => _ 
        refine' Quotientₓ.ind' fun b => _ 
        have key : Quotientₓ.mk' (f (Quotientₓ.mk' a)*b) = Quotientₓ.mk' a :=
          (QuotientGroup.mk_mul_of_mem (f a) («expr↑ » b) b.2).trans (hf a)
        simpRw [Quotientₓ.map'_mk', id.def, key, inv_mul_cancel_leftₓ, Subtype.coe_eta] }

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`. -/
@[toAdditive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.\nThe constructive version is `quotient_equiv_prod_of_le'`.",
  simps]
noncomputable def quotient_equiv_prod_of_le (h_le : s ≤ t) : Quotientₓ s ≃ Quotientₓ t × Quotientₓ (s.subgroup_of t) :=
  quotient_equiv_prod_of_le' h_le Quotientₓ.out' Quotientₓ.out_eq'

@[toAdditive]
theorem card_eq_card_quotient_mul_card_subgroup [Fintype α] (s : Subgroup α) [Fintype s]
  [DecidablePred fun a => a ∈ s] : Fintype.card α = Fintype.card (Quotientₓ s)*Fintype.card s :=
  by 
    rw [←Fintype.card_prod] <;> exact Fintype.card_congr Subgroup.groupEquivQuotientTimesSubgroup

/-- **Order of a Subgroup** -/
theorem card_subgroup_dvd_card [Fintype α] (s : Subgroup α) [Fintype s] : Fintype.card s ∣ Fintype.card α :=
  by 
    haveI  := Classical.propDecidable <;> simp [card_eq_card_quotient_mul_card_subgroup s]

theorem card_quotient_dvd_card [Fintype α] (s : Subgroup α) [DecidablePred fun a => a ∈ s] [Fintype s] :
  Fintype.card (Quotientₓ s) ∣ Fintype.card α :=
  by 
    simp [card_eq_card_quotient_mul_card_subgroup s]

open Fintype

variable{H : Type _}[Groupₓ H]

theorem card_dvd_of_injective [Fintype α] [Fintype H] (f : α →* H) (hf : Function.Injective f) : card α ∣ card H :=
  by 
    classical <;>
      calc card α = card (f.range : Subgroup H) := card_congr (Equiv.ofInjective f hf)_ ∣ card H :=
        card_subgroup_dvd_card _

theorem card_dvd_of_le {H K : Subgroup α} [Fintype H] [Fintype K] (hHK : H ≤ K) : card H ∣ card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

theorem card_comap_dvd_of_injective (K : Subgroup H) [Fintype K] (f : α →* H) [Fintype (K.comap f)]
  (hf : Function.Injective f) : Fintype.card (K.comap f) ∣ Fintype.card K :=
  by 
    haveI  : Fintype ((K.comap f).map f) := Fintype.ofEquiv _ (equiv_map_of_injective _ _ hf).toEquiv <;>
      calc Fintype.card (K.comap f) = Fintype.card ((K.comap f).map f) :=
        Fintype.card_congr (equiv_map_of_injective _ _ hf).toEquiv _ ∣ Fintype.card K :=
        card_dvd_of_le (map_comap_le _ _)

end Subgroup

namespace QuotientGroup

variable[Groupₓ α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α/s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in
`α` and the product `s × t`. -/
noncomputable def preimage_mk_equiv_subgroup_times_set (s : Subgroup α) (t : Set (Quotientₓ s)) :
  QuotientGroup.mk ⁻¹' t ≃ s × t :=
  have h :
    ∀ {x : Quotientₓ s} {a : α},
      x ∈ t → a ∈ s → (Quotientₓ.mk' (Quotientₓ.out' x*a) : Quotientₓ s) = Quotientₓ.mk' (Quotientₓ.out' x) :=
    fun x a hx ha =>
      Quotientₓ.sound'
        (show ((Quotientₓ.out' x*a)⁻¹*Quotientₓ.out' x) ∈ s from
          s.inv_mem_iff.1$
            by 
              rwa [mul_inv_rev, inv_invₓ, ←mul_assocₓ, inv_mul_selfₓ, one_mulₓ])
  { toFun :=
      fun ⟨a, ha⟩ =>
        ⟨⟨Quotientₓ.out' (Quotientₓ.mk' a)⁻¹*a, @Quotientₓ.exact' _ (left_rel s) _ _$ Quotientₓ.out_eq' _⟩,
          ⟨Quotientₓ.mk' a, ha⟩⟩,
    invFun :=
      fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
        ⟨Quotientₓ.out' x*a,
          show Quotientₓ.mk' _ ∈ t by 
            simp [h hx ha, hx]⟩,
    left_inv :=
      fun ⟨a, ha⟩ =>
        Subtype.eq$
          show (_*_) = a by 
            simp ,
    right_inv :=
      fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
        show (_, _) = _ by 
          simp [h hx ha] }

end QuotientGroup

/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/
library_note "use has_coe_t"

