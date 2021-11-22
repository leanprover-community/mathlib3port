import Mathbin.Algebra.Module.Basic 
import Mathbin.Data.Set.Finite 
import Mathbin.GroupTheory.Submonoid.Basic

/-!
# Pointwise addition, multiplication, and scalar multiplication of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.
* We also define pointwise multiplication on `finset`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication

-/


namespace Set

open Function

variable{α : Type _}{β : Type _}{s s₁ s₂ t t₁ t₂ u : Set α}{a b : α}{x y : β}

/-! ### Properties about 1 -/


/-- The set `(1 : set α)` is defined as `{1}` in locale `pointwise`. -/
@[toAdditive "The set `(0 : set α)` is defined as `{0}` in locale `pointwise`. "]
protected def HasOne [HasOne α] : HasOne (Set α) :=
  ⟨{1}⟩

localized [Pointwise] attribute [instance] Set.hasOne Set.hasZero

@[toAdditive]
theorem singleton_one [HasOne α] : ({1} : Set α) = 1 :=
  rfl

@[simp, toAdditive]
theorem mem_one [HasOne α] : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl

@[toAdditive]
theorem one_mem_one [HasOne α] : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _

@[simp, toAdditive]
theorem one_subset [HasOne α] : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[toAdditive]
theorem one_nonempty [HasOne α] : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩

@[simp, toAdditive]
theorem image_one [HasOne α] {f : α → β} : f '' 1 = {f 1} :=
  image_singleton

/-! ### Properties about multiplication -/


/-- The set `(s * t : set α)` is defined as `{x * y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[toAdditive " The set `(s + t : set α)` is defined as `{x + y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def Mul [Mul α] : Mul (Set α) :=
  ⟨image2 Mul.mul⟩

localized [Pointwise] attribute [instance] Set.hasMul Set.hasAdd

@[simp, toAdditive]
theorem image2_mul [Mul α] : image2 Mul.mul s t = s*t :=
  rfl

@[toAdditive]
theorem mem_mul [Mul α] : (a ∈ s*t) ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ (x*y) = a :=
  Iff.rfl

@[toAdditive]
theorem mul_mem_mul [Mul α] (ha : a ∈ s) (hb : b ∈ t) : (a*b) ∈ s*t :=
  mem_image2_of_mem ha hb

@[toAdditive add_image_prod]
theorem image_mul_prod [Mul α] : (fun x : α × α => x.fst*x.snd) '' s.prod t = s*t :=
  image_prod _

@[simp, toAdditive]
theorem image_mul_left [Groupₓ α] : (fun b => a*b) '' t = (fun b => a⁻¹*b) ⁻¹' t :=
  by 
    rw [image_eq_preimage_of_inverse] <;> intro c <;> simp 

@[simp, toAdditive]
theorem image_mul_right [Groupₓ α] : (fun a => a*b) '' t = (fun a => a*b⁻¹) ⁻¹' t :=
  by 
    rw [image_eq_preimage_of_inverse] <;> intro c <;> simp 

@[toAdditive]
theorem image_mul_left' [Groupₓ α] : (fun b => a⁻¹*b) '' t = (fun b => a*b) ⁻¹' t :=
  by 
    simp 

@[toAdditive]
theorem image_mul_right' [Groupₓ α] : (fun a => a*b⁻¹) '' t = (fun a => a*b) ⁻¹' t :=
  by 
    simp 

@[simp, toAdditive]
theorem preimage_mul_left_singleton [Groupₓ α] : (·*·) a ⁻¹' {b} = {a⁻¹*b} :=
  by 
    rw [←image_mul_left', image_singleton]

@[simp, toAdditive]
theorem preimage_mul_right_singleton [Groupₓ α] : (·*a) ⁻¹' {b} = {b*a⁻¹} :=
  by 
    rw [←image_mul_right', image_singleton]

@[simp, toAdditive]
theorem preimage_mul_left_one [Groupₓ α] : (fun b => a*b) ⁻¹' 1 = {a⁻¹} :=
  by 
    rw [←image_mul_left', image_one, mul_oneₓ]

@[simp, toAdditive]
theorem preimage_mul_right_one [Groupₓ α] : (fun a => a*b) ⁻¹' 1 = {b⁻¹} :=
  by 
    rw [←image_mul_right', image_one, one_mulₓ]

@[toAdditive]
theorem preimage_mul_left_one' [Groupₓ α] : (fun b => a⁻¹*b) ⁻¹' 1 = {a} :=
  by 
    simp 

@[toAdditive]
theorem preimage_mul_right_one' [Groupₓ α] : (fun a => a*b⁻¹) ⁻¹' 1 = {b} :=
  by 
    simp 

@[simp, toAdditive]
theorem mul_singleton [Mul α] : (s*{b}) = (fun a => a*b) '' s :=
  image2_singleton_right

@[simp, toAdditive]
theorem singleton_mul [Mul α] : ({a}*t) = (fun b => a*b) '' t :=
  image2_singleton_left

@[simp, toAdditive]
theorem singleton_mul_singleton [Mul α] : (({a} : Set α)*{b}) = {a*b} :=
  image2_singleton

@[toAdditive]
protected theorem mul_commₓ [CommSemigroupₓ α] : (s*t) = t*s :=
  by 
    simp only [←image2_mul, image2_swap _ s, mul_commₓ]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[toAdditive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def MulOneClass [MulOneClass α] : MulOneClass (Set α) :=
  { Set.hasOne, Set.hasMul with
    mul_one :=
      fun s =>
        by 
          simp only [←singleton_one, mul_singleton, mul_oneₓ, image_id'],
    one_mul :=
      fun s =>
        by 
          simp only [←singleton_one, singleton_mul, one_mulₓ, image_id'] }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[toAdditive "`set α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def Semigroupₓ [Semigroupₓ α] : Semigroupₓ (Set α) :=
  { Set.hasMul with mul_assoc := fun _ _ _ => image2_assoc mul_assocₓ }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[toAdditive "`set α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def Monoidₓ [Monoidₓ α] : Monoidₓ (Set α) :=
  { Set.semigroup, Set.mulOneClass with  }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[toAdditive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def CommMonoidₓ [CommMonoidₓ α] : CommMonoidₓ (Set α) :=
  { Set.monoid with mul_comm := fun _ _ => Set.mul_comm }

localized [Pointwise]
  attribute [instance] Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.monoid Set.addMonoid
    Set.commMonoid Set.addCommMonoid

theorem pow_mem_pow [Monoidₓ α] (ha : a ∈ s) (n : ℕ) : a ^ n ∈ s ^ n :=
  by 
    induction' n with n ih
    ·
      rw [pow_zeroₓ]
      exact Set.mem_singleton 1
    ·
      rw [pow_succₓ]
      exact Set.mul_mem_mul ha ih

/-- Under `[has_mul M]`, the `singleton` map from `M` to `set M` as a `mul_hom`, that is, a map
which preserves multiplication. -/
@[toAdditive
      "Under `[has_add A]`, the `singleton` map from `A` to `set A` as an `add_hom`,\nthat is, a map which preserves addition.",
  simps]
def singleton_mul_hom [Mul α] : MulHom α (Set α) :=
  { toFun := singleton, map_mul' := fun a b => singleton_mul_singleton.symm }

@[simp, toAdditive]
theorem empty_mul [Mul α] : (∅*s) = ∅ :=
  image2_empty_left

@[simp, toAdditive]
theorem mul_empty [Mul α] : (s*∅) = ∅ :=
  image2_empty_right

theorem empty_pow [Monoidₓ α] (n : ℕ) (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ :=
  by 
    rw [←tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ$ Nat.pos_of_ne_zeroₓ hn), pow_succₓ, empty_mul]

instance decidable_mem_mul [Monoidₓ α] [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
  DecidablePred (· ∈ s*t) :=
  fun _ => decidableOfIff _ mem_mul.symm

instance decidable_mem_pow [Monoidₓ α] [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
  DecidablePred (· ∈ s ^ n) :=
  by 
    induction' n with n ih
    ·
      simpRw [pow_zeroₓ, mem_one]
      infer_instance
    ·
      letI this := ih 
      rw [pow_succₓ]
      infer_instance

@[toAdditive]
theorem mul_subset_mul [Mul α] (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : (s₁*s₂) ⊆ t₁*t₂ :=
  image2_subset h₁ h₂

theorem pow_subset_pow [Monoidₓ α] (hst : s ⊆ t) (n : ℕ) : s ^ n ⊆ t ^ n :=
  by 
    induction' n with n ih
    ·
      rw [pow_zeroₓ]
      exact subset.rfl
    ·
      rw [pow_succₓ, pow_succₓ]
      exact mul_subset_mul hst ih

@[toAdditive]
theorem union_mul [Mul α] : ((s ∪ t)*u) = (s*u) ∪ t*u :=
  image2_union_left

@[toAdditive]
theorem mul_union [Mul α] : (s*t ∪ u) = (s*t) ∪ s*u :=
  image2_union_right

@[toAdditive]
theorem Union_mul_left_image [Mul α] : (⋃(a : _)(_ : a ∈ s), (fun x => a*x) '' t) = s*t :=
  Union_image_left _

@[toAdditive]
theorem Union_mul_right_image [Mul α] : (⋃(a : _)(_ : a ∈ t), (fun x => x*a) '' s) = s*t :=
  Union_image_right _

@[toAdditive]
theorem Union_mul {ι : Sort _} [Mul α] (s : ι → Set α) (t : Set α) : ((⋃i, s i)*t) = ⋃i, s i*t :=
  image2_Union_left _ _ _

@[toAdditive]
theorem mul_Union {ι : Sort _} [Mul α] (t : Set α) (s : ι → Set α) : (t*⋃i, s i) = ⋃i, t*s i :=
  image2_Union_right _ _ _

@[simp, toAdditive]
theorem univ_mul_univ [Monoidₓ α] : ((univ : Set α)*univ) = univ :=
  by 
    have  : ∀ x, ∃ a b : α, (a*b) = x := fun x => ⟨x, ⟨1, mul_oneₓ x⟩⟩
    simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_andₓ]

/-- `singleton` is a monoid hom. -/
@[toAdditive singleton_add_hom "singleton is an add monoid hom"]
def singleton_hom [Monoidₓ α] : α →* Set α :=
  { toFun := singleton, map_one' := rfl, map_mul' := fun a b => singleton_mul_singleton.symm }

@[toAdditive]
theorem nonempty.mul [Mul α] : s.nonempty → t.nonempty → (s*t).Nonempty :=
  nonempty.image2

@[toAdditive]
theorem finite.mul [Mul α] (hs : finite s) (ht : finite t) : finite (s*t) :=
  hs.image2 _ ht

/-- multiplication preserves finiteness -/
@[toAdditive "addition preserves finiteness"]
def fintype_mul [Mul α] [DecidableEq α] (s t : Set α) [hs : Fintype s] [ht : Fintype t] : Fintype (s*t : Set α) :=
  Set.fintypeImage2 _ s t

@[toAdditive]
theorem bdd_above_mul [OrderedCommMonoid α] {A B : Set α} : BddAbove A → BddAbove B → BddAbove (A*B) :=
  by 
    rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
    use bA*bB 
    rintro x ⟨xa, xb, hxa, hxb, rfl⟩
    exact mul_le_mul' (hbA hxa) (hbB hxb)

section BigOperators

open_locale BigOperators

variable{ι : Type _}[CommMonoidₓ α]

/-- The n-ary version of `set.mem_mul`. -/
@[toAdditive " The n-ary version of `set.mem_add`. "]
theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
  (a ∈ ∏i in t, f i) ↔ ∃ (g : ι → α)(hg : ∀ {i}, i ∈ t → g i ∈ f i), (∏i in t, g i) = a :=
  by 
    classical 
    induction' t using Finset.induction_on with i is hi ih generalizing a
    ·
      simpRw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h => ⟨fun i => a, fun i => False.elim, h.symm⟩, fun ⟨f, _, hf⟩ => hf.symm⟩
    rw [Finset.prod_insert hi, Set.mem_mul]
    simpRw [Finset.prod_insert hi]
    simpRw [ih]
    split 
    ·
      rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine' ⟨Function.update g i x, fun j hj => _, _⟩
      obtain rfl | hj := finset.mem_insert.mp hj
      ·
        rw [Function.update_same]
        exact hx
      ·
        rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
        exact hg hj 
      rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    ·
      rintro ⟨g, hg, rfl⟩
      exact ⟨g i, is.prod g, hg (is.mem_insert_self _), ⟨g, fun i hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[toAdditive " A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
  (a ∈ ∏i, f i) ↔ ∃ (g : ι → α)(hg : ∀ i, g i ∈ f i), (∏i, g i) = a :=
  by 
    rw [mem_finset_prod]
    simp 

/-- The n-ary version of `set.mul_mem_mul`. -/
@[toAdditive " The n-ary version of `set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i _ : i ∈ t, g i ∈ f i) :
  (∏i in t, g i) ∈ ∏i in t, f i :=
  by 
    rw [mem_finset_prod]
    exact ⟨g, hg, rfl⟩

/-- The n-ary version of `set.mul_subset_mul`. -/
@[toAdditive " The n-ary version of `set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α) (hf : ∀ {i}, i ∈ t → f₁ i ⊆ f₂ i) :
  (∏i in t, f₁ i) ⊆ ∏i in t, f₂ i :=
  by 
    intro a 
    rw [mem_finset_prod, mem_finset_prod]
    rintro ⟨g, hg, rfl⟩
    exact ⟨g, fun i hi => hf hi$ hg hi, rfl⟩

@[toAdditive]
theorem finset_prod_singleton {M ι : Type _} [CommMonoidₓ M] (s : Finset ι) (I : ι → M) :
  (∏i : ι in s, ({I i} : Set M)) = {∏i : ι in s, I i} :=
  by 
    letI this := Classical.decEq ι 
    refine' Finset.induction_on s _ _
    ·
      simpa
    ·
      intro _ _ H ih 
      rw [Finset.prod_insert H, Finset.prod_insert H, ih]
      simp 

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end BigOperators

/-! ### Properties about inversion -/


/-- The set `(s⁻¹ : set α)` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`.
It is equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[toAdditive
      " The set `(-s : set α)` is defined as `{x | -x ∈ s}` in locale `pointwise`.\nIt is equal to `{-x | x ∈ s}`, see `set.image_neg`. "]
protected def HasInv [HasInv α] : HasInv (Set α) :=
  ⟨preimage HasInv.inv⟩

localized [Pointwise] attribute [instance] Set.hasInv Set.hasNeg

@[simp, toAdditive]
theorem inv_empty [HasInv α] : (∅ : Set α)⁻¹ = ∅ :=
  rfl

@[simp, toAdditive]
theorem inv_univ [HasInv α] : (univ : Set α)⁻¹ = univ :=
  rfl

@[simp, toAdditive]
theorem nonempty_inv [Groupₓ α] {s : Set α} : s⁻¹.Nonempty ↔ s.nonempty :=
  inv_involutive.Surjective.nonempty_preimage

@[toAdditive]
theorem nonempty.inv [Groupₓ α] {s : Set α} (h : s.nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h

@[simp, toAdditive]
theorem mem_inv [HasInv α] : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl

@[toAdditive]
theorem inv_mem_inv [Groupₓ α] : a⁻¹ ∈ s⁻¹ ↔ a ∈ s :=
  by 
    simp only [mem_inv, inv_invₓ]

@[simp, toAdditive]
theorem inv_preimage [HasInv α] : HasInv.inv ⁻¹' s = s⁻¹ :=
  rfl

@[simp, toAdditive]
theorem image_inv [Groupₓ α] : HasInv.inv '' s = s⁻¹ :=
  by 
    simp only [←inv_preimage]
    rw [image_eq_preimage_of_inverse] <;> intro  <;> simp only [inv_invₓ]

@[simp, toAdditive]
theorem inter_inv [HasInv α] : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter

@[simp, toAdditive]
theorem union_inv [HasInv α] : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union

@[simp, toAdditive]
theorem compl_inv [HasInv α] : «expr ᶜ» s⁻¹ = «expr ᶜ» (s⁻¹) :=
  preimage_compl

@[simp, toAdditive]
protected theorem inv_invₓ [Groupₓ α] : s⁻¹⁻¹ = s :=
  by 
    simp only [←inv_preimage, preimage_preimage, inv_invₓ, preimage_id']

@[simp, toAdditive]
protected theorem univ_inv [Groupₓ α] : (univ : Set α)⁻¹ = univ :=
  preimage_univ

@[simp, toAdditive]
theorem inv_subset_inv [Groupₓ α] {s t : Set α} : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).Surjective.preimage_subset_preimage_iff

@[toAdditive]
theorem inv_subset [Groupₓ α] {s t : Set α} : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ :=
  by 
    rw [←inv_subset_inv, Set.inv_inv]

@[toAdditive]
theorem finite.inv [Groupₓ α] {s : Set α} (hs : finite s) : finite (s⁻¹) :=
  hs.preimage$ inv_injective.InjOn _

@[toAdditive]
theorem inv_singleton {β : Type _} [Groupₓ β] (x : β) : ({x} : Set β)⁻¹ = {x⁻¹} :=
  by 
    ext1 y 
    rw [mem_inv, mem_singleton_iff, mem_singleton_iff, inv_eq_iff_inv_eq, eq_comm]

/-! ### Properties about scalar multiplication -/


/-- The scaling of a set `(x • s : set β)` by a scalar `x ∶ α` is defined as `{x • y | y ∈ s}`
in locale `pointwise`. -/
@[toAdditive has_vadd_set
      "The translation of a set `(x +ᵥ s : set β)` by a scalar `x ∶ α` is\ndefined as `{x +ᵥ y | y ∈ s}` in locale `pointwise`."]
protected def has_scalar_set [HasScalar α β] : HasScalar α (Set β) :=
  ⟨fun a => image (HasScalar.smul a)⟩

/-- The pointwise scalar multiplication `(s • t : set β)` by a set of scalars `s ∶ set α`
is defined as `{x • y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[toAdditive HasVadd
      "The pointwise translation `(s +ᵥ t : set β)` by a set of constants\n`s ∶ set α` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def HasScalar [HasScalar α β] : HasScalar (Set α) (Set β) :=
  ⟨image2 HasScalar.smul⟩

localized [Pointwise] attribute [instance] Set.hasScalarSet Set.hasScalar

localized [Pointwise] attribute [instance] Set.hasVaddSet Set.hasVadd

@[simp, toAdditive]
theorem image_smul [HasScalar α β] {t : Set β} : (fun x => a • x) '' t = a • t :=
  rfl

@[toAdditive]
theorem mem_smul_set [HasScalar α β] {t : Set β} : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl

@[toAdditive]
theorem smul_mem_smul_set [HasScalar α β] {t : Set β} (hy : y ∈ t) : a • y ∈ a • t :=
  ⟨y, hy, rfl⟩

@[toAdditive]
theorem smul_set_union [HasScalar α β] {s t : Set β} : a • (s ∪ t) = a • s ∪ a • t :=
  by 
    simp only [←image_smul, image_union]

@[toAdditive]
theorem smul_set_inter [Groupₓ α] [MulAction α β] {s t : Set β} : a • (s ∩ t) = a • s ∩ a • t :=
  (image_inter$ MulAction.injective a).symm

theorem smul_set_inter₀ [GroupWithZeroₓ α] [MulAction α β] {s t : Set β} (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

@[toAdditive]
theorem smul_set_inter_subset [HasScalar α β] {s t : Set β} : a • (s ∩ t) ⊆ a • s ∩ a • t :=
  image_inter_subset _ _ _

@[simp, toAdditive]
theorem smul_set_empty [HasScalar α β] (a : α) : a • (∅ : Set β) = ∅ :=
  by 
    rw [←image_smul, image_empty]

@[toAdditive]
theorem smul_set_mono [HasScalar α β] {s t : Set β} (h : s ⊆ t) : a • s ⊆ a • t :=
  by 
    simp only [←image_smul, image_subset, h]

@[simp, toAdditive]
theorem image2_smul [HasScalar α β] {t : Set β} : image2 HasScalar.smul s t = s • t :=
  rfl

@[toAdditive]
theorem mem_smul [HasScalar α β] {t : Set β} : x ∈ s • t ↔ ∃ a y, a ∈ s ∧ y ∈ t ∧ a • y = x :=
  Iff.rfl

theorem mem_smul_of_mem [HasScalar α β] {t : Set β} {a} {b} (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t :=
  ⟨a, b, ha, hb, rfl⟩

@[toAdditive]
theorem image_smul_prod [HasScalar α β] {t : Set β} : (fun x : α × β => x.fst • x.snd) '' s.prod t = s • t :=
  image_prod _

@[toAdditive]
theorem range_smul_range [HasScalar α β] {ι κ : Type _} (b : ι → α) (c : κ → β) :
  range b • range c = range fun p : ι × κ => b p.1 • c p.2 :=
  ext$
    fun x =>
      ⟨fun hx =>
          let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
          ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
        fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[simp, toAdditive]
theorem singleton_smul [HasScalar α β] {t : Set β} : ({a} : Set α) • t = a • t :=
  image2_singleton_left

@[toAdditive]
instance smul_comm_class_set {γ : Type _} [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
  SmulCommClass α (Set β) (Set γ) :=
  { smul_comm :=
      fun a T T' =>
        by 
          simp only [←image2_smul, ←image_smul, image2_image_right, image_image2, smul_comm] }

@[toAdditive]
instance smul_comm_class_set' {γ : Type _} [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
  SmulCommClass (Set α) β (Set γ) :=
  by 
    haveI  := SmulCommClass.symm α β γ <;> exact SmulCommClass.symm _ _ _

@[toAdditive]
instance SmulCommClass {γ : Type _} [HasScalar α γ] [HasScalar β γ] [SmulCommClass α β γ] :
  SmulCommClass (Set α) (Set β) (Set γ) :=
  { smul_comm :=
      fun T T' T'' =>
        by 
          simp only [←image2_smul, image2_swap _ T]
          exact image2_assoc fun b c a => smul_comm a b c }

instance IsScalarTower {γ : Type _} [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
  IsScalarTower α β (Set γ) :=
  { smul_assoc :=
      fun a b T =>
        by 
          simp only [←image_smul, image_image, smul_assoc] }

instance is_scalar_tower' {γ : Type _} [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
  IsScalarTower α (Set β) (Set γ) :=
  { smul_assoc :=
      fun a T T' =>
        by 
          simp only [←image_smul, ←image2_smul, image_image2, image2_image_left, smul_assoc] }

instance is_scalar_tower'' {γ : Type _} [HasScalar α β] [HasScalar α γ] [HasScalar β γ] [IsScalarTower α β γ] :
  IsScalarTower (Set α) (Set β) (Set γ) :=
  { smul_assoc := fun T T' T'' => image2_assoc smul_assoc }

section Monoidₓ

/-! ### `set α` as a `(∪,*)`-semiring -/


-- error in Algebra.Pointwise: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler inhabited
/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/ @[derive #[expr inhabited]] def set_semiring (α : Type*) : Type* :=
set α

/-- The identitiy function `set α → set_semiring α`. -/
protected def up (s : Set α) : set_semiring α :=
  s

/-- The identitiy function `set_semiring α → set α`. -/
protected def set_semiring.down (s : set_semiring α) : Set α :=
  s

@[simp]
protected theorem down_up {s : Set α} : s.up.down = s :=
  rfl

@[simp]
protected theorem up_down {s : set_semiring α} : s.down.up = s :=
  rfl

instance set_semiring.add_comm_monoid : AddCommMonoidₓ (set_semiring α) :=
  { add := fun s t => (s ∪ t : Set α), zero := (∅ : Set α), add_assoc := union_assoc, zero_add := empty_union,
    add_zero := union_empty, add_comm := union_comm }

instance set_semiring.non_unital_non_assoc_semiring [Mul α] : NonUnitalNonAssocSemiring (set_semiring α) :=
  { Set.hasMul, set_semiring.add_comm_monoid with zero_mul := fun s => empty_mul, mul_zero := fun s => mul_empty,
    left_distrib := fun _ _ _ => mul_union, right_distrib := fun _ _ _ => union_mul }

instance set_semiring.non_assoc_semiring [MulOneClass α] : NonAssocSemiring (set_semiring α) :=
  { set_semiring.non_unital_non_assoc_semiring, Set.mulOneClass with  }

instance set_semiring.non_unital_semiring [Semigroupₓ α] : NonUnitalSemiring (set_semiring α) :=
  { set_semiring.non_unital_non_assoc_semiring, Set.semigroup with  }

instance set_semiring.semiring [Monoidₓ α] : Semiringₓ (set_semiring α) :=
  { set_semiring.non_assoc_semiring, set_semiring.non_unital_semiring with  }

instance set_semiring.comm_semiring [CommMonoidₓ α] : CommSemiringₓ (set_semiring α) :=
  { Set.commMonoid, set_semiring.semiring with  }

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
@[toAdditive "An additive action of an additive monoid on a type β gives also an additive action\non the subsets of β."]
protected def mul_action_set [Monoidₓ α] [MulAction α β] : MulAction α (Set β) :=
  { Set.hasScalarSet with
    mul_smul :=
      by 
        intros 
        simp only [←image_smul, image_image, ←mul_smul],
    one_smul :=
      by 
        intros 
        simp only [←image_smul, image_eta, one_smul, image_id'] }

localized [Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet

section MulHom

variable[Mul α][Mul β](m : MulHom α β)

@[toAdditive]
theorem image_mul : (m '' s*t) = (m '' s)*m '' t :=
  by 
    simp only [←image2_mul, image_image2, image2_image_left, image2_image_right, m.map_mul]

@[toAdditive]
theorem preimage_mul_preimage_subset {s t : Set β} : ((m ⁻¹' s)*m ⁻¹' t) ⊆ m ⁻¹' s*t :=
  by 
    rintro _ ⟨_, _, _, _, rfl⟩
    exact ⟨_, _, ‹_›, ‹_›, (m.map_mul _ _).symm⟩

end MulHom

/-- The image of a set under function is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom [Monoidₓ α] [Monoidₓ β] (f : α →* β) : set_semiring α →+* set_semiring β :=
  { toFun := image f, map_zero' := image_empty _,
    map_one' :=
      by 
        simp only [←singleton_one, image_singleton, f.map_one],
    map_add' := image_union _, map_mul' := fun _ _ => image_mul f.to_mul_hom }

end Monoidₓ

end Set

open Set

open_locale Pointwise

section 

variable{α : Type _}{β : Type _}

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set [HasZero α] [HasZero β] [SmulWithZero α β] {s : Set β} (h : s.nonempty) :
  (0 : α) • s = (0 : Set β) :=
  by 
    simp only [←image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

theorem zero_smul_subset [HasZero α] [HasZero β] [SmulWithZero α β] (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2$ fun x _ => zero_smul α x

theorem subsingleton_zero_smul_set [HasZero α] [HasZero β] [SmulWithZero α β] (s : Set β) :
  ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.mono (zero_smul_subset s)

section Groupₓ

variable[Groupₓ α][MulAction α β]

@[simp, toAdditive]
theorem smul_mem_smul_set_iff {a : α} {A : Set β} {x : β} : a • x ∈ a • A ↔ x ∈ A :=
  ⟨fun h =>
      by 
        rw [←inv_smul_smul a x, ←inv_smul_smul a A]
        exact smul_mem_smul_set h,
    smul_mem_smul_set⟩

@[toAdditive]
theorem mem_smul_set_iff_inv_smul_mem {a : α} {A : Set β} {x : β} : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[toAdditive]
theorem mem_inv_smul_set_iff {a : α} {A : Set β} {x : β} : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  by 
    simp only [←image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[toAdditive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm

@[toAdditive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a⁻¹) t

@[simp, toAdditive]
theorem set_smul_subset_set_smul_iff {a : α} {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff$ MulAction.injective _

@[toAdditive]
theorem set_smul_subset_iff {a : α} {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans$ iff_of_eq$ congr_argₓ _$ preimage_equiv_eq_image_symm _$ MulAction.toPerm _

@[toAdditive]
theorem subset_set_smul_iff {a : α} {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm$
    image_subset_iff.trans$ Iff.symm$ iff_of_eq$ congr_argₓ _$ image_equiv_eq_preimage_symm _$ MulAction.toPerm _

end Groupₓ

section GroupWithZeroₓ

variable[GroupWithZeroₓ α][MulAction α β]

@[simp]
theorem smul_mem_smul_set_iff₀ {a : α} (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

theorem mem_smul_set_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

theorem mem_inv_smul_set_iff₀ {a : α} (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ Units.mk0 a ha⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

theorem preimage_smul₀ {a : α} (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

theorem preimage_smul_inv₀ {a : α} (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha⁻¹) t

@[simp]
theorem set_smul_subset_set_smul_iff₀ {a : α} (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff

theorem set_smul_subset_iff₀ {a : α} (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff

theorem subset_set_smul_iff₀ {a : α} (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff

end GroupWithZeroₓ

end 

namespace Finset

variable{α : Type _}[DecidableEq α]

/-- The pointwise product of two finite sets `s` and `t`:
`st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[toAdditive "The pointwise sum of two finite sets `s` and `t`:\n`s + t = { x + y | x ∈ s, y ∈ t }`. "]
protected def Mul [Mul α] : Mul (Finset α) :=
  ⟨fun s t => (s.product t).Image fun p : α × α => p.1*p.2⟩

localized [Pointwise] attribute [instance] Finset.hasMul Finset.hasAdd

@[toAdditive]
theorem mul_def [Mul α] {s t : Finset α} : (s*t) = (s.product t).Image fun p : α × α => p.1*p.2 :=
  rfl

@[toAdditive]
theorem mem_mul [Mul α] {s t : Finset α} {x : α} : (x ∈ s*t) ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ (y*z) = x :=
  by 
    simp only [Finset.mul_def, And.assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[simp, normCast, toAdditive]
theorem coe_mul [Mul α] {s t : Finset α} : («expr↑ » (s*t) : Set α) = «expr↑ » s*«expr↑ » t :=
  by 
    ext 
    simp only [mem_mul, Set.mem_mul, mem_coe]

@[toAdditive]
theorem mul_mem_mul [Mul α] {s t : Finset α} {x y : α} (hx : x ∈ s) (hy : y ∈ t) : (x*y) ∈ s*t :=
  by 
    simp only [Finset.mem_mul]
    exact ⟨x, y, hx, hy, rfl⟩

@[toAdditive]
theorem mul_card_le [Mul α] {s t : Finset α} : (s*t).card ≤ s.card*t.card :=
  by 
    convert Finset.card_image_le 
    rw [Finset.card_product, mul_commₓ]

open_locale Classical

-- error in Algebra.Pointwise: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- A finite set `U` contained in the product of two sets `S * S'` is also contained in the product
of two finite sets `T * T' ⊆ S * S'`. -/
@[to_additive #[]]
theorem subset_mul
{M : Type*}
[monoid M]
{S : set M}
{S' : set M}
{U : finset M}
(f : «expr ⊆ »(«expr↑ »(U), «expr * »(S, S'))) : «expr∃ , »((T
  T' : finset M), «expr ∧ »(«expr ⊆ »(«expr↑ »(T), S), «expr ∧ »(«expr ⊆ »(«expr↑ »(T'), S'), «expr ⊆ »(U, «expr * »(T, T'))))) :=
begin
  apply [expr finset.induction_on' U],
  { use ["[", expr «expr∅»(), ",", expr «expr∅»(), "]"],
    simp [] [] ["only"] ["[", expr finset.empty_subset, ",", expr finset.coe_empty, ",", expr set.empty_subset, ",", expr and_self, "]"] [] [] },
  rintros [ident a, ident s, ident haU, ident hs, ident has, "⟨", ident T, ",", ident T', ",", ident hS, ",", ident hS', ",", ident h, "⟩"],
  obtain ["⟨", ident x, ",", ident y, ",", ident hx, ",", ident hy, ",", ident ha, "⟩", ":=", expr set.mem_mul.1 (f haU)],
  use ["[", expr insert x T, ",", expr insert y T', "]"],
  simp [] [] ["only"] ["[", expr finset.coe_insert, "]"] [] [],
  repeat { rw ["[", expr set.insert_subset, "]"] [] },
  use ["[", expr hx, ",", expr hS, ",", expr hy, ",", expr hS', "]"],
  refine [expr finset.insert_subset.mpr ⟨_, _⟩],
  { rw [expr finset.mem_mul] [],
    use ["[", expr x, ",", expr y, "]"],
    simpa [] [] ["only"] ["[", expr true_and, ",", expr true_or, ",", expr eq_self_iff_true, ",", expr finset.mem_insert, "]"] [] [] },
  { suffices [ident g] [":", expr «expr ⊆ »((s : set M), «expr * »(insert x T, insert y T'))],
    { norm_cast ["at", ident g],
      assumption },
    transitivity [expr «expr↑ »(«expr * »(T, T'))],
    apply [expr h],
    rw [expr finset.coe_mul] [],
    apply [expr set.mul_subset_mul (set.subset_insert x T) (set.subset_insert y T')] }
end

end Finset

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/


namespace Submonoid

variable{M : Type _}[Monoidₓ M]

@[toAdditive]
theorem mul_subset {s t : Set M} {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : (s*t) ⊆ S :=
  by 
    rintro _ ⟨p, q, hp, hq, rfl⟩
    exact Submonoid.mul_mem _ (hs hp) (ht hq)

@[toAdditive]
theorem mul_subset_closure {s t u : Set M} (hs : s ⊆ u) (ht : t ⊆ u) : (s*t) ⊆ Submonoid.closure u :=
  mul_subset (subset.trans hs Submonoid.subset_closure) (subset.trans ht Submonoid.subset_closure)

@[toAdditive]
theorem coe_mul_self_eq (s : Submonoid M) : ((s : Set M)*s) = s :=
  by 
    ext x 
    refine' ⟨_, fun h => ⟨x, 1, h, s.one_mem, mul_oneₓ x⟩⟩
    rintro ⟨a, b, ha, hb, rfl⟩
    exact s.mul_mem ha hb

@[toAdditive]
theorem closure_mul_le (S T : Set M) : closure (S*T) ≤ closure S⊔closure T :=
  Inf_le$
    fun x ⟨s, t, hs, ht, hx⟩ =>
      hx ▸
        (closure S⊔closure T).mul_mem (SetLike.le_def.mp le_sup_left$ subset_closure hs)
          (SetLike.le_def.mp le_sup_right$ subset_closure ht)

@[toAdditive]
theorem sup_eq_closure (H K : Submonoid M) : H⊔K = closure (H*K) :=
  le_antisymmₓ
    (sup_le (fun h hh => subset_closure ⟨h, 1, hh, K.one_mem, mul_oneₓ h⟩)
      fun k hk => subset_closure ⟨1, k, H.one_mem, hk, one_mulₓ k⟩)
    (by 
      convRHS => rw [←closure_eq H, ←closure_eq K] <;> apply closure_mul_le)

end Submonoid

namespace Groupₓ

theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
  (h3 : ∀ n, f n = f (n+1) → f (n+1) = f (n+2)) : ∀ k, B ≤ k → f k = f B :=
  by 
    have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n+1)
    ·
      contrapose! h2 
      suffices  : ∀ n : ℕ, (n ≤ B+1) → n ≤ f n
      ·
        exact ⟨B+1, this (B+1) (le_reflₓ (B+1))⟩
      exact
        fun n =>
          Nat.rec (fun h => Nat.zero_leₓ (f 0))
            (fun n ih h =>
              lt_of_le_of_ltₓ (ih (n.le_succ.trans h))
                (lt_of_le_of_neₓ (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
            n
    ·
      obtain ⟨n, hn1, hn2⟩ := key 
      replace key : ∀ k : ℕ, f (n+k) = f ((n+k)+1) ∧ f (n+k) = f n :=
        fun k => Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k 
      replace key : ∀ k : ℕ, n ≤ k → f k = f n :=
        fun k hk => (congr_argₓ f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2 
      exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm

variable{G : Type _}[Groupₓ G][Fintype G](S : Set G)

theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
  ∀ k, Fintype.card G ≤ k → Fintype.card («expr↥ » (S ^ k)) = Fintype.card («expr↥ » (S ^ Fintype.card G)) :=
  by 
    have hG : 0 < Fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩
    byCases' hS : S = ∅
    ·
      intro k hk 
      congr 2
      rw [hS, empty_pow _ (ne_of_gtₓ (lt_of_lt_of_leₓ hG hk)), empty_pow _ (ne_of_gtₓ hG)]
    obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS 
    classical 
    have key : ∀ a s t : Set G, (∀ b : G, b ∈ s → (a*b) ∈ t) → Fintype.card s ≤ Fintype.card t
    ·
      refine' fun a s t h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨a*b, h b hb⟩) _ 
      rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc 
      exact Subtype.ext (mul_left_cancelₓ (subtype.ext_iff.mp hbc))
    have mono : Monotone (fun n => Fintype.card («expr↥ » (S ^ n)) : ℕ → ℕ) :=
      monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul ha hb 
    convert
      card_pow_eq_card_pow_card_univ_aux mono (fun n => set_fintype_card_le_univ (S ^ n))
        fun n h => le_antisymmₓ (mono (n+1).le_succ) (key (a⁻¹) _ _ _)
    ·
      simp only [Finset.filter_congr_decidable, Fintype.card_of_finset]
    replace h : ({a}*S ^ n) = S ^ n+1
    ·
      refine' Set.eq_of_subset_of_card_le _ (le_transₓ (ge_of_eq h) _)
      ·
        exact mul_subset_mul (set.singleton_subset_iff.mpr ha) Set.Subset.rfl
      ·
        convert key a (S ^ n) ({a}*S ^ n) fun b hb => Set.mul_mem_mul (Set.mem_singleton a) hb 
    rw [pow_succ'ₓ, ←h, mul_assocₓ, ←pow_succ'ₓ, h]
    rintro _ ⟨b, c, hb, hc, rfl⟩
    rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_leftₓ]

end Groupₓ

