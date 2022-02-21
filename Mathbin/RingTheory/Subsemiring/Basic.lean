/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Ring.Prod
import Mathbin.Algebra.Module.Basic
import Mathbin.GroupTheory.Submonoid.Membership
import Mathbin.GroupTheory.Submonoid.Center
import Mathbin.Data.Set.Finite
import Mathbin.Data.Equiv.Ring

/-!
# Bundled subsemirings

We define bundled subsemirings and some standard constructions: `complete_lattice` structure,
`subtype` and `inclusion` ring homomorphisms, subsemiring `map`, `comap` and range (`srange`) of
a `ring_hom` etc.
-/


open_locale BigOperators

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] [NonAssocSemiringₓ T]
  (M : Submonoid R)

/-- A subsemiring of a semiring `R` is a subset `s` that is both a multiplicative and an additive
submonoid. -/
structure Subsemiring (R : Type u) [NonAssocSemiringₓ R] extends Submonoid R, AddSubmonoid R

/-- Reinterpret a `subsemiring` as a `submonoid`. -/
add_decl_doc Subsemiring.toSubmonoid

/-- Reinterpret a `subsemiring` as an `add_submonoid`. -/
add_decl_doc Subsemiring.toAddSubmonoid

namespace Subsemiring

instance : SetLike (Subsemiring R) R :=
  ⟨Subsemiring.Carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

@[simp]
theorem mem_carrier {s : Subsemiring R} {x : R} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two subsemirings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subsemiring with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : Subsemiring R :=
  { S.toAddSubmonoid.copy s hs, S.toSubmonoid.copy s hs with Carrier := s }

@[simp]
theorem coe_copy (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem to_submonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_submonoid_strict_mono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) := fun _ _ => id

@[mono]
theorem to_submonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) :=
  to_submonoid_strict_mono.Monotone

theorem to_add_submonoid_injective : Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)

@[mono]
theorem to_add_submonoid_strict_mono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) := fun _ _ => id

@[mono]
theorem to_add_submonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  to_add_submonoid_strict_mono.Monotone

/-- Construct a `subsemiring R` from a set `s`, a submonoid `sm`, and an additive
submonoid `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (hm : ↑sm = s) (sa : AddSubmonoid R) (ha : ↑sa = s) :
    Subsemiring R where
  Carrier := s
  zero_mem' := ha ▸ sa.zero_mem
  one_mem' := hm ▸ sm.one_mem
  add_mem' := fun x y => by
    simpa only [← ha] using sa.add_mem
  mul_mem' := fun x y => by
    simpa only [← hm] using sm.mul_mem

@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha : Set R) = s :=
  rfl

@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) {x : R} :
    x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mk'_to_submonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm

@[simp]
theorem mk'_to_add_submonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s) :
    (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa :=
  SetLike.coe_injective ha.symm

end Subsemiring

namespace Subsemiring

variable (s : Subsemiring R)

/-- A subsemiring contains the semiring's 1. -/
theorem one_mem : (1 : R) ∈ s :=
  s.one_mem'

/-- A subsemiring contains the semiring's 0. -/
theorem zero_mem : (0 : R) ∈ s :=
  s.zero_mem'

/-- A subsemiring is closed under multiplication. -/
theorem mul_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x * y ∈ s :=
  s.mul_mem'

/-- A subsemiring is closed under addition. -/
theorem add_mem : ∀ {x y : R}, x ∈ s → y ∈ s → x + y ∈ s :=
  s.add_mem'

/-- Product of a list of elements in a `subsemiring` is in the `subsemiring`. -/
theorem list_prod_mem {R : Type _} [Semiringₓ R] (s : Subsemiring R) {l : List R} :
    (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Prod ∈ s :=
  s.toSubmonoid.list_prod_mem

/-- Sum of a list of elements in a `subsemiring` is in the `subsemiring`. -/
theorem list_sum_mem {l : List R} : (∀, ∀ x ∈ l, ∀, x ∈ s) → l.Sum ∈ s :=
  s.toAddSubmonoid.list_sum_mem

/-- Product of a multiset of elements in a `subsemiring` of a `comm_semiring`
    is in the `subsemiring`. -/
theorem multiset_prod_mem {R} [CommSemiringₓ R] (s : Subsemiring R) (m : Multiset R) :
    (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Prod ∈ s :=
  s.toSubmonoid.multiset_prod_mem m

/-- Sum of a multiset of elements in a `subsemiring` of a `semiring` is
in the `add_subsemiring`. -/
theorem multiset_sum_mem (m : Multiset R) : (∀, ∀ a ∈ m, ∀, a ∈ s) → m.Sum ∈ s :=
  s.toAddSubmonoid.multiset_sum_mem m

/-- Product of elements of a subsemiring of a `comm_semiring` indexed by a `finset` is in the
    subsemiring. -/
theorem prod_mem {R : Type _} [CommSemiringₓ R] (s : Subsemiring R) {ι : Type _} {t : Finset ι} {f : ι → R}
    (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) : (∏ i in t, f i) ∈ s :=
  s.toSubmonoid.prod_mem h

/-- Sum of elements in an `subsemiring` of an `semiring` indexed by a `finset`
is in the `add_subsemiring`. -/
theorem sum_mem (s : Subsemiring R) {ι : Type _} {t : Finset ι} {f : ι → R} (h : ∀, ∀ c ∈ t, ∀, f c ∈ s) :
    (∑ i in t, f i) ∈ s :=
  s.toAddSubmonoid.sum_mem h

theorem pow_mem {R : Type _} [Semiringₓ R] (s : Subsemiring R) {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  s.toSubmonoid.pow_mem hx n

theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s :=
  s.toAddSubmonoid.nsmul_mem hx n

theorem coe_nat_mem (n : ℕ) : (n : R) ∈ s := by
  simp only [← nsmul_one, nsmul_mem, one_mem]

/-- A subsemiring of a `non_assoc_semiring` inherits a `non_assoc_semiring` structure -/
instance toNonAssocSemiring : NonAssocSemiringₓ s :=
  { s.toSubmonoid.toMulOneClass, s.toAddSubmonoid.toAddCommMonoid with mul_zero := fun x => Subtype.eq <| mul_zero x,
    zero_mul := fun x => Subtype.eq <| zero_mul x, right_distrib := fun x y z => Subtype.eq <| right_distrib x y z,
    left_distrib := fun x y z => Subtype.eq <| left_distrib x y z }

@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = (1 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = (0 : R) :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : s) : ((x + y : s) : R) = (x + y : R) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : ((x * y : s) : R) = (x * y : R) :=
  rfl

instance nontrivial [Nontrivial R] : Nontrivial s :=
  (nontrivial_of_ne 0 1) fun H => zero_ne_one (congr_argₓ Subtype.val H)

instance no_zero_divisors [NoZeroDivisors R] : NoZeroDivisors s where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun x y h =>
    Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero <| Subtype.ext_iff.mp h) (fun h => Or.inl <| Subtype.eq h) fun h =>
      Or.inr <| Subtype.eq h

/-- A subsemiring of a `semiring` is a `semiring`. -/
instance toSemiring {R} [Semiringₓ R] (s : Subsemiring R) : Semiringₓ s :=
  { s.toNonAssocSemiring, s.toSubmonoid.toMonoid with }

@[simp, norm_cast]
theorem coe_pow {R} [Semiringₓ R] (s : Subsemiring R) (x : s) (n : ℕ) : ((x ^ n : s) : R) = (x ^ n : R) := by
  induction' n with n ih
  · simp
    
  · simp [pow_succₓ, ih]
    

/-- A subsemiring of a `comm_semiring` is a `comm_semiring`. -/
instance toCommSemiring {R} [CommSemiringₓ R] (s : Subsemiring R) : CommSemiringₓ s :=
  { s.toSemiring with mul_comm := fun _ _ => Subtype.eq <| mul_comm _ _ }

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { s.toSubmonoid.Subtype, s.toAddSubmonoid.Subtype with toFun := coe }

@[simp]
theorem coe_subtype : ⇑s.Subtype = coe :=
  rfl

/-- A subsemiring of an `ordered_semiring` is an `ordered_semiring`. -/
instance toOrderedSemiring {R} [OrderedSemiring R] (s : Subsemiring R) : OrderedSemiring s :=
  Subtype.coe_injective.OrderedSemiring coe rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A subsemiring of an `ordered_comm_semiring` is an `ordered_comm_semiring`. -/
instance toOrderedCommSemiring {R} [OrderedCommSemiring R] (s : Subsemiring R) : OrderedCommSemiring s :=
  Subtype.coe_injective.OrderedCommSemiring coe rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A subsemiring of a `linear_ordered_semiring` is a `linear_ordered_semiring`. -/
instance toLinearOrderedSemiring {R} [LinearOrderedSemiring R] (s : Subsemiring R) : LinearOrderedSemiring s :=
  Subtype.coe_injective.LinearOrderedSemiring coe rfl rfl (fun _ _ => rfl) fun _ _ => rfl

/-! Note: currently, there is no `linear_ordered_comm_semiring`. -/


@[simp]
theorem mem_to_submonoid {s : Subsemiring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_submonoid (s : Subsemiring R) : (s.toSubmonoid : Set R) = s :=
  rfl

@[simp]
theorem mem_to_add_submonoid {s : Subsemiring R} {x : R} : x ∈ s.toAddSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_to_add_submonoid (s : Subsemiring R) : (s.toAddSubmonoid : Set R) = s :=
  rfl

/-- The subsemiring `R` of the semiring `R`. -/
instance : HasTop (Subsemiring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubmonoid R) with }⟩

@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : Subsemiring R) : Set R) = Set.Univ :=
  rfl

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with Carrier := f ⁻¹' s }

@[simp]
theorem coe_comap (s : Subsemiring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
theorem mem_comap {s : Subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_comap (s : Subsemiring T) (g : S →+* T) (f : R →+* S) : (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with Carrier := f '' s }

@[simp]
theorem coe_map (f : R →+* S) (s : Subsemiring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : R →+* S} {s : Subsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image_iff_bex

@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _

theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _

theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} : s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff

theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equivₓ.Set.image f s hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _),
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
theorem coe_equiv_map_of_injective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subsemiring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
def srange : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.Range f) Set.image_univ.symm

@[simp]
theorem coe_srange : (f.srange : Set S) = Set.Range f :=
  rfl

@[simp]
theorem mem_srange {f : R →+* S} {y : S} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl

theorem srange_eq_map (f : R →+* S) : f.srange = (⊤ : Subsemiring R).map f := by
  ext
  simp

theorem mem_srange_self (f : R →+* S) (x : R) : f x ∈ f.srange :=
  mem_srange.mpr ⟨x, rfl⟩

theorem map_srange : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemiring R).map_map g f

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`.-/
instance fintypeSrange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (srange f) :=
  Set.fintypeRange f

end RingHom

namespace Subsemiring

instance : HasBot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).srange⟩

instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.Range (coe : ℕ → R) :=
  (Nat.castRingHom R).coe_srange

theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_srange

/-- The inf of two subsemirings is their intersection. -/
instance : HasInf (Subsemiring R) :=
  ⟨fun s t => { s.toSubmonoid⊓t.toSubmonoid, s.toAddSubmonoid⊓t.toAddSubmonoid with Carrier := s ∩ t }⟩

@[simp]
theorem coe_inf (p p' : Subsemiring R) : ((p⊓p' : Subsemiring R) : Set R) = p ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : Subsemiring R} {x : R} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : HasInfₓ (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t)
      (by
        simp )
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by
        simp )⟩

@[simp, norm_cast]
theorem coe_Inf (S : Set (Subsemiring R)) : ((inf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_Inf {S : Set (Subsemiring R)} {x : R} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

@[simp]
theorem Inf_to_submonoid (s : Set (Subsemiring R)) : (inf s).toSubmonoid = ⨅ t ∈ s, Subsemiring.toSubmonoid t :=
  mk'_to_submonoid _ _

@[simp]
theorem Inf_to_add_submonoid (s : Set (Subsemiring R)) :
    (inf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t :=
  mk'_to_add_submonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun s =>
      IsGlb.of_image (fun s t => show (s : Set R) ≤ t ↔ s ≤ t from SetLike.coe_subset_coe) is_glb_binfi with
    bot := ⊥,
    bot_le := fun s x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ s.coe_nat_mem n,
    top := ⊤, le_top := fun s x hx => trivialₓ, inf := (·⊓·), inf_le_left := fun s t x => And.left,
    inf_le_right := fun s t x => And.right, le_inf := fun s t₁ t₂ h₁ h₂ x hx => ⟨h₁ hx, h₂ hx⟩ }

theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

section

/-- The center of a semiring `R` is the set of elements that commute with everything in `R` -/
def center R [Semiringₓ R] : Subsemiring R :=
  { Submonoid.center R with Carrier := Set.Center R, zero_mem' := Set.zero_mem_center R,
    add_mem' := fun a b => Set.add_mem_center }

theorem coe_center R [Semiringₓ R] : ↑(center R) = Set.Center R :=
  rfl

@[simp]
theorem center_to_submonoid R [Semiringₓ R] : (center R).toSubmonoid = Submonoid.center R :=
  rfl

theorem mem_center_iff {R} [Semiringₓ R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter {R} [Semiringₓ R] [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidableOfIff' _ mem_center_iff

@[simp]
theorem center_eq_top R [CommSemiringₓ R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
instance {R} [Semiringₓ R] : CommSemiringₓ (center R) :=
  { Submonoid.center.commMonoid, (center R).toSemiring with }

end

/-- The `subsemiring` generated by a set. -/
def closure (s : Set R) : Subsemiring R :=
  inf { S | s ⊆ S }

theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The subsemiring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx

theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h => hP (subset_closure h)

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => Inf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure

theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymmₓ (closure_le.2 h₁) h₂

theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} : x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x

theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) : K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)

theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) : K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subsemiring

namespace Submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with one_mem' := AddSubmonoid.mem_closure.mpr fun y hy => hy M.one_mem,
    mul_mem' := fun x y => M.mul_mem_add_closure }

theorem subsemiring_closure_coe : (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl

theorem subsemiring_closure_to_add_submonoid : M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/-- The `subsemiring` generated by a multiplicative submonoid coincides with the
`subsemiring.closure` of the submonoid itself . -/
theorem subsemiring_closure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine' ⟨fun hx => _, fun hx => (subsemiring.mem_closure.mp hx) M.subsemiring_closure fun s sM => _⟩ <;>
    rintro - ⟨H1, rfl⟩ <;> rintro - ⟨H2, rfl⟩
  · exact add_submonoid.mem_closure.mp hx H1.to_add_submonoid H2
    
  · exact H2 sM
    

end Submonoid

namespace Subsemiring

@[simp]
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymmₓ (closure_le.mpr fun y hy => (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
theorem coe_closure_eq (s : Set R) : (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiring_closure_to_add_submonoid, Submonoid.subsemiring_closure_eq_closure]

theorem mem_closure_iff {s : Set R} {x} : x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
theorem closure_add_submonoid_closure {s : Set R} : closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine' ⟨fun hx => _, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine' (add_submonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.to_add_submonoid fun y hy => _
  refine' (submonoid.mem_closure.mp hy) H.to_submonoid fun z hz => _
  exact (add_submonoid.mem_closure.mp hz) H.to_add_submonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_eliminator]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀, ∀ x ∈ s, ∀, p x) (H0 : p 0)
    (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, H1, Hmul, H0, Hadd⟩).2 Hs h

theorem mem_closure_iff_exists_list {R} [Semiringₓ R] {s : Set R} {x} :
    x ∈ closure s ↔ ∃ L : List (List R), (∀, ∀ t ∈ L, ∀, ∀, ∀ y ∈ t, ∀, y ∈ s) ∧ (L.map List.prod).Sum = x :=
  ⟨fun hx =>
    AddSubmonoid.closure_induction (mem_closure_iff.1 hx)
      (fun x hx =>
        suffices ∃ t : List R, (∀, ∀ y ∈ t, ∀, y ∈ s) ∧ t.Prod = x from
          let ⟨t, ht1, ht2⟩ := this
          ⟨[t], List.forall_mem_singleton.2 ht1, by
            rw [List.map_singleton, List.sum_singleton, ht2]⟩
        Submonoid.closure_induction hx (fun x hx => ⟨[x], List.forall_mem_singleton.2 hx, one_mulₓ x⟩)
          ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨t, ht1, ht2⟩ ⟨u, hu1, hu2⟩ =>
          ⟨t ++ u, List.forall_mem_appendₓ.2 ⟨ht1, hu1⟩, by
            rw [List.prod_append, ht2, hu2]⟩)
      ⟨[], List.forall_mem_nil _, rfl⟩ fun x y ⟨L, HL1, HL2⟩ ⟨M, HM1, HM2⟩ =>
      ⟨L ++ M, List.forall_mem_appendₓ.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩,
    fun ⟨L, HL1, HL2⟩ =>
    HL2 ▸
      list_sum_mem _ fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_mapₓ.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => subset_closure <| HL1 t ht1 y hy⟩

variable (R)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) coe where
  choice := fun s _ => closure s
  gc := fun s t => closure_le
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {R}

/-- Closure of a subsemiring `S` equals `S`. -/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s

@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot

@[simp]
theorem closure_univ : closure (Set.Univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤

theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s⊔closure t :=
  (Subsemiring.gi R).gc.l_sup

theorem closure_Union {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_supr

theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀s) = ⨆ t ∈ s, closure t :=
  (Subsemiring.gi R).gc.l_Sup

theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s⊔t).map f = s.map f⊔t.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : R →+* S) (s : ι → Subsemiring R) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s⊓t).comap f = s.comap f⊓t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_infi {ι : Sort _} (f : R →+* S) (s : ι → Subsemiring S) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.Prod t.toSubmonoid, s.toAddSubmonoid.Prod t.toAddSubmonoid with
    Carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) : (s.Prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl

theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[mono]
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht

theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.Prod t :=
  prod_mono (le_reflₓ s)

theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.Prod t := fun s₁ s₂ hs =>
  prod_mono hs (le_reflₓ t)

theorem prod_top (s : Subsemiring R) : s.Prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by
    simp [mem_prod, MonoidHom.coe_fst]

theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).Prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by
    simp [mem_prod, MonoidHom.coe_snd]

@[simp]
theorem top_prod_top : (⊤ : Subsemiring R).Prod (⊤ : Subsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

/-- Product of subsemirings is isomorphic to their product as monoids. -/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.Prod t ≃+* s × t :=
  { Equivₓ.Set.prod ↑s ↑t with map_mul' := fun x y => rfl, map_add' := fun x y => rfl }

theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S) {x : R} :
    (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supr S i) hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid)
      (Submonoid.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id) (⨆ i, (S i).toAddSubmonoid)
      (AddSubmonoid.coe_supr_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by
    simpa using @this x
  exact supr_le fun i x hx => Set.mem_Union.2 ⟨i, hx⟩

theorem coe_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by
    simp [mem_supr_of_directed hS]

theorem mem_Sup_of_directed_on {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) {x : R} :
    x ∈ sup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, SetCoe.exists, Subtype.coe_mk]

theorem coe_Sup_of_directed_on {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S) :
    (↑(sup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by
    simp [mem_Sup_of_directed_on Sne hS]

end Subsemiring

namespace RingHom

variable [NonAssocSemiringₓ T] {s : Subsemiring R}

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the domain. -/
def srestrict (f : R →+* S) (s : Subsemiring R) : s →+* S :=
  f.comp s.Subtype

@[simp]
theorem srestrict_apply (f : R →+* S) (x : s) : f.srestrict s x = f x :=
  rfl

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
def codSrestrict (f : R →+* S) (s : Subsemiring S) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codMrestrict s.toSubmonoid h, (f : R →+ S).codMrestrict s.toAddSubmonoid h with
    toFun := fun n => ⟨f n, h n⟩ }

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `set.range_factorization`. -/
def srangeRestrict (f : R →+* S) : R →+* f.srange :=
  f.codSrestrict f.srange f.mem_srange_self

@[simp]
theorem coe_srange_restrict (f : R →+* S) (x : R) : (f.srangeRestrict x : S) = f x :=
  rfl

theorem srange_restrict_surjective (f : R →+* S) : Function.Surjective f.srangeRestrict := fun ⟨y, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩

theorem srange_top_iff_surjective {f : R →+* S} : f.srange = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <|
    Iff.trans
      (by
        rw [coe_srange, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem srange_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) : f.srange = (⊤ : Subsemiring S) :=
  srange_top_iff_surjective.2 hf

/-- The subsemiring of elements `x : R` such that `f x = g x` -/
def eqSlocus (f g : R →+* S) : Subsemiring R :=
  { (f : R →* S).eqMlocus g, (f : R →+ S).eqMlocus g with Carrier := { x | f x = g x } }

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
theorem eq_on_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqSlocus g from closure_le.2 h

theorem eq_of_eq_on_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun x => h trivialₓ

theorem eq_of_eq_on_sdense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) : f = g :=
  eq_of_eq_on_stop <| hs ▸ eq_on_sclosure h

theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
theorem map_sclosure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2 <| le_transₓ (closure_mono <| Set.subset_preimage_image _ _) (sclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)

end RingHom

namespace Subsemiring

open RingHom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →* T :=
  S.Subtype.codSrestrict _ fun x => h x.2

@[simp]
theorem srange_subtype (s : Subsemiring R) : s.Subtype.srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

@[simp]
theorem range_fst : (fst R S).srange = ⊤ :=
  (fst R S).srange_top_of_surjective <| Prod.fst_surjectiveₓ

@[simp]
theorem range_snd : (snd R S).srange = ⊤ :=
  (snd R S).srange_top_of_surjective <| Prod.snd_surjective

@[simp]
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) : s.Prod ⊥⊔prod ⊥ t = s.Prod t :=
  (le_antisymmₓ (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le))) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem _ ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥⊔prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥⊔prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
    monoid are equal. -/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  { Equivₓ.setCongr <| congr_argₓ _ h with map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.srange`. -/
def sofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.srange :=
  { f.srangeRestrict with toFun := fun x => f.srangeRestrict x, invFun := fun x => (g ∘ f.srange.Subtype) x,
    left_inv := h,
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_srange.mp x.Prop
        show f (g x) = x by
          rw [← hx', h x'] }

@[simp]
theorem sof_left_inverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(sofLeftInverse h x) = f x :=
  rfl

@[simp]
theorem sof_left_inverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : f.srange) :
    (sofLeftInverse h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiring_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps]
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map e.toRingHom :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

end RingEquiv

/-! ### Actions by `subsemiring`s

These are just copies of the definitions about `submonoid` starting from `submonoid.mul_action`.
The only new result is `subsemiring.module`.

When `R` is commutative, `algebra.of_subsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type _} [Semiringₓ R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  S.toSubmonoid.MulAction

theorem smul_def [MulAction R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl

instance smul_comm_class_left [MulAction R' β] [HasScalar α β] [SmulCommClass R' α β] (S : Subsemiring R') :
    SmulCommClass S α β :=
  S.toSubmonoid.smul_comm_class_left

instance smul_comm_class_right [HasScalar α β] [MulAction R' β] [SmulCommClass α R' β] (S : Subsemiring R') :
    SmulCommClass α S β :=
  S.toSubmonoid.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance [HasScalar α β] [MulAction R' α] [MulAction R' β] [IsScalarTower R' α β] (S : Subsemiring R') :
    IsScalarTower S α β :=
  S.toSubmonoid.IsScalarTower

instance [MulAction R' α] [HasFaithfulScalar R' α] (S : Subsemiring R') : HasFaithfulScalar S α :=
  S.toSubmonoid.HasFaithfulScalar

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [AddMonoidₓ α] [DistribMulAction R' α] (S : Subsemiring R') : DistribMulAction S α :=
  S.toSubmonoid.DistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [Monoidₓ α] [MulDistribMulAction R' α] (S : Subsemiring R') : MulDistribMulAction S α :=
  S.toSubmonoid.MulDistribMulAction

/-- The action by a subsemiring is the action by the underlying semiring. -/
instance [AddCommMonoidₓ α] [Module R' α] (S : Subsemiring R') : Module S α :=
  { Module.compHom _ S.Subtype with smul := (· • ·) }

end Subsemiring

end Actions

/-- Submonoid of positive elements of an ordered semiring. -/
-- While this definition is not about `subsemiring`s, this is the earliest we have
-- both `ordered_semiring` and `submonoid` available.
def posSubmonoid (R : Type _) [OrderedSemiring R] [Nontrivial R] : Submonoid R where
  Carrier := { x | 0 < x }
  one_mem' := show (0 : R) < 1 from zero_lt_one
  mul_mem' := fun hy : 0 < y => mul_pos hx hy

@[simp]
theorem mem_pos_monoid {R : Type _} [OrderedSemiring R] [Nontrivial R] (u : Rˣ) : ↑u ∈ posSubmonoid R ↔ (0 : R) < u :=
  Iff.rfl

