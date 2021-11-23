import Mathbin.GroupTheory.Submonoid.Basic 
import Mathbin.Data.Equiv.MulAdd 
import Mathbin.Algebra.Group.Prod 
import Mathbin.Algebra.Group.InjSurj 
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Operations on `submonoid`s

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `submonoid.to_add_submonoid`, `submonoid.to_add_submonoid'`, `add_submonoid.to_submonoid`,
  `add_submonoid.to_submonoid'`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) monoid structure on a submonoid

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `submonoid.mul_action`, `submonoid.distrib_mul_action`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `monoid_hom.mrestrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_mrestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/


variable{M N P : Type _}[MulOneClass M][MulOneClass N][MulOneClass P](S : Submonoid M)

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section 

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
@[simps]
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) :=
  { toFun := fun S => { Carrier := Additive.toMul ⁻¹' S, zero_mem' := S.one_mem', add_mem' := S.mul_mem' },
    invFun := fun S => { Carrier := Additive.ofMul ⁻¹' S, one_mem' := S.zero_mem', mul_mem' := S.add_mem' },
    left_inv :=
      fun x =>
        by 
          cases x <;> rfl,
    right_inv :=
      fun x =>
        by 
          cases x <;> rfl,
    map_rel_iff' := fun a b => Iff.rfl }

/-- Additive submonoids of an additive monoid `additive M` are isomorphic to submonoids of `M`. -/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm

theorem Submonoid.to_add_submonoid_closure (S : Set M) :
  (Submonoid.closure S).toAddSubmonoid = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymmₓ (Submonoid.toAddSubmonoid.le_symm_apply.1$ Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)

theorem AddSubmonoid.to_submonoid'_closure (S : Set (Additive M)) :
  (AddSubmonoid.closure S).toSubmonoid' = Submonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymmₓ (AddSubmonoid.toSubmonoid'.le_symm_apply.1$ AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)

end 

section 

variable{A : Type _}[AddZeroClass A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `multiplicative A`. -/
@[simps]
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) :=
  { toFun := fun S => { Carrier := Multiplicative.toAdd ⁻¹' S, one_mem' := S.zero_mem', mul_mem' := S.add_mem' },
    invFun := fun S => { Carrier := Multiplicative.ofAdd ⁻¹' S, zero_mem' := S.one_mem', add_mem' := S.mul_mem' },
    left_inv :=
      fun x =>
        by 
          cases x <;> rfl,
    right_inv :=
      fun x =>
        by 
          cases x <;> rfl,
    map_rel_iff' := fun a b => Iff.rfl }

/-- Submonoids of a monoid `multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm

theorem AddSubmonoid.to_submonoid_closure (S : Set A) :
  (AddSubmonoid.closure S).toSubmonoid = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymmₓ (AddSubmonoid.toSubmonoid.to_galois_connection.l_le$ AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)

theorem Submonoid.to_add_submonoid'_closure (S : Set (Multiplicative A)) :
  (Submonoid.closure S).toAddSubmonoid' = AddSubmonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymmₓ (Submonoid.toAddSubmonoid'.to_galois_connection.l_le$ Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)

end 

namespace Submonoid

open Set

/-!
### `comap` and `map`
-/


/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[toAdditive "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an\n`add_submonoid`."]
def comap (f : M →* N) (S : Submonoid N) : Submonoid M :=
  { Carrier := f ⁻¹' S,
    one_mem' :=
      show f 1 ∈ S by 
        rw [f.map_one] <;> exact S.one_mem,
    mul_mem' :=
      fun a b ha hb =>
        show f (a*b) ∈ S by 
          rw [f.map_mul] <;> exact S.mul_mem ha hb }

@[simp, toAdditive]
theorem coe_comap (S : Submonoid N) (f : M →* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[simp, toAdditive]
theorem mem_comap {S : Submonoid N} {f : M →* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

@[toAdditive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) : (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp, toAdditive]
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id _) = S :=
  ext
    (by 
      simp )

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[toAdditive "The image of an `add_submonoid` along an `add_monoid` homomorphism is\nan `add_submonoid`."]
def map (f : M →* N) (S : Submonoid M) : Submonoid N :=
  { Carrier := f '' S, one_mem' := ⟨1, S.one_mem, f.map_one⟩,
    mul_mem' :=
      by 
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact
          ⟨x*y, S.mul_mem hx hy,
            by 
              rw [f.map_mul] <;> rfl⟩ }

@[simp, toAdditive]
theorem coe_map (f : M →* N) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl

@[simp, toAdditive]
theorem mem_map {f : M →* N} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ (x : _)(_ : x ∈ S), f x = y :=
  mem_image_iff_bex

@[toAdditive]
theorem mem_map_of_mem (f : M →* N) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

@[toAdditive]
theorem apply_coe_mem_map (f : M →* N) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop

@[toAdditive]
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective$ image_image _ _ _

@[toAdditive]
theorem mem_map_iff_mem {f : M →* N} (hf : Function.Injective f) {S : Submonoid M} {x : M} : f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image

@[toAdditive]
theorem map_le_iff_le_comap {f : M →* N} {S : Submonoid M} {T : Submonoid N} : S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

@[toAdditive]
theorem gc_map_comap (f : M →* N) : GaloisConnection (map f) (comap f) :=
  fun S T => map_le_iff_le_comap

@[toAdditive]
theorem map_le_of_le_comap {T : Submonoid N} {f : M →* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

@[toAdditive]
theorem le_comap_of_map_le {T : Submonoid N} {f : M →* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

@[toAdditive]
theorem le_comap_map {f : M →* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[toAdditive]
theorem map_comap_le {S : Submonoid N} {f : M →* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

@[toAdditive]
theorem monotone_map {f : M →* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[toAdditive]
theorem monotone_comap {f : M →* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp, toAdditive]
theorem map_comap_map {f : M →* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp, toAdditive]
theorem comap_map_comap {S : Submonoid N} {f : M →* N} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[toAdditive]
theorem map_sup (S T : Submonoid M) (f : M →* N) : (S⊔T).map f = S.map f⊔T.map f :=
  (gc_map_comap f).l_sup

@[toAdditive]
theorem map_supr {ι : Sort _} (f : M →* N) (s : ι → Submonoid M) : (supr s).map f = ⨆i, (s i).map f :=
  (gc_map_comap f).l_supr

@[toAdditive]
theorem comap_inf (S T : Submonoid N) (f : M →* N) : (S⊓T).comap f = S.comap f⊓T.comap f :=
  (gc_map_comap f).u_inf

@[toAdditive]
theorem comap_infi {ι : Sort _} (f : M →* N) (s : ι → Submonoid N) : (infi s).comap f = ⨅i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp, toAdditive]
theorem map_bot (f : M →* N) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp, toAdditive]
theorem comap_top (f : M →* N) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp, toAdditive]
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable{ι : Type _}{f : M →* N}(hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[toAdditive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gci_map_comap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion
    fun S x =>
      by 
        simp [mem_comap, mem_map, hf.eq_iff]

@[toAdditive]
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gci_map_comap hf).u_l_eq _

@[toAdditive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gci_map_comap hf).u_surjective

@[toAdditive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gci_map_comap hf).l_injective

@[toAdditive]
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f⊓T.map f).comap f = S⊓T :=
  (gci_map_comap hf).u_inf_l _ _

@[toAdditive]
theorem comap_infi_map_of_injective (S : ι → Submonoid M) : (⨅i, (S i).map f).comap f = infi S :=
  (gci_map_comap hf).u_infi_l _

@[toAdditive]
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f⊔T.map f).comap f = S⊔T :=
  (gci_map_comap hf).u_sup_l _ _

@[toAdditive]
theorem comap_supr_map_of_injective (S : ι → Submonoid M) : (⨆i, (S i).map f).comap f = supr S :=
  (gci_map_comap hf).u_supr_l _

@[toAdditive]
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gci_map_comap hf).l_le_l_iff

@[toAdditive]
theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gci_map_comap hf).strict_mono_l

end GaloisCoinsertion

section GaloisInsertion

variable{ι : Type _}{f : M →* N}(hf : Function.Surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[toAdditive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def gi_map_comap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion
    fun S x h =>
      let ⟨y, hy⟩ := hf x 
      mem_map.2
        ⟨y,
          by 
            simp [hy, h]⟩

@[toAdditive]
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (gi_map_comap hf).l_u_eq _

@[toAdditive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (gi_map_comap hf).l_surjective

@[toAdditive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (gi_map_comap hf).u_injective

@[toAdditive]
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f⊓T.comap f).map f = S⊓T :=
  (gi_map_comap hf).l_inf_u _ _

@[toAdditive]
theorem map_infi_comap_of_surjective (S : ι → Submonoid N) : (⨅i, (S i).comap f).map f = infi S :=
  (gi_map_comap hf).l_infi_u _

@[toAdditive]
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f⊔T.comap f).map f = S⊔T :=
  (gi_map_comap hf).l_sup_u _ _

@[toAdditive]
theorem map_supr_comap_of_surjective (S : ι → Submonoid N) : (⨆i, (S i).comap f).map f = supr S :=
  (gi_map_comap hf).l_supr_u _

@[toAdditive]
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (gi_map_comap hf).u_le_u_iff

@[toAdditive]
theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (gi_map_comap hf).strict_mono_u

end GaloisInsertion

/-- A submonoid of a monoid inherits a multiplication. -/
@[toAdditive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance Mul : Mul S :=
  ⟨fun a b => ⟨a.1*b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[toAdditive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance HasOne : HasOne S :=
  ⟨⟨_, S.one_mem⟩⟩

@[simp, normCast, toAdditive]
theorem coe_mul (x y : S) : («expr↑ » (x*y) : M) = «expr↑ » x*«expr↑ » y :=
  rfl

@[simp, normCast, toAdditive]
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl

@[simp, toAdditive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) : ((⟨x, hx⟩ : S)*⟨y, hy⟩) = ⟨x*y, S.mul_mem hx hy⟩ :=
  rfl

@[toAdditive]
theorem mul_def (x y : S) : (x*y) = ⟨x*y, S.mul_mem x.2 y.2⟩ :=
  rfl

@[toAdditive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl

/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[toAdditive "An `add_submonoid` of an unital additive magma inherits an unital additive magma\nstructure."]
instance to_mul_one_class {M : Type _} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  Subtype.coe_injective.MulOneClass coeₓ rfl fun _ _ => rfl

/-- A submonoid of a monoid inherits a monoid structure. -/
@[toAdditive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance to_monoid {M : Type _} [Monoidₓ M] (S : Submonoid M) : Monoidₓ S :=
  Subtype.coe_injective.Monoid coeₓ rfl fun _ _ => rfl

/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[toAdditive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance to_comm_monoid {M} [CommMonoidₓ M] (S : Submonoid M) : CommMonoidₓ S :=
  Subtype.coe_injective.CommMonoid coeₓ rfl fun _ _ => rfl

/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
@[toAdditive "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance to_ordered_comm_monoid {M} [OrderedCommMonoid M] (S : Submonoid M) : OrderedCommMonoid S :=
  Subtype.coe_injective.OrderedCommMonoid coeₓ rfl fun _ _ => rfl

/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
@[toAdditive "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is\na `linear_ordered_add_comm_monoid`."]
instance to_linear_ordered_comm_monoid {M} [LinearOrderedCommMonoid M] (S : Submonoid M) : LinearOrderedCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCommMonoid coeₓ rfl fun _ _ => rfl

/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
@[toAdditive "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is\nan `ordered_cancel_add_comm_monoid`."]
instance to_ordered_cancel_comm_monoid {M} [OrderedCancelCommMonoid M] (S : Submonoid M) : OrderedCancelCommMonoid S :=
  Subtype.coe_injective.OrderedCancelCommMonoid coeₓ rfl fun _ _ => rfl

/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
@[toAdditive
      "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is\na `linear_ordered_cancel_add_comm_monoid`."]
instance to_linear_ordered_cancel_comm_monoid {M} [LinearOrderedCancelCommMonoid M] (S : Submonoid M) :
  LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelCommMonoid coeₓ rfl fun _ _ => rfl

/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[toAdditive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def Subtype : S →* M :=
  ⟨coeₓ, rfl, fun _ _ => rfl⟩

@[simp, toAdditive]
theorem coeSubtype : «expr⇑ » S.subtype = coeₓ :=
  rfl

/-- A submonoid is isomorphic to its image under an injective function -/
@[toAdditive "An additive submonoid is isomorphic to its image under an injective function"]
noncomputable def equiv_map_of_injective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[simp, toAdditive]
theorem coe_equiv_map_of_injective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
  (equiv_map_of_injective S f hf x : N) = f x :=
  rfl

/-- An induction principle on elements of the type `submonoid.closure s`.
If `p` holds for `1` and all elements of `s`, and is preserved under multiplication, then `p`
holds for all elements of the closure of `s`.

The difference with `submonoid.closure_induction` is that this acts on the subtype.
-/
@[elab_as_eliminator,
  toAdditive
      "An induction principle on elements of the type\n`add_submonoid.closure s`.  If `p` holds for `0` and all elements of `s`, and is preserved under\naddition, then `p` holds for all elements of the closure of `s`.\n\nThe difference with `add_submonoid.closure_induction` is that this acts on the subtype."]
theorem closure_induction' (s : Set M) {p : closure s → Prop} (Hs : ∀ x h : x ∈ s, p ⟨x, subset_closure h⟩) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x*y)) (x : closure s) : p x :=
  Subtype.recOn x$
    fun x hx =>
      by 
        refine' Exists.elim _ fun hx : x ∈ closure s hc : p ⟨x, hx⟩ => hc 
        exact
          closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) ⟨one_mem _, H1⟩
            fun x y hx hy =>
              Exists.elim hx$ fun hx' hx => Exists.elim hy$ fun hy' hy => ⟨mul_mem _ hx' hy', Hmul _ _ hx hy⟩

/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[toAdditive Prod
      "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`\nas an `add_submonoid` of `A × B`."]
def Prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N) :=
  { Carrier := (s : Set M).Prod t, one_mem' := ⟨s.one_mem, t.one_mem⟩,
    mul_mem' := fun p q hp hq => ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩ }

@[toAdditive coe_prod]
theorem coe_prod (s : Submonoid M) (t : Submonoid N) : (s.prod t : Set (M × N)) = (s : Set M).Prod (t : Set N) :=
  rfl

@[toAdditive mem_prod]
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[toAdditive prod_mono]
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht

@[toAdditive prod_top]
theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext$
    fun x =>
      by 
        simp [mem_prod, MonoidHom.coe_fst]

@[toAdditive top_prod]
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).Prod s = s.comap (MonoidHom.snd M N) :=
  ext$
    fun x =>
      by 
        simp [mem_prod, MonoidHom.coe_snd]

@[simp, toAdditive top_prod_top]
theorem top_prod_top : (⊤ : Submonoid M).Prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans$ comap_top _

@[toAdditive]
theorem bot_prod_bot : (⊥ : Submonoid M).Prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective$
    by 
      simp [coe_prod, Prod.one_eq_mk]

/-- The product of submonoids is isomorphic to their product as monoids. -/
@[toAdditive prod_equiv "The product of additive submonoids is isomorphic to their product\nas additive monoids"]
def prod_equiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { Equiv.Set.prod («expr↑ » s) («expr↑ » t) with map_mul' := fun x y => rfl }

open MonoidHom

@[toAdditive]
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ :=
  ext$
    fun p =>
      ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩,
        fun ⟨hps, hp1⟩ => ⟨p.1, hps, Prod.extₓ rfl$ (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[toAdditive]
theorem map_inr (s : Submonoid N) : s.map (inr M N) = Prod ⊥ s :=
  ext$
    fun p =>
      ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩,
        fun ⟨hp1, hps⟩ => ⟨p.2, hps, Prod.extₓ (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[simp, toAdditive prod_bot_sup_bot_prod]
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) : s.prod ⊥⊔Prod ⊥ t = s.prod t :=
  le_antisymmₓ (sup_le (prod_mono (le_reflₓ s) bot_le) (prod_mono bot_le (le_reflₓ t)))$
    fun p hp =>
      Prod.fst_mul_snd p ▸
        mul_mem _ ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥⊔Prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
          ((le_sup_right : Prod ⊥ t ≤ s.prod ⊥⊔Prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

@[toAdditive]
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} : x ∈ K.map f.to_monoid_hom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ («expr↑ » K) f.to_equiv x

@[toAdditive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) : K.map f.to_monoid_hom = K.comap f.symm.to_monoid_hom :=
  SetLike.coe_injective (f.to_equiv.image_eq_preimage K)

@[toAdditive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) : K.comap f.to_monoid_hom = K.map f.symm.to_monoid_hom :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Submonoid

namespace MonoidHom

open Submonoid

/-- For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`set.range f`. In particular this means that the types `↥(set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`set.range` could have been defined as `f '' set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `set.range`, and that it introduces a redudant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`monoid_hom.mrange` would be `(⊤ : submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `submonoid.copy` as follows:
```lean
protected def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier  := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : submonoid N :=
((⊤ : submonoid M).map f).copy (set.range f) set.image_univ.symm
```
-/
library_note "range copy pattern"

/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[toAdditive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : M →* N) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.Range f) Set.image_univ.symm

@[simp, toAdditive]
theorem coe_mrange (f : M →* N) : (f.mrange : Set N) = Set.Range f :=
  rfl

@[simp, toAdditive]
theorem mem_mrange {f : M →* N} {y : N} : y ∈ f.mrange ↔ ∃ x, f x = y :=
  Iff.rfl

@[toAdditive]
theorem mrange_eq_map (f : M →* N) : f.mrange = (⊤ : Submonoid M).map f :=
  copy_eq _

@[toAdditive]
theorem map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange :=
  by 
    simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f

@[toAdditive]
theorem mrange_top_iff_surjective {N} [MulOneClass N] {f : M →* N} :
  f.mrange = (⊤ : Submonoid N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans$
    Iff.trans
      (by 
        rw [coe_mrange, coe_top])
      Set.range_iff_surjective

/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[toAdditive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
theorem mrange_top_of_surjective {N} [MulOneClass N] (f : M →* N) (hf : Function.Surjective f) :
  f.mrange = (⊤ : Submonoid N) :=
  mrange_top_iff_surjective.2 hf

@[toAdditive]
theorem mclosure_preimage_le (f : M →* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2$ fun x hx => SetLike.mem_coe.2$ mem_comap.2$ subset_closure hx

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[toAdditive
      "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals\nthe `add_submonoid` generated by the image of the set."]
theorem map_mclosure (f : M →* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymmₓ
    (map_le_iff_le_comap.2$ le_transₓ (closure_mono$ Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2$ Set.image_subset _ subset_closure)

/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[toAdditive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def mrestrict {N : Type _} [MulOneClass N] (f : M →* N) (S : Submonoid M) : S →* N :=
  f.comp S.subtype

@[simp, toAdditive]
theorem mrestrict_apply {N : Type _} [MulOneClass N] (f : M →* N) (x : S) : f.mrestrict S x = f x :=
  rfl

/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[toAdditive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain.", simps]
def cod_mrestrict (f : M →* N) (S : Submonoid N) (h : ∀ x, f x ∈ S) : M →* S :=
  { toFun := fun n => ⟨f n, h n⟩, map_one' := Subtype.eq f.map_one, map_mul' := fun x y => Subtype.eq (f.map_mul x y) }

/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[toAdditive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrange_restrict {N} [MulOneClass N] (f : M →* N) : M →* f.mrange :=
  f.cod_mrestrict f.mrange$ fun x => ⟨x, rfl⟩

@[simp, toAdditive]
theorem coe_mrange_restrict {N} [MulOneClass N] (f : M →* N) (x : M) : (f.mrange_restrict x : N) = f x :=
  rfl

/-- The multiplicative kernel of a monoid homomorphism is the submonoid of elements `x : G` such
that `f x = 1` -/
@[toAdditive
      "The additive kernel of an `add_monoid` homomorphism is the `add_submonoid` of\nelements such that `f x = 0`"]
def mker (f : M →* N) : Submonoid M :=
  (⊥ : Submonoid N).comap f

@[toAdditive]
theorem mem_mker (f : M →* N) {x : M} : x ∈ f.mker ↔ f x = 1 :=
  Iff.rfl

@[toAdditive]
theorem coe_mker (f : M →* N) : (f.mker : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl

@[toAdditive]
instance decidable_mem_mker [DecidableEq N] (f : M →* N) : DecidablePred (· ∈ f.mker) :=
  fun x => decidableOfIff (f x = 1) f.mem_mker

@[toAdditive]
theorem comap_mker (g : N →* P) (f : M →* N) : g.mker.comap f = (g.comp f).mker :=
  rfl

@[simp, toAdditive]
theorem comap_bot' (f : M →* N) : (⊥ : Submonoid N).comap f = f.mker :=
  rfl

@[toAdditive]
theorem range_restrict_mker (f : M →* N) : mker (mrange_restrict f) = mker f :=
  by 
    ext 
    change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
    simp only 

@[simp, toAdditive]
theorem mker_one : (1 : M →* N).mker = ⊤ :=
  by 
    ext 
    simp [mem_mker]

@[toAdditive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] (f : M →* N) (g : M' →* N')
  (S : Submonoid N) (S' : Submonoid N') : (S.prod S').comap (prod_mapₓ f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective$ Set.preimage_prod_map_prod f g _ _

@[toAdditive]
theorem mker_prod_map {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] (f : M →* N) (g : M' →* N') :
  (prod_mapₓ f g).mker = f.mker.prod g.mker :=
  by 
    rw [←comap_bot', ←comap_bot', ←comap_bot', ←prod_map_comap_prod', bot_prod_bot]

end MonoidHom

namespace Submonoid

open MonoidHom

@[toAdditive]
theorem mrange_inl : (inl M N).mrange = Prod ⊤ ⊥ :=
  by 
    simpa only [mrange_eq_map] using map_inl ⊤

@[toAdditive]
theorem mrange_inr : (inr M N).mrange = Prod ⊥ ⊤ :=
  by 
    simpa only [mrange_eq_map] using map_inr ⊤

@[toAdditive]
theorem mrange_inl' : (inl M N).mrange = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)

@[toAdditive]
theorem mrange_inr' : (inr M N).mrange = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)

@[simp, toAdditive]
theorem mrange_fst : (fst M N).mrange = ⊤ :=
  (fst M N).mrange_top_of_surjective$ @Prod.fst_surjectiveₓ _ _ ⟨1⟩

@[simp, toAdditive]
theorem mrange_snd : (snd M N).mrange = ⊤ :=
  (snd M N).mrange_top_of_surjective$ @Prod.snd_surjective _ _ ⟨1⟩

@[simp, toAdditive]
theorem mrange_inl_sup_mrange_inr : (inl M N).mrange⊔(inr M N).mrange = ⊤ :=
  by 
    simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

/-- The monoid hom associated to an inclusion of submonoids. -/
@[toAdditive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.subtype.cod_mrestrict _ fun x => h x.2

@[simp, toAdditive]
theorem range_subtype (s : Submonoid M) : s.subtype.mrange = s :=
  SetLike.coe_injective$ (coe_mrange _).trans$ Subtype.range_coe

@[toAdditive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h$ mem_top m, fun h m _ => h m⟩

-- error in GroupTheory.Submonoid.Operations: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem eq_bot_iff_forall : «expr ↔ »(«expr = »(S, «expr⊥»()), ∀ x «expr ∈ » S, «expr = »(x, (1 : M))) :=
«expr $ »(set_like.ext_iff.trans, by simp [] [] [] ["[", expr iff_def, ",", expr S.one_mem, "]"] [] [] { contextual := tt })

@[toAdditive]
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ (x : _)(_ : x ∈ S), x ≠ (1 : M) :=
  calc Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _)(hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists 
    _ ↔ ∃ (x : _)(_ : x ∈ S), x ≠ (1 : M) :=
    by 
      simp only [Ne.def]
    

/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[toAdditive]
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S :=
  by 
    simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ←not_forall, Classical.em]

/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[toAdditive]
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ (x : _)(_ : x ∈ S), x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

end Submonoid

namespace MulEquiv

variable{S}{T : Submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[toAdditive "Makes the identity additive isomorphism from a proof two\nsubmonoids of an additive monoid are equal."]
def submonoid_congr (h : S = T) : S ≃* T :=
  { Equiv.setCongr$ congr_argₓ _ h with map_mul' := fun _ _ => rfl }

/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `monoid_hom.mrange_restrict`. -/
@[toAdditive
      "\nAn additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.mrange`.\n\nThis is a bidirectional version of `add_monoid_hom.mrange_restrict`. ",
  simps (config := { simpRhs := tt })]
def of_left_inverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.mrange :=
  { f.mrange_restrict with toFun := f.mrange_restrict, invFun := g ∘ f.mrange.subtype, left_inv := h,
    right_inv :=
      fun x =>
        Subtype.ext$
          let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.prop 
          show f (g x) = x by 
            rw [←hx', h x'] }

/-- A `mul_equiv` `φ` between two monoids `M` and `N` induces a `mul_equiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. -/
@[toAdditive
      "An `add_equiv` `φ` between two additive monoids `M` and `N` induces an `add_equiv`\nbetween a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. ",
  simps]
def submonoid_equiv_map (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e.to_monoid_hom :=
  { Equiv.image e.to_equiv S with toFun := fun x => ⟨e x, _⟩, invFun := fun x => ⟨e.symm x, _⟩,
    map_mul' := fun _ _ => Subtype.ext (e.map_mul _ _) }

end MulEquiv

section Actions

/-! ### Actions by `submonoid`s

These instances tranfer the action by an element `m : M` of a monoid `M` written as `m • a` onto the
action by an element `s : S` of a submonoid `S : submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `monoid.to_mul_action`, enabling
`s • m` as an alias for `↑s * m`.
-/


namespace Submonoid

variable{M' : Type _}{α β : Type _}[Monoidₓ M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[toAdditive "The additive action by an add_submonoid is the action by the underlying\nadd_monoid. "]
instance  [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  MulAction.compHom _ S.subtype

@[toAdditive]
theorem smul_def [MulAction M' α] {S : Submonoid M'} (g : S) (m : α) : g • m = (g : M') • m :=
  rfl

/-- The action by a submonoid is the action by the underlying monoid. -/
instance  [AddMonoidₓ α] [DistribMulAction M' α] (S : Submonoid M') : DistribMulAction S α :=
  DistribMulAction.compHom _ S.subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance  [Monoidₓ α] [MulDistribMulAction M' α] (S : Submonoid M') : MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.subtype

@[toAdditive]
instance smul_comm_class_left [MulAction M' β] [HasScalar α β] [SmulCommClass M' α β] (S : Submonoid M') :
  SmulCommClass S α β :=
  ⟨fun a => (smul_comm (a : M') : _)⟩

@[toAdditive]
instance smul_comm_class_right [HasScalar α β] [MulAction M' β] [SmulCommClass α M' β] (S : Submonoid M') :
  SmulCommClass α S β :=
  ⟨fun a s => (smul_comm a (s : M') : _)⟩

/-- Note that this provides `is_scalar_tower S M' M'` which is needed by `smul_mul_assoc`. -/
instance  [HasScalar α β] [MulAction M' α] [MulAction M' β] [IsScalarTower M' α β] (S : Submonoid M') :
  IsScalarTower S α β :=
  ⟨fun a => (smul_assoc (a : M') : _)⟩

example  {S : Submonoid M'} : IsScalarTower S M' M' :=
  by 
    infer_instance

instance  [MulAction M' α] [HasFaithfulScalar M' α] (S : Submonoid M') : HasFaithfulScalar S α :=
  { eq_of_smul_eq_smul := fun x y h => Subtype.ext (eq_of_smul_eq_smul h) }

end Submonoid

end Actions

