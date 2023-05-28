/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.hom.freiman
! leanprover-community/mathlib commit 68d1483e8a718ec63219f0e227ca3f0140361086
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Multiset.Basic
import Mathbin.Data.FunLike.Basic

/-!
# Freiman homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define Freiman homomorphisms. A `n`-Freiman homomorphism on `A` is a function
`f : α → β` such that `f (x₁) * ... * f (xₙ) = f (y₁) * ... * f (yₙ)` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that `x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any
`mul_hom` is a Freiman homomorphism.

They are of interest in additive combinatorics.

## Main declaration

* `freiman_hom`: Freiman homomorphism.
* `add_freiman_hom`: Additive Freiman homomorphism.

## Notation

* `A →*[n] β`: Multiplicative `n`-Freiman homomorphism on `A`
* `A →+[n] β`: Additive `n`-Freiman homomorphism on `A`

## Implementation notes

In the context of combinatorics, we are interested in Freiman homomorphisms over sets which are not
necessarily closed under addition/multiplication. This means we must parametrize them with a set in
an `add_monoid`/`monoid` instead of the `add_monoid`/`monoid` itself.

## References

[Yufei Zhao, *18.225: Graph Theory and Additive Combinatorics*](https://yufeizhao.com/gtac/)

## TODO

`monoid_hom.to_freiman_hom` could be relaxed to `mul_hom.to_freiman_hom` by proving
`(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.

Define `n`-Freiman isomorphisms.

Affine maps induce Freiman homs. Concretely, provide the `add_freiman_hom_class (α →ₐ[𝕜] β) A β n`
instance.
-/


open Multiset

variable {F α β γ δ G : Type _}

#print AddFreimanHom /-
/-- An additive `n`-Freiman homomorphism is a map which preserves sums of `n` elements. -/
structure AddFreimanHom (A : Set α) (β : Type _) [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) where
  toFun : α → β
  map_sum_eq_map_sum' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : s.card = n) (ht : t.card = n) (h : s.Sum = t.Sum) :
    (s.map to_fun).Sum = (t.map to_fun).Sum
#align add_freiman_hom AddFreimanHom
-/

#print FreimanHom /-
/-- A `n`-Freiman homomorphism on a set `A` is a map which preserves products of `n` elements. -/
@[to_additive AddFreimanHom]
structure FreimanHom (A : Set α) (β : Type _) [CommMonoid α] [CommMonoid β] (n : ℕ) where
  toFun : α → β
  map_prod_eq_map_prod' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : s.card = n) (ht : t.card = n) (h : s.Prod = t.Prod) :
    (s.map to_fun).Prod = (t.map to_fun).Prod
#align freiman_hom FreimanHom
#align add_freiman_hom AddFreimanHom
-/

-- mathport name: add_freiman_hom
notation:25 A " →+[" n:25 "] " β:0 => AddFreimanHom A β n

-- mathport name: freiman_hom
notation:25 A " →*[" n:25 "] " β:0 => FreimanHom A β n

#print AddFreimanHomClass /-
/-- `add_freiman_hom_class F s β n` states that `F` is a type of `n`-ary sums-preserving morphisms.
You should extend this class when you extend `add_freiman_hom`. -/
class AddFreimanHomClass (F : Type _) (A : outParam <| Set α) (β : outParam <| Type _)
  [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) [FunLike F α fun _ => β] : Prop where
  map_sum_eq_map_sum' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
    (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n) (h : s.Sum = t.Sum) :
    (s.map f).Sum = (t.map f).Sum
#align add_freiman_hom_class AddFreimanHomClass
-/

#print FreimanHomClass /-
/-- `freiman_hom_class F A β n` states that `F` is a type of `n`-ary products-preserving morphisms.
You should extend this class when you extend `freiman_hom`. -/
@[to_additive AddFreimanHomClass
      "`add_freiman_hom_class F A β n` states that `F` is a type of `n`-ary sums-preserving morphisms.\nYou should extend this class when you extend `add_freiman_hom`."]
class FreimanHomClass (F : Type _) (A : outParam <| Set α) (β : outParam <| Type _) [CommMonoid α]
  [CommMonoid β] (n : ℕ) [FunLike F α fun _ => β] : Prop where
  map_prod_eq_map_prod' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
    (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n) (h : s.Prod = t.Prod) :
    (s.map f).Prod = (t.map f).Prod
#align freiman_hom_class FreimanHomClass
#align add_freiman_hom_class AddFreimanHomClass
-/

variable [FunLike F α fun _ => β]

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [CommMonoid γ] [CommMonoid δ] [CommGroup G] {A : Set α}
  {B : Set β} {C : Set γ} {n : ℕ} {a b c d : α}

/- warning: map_prod_eq_map_prod -> map_prod_eq_map_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align map_prod_eq_map_prod map_prod_eq_map_prodₓ'. -/
@[to_additive]
theorem map_prod_eq_map_prod [FreimanHomClass F A β n] (f : F) {s t : Multiset α}
    (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n)
    (h : s.Prod = t.Prod) : (s.map f).Prod = (t.map f).Prod :=
  FreimanHomClass.map_prod_eq_map_prod' f hsA htA hs ht h
#align map_prod_eq_map_prod map_prod_eq_map_prod
#align map_sum_eq_map_sum map_sum_eq_map_sum

/- warning: map_mul_map_eq_map_mul_map -> map_mul_map_eq_map_mul_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : FunLike.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β)] [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u3} β] {A : Set.{u2} α} {a : α} {b : α} {c : α} {d : α} [_inst_7 : FreimanHomClass.{u2, u1, u3} α F A β _inst_2 _inst_3 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) _inst_1] (f : F), (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) a A) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) b A) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) c A) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) d A) -> (Eq.{succ u2} α (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)))) a b) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)))) c d)) -> (Eq.{succ u3} β (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_3)))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_1) f a) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_1) f b)) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_3)))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_1) f c) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) _inst_1) f d)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : FunLike.{succ u2, succ u3, succ u1} F α (fun (_x : α) => β)] [_inst_2 : CommMonoid.{u3} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u3} α} {a : α} {b : α} {c : α} {d : α} [_inst_7 : FreimanHomClass.{u3, u2, u1} α F A β _inst_2 _inst_3 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) _inst_1] (f : F), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a A) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) b A) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) c A) -> (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) d A) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_2)))) a b) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_2)))) c d)) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) (CommMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) a) _inst_3)))) (FunLike.coe.{succ u2, succ u3, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) _x) _inst_1 f a) (FunLike.coe.{succ u2, succ u3, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) _x) _inst_1 f b)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) d) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) (CommMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) c) _inst_3)))) (FunLike.coe.{succ u2, succ u3, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) _x) _inst_1 f c) (FunLike.coe.{succ u2, succ u3, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2158 : α) => β) _x) _inst_1 f d)))
Case conversion may be inaccurate. Consider using '#align map_mul_map_eq_map_mul_map map_mul_map_eq_map_mul_mapₓ'. -/
@[to_additive]
theorem map_mul_map_eq_map_mul_map [FreimanHomClass F A β 2] (f : F) (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hd : d ∈ A) (h : a * b = c * d) : f a * f b = f c * f d :=
  by
  simp_rw [← prod_pair] at h⊢
  refine' map_prod_eq_map_prod f _ _ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]
#align map_mul_map_eq_map_mul_map map_mul_map_eq_map_mul_map
#align map_add_map_eq_map_add_map map_add_map_eq_map_add_map

namespace FreimanHom

#print FreimanHom.funLike /-
@[to_additive]
instance funLike : FunLike (A →*[n] β) α fun _ => β
    where
  coe := toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
#align freiman_hom.fun_like FreimanHom.funLike
#align add_freiman_hom.fun_like AddFreimanHom.funLike
-/

#print FreimanHom.freimanHomClass /-
@[to_additive]
instance freimanHomClass : FreimanHomClass (A →*[n] β) A β n
    where map_prod_eq_map_prod' := map_prod_eq_map_prod'
#align freiman_hom.freiman_hom_class FreimanHom.freimanHomClass
#align add_freiman_hom.freiman_hom_class AddFreimanHom.addFreimanHomClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun` directly."]
instance : CoeFun (A →*[n] β) fun _ => α → β :=
  ⟨toFun⟩

initialize_simps_projections FreimanHom (toFun → apply)

/- warning: freiman_hom.to_fun_eq_coe -> FreimanHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n), Eq.{max (succ u1) (succ u2)} (α -> β) (FreimanHom.toFun.{u1, u2} α A β _inst_2 _inst_3 n f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat} (f : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n), Eq.{max (succ u2) (succ u1)} (α -> β) (FreimanHom.toFun.{u2, u1} α A β _inst_2 _inst_3 n f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) f)
Case conversion may be inaccurate. Consider using '#align freiman_hom.to_fun_eq_coe FreimanHom.toFun_eq_coeₓ'. -/
@[simp, to_additive]
theorem toFun_eq_coe (f : A →*[n] β) : f.toFun = f :=
  rfl
#align freiman_hom.to_fun_eq_coe FreimanHom.toFun_eq_coe
#align add_freiman_hom.to_fun_eq_coe AddFreimanHom.toFun_eq_coe

/- warning: freiman_hom.ext -> FreimanHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} {{f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n}} {{g : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n}}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g x)) -> (Eq.{max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat} {{f : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n}} {{g : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n}}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) g x)) -> (Eq.{max (succ u2) (succ u1)} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) f g)
Case conversion may be inaccurate. Consider using '#align freiman_hom.ext FreimanHom.extₓ'. -/
@[ext, to_additive]
theorem ext ⦃f g : A →*[n] β⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align freiman_hom.ext FreimanHom.ext
#align add_freiman_hom.ext AddFreimanHom.ext

/- warning: freiman_hom.coe_mk -> FreimanHom.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.coe_mk FreimanHom.coe_mkₓ'. -/
@[simp, to_additive]
theorem coe_mk (f : α → β)
    (h :
      ∀ s t : Multiset α,
        (∀ ⦃x⦄, x ∈ s → x ∈ A) →
          (∀ ⦃x⦄, x ∈ t → x ∈ A) →
            s.card = n → t.card = n → s.Prod = t.Prod → (s.map f).Prod = (t.map f).Prod) :
    ⇑(mk f h) = f :=
  rfl
#align freiman_hom.coe_mk FreimanHom.coe_mk
#align add_freiman_hom.coe_mk AddFreimanHom.coe_mk

/- warning: freiman_hom.mk_coe -> FreimanHom.mk_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.mk_coe FreimanHom.mk_coeₓ'. -/
@[simp, to_additive]
theorem mk_coe (f : A →*[n] β) (h) : mk f h = f :=
  ext fun _ => rfl
#align freiman_hom.mk_coe FreimanHom.mk_coe
#align add_freiman_hom.mk_coe AddFreimanHom.mk_coe

#print FreimanHom.id /-
/-- The identity map from a commutative monoid to itself. -/
@[to_additive "The identity map from an additive commutative monoid to itself.", simps]
protected def id (A : Set α) (n : ℕ) : A →*[n] α
    where
  toFun x := x
  map_prod_eq_map_prod' s t _ _ _ _ h := by rw [map_id', map_id', h]
#align freiman_hom.id FreimanHom.id
#align add_freiman_hom.id AddFreimanHom.id
-/

#print FreimanHom.comp /-
/-- Composition of Freiman homomorphisms as a Freiman homomorphism. -/
@[to_additive "Composition of additive Freiman homomorphisms as an additive Freiman homomorphism."]
protected def comp (f : B →*[n] γ) (g : A →*[n] β) (hAB : A.MapsTo g B) : A →*[n] γ
    where
  toFun := f ∘ g
  map_prod_eq_map_prod' s t hsA htA hs ht h :=
    by
    rw [← map_map,
      map_prod_eq_map_prod f _ _ ((s.card_map _).trans hs) ((t.card_map _).trans ht)
        (map_prod_eq_map_prod g hsA htA hs ht h),
      map_map]
    · simpa using fun a h => hAB (hsA h)
    · simpa using fun a h => hAB (htA h)
#align freiman_hom.comp FreimanHom.comp
#align add_freiman_hom.comp AddFreimanHom.comp
-/

/- warning: freiman_hom.coe_comp -> FreimanHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u3} γ] {A : Set.{u1} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) (g : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hfg : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g) A B}, Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) (fun (_x : FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) => α -> γ) (FreimanHom.hasCoeToFun.{u1, u3} α γ _inst_2 _inst_4 A n) (FreimanHom.comp.{u1, u2, u3} α β γ _inst_2 _inst_3 _inst_4 A B n f g hfg)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) (fun (_x : FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) => β -> γ) (FreimanHom.hasCoeToFun.{u2, u3} β γ _inst_3 _inst_4 B n) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u3} β] [_inst_4 : CommMonoid.{u2} γ] {A : Set.{u1} α} {B : Set.{u3} β} {n : Nat} (f : FreimanHom.{u3, u2} β B γ _inst_3 _inst_4 n) (g : FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) {hfg : Set.MapsTo.{u1, u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g) A B}, Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FreimanHom.{u1, u2} α A γ _inst_2 _inst_4 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => γ) _x) (FreimanHom.funLike.{u1, u2} α γ _inst_2 _inst_4 A n) (FreimanHom.comp.{u1, u3, u2} α β γ _inst_2 _inst_3 _inst_4 A B n f g hfg)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FreimanHom.{u3, u2} β B γ _inst_3 _inst_4 n) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : β) => γ) _x) (FreimanHom.funLike.{u3, u2} β γ _inst_3 _inst_4 B n) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g))
Case conversion may be inaccurate. Consider using '#align freiman_hom.coe_comp FreimanHom.coe_compₓ'. -/
@[simp, to_additive]
theorem coe_comp (f : B →*[n] γ) (g : A →*[n] β) {hfg} : ⇑(f.comp g hfg) = f ∘ g :=
  rfl
#align freiman_hom.coe_comp FreimanHom.coe_comp
#align add_freiman_hom.coe_comp AddFreimanHom.coe_comp

/- warning: freiman_hom.comp_apply -> FreimanHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u3} γ] {A : Set.{u1} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) (g : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hfg : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g) A B} (x : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) (fun (_x : FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) => α -> γ) (FreimanHom.hasCoeToFun.{u1, u3} α γ _inst_2 _inst_4 A n) (FreimanHom.comp.{u1, u2, u3} α β γ _inst_2 _inst_3 _inst_4 A B n f g hfg) x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) (fun (_x : FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) => β -> γ) (FreimanHom.hasCoeToFun.{u2, u3} β γ _inst_3 _inst_4 B n) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u3} β] [_inst_4 : CommMonoid.{u2} γ] {A : Set.{u1} α} {B : Set.{u3} β} {n : Nat} (f : FreimanHom.{u3, u2} β B γ _inst_3 _inst_4 n) (g : FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) {hfg : Set.MapsTo.{u1, u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g) A B} (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => γ) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FreimanHom.{u1, u2} α A γ _inst_2 _inst_4 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => γ) _x) (FreimanHom.funLike.{u1, u2} α γ _inst_2 _inst_4 A n) (FreimanHom.comp.{u1, u3, u2} α β γ _inst_2 _inst_3 _inst_4 A B n f g hfg) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FreimanHom.{u3, u2} β B γ _inst_3 _inst_4 n) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : β) => γ) _x) (FreimanHom.funLike.{u3, u2} β γ _inst_3 _inst_4 B n) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g x))
Case conversion may be inaccurate. Consider using '#align freiman_hom.comp_apply FreimanHom.comp_applyₓ'. -/
@[to_additive]
theorem comp_apply (f : B →*[n] γ) (g : A →*[n] β) {hfg} (x : α) : f.comp g hfg x = f (g x) :=
  rfl
#align freiman_hom.comp_apply FreimanHom.comp_apply
#align add_freiman_hom.comp_apply AddFreimanHom.comp_apply

/- warning: freiman_hom.comp_assoc -> FreimanHom.comp_assoc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.comp_assoc FreimanHom.comp_assocₓ'. -/
@[to_additive]
theorem comp_assoc (f : A →*[n] β) (g : B →*[n] γ) (h : C →*[n] δ) {hf hhg hgf}
    {hh : A.MapsTo (g.comp f hgf) C} : (h.comp g hhg).comp f hf = h.comp (g.comp f hgf) hh :=
  rfl
#align freiman_hom.comp_assoc FreimanHom.comp_assoc
#align add_freiman_hom.comp_assoc AddFreimanHom.comp_assoc

/- warning: freiman_hom.cancel_right -> FreimanHom.cancel_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.cancel_right FreimanHom.cancel_rightₓ'. -/
@[to_additive]
theorem cancel_right {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : Function.Surjective f) {hg₁ hg₂} :
    g₁.comp f hg₁ = g₂.comp f hg₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => h ▸ rfl⟩
#align freiman_hom.cancel_right FreimanHom.cancel_right
#align add_freiman_hom.cancel_right AddFreimanHom.cancel_right

/- warning: freiman_hom.cancel_right_on -> FreimanHom.cancel_right_on is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.cancel_right_on FreimanHom.cancel_right_onₓ'. -/
@[to_additive]
theorem cancel_right_on {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : A.SurjOn f B) {hf'} :
    A.EqOn (g₁.comp f hf') (g₂.comp f hf') ↔ B.EqOn g₁ g₂ :=
  hf.cancel_right hf'
#align freiman_hom.cancel_right_on FreimanHom.cancel_right_on
#align add_freiman_hom.cancel_right_on AddFreimanHom.cancel_right_on

/- warning: freiman_hom.cancel_left_on -> FreimanHom.cancel_left_on is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.cancel_left_on FreimanHom.cancel_left_onₓ'. -/
@[to_additive]
theorem cancel_left_on {g : B →*[n] γ} {f₁ f₂ : A →*[n] β} (hg : B.InjOn g) {hf₁ hf₂} :
    A.EqOn (g.comp f₁ hf₁) (g.comp f₂ hf₂) ↔ A.EqOn f₁ f₂ :=
  hg.cancel_left hf₁ hf₂
#align freiman_hom.cancel_left_on FreimanHom.cancel_left_on
#align add_freiman_hom.cancel_left_on AddFreimanHom.cancel_left_on

/- warning: freiman_hom.comp_id -> FreimanHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u1} α α (coeFn.{succ u1, succ u1} (FreimanHom.{u1, u1} α A α _inst_2 _inst_2 n) (fun (_x : FreimanHom.{u1, u1} α A α _inst_2 _inst_2 n) => α -> α) (FreimanHom.hasCoeToFun.{u1, u1} α α _inst_2 _inst_2 A n) (FreimanHom.id.{u1} α _inst_2 A n)) A A}, Eq.{max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.comp.{u1, u1, u2} α α β _inst_2 _inst_2 _inst_3 A A n f (FreimanHom.id.{u1} α _inst_2 A n) hf) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat} (f : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u2, u2} α α (FunLike.coe.{succ u2, succ u2, succ u2} (FreimanHom.{u2, u2} α A α _inst_2 _inst_2 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => α) _x) (FreimanHom.funLike.{u2, u2} α α _inst_2 _inst_2 A n) (FreimanHom.id.{u2} α _inst_2 A n)) A A}, Eq.{max (succ u2) (succ u1)} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (FreimanHom.comp.{u2, u2, u1} α α β _inst_2 _inst_2 _inst_3 A A n f (FreimanHom.id.{u2} α _inst_2 A n) hf) f
Case conversion may be inaccurate. Consider using '#align freiman_hom.comp_id FreimanHom.comp_idₓ'. -/
@[simp, to_additive]
theorem comp_id (f : A →*[n] β) {hf} : f.comp (FreimanHom.id A n) hf = f :=
  ext fun x => rfl
#align freiman_hom.comp_id FreimanHom.comp_id
#align add_freiman_hom.comp_id AddFreimanHom.comp_id

/- warning: freiman_hom.id_comp -> FreimanHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.comp.{u1, u2, u2} α β β _inst_2 _inst_3 _inst_3 A B n (FreimanHom.id.{u2} β _inst_3 B n) f hf) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {B : Set.{u1} β} {n : Nat} (f : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u2) (succ u1)} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (FreimanHom.comp.{u2, u1, u1} α β β _inst_2 _inst_3 _inst_3 A B n (FreimanHom.id.{u1} β _inst_3 B n) f hf) f
Case conversion may be inaccurate. Consider using '#align freiman_hom.id_comp FreimanHom.id_compₓ'. -/
@[simp, to_additive]
theorem id_comp (f : A →*[n] β) {hf} : (FreimanHom.id B n).comp f hf = f :=
  ext fun x => rfl
#align freiman_hom.id_comp FreimanHom.id_comp
#align add_freiman_hom.id_comp AddFreimanHom.id_comp

#print FreimanHom.const /-
/-- `freiman_hom.const A n b` is the Freiman homomorphism sending everything to `b`. -/
@[to_additive "`add_freiman_hom.const n b` is the Freiman homomorphism sending everything to `b`."]
def const (A : Set α) (n : ℕ) (b : β) : A →*[n] β
    where
  toFun _ := b
  map_prod_eq_map_prod' s t _ _ hs ht _ := by
    rw [Multiset.map_const, Multiset.map_const, prod_replicate, prod_replicate, hs, ht]
#align freiman_hom.const FreimanHom.const
#align add_freiman_hom.const AddFreimanHom.const
-/

#print FreimanHom.const_apply /-
@[simp, to_additive]
theorem const_apply (n : ℕ) (b : β) (x : α) : const A n b x = b :=
  rfl
#align freiman_hom.const_apply FreimanHom.const_apply
#align add_freiman_hom.const_apply AddFreimanHom.const_apply
-/

/- warning: freiman_hom.const_comp -> FreimanHom.const_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u3} γ] {A : Set.{u1} α} {B : Set.{u2} β} (n : Nat) (c : γ) (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u1) (succ u3)} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) (FreimanHom.comp.{u1, u2, u3} α β γ _inst_2 _inst_3 _inst_4 A B n (FreimanHom.const.{u2, u3} β γ _inst_3 _inst_4 B n c) f hf) (FreimanHom.const.{u1, u3} α γ _inst_2 _inst_4 A n c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_2 : CommMonoid.{u3} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u1} γ] {A : Set.{u3} α} {B : Set.{u2} β} (n : Nat) (c : γ) (f : FreimanHom.{u3, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u3, u2} α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FreimanHom.{u3, u2} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u3, u2} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u3) (succ u1)} (FreimanHom.{u3, u1} α A γ _inst_2 _inst_4 n) (FreimanHom.comp.{u3, u2, u1} α β γ _inst_2 _inst_3 _inst_4 A B n (FreimanHom.const.{u2, u1} β γ _inst_3 _inst_4 B n c) f hf) (FreimanHom.const.{u3, u1} α γ _inst_2 _inst_4 A n c)
Case conversion may be inaccurate. Consider using '#align freiman_hom.const_comp FreimanHom.const_compₓ'. -/
@[simp, to_additive]
theorem const_comp (n : ℕ) (c : γ) (f : A →*[n] β) {hf} : (const B n c).comp f hf = const A n c :=
  rfl
#align freiman_hom.const_comp FreimanHom.const_comp
#align add_freiman_hom.const_comp AddFreimanHom.const_comp

/-- `1` is the Freiman homomorphism sending everything to `1`. -/
@[to_additive "`0` is the Freiman homomorphism sending everything to `0`."]
instance : One (A →*[n] β) :=
  ⟨const A n 1⟩

/- warning: freiman_hom.one_apply -> FreimanHom.one_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) (OfNat.ofNat.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) 1 (OfNat.mk.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) 1 (One.one.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.hasOne.{u1, u2} α β _inst_2 _inst_3 A n)))) x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u2} α β _inst_2 _inst_3 A n) (OfNat.ofNat.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) 1 (One.toOfNat1.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.instOneFreimanHom.{u1, u2} α β _inst_2 _inst_3 A n))) x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (Monoid.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (CommMonoid.toMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) _inst_3))))
Case conversion may be inaccurate. Consider using '#align freiman_hom.one_apply FreimanHom.one_applyₓ'. -/
@[simp, to_additive]
theorem one_apply (x : α) : (1 : A →*[n] β) x = 1 :=
  rfl
#align freiman_hom.one_apply FreimanHom.one_apply
#align add_freiman_hom.zero_apply AddFreimanHom.zero_apply

/- warning: freiman_hom.one_comp -> FreimanHom.one_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u3} γ] {A : Set.{u1} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u1) (succ u3)} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) (FreimanHom.comp.{u1, u2, u3} α β γ _inst_2 _inst_3 _inst_4 A B n (OfNat.ofNat.{max u2 u3} (FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) 1 (OfNat.mk.{max u2 u3} (FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) 1 (One.one.{max u2 u3} (FreimanHom.{u2, u3} β B γ _inst_3 _inst_4 n) (FreimanHom.hasOne.{u2, u3} β γ _inst_3 _inst_4 B n)))) f hf) (OfNat.ofNat.{max u1 u3} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) 1 (OfNat.mk.{max u1 u3} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) 1 (One.one.{max u1 u3} (FreimanHom.{u1, u3} α A γ _inst_2 _inst_4 n) (FreimanHom.hasOne.{u1, u3} α γ _inst_2 _inst_4 A n))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_2 : CommMonoid.{u3} α] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : CommMonoid.{u1} γ] {A : Set.{u3} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u3, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u3, u2} α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FreimanHom.{u3, u2} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u3, u2} α β _inst_2 _inst_3 A n) f) A B}, Eq.{max (succ u3) (succ u1)} (FreimanHom.{u3, u1} α A γ _inst_2 _inst_4 n) (FreimanHom.comp.{u3, u2, u1} α β γ _inst_2 _inst_3 _inst_4 A B n (OfNat.ofNat.{max u2 u1} (FreimanHom.{u2, u1} β B γ _inst_3 _inst_4 n) 1 (One.toOfNat1.{max u2 u1} (FreimanHom.{u2, u1} β B γ _inst_3 _inst_4 n) (FreimanHom.instOneFreimanHom.{u2, u1} β γ _inst_3 _inst_4 B n))) f hf) (OfNat.ofNat.{max u3 u1} (FreimanHom.{u3, u1} α A γ _inst_2 _inst_4 n) 1 (One.toOfNat1.{max u3 u1} (FreimanHom.{u3, u1} α A γ _inst_2 _inst_4 n) (FreimanHom.instOneFreimanHom.{u3, u1} α γ _inst_2 _inst_4 A n)))
Case conversion may be inaccurate. Consider using '#align freiman_hom.one_comp FreimanHom.one_compₓ'. -/
@[simp, to_additive]
theorem one_comp (f : A →*[n] β) {hf} : (1 : B →*[n] γ).comp f hf = 1 :=
  rfl
#align freiman_hom.one_comp FreimanHom.one_comp
#align add_freiman_hom.zero_comp AddFreimanHom.zero_comp

@[to_additive]
instance : Inhabited (A →*[n] β) :=
  ⟨1⟩

/-- `f * g` is the Freiman homomorphism  sends `x` to `f x * g x`. -/
@[to_additive "`f + g` is the Freiman homomorphism sending `x` to `f x + g x`."]
instance : Mul (A →*[n] β) :=
  ⟨fun f g =>
    { toFun := fun x => f x * g x
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_mul, prod_map_mul, map_prod_eq_map_prod f hsA htA hs ht h,
          map_prod_eq_map_prod g hsA htA hs ht h] }⟩

/- warning: freiman_hom.mul_apply -> FreimanHom.mul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (f : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (g : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (instHMul.{max u1 u2} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (FreimanHom.hasMul.{u1, u2} α β _inst_2 _inst_3 A n)) f g) x) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat} (f : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (g : FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (instHMul.{max u2 u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (FreimanHom.instMulFreimanHom.{u2, u1} α β _inst_2 _inst_3 A n)) f g) x) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) (CommMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) x) _inst_3)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) g x))
Case conversion may be inaccurate. Consider using '#align freiman_hom.mul_apply FreimanHom.mul_applyₓ'. -/
@[simp, to_additive]
theorem mul_apply (f g : A →*[n] β) (x : α) : (f * g) x = f x * g x :=
  rfl
#align freiman_hom.mul_apply FreimanHom.mul_apply
#align add_freiman_hom.add_apply AddFreimanHom.add_apply

/- warning: freiman_hom.mul_comp -> FreimanHom.mul_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.mul_comp FreimanHom.mul_compₓ'. -/
@[to_additive]
theorem mul_comp (g₁ g₂ : B →*[n] γ) (f : A →*[n] β) {hg hg₁ hg₂} :
    (g₁ * g₂).comp f hg = g₁.comp f hg₁ * g₂.comp f hg₂ :=
  rfl
#align freiman_hom.mul_comp FreimanHom.mul_comp
#align add_freiman_hom.add_comp AddFreimanHom.add_comp

/-- If `f` is a Freiman homomorphism to a commutative group, then `f⁻¹` is the Freiman homomorphism
sending `x` to `(f x)⁻¹`. -/
@[to_additive
      "If `f` is a Freiman homomorphism to an additive commutative group, then `-f` is the\nFreiman homomorphism sending `x` to `-f x`."]
instance : Inv (A →*[n] G) :=
  ⟨fun f =>
    { toFun := fun x => (f x)⁻¹
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_inv, prod_map_inv, map_prod_eq_map_prod f hsA htA hs ht h] }⟩

/- warning: freiman_hom.inv_apply -> FreimanHom.inv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_6 : CommGroup.{u2} G] {A : Set.{u1} α} {n : Nat} (f : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (x : α), Eq.{succ u2} G (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (fun (_x : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) => α -> G) (FreimanHom.hasCoeToFun.{u1, u2} α G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) A n) (Inv.inv.{max u1 u2} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.hasInv.{u1, u2} α G _inst_2 _inst_6 A n) f) x) (Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G _inst_6))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (fun (_x : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) => α -> G) (FreimanHom.hasCoeToFun.{u1, u2} α G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) A n) f x))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_6 : CommGroup.{u1} G] {A : Set.{u2} α} {n : Nat} (f : FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) _x) (FreimanHom.funLike.{u2, u1} α G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) A n) (Inv.inv.{max u2 u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (FreimanHom.instInvFreimanHomToCommMonoid.{u2, u1} α G _inst_2 _inst_6 A n) f) x) (Inv.inv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (InvOneClass.toInv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (DivInvOneMonoid.toInvOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (DivisionMonoid.toDivInvOneMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (DivisionCommMonoid.toDivisionMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (CommGroup.toDivisionCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) _inst_6))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) _x) (FreimanHom.funLike.{u2, u1} α G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) A n) f x))
Case conversion may be inaccurate. Consider using '#align freiman_hom.inv_apply FreimanHom.inv_applyₓ'. -/
@[simp, to_additive]
theorem inv_apply (f : A →*[n] G) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align freiman_hom.inv_apply FreimanHom.inv_apply
#align add_freiman_hom.neg_apply AddFreimanHom.neg_apply

/- warning: freiman_hom.inv_comp -> FreimanHom.inv_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] [_inst_6 : CommGroup.{u3} G] {A : Set.{u1} α} {B : Set.{u2} β} {n : Nat} (f : FreimanHom.{u2, u3} β B G _inst_3 (CommGroup.toCommMonoid.{u3} G _inst_6) n) (g : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g) A B} {hf' : Set.MapsTo.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) g) A B}, Eq.{max (succ u1) (succ u3)} (FreimanHom.{u1, u3} α A G _inst_2 (CommGroup.toCommMonoid.{u3} G _inst_6) n) (FreimanHom.comp.{u1, u2, u3} α β G _inst_2 _inst_3 (CommGroup.toCommMonoid.{u3} G _inst_6) A B n (Inv.inv.{max u2 u3} (FreimanHom.{u2, u3} β B G _inst_3 (CommGroup.toCommMonoid.{u3} G _inst_6) n) (FreimanHom.hasInv.{u2, u3} β G _inst_3 _inst_6 B n) f) g hf) (Inv.inv.{max u1 u3} (FreimanHom.{u1, u3} α A G _inst_2 (CommGroup.toCommMonoid.{u3} G _inst_6) n) (FreimanHom.hasInv.{u1, u3} α G _inst_2 _inst_6 A n) (FreimanHom.comp.{u1, u2, u3} α β G _inst_2 _inst_3 (CommGroup.toCommMonoid.{u3} G _inst_6) A B n f g hf'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {G : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u3} β] [_inst_6 : CommGroup.{u2} G] {A : Set.{u1} α} {B : Set.{u3} β} {n : Nat} (f : FreimanHom.{u3, u2} β B G _inst_3 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (g : FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) {hf : Set.MapsTo.{u1, u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g) A B} {hf' : Set.MapsTo.{u1, u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FreimanHom.{u1, u3} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u1, u3} α β _inst_2 _inst_3 A n) g) A B}, Eq.{max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.comp.{u1, u3, u2} α β G _inst_2 _inst_3 (CommGroup.toCommMonoid.{u2} G _inst_6) A B n (Inv.inv.{max u3 u2} (FreimanHom.{u3, u2} β B G _inst_3 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.instInvFreimanHomToCommMonoid.{u3, u2} β G _inst_3 _inst_6 B n) f) g hf) (Inv.inv.{max u2 u1} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.instInvFreimanHomToCommMonoid.{u1, u2} α G _inst_2 _inst_6 A n) (FreimanHom.comp.{u1, u3, u2} α β G _inst_2 _inst_3 (CommGroup.toCommMonoid.{u2} G _inst_6) A B n f g hf'))
Case conversion may be inaccurate. Consider using '#align freiman_hom.inv_comp FreimanHom.inv_compₓ'. -/
@[simp, to_additive]
theorem inv_comp (f : B →*[n] G) (g : A →*[n] β) {hf hf'} : f⁻¹.comp g hf = (f.comp g hf')⁻¹ :=
  ext fun x => rfl
#align freiman_hom.inv_comp FreimanHom.inv_comp
#align add_freiman_hom.neg_comp AddFreimanHom.neg_comp

/-- If `f` and `g` are Freiman homomorphisms to a commutative group, then `f / g` is the Freiman
homomorphism sending `x` to `f x / g x`. -/
@[to_additive
      "If `f` and `g` are additive Freiman homomorphisms to an additive commutative group,\nthen `f - g` is the additive Freiman homomorphism sending `x` to `f x - g x`"]
instance : Div (A →*[n] G) :=
  ⟨fun f g =>
    { toFun := fun x => f x / g x
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_div, prod_map_div, map_prod_eq_map_prod f hsA htA hs ht h,
          map_prod_eq_map_prod g hsA htA hs ht h] }⟩

/- warning: freiman_hom.div_apply -> FreimanHom.div_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_6 : CommGroup.{u2} G] {A : Set.{u1} α} {n : Nat} (f : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (g : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (x : α), Eq.{succ u2} G (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (fun (_x : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) => α -> G) (FreimanHom.hasCoeToFun.{u1, u2} α G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) A n) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (instHDiv.{max u1 u2} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (FreimanHom.hasDiv.{u1, u2} α G _inst_2 _inst_6 A n)) f g) x) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G _inst_6)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (fun (_x : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) => α -> G) (FreimanHom.hasCoeToFun.{u1, u2} α G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) A n) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) (fun (_x : FreimanHom.{u1, u2} α A G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) n) => α -> G) (FreimanHom.hasCoeToFun.{u1, u2} α G _inst_2 (CommGroup.toCommMonoid.{u2} G _inst_6) A n) g x))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_6 : CommGroup.{u1} G] {A : Set.{u2} α} {n : Nat} (f : FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (g : FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) _x) (FreimanHom.funLike.{u2, u1} α G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) A n) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (instHDiv.{max u2 u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) (FreimanHom.instDivFreimanHomToCommMonoid.{u2, u1} α G _inst_2 _inst_6 A n)) f g) x) (HDiv.hDiv.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (instHDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (DivInvMonoid.toDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (Group.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) (CommGroup.toGroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) x) _inst_6)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) _x) (FreimanHom.funLike.{u2, u1} α G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) A n) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => G) _x) (FreimanHom.funLike.{u2, u1} α G _inst_2 (CommGroup.toCommMonoid.{u1} G _inst_6) A n) g x))
Case conversion may be inaccurate. Consider using '#align freiman_hom.div_apply FreimanHom.div_applyₓ'. -/
@[simp, to_additive]
theorem div_apply (f g : A →*[n] G) (x : α) : (f / g) x = f x / g x :=
  rfl
#align freiman_hom.div_apply FreimanHom.div_apply
#align add_freiman_hom.sub_apply AddFreimanHom.sub_apply

/- warning: freiman_hom.div_comp -> FreimanHom.div_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align freiman_hom.div_comp FreimanHom.div_compₓ'. -/
@[simp, to_additive]
theorem div_comp (f₁ f₂ : B →*[n] G) (g : A →*[n] β) {hf hf₁ hf₂} :
    (f₁ / f₂).comp g hf = f₁.comp g hf₁ / f₂.comp g hf₂ :=
  ext fun x => rfl
#align freiman_hom.div_comp FreimanHom.div_comp
#align add_freiman_hom.sub_comp AddFreimanHom.sub_comp

/-! ### Instances -/


/-- `A →*[n] β` is a `comm_monoid`. -/
@[to_additive "`α →+[n] β` is an `add_comm_monoid`."]
instance : CommMonoid (A →*[n] β) where
  mul := (· * ·)
  mul_assoc a b c := by
    ext
    apply mul_assoc
  one := 1
  one_mul a := by
    ext
    apply one_mul
  mul_one a := by
    ext
    apply mul_one
  mul_comm a b := by
    ext
    apply mul_comm
  npow m f :=
    { toFun := fun x => f x ^ m
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_pow, prod_map_pow, map_prod_eq_map_prod f hsA htA hs ht h] }
  npow_zero f := by
    ext x
    exact pow_zero _
  npow_succ n f := by
    ext x
    exact pow_succ _ _

/-- If `β` is a commutative group, then `A →*[n] β` is a commutative group too. -/
@[to_additive
      "If `β` is an additive commutative group, then `A →*[n] β` is an additive commutative\ngroup too."]
instance {β} [CommGroup β] : CommGroup (A →*[n] β) :=
  { FreimanHom.commMonoid with
    inv := Inv.inv
    div := Div.div
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv
    mul_left_inv := by
      intros
      ext
      apply mul_left_inv
    zpow := fun n f =>
      { toFun := fun x => f x ^ n
        map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
          rw [prod_map_zpow, prod_map_zpow, map_prod_eq_map_prod f hsA htA hs ht h] }
    zpow_zero' := fun f => by
      ext x
      exact zpow_zero _
    zpow_succ' := fun n f => by
      ext x
      simp_rw [zpow_ofNat, pow_succ, mul_apply, coe_mk]
    zpow_neg' := fun n f => by
      ext x
      simp_rw [zpow_negSucc, zpow_ofNat]
      rfl }

end FreimanHom

/-! ### Hom hierarchy -/


#print MonoidHom.freimanHomClass /-
--TODO: change to `monoid_hom_class F A β → freiman_hom_class F A β n` once `map_multiset_prod` is
-- generalized
/-- A monoid homomorphism is naturally a `freiman_hom` on its entire domain.

We can't leave the domain `A : set α` of the `freiman_hom` a free variable, since it wouldn't be
inferrable. -/
@[to_additive
      " An additive monoid homomorphism is naturally an `add_freiman_hom` on its entire\ndomain.\n\nWe can't leave the domain `A : set α` of the `freiman_hom` a free variable, since it wouldn't be\ninferrable."]
instance MonoidHom.freimanHomClass : FreimanHomClass (α →* β) Set.univ β n
    where map_prod_eq_map_prod' f s t _ _ _ _ h := by
    rw [← f.map_multiset_prod, h, f.map_multiset_prod]
#align monoid_hom.freiman_hom_class MonoidHom.freimanHomClass
#align add_monoid_hom.freiman_hom_class AddMonoidHom.addFreimanHomClass
-/

#print MonoidHom.toFreimanHom /-
/-- A `monoid_hom` is naturally a `freiman_hom`. -/
@[to_additive AddMonoidHom.toAddFreimanHom "An `add_monoid_hom` is naturally an\n`add_freiman_hom`"]
def MonoidHom.toFreimanHom (A : Set α) (n : ℕ) (f : α →* β) : A →*[n] β
    where
  toFun := f
  map_prod_eq_map_prod' s t hsA htA :=
    map_prod_eq_map_prod f (fun _ _ => Set.mem_univ _) fun _ _ => Set.mem_univ _
#align monoid_hom.to_freiman_hom MonoidHom.toFreimanHom
#align add_monoid_hom.to_add_freiman_hom AddMonoidHom.toAddFreimanHom
-/

/- warning: monoid_hom.to_freiman_hom_coe -> MonoidHom.toFreimanHom_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat} (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))), Eq.{max (succ u1) (succ u2)} ((fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (MonoidHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A n f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3 A n) (MonoidHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A n f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat} (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 _inst_3 A n) (MonoidHom.toFreimanHom.{u2, u1} α β _inst_2 _inst_3 A n f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))) α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3)) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_freiman_hom_coe MonoidHom.toFreimanHom_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.toFreimanHom_coe (f : α →* β) : (f.toFreimanHom A n : α → β) = f :=
  rfl
#align monoid_hom.to_freiman_hom_coe MonoidHom.toFreimanHom_coe
#align add_monoid_hom.to_freiman_hom_coe AddMonoidHom.toAddFreimanHom_coe

/- warning: monoid_hom.to_freiman_hom_injective -> MonoidHom.toFreimanHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CommMonoid.{u2} β] {A : Set.{u1} α} {n : Nat}, Function.Injective.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3))) (FreimanHom.{u1, u2} α A β _inst_2 _inst_3 n) (MonoidHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CommMonoid.{u1} β] {A : Set.{u2} α} {n : Nat}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3))) (FreimanHom.{u2, u1} α A β _inst_2 _inst_3 n) (MonoidHom.toFreimanHom.{u2, u1} α β _inst_2 _inst_3 A n)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_freiman_hom_injective MonoidHom.toFreimanHom_injectiveₓ'. -/
@[to_additive]
theorem MonoidHom.toFreimanHom_injective :
    Function.Injective (MonoidHom.toFreimanHom A n : (α →* β) → A →*[n] β) := fun f g h =>
  MonoidHom.ext <| show _ from FunLike.ext_iff.mp h
#align monoid_hom.to_freiman_hom_injective MonoidHom.toFreimanHom_injective
#align add_monoid_hom.to_freiman_hom_injective AddMonoidHom.toAddFreimanHom_injective

end CommMonoid

section CancelCommMonoid

variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {m n : ℕ}

/- warning: map_prod_eq_map_prod_of_le -> map_prod_eq_map_prod_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align map_prod_eq_map_prod_of_le map_prod_eq_map_prod_of_leₓ'. -/
@[to_additive]
theorem map_prod_eq_map_prod_of_le [FreimanHomClass F A β n] (f : F) {s t : Multiset α}
    (hsA : ∀ x ∈ s, x ∈ A) (htA : ∀ x ∈ t, x ∈ A) (hs : s.card = m) (ht : t.card = m)
    (hst : s.Prod = t.Prod) (h : m ≤ n) : (s.map f).Prod = (t.map f).Prod :=
  by
  obtain rfl | hm := m.eq_zero_or_pos
  · rw [card_eq_zero] at hs ht
    rw [hs, ht]
  rw [← hs, card_pos_iff_exists_mem] at hm
  obtain ⟨a, ha⟩ := hm
  suffices ((s + replicate (n - m) a).map f).Prod = ((t + replicate (n - m) a).map f).Prod
    by
    simp_rw [Multiset.map_add, prod_add] at this
    exact mul_right_cancel this
  replace ha := hsA _ ha
  refine' map_prod_eq_map_prod f (fun x hx => _) (fun x hx => _) _ _ _
  rotate_left 2
  assumption
  -- Can't infer `A` and `n` from the context, so do it manually.
  · rw [mem_add] at hx
    refine' hx.elim (hsA _) fun h => _
    rwa [eq_of_mem_replicate h]
  · rw [mem_add] at hx
    refine' hx.elim (htA _) fun h => _
    rwa [eq_of_mem_replicate h]
  · rw [card_add, hs, card_replicate, add_tsub_cancel_of_le h]
  · rw [card_add, ht, card_replicate, add_tsub_cancel_of_le h]
  · rw [prod_add, prod_add, hst]
#align map_prod_eq_map_prod_of_le map_prod_eq_map_prod_of_le
#align map_sum_eq_map_sum_of_le map_sum_eq_map_sum_of_le

#print FreimanHom.toFreimanHom /-
/-- `α →*[n] β` is naturally included in  `A →*[m] β` for any `m ≤ n`. -/
@[to_additive AddFreimanHom.toAddFreimanHom
      "`α →+[n] β` is naturally included in  `α →+[m] β`\nfor any `m ≤ n`"]
def FreimanHom.toFreimanHom (h : m ≤ n) (f : A →*[n] β) : A →*[m] β
    where
  toFun := f
  map_prod_eq_map_prod' s t hsA htA hs ht hst := map_prod_eq_map_prod_of_le f hsA htA hs ht hst h
#align freiman_hom.to_freiman_hom FreimanHom.toFreimanHom
#align add_freiman_hom.to_add_freiman_hom AddFreimanHom.toAddFreimanHom
-/

/- warning: freiman_hom.freiman_hom_class_of_le -> FreimanHom.FreimanHomClass_of_le is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : FunLike.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β)] [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CancelCommMonoid.{u3} β] {A : Set.{u2} α} {m : Nat} {n : Nat} [_inst_4 : FreimanHomClass.{u2, u1, u3} α F A β _inst_2 (CancelCommMonoid.toCommMonoid.{u3} β _inst_3) n _inst_1], (LE.le.{0} Nat Nat.hasLe m n) -> (FreimanHomClass.{u2, u1, u3} α F A β _inst_2 (CancelCommMonoid.toCommMonoid.{u3} β _inst_3) m _inst_1)
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u3}} {β : Type.{u1}} [_inst_1 : FunLike.{succ u2, succ u3, succ u1} F α (fun (_x : α) => β)] [_inst_2 : CommMonoid.{u3} α] [_inst_3 : CancelCommMonoid.{u1} β] {A : Set.{u3} α} {m : Nat} {n : Nat} [_inst_4 : FreimanHomClass.{u3, u2, u1} α F A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) n _inst_1], (LE.le.{0} Nat instLENat m n) -> (FreimanHomClass.{u3, u2, u1} α F A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) m _inst_1)
Case conversion may be inaccurate. Consider using '#align freiman_hom.freiman_hom_class_of_le FreimanHom.FreimanHomClass_of_leₓ'. -/
/-- A `n`-Freiman homomorphism is also a `m`-Freiman homomorphism for any `m ≤ n`. -/
@[to_additive AddFreimanHom.addFreimanHomClass_of_le
      "An additive `n`-Freiman homomorphism is\nalso an additive `m`-Freiman homomorphism for any `m ≤ n`."]
theorem FreimanHom.FreimanHomClass_of_le [FreimanHomClass F A β n] (h : m ≤ n) :
    FreimanHomClass F A β m :=
  {
    map_prod_eq_map_prod' := fun f s t hsA htA hs ht hst =>
      map_prod_eq_map_prod_of_le f hsA htA hs ht hst h }
#align freiman_hom.freiman_hom_class_of_le FreimanHom.FreimanHomClass_of_le
#align add_freiman_hom.add_freiman_hom_class_of_le AddFreimanHom.addFreimanHomClass_of_le

/- warning: freiman_hom.to_freiman_hom_coe -> FreimanHom.toFreimanHom_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CancelCommMonoid.{u2} β] {A : Set.{u1} α} {m : Nat} {n : Nat} (h : LE.le.{0} Nat Nat.hasLe m n) (f : FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) n), Eq.{max (succ u1) (succ u2)} ((fun (_x : FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) m) => α -> β) (FreimanHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A m n h f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) m) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) m) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) A m) (FreimanHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A m n h f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) n) (fun (_x : FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) n) => α -> β) (FreimanHom.hasCoeToFun.{u1, u2} α β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) A n) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CancelCommMonoid.{u1} β] {A : Set.{u2} α} {m : Nat} {n : Nat} (h : LE.le.{0} Nat instLENat m n) (f : FreimanHom.{u2, u1} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) n), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) m) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) A m) (FreimanHom.toFreimanHom.{u2, u1} α β _inst_2 _inst_3 A m n h f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FreimanHom.{u2, u1} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) n) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Freiman._hyg.2336 : α) => β) _x) (FreimanHom.funLike.{u2, u1} α β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) A n) f)
Case conversion may be inaccurate. Consider using '#align freiman_hom.to_freiman_hom_coe FreimanHom.toFreimanHom_coeₓ'. -/
@[simp, to_additive AddFreimanHom.toAddFreimanHom_coe]
theorem FreimanHom.toFreimanHom_coe (h : m ≤ n) (f : A →*[n] β) : (f.toFreimanHom h : α → β) = f :=
  rfl
#align freiman_hom.to_freiman_hom_coe FreimanHom.toFreimanHom_coe
#align add_freiman_hom.to_add_freiman_hom_coe AddFreimanHom.toAddFreimanHom_coe

/- warning: freiman_hom.to_freiman_hom_injective -> FreimanHom.toFreimanHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CancelCommMonoid.{u2} β] {A : Set.{u1} α} {m : Nat} {n : Nat} (h : LE.le.{0} Nat Nat.hasLe m n), Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) n) (FreimanHom.{u1, u2} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u2} β _inst_3) m) (FreimanHom.toFreimanHom.{u1, u2} α β _inst_2 _inst_3 A m n h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] [_inst_3 : CancelCommMonoid.{u1} β] {A : Set.{u2} α} {m : Nat} {n : Nat} (h : LE.le.{0} Nat instLENat m n), Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (FreimanHom.{u2, u1} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) n) (FreimanHom.{u2, u1} α A β _inst_2 (CancelCommMonoid.toCommMonoid.{u1} β _inst_3) m) (FreimanHom.toFreimanHom.{u2, u1} α β _inst_2 _inst_3 A m n h)
Case conversion may be inaccurate. Consider using '#align freiman_hom.to_freiman_hom_injective FreimanHom.toFreimanHom_injectiveₓ'. -/
@[to_additive]
theorem FreimanHom.toFreimanHom_injective (h : m ≤ n) :
    Function.Injective (FreimanHom.toFreimanHom h : (A →*[n] β) → A →*[m] β) := fun f g hfg =>
  FreimanHom.ext <| by convert FunLike.ext_iff.1 hfg
#align freiman_hom.to_freiman_hom_injective FreimanHom.toFreimanHom_injective
#align add_freiman_hom.to_freiman_hom_injective AddFreimanHom.toAddFreimanHom_injective

end CancelCommMonoid

