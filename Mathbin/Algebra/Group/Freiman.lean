/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.BigOperators.Multiset
import Mathbin.Data.FunLike.Basic

/-!
# Freiman homomorphisms

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

/-- An additive `n`-Freiman homomorphism is a map which preserves sums of `n` elements. -/
structure AddFreimanHom (A : Set α) (β : Type _) [AddCommMonoidₓ α] [AddCommMonoidₓ β] (n : ℕ) where
  toFun : α → β
  map_sum_eq_map_sum' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n)
    (ht : t.card = n) (h : s.Sum = t.Sum) : (s.map to_fun).Sum = (t.map to_fun).Sum

/-- A `n`-Freiman homomorphism on a set `A` is a map which preserves products of `n` elements. -/
@[to_additive AddFreimanHom]
structure FreimanHom (A : Set α) (β : Type _) [CommMonoidₓ α] [CommMonoidₓ β] (n : ℕ) where
  toFun : α → β
  map_prod_eq_map_prod' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n)
    (ht : t.card = n) (h : s.Prod = t.Prod) : (s.map to_fun).Prod = (t.map to_fun).Prod

-- mathport name: «expr →+[ ] »
notation:25 A " →+[" n:25 "] " β:0 => AddFreimanHom A β n

-- mathport name: «expr →*[ ] »
notation:25 A " →*[" n:25 "] " β:0 => FreimanHom A β n

/-- `add_freiman_hom_class F s β n` states that `F` is a type of `n`-ary sums-preserving morphisms.
You should extend this class when you extend `add_freiman_hom`. -/
class AddFreimanHomClass (F : Type _) (A : outParam <| Set α) (β : outParam <| Type _) [AddCommMonoidₓ α]
  [AddCommMonoidₓ β] (n : ℕ) [FunLike F α fun _ => β] where
  map_sum_eq_map_sum' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : s.card = n) (ht : t.card = n) (h : s.Sum = t.Sum) : (s.map f).Sum = (t.map f).Sum

/-- `freiman_hom_class F A β n` states that `F` is a type of `n`-ary products-preserving morphisms.
You should extend this class when you extend `freiman_hom`. -/
@[to_additive AddFreimanHomClass]
class FreimanHomClass (F : Type _) (A : outParam <| Set α) (β : outParam <| Type _) [CommMonoidₓ α] [CommMonoidₓ β]
  (n : ℕ) [FunLike F α fun _ => β] where
  map_prod_eq_map_prod' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : s.card = n) (ht : t.card = n) (h : s.Prod = t.Prod) : (s.map f).Prod = (t.map f).Prod

variable [FunLike F α fun _ => β]

section CommMonoidₓ

variable [CommMonoidₓ α] [CommMonoidₓ β] [CommMonoidₓ γ] [CommMonoidₓ δ] [CommGroupₓ G] {A : Set α} {B : Set β}
  {C : Set γ} {n : ℕ}

@[to_additive]
theorem map_prod_eq_map_prod [FreimanHomClass F A β n] (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
    (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n) (h : s.Prod = t.Prod) :
    (s.map f).Prod = (t.map f).Prod :=
  FreimanHomClass.map_prod_eq_map_prod' f hsA htA hs ht h

namespace FreimanHom

@[to_additive]
instance funLike : FunLike (A →*[n] β) α fun _ => β where
  coe := toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr

@[to_additive]
instance freimanHomClass : FreimanHomClass (A →*[n] β) A β n where
  map_prod_eq_map_prod' := map_prod_eq_map_prod'

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
@[to_additive]
instance : CoeFun (A →*[n] β) fun _ => α → β :=
  ⟨toFun⟩

initialize_simps_projections FreimanHom (toFun → apply)

@[simp, to_additive]
theorem to_fun_eq_coe (f : A →*[n] β) : f.toFun = f :=
  rfl

@[ext, to_additive]
theorem ext ⦃f g : A →*[n] β⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[simp, to_additive]
theorem coe_mk (f : α → β)
    (h :
      ∀ s t : Multiset α,
        (∀ ⦃x⦄, x ∈ s → x ∈ A) →
          (∀ ⦃x⦄, x ∈ t → x ∈ A) → s.card = n → t.card = n → s.Prod = t.Prod → (s.map f).Prod = (t.map f).Prod) :
    ⇑(mk f h) = f :=
  rfl

@[simp, to_additive]
theorem mk_coe (f : A →*[n] β) h : mk f h = f :=
  ext fun _ => rfl

/-- The identity map from a commutative monoid to itself. -/
@[to_additive "The identity map from an additive commutative monoid to itself.", simps]
protected def id (A : Set α) (n : ℕ) : A →*[n] α where
  toFun := fun x => x
  map_prod_eq_map_prod' := fun s t _ _ _ _ h => by
    rw [map_id', map_id', h]

/-- Composition of Freiman homomorphisms as a Freiman homomorphism. -/
@[to_additive "Composition of additive Freiman homomorphisms as an additive Freiman homomorphism."]
protected def comp (f : B →*[n] γ) (g : A →*[n] β) (hAB : A.MapsTo g B) : A →*[n] γ where
  toFun := f ∘ g
  map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
    rw [← map_map,
      map_prod_eq_map_prod f _ _ ((s.card_map _).trans hs) ((t.card_map _).trans ht)
        (map_prod_eq_map_prod g hsA htA hs ht h),
      map_map]
    · simpa using fun a h => hAB (hsA h)
      
    · simpa using fun a h => hAB (htA h)
      

@[simp, to_additive]
theorem coe_comp (f : B →*[n] γ) (g : A →*[n] β) {hfg} : ⇑(f.comp g hfg) = f ∘ g :=
  rfl

@[to_additive]
theorem comp_apply (f : B →*[n] γ) (g : A →*[n] β) {hfg} (x : α) : f.comp g hfg x = f (g x) :=
  rfl

@[to_additive]
theorem comp_assoc (f : A →*[n] β) (g : B →*[n] γ) (h : C →*[n] δ) {hf hhg hgf} {hh : A.MapsTo (g.comp f hgf) C} :
    (h.comp g hhg).comp f hf = h.comp (g.comp f hgf) hh :=
  rfl

@[to_additive]
theorem cancel_right {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : Function.Surjective f) {hg₁ hg₂} :
    g₁.comp f hg₁ = g₂.comp f hg₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, fun h => h ▸ rfl⟩

@[to_additive]
theorem cancel_right_on {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : A.SurjOn f B) {hf'} :
    A.EqOn (g₁.comp f hf') (g₂.comp f hf') ↔ B.EqOn g₁ g₂ :=
  hf.cancel_right hf'

@[to_additive]
theorem cancel_left_on {g : B →*[n] γ} {f₁ f₂ : A →*[n] β} (hg : B.InjOn g) {hf₁ hf₂} :
    A.EqOn (g.comp f₁ hf₁) (g.comp f₂ hf₂) ↔ A.EqOn f₁ f₂ :=
  hg.cancel_left hf₁ hf₂

@[simp, to_additive]
theorem comp_id (f : A →*[n] β) {hf} : f.comp (FreimanHom.id A n) hf = f :=
  ext fun x => rfl

@[simp, to_additive]
theorem id_comp (f : A →*[n] β) {hf} : (FreimanHom.id B n).comp f hf = f :=
  ext fun x => rfl

/-- `freiman_hom.const A n b` is the Freiman homomorphism sending everything to `b`. -/
@[to_additive "`add_freiman_hom.const n b` is the Freiman homomorphism sending everything to `b`."]
def const (A : Set α) (n : ℕ) (b : β) : A →*[n] β where
  toFun := fun _ => b
  map_prod_eq_map_prod' := fun s t _ _ hs ht _ => by
    rw [Multiset.map_const, Multiset.map_const, prod_repeat, prod_repeat, hs, ht]

@[simp, to_additive]
theorem const_apply (n : ℕ) (b : β) (x : α) : const A n b x = b :=
  rfl

@[simp, to_additive]
theorem const_comp (n : ℕ) (c : γ) (f : A →*[n] β) {hf} : (const B n c).comp f hf = const A n c :=
  rfl

/-- `1` is the Freiman homomorphism sending everything to `1`. -/
@[to_additive "`0` is the Freiman homomorphism sending everything to `0`."]
instance : One (A →*[n] β) :=
  ⟨const A n 1⟩

@[simp, to_additive]
theorem one_apply (x : α) : (1 : A →*[n] β) x = 1 :=
  rfl

@[simp, to_additive]
theorem one_comp (f : A →*[n] β) {hf} : (1 : B →*[n] γ).comp f hf = 1 :=
  rfl

@[to_additive]
instance : Inhabited (A →*[n] β) :=
  ⟨1⟩

/-- `f * g` is the Freiman homomorphism  sends `x` to `f x * g x`. -/
@[to_additive "`f + g` is the Freiman homomorphism sending `x` to `f x + g x`."]
instance : Mul (A →*[n] β) :=
  ⟨fun f g =>
    { toFun := fun x => f x * g x,
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_mul, prod_map_mul, map_prod_eq_map_prod f hsA htA hs ht h,
          map_prod_eq_map_prod g hsA htA hs ht h] }⟩

@[simp, to_additive]
theorem mul_apply (f g : A →*[n] β) (x : α) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
theorem mul_comp (g₁ g₂ : B →*[n] γ) (f : A →*[n] β) {hg hg₁ hg₂} :
    (g₁ * g₂).comp f hg = g₁.comp f hg₁ * g₂.comp f hg₂ :=
  rfl

/-- If `f` is a Freiman homomorphism to a commutative group, then `f⁻¹` is the Freiman homomorphism
sending `x` to `(f x)⁻¹`. -/
@[to_additive]
instance : Inv (A →*[n] G) :=
  ⟨fun f =>
    { toFun := fun x => (f x)⁻¹,
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_inv', prod_map_inv', map_prod_eq_map_prod f hsA htA hs ht h] }⟩

@[simp, to_additive]
theorem inv_apply (f : A →*[n] G) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[simp, to_additive]
theorem inv_comp (f : B →*[n] G) (g : A →*[n] β) {hf hf'} : f⁻¹.comp g hf = (f.comp g hf')⁻¹ :=
  ext fun x => rfl

/-- If `f` and `g` are Freiman homomorphisms to a commutative group, then `f / g` is the Freiman
homomorphism sending `x` to `f x / g x`. -/
@[to_additive
      "If `f` and `g` are additive Freiman homomorphisms to an additive commutative group,\nthen `f - g` is the additive Freiman homomorphism sending `x` to `f x - g x`"]
instance : Div (A →*[n] G) :=
  ⟨fun f g =>
    { toFun := fun x => f x / g x,
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_div, prod_map_div, map_prod_eq_map_prod f hsA htA hs ht h,
          map_prod_eq_map_prod g hsA htA hs ht h] }⟩

@[simp, to_additive]
theorem div_apply (f g : A →*[n] G) (x : α) : (f / g) x = f x / g x :=
  rfl

@[simp, to_additive]
theorem div_comp (f₁ f₂ : B →*[n] G) (g : A →*[n] β) {hf hf₁ hf₂} :
    (f₁ / f₂).comp g hf = f₁.comp g hf₁ / f₂.comp g hf₂ :=
  ext fun x => rfl

/-! ### Instances -/


/-- `A →*[n] β` is a `comm_monoid`. -/
@[to_additive "`α →+[n] β` is an `add_comm_monoid`."]
instance : CommMonoidₓ (A →*[n] β) where
  mul := (· * ·)
  mul_assoc := fun a b c => by
    ext
    apply mul_assoc
  one := 1
  one_mul := fun a => by
    ext
    apply one_mulₓ
  mul_one := fun a => by
    ext
    apply mul_oneₓ
  mul_comm := fun a b => by
    ext
    apply mul_comm
  npow := fun m f =>
    { toFun := fun x => f x ^ m,
      map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
        rw [prod_map_pow, prod_map_pow, map_prod_eq_map_prod f hsA htA hs ht h] }
  npow_zero' := fun f => by
    ext x
    exact pow_zeroₓ _
  npow_succ' := fun n f => by
    ext x
    exact pow_succₓ _ _

/-- If `β` is a commutative group, then `A →*[n] β` is a commutative group too. -/
@[to_additive "If `β` is an additive commutative group, then `A →*[n] β` is an additive commutative\ngroup too."]
instance {β} [CommGroupₓ β] : CommGroupₓ (A →*[n] β) :=
  { FreimanHom.commMonoid with inv := Inv.inv, div := Div.div,
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv,
    mul_left_inv := by
      intros
      ext
      apply mul_left_invₓ,
    zpow := fun n f =>
      { toFun := fun x => f x ^ n,
        map_prod_eq_map_prod' := fun s t hsA htA hs ht h => by
          rw [prod_map_zpow, prod_map_zpow, map_prod_eq_map_prod f hsA htA hs ht h] },
    zpow_zero' := fun f => by
      ext x
      exact zpow_zero _,
    zpow_succ' := fun n f => by
      ext x
      simp_rw [zpow_of_nat, pow_succₓ, mul_apply, coe_mk],
    zpow_neg' := fun n f => by
      ext x
      simp_rw [zpow_neg_succ_of_nat, zpow_coe_nat]
      rfl }

end FreimanHom

/-! ### Hom hierarchy -/


/-- A monoid homomorphism is naturally a `freiman_hom` on its entire domain.

We can't leave the domain `A : set α` of the `freiman_hom` a free variable, since it wouldn't be
inferrable. -/
--TODO: change to `monoid_hom_class F A β → freiman_hom_class F A β n` once `map_multiset_prod` is
-- generalized
@[to_additive]
instance MonoidHom.freimanHomClass : FreimanHomClass (α →* β) Set.Univ β n where
  map_prod_eq_map_prod' := fun f s t _ _ _ _ h => by
    rw [← f.map_multiset_prod, h, f.map_multiset_prod]

/-- A `monoid_hom` is naturally a `freiman_hom`. -/
@[to_additive AddMonoidHom.toAddFreimanHom "An `add_monoid_hom` is naturally an\n`add_freiman_hom`"]
def MonoidHom.toFreimanHom (A : Set α) (n : ℕ) (f : α →* β) : A →*[n] β where
  toFun := f
  map_prod_eq_map_prod' := fun s t hsA htA =>
    map_prod_eq_map_prod f (fun _ _ => Set.mem_univ _) fun _ _ => Set.mem_univ _

@[simp, to_additive]
theorem MonoidHom.to_freiman_hom_coe (f : α →* β) : (f.toFreimanHom A n : α → β) = f :=
  rfl

@[to_additive]
theorem MonoidHom.to_freiman_hom_injective : Function.Injective (MonoidHom.toFreimanHom A n : (α →* β) → A →*[n] β) :=
  fun f g h => MonoidHom.ext <| show _ from FunLike.ext_iff.mp h

end CommMonoidₓ

section CancelCommMonoid

variable [CommMonoidₓ α] [CancelCommMonoid β] {A : Set α} {m n : ℕ}

@[to_additive]
theorem map_prod_eq_map_prod_of_le [FreimanHomClass F A β n] (f : F) {s t : Multiset α} (hsA : ∀, ∀ x ∈ s, ∀, x ∈ A)
    (htA : ∀, ∀ x ∈ t, ∀, x ∈ A) (hs : s.card = m) (ht : t.card = m) (hst : s.Prod = t.Prod) (h : m ≤ n) :
    (s.map f).Prod = (t.map f).Prod := by
  obtain rfl | hm := m.eq_zero_or_pos
  · rw [card_eq_zero] at hs ht
    rw [hs, ht]
    
  rw [← hs, card_pos_iff_exists_mem] at hm
  obtain ⟨a, ha⟩ := hm
  suffices ((s + repeat a (n - m)).map f).Prod = ((t + repeat a (n - m)).map f).Prod by
    simp_rw [Multiset.map_add, prod_add]  at this
    exact mul_right_cancelₓ this
  replace ha := hsA _ ha
  refine' map_prod_eq_map_prod f (fun x hx => _) (fun x hx => _) _ _ _
  rotate_left 2
  assumption
  -- Can't infer `A` and `n` from the context, so do it manually.
  · rw [mem_add] at hx
    refine' hx.elim (hsA _) fun h => _
    rwa [eq_of_mem_repeat h]
    
  · rw [mem_add] at hx
    refine' hx.elim (htA _) fun h => _
    rwa [eq_of_mem_repeat h]
    
  · rw [card_add, hs, card_repeat, add_tsub_cancel_of_le h]
    
  · rw [card_add, ht, card_repeat, add_tsub_cancel_of_le h]
    
  · rw [prod_add, prod_add, hst]
    

/-- `α →*[n] β` is naturally included in  `A →*[m] β` for any `m ≤ n`. -/
@[to_additive AddFreimanHom.toAddFreimanHom "`α →+[n] β` is naturally included in  `α →+[m] β`\nfor any `m ≤ n`"]
def FreimanHom.toFreimanHom (h : m ≤ n) (f : A →*[n] β) : A →*[m] β where
  toFun := f
  map_prod_eq_map_prod' := fun s t hsA htA hs ht hst => map_prod_eq_map_prod_of_le f hsA htA hs ht hst h

/-- A `n`-Freiman homomorphism is also a `m`-Freiman homomorphism for any `m ≤ n`. -/
@[to_additive AddFreimanHom.addFreimanHomClassOfLe
      "An additive `n`-Freiman homomorphism is\nalso an additive `m`-Freiman homomorphism for any `m ≤ n`."]
def FreimanHom.freimanHomClassOfLe [FreimanHomClass F A β n] (h : m ≤ n) : FreimanHomClass F A β m where
  map_prod_eq_map_prod' := fun f s t hsA htA hs ht hst => map_prod_eq_map_prod_of_le f hsA htA hs ht hst h

@[simp, to_additive AddFreimanHom.to_add_freiman_hom_coe]
theorem FreimanHom.to_freiman_hom_coe (h : m ≤ n) (f : A →*[n] β) : (f.toFreimanHom h : α → β) = f :=
  rfl

@[to_additive]
theorem FreimanHom.to_freiman_hom_injective (h : m ≤ n) :
    Function.Injective (FreimanHom.toFreimanHom h : (A →*[n] β) → A →*[m] β) := fun f g hfg =>
  FreimanHom.ext <| by
    convert FunLike.ext_iff.1 hfg

end CancelCommMonoid

