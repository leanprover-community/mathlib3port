import Mathbin.Algebra.Module.Pi 
import Mathbin.Algebra.Module.LinearMap 
import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Set.Finite 
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open_locale BigOperators

variable (ι : Type u) {γ : Type w} (β : ι → Type v) {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace Dfinsupp

variable [∀ i, HasZero (β i)]

/-- An auxiliary structure used in the definition of of `dfinsupp`,
the type used to make infinite direct sum of modules over a ring. -/
structure pre : Type max u v where 
  toFun : ∀ i, β i 
  preSupport : Multiset ι 
  zero : ∀ i, i ∈ pre_support ∨ to_fun i = 0

instance inhabited_pre : Inhabited (pre ι β) :=
  ⟨⟨fun i => 0, ∅, fun i => Or.inr rfl⟩⟩

instance : Setoidₓ (pre ι β) :=
  { R := fun x y => ∀ i, x.to_fun i = y.to_fun i,
    iseqv := ⟨fun f i => rfl, fun f g H i => (H i).symm, fun f g h H1 H2 i => (H1 i).trans (H2 i)⟩ }

end Dfinsupp

variable {ι}

/-- A dependent function `Π i, β i` with finite support. -/
@[reducible]
def Dfinsupp [∀ i, HasZero (β i)] : Type _ :=
  Quotientₓ (Dfinsupp.Pre.setoid ι β)

variable {β}

notation3  "Π₀" (...) ", " r:(scoped f => Dfinsupp f) => r

infixl:25 " →ₚ " => Dfinsupp

namespace Dfinsupp

section Basic

variable [∀ i, HasZero (β i)] [∀ i, HasZero (β₁ i)] [∀ i, HasZero (β₂ i)]

instance : CoeFun (Π₀i, β i) fun _ => ∀ i, β i :=
  ⟨fun f => Quotientₓ.liftOn f pre.to_fun$ fun _ _ => funext⟩

instance : HasZero (Π₀i, β i) :=
  ⟨«expr⟦ ⟧» ⟨0, ∅, fun i => Or.inr rfl⟩⟩

instance : Inhabited (Π₀i, β i) :=
  ⟨0⟩

@[simp]
theorem coe_pre_mk (f : ∀ i, β i) (s : Multiset ι) hf : «expr⇑ » («expr⟦ ⟧» ⟨f, s, hf⟩ : Π₀i, β i) = f :=
  rfl

@[simp]
theorem coe_zero : «expr⇑ » (0 : Π₀i, β i) = 0 :=
  rfl

theorem zero_apply (i : ι) : (0 : Π₀i, β i) i = 0 :=
  rfl

theorem coe_fn_injective : @Function.Injective (Π₀i, β i) (∀ i, β i) coeFn :=
  fun f g H => Quotientₓ.induction_on₂ f g (fun _ _ H => Quotientₓ.sound H) (congr_funₓ H)

@[ext]
theorem ext {f g : Π₀i, β i} (H : ∀ i, f i = g i) : f = g :=
  coe_fn_injective (funext H)

theorem ext_iff {f g : Π₀i, β i} : f = g ↔ ∀ i, f i = g i :=
  coe_fn_injective.eq_iff.symm.trans Function.funext_iffₓ

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
-/
def map_range (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) : (Π₀i, β₁ i) → Π₀i, β₂ i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => f i (x.1 i), x.2,
        fun i =>
          (x.3 i).imp_right$
            fun H =>
              by 
                rw [H, hf]⟩)
    fun x y H i =>
      by 
        simp only [H i]

@[simp]
theorem map_range_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀i, β₁ i) (i : ι) :
  map_range f hf g i = f i (g i) :=
  Quotientₓ.induction_on g$ fun x => rfl

@[simp]
theorem map_range_id (h : ∀ i, id (0 : β₁ i) = 0 := fun i => rfl) (g : Π₀i : ι, β₁ i) :
  map_range (fun i => (id : β₁ i → β₁ i)) h g = g :=
  by 
    ext 
    simp only [map_range_apply, id.def]

theorem map_range_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0) (hf₂ : ∀ i, f₂ i 0 = 0)
  (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀i : ι, β i) :
  map_range (fun i => f i ∘ f₂ i) h g = map_range f hf (map_range f₂ hf₂ g) :=
  by 
    ext 
    simp only [map_range_apply]

@[simp]
theorem map_range_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) : map_range f hf (0 : Π₀i, β₁ i) = 0 :=
  by 
    ext 
    simp only [map_range_apply, coe_zero, Pi.zero_apply, hf]

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zip_with f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zip_with (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) : (Π₀i, β₁ i) → (Π₀i, β₂ i) → Π₀i, β i :=
  by 
    refine' Quotientₓ.map₂ (fun x y => ⟨fun i => f i (x.1 i) (y.1 i), x.2+y.2, fun i => _⟩) _
    ·
      cases' x.3 i with h1 h1
      ·
        left 
        rw [Multiset.mem_add]
        left 
        exact h1 
      cases' y.3 i with h2 h2
      ·
        left 
        rw [Multiset.mem_add]
        right 
        exact h2 
      right 
      rw [h1, h2, hf]
    exact
      fun x₁ x₂ H1 y₁ y₂ H2 i =>
        by 
          simp only [H1 i, H2 i]

@[simp]
theorem zip_with_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀i, β₁ i) (g₂ : Π₀i, β₂ i) (i : ι) :
  zip_with f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  Quotientₓ.induction_on₂ g₁ g₂$ fun _ _ => rfl

end Basic

section Algebra

instance [∀ i, AddZeroClass (β i)] : Add (Π₀i, β i) :=
  ⟨zip_with (fun _ => ·+·) fun _ => add_zeroₓ 0⟩

theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀i, β i) (i : ι) : (g₁+g₂) i = g₁ i+g₂ i :=
  zip_with_apply _ _ g₁ g₂ i

@[simp]
theorem coe_add [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀i, β i) : «expr⇑ » (g₁+g₂) = g₁+g₂ :=
  funext$ add_apply g₁ g₂

instance [∀ i, AddZeroClass (β i)] : AddZeroClass (Π₀i, β i) :=
  { zero := 0, add := ·+·,
    zero_add :=
      fun f =>
        ext$
          fun i =>
            by 
              simp only [add_apply, zero_apply, zero_addₓ],
    add_zero :=
      fun f =>
        ext$
          fun i =>
            by 
              simp only [add_apply, zero_apply, add_zeroₓ] }

instance [∀ i, AddMonoidₓ (β i)] : AddMonoidₓ (Π₀i, β i) :=
  { Dfinsupp.addZeroClass with zero := 0, add := ·+·,
    add_assoc :=
      fun f g h =>
        ext$
          fun i =>
            by 
              simp only [add_apply, add_assocₓ] }

/-- Coercion from a `dfinsupp` to a pi type is an `add_monoid_hom`. -/
def coe_fn_add_monoid_hom [∀ i, AddZeroClass (β i)] : (Π₀i, β i) →+ ∀ i, β i :=
  { toFun := coeFn, map_zero' := coe_zero, map_add' := coe_add }

/-- Evaluation at a point is an `add_monoid_hom`. This is the finitely-supported version of
`pi.eval_add_monoid_hom`. -/
def eval_add_monoid_hom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coe_fn_add_monoid_hom

instance [∀ i, AddCommMonoidₓ (β i)] : AddCommMonoidₓ (Π₀i, β i) :=
  { Dfinsupp.addMonoid with
    add_comm :=
      fun f g =>
        ext$
          fun i =>
            by 
              simp only [add_apply, add_commₓ],
    nsmul := fun n v => v.map_range (fun _ => (· • ·) n) fun _ => smul_zero _,
    nsmul_zero' :=
      fun n =>
        ext$
          fun i =>
            by 
              simp only [map_range_apply, zero_apply, zero_smul],
    nsmul_succ' :=
      fun n z =>
        ext$
          fun i =>
            by 
              simp only [map_range_apply, add_apply, Nat.succ_eq_one_add, add_smul, one_smul] }

@[simp]
theorem coe_finset_sum {α} [∀ i, AddCommMonoidₓ (β i)] (s : Finset α) (g : α → Π₀i, β i) :
  «expr⇑ » (∑a in s, g a) = ∑a in s, g a :=
  (coe_fn_add_monoid_hom : _ →+ ∀ i, β i).map_sum g s

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoidₓ (β i)] (s : Finset α) (g : α → Π₀i, β i) (i : ι) :
  (∑a in s, g a) i = ∑a in s, g a i :=
  (eval_add_monoid_hom i : _ →+ β i).map_sum g s

instance [∀ i, AddGroupₓ (β i)] : Neg (Π₀i, β i) :=
  ⟨fun f => f.map_range (fun _ => Neg.neg) fun _ => neg_zero⟩

theorem neg_apply [∀ i, AddGroupₓ (β i)] (g : Π₀i, β i) (i : ι) : (-g) i = -g i :=
  map_range_apply _ _ g i

@[simp]
theorem coe_neg [∀ i, AddGroupₓ (β i)] (g : Π₀i, β i) : «expr⇑ » (-g) = -g :=
  funext$ neg_apply g

instance [∀ i, AddGroupₓ (β i)] : Sub (Π₀i, β i) :=
  ⟨zip_with (fun _ => Sub.sub) fun _ => sub_zero 0⟩

theorem sub_apply [∀ i, AddGroupₓ (β i)] (g₁ g₂ : Π₀i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  zip_with_apply _ _ g₁ g₂ i

@[simp]
theorem coe_sub [∀ i, AddGroupₓ (β i)] (g₁ g₂ : Π₀i, β i) : «expr⇑ » (g₁ - g₂) = g₁ - g₂ :=
  funext$ sub_apply g₁ g₂

instance [∀ i, AddGroupₓ (β i)] : AddGroupₓ (Π₀i, β i) :=
  { Dfinsupp.addMonoid, Dfinsupp.hasSub, Dfinsupp.hasNeg with
    add_left_neg :=
      fun f =>
        ext$
          fun i =>
            by 
              simp only [add_apply, neg_apply, zero_apply, add_left_negₓ],
    sub_eq_add_neg :=
      fun f g =>
        ext$
          fun i =>
            by 
              simp only [sub_apply, add_apply, neg_apply, sub_eq_add_neg] }

instance [∀ i, AddCommGroupₓ (β i)] : AddCommGroupₓ (Π₀i, β i) :=
  { @Dfinsupp.addCommMonoid _ β _, Dfinsupp.addGroup with
    zsmul := fun n v => v.map_range (fun _ => (· • ·) n) fun _ => smul_zero _,
    zsmul_neg' :=
      fun n f =>
        ext$
          fun i =>
            by 
              rw [neg_apply, map_range_apply, map_range_apply, zsmul_neg_succ_of_nat, nsmul_eq_smul_cast ℤ,
                Int.nat_cast_eq_coe_nat],
    zsmul_zero' :=
      fun n =>
        ext$
          fun i =>
            by 
              simp only [map_range_apply, zero_apply, zero_smul],
    zsmul_succ' :=
      fun n f =>
        ext$
          fun i =>
            by 
              simp [map_range_apply, add_smul, add_commₓ] }

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] : HasScalar γ (Π₀i, β i) :=
  ⟨fun c v => v.map_range (fun _ => (· • ·) c) fun _ => smul_zero _⟩

theorem smul_apply [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ) (v : Π₀i, β i) (i : ι) :
  (b • v) i = b • v i :=
  map_range_apply _ _ v i

@[simp]
theorem coe_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ) (v : Π₀i, β i) :
  «expr⇑ » (b • v) = b • v :=
  funext$ smul_apply b v

instance {δ : Type _} [Monoidₓ γ] [Monoidₓ δ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]
  [∀ i, DistribMulAction δ (β i)] [∀ i, SmulCommClass γ δ (β i)] : SmulCommClass γ δ (Π₀i, β i) :=
  { smul_comm :=
      fun r s m =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, smul_comm r s (m i)] }

instance {δ : Type _} [Monoidₓ γ] [Monoidₓ δ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]
  [∀ i, DistribMulAction δ (β i)] [HasScalar γ δ] [∀ i, IsScalarTower γ δ (β i)] : IsScalarTower γ δ (Π₀i, β i) :=
  { smul_assoc :=
      fun r s m =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, smul_assoc r s (m i)] }

/-- Dependent functions with finite support inherit a `distrib_mul_action` structure from such a
structure on each coordinate. -/
instance [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] : DistribMulAction γ (Π₀i, β i) :=
  { Dfinsupp.hasScalar with
    smul_zero :=
      fun c =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, smul_zero, zero_apply],
    smul_add :=
      fun c x y =>
        ext$
          fun i =>
            by 
              simp only [add_apply, smul_apply, smul_add],
    one_smul :=
      fun x =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, one_smul],
    mul_smul :=
      fun r s x =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, smul_smul] }

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] : Module γ (Π₀i, β i) :=
  { Dfinsupp.distribMulAction with
    zero_smul :=
      fun c =>
        ext$
          fun i =>
            by 
              simp only [smul_apply, zero_smul, zero_apply],
    add_smul :=
      fun c x y =>
        ext$
          fun i =>
            by 
              simp only [add_apply, smul_apply, add_smul] }

end Algebra

section FilterAndSubtypeDomain

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [∀ i, HasZero (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀i, β i) → Π₀i, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => if p i then x.1 i else 0, x.2,
        fun i =>
          (x.3 i).imp_right$
            fun H =>
              by 
                rw [H, if_t_t]⟩)
    fun x y H i =>
      by 
        simp only [H i]

@[simp]
theorem filter_apply [∀ i, HasZero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀i, β i) :
  f.filter p i = if p i then f i else 0 :=
  Quotientₓ.induction_on f$ fun x => rfl

theorem filter_apply_pos [∀ i, HasZero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀i, β i) {i : ι} (h : p i) :
  f.filter p i = f i :=
  by 
    simp only [filter_apply, if_pos h]

theorem filter_apply_neg [∀ i, HasZero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀i, β i) {i : ι} (h : ¬p i) :
  f.filter p i = 0 :=
  by 
    simp only [filter_apply, if_neg h]

theorem filter_pos_add_filter_neg [∀ i, AddZeroClass (β i)] (f : Π₀i, β i) (p : ι → Prop) [DecidablePred p] :
  (f.filter p+f.filter fun i => ¬p i) = f :=
  ext$
    fun i =>
      by 
        simp only [add_apply, filter_apply] <;> splitIfs <;> simp only [add_zeroₓ, zero_addₓ]

@[simp]
theorem filter_zero [∀ i, HasZero (β i)] (p : ι → Prop) [DecidablePred p] : (0 : Π₀i, β i).filter p = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem filter_add [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀i, β i) :
  (f+g).filter p = f.filter p+g.filter p :=
  by 
    ext 
    simp [ite_add_zero]

@[simp]
theorem filter_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (p : ι → Prop) [DecidablePred p]
  (r : γ) (f : Π₀i, β i) : (r • f).filter p = r • f.filter p :=
  by 
    ext 
    simp [smul_ite]

variable (γ β)

/-- `dfinsupp.filter` as an `add_monoid_hom`. -/
@[simps]
def filter_add_monoid_hom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀i, β i) →+ Π₀i, β i :=
  { toFun := filter p, map_zero' := filter_zero p, map_add' := filter_add p }

/-- `dfinsupp.filter` as a `linear_map`. -/
@[simps]
def filter_linear_map [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] (p : ι → Prop) [DecidablePred p] :
  (Π₀i, β i) →ₗ[γ] Π₀i, β i :=
  { toFun := filter p, map_add' := filter_add p, map_smul' := filter_smul p }

variable {γ β}

@[simp]
theorem filter_neg [∀ i, AddGroupₓ (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀i, β i) :
  (-f).filter p = -f.filter p :=
  (filter_add_monoid_hom β p).map_neg f

@[simp]
theorem filter_sub [∀ i, AddGroupₓ (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀i, β i) :
  (f - g).filter p = f.filter p - g.filter p :=
  (filter_add_monoid_hom β p).map_sub f g

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain [∀ i, HasZero (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀i, β i) → Π₀i : Subtype p, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => x.1 (i : ι), (x.2.filter p).attach.map$ fun j => ⟨j, (Multiset.mem_filter.1 j.2).2⟩,
        fun i =>
          (x.3 i).imp_left$
            fun H =>
              Multiset.mem_map.2 ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩)
    fun x y H i => H i

@[simp]
theorem subtype_domain_zero [∀ i, HasZero (β i)] {p : ι → Prop} [DecidablePred p] :
  subtype_domain p (0 : Π₀i, β i) = 0 :=
  rfl

@[simp]
theorem subtype_domain_apply [∀ i, HasZero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p} {v : Π₀i, β i} :
  (subtype_domain p v) i = v i :=
  Quotientₓ.induction_on v$ fun x => rfl

@[simp]
theorem subtype_domain_add [∀ i, AddZeroClass (β i)] {p : ι → Prop} [DecidablePred p] (v v' : Π₀i, β i) :
  (v+v').subtypeDomain p = v.subtype_domain p+v'.subtype_domain p :=
  ext$
    fun i =>
      by 
        simp only [add_apply, subtype_domain_apply]

@[simp]
theorem subtype_domain_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] {p : ι → Prop}
  [DecidablePred p] (r : γ) (f : Π₀i, β i) : (r • f).subtypeDomain p = r • f.subtype_domain p :=
  Quotientₓ.induction_on f$ fun x => rfl

variable (γ β)

/-- `subtype_domain` but as an `add_monoid_hom`. -/
@[simps]
def subtype_domain_add_monoid_hom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
  (Π₀i : ι, β i) →+ Π₀i : Subtype p, β i :=
  { toFun := subtype_domain p, map_zero' := subtype_domain_zero, map_add' := subtype_domain_add }

/-- `dfinsupp.subtype_domain` as a `linear_map`. -/
@[simps]
def subtype_domain_linear_map [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
  [DecidablePred p] : (Π₀i, β i) →ₗ[γ] Π₀i : Subtype p, β i :=
  { toFun := subtype_domain p, map_add' := subtype_domain_add, map_smul' := subtype_domain_smul }

variable {γ β}

@[simp]
theorem subtype_domain_neg [∀ i, AddGroupₓ (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀i, β i} :
  (-v).subtypeDomain p = -v.subtype_domain p :=
  ext$
    fun i =>
      by 
        simp only [neg_apply, subtype_domain_apply]

@[simp]
theorem subtype_domain_sub [∀ i, AddGroupₓ (β i)] {p : ι → Prop} [DecidablePred p] {v v' : Π₀i, β i} :
  (v - v').subtypeDomain p = v.subtype_domain p - v'.subtype_domain p :=
  ext$
    fun i =>
      by 
        simp only [sub_apply, subtype_domain_apply]

end FilterAndSubtypeDomain

variable [dec : DecidableEq ι]

include dec

section Basic

variable [∀ i, HasZero (β i)]

omit dec

theorem finite_support (f : Π₀i, β i) : Set.Finite { i | f i ≠ 0 } :=
  by 
    classical 
    exact
      Quotientₓ.induction_on f
        fun x => x.2.toFinset.finite_to_set.Subset fun i H => Multiset.mem_to_finset.2 ((x.3 i).resolve_right H)

include dec

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `finset`. -/
def mk (s : Finset ι) (x : ∀ i : («expr↑ » s : Set ι), β (i : ι)) : Π₀i, β i :=
  «expr⟦ ⟧»
    ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0, s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr$ dif_neg H⟩

@[simp]
theorem mk_apply {s : Finset ι} {x : ∀ i : («expr↑ » s : Set ι), β i} {i : ι} :
  (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk_injective (s : finset ι) : function.injective (@mk ι β _ _ s) :=
begin
  intros [ident x, ident y, ident H],
  ext [] [ident i] [],
  have [ident h1] [":", expr «expr = »((mk s x : ∀ i, β i) i, (mk s y : ∀ i, β i) i)] [],
  { rw [expr H] [] },
  cases [expr i] ["with", ident i, ident hi],
  change [expr «expr ∈ »(i, s)] [] ["at", ident hi],
  dsimp ["only"] ["[", expr mk_apply, ",", expr subtype.coe_mk, "]"] [] ["at", ident h1],
  simpa [] [] ["only"] ["[", expr dif_pos hi, "]"] [] ["using", expr h1]
end

omit dec

/-- Given `fintype ι`, `equiv_fun_on_fintype` is the `equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equiv_fun_on_fintype [Fintype ι] : (Π₀i, β i) ≃ ∀ i, β i :=
  { toFun := coeFn, invFun := fun f => «expr⟦ ⟧» ⟨f, Finset.univ.1, fun i => Or.inl$ Finset.mem_univ_val _⟩,
    left_inv := fun x => coe_fn_injective rfl, right_inv := fun x => rfl }

@[simp]
theorem equiv_fun_on_fintype_symm_coe [Fintype ι] (f : Π₀i, β i) : equiv_fun_on_fintype.symm f = f :=
  Equiv.symm_apply_apply _ _

include dec

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀i, β i :=
  mk {i}$ fun j => Eq.recOnₓ (Finset.mem_singleton.1 j.prop).symm b

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem single_apply
{i i' b} : «expr = »((single i b : «exprΠ₀ , »((i), β i)) i', if h : «expr = »(i, i') then eq.rec_on h b else 0) :=
begin
  dsimp ["only"] ["[", expr single, "]"] [] [],
  by_cases [expr h, ":", expr «expr = »(i, i')],
  { have [ident h1] [":", expr «expr ∈ »(i', ({i} : finset ι))] [":=", expr finset.mem_singleton.2 h.symm],
    simp [] [] ["only"] ["[", expr mk_apply, ",", expr dif_pos h, ",", expr dif_pos h1, "]"] [] [],
    refl },
  { have [ident h1] [":", expr «expr ∉ »(i', ({i} : finset ι))] [":=", expr finset.not_mem_singleton.2 (ne.symm h)],
    simp [] [] ["only"] ["[", expr mk_apply, ",", expr dif_neg h, ",", expr dif_neg h1, "]"] [] [] }
end

theorem single_eq_pi_single {i b} : «expr⇑ » (single i b : Π₀i, β i) = Pi.single i b :=
  by 
    ext i' 
    simp only [Pi.single, Function.update]
    splitIfs
    ·
      simp [h]
    ·
      simp [Ne.symm h]

@[simp]
theorem single_zero i : (single i 0 : Π₀i, β i) = 0 :=
  Quotientₓ.sound$
    fun j =>
      if H : j ∈ ({i} : Finset _) then
        by 
          dsimp only <;> rw [dif_pos H] <;> cases Finset.mem_singleton.1 H <;> rfl
      else dif_neg H

@[simp]
theorem single_eq_same {i b} : (single i b : Π₀i, β i) i = b :=
  by 
    simp only [single_apply, dif_pos rfl]

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀i, β i) i' = 0 :=
  by 
    simp only [single_apply, dif_neg h]

theorem single_injective {i} : Function.Injective (single i : β i → Π₀i, β i) :=
  fun x y H =>
    congr_funₓ (mk_injective _ H)
      ⟨i,
        by 
          simp ⟩

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Like `finsupp.single_eq_single_iff`, but with a `heq` due to dependent types -/
theorem single_eq_single_iff
(i j : ι)
(xi : β i)
(xj : β j) : «expr ↔ »(«expr = »(dfinsupp.single i xi, dfinsupp.single j xj), «expr ∨ »(«expr ∧ »(«expr = »(i, j), «expr == »(xi, xj)), «expr ∧ »(«expr = »(xi, 0), «expr = »(xj, 0)))) :=
begin
  split,
  { intro [ident h],
    by_cases [expr hij, ":", expr «expr = »(i, j)],
    { subst [expr hij],
      exact [expr or.inl ⟨rfl, heq_of_eq (dfinsupp.single_injective h)⟩] },
    { have [ident h_coe] [":", expr «expr = »(«expr⇑ »(dfinsupp.single i xi), dfinsupp.single j xj)] [":=", expr congr_arg coe_fn h],
      have [ident hci] [] [":=", expr congr_fun h_coe i],
      have [ident hcj] [] [":=", expr congr_fun h_coe j],
      rw [expr dfinsupp.single_eq_same] ["at", ident hci, ident hcj],
      rw [expr dfinsupp.single_eq_of_ne (ne.symm hij)] ["at", ident hci],
      rw [expr dfinsupp.single_eq_of_ne hij] ["at", ident hcj],
      exact [expr or.inr ⟨hci, hcj.symm⟩] } },
  { rintros ["(", "⟨", ident hi, ",", ident hxi, "⟩", "|", "⟨", ident hi, ",", ident hj, "⟩", ")"],
    { subst [expr hi],
      rw [expr eq_of_heq hxi] [] },
    { rw ["[", expr hi, ",", expr hj, ",", expr dfinsupp.single_zero, ",", expr dfinsupp.single_zero, "]"] [] } }
end

@[simp]
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 :=
  by 
    rw [←single_zero i, single_eq_single_iff]
    simp 

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem filter_single
(p : ι → exprProp())
[decidable_pred p]
(i : ι)
(x : β i) : «expr = »((single i x).filter p, if p i then single i x else 0) :=
begin
  ext [] [ident j] [],
  have [] [] [":=", expr apply_ite (λ x : «exprΠ₀ , »((i), β i), x j) (p i) (single i x) 0],
  dsimp [] [] [] ["at", ident this],
  rw ["[", expr filter_apply, ",", expr this, "]"] [],
  obtain [ident rfl, "|", ident hij, ":=", expr decidable.eq_or_ne i j],
  { refl },
  { rw ["[", expr single_eq_of_ne hij, ",", expr if_t_t, ",", expr if_t_t, "]"] [] }
end

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
  (single i x).filter p = single i x :=
  by 
    rw [filter_single, if_pos h]

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) : (single i x).filter p = 0 :=
  by 
    rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `dfinsupp`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
  Dfinsupp.single i xi = Dfinsupp.single j xj :=
  by 
    cases h 
    rfl

@[simp]
theorem equiv_fun_on_fintype_single [Fintype ι] (i : ι) (m : β i) :
  (@Dfinsupp.equivFunOnFintype ι β _ _) (Dfinsupp.single i m) = Pi.single i m :=
  by 
    ext 
    simp [Dfinsupp.single_eq_pi_single]

@[simp]
theorem equiv_fun_on_fintype_symm_single [Fintype ι] (i : ι) (m : β i) :
  (@Dfinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = Dfinsupp.single i m :=
  by 
    ext i' 
    simp only [←single_eq_pi_single, equiv_fun_on_fintype_symm_coe]

/-- Redefine `f i` to be `0`. -/
def erase (i : ι) : (Π₀i, β i) → Π₀i, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun j => if j = i then 0 else x.1 j, x.2,
        fun j =>
          (x.3 j).imp_right$
            fun H =>
              by 
                simp only [H, if_t_t]⟩)
    fun x y H j =>
      if h : j = i then
        by 
          simp only [if_pos h]
      else
        by 
          simp only [if_neg h, H j]

@[simp]
theorem erase_apply {i j : ι} {f : Π₀i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  Quotientₓ.induction_on f$ fun x => rfl

@[simp]
theorem erase_same {i : ι} {f : Π₀i, β i} : (f.erase i) i = 0 :=
  by 
    simp 

theorem erase_ne {i i' : ι} {f : Π₀i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' :=
  by 
    simp [h]

theorem erase_eq_sub_single {β : ι → Type _} [∀ i, AddGroupₓ (β i)] (f : Π₀i, β i) (i : ι) :
  f.erase i = f - single i (f i) :=
  by 
    ext j 
    rcases eq_or_ne i j with (rfl | h)
    ·
      simp 
    ·
      simp [erase_ne h.symm, single_eq_of_ne h]

@[simp]
theorem erase_zero (i : ι) : erase i (0 : Π₀i, β i) = 0 :=
  ext$ fun _ => if_t_t _ _

@[simp]
theorem filter_ne_eq_erase (f : Π₀i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i :=
  by 
    ext1 j 
    simp only [Dfinsupp.filter_apply, Dfinsupp.erase_apply, ite_not]

@[simp]
theorem filter_ne_eq_erase' (f : Π₀i, β i) (i : ι) : f.filter ((· ≠ ·) i) = f.erase i :=
  by 
    rw [←filter_ne_eq_erase f i]
    congr with j 
    exact ne_comm

theorem erase_single (j : ι) (i : ι) (x : β i) : (single i x).erase j = if i = j then 0 else single i x :=
  by 
    rw [←filter_ne_eq_erase, filter_single, ite_not]

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 :=
  by 
    rw [erase_single, if_pos rfl]

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x :=
  by 
    rw [erase_single, if_neg h]

section Update

variable (f : Π₀i, β i) (i : ι) (b : β i) [Decidable (b = 0)]

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `function.update`. -/
def update : Π₀i, β i :=
  Quotientₓ.map
    (fun x : pre _ _ =>
      ⟨Function.update x.to_fun i b, if b = 0 then x.pre_support.erase i else i ::ₘ x.pre_support,
        by 
          intro j 
          rcases eq_or_ne i j with (rfl | hi)
          ·
            splitIfs with hb
            ·
              simp [hb]
            ·
              simp 
          ·
            cases' x.zero j with hj hj
            ·
              splitIfs <;> simp [Multiset.mem_erase_of_ne hi.symm, hj]
            ·
              simp [Function.update_noteq hi.symm, hj]⟩)
    (fun x y h j =>
      show Function.update x.to_fun i b j = Function.update y.to_fun i b j by 
        rw [(funext h : x.to_fun = y.to_fun)])
    f

variable (j : ι)

@[simp]
theorem coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b :=
  Quotientₓ.induction_on f fun _ => rfl

@[simp]
theorem update_self [Decidable (f i = 0)] : f.update i (f i) = f :=
  by 
    ext 
    simp 

@[simp]
theorem update_eq_erase [Decidable ((0 : β i) = 0)] : f.update i 0 = f.erase i :=
  by 
    ext j 
    rcases eq_or_ne i j with (rfl | hi)
    ·
      simp 
    ·
      simp [hi.symm]

theorem update_eq_single_add_erase {β : ι → Type _} [∀ i, AddZeroClass (β i)] (f : Π₀i, β i) (i : ι) (b : β i)
  [Decidable (b = 0)] : f.update i b = single i b+f.erase i :=
  by 
    ext j 
    rcases eq_or_ne i j with (rfl | h)
    ·
      simp 
    ·
      simp [Function.update_noteq h.symm, h, erase_ne, h.symm]

theorem update_eq_erase_add_single {β : ι → Type _} [∀ i, AddZeroClass (β i)] (f : Π₀i, β i) (i : ι) (b : β i)
  [Decidable (b = 0)] : f.update i b = f.erase i+single i b :=
  by 
    ext j 
    rcases eq_or_ne i j with (rfl | h)
    ·
      simp 
    ·
      simp [Function.update_noteq h.symm, h, erase_ne, h.symm]

theorem update_eq_sub_add_single {β : ι → Type _} [∀ i, AddGroupₓ (β i)] (f : Π₀i, β i) (i : ι) (b : β i)
  [Decidable (b = 0)] : f.update i b = (f - single i (f i))+single i b :=
  by 
    rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]

end Update

end Basic

section AddMonoidₓ

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁+b₂) = single i b₁+single i b₂ :=
  ext$
    fun i' =>
      by 
        byCases' h : i = i'
        ·
          subst h 
          simp only [add_apply, single_eq_same]
        ·
          simp only [add_apply, single_eq_of_ne h, zero_addₓ]

@[simp]
theorem erase_add (i : ι) (f₁ f₂ : Π₀i, β i) : erase i (f₁+f₂) = erase i f₁+erase i f₂ :=
  ext$
    fun _ =>
      by 
        simp [ite_zero_add]

variable (β)

/-- `dfinsupp.single` as an `add_monoid_hom`. -/
@[simps]
def single_add_hom (i : ι) : β i →+ Π₀i, β i :=
  { toFun := single i, map_zero' := single_zero i, map_add' := single_add i }

/-- `dfinsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def erase_add_hom (i : ι) : (Π₀i, β i) →+ Π₀i, β i :=
  { toFun := erase i, map_zero' := erase_zero i, map_add' := erase_add i }

variable {β}

@[simp]
theorem single_neg {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (x : β i) : single i (-x) = -single i x :=
  (single_add_hom β i).map_neg x

@[simp]
theorem single_sub {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (x y : β i) :
  single i (x - y) = single i x - single i y :=
  (single_add_hom β i).map_sub x y

@[simp]
theorem erase_neg {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (f : Π₀i, β i) : (-f).erase i = -f.erase i :=
  (erase_add_hom β i).map_neg f

@[simp]
theorem erase_sub {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (f g : Π₀i, β i) :
  (f - g).erase i = f.erase i - g.erase i :=
  (erase_add_hom β i).map_sub f g

theorem single_add_erase (i : ι) (f : Π₀i, β i) : (single i (f i)+f.erase i) = f :=
  ext$
    fun i' =>
      if h : i = i' then
        by 
          subst h <;> simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, add_zeroₓ]
      else
        by 
          simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_addₓ]

theorem erase_add_single (i : ι) (f : Π₀i, β i) : (f.erase i+single i (f i)) = f :=
  ext$
    fun i' =>
      if h : i = i' then
        by 
          subst h <;> simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, zero_addₓ]
      else
        by 
          simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zeroₓ]

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem induction
{p : «exprΠ₀ , »((i), β i) → exprProp()}
(f : «exprΠ₀ , »((i), β i))
(h0 : p 0)
(ha : ∀
 (i b)
 (f : «exprΠ₀ , »((i), β i)), «expr = »(f i, 0) → «expr ≠ »(b, 0) → p f → p «expr + »(single i b, f)) : p f :=
begin
  refine [expr quotient.induction_on f (λ x, _)],
  cases [expr x] ["with", ident f, ident s, ident H],
  revert [ident f, ident H],
  apply [expr multiset.induction_on s],
  { intros [ident f, ident H],
    convert [] [expr h0] [],
    ext [] [ident i] [],
    exact [expr (H i).resolve_left id] },
  intros [ident i, ident s, ident ih, ident f, ident H],
  by_cases [expr H1, ":", expr «expr ∈ »(i, s)],
  { have [ident H2] [":", expr ∀ j, «expr ∨ »(«expr ∈ »(j, s), «expr = »(f j, 0))] [],
    { intro [ident j],
      cases [expr H j] ["with", ident H2, ident H2],
      { cases [expr multiset.mem_cons.1 H2] ["with", ident H3, ident H3],
        { left,
          rw [expr H3] [],
          exact [expr H1] },
        { left,
          exact [expr H3] } },
      right,
      exact [expr H2] },
    have [ident H3] [":", expr «expr = »((«expr⟦ ⟧»({ to_fun := f,
         pre_support := «expr ::ₘ »(i, s),
         zero := H }) : «exprΠ₀ , »((i), β i)), «expr⟦ ⟧»({ to_fun := f, pre_support := s, zero := H2 }))] [],
    { exact [expr quotient.sound (λ i, rfl)] },
    rw [expr H3] [],
    apply [expr ih] },
  have [ident H2] [":", expr p (erase i «expr⟦ ⟧»({ to_fun := f, pre_support := «expr ::ₘ »(i, s), zero := H }))] [],
  { dsimp ["only"] ["[", expr erase, ",", expr quotient.map_mk, "]"] [] [],
    have [ident H2] [":", expr ∀ j, «expr ∨ »(«expr ∈ »(j, s), «expr = »(ite «expr = »(j, i) 0 (f j), 0))] [],
    { intro [ident j],
      cases [expr H j] ["with", ident H2, ident H2],
      { cases [expr multiset.mem_cons.1 H2] ["with", ident H3, ident H3],
        { right,
          exact [expr if_pos H3] },
        { left,
          exact [expr H3] } },
      right,
      split_ifs [] []; [refl, exact [expr H2]] },
    have [ident H3] [":", expr «expr = »((«expr⟦ ⟧»({ to_fun := λ j : ι, ite «expr = »(j, i) 0 (f j),
         pre_support := «expr ::ₘ »(i, s),
         zero := _ }) : «exprΠ₀ , »((i), β i)), «expr⟦ ⟧»({ to_fun := λ j : ι, ite «expr = »(j, i) 0 (f j),
         pre_support := s,
         zero := H2 }))] [":=", expr quotient.sound (λ i, rfl)],
    rw [expr H3] [],
    apply [expr ih] },
  have [ident H3] [":", expr «expr = »(«expr + »(single i _, _), («expr⟦ ⟧»({ to_fun := f,
       pre_support := «expr ::ₘ »(i, s),
       zero := H }) : «exprΠ₀ , »((i), β i)))] [":=", expr single_add_erase _ _],
  rw ["<-", expr H3] [],
  change [expr p «expr + »(single i (f i), _)] [] [],
  cases [expr classical.em «expr = »(f i, 0)] ["with", ident h, ident h],
  { rw ["[", expr h, ",", expr single_zero, ",", expr zero_add, "]"] [],
    exact [expr H2] },
  refine [expr ha _ _ _ _ h H2],
  rw [expr erase_same] []
end

theorem induction₂ {p : (Π₀i, β i) → Prop} (f : Π₀i, β i) (h0 : p 0)
  (ha : ∀ i b f : Π₀i, β i, f i = 0 → b ≠ 0 → p f → p (f+single i b)) : p f :=
  Dfinsupp.induction f h0$
    fun i b f h1 h2 h3 =>
      have h4 : (f+single i b) = single i b+f :=
        by 
          ext j 
          byCases' H : i = j
          ·
            subst H 
            simp [h1]
          ·
            simp [H]
      Eq.recOnₓ h4$ ha i b f h1 h2 h3

@[simp]
theorem add_closure_Union_range_single : AddSubmonoid.closure (⋃i : ι, Set.Range (single i : β i → Π₀i, β i)) = ⊤ :=
  top_unique$
    fun x hx =>
      by 
        apply Dfinsupp.induction x 
        exact AddSubmonoid.zero_mem _ 
        exact
          fun a b f ha hb hf =>
            AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure$ Set.mem_Union.2 ⟨a, Set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀i, β i) →+ γ⦄
  (H : ∀ i : ι y : β i, f (single i y) = g (single i y)) : f = g :=
  by 
    refine' AddMonoidHom.eq_of_eq_on_mdense add_closure_Union_range_single fun f hf => _ 
    simp only [Set.mem_Union, Set.mem_range] at hf 
    rcases hf with ⟨x, y, rfl⟩
    apply H

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem add_hom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀i, β i) →+ γ⦄
  (H : ∀ x, f.comp (single_add_hom β x) = g.comp (single_add_hom β x)) : f = g :=
  add_hom_ext$ fun x => AddMonoidHom.congr_fun (H x)

end AddMonoidₓ

@[simp]
theorem mk_add [∀ i, AddZeroClass (β i)] {s : Finset ι} {x y : ∀ i : («expr↑ » s : Set ι), β i} :
  mk s (x+y) = mk s x+mk s y :=
  ext$
    fun i =>
      by 
        simp only [add_apply, mk_apply] <;> splitIfs <;> [rfl, rw [zero_addₓ]]

@[simp]
theorem mk_zero [∀ i, HasZero (β i)] {s : Finset ι} : mk s (0 : ∀ i : («expr↑ » s : Set ι), β i.1) = 0 :=
  ext$
    fun i =>
      by 
        simp only [mk_apply] <;> splitIfs <;> rfl

@[simp]
theorem mk_neg [∀ i, AddGroupₓ (β i)] {s : Finset ι} {x : ∀ i : («expr↑ » s : Set ι), β i.1} : mk s (-x) = -mk s x :=
  ext$
    fun i =>
      by 
        simp only [neg_apply, mk_apply] <;> splitIfs <;> [rfl, rw [neg_zero]]

@[simp]
theorem mk_sub [∀ i, AddGroupₓ (β i)] {s : Finset ι} {x y : ∀ i : («expr↑ » s : Set ι), β i.1} :
  mk s (x - y) = mk s x - mk s y :=
  ext$
    fun i =>
      by 
        simp only [sub_apply, mk_apply] <;> splitIfs <;> [rfl, rw [sub_zero]]

/-- If `s` is a subset of `ι` then `mk_add_group_hom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i.$-/
def mk_add_group_hom [∀ i, AddGroupₓ (β i)] (s : Finset ι) : (∀ i : (s : Set ι), β («expr↑ » i)) →+ Π₀i : ι, β i :=
  { toFun := mk s, map_zero' := mk_zero, map_add' := fun _ _ => mk_add }

section 

variable [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]

@[simp]
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : («expr↑ » s : Set ι), β (i : ι)) : mk s (c • x) = c • mk s x :=
  ext$
    fun i =>
      by 
        simp only [smul_apply, mk_apply] <;> splitIfs <;> [rfl, rw [smul_zero]]

@[simp]
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext$
    fun i =>
      by 
        simp only [smul_apply, single_apply] <;> splitIfs <;> [cases h, rw [smul_zero]] <;> rfl

end 

section SupportBasic

variable [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `finset`. -/
def support (f : Π₀i, β i) : Finset ι :=
  (Quotientₓ.liftOn f fun x => x.2.toFinset.filter$ fun i => x.1 i ≠ 0)$
    by 
      intro x y Hxy 
      ext i 
      split 
      ·
        intro H 
        rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
        rw [Hxy i] at h2 
        exact Finset.mem_filter.2 ⟨Multiset.mem_to_finset.2$ (y.3 i).resolve_right h2, h2⟩
      ·
        intro H 
        rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
        rw [←Hxy i] at h2 
        exact Finset.mem_filter.2 ⟨Multiset.mem_to_finset.2$ (x.3 i).resolve_right h2, h2⟩

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : («expr↑ » s : Set ι), β i.1} : (mk s x).support ⊆ s :=
  fun i H => Multiset.mem_to_finset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem mem_support_to_fun (f : Π₀i, β i) i : i ∈ f.support ↔ f i ≠ 0 :=
  by 
    refine' Quotientₓ.induction_on f fun x => _ 
    dsimp only [support, Quotientₓ.lift_on_mk]
    rw [Finset.mem_filter, Multiset.mem_to_finset]
    exact and_iff_right_of_imp (x.3 i).resolve_right

theorem eq_mk_support (f : Π₀i, β i) : f = mk f.support fun i => f i :=
  by 
    change f = mk f.support fun i => f i.1 
    ext i 
    byCases' h : f i ≠ 0 <;> [skip, rw [not_not] at h] <;> simp [h]

@[simp]
theorem support_zero : (0 : Π₀i, β i).support = ∅ :=
  rfl

theorem mem_support_iff (f : Π₀i, β i) : ∀ i : ι, i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_to_fun

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem support_eq_empty {f : «exprΠ₀ , »((i), β i)} : «expr ↔ »(«expr = »(f.support, «expr∅»()), «expr = »(f, 0)) :=
⟨λ
 H, «expr $ »(ext, by simpa [] [] [] ["[", expr finset.ext_iff, "]"] [] ["using", expr H]), by simp [] [] [] [] [] [] { contextual := tt }⟩

instance decidable_zero : DecidablePred (Eq (0 : Π₀i, β i)) :=
  fun f => decidableOfIff _$ support_eq_empty.trans eq_comm

theorem support_subset_iff {s : Set ι} {f : Π₀i, β i} : «expr↑ » f.support ⊆ s ↔ ∀ i _ : i ∉ s, f i = 0 :=
  by 
    simp [Set.subset_def] <;> exact forall_congrₓ fun i => not_imp_comm

theorem support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} :=
  by 
    ext j 
    byCases' h : i = j
    ·
      subst h 
      simp [hb]
    simp [Ne.symm h, h]

theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk_subset

section MapRangeAndZipWith

variable [∀ i, HasZero (β₁ i)] [∀ i, HasZero (β₂ i)]

theorem map_range_def [∀ i x : β₁ i, Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀i, β₁ i} :
  map_range f hf g = mk g.support fun i => f i.1 (g i.1) :=
  by 
    ext i 
    byCases' h : g i ≠ 0 <;> simp  at h <;> simp [h, hf]

@[simp]
theorem map_range_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
  map_range f hf (single i b) = single i (f i b) :=
  Dfinsupp.ext$
    fun i' =>
      by 
        byCases' i = i' <;>
          [·
            subst i' 
            simp ,
          simp [h, hf]]

variable [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i x : β₂ i, Decidable (x ≠ 0)]

theorem support_map_range {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀i, β₁ i} :
  (map_range f hf g).support ⊆ g.support :=
  by 
    simp [map_range_def]

theorem zip_with_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [dec : DecidableEq ι]
  [∀ i : ι, HasZero (β i)] [∀ i : ι, HasZero (β₁ i)] [∀ i : ι, HasZero (β₂ i)] [∀ i : ι x : β₁ i, Decidable (x ≠ 0)]
  [∀ i : ι x : β₂ i, Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀i, β₁ i}
  {g₂ : Π₀i, β₂ i} : zip_with f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) :=
  by 
    ext i 
    byCases' h1 : g₁ i ≠ 0 <;> byCases' h2 : g₂ i ≠ 0 <;> simp only [not_not, Ne.def] at h1 h2 <;> simp [h1, h2, hf]

theorem support_zip_with {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀i, β₁ i} {g₂ : Π₀i, β₂ i} :
  (zip_with f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support :=
  by 
    simp [zip_with_def]

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 :=
  by 
    ext j 
    byCases' h1 : j = i <;> byCases' h2 : f j ≠ 0 <;> simp  at h2 <;> simp [h1, h2]

@[simp]
theorem support_erase (i : ι) (f : Π₀i, β i) : (f.erase i).support = f.support.erase i :=
  by 
    ext j 
    byCases' h1 : j = i <;> byCases' h2 : f j ≠ 0 <;> simp  at h2 <;> simp [h1, h2]

theorem support_update_ne_zero (f : Π₀i, β i) (i : ι) {b : β i} [Decidable (b = 0)] (h : b ≠ 0) :
  support (f.update i b) = insert i f.support :=
  by 
    ext j 
    rcases eq_or_ne i j with (rfl | hi)
    ·
      simp [h]
    ·
      simp [hi.symm]

theorem support_update (f : Π₀i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
  support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support :=
  by 
    ext j 
    splitIfs with hb
    ·
      simp only [hb, update_eq_erase, support_erase]
    ·
      rw [support_update_ne_zero f _ hb]

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 :=
  by 
    ext i <;> byCases' h1 : p i <;> byCases' h2 : f i ≠ 0 <;> simp  at h2 <;> simp [h1, h2]

@[simp]
theorem support_filter (f : Π₀i, β i) : (f.filter p).support = f.support.filter p :=
  by 
    ext i <;> byCases' h : p i <;> simp [h]

theorem subtype_domain_def (f : Π₀i, β i) : f.subtype_domain p = mk (f.support.subtype p) fun i => f i :=
  by 
    ext i <;>
      byCases' h1 : p i <;>
        byCases' h2 : f i ≠ 0 <;>
          try 
              simp  at h2 <;>
            dsimp <;> simp [h1, h2, ←Subtype.val_eq_coe]

@[simp]
theorem support_subtype_domain {f : Π₀i, β i} : (subtype_domain p f).support = f.support.subtype p :=
  by 
    ext i <;>
      byCases' h1 : p i <;>
        byCases' h2 : f i ≠ 0 <;>
          try 
              simp  at h2 <;>
            dsimp <;> simp [h1, h2]

end FilterAndSubtypeDomain

end SupportBasic

theorem support_add [∀ i, AddZeroClass (β i)] [∀ i x : β i, Decidable (x ≠ 0)] {g₁ g₂ : Π₀i, β i} :
  (g₁+g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zip_with

@[simp]
theorem support_neg [∀ i, AddGroupₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] {f : Π₀i, β i} : support (-f) = support f :=
  by 
    ext i <;> simp 

theorem support_smul {γ : Type w} [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)]
  [∀ i : ι x : β i, Decidable (x ≠ 0)] (b : γ) (v : Π₀i, β i) : (b • v).support ⊆ v.support :=
  support_map_range

instance [∀ i, HasZero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀i, β i) :=
  fun f g =>
    decidableOfIff (f.support = g.support ∧ ∀ i _ : i ∈ f.support, f i = g i)
      ⟨fun ⟨h₁, h₂⟩ =>
          ext$
            fun i =>
              if h : i ∈ f.support then h₂ i h else
                have hf : f i = 0 :=
                  by 
                    rwa [f.mem_support_iff, not_not] at h 
                have hg : g i = 0 :=
                  by 
                    rwa [h₁, g.mem_support_iff, not_not] at h 
                by 
                  rw [hf, hg],
        by 
          intro h <;> subst h <;> simp ⟩

section ProdAndSum

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[toAdditive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def Prod [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] (f : Π₀i, β i) (g : ∀ i, β i → γ) : γ :=
  ∏i in f.support, g i (f i)

@[toAdditive]
theorem prod_map_range_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, HasZero (β₁ i)] [∀ i, HasZero (β₂ i)]
  [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i x : β₂ i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : ∀ i, β₁ i → β₂ i}
  {hf : ∀ i, f i 0 = 0} {g : Π₀i, β₁ i} {h : ∀ i, β₂ i → γ} (h0 : ∀ i, h i 0 = 1) :
  (map_range f hf g).Prod h = g.prod fun i b => h i (f i b) :=
  by 
    rw [map_range_def]
    refine' (Finset.prod_subset support_mk_subset _).trans _
    ·
      intro i h1 h2 
      dsimp 
      simp [h1] at h2 
      dsimp  at h2 
      simp [h1, h2, h0]
    ·
      refine' Finset.prod_congr rfl _ 
      intro i h1 
      simp [h1]

@[toAdditive]
theorem prod_zero_index [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ]
  {h : ∀ i, β i → γ} : (0 : Π₀i, β i).Prod h = 1 :=
  rfl

@[toAdditive]
theorem prod_single_index [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {i : ι} {b : β i}
  {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).Prod h = h i b :=
  by 
    byCases' h : b ≠ 0
    ·
      simp [Dfinsupp.prod, support_single_ne_zero h]
    ·
      rw [not_not] at h 
      simp [h, prod_zero_index, h_zero]
      rfl

@[toAdditive]
theorem prod_neg_index [∀ i, AddGroupₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {g : Π₀i, β i}
  {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) : (-g).Prod h = g.prod fun i b => h i (-b) :=
  prod_map_range_index h0

omit dec

@[toAdditive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ i, HasZero (β₁ i)] [∀ i, HasZero (β₂ i)] [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i x : β₂ i, Decidable (x ≠ 0)]
  [CommMonoidₓ γ] (f₁ : Π₀i, β₁ i) (f₂ : Π₀i, β₂ i) (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
  (f₁.prod fun i₁ x₁ => f₂.prod$ fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
    f₂.prod fun i₂ x₂ => f₁.prod$ fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[simp]
theorem sum_apply {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, HasZero (β₁ i₁)]
  [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] {f : Π₀i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀i, β i}
  {i₂ : ι} : (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂ :=
  (eval_add_monoid_hom i₂ : (Π₀i, β i) →+ β i₂).map_sum _ f.support

include dec

theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, HasZero (β₁ i₁)]
  [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] {f : Π₀i₁, β₁ i₁}
  {g : ∀ i₁, β₁ i₁ → Π₀i, β i} : (f.sum g).support ⊆ f.support.bUnion fun i => (g i (f i)).support :=
  have  : ∀ i₁ : ι, (f.sum fun i : ι₁ b : β₁ i => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
      let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      ⟨i, (f.mem_support_iff i).mp hi, Ne⟩
  by 
    simpa [Finset.subset_iff, mem_support_iff, Finset.mem_bUnion, sum_apply] using this

@[simp, toAdditive]
theorem prod_one [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : Π₀i, β i} :
  (f.prod fun i b => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[simp, toAdditive]
theorem prod_mul [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : Π₀i, β i}
  {h₁ h₂ : ∀ i, β i → γ} : (f.prod fun i b => h₁ i b*h₂ i b) = f.prod h₁*f.prod h₂ :=
  Finset.prod_mul_distrib

@[simp, toAdditive]
theorem prod_inv [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommGroupₓ γ] {f : Π₀i, β i}
  {h : ∀ i, β i → γ} : (f.prod fun i b => h i b⁻¹) = f.prod h⁻¹ :=
  ((CommGroupₓ.invMonoidHom : γ →* γ).map_prod _ f.support).symm

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_add_index
[∀ i, add_comm_monoid (β i)]
[∀ (i) (x : β i), decidable «expr ≠ »(x, 0)]
[comm_monoid γ]
{f g : «exprΠ₀ , »((i), β i)}
{h : ∀ i, β i → γ}
(h_zero : ∀ i, «expr = »(h i 0, 1))
(h_add : ∀
 i
 b₁
 b₂, «expr = »(h i «expr + »(b₁, b₂), «expr * »(h i b₁, h i b₂))) : «expr = »(«expr + »(f, g).prod h, «expr * »(f.prod h, g.prod h)) :=
have f_eq : «expr = »(«expr∏ in , »((i), «expr ∪ »(f.support, g.support), h i (f i)), f.prod h), from «expr $ »(finset.prod_subset (finset.subset_union_left _ _), by simp [] [] [] ["[", expr mem_support_iff, ",", expr h_zero, "]"] [] [] { contextual := tt }).symm,
have g_eq : «expr = »(«expr∏ in , »((i), «expr ∪ »(f.support, g.support), h i (g i)), g.prod h), from «expr $ »(finset.prod_subset (finset.subset_union_right _ _), by simp [] [] [] ["[", expr mem_support_iff, ",", expr h_zero, "]"] [] [] { contextual := tt }).symm,
calc
  «expr = »(«expr∏ in , »((i), «expr + »(f, g).support, h i («expr + »(f, g) i)), «expr∏ in , »((i), «expr ∪ »(f.support, g.support), h i («expr + »(f, g) i))) : «expr $ »(finset.prod_subset support_add, by simp [] [] [] ["[", expr mem_support_iff, ",", expr h_zero, "]"] [] [] { contextual := tt })
  «expr = »(..., «expr * »(«expr∏ in , »((i), «expr ∪ »(f.support, g.support), h i (f i)), «expr∏ in , »((i), «expr ∪ »(f.support, g.support), h i (g i)))) : by simp [] [] [] ["[", expr h_add, ",", expr finset.prod_mul_distrib, "]"] [] []
  «expr = »(..., _) : by rw ["[", expr f_eq, ",", expr g_eq, "]"] []

@[toAdditive]
theorem _root_.submonoid.dfinsupp_prod_mem [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ]
  (S : Submonoid γ) (f : Π₀i, β i) (g : ∀ i, β i → γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.prod g ∈ S :=
  S.prod_mem$ fun i hi => h _$ (f.mem_support_iff _).mp hi

@[simp, toAdditive]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, HasZero (β i)] [∀ i : ι x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ]
  (v : Π₀i, β i) {f : ∀ i, β i → γ} (hf : ∀ i, f i 0 = 1) : v.prod f = ∏i, f i (Dfinsupp.equivFunOnFintype v i) :=
  by 
    suffices  : (∏i in v.support, f i (v i)) = ∏i, f i (v i)
    ·
      simp [Dfinsupp.prod, this]
    apply Finset.prod_subset v.support.subset_univ 
    intro i hi' hi 
    rw [mem_support_iff, not_not] at hi 
    rw [hi, hf]

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sum_add_hom
[∀ i, add_zero_class (β i)]
[add_comm_monoid γ]
(φ : ∀ i, «expr →+ »(β i, γ)) : «expr →+ »(«exprΠ₀ , »((i), β i), γ) :=
{ to_fun := λ
  f, «expr $ »(quotient.lift_on f (λ x, «expr∑ in , »((i), x.2.to_finset, φ i (x.1 i))), λ x y H, begin
     have [ident H1] [":", expr «expr ⊆ »(«expr ∩ »(x.2.to_finset, y.2.to_finset), x.2.to_finset)] [],
     from [expr finset.inter_subset_left _ _],
     have [ident H2] [":", expr «expr ⊆ »(«expr ∩ »(x.2.to_finset, y.2.to_finset), y.2.to_finset)] [],
     from [expr finset.inter_subset_right _ _],
     refine [expr (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _))],
     { intros [ident i, ident H1, ident H2],
       rw [expr finset.mem_inter] ["at", ident H2],
       rw [expr H i] [],
       simp [] [] ["only"] ["[", expr multiset.mem_to_finset, "]"] [] ["at", ident H1, ident H2],
       rw ["[", expr (y.3 i).resolve_left (mt (and.intro H1) H2), ",", expr add_monoid_hom.map_zero, "]"] [] },
     { intros [ident i, ident H1],
       rw [expr H i] [] },
     { intros [ident i, ident H1, ident H2],
       rw [expr finset.mem_inter] ["at", ident H2],
       rw ["<-", expr H i] [],
       simp [] [] ["only"] ["[", expr multiset.mem_to_finset, "]"] [] ["at", ident H1, ident H2],
       rw ["[", expr (x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), ",", expr add_monoid_hom.map_zero, "]"] [] }
   end),
  map_add' := assume f g, begin
    refine [expr quotient.induction_on f (λ x, _)],
    refine [expr quotient.induction_on g (λ y, _)],
    change [expr «expr = »(«expr∑ in , »((i), _, _), «expr + »(«expr∑ in , »((i), _, _), «expr∑ in , »((i), _, _)))] [] [],
    simp [] [] ["only"] [] [] [],
    conv [] [] { to_lhs,
      congr,
      skip,
      funext,
      rw [expr add_monoid_hom.map_add] },
    simp [] [] ["only"] ["[", expr finset.sum_add_distrib, "]"] [] [],
    congr' [1] [],
    { refine [expr (finset.sum_subset _ _).symm],
      { intro [ident i],
        simp [] [] ["only"] ["[", expr multiset.mem_to_finset, ",", expr multiset.mem_add, "]"] [] [],
        exact [expr or.inl] },
      { intros [ident i, ident H1, ident H2],
        simp [] [] ["only"] ["[", expr multiset.mem_to_finset, ",", expr multiset.mem_add, "]"] [] ["at", ident H2],
        rw ["[", expr (x.3 i).resolve_left H2, ",", expr add_monoid_hom.map_zero, "]"] [] } },
    { refine [expr (finset.sum_subset _ _).symm],
      { intro [ident i],
        simp [] [] ["only"] ["[", expr multiset.mem_to_finset, ",", expr multiset.mem_add, "]"] [] [],
        exact [expr or.inr] },
      { intros [ident i, ident H1, ident H2],
        simp [] [] ["only"] ["[", expr multiset.mem_to_finset, ",", expr multiset.mem_add, "]"] [] ["at", ident H2],
        rw ["[", expr (y.3 i).resolve_left H2, ",", expr add_monoid_hom.map_zero, "]"] [] } }
  end,
  map_zero' := rfl }

@[simp]
theorem sum_add_hom_single [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (φ : ∀ i, β i →+ γ) i (x : β i) :
  sum_add_hom φ (single i x) = φ i x :=
  (add_zeroₓ _).trans$
    congr_argₓ (φ i)$ show (if H : i ∈ ({i} : Finset _) then x else 0) = x from dif_pos$ Finset.mem_singleton_self i

@[simp]
theorem sum_add_hom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) :
  (sum_add_hom f).comp (single_add_hom β i) = f i :=
  AddMonoidHom.ext$ fun x => sum_add_hom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sum_add_hom_apply [∀ i, AddZeroClass (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [AddCommMonoidₓ γ]
  (φ : ∀ i, β i →+ γ) (f : Π₀i, β i) : sum_add_hom φ f = f.sum fun x => φ x :=
  by 
    refine' Quotientₓ.induction_on f fun x => _ 
    change (∑i in _, _) = ∑i in Finset.filter _ _, _ 
    rw [Finset.sum_filter, Finset.sum_congr rfl]
    intro i _ 
    dsimp only 
    splitIfs 
    rfl 
    rw [not_not.mp h, AddMonoidHom.map_zero]

theorem _root_.add_submonoid.dfinsupp_sum_add_hom_mem [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (S : AddSubmonoid γ)
  (f : Π₀i, β i) (g : ∀ i, β i →+ γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : Dfinsupp.sumAddHom g f ∈ S :=
  by 
    classical 
    rw [Dfinsupp.sum_add_hom_apply]
    convert S.dfinsupp_sum_mem _ _ _ 
    exact h

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom`; that is, every element in the `supr` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
theorem _root_.add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ) :
  supr S = (Dfinsupp.sumAddHom fun i => (S i).Subtype).mrange :=
  by 
    apply le_antisymmₓ
    ·
      apply supr_le _ 
      intro i y hy 
      exact ⟨Dfinsupp.single i ⟨y, hy⟩, Dfinsupp.sum_add_hom_single _ _ _⟩
    ·
      rintro x ⟨v, rfl⟩
      exact AddSubmonoid.dfinsupp_sum_add_hom_mem _ v _ fun i _ => (le_supr S i : S i ≤ _) (v i).Prop

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem _root_.add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom (p : ι → Prop) [DecidablePred p] [AddCommMonoidₓ γ]
  (S : ι → AddSubmonoid γ) :
  (⨆(i : _)(h : p i), S i) = ((sum_add_hom fun i => (S i).Subtype).comp (filter_add_monoid_hom _ p)).mrange :=
  by 
    apply le_antisymmₓ
    ·
      apply bsupr_le _ 
      intro i hi y hy 
      refine' ⟨Dfinsupp.single i ⟨y, hy⟩, _⟩
      rw [AddMonoidHom.comp_apply, filter_add_monoid_hom_apply, filter_single_pos _ _ hi]
      exact sum_add_hom_single _ _ _
    ·
      rintro x ⟨v, rfl⟩
      refine' AddSubmonoid.dfinsupp_sum_add_hom_mem _ _ _ fun i hi => _ 
      refine' AddSubmonoid.mem_supr_of_mem i _ 
      byCases' hp : p i
      ·
        simp [hp]
      ·
        simp [hp]

theorem _root_.add_submonoid.mem_supr_iff_exists_dfinsupp [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ) (x : γ) :
  x ∈ supr S ↔ ∃ f : Π₀i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.supr_eq_mrange_dfinsupp_sum_add_hom S) x

/-- A variant of `add_submonoid.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem _root_.add_submonoid.mem_supr_iff_exists_dfinsupp' [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ)
  [∀ i x : S i, Decidable (x ≠ 0)] (x : γ) : x ∈ supr S ↔ ∃ f : Π₀i, S i, (f.sum fun i xi => «expr↑ » xi) = x :=
  by 
    rw [AddSubmonoid.mem_supr_iff_exists_dfinsupp]
    simpRw [sum_add_hom_apply]
    congr

theorem _root_.add_submonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] [AddCommMonoidₓ γ]
  (S : ι → AddSubmonoid γ) (x : γ) :
  (x ∈ ⨆(i : _)(h : p i), S i) ↔ ∃ f : Π₀i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom p S) x

omit dec

theorem sum_add_hom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} {γ : Type _} [DecidableEq ι₁]
  [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)] [AddCommMonoidₓ γ] (f₁ : Π₀i, β₁ i)
  (f₂ : Π₀i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
  sum_add_hom (fun i₂ => sum_add_hom (fun i₁ => h i₁ i₂) f₁) f₂ =
    sum_add_hom (fun i₁ => sum_add_hom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ :=
  by 
    refine' Quotientₓ.induction_on₂ f₁ f₂ fun x₁ x₂ => _ 
    simp only [sum_add_hom, AddMonoidHom.finset_sum_apply, Quotientₓ.lift_on_mk, AddMonoidHom.coe_mk,
      AddMonoidHom.flip_apply]
    exact Finset.sum_comm

include dec

/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simps apply symmApply]
def lift_add_hom [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] : (∀ i, β i →+ γ) ≃+ ((Π₀i, β i) →+ γ) :=
  { toFun := sum_add_hom, invFun := fun F i => F.comp (single_add_hom β i),
    left_inv :=
      fun x =>
        by 
          ext 
          simp ,
    right_inv :=
      fun ψ =>
        by 
          ext 
          simp ,
    map_add' :=
      fun F G =>
        by 
          ext 
          simp  }

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp]
theorem lift_add_hom_single_add_hom [∀ i, AddCommMonoidₓ (β i)] :
  lift_add_hom (single_add_hom β) = AddMonoidHom.id (Π₀i, β i) :=
  lift_add_hom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
theorem lift_add_hom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) (x : β i) :
  lift_add_hom f (single i x) = f i x :=
  by 
    simp 

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
theorem lift_add_hom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) :
  (lift_add_hom f).comp (single_add_hom β i) = f i :=
  by 
    simp 

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
theorem comp_lift_add_hom {δ : Type _} [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] [AddCommMonoidₓ δ] (g : γ →+ δ)
  (f : ∀ i, β i →+ γ) : g.comp (lift_add_hom f) = lift_add_hom fun a => g.comp (f a) :=
  lift_add_hom.symm_apply_eq.1$
    funext$
      fun a =>
        by 
          rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]

@[simp]
theorem sum_add_hom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] : (sum_add_hom fun i => (0 : β i →+ γ)) = 0 :=
  (lift_add_hom : (∀ i, β i →+ γ) ≃+ _).map_zero

@[simp]
theorem sum_add_hom_add [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] (g : ∀ i, β i →+ γ) (h : ∀ i, β i →+ γ) :
  (sum_add_hom fun i => g i+h i) = sum_add_hom g+sum_add_hom h :=
  lift_add_hom.map_add _ _

@[simp]
theorem sum_add_hom_single_add_hom [∀ i, AddCommMonoidₓ (β i)] : sum_add_hom (single_add_hom β) = AddMonoidHom.id _ :=
  lift_add_hom_single_add_hom

theorem comp_sum_add_hom {δ : Type _} [∀ i, AddZeroClass (β i)] [AddCommMonoidₓ γ] [AddCommMonoidₓ δ] (g : γ →+ δ)
  (f : ∀ i, β i →+ γ) : g.comp (sum_add_hom f) = sum_add_hom fun a => g.comp (f a) :=
  comp_lift_add_hom _ _

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_sub_index
[∀ i, add_group (β i)]
[∀ (i) (x : β i), decidable «expr ≠ »(x, 0)]
[add_comm_group γ]
{f g : «exprΠ₀ , »((i), β i)}
{h : ∀ i, β i → γ}
(h_sub : ∀
 i
 b₁
 b₂, «expr = »(h i «expr - »(b₁, b₂), «expr - »(h i b₁, h i b₂))) : «expr = »(«expr - »(f, g).sum h, «expr - »(f.sum h, g.sum h)) :=
begin
  have [] [] [":=", expr (lift_add_hom (λ a, add_monoid_hom.of_map_sub (h a) (h_sub a))).map_sub f g],
  rw ["[", expr lift_add_hom_apply, ",", expr sum_add_hom_apply, ",", expr sum_add_hom_apply, ",", expr sum_add_hom_apply, "]"] ["at", ident this],
  exact [expr this]
end

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_finset_sum_index
{γ : Type w}
{α : Type x}
[∀ i, add_comm_monoid (β i)]
[∀ (i) (x : β i), decidable «expr ≠ »(x, 0)]
[comm_monoid γ]
{s : finset α}
{g : α → «exprΠ₀ , »((i), β i)}
{h : ∀ i, β i → γ}
(h_zero : ∀ i, «expr = »(h i 0, 1))
(h_add : ∀
 i
 b₁
 b₂, «expr = »(h i «expr + »(b₁, b₂), «expr * »(h i b₁, h i b₂))) : «expr = »(«expr∏ in , »((i), s, (g i).prod h), «expr∑ in , »((i), s, g i).prod h) :=
begin
  classical,
  exact [expr finset.induction_on s (by simp [] [] [] ["[", expr prod_zero_index, "]"] [] []) (by simp [] [] [] ["[", expr prod_add_index, ",", expr h_zero, ",", expr h_add, "]"] [] [] { contextual := tt })]
end

@[toAdditive]
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, HasZero (β₁ i₁)]
  [∀ i x : β₁ i, Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ]
  {f : Π₀i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
  (h_add : ∀ i b₁ b₂, h i (b₁+b₂) = h i b₁*h i b₂) : (f.sum g).Prod h = f.prod fun i b => (g i b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm

-- error in Data.Dfinsupp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem sum_single
[∀ i, add_comm_monoid (β i)]
[∀ (i) (x : β i), decidable «expr ≠ »(x, 0)]
{f : «exprΠ₀ , »((i), β i)} : «expr = »(f.sum single, f) :=
begin
  have [] [] [":=", expr add_monoid_hom.congr_fun lift_add_hom_single_add_hom f],
  rw ["[", expr lift_add_hom_apply, ",", expr sum_add_hom_apply, "]"] ["at", ident this],
  exact [expr this]
end

@[toAdditive]
theorem prod_subtype_domain_index [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)] [CommMonoidₓ γ] {v : Π₀i, β i}
  {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ} (hp : ∀ x _ : x ∈ v.support, p x) :
  ((v.subtype_domain p).Prod fun i b => h i b) = v.prod h :=
  Finset.prod_bij (fun p _ => p)
    (by 
      simp )
    (by 
      simp )
    (fun ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩ =>
      by 
        simp )
    fun i hi =>
      ⟨⟨i, hp i hi⟩,
        by 
          simpa using hi,
        rfl⟩

omit dec

theorem subtype_domain_sum [∀ i, AddCommMonoidₓ (β i)] {s : Finset γ} {h : γ → Π₀i, β i} {p : ι → Prop}
  [DecidablePred p] : (∑c in s, h c).subtypeDomain p = ∑c in s, (h c).subtypeDomain p :=
  (subtype_domain_add_monoid_hom β p).map_sum _ s

theorem subtype_domain_finsupp_sum {δ : γ → Type x} [DecidableEq γ] [∀ c, HasZero (δ c)]
  [∀ c x : δ c, Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] {p : ι → Prop} [DecidablePred p] {s : Π₀c, δ c}
  {h : ∀ c, δ c → Π₀i, β i} : (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum

end ProdAndSum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/


section MapRange

omit dec

variable [∀ i, AddZeroClass (β i)] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]

theorem map_range_add (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (hf' : ∀ i x y, f i (x+y) = f i x+f i y)
  (g₁ g₂ : Π₀i, β₁ i) : map_range f hf (g₁+g₂) = map_range f hf g₁+map_range f hf g₂ :=
  by 
    ext 
    simp only [map_range_apply f, coe_add, Pi.add_apply, hf']

/-- `dfinsupp.map_range` as an `add_monoid_hom`. -/
@[simps apply]
def map_range.add_monoid_hom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀i, β₁ i) →+ Π₀i, β₂ i :=
  { toFun := map_range (fun i x => f i x) fun i => (f i).map_zero, map_zero' := map_range_zero _ _,
    map_add' := map_range_add _ _ fun i => (f i).map_add }

@[simp]
theorem map_range.add_monoid_hom_id : (map_range.add_monoid_hom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext map_range_id

theorem map_range.add_monoid_hom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
  (map_range.add_monoid_hom fun i => (f i).comp (f₂ i)) =
    (map_range.add_monoid_hom f).comp (map_range.add_monoid_hom f₂) :=
  AddMonoidHom.ext$ map_range_comp (fun i x => f i x) (fun i x => f₂ i x) _ _ _

/-- `dfinsupp.map_range.add_monoid_hom` as an `add_equiv`. -/
@[simps apply]
def map_range.add_equiv (e : ∀ i, β₁ i ≃+ β₂ i) : (Π₀i, β₁ i) ≃+ Π₀i, β₂ i :=
  { map_range.add_monoid_hom fun i => (e i).toAddMonoidHom with
    toFun := map_range (fun i x => e i x) fun i => (e i).map_zero,
    invFun := map_range (fun i x => (e i).symm x) fun i => (e i).symm.map_zero,
    left_inv :=
      fun x =>
        by 
          rw [←map_range_comp] <;>
            ·
              simpRw [AddEquiv.symm_comp_self]
              simp ,
    right_inv :=
      fun x =>
        by 
          rw [←map_range_comp] <;>
            ·
              simpRw [AddEquiv.self_comp_symm]
              simp  }

@[simp]
theorem map_range.add_equiv_refl : (map_range.add_equiv$ fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext map_range_id

theorem map_range.add_equiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
  (map_range.add_equiv fun i => (f i).trans (f₂ i)) = (map_range.add_equiv f).trans (map_range.add_equiv f₂) :=
  AddEquiv.ext$ map_range_comp (fun i x => f₂ i x) (fun i x => f i x) _ _ _

@[simp]
theorem map_range.add_equiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
  (map_range.add_equiv e).symm = map_range.add_equiv fun i => (e i).symm :=
  rfl

end MapRange

end Dfinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `add_monoid_hom.map_sum`, `add_monoid_hom.coe_sum`, and
`add_monoid_hom.sum_apply` for `dfinsupp.sum` and `dfinsupp.sum_add_hom` instead of `finset.sum`.

We provide these for `add_monoid_hom`, `monoid_hom`, `ring_hom`, `add_equiv`, and `mul_equiv`.

Lemmas for `linear_map` and `linear_equiv` are in another file.
-/


section 

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type _}

variable [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)]

@[simp, toAdditive]
theorem map_dfinsupp_prod [CommMonoidₓ R] [CommMonoidₓ S] (h : R →* S) (f : Π₀i, β i) (g : ∀ i, β i → R) :
  h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

@[toAdditive]
theorem coe_dfinsupp_prod [Monoidₓ R] [CommMonoidₓ S] (f : Π₀i, β i) (g : ∀ i, β i → R →* S) :
  «expr⇑ » (f.prod g) = f.prod fun a b => g a b :=
  coe_prod _ _

@[simp, toAdditive]
theorem dfinsupp_prod_apply [Monoidₓ R] [CommMonoidₓ S] (f : Π₀i, β i) (g : ∀ i, β i → R →* S) (r : R) :
  (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _

end MonoidHom

namespace RingHom

variable {R S : Type _}

variable [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)]

@[simp]
theorem map_dfinsupp_prod [CommSemiringₓ R] [CommSemiringₓ S] (h : R →+* S) (f : Π₀i, β i) (g : ∀ i, β i → R) :
  h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

@[simp]
theorem map_dfinsupp_sum [NonAssocSemiring R] [NonAssocSemiring S] (h : R →+* S) (f : Π₀i, β i) (g : ∀ i, β i → R) :
  h (f.sum g) = f.sum fun a b => h (g a b) :=
  h.map_sum _ _

end RingHom

namespace MulEquiv

variable {R S : Type _}

variable [∀ i, HasZero (β i)] [∀ i x : β i, Decidable (x ≠ 0)]

@[simp, toAdditive]
theorem map_dfinsupp_prod [CommMonoidₓ R] [CommMonoidₓ S] (h : R ≃* S) (f : Π₀i, β i) (g : ∀ i, β i → R) :
  h (f.prod g) = f.prod fun a b => h (g a b) :=
  h.map_prod _ _

end MulEquiv

/-! The above lemmas, repeated for `dfinsupp.sum_add_hom`. -/


namespace AddMonoidHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [AddCommMonoidₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClass (β i)] (h : R →+ S)
  (f : Π₀i, β i) (g : ∀ i, β i →+ R) : h (sum_add_hom g f) = sum_add_hom (fun i => h.comp (g i)) f :=
  congr_funₓ (comp_lift_add_hom h g) f

@[simp]
theorem dfinsupp_sum_add_hom_apply [AddZeroClass R] [AddCommMonoidₓ S] [∀ i, AddZeroClass (β i)] (f : Π₀i, β i)
  (g : ∀ i, β i →+ R →+ S) (r : R) : (sum_add_hom g f) r = sum_add_hom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sum_add_hom (eval r) f g

theorem coe_dfinsupp_sum_add_hom [AddZeroClass R] [AddCommMonoidₓ S] [∀ i, AddZeroClass (β i)] (f : Π₀i, β i)
  (g : ∀ i, β i →+ R →+ S) : «expr⇑ » (sum_add_hom g f) = sum_add_hom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sum_add_hom (coeFn R S) f g

end AddMonoidHom

namespace RingHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)] (h : R →+* S)
  (f : Π₀i, β i) (g : ∀ i, β i →+ R) : h (sum_add_hom g f) = sum_add_hom (fun i => h.to_add_monoid_hom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end RingHom

namespace AddEquiv

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [AddCommMonoidₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClass (β i)] (h : R ≃+ S)
  (f : Π₀i, β i) (g : ∀ i, β i →+ R) : h (sum_add_hom g f) = sum_add_hom (fun i => h.to_add_monoid_hom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_lift_add_hom h.to_add_monoid_hom g) f

end AddEquiv

end 

