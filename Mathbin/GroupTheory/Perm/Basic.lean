import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.GroupPower.Lemmas

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `group` structure on `equiv.perm α`.
-/


universe u v

namespace Equivₓ

variable {α : Type u} {β : Type v}

namespace Perm

instance perm_group : Groupₓ (perm α) where
  mul := fun f g => Equivₓ.trans g f
  one := Equivₓ.refl α
  inv := Equivₓ.symm
  mul_assoc := fun f g h => (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm

theorem mul_apply (f g : perm α) x : (f * g) x = f (g x) :=
  Equivₓ.trans_apply _ _ _

theorem one_apply x : (1 : perm α) x = x :=
  rfl

@[simp]
theorem inv_apply_self (f : perm α) x : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

@[simp]
theorem apply_inv_self (f : perm α) x : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem one_def : (1 : perm α) = Equivₓ.refl α :=
  rfl

theorem mul_def (f g : perm α) : f * g = g.trans f :=
  rfl

theorem inv_def (f : perm α) : f⁻¹ = f.symm :=
  rfl

@[simp]
theorem coe_mul (f g : perm α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : perm α) = id :=
  rfl

theorem eq_inv_iff_eq {f : perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply

theorem inv_eq_iff_eq {f : perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq

theorem zpow_apply_comm {α : Type _} (σ : Equivₓ.Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equivₓ.Perm.mul_apply, ← Equivₓ.Perm.mul_apply, zpow_mul_comm]

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/


@[simp]
theorem trans_one {α : Sort _} {β : Type _} (e : α ≃ β) : e.trans (1 : perm β) = e :=
  Equivₓ.trans_refl e

@[simp]
theorem mul_refl (e : perm α) : e * Equivₓ.refl α = e :=
  Equivₓ.trans_refl e

@[simp]
theorem one_symm : (1 : perm α).symm = 1 :=
  Equivₓ.refl_symm

@[simp]
theorem refl_inv : (Equivₓ.refl α : perm α)⁻¹ = 1 :=
  Equivₓ.refl_symm

@[simp]
theorem one_trans {α : Type _} {β : Sort _} (e : α ≃ β) : (1 : perm α).trans e = e :=
  Equivₓ.refl_trans e

@[simp]
theorem refl_mul (e : perm α) : Equivₓ.refl α * e = e :=
  Equivₓ.refl_trans e

@[simp]
theorem inv_trans_self (e : perm α) : e⁻¹.trans e = 1 :=
  Equivₓ.symm_trans_self e

@[simp]
theorem mul_symm (e : perm α) : e * e.symm = 1 :=
  Equivₓ.symm_trans_self e

@[simp]
theorem self_trans_inv (e : perm α) : e.trans e⁻¹ = 1 :=
  Equivₓ.self_trans_symm e

@[simp]
theorem symm_mul (e : perm α) : e.symm * e = 1 :=
  Equivₓ.self_trans_symm e

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/


@[simp]
theorem sum_congr_mul {α β : Type _} (e : perm α) (f : perm β) (g : perm α) (h : perm β) :
    sum_congr e f * sum_congr g h = sum_congr (e * g) (f * h) :=
  sum_congr_trans g h e f

@[simp]
theorem sum_congr_inv {α β : Type _} (e : perm α) (f : perm β) : (sum_congr e f)⁻¹ = sum_congr e⁻¹ f⁻¹ :=
  sum_congr_symm e f

@[simp]
theorem sum_congr_one {α β : Type _} : sum_congr (1 : perm α) (1 : perm β) = 1 :=
  sum_congr_refl

/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sum_congr_hom (α β : Type _) : perm α × perm β →* perm (Sum α β) where
  toFun := fun a => sum_congr a.1 a.2
  map_one' := sum_congr_one
  map_mul' := fun a b => (sum_congr_mul _ _ _ _).symm

theorem sum_congr_hom_injective {α β : Type _} : Function.Injective (sum_congr_hom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iffₓ]
  constructor <;> ext i
  · simpa using Equivₓ.congr_fun h (Sum.inl i)
    
  · simpa using Equivₓ.congr_fun h (Sum.inr i)
    

@[simp]
theorem sum_congr_swap_one {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : α) :
    sum_congr (Equivₓ.swap i j) (1 : perm β) = Equivₓ.swap (Sum.inl i) (Sum.inl j) :=
  sum_congr_swap_refl i j

@[simp]
theorem sum_congr_one_swap {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : β) :
    sum_congr (1 : perm α) (Equivₓ.swap i j) = Equivₓ.swap (Sum.inr i) (Sum.inr j) :=
  sum_congr_refl_swap i j

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/


@[simp]
theorem sigma_congr_right_mul {α : Type _} {β : α → Type _} (F : ∀ a, perm (β a)) (G : ∀ a, perm (β a)) :
    sigma_congr_right F * sigma_congr_right G = sigma_congr_right (F * G) :=
  sigma_congr_right_trans G F

@[simp]
theorem sigma_congr_right_inv {α : Type _} {β : α → Type _} (F : ∀ a, perm (β a)) :
    (sigma_congr_right F)⁻¹ = sigma_congr_right fun a => (F a)⁻¹ :=
  sigma_congr_right_symm F

@[simp]
theorem sigma_congr_right_one {α : Type _} {β : α → Type _} : sigma_congr_right (1 : ∀ a, Equivₓ.Perm <| β a) = 1 :=
  sigma_congr_right_refl

/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigma_congr_right_hom {α : Type _} (β : α → Type _) : (∀ a, perm (β a)) →* perm (Σ a, β a) where
  toFun := sigma_congr_right
  map_one' := sigma_congr_right_one
  map_mul' := fun a b => (sigma_congr_right_mul _ _).symm

theorem sigma_congr_right_hom_injective {α : Type _} {β : α → Type _} : Function.Injective (sigma_congr_right_hom β) :=
  by
  intro x y h
  ext a b
  simpa using Equivₓ.congr_fun h ⟨a, b⟩

/-- `equiv.perm.subtype_congr` as a `monoid_hom`. -/
@[simps]
def subtype_congr_hom (p : α → Prop) [DecidablePred p] : perm { a // p a } × perm { a // ¬p a } →* perm α where
  toFun := fun pair => perm.subtype_congr pair.fst pair.snd
  map_one' := perm.subtype_congr.refl
  map_mul' := fun _ _ => (perm.subtype_congr.trans _ _ _ _).symm

theorem subtype_congr_hom_injective (p : α → Prop) [DecidablePred p] : Function.Injective (subtype_congr_hom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iffₓ]
  constructor <;> ext i <;> simpa using Equivₓ.congr_fun h i

/-- If `e` is also a permutation, we can write `perm_congr`
completely in terms of the group structure. -/
@[simp]
theorem perm_congr_eq_mul (e p : perm α) : e.perm_congr p = e * p * e⁻¹ :=
  rfl

section ExtendDomain

/-! Lemmas about `equiv.perm.extend_domain` re-expressed via the group structure. -/


variable (e : perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[simp]
theorem extend_domain_one : extend_domain 1 f = 1 :=
  extend_domain_refl f

@[simp]
theorem extend_domain_inv : (e.extend_domain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl

@[simp]
theorem extend_domain_mul (e e' : perm α) : e.extend_domain f * e'.extend_domain f = (e * e').extendDomain f :=
  extend_domain_trans _ _ _

/-- `extend_domain` as a group homomorphism -/
@[simps]
def extend_domain_hom : perm α →* perm β where
  toFun := fun e => extend_domain e f
  map_one' := extend_domain_one f
  map_mul' := fun e e' => (extend_domain_mul f e e').symm

theorem extend_domain_hom_injective : Function.Injective (extend_domain_hom f) :=
  (extend_domain_hom f).injective_iff.mpr fun e he =>
    ext fun x => f.injective (Subtype.ext ((extend_domain_apply_image e f x).symm.trans (ext_iff.mp he (f x))))

@[simp]
theorem extend_domain_eq_one_iff {e : perm α} {f : α ≃ Subtype p} : e.extend_domain f = 1 ↔ e = 1 :=
  (extend_domain_hom f).injective_iff'.mp (extend_domain_hom_injective f) e

end ExtendDomain

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtype_perm (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : perm { x // p x } :=
  ⟨fun x => ⟨f x, (h _).1 x.2⟩, fun x =>
    ⟨f⁻¹ x,
      (h (f⁻¹ x)).2 <| by
        simpa using x.2⟩,
    fun _ => by
    simp only [perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk], fun _ => by
    simp only [perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]⟩

@[simp]
theorem subtype_perm_apply (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) (x : { x // p x }) :
    subtype_perm f h x = ⟨f x, (h _).1 x.2⟩ :=
  rfl

@[simp]
theorem subtype_perm_one (p : α → Prop) (h : ∀ x, p x ↔ p ((1 : perm α) x)) : @subtype_perm α 1 p h = 1 :=
  Equivₓ.ext fun ⟨_, _⟩ => rfl

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def of_subtype {p : α → Prop} [DecidablePred p] : perm (Subtype p) →* perm α where
  toFun := fun f =>
    ⟨fun x => if h : p x then f ⟨x, h⟩ else x, fun x => if h : p x then f⁻¹ ⟨x, h⟩ else x, fun x => by
      have h : ∀ h : p x, p (f ⟨x, h⟩) := fun h => (f ⟨x, h⟩).2
      simp only
      split_ifs  at * <;> simp_all only [perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk, not_true], fun x => by
      have h : ∀ h : p x, p (f⁻¹ ⟨x, h⟩) := fun h => (f⁻¹ ⟨x, h⟩).2
      simp only
      split_ifs  at * <;> simp_all only [perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk, not_true]⟩
  map_one' := by
    ext
    dsimp
    split_ifs <;> rfl
  map_mul' := fun f g =>
    Equivₓ.ext fun x => by
      by_cases' h : p x
      · have h₁ : p (f (g ⟨x, h⟩)) := (f (g ⟨x, h⟩)).2
        have h₂ : p (g ⟨x, h⟩) := (g ⟨x, h⟩).2
        simp only [h, h₂, coe_fn_mk, perm.mul_apply, dif_pos, Subtype.coe_eta]
        
      · simp only [h, coe_fn_mk, perm.mul_apply, dif_neg, not_false_iff]
        

theorem of_subtype_subtype_perm {f : perm α} {p : α → Prop} [DecidablePred p] (h₁ : ∀ x, p x ↔ p (f x))
    (h₂ : ∀ x, f x ≠ x → p x) : of_subtype (subtype_perm f h₁) = f :=
  Equivₓ.ext fun x => by
    rw [of_subtype, subtype_perm]
    by_cases' hx : p x
    · simp only [hx, coe_fn_mk, dif_pos, MonoidHom.coe_mk, Subtype.coe_mk]
      
    · have := Classical.propDecidable
      simp only [hx, not_not.mp (mt (h₂ x) hx), coe_fn_mk, dif_neg, not_false_iff, MonoidHom.coe_mk]
      

theorem of_subtype_apply_of_mem {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) {x : α} (hx : p x) :
    of_subtype f x = f ⟨x, hx⟩ :=
  dif_pos hx

@[simp]
theorem of_subtype_apply_coe {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) (x : Subtype p) :
    of_subtype f x = f x :=
  (Subtype.casesOn x) fun _ => of_subtype_apply_of_mem f

theorem of_subtype_apply_of_not_mem {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) {x : α} (hx : ¬p x) :
    of_subtype f x = x :=
  dif_neg hx

theorem mem_iff_of_subtype_apply_mem {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) (x : α) :
    p x ↔ p ((of_subtype f : α → α) x) :=
  if h : p x then by
    simpa only [of_subtype, h, coe_fn_mk, dif_pos, true_iffₓ, MonoidHom.coe_mk] using (f ⟨x, h⟩).2
  else by
    simp [h, of_subtype_apply_of_not_mem f h]

@[simp]
theorem subtype_perm_of_subtype {p : α → Prop} [DecidablePred p] (f : perm (Subtype p)) :
    subtype_perm (of_subtype f) (mem_iff_of_subtype_apply_mem f) = f :=
  Equivₓ.ext fun ⟨x, hx⟩ => by
    dsimp [subtype_perm, of_subtype]
    simp only [show p x from hx, dif_pos, Subtype.coe_eta]

@[simp]
theorem default_perm {n : Type _} : (default : perm n) = 1 :=
  rfl

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
protected def subtype_equiv_subtype_perm (p : α → Prop) [DecidablePred p] :
    perm (Subtype p) ≃ { f : perm α // ∀ a, ¬p a → f a = a } where
  toFun := fun f => ⟨f.of_subtype, fun a => f.of_subtype_apply_of_not_mem⟩
  invFun := fun f =>
    (f : perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.injective (f.prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.prop a ha ▸ hfa⟩
  left_inv := Equivₓ.Perm.subtype_perm_of_subtype
  right_inv := fun f =>
    Subtype.ext ((Equivₓ.Perm.of_subtype_subtype_perm _) fun a => Not.decidable_imp_symm <| f.prop a)

theorem subtype_equiv_subtype_perm_apply_of_mem {α : Type _} {p : α → Prop} [DecidablePred p] (f : perm (Subtype p))
    {a : α} (h : p a) : perm.subtype_equiv_subtype_perm p f a = f ⟨a, h⟩ :=
  f.of_subtype_apply_of_mem h

theorem subtype_equiv_subtype_perm_apply_of_not_mem {α : Type _} {p : α → Prop} [DecidablePred p] (f : perm (Subtype p))
    {a : α} (h : ¬p a) : perm.subtype_equiv_subtype_perm p f a = a :=
  f.of_subtype_apply_of_not_mem h

variable (e : perm α) (ι : α ↪ β)

open_locale Classical

/-- Noncomputable version of `equiv.perm.via_fintype_embedding` that does not assume `fintype` -/
noncomputable def via_embedding : perm β :=
  extend_domain e (of_injective ι.1 ι.2)

theorem via_embedding_apply (x : α) : e.via_embedding ι (ι x) = ι (e x) :=
  extend_domain_apply_image e (of_injective ι.1 ι.2) x

theorem via_embedding_apply_of_not_mem (x : β) (hx : x ∉ _root_.set.range ι) : e.via_embedding ι x = x :=
  extend_domain_apply_not_subtype e (of_injective ι.1 ι.2) hx

/-- `via_embedding` as a group homomorphism -/
noncomputable def via_embedding_hom : perm α →* perm β :=
  extend_domain_hom (of_injective ι.1 ι.2)

theorem via_embedding_hom_apply : via_embedding_hom ι e = via_embedding e ι :=
  rfl

theorem via_embedding_hom_injective : Function.Injective (via_embedding_hom ι) :=
  extend_domain_hom_injective (of_injective ι.1 ι.2)

end Perm

section Swap

variable [DecidableEq α]

@[simp]
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl

@[simp]
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j

theorem swap_mul_eq_mul_swap (f : perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equivₓ.ext fun z => by
    simp only [perm.mul_apply, swap_apply_def]
    split_ifs <;> simp_all only [perm.apply_inv_self, perm.eq_inv_iff_eq, eq_self_iff_true, not_true]

theorem mul_swap_eq_swap_mul (f : perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  rw [swap_mul_eq_mul_swap, perm.inv_apply_self, perm.inv_apply_self]

theorem swap_apply_apply (f : perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul, mul_inv_cancel_rightₓ]

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem swap_mul_self_mul (i j : α) (σ : perm α) : Equivₓ.swap i j * (Equivₓ.swap i j * σ) = σ := by
  rw [← mul_assoc, swap_mul_self, one_mulₓ]

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem mul_swap_mul_self (i j : α) (σ : perm α) : σ * Equivₓ.swap i j * Equivₓ.swap i j = σ := by
  rw [mul_assoc, swap_mul_self, mul_oneₓ]

/-- A stronger version of `mul_right_injective` -/
@[simp]
theorem swap_mul_involutive (i j : α) : Function.Involutive ((· * ·) (Equivₓ.swap i j)) :=
  swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equivₓ.swap i j) :=
  mul_swap_mul_self i j

@[simp]
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : perm α) ↔ i = j :=
  swap_eq_refl_iff

theorem swap_mul_eq_iff {i j : α} {σ : perm α} : swap i j * σ = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_right_cancelₓ (trans h (one_mulₓ σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by
    erw [h, swap_self, one_mulₓ]⟩

theorem mul_swap_eq_iff {i j : α} {σ : perm α} : σ * swap i j = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_left_cancelₓ (trans h (one_mulₓ σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by
    erw [h, swap_self, mul_oneₓ]⟩

theorem swap_mul_swap_mul_swap {x y z : α} (hwz : x ≠ y) (hxz : x ≠ z) : swap y z * swap x y * swap y z = swap z x :=
  Equivₓ.ext fun n => by
    simp only [swap_apply_def, perm.mul_apply]
    split_ifs <;> cc

end Swap

end Equivₓ

