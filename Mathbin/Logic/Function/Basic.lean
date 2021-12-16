import Mathbin.Logic.Basic 
import Mathbin.Data.Option.Defs

/-!
# Miscellaneous function constructions and lemmas
-/


universe u v w

namespace Function

section 

variable {α β γ : Sort _} {f : α → β}

/-- Evaluate a function at an argument. Useful if you want to talk about the partially applied
  `function.eval x : (Π x, β x) → β x`. -/
@[reducible]
def eval {β : α → Sort _} (x : α) (f : ∀ x, β x) : β x :=
  f x

@[simp]
theorem eval_apply {β : α → Sort _} (x : α) (f : ∀ x, β x) : eval x f = f x :=
  rfl

theorem comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) :=
  rfl

theorem const_def {y : β} : (fun x : α => y) = const α y :=
  rfl

@[simp]
theorem const_apply {y : β} {x : α} : const α y x = y :=
  rfl

@[simp]
theorem const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c :=
  rfl

@[simp]
theorem comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) :=
  rfl

theorem id_def : @id α = fun x => x :=
  rfl

theorem hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀ a, β a} {f' : ∀ a, β' a} (hα : α = α')
  (h : ∀ a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' :=
  by 
    subst hα 
    have  : ∀ a, HEq (f a) (f' a)
    ·
      intro a 
      exact h a a (HEq.refl a)
    have  : β = β'
    ·
      funext a 
      exact type_eq_of_heqₓ (this a)
    subst this 
    apply heq_of_eq 
    funext a 
    exact eq_of_heq (this a)

theorem funext_iff {β : α → Sort _} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h a => h ▸ rfl) funext

protected theorem bijective.injective {f : α → β} (hf : bijective f) : injective f :=
  hf.1

protected theorem bijective.surjective {f : α → β} (hf : bijective f) : surjective f :=
  hf.2

theorem injective.eq_iff (I : injective f) {a b : α} : f a = f b ↔ a = b :=
  ⟨@I _ _, congr_argₓ f⟩

theorem injective.eq_iff' (I : injective f) {a b : α} {c : β} (h : f b = c) : f a = c ↔ a = b :=
  h ▸ I.eq_iff

theorem injective.ne (hf : injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
  mt fun h => hf h

theorem injective.ne_iff (hf : injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
  ⟨mt$ congr_argₓ f, hf.ne⟩

theorem injective.ne_iff' (hf : injective f) {x y : α} {z : β} (h : f y = z) : f x ≠ z ↔ x ≠ y :=
  h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def injective.decidable_eq [DecidableEq β] (I : injective f) : DecidableEq α :=
  fun a b => decidableOfIff _ I.eq_iff

theorem injective.of_comp {g : γ → α} (I : injective (f ∘ g)) : injective g :=
  fun x y h => I$ show f (g x) = f (g y) from congr_argₓ f h

theorem injective.of_comp_iff {f : α → β} (hf : injective f) (g : γ → α) : injective (f ∘ g) ↔ injective g :=
  ⟨injective.of_comp, hf.comp⟩

theorem injective.of_comp_iff' (f : α → β) {g : γ → α} (hg : bijective g) : injective (f ∘ g) ↔ injective f :=
  ⟨fun h x y =>
      let ⟨x', hx⟩ := hg.surjective x 
      let ⟨y', hy⟩ := hg.surjective y 
      hx ▸ hy ▸ fun hf => h hf ▸ rfl,
    fun h => h.comp hg.injective⟩

/-- Composition by an injective function on the left is itself injective. -/
theorem injective.comp_left {g : β → γ} (hg : Function.Injective g) :
  Function.Injective ((· ∘ ·) g : (α → β) → α → γ) :=
  fun f₁ f₂ hgf => funext$ fun i => hg$ (congr_funₓ hgf i : _)

theorem injective_of_subsingleton [Subsingleton α] (f : α → β) : injective f :=
  fun a b ab => Subsingleton.elimₓ _ _

theorem injective.dite (p : α → Prop) [DecidablePred p] {f : { a : α // p a } → β} {f' : { a : α // ¬p a } → β}
  (hf : injective f) (hf' : injective f') (im_disj : ∀ {x x' : α} {hx : p x} {hx' : ¬p x'}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  Function.Injective fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩ :=
  fun x₁ x₂ h =>
    by 
      dsimp only  at h 
      byCases' h₁ : p x₁ <;> byCases' h₂ : p x₂
      ·
        rw [dif_pos h₁, dif_pos h₂] at h 
        injection hf h
      ·
        rw [dif_pos h₁, dif_neg h₂] at h 
        exact (im_disj h).elim
      ·
        rw [dif_neg h₁, dif_pos h₂] at h 
        exact (im_disj h.symm).elim
      ·
        rw [dif_neg h₁, dif_neg h₂] at h 
        injection hf' h

theorem surjective.of_comp {g : γ → α} (S : surjective (f ∘ g)) : surjective f :=
  fun y =>
    let ⟨x, h⟩ := S y
    ⟨g x, h⟩

theorem surjective.of_comp_iff (f : α → β) {g : γ → α} (hg : surjective g) : surjective (f ∘ g) ↔ surjective f :=
  ⟨surjective.of_comp, fun h => h.comp hg⟩

theorem surjective.of_comp_iff' (hf : bijective f) (g : γ → α) : surjective (f ∘ g) ↔ surjective g :=
  ⟨fun h x =>
      let ⟨x', hx'⟩ := h (f x)
      ⟨x', hf.injective hx'⟩,
    hf.surjective.comp⟩

instance decidable_eq_pfun (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, DecidableEq (α hp)] :
  DecidableEq (∀ hp, α hp)
| f, g => decidableOfIff (∀ hp, f hp = g hp) funext_iff.symm

protected theorem surjective.forall (hf : surjective f) {p : β → Prop} : (∀ y, p y) ↔ ∀ x, p (f x) :=
  ⟨fun h x => h (f x),
    fun h y =>
      let ⟨x, hx⟩ := hf y 
      hx ▸ h x⟩

protected theorem surjective.forall₂ (hf : surjective f) {p : β → β → Prop} :
  (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
  hf.forall.trans$ forall_congrₓ$ fun x => hf.forall

protected theorem surjective.forall₃ (hf : surjective f) {p : β → β → β → Prop} :
  (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.forall.trans$ forall_congrₓ$ fun x => hf.forall₂

protected theorem surjective.exists (hf : surjective f) {p : β → Prop} : (∃ y, p y) ↔ ∃ x, p (f x) :=
  ⟨fun ⟨y, hy⟩ =>
      let ⟨x, hx⟩ := hf y
      ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

protected theorem surjective.exists₂ (hf : surjective f) {p : β → β → Prop} :
  (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
  hf.exists.trans$ exists_congr$ fun x => hf.exists

protected theorem surjective.exists₃ (hf : surjective f) {p : β → β → β → Prop} :
  (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
  hf.exists.trans$ exists_congr$ fun x => hf.exists₂

theorem surjective.injective_comp_right (hf : surjective f) : injective fun g : β → γ => g ∘ f :=
  fun g₁ g₂ h => funext$ hf.forall.2$ congr_funₓ h

protected theorem surjective.right_cancellable (hf : surjective f) {g₁ g₂ : β → γ} : g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

theorem surjective_of_right_cancellable_Prop (h : ∀ g₁ g₂ : β → Prop, g₁ ∘ f = g₂ ∘ f → g₁ = g₂) : surjective f :=
  by 
    specialize h (fun _ => True) (fun y => ∃ x, f x = y) (funext$ fun x => _)
    ·
      simp only [· ∘ ·, exists_apply_eq_applyₓ]
    ·
      intro y 
      have  : True = ∃ x, f x = y 
      exact congr_funₓ h y 
      rw [←this]
      exact trivialₓ

theorem bijective_iff_exists_unique (f : α → β) : bijective f ↔ ∀ b : β, ∃! a : α, f a = b :=
  ⟨fun hf b =>
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun a' ha' => hf.injective (ha'.trans ha.symm)⟩,
    fun he => ⟨fun a a' h => unique_of_exists_unique (he (f a')) h rfl, fun b => exists_of_exists_unique (he b)⟩⟩

/-- Shorthand for using projection notation with `function.bijective_iff_exists_unique`. -/
protected theorem bijective.exists_unique {f : α → β} (hf : bijective f) (b : β) : ∃! a : α, f a = b :=
  (bijective_iff_exists_unique f).mp hf b

theorem bijective.exists_unique_iff {f : α → β} (hf : bijective f) {p : β → Prop} : (∃! y, p y) ↔ ∃! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ =>
      let ⟨x, hx⟩ := hf.surjective y
      ⟨x,
        by 
          rwa [hx],
        fun z hz : p (f z) => hf.injective$ hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ =>
      ⟨f x, hpx,
        fun y hy =>
          let ⟨z, hz⟩ := hf.surjective y 
          hz ▸ congr_argₓ f$
            hx _$
              by 
                rwa [hz]⟩⟩

theorem bijective.of_comp_iff (f : α → β) {g : γ → α} (hg : bijective g) : bijective (f ∘ g) ↔ bijective f :=
  and_congr (injective.of_comp_iff' _ hg) (surjective.of_comp_iff _ hg.surjective)

theorem bijective.of_comp_iff' {f : α → β} (hf : bijective f) (g : γ → α) :
  Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr (injective.of_comp_iff hf.injective _) (surjective.of_comp_iff' hf _)

/-- **Cantor's diagonal argument** implies that there are no surjective functions from `α`
to `set α`. -/
theorem cantor_surjective {α} (f : α → Set α) : ¬Function.Surjective f
| h =>
  let ⟨D, e⟩ := h fun a => ¬f a a
  (iff_not_selfₓ (f D D)).1$ iff_of_eq (congr_funₓ e D)

/-- **Cantor's diagonal argument** implies that there are no injective functions from `set α`
to `α`. -/
theorem cantor_injective {α : Type _} (f : Set α → α) : ¬Function.Injective f
| i =>
  (cantor_surjective fun a b => ∀ U, a = f U → U b)$
    right_inverse.surjective fun U => funext$ fun a => propext ⟨fun h => h U rfl, fun h' U' e => i e ▸ h'⟩

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → Option α) : Prop :=
  ∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) x : g (f x) = some x :=
  (H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : injective f :=
  fun a b h => Option.some.injₓ$ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g) x y b (h₁ : b ∈ g x)
  (h₂ : b ∈ g y) : x = y :=
  ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem left_inverse.comp_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
  funext h

theorem left_inverse_iff_comp {f : α → β} {g : β → α} : left_inverse f g ↔ f ∘ g = id :=
  ⟨left_inverse.comp_eq_id, congr_funₓ⟩

theorem right_inverse.comp_eq_id {f : α → β} {g : β → α} (h : RightInverse f g) : g ∘ f = id :=
  funext h

theorem right_inverse_iff_comp {f : α → β} {g : β → α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨right_inverse.comp_eq_id, congr_funₓ⟩

theorem left_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : left_inverse f g)
  (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
  fun a =>
    show h (f (g (i a))) = a by 
      rw [hf (i a), hh a]

theorem right_inverse.comp {f : α → β} {g : β → α} {h : β → γ} {i : γ → β} (hf : RightInverse f g)
  (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
  left_inverse.comp hh hf

theorem left_inverse.right_inverse {f : α → β} {g : β → α} (h : left_inverse g f) : RightInverse f g :=
  h

theorem right_inverse.left_inverse {f : α → β} {g : β → α} (h : RightInverse g f) : left_inverse f g :=
  h

theorem left_inverse.surjective {f : α → β} {g : β → α} (h : left_inverse f g) : surjective f :=
  h.right_inverse.surjective

theorem right_inverse.injective {f : α → β} {g : β → α} (h : RightInverse f g) : injective f :=
  h.left_inverse.injective

theorem left_inverse.right_inverse_of_injective {f : α → β} {g : β → α} (h : left_inverse f g) (hf : injective f) :
  RightInverse f g :=
  fun x => hf$ h (f x)

theorem left_inverse.right_inverse_of_surjective {f : α → β} {g : β → α} (h : left_inverse f g) (hg : surjective g) :
  RightInverse f g :=
  fun x =>
    let ⟨y, hy⟩ := hg x 
    hy ▸ congr_argₓ g (h y)

theorem left_inverse.eq_right_inverse {f : α → β} {g₁ g₂ : β → α} (h₁ : left_inverse g₁ f) (h₂ : RightInverse g₂ f) :
  g₁ = g₂ :=
  calc g₁ = g₁ ∘ f ∘ g₂ :=
    by 
      rw [h₂.comp_eq_id, comp.right_id]
    _ = g₂ :=
    by 
      rw [←comp.assoc, h₁.comp_eq_id, comp.left_id]
    

attribute [local instance] Classical.propDecidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : Option α :=
  if h : ∃ a, f a = b then some (Classical.some h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : injective f) : is_partial_inv f (partial_inv f)
| a, b =>
  ⟨fun h =>
      if h' : ∃ a, f a = b then
        by 
          rw [partial_inv, dif_pos h'] at h 
          injection h with h 
          subst h 
          apply Classical.some_spec h'
      else
        by 
          rw [partial_inv, dif_neg h'] at h <;> contradiction,
    fun e =>
      e ▸
        have h : ∃ a', f a' = f a := ⟨_, rfl⟩
        (dif_pos h).trans (congr_argₓ _ (I$ Classical.some_spec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : injective f) : ∀ x, partial_inv f (f x) = some x :=
  is_partial_inv_left (partial_inv_of_injective I)

end 

section InvFunOn

variable {α : Type u} [n : Nonempty α] {β : Sort v} {f : α → β} {s : Set α} {a : α} {b : β}

include n

attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def inv_fun_on (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.some h else Classical.choice n

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
theorem inv_fun_on_pos (h : ∃ (a : _)(_ : a ∈ s), f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
  by 
    rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.some_spec h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
theorem inv_fun_on_mem (h : ∃ (a : _)(_ : a ∈ s), f a = b) : inv_fun_on f s b ∈ s :=
  (inv_fun_on_pos h).left

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
theorem inv_fun_on_eq (h : ∃ (a : _)(_ : a ∈ s), f a = b) : f (inv_fun_on f s b) = b :=
  (inv_fun_on_pos h).right

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a' «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem inv_fun_on_eq' (h : ∀ x _ : x ∈ s y _ : y ∈ s, f x = f y → x = y) (ha : a ∈ s) : inv_fun_on f s (f a) = a :=
  have  : ∃ (a' : _)(_ : a' ∈ s), f a' = f a := ⟨a, ha, rfl⟩
  h _ (inv_fun_on_mem this) _ ha (inv_fun_on_eq this)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » s)
theorem inv_fun_on_neg (h : ¬∃ (a : _)(_ : a ∈ s), f a = b) : inv_fun_on f s b = Classical.choice n :=
  by 
    rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]

end InvFunOn

section InvFun

variable {α β : Sort _} [Nonempty α] {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α :=
  fun y => if h : ∃ x, f x = y then h.some else Classical.arbitrary α

theorem inv_fun_eq (h : ∃ a, f a = b) : f (inv_fun f b) = b :=
  by 
    simp only [inv_fun, dif_pos h, h.some_spec]

theorem inv_fun_neg (h : ¬∃ a, f a = b) : inv_fun f b = Classical.choice ‹_› :=
  dif_neg h

theorem inv_fun_eq_of_injective_of_right_inverse {g : β → α} (hf : injective f) (hg : RightInverse g f) :
  inv_fun f = g :=
  funext$
    fun b =>
      hf
        (by 
          rw [hg b]
          exact inv_fun_eq ⟨g b, hg b⟩)

theorem right_inverse_inv_fun (hf : surjective f) : RightInverse (inv_fun f) f :=
  fun b => inv_fun_eq$ hf b

theorem left_inverse_inv_fun (hf : injective f) : left_inverse (inv_fun f) f :=
  fun b => hf$ inv_fun_eq ⟨b, rfl⟩

theorem inv_fun_surjective (hf : injective f) : surjective (inv_fun f) :=
  (left_inverse_inv_fun hf).Surjective

theorem inv_fun_comp (hf : injective f) : inv_fun f ∘ f = id :=
  funext$ left_inverse_inv_fun hf

theorem injective.has_left_inverse (hf : injective f) : has_left_inverse f :=
  ⟨inv_fun f, left_inverse_inv_fun hf⟩

theorem injective_iff_has_left_inverse : injective f ↔ has_left_inverse f :=
  ⟨injective.has_left_inverse, has_left_inverse.injective⟩

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surj_inv {f : α → β} (h : surjective f) (b : β) : α :=
  Classical.some (h b)

theorem surj_inv_eq (h : surjective f) b : f (surj_inv h b) = b :=
  Classical.some_spec (h b)

theorem right_inverse_surj_inv (hf : surjective f) : RightInverse (surj_inv hf) f :=
  surj_inv_eq hf

theorem left_inverse_surj_inv (hf : bijective f) : left_inverse (surj_inv hf.2) f :=
  right_inverse_of_injective_of_left_inverse hf.1 (right_inverse_surj_inv hf.2)

theorem surjective.has_right_inverse (hf : surjective f) : has_right_inverse f :=
  ⟨_, right_inverse_surj_inv hf⟩

theorem surjective_iff_has_right_inverse : surjective f ↔ has_right_inverse f :=
  ⟨surjective.has_right_inverse, has_right_inverse.surjective⟩

theorem bijective_iff_has_inverse : bijective f ↔ ∃ g, left_inverse g f ∧ RightInverse g f :=
  ⟨fun hf => ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩,
    fun ⟨g, gl, gr⟩ => ⟨gl.injective, gr.surjective⟩⟩

theorem injective_surj_inv (h : surjective f) : injective (surj_inv h) :=
  (right_inverse_surj_inv h).Injective

theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α → β) : surjective f :=
  fun y =>
    let ⟨a⟩ := na
    ⟨a, Subsingleton.elimₓ _ _⟩

/-- Composition by an surjective function on the left is itself surjective. -/
theorem surjective.comp_left {g : β → γ} (hg : surjective g) : surjective ((· ∘ ·) g : (α → β) → α → γ) :=
  fun f => ⟨surj_inv hg ∘ f, funext$ fun x => right_inverse_surj_inv _ _⟩

/-- Composition by an bijective function on the left is itself bijective. -/
theorem bijective.comp_left {g : β → γ} (hg : bijective g) : bijective ((· ∘ ·) g : (α → β) → α → γ) :=
  ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

end SurjInv

section Update

variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α] [DecidableEq α']

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
theorem update_apply {β : Sort _} (f : α → β) (a' : α) (b : β) (a : α) : update f a' b a = if a = a' then b else f a :=
  by 
    dunfold update 
    congr 
    funext 
    rw [eq_rec_constant]

@[simp]
theorem update_same (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

theorem surjective_eval {α : Sort u} {β : α → Sort v} [h : ∀ a, Nonempty (β a)] (a : α) :
  surjective (eval a : (∀ a, β a) → β a) :=
  fun b => ⟨@update _ _ (Classical.decEq α) (fun a => (h a).some) a b, @update_same _ _ (Classical.decEq α) _ _ _⟩

theorem update_injective (f : ∀ a, β a) (a' : α) : injective (update f a') :=
  fun v v' h =>
    have  := congr_funₓ h a' 
    by 
      rwa [update_same, update_same] at this

@[simp]
theorem update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ≠ » a)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  forall_update_iff
  ( f : ∀ a , β a ) { a : α } { b : β a } ( p : ∀ a , β a → Prop )
    : ∀ x , p x update f a b x ↔ p a b ∧ ∀ x _ : x ≠ a , p x f x
  := by rw [ ← and_forall_ne a , update_same ] simp ( config := { contextual := Bool.true._@._internal._hyg.0 } )

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ≠ » a)
theorem exists_update_iff (f : ∀ a, β a) {a : α} {b : β a} (p : ∀ a, β a → Prop) :
  (∃ x, p x (update f a b x)) ↔ p a b ∨ ∃ (x : _)(_ : x ≠ a), p x (f x) :=
  by 
    rw [←not_forall_not, forall_update_iff f fun a b => ¬p a b]
    simp [not_and_distrib]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ≠ » a)
theorem update_eq_iff {a : α} {b : β a} {f g : ∀ a, β a} : update f a b = g ↔ b = g a ∧ ∀ x _ : x ≠ a, f x = g x :=
  funext_iff.trans$ forall_update_iff _ fun x y => y = g x

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ≠ » a)
theorem eq_update_iff {a : α} {b : β a} {f g : ∀ a, β a} : g = update f a b ↔ g a = b ∧ ∀ x _ : x ≠ a, g x = f x :=
  funext_iff.trans$ forall_update_iff _ fun x y => g x = y

@[simp]
theorem update_eq_self (a : α) (f : ∀ a, β a) : update f a (f a) = f :=
  update_eq_iff.2 ⟨rfl, fun _ _ => rfl⟩

theorem update_comp_eq_of_forall_ne' {α'} (g : ∀ a, β a) {f : α' → α} {i : α} (a : β i) (h : ∀ x, f x ≠ i) :
  (fun j => (update g i a) (f j)) = fun j => g (f j) :=
  funext$ fun x => update_noteq (h _) _ _

/-- Non-dependent version of `function.update_comp_eq_of_forall_ne'` -/
theorem update_comp_eq_of_forall_ne {α β : Sort _} (g : α' → β) {f : α → α'} {i : α'} (a : β) (h : ∀ x, f x ≠ i) :
  update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

theorem update_comp_eq_of_injective' (g : ∀ a, β a) {f : α' → α} (hf : Function.Injective f) (i : α') (a : β (f i)) :
  (fun j => update g (f i) a (f j)) = update (fun i => g (f i)) i a :=
  eq_update_iff.2 ⟨update_same _ _ _, fun j hj => update_noteq (hf.ne hj) _ _⟩

/-- Non-dependent version of `function.update_comp_eq_of_injective'` -/
theorem update_comp_eq_of_injective {β : Sort _} (g : α' → β) {f : α → α'} (hf : Function.Injective f) (i : α) (a : β) :
  Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

theorem apply_update {ι : Sort _} [DecidableEq ι] {α β : ι → Sort _} (f : ∀ i, α i → β i) (g : ∀ i, α i) (i : ι)
  (v : α i) (j : ι) : f j (update g i v j) = update (fun k => f k (g k)) i (f i v) j :=
  by 
    byCases' h : j = i
    ·
      subst j 
      simp 
    ·
      simp [h]

theorem apply_update₂ {ι : Sort _} [DecidableEq ι] {α β γ : ι → Sort _} (f : ∀ i, α i → β i → γ i) (g : ∀ i, α i)
  (h : ∀ i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
  f j (update g i v j) (update h i w j) = update (fun k => f k (g k) (h k)) i (f i v w) j :=
  by 
    byCases' h : j = i
    ·
      subst j 
      simp 
    ·
      simp [h]

theorem comp_update {α' : Sort _} {β : Sort _} (f : α' → β) (g : α → α') (i : α) (v : α') :
  f ∘ update g i v = update (f ∘ g) i (f v) :=
  funext$ apply_update _ _ _ _

theorem update_comm {α} [DecidableEq α] {β : α → Sort _} {a b : α} (h : a ≠ b) (v : β a) (w : β b) (f : ∀ a, β a) :
  update (update f a v) b w = update (update f b w) a v :=
  by 
    funext c 
    simp only [update]
    byCases' h₁ : c = b <;>
      byCases' h₂ : c = a <;>
        try 
          simp [h₁, h₂]
    cases h (h₂.symm.trans h₁)

@[simp]
theorem update_idem {α} [DecidableEq α] {β : α → Sort _} {a : α} (v w : β a) (f : ∀ a, β a) :
  update (update f a v) a w = update f a w :=
  by 
    funext b 
    byCases' b = a <;> simp [update, h]

end Update

section Extend

noncomputable section 

attribute [local instance] Classical.propDecidable

variable {α β γ : Sort _} {f : α → β}

/-- `extend f g e'` extends a function `g : α → γ`
along a function `f : α → β` to a function `β → γ`,
by using the values of `g` on the range of `f`
and the values of an auxiliary function `e' : β → γ` elsewhere.

Mostly useful when `f` is injective. -/
def extend (f : α → β) (g : α → γ) (e' : β → γ) : β → γ :=
  fun b => if h : ∃ a, f a = b then g (Classical.some h) else e' b

theorem extend_def (f : α → β) (g : α → γ) (e' : β → γ) (b : β) [Decidable (∃ a, f a = b)] :
  extend f g e' b = if h : ∃ a, f a = b then g (Classical.some h) else e' b :=
  by 
    unfold extend 
    congr

@[simp]
theorem extend_apply (hf : injective f) (g : α → γ) (e' : β → γ) (a : α) : extend f g e' (f a) = g a :=
  by 
    simp only [extend_def, dif_pos, exists_apply_eq_applyₓ]
    exact congr_argₓ g (hf$ Classical.some_spec (exists_apply_eq_applyₓ f a))

@[simp]
theorem extend_apply' (g : α → γ) (e' : β → γ) (b : β) (hb : ¬∃ a, f a = b) : extend f g e' b = e' b :=
  by 
    simp [Function.extend_defₓ, hb]

theorem extend_injective (hf : injective f) (e' : β → γ) : injective fun g => extend f g e' :=
  by 
    intro g₁ g₂ hg 
    refine' funext fun x => _ 
    have H := congr_funₓ hg (f x)
    simp only [hf, extend_apply] at H 
    exact H

@[simp]
theorem extend_comp (hf : injective f) (g : α → γ) (e' : β → γ) : extend f g e' ∘ f = g :=
  funext$ fun a => extend_apply hf g e' a

theorem injective.surjective_comp_right' (hf : injective f) (g₀ : β → γ) : surjective fun g : β → γ => g ∘ f :=
  fun g => ⟨extend f g g₀, extend_comp hf _ _⟩

theorem injective.surjective_comp_right [Nonempty γ] (hf : injective f) : surjective fun g : β → γ => g ∘ f :=
  hf.surjective_comp_right' fun _ => Classical.choice ‹_›

theorem bijective.comp_right (hf : bijective f) : bijective fun g : β → γ => g ∘ f :=
  ⟨hf.surjective.injective_comp_right,
    fun g =>
      ⟨g ∘ surj_inv hf.surjective,
        by 
          simp only [comp.assoc g _ f, (left_inverse_surj_inv hf).comp_eq_id, comp.right_id]⟩⟩

end Extend

theorem uncurry_def {α β γ} (f : α → β → γ) : uncurry f = fun p => f p.1 p.2 :=
  rfl

@[simp]
theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) : uncurry f (x, y) = f x y :=
  rfl

@[simp]
theorem curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

section Bicomp

variable {α β γ δ ε : Type _}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) a b :=
  f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) a b :=
  f (g a b)

local notation f "∘₂" g => bicompr f g

theorem uncurry_bicompr (f : α → β → γ) (g : γ → δ) : uncurry (g∘₂f) = g ∘ uncurry f :=
  rfl

theorem uncurry_bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) : uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h :=
  rfl

end Bicomp

section Uncurry

variable {α β γ δ : Type _}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. The most generic use
is to recursively uncurry. For instance `f : α → β → γ → δ` will be turned into
`↿f : α × β × γ → δ`. One can also add instances for bundled maps. -/
class has_uncurry (α : Type _) (β : outParam (Type _)) (γ : outParam (Type _)) where 
  uncurry : α → β → γ

/-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
`f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
for bundled maps.-/
add_decl_doc has_uncurry.uncurry

-- ././Mathport/Syntax/Translate/Basic.lean:308:9: unsupported: advanced prec syntax
-- ././Mathport/Syntax/Translate/Basic.lean:308:9: unsupported: advanced prec syntax
notation:999 "↿" x:999 => has_uncurry.uncurry x

instance has_uncurry_base : has_uncurry (α → β) α β :=
  ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
  ⟨fun f p => (↿f p.1) p.2⟩

end Uncurry

/-- A function is involutive, if `f ∘ f = id`. -/
def involutive {α} (f : α → α) : Prop :=
  ∀ x, f (f x) = x

theorem involutive_iff_iter_2_eq_id {α} {f : α → α} : involutive f ↔ f^[2] = id :=
  funext_iff.symm

namespace Involutive

variable {α : Sort u} {f : α → α} (h : involutive f)

include h

@[simp]
theorem comp_self : f ∘ f = id :=
  funext h

protected theorem left_inverse : left_inverse f f :=
  h

protected theorem RightInverse : RightInverse f f :=
  h

protected theorem injective : injective f :=
  h.left_inverse.injective

protected theorem surjective : surjective f :=
  fun x => ⟨f x, h x⟩

protected theorem bijective : bijective f :=
  ⟨h.injective, h.surjective⟩

/-- Involuting an `ite` of an involuted value `x : α` negates the `Prop` condition in the `ite`. -/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) : f (ite P x (f x)) = ite (¬P) x (f x) :=
  by 
    rw [apply_ite f, h, ite_not]

/-- An involution commutes across an equality. Compare to `function.injective.eq_iff`. -/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.injective.eq_iff' (h y)

end Involutive

/-- The property of a binary function `f : α → β → γ` being injective.
Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
@[reducible]
def injective2 {α β γ} (f : α → β → γ) : Prop :=
  ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Type _} (f : α → β → γ)

protected theorem left (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : a₁ = a₂ :=
  (hf h).1

protected theorem right (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : b₁ = b₂ :=
  (hf h).2

theorem eq_iff (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h => hf h, fun ⟨h1, h2⟩ => congr_arg2ₓ f h1 h2⟩

end Injective2

section Sometimes

attribute [local instance] Classical.propDecidable

/-- `sometimes f` evaluates to some value of `f`, if it exists. This function is especially
interesting in the case where `α` is a proposition, in which case `f` is necessarily a
constant function, so that `sometimes f = f a` for all `a`. -/
noncomputable def sometimes {α β} [Nonempty β] (f : α → β) : β :=
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p → α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩

theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α → Prop) (f : p → α) (a : p) (h : P (f a)) : P (sometimes f) :=
  by 
    rwa [sometimes_eq]

end Sometimes

end Function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def Set.piecewise {α : Type u} {β : α → Sort v} (s : Set α) (f g : ∀ i, β i) [∀ j, Decidable (j ∈ s)] : ∀ i, β i :=
  fun i => if i ∈ s then f i else g i

/-! ### Bijectivity of `eq.rec`, `eq.mp`, `eq.mpr`, and `cast` -/


theorem eq_rec_on_bijective {α : Sort _} {C : α → Sort _} :
  ∀ {a a' : α} h : a = a', Function.Bijective (@Eq.recOnₓ _ _ C _ h)
| _, _, rfl => ⟨fun x y => id, fun x => ⟨x, rfl⟩⟩

theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) :=
  eq_rec_on_bijective h

theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) :=
  eq_rec_on_bijective h.symm

theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) :=
  eq_rec_on_bijective h

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway.-/


@[simp]
theorem eq_rec_inj {α : Sort _} {a a' : α} (h : a = a') {C : α → Type _} (x y : C a) :
  (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).Injective.eq_iff

@[simp]
theorem cast_inj {α β : Type _} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).Injective.eq_iff

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (f «expr ∈ » A)
/-- A set of functions "separates points"
if for each pair of distinct points there is a function taking different values on them. -/
def Set.SeparatesPoints {α β : Type _} (A : Set (α → β)) : Prop :=
  ∀ ⦃x y : α⦄, x ≠ y → ∃ (f : _)(_ : f ∈ A), (f x : β) ≠ f y

theorem IsSymmOp.flip_eq {α β} op [IsSymmOp α β op] : flip op = op :=
  funext$ fun a => funext$ fun b => (IsSymmOp.symm_op a b).symm

