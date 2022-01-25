import Mathbin.Data.Equiv.Basic
import Mathbin.Data.Set.Basic
import Mathbin.Data.Sigma.Basic
import Mathbin.Data.Pprod

/-!
# Injective functions
-/


universe u v w x

namespace Function

/-- `α ↪ β` is a bundled injective function. -/
@[nolint has_inhabited_instance]
structure embedding (α : Sort _) (β : Sort _) where
  toFun : α → β
  inj' : injective to_fun

infixr:25 " ↪ " => embedding

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) fun _ => α → β :=
  ⟨embedding.to_fun⟩

initialize_simps_projections Embedding (toFun → apply)

end Function

section Equivₓ

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `equiv.coe_embedding`.
The explicit `equiv.to_embedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f.to_embedding = s.map f := by simp
-- Error, `f` has type `fin 3 ≃ fin 3` but is expected to have type `fin 3 ↪ ?m_1 : Type ?`
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f = s.map f.to_embedding := by simp
```
-/
@[simps]
protected def Equivₓ.toEmbedding : α ↪ β :=
  ⟨f, f.injective⟩

instance Equivₓ.coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equivₓ.toEmbedding⟩

@[reducible]
instance Equivₓ.Perm.coeEmbedding : Coe (Equivₓ.Perm α) (α ↪ α) :=
  Equivₓ.coeEmbedding

@[simp]
theorem Equivₓ.coe_eq_to_embedding : ↑f = f.to_embedding :=
  rfl

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps]
def Equivₓ.asEmbedding {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  ⟨coe ∘ e, Subtype.coe_injective.comp e.injective⟩

@[simp]
theorem Equivₓ.as_embedding_range {α β : Sort _} {p : β → Prop} (e : α ≃ Subtype p) :
    Set.Range e.as_embedding = SetOf p :=
  Set.ext $ fun x =>
    ⟨fun ⟨y, h⟩ => h ▸ Subtype.coe_prop (e y), fun hs =>
      ⟨e.symm ⟨x, hs⟩, by
        simp ⟩⟩

end Equivₓ

namespace Function

namespace Embedding

theorem coe_injective {α β} : @Function.Injective (α ↪ β) (α → β) coeFn
  | ⟨x, _⟩, ⟨y, _⟩, rfl => rfl

@[ext]
theorem ext {α β} {f g : embedding α β} (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {α β} {f g : embedding α β} : (∀ x, f x = g x) ↔ f = g :=
  ⟨ext, fun h _ => by
    rw [h]⟩

@[simp]
theorem to_fun_eq_coe {α β} (f : α ↪ β) : to_fun f = f :=
  rfl

@[simp]
theorem coe_fn_mk {α β} (f : α → β) i : (@mk _ _ f i : α → β) = f :=
  rfl

@[simp]
theorem mk_coe {α β : Type _} (f : α ↪ β) inj : (⟨f, inj⟩ : α ↪ β) = f := by
  ext
  simp

protected theorem injective {α β} (f : α ↪ β) : injective f :=
  f.inj'

@[simp]
theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  f.injective.eq_iff

/-- The identity map as a `function.embedding`. -/
@[refl, simps (config := { simpRhs := tt })]
protected def refl (α : Sort _) : α ↪ α :=
  ⟨id, injective_id⟩

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps (config := { simpRhs := tt })]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.injective.comp f.injective⟩

@[simp]
theorem equiv_to_embedding_trans_symm_to_embedding {α β : Sort _} (e : α ≃ β) :
    e.to_embedding.trans e.symm.to_embedding = embedding.refl _ := by
  ext
  simp

@[simp]
theorem equiv_symm_to_embedding_trans_to_embedding {α β : Sort _} (e : α ≃ β) :
    e.symm.to_embedding.trans e.to_embedding = embedding.refl _ := by
  ext
  simp

/-- Transfer an embedding along a pair of equivalences. -/
@[simps (config := { fullyApplied := ff })]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : β ↪ δ :=
  (Equivₓ.toEmbedding e₁.symm).trans (f.trans e₂.to_embedding)

/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def of_surjective {α β} (f : β → α) (hf : surjective f) : α ↪ β :=
  ⟨surj_inv hf, injective_surj_inv _⟩

/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equiv_of_surjective {α β} (f : α ↪ β) (hf : surjective f) : α ≃ β :=
  Equivₓ.ofBijective f ⟨f.injective, hf⟩

/-- There is always an embedding from an empty type. --/
protected def of_is_empty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def set_value {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    dsimp  at h
    split_ifs  at h <;>
      try
          subst b <;>
        try
            simp only [f.injective.eq_iff] at * <;>
          cc⟩

theorem set_value_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] :
    set_value f a b a = b := by
  simp [set_value]

/-- Embedding into `option α` using `some`. -/
@[simps (config := { fullyApplied := ff })]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩

/-- Embedding into `option α` using `coe`. Usually the correct synctatical form for `simp`. -/
@[simps (config := { fullyApplied := ff })]
def coeOption {α} : α ↪ Option α :=
  ⟨coe, Option.some_injective α⟩

/-- Embedding into `with_top α`. -/
@[simps]
def coe_with_top {α} : α ↪ WithTop α :=
  { embedding.some with toFun := coe }

/-- Given an embedding `f : α ↪ β` and a point outside of `set.range f`, construct an embedding
`option α ↪ β`. -/
@[simps]
def option_elim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.Range f) : Option α ↪ β :=
  ⟨fun o => o.elim x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

/-- Embedding of a `subtype`. -/
def Subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨coe, fun _ _ => Subtype.ext_val⟩

@[simp]
theorem coeSubtype {α} (p : α → Prop) : ⇑Subtype p = coe :=
  rfl

/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def PUnit {β : Sort _} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun a a' h => congr_argₓ Prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun b b' h => congr_argₓ Prod.snd h⟩

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a => ⟨f a, H a⟩, fun a b h => f.injective (@congr_argₓ _ _ _ _ Subtype.val h)⟩

@[simp]
theorem cod_restrict_apply {α β} p (f : α ↪ β) H a : cod_restrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prod_mapₓ {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.injective.prod_map e₂.injective⟩

@[simp]
theorem coe_prod_map {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑e₁.prod_map e₂ = Prod.map e₁ e₂ :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `λ ⟨a, b⟩, ⟨e₁ a, e₂ b⟩ : pprod α γ → pprod β δ`. -/
def pprod_map {α β γ δ : Sort _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

section Sum

open Sum

/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sum_map {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, fun s₁ s₂ h =>
    match s₁, s₂, h with
    | inl a₁, inl a₂, h => congr_argₓ inl $ e₁.injective $ inl.inj h
    | inr b₁, inr b₂, h => congr_argₓ inr $ e₂.injective $ inr.inj h⟩

@[simp]
theorem coe_sum_map {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑sum_map e₁ e₂ = Sum.map e₁ e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type _} : α ↪ Sum α β :=
  ⟨Sum.inl, fun a b => Sum.inl.injₓ⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type _} : β ↪ Sum α β :=
  ⟨Sum.inr, fun a b => Sum.inr.injₓ⟩

end Sum

section Sigma

variable {α α' : Type _} {β : α → Type _} {β' : α' → Type _}

/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply]
def sigma_mk (a : α) : β a ↪ Σ x, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply]
def sigma_map (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σ a, β a) ↪ Σ a', β' a' :=
  ⟨Sigma.map f fun a => g a, f.injective.sigma_map fun a => (g a).Injective⟩

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `λ a, e a (f a)`. -/
@[simps]
def Pi_congr_right {α : Sort _} {β γ : α → Sort _} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun f₁ f₂ h => funext $ fun a => (e a).Injective (congr_funₓ h a)⟩

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrow_congr_right {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  Pi_congr_right fun _ => e

@[simp]
theorem arrow_congr_right_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ ↪ α) :
    arrow_congr_right e f = e ∘ f :=
  rfl

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrow_congr_left {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) : (α → γ) ↪ β → γ :=
  ⟨fun f => extend e f fun _ => default, fun f₁ f₂ h =>
    funext $ fun x => by
      simpa only [extend_apply e.injective] using congr_funₓ h (e x)⟩

/-- Restrict both domain and codomain of an embedding. -/
protected def subtype_map {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β) (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

open Set

/-- `set.image` as an embedding `set α ↪ set β`. -/
@[simps apply]
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩

theorem swap_apply {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equivₓ.swap (f x) (f y) (f z) = f (Equivₓ.swap x y z) :=
  f.injective.swap_apply x y z

theorem swap_comp {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equivₓ.swap (f x) (f y) ∘ f = f ∘ Equivₓ.swap x y :=
  f.injective.swap_comp x y

end Embedding

end Function

namespace Equivₓ

open Function.Embedding

/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtype_injective_equiv_embedding (α β : Sort _) : { f : α → β // Function.Injective f } ≃ (α ↪ β) where
  toFun := fun f => ⟨f.val, f.property⟩
  invFun := fun f => ⟨f, f.injective⟩
  left_inv := fun f => by
    simp
  right_inv := fun f => by
    ext
    rfl

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[congr, simps apply]
def embedding_congr {α β γ δ : Sort _} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun := fun f => f.congr h h'
  invFun := fun f => f.congr h.symm h'.symm
  left_inv := fun x => by
    ext
    simp
  right_inv := fun x => by
    ext
    simp

@[simp]
theorem embedding_congr_refl {α β : Sort _} : embedding_congr (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (α ↪ β) :=
  by
  ext
  rfl

@[simp]
theorem embedding_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃)
    (e₂' : β₂ ≃ β₃) :
    embedding_congr (e₁.trans e₂) (e₁'.trans e₂') = (embedding_congr e₁ e₁').trans (embedding_congr e₂ e₂') :=
  rfl

@[simp]
theorem embedding_congr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embedding_congr e₁ e₂).symm = embedding_congr e₁.symm e₂.symm :=
  rfl

theorem embedding_congr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equivₓ.embeddingCongr ea ec (f.trans g) = (Equivₓ.embeddingCongr ea eb f).trans (Equivₓ.embeddingCongr eb ec g) :=
  by
  ext
  simp

@[simp]
theorem refl_to_embedding {α : Type _} : (Equivₓ.refl α).toEmbedding = Function.Embedding.refl α :=
  rfl

@[simp]
theorem trans_to_embedding {α β γ : Type _} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.to_embedding.trans f.to_embedding :=
  rfl

end Equivₓ

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply]
def embedding_of_subset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x => ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h => by
    congr
    injection h⟩

end Set

section Subtype

variable {α : Type _}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] : { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.prop.resolve_left h⟩, by
    intro x y
    dsimp only
    split_ifs <;> simp [Subtype.ext_iff]⟩

theorem subtype_or_left_embedding_apply_left {p q : α → Prop} [DecidablePred p] (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx

theorem subtype_or_left_embedding_apply_right {p q : α → Prop} [DecidablePred p] (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
  dif_neg hx

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps]
def Subtype.impEmbedding (p q : α → Prop) (h : p ≤ q) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.prop⟩, fun x y => by
    simp [Subtype.ext_iff]⟩

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`disjoint p q`.

See also `equiv.sum_compl`, for when `is_compl p q`.  -/
@[simps apply]
def subtypeOrEquiv (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ Sum { x // p x } { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx => (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx => (Or.inr hx : p x ∨ q x))
  left_inv := fun x => by
    by_cases' hx : p x
    · rw [subtype_or_left_embedding_apply_left _ hx]
      simp [Subtype.ext_iff]
      
    · rw [subtype_or_left_embedding_apply_right _ hx]
      simp [Subtype.ext_iff]
      
  right_inv := fun x => by
    cases x
    · simp only [Sum.elim_inl]
      rw [subtype_or_left_embedding_apply_left]
      · simp
        
      · simpa using x.prop
        
      
    · simp only [Sum.elim_inr]
      rw [subtype_or_left_embedding_apply_right]
      · simp
        
      · suffices ¬p x by
          simpa
        intro hp
        simpa using h x ⟨hp, x.prop⟩
        
      

@[simp]
theorem subtype_or_equiv_symm_inl (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) (x : { x // p x }) :
    (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.prop⟩ :=
  rfl

@[simp]
theorem subtype_or_equiv_symm_inr (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) (x : { x // q x }) :
    (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.prop⟩ :=
  rfl

end Subtype

