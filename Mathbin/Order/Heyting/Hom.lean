/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Lattice

/-!
# Heyting algebra morphisms

A Heyting homomorphism between two Heyting algebras is a bounded lattice homomorphism that preserves
Heyting implication.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `heyting_hom`: Heyting homomorphisms.
* `coheyting_hom`: Co-Heyting homomorphisms.
* `biheyting_hom`: Bi-Heyting homomorphisms.

## Typeclasses

* `heyting_hom_class`
* `coheyting_hom_class`
* `biheyting_hom_class`
-/


open Function

variable {F α β γ δ : Type _}

/-- The type of Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that preserve
Heyting implication. -/
@[protect_proj]
structure HeytingHom (α β : Type _) [HeytingAlgebra α] [HeytingAlgebra β] extends LatticeHom α β where
  map_bot' : to_fun ⊥ = ⊥
  map_himp' : ∀ a b, to_fun (a ⇨ b) = to_fun a ⇨ to_fun b

/-- The type of co-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve difference. -/
@[protect_proj]
structure CoheytingHom (α β : Type _) [CoheytingAlgebra α] [CoheytingAlgebra β] extends LatticeHom α β where
  map_top' : to_fun ⊤ = ⊤
  map_sdiff' : ∀ a b, to_fun (a \ b) = to_fun a \ to_fun b

/-- The type of bi-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve Heyting implication and difference. -/
@[protect_proj]
structure BiheytingHom (α β : Type _) [BiheytingAlgebra α] [BiheytingAlgebra β] extends LatticeHom α β where
  map_himp' : ∀ a b, to_fun (a ⇨ b) = to_fun a ⇨ to_fun b
  map_sdiff' : ∀ a b, to_fun (a \ b) = to_fun a \ to_fun b

/-- `heyting_hom_class F α β` states that `F` is a type of Heyting homomorphisms.

You should extend this class when you extend `heyting_hom`. -/
class HeytingHomClass (F : Type _) (α β : outParam <| Type _) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHomClass F α β where
  map_bot (f : F) : f ⊥ = ⊥
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b

/-- `coheyting_hom_class F α β` states that `F` is a type of co-Heyting homomorphisms.

You should extend this class when you extend `coheyting_hom`. -/
class CoheytingHomClass (F : Type _) (α β : outParam <| Type _) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

/-- `biheyting_hom_class F α β` states that `F` is a type of bi-Heyting homomorphisms.

You should extend this class when you extend `biheyting_hom`. -/
class BiheytingHomClass (F : Type _) (α β : outParam <| Type _) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHomClass F α β where
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

export HeytingHomClass (map_himp)

export CoheytingHomClass (map_sdiff)

attribute [simp] map_himp map_sdiff

-- See note [lower instance priority]
instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [HeytingAlgebra α] [HeytingAlgebra β]
    [HeytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

-- See note [lower instance priority]
instance (priority := 100) CoheytingHomClass.toBoundedLatticeHomClass [CoheytingAlgebra α] [CoheytingAlgebra β]
    [CoheytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹CoheytingHomClass F α β› with map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, map_sdiff] }

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toHeytingHomClass [BiheytingAlgebra α] [BiheytingAlgebra β]
    [BiheytingHomClass F α β] : HeytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, BiheytingHomClass.map_sdiff] }

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toCoheytingHomClass [BiheytingAlgebra α] [BiheytingAlgebra β]
    [BiheytingHomClass F α β] : CoheytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toHeytingHomClass [HeytingAlgebra α] [HeytingAlgebra β] [OrderIsoClass F α β] :
    HeytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iffₓ fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCoheytingHomClass [CoheytingAlgebra α] [CoheytingAlgebra β]
    [OrderIsoClass F α β] : CoheytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iffₓ fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBiheytingHomClass [BiheytingAlgebra α] [BiheytingAlgebra β]
    [OrderIsoClass F α β] : BiheytingHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iffₓ fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp,
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iffₓ fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [reducible non instances]
/-- This can't be an instance because of typeclass loops. -/
@[reducible]
def BoundedLatticeHomClass.toBiheytingHomClass [BooleanAlgebra α] [BooleanAlgebra β] [BoundedLatticeHomClass F α β] :
    BiheytingHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (is_compl_compl.map _).compl_eq],
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (is_compl_compl.map _).compl_eq] }

section HeytingAlgebra

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] (f : F)

include β

@[simp]
theorem map_compl (a : α) : f (aᶜ) = f aᶜ := by rw [← himp_bot, ← himp_bot, map_himp, map_bot]

@[simp]
theorem map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b := by simp_rw [bihimp, map_inf, map_himp]

-- TODO: `map_bihimp`
end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] (f : F)

include β

@[simp]
theorem map_hnot (a : α) : f (￢a) = ￢f a := by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]

@[simp]
theorem map_symm_diff (a b : α) : f (a ∆ b) = f a ∆ f b := by simp_rw [symmDiff, map_sup, map_sdiff]

end CoheytingAlgebra

instance [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTₓ F (HeytingHom α β) :=
  ⟨fun f =>
    { toFun := f, map_sup' := map_sup f, map_inf' := map_inf f, map_bot' := map_bot f, map_himp' := map_himp f }⟩

instance [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] : CoeTₓ F (CoheytingHom α β) :=
  ⟨fun f =>
    { toFun := f, map_sup' := map_sup f, map_inf' := map_inf f, map_top' := map_top f, map_sdiff' := map_sdiff f }⟩

instance [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingHomClass F α β] : CoeTₓ F (BiheytingHom α β) :=
  ⟨fun f =>
    { toFun := f, map_sup' := map_sup f, map_inf' := map_inf f, map_himp' := map_himp f, map_sdiff' := map_sdiff f }⟩

namespace HeytingHom

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]

instance : HeytingHomClass (HeytingHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'
  map_bot := fun f => f.map_bot'
  map_himp := HeytingHom.map_himp'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (HeytingHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : HeytingHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `heyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : HeytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f

variable (α)

/-- `id` as a `heyting_hom`. -/
protected def id : HeytingHom α α :=
  { BotHom.id _ with toLatticeHom := LatticeHom.id _, map_himp' := fun a b => rfl }

@[simp]
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl

instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩

instance : PartialOrderₓ (HeytingHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

/-- Composition of `heyting_hom`s as a `heyting_hom`. -/
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with toFun := f ∘ g, map_bot' := by simp, map_himp' := fun a b => by simp }

variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}

@[simp]
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end HeytingHom

namespace CoheytingHom

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingAlgebra γ] [CoheytingAlgebra δ]

instance : CoheytingHomClass (CoheytingHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'
  map_top := fun f => f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CoheytingHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : CoheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `coheyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : CoheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f

variable (α)

/-- `id` as a `coheyting_hom`. -/
protected def id : CoheytingHom α α :=
  { TopHom.id _ with toLatticeHom := LatticeHom.id _, map_sdiff' := fun a b => rfl }

@[simp]
theorem coe_id : ⇑(CoheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : CoheytingHom.id α a = a :=
  rfl

instance : Inhabited (CoheytingHom α α) :=
  ⟨CoheytingHom.id _⟩

instance : PartialOrderₓ (CoheytingHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

/-- Composition of `coheyting_hom`s as a `coheyting_hom`. -/
def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with toFun := f ∘ g, map_top' := by simp, map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : CoheytingHom α β} {g g₁ g₂ : CoheytingHom β γ}

@[simp]
theorem coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => CoheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CoheytingHom

namespace BiheytingHom

variable [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingAlgebra γ] [BiheytingAlgebra δ]

instance : BiheytingHomClass (BiheytingHom α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'
  map_himp := fun f => f.map_himp'
  map_sdiff := fun f => f.map_sdiff'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BiheytingHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : BiheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `biheyting_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : BiheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f

variable (α)

/-- `id` as a `biheyting_hom`. -/
protected def id : BiheytingHom α α :=
  { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }

@[simp]
theorem coe_id : ⇑(BiheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BiheytingHom.id α a = a :=
  rfl

instance : Inhabited (BiheytingHom α α) :=
  ⟨BiheytingHom.id _⟩

instance : PartialOrderₓ (BiheytingHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

/-- Composition of `biheyting_hom`s as a `biheyting_hom`. -/
def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with toFun := f ∘ g, map_himp' := fun a b => by simp,
    map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : BiheytingHom α β} {g g₁ g₂ : BiheytingHom β γ}

@[simp]
theorem coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => BiheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end BiheytingHom

