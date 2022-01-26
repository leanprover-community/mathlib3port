import Mathbin.Order.Hom.Basic
import Mathbin.Order.BoundedOrder

/-!
# Lattice homomorphisms

This file defines (bounded) lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `top_hom`: Maps which preserve `⊤`.
* `bot_hom`: Maps which preserve `⊥`.
* `sup_hom`: Maps which preserve `⊔`.
* `inf_hom`: Maps which preserve `⊓`.
* `lattice_hom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.
* `bounded_lattice_hom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `top_hom_class`
* `bot_hom_class`
* `sup_hom_class`
* `inf_hom_class`
* `lattice_hom_class`
* `bounded_lattice_hom_class`

## TODO

Do we need more intersections between `bot_hom`, `top_hom` and lattice homomorphisms?
-/


variable {F α β : Type _}

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
structure TopHom (α β : Type _) [HasTop α] [HasTop β] where
  toFun : α → β
  map_top' : to_fun ⊤ = ⊤

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
structure BotHom (α β : Type _) [HasBot α] [HasBot β] where
  toFun : α → β
  map_bot' : to_fun ⊥ = ⊥

/-- The type of `⊔`-preserving functions from `α` to `β`. -/
structure SupHom (α β : Type _) [HasSup α] [HasSup β] where
  toFun : α → β
  map_sup' (a b : α) : to_fun (a⊔b) = to_fun a⊔to_fun b

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
structure InfHom (α β : Type _) [HasInf α] [HasInf β] where
  toFun : α → β
  map_inf' (a b : α) : to_fun (a⊓b) = to_fun a⊓to_fun b

/-- The type of lattice homomorphisms from `α` to `β`. -/
structure LatticeHom (α β : Type _) [Lattice α] [Lattice β] extends SupHom α β where
  map_inf' (a b : α) : to_fun (a⊓b) = to_fun a⊓to_fun b

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
structure BoundedLatticeHom (α β : Type _) [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] extends
  LatticeHom α β where
  map_top' : to_fun ⊤ = ⊤
  map_bot' : to_fun ⊥ = ⊥

/-- `top_hom_class F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class TopHomClass (F : Type _) (α β : outParam <| Type _) [HasTop α] [HasTop β] extends FunLike F α fun _ => β where
  map_top (f : F) : f ⊤ = ⊤

/-- `bot_hom_class F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class BotHomClass (F : Type _) (α β : outParam <| Type _) [HasBot α] [HasBot β] extends FunLike F α fun _ => β where
  map_bot (f : F) : f ⊥ = ⊥

/-- `sup_hom_class F α β` states that `F` is a type of `⊔`-preserving morphisms.

You should extend this class when you extend `sup_hom`. -/
class SupHomClass (F : Type _) (α β : outParam <| Type _) [HasSup α] [HasSup β] extends FunLike F α fun _ => β where
  map_sup (f : F) (a b : α) : f (a⊔b) = f a⊔f b

/-- `inf_hom_class F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `inf_hom`. -/
class InfHomClass (F : Type _) (α β : outParam <| Type _) [HasInf α] [HasInf β] extends FunLike F α fun _ => β where
  map_inf (f : F) (a b : α) : f (a⊓b) = f a⊓f b

/-- `lattice_hom_class F α β` states that `F` is a type of lattice morphisms.

You should extend this class when you extend `sup_hom`. -/
class LatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β] extends SupHomClass F α β where
  map_inf (f : F) (a b : α) : f (a⊓b) = f a⊓f b

/-- `bounded_lattice_hom_class F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `bounded_lattice_hom`. -/
class BoundedLatticeHomClass (F : Type _) (α β : outParam <| Type _) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHomClass F α β where
  map_top (f : F) : f ⊤ = ⊤
  map_bot (f : F) : f ⊥ = ⊥

export TopHomClass (map_top)

export BotHomClass (map_bot)

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_top map_bot map_sup map_inf

namespace TopHom

variable [HasTop α]

section HasTop

variable [HasTop β]

instance : TopHomClass (TopHom α β) α β where
  coe := TopHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_top := TopHom.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (TopHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : TopHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : TopHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : TopHom α β) (f' : α → β) (h : f' = f) : TopHom α β where
  toFun := f'
  map_top' := h.symm ▸ f.map_top'

instance : Inhabited (TopHom α β) :=
  ⟨⟨fun _ => ⊤, rfl⟩⟩

variable (α)

/-- `id` as a `top_hom`. -/
protected def id : TopHom α α :=
  ⟨id, rfl⟩

@[simp]
theorem coe_id : ⇑TopHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : TopHom.id α a = a :=
  rfl

end HasTop

instance [Preorderₓ β] [HasTop β] : Preorderₓ (TopHom α β) :=
  Preorderₓ.lift (coeFn : TopHom α β → α → β)

instance [PartialOrderₓ β] [HasTop β] : PartialOrderₓ (TopHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

section OrderTop

variable [Preorderₓ β] [OrderTop β]

instance : OrderTop (TopHom α β) :=
  ⟨⟨⊤, rfl⟩, fun _ => le_top⟩

@[simp]
theorem coe_top : ⇑(⊤ : TopHom α β) = ⊤ :=
  rfl

@[simp]
theorem top_apply (a : α) : (⊤ : TopHom α β) a = ⊤ :=
  rfl

end OrderTop

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] (f g : TopHom α β)

instance : HasInf (TopHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, by
      rw [Pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

instance : SemilatticeInf (TopHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun _ _ => rfl

@[simp]
theorem coe_inf : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderTop β] (f g : TopHom α β)

instance : HasSup (TopHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, by
      rw [Pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

instance : SemilatticeSup (TopHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun _ _ => rfl

@[simp]
theorem coe_sup : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderTop β] : Lattice (TopHom α β) :=
  FunLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance [DistribLattice β] [OrderTop β] : DistribLattice (TopHom α β) :=
  FunLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

end TopHom

namespace BotHom

variable [HasBot α]

section HasBot

variable [HasBot β]

instance : BotHomClass (BotHom α β) α β where
  coe := BotHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_bot := BotHom.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BotHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : BotHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : BotHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : BotHom α β) (f' : α → β) (h : f' = f) : BotHom α β where
  toFun := f'
  map_bot' := h.symm ▸ f.map_bot'

instance : Inhabited (BotHom α β) :=
  ⟨⟨fun _ => ⊥, rfl⟩⟩

variable (α)

/-- `id` as a `bot_hom`. -/
protected def id : BotHom α α :=
  ⟨id, rfl⟩

@[simp]
theorem coe_id : ⇑BotHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BotHom.id α a = a :=
  rfl

end HasBot

instance [Preorderₓ β] [HasBot β] : Preorderₓ (BotHom α β) :=
  Preorderₓ.lift (coeFn : BotHom α β → α → β)

instance [PartialOrderₓ β] [HasBot β] : PartialOrderₓ (BotHom α β) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

section OrderBot

variable [Preorderₓ β] [OrderBot β]

instance : OrderBot (BotHom α β) :=
  ⟨⟨⊥, rfl⟩, fun _ => bot_le⟩

@[simp]
theorem coe_bot : ⇑(⊥ : BotHom α β) = ⊥ :=
  rfl

@[simp]
theorem bot_apply (a : α) : (⊥ : BotHom α β) a = ⊥ :=
  rfl

end OrderBot

section SemilatticeInf

variable [SemilatticeInf β] [OrderBot β] (f g : BotHom α β)

instance : HasInf (BotHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, by
      rw [Pi.inf_apply, map_bot, map_bot, inf_bot_eq]⟩⟩

instance : SemilatticeInf (BotHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun _ _ => rfl

@[simp]
theorem coe_inf : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem inf_apply (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] (f g : BotHom α β)

instance : HasSup (BotHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, by
      rw [Pi.sup_apply, map_bot, map_bot, sup_bot_eq]⟩⟩

instance : SemilatticeSup (BotHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun _ _ => rfl

@[simp]
theorem coe_sup : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem sup_apply (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

end SemilatticeSup

instance [Lattice β] [OrderBot β] : Lattice (BotHom α β) :=
  FunLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance [DistribLattice β] [OrderBot β] : DistribLattice (BotHom α β) :=
  FunLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

end BotHom

namespace SupHom

variable [HasSup α]

section HasSup

variable [HasSup β]

instance : SupHomClass (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_sup := SupHom.map_sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : SupHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupHom α β) (f' : α → β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

variable (α)

/-- `id` as a `sup_hom`. -/
protected def id : SupHom α α :=
  ⟨id, fun a b => rfl⟩

instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[simp]
theorem coe_id : ⇑SupHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl

end HasSup

variable [SemilatticeSup β]

instance : HasSup (SupHom α β) :=
  ⟨fun f g =>
    ⟨f⊔g, fun a b => by
      rw [Pi.sup_apply, map_sup, map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

instance : SemilatticeSup (SupHom α β) :=
  (FunLike.coe_injective.SemilatticeSup _) fun f g => rfl

@[simp]
theorem coe_sup (f g : SupHom α β) : ⇑(f⊔g) = f⊔g :=
  rfl

@[simp]
theorem sup_apply (f g : SupHom α β) (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

variable (α)

/-- The constant function as an `sup_hom`. -/
def const (b : β) : SupHom α β :=
  ⟨fun _ => b, fun _ _ => sup_idem.symm⟩

@[simp]
theorem coe_const (b : β) : ⇑const α b = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

end SupHom

instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β] [SupHomClass F α β] :
    OrderHomClass F α β :=
  ⟨fun f a b h => by
    rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h]⟩

namespace InfHom

variable [HasInf α]

section HasInf

variable [HasInf β]

instance : InfHomClass (InfHom α β) α β where
  coe := InfHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_inf := InfHom.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : InfHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : InfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfHom α β) (f' : α → β) (h : f' = f) : InfHom α β where
  toFun := f'
  map_inf' := h.symm ▸ f.map_inf'

variable (α)

/-- `id` as an `inf_hom`. -/
protected def id : InfHom α α :=
  ⟨id, fun a b => rfl⟩

instance : Inhabited (InfHom α α) :=
  ⟨InfHom.id α⟩

@[simp]
theorem coe_id : ⇑InfHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : InfHom.id α a = a :=
  rfl

end HasInf

variable [SemilatticeInf β]

instance : HasInf (InfHom α β) :=
  ⟨fun f g =>
    ⟨f⊓g, fun a b => by
      rw [Pi.inf_apply, map_inf, map_inf]
      exact inf_inf_inf_comm _ _ _ _⟩⟩

instance : SemilatticeInf (InfHom α β) :=
  (FunLike.coe_injective.SemilatticeInf _) fun f g => rfl

@[simp]
theorem coe_inf (f g : InfHom α β) : ⇑(f⊓g) = f⊓g :=
  rfl

@[simp]
theorem inf_apply (f g : InfHom α β) (a : α) : (f⊓g) a = f a⊓g a :=
  rfl

variable (α)

/-- The constant function as an `inf_hom`. -/
def const (b : β) : InfHom α β :=
  ⟨fun _ => b, fun _ _ => inf_idem.symm⟩

@[simp]
theorem coe_const (b : β) : ⇑const α b = Function.const α b :=
  rfl

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

end InfHom

instance (priority := 100) InfHomClass.toOrderHomClass [SemilatticeInf α] [SemilatticeInf β] [InfHomClass F α β] :
    OrderHomClass F α β :=
  ⟨fun f a b h => by
    rw [← inf_eq_left, ← map_inf, inf_eq_left.2 h]⟩

namespace LatticeHom

variable [Lattice α] [Lattice β]

/-- Reinterpret a `lattice_hom` as an `inf_hom`. -/
def to_inf_hom (f : LatticeHom α β) : InfHom α β :=
  { f with }

instance : LatticeHomClass (LatticeHom α β) α β where
  coe := fun f => f.to_fun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : LatticeHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `lattice_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : LatticeHom α β) (f' : α → β) (h : f' = f) : LatticeHom α β :=
  { f.to_sup_hom.copy f' <| by
      ext
      exact congr_funₓ h _,
    f.to_inf_hom.copy f' <| by
      ext
      exact congr_funₓ h _ with
    toFun := f' }

variable (α)

/-- `id` as a `lattice_hom`. -/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl

instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑LatticeHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl

end LatticeHom

instance (priority := 100) LatticeHomClass.toInfHomClass [Lattice α] [Lattice β] [LatticeHomClass F α β] :
    InfHomClass F α β :=
  { ‹LatticeHomClass F α β› with }

namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β]

/-- Reinterpret a `bounded_lattice_hom` as a `top_hom`. -/
def to_top_hom (f : BoundedLatticeHom α β) : TopHom α β :=
  { f with }

/-- Reinterpret a `bounded_lattice_hom` as a `bot_hom`. -/
def to_bot_hom (f : BoundedLatticeHom α β) : BotHom α β :=
  { f with }

instance : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  coe := fun f => f.to_fun
  coe_injective' := fun f g h => by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f <;> obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g <;> congr
  map_sup := fun f => f.map_sup'
  map_inf := fun f => f.map_inf'
  map_top := fun f => f.map_top'
  map_bot := fun f => f.map_bot'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (BoundedLatticeHom α β) fun _ => α → β :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : BoundedLatticeHom α β} : f.to_fun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `bounded_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.to_lattice_hom.copy f' <| by
      ext
      exact congr_funₓ h _,
    f.to_top_hom.copy f' <| by
      ext
      exact congr_funₓ h _,
    f.to_bot_hom.copy f' <| by
      ext
      exact congr_funₓ h _ with
    toFun := f' }

variable (α)

/-- `id` as an `bounded_lattice_hom`. -/
protected def id : BoundedLatticeHom α α where
  toFun := id
  map_sup' := fun _ _ => rfl
  map_inf' := fun _ _ => rfl
  map_top' := rfl
  map_bot' := rfl

instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp]
theorem coe_id : ⇑BoundedLatticeHom.id α = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl

end BoundedLatticeHom

instance (priority := 100) BoundedLatticeHomClass.toTopHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [BoundedLatticeHomClass F α β] : TopHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

instance (priority := 100) BoundedLatticeHomClass.toBotHomClass [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [BoundedLatticeHomClass F α β] : BotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

