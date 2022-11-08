/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Control.Applicative
import Mathbin.Control.Traversable.Basic
import Mathbin.Logic.Equiv.Defs
import Mathbin.Data.List.Basic

/-!
# Free constructions

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.assoc_quotient α`: quotient of a magma `α` by the associativity equivalence relation.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a structure with two fields
  `head : α` and `tail : list α` (i.e. nonempty lists), with traversable instance and decidable
  equality.
* `free_magma_assoc_quotient_equiv α`: isomorphism between `magma.assoc_quotient (free_magma α)` and
  `free_semigroup α`.
* `free_magma.lift`: the universal property of the free magma, expressing its adjointness.
-/


universe u v l

/-- Free magma over a given alphabet. -/
inductive FreeMagma (α : Type u) : Type u
  | of : α → FreeMagma
  | mul : FreeMagma → FreeMagma → FreeMagma
  deriving DecidableEq

/-- Free nonabelian additive magma over a given alphabet. -/
inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma
  | add : FreeAddMagma → FreeAddMagma → FreeAddMagma
  deriving DecidableEq

attribute [to_additive] FreeMagma

namespace FreeMagma

variable {α : Type u}

@[to_additive]
instance [Inhabited α] : Inhabited (FreeMagma α) :=
  ⟨of default⟩

@[to_additive]
instance : Mul (FreeMagma α) :=
  ⟨FreeMagma.mul⟩

attribute [match_pattern] Mul.mul

@[simp, to_additive]
theorem mul_eq (x y : FreeMagma α) : mul x y = x * y :=
  rfl

/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
@[elab_as_elim, to_additive "Recursor for `free_add_magma` using `x + y` instead of `free_add_magma.add x y`."]
def recOnMul {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C x → C y → C (x * y)) : C x :=
  FreeMagma.recOn x ih1 ih2

@[ext, to_additive]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeMagma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (FunLike.ext _ _) fun x =>
    recOnMul x (congr_fun h) <| by
      intros
      simp only [map_mul, *]

end FreeMagma

/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def FreeMagma.liftAux {α : Type u} {β : Type v} [Mul β] (f : α → β) : FreeMagma α → β
  | FreeMagma.of x => f x
  | x * y => x.liftAux * y.liftAux

/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def FreeAddMagma.liftAux {α : Type u} {β : Type v} [Add β] (f : α → β) : FreeAddMagma α → β
  | FreeAddMagma.of x => f x
  | x + y => x.liftAux + y.liftAux

attribute [to_additive FreeAddMagma.liftAux] FreeMagma.liftAux

namespace FreeMagma

section lift

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

/-- The universal property of the free magma expressing its adjointness. -/
@[to_additive "The universal property of the free additive magma expressing its adjointness.", simps symmApply]
def lift : (α → β) ≃ (FreeMagma α →ₙ* β) where
  toFun f := { toFun := liftAux f, map_mul' := fun x y => rfl }
  invFun F := F ∘ of
  left_inv f := by
    ext
    rfl
  right_inv F := by
    ext
    rfl

@[simp, to_additive]
theorem lift_of (x) : lift f (of x) = f x :=
  rfl

@[simp, to_additive]
theorem lift_comp_of : lift f ∘ of = f :=
  rfl

@[simp, to_additive]
theorem lift_comp_of' (f : FreeMagma α →ₙ* β) : lift (f ∘ of) = f :=
  lift.apply_symm_apply f

end lift

section Map

variable {α : Type u} {β : Type v} (f : α → β)

/-- The unique magma homomorphism `free_magma α →ₙ* free_magma β` that sends
each `of x` to `of (f x)`. -/
@[to_additive
      "The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that\nsends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMagma α →ₙ* FreeMagma β :=
  lift (of ∘ f)

@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl

end Map

section Category

variable {α β : Type u}

@[to_additive]
instance : Monad FreeMagma where
  pure _ := of
  bind _ _ x f := lift f x

/-- Recursor on `free_magma` using `pure` instead of `of`. -/
@[elab_as_elim, to_additive "Recursor on `free_add_magma` using `pure` instead of `of`."]
protected def recOnPure {C : FreeMagma α → Sort l} (x) (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
    C x :=
  FreeMagma.recOnMul x ih1 ih2

@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeMagma β) = pure (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeMagma α) : f <$> (x * y) = f <$> x * f <$> y :=
  rfl

@[simp, to_additive]
theorem pure_bind (f : α → FreeMagma β) (x) : pure x >>= f = f x :=
  rfl

@[simp, to_additive]
theorem mul_bind (f : α → FreeMagma β) (x y : FreeMagma α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  rfl

@[simp, to_additive]
theorem pure_seq {α β : Type u} {f : α → β} {x : FreeMagma α} : pure f <*> x = f <$> x :=
  rfl

@[simp, to_additive]
theorem mul_seq {α β : Type u} {f g : FreeMagma (α → β)} {x : FreeMagma α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  rfl

@[to_additive]
instance : LawfulMonad FreeMagma.{u} where
  pure_bind _ _ _ _ := rfl
  bind_assoc α β γ x f g :=
    FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map α x := FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by rw [map_mul', ih1, ih2]

end Category

end FreeMagma

/-- `free_magma` is traversable. -/
protected def FreeMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (F : α → m β) :
    FreeMagma α → m (FreeMagma β)
  | FreeMagma.of x => FreeMagma.of <$> F x
  | x * y => (· * ·) <$> x.traverse <*> y.traverse

/-- `free_add_magma` is traversable. -/
protected def FreeAddMagma.traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (F : α → m β) :
    FreeAddMagma α → m (FreeAddMagma β)
  | FreeAddMagma.of x => FreeAddMagma.of <$> F x
  | x + y => (· + ·) <$> x.traverse <*> y.traverse

attribute [to_additive FreeAddMagma.traverse] FreeMagma.traverse

namespace FreeMagma

variable {α : Type u}

section Category

variable {β : Type u}

@[to_additive]
instance : Traversable FreeMagma :=
  ⟨@FreeMagma.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeMagma α) = pure <$> F x :=
  rfl

@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeMagma β)) :=
  rfl

@[simp, to_additive]
theorem traverse_mul (x y : FreeMagma α) : traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  rfl

@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeMagma α) _ = fun x y => (· * ·) <$> traverse F x <*> traverse F y :=
  rfl

@[simp, to_additive]
theorem traverse_eq (x) : FreeMagma.traverse F x = traverse F x :=
  rfl

@[simp, to_additive]
theorem mul_map_seq (x y : FreeMagma α) : ((· * ·) <$> x <*> y : id (FreeMagma α)) = (x * y : FreeMagma α) :=
  rfl

@[to_additive]
instance : IsLawfulTraversable FreeMagma.{u} :=
  { FreeMagma.is_lawful_monad with
    id_traverse := fun α x =>
      FreeMagma.recOnPure x (fun x => rfl) fun x y ih1 ih2 => by rw [traverse_mul, ih1, ih2, mul_map_seq],
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      FreeMagma.recOnPure x (fun x => by skip <;> simp only [traverse_pure, traverse_pure', functor_norm])
        fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;> simp only [traverse_mul', functor_norm],
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      FreeMagma.recOnPure x (fun x => by simp only [traverse_pure, functor_norm]) fun x y ih1 ih2 => by
        simp only [traverse_mul, functor_norm] <;> rw [ih1, ih2],
    traverse_eq_map_id := fun α β f x =>
      FreeMagma.recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

end FreeMagma

/-- Representation of an element of a free magma. -/
protected def FreeMagma.repr {α : Type u} [Repr α] : FreeMagma α → String
  | FreeMagma.of x => repr x
  | x * y => "( " ++ x.repr ++ " * " ++ y.repr ++ " )"

/-- Representation of an element of a free additive magma. -/
protected def FreeAddMagma.repr {α : Type u} [Repr α] : FreeAddMagma α → String
  | FreeAddMagma.of x => repr x
  | x + y => "( " ++ x.repr ++ " + " ++ y.repr ++ " )"

attribute [to_additive FreeAddMagma.repr] FreeMagma.repr

@[to_additive]
instance {α : Type u} [Repr α] : Repr (FreeMagma α) :=
  ⟨FreeMagma.repr⟩

/-- Length of an element of a free magma. -/
@[simp]
def FreeMagma.length {α : Type u} : FreeMagma α → ℕ
  | FreeMagma.of x => 1
  | x * y => x.length + y.length

/-- Length of an element of a free additive magma. -/
@[simp]
def FreeAddMagma.length {α : Type u} : FreeAddMagma α → ℕ
  | FreeAddMagma.of x => 1
  | x + y => x.length + y.length

attribute [to_additive FreeAddMagma.length] FreeMagma.length

/-- Associativity relations for an additive magma. -/
inductive AddMagma.AssocRel (α : Type u) [Add α] : α → α → Prop
  | intro : ∀ x y z, AddMagma.AssocRel (x + y + z) (x + (y + z))
  | left : ∀ w x y z, AddMagma.AssocRel (w + (x + y + z)) (w + (x + (y + z)))

/-- Associativity relations for a magma. -/
@[to_additive AddMagma.AssocRel "Associativity relations for an additive magma."]
inductive Magma.AssocRel (α : Type u) [Mul α] : α → α → Prop
  | intro : ∀ x y z, Magma.AssocRel (x * y * z) (x * (y * z))
  | left : ∀ w x y z, Magma.AssocRel (w * (x * y * z)) (w * (x * (y * z)))

namespace Magma

/-- Semigroup quotient of a magma. -/
@[to_additive AddMagma.FreeAddSemigroup "Additive semigroup quotient of an additive magma."]
def AssocQuotient (α : Type u) [Mul α] : Type u :=
  Quot <| AssocRel α

namespace AssocQuotient

variable {α : Type u} [Mul α]

@[to_additive]
theorem quot_mk_assoc (x y z : α) : Quot.mk (AssocRel α) (x * y * z) = Quot.mk _ (x * (y * z)) :=
  Quot.sound (AssocRel.intro _ _ _)

@[to_additive]
theorem quot_mk_assoc_left (x y z w : α) : Quot.mk (AssocRel α) (x * (y * z * w)) = Quot.mk _ (x * (y * (z * w))) :=
  Quot.sound (AssocRel.left _ _ _ _)

@[to_additive]
instance : Semigroup (AssocQuotient α) where
  mul x y := by
    refine' Quot.liftOn₂ x y (fun x y => Quot.mk _ (x * y)) _ _
    · rintro a b₁ b₂ (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · exact quot_mk_assoc_left _ _ _ _
        
      · rw [← quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc]
        
      
    · rintro a₁ a₂ b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only
      · simp only [quot_mk_assoc, quot_mk_assoc_left]
        
      · rw [quot_mk_assoc, quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc_left, quot_mk_assoc_left, ←
          quot_mk_assoc c d, ← quot_mk_assoc c d, quot_mk_assoc_left]
        
      
  mul_assoc x y z := (Quot.induction_on₃ x y z) fun p q r => quot_mk_assoc p q r

/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α →ₙ* AssocQuotient α :=
  ⟨Quot.mk _, fun x y => rfl⟩

@[to_additive]
instance [Inhabited α] : Inhabited (AssocQuotient α) :=
  ⟨of default⟩

@[elab_as_elim, to_additive]
protected theorem induction_on {C : AssocQuotient α → Prop} (x : AssocQuotient α) (ih : ∀ x, C (of x)) : C x :=
  Quot.induction_on x ih

section lift

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

@[ext, to_additive]
theorem hom_ext {f g : AssocQuotient α →ₙ* β} (h : f.comp of = g.comp of) : f = g :=
  (FunLike.ext _ _) fun x => AssocQuotient.induction_on x <| FunLike.congr_fun h

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.assoc_quotient α → β`
given a semigroup `β`. -/
@[to_additive
      "Lifts an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.assoc_quotient α → β` given an additive semigroup `β`.",
  simps symmApply]
def lift : (α →ₙ* β) ≃ (AssocQuotient α →ₙ* β) where
  toFun f :=
    { toFun := fun x => Quot.liftOn x f <| by rintro a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩) <;> simp only [map_mul, mul_assoc],
      map_mul' := fun x y => Quot.induction_on₂ x y (map_mul f) }
  invFun f := f.comp of
  left_inv f := (FunLike.ext _ _) fun x => rfl
  right_inv f := hom_ext <| (FunLike.ext _ _) fun x => rfl

@[simp, to_additive]
theorem lift_of (x : α) : lift f (of x) = f x :=
  rfl

@[simp, to_additive]
theorem lift_comp_of : (lift f).comp of = f :=
  lift.symm_apply_apply f

@[simp, to_additive]
theorem lift_comp_of' (f : AssocQuotient α →ₙ* β) : lift (f.comp of) = f :=
  lift.apply_symm_apply f

end lift

variable {β : Type v} [Mul β] (f : α →ₙ* β)

/-- From a magma homomorphism `α →ₙ* β` to a semigroup homomorphism
`magma.assoc_quotient α →ₙ* magma.assoc_quotient β`. -/
@[to_additive
      "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism\n`add_magma.assoc_quotient α → add_magma.assoc_quotient β`."]
def map : AssocQuotient α →ₙ* AssocQuotient β :=
  lift (of.comp f)

@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl

end AssocQuotient

end Magma

/-- Free additive semigroup over a given alphabet. -/
@[ext]
structure FreeAddSemigroup (α : Type u) where
  head : α
  tail : List α

/-- Free semigroup over a given alphabet. -/
@[ext, to_additive]
structure FreeSemigroup (α : Type u) where
  head : α
  tail : List α

namespace FreeSemigroup

variable {α : Type u}

@[to_additive]
instance : Semigroup (FreeSemigroup α) where
  mul L1 L2 := ⟨L1.1, L1.2 ++ L2.1 :: L2.2⟩
  mul_assoc L1 L2 L3 := ext _ _ rfl <| List.append_assoc _ _ _

@[simp, to_additive]
theorem head_mul (x y : FreeSemigroup α) : (x * y).1 = x.1 :=
  rfl

@[simp, to_additive]
theorem tail_mul (x y : FreeSemigroup α) : (x * y).2 = x.2 ++ y.1 :: y.2 :=
  rfl

@[simp, to_additive]
theorem mk_mul_mk (x y : α) (L1 L2 : List α) : mk x L1 * mk y L2 = mk x (L1 ++ y :: L2) :=
  rfl

/-- The embedding `α → free_semigroup α`. -/
@[to_additive "The embedding `α → free_add_semigroup α`.", simps]
def of (x : α) : FreeSemigroup α :=
  ⟨x, []⟩

/-- Length of an element of free semigroup. -/
@[to_additive "Length of an element of free additive semigroup"]
def length (x : FreeSemigroup α) : ℕ :=
  x.tail.length + 1

@[simp, to_additive]
theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [length, ← add_assoc, add_right_comm]

@[simp, to_additive]
theorem length_of (x : α) : (of x).length = 1 :=
  rfl

@[to_additive]
instance [Inhabited α] : Inhabited (FreeSemigroup α) :=
  ⟨of default⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[elab_as_elim, to_additive "Recursor for free additive semigroup using `of` and `+`."]
protected def recOnMul {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (of x))
    (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) : C x :=
  (FreeSemigroup.recOn x) fun f s => List.recOn s ih1 (fun hd tl ih f => ih2 f ⟨hd, tl⟩ (ih1 f) (ih hd)) f

@[ext, to_additive]
theorem hom_ext {β : Type v} [Mul β] {f g : FreeSemigroup α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
  (FunLike.ext _ _) fun x => (FreeSemigroup.recOnMul x (congr_fun h)) fun x y hx hy => by simp only [map_mul, *]

section lift

variable {β : Type v} [Semigroup β] (f : α → β)

/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
@[to_additive
      "Lifts a function `α → β` to an additive semigroup homomorphism\n`free_add_semigroup α → β` given an additive semigroup `β`.",
  simps symmApply]
def lift : (α → β) ≃ (FreeSemigroup α →ₙ* β) where
  toFun f :=
    { toFun := fun x => x.2.foldl (fun a b => a * f b) (f x.1),
      map_mul' := fun x y => by
        simp only [head_mul, tail_mul, ← List.foldl_map f, List.foldl_append, List.foldl_cons, List.foldl_assoc] }
  invFun f := f ∘ of
  left_inv f := rfl
  right_inv f := hom_ext rfl

@[simp, to_additive]
theorem lift_of (x : α) : lift f (of x) = f x :=
  rfl

@[simp, to_additive]
theorem lift_comp_of : lift f ∘ of = f :=
  rfl

@[simp, to_additive]
theorem lift_comp_of' (f : FreeSemigroup α →ₙ* β) : lift (f ∘ of) = f :=
  hom_ext rfl

@[to_additive]
theorem lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := by rw [map_mul, lift_of]

end lift

section Map

variable {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : FreeSemigroup α →ₙ* FreeSemigroup β :=
  lift <| of ∘ f

@[simp, to_additive]
theorem map_of (x) : map f (of x) = of (f x) :=
  rfl

@[simp, to_additive]
theorem length_map (x) : (map f x).length = x.length :=
  (FreeSemigroup.recOnMul x fun x => rfl) fun x y hx hy => by simp only [map_mul, length_mul, *]

end Map

section Category

variable {β : Type u}

@[to_additive]
instance : Monad FreeSemigroup where
  pure _ := of
  bind _ _ x f := lift f x

/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_elim, to_additive "Recursor that uses `pure` instead of `of`."]
def recOnPure {C : FreeSemigroup α → Sort l} (x) (ih1 : ∀ x, C (pure x))
    (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) : C x :=
  FreeSemigroup.recOnMul x ih1 ih2

@[simp, to_additive]
theorem map_pure (f : α → β) (x) : (f <$> pure x : FreeSemigroup β) = pure (f x) :=
  rfl

@[simp, to_additive]
theorem map_mul' (f : α → β) (x y : FreeSemigroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  map_mul (map f) _ _

@[simp, to_additive]
theorem pure_bind (f : α → FreeSemigroup β) (x) : pure x >>= f = f x :=
  rfl

@[simp, to_additive]
theorem mul_bind (f : α → FreeSemigroup β) (x y : FreeSemigroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  map_mul (lift f) _ _

@[simp, to_additive]
theorem pure_seq {f : α → β} {x : FreeSemigroup α} : pure f <*> x = f <$> x :=
  rfl

@[simp, to_additive]
theorem mul_seq {f g : FreeSemigroup (α → β)} {x : FreeSemigroup α} : f * g <*> x = (f <*> x) * (g <*> x) :=
  mul_bind _ _ _

@[to_additive]
instance : LawfulMonad FreeSemigroup.{u} where
  pure_bind _ _ _ _ := rfl
  bind_assoc α β γ x f g := recOnPure x (fun x => rfl) fun x y ih1 ih2 => by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]
  id_map α x := recOnPure x (fun _ => rfl) fun x y ih1 ih2 => by rw [map_mul', ih1, ih2]

/-- `free_semigroup` is traversable. -/
@[to_additive "`free_add_semigroup` is traversable."]
protected def traverse {m : Type u → Type u} [Applicative m] {α β : Type u} (F : α → m β) (x : FreeSemigroup α) :
    m (FreeSemigroup β) :=
  recOnPure x (fun x => pure <$> F x) fun x y ihx ihy => (· * ·) <$> ihx <*> ihy

@[to_additive]
instance : Traversable FreeSemigroup :=
  ⟨@FreeSemigroup.traverse⟩

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

@[simp, to_additive]
theorem traverse_pure (x) : traverse F (pure x : FreeSemigroup α) = pure <$> F x :=
  rfl

@[simp, to_additive]
theorem traverse_pure' : traverse F ∘ pure = fun x => (pure <$> F x : m (FreeSemigroup β)) :=
  rfl

section

variable [LawfulApplicative m]

@[simp, to_additive]
theorem traverse_mul (x y : FreeSemigroup α) : traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y :=
  let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun x => rfl)
    (fun hd tl ih x =>
      show
        (· * ·) <$> pure <$> F x <*> traverse F (mk hd tl * mk y L2) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (mk hd tl)) <*> traverse F (mk y L2)
        by rw [ih] <;> simp only [(· ∘ ·), (mul_assoc _ _ _).symm, functor_norm])
    x

@[simp, to_additive]
theorem traverse_mul' :
    Function.comp (traverse F) ∘ @Mul.mul (FreeSemigroup α) _ = fun x y => (· * ·) <$> traverse F x <*> traverse F y :=
  funext fun x => funext fun y => traverse_mul F x y

end

@[simp, to_additive]
theorem traverse_eq (x) : FreeSemigroup.traverse F x = traverse F x :=
  rfl

@[simp, to_additive]
theorem mul_map_seq (x y : FreeSemigroup α) :
    ((· * ·) <$> x <*> y : id (FreeSemigroup α)) = (x * y : FreeSemigroup α) :=
  rfl

@[to_additive]
instance : IsLawfulTraversable FreeSemigroup.{u} :=
  { FreeSemigroup.is_lawful_monad with
    id_traverse := fun α x =>
      FreeSemigroup.recOnMul x (fun x => rfl) fun x y ih1 ih2 => by rw [traverse_mul, ih1, ih2, mul_map_seq],
    comp_traverse := fun F G hf1 hg1 hf2 hg2 α β γ f g x =>
      recOnPure x (fun x => by skip <;> simp only [traverse_pure, traverse_pure', functor_norm]) fun x y ih1 ih2 => by
        skip <;> rw [traverse_mul, ih1, ih2, traverse_mul] <;> simp only [traverse_mul', functor_norm],
    naturality := fun F G hf1 hg1 hf2 hg2 η α β f x =>
      recOnPure x (fun x => by simp only [traverse_pure, functor_norm]) fun x y ih1 ih2 => by
        skip <;> simp only [traverse_mul, functor_norm] <;> rw [ih1, ih2],
    traverse_eq_map_id := fun α β f x =>
      FreeSemigroup.recOnMul x (fun _ => rfl) fun x y ih1 ih2 => by
        rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq] <;> rfl }

end Category

@[to_additive]
instance [DecidableEq α] : DecidableEq (FreeSemigroup α) := fun x y => decidable_of_iff' _ (ext_iff _ _)

end FreeSemigroup

namespace FreeMagma

variable {α : Type u} {β : Type v}

/-- The canonical multiplicative morphism from `free_magma α` to `free_semigroup α`. -/
@[to_additive "The canonical additive morphism from `free_add_magma α` to `free_add_semigroup α`."]
def toFreeSemigroup : FreeMagma α →ₙ* FreeSemigroup α :=
  FreeMagma.lift FreeSemigroup.of

@[simp, to_additive]
theorem to_free_semigroup_of (x : α) : toFreeSemigroup (of x) = FreeSemigroup.of x :=
  rfl

@[simp, to_additive]
theorem to_free_semigroup_comp_of : @toFreeSemigroup α ∘ of = FreeSemigroup.of :=
  rfl

@[to_additive]
theorem to_free_semigroup_comp_map (f : α → β) :
    toFreeSemigroup.comp (map f) = (FreeSemigroup.map f).comp toFreeSemigroup := by
  ext1
  rfl

@[to_additive]
theorem to_free_semigroup_map (f : α → β) (x : FreeMagma α) :
    (map f x).toFreeSemigroup = FreeSemigroup.map f x.toFreeSemigroup :=
  FunLike.congr_fun (to_free_semigroup_comp_map f) x

@[simp, to_additive]
theorem length_to_free_semigroup (x : FreeMagma α) : x.toFreeSemigroup.length = x.length :=
  (FreeMagma.recOnMul x fun x => rfl) fun x y hx hy => by rw [map_mul, FreeSemigroup.length_mul, length, hx, hy]

end FreeMagma

/-- Isomorphism between `magma.assoc_quotient (free_magma α)` and `free_semigroup α`. -/
@[to_additive "Isomorphism between\n`add_magma.assoc_quotient (free_add_magma α)` and `free_add_semigroup α`."]
def freeMagmaAssocQuotientEquiv (α : Type u) : Magma.AssocQuotient (FreeMagma α) ≃* FreeSemigroup α :=
  (Magma.AssocQuotient.lift FreeMagma.toFreeSemigroup).toMulEquiv
    (FreeSemigroup.lift (Magma.AssocQuotient.of ∘ FreeMagma.of))
    (by
      ext
      rfl)
    (by
      ext1
      rfl)

