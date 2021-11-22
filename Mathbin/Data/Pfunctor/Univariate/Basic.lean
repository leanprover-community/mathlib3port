import Mathbin.Data.W.Basic

/-!
# Polynomial functors

This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/


universe u

/--
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.obj α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P.obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
structure Pfunctor where 
  A : Type u 
  B : A → Type u

namespace Pfunctor

instance  : Inhabited Pfunctor :=
  ⟨⟨default _, default _⟩⟩

variable(P : Pfunctor){α β : Type u}

/-- Applying `P` to an object of `Type` -/
def obj (α : Type _) :=
  Σx : P.A, P.B x → α

/-- Applying `P` to a morphism of `Type` -/
def map {α β : Type _} (f : α → β) : P.obj α → P.obj β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

instance obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P.obj α) :=
  ⟨⟨default _, fun _ => default _⟩⟩

instance  : Functor P.obj :=
  { map := @map P }

protected theorem map_eq {α β : Type _} (f : α → β) (a : P.A) (g : P.B a → α) :
  @Functor.map P.obj _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

protected theorem id_map {α : Type _} : ∀ x : P.obj α, id <$> x = id x :=
  fun ⟨a, b⟩ => rfl

protected theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) : ∀ x : P.obj α, (g ∘ f) <$> x = g <$> f <$> x :=
  fun ⟨a, b⟩ => rfl

instance  : IsLawfulFunctor P.obj :=
  { id_map := @Pfunctor.id_map P, comp_map := @Pfunctor.comp_map P }

/-- re-export existing definition of W-types and
adapt it to a packaged definition of polynomial functor -/
def W :=
  _root_.W_type P.B

attribute [nolint has_inhabited_instance] W

variable{P}

/-- root element  of a W tree -/
def W.head : W P → P.A
| ⟨a, f⟩ => a

/-- children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
| ⟨a, f⟩ => f

/-- destructor for W-types -/
def W.dest : W P → P.obj (W P)
| ⟨a, f⟩ => ⟨a, f⟩

/-- constructor for W-types -/
def W.mk : P.obj (W P) → W P
| ⟨a, f⟩ => ⟨a, f⟩

@[simp]
theorem W.dest_mk (p : P.obj (W P)) : W.dest (W.mk p) = p :=
  by 
    cases p <;> rfl

@[simp]
theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p :=
  by 
    cases p <;> rfl

variable(P)

/-- `Idx` identifies a location inside the application of a pfunctor.
For `F : pfunctor`, `x : F.obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx :=
  Σx : P.A, P.B x

instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B (default _))] : Inhabited P.Idx :=
  ⟨⟨default _, default _⟩⟩

variable{P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P.obj α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congr_argₓ _ h) i.2) else default _

@[simp]
theorem fst_map {α β : Type u} (x : P.obj α) (f : α → β) : (f <$> x).1 = x.1 :=
  by 
    cases x <;> rfl

@[simp]
theorem iget_map [DecidableEq P.A] {α β : Type u} [Inhabited α] [Inhabited β] (x : P.obj α) (f : α → β) (i : P.Idx)
  (h : i.1 = x.1) : (f <$> x).iget i = f (x.iget i) :=
  by 
    simp only [obj.iget, fst_map, dif_pos, eq_self_iff_true]
    cases x 
    rfl

end Pfunctor

namespace Pfunctor

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : Pfunctor.{u}) : Pfunctor.{u} :=
  ⟨Σa₂ : P₂.1, P₂.2 a₂ → P₁.1, fun a₂a₁ => Σu : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

/-- constructor for composition -/
def comp.mk (P₂ P₁ : Pfunctor.{u}) {α : Type} (x : P₂.obj (P₁.obj α)) : (comp P₂ P₁).Obj α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/-- destructor for composition -/
def comp.get (P₂ P₁ : Pfunctor.{u}) {α : Type} (x : (comp P₂ P₁).Obj α) : P₂.obj (P₁.obj α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

end Pfunctor

namespace Pfunctor

variable{P : Pfunctor.{u}}

open Functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P.obj α) : liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) :=
  by 
    split 
    ·
      rintro ⟨y, hy⟩
      cases' h : y with a f 
      refine' ⟨a, fun i => (f i).val, _, fun i => (f i).property⟩
      rw [←hy, h, Pfunctor.map_eq]
    rintro ⟨a, f, xeq, pf⟩
    use ⟨a, fun i => ⟨f i, pf i⟩⟩
    rw [xeq]
    rfl

-- error in Data.Pfunctor.Univariate.Basic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem liftp_iff'
{α : Type u}
(p : α → exprProp())
(a : P.A)
(f : P.B a → α) : «expr ↔ »(@liftp.{u} P.obj _ α p ⟨a, f⟩, ∀ i, p (f i)) :=
begin
  simp [] [] ["only"] ["[", expr liftp_iff, ",", expr sigma.mk.inj_iff, "]"] [] []; split; intro [],
  { casesm ["*"] ["[", expr Exists _, ",", expr «expr ∧ »(_, _), "]"],
    subst_vars,
    assumption },
  repeat { constructor <|> assumption }
end

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P.obj α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) :=
  by 
    split 
    ·
      rintro ⟨u, xeq, yeq⟩
      cases' h : u with a f 
      use a, fun i => (f i).val.fst, fun i => (f i).val.snd 
      split 
      ·
        rw [←xeq, h]
        rfl 
      split 
      ·
        rw [←yeq, h]
        rfl 
      intro i 
      exact (f i).property 
    rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
    use ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
    split 
    ·
      rw [xeq]
      rfl 
    rw [yeq]
    rfl

open Set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) : @supp.{u} P.obj _ α (⟨a, f⟩ : P.obj α) = f '' univ :=
  by 
    ext 
    simp only [supp, image_univ, mem_range, mem_set_of_eq]
    split  <;> intro h
    ·
      apply @h fun x => ∃ y : P.B a, f y = x 
      rw [liftp_iff']
      intro 
      refine' ⟨_, rfl⟩
    ·
      simp only [liftp_iff']
      cases h 
      subst x 
      tauto

end Pfunctor

