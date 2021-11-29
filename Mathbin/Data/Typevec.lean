import Mathbin.Data.Fin.Fin2 
import Mathbin.Logic.Function.Basic 
import Mathbin.Tactic.Basic

/-!

# Tuples of types, and their categorical structure.

## Features

* `typevec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `append_fun f g` - appends a function g to an n-tuple of functions
* `drop_fun f`     - drops the last function from an n+1-tuple
* `last_fun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/


universe u v w

/--
n-tuples of types, as a category
-/
def Typevec (n : ℕ) :=
  Fin2 n → Type _

instance  {n} : Inhabited (Typevec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace Typevec

variable{n : ℕ}

/-- arrow in the category of `typevec` -/
def arrow (α β : Typevec n) :=
  ∀ (i : Fin2 n), α i → β i

localized [Mvfunctor] infixl:40 " ⟹ " => Typevec.Arrow

instance arrow.inhabited (α β : Typevec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default _⟩

/-- identity of arrow composition -/
def id {α : Typevec n} : α ⟹ α :=
  fun i x => x

/-- arrow composition in the category of `typevec` -/
def comp {α β γ : Typevec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
  fun i x => g i (f i x)

localized [Mvfunctor] infixr:80 " ⊚ " => Typevec.comp

@[simp]
theorem id_comp {α β : Typevec n} (f : α ⟹ β) : id ⊚ f = f :=
  rfl

@[simp]
theorem comp_id {α β : Typevec n} (f : α ⟹ β) : f ⊚ id = f :=
  rfl

theorem comp_assoc {α β γ δ : Typevec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) : (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl

/--
Support for extending a typevec by one element.
-/
def append1 (α : Typevec n) (β : Type _) : Typevec (n+1)
| Fin2.fs i => α i
| Fin2.fz => β

infixl:67 " ::: " => append1

/-- retain only a `n-length` prefix of the argument -/
def drop (α : Typevec.{u} (n+1)) : Typevec n :=
  fun i => α i.fs

/-- take the last value of a `(n+1)-length` vector -/
def last (α : Typevec.{u} (n+1)) : Type _ :=
  α Fin2.fz

instance last.inhabited (α : Typevec (n+1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨(default (α Fin2.fz) : α Fin2.fz)⟩

theorem drop_append1 {α : Typevec n} {β : Type _} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl

theorem drop_append1' {α : Typevec n} {β : Type _} : drop (append1 α β) = α :=
  by 
    ext <;> apply drop_append1

theorem last_append1 {α : Typevec n} {β : Type _} : last (append1 α β) = β :=
  rfl

@[simp]
theorem append1_drop_last (α : Typevec (n+1)) : append1 (drop α) (last α) = α :=
  funext$
    fun i =>
      by 
        cases i <;> rfl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_eliminator]
def append1_cases {C : Typevec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) γ : C γ :=
  by 
    rw [←@append1_drop_last _ γ] <;> apply H

@[simp]
theorem append1_cases_append1 {C : Typevec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) α β :
  @append1_cases _ C H (append1 α β) = H α β :=
  rfl

/-- append an arrow and a function for arbitrary source and target
type vectors -/
def split_fun {α α' : Typevec (n+1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
| Fin2.fs i => f i
| Fin2.fz => g

/-- append an arrow and a function as well as their respective source
and target types / typevecs -/
def append_fun {α α' : Typevec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' :=
  split_fun f g

infixl:0 " ::: " => append_fun

/-- split off the prefix of an arrow -/
def drop_fun {α β : Typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
  fun i => f i.fs

/-- split off the last function of an arrow -/
def last_fun {α β : Typevec (n+1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz

/-- arrow in the category of `0-length` vectors -/
def nil_fun {α : Typevec 0} {β : Typevec 0} : α ⟹ β :=
  fun i => Fin2.elim0 i

theorem eq_of_drop_last_eq {α β : Typevec (n+1)} {f g : α ⟹ β} (h₀ : drop_fun f = drop_fun g)
  (h₁ : last_fun f = last_fun g) : f = g :=
  by 
    replace h₀ := congr_funₓ h₀ <;> ext1 (ieq | ⟨j, ieq⟩) <;> applyAssumption

@[simp]
theorem drop_fun_split_fun {α α' : Typevec (n+1)} (f : drop α ⟹ drop α') (g : last α → last α') :
  drop_fun (split_fun f g) = f :=
  rfl

/-- turn an equality into an arrow -/
def arrow.mp {α β : Typevec n} (h : α = β) : α ⟹ β
| i => Eq.mp (congr_funₓ h _)

/-- turn an equality into an arrow, with reverse direction -/
def arrow.mpr {α β : Typevec n} (h : α = β) : β ⟹ α
| i => Eq.mpr (congr_funₓ h _)

/-- decompose a vector into its prefix appended with its last element -/
def to_append1_drop_last {α : Typevec (n+1)} : α ⟹ (drop α ::: last α) :=
  arrow.mpr (append1_drop_last _)

/-- stitch two bits of a vector back together -/
def from_append1_drop_last {α : Typevec (n+1)} : (drop α ::: last α) ⟹ α :=
  arrow.mp (append1_drop_last _)

@[simp]
theorem last_fun_split_fun {α α' : Typevec (n+1)} (f : drop α ⟹ drop α') (g : last α → last α') :
  last_fun (split_fun f g) = g :=
  rfl

@[simp]
theorem drop_fun_append_fun {α α' : Typevec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') : drop_fun (f ::: g) = f :=
  rfl

@[simp]
theorem last_fun_append_fun {α α' : Typevec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') : last_fun (f ::: g) = g :=
  rfl

theorem split_drop_fun_last_fun {α α' : Typevec (n+1)} (f : α ⟹ α') : split_fun (drop_fun f) (last_fun f) = f :=
  eq_of_drop_last_eq rfl rfl

theorem split_fun_inj {α α' : Typevec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
  by 
    rw [←drop_fun_split_fun f g, H, ←last_fun_split_fun f g, H] <;> simp 

theorem append_fun_inj {α α' : Typevec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
  (f ::: g) = (f' ::: g') → f = f' ∧ g = g' :=
  split_fun_inj

theorem split_fun_comp {α₀ α₁ α₂ : Typevec (n+1)} (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
  (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
  split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_comp_split_fun {α γ : Typevec n} {β δ : Type _} {ε : Typevec (n+1)} (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ)
  (g₀ : last ε → β) (g₁ : β → δ) : append_fun f₁ g₁ ⊚ split_fun f₀ g₀ = split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (split_fun_comp _ _ _ _).symm

theorem append_fun_comp {α₀ α₁ α₂ : Typevec n} {β₀ β₁ β₂ : Type _} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁)
  (g₁ : β₁ → β₂) : (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_comp' {α₀ α₁ α₂ : Typevec n} {β₀ β₁ β₂ : Type _} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁)
  (g₁ : β₁ → β₂) : (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl

theorem nil_fun_comp {α₀ : Typevec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nil_fun ⊚ f₀ = f₀ :=
  funext$ fun x => Fin2.elim0 x

theorem append_fun_comp_id {α : Typevec n} {β₀ β₁ β₂ : Type _} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp]
theorem drop_fun_comp {α₀ α₁ α₂ : Typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ :=
  rfl

@[simp]
theorem last_fun_comp {α₀ α₁ α₂ : Typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ :=
  rfl

theorem append_fun_aux {α α' : Typevec n} {β β' : Type _} (f : (α ::: β) ⟹ (α' ::: β')) :
  (drop_fun f ::: last_fun f) = f :=
  eq_of_drop_last_eq rfl rfl

theorem append_fun_id_id {α : Typevec n} {β : Type _} : (@Typevec.id n α ::: @_root_.id β) = Typevec.id :=
  eq_of_drop_last_eq rfl rfl

instance subsingleton0 : Subsingleton (Typevec 0) :=
  ⟨fun a b => funext$ fun a => Fin2.elim0 a⟩

run_cmd 
  do 
      mk_simp_attr `typevec 
      tactic.add_doc_string `simp_attr.typevec "simp set for the manipulation of typevec and arrow expressions"

local prefix:0 "♯" =>
  cast
    (by 
      try 
          simp  <;>
        congr 1 <;>
          try 
            simp )

/-- cases distinction for 0-length type vector -/
protected def cases_nil {β : Typevec 0 → Sort _} (f : β Fin2.elim0) : ∀ v, β v :=
  fun v => ♯f

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- cases distinction for (n+1)-length type vector -/
protected
def cases_cons
(n : exprℕ())
{β : typevec «expr + »(n, 1) → Sort*}
(f : ∀ (t) (v : typevec n), β [«expr ::: »/«expr ::: »](v, t)) : ∀ v, β v :=
λ v : typevec «expr + »(n, 1), «expr♯ »(f v.last v.drop)

protected theorem cases_nil_append1 {β : Typevec 0 → Sort _} (f : β Fin2.elim0) : Typevec.casesNil f Fin2.elim0 = f :=
  rfl

protected theorem cases_cons_append1 (n : ℕ) {β : Typevec (n+1) → Sort _} (f : ∀ t (v : Typevec n), β (v ::: t))
  (v : Typevec n) α : Typevec.casesCons n f (v ::: α) = f α v :=
  rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₃ {β : ∀ (v v' : Typevec 0), v ⟹ v' → Sort _} (f : β Fin2.elim0 Fin2.elim0 nil_fun) :
  ∀ v v' fs, β v v' fs :=
  fun v v' fs =>
    by 
      refine' cast _ f <;>
        congr 1 <;>
          ext <;>
            try 
              intros  <;> casesM Fin2 0
      rfl

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₃ (n : ℕ) {β : ∀ (v v' : Typevec (n+1)), v ⟹ v' → Sort _}
  (F : ∀ t t' (f : t → t') (v v' : Typevec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
  ∀ v v' fs, β v v' fs :=
  by 
    intro v v' 
    rw [←append1_drop_last v, ←append1_drop_last v']
    intro fs 
    rw [←split_drop_fun_last_fun fs]
    apply F

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₂ {β : «expr ⟹ »(fin2.elim0, fin2.elim0) → Sort*} (f : β nil_fun) : ∀ f, β f :=
begin
  intro [ident g],
  have [] [":", expr «expr = »(g, nil_fun)] [],
  ext [] ["⟨", "⟩"] [],
  rw [expr this] [],
  exact [expr f]
end

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₂ (n : ℕ) (t t' : Type _) (v v' : Typevec n) {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
  (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs :=
  by 
    intro fs 
    rw [←split_drop_fun_last_fun fs]
    apply F

theorem typevec_cases_nil₂_append_fun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort _} (f : β nil_fun) :
  typevec_cases_nil₂ f nil_fun = f :=
  rfl

theorem typevec_cases_cons₂_append_fun (n : ℕ) (t t' : Type _) (v v' : Typevec n) {β : (v ::: t) ⟹ (v' ::: t') → Sort _}
  (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) f fs : typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : Typevec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
| Fin2.fs i => fun x => True
| Fin2.fz => p

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and
all the other elements are equal. -/
def rel_last (α : Typevec n) {β γ : Type _} (r : β → γ → Prop) : ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
| Fin2.fs i => Eq
| Fin2.fz => r

section Liftp'

open Nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def repeat : ∀ (n : ℕ) (t : Sort _), Typevec n
| 0, t => Fin2.elim0
| Nat.succ i, t => append1 (repeat i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def Prod : ∀ {n} (α β : Typevec.{u} n), Typevec n
| 0, α, β => Fin2.elim0
| n+1, α, β => Prod (drop α) (drop β) ::: last α × last β

localized [Mvfunctor] infixl:45 " ⊗ " => Typevec.Prod

/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β} (x : β) : ∀ {n} (α : Typevec n), α ⟹ repeat _ β
| succ n, α, Fin2.fs i => const (drop α) _
| succ n, α, Fin2.fz => fun _ => x

open function(uncurry)

/-- vector of equality on a product of vectors -/
def repeat_eq : ∀ {n} (α : Typevec n), α ⊗ α ⟹ repeat _ Prop
| 0, α => nil_fun
| succ n, α => repeat_eq (drop α) ::: uncurry Eq

theorem const_append1 {β γ} (x : γ) {n} (α : Typevec n) :
  Typevec.constₓ x (α ::: β) = append_fun (Typevec.constₓ x α) fun _ => x :=
  by 
    ext i : 1 <;> cases i <;> rfl

theorem eq_nil_fun {α β : Typevec 0} (f : α ⟹ β) : f = nil_fun :=
  by 
    ext x <;> cases x

theorem id_eq_nil_fun {α : Typevec 0} : @id _ α = nil_fun :=
  by 
    ext x <;> cases x

theorem const_nil {β} (x : β) (α : Typevec 0) : Typevec.constₓ x α = nil_fun :=
  by 
    ext i : 1 <;> cases i <;> rfl

@[typevec]
theorem repeat_eq_append1 {β} {n} (α : Typevec n) : repeat_eq (α ::: β) = split_fun (repeat_eq α) (uncurry Eq) :=
  by 
    induction n <;> rfl

@[typevec]
theorem repeat_eq_nil (α : Typevec 0) : repeat_eq α = nil_fun :=
  by 
    ext i : 1 <;> cases i <;> rfl

/-- predicate on a type vector to constrain only the last object -/
def pred_last' (α : Typevec n) {β : Type _} (p : β → Prop) : (α ::: β) ⟹ repeat (n+1) Prop :=
  split_fun (Typevec.constₓ True α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
def rel_last' (α : Typevec n) {β : Type _} (p : β → β → Prop) : (α ::: β) ⊗ (α ::: β) ⟹ repeat (n+1) Prop :=
  split_fun (repeat_eq α) (uncurry p)

/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def curry (F : Typevec.{u} (n+1) → Type _) (α : Type u) (β : Typevec.{u} n) : Type _ :=
  F (β ::: α)

instance curry.inhabited (F : Typevec.{u} (n+1) → Type _) (α : Type u) (β : Typevec.{u} n)
  [I : Inhabited (F$ (β ::: α))] : Inhabited (curry F α β) :=
  I

/-- arrow to remove one element of a `repeat` vector -/
def drop_repeat (α : Type _) : ∀ {n}, drop (repeat (succ n) α) ⟹ repeat n α
| succ n, Fin2.fs i => drop_repeat i
| succ n, Fin2.fz => _root_.id

/-- projection for a repeat vector -/
def of_repeat {α : Sort _} : ∀ {n i}, repeat n α i → α
| _, Fin2.fz => _root_.id
| _, Fin2.fs i => @of_repeat _ i

theorem const_iff_true {α : Typevec n} {i x p} : of_repeat (Typevec.constₓ p α i x) ↔ p :=
  by 
    induction i <;> [rfl, erw [Typevec.constₓ, @i_ih (drop α) x]]

variable{α β γ : Typevec.{u} n}

variable(p : α ⟹ repeat n Prop)(r : α ⊗ α ⟹ repeat n Prop)

/-- left projection of a `prod` vector -/
def Prod.fst : ∀ {n} {α β : Typevec.{u} n}, α ⊗ β ⟹ α
| succ n, α, β, Fin2.fs i => @Prod.fst _ (drop α) (drop β) i
| succ n, α, β, Fin2.fz => _root_.prod.fst

/-- right projection of a `prod` vector -/
def Prod.snd : ∀ {n} {α β : Typevec.{u} n}, α ⊗ β ⟹ β
| succ n, α, β, Fin2.fs i => @Prod.snd _ (drop α) (drop β) i
| succ n, α, β, Fin2.fz => _root_.prod.snd

/-- introduce a product where both components are the same -/
def prod.diag : ∀ {n} {α : Typevec.{u} n}, α ⟹ α ⊗ α
| succ n, α, Fin2.fs i, x => @prod.diag _ (drop α) _ x
| succ n, α, Fin2.fz, x => (x, x)

/-- constructor for `prod` -/
def Prod.mk : ∀ {n} {α β : Typevec.{u} n} (i : Fin2 n), α i → β i → (α ⊗ β) i
| succ n, α, β, Fin2.fs i => Prod.mk i
| succ n, α, β, Fin2.fz => _root_.prod.mk

@[simp]
theorem prod_fst_mk {α β : Typevec n} (i : Fin2 n) (a : α i) (b : β i) : Typevec.Prod.fst i (Prod.mk i a b) = a :=
  by 
    induction i <;> simp_all [Prod.fst, Prod.mk]

@[simp]
theorem prod_snd_mk {α β : Typevec n} (i : Fin2 n) (a : α i) (b : β i) : Typevec.Prod.snd i (Prod.mk i a b) = b :=
  by 
    induction i <;> simp_all [Prod.snd, Prod.mk]

/-- `prod` is functorial -/
protected def Prod.mapₓ : ∀ {n} {α α' β β' : Typevec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
| succ n, α, α', β, β', x, y, Fin2.fs i, a =>
  @Prod.mapₓ _ (drop α) (drop α') (drop β) (drop β') (drop_fun x) (drop_fun y) _ a
| succ n, α, α', β, β', x, y, Fin2.fz, a => (x _ a.1, y _ a.2)

localized [Mvfunctor] infixl:45 " ⊗' " => Typevec.Prod.map

theorem fst_prod_mk {α α' β β' : Typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  Typevec.Prod.fst ⊚ (f ⊗' g) = f ⊚ Typevec.Prod.fst :=
  by 
    ext i <;> induction i <;> [rfl, apply i_ih]

theorem snd_prod_mk {α α' β β' : Typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  Typevec.Prod.snd ⊚ (f ⊗' g) = g ⊚ Typevec.Prod.snd :=
  by 
    ext i <;> induction i <;> [rfl, apply i_ih]

theorem fst_diag {α : Typevec n} : Typevec.Prod.fst ⊚ (prod.diag : α ⟹ _) = id :=
  by 
    ext i <;> induction i <;> [rfl, apply i_ih]

theorem snd_diag {α : Typevec n} : Typevec.Prod.snd ⊚ (prod.diag : α ⟹ _) = id :=
  by 
    ext i <;> induction i <;> [rfl, apply i_ih]

theorem repeat_eq_iff_eq {α : Typevec n} {i x y} : of_repeat (repeat_eq α i (Prod.mk _ x y)) ↔ x = y :=
  by 
    induction i <;> [rfl, erw [repeat_eq, @i_ih (drop α) x y]]

/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def subtype_ : ∀ {n} {α : Typevec.{u} n} (p : α ⟹ repeat n Prop), Typevec n
| _, α, p, Fin2.fz => _root_.subtype fun x => p Fin2.fz x
| _, α, p, Fin2.fs i => subtype_ (drop_fun p) i

/-- projection on `subtype_` -/
def subtype_val : ∀ {n} {α : Typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ α
| succ n, α, p, Fin2.fs i => @subtype_val n _ _ i
| succ n, α, p, Fin2.fz => _root_.subtype.val

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def to_subtype : ∀
{n}
{α : typevec.{u} n}
(p : «expr ⟹ »(α, repeat n exprProp())), «expr ⟹ »(λ i : fin2 n, {x // «expr $ »(of_repeat, p i x)}, subtype_ p)
| succ n, α, p, fin2.fs i, x := to_subtype (drop_fun p) i x
| succ n, α, p, fin2.fz, x := x

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def of_subtype : ∀
{n}
{α : typevec.{u} n}
(p : «expr ⟹ »(α, repeat n exprProp())), «expr ⟹ »(subtype_ p, λ i : fin2 n, {x // «expr $ »(of_repeat, p i x)})
| succ n, α, p, fin2.fs i, x := of_subtype _ i x
| succ n, α, p, fin2.fz, x := x

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def to_subtype' : ∀
{n}
{α : typevec.{u} n}
(p : «expr ⟹ »(«expr ⊗ »(α, α), repeat n exprProp())), «expr ⟹ »(λ
 i : fin2 n, {x : «expr × »(α i, α i) // «expr $ »(of_repeat, p i (prod.mk _ x.1 x.2))}, subtype_ p)
| succ n, α, p, fin2.fs i, x := to_subtype' (drop_fun p) i x
| succ n, α, p, fin2.fz, x := ⟨x.val, cast (by congr; simp [] [] [] ["[", expr prod.mk, "]"] [] []) x.property⟩

-- error in Data.Typevec: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def of_subtype' : ∀
{n}
{α : typevec.{u} n}
(p : «expr ⟹ »(«expr ⊗ »(α, α), repeat n exprProp())), «expr ⟹ »(subtype_ p, λ
 i : fin2 n, {x : «expr × »(α i, α i) // «expr $ »(of_repeat, p i (prod.mk _ x.1 x.2))})
| ._, α, p, fin2.fs i, x := of_subtype' _ i x
| ._, α, p, fin2.fz, x := ⟨x.val, cast (by congr; simp [] [] [] ["[", expr prod.mk, "]"] [] []) x.property⟩

/-- similar to `diag` but the target vector is a `subtype_`
guaranteeing the equality of the components -/
def diag_sub : ∀ {n} {α : Typevec.{u} n}, α ⟹ subtype_ (repeat_eq α)
| succ n, α, Fin2.fs i, x => @diag_sub _ (drop α) _ x
| succ n, α, Fin2.fz, x => ⟨(x, x), rfl⟩

theorem subtype_val_nil {α : Typevec.{u} 0} (ps : α ⟹ repeat 0 Prop) : Typevec.subtypeVal ps = nil_fun :=
  funext$
    by 
      rintro ⟨⟩ <;> rfl

theorem diag_sub_val {n} {α : Typevec.{u} n} : subtype_val (repeat_eq α) ⊚ diag_sub = prod.diag :=
  by 
    ext i <;> induction i <;> [rfl, apply i_ih]

theorem prod_id : ∀ {n} {α β : Typevec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) :=
  by 
    intros 
    ext i a 
    induction i
    ·
      cases a 
      rfl
    ·
      apply i_ih

theorem append_prod_append_fun {n} {α α' β β' : Typevec.{u} n} {φ φ' ψ ψ' : Type u} {f₀ : α ⟹ α'} {g₀ : β ⟹ β'}
  {f₁ : φ → φ'} {g₁ : ψ → ψ'} : (f₀ ⊗' g₀ ::: _root_.prod.map f₁ g₁) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) :=
  by 
    ext i a <;> cases i <;> [cases a, skip] <;> rfl

end Liftp'

@[simp]
theorem drop_fun_diag {α} : drop_fun (@prod.diag (n+1) α) = prod.diag :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem drop_fun_subtype_val {α} (p : α ⟹ repeat (n+1) Prop) : drop_fun (subtype_val p) = subtype_val _ :=
  rfl

@[simp]
theorem last_fun_subtype_val {α} (p : α ⟹ repeat (n+1) Prop) : last_fun (subtype_val p) = Subtype.val :=
  rfl

@[simp]
theorem drop_fun_to_subtype {α} (p : α ⟹ repeat (n+1) Prop) : drop_fun (to_subtype p) = to_subtype _ :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem last_fun_to_subtype {α} (p : α ⟹ repeat (n+1) Prop) : last_fun (to_subtype p) = _root_.id :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem drop_fun_of_subtype {α} (p : α ⟹ repeat (n+1) Prop) : drop_fun (of_subtype p) = of_subtype _ :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem last_fun_of_subtype {α} (p : α ⟹ repeat (n+1) Prop) : last_fun (of_subtype p) = _root_.id :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem drop_fun_rel_last {α : Typevec n} {β} (R : β → β → Prop) : drop_fun (rel_last' α R) = repeat_eq α :=
  rfl

attribute [simp] drop_append1'

open_locale Mvfunctor

@[simp]
theorem drop_fun_prod {α α' β β' : Typevec (n+1)} (f : α ⟹ β) (f' : α' ⟹ β') :
  drop_fun (f ⊗' f') = (drop_fun f ⊗' drop_fun f') :=
  by 
    ext i : 2
    induction i <;> simp [drop_fun] <;> rfl

@[simp]
theorem last_fun_prod {α α' β β' : Typevec (n+1)} (f : α ⟹ β) (f' : α' ⟹ β') :
  last_fun (f ⊗' f') = _root_.prod.map (last_fun f) (last_fun f') :=
  by 
    ext i : 1
    induction i <;> simp [last_fun] <;> rfl

@[simp]
theorem drop_fun_from_append1_drop_last {α : Typevec (n+1)} : drop_fun (@from_append1_drop_last _ α) = id :=
  rfl

@[simp]
theorem last_fun_from_append1_drop_last {α : Typevec (n+1)} : last_fun (@from_append1_drop_last _ α) = _root_.id :=
  rfl

@[simp]
theorem drop_fun_id {α : Typevec (n+1)} : drop_fun (@Typevec.id _ α) = id :=
  rfl

@[simp]
theorem prod_map_id {α β : Typevec n} : (@Typevec.id _ α ⊗' @Typevec.id _ β) = id :=
  by 
    ext i : 2
    induction i <;> simp only [Typevec.Prod.map, drop_fun_id]
    cases x 
    rfl 
    rfl

@[simp]
theorem subtype_val_diag_sub {α : Typevec n} : subtype_val (repeat_eq α) ⊚ diag_sub = prod.diag :=
  by 
    clear * - 
    ext i 
    induction i <;> [rfl, apply i_ih]

@[simp]
theorem to_subtype_of_subtype {α : Typevec n} (p : α ⟹ repeat n Prop) : to_subtype p ⊚ of_subtype p = id :=
  by 
    ext i x <;> induction i <;> dsimp only [id, to_subtype, comp, of_subtype]  at * <;> simp 

@[simp]
theorem subtype_val_to_subtype {α : Typevec n} (p : α ⟹ repeat n Prop) :
  subtype_val p ⊚ to_subtype p = fun _ => Subtype.val :=
  by 
    ext i x <;> induction i <;> dsimp only [to_subtype, comp, subtype_val]  at * <;> simp 

@[simp]
theorem to_subtype_of_subtype_assoc {α β : Typevec n} (p : α ⟹ repeat n Prop) (f : β ⟹ subtype_ p) :
  @to_subtype n _ p ⊚ of_subtype _ ⊚ f = f :=
  by 
    rw [←comp_assoc, to_subtype_of_subtype] <;> simp 

@[simp]
theorem to_subtype'_of_subtype' {α : Typevec n} (r : α ⊗ α ⟹ repeat n Prop) : to_subtype' r ⊚ of_subtype' r = id :=
  by 
    ext i x <;> induction i <;> dsimp only [id, to_subtype', comp, of_subtype']  at * <;> simp [Subtype.eta]

theorem subtype_val_to_subtype' {α : Typevec n} (r : α ⊗ α ⟹ repeat n Prop) :
  subtype_val r ⊚ to_subtype' r = fun i x => Prod.mk i x.1.fst x.1.snd :=
  by 
    ext i x <;> induction i <;> dsimp only [id, to_subtype', comp, subtype_val, Prod.mk]  at * <;> simp 

end Typevec

