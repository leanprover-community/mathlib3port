import Mathbin.Data.Pfunctor.Multivariate.Basic

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive list_shape (a b : Type)
| nil : list_shape
| cons : a -> b -> list_shape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def list (a : Type) := fix list_shape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def multiset (a : Type) := qpf.quot list.perm list a -- not the actual notion
```

And `multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive tree (a : Type)
| node : a -> multiset tree -> tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive tree' (a : Type)
| node : a -> multiset tree' -> tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp
   * sigma / pi
   * prj
   * const

each proves that some operations on functors preserves the QPF structure

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open_locale Mvfunctor

/--
Multivariate quotients of polynomial functors.
-/
class Mvqpf{n : ℕ}(F : Typevec.{u} n → Type _)[Mvfunctor F] where 
  p : Mvpfunctor.{u} n 
  abs : ∀ {α}, P.obj α → F α 
  repr : ∀ {α}, F α → P.obj α 
  abs_repr : ∀ {α} (x : F α), abs (reprₓ x) = x 
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P.obj α), abs (f <$$> p) = f <$$> abs p

namespace Mvqpf

variable{n : ℕ}{F : Typevec.{u} n → Type _}[Mvfunctor F][q : Mvqpf F]

include q

open mvfunctor(Liftp Liftr)

/-!
### Show that every mvqpf is a lawful mvfunctor.
-/


protected theorem id_map {α : Typevec n} (x : F α) : Typevec.id <$$> x = x :=
  by 
    rw [←abs_repr x]
    cases' reprₓ x with a f 
    rw [←abs_map]
    rfl

@[simp]
theorem comp_map {α β γ : Typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) : (g ⊚ f) <$$> x = g <$$> f <$$> x :=
  by 
    rw [←abs_repr x]
    cases' reprₓ x with a f 
    rw [←abs_map, ←abs_map, ←abs_map]
    rfl

instance (priority := 100)IsLawfulMvfunctor : IsLawfulMvfunctor F :=
  { id_map := @Mvqpf.id_map n F _ _, comp_map := @comp_map n F _ _ }

theorem liftp_iff {α : Typevec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
  liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
  by 
    split 
    ·
      rintro ⟨y, hy⟩
      cases' h : reprₓ y with a f 
      use a, fun i j => (f i j).val 
      split 
      ·
        rw [←hy, ←abs_repr y, h, ←abs_map]
        rfl 
      intro i j 
      apply (f i j).property 
    rintro ⟨a, f, h₀, h₁⟩
    dsimp  at *
    use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
    rw [←abs_map, h₀]
    rfl

theorem liftr_iff {α : Typevec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
  by 
    split 
    ·
      rintro ⟨u, xeq, yeq⟩
      cases' h : reprₓ u with a f 
      use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd 
      split 
      ·
        rw [←xeq, ←abs_repr u, h, ←abs_map]
        rfl 
      split 
      ·
        rw [←yeq, ←abs_repr u, h, ←abs_map]
        rfl 
      intro i j 
      exact (f i j).property 
    rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
    use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
    dsimp 
    split 
    ·
      rw [xeq, ←abs_map]
      rfl 
    rw [yeq, ←abs_map]
    rfl

open Set

open Mvfunctor

-- error in Data.Qpf.Multivariate.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_supp
{α : typevec n}
(x : F α)
(i)
(u : α i) : «expr ↔ »(«expr ∈ »(u, supp x i), ∀ a f, «expr = »(abs ⟨a, f⟩, x) → «expr ∈ »(u, «expr '' »(f i, univ))) :=
begin
  rw ["[", expr supp, "]"] [],
  dsimp [] [] [] [],
  split,
  { intros [ident h, ident a, ident f, ident haf],
    have [] [":", expr liftp (λ i u, «expr ∈ »(u, «expr '' »(f i, univ))) x] [],
    { rw [expr liftp_iff] [],
      refine [expr ⟨a, f, haf.symm, _⟩],
      intros [ident i, ident u],
      exact [expr mem_image_of_mem _ (mem_univ _)] },
    exact [expr h this] },
  intros [ident h, ident p],
  rw [expr liftp_iff] [],
  rintros ["⟨", ident a, ",", ident f, ",", ident xeq, ",", ident h', "⟩"],
  rcases [expr h a f xeq.symm, "with", "⟨", ident i, ",", "_", ",", ident hi, "⟩"],
  rw ["<-", expr hi] [],
  apply [expr h']
end

theorem supp_eq {α : Typevec n} {i} (x : F α) : supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } :=
  by 
    ext <;> apply mem_supp

-- error in Data.Qpf.Multivariate.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_good_supp_iff
{α : typevec n}
(x : F α) : «expr ↔ »(∀
 p, «expr ↔ »(liftp p x, ∀
  (i)
  (u «expr ∈ » supp x i), p i u), «expr∃ , »((a
   f), «expr ∧ »(«expr = »(abs ⟨a, f⟩, x), ∀
   i a' f', «expr = »(abs ⟨a', f'⟩, x) → «expr ⊆ »(«expr '' »(f i, univ), «expr '' »(f' i, univ))))) :=
begin
  split,
  { intros [ident h],
    have [] [":", expr liftp (supp x) x] [],
    by { rw [expr h] [],
      introv [],
      exact [expr id] },
    rw [expr liftp_iff] ["at", ident this],
    rcases [expr this, "with", "⟨", ident a, ",", ident f, ",", ident xeq, ",", ident h', "⟩"],
    refine [expr ⟨a, f, xeq.symm, _⟩],
    intros [ident a', ident f', ident h''],
    rintros [ident hu, ident u, "⟨", ident j, ",", ident h₂, ",", ident hfi, "⟩"],
    have [ident hh] [":", expr «expr ∈ »(u, supp x a')] [],
    by rw ["<-", expr hfi] []; apply [expr h'],
    refine [expr (mem_supp x _ u).mp hh _ _ hu] },
  rintros ["⟨", ident a, ",", ident f, ",", ident xeq, ",", ident h, "⟩", ident p],
  rw [expr liftp_iff] [],
  split,
  { rintros ["⟨", ident a', ",", ident f', ",", ident xeq', ",", ident h', "⟩", ident i, ident u, ident usuppx],
    rcases [expr (mem_supp x _ u).mp @usuppx a' f' xeq'.symm, "with", "⟨", ident i, ",", "_", ",", ident f'ieq, "⟩"],
    rw ["<-", expr f'ieq] [],
    apply [expr h'] },
  intro [ident h'],
  refine [expr ⟨a, f, xeq.symm, _⟩],
  intros [ident j, ident y],
  apply [expr h'],
  rw [expr mem_supp] [],
  intros [ident a', ident f', ident xeq'],
  apply [expr h _ a' f' xeq'],
  apply [expr mem_image_of_mem _ (mem_univ _)]
end

variable(q)

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform : Prop :=
  ∀ ⦃α : Typevec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ

/-- does `abs` preserve `liftp`? -/
def liftp_preservation : Prop :=
  ∀ ⦃α : Typevec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P.obj α), liftp p (abs x) ↔ liftp p x

/-- does `abs` preserve `supp`? -/
def supp_preservation : Prop :=
  ∀ ⦃α⦄ (x : q.P.obj α), supp (abs x) = supp x

variable(q)

theorem supp_eq_of_is_uniform (h : q.is_uniform) {α : Typevec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
  ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ :=
  by 
    intro 
    ext u 
    rw [mem_supp]
    split 
    ·
      intro h' 
      apply h' _ _ rfl 
    intro h' a' f' e 
    rw [←h _ _ _ _ e.symm]
    apply h'

theorem liftp_iff_of_is_uniform (h : q.is_uniform) {α : Typevec n} (x : F α) (p : ∀ i, α i → Prop) :
  liftp p x ↔ ∀ i u (_ : u ∈ supp x i), p i u :=
  by 
    rw [liftp_iff, ←abs_repr x]
    cases' reprₓ x with a f 
    split 
    ·
      rintro ⟨a', f', abseq, hf⟩ u 
      rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq]
      rintro b ⟨i, _, hi⟩
      rw [←hi]
      apply hf 
    intro h' 
    refine' ⟨a, f, rfl, fun _ i => h' _ _ _⟩
    rw [supp_eq_of_is_uniform h]
    exact ⟨i, mem_univ i, rfl⟩

theorem supp_map (h : q.is_uniform) {α β : Typevec n} (g : α ⟹ β) (x : F α) i : supp (g <$$> x) i = g i '' supp x i :=
  by 
    rw [←abs_repr x]
    cases' reprₓ x with a f 
    rw [←abs_map, Mvpfunctor.map_eq]
    rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, ←image_comp]
    rfl

theorem supp_preservation_iff_uniform : q.supp_preservation ↔ q.is_uniform :=
  by 
    split 
    ·
      intro h α a a' f f' h' i 
      rw [←Mvpfunctor.supp_eq, ←Mvpfunctor.supp_eq, ←h, h', h]
    ·
      rintro h α ⟨a, f⟩
      ext 
      rwa [supp_eq_of_is_uniform, Mvpfunctor.supp_eq]

-- error in Data.Qpf.Multivariate.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem supp_preservation_iff_liftp_preservation : «expr ↔ »(q.supp_preservation, q.liftp_preservation) :=
begin
  split; intro [ident h],
  { rintros [ident α, ident p, "⟨", ident a, ",", ident f, "⟩"],
    have [ident h'] [] [":=", expr h],
    rw [expr supp_preservation_iff_uniform] ["at", ident h'],
    dsimp ["only"] ["[", expr supp_preservation, ",", expr supp, "]"] [] ["at", ident h],
    simp [] [] ["only"] ["[", expr liftp_iff_of_is_uniform, ",", expr supp_eq_of_is_uniform, ",", expr mvpfunctor.liftp_iff', ",", expr h', ",", expr image_univ, ",", expr mem_range, ",", expr exists_imp_distrib, "]"] [] [],
    split; intros []; subst_vars; solve_by_elim [] [] [] [] },
  { rintros [ident α, "⟨", ident a, ",", ident f, "⟩"],
    simp [] [] ["only"] ["[", expr liftp_preservation, "]"] [] ["at", ident h],
    ext [] [] [],
    simp [] [] [] ["[", expr supp, ",", expr h, "]"] [] [] }
end

theorem liftp_preservation_iff_uniform : q.liftp_preservation ↔ q.is_uniform :=
  by 
    rw [←supp_preservation_iff_liftp_preservation, supp_preservation_iff_uniform]

end Mvqpf

