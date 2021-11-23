import Mathbin.Data.Equiv.Basic 
import Mathbin.Data.Set.Basic

/-!
# Partial values of a type

This file defines `part α`, the partial values of a type.

`o : part α` carries a proposition `o.dom`, its domain, along with a function `get : o.dom → α`, its
value. The rule is then that every partial value has a value but, to access it, you need to provide
a proof of the domain.

`part α` behaves the same as `option α` except that `o : option α` is decidably `none` or `some a`
for some `a : α`, while the domain of `o : part α` doesn't have to be decidable. That means you can
translate back and forth between a partial value with a decidable domain and an option, and
`option α` and `part α` are classically equivalent. In general, `part α` is bigger than `option α`.

In current mathlib, `part ℕ`, aka `enat`, is used to move decidability of the order to decidability
of `enat.find` (which is the smallest natural satisfying a predicate, or `∞` if there's none).

## Main declarations

`option`-like declarations:
* `part.none`: The partial value whose domain is `false`.
* `part.some a`: The partial value whose domain is `true` and whose value is `a`.
* `part.of_option`: Converts an `option α` to a `part α` by sending `none` to `none` and `some a` to
  `some a`.
* `part.to_option`: Converts a `part α` with a decidable domain to an `option α`.
* `part.equiv_option`: Classical equivalence between `part α` and `option α`.

Monadic structure:
* `part.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* `part.map`: Maps the value and keeps the same domain.

Other:
* `part.restrict`: `part.restrict p o` replaces the domain of `o : part α` by `p : Prop` so long as
  `p → o.dom`.
* `part.assert`: `assert p f` appends `p` to the domains of the values of a partial function.
* `part.unwrap`: Gets the value of a partial value regardless of its domain. Unsound.

## Notation

For `a : α`, `o : part α`, `a ∈ o` means that `o` is defined and equal to `a`. Formally, it means
`o.dom` and `o.get _ = a`.
-/


/-- `part α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure Part.{u}(α : Type u) : Type u where 
  Dom : Prop 
  get : dom → α

namespace Part

variable{α : Type _}{β : Type _}{γ : Type _}

/-- Convert a `part α` with a decidable domain to an option -/
def to_option (o : Part α) [Decidable o.dom] : Option α :=
  if h : dom o then some (o.get h) else none

/-- `part` extensionality -/
theorem ext' : ∀ {o p : Part α} H1 : o.dom ↔ p.dom H2 : ∀ h₁ h₂, o.get h₁ = p.get h₂, o = p
| ⟨od, o⟩, ⟨pd, p⟩, H1, H2 =>
  have t : od = pd := propext H1 
  by 
    cases t <;> rw [show o = p from funext$ fun p => H2 p p]

/-- `part` eta expansion -/
@[simp]
theorem eta : ∀ o : Part α, (⟨o.dom, fun h => o.get h⟩ : Part α) = o
| ⟨h, f⟩ => rfl

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem (a : α) (o : Part α) : Prop :=
  ∃ h, o.get h = a

instance  : HasMem α (Part α) :=
  ⟨Part.Mem⟩

theorem mem_eq (a : α) (o : Part α) : (a ∈ o) = ∃ h, o.get h = a :=
  rfl

theorem dom_iff_mem : ∀ {o : Part α}, o.dom ↔ ∃ y, y ∈ o
| ⟨p, f⟩ => ⟨fun h => ⟨f h, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩

theorem get_mem {o : Part α} h : get o h ∈ o :=
  ⟨_, rfl⟩

/-- `part` extensionality -/
@[ext]
theorem ext {o p : Part α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
  ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩$ fun a b => ((H _).2 ⟨_, rfl⟩).snd

/-- The `none` value in `part` has a `false` domain and an empty function. -/
def none : Part α :=
  ⟨False, False.ndrec _⟩

instance  : Inhabited (Part α) :=
  ⟨none⟩

@[simp]
theorem not_mem_none (a : α) : a ∉ @none α :=
  fun h => h.fst

/-- The `some a` value in `part` has a `true` domain and the
  function returns `a`. -/
def some (a : α) : Part α :=
  ⟨True, fun _ => a⟩

theorem mem_unique : ∀ {a b : α} {o : Part α}, a ∈ o → b ∈ o → a = b
| _, _, ⟨p, f⟩, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩ => rfl

theorem mem.left_unique : Relator.LeftUnique (· ∈ · : α → Part α → Prop) :=
  fun a o b => mem_unique

theorem get_eq_of_mem {o : Part α} {a} (h : a ∈ o) h' : get o h' = a :=
  mem_unique ⟨_, rfl⟩ h

protected theorem Subsingleton (o : Part α) : Set.Subsingleton { a | a ∈ o } :=
  fun a ha b hb => mem_unique ha hb

@[simp]
theorem get_some {a : α} (ha : (some a).Dom) : get (some a) ha = a :=
  rfl

theorem mem_some (a : α) : a ∈ some a :=
  ⟨trivialₓ, rfl⟩

@[simp]
theorem mem_some_iff {a b} : b ∈ (some a : Part α) ↔ b = a :=
  ⟨fun ⟨h, e⟩ => e.symm, fun e => ⟨trivialₓ, e.symm⟩⟩

theorem eq_some_iff {a : α} {o : Part α} : o = some a ↔ a ∈ o :=
  ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩

theorem eq_none_iff {o : Part α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e => e.symm ▸ not_mem_none,
    fun h =>
      ext
        (by 
          simpa)⟩

theorem eq_none_iff' {o : Part α} : o = none ↔ ¬o.dom :=
  ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun a h' => h h'.fst⟩

@[simp]
theorem some_ne_none (x : α) : some x ≠ none :=
  by 
    intro h 
    change none.dom 
    rw [←h]
    trivial

@[simp]
theorem none_ne_some (x : α) : none ≠ some x :=
  (some_ne_none x).symm

theorem ne_none_iff {o : Part α} : o ≠ none ↔ ∃ x, o = some x :=
  by 
    split 
    ·
      rw [Ne, eq_none_iff', not_not]
      exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
    ·
      rintro ⟨x, rfl⟩
      apply some_ne_none

theorem eq_none_or_eq_some (o : Part α) : o = none ∨ ∃ x, o = some x :=
  or_iff_not_imp_left.2 ne_none_iff.1

@[simp]
theorem some_inj {a b : α} : Part.some a = some b ↔ a = b :=
  Function.Injective.eq_iff fun a b h => congr_funₓ (eq_of_heq (Part.mk.inj h).2) trivialₓ

@[simp]
theorem some_get {a : Part α} (ha : a.dom) : Part.some (Part.get a ha) = a :=
  Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

theorem get_eq_iff_eq_some {a : Part α} {ha : a.dom} {b : α} : a.get ha = b ↔ a = some b :=
  ⟨fun h =>
      by 
        simp [h.symm],
    fun h =>
      by 
        simp [h]⟩

theorem get_eq_get_of_eq (a : Part α) (ha : a.dom) {b : Part α} (h : a = b) : a.get ha = b.get (h ▸ ha) :=
  by 
    congr 
    exact h

theorem get_eq_iff_mem {o : Part α} {a : α} (h : o.dom) : o.get h = a ↔ a ∈ o :=
  ⟨fun H => ⟨h, H⟩, fun ⟨h', H⟩ => H⟩

theorem eq_get_iff_mem {o : Part α} {a : α} (h : o.dom) : a = o.get h ↔ a ∈ o :=
  eq_comm.trans (get_eq_iff_mem h)

@[simp]
theorem none_to_option [Decidable (@none α).Dom] : (none : Part α).toOption = Option.none :=
  dif_neg id

@[simp]
theorem some_to_option (a : α) [Decidable (some a).Dom] : (some a).toOption = Option.some a :=
  dif_pos trivialₓ

instance none_decidable : Decidable (@none α).Dom :=
  Decidable.false

instance some_decidable (a : α) : Decidable (some a).Dom :=
  Decidable.true

/-- Retrieves the value of `a : part α` if it exists, and return the provided default value
otherwise. -/
def get_or_else (a : Part α) [Decidable a.dom] (d : α) :=
  if ha : a.dom then a.get ha else d

@[simp]
theorem get_or_else_none (d : α) [Decidable (none : Part α).Dom] : get_or_else none d = d :=
  dif_neg id

@[simp]
theorem get_or_else_some (a : α) (d : α) [Decidable (some a).Dom] : get_or_else (some a) d = a :=
  dif_pos trivialₓ

@[simp]
theorem mem_to_option {o : Part α} [Decidable o.dom] {a : α} : a ∈ to_option o ↔ a ∈ o :=
  by 
    unfold to_option 
    byCases' h : o.dom <;> simp [h]
    ·
      exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
    ·
      exact mt Exists.fst h

/-- Converts an `option α` into a `part α`. -/
def of_option : Option α → Part α
| Option.none => none
| Option.some a => some a

@[simp]
theorem mem_of_option {a : α} : ∀ {o : Option α}, a ∈ of_option o ↔ a ∈ o
| Option.none => ⟨fun h => h.fst.elim, fun h => Option.noConfusion h⟩
| Option.some b => ⟨fun h => congr_argₓ Option.some h.snd, fun h => ⟨trivialₓ, Option.some.injₓ h⟩⟩

@[simp]
theorem of_option_dom {α} : ∀ o : Option α, (of_option o).Dom ↔ o.is_some
| Option.none =>
  by 
    simp [of_option, none]
| Option.some a =>
  by 
    simp [of_option]

theorem of_option_eq_get {α} (o : Option α) : of_option o = ⟨_, @Option.get _ o⟩ :=
  Part.ext' (of_option_dom o)$
    fun h₁ h₂ =>
      by 
        cases o <;> [cases h₁, rfl]

instance  : Coe (Option α) (Part α) :=
  ⟨of_option⟩

@[simp]
theorem mem_coe {a : α} {o : Option α} : a ∈ (o : Part α) ↔ a ∈ o :=
  mem_of_option

@[simp]
theorem coe_none : (@Option.none α : Part α) = none :=
  rfl

@[simp]
theorem coe_some (a : α) : (Option.some a : Part α) = some a :=
  rfl

@[elab_as_eliminator]
protected theorem induction_on {P : Part α → Prop} (a : Part α) (hnone : P none) (hsome : ∀ a : α, P (some a)) : P a :=
  (Classical.em a.dom).elim (fun h => Part.some_get h ▸ hsome _) fun h => (eq_none_iff'.2 h).symm ▸ hnone

instance of_option_decidable : ∀ o : Option α, Decidable (of_option o).Dom
| Option.none => Part.noneDecidable
| Option.some a => Part.someDecidable a

@[simp]
theorem to_of_option (o : Option α) : to_option (of_option o) = o :=
  by 
    cases o <;> rfl

@[simp]
theorem of_to_option (o : Part α) [Decidable o.dom] : of_option (to_option o) = o :=
  ext$ fun a => mem_of_option.trans mem_to_option

-- error in Data.Part: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `part α` is (classically) equivalent to `option α`. -/
noncomputable
def equiv_option : «expr ≃ »(part α, option α) :=
by haveI [] [] [":=", expr classical.dec]; exact [expr ⟨λ
  o, to_option o, of_option, λ o, of_to_option o, λ o, eq.trans (by dsimp [] [] [] []; congr) (to_of_option o)⟩]

/-- We give `part α` the order where everything is greater than `none`. -/
instance  : PartialOrderₓ (Part α) :=
  { le := fun x y => ∀ i, i ∈ x → i ∈ y, le_refl := fun x y => id, le_trans := fun x y z f g i => g _ ∘ f _,
    le_antisymm := fun x y f g => Part.ext$ fun z => ⟨f _, g _⟩ }

-- error in Data.Part: ././Mathport/Syntax/Translate/Basic.lean:179:15: failed to format: format: uncaught backtrack exception
instance : order_bot (part α) :=
{ bot := none, bot_le := by { introv [ident x], rintro ["⟨", "⟨", "_", "⟩", ",", "_", "⟩"] } }

instance  : Preorderₓ (Part α) :=
  by 
    infer_instance

theorem le_total_of_le_of_le {x y : Part α} (z : Part α) (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x :=
  by 
    rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
    ·
      rw [h]
      left 
      apply OrderBot.bot_le _ 
    right 
    intro b' h₁ 
    rw [Part.eq_some_iff] at h₀ 
    replace hx := hx _ h₀ 
    replace hy := hy _ h₁ 
    replace hx := Part.mem_unique hx hy 
    subst hx 
    exact h₀

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → Part α) : Part α :=
  ⟨∃ h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : Part α) (g : α → Part β) : Part β :=
  assert (dom f) fun b => g (f.get b)

/-- The map operation for `part` just maps the value and maintains the same domain. -/
@[simps]
def map (f : α → β) (o : Part α) : Part β :=
  ⟨o.dom, f ∘ o.get⟩

theorem mem_map (f : α → β) {o : Part α} : ∀ {a}, a ∈ o → f a ∈ map f o
| _, ⟨h, rfl⟩ => ⟨_, rfl⟩

@[simp]
theorem mem_map_iff (f : α → β) {o : Part α} {b} : b ∈ map f o ↔ ∃ (a : _)(_ : a ∈ o), f a = b :=
  ⟨match b with 
    | _, ⟨h, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨a, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩

@[simp]
theorem map_none (f : α → β) : map f none = none :=
  eq_none_iff.2$
    fun a =>
      by 
        simp 

@[simp]
theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
  eq_some_iff.2$ mem_map f$ mem_some _

theorem mem_assert {p : Prop} {f : p → Part α} : ∀ {a} h : p, a ∈ f h → a ∈ assert p f
| _, x, ⟨h, rfl⟩ => ⟨⟨x, h⟩, rfl⟩

@[simp]
theorem mem_assert_iff {p : Prop} {f : p → Part α} {a} : a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
  ⟨match a with 
    | _, ⟨h, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨a, h⟩ => mem_assert _ h⟩

theorem assert_pos {p : Prop} {f : p → Part α} (h : p) : assert p f = f h :=
  by 
    dsimp [assert]
    cases h' : f h 
    simp only [h', h, true_andₓ, iff_selfₓ, exists_prop_of_true, eq_iff_iff]
    apply Function.hfunext
    ·
      simp only [h, h', exists_prop_of_true]
    ·
      cc

theorem assert_neg {p : Prop} {f : p → Part α} (h : ¬p) : assert p f = none :=
  by 
    dsimp [assert, none]
    congr
    ·
      simp only [h, not_false_iff, exists_prop_of_false]
    ·
      apply Function.hfunext
      ·
        simp only [h, not_false_iff, exists_prop_of_false]
      cc

theorem mem_bind {f : Part α} {g : α → Part β} : ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
| _, _, ⟨h, rfl⟩, ⟨h₂, rfl⟩ => ⟨⟨h, h₂⟩, rfl⟩

@[simp]
theorem mem_bind_iff {f : Part α} {g : α → Part β} {b} : b ∈ f.bind g ↔ ∃ (a : _)(_ : a ∈ f), b ∈ g a :=
  ⟨match b with 
    | _, ⟨⟨h₁, h₂⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨a, h₁, h₂⟩ => mem_bind h₁ h₂⟩

@[simp]
theorem bind_none (f : α → Part β) : none.bind f = none :=
  eq_none_iff.2$
    fun a =>
      by 
        simp 

@[simp]
theorem bind_some (a : α) (f : α → Part β) : (some a).bind f = f a :=
  ext$
    by 
      simp 

theorem bind_of_mem {o : Part α} {a : α} (h : a ∈ o) (f : α → Part β) : o.bind f = f a :=
  by 
    rw [eq_some_iff.2 h, bind_some]

theorem bind_some_eq_map (f : α → β) (x : Part α) : x.bind (some ∘ f) = map f x :=
  ext$
    by 
      simp [eq_comm]

theorem bind_assoc {γ} (f : Part α) (g : α → Part β) (k : β → Part γ) :
  (f.bind g).bind k = f.bind fun x => (g x).bind k :=
  ext$
    fun a =>
      by 
        simp  <;> exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩, fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp]
theorem bind_map {γ} (f : α → β) x (g : β → Part γ) : (map f x).bind g = x.bind fun y => g (f y) :=
  by 
    rw [←bind_some_eq_map, bind_assoc] <;> simp 

@[simp]
theorem map_bind {γ} (f : α → Part β) (x : Part α) (g : β → γ) : map g (x.bind f) = x.bind fun y => map g (f y) :=
  by 
    rw [←bind_some_eq_map, bind_assoc] <;> simp [bind_some_eq_map]

theorem map_map (g : β → γ) (f : α → β) (o : Part α) : map g (map f o) = map (g ∘ f) o :=
  by 
    rw [←bind_some_eq_map, bind_map, bind_some_eq_map]

instance  : Monadₓ Part :=
  { pure := @some, map := @map, bind := @Part.bind }

instance  : IsLawfulMonad Part :=
  { bind_pure_comp_eq_map := @bind_some_eq_map,
    id_map :=
      fun β f =>
        by 
          cases f <;> rfl,
    pure_bind := @bind_some, bind_assoc := @bind_assoc }

theorem map_id' {f : α → α} (H : ∀ x : α, f x = x) o : map f o = o :=
  by 
    rw [show f = id from funext H] <;> exact id_map o

@[simp]
theorem bind_some_right (x : Part α) : x.bind some = x :=
  by 
    rw [bind_some_eq_map] <;> simp [map_id']

@[simp]
theorem pure_eq_some (a : α) : pure a = some a :=
  rfl

@[simp]
theorem ret_eq_some (a : α) : return a = some a :=
  rfl

@[simp]
theorem map_eq_map {α β} (f : α → β) (o : Part α) : f <$> o = map f o :=
  rfl

@[simp]
theorem bind_eq_bind {α β} (f : Part α) (g : α → Part β) : f >>= g = f.bind g :=
  rfl

theorem bind_le {α} (x : Part α) (f : α → Part β) (y : Part β) : x >>= f ≤ y ↔ ∀ a, a ∈ x → f a ≤ y :=
  by 
    split  <;> intro h
    ·
      intro a h' b 
      replace h := h b 
      simp only [and_imp, exists_prop, bind_eq_bind, mem_bind_iff, exists_imp_distrib] at h 
      apply h _ h'
    ·
      intro b h' 
      simp only [exists_prop, bind_eq_bind, mem_bind_iff] at h' 
      rcases h' with ⟨a, h₀, h₁⟩
      apply h _ h₀ _ h₁

instance  : MonadFail Part :=
  { Part.monad with fail := fun _ _ => none }

/-- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) (o : Part α) (H : p → o.dom) : Part α :=
  ⟨p, fun h => o.get (H h)⟩

@[simp]
theorem mem_restrict (p : Prop) (o : Part α) (h : p → o.dom) (a : α) : a ∈ restrict p o h ↔ p ∧ a ∈ o :=
  by 
    dsimp [restrict, mem_eq]
    split 
    ·
      rintro ⟨h₀, h₁⟩
      exact ⟨h₀, ⟨_, h₁⟩⟩
    rintro ⟨h₀, h₁, h₂⟩
    exact ⟨h₀, h₂⟩

/-- `unwrap o` gets the value at `o`, ignoring the condition. This function is unsound. -/
unsafe def unwrap (o : Part α) : α :=
  o.get undefined

theorem assert_defined {p : Prop} {f : p → Part α} : ∀ h : p, (f h).Dom → (assert p f).Dom :=
  Exists.introₓ

theorem bind_defined {f : Part α} {g : α → Part β} : ∀ h : f.dom, (g (f.get h)).Dom → (f.bind g).Dom :=
  assert_defined

@[simp]
theorem bind_dom {f : Part α} {g : α → Part β} : (f.bind g).Dom ↔ ∃ h : f.dom, (g (f.get h)).Dom :=
  Iff.rfl

end Part

