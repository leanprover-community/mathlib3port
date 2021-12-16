import Mathbin.Data.Part 
import Mathbin.Data.Rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → part β`.

## Definitions

* `pfun α β`: Type of partial functions from `α` to `β`. Defined as `α → part β` and denoted
  `α →. β`.
* `pfun.dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `pfun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `dom`.
* `pfun.as_subtype`: Returns a partial function as a function from its `dom`.
* `pfun.eval_opt`: Returns a partial function with a decidable `dom` as a function `a → option β`.
* `pfun.lift`: Turns a function into a partial function.
* `pfun.restrict`: Restriction of a partial function to a smaller `dom`.
* `pfun.res`: Turns a function into a partial function with a prescribed domain.
* `pfun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `pfun.fix_induction`: A recursion principle for `pfun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `rel` definitions to `pfun`:
* `pfun.image`: Preimage of a set under a partial function.
* `pfun.ran`: Range of a partial function.
* `pfun.preimage`: Preimage of a set under a partial function.
* `pfun.core`: Core of a set under a partial function.
* `pfun.graph`: Graph of a partial function `a →. β`as a `set (α × β)`.
* `pfun.graph'`: Graph of a partial function `a →. β`as a `rel α β`.

### `pfun α` as a monad

Monad operations:
* `pfun.pure`: The monad `pure` function, the constant `x` function.
* `pfun.bind`: The monad `bind` function, pointwise `part.bind`
* `pfun.map`: The monad `map` function, pointwise `part.map`.
-/


/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → part β`. -/
def Pfun (α β : Type _) :=
  α → Part β

infixr:25 " →. " => Pfun

namespace Pfun

variable {α β γ : Type _}

instance : Inhabited (α →. β) :=
  ⟨fun a => Part.none⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- The domain of a partial function -/ def dom ( f : α →. β ) : Set α := { a | f a . Dom }

theorem mem_dom (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ y, y ∈ f x :=
  by 
    simp [dom, Part.dom_iff_mem]

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem dom_eq ( f : α →. β ) : dom f = { x | ∃ y , y ∈ f x } := Set.ext mem_dom f

/-- Evaluate a partial function -/
def fn (f : α →. β) x (h : dom f x) : β :=
  (f x).get h

/-- Evaluate a partial function to return an `option` -/
def eval_opt (f : α →. β) [D : DecidablePred (· ∈ dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)

/-- Partial function extensionality -/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ dom f ↔ a ∈ dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) : f = g :=
  funext$ fun a => Part.ext' (H1 a) (H2 a)

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext$ fun a => Part.ext (H a)

/-- Turns a partial function into a function out of its domain. -/
def as_subtype (f : α →. β) (s : f.dom) : β :=
  f.fn s s.2

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equiv_subtype : (α →. β) ≃ Σ p : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, as_subtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩,
    fun f => funext$ fun a => Part.eta _,
    fun ⟨p, f⟩ =>
      by 
        dsimp <;> congr <;> funext a <;> cases a <;> rfl⟩

theorem as_subtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.dom) :
  f.as_subtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy

/-- Turn a total function into a partial function. -/
protected def lift (f : α → β) : α →. β :=
  fun a => Part.some (f a)

instance : Coe (α → β) (α →. β) :=
  ⟨Pfun.lift⟩

@[simp]
theorem lift_eq_coe (f : α → β) : Pfun.lift f = f :=
  rfl

@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
    `f`. -/
  def graph ( f : α →. β ) : Set α × β := { p | p . 2 ∈ f p . 1 }

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def graph' (f : α →. β) : Rel α β :=
  fun x y => y ∈ f x

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/--
    The range of a partial function is the set of values
      `f x` where `x` is in the domain of `f`. -/
  def ran ( f : α →. β ) : Set β := { b | ∃ a , b ∈ f a }

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.dom) : α →. β :=
  fun x => (f x).restrict (x ∈ p) (@H x)

@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.dom) (a : α) (b : β) : b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a :=
  by 
    simp [restrict]

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (Pfun.lift f).restrict s.subset_univ

theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b :=
  by 
    simp [res, @eq_comm _ b]

theorem res_univ (f : α → β) : Pfun.res f Set.Univ = f :=
  rfl

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.dom ↔ ∃ y, (x, y) ∈ f.graph :=
  Part.dom_iff_mem

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).Graph ↔ f a = b :=
  show (∃ h : True, f a = b) ↔ f a = b by 
    simp 

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β :=
  fun _ => Part.some x

/-- The monad `bind` function, pointwise `part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
  fun a => (f a).bind fun b => g b a

/-- The monad `map` function, pointwise `part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ :=
  fun a => (g a).map f

instance : Monadₓ (Pfun α) :=
  { pure := @Pfun.pure _, bind := @Pfun.bind _, map := @Pfun.map _ }

instance : IsLawfulMonad (Pfun α) :=
  { bind_pure_comp_eq_map := fun β γ f x => funext$ fun a => Part.bind_some_eq_map _ _,
    id_map :=
      fun β f =>
        by 
          funext a <;> dsimp [Functor.map, Pfun.map] <;> cases f a <;> rfl,
    pure_bind := fun β γ x f => funext$ fun a => Part.bind_some.{u_1, u_2} _ (f x),
    bind_assoc := fun β γ δ f g k => funext$ fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a }

theorem pure_defined (p : Set α) (x : β) : p ⊆ (@Pfun.pure α _ x).Dom :=
  p.subset_univ

theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.dom) (H2 : ∀ x, p ⊆ (g x).Dom) :
  p ⊆ (f >>= g).Dom :=
  fun a ha => (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. Sum β α) : α →. β :=
  fun a =>
    Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a)$
      fun h =>
        @WellFounded.fixF _ (fun x y => Sum.inr x ∈ f y) _
          (fun a IH =>
            Part.assert (f a).Dom$
              fun hf =>
                by 
                  cases' e : (f a).get hf with b a' <;> [exact Part.some b, exact IH _ ⟨hf, e⟩])
          a h

theorem dom_of_mem_fix {f : α →. Sum β α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom :=
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h 
  by 
    rw [WellFounded.fix_F_eq] at h₂ <;> exact h₂.fst.fst

theorem mem_fix_iff {f : α →. Sum β α} {a : α} {b : β} :
  b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h =>
      let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h 
      by 
        rw [WellFounded.fix_F_eq] at h₂ 
        simp  at h₂ 
        cases' h₂ with h₂ h₃ 
        cases' e : (f a).get h₂ with b' a' <;> simp [e] at h₃
        ·
          subst b' 
          refine' Or.inl ⟨h₂, e⟩
        ·
          exact Or.inr ⟨a', ⟨_, e⟩, Part.mem_assert _ h₃⟩,
    fun h =>
      by 
        simp [fix]
        rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
        ·
          refine' ⟨⟨_, fun y h' => _⟩, _⟩
          ·
            injection Part.mem_unique ⟨h₁, h₂⟩ h'
          ·
            rw [WellFounded.fix_F_eq]
            simp [h₁, h₂]
        ·
          simp [fix] at h₃ 
          cases' h₃ with h₃ h₄ 
          refine' ⟨⟨_, fun y h' => _⟩, _⟩
          ·
            injection Part.mem_unique h h' with e 
            exact e ▸ h₃
          ·
            cases' h with h₁ h₂ 
            rw [WellFounded.fix_F_eq]
            simp [h₁, h₂, h₄]⟩

/-- A recursion principle for `pfun.fix`. -/
@[elab_as_eliminator]
def fix_induction {f : α →. Sum β α} {b : β} {C : α → Sort _} {a : α} (h : b ∈ f.fix a)
  (H : ∀ a, b ∈ f.fix a → (∀ a', b ∈ f.fix a' → Sum.inr a' ∈ f a → C a') → C a) : C a :=
  by 
    replace h := Part.mem_assert_iff.1 h 
    have  := h.snd 
    revert this 
    induction' h.fst with a ha IH 
    intro h₂ 
    refine' H a (Part.mem_assert_iff.2 ⟨⟨_, ha⟩, h₂⟩) fun a' ha' fa' => _ 
    have  := (Part.mem_assert_iff.1 ha').snd 
    exact IH _ fa' ⟨ha _ fa', this⟩ this

end Pfun

namespace Pfun

variable {α β : Type _} (f : α →. β)

/-- Image of a set under a partial function. -/
def image (s : Set α) : Set β :=
  f.graph'.image s

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem image_def ( s : Set α ) : f.image s = { y | ∃ ( x : _ ) ( _ : x ∈ s ) , y ∈ f x } := rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem mem_image (y : β) (s : Set α) : y ∈ f.image s ↔ ∃ (x : _)(_ : x ∈ s), y ∈ f x :=
  Iff.rfl

theorem image_mono {s t : Set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
  Rel.image_mono _ h

theorem image_inter (s t : Set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
  Rel.image_inter _ s t

theorem image_union (s t : Set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
  Rel.image_union _ s t

/-- Preimage of a set under a partial function. -/
def preimage (s : Set β) : Set α :=
  Rel.Image (fun x y => x ∈ f y) s

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem preimage_def ( s : Set β ) : f.preimage s = { x | ∃ ( y : _ ) ( _ : y ∈ s ) , y ∈ f x } := rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.preimage s ↔ ∃ (y : _)(_ : y ∈ s), y ∈ f x :=
  Iff.rfl

theorem preimage_subset_dom (s : Set β) : f.preimage s ⊆ f.dom :=
  fun x ⟨y, ys, fxy⟩ => Part.dom_iff_mem.mpr ⟨y, fxy⟩

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
  Rel.preimage_mono _ h

theorem preimage_inter (s t : Set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
  Rel.preimage_inter _ s t

theorem preimage_union (s t : Set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
  Rel.preimage_union _ s t

theorem preimage_univ : f.preimage Set.Univ = f.dom :=
  by 
    ext <;> simp [mem_preimage, mem_dom]

/-- Core of a set `s : set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def core (s : Set β) : Set α :=
  f.graph'.core s

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem core_def ( s : Set β ) : f.core s = { x | ∀ y , y ∈ f x → y ∈ s } := rfl

theorem mem_core (x : α) (s : Set β) : x ∈ f.core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl

theorem compl_dom_subset_core (s : Set β) : f.domᶜ ⊆ f.core s :=
  fun x hx y fxy => absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

theorem core_mono {s t : Set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
  Rel.core_mono _ h

theorem core_inter (s t : Set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
  Rel.core_inter _ s t

theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) : x ∈ (res f s).Core t ↔ x ∈ s → f x ∈ t :=
  by 
    simp [mem_core, mem_res]

section 

open_locale Classical

theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).Core t = sᶜ ∪ f ⁻¹' t :=
  by 
    ext 
    rw [mem_core_res]
    byCases' h : x ∈ s <;> simp [h]

end 

theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).Core s = s.preimage f :=
  by 
    ext x <;> simp [core_def]

theorem preimage_subset_core (f : α →. β) (s : Set β) : f.preimage s ⊆ f.core s :=
  fun x ⟨y, ys, fxy⟩ y' fxy' =>
    have  : y = y' := Part.mem_unique fxy fxy' 
    this ▸ ys

theorem preimage_eq (f : α →. β) (s : Set β) : f.preimage s = f.core s ∩ f.dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
      let y := (f x).get xdom 
      have ys : y ∈ s := xcore _ (Part.get_mem _)
      show x ∈ f.preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩

theorem core_eq (f : α →. β) (s : Set β) : f.core s = f.preimage s ∪ f.domᶜ :=
  by 
    rw [preimage_eq, Set.union_distrib_right, Set.union_comm (dom f), Set.compl_union_self, Set.inter_univ,
      Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » s)
theorem preimage_as_subtype (f : α →. β) (s : Set β) : f.as_subtype ⁻¹' s = Subtype.val ⁻¹' f.preimage s :=
  by 
    ext x 
    simp only [Set.mem_preimage, Set.mem_set_of_eq, Pfun.asSubtype, Pfun.mem_preimage]
    show f.fn x.val _ ∈ s ↔ ∃ (y : _)(_ : y ∈ s), y ∈ f x.val 
    exact
      Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩)
        fun ⟨y, ys, fxy⟩ =>
          have  : f.fn x.val x.property ∈ f x.val := Part.get_mem _ 
          Part.mem_unique fxy this ▸ ys

end Pfun

