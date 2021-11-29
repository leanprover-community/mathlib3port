import Mathbin.Data.Sym.Basic 
import Mathbin.Tactic.Linarith.Default

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym.basic`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : sym2 α`, then `h.other` is the other
element of the pair, defined using `classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `sym2` is provided as `sym2.lift`, which
states that functions from `sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel` which is a special case of `sym2.lift`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/


open Finset Fintype Function Sym

universe u

variable {α : Type u}

namespace Sym2

/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : rel (x, y) (x, y)
  | swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm]
theorem rel.symm {x y : α × α} : rel α x y → rel α y x :=
  by 
    rintro ⟨_, _⟩ <;> constructor

@[trans]
theorem rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
  by 
    intro a b 
    casesM* rel _ _ _ <;>
      first |
        apply rel.refl|
        apply rel.swap

theorem rel.is_equivalence : Equivalenceₓ (rel α) :=
  by 
    tidy <;> apply rel.trans <;> assumption

instance rel.setoid (α : Type u) : Setoidₓ (α × α) :=
  ⟨rel α, rel.is_equivalence⟩

end Sym2

/--
`sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
-/
@[reducible]
def Sym2 (α : Type u) :=
  Quotientₓ (Sym2.Rel.setoid α)

namespace Sym2

@[elab_as_eliminator]
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f («expr⟦ ⟧» (x, y))) : ∀ i, f i :=
  Quotientₓ.ind$
    Prod.rec$
      by 
        exact h

@[elab_as_eliminator]
protected theorem induction_on {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f («expr⟦ ⟧» (x, y))) : f i :=
  i.ind hf

protected theorem exists {α : Sort _} {f : Sym2 α → Prop} : (∃ x : Sym2 α, f x) ↔ ∃ x y, f («expr⟦ ⟧» (x, y)) :=
  (surjective_quotient_mk _).exists.trans Prod.exists

protected theorem forall {α : Sort _} {f : Sym2 α → Prop} : (∀ x : Sym2 α, f x) ↔ ∀ x y, f («expr⟦ ⟧» (x, y)) :=
  (surjective_quotient_mk _).forall.trans Prod.forall

theorem eq_swap {a b : α} : «expr⟦ ⟧» (a, b) = «expr⟦ ⟧» (b, a) :=
  by 
    rw [Quotientₓ.eq]
    apply rel.swap

theorem congr_right {a b c : α} : «expr⟦ ⟧» (a, b) = «expr⟦ ⟧» (a, c) ↔ b = c :=
  by 
    split  <;> intro h
    ·
      rw [Quotientₓ.eq] at h 
      cases h <;> rfl 
    rw [h]

theorem congr_left {a b c : α} : «expr⟦ ⟧» (b, a) = «expr⟦ ⟧» (c, a) ↔ b = c :=
  by 
    split  <;> intro h
    ·
      rw [Quotientₓ.eq] at h 
      cases h <;> rfl 
    rw [h]

theorem eq_iff {x y z w : α} : «expr⟦ ⟧» (x, y) = «expr⟦ ⟧» (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  by 
    split  <;> intro h
    ·
      rw [Quotientₓ.eq] at h 
      cases h <;> tidy
    ·
      cases h <;> rw [h.1, h.2]
      rw [eq_swap]

/-- The universal property of `sym2`; symmetric functions of two arguments are equivalent to
functions from `sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`sym2.from_rel` instead. -/
def lift {β : Type _} : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β) :=
  { toFun :=
      fun f =>
        Quotientₓ.lift (uncurry («expr↑ » f))$
          by 
            rintro _ _ ⟨⟩
            exacts[rfl, f.prop _ _],
    invFun := fun F => ⟨curry (F ∘ Quotientₓ.mk), fun a₁ a₂ => congr_argₓ F eq_swap⟩,
    left_inv := fun f => Subtype.ext rfl,
    right_inv :=
      fun F =>
        funext$
          Sym2.ind$
            by 
              exact fun x y => rfl }

@[simp]
theorem lift_mk {β : Type _} (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a₁ a₂ : α) :
  lift f («expr⟦ ⟧» (a₁, a₂)) = (f : α → α → β) a₁ a₂ :=
  rfl

@[simp]
theorem coe_lift_symm_apply {β : Type _} (F : Sym2 α → β) (a₁ a₂ : α) :
  (lift.symm F : α → α → β) a₁ a₂ = F («expr⟦ ⟧» (a₁, a₂)) :=
  rfl

/--
The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map {α β : Type _} (f : α → β) : Sym2 α → Sym2 β :=
  Quotientₓ.map (Prod.map f f)
    (by 
      rintro _ _ h 
      cases h
      ·
        rfl 
      apply rel.swap)

@[simp]
theorem map_id : Sym2.map (@id α) = id :=
  by 
    tidy

theorem map_comp {α β γ : Type _} {g : β → γ} {f : α → β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f :=
  by 
    tidy

theorem map_map {α β γ : Type _} {g : β → γ} {f : α → β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x :=
  by 
    tidy

@[simp]
theorem map_pair_eq {α β : Type _} (f : α → β) (x y : α) : map f («expr⟦ ⟧» (x, y)) = «expr⟦ ⟧» (f x, f y) :=
  rfl

theorem map.injective {α β : Type _} {f : α → β} (hinj : injective f) : injective (map f) :=
  by 
    intro z z' 
    refine' Quotientₓ.ind₂ (fun z z' => _) z z' 
    cases' z with x y 
    cases' z' with x' y' 
    repeat' 
      rw [map_pair_eq, eq_iff]
    rintro (h | h) <;> simp [hinj h.1, hinj h.2]

section Membership

/-! ### Declarations about membership -/


/--
This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
def mem (x : α) (z : Sym2 α) : Prop :=
  ∃ y : α, z = «expr⟦ ⟧» (x, y)

instance : HasMem α (Sym2 α) :=
  ⟨mem⟩

theorem mk_has_mem (x y : α) : x ∈ «expr⟦ ⟧» (x, y) :=
  ⟨y, rfl⟩

theorem mk_has_mem_right (x y : α) : y ∈ «expr⟦ ⟧» (x, y) :=
  by 
    rw [eq_swap]
    apply mk_has_mem

/--
Given an element of the unordered pair, give the other element using `classical.some`.
See also `mem.other'` for the computable version.
-/
noncomputable def mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.some h

@[simp]
theorem mem_other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : «expr⟦ ⟧» (a, h.other) = z :=
  by 
    erw [←Classical.some_spec h]

@[simp]
theorem mem_iff {a b c : α} : a ∈ «expr⟦ ⟧» (b, c) ↔ a = b ∨ a = c :=
  { mp :=
      by 
        rintro ⟨_, h⟩
        rw [eq_iff] at h 
        tidy,
    mpr :=
      by 
        rintro ⟨_⟩ <;> subst a
        ·
          apply mk_has_mem 
        apply mk_has_mem_right }

theorem mem_other_mem {a : α} {z : Sym2 α} (h : a ∈ z) : h.other ∈ z :=
  by 
    convert mk_has_mem_right a h.other 
    rw [mem_other_spec h]

theorem elems_iff_eq {x y : α} {z : Sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = «expr⟦ ⟧» (x, y) :=
  by 
    split 
    ·
      refine' Quotientₓ.recOnSubsingleton z _ 
      rintro ⟨z₁, z₂⟩ ⟨hx, hy⟩
      rw [eq_iff]
      cases' mem_iff.mp hx with hx hx <;>
        cases' mem_iff.mp hy with hy hy <;>
          subst x <;>
            subst y <;>
              try 
                  exact (hne rfl).elim <;>
                simp only [true_orₓ, eq_self_iff_true, and_selfₓ, or_trueₓ]
    ·
      rintro rfl 
      simp 

-- error in Data.Sym.Sym2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]]
theorem sym2_ext (z z' : sym2 α) (h : ∀ x, «expr ↔ »(«expr ∈ »(x, z), «expr ∈ »(x, z'))) : «expr = »(z, z') :=
begin
  refine [expr quotient.rec_on_subsingleton z (λ w, _) h],
  refine [expr quotient.rec_on_subsingleton z' (λ w', _)],
  intro [ident h],
  cases [expr w] ["with", ident x, ident y],
  cases [expr w'] ["with", ident x', ident y'],
  simp [] [] ["only"] ["[", expr mem_iff, "]"] [] ["at", ident h],
  apply [expr eq_iff.mpr],
  have [ident hx] [] [":=", expr h x],
  have [ident hy] [] [":=", expr h y],
  have [ident hx'] [] [":=", expr h x'],
  have [ident hy'] [] [":=", expr h y'],
  simp [] [] ["only"] ["[", expr true_iff, ",", expr true_or, ",", expr eq_self_iff_true, ",", expr iff_true, ",", expr or_true, "]"] [] ["at", ident hx, ident hy, ident hx', ident hy'],
  cases [expr hx] []; subst [expr x]; cases [expr hy] []; subst [expr y]; cases [expr hx'] []; try { subst [expr x'] }; cases [expr hy'] []; try { subst [expr y'] }; simp [] [] ["only"] ["[", expr eq_self_iff_true, ",", expr and_self, ",", expr or_self, ",", expr true_or, ",", expr or_true, "]"] [] []
end

instance mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x ∈ z) :=
  Quotientₓ.recOnSubsingleton z fun ⟨y₁, y₂⟩ => decidableOfIff' _ mem_iff

end Membership

/--
A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `sym2 α`.
-/
def diag (x : α) : Sym2 α :=
  «expr⟦ ⟧» (x, x)

theorem diag_injective : Function.Injective (Sym2.diag : α → Sym2 α) :=
  fun x y h =>
    by 
      cases Quotientₓ.exact h <;> rfl

/--
A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def is_diag : Sym2 α → Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩

theorem is_diag_iff_eq {x y : α} : is_diag («expr⟦ ⟧» (x, y)) ↔ x = y :=
  Iff.rfl

@[simp]
theorem is_diag_iff_proj_eq (z : α × α) : is_diag («expr⟦ ⟧» z) ↔ z.1 = z.2 :=
  Prod.recOn z$ fun _ _ => is_diag_iff_eq

@[simp]
theorem diag_is_diag (a : α) : is_diag (diag a) :=
  Eq.refl a

theorem is_diag.mem_range_diag {z : Sym2 α} : is_diag z → z ∈ Set.Range (@diag α) :=
  by 
    induction z using Quotientₓ.induction_on 
    cases z 
    rintro (rfl : z_fst = z_snd)
    exact ⟨z_fst, rfl⟩

theorem is_diag_iff_mem_range_diag (z : Sym2 α) : is_diag z ↔ z ∈ Set.Range (@diag α) :=
  ⟨is_diag.mem_range_diag, fun ⟨i, hi⟩ => hi ▸ diag_is_diag i⟩

instance is_diag.decidable_pred (α : Type u) [DecidableEq α] : DecidablePred (@is_diag α) :=
  by 
    refine' fun z => Quotientₓ.recOnSubsingleton z fun a => _ 
    erw [is_diag_iff_proj_eq]
    infer_instance

-- error in Data.Sym.Sym2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_other_ne {a : α} {z : sym2 α} (hd : «expr¬ »(is_diag z)) (h : «expr ∈ »(a, z)) : «expr ≠ »(h.other, a) :=
begin
  intro [ident hn],
  apply [expr hd],
  have [ident h'] [] [":=", expr sym2.mem_other_spec h],
  rw [expr hn] ["at", ident h'],
  rw ["<-", expr h'] [],
  simp [] [] [] [] [] []
end

section Relations

/-! ### Declarations about symmetric relations -/


variable {r : α → α → Prop}

/--
Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def from_rel (sym : Symmetric r) : Set (Sym2 α) :=
  SetOf (lift ⟨r, fun x y => propext ⟨fun h => Sym h, fun h => Sym h⟩⟩)

@[simp]
theorem from_rel_proj_prop {sym : Symmetric r} {z : α × α} : «expr⟦ ⟧» z ∈ from_rel Sym ↔ r z.1 z.2 :=
  Iff.rfl

@[simp]
theorem from_rel_prop {sym : Symmetric r} {a b : α} : «expr⟦ ⟧» (a, b) ∈ from_rel Sym ↔ r a b :=
  Iff.rfl

theorem from_rel_irreflexive {sym : Symmetric r} : Irreflexive r ↔ ∀ {z}, z ∈ from_rel Sym → ¬is_diag z :=
  { mp :=
      fun h =>
        Sym2.ind$
          by 
            rintro a b hr (rfl : a = b)
            exact h _ hr,
    mpr := fun h x hr => h (from_rel_prop.mpr hr) rfl }

theorem mem_from_rel_irrefl_other_ne {sym : Symmetric r} (irrefl : Irreflexive r) {a : α} {z : Sym2 α}
  (hz : z ∈ from_rel Sym) (h : a ∈ z) : h.other ≠ a :=
  mem_other_ne (from_rel_irreflexive.mp irrefl hz) h

instance from_rel.decidable_pred (sym : Symmetric r) [h : DecidableRel r] : DecidablePred (· ∈ Sym2.FromRel Sym) :=
  fun z => Quotientₓ.recOnSubsingleton z fun x => h _ _

end Relations

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] Vector.Perm.isSetoid

private def from_vector {α : Type _} : Vector α 2 → α × α
| ⟨[a, b], h⟩ => (a, b)

private theorem perm_card_two_iff {α : Type _} {a₁ b₁ a₂ b₂ : α} :
  [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp :=
      by 
        simp [←Multiset.coe_eq_coe, ←Multiset.cons_coe, Multiset.cons_eq_cons] <;> tidy,
    mpr :=
      by 
        intro h 
        cases h <;> rw [h.1, h.2]
        apply List.Perm.swap' 
        rfl }

/--
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2_equiv_sym' {α : Type _} : Equiv (Sym2 α) (sym' α 2) :=
  { toFun :=
      Quotientₓ.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
        (by 
          rintro _ _ ⟨_⟩
          ·
            rfl 
          apply List.Perm.swap' 
          rfl),
    invFun :=
      Quotientₓ.map from_vector
        (by 
          rintro ⟨x, hx⟩ ⟨y, hy⟩ h 
          cases' x with _ x
          ·
            simpa using hx 
          cases' x with _ x
          ·
            simpa using hx 
          cases' x with _ x 
          swap
          ·
            exfalso 
            simp  at hx 
            linarith [hx]
          cases' y with _ y
          ·
            simpa using hy 
          cases' y with _ y
          ·
            simpa using hy 
          cases' y with _ y 
          swap
          ·
            exfalso 
            simp  at hy 
            linarith [hy]
          rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          ·
            rfl 
          apply Sym2.Rel.swap),
    left_inv :=
      by 
        tidy,
    right_inv :=
      fun x =>
        by 
          refine' Quotientₓ.recOnSubsingleton x fun x => _
          ·
            cases' x with x hx 
            cases' x with _ x
            ·
              simpa using hx 
            cases' x with _ x
            ·
              simpa using hx 
            cases' x with _ x 
            swap
            ·
              exfalso 
              simp  at hx 
              linarith [hx]
            rfl }

/--
The symmetric square is equivalent to the second symmetric power.
-/
def equiv_sym (α : Type _) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2_equiv_sym' sym_equiv_sym'.symm

/--
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equiv_multiset (α : Type _) : Sym2 α ≃ { s : Multiset α // s.card = 2 } :=
  equiv_sym α

end SymEquiv

section Decidable

/--
An algorithm for computing `sym2.rel`.
-/
def rel_bool [DecidableEq α] (x y : α × α) : Bool :=
  if x.1 = y.1 then x.2 = y.2 else if x.1 = y.2 then x.2 = y.1 else ff

theorem rel_bool_spec [DecidableEq α] (x y : α × α) : «expr↥ » (rel_bool x y) ↔ rel α x y :=
  by 
    cases' x with x₁ x₂ 
    cases' y with y₁ y₂ 
    dsimp [rel_bool]
    splitIfs <;> simp only [false_iffₓ, Bool.coe_sort_ff, Bool.of_to_bool_iff]
    rotate 2
    ·
      contrapose! h 
      cases h <;> cc 
    all_goals 
      subst x₁ 
      split  <;> intro h1
      ·
        subst h1 <;> apply Sym2.Rel.swap
      ·
        cases h1 <;> cc

/--
Given `[decidable_eq α]` and `[fintype α]`, the following instance gives `fintype (sym2 α)`.
-/
instance (α : Type _) [DecidableEq α] : DecidableRel (Sym2.Rel α) :=
  fun x y => decidableOfBool (rel_bool x y) (rel_bool_spec x y)

/--
A function that gives the other element of a pair given one of the elements.  Used in `mem.other'`.
-/
private def pair_other [DecidableEq α] (a : α) (z : α × α) : α :=
  if a = z.1 then z.2 else z.1

-- error in Data.Sym.Sym2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Get the other element of the unordered pair using the decidable equality.
This is the computable version of `mem.other`.
-/ def mem.other' [decidable_eq α] {a : α} {z : sym2 α} (h : «expr ∈ »(a, z)) : α :=
quot.rec (λ
 x
 h', pair_other a x) (begin
   clear [ident h, ident z],
   intros [ident x, ident y, ident h],
   ext [] [ident hy] [],
   convert_to [expr «expr = »(pair_other a x, _)] [],
   { have [ident h'] [":", expr ∀
      {c
       e
       h}, «expr = »(@eq.rec _ «expr⟦ ⟧»(x) (λ s, «expr ∈ »(a, s) → α) (λ _, pair_other a x) c e h, pair_other a x)] [],
     { intros ["_", ident e, "_"],
       subst [expr e] },
     apply [expr h'] },
   have [ident h'] [] [":=", expr (rel_bool_spec x y).mpr h],
   cases [expr x] ["with", ident x₁, ident x₂],
   cases [expr y] ["with", ident y₁, ident y₂],
   cases [expr mem_iff.mp hy] ["with", ident hy']; subst [expr a]; dsimp [] ["[", expr rel_bool, "]"] [] ["at", ident h']; split_ifs ["at", ident h'] []; try { rw [expr bool.of_to_bool_iff] ["at", ident h'],
     subst [expr x₁],
     subst [expr x₂] }; dsimp [] ["[", expr pair_other, "]"] [] [],
   simp [] [] ["only"] ["[", expr ne.symm h_1, ",", expr if_true, ",", expr eq_self_iff_true, ",", expr if_false, "]"] [] [],
   exfalso,
   exact [expr bool.not_ff h'],
   simp [] [] ["only"] ["[", expr h_1, ",", expr if_true, ",", expr eq_self_iff_true, ",", expr if_false, "]"] [] [],
   exfalso,
   exact [expr bool.not_ff h']
 end) z h

-- error in Data.Sym.Sym2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem mem_other_spec'
[decidable_eq α]
{a : α}
{z : sym2 α}
(h : «expr ∈ »(a, z)) : «expr = »(«expr⟦ ⟧»((a, h.other')), z) :=
begin
  induction [expr z] [] [] [],
  cases [expr z] ["with", ident x, ident y],
  have [ident h'] [] [":=", expr mem_iff.mp h],
  dsimp [] ["[", expr mem.other', ",", expr quot.rec, ",", expr pair_other, "]"] [] [],
  cases [expr h'] []; subst [expr a],
  { simp [] [] ["only"] ["[", expr if_true, ",", expr eq_self_iff_true, "]"] [] [],
    refl },
  { split_ifs [] [],
    subst [expr h_1],
    refl,
    rw [expr eq_swap] [],
    refl },
  refl
end

@[simp]
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : h.other = h.other' :=
  by 
    rw [←congr_right, mem_other_spec' h, mem_other_spec]

theorem mem_other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : h.other' ∈ z :=
  by 
    rw [←other_eq_other']
    exact mem_other_mem h

theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : ha.other' ∈ z) : hb.other' = a :=
  by 
    induction z 
    cases' z with x y 
    dsimp [mem.other', Quot.recₓ, pair_other]  at hb 
    splitIfs  at hb <;> dsimp [mem.other', Quot.recₓ, pair_other]
    simp only [h, if_true, eq_self_iff_true]
    splitIfs 
    assumption 
    rfl 
    simp only [h, if_false, if_true, eq_self_iff_true]
    exact ((mem_iff.mp ha).resolve_left h).symm 
    rfl

theorem other_invol {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : ha.other ∈ z) : hb.other = a :=
  by 
    classical 
    rw [other_eq_other'] at hb⊢
    convert other_invol' ha hb 
    rw [other_eq_other']

theorem filter_image_quotient_mk_is_diag [DecidableEq α] (s : Finset α) :
  ((s.product s).Image Quotientₓ.mk).filter is_diag = s.diag.image Quotientₓ.mk :=
  by 
    ext z 
    induction z using Quotientₓ.induction_on 
    rcases z with ⟨x, y⟩
    simp only [mem_image, mem_diag, exists_prop, mem_filter, Prod.exists, mem_product]
    split 
    ·
      rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
      rw [←h, Sym2.is_diag_iff_eq] at hab 
      exact ⟨a, b, ⟨ha, hab⟩, h⟩
    ·
      rintro ⟨a, b, ⟨ha, rfl⟩, h⟩
      rw [←h]
      exact ⟨⟨a, a, ⟨ha, ha⟩, rfl⟩, rfl⟩

theorem filter_image_quotient_mk_not_is_diag [DecidableEq α] (s : Finset α) :
  (((s.product s).Image Quotientₓ.mk).filter fun a : Sym2 α => ¬a.is_diag) = s.off_diag.image Quotientₓ.mk :=
  by 
    ext z 
    induction z using Quotientₓ.induction_on 
    rcases z with ⟨x, y⟩
    simp only [mem_image, mem_off_diag, exists_prop, mem_filter, Prod.exists, mem_product]
    split 
    ·
      rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
      rw [←h, Sym2.is_diag_iff_eq] at hab 
      exact ⟨a, b, ⟨ha, hb, hab⟩, h⟩
    ·
      rintro ⟨a, b, ⟨ha, hb, hab⟩, h⟩
      rw [Ne.def, ←Sym2.is_diag_iff_eq, h] at hab 
      exact ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩

end Decidable

end Sym2

