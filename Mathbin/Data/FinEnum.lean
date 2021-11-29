import Mathbin.Control.Monad.Basic 
import Mathbin.Data.Fintype.Basic 
import Mathbin.Data.List.ProdSigma

/-!
Type class for finitely enumerable types. The property is stronger
than `fintype` in that it assigns each element a rank in a finite
enumeration.
-/


universe u v

open Finset

/-- `fin_enum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `fin n` for some n. -/
class FinEnum (α : Sort _) where 
  card : ℕ 
  Equiv{} : α ≃ Finₓ card
  [decEq : DecidableEq α]

attribute [instance] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

/-- transport a `fin_enum` instance across an equivalence -/
def of_equiv α {β} [FinEnum α] (h : β ≃ α) : FinEnum β :=
  { card := card α, Equiv := h.trans (Equiv α), decEq := (h.trans (Equiv _)).DecidableEq }

/-- create a `fin_enum` instance from an exhaustive list without duplicates -/
def of_nodup_list [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) : FinEnum α :=
  { card := xs.length,
    Equiv :=
      ⟨fun x =>
          ⟨xs.index_of x,
            by 
              rw [List.index_of_lt_length] <;> apply h⟩,
        fun ⟨i, h⟩ => xs.nth_le _ h,
        fun x =>
          by 
            simp [of_nodup_list._match_1],
        fun ⟨i, h⟩ =>
          by 
            simp [of_nodup_list._match_1] <;> rw [List.nth_le_index_of] <;> apply List.nodup_erase_dup⟩ }

/-- create a `fin_enum` instance from an exhaustive list; duplicates are removed -/
def of_list [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  of_nodup_list xs.erase_dup
    (by 
      simp )
    (List.nodup_erase_dup _)

/-- create an exhaustive list of the values of a given type -/
def to_list α [FinEnum α] : List α :=
  (List.finRange (card α)).map (Equiv α).symm

open Function

@[simp]
theorem mem_to_list [FinEnum α] (x : α) : x ∈ to_list α :=
  by 
    simp [to_list] <;> exists Equiv α x <;> simp 

@[simp]
theorem nodup_to_list [FinEnum α] : List.Nodup (to_list α) :=
  by 
    simp [to_list] <;> apply List.nodup_map <;> [apply Equiv.injective, apply List.nodup_fin_range]

/-- create a `fin_enum` instance using a surjection -/
def of_surjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : surjective f) : FinEnum α :=
  of_list ((to_list β).map f)
    (by 
      intro  <;> simp  <;> exact h _)

/-- create a `fin_enum` instance using an injection -/
noncomputable def of_injective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : injective f) : FinEnum α :=
  of_list ((to_list β).filterMap (partial_inv f))
    (by 
      intro x 
      simp only [mem_to_list, true_andₓ, List.mem_filter_map]
      use f x 
      simp only [h, Function.partial_inv_left])

instance Pempty : FinEnum Pempty :=
  of_list [] fun x => Pempty.elimₓ x

instance Empty : FinEnum Empty :=
  of_list [] fun x => Empty.elimₓ x

instance PUnit : FinEnum PUnit :=
  of_list [PUnit.unit]
    fun x =>
      by 
        cases x <;> simp 

instance Prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  of_list ((to_list α).product (to_list β))
    fun x =>
      by 
        cases x <;> simp 

instance Sum {β} [FinEnum α] [FinEnum β] : FinEnum (Sum α β) :=
  of_list ((to_list α).map Sum.inl ++ (to_list β).map Sum.inr)
    fun x =>
      by 
        cases x <;> simp 

instance Finₓ {n} : FinEnum (Finₓ n) :=
  of_list (List.finRange _)
    (by 
      simp )

instance quotient.enum [FinEnum α] (s : Setoidₓ α) [DecidableRel (· ≈ · : α → α → Prop)] : FinEnum (Quotientₓ s) :=
  FinEnum.ofSurjective Quotientₓ.mk fun x => Quotientₓ.induction_on x fun x => ⟨x, rfl⟩

/-- enumerate all finite sets of a given type -/
def finset.enum [DecidableEq α] : List α → List (Finset α)
| [] => [∅]
| x :: xs =>
  do 
    let r ← finset.enum xs
    [r, {x} ∪ r]

-- error in Data.FinEnum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem finset.mem_enum
[decidable_eq α]
(s : finset α)
(xs : list α) : «expr ↔ »(«expr ∈ »(s, finset.enum xs), ∀ x «expr ∈ » s, «expr ∈ »(x, xs)) :=
begin
  induction [expr xs] [] [] ["generalizing", ident s]; simp [] [] [] ["[", "*", ",", expr finset.enum, "]"] [] [],
  { simp [] [] [] ["[", expr finset.eq_empty_iff_forall_not_mem, ",", expr («expr ∉ »), "]"] [] [],
    refl },
  { split,
    rintro ["⟨", ident a, ",", ident h, ",", ident h', "⟩", ident x, ident hx],
    cases [expr h'] [],
    { right,
      apply [expr h],
      subst [expr a],
      exact [expr hx] },
    { simp [] [] ["only"] ["[", expr h', ",", expr mem_union, ",", expr mem_singleton, "]"] [] ["at", ident hx, "⊢"],
      cases [expr hx] [],
      { exact [expr or.inl hx] },
      { exact [expr or.inr (h _ hx)] } },
    intro [ident h],
    existsi [expr «expr \ »(s, ({xs_hd} : finset α))],
    simp [] [] ["only"] ["[", expr and_imp, ",", expr union_comm, ",", expr mem_sdiff, ",", expr mem_singleton, "]"] [] [],
    simp [] [] ["only"] ["[", expr or_iff_not_imp_left, "]"] [] ["at", ident h],
    existsi [expr h],
    by_cases [expr «expr ∈ »(xs_hd, s)],
    { have [] [":", expr «expr ⊆ »({xs_hd}, s)] [],
      simp [] [] ["only"] ["[", expr has_subset.subset, ",", "*", ",", expr forall_eq, ",", expr mem_singleton, "]"] [] [],
      simp [] [] ["only"] ["[", expr union_sdiff_of_subset this, ",", expr or_true, ",", expr finset.union_sdiff_of_subset, ",", expr eq_self_iff_true, "]"] [] [] },
    { left,
      symmetry,
      simp [] [] ["only"] ["[", expr sdiff_eq_self, "]"] [] [],
      intro [ident a],
      simp [] [] ["only"] ["[", expr and_imp, ",", expr mem_inter, ",", expr mem_singleton, ",", expr not_mem_empty, "]"] [] [],
      intros [ident h₀, ident h₁],
      subst [expr a],
      apply [expr h h₀] } }
end

instance finset.fin_enum [FinEnum α] : FinEnum (Finset α) :=
  of_list (finset.enum (to_list α))
    (by 
      intro  <;> simp )

instance subtype.fin_enum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  of_list ((to_list α).filterMap$ fun x => if h : p x then some ⟨_, h⟩ else none)
    (by 
      rintro ⟨x, h⟩ <;> simp  <;> exists x <;> simp )

instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  of_list ((to_list α).bind$ fun a => (to_list (β a)).map$ Sigma.mk a)
    (by 
      intro x <;> cases x <;> simp )

instance psigma.fin_enum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)

instance psigma.fin_enum_prop_left {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
  FinEnum (Σ'a, β a) :=
  if h : α then
    of_list ((to_list (β h)).map$ Psigma.mk h)
      fun ⟨a, Ba⟩ =>
        by 
          simp 
  else of_list [] fun ⟨a, Ba⟩ => (h a).elim

instance psigma.fin_enum_prop_right {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] : FinEnum (Σ'a, β a) :=
  FinEnum.ofEquiv { a // β a } ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => rfl, fun ⟨x, y⟩ => rfl⟩

instance psigma.fin_enum_prop_prop {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
  FinEnum (Σ'a, β a) :=
  if h : ∃ a, β a then
    of_list [⟨h.fst, h.snd⟩]
      (by 
        rintro ⟨⟩ <;> simp )
  else of_list [] fun a => (h ⟨a.fst, a.snd⟩).elim

instance (priority := 100) [FinEnum α] : Fintype α :=
  { elems := univ.map (Equiv α).symm.toEmbedding,
    complete :=
      by 
        intros  <;> simp  <;> exists Equiv α x <;> simp  }

/-- For `pi.cons x xs y f` create a function where every `i ∈ xs` is mapped to `f i` and
`x` is mapped to `y`  -/
def pi.cons [DecidableEq α] (x : α) (xs : List α) (y : β x) (f : ∀ a, a ∈ xs → β a) : ∀ a, a ∈ (x :: xs : List α) → β a
| b, h =>
  if h' : b = x then
    cast
      (by 
        rw [h'])
      y
  else f b (List.mem_of_ne_of_memₓ h' h)

/-- Given `f` a function whose domain is `x :: xs`, produce a function whose domain
is restricted to `xs`.  -/
def pi.tail {x : α} {xs : List α} (f : ∀ a, a ∈ (x :: xs : List α) → β a) : ∀ a, a ∈ xs → β a
| a, h => f a (List.mem_cons_of_memₓ _ h)

/-- `pi xs f` creates the list of functions `g` such that, for `x ∈ xs`, `g x ∈ f x` -/
def pi {β : α → Type max u v} [DecidableEq α] : ∀ xs : List α, (∀ a, List (β a)) → List (∀ a, a ∈ xs → β a)
| [], fs => [fun x h => h.elim]
| x :: xs, fs => (FinEnum.Pi.cons x xs <$> fs x)<*>pi xs fs

theorem mem_pi {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] (xs : List α) (f : ∀ a, a ∈ xs → β a) :
  f ∈ pi xs fun x => to_list (β x) :=
  by 
    induction xs <;> simp' [pi, -List.map_eq_map] with monad_norm functor_norm
    ·
      ext a ⟨⟩
    ·
      exists pi.cons xs_hd xs_tl (f _ (List.mem_cons_selfₓ _ _))
      split 
      exact ⟨_, rfl⟩
      exists pi.tail f 
      split 
      ·
        apply xs_ih
      ·
        ext x h 
        simp [pi.cons]
        splitIfs 
        subst x 
        rfl 
        rfl

/-- enumerate all functions whose domain and range are finitely enumerable -/
def pi.enum (β : α → Type max u v) [FinEnum α] [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (to_list α) fun x => to_list (β x)).map fun f x => f x (mem_to_list _)

theorem pi.mem_enum {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] (f : ∀ a, β a) : f ∈ pi.enum β :=
  by 
    simp [pi.enum] <;> refine' ⟨fun a h => f a, mem_pi _ _, rfl⟩

instance pi.fin_enum {β : α → Type max u v} [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (∀ a, β a) :=
  of_list (pi.enum _) fun x => pi.mem_enum _

instance pfun_fin_enum (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, FinEnum (α hp)] : FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    of_list ((to_list (α hp)).map$ fun x hp' => x)
      (by 
        intro  <;> simp  <;> exact ⟨x hp, rfl⟩)
  else
    of_list [fun hp' => (hp hp').elim]
      (by 
        intro  <;> simp  <;> ext hp' <;> cases hp hp')

end FinEnum

