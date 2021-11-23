import Mathbin.Data.List.EraseDup 
import Mathbin.Data.List.Lattice 
import Mathbin.Data.List.Permutation 
import Mathbin.Data.List.Zip 
import Mathbin.Logic.Relation

/-!
# List Permutations

This file introduces the `list.perm` relation, which is true if two lists are permutations of one
another.

## Notation

The notation `~` is used for permutation equivalence.
-/


open_locale Nat

universe uu vv

namespace List

variable{α : Type uu}{β : Type vv}

/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive perm : List α → List α → Prop
  | nil : perm [] []
  | cons : ∀ x : α {l₁ l₂ : List α}, perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
  | swap : ∀ x y : α l : List α, perm (y :: x :: l) (x :: y :: l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

open perm(swap)

infixl:50 " ~ " => perm

@[refl]
protected theorem perm.refl : ∀ l : List α, l ~ l
| [] => perm.nil
| x :: xs => (perm.refl xs).cons x

@[symm]
protected theorem perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
  perm.rec_on p perm.nil (fun x l₁ l₂ p₁ r₁ => r₁.cons x) (fun x y l => swap y x l)
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => r₂.trans r₁

theorem perm_comm {l₁ l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ :=
  ⟨perm.symm, perm.symm⟩

theorem perm.swap' (x y : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  (swap _ _ _).trans ((p.cons _).cons _)

attribute [trans] perm.trans

theorem perm.eqv α : Equivalenceₓ (@perm α) :=
  mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

instance is_setoid α : Setoidₓ (List α) :=
  Setoidₓ.mk (@perm α) (perm.eqv α)

theorem perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ :=
  fun a =>
    perm.rec_on p (fun h => h)
      (fun x l₁ l₂ p₁ r₁ i =>
        Or.elim i
          (fun ax =>
            by 
              simp [ax])
          fun al₁ => Or.inr (r₁ al₁))
      (fun x y l ayxl =>
        Or.elim ayxl
          (fun ay =>
            by 
              simp [ay])
          fun axl =>
            Or.elim axl
              (fun ax =>
                by 
                  simp [ax])
              fun al => Or.inr (Or.inr al))
      fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁ => r₂ (r₁ ainl₁)

theorem perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  Iff.intro (fun m => h.subset m) fun m => h.symm.subset m

theorem perm.append_right {l₁ l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ :=
  perm.rec_on p (perm.refl ([] ++ t₁)) (fun x l₁ l₂ p₁ r₁ => r₁.cons x) (fun x y l => swap x y _)
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => r₁.trans r₂

theorem perm.append_left {t₁ t₂ : List α} : ∀ l : List α, t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂
| [], p => p
| x :: xs, p => (perm.append_left xs p).cons x

theorem perm.append {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  (p₁.append_right t₁).trans (p₂.append_left l₂)

theorem perm.append_cons (a : α) {h₁ h₂ t₁ t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) : h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ :=
  p₁.append (p₂.cons a)

@[simp]
theorem perm_middle {a : α} : ∀ {l₁ l₂ : List α}, l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂)
| [], l₂ => perm.refl _
| b :: l₁, l₂ => ((@perm_middle l₁ l₂).cons _).trans (swap a b _)

@[simp]
theorem perm_append_singleton (a : α) (l : List α) : l ++ [a] ~ a :: l :=
  perm_middle.trans$
    by 
      rw [append_nil]

theorem perm_append_comm : ∀ {l₁ l₂ : List α}, l₁ ++ l₂ ~ l₂ ++ l₁
| [], l₂ =>
  by 
    simp 
| a :: t, l₂ => (perm_append_comm.cons _).trans perm_middle.symm

theorem concat_perm (l : List α) (a : α) : concat l a ~ a :: l :=
  by 
    simp 

theorem perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ :=
  perm.rec_on p rfl
    (fun x l₁ l₂ p r =>
      by 
        simp [r])
    (fun x y l =>
      by 
        simp )
    fun l₁ l₂ l₃ p₁ p₂ r₁ r₂ => Eq.trans r₁ r₂

theorem perm.eq_nil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.length_eq

theorem perm.nil_eq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eq_nil.symm

@[simp]
theorem perm_nil {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
  ⟨fun p => p.eq_nil, fun e => e ▸ perm.refl _⟩

@[simp]
theorem nil_perm {l₁ : List α} : [] ~ l₁ ↔ l₁ = [] :=
  perm_comm.trans perm_nil

theorem not_perm_nil_cons (x : α) (l : List α) : ¬[] ~ x :: l
| p =>
  by 
    injection p.symm.eq_nil

@[simp]
theorem reverse_perm : ∀ l : List α, reverse l ~ l
| [] => perm.nil
| a :: l =>
  by 
    rw [reverse_cons]
    exact (perm_append_singleton _ _).trans ((reverse_perm l).cons a)

theorem perm_cons_append_cons {l l₁ l₂ : List α} (a : α) (p : l ~ l₁ ++ l₂) : a :: l ~ l₁ ++ a :: l₂ :=
  (p.cons a).trans perm_middle.symm

@[simp]
theorem perm_repeat {a : α} {n : ℕ} {l : List α} : l ~ repeat a n ↔ l = repeat a n :=
  ⟨fun p => eq_repeat.2 ⟨p.length_eq.trans$ length_repeat _ _, fun b m => eq_of_mem_repeat$ p.subset m⟩,
    fun h => h ▸ perm.refl _⟩

@[simp]
theorem repeat_perm {a : α} {n : ℕ} {l : List α} : repeat a n ~ l ↔ repeat a n = l :=
  (perm_comm.trans perm_repeat).trans eq_comm

@[simp]
theorem perm_singleton {a : α} {l : List α} : l ~ [a] ↔ l = [a] :=
  @perm_repeat α a 1 l

@[simp]
theorem singleton_perm {a : α} {l : List α} : [a] ~ l ↔ [a] = l :=
  @repeat_perm α a 1 l

theorem perm.eq_singleton {a : α} {l : List α} (p : l ~ [a]) : l = [a] :=
  perm_singleton.1 p

theorem perm.singleton_eq {a : α} {l : List α} (p : [a] ~ l) : [a] = l :=
  p.symm.eq_singleton.symm

theorem singleton_perm_singleton {a b : α} : [a] ~ [b] ↔ a = b :=
  by 
    simp 

theorem perm_cons_erase [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: l.erase a :=
  let ⟨l₁, l₂, _, e₁, e₂⟩ := exists_erase_eq h 
  e₂.symm ▸ e₁.symm ▸ perm_middle

@[elab_as_eliminator]
theorem perm_induction_on {P : List α → List α → Prop} {l₁ l₂ : List α} (p : l₁ ~ l₂) (h₁ : P [] [])
  (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x :: l₁) (x :: l₂))
  (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y :: x :: l₁) (x :: y :: l₂))
  (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) : P l₁ l₂ :=
  have P_refl : ∀ l, P l l := fun l => List.recOn l h₁ fun x xs ih => h₂ x xs xs (perm.refl xs) ih 
  perm.rec_on p h₁ h₂ (fun x y l => h₃ x y l l (perm.refl l) (P_refl l)) h₄

@[congr]
theorem perm.filter_map (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : filter_map f l₁ ~ filter_map f l₂ :=
  by 
    induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      simp only [filter_map]
      cases' f x with a <;> simp [filter_map, IH, perm.cons]
    ·
      simp only [filter_map]
      cases' f x with a <;> cases' f y with b <;> simp [filter_map, swap]
    ·
      exact IH₁.trans IH₂

@[congr]
theorem perm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filter_map_eq_map f ▸ p.filter_map _

theorem perm.pmap {p : α → Prop} (f : ∀ a, p a → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) {H₁ H₂} :
  pmap f l₁ H₁ ~ pmap f l₂ H₂ :=
  by 
    induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      simp [IH, perm.cons]
    ·
      simp [swap]
    ·
      refine' IH₁.trans IH₂ 
      exact fun a m => H₂ a (p₂.subset m)

theorem perm.filter (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} (s : l₁ ~ l₂) : filter p l₁ ~ filter p l₂ :=
  by 
    rw [←filter_map_eq_filter] <;> apply s.filter_map _

theorem exists_perm_sublist {l₁ l₂ l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') :
  ∃ (l₁' : _)(_ : l₁' ~ l₁), l₁' <+ l₂' :=
  by 
    induction' p with x l₂ l₂' p IH x y l₂ l₂ m₂ r₂ p₁ p₂ IH₁ IH₂ generalizing l₁ s
    ·
      exact ⟨[], eq_nil_of_sublist_nil s ▸ perm.refl _, nil_sublist _⟩
    ·
      cases' s with _ _ _ s l₁ _ _ s
      ·
        exact
          let ⟨l₁', p', s'⟩ := IH s
          ⟨l₁', p', s'.cons _ _ _⟩
      ·
        exact
          let ⟨l₁', p', s'⟩ := IH s
          ⟨x :: l₁', p'.cons x, s'.cons2 _ _ _⟩
    ·
      cases' s with _ _ _ s l₁ _ _ s <;> cases' s with _ _ _ s l₁ _ _ s
      ·
        exact ⟨l₁, perm.refl _, (s.cons _ _ _).cons _ _ _⟩
      ·
        exact ⟨x :: l₁, perm.refl _, (s.cons _ _ _).cons2 _ _ _⟩
      ·
        exact ⟨y :: l₁, perm.refl _, (s.cons2 _ _ _).cons _ _ _⟩
      ·
        exact ⟨x :: y :: l₁, perm.swap _ _ _, (s.cons2 _ _ _).cons2 _ _ _⟩
    ·
      exact
        let ⟨m₁, pm, sm⟩ := IH₁ s 
        let ⟨r₁, pr, sr⟩ := IH₂ sm
        ⟨r₁, pr.trans pm, sr⟩

theorem perm.sizeof_eq_sizeof [SizeOf α] {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.sizeof = l₂.sizeof :=
  by 
    induction' h with hd l₁ l₂ h₁₂ h_sz₁₂ a b l l₁ l₂ l₃ h₁₂ h₂₃ h_sz₁₂ h_sz₂₃
    ·
      rfl
    ·
      simp only [List.sizeof, h_sz₁₂]
    ·
      simp only [List.sizeof, add_left_commₓ]
    ·
      simp only [h_sz₁₂, h_sz₂₃]

section Rel

open Relator

variable{γ : Type _}{δ : Type _}{r : α → β → Prop}{p : γ → δ → Prop}

local infixr:80 " ∘r " => Relation.Comp

theorem perm_comp_perm : (perm ∘r perm : List α → List α → Prop) = perm :=
  by 
    funext a c 
    apply propext 
    split 
    ·
      exact fun ⟨b, hab, hba⟩ => perm.trans hab hba
    ·
      exact fun h => ⟨a, perm.refl a, h⟩

theorem perm_comp_forall₂ {l u v} (hlu : perm l u) (huv : forall₂ r u v) : (forall₂ r ∘r perm) l v :=
  by 
    induction hlu generalizing v 
    case perm.nil => 
      cases huv 
      exact ⟨[], forall₂.nil, perm.nil⟩
    case perm.cons a l u hlu ih => 
      cases' huv with _ b _ v hab huv' 
      rcases ih huv' with ⟨l₂, h₁₂, h₂₃⟩
      exact ⟨b :: l₂, forall₂.cons hab h₁₂, h₂₃.cons _⟩
    case perm.swap a₁ a₂ l₁ l₂ h₂₃ => 
      cases' h₂₃ with _ b₁ _ l₂ h₁ hr_₂₃ 
      cases' hr_₂₃ with _ b₂ _ l₂ h₂ h₁₂ 
      exact ⟨b₂ :: b₁ :: l₂, forall₂.cons h₂ (forall₂.cons h₁ h₁₂), perm.swap _ _ _⟩
    case perm.trans la₁ la₂ la₃ _ _ ih₁ ih₂ => 
      rcases ih₂ huv with ⟨lb₂, hab₂, h₂₃⟩
      rcases ih₁ hab₂ with ⟨lb₁, hab₁, h₁₂⟩
      exact ⟨lb₁, hab₁, perm.trans h₁₂ h₂₃⟩

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem forall₂_comp_perm_eq_perm_comp_forall₂ : «expr = »(«expr ∘r »(forall₂ r, perm), «expr ∘r »(perm, forall₂ r)) :=
begin
  funext [ident l₁, ident l₃],
  apply [expr propext],
  split,
  { assume [binders (h)],
    rcases [expr h, "with", "⟨", ident l₂, ",", ident h₁₂, ",", ident h₂₃, "⟩"],
    have [] [":", expr forall₂ (flip r) l₂ l₁] [],
    from [expr h₁₂.flip],
    rcases [expr perm_comp_forall₂ h₂₃.symm this, "with", "⟨", ident l', ",", ident h₁, ",", ident h₂, "⟩"],
    exact [expr ⟨l', h₂.symm, h₁.flip⟩] },
  { exact [expr assume ⟨l₂, h₁₂, h₂₃⟩, perm_comp_forall₂ h₁₂ h₂₃] }
end

theorem rel_perm_imp (hr : right_unique r) : (forall₂ r⇒forall₂ r⇒Implies) perm perm :=
  fun a b h₁ c d h₂ h =>
    have  : (flip (forall₂ r) ∘r perm ∘r forall₂ r) b d := ⟨a, h₁, c, h, h₂⟩
    have  : ((flip (forall₂ r) ∘r forall₂ r) ∘r perm) b d :=
      by 
        rwa [←forall₂_comp_perm_eq_perm_comp_forall₂, ←Relation.comp_assoc] at this 
    let ⟨b', ⟨c', hbc, hcb⟩, hbd⟩ := this 
    have  : b' = b := right_unique_forall₂' hr hcb hbc 
    this ▸ hbd

theorem rel_perm (hr : bi_unique r) : (forall₂ r⇒forall₂ r⇒(· ↔ ·)) perm perm :=
  fun a b hab c d hcd => Iff.intro (rel_perm_imp hr.2 hab hcd) (rel_perm_imp hr.left.flip hab.flip hcd.flip)

end Rel

section Subperm

/-- `subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def subperm (l₁ l₂ : List α) : Prop :=
  ∃ (l : _)(_ : l ~ l₁), l <+ l₂

infixl:50 " <+~ " => subperm

theorem nil_subperm {l : List α} : [] <+~ l :=
  ⟨[], perm.nil,
    by 
      simp ⟩

theorem perm.subperm_left {l l₁ l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ :=
  suffices ∀ {l₁ l₂ : List α}, l₁ ~ l₂ → l <+~ l₁ → l <+~ l₂ from ⟨this p, this p.symm⟩
  fun l₁ l₂ p ⟨u, pu, su⟩ =>
    let ⟨v, pv, sv⟩ := exists_perm_sublist su p
    ⟨v, pv.trans pu, sv⟩

theorem perm.subperm_right {l₁ l₂ l : List α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l :=
  ⟨fun ⟨u, pu, su⟩ => ⟨u, pu.trans p, su⟩, fun ⟨u, pu, su⟩ => ⟨u, pu.trans p.symm, su⟩⟩

theorem sublist.subperm {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
  ⟨l₁, perm.refl _, s⟩

theorem perm.subperm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
  ⟨l₂, p.symm, sublist.refl _⟩

@[refl]
theorem subperm.refl (l : List α) : l <+~ l :=
  (perm.refl _).Subperm

@[trans]
theorem subperm.trans {l₁ l₂ l₃ : List α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃
| s, ⟨l₂', p₂, s₂⟩ =>
  let ⟨l₁', p₁, s₁⟩ := p₂.subperm_left.2 s
  ⟨l₁', p₁, s₁.trans s₂⟩

theorem subperm.length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₁ ≤ length l₂
| ⟨l, p, s⟩ => p.length_eq ▸ length_le_of_sublist s

theorem subperm.perm_of_length_le {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂
| ⟨l, p, s⟩, h =>
  suffices l = l₂ from this ▸ p.symm 
  eq_of_sublist_of_length_le s$ p.symm.length_eq ▸ h

theorem subperm.antisymm {l₁ l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
  h₁.perm_of_length_le h₂.length_le

theorem subperm.subset {l₁ l₂ : List α} : l₁ <+~ l₂ → l₁ ⊆ l₂
| ⟨l, p, s⟩ => subset.trans p.symm.subset s.subset

theorem subperm.filter (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l <+~ l') : filter p l <+~ filter p l' :=
  by 
    obtain ⟨xs, hp, h⟩ := h 
    exact ⟨_, hp.filter p, h.filter p⟩

end Subperm

theorem sublist.exists_perm_append : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → ∃ l, l₂ ~ l₁ ++ l
| _, _, sublist.slnil => ⟨nil, perm.refl _⟩
| _, _, sublist.cons l₁ l₂ a s =>
  let ⟨l, p⟩ := sublist.exists_perm_append s
  ⟨a :: l, (p.cons a).trans perm_middle.symm⟩
| _, _, sublist.cons2 l₁ l₂ a s =>
  let ⟨l, p⟩ := sublist.exists_perm_append s
  ⟨l, p.cons a⟩

theorem perm.countp_eq (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} (s : l₁ ~ l₂) : countp p l₁ = countp p l₂ :=
  by 
    rw [countp_eq_length_filter, countp_eq_length_filter] <;> exact (s.filter _).length_eq

theorem subperm.countp_le (p : α → Prop) [DecidablePred p] {l₁ l₂ : List α} : l₁ <+~ l₂ → countp p l₁ ≤ countp p l₂
| ⟨l, p', s⟩ => p'.countp_eq p ▸ s.countp_le p

theorem perm.count_eq [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) a : count a l₁ = count a l₂ :=
  p.countp_eq _

theorem subperm.count_le [DecidableEq α] {l₁ l₂ : List α} (s : l₁ <+~ l₂) a : count a l₁ ≤ count a l₂ :=
  s.countp_le _

theorem perm.foldl_eq' {f : β → α → β} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
  (∀ x _ : x ∈ l₁ y _ : y ∈ l₁ z, f (f z x) y = f (f z y) x) → ∀ b, foldl f b l₁ = foldl f b l₂ :=
  perm_induction_on p (fun H b => rfl) (fun x t₁ t₂ p r H b => r (fun x hx y hy => H _ (Or.inr hx) _ (Or.inr hy)) _)
    (fun x y t₁ t₂ p r H b =>
      by 
        simp only [foldl]
        rw [H x (Or.inr$ Or.inl rfl) y (Or.inl rfl)]
        exact r (fun x hx y hy => H _ (Or.inr$ Or.inr hx) _ (Or.inr$ Or.inr hy)) _)
    fun t₁ t₂ t₃ p₁ p₂ r₁ r₂ H b =>
      Eq.trans (r₁ H b) (r₂ (fun x hx y hy => H _ (p₁.symm.subset hx) _ (p₁.symm.subset hy)) b)

theorem perm.foldl_eq {f : β → α → β} {l₁ l₂ : List α} (rcomm : RightCommutative f) (p : l₁ ~ l₂) :
  ∀ b, foldl f b l₁ = foldl f b l₂ :=
  p.foldl_eq'$ fun x hx y hy z => rcomm z x y

theorem perm.foldr_eq {f : α → β → β} {l₁ l₂ : List α} (lcomm : LeftCommutative f) (p : l₁ ~ l₂) :
  ∀ b, foldr f b l₁ = foldr f b l₂ :=
  perm_induction_on p (fun b => rfl)
    (fun x t₁ t₂ p r b =>
      by 
        simp  <;> rw [r b])
    (fun x y t₁ t₂ p r b =>
      by 
        simp  <;> rw [lcomm, r b])
    fun t₁ t₂ t₃ p₁ p₂ r₁ r₂ a => Eq.trans (r₁ a) (r₂ a)

theorem perm.rec_heq {β : List α → Sort _} {f : ∀ a l, β l → β (a :: l)} {b : β []} {l l' : List α} (hl : perm l l')
  (f_congr : ∀ {a l l' b b'}, perm l l' → HEq b b' → HEq (f a l b) (f a l' b'))
  (f_swap : ∀ {a a' l b}, HEq (f a (a' :: l) (f a' l b)) (f a' (a :: l) (f a l b))) :
  HEq (@List.rec α β b f l) (@List.rec α β b f l') :=
  by 
    induction hl 
    case list.perm.nil => 
      rfl 
    case list.perm.cons a l l' h ih => 
      exact f_congr h ih 
    case list.perm.swap a a' l => 
      exact f_swap 
    case list.perm.trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ => 
      exact HEq.trans ih₁ ih₂

section 

variable{op : α → α → α}[IsAssociative α op][IsCommutative α op]

local notation a "*" b => op a b

local notation l "<*>" a => foldl op a l

theorem perm.fold_op_eq {l₁ l₂ : List α} {a : α} (h : l₁ ~ l₂) : (l₁<*>a) = l₂<*>a :=
  h.foldl_eq (right_comm _ IsCommutative.comm IsAssociative.assoc) _

end 

section CommMonoidₓ

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements-/
@[toAdditive]
theorem perm.prod_eq' [Monoidₓ α] {l₁ l₂ : List α} (h : l₁ ~ l₂) (hc : l₁.pairwise fun x y => (x*y) = y*x) :
  l₁.prod = l₂.prod :=
  h.foldl_eq'
    ((forall_of_forall_of_pairwise (fun x y h z => (h z).symm) fun x hx z => rfl)$
      hc.imp$
        fun x y h z =>
          by 
            simp only [mul_assocₓ, h])
    _

variable[CommMonoidₓ α]

@[toAdditive]
theorem perm.prod_eq {l₁ l₂ : List α} (h : perm l₁ l₂) : Prod l₁ = Prod l₂ :=
  h.fold_op_eq

@[toAdditive]
theorem prod_reverse (l : List α) : Prod l.reverse = Prod l :=
  (reverse_perm l).prod_eq

end CommMonoidₓ

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_inv_core
{a : α}
{l₁
 l₂
 r₁
 r₂ : list α} : «expr ~ »(«expr ++ »(l₁, «expr :: »(a, r₁)), «expr ++ »(l₂, «expr :: »(a, r₂))) → «expr ~ »(«expr ++ »(l₁, r₁), «expr ++ »(l₂, r₂)) :=
begin
  generalize [ident e₁] [":"] [expr «expr = »(«expr ++ »(l₁, «expr :: »(a, r₁)), s₁)],
  generalize [ident e₂] [":"] [expr «expr = »(«expr ++ »(l₂, «expr :: »(a, r₂)), s₂)],
  intro [ident p],
  revert [ident l₁, ident l₂, ident r₁, ident r₂, ident e₁, ident e₂],
  refine [expr perm_induction_on p _ (λ
    x
    t₁
    t₂
    p
    IH, _) (λ
    x
    y
    t₁
    t₂
    p
    IH, _) (λ t₁ t₂ t₃ p₁ p₂ IH₁ IH₂, _)]; intros [ident l₁, ident l₂, ident r₁, ident r₂, ident e₁, ident e₂],
  { apply [expr (not_mem_nil a).elim],
    rw ["<-", expr e₁] [],
    simp [] [] [] [] [] [] },
  { cases [expr l₁] ["with", ident y, ident l₁]; cases [expr l₂] ["with", ident z, ident l₂]; dsimp [] [] [] ["at", ident e₁, ident e₂]; injections []; subst [expr x],
    { substs [ident t₁, ident t₂],
      exact [expr p] },
    { substs [ident z, ident t₁, ident t₂],
      exact [expr p.trans perm_middle] },
    { substs [ident y, ident t₁, ident t₂],
      exact [expr perm_middle.symm.trans p] },
    { substs [ident z, ident t₁, ident t₂],
      exact [expr (IH rfl rfl).cons y] } },
  { rcases [expr l₁, "with", "_", "|", "⟨", ident y, ",", "_", "|", "⟨", ident z, ",", ident l₁, "⟩", "⟩"]; rcases [expr l₂, "with", "_", "|", "⟨", ident u, ",", "_", "|", "⟨", ident v, ",", ident l₂, "⟩", "⟩"]; dsimp [] [] [] ["at", ident e₁, ident e₂]; injections []; substs [ident x, ident y],
    { substs [ident r₁, ident r₂],
      exact [expr p.cons a] },
    { substs [ident r₁, ident r₂],
      exact [expr p.cons u] },
    { substs [ident r₁, ident v, ident t₂],
      exact [expr (p.trans perm_middle).cons u] },
    { substs [ident r₁, ident r₂],
      exact [expr p.cons y] },
    { substs [ident r₁, ident r₂, ident y, ident u],
      exact [expr p.cons a] },
    { substs [ident r₁, ident u, ident v, ident t₂],
      exact [expr ((p.trans perm_middle).cons y).trans (swap _ _ _)] },
    { substs [ident r₂, ident z, ident t₁],
      exact [expr (perm_middle.symm.trans p).cons y] },
    { substs [ident r₂, ident y, ident z, ident t₁],
      exact [expr (swap _ _ _).trans ((perm_middle.symm.trans p).cons u)] },
    { substs [ident u, ident v, ident t₁, ident t₂],
      exact [expr (IH rfl rfl).swap' _ _] } },
  { substs [ident t₁, ident t₃],
    have [] [":", expr «expr ∈ »(a, t₂)] [":=", expr p₁.subset (by simp [] [] [] [] [] [])],
    rcases [expr mem_split this, "with", "⟨", ident l₂, ",", ident r₂, ",", ident e₂, "⟩"],
    subst [expr t₂],
    exact [expr (IH₁ rfl rfl).trans (IH₂ rfl rfl)] }
end

theorem perm.cons_inv {a : α} {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  @perm_inv_core _ _ [] [] _ _

@[simp]
theorem perm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ ~ a :: l₂ ↔ l₁ ~ l₂ :=
  ⟨perm.cons_inv, perm.cons a⟩

theorem perm_append_left_iff {l₁ l₂ : List α} : ∀ l, l ++ l₁ ~ l ++ l₂ ↔ l₁ ~ l₂
| [] => Iff.rfl
| a :: l => (perm_cons a).trans (perm_append_left_iff l)

theorem perm_append_right_iff {l₁ l₂ : List α} l : l₁ ++ l ~ l₂ ++ l ↔ l₁ ~ l₂ :=
  ⟨fun p => (perm_append_left_iff _).1$ perm_append_comm.trans$ p.trans perm_append_comm, perm.append_right _⟩

theorem perm_option_to_list {o₁ o₂ : Option α} : o₁.to_list ~ o₂.to_list ↔ o₁ = o₂ :=
  by 
    refine' ⟨fun p => _, fun e => e ▸ perm.refl _⟩
    cases' o₁ with a <;> cases' o₂ with b
    ·
      rfl
    ·
      cases p.length_eq
    ·
      cases p.length_eq
    ·
      exact
        Option.mem_to_list.1
          (p.symm.subset$
            by 
              simp )

theorem subperm_cons (a : α) {l₁ l₂ : List α} : a :: l₁ <+~ a :: l₂ ↔ l₁ <+~ l₂ :=
  ⟨fun ⟨l, p, s⟩ =>
      by 
        cases' s with _ _ _ s' u _ _ s'
        ·
          exact (p.subperm_left.2$ (sublist_cons _ _).Subperm).trans s'.subperm
        ·
          exact ⟨u, p.cons_inv, s'⟩,
    fun ⟨l, p, s⟩ => ⟨a :: l, p.cons a, s.cons2 _ _ _⟩⟩

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cons_subperm_of_mem
{a : α}
{l₁ l₂ : list α}
(d₁ : nodup l₁)
(h₁ : «expr ∉ »(a, l₁))
(h₂ : «expr ∈ »(a, l₂))
(s : «expr <+~ »(l₁, l₂)) : «expr <+~ »(«expr :: »(a, l₁), l₂) :=
begin
  rcases [expr s, "with", "⟨", ident l, ",", ident p, ",", ident s, "⟩"],
  induction [expr s] [] [] ["generalizing", ident l₁],
  case [ident list.sublist.slnil] { cases [expr h₂] [] },
  case [ident list.sublist.cons, ":", ident r₁, ident r₂, ident b, ident s', ident ih] { simp [] [] [] [] [] ["at", ident h₂],
    cases [expr h₂] ["with", ident e, ident m],
    { subst [expr b],
      exact [expr ⟨«expr :: »(a, r₁), p.cons a, s'.cons2 _ _ _⟩] },
    { rcases [expr ih m d₁ h₁ p, "with", "⟨", ident t, ",", ident p', ",", ident s', "⟩"],
      exact [expr ⟨t, p', s'.cons _ _ _⟩] } },
  case [ident list.sublist.cons2, ":", ident r₁, ident r₂, ident b, ident s', ident ih] { have [ident bm] [":", expr «expr ∈ »(b, l₁)] [":=", expr «expr $ »(p.subset, mem_cons_self _ _)],
    have [ident am] [":", expr «expr ∈ »(a, r₂)] [":=", expr h₂.resolve_left (λ
      e, «expr $ »(h₁, «expr ▸ »(e.symm, bm)))],
    rcases [expr mem_split bm, "with", "⟨", ident t₁, ",", ident t₂, ",", ident rfl, "⟩"],
    have [ident st] [":", expr «expr <+ »(«expr ++ »(t₁, t₂), «expr ++ »(t₁, «expr :: »(b, t₂)))] [":=", expr by simp [] [] [] [] [] []],
    rcases [expr ih am (nodup_of_sublist st d₁) (mt (λ
       x, st.subset x) h₁) «expr $ »(perm.cons_inv, p.trans perm_middle), "with", "⟨", ident t, ",", ident p', ",", ident s', "⟩"],
    exact [expr ⟨«expr :: »(b, t), «expr $ »((p'.cons b).trans, (swap _ _ _).trans (perm_middle.symm.cons a)), s'.cons2 _ _ _⟩] }
end

theorem subperm_append_left {l₁ l₂ : List α} : ∀ l, l ++ l₁ <+~ l ++ l₂ ↔ l₁ <+~ l₂
| [] => Iff.rfl
| a :: l => (subperm_cons a).trans (subperm_append_left l)

theorem subperm_append_right {l₁ l₂ : List α} l : l₁ ++ l <+~ l₂ ++ l ↔ l₁ <+~ l₂ :=
  (perm_append_comm.subperm_left.trans perm_append_comm.subperm_right).trans (subperm_append_left l)

theorem subperm.exists_of_length_lt {l₁ l₂ : List α} : l₁ <+~ l₂ → length l₁ < length l₂ → ∃ a, a :: l₁ <+~ l₂
| ⟨l, p, s⟩, h =>
  suffices length l < length l₂ → ∃ a : α, a :: l <+~ l₂ from
    (this$ p.symm.length_eq ▸ h).imp fun a => (p.cons a).subperm_right.1
  by 
    clear subperm.exists_of_length_lt p h l₁ 
    rename' l₂ => u 
    induction' s with l₁ l₂ a s IH _ _ b s IH <;> intro h
    ·
      cases h
    ·
      cases' lt_or_eq_of_leₓ (Nat.le_of_lt_succₓ h : length l₁ ≤ length l₂) with h h
      ·
        exact (IH h).imp fun a s => s.trans (sublist_cons _ _).Subperm
      ·
        exact ⟨a, eq_of_sublist_of_length_eq s h ▸ subperm.refl _⟩
    ·
      exact (IH$ Nat.lt_of_succ_lt_succₓ h).imp fun a s => (swap _ _ _).subperm_right.1$ (subperm_cons _).2 s

theorem subperm_of_subset_nodup {l₁ l₂ : List α} (d : nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ :=
  by 
    induction' d with a l₁' h d IH
    ·
      exact ⟨nil, perm.nil, nil_sublist _⟩
    ·
      cases' forall_mem_cons.1 H with H₁ H₂ 
      simp  at h 
      exact cons_subperm_of_mem d h H₁ (IH H₂)

theorem perm_ext {l₁ l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) : l₁ ~ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ :=
  ⟨fun p a => p.mem_iff,
    fun H =>
      subperm.antisymm (subperm_of_subset_nodup d₁ fun a => (H a).1) (subperm_of_subset_nodup d₂ fun a => (H a).2)⟩

theorem nodup.sublist_ext {l₁ l₂ l : List α} (d : nodup l) (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) : l₁ ~ l₂ ↔ l₁ = l₂ :=
  ⟨fun h =>
      by 
        induction' s₂ with l₂ l a s₂ IH l₂ l a s₂ IH generalizing l₁
        ·
          exact h.eq_nil
        ·
          simp  at d 
          cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
          ·
            exact IH d.2 s₁ h
          ·
            apply d.1.elim 
            exact subperm.subset ⟨_, h.symm, s₂⟩ (mem_cons_self _ _)
        ·
          simp  at d 
          cases' s₁ with _ _ _ s₁ l₁ _ _ s₁
          ·
            apply d.1.elim 
            exact subperm.subset ⟨_, h, s₁⟩ (mem_cons_self _ _)
          ·
            rw [IH d.2 s₁ h.cons_inv],
    fun h =>
      by 
        rw [h]⟩

section 

variable[DecidableEq α]

theorem perm.erase (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁.erase a ~ l₂.erase a :=
  if h₁ : a ∈ l₁ then
    have h₂ : a ∈ l₂ := p.subset h₁ 
    perm.cons_inv$ (perm_cons_erase h₁).symm.trans$ p.trans (perm_cons_erase h₂)
  else
    have h₂ : a ∉ l₂ := mt p.mem_iff.2 h₁ 
    by 
      rw [erase_of_not_mem h₁, erase_of_not_mem h₂] <;> exact p

theorem subperm_cons_erase (a : α) (l : List α) : l <+~ a :: l.erase a :=
  by 
    byCases' h : a ∈ l
    ·
      exact (perm_cons_erase h).Subperm
    ·
      rw [erase_of_not_mem h]
      exact (sublist_cons _ _).Subperm

theorem erase_subperm (a : α) (l : List α) : l.erase a <+~ l :=
  (erase_sublist _ _).Subperm

theorem subperm.erase {l₁ l₂ : List α} (a : α) (h : l₁ <+~ l₂) : l₁.erase a <+~ l₂.erase a :=
  let ⟨l, hp, hs⟩ := h
  ⟨l.erase a, hp.erase _, hs.erase _⟩

theorem perm.diff_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) : l₁.diff t ~ l₂.diff t :=
  by 
    induction t generalizing l₁ l₂ h <;> simp [perm.erase]

theorem perm.diff_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l.diff t₁ = l.diff t₂ :=
  by 
    induction h generalizing l <;>
      first |
        simp [perm.erase, erase_comm]|
        exact (ih_1 _).trans (ih_2 _)

theorem perm.diff {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : l₁.diff t₁ ~ l₂.diff t₂ :=
  ht.diff_left l₂ ▸ hl.diff_right _

theorem subperm.diff_right {l₁ l₂ : List α} (h : l₁ <+~ l₂) (t : List α) : l₁.diff t <+~ l₂.diff t :=
  by 
    induction t generalizing l₁ l₂ h <;> simp [subperm.erase]

theorem erase_cons_subperm_cons_erase (a b : α) (l : List α) : (a :: l).erase b <+~ a :: l.erase b :=
  by 
    byCases' h : a = b
    ·
      subst b 
      rw [erase_cons_head]
      apply subperm_cons_erase
    ·
      rw [erase_cons_tail _ h]

theorem subperm_cons_diff {a : α} : ∀ {l₁ l₂ : List α}, (a :: l₁).diff l₂ <+~ a :: l₁.diff l₂
| l₁, [] =>
  ⟨a :: l₁,
    by 
      simp ⟩
| l₁, b :: l₂ =>
  by 
    simp only [diff_cons]
    refine' ((erase_cons_subperm_cons_erase a b l₁).diff_right l₂).trans _ 
    apply subperm_cons_diff

theorem subset_cons_diff {a : α} {l₁ l₂ : List α} : (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ :=
  subperm_cons_diff.Subset

theorem perm.bag_inter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) : l₁.bag_inter t ~ l₂.bag_inter t :=
  by 
    induction' h with x _ _ _ _ x y _ _ _ _ _ _ ih_1 ih_2 generalizing t
    ·
      simp 
    ·
      byCases' x ∈ t <;> simp [perm.cons]
    ·
      byCases' x = y
      ·
        simp [h]
      byCases' xt : x ∈ t <;> byCases' yt : y ∈ t
      ·
        simp [xt, yt, mem_erase_of_ne h, mem_erase_of_ne (Ne.symm h), erase_comm, swap]
      ·
        simp [xt, yt, mt mem_of_mem_erase, perm.cons]
      ·
        simp [xt, yt, mt mem_of_mem_erase, perm.cons]
      ·
        simp [xt, yt]
    ·
      exact (ih_1 _).trans (ih_2 _)

theorem perm.bag_inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) : l.bag_inter t₁ = l.bag_inter t₂ :=
  by 
    induction' l with a l IH generalizing t₁ t₂ p
    ·
      simp 
    byCases' a ∈ t₁
    ·
      simp [h, p.subset h, IH (p.erase _)]
    ·
      simp [h, mt p.mem_iff.2 h, IH p]

theorem perm.bag_inter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : l₁.bag_inter t₁ ~ l₂.bag_inter t₂ :=
  ht.bag_inter_left l₂ ▸ hl.bag_inter_right _

theorem cons_perm_iff_perm_erase {a : α} {l₁ l₂ : List α} : a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ l₂.erase a :=
  ⟨fun h =>
      have  : a ∈ l₂ := h.subset (mem_cons_self a l₁)
      ⟨this, (h.trans$ perm_cons_erase this).cons_inv⟩,
    fun ⟨m, h⟩ => (h.cons a).trans (perm_cons_erase m).symm⟩

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_iff_count {l₁ l₂ : list α} : «expr ↔ »(«expr ~ »(l₁, l₂), ∀ a, «expr = »(count a l₁, count a l₂)) :=
⟨perm.count_eq, λ H, begin
   induction [expr l₁] [] ["with", ident a, ident l₁, ident IH] ["generalizing", ident l₂],
   { cases [expr l₂] ["with", ident b, ident l₂],
     { refl },
     specialize [expr H b],
     simp [] [] [] [] [] ["at", ident H],
     contradiction },
   { have [] [":", expr «expr ∈ »(a, l₂)] [":=", expr count_pos.1 (by rw ["<-", expr H] []; simp [] [] [] [] [] []; apply [expr nat.succ_pos])],
     refine [expr («expr $ »(IH, λ b, _).cons a).trans (perm_cons_erase this).symm],
     specialize [expr H b],
     rw [expr (perm_cons_erase this).count_eq] ["at", ident H],
     by_cases [expr «expr = »(b, a)]; simp [] [] [] ["[", expr h, "]"] [] ["at", ident H, "⊢"]; assumption }
 end⟩

theorem subperm.cons_right {α : Type _} {l l' : List α} (x : α) (h : l <+~ l') : l <+~ x :: l' :=
  h.trans (sublist_cons x l').Subperm

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The list version of `add_tsub_cancel_of_le` for multisets. -/
theorem subperm_append_diff_self_of_count_le
{l₁ l₂ : list α}
(h : ∀ x «expr ∈ » l₁, «expr ≤ »(count x l₁, count x l₂)) : «expr ~ »(«expr ++ »(l₁, l₂.diff l₁), l₂) :=
begin
  induction [expr l₁] [] ["with", ident hd, ident tl, ident IH] ["generalizing", ident l₂],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr ∈ »(hd, l₂)] [],
    { rw ["<-", expr count_pos] [],
      exact [expr lt_of_lt_of_le (count_pos.mpr (mem_cons_self _ _)) (h hd (mem_cons_self _ _))] },
    replace [ident this] [":", expr «expr ~ »(l₂, «expr :: »(hd, l₂.erase hd))] [":=", expr perm_cons_erase this],
    refine [expr perm.trans _ this.symm],
    rw ["[", expr cons_append, ",", expr diff_cons, ",", expr perm_cons, "]"] [],
    refine [expr IH (λ x hx, _)],
    specialize [expr h x (mem_cons_of_mem _ hx)],
    rw [expr perm_iff_count.mp this] ["at", ident h],
    by_cases [expr hx, ":", expr «expr = »(x, hd)],
    { subst [expr hd],
      simpa [] [] [] ["[", expr nat.succ_le_succ_iff, "]"] [] ["using", expr h] },
    { simpa [] [] [] ["[", expr hx, "]"] [] ["using", expr h] } }
end

/-- The list version of `multiset.le_iff_count`. -/
theorem subperm_ext_iff {l₁ l₂ : List α} : l₁ <+~ l₂ ↔ ∀ x _ : x ∈ l₁, count x l₁ ≤ count x l₂ :=
  by 
    refine' ⟨fun h x hx => subperm.count_le h x, fun h => _⟩
    suffices  : l₁ <+~ l₂.diff l₁ ++ l₁
    ·
      refine' this.trans (perm.subperm _)
      exact perm_append_comm.trans (subperm_append_diff_self_of_count_le h)
    convert (subperm_append_right _).mpr nil_subperm using 1

theorem subperm.cons_left {l₁ l₂ : List α} (h : l₁ <+~ l₂) (x : α) (hx : count x l₁ < count x l₂) : x :: l₁ <+~ l₂ :=
  by 
    rw [subperm_ext_iff] at h⊢
    intro y hy 
    byCases' hy' : y = x
    ·
      subst x 
      simpa using Nat.succ_le_of_ltₓ hx
    ·
      rw [count_cons_of_ne hy']
      refine' h y _ 
      simpa [hy'] using hy

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance decidable_perm : ∀ l₁ l₂ : list α, decidable «expr ~ »(l₁, l₂)
| «expr[ , ]»([]), «expr[ , ]»([]) := «expr $ »(is_true, perm.refl _)
| «expr[ , ]»([]), «expr :: »(b, l₂) := «expr $ »(is_false, λ h, by have [] [] [":=", expr h.nil_eq]; contradiction)
| «expr :: »(a, l₁), l₂ := by haveI [] [] [":=", expr decidable_perm l₁ (l₂.erase a)]; exact [expr decidable_of_iff' _ cons_perm_iff_perm_erase]

theorem perm.erase_dup {l₁ l₂ : List α} (p : l₁ ~ l₂) : erase_dup l₁ ~ erase_dup l₂ :=
  perm_iff_count.2$
    fun a =>
      if h : a ∈ l₁ then
        by 
          simp [nodup_erase_dup, h, p.subset h]
      else
        by 
          simp [h, mt p.mem_iff.2 h]

theorem perm.insert (a : α) {l₁ l₂ : List α} (p : l₁ ~ l₂) : insert a l₁ ~ insert a l₂ :=
  if h : a ∈ l₁ then
    by 
      simpa [h, p.subset h] using p
  else
    by 
      simpa [h, mt p.mem_iff.2 h] using p.cons a

theorem perm_insert_swap (x y : α) (l : List α) : insert x (insert y l) ~ insert y (insert x l) :=
  by 
    byCases' xl : x ∈ l <;> byCases' yl : y ∈ l <;> simp [xl, yl]
    byCases' xy : x = y
    ·
      simp [xy]
    simp [not_mem_cons_of_ne_of_not_mem xy xl, not_mem_cons_of_ne_of_not_mem (Ne.symm xy) yl]
    constructor

theorem perm_insert_nth {α} (x : α) (l : List α) {n} (h : n ≤ l.length) : insert_nth n x l ~ x :: l :=
  by 
    induction l generalizing n
    ·
      cases n 
      rfl 
      cases h 
    cases n
    ·
      simp [insert_nth]
    ·
      simp only [insert_nth, modify_nth_tail]
      trans
      ·
        apply perm.cons 
        apply l_ih 
        apply Nat.le_of_succ_le_succₓ h
      ·
        apply perm.swap

theorem perm.union_right {l₁ l₂ : List α} (t₁ : List α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ :=
  by 
    induction' h with a _ _ _ ih _ _ _ _ _ _ _ _ ih_1 ih_2 <;>
      try 
        simp 
    ·
      exact ih.insert a
    ·
      apply perm_insert_swap
    ·
      exact ih_1.trans ih_2

theorem perm.union_left (l : List α) {t₁ t₂ : List α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ :=
  by 
    induction l <;> simp [perm.insert]

theorem perm.union {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  (p₁.union_right t₁).trans (p₂.union_left l₂)

theorem perm.inter_right {l₁ l₂ : List α} (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
  perm.filter _

theorem perm.inter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ :=
  by 
    dsimp [· ∩ ·, List.interₓ]
    congr 
    funext a 
    rw [p.mem_iff]

theorem perm.inter {l₁ l₂ t₁ t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
  p₂.inter_left l₂ ▸ p₁.inter_right t₁

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem perm.inter_append
{l t₁ t₂ : list α}
(h : disjoint t₁ t₂) : «expr ~ »(«expr ∩ »(l, «expr ++ »(t₁, t₂)), «expr ++ »(«expr ∩ »(l, t₁), «expr ∩ »(l, t₂))) :=
begin
  induction [expr l] [] [] [],
  case [ident list.nil] { simp [] [] [] [] [] [] },
  case [ident list.cons, ":", ident x, ident xs, ident l_ih] { by_cases [expr h₁, ":", expr «expr ∈ »(x, t₁)],
    { have [ident h₂] [":", expr «expr ∉ »(x, t₂)] [":=", expr h h₁],
      simp [] [] [] ["*"] [] [] },
    by_cases [expr h₂, ":", expr «expr ∈ »(x, t₂)],
    { simp [] [] ["only"] ["[", "*", ",", expr inter_cons_of_not_mem, ",", expr false_or, ",", expr mem_append, ",", expr inter_cons_of_mem, ",", expr not_false_iff, "]"] [] [],
      transitivity [],
      { apply [expr perm.cons _ l_ih] },
      change [expr «expr ~ »(«expr ++ »(«expr ++ »(«expr[ , ]»([x]), «expr ∩ »(xs, t₁)), «expr ∩ »(xs, t₂)), «expr ++ »(«expr ∩ »(xs, t₁), «expr ++ »(«expr[ , ]»([x]), «expr ∩ »(xs, t₂))))] [] [],
      rw ["[", "<-", expr list.append_assoc, "]"] [],
      solve_by_elim [] [] ["[", expr perm.append_right, ",", expr perm_append_comm, "]"] [] },
    { simp [] [] [] ["*"] [] [] } }
end

end 

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm.pairwise_iff
{R : α → α → exprProp()}
(S : symmetric R) : ∀ {l₁ l₂ : list α} (p : «expr ~ »(l₁, l₂)), «expr ↔ »(pairwise R l₁, pairwise R l₂) :=
suffices ∀ {l₁ l₂}, «expr ~ »(l₁, l₂) → pairwise R l₁ → pairwise R l₂, from λ l₁ l₂ p, ⟨this p, this p.symm⟩,
λ l₁ l₂ p d, begin
  induction [expr d] [] ["with", ident a, ident l₁, ident h, ident d, ident IH] ["generalizing", ident l₂],
  { rw ["<-", expr p.nil_eq] [],
    constructor },
  { have [] [":", expr «expr ∈ »(a, l₂)] [":=", expr p.subset (mem_cons_self _ _)],
    rcases [expr mem_split this, "with", "⟨", ident s₂, ",", ident t₂, ",", ident rfl, "⟩"],
    have [ident p'] [] [":=", expr (p.trans perm_middle).cons_inv],
    refine [expr (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩)],
    exact [expr h _ (p'.symm.subset m)] }
end

theorem perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (nodup l₁ ↔ nodup l₂) :=
  perm.pairwise_iff$ @Ne.symm α

theorem perm.bind_right {l₁ l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : l₁.bind f ~ l₂.bind f :=
  by 
    induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      simp 
      exact IH.append_left _
    ·
      simp 
      rw [←append_assoc, ←append_assoc]
      exact perm_append_comm.append_right _
    ·
      exact IH₁.trans IH₂

theorem perm.bind_left (l : List α) {f g : α → List β} (h : ∀ a, f a ~ g a) : l.bind f ~ l.bind g :=
  by 
    induction' l with a l IH <;> simp  <;> exact (h a).append IH

theorem bind_append_perm (l : List α) (f g : α → List β) : l.bind f ++ l.bind g ~ l.bind fun x => f x ++ g x :=
  by 
    induction' l with a l IH <;> simp 
    refine' (perm.trans _ (IH.append_left _)).append_left _ 
    rw [←append_assoc, ←append_assoc]
    exact perm_append_comm.append_right _

theorem perm.product_right {l₁ l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) : product l₁ t₁ ~ product l₂ t₁ :=
  p.bind_right _

theorem perm.product_left (l : List α) {t₁ t₂ : List β} (p : t₁ ~ t₂) : product l t₁ ~ product l t₂ :=
  perm.bind_left _$ fun a => p.map _

@[congr]
theorem perm.product {l₁ l₂ : List α} {t₁ t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : product l₁ t₁ ~ product l₂ t₂ :=
  (p₁.product_right t₁).trans (p₂.product_left l₂)

theorem sublists_cons_perm_append (a : α) (l : List α) : sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
  by 
    simp only [sublists, sublists_aux_cons_cons, cons_append, perm_cons]
    refine' (perm.cons _ _).trans perm_middle.symm 
    induction' sublists_aux l cons with b l IH <;> simp 
    exact (IH.cons _).trans perm_middle.symm

theorem sublists_perm_sublists' : ∀ l : List α, sublists l ~ sublists' l
| [] => perm.refl _
| a :: l =>
  let IH := sublists_perm_sublists' l 
  by 
    rw [sublists'_cons] <;> exact (sublists_cons_perm_append _ _).trans (IH.append (IH.map _))

theorem revzip_sublists (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists → l₁ ++ l₂ ~ l :=
  by 
    rw [revzip]
    apply List.reverseRecOn l
    ·
      intro l₁ l₂ h 
      simp  at h 
      simp [h]
    ·
      intro l a IH l₁ l₂ h 
      rw [sublists_concat, reverse_append, zip_append, ←map_reverse, zip_map_right, zip_map_left] at h <;> [skip,
        ·
          simp ]
      simp only [Prod.mk.inj_iffₓ, mem_map, mem_append, Prod.map_mkₓ, Prod.exists] at h 
      rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
      ·
        rw [←append_assoc]
        exact (IH _ _ h).append_right _
      ·
        rw [append_assoc]
        apply (perm_append_comm.append_left _).trans 
        rw [←append_assoc]
        exact (IH _ _ h).append_right _

theorem revzip_sublists' (l : List α) : ∀ l₁ l₂, (l₁, l₂) ∈ revzip l.sublists' → l₁ ++ l₂ ~ l :=
  by 
    rw [revzip]
    induction' l with a l IH <;> intro l₁ l₂ h
    ·
      simp  at h 
      simp [h]
    ·
      rw [sublists'_cons, reverse_append, zip_append, ←map_reverse, zip_map_right, zip_map_left] at h <;> [simp  at h,
        simp ]
      rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
      ·
        exact perm_middle.trans ((IH _ _ h).cons _)
      ·
        exact (IH _ _ h).cons _

theorem perm_lookmap (f : α → Option α) {l₁ l₂ : List α}
  (H : Pairwise (fun a b => ∀ c _ : c ∈ f a d _ : d ∈ f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
  lookmap f l₁ ~ lookmap f l₂ :=
  by 
    let F := fun a b => ∀ c _ : c ∈ f a d _ : d ∈ f b, a = b ∧ c = d 
    change Pairwise F l₁ at H 
    induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      cases h : f a
      ·
        simp [h]
        exact IH (pairwise_cons.1 H).2
      ·
        simp [lookmap_cons_some _ _ h, p]
    ·
      cases' h₁ : f a with c <;> cases' h₂ : f b with d
      ·
        simp [h₁, h₂]
        apply swap
      ·
        simp [h₁, lookmap_cons_some _ _ h₂]
        apply swap
      ·
        simp [lookmap_cons_some _ _ h₁, h₂]
        apply swap
      ·
        simp [lookmap_cons_some _ _ h₁, lookmap_cons_some _ _ h₂]
        rcases(pairwise_cons.1 H).1 _ (Or.inl rfl) _ h₂ _ h₁ with ⟨rfl, rfl⟩
        rfl
    ·
      refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
      exact fun a b h c h₁ d h₂ => (h d h₂ c h₁).imp Eq.symm Eq.symm

theorem perm.erasep (f : α → Prop) [DecidablePred f] {l₁ l₂ : List α} (H : Pairwise (fun a b => f a → f b → False) l₁)
  (p : l₁ ~ l₂) : erasep f l₁ ~ erasep f l₂ :=
  by 
    let F := fun a b => f a → f b → False 
    change Pairwise F l₁ at H 
    induction' p with a l₁ l₂ p IH a b l l₁ l₂ l₃ p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      byCases' h : f a
      ·
        simp [h, p]
      ·
        simp [h]
        exact IH (pairwise_cons.1 H).2
    ·
      byCases' h₁ : f a <;> byCases' h₂ : f b <;> simp [h₁, h₂]
      ·
        cases (pairwise_cons.1 H).1 _ (Or.inl rfl) h₂ h₁
      ·
        apply swap
    ·
      refine' (IH₁ H).trans (IH₂ ((p₁.pairwise_iff _).1 H))
      exact fun a b h h₁ h₂ => h h₂ h₁

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem perm.take_inter
{α}
[decidable_eq α]
{xs ys : list α}
(n : exprℕ())
(h : «expr ~ »(xs, ys))
(h' : ys.nodup) : «expr ~ »(xs.take n, ys.inter (xs.take n)) :=
begin
  simp [] [] ["only"] ["[", expr list.inter, "]"] [] ["at", "*"],
  induction [expr h] [] [] ["generalizing", ident n],
  case [ident list.perm.nil, ":", ident n] { simp [] [] ["only"] ["[", expr not_mem_nil, ",", expr filter_false, ",", expr take_nil, "]"] [] [] },
  case [ident list.perm.cons, ":", ident h_x, ident h_l₁, ident h_l₂, ident h_a, ident h_ih, ident n] { cases [expr n] []; simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr true_or, ",", expr eq_self_iff_true, ",", expr filter_cons_of_pos, ",", expr perm_cons, ",", expr take, ",", expr not_mem_nil, ",", expr filter_false, "]"] [] [],
    cases [expr h'] ["with", "_", "_", ident h₁, ident h₂],
    convert [] [expr h_ih h₂ n] ["using", 1],
    apply [expr filter_congr],
    introv [ident h],
    simp [] [] ["only"] ["[", expr (h₁ x h).symm, ",", expr false_or, "]"] [] [] },
  case [ident list.perm.swap, ":", ident h_x, ident h_y, ident h_l, ident n] { cases [expr h'] ["with", "_", "_", ident h₁, ident h₂],
    cases [expr h₂] ["with", "_", "_", ident h₂, ident h₃],
    have [] [] [":=", expr h₁ _ (or.inl rfl)],
    cases [expr n] []; simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr not_mem_nil, ",", expr filter_false, ",", expr take, "]"] [] [],
    cases [expr n] []; simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr false_or, ",", expr true_or, ",", expr filter, ",", "*", ",", expr nat.nat_zero_eq_zero, ",", expr if_true, ",", expr not_mem_nil, ",", expr eq_self_iff_true, ",", expr or_false, ",", expr if_false, ",", expr perm_cons, ",", expr take, "]"] [] [],
    { rw [expr filter_eq_nil.2] [],
      intros [],
      solve_by_elim [] [] ["[", expr ne.symm, "]"] [] },
    { convert [] [expr perm.swap _ _ _] [],
      rw [expr @filter_congr _ _ ((«expr ∈ » take n h_l))] [],
      { clear [ident h₁],
        induction [expr n] [] [] ["generalizing", ident h_l]; simp [] [] ["only"] ["[", expr not_mem_nil, ",", expr filter_false, ",", expr take, "]"] [] [],
        cases [expr h_l] []; simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr true_or, ",", expr eq_self_iff_true, ",", expr filter_cons_of_pos, ",", expr true_and, ",", expr take, ",", expr not_mem_nil, ",", expr filter_false, ",", expr take_nil, "]"] [] [],
        cases [expr h₃] ["with", "_", "_", ident h₃, ident h₄],
        rwa ["[", expr @filter_congr _ _ ((«expr ∈ » take n_n h_l_tl)), ",", expr n_ih, "]"] [],
        { introv [ident h],
          apply [expr h₂ _ (or.inr h)] },
        { introv [ident h],
          simp [] [] ["only"] ["[", expr (h₃ x h).symm, ",", expr false_or, "]"] [] [] } },
      { introv [ident h],
        simp [] [] ["only"] ["[", expr (h₂ x h).symm, ",", expr (h₁ x (or.inr h)).symm, ",", expr false_or, "]"] [] [] } } },
  case [ident list.perm.trans, ":", ident h_l₁, ident h_l₂, ident h_l₃, ident h₀, ident h₁, ident h_ih₀, ident h_ih₁, ident n] { transitivity [],
    { apply [expr h_ih₀],
      rwa [expr h₁.nodup_iff] [] },
    { apply [expr perm.filter _ h₁] } }
end

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm.drop_inter
{α}
[decidable_eq α]
{xs ys : list α}
(n : exprℕ())
(h : «expr ~ »(xs, ys))
(h' : ys.nodup) : «expr ~ »(xs.drop n, ys.inter (xs.drop n)) :=
begin
  by_cases [expr h'', ":", expr «expr ≤ »(n, xs.length)],
  { let [ident n'] [] [":=", expr «expr - »(xs.length, n)],
    have [ident h₀] [":", expr «expr = »(n, «expr - »(xs.length, n'))] [],
    { dsimp [] ["[", expr n', "]"] [] [],
      rwa [expr tsub_tsub_cancel_of_le] [] },
    have [ident h₁] [":", expr «expr ≤ »(n', xs.length)] [],
    { apply [expr tsub_le_self] },
    have [ident h₂] [":", expr «expr = »(xs.drop n, (xs.reverse.take n').reverse)] [],
    { rw ["[", expr reverse_take _ h₁, ",", expr h₀, ",", expr reverse_reverse, "]"] [] },
    rw ["[", expr h₂, "]"] [],
    apply [expr (reverse_perm _).trans],
    rw [expr inter_reverse] [],
    apply [expr perm.take_inter _ _ h'],
    apply [expr (reverse_perm _).trans]; assumption },
  { have [] [":", expr «expr = »(drop n xs, «expr[ , ]»([]))] [],
    { apply [expr eq_nil_of_length_eq_zero],
      rw ["[", expr length_drop, ",", expr tsub_eq_zero_iff_le, "]"] [],
      apply [expr le_of_not_ge h''] },
    simp [] [] [] ["[", expr this, ",", expr list.inter, "]"] [] [] }
end

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem perm.slice_inter
{α}
[decidable_eq α]
{xs ys : list α}
(n m : exprℕ())
(h : «expr ~ »(xs, ys))
(h' : ys.nodup) : «expr ~ »(list.slice n m xs, «expr ∩ »(ys, list.slice n m xs)) :=
begin
  simp [] [] ["only"] ["[", expr slice_eq, "]"] [] [],
  have [] [":", expr «expr ≤ »(n, «expr + »(n, m))] [":=", expr nat.le_add_right _ _],
  have [] [] [":=", expr h.nodup_iff.2 h'],
  apply [expr perm.trans _ (perm.inter_append _).symm]; solve_by_elim [] [] ["[", expr perm.append, ",", expr perm.drop_inter, ",", expr perm.take_inter, ",", expr disjoint_take_drop, ",", expr h, ",", expr h', "]"] [] { max_depth := 7 }
end

section Permutations

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_of_mem_permutations_aux : ∀
{ts is l : list α}, «expr ∈ »(l, permutations_aux ts is) → «expr ~ »(l, «expr ++ »(ts, is)) :=
begin
  refine [expr permutations_aux.rec (by simp [] [] [] [] [] []) _],
  introv [ident IH1, ident IH2, ident m],
  rw ["[", expr permutations_aux_cons, ",", expr permutations, ",", expr mem_foldr_permutations_aux2, "]"] ["at", ident m],
  rcases [expr m, "with", ident m, "|", "⟨", ident l₁, ",", ident l₂, ",", ident m, ",", "_", ",", ident e, "⟩"],
  { exact [expr (IH1 m).trans perm_middle] },
  { subst [expr e],
    have [ident p] [":", expr «expr ~ »(«expr ++ »(l₁, l₂), is)] [],
    { simp [] [] [] ["[", expr permutations, "]"] [] ["at", ident m],
      cases [expr m] ["with", ident e, ident m],
      { simp [] [] [] ["[", expr e, "]"] [] [] },
      exact [expr «expr ▸ »(is.append_nil, IH2 m)] },
    exact [expr ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)] }
end

theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ perm.refl _) fun m => append_nil l₂ ▸ perm_of_mem_permutations_aux m

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem length_permutations_aux : ∀
ts
is : list α, «expr = »(«expr + »(length (permutations_aux ts is), «expr !»(is.length)), «expr !»(«expr + »(length ts, length is))) :=
begin
  refine [expr permutations_aux.rec (by simp [] [] [] [] [] []) _],
  intros [ident t, ident ts, ident is, ident IH1, ident IH2],
  have [ident IH2] [":", expr «expr = »(«expr + »(length (permutations_aux is nil), 1), «expr !»(is.length))] [],
  { simpa [] [] [] [] [] ["using", expr IH2] },
  simp [] [] [] ["[", "-", ident add_comm, ",", expr nat.factorial, ",", expr nat.add_succ, ",", expr mul_comm, "]"] [] ["at", ident IH1],
  rw ["[", expr permutations_aux_cons, ",", expr length_foldr_permutations_aux2' _ _ _ _ _ (λ
    l
    m, (perm_of_mem_permutations m).length_eq), ",", expr permutations, ",", expr length, ",", expr length, ",", expr IH2, ",", expr nat.succ_add, ",", expr nat.factorial_succ, ",", expr mul_comm (nat.succ _), ",", "<-", expr IH1, ",", expr add_comm «expr * »(_, _), ",", expr add_assoc, ",", expr nat.mul_succ, ",", expr mul_comm, "]"] []
end

theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutations_aux l []

theorem mem_permutations_of_perm_lemma {is l : List α}
  (H : l ~ [] ++ is → (∃ (ts' : _)(_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutations_aux is []) :
  l ~ is → l ∈ permutations is :=
  by 
    simpa [permutations, perm_nil] using H

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_permutations_aux_of_perm : ∀
{ts
 is
 l : list α}, «expr ~ »(l, «expr ++ »(is, ts)) → «expr ∨ »(«expr∃ , »((is' «expr ~ » is), «expr = »(l, «expr ++ »(is', ts))), «expr ∈ »(l, permutations_aux ts is)) :=
begin
  refine [expr permutations_aux.rec (by simp [] [] [] [] [] []) _],
  intros [ident t, ident ts, ident is, ident IH1, ident IH2, ident l, ident p],
  rw ["[", expr permutations_aux_cons, ",", expr mem_foldr_permutations_aux2, "]"] [],
  rcases [expr IH1 (p.trans perm_middle), "with", "⟨", ident is', ",", ident p', ",", ident e, "⟩", "|", ident m],
  { clear [ident p],
    subst [expr e],
    rcases [expr mem_split (p'.symm.subset (mem_cons_self _ _)), "with", "⟨", ident l₁, ",", ident l₂, ",", ident e, "⟩"],
    subst [expr is'],
    have [ident p] [] [":=", expr (perm_middle.symm.trans p').cons_inv],
    cases [expr l₂] ["with", ident a, ident l₂'],
    { exact [expr or.inl ⟨l₁, by simpa [] [] [] [] [] ["using", expr p]⟩] },
    { exact [expr or.inr (or.inr ⟨l₁, «expr :: »(a, l₂'), mem_permutations_of_perm_lemma IH2 p, by simp [] [] [] [] [] []⟩)] } },
  { exact [expr or.inr (or.inl m)] }
end

@[simp]
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutations_aux_of_perm⟩

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem perm_permutations'_aux_comm
(a b : α)
(l : list α) : «expr ~ »((permutations'_aux a l).bind (permutations'_aux b), (permutations'_aux b l).bind (permutations'_aux a)) :=
begin
  induction [expr l] [] ["with", ident c, ident l, ident ih] [],
  { simp [] [] [] ["[", expr swap, "]"] [] [] },
  simp [] [] [] ["[", expr permutations'_aux, "]"] [] [],
  apply [expr perm.swap'],
  have [] [":", expr ∀
   a
   b, «expr ~ »((map (cons c) (permutations'_aux a l)).bind (permutations'_aux b), «expr ++ »(map «expr ∘ »(cons b, cons c) (permutations'_aux a l), map (cons c) ((permutations'_aux a l).bind (permutations'_aux b))))] [],
  { intros [],
    simp [] [] ["only"] ["[", expr map_bind, ",", expr permutations'_aux, "]"] [] [],
    refine [expr (bind_append_perm _ (λ x, «expr[ , ]»([_])) _).symm.trans _],
    rw ["[", "<-", expr map_eq_bind, ",", "<-", expr bind_map, "]"] [] },
  refine [expr (((this _ _).append_left _).trans _).trans ((this _ _).append_left _).symm],
  rw ["[", "<-", expr append_assoc, ",", "<-", expr append_assoc, "]"] [],
  exact [expr perm_append_comm.append (ih.map _)]
end

theorem perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t :=
  by 
    induction' p with a s t p IH a b l s t u p₁ p₂ IH₁ IH₂
    ·
      simp 
    ·
      simp only [permutations']
      exact IH.bind_right _
    ·
      simp only [permutations']
      rw [bind_assoc, bind_assoc]
      apply perm.bind_left 
      apply perm_permutations'_aux_comm
    ·
      exact IH₁.trans IH₂

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem permutations_perm_permutations' (ts : list α) : «expr ~ »(ts.permutations, ts.permutations') :=
begin
  obtain ["⟨", ident n, ",", ident h, "⟩", ":", expr «expr∃ , »((n), «expr < »(length ts, n)), ":=", expr ⟨_, nat.lt_succ_self _⟩],
  induction [expr n] [] ["with", ident n, ident IH] ["generalizing", ident ts],
  { cases [expr h] [] },
  refine [expr list.reverse_rec_on ts (λ h, _) (λ ts t _ h, _) h],
  { simp [] [] [] ["[", expr permutations, "]"] [] [] },
  rw ["[", "<-", expr concat_eq_append, ",", expr length_concat, ",", expr nat.succ_lt_succ_iff, "]"] ["at", ident h],
  have [ident IH₂] [] [":=", expr (IH ts.reverse (by rwa ["[", expr length_reverse, "]"] [])).trans (reverse_perm _).permutations'],
  simp [] [] ["only"] ["[", expr permutations_append, ",", expr foldr_permutations_aux2, ",", expr permutations_aux_nil, ",", expr permutations_aux_cons, ",", expr append_nil, "]"] [] [],
  refine [expr (perm_append_comm.trans ((IH₂.bind_right _).append ((IH _ h).map _))).trans (perm.trans _ perm_append_comm.permutations')],
  rw ["[", expr map_eq_bind, ",", expr singleton_append, ",", expr permutations', "]"] [],
  convert [] [expr bind_append_perm _ _ _] [],
  funext [ident ys],
  rw ["[", expr permutations'_aux_eq_permutations_aux2, ",", expr permutations_aux2_append, "]"] []
end

@[simp]
theorem mem_permutations' {s t : List α} : s ∈ permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations

theorem perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
  (permutations_perm_permutations' _).trans$ h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
  ⟨fun h => mem_permutations.1$ h.mem_iff.1$ mem_permutations.2 (perm.refl _), perm.permutations⟩

@[simp]
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
  ⟨fun h => mem_permutations'.1$ h.mem_iff.1$ mem_permutations'.2 (perm.refl _), perm.permutations'⟩

theorem nth_le_permutations'_aux (s : List α) (x : α) (n : ℕ) (hn : n < length (permutations'_aux x s)) :
  (permutations'_aux x s).nthLe n hn = s.insert_nth n x :=
  by 
    induction' s with y s IH generalizing n
    ·
      simp only [length, permutations'_aux, Nat.lt_one_iff] at hn 
      simp [hn]
    ·
      cases n
      ·
        simp 
      ·
        simpa using IH _ _

theorem count_permutations'_aux_self [DecidableEq α] (l : List α) (x : α) :
  count (x :: l) (permutations'_aux x l) = length (take_while ((· = ·) x) l)+1 :=
  by 
    induction' l with y l IH generalizing x
    ·
      simp [take_while]
    ·
      rw [permutations'_aux, count_cons_self]
      byCases' hx : x = y
      ·
        subst hx 
        simpa [take_while, Nat.succ_inj'] using IH _
      ·
        rw [take_while]
        rw [if_neg hx]
        cases' permutations'_aux x l with a as
        ·
          simp 
        ·
          rw [count_eq_zero_of_not_mem, length, zero_addₓ]
          simp [hx, Ne.symm hx]

@[simp]
theorem length_permutations'_aux (s : List α) (x : α) : length (permutations'_aux x s) = length s+1 :=
  by 
    induction' s with y s IH
    ·
      simp 
    ·
      simpa using IH

@[simp]
theorem permutations'_aux_nth_le_zero (s : List α) (x : α)
  (hn : 0 < length (permutations'_aux x s) :=
    by 
      simp ) :
  (permutations'_aux x s).nthLe 0 hn = x :: s :=
  nth_le_permutations'_aux _ _ _ _

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem injective_permutations'_aux (x : α) : function.injective (permutations'_aux x) :=
begin
  intros [ident s, ident t, ident h],
  apply [expr insert_nth_injective s.length x],
  have [ident hl] [":", expr «expr = »(s.length, t.length)] [":=", expr by simpa [] [] [] [] [] ["using", expr congr_arg length h]],
  rw ["[", "<-", expr nth_le_permutations'_aux s x s.length (by simp [] [] [] [] [] []), ",", "<-", expr nth_le_permutations'_aux t x s.length (by simp [] [] [] ["[", expr hl, "]"] [] []), "]"] [],
  simp [] [] [] ["[", expr h, ",", expr hl, "]"] [] []
end

theorem nodup_permutations'_aux_of_not_mem (s : List α) (x : α) (hx : x ∉ s) : nodup (permutations'_aux x s) :=
  by 
    induction' s with y s IH
    ·
      simp 
    ·
      simp only [not_or_distrib, mem_cons_iff] at hx 
      simp only [not_and, exists_eq_right_right, mem_map, permutations'_aux, nodup_cons]
      refine' ⟨fun _ => Ne.symm hx.left, _⟩
      rw [nodup_map_iff]
      ·
        exact IH hx.right
      ·
        simp 

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup_permutations'_aux_iff {s : list α} {x : α} : «expr ↔ »(nodup (permutations'_aux x s), «expr ∉ »(x, s)) :=
begin
  refine [expr ⟨λ h, _, nodup_permutations'_aux_of_not_mem _ _⟩],
  intro [ident H],
  obtain ["⟨", ident k, ",", ident hk, ",", ident hk', "⟩", ":=", expr nth_le_of_mem H],
  rw [expr nodup_iff_nth_le_inj] ["at", ident h],
  suffices [] [":", expr «expr = »(k, «expr + »(k, 1))],
  { simpa [] [] [] [] [] ["using", expr this] },
  refine [expr h k «expr + »(k, 1) _ _ _],
  { simpa [] [] [] ["[", expr nat.lt_succ_iff, "]"] [] ["using", expr hk.le] },
  { simpa [] [] [] [] [] ["using", expr hk] },
  rw ["[", expr nth_le_permutations'_aux, ",", expr nth_le_permutations'_aux, "]"] [],
  have [ident hl] [":", expr «expr = »(length (insert_nth k x s), length (insert_nth «expr + »(k, 1) x s))] [],
  { rw ["[", expr length_insert_nth _ _ hk.le, ",", expr length_insert_nth _ _ (nat.succ_le_of_lt hk), "]"] [] },
  refine [expr ext_le hl (λ n hn hn', _)],
  rcases [expr lt_trichotomy n k, "with", ident H, "|", ident rfl, "|", ident H],
  { rw ["[", expr nth_le_insert_nth_of_lt _ _ _ _ H (H.trans hk), ",", expr nth_le_insert_nth_of_lt _ _ _ _ (H.trans (nat.lt_succ_self _)), "]"] [] },
  { rw ["[", expr nth_le_insert_nth_self _ _ _ hk.le, ",", expr nth_le_insert_nth_of_lt _ _ _ _ (nat.lt_succ_self _) hk, ",", expr hk', "]"] [] },
  { rcases [expr (nat.succ_le_of_lt H).eq_or_lt, "with", ident rfl, "|", ident H'],
    { rw ["[", expr nth_le_insert_nth_self _ _ _ (nat.succ_le_of_lt hk), "]"] [],
      convert [] [expr hk'] ["using", 1],
      convert [] [expr nth_le_insert_nth_add_succ _ _ _ 0 _] [],
      simpa [] [] [] [] [] ["using", expr hk] },
    { obtain ["⟨", ident m, ",", ident rfl, "⟩", ":=", expr nat.exists_eq_add_of_lt H'],
      rw ["[", expr length_insert_nth _ _ hk.le, ",", expr nat.succ_lt_succ_iff, ",", expr nat.succ_add, "]"] ["at", ident hn],
      rw [expr nth_le_insert_nth_add_succ] [],
      convert [] [expr nth_le_insert_nth_add_succ s x k m.succ _] ["using", 2],
      { simp [] [] [] ["[", expr nat.add_succ, ",", expr nat.succ_add, "]"] [] [] },
      { simp [] [] [] ["[", expr add_left_comm, ",", expr add_comm, "]"] [] [] },
      { simpa [] [] [] ["[", expr nat.add_succ, "]"] [] ["using", expr hn] },
      { simpa [] [] [] ["[", expr nat.succ_add, "]"] [] ["using", expr hn] } } }
end

-- error in Data.List.Perm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup_permutations (s : list α) (hs : nodup s) : nodup s.permutations :=
begin
  rw [expr (permutations_perm_permutations' s).nodup_iff] [],
  induction [expr hs] [] ["with", ident x, ident l, ident h, ident h', ident IH] [],
  { simp [] [] [] [] [] [] },
  { rw ["[", expr permutations', "]"] [],
    rw [expr nodup_bind] [],
    split,
    { intros [ident ys, ident hy],
      rw [expr mem_permutations'] ["at", ident hy],
      rw ["[", expr nodup_permutations'_aux_iff, ",", expr hy.mem_iff, "]"] [],
      exact [expr λ H, h x H rfl] },
    { refine [expr IH.pairwise_of_forall_ne (λ as ha bs hb H, _)],
      rw [expr disjoint_iff_ne] [],
      rintro [ident a, ident ha', ident b, ident hb', ident rfl],
      obtain ["⟨", ident n, ",", ident hn, ",", ident hn', "⟩", ":=", expr nth_le_of_mem ha'],
      obtain ["⟨", ident m, ",", ident hm, ",", ident hm', "⟩", ":=", expr nth_le_of_mem hb'],
      rw [expr mem_permutations'] ["at", ident ha, ident hb],
      have [ident hl] [":", expr «expr = »(as.length, bs.length)] [":=", expr (ha.trans hb.symm).length_eq],
      simp [] [] ["only"] ["[", expr nat.lt_succ_iff, ",", expr length_permutations'_aux, "]"] [] ["at", ident hn, ident hm],
      rw [expr nth_le_permutations'_aux] ["at", ident hn', ident hm'],
      have [ident hx] [":", expr «expr = »(nth_le (insert_nth n x as) m (by rwa ["[", expr length_insert_nth _ _ hn, ",", expr nat.lt_succ_iff, ",", expr hl, "]"] []), x)] [],
      { simp [] [] [] ["[", expr hn', ",", "<-", expr hm', ",", expr hm, "]"] [] [] },
      have [ident hx'] [":", expr «expr = »(nth_le (insert_nth m x bs) n (by rwa ["[", expr length_insert_nth _ _ hm, ",", expr nat.lt_succ_iff, ",", "<-", expr hl, "]"] []), x)] [],
      { simp [] [] [] ["[", expr hm', ",", "<-", expr hn', ",", expr hn, "]"] [] [] },
      rcases [expr lt_trichotomy n m, "with", ident ht, "|", ident ht, "|", ident ht],
      { suffices [] [":", expr «expr ∈ »(x, bs)],
        { exact [expr h x (hb.subset this) rfl] },
        rw ["[", "<-", expr hx', ",", expr nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hm), "]"] [],
        exact [expr nth_le_mem _ _ _] },
      { simp [] [] ["only"] ["[", expr ht, "]"] [] ["at", ident hm', ident hn'],
        rw ["<-", expr hm'] ["at", ident hn'],
        exact [expr H (insert_nth_injective _ _ hn')] },
      { suffices [] [":", expr «expr ∈ »(x, as)],
        { exact [expr h x (ha.subset this) rfl] },
        rw ["[", "<-", expr hx, ",", expr nth_le_insert_nth_of_lt _ _ _ _ ht (ht.trans_le hn), "]"] [],
        exact [expr nth_le_mem _ _ _] } } }
end

end Permutations

end List

