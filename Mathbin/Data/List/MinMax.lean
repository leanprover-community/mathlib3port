/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes
-/
import Mathbin.Data.List.Basic

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/


namespace List

variable {α : Type _} {β : Type _} [LinearOrderₓ β]

/-- Auxiliary definition to define `argmax` -/
def argmax₂ (f : α → β) (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if f b ≤ f c then some c else some b

/-- `argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmax f []` = none` -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argmax₂ f) none

/-- `argmin f l` returns `some a`, where `a` of `l` that minimises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmin f []` = none` -/
def argmin (f : α → β) (l : List α) :=
  @argmax _ (OrderDual β) _ f l

@[simp]
theorem argmax_two_self (f : α → β) (a : α) : argmax₂ f (some a) a = a :=
  if_pos le_rfl

@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl

@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = some a :=
  rfl

@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl

@[simp]
theorem foldl_argmax₂_eq_none {f : α → β} {l : List α} {o : Option α} :
    l.foldl (argmax₂ f) o = none ↔ l = [] ∧ o = none :=
  (List.reverseRecOn l
      (by
        simp ))
    fun tl hd => by
    simp [argmax₂] <;>
      cases foldl (argmax₂ f) o tl <;>
        simp <;>
          try
              split_ifs <;>
            simp

private theorem le_of_foldl_argmax₂ {f : α → β} {l} :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldlₓ (argmax₂ f) o l → f a ≤ f m :=
  List.reverseRecOn l (fun _ _ _ h => absurd h <| not_mem_nilₓ _)
    (by
      intro tl _ ih _ _ _ h ho
      rw [foldl_append, foldl_cons, foldl_nil, argmax₂] at ho
      cases hf : foldl (argmax₂ f) o tl
      · rw [hf] at ho
        rw [foldl_argmax₂_eq_none] at hf
        simp_all [hf.1, hf.2]
        
      rw [hf, Option.mem_def] at ho
      dsimp' only  at ho
      cases' mem_append.1 h with h h
      · refine' le_transₓ (ih h hf) _
        have := @le_of_ltₓ _ _ (f val) (f m)
        split_ifs  at ho <;> simp_all
        
      · split_ifs  at ho <;> simp_all
        )

private theorem foldl_argmax₂_mem (f : α → β) l : ∀ a m : α, m ∈ foldlₓ (argmax₂ f) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l
    (by
      simp [eq_comm])
    (by
      intro tl hd ih a m
      simp only [foldl_append, foldl_cons, foldl_nil, argmax₂]
      cases hf : foldl (argmax₂ f) (some a) tl
      · simp (config := { contextual := true })
        
      · dsimp' only
        split_ifs
        · -- `finish [ih _ _ hf]` closes this goal
          rcases ih _ _ hf with (rfl | H)
          · simp only [mem_cons_iff, mem_append, mem_singleton, Option.mem_def]
            tauto
            
          · apply fun hm => Or.inr (list.mem_append.mpr <| Or.inl _)
            exact option.mem_some_iff.mp hm ▸ H
            
          
        · simp (config := { contextual := true })
          
        )

theorem argmax_mem {f : α → β} : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by
    simp
  | hd :: tl, m => by
    simpa [argmax, argmax₂] using foldl_argmax₂_mem f tl hd m

theorem argmin_mem {f : α → β} : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ (OrderDual β) _ _

@[simp]
theorem argmax_eq_none {f : α → β} {l : List α} : l.argmax f = none ↔ l = [] := by
  simp [argmax]

@[simp]
theorem argmin_eq_none {f : α → β} {l : List α} : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ (OrderDual β) _ _ _

theorem le_argmax_of_mem {f : α → β} {a m : α} {l : List α} : a ∈ l → m ∈ argmax f l → f a ≤ f m :=
  le_of_foldl_argmax₂

theorem argmin_le_of_mem {f : α → β} {a m : α} {l : List α} : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_argmax_of_mem _ (OrderDual β) _ _ _ _ _

theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) = Option.casesOn (argmax f l) (some a) fun c => if f a ≤ f c then some c else some a := by
  rw [argmax, argmax] <;> simp [argmax₂]

theorem argmin_concat (f : α → β) (a : α) (l : List α) :
    argmin f (l ++ [a]) = Option.casesOn (argmin f l) (some a) fun c => if f c ≤ f a then some c else some a :=
  @argmax_concat _ (OrderDual β) _ _ _ _

theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) = Option.casesOn (argmax f l) (some a) fun c => if f c ≤ f a then some a else some c :=
  (List.reverseRecOn l rfl) fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    cases' h : argmax f hd with m
    · simp [h]
      
    · simp [h]
      dsimp'
      by_cases' ham : f m ≤ f a
      · rw [if_pos ham]
        dsimp'
        by_cases' htlm : f tl ≤ f m
        · rw [if_pos htlm]
          dsimp'
          rw [if_pos (le_transₓ htlm ham), if_pos ham]
          
        · rw [if_neg htlm]
          
        
      · rw [if_neg ham]
        dsimp'
        by_cases' htlm : f tl ≤ f m
        · rw [if_pos htlm]
          dsimp'
          rw [if_neg ham]
          
        · rw [if_neg htlm]
          dsimp'
          rw [if_neg (not_le_of_gtₓ (lt_transₓ (lt_of_not_geₓ ham) (lt_of_not_geₓ htlm)))]
          
        
      

theorem argmin_cons (f : α → β) (a : α) (l : List α) :
    argmin f (a :: l) = Option.casesOn (argmin f l) (some a) fun c => if f a ≤ f c then some a else some c :=
  @argmax_cons _ (OrderDual β) _ _ _ _

theorem index_of_argmax [DecidableEq α] {f : α → β} :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.indexOf m ≤ l.indexOf a
  | [], m, _, _, _, _ => by
    simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [index_of_cons, argmax_cons, Option.mem_def] at hm⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
      
    · rw [h] at hm
      dsimp' only  at hm
      cases' ha with hahd hatl
      · clear index_of_argmax
        subst hahd
        split_ifs  at hm
        · subst hm
          
        · subst hm
          contradiction
          
        
      · have := index_of_argmax h hatl
        clear index_of_argmax
        split_ifs  at * <;>
          first |
            rfl|
            exact Nat.zero_leₓ _|
            simp_all [Nat.succ_le_succ_iff, -not_leₓ]
        
      

theorem index_of_argmin [DecidableEq α] {f : α → β} :
    ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @index_of_argmax _ (OrderDual β) _ _ _

theorem mem_argmax_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
    m ∈ argmax f l ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f a ≤ f m) ∧ ∀, ∀ a ∈ l, ∀, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun a ha => le_argmax_of_mem ha hm, fun _ => index_of_argmax hm⟩, by
    rintro ⟨hml, ham, hma⟩
    cases' harg : argmax f l with n
    · simp_all
      
    · have :=
        le_antisymmₓ (hma n (argmax_mem harg) (le_argmax_of_mem hml harg))
          (index_of_argmax harg hml (ham _ (argmax_mem harg)))
      rw [(index_of_inj hml (argmax_mem harg)).1 this, Option.mem_def]
      ⟩

theorem argmax_eq_some_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
    argmax f l = some m ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f a ≤ f m) ∧ ∀, ∀ a ∈ l, ∀, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  mem_argmax_iff

theorem mem_argmin_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
    m ∈ argmin f l ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f m ≤ f a) ∧ ∀, ∀ a ∈ l, ∀, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @mem_argmax_iff _ (OrderDual β) _ _ _ _ _

theorem argmin_eq_some_iff [DecidableEq α] {f : α → β} {m : α} {l : List α} :
    argmin f l = some m ↔ m ∈ l ∧ (∀, ∀ a ∈ l, ∀, f m ≤ f a) ∧ ∀, ∀ a ∈ l, ∀, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  mem_argmin_iff

variable [LinearOrderₓ α]

/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : List α) : WithBot α :=
  argmax id l

/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : List α) : WithTop α :=
  argmin id l

@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl

@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl

theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem

@[simp]
theorem maximum_eq_none {l : List α} : l.maximum = none ↔ l = [] :=
  argmax_eq_none

@[simp]
theorem minimum_eq_none {l : List α} : l.minimum = none ↔ l = [] :=
  argmin_eq_none

theorem le_maximum_of_mem {a m : α} {l : List α} : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_argmax_of_mem

theorem minimum_le_of_mem {a m : α} {l : List α} : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  argmin_le_of_mem

theorem le_maximum_of_mem' {a : α} {l : List α} (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  Option.casesOn (maximum l) (fun _ h => absurd ha ((h rfl).symm ▸ not_mem_nilₓ _))
    (fun m hm _ => WithBot.coe_le_coe.2 <| hm _ rfl) (fun m => @le_maximum_of_mem _ _ _ m _ ha)
    (@maximum_eq_none _ _ l).1

theorem le_minimum_of_mem' {a : α} {l : List α} (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  @le_maximum_of_mem' (OrderDual α) _ _ _ ha

theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  rw [max_commₓ]
  simp only [maximum, argmax_concat, id]
  cases h : argmax id l
  · rw [max_eq_leftₓ]
    rfl
    exact bot_le
    
  change (coe : α → WithBot α) with some
  rw [max_commₓ]
  simp [max_def]

theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat (OrderDual α) _ _ _

theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max a (maximum l) :=
  List.reverseRecOn l
    (by
      simp [@max_eq_leftₓ (WithBot α) _ _ _ bot_le])
    fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assocₓ]

theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min a (minimum l) :=
  @maximum_cons (OrderDual α) _ _ _

theorem maximum_eq_coe_iff {m : α} {l : List α} : maximum l = m ↔ m ∈ l ∧ ∀, ∀ a ∈ l, ∀, a ≤ m := by
  unfold_coes
  simp only [maximum, argmax_eq_some_iff, id]
  constructor
  · simp (config := { contextual := true })only [true_andₓ, forall_true_iff]
    
  · simp (config := { contextual := true })only [true_andₓ, forall_true_iff]
    intro h a hal hma
    rw [le_antisymmₓ hma (h.2 a hal)]
    

theorem minimum_eq_coe_iff {m : α} {l : List α} : minimum l = m ↔ m ∈ l ∧ ∀, ∀ a ∈ l, ∀, m ≤ a :=
  @maximum_eq_coe_iff (OrderDual α) _ _ _

section Fold

variable {M : Type _} [CanonicallyLinearOrderedAddMonoid M]

/-! Note: since there is no typeclass typeclass dual
to `canonically_linear_ordered_add_monoid α` we cannot express these lemmas generally for
`minimum`; instead we are limited to doing so on `order_dual α`. -/


theorem maximum_eq_coe_foldr_max_of_ne_nil (l : List M) (h : l ≠ []) : l.maximum = (l.foldr max ⊥ : M) := by
  induction' l with hd tl IH
  · contradiction
    
  · rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases' h : tl = []
    · simp [h, -WithTop.coe_zero]
      
    · simp [IH h]
      
    

theorem minimum_eq_coe_foldr_min_of_ne_nil (l : List (OrderDual M)) (h : l ≠ []) :
    l.minimum = (l.foldr min ⊤ : OrderDual M) :=
  maximum_eq_coe_foldr_max_of_ne_nil l h

theorem maximum_nat_eq_coe_foldr_max_of_ne_nil (l : List ℕ) (h : l ≠ []) : l.maximum = (l.foldr max 0 : ℕ) :=
  maximum_eq_coe_foldr_max_of_ne_nil l h

theorem max_le_of_forall_le (l : List M) (n : M) (h : ∀, ∀ x ∈ l, ∀, x ≤ n) : l.foldr max ⊥ ≤ n := by
  induction' l with y l IH
  · simp
    
  · specialize IH fun x hx => h x (mem_cons_of_mem _ hx)
    have hy : y ≤ n := h y (mem_cons_self _ _)
    simpa [hy] using IH
    

theorem le_min_of_le_forall (l : List (OrderDual M)) (n : OrderDual M) (h : ∀, ∀ x ∈ l, ∀, n ≤ x) : n ≤ l.foldr min ⊤ :=
  max_le_of_forall_le l n h

theorem max_nat_le_of_forall_le (l : List ℕ) (n : ℕ) (h : ∀, ∀ x ∈ l, ∀, x ≤ n) : l.foldr max 0 ≤ n :=
  max_le_of_forall_le l n h

end Fold

end List

