
/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.  -/


open Nat Function Option

universe u v w

def Streamₓ (α : Type u) :=
  Nat → α

namespace Streamₓ

variable{α : Type u}{β : Type v}{δ : Type w}

def cons (a : α) (s : Streamₓ α) : Streamₓ α :=
  fun i =>
    match i with 
    | 0 => a
    | succ n => s n

@[reducible]
def head (s : Streamₓ α) : α :=
  s 0

def tail (s : Streamₓ α) : Streamₓ α :=
  fun i => s (i+1)

def drop (n : Nat) (s : Streamₓ α) : Streamₓ α :=
  fun i => s (i+n)

@[reducible]
def nth (n : Nat) (s : Streamₓ α) : α :=
  s n

protected theorem eta (s : Streamₓ α) : head s :: tail s = s :=
  funext
    fun i =>
      by 
        cases i <;> rfl

theorem nth_zero_cons (a : α) (s : Streamₓ α) : nth 0 (a :: s) = a :=
  rfl

theorem head_cons (a : α) (s : Streamₓ α) : head (a :: s) = a :=
  rfl

theorem tail_cons (a : α) (s : Streamₓ α) : tail (a :: s) = s :=
  rfl

theorem tail_drop (n : Nat) (s : Streamₓ α) : tail (drop n s) = drop n (tail s) :=
  funext
    fun i =>
      by 
        unfold tail drop 
        simp [Nat.add_comm, Nat.add_left_comm]

theorem nth_drop (n m : Nat) (s : Streamₓ α) : nth n (drop m s) = nth (n+m) s :=
  rfl

theorem tail_eq_drop (s : Streamₓ α) : tail s = drop 1 s :=
  rfl

theorem drop_drop (n m : Nat) (s : Streamₓ α) : drop n (drop m s) = drop (n+m) s :=
  funext
    fun i =>
      by 
        unfold drop 
        rw [Nat.add_assoc]

theorem nth_succ (n : Nat) (s : Streamₓ α) : nth (succ n) s = nth n (tail s) :=
  rfl

theorem drop_succ (n : Nat) (s : Streamₓ α) : drop (succ n) s = drop n (tail s) :=
  rfl

protected theorem ext {s₁ s₂ : Streamₓ α} : (∀ n, nth n s₁ = nth n s₂) → s₁ = s₂ :=
  fun h => funext h

def all (p : α → Prop) (s : Streamₓ α) :=
  ∀ n, p (nth n s)

def any (p : α → Prop) (s : Streamₓ α) :=
  ∃ n, p (nth n s)

theorem all_def (p : α → Prop) (s : Streamₓ α) : all p s = ∀ n, p (nth n s) :=
  rfl

theorem any_def (p : α → Prop) (s : Streamₓ α) : any p s = ∃ n, p (nth n s) :=
  rfl

protected def mem (a : α) (s : Streamₓ α) :=
  any (fun b => a = b) s

instance  : HasMem α (Streamₓ α) :=
  ⟨Streamₓ.Mem⟩

theorem mem_cons (a : α) (s : Streamₓ α) : a ∈ a :: s :=
  Exists.introₓ 0 rfl

theorem mem_cons_of_mem {a : α} {s : Streamₓ α} (b : α) : a ∈ s → a ∈ b :: s :=
  fun ⟨n, h⟩ =>
    Exists.introₓ (succ n)
      (by 
        rw [nth_succ, tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : α} {s : Streamₓ α} : a ∈ b :: s → a = b ∨ a ∈ s :=
  fun ⟨n, h⟩ =>
    by 
      cases' n with n'
      ·
        left 
        exact h
      ·
        right 
        rw [nth_succ, tail_cons] at h 
        exact ⟨n', h⟩

theorem mem_of_nth_eq {n : Nat} {s : Streamₓ α} {a : α} : a = nth n s → a ∈ s :=
  fun h => Exists.introₓ n h

section Map

variable(f : α → β)

def map (s : Streamₓ α) : Streamₓ β :=
  fun n => f (nth n s)

theorem drop_map (n : Nat) (s : Streamₓ α) : drop n (map f s) = map f (drop n s) :=
  Streamₓ.ext fun i => rfl

theorem nth_map (n : Nat) (s : Streamₓ α) : nth n (map f s) = f (nth n s) :=
  rfl

theorem tail_map (s : Streamₓ α) : tail (map f s) = map f (tail s) :=
  by 
    rw [tail_eq_drop]
    rfl

theorem head_map (s : Streamₓ α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq (s : Streamₓ α) : map f s = f (head s) :: map f (tail s) :=
  by 
    rw [←Streamₓ.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : Streamₓ α) : map f (a :: s) = f a :: map f s :=
  by 
    rw [←Streamₓ.eta (map f (a :: s)), map_eq]
    rfl

theorem map_id (s : Streamₓ α) : map id s = s :=
  rfl

theorem map_map (g : β → δ) (f : α → β) (s : Streamₓ α) : map g (map f s) = map (g ∘ f) s :=
  rfl

theorem map_tail (s : Streamₓ α) : map f (tail s) = tail (map f s) :=
  rfl

theorem mem_map {a : α} {s : Streamₓ α} : a ∈ s → f a ∈ map f s :=
  fun ⟨n, h⟩ =>
    Exists.introₓ n
      (by 
        rw [nth_map, h])

theorem exists_of_mem_map {f} {b : β} {s : Streamₓ α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨nth n s, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable(f : α → β → δ)

def zip (s₁ : Streamₓ α) (s₂ : Streamₓ β) : Streamₓ δ :=
  fun n => f (nth n s₁) (nth n s₂)

theorem drop_zip (n : Nat) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Streamₓ.ext fun i => rfl

theorem nth_zip (n : Nat) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : nth n (zip f s₁ s₂) = f (nth n s₁) (nth n s₂) :=
  rfl

theorem head_zip (s₁ : Streamₓ α) (s₂ : Streamₓ β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

theorem tail_zip (s₁ : Streamₓ α) (s₂ : Streamₓ β) : tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

theorem zip_eq (s₁ : Streamₓ α) (s₂ : Streamₓ β) : zip f s₁ s₂ = f (head s₁) (head s₂) :: zip f (tail s₁) (tail s₂) :=
  by 
    rw [←Streamₓ.eta (zip f s₁ s₂)]
    rfl

end Zip

def const (a : α) : Streamₓ α :=
  fun n => a

theorem mem_const (a : α) : a ∈ const a :=
  Exists.introₓ 0 rfl

theorem const_eq (a : α) : const a = a :: const a :=
  by 
    apply Streamₓ.ext 
    intro n 
    cases n <;> rfl

theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a :: const a) = const a by 
    rwa [←const_eq] at this 
  rfl

theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

theorem nth_const (n : Nat) (a : α) : nth n (const a) = a :=
  rfl

theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a :=
  Streamₓ.ext fun i => rfl

def iterate (f : α → α) (a : α) : Streamₓ α :=
  fun n => Nat.recOn n a fun n r => f r

theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) :=
  by 
    funext n 
    induction' n with n' ih
    ·
      rfl
    ·
      unfold tail iterate 
      unfold tail iterate  at ih 
      rw [add_one] at ih 
      dsimp  at ih 
      rw [add_one]
      dsimp 
      rw [ih]

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a :: iterate f (f a) :=
  by 
    rw [←Streamₓ.eta (iterate f a)]
    rw [tail_iterate]
    rfl

theorem nth_zero_iterate (f : α → α) (a : α) : nth 0 (iterate f a) = a :=
  rfl

theorem nth_succ_iterate (n : Nat) (f : α → α) (a : α) : nth (succ n) (iterate f a) = nth n (iterate f (f a)) :=
  by 
    rw [nth_succ, tail_iterate]

section Bisim

variable(R : Streamₓ α → Streamₓ α → Prop)

local infixl:50 " ~ " => R

def is_bisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

theorem nth_of_bisim (bisim : is_bisimulation R) :
  ∀ {s₁ s₂} n, s₁ ~ s₂ → nth n s₁ = nth n s₂ ∧ drop (n+1) s₁ ~ drop (n+1) s₂
| s₁, s₂, 0, h => bisim h
| s₁, s₂, n+1, h =>
  match bisim h with 
  | ⟨h₁, trel⟩ => nth_of_bisim n trel

theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  fun s₁ s₂ r => Streamₓ.ext fun n => And.elim_left (nth_of_bisim R bisim n r)

end Bisim

-- error in Data.Stream.Init: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem bisim_simple
(s₁
 s₂ : stream α) : «expr = »(head s₁, head s₂) → «expr = »(s₁, tail s₁) → «expr = »(s₂, tail s₂) → «expr = »(s₁, s₂) :=
assume
hh
ht₁
ht₂, eq_of_bisim (λ
 s₁
 s₂, «expr ∧ »(«expr = »(head s₁, head s₂), «expr ∧ »(«expr = »(s₁, tail s₁), «expr = »(s₂, tail s₂)))) (λ
 (s₁ s₂)
 ⟨h₁, h₂, h₃⟩, begin
   constructor,
   exact [expr h₁],
   rw ["[", "<-", expr h₂, ",", "<-", expr h₃, "]"] [],
   repeat { constructor }; assumption
 end) (and.intro hh (and.intro ht₁ ht₂))

theorem coinduction {s₁ s₂ : Streamₓ α} :
  head s₁ = head s₂ → (∀ β : Type u fr : Streamₓ α → β, fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
    eq_of_bisim
      (fun s₁ s₂ => head s₁ = head s₂ ∧ ∀ β : Type u fr : Streamₓ α → β, fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
      (fun s₁ s₂ h =>
        have h₁ : head s₁ = head s₂ := And.elim_left h 
        have h₂ : head (tail s₁) = head (tail s₂) := And.elim_right h α (@head α) h₁ 
        have h₃ :
          ∀ β : Type u fr : Streamₓ α → β, fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
          fun β fr => And.elim_right h β fun s => fr (tail s)
        And.intro h₁ (And.intro h₂ h₃))
      (And.intro hh ht)

theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl
    fun β fr ch =>
      by 
        rw [tail_iterate, tail_const]
        exact ch

attribute [local reducible] Streamₓ

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) :=
  by 
    funext n 
    induction' n with n' ih
    ·
      rfl
    ·
      unfold map iterate nth 
      dsimp 
      unfold map iterate nth  at ih 
      dsimp  at ih 
      rw [ih]

section Corec

def corec (f : α → β) (g : α → α) : α → Streamₓ β :=
  fun a => map f (iterate g a)

def corec_on (a : α) (f : α → β) (g : α → α) : Streamₓ β :=
  corec f g a

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) :=
  by 
    rw [corec_def, map_eq, head_iterate, tail_iterate]
    rfl

theorem corec_id_id_eq_const (a : α) : corec id id a = const a :=
  by 
    rw [corec_def, map_id, iterate_id]

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

def corec' (f : α → β × α) : α → Streamₓ β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

def unfolds (g : α → β) (f : α → α) (a : α) : Streamₓ β :=
  corec g f a

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) :=
  by 
    unfold unfolds 
    rw [corec_eq]

theorem nth_unfolds_head_tail : ∀ n : Nat s : Streamₓ α, nth n (unfolds head tail s) = nth n s :=
  by 
    intro n 
    induction' n with n' ih
    ·
      intro s 
      rfl
    ·
      intro s 
      rw [nth_succ, nth_succ, unfolds_eq, tail_cons, ih]

theorem unfolds_head_eq : ∀ s : Streamₓ α, unfolds head tail s = s :=
  fun s => Streamₓ.ext fun n => nth_unfolds_head_tail n s

def interleave (s₁ s₂ : Streamₓ α) : Streamₓ α :=
  corec_on (s₁, s₂) (fun ⟨s₁, s₂⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

infixl:65 "⋈" => interleave

theorem interleave_eq (s₁ s₂ : Streamₓ α) : s₁⋈s₂ = head s₁ :: head s₂ :: (tail s₁⋈tail s₂) :=
  by 
    unfold interleave corec_on 
    rw [corec_eq]
    dsimp 
    rw [corec_eq]
    rfl

theorem tail_interleave (s₁ s₂ : Streamₓ α) : tail (s₁⋈s₂) = s₂⋈tail s₁ :=
  by 
    unfold interleave corec_on 
    rw [corec_eq]
    rfl

theorem interleave_tail_tail (s₁ s₂ : Streamₓ α) : tail s₁⋈tail s₂ = tail (tail (s₁⋈s₂)) :=
  by 
    rw [interleave_eq s₁ s₂]
    rfl

theorem nth_interleave_left : ∀ n : Nat s₁ s₂ : Streamₓ α, nth (2*n) (s₁⋈s₂) = nth n s₁
| 0, s₁, s₂ => rfl
| succ n, s₁, s₂ =>
  by 
    change nth (succ (succ (2*n))) (s₁⋈s₂) = nth (succ n) s₁ 
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_left]
    rfl

theorem nth_interleave_right : ∀ n : Nat s₁ s₂ : Streamₓ α, nth ((2*n)+1) (s₁⋈s₂) = nth n s₂
| 0, s₁, s₂ => rfl
| succ n, s₁, s₂ =>
  by 
    change nth (succ (succ ((2*n)+1))) (s₁⋈s₂) = nth (succ n) s₂ 
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons, nth_interleave_right]
    rfl

theorem mem_interleave_left {a : α} {s₁ : Streamₓ α} (s₂ : Streamₓ α) : a ∈ s₁ → a ∈ s₁⋈s₂ :=
  fun ⟨n, h⟩ =>
    Exists.introₓ (2*n)
      (by 
        rw [h, nth_interleave_left])

theorem mem_interleave_right {a : α} {s₁ : Streamₓ α} (s₂ : Streamₓ α) : a ∈ s₂ → a ∈ s₁⋈s₂ :=
  fun ⟨n, h⟩ =>
    Exists.introₓ ((2*n)+1)
      (by 
        rw [h, nth_interleave_right])

def even (s : Streamₓ α) : Streamₓ α :=
  corec (fun s => head s) (fun s => tail (tail s)) s

def odd (s : Streamₓ α) : Streamₓ α :=
  even (tail s)

theorem odd_eq (s : Streamₓ α) : odd s = even (tail s) :=
  rfl

theorem head_even (s : Streamₓ α) : head (even s) = head s :=
  rfl

theorem tail_even (s : Streamₓ α) : tail (even s) = even (tail (tail s)) :=
  by 
    unfold even 
    rw [corec_eq]
    rfl

theorem even_cons_cons (a₁ a₂ : α) (s : Streamₓ α) : even (a₁ :: a₂ :: s) = a₁ :: even s :=
  by 
    unfold even 
    rw [corec_eq]
    rfl

theorem even_tail (s : Streamₓ α) : even (tail s) = odd s :=
  rfl

theorem even_interleave (s₁ s₂ : Streamₓ α) : even (s₁⋈s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁⋈s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ =>
      by 
        rw [h₁]
        constructor
        ·
          rfl
        ·
          exact
            ⟨tail s₂,
              by 
                rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.introₓ s₂ rfl)

theorem interleave_even_odd (s₁ : Streamₓ α) : even s₁⋈odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s⋈odd s)
    (fun s' s h : s' = even s⋈odd s =>
      by 
        rw [h]
        constructor
        ·
          rfl
        ·
          simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

theorem nth_even : ∀ n : Nat s : Streamₓ α, nth n (even s) = nth (2*n) s
| 0, s => rfl
| succ n, s =>
  by 
    change nth (succ n) (even s) = nth (succ (succ (2*n))) s 
    rw [nth_succ, nth_succ, tail_even, nth_even]
    rfl

theorem nth_odd : ∀ n : Nat s : Streamₓ α, nth n (odd s) = nth ((2*n)+1) s :=
  fun n s =>
    by 
      rw [odd_eq, nth_even]
      rfl

theorem mem_of_mem_even (a : α) (s : Streamₓ α) : a ∈ even s → a ∈ s :=
  fun ⟨n, h⟩ =>
    Exists.introₓ (2*n)
      (by 
        rw [h, nth_even])

theorem mem_of_mem_odd (a : α) (s : Streamₓ α) : a ∈ odd s → a ∈ s :=
  fun ⟨n, h⟩ =>
    Exists.introₓ ((2*n)+1)
      (by 
        rw [h, nth_odd])

def append_stream : List α → Streamₓ α → Streamₓ α
| [], s => s
| List.cons a l, s => a :: append_stream l s

theorem nil_append_stream (s : Streamₓ α) : append_stream [] s = s :=
  rfl

theorem cons_append_stream (a : α) (l : List α) (s : Streamₓ α) : append_stream (a :: l) s = a :: append_stream l s :=
  rfl

infixl:65 "++ₛ" => append_stream

theorem append_append_stream : ∀ l₁ l₂ : List α s : Streamₓ α, l₁ ++ l₂++ₛs = l₁++ₛ(l₂++ₛs)
| [], l₂, s => rfl
| List.cons a l₁, l₂, s =>
  by 
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream]

theorem map_append_stream (f : α → β) : ∀ l : List α s : Streamₓ α, map f (l++ₛs) = List.map f l++ₛmap f s
| [], s => rfl
| List.cons a l, s =>
  by 
    rw [cons_append_stream, List.map_consₓ, map_cons, cons_append_stream, map_append_stream]

theorem drop_append_stream : ∀ l : List α s : Streamₓ α, drop l.length (l++ₛs) = s
| [], s =>
  by 
    rfl
| List.cons a l, s =>
  by 
    rw [List.length_cons, add_one, drop_succ, cons_append_stream, tail_cons, drop_append_stream]

theorem append_stream_head_tail (s : Streamₓ α) : [head s]++ₛtail s = s :=
  by 
    rw [cons_append_stream, nil_append_stream, Streamₓ.eta]

theorem mem_append_stream_right : ∀ {a : α} l : List α {s : Streamₓ α}, a ∈ s → a ∈ l++ₛs
| a, [], s, h => h
| a, List.cons b l, s, h =>
  have ih : a ∈ l++ₛs := mem_append_stream_right l h 
  mem_cons_of_mem _ ih

theorem mem_append_stream_left : ∀ {a : α} {l : List α} s : Streamₓ α, a ∈ l → a ∈ l++ₛs
| a, [], s, h => absurd h (List.not_mem_nil _)
| a, List.cons b l, s, h =>
  Or.elim (List.eq_or_mem_of_mem_consₓ h) (fun aeqb : a = b => Exists.introₓ 0 aeqb)
    fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_stream_left s ainl)

def approx : Nat → Streamₓ α → List α
| 0, s => []
| n+1, s => List.cons (head s) (approx n (tail s))

theorem approx_zero (s : Streamₓ α) : approx 0 s = [] :=
  rfl

theorem approx_succ (n : Nat) (s : Streamₓ α) : approx (succ n) s = head s :: approx n (tail s) :=
  rfl

theorem nth_approx : ∀ n : Nat s : Streamₓ α, List.nth (approx (succ n) s) n = some (nth n s)
| 0, s => rfl
| n+1, s =>
  by 
    rw [approx_succ, add_one, List.nth, nth_approx]
    rfl

theorem append_approx_drop : ∀ n : Nat s : Streamₓ α, append_stream (approx n s) (drop n s) = s :=
  by 
    intro n 
    induction' n with n' ih
    ·
      intro s 
      rfl
    ·
      intro s 
      rw [approx_succ, drop_succ, cons_append_stream, ih (tail s), Streamₓ.eta]

theorem take_theorem (s₁ s₂ : Streamₓ α) : (∀ n : Nat, approx n s₁ = approx n s₂) → s₁ = s₂ :=
  by 
    intro h 
    apply Streamₓ.ext 
    intro n 
    induction' n with n ih
    ·
      have aux := h 1
      simp [approx] at aux 
      exact aux
    ·
      have h₁ : some (nth (succ n) s₁) = some (nth (succ n) s₂)
      ·
        rw [←nth_approx, ←nth_approx, h (succ (succ n))]
      injection h₁

private def cycle_f : α × List α × α × List α → α
| (v, _, _, _) => v

private def cycle_g : α × List α × α × List α → α × List α × α × List α
| (v₁, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
| (v₁, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

private theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
  cycle_g (a, a₁ :: l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl

def cycle : ∀ l : List α, l ≠ [] → Streamₓ α
| [], h => absurd rfl h
| List.cons a l, h => corec cycle_f cycle_g (a, l, a, l)

theorem cycle_eq : ∀ l : List α h : l ≠ [], cycle l h = l++ₛcycle l h
| [], h => absurd rfl h
| List.cons a l, h =>
  have gen : ∀ l' a', corec cycle_f cycle_g (a', l', a, l) = a' :: l'++ₛcorec cycle_f cycle_g (a, l, a, l) :=
    by 
      intro l' 
      induction' l' with a₁ l₁ ih
      ·
        intros 
        rw [corec_eq]
        rfl
      ·
        intros 
        rw [corec_eq, cycle_g_cons, ih a₁]
        rfl 
  gen l a

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h :=
  fun h ainl =>
    by 
      rw [cycle_eq]
      exact mem_append_stream_left _ ainl

theorem cycle_singleton (a : α) (h : [a] ≠ []) : cycle [a] h = const a :=
  coinduction rfl
    fun β fr ch =>
      by 
        rwa [cycle_eq, const_eq]

def tails (s : Streamₓ α) : Streamₓ (Streamₓ α) :=
  corec id tail (tail s)

theorem tails_eq (s : Streamₓ α) : tails s = tail s :: tails (tail s) :=
  by 
    unfold tails <;> rw [corec_eq] <;> rfl

theorem nth_tails : ∀ n : Nat s : Streamₓ α, nth n (tails s) = drop n (tail s) :=
  by 
    intro n 
    induction' n with n' ih
    ·
      intros 
      rfl
    ·
      intro s 
      rw [nth_succ, drop_succ, tails_eq, tail_cons, ih]

theorem tails_eq_iterate (s : Streamₓ α) : tails s = iterate tail (tail s) :=
  rfl

def inits_core (l : List α) (s : Streamₓ α) : Streamₓ (List α) :=
  corec_on (l, s) (fun ⟨a, b⟩ => a)
    fun p =>
      match p with 
      | (l', s') => (l' ++ [head s'], tail s')

def inits (s : Streamₓ α) : Streamₓ (List α) :=
  inits_core [head s] (tail s)

theorem inits_core_eq (l : List α) (s : Streamₓ α) : inits_core l s = l :: inits_core (l ++ [head s]) (tail s) :=
  by 
    unfold inits_core corec_on 
    rw [corec_eq]
    rfl

theorem tail_inits (s : Streamₓ α) : tail (inits s) = inits_core [head s, head (tail s)] (tail (tail s)) :=
  by 
    unfold inits 
    rw [inits_core_eq]
    rfl

theorem inits_tail (s : Streamₓ α) : inits (tail s) = inits_core [head (tail s)] (tail (tail s)) :=
  rfl

theorem cons_nth_inits_core :
  ∀ a : α n : Nat l : List α s : Streamₓ α, a :: nth n (inits_core l s) = nth n (inits_core (a :: l) s) :=
  by 
    intro a n 
    induction' n with n' ih
    ·
      intros 
      rfl
    ·
      intro l s 
      rw [nth_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a :: l) s]
      rfl

theorem nth_inits : ∀ n : Nat s : Streamₓ α, nth n (inits s) = approx (succ n) s :=
  by 
    intro n 
    induction' n with n' ih
    ·
      intros 
      rfl
    ·
      intros 
      rw [nth_succ, approx_succ, ←ih, tail_inits, inits_tail, cons_nth_inits_core]

theorem inits_eq (s : Streamₓ α) : inits s = [head s] :: map (List.cons (head s)) (inits (tail s)) :=
  by 
    apply Streamₓ.ext 
    intro n 
    cases n
    ·
      rfl
    ·
      rw [nth_inits, nth_succ, tail_cons, nth_map, nth_inits]
      rfl

theorem zip_inits_tails (s : Streamₓ α) : zip append_stream (inits s) (tails s) = const s :=
  by 
    apply Streamₓ.ext 
    intro n 
    rw [nth_zip, nth_inits, nth_tails, nth_const, approx_succ, cons_append_stream, append_approx_drop, Streamₓ.eta]

def pure (a : α) : Streamₓ α :=
  const a

def apply (f : Streamₓ (α → β)) (s : Streamₓ α) : Streamₓ β :=
  fun n => (nth n f) (nth n s)

infixl:75 "⊛" => apply

theorem identity (s : Streamₓ α) : pure id⊛s = s :=
  rfl

theorem composition (g : Streamₓ (β → δ)) (f : Streamₓ (α → β)) (s : Streamₓ α) : pure comp⊛g⊛f⊛s = g⊛(f⊛s) :=
  rfl

theorem homomorphism (f : α → β) (a : α) : pure f⊛pure a = pure (f a) :=
  rfl

theorem interchange (fs : Streamₓ (α → β)) (a : α) : fs⊛pure a = (pure fun f : α → β => f a)⊛fs :=
  rfl

theorem map_eq_apply (f : α → β) (s : Streamₓ α) : map f s = pure f⊛s :=
  rfl

def nats : Streamₓ Nat :=
  fun n => n

theorem nth_nats (n : Nat) : nth n nats = n :=
  rfl

theorem nats_eq : nats = 0 :: map succ nats :=
  by 
    apply Streamₓ.ext 
    intro n 
    cases n 
    rfl 
    rw [nth_succ]
    rfl

end Streamₓ

