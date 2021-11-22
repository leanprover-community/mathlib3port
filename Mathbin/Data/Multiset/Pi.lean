import Mathbin.Data.Multiset.Nodup

/-!
# The cartesian product of multisets
-/


namespace Multiset

section Pi

variable{α : Type _}

open Function

/-- Given `δ : α → Type*`, `pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def pi.empty (δ : α → Type _) : ∀ a _ : a ∈ (0 : Multiset α), δ a :=
  fun.

variable[DecidableEq α]{δ : α → Type _}

/-- Given `δ : α → Type*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def pi.cons (m : Multiset α) (a : α) (b : δ a) (f : ∀ a _ : a ∈ m, δ a) : ∀ a' _ : a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a'$ (mem_cons.1 ha').resolve_left h

theorem pi.cons_same {m : Multiset α} {a : α} {b : δ a} {f : ∀ a _ : a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
  pi.cons m a b f a h = b :=
  dif_pos rfl

theorem pi.cons_ne {m : Multiset α} {a a' : α} {b : δ a} {f : ∀ a _ : a ∈ m, δ a} (h' : a' ∈ a ::ₘ m) (h : a' ≠ a) :
  pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h

theorem pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a _ : a ∈ m, δ a} (h : a ≠ a') :
  HEq (pi.cons (a' ::ₘ m) a b (pi.cons m a' b' f)) (pi.cons (a ::ₘ m) a' b' (pi.cons m a b f)) :=
  by 
    apply hfunext
    ·
      rfl 
    intro a'' _ h 
    subst h 
    apply hfunext
    ·
      rw [cons_swap]
    intro ha₁ ha₂ h 
    byCases' h₁ : a'' = a <;> byCases' h₂ : a'' = a' <;> simp_all [pi.cons_same, pi.cons_ne]
    ·
      subst h₁ 
      rw [pi.cons_same, pi.cons_same]
    ·
      subst h₂ 
      rw [pi.cons_same, pi.cons_same]

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (δ a)) : Multiset (∀ a _ : a ∈ m, δ a) :=
  m.rec_on {pi.empty δ} (fun a m p : Multiset (∀ a _ : a ∈ m, δ a) => (t a).bind$ fun b => p.map$ pi.cons m a b)
    (by 
      intro a a' m n 
      byCases' eq : a = a'
      ·
        subst eq
      ·
        simp [map_bind, bind_bind (t a') (t a)]
        apply bind_hcongr
        ·
          rw [cons_swap a a']
        intro b hb 
        apply bind_hcongr
        ·
          rw [cons_swap a a']
        intro b' hb' 
        apply map_hcongr
        ·
          rw [cons_swap a a']
        intro f hf 
        exact pi.cons_swap Eq)

@[simp]
theorem pi_zero (t : ∀ a, Multiset (δ a)) : pi 0 t = {pi.empty δ} :=
  rfl

@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (δ a)) (a : α) :
  pi (a ::ₘ m) t = ((t a).bind$ fun b => (pi m t).map$ pi.cons m a b) :=
  rec_on_cons a m

theorem pi_cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) : Function.Injective (pi.cons s a b) :=
  fun f₁ f₂ eq =>
    funext$
      fun a' =>
        funext$
          fun h' =>
            have ne : a ≠ a' := fun h => hs$ h.symm ▸ h' 
            have  : a' ∈ a ::ₘ s := mem_cons_of_mem h' 
            calc f₁ a' h' = pi.cons s a b f₁ a' this :=
              by 
                rw [pi.cons_ne this Ne.symm]
              _ = pi.cons s a b f₂ a' this :=
              by 
                rw [Eq]
              _ = f₂ a' h' :=
              by 
                rw [pi.cons_ne this Ne.symm]
              

-- error in Data.Multiset.Pi: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_pi
(m : multiset α)
(t : ∀ a, multiset (δ a)) : «expr = »(card (pi m t), prod «expr $ »(m.map, λ a, card (t a))) :=
multiset.induction_on m (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr mul_comm, "]"] [] [] { contextual := tt })

theorem nodup_pi {s : Multiset α} {t : ∀ a, Multiset (δ a)} : nodup s → (∀ a _ : a ∈ s, nodup (t a)) → nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by 
      intro a s ih hs ht 
      have has : a ∉ s
      ·
        simp  at hs <;> exact hs.1
      have hs : nodup s
      ·
        simp  at hs <;> exact hs.2
      simp 
      split 
      ·
        intro b hb 
        exact nodup_map (pi_cons_injective has) (ih hs$ fun a' h' => ht a'$ mem_cons_of_mem h')
      ·
        apply pairwise_of_nodup _ (ht a$ mem_cons_self _ _)
        exact
          fun b₁ hb₁ b₂ hb₂ neb =>
            disjoint_map_map.2
              fun f hf g hg eq =>
                have  : pi.cons s a b₁ f a (mem_cons_self _ _) = pi.cons s a b₂ g a (mem_cons_self _ _) :=
                  by 
                    rw [Eq]
                neb$
                  show b₁ = b₂ by 
                    rwa [pi.cons_same, pi.cons_same] at this)

theorem mem_pi (m : Multiset α) (t : ∀ a, Multiset (δ a)) :
  ∀ f : ∀ a _ : a ∈ m, δ a, f ∈ pi m t ↔ ∀ a h : a ∈ m, f a h ∈ t a :=
  by 
    refine' Multiset.induction_on m (fun f => _) fun a m ih f => _
    ·
      simpa using
        show f = pi.empty δ by 
          funext a ha <;> exact ha.elim 
    simp only [mem_bind, exists_prop, mem_cons, pi_cons, mem_map]
    split 
    ·
      rintro ⟨b, hb, f', hf', rfl⟩ a' ha' 
      rw [ih] at hf' 
      byCases' a' = a
      ·
        subst h 
        rwa [pi.cons_same]
      ·
        rw [pi.cons_ne _ h]
        apply hf'
    ·
      intro hf 
      refine' ⟨_, hf a (mem_cons_self a _), fun a ha => f a (mem_cons_of_mem ha), (ih _).2 fun a' h' => hf _ _, _⟩
      funext a' h' 
      byCases' a' = a
      ·
        subst h 
        rw [pi.cons_same]
      ·
        rw [pi.cons_ne _ h]

end Pi

end Multiset

