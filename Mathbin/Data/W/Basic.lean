import Mathbin.Data.Equiv.List

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `W_type β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `W_type` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/


/--
Given `β : α → Type*`, `W_type β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
inductive WType {α : Type _} (β : α → Type _)
  | mk (a : α) (f : β a → WType) : WType

instance : Inhabited (WType fun _ : Unit => Empty) :=
  ⟨WType.mk Unit.star Empty.elimₓ⟩

namespace WType

variable {α : Type _} {β : α → Type _}

/-- The canonical map to the corresponding sigma type, returning the label of a node as an
  element `a` of `α`, and the children of the node as a function `β a → W_type β`. -/
def to_sigma : WType β → Σa : α, β a → WType β
| ⟨a, f⟩ => ⟨a, f⟩

/-- The canonical map from the sigma type into a `W_type`. Given a node `a : α`, and
  its children as a function `β a → W_type β`, return the corresponding tree. -/
def of_sigma : (Σa : α, β a → WType β) → WType β
| ⟨a, f⟩ => WType.mk a f

@[simp]
theorem of_sigma_to_sigma : ∀ w : WType β, of_sigma (to_sigma w) = w
| ⟨a, f⟩ => rfl

@[simp]
theorem to_sigma_of_sigma : ∀ s : Σa : α, β a → WType β, to_sigma (of_sigma s) = s
| ⟨a, f⟩ => rfl

variable (β)

/-- The canonical bijection with the sigma type, showing that `W_type` is a fixed point of
  the polynomial `Σ a : α, β a → W_type β`.  -/
@[simps]
def equiv_sigma : WType β ≃ Σa : α, β a → WType β :=
  { toFun := to_sigma, invFun := of_sigma, left_inv := of_sigma_to_sigma, right_inv := to_sigma_of_sigma }

variable {β}

/-- The canonical map from `W_type β` into any type `γ` given a map `(Σ a : α, β a → γ) → γ`. -/
def elim (γ : Type _) (fγ : (Σa : α, β a → γ) → γ) : WType β → γ
| ⟨a, f⟩ => fγ ⟨a, fun b => elim (f b)⟩

theorem elim_injective (γ : Type _) (fγ : (Σa : α, β a → γ) → γ) (fγ_injective : Function.Injective fγ) :
  Function.Injective (elim γ fγ)
| ⟨a₁, f₁⟩, ⟨a₂, f₂⟩, h =>
  by 
    obtain ⟨rfl, h⟩ := Sigma.mk.inj (fγ_injective h)
    congr with x 
    exact elim_injective (congr_funₓ (eq_of_heq h) x : _)

instance [hα : IsEmpty α] : IsEmpty (WType β) :=
  ⟨fun w => WType.recOn w (IsEmpty.elim hα)⟩

-- error in Data.W.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem infinite_of_nonempty_of_is_empty (a b : α) [ha : nonempty (β a)] [he : is_empty (β b)] : infinite (W_type β) :=
⟨begin
   introsI [ident hf],
   have [ident hba] [":", expr «expr ≠ »(b, a)] [],
   from [expr λ h, ha.elim (is_empty.elim' (show is_empty (β a), from «expr ▸ »(h, he)))],
   refine [expr not_injective_infinite_fintype (λ
     n : exprℕ(), show W_type β, from nat.rec_on n ⟨b, is_empty.elim' he⟩ (λ n ih, ⟨a, λ _, ih⟩)) _],
   intros [ident n, ident m, ident h],
   induction [expr n] [] ["with", ident n, ident ih] ["generalizing", ident m, ident h],
   { cases [expr m] ["with", ident m]; simp [] [] [] ["*"] [] ["at", "*"] },
   { cases [expr m] ["with", ident m],
     { simp [] [] [] ["*"] [] ["at", "*"] },
     { refine [expr congr_arg nat.succ (ih _)],
       simp [] [] [] ["[", expr function.funext_iff, ",", "*", "]"] [] ["at", "*"] } }
 end⟩

variable [∀ a : α, Fintype (β a)]

/-- The depth of a finitely branching tree. -/
def depth : WType β → ℕ
| ⟨a, f⟩ => (Finset.sup Finset.univ fun n => depth (f n))+1

theorem depth_pos (t : WType β) : 0 < t.depth :=
  by 
    cases t 
    apply Nat.succ_posₓ

theorem depth_lt_depth_mk (a : α) (f : β a → WType β) (i : β a) : depth (f i) < depth ⟨a, f⟩ :=
  Nat.lt_succ_of_leₓ (Finset.le_sup (Finset.mem_univ i))

end WType

namespace Encodable

@[reducible]
private def W_type' {α : Type _} (β : α → Type _) [∀ a : α, Fintype (β a)] [∀ a : α, Encodable (β a)] (n : ℕ) :=
  { t : WType β // t.depth ≤ n }

variable {α : Type _} {β : α → Type _} [∀ a : α, Fintype (β a)] [∀ a : α, Encodable (β a)]

private def encodable_zero : Encodable (W_type' β 0) :=
  let f : W_type' β 0 → Empty := fun ⟨x, h⟩ => False.elim$ not_lt_of_geₓ h (WType.depth_pos _)
  let finv : Empty → W_type' β 0 :=
    by 
      intro x 
      cases x 
  have  : ∀ x, finv (f x) = x := fun ⟨x, h⟩ => False.elim$ not_lt_of_geₓ h (WType.depth_pos _)
  Encodable.ofLeftInverse f finv this

-- error in Data.W.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private def f (n : exprℕ()) : W_type' β «expr + »(n, 1) → «exprΣ , »((a : α), β a → W_type' β n)
| ⟨t, h⟩ := begin
  cases [expr t] ["with", ident a, ident f],
  have [ident h₀] [":", expr ∀ i : β a, «expr ≤ »(W_type.depth (f i), n)] [],
  from [expr λ i, nat.le_of_lt_succ (lt_of_lt_of_le (W_type.depth_lt_depth_mk a f i) h)],
  exact [expr ⟨a, λ i : β a, ⟨f i, h₀ i⟩⟩]
end

private def finv (n : ℕ) : (Σa : α, β a → W_type' β n) → W_type' β (n+1)
| ⟨a, f⟩ =>
  let f' := fun i : β a => (f i).val 
  have  : WType.depth ⟨a, f'⟩ ≤ n+1 := add_le_add_right (Finset.sup_le fun b h => (f b).2) 1
  ⟨⟨a, f'⟩, this⟩

variable [Encodable α]

private def encodable_succ (n : Nat) (h : Encodable (W_type' β n)) : Encodable (W_type' β (n+1)) :=
  Encodable.ofLeftInverse (f n) (finv n)
    (by 
      rintro ⟨⟨_, _⟩, _⟩
      rfl)

-- error in Data.W.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `W_type` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/ instance : encodable (W_type β) :=
begin
  haveI [ident h'] [":", expr ∀
   n, encodable (W_type' β n)] [":=", expr λ n, nat.rec_on n encodable_zero encodable_succ],
  let [ident f] [":", expr W_type β → «exprΣ , »((n), W_type' β n)] [":=", expr λ t, ⟨t.depth, ⟨t, le_refl _⟩⟩],
  let [ident finv] [":", expr «exprΣ , »((n), W_type' β n) → W_type β] [":=", expr λ p, p.2.1],
  have [] [":", expr ∀ t, «expr = »(finv (f t), t)] [],
  from [expr λ t, rfl],
  exact [expr encodable.of_left_inverse f finv this]
end

end Encodable

