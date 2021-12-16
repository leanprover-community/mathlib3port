import Mathbin.Order.Filter.Basic 
import Mathbin.Algebra.Module.Pi

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : filter α` is the equivalence class of `f`
with respect to the equivalence relation `eventually_eq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `germ l β` to be the space of germs of functions `α → β` at a filter `l : filter α`;
* coercion from `α → β` to `germ l β`: `(f : germ l β)` is the germ of `f : α → β`
  at `l : filter α`; this coercion is declared as `has_coe_t`, so it does not require an explicit
  up arrow `↑`;
* coercion from `β` to `germ l β`: `(↑c : germ l β)` is the germ of the constant function
  `λ x:α, c` at a filter `l`; this coercion is declared as `has_lift_t`, so it requires an explicit
  up arrow `↑`, see [TPiL][TPiL_coe] for details.
* `map (F : β → γ) (f : germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : germ l β) (g : germ l γ)` to be the germ of `λ x, F (f x) (g x)`
  at `l`;
* `f.tendsto lb`: we say that a germ `f : germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.comp_tendsto g hg` and `f.comp_tendsto' g hg`: given `f : germ l β` and a function
  `g : γ → α` (resp., a germ `g : germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `germ.lift_pred`, `germ.lift_rel`: lift a predicate or a relation to the space of germs:
  `(f : germ l β).lift_pred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.
[TPiL_coe]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

We also define `map (F : β → γ) : germ l β → germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`germ l β`:

* one-operation algebraic structures up to `comm_group`;
* `mul_zero_class`, `distrib`, `semiring`, `comm_semiring`, `ring`, `comm_ring`;
* `mul_action`, `distrib_mul_action`, `module`;
* `preorder`, `partial_order`, and `lattice` structures, as well as `bounded_order`;
* `ordered_cancel_comm_monoid` and `ordered_cancel_add_comm_monoid`.

## Tags

filter, germ
-/


namespace Filter

variable {α β γ δ : Type _} {l : Filter α} {f g h : α → β}

theorem const_eventually_eq' [ne_bot l] {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
  eventually_const

theorem const_eventually_eq [ne_bot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventually_eq' _ _ _ _ a b

theorem eventually_eq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ} (hg : tendsto g lc l) :
  f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H

/-- Setoid used to define the space of germs. -/
def germ_setoid (l : Filter α) (β : Type _) : Setoidₓ (α → β) :=
  { R := eventually_eq l,
    iseqv := ⟨eventually_eq.refl _, fun _ _ => eventually_eq.symm, fun _ _ _ => eventually_eq.trans⟩ }

/-- The space of germs of functions `α → β` at a filter `l`. -/
def germ (l : Filter α) (β : Type _) : Type _ :=
  Quotientₓ (germ_setoid l β)

namespace Germ

instance : CoeTₓ (α → β) (germ l β) :=
  ⟨Quotientₓ.mk'⟩

instance : HasLiftT β (germ l β) :=
  ⟨fun c => ↑fun x : α => c⟩

@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : germ l β) :=
  rfl

@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) : Quotientₓ.mk' f = (f : germ l β) :=
  rfl

@[elab_as_eliminator]
theorem induction_on (f : germ l β) {p : germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotientₓ.induction_on' f h

@[elab_as_eliminator]
theorem induction_on₂ (f : germ l β) (g : germ l γ) {p : germ l β → germ l γ → Prop}
  (h : ∀ f : α → β g : α → γ, p f g) : p f g :=
  Quotientₓ.induction_on₂' f g h

@[elab_as_eliminator]
theorem induction_on₃ (f : germ l β) (g : germ l γ) (h : germ l δ) {p : germ l β → germ l γ → germ l δ → Prop}
  (H : ∀ f : α → β g : α → γ h : α → δ, p f g h) : p f g h :=
  Quotientₓ.induction_on₃' f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `germ l β` to `germ lc δ`. -/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.eventually_eq⇒lc.eventually_eq) F F) : germ l β → germ lc δ :=
  Quotientₓ.map' F hF

/-- Given a germ `f : germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def lift_on {γ : Sort _} (f : germ l β) (F : (α → β) → γ) (hF : (l.eventually_eq⇒· = ·) F F) : γ :=
  Quotientₓ.liftOn' f F hF

@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.eventually_eq⇒lc.eventually_eq) F F) (f : α → β) :
  map' F hF f = F f :=
  rfl

@[simp, normCast]
theorem coe_eq : (f : germ l β) = g ↔ f =ᶠ[l] g :=
  Quotientₓ.eq'

alias coe_eq ↔ _ Filter.EventuallyEq.germ_eq

/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map (op : β → γ) : germ l β → germ l γ :=
  map' ((· ∘ ·) op)$ fun f g H => H.mono$ fun x H => congr_argₓ op H

@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : germ l β) = op ∘ f :=
  rfl

@[simp]
theorem map_id : map id = (id : germ l β → germ l β) :=
  by 
    ext ⟨f⟩
    rfl

theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : germ l β) : map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  induction_on f$ fun f => rfl

/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ (op : β → γ → δ) : germ l β → germ l γ → germ l δ :=
  (Quotientₓ.map₂' fun f g x => op (f x) (g x))$
    fun f f' Hf g g' Hg =>
      Hg.mp$
        Hf.mono$
          fun x Hf Hg =>
            by 
              simp only [Hf, Hg]

@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) : map₂ op (f : germ l β) g = fun x => op (f x) (g x) :=
  rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def tendsto (f : germ l β) (lb : Filter β) : Prop :=
  (lift_on f fun f => tendsto f l lb)$ fun f g H => propext (tendsto_congr' H)

@[simp, normCast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : germ l β).Tendsto lb ↔ tendsto f l lb :=
  Iff.rfl

alias coe_tendsto ↔ _ Filter.Tendsto.germ_tendsto

/-- Given two germs `f : germ l β`, and `g : germ lc α`, where `l : filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto' (f : germ l β) {lc : Filter γ} (g : germ lc α) (hg : g.tendsto l) : germ lc β :=
  (lift_on f fun f => g.map f)$ fun f₁ f₂ hF => (induction_on g$ fun g hg => coe_eq.2$ hg.eventually hF) hg

@[simp]
theorem coe_comp_tendsto' (f : α → β) {lc : Filter γ} {g : germ lc α} (hg : g.tendsto l) :
  (f : germ l β).compTendsto' g hg = g.map f :=
  rfl

/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto (f : germ l β) {lc : Filter γ} (g : γ → α) (hg : tendsto g lc l) : germ lc β :=
  f.comp_tendsto' _ hg.germ_tendsto

@[simp]
theorem coe_comp_tendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : tendsto g lc l) :
  (f : germ l β).comp_tendsto g hg = f ∘ g :=
  rfl

@[simp]
theorem comp_tendsto'_coe (f : germ l β) {lc : Filter γ} {g : γ → α} (hg : tendsto g lc l) :
  f.comp_tendsto' _ hg.germ_tendsto = f.comp_tendsto g hg :=
  rfl

@[simp, normCast]
theorem const_inj [ne_bot l] {a b : β} : (↑a : germ l β) = ↑b ↔ a = b :=
  coe_eq.trans$ const_eventually_eq

@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : germ l β).map f = ↑f a :=
  rfl

@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) : map₂ f (↑b : germ l β) (↑c) = ↑f b c :=
  rfl

@[simp]
theorem const_comp_tendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : tendsto g lc l) :
  (↑b : germ l β).comp_tendsto g hg = ↑b :=
  rfl

@[simp]
theorem const_comp_tendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : germ lc α} (hg : g.tendsto l) :
  (↑b : germ l β).compTendsto' g hg = ↑b :=
  induction_on g (fun _ _ => rfl) hg

/-- Lift a predicate on `β` to `germ l β`. -/
def lift_pred (p : β → Prop) (f : germ l β) : Prop :=
  (lift_on f fun f => ∀ᶠ x in l, p (f x))$ fun f g H => propext$ eventually_congr$ H.mono$ fun x hx => hx ▸ Iff.rfl

@[simp]
theorem lift_pred_coe {p : β → Prop} {f : α → β} : lift_pred p (f : germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl

theorem lift_pred_const {p : β → Prop} {x : β} (hx : p x) : lift_pred p (↑x : germ l β) :=
  eventually_of_forall$ fun y => hx

@[simp]
theorem lift_pred_const_iff [ne_bot l] {p : β → Prop} {x : β} : lift_pred p (↑x : germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)

/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def lift_rel (r : β → γ → Prop) (f : germ l β) (g : germ l γ) : Prop :=
  (Quotientₓ.liftOn₂' f g fun f g => ∀ᶠ x in l, r (f x) (g x))$
    fun f g f' g' Hf Hg => propext$ eventually_congr$ Hg.mp$ Hf.mono$ fun x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]
theorem lift_rel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
  lift_rel r (f : germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl

theorem lift_rel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) : lift_rel r (↑x : germ l β) (↑y) :=
  eventually_of_forall$ fun _ => h

@[simp]
theorem lift_rel_const_iff [ne_bot l] {r : β → γ → Prop} {x : β} {y : γ} : lift_rel r (↑x : germ l β) (↑y) ↔ r x y :=
  @eventually_const _ _ _ (r x y)

instance [Inhabited β] : Inhabited (germ l β) :=
  ⟨↑default β⟩

section Monoidₓ

variable {M : Type _} {G : Type _}

@[toAdditive]
instance [Mul M] : Mul (germ l M) :=
  ⟨map₂ (·*·)⟩

@[simp, normCast, toAdditive]
theorem coe_mul [Mul M] (f g : α → M) : (↑f*g) = (f*g : germ l M) :=
  rfl

@[toAdditive]
instance [HasOne M] : HasOne (germ l M) :=
  ⟨↑(1 : M)⟩

@[simp, normCast, toAdditive]
theorem coe_one [HasOne M] : ↑(1 : α → M) = (1 : germ l M) :=
  rfl

@[toAdditive]
instance [Semigroupₓ M] : Semigroupₓ (germ l M) :=
  { mul := ·*·,
    mul_assoc :=
      by 
        rintro ⟨f⟩ ⟨g⟩ ⟨h⟩
        simp only [mul_assocₓ, quot_mk_eq_coe, ←coe_mul] }

@[toAdditive]
instance [CommSemigroupₓ M] : CommSemigroupₓ (germ l M) :=
  { germ.semigroup with mul := ·*·,
    mul_comm :=
      by 
        rintro ⟨f⟩ ⟨g⟩
        simp only [mul_commₓ, quot_mk_eq_coe, ←coe_mul] }

@[toAdditive AddLeftCancelSemigroup]
instance [LeftCancelSemigroup M] : LeftCancelSemigroup (germ l M) :=
  { germ.semigroup with mul := ·*·,
    mul_left_cancel :=
      fun f₁ f₂ f₃ =>
        induction_on₃ f₁ f₂ f₃$ fun f₁ f₂ f₃ H => coe_eq.2 ((coe_eq.1 H).mono$ fun x => mul_left_cancelₓ) }

@[toAdditive AddRightCancelSemigroup]
instance [RightCancelSemigroup M] : RightCancelSemigroup (germ l M) :=
  { germ.semigroup with mul := ·*·,
    mul_right_cancel :=
      fun f₁ f₂ f₃ =>
        induction_on₃ f₁ f₂ f₃$ fun f₁ f₂ f₃ H => coe_eq.2$ (coe_eq.1 H).mono$ fun x => mul_right_cancelₓ }

@[toAdditive]
instance [Monoidₓ M] : Monoidₓ (germ l M) :=
  { germ.semigroup with mul := ·*·, one := 1,
    one_mul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              rw [one_mulₓ],
    mul_one :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              rw [mul_oneₓ] }

/-- coercion from functions to germs as a monoid homomorphism. -/
@[toAdditive]
def coe_mul_hom [Monoidₓ M] (l : Filter α) : (α → M) →* germ l M :=
  ⟨coeₓ, rfl, fun f g => rfl⟩

/-- coercion from functions to germs as an additive monoid homomorphism. -/
add_decl_doc coe_add_hom

@[simp, toAdditive]
theorem coe_coe_mul_hom [Monoidₓ M] : (coe_mul_hom l : (α → M) → germ l M) = coeₓ :=
  rfl

@[toAdditive]
instance [CommMonoidₓ M] : CommMonoidₓ (germ l M) :=
  { germ.comm_semigroup, germ.monoid with mul := ·*·, one := 1 }

@[toAdditive]
instance [HasInv G] : HasInv (germ l G) :=
  ⟨map HasInv.inv⟩

@[simp, normCast, toAdditive]
theorem coe_inv [HasInv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : germ l G) :=
  rfl

@[toAdditive]
instance [Div M] : Div (germ l M) :=
  ⟨map₂ (· / ·)⟩

@[simp, normCast, toAdditive]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : germ l M) :=
  rfl

@[toAdditive]
instance [DivInvMonoidₓ G] : DivInvMonoidₓ (germ l G) :=
  { germ.monoid with inv := HasInv.inv, div := Div.div,
    div_eq_mul_inv :=
      by 
        rintro ⟨f⟩ ⟨g⟩
        exact congr_argₓ (Quot.mk _) (div_eq_mul_inv f g) }

@[toAdditive]
instance [Groupₓ G] : Groupₓ (germ l G) :=
  { germ.div_inv_monoid with mul := ·*·, one := 1,
    mul_left_inv :=
      by 
        rintro ⟨f⟩
        exact congr_argₓ (Quot.mk _) (mul_left_invₓ f) }

@[toAdditive]
instance [CommGroupₓ G] : CommGroupₓ (germ l G) :=
  { germ.group, germ.comm_monoid with mul := ·*·, one := 1, inv := HasInv.inv }

end Monoidₓ

section Ringₓ

variable {R : Type _}

instance Nontrivial [Nontrivial R] [ne_bot l] : Nontrivial (germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

instance [MulZeroClass R] : MulZeroClass (germ l R) :=
  { zero := 0, mul := ·*·,
    mul_zero :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              rw [mul_zero],
    zero_mul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              rw [zero_mul] }

instance [Distrib R] : Distrib (germ l R) :=
  { mul := ·*·, add := ·+·,
    left_distrib :=
      fun f g h =>
        induction_on₃ f g h$
          fun f g h =>
            by 
              normCast 
              rw [left_distrib],
    right_distrib :=
      fun f g h =>
        induction_on₃ f g h$
          fun f g h =>
            by 
              normCast 
              rw [right_distrib] }

instance [Semiringₓ R] : Semiringₓ (germ l R) :=
  { germ.add_comm_monoid, germ.monoid, germ.distrib, germ.mul_zero_class with  }

/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coe_ring_hom [Semiringₓ R] (l : Filter α) : (α → R) →+* germ l R :=
  { (coe_mul_hom l : _ →* germ l R), (coe_add_hom l : _ →+ germ l R) with toFun := coeₓ }

@[simp]
theorem coe_coe_ring_hom [Semiringₓ R] : (coe_ring_hom l : (α → R) → germ l R) = coeₓ :=
  rfl

instance [Ringₓ R] : Ringₓ (germ l R) :=
  { germ.add_comm_group, germ.monoid, germ.distrib, germ.mul_zero_class with  }

instance [CommSemiringₓ R] : CommSemiringₓ (germ l R) :=
  { germ.semiring, germ.comm_monoid with  }

instance [CommRingₓ R] : CommRingₓ (germ l R) :=
  { germ.ring, germ.comm_monoid with  }

end Ringₓ

section Module

variable {M N R : Type _}

instance [HasScalar M β] : HasScalar M (germ l β) :=
  ⟨fun c => map ((· • ·) c)⟩

instance has_scalar' [HasScalar M β] : HasScalar (germ l M) (germ l β) :=
  ⟨map₂ (· • ·)⟩

@[simp, normCast]
theorem coe_smul [HasScalar M β] (c : M) (f : α → β) : ↑(c • f) = (c • f : germ l β) :=
  rfl

@[simp, normCast]
theorem coe_smul' [HasScalar M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : germ l M) • (f : germ l β) :=
  rfl

instance [Monoidₓ M] [MulAction M β] : MulAction M (germ l β) :=
  { one_smul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              simp only [one_smul],
    mul_smul :=
      fun c₁ c₂ f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              simp only [mul_smul] }

instance mul_action' [Monoidₓ M] [MulAction M β] : MulAction (germ l M) (germ l β) :=
  { one_smul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              simp only [←coe_one, ←coe_smul', one_smul],
    mul_smul :=
      fun c₁ c₂ f =>
        induction_on₃ c₁ c₂ f$
          fun c₁ c₂ f =>
            by 
              normCast 
              simp only [mul_smul] }

instance [Monoidₓ M] [AddMonoidₓ N] [DistribMulAction M N] : DistribMulAction M (germ l N) :=
  { smul_add :=
      fun c f g =>
        induction_on₂ f g$
          fun f g =>
            by 
              normCast 
              simp only [smul_add],
    smul_zero :=
      fun c =>
        by 
          simp only [←coe_zero, ←coe_smul, smul_zero] }

instance distrib_mul_action' [Monoidₓ M] [AddMonoidₓ N] [DistribMulAction M N] :
  DistribMulAction (germ l M) (germ l N) :=
  { smul_add :=
      fun c f g =>
        induction_on₃ c f g$
          fun c f g =>
            by 
              normCast 
              simp only [smul_add],
    smul_zero :=
      fun c =>
        induction_on c$
          fun c =>
            by 
              simp only [←coe_zero, ←coe_smul', smul_zero] }

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (germ l M) :=
  { add_smul :=
      fun c₁ c₂ f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              simp only [add_smul],
    zero_smul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              normCast 
              simp only [zero_smul, coe_zero] }

instance module' [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module (germ l R) (germ l M) :=
  { add_smul :=
      fun c₁ c₂ f =>
        induction_on₃ c₁ c₂ f$
          fun c₁ c₂ f =>
            by 
              normCast 
              simp only [add_smul],
    zero_smul :=
      fun f =>
        induction_on f$
          fun f =>
            by 
              simp only [←coe_zero, ←coe_smul', zero_smul] }

end Module

instance [LE β] : LE (germ l β) :=
  ⟨lift_rel (· ≤ ·)⟩

@[simp]
theorem coe_le [LE β] : (f : germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl

theorem le_def [LE β] : (· ≤ · : germ l β → germ l β → Prop) = lift_rel (· ≤ ·) :=
  rfl

theorem const_le [LE β] {x y : β} (h : x ≤ y) : (↑x : germ l β) ≤ ↑y :=
  lift_rel_const h

@[simp, normCast]
theorem const_le_iff [LE β] [ne_bot l] {x y : β} : (↑x : germ l β) ≤ ↑y ↔ x ≤ y :=
  lift_rel_const_iff

instance [Preorderₓ β] : Preorderₓ (germ l β) :=
  { le := · ≤ ·, le_refl := fun f => induction_on f$ eventually_le.refl l,
    le_trans := fun f₁ f₂ f₃ => induction_on₃ f₁ f₂ f₃$ fun f₁ f₂ f₃ => eventually_le.trans }

instance [PartialOrderₓ β] : PartialOrderₓ (germ l β) :=
  { germ.preorder with le := · ≤ ·,
    le_antisymm := fun f g => induction_on₂ f g$ fun f g h₁ h₂ => (eventually_le.antisymm h₁ h₂).germ_eq }

instance [HasBot β] : HasBot (germ l β) :=
  ⟨↑(⊥ : β)⟩

@[simp, normCast]
theorem const_bot [HasBot β] : (↑(⊥ : β) : germ l β) = ⊥ :=
  rfl

instance [LE β] [OrderBot β] : OrderBot (germ l β) :=
  { bot := ⊥, bot_le := fun f => induction_on f$ fun f => eventually_of_forall$ fun x => bot_le }

instance [HasTop β] : HasTop (germ l β) :=
  ⟨↑(⊤ : β)⟩

@[simp, normCast]
theorem const_top [HasTop β] : (↑(⊤ : β) : germ l β) = ⊤ :=
  rfl

instance [LE β] [OrderTop β] : OrderTop (germ l β) :=
  { top := ⊤, le_top := fun f => induction_on f$ fun f => eventually_of_forall$ fun x => le_top }

instance [HasSup β] : HasSup (germ l β) :=
  ⟨map₂ (·⊔·)⟩

@[simp, normCast]
theorem const_sup [HasSup β] (a b : β) : ↑(a⊔b) = (↑a⊔↑b : germ l β) :=
  rfl

instance [HasInf β] : HasInf (germ l β) :=
  ⟨map₂ (·⊓·)⟩

@[simp, normCast]
theorem const_inf [HasInf β] (a b : β) : ↑(a⊓b) = (↑a⊓↑b : germ l β) :=
  rfl

instance [SemilatticeSup β] : SemilatticeSup (germ l β) :=
  { germ.partial_order with sup := ·⊔·,
    le_sup_left := fun f g => induction_on₂ f g$ fun f g => eventually_of_forall$ fun x => le_sup_left,
    le_sup_right := fun f g => induction_on₂ f g$ fun f g => eventually_of_forall$ fun x => le_sup_right,
    sup_le := fun f₁ f₂ g => induction_on₃ f₁ f₂ g$ fun f₁ f₂ g h₁ h₂ => h₂.mp$ h₁.mono$ fun x => sup_le }

instance [SemilatticeInf β] : SemilatticeInf (germ l β) :=
  { germ.partial_order with inf := ·⊓·,
    inf_le_left := fun f g => induction_on₂ f g$ fun f g => eventually_of_forall$ fun x => inf_le_left,
    inf_le_right := fun f g => induction_on₂ f g$ fun f g => eventually_of_forall$ fun x => inf_le_right,
    le_inf := fun f₁ f₂ g => induction_on₃ f₁ f₂ g$ fun f₁ f₂ g h₁ h₂ => h₂.mp$ h₁.mono$ fun x => le_inf }

instance [Lattice β] : Lattice (germ l β) :=
  { germ.semilattice_sup, germ.semilattice_inf with  }

instance [LE β] [BoundedOrder β] : BoundedOrder (germ l β) :=
  { germ.order_bot, germ.order_top with  }

@[toAdditive]
instance [OrderedCancelCommMonoid β] : OrderedCancelCommMonoid (germ l β) :=
  { germ.partial_order, germ.comm_monoid, germ.left_cancel_semigroup with
    mul_le_mul_left :=
      fun f g => induction_on₂ f g$ fun f g H h => induction_on h$ fun h => H.mono$ fun x H => mul_le_mul_left' H _,
    le_of_mul_le_mul_left := fun f g h => induction_on₃ f g h$ fun f g h H => H.mono$ fun x => le_of_mul_le_mul_left' }

@[toAdditive]
instance OrderedCommGroup [OrderedCommGroup β] : OrderedCommGroup (germ l β) :=
  { germ.partial_order, germ.comm_group with
    mul_le_mul_left :=
      fun f g => induction_on₂ f g$ fun f g H h => induction_on h$ fun h => H.mono$ fun x H => mul_le_mul_left' H _ }

end Germ

end Filter

