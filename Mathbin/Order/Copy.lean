import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/


universe u

variable{α : Type u}

/-- A function to create a provable equal copy of a bounded lattice
with possibly different definitional equalities. -/
def BoundedLattice.copy (c : BoundedLattice α) (le : α → α → Prop) (eq_le : le = @BoundedLattice.Le α c) (top : α)
  (eq_top : top = @BoundedLattice.top α c) (bot : α) (eq_bot : bot = @BoundedLattice.bot α c) (sup : α → α → α)
  (eq_sup : sup = @BoundedLattice.sup α c) (inf : α → α → α) (eq_inf : inf = @BoundedLattice.inf α c) :
  BoundedLattice α :=
  by 
    refine' { le, top, bot, sup, inf, .. }
    all_goals 
      abstract 
        substVars 
        casesI c 
        assumption

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def DistribLattice.copy (c : DistribLattice α) (le : α → α → Prop) (eq_le : le = @DistribLattice.Le α c)
  (sup : α → α → α) (eq_sup : sup = @DistribLattice.sup α c) (inf : α → α → α)
  (eq_inf : inf = @DistribLattice.inf α c) : DistribLattice α :=
  by 
    refine' { le, sup, inf, .. }
    all_goals 
      abstract 
        substVars 
        casesI c 
        assumption

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def CompleteLattice.copy (c : CompleteLattice α) (le : α → α → Prop) (eq_le : le = @CompleteLattice.Le α c) (top : α)
  (eq_top : top = @CompleteLattice.top α c) (bot : α) (eq_bot : bot = @CompleteLattice.bot α c) (sup : α → α → α)
  (eq_sup : sup = @CompleteLattice.sup α c) (inf : α → α → α) (eq_inf : inf = @CompleteLattice.inf α c)
  (Sup : Set α → α) (eq_Sup : Sup = @CompleteLattice.supₓ α c) (Inf : Set α → α)
  (eq_Inf : Inf = @CompleteLattice.infₓ α c) : CompleteLattice α :=
  by 
    refine'
      { BoundedLattice.copy (@CompleteLattice.toBoundedLattice α c) le eq_le top eq_top bot eq_bot sup eq_sup inf
          eq_inf with
        le, top, bot, sup, inf, sup, inf, .. }
    all_goals 
      abstract 
        substVars 
        casesI c 
        assumption

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α) (le : α → α → Prop)
  (eq_le : le = @CompleteDistribLattice.Le α c) (top : α) (eq_top : top = @CompleteDistribLattice.top α c) (bot : α)
  (eq_bot : bot = @CompleteDistribLattice.bot α c) (sup : α → α → α) (eq_sup : sup = @CompleteDistribLattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @CompleteDistribLattice.inf α c) (Sup : Set α → α)
  (eq_Sup : Sup = @CompleteDistribLattice.supₓ α c) (Inf : Set α → α)
  (eq_Inf : Inf = @CompleteDistribLattice.infₓ α c) : CompleteDistribLattice α :=
  by 
    refine'
      { CompleteLattice.copy (@CompleteDistribLattice.toCompleteLattice α c) le eq_le top eq_top bot eq_bot sup eq_sup
          inf eq_inf Sup eq_Sup Inf eq_Inf with
        le, top, bot, sup, inf, sup, inf, .. }
    all_goals 
      abstract 
        substVars 
        casesI c 
        assumption

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α) (le : α → α → Prop)
  (eq_le : le = @ConditionallyCompleteLattice.Le α c) (sup : α → α → α)
  (eq_sup : sup = @ConditionallyCompleteLattice.sup α c) (inf : α → α → α)
  (eq_inf : inf = @ConditionallyCompleteLattice.inf α c) (Sup : Set α → α)
  (eq_Sup : Sup = @ConditionallyCompleteLattice.supₓ α c) (Inf : Set α → α)
  (eq_Inf : Inf = @ConditionallyCompleteLattice.infₓ α c) : ConditionallyCompleteLattice α :=
  by 
    refine' { le, sup, inf, sup, inf, .. }
    all_goals 
      abstract 
        substVars 
        casesI c 
        assumption

