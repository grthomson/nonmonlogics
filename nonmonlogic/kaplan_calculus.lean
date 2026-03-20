import Mathlib.Data.Multiset.Basic

namespace Syntax

universe u

/-! ## Atomic symbols and formulas -/

/--
Atomic proposition symbols.
This is still just a toy choice; later may prefer `String`, `Nat`,
or a parameter type of atoms.
-/
inductive Atomic : Type
| Int : Atomic
| String : Atomic
deriving DecidableEq, Repr

/--
Formulas of propositional logic with implication, conjunction,
disjunction, and negation.
-/
inductive MyProp : Type u
| atom : Atomic → MyProp
| imp  : MyProp → MyProp → MyProp
| conj : MyProp → MyProp → MyProp
| disj : MyProp → MyProp → MyProp
| neg  : MyProp → MyProp
deriving DecidableEq, Repr

infixr:60 " ⇒ " => MyProp.imp
infixr:55 " & " => MyProp.conj
infixr:50 " ∨ " => MyProp.disj
prefix:max "¬" => MyProp.neg

/-! ## Multi-succedent sequents -/

/--
A two-sided sequent with multiset antecedent and multiset succedent.
Using `Multiset` means order is irrelevant but multiplicity is retained.
-/
structure MultiSequent : Type u where
  lhs : Multiset MyProp
  rhs : Multiset MyProp
deriving DecidableEq

notation:55 Γ " ∣∼ " Δ => MultiSequent.mk Γ Δ

/-! ## Variables -/

variable {A B : MyProp}
variable {Γ Θ : Multiset MyProp}

/-!
`BaseRel` is the primitive defeasible / material consequence relation
that provides the leaves of proof trees.
-/
abbrev BaseRel := Multiset MyProp → Multiset MyProp → Prop

/--
`NMMS base s` means: `s` has a derivation in the nonmonotonic
multi-succedent sequent calculus generated from the base relation `base`.

Rules included here:

* base axiom from `base`
* left/right implication
* left/right conjunction
* left/right disjunction
* left/right negation
-/
inductive NMMS (base : BaseRel) : MultiSequent → Type u
| baseAx
    (h : base Γ Θ) :
    NMMS base (Γ ∣∼ Θ)

| imp_l
    (d₁ : NMMS base (Γ ∣∼ A ::ₘ Θ))
    (d₂ : NMMS base (B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A ⇒ B) ::ₘ Γ ∣∼ Θ)

| imp_r
    (d : NMMS base (A ::ₘ Γ ∣∼ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A ⇒ B) ::ₘ Θ)

| conj_l
    (d : NMMS base (A ::ₘ B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A & B) ::ₘ Γ ∣∼ Θ)

| conj_r
    (d₁ : NMMS base (Γ ∣∼ A ::ₘ Θ))
    (d₂ : NMMS base (Γ ∣∼ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A & B) ::ₘ Θ)

| disj_l
    (d₁ : NMMS base (A ::ₘ Γ ∣∼ Θ))
    (d₂ : NMMS base (B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A ∨ B) ::ₘ Γ ∣∼ Θ)

| disj_r
    (d : NMMS base (Γ ∣∼ A ::ₘ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A ∨ B) ::ₘ Θ)

| neg_l
    (d : NMMS base (Γ ∣∼ A ::ₘ Θ)) :
    NMMS base ((¬A) ::ₘ Γ ∣∼ Θ)

| neg_r
    (d : NMMS base (A ::ₘ Γ ∣∼ Θ)) :
    NMMS base (Γ ∣∼ (¬A) ::ₘ Θ)
end Syntax
