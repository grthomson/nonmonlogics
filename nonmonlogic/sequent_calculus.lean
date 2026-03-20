import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Basic

/-!
This file sets up the basic syntax for several proof systems:

* propositional formulas built from atomic symbols and implication
* single-succedent sequents
* multi-succedent sequents
* a natural deduction system `ND_`
* a sequent calculus `SC_`
* an experimental multi-succedent sequent calculus `MultiSC_`

At this stage we are only defining syntax and derivation objects.
We are not yet committing to the final nonmonotonic proof theory.
-/

namespace Syntax

universe u

/-! ## Atomic symbols and formulas -/

/--
`Atomic` is the type of atomic proposition symbols.

At present it has only two constructors, `Int` and `String`,
so it behaves more like a tiny toy language of atom "sorts"
than a genuine infinite stock of propositional variables.

You may later want to replace this with something like:

* `String`
* `Nat`
* or a parameter `α` of atomic symbols.
-/
inductive Atomic : Type
| Int : Atomic
| String : Atomic
deriving DecidableEq, Repr

/--
`MyProp` is the language of implicational formulas.

* `El a` embeds an atomic symbol as a formula
* `imp A B` is implication
-/
inductive MyProp : Type u
| El  : Atomic → MyProp
| imp : MyProp → MyProp → MyProp
deriving DecidableEq, Repr

infixr:60 " ⇒ " => MyProp.imp

/-! ## Sequents -/

/--
A single-succedent sequent `Γ ⊢ A` consists of:

* a list `Γ` of assumptions on the left
* a single conclusion `A` on the right

Using `List MyProp` means the left context is ordered and may contain repeats.
That is often a useful first choice in Lean, even if later one wants to
quotient by permutation or move to multisets.
-/
inductive Sequent : Type u
| Proof : List MyProp → MyProp → Sequent
deriving Repr

infixr:55 " ⊢ " => Sequent.Proof

/--
A multi-succedent sequent `Γ ⊩ Δ` has lists on both sides.

This is included as an experimental object for a possible classical or
multiple-conclusion calculus. Since both sides are lists, this again
retains order and multiplicity.
-/
inductive MultiSequent : Type u
| Proof : List MyProp → List MyProp → MultiSequent
deriving Repr

infixr:55 " ⊩ " => MultiSequent.Proof

/-! ## Common variables -/

variable {A B C : MyProp}
variable {Γ Γ' Δ : List MyProp}
variable {S : Sequent}

/-! ## Natural deduction -/

/--
`ND_` is a very small natural deduction system for the implicational fragment.

Rules:

* `ax`    : assumption
* `imp_i` : implication introduction
* `imp_e` : implication elimination (modus ponens)

Because assumptions are represented by membership in a list, this is a
proof-relevant system of derivation trees rather than merely a provability predicate.
-/
inductive ND_ : Sequent → Type u
| ax    : A ∈ Γ → ND_ (Γ ⊢ A)
| imp_i : ND_ (A :: Γ ⊢ B) → ND_ (Γ ⊢ (A ⇒ B))
| imp_e : ND_ (Γ ⊢ (A ⇒ B)) → ND_ (Γ ⊢ A) → ND_ (Γ ⊢ B)

#check ND_

/--
Convenience notation so one can write `ND_ s` infix-style if desired.

This notation is optional and mostly cosmetic.
-/
infix:3 " ND_ " => ND_

/-! ## Single-succedent sequent calculus -/

/--
`SC_` is a small single-succedent sequent calculus for the implicational fragment.

Rules:

* `ax`    : identity / initial rule
* `cut`   : cut
* `imp_l` : implication left
* `imp_r` : implication right

As written, this is structurally weak: there are no explicit weakening,
contraction, or exchange rules. Since contexts are lists, order matters
unless further equivalence principles are added later.

This makes it a good candidate starting point for a nonmonotonic or
substructural development.
-/
inductive SC_ : Sequent → Type u
| ax    : A ∈ Γ → SC_ (Γ ⊢ A)
| cut   : SC_ (Γ ⊢ A) → SC_ (A :: Γ ⊢ B) → SC_ (Γ ⊢ B)
| imp_l : SC_ (Γ ⊢ A) → SC_ (B :: Γ ⊢ C) → SC_ (((A ⇒ B) :: Γ) ⊢ C)
| imp_r : SC_ (A :: Γ ⊢ B) → SC_ (Γ ⊢ (A ⇒ B))

/--
Optional notation for the sequent calculus derivation type.
-/
infix:3 " SC_ " => SC_

/-! ## Multi-succedent sequent calculus (experimental) -/

/--
`MultiSC_` is an experimental multiple-succedent system.

It is not yet clear whether this is the right logic for this project.
In particular, the axiom rule is currently formulated using subset inclusion:

`Δ ⊆ Γ`

which is more set-like than list-like, while the rest of the rules use
list constructors `::`. So this definition should be treated as provisional.

It may later be revised to use:

* explicit membership / permutation conditions,
* multisets instead of lists,
* or a more standard multiple-conclusion sequent presentation.
-/
inductive MultiSC_ : MultiSequent → Type u
| ax    : Δ ⊆ Γ → MultiSC_ (Γ ⊩ Δ)
| imp_l : MultiSC_ (Γ ⊩ (A :: Δ)) →
          MultiSC_ ((B :: Γ) ⊩ Δ) →
          MultiSC_ (((A ⇒ B) :: Γ) ⊩ Δ)
| imp_r : MultiSC_ ((A :: Γ) ⊩ (B :: Δ)) →
          MultiSC_ (Γ ⊩ ((A ⇒ B) :: Δ))

/-! ## Experimental distinction between empirical and mathematical propositions

This section is not used by the systems above, but it may become relevant later
if we want to distinguish a nonmonotonic empirical layer from a monotonic
mathematical or meta-level layer.
-/

/--
`EmpiricalProp` is a possible future language for nonmonotonic empirical content.
Currently unused.
-/
inductive EmpiricalProp : Type u
| atom : Atomic → EmpiricalProp
| conj : EmpiricalProp → EmpiricalProp → EmpiricalProp
| impl : EmpiricalProp → EmpiricalProp → EmpiricalProp
deriving DecidableEq, Repr

/--
`MathProp` is a possible future language for a more stable or monotonic layer
built over empirical propositions. Currently unused.
-/
inductive MathProp : Type u
| base : EmpiricalProp → MathProp
| conj : MathProp → MathProp → MathProp
| impl : MathProp → MathProp → MathProp
deriving DecidableEq, Repr

end Syntax


/-!
Generic list utilities are better kept outside the logical syntax namespace,
since they are not specific to sequents or formulas.
-/
namespace HeteroProperties

universe u

/--
A hand-written recursive list concatenation function.

This duplicates `List.append` / `++`, so in ordinary Lean development one
would usually just use the built-in append. It is retained here only in case
we want an explicit recursive definition for later proofs by induction.
-/
def concatLists {α : Type u} : List α → List α → List α
| [], ys => ys
| x :: xs, ys => x :: concatLists xs ys

/-
A possible future helper about sublists or subsets after concatenation.
Left commented for now because it is not yet used and its exact statement
depends on whether we want `Sublist`, subset-of-membership, or something else.
-/

/-
Example shape only:

`concatSublist` should say that if `as` is a sublist of `bs`,
then `as` is also a sublist of `cs ++ bs`.
--   def concatSublist {α : Type u} {as bs cs : List α}
--   (h : List.Sublist as bs) : List.Sublist as (concatLists cs bs) :=
--   sorry
--/
end HeteroProperties
