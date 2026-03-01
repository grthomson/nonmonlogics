import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

#check Set

-- A set is defined as a predicate,
-- i.e. a function α → Prop


/--structure ConseqRel (α : Type) where
  antecedents : Finset α
  consequents : Finset α
  conseq_rel : (Finset α) → (Finset α) → Prop
--/

--Or perhaps better...
--inductive Atomic : Type
--| Int : Atomic
--| String : Atomic
--inductive MyProp : Type u
--| El : Atomic → MyProp
--| imp : MyProp → MyProp → MyProp
--infixr: 6 "⇒" => MyProp.imp

--05/10/25
-- parametrise atom type so letter variables can be used
/-
STEP 0: Basic syntax (atoms and implication)

• We parametrize atomic propositions by a String label (e.g. "p", "q").
• `deriving DecidableEq` asks Lean to automatically generate an equality
  decision procedure — crucial for `Multiset` membership (`A ∈ Γ`), which
  needs to decide whether two `Formula`s are equal.
-/
inductive Atom : Type
| var : String → Atom
deriving DecidableEq

/-
`Formula` is the abstract syntax tree (AST) for our object language.
We keep only atoms and implication for now.
-/
inductive Formula : Type
| atom : Atom → Formula
| imp  : Formula → Formula → Formula
deriving DecidableEq

/-
Operator for implication.

• `infixr: 60` declares a right-associative infix operator at precedence 60.
• We choose 60 (rather than the very low 6) so that `A ⇒ B ∈ Γ`
  parses as `(A ⇒ B) ∈ Γ` instead of `A ⇒ (B ∈ Γ)`.
  (Membership `∈` binds tighter than low-precedence arrows otherwise.)
-/
infixr: 60 " ⇒ " => Formula.imp


/-
STEP 1: Contexts and consequence relations

• `Ctx` is a *multiset* of formulas: order doesn’t matter (exchange is built-in),
  but multiplicity does (so contraction is NOT baked in).
• This is exactly what we want for substructural work: exchange yes,
  weakening/contracton no (unless we add them explicitly later).

• `ConseqRel` is a *raw entailment relation*: a function taking (Γ, Δ) to a Prop.
  This is a *syntactic* notion (“provable via some proof system”), not semantics.
-/
abbrev Ctx := Multiset Formula
abbrev ConseqRel := Ctx → Ctx → Prop

/-
STEP 2: Turnstile notation

• Purely syntactic sugar: `Γ ⊢[R] Δ` means `R Γ Δ`.
• Read: “Under relation R, Γ entails Δ.”

IMPORTANT: This does NOT define a *semantic* reading (“if Γ is true then Δ is true”).
Semantics can be added later and related by soundness/completeness theorems.
-/
notation:50 Γ " ⊢[" R:50 "] " Δ => R Γ Δ


/-
STEP 3: A tiny sanity-check relation

• `idRel` (identity) says: Γ ⊢ Δ iff Γ = Δ.
  Not a real logic — just useful to test types/notation are wired up.
• `fun Γ Δ => ...` is Lean’s lambda (“λ Γ Δ, ...”).
-/
def idRel : ConseqRel :=
  fun Γ Δ => Γ = Δ

-- Convenience names for two example formulas (just to build contexts below).
open Formula
def A : Formula := atom (.var "p")
def B : Formula := atom (.var "q")

/-
`#check` asks Lean for the type of an expression; it doesn't run anything.

Below we ask: what is the type of `({A} : Ctx) ⊢[idRel] {A}`?
• `{A}` here is using a literal notation that Lean can resolve to a multiset
  because the expected type is `Ctx` (= `Multiset Formula`). If our setup
  ever complains about this, we can build multisets explicitly as:
    `A ::ₘ 0`  (singleton)  or  `A ::ₘ B ::ₘ 0` (two elements), etc.
-/
#check ({A} : Ctx) ⊢[idRel] {A}


/-
STEP 4: A toy “modus ponens step” relation

• This is a deliberately tiny, *syntactic* one-step entailment:
  if Γ contains A and (A ⇒ B), then Δ must contain B.

• The `∀ (A B : Formula), ...` makes this *very strong* (for every A, B that appears
  as a modus ponens pattern in Γ, B must be in Δ). For a “there exists a step”
  flavor, we could use `∃ A B, ...` instead; both are useful for experiments.
-/
def implStepRel : ConseqRel :=
  fun Γ Δ =>
    ∀ (A B : Formula), A ∈ Γ → ((A ⇒ B) ∈ Γ) → (B ∈ Δ)

-- Usage idea (no proof requested; `#check` only type-checks the statement):
#check ({A, A ⇒ B} : Ctx) ⊢[implStepRel] {B}


open Multiset

/-
STEP 5: Handy singleton notation for multisets

• `::ₘ` is “cons” for multisets; `0 : Ctx` is the empty multiset.
• We define `⟦A⟧` as the singleton multiset containing A.
  This avoids confusion with `{A}`, which some users associate with sets/finsets.
-/
notation "⟦" A "⟧" => (A ::ₘ (0 : Ctx))


/-
STEP 6: Structural/metalogical properties (no weakening or contraction)

• `Structural R` bundles properties you *may* want to assume/prove about a relation `R`.
• We add only Identity and Cut — matching your “no weakening on either side”
  and “no contraction” requirement.
• Braced binders `{A : Formula}` are *implicit* parameters:
  Lean infers them at use sites; we can supply them explicitly as needed.
-/
structure Structural (R : ConseqRel) : Prop :=
  /-- Identity: with empty side-contexts, A entails A (i.e. ⟦A⟧ ⊢[R] ⟦A⟧). -/
  (id  : ∀ {A : Formula}, (⟦A⟧ ⊢[R] ⟦A⟧))
  /-- Cut: if Γ ⊢ A,Δ and A,Γ ⊢ Δ then Γ ⊢ Δ. -/
  (cut :
    ∀ {Γ Δ : Ctx} {A : Formula},
      (Γ ⊢[R] (A ::ₘ Δ)) →
      ((A ::ₘ Γ) ⊢[R] Δ) →
      (Γ ⊢[R] Δ))


/-
STEP 7: (Conservativity)
“X is conservative over R w.r.t. a language L”:
whenever R proves Γ ⊢ Δ and every formula in Δ is in L,
then X also proves Γ ⊢ Δ.

We model the ‘language’ as a predicate L : Formula → Prop.
-/
def conservativeOver (R X : ConseqRel) (L : Formula → Prop) : Prop :=
  ∀ Γ Δ, (Γ ⊢[R] Δ) → (∀ A ∈ Δ, L A) → (Γ ⊢[X] Δ)



--Type Alias
--def ConseqRel := Finset Formula → Finset Formula → Prop
--def MultiConseqRel (α : Type) := Multiset α → Multiset α → Prop
--def is_conservative_extension_MCR (R R' : MultiConseqRel α) (L : Multiset α) : Prop :=
--∀ (Γ Δ : Multiset α), R' Γ Δ → (∀ A ∈ Δ, A ∈ L) → R Γ Δ

--Structure
--Type for relations defined over pairs of multisets
--structure MultiConseqRel (α : Type) :=
 -- (rel : Multiset α → Multiset α → Prop)

-- THIS IS JUST AN ORDERED PAIR OF MULTISETS! WE NEED REFLEXIVITY
-- AND ALSO SOME FORM OF CUT (RESTRICTED CUT) BUT NOT WEAKENING

-- Helper function to apply the consequence relation
--def holds {α : Type} (R : MultiConseqRel α) (Γ Δ : Multiset α) : Prop :=
--  R.rel Γ Δ
--infix: 50 "R⊢ " => holds

-- Define specific consequence relation on MyProp
--def my_CR : MultiConseqRel MyProp :=
--  { rel := λ Γ Δ => ((MyProp.El (Atomic.String) ∈ Γ) → (MyProp.El (Atomic.String) ∈ Δ)) }

-- Define is_conservative_extension_MCR to check if one consequence relation is a
--conservative extension of another
--def is_conservative_extension_MCR (R X : MultiConseqRel α) (L : Multiset α) : Prop :=
--∀ (Γ Δ : Multiset α), (Γ R⊢ Δ) → (∀ A ∈ Δ, A ∈ L) → X.rel Γ Δ

--07/01/25 cockett seely
-- tensor connective is just comma, no struct rules
-- but they assume a cut rule

structure Category (Obj : Type) (Hom : Obj → Obj → Type) :=
  (identity : Π (A : Obj), Hom A A)
  (compose : Π {A B C : Obj}, Hom A B → Hom B C → Hom A C)
  (left_identity : ∀ {A B : Obj} (f : Hom A B), compose (identity A) f = f)
  (right_identity : ∀ {A B : Obj} (f : Hom A B), compose f (identity B) = f)
  (associativity : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
     compose (compose f g) h = compose f (compose g h))

-- the baseline consequence relation is nonmonotonic
-- in general you can't do weakening (i.e. not always), that's TRUE
-- i.e. when EXPANDING premise set
-- adding to premise set doesn't ALWAYS preserve conclusion
-- linear logic bit different to this???

-- but it IS conservative!!! existing guys hold OK! it's
-- new lingo that causes problems
-- addition of new props to nonmon conseq relation
-- existing derivations hold but...
-- what if we can NOW generate contradiction? see hlobil
-- ". It is trivially the case that A ` A, and also if A `
-- B and B ` C then A ` C ." -- Awodey on transitivity.. BUT SEE HLOBIL ON CUT?

-- MONOTONICITY AS A TYPE REFINEMENT?!
-- ANDREJ IS SAYING THAT SUBOBJECT IS THE USUAL NOTION OF ENTAILMENT IN CATEGORICAL
-- SEMANTICS
-- I NEED SOMETHING TO CAPTURE THE IDEA THAT ENTAILMENT ISN'T AS SIMPLE
-- TBH THE 2-CATEGORICAL SEMANTICS COULD DO THIS
-- move from X |-- A to | -- X --> A seems to be key in categorical semantics
-- do deduction theorems always fail for nonmonotonic logics?
--
-- "The subobjects in a 2-category are fully faithful inclusions."
