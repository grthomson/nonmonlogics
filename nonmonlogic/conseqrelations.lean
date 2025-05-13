import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

#check set

-- A set is defined as a predicate,
-- i.e. a function α → Prop


/--structure ConseqRel (α : Type) where
  antecedents : Finset α
  consequents : Finset α
  conseq_rel : (Finset α) → (Finset α) → Prop
--/

--Or perhaps better...
inductive Atomic : Type
--| Int : Atomic
| String : Atomic
inductive MyProp : Type u
| El : Atomic → MyProp
| imp : MyProp → MyProp → MyProp
infixr: 6 "⇒" => MyProp.imp

--Type Alias
def ConseqRel := Finset MyProp → Finset MyProp → Prop
--def MultiConseqRel (α : Type) := Multiset α → Multiset α → Prop
--def is_conservative_extension_MCR (R R' : MultiConseqRel α) (L : Multiset α) : Prop :=
--∀ (Γ Δ : Multiset α), R' Γ Δ → (∀ A ∈ Δ, A ∈ L) → R Γ Δ

--Structure
--Type for relations defined over pairs of multisets
structure MultiConseqRel (α : Type) :=
  (rel : Multiset α → Multiset α → Prop)

-- THIS IS JUST AN ORDERED PAIR OF MULTISETS! WE NEED REFLEXIVITY
-- AND ALSO SOME FORM OF CUT (RESTRICTED CUT) BUT NOT WEAKENING

-- Helper function to apply the consequence relation
def holds {α : Type} (R : MultiConseqRel α) (Γ Δ : Multiset α) : Prop :=
  R.rel Γ Δ
infix: 50 "R⊢ " => holds

-- Define specific consequence relation on MyProp
def my_CR : MultiConseqRel MyProp :=
  { rel := λ Γ Δ => ((MyProp.El (Atomic.String) ∈ Γ) → (MyProp.El (Atomic.String) ∈ Δ)) }

-- Define is_conservative_extension_MCR to check if one consequence relation is a
--conservative extension of another
def is_conservative_extension_MCR (R X : MultiConseqRel α) (L : Multiset α) : Prop :=
∀ (Γ Δ : Multiset α), (Γ R⊢ Δ) → (∀ A ∈ Δ, A ∈ L) → X.rel Γ Δ

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