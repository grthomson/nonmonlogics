import Mathlib.Data.Finset.Basic

#check set

-- A set is defined as a predicate,
-- i.e. a function α → Prop

structure MultiConseqRel (α : Type) where
  antecedents : Finset α
  consequents : Finset α
  conseq_rel : (Finset α) → (Finset α) → Prop

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
