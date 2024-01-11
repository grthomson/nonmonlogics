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
