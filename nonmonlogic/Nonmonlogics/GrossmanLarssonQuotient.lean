import Nonmonlogics.GrossmanLarsson
import Mathlib.SetTheory.Cardinal.Basic

#check Cardinal
#check Cardinal.mk
#check Cardinal.lift

/-!
# Quotient / canonical witness layer for the Grossman–Larson proof-tree development

This file builds on `grossman_larson.lean`.

The previous file developed:
- proof trees `PTree`
- matching-leaf grafting
- structural inner/outer decomposition for two-step grafts
- a raw address-counting pre-Lie attempt

That raw approach appears to over-distinguish witnesses by address bookkeeping.
The goal of this file is to define a more invariant notion of two-step witness
(or a canonical representative / quotient of witnesses) that identifies
bureaucratically equivalent derivation histories while preserving genuine
proof-theoretic structure.

Planned steps:
1. define canonical / quotient witness data;
2. identify outer commutations and inner reassociations;
3. prove left/right correspondence at the new level;
4. define the corrected pre-Lie product;
5. return to the symmetric-algebra / Hopf-algebra construction.
-/

/-!
We treat raw address-labelled two-step graft witnesses as *codes of derivations* -- i.e.
not yet canonical proof objects.

A raw witness remembers:
- the first graft site
- the second graft site
- an intermediate tree
- and therefore a particular bureaucratic history of construction.

For the pre-Lie identity this coding is too fine:
independent grafts may commute and nested grafts may admit equivalent
reassociations without changing the essential proof-composition structure.

Following Lambek/Dosen-style identity-of-proofs philosophy we seek
an equivalence relation on two-step witness codes that:

- preserves the directionality of grafting
  (inserted-tree conclusion matched into a receiver-tree premise leaf)
- preserves the structural dependency of the two grafts
  (nested vs independent)
- preserves the final resulting proof tree

while forgetting inessential address bookkeeping and scheduling artefacts.

The goal is to recover the pre-Lie identity at the level of equivalence classes
or canonical representatives of two-step witnesses and then linearise that
structure to obtain an a Hopf Algebra via Oudom-Guin construction.
-/

open scoped TensorProduct
open Syntax


/-!
## Canonical two-step witness data

The following type is intended as a more invariant representation of
two-step proof-composition data for the associator.

`outer z₃` means:
  first graft `x` into `z`, obtaining `z₃`,
  then graft `y` into `z₃`, obtaining `w`.

`inner y'` means:
  first graft `x` into `y`, obtaining `y'`,
  then graft `y'` into `z`, obtaining `w`.

So this forgets raw address bookkeeping while preserving:
- the conclusion-to-premise directionality of grafting,
- the dependency pattern of the two grafts,
- and the intermediate proof object that matters algebraically.
-/
inductive TwoStepCanonical (x y z w : PTree) : Type where
| outer
    (z₃ : PTree)
    (hxz : z₃ ∈ PTree.matchingLeafGraftings x z)
    (hyw : w ∈ PTree.matchingLeafGraftings y z₃) :
    TwoStepCanonical x y z w
| inner
    (y' : Syntax.PTree)
    (hxy : y' ∈ PTree.matchingLeafGraftings x y)
    (hyw : w ∈ PTree.matchingLeafGraftings y' z) :
    TwoStepCanonical x y z w

inductive TwoStepCode (x y z w : PTree) : Type where
| leftOuter
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    TwoStepCode x y z w
| leftInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepCode x y z w
| rightOuter
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    TwoStepCode x y z w
| rightInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepCode x y z w


/--
A left-outer raw two-step code can be transported to some right-oriented code
with the same parameters `(x,y,z,w)`.

This uses the already-proved left-to-right witness transport theorem, so the
result may be either a right-outer code or a right-inner code.
-/
theorem leftOuter_to_some_rightCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      match c with
      | TwoStepCode.rightOuter _ _ _ _ _ => True
      | TwoStepCode.rightInner _ _ _ _ _ => True
      | _ => False := by
  have hr : Nonempty (TwoStepWitnessRight x y z w) :=
    outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hr with ⟨r⟩
  cases r with
  | outer a' b' z'' haz'' hbw'' =>
      exact ⟨TwoStepCode.rightOuter a' b' z'' haz'' hbw'', trivial⟩
  | inner a' b' y' hay' hbw'' =>
      exact ⟨TwoStepCode.rightInner a' b' y' hay' hbw'', trivial⟩

/--
A left-inner raw code is already, by inspection, a right-inner code with
`x` and `y` swapped.

So the natural codomain here is `TwoStepCode y x z w`.
-/
theorem leftInner_to_some_rightCode
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      match c with
      | TwoStepCode.rightInner _ _ _ _ _ => True
      | _ => False := by
  exact ⟨TwoStepCode.rightInner a b y' hay hbw, trivial⟩

/--
A right-outer raw two-step code can be transported to some left-oriented code
with the same parameters `(x,y,z,w)`.

This uses the already-proved right-to-left witness transport theorem, so the
result may be either a left-outer code or a left-inner code.
-/
theorem rightOuter_to_some_leftCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      match c with
      | TwoStepCode.leftOuter _ _ _ _ _ => True
      | TwoStepCode.leftInner _ _ _ _ _ => True
      | _ => False := by
  have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
    outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hl with ⟨l⟩
  cases l with
  | outer a' b' z'' haz'' hbw'' =>
      exact ⟨TwoStepCode.leftOuter a' b' z'' haz'' hbw'', trivial⟩
  | inner a' b' y' hay' hbw'' =>
      exact ⟨TwoStepCode.leftInner a' b' y' hay' hbw'', trivial⟩

/--
A right-inner raw code is already, by inspection, a left-inner code with
`x` and `y` swapped.

So the natural codomain here is `TwoStepCode y x z w`.
-/
theorem rightInner_to_some_leftCode
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      match c with
      | TwoStepCode.leftInner _ _ _ _ _ => True
      | _ => False := by
  exact ⟨TwoStepCode.leftInner a b y' hay hbw, trivial⟩


inductive TwoStepEquiv (x y z w : PTree) :
    TwoStepCode x y z w → TwoStepCode x y z w → Prop where
| refl : ∀ c, TwoStepEquiv x y z w c c
| symm : ∀ {c d}, TwoStepEquiv x y z w c d → TwoStepEquiv x y z w d c
| trans : ∀ {c d e},
    TwoStepEquiv x y z w c d →
    TwoStepEquiv x y z w d e →
    TwoStepEquiv x y z w c e

| outer_comm_outer :
    ∀ {a b z' a' b' z''}
      (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
      (haz' : (a', z'') ∈ matchingLeafGraftWitnesses x z)
      (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y z''),
      ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z →
      TwoStepEquiv x y z w
        (TwoStepCode.leftOuter a b z' haz hbw)
        (TwoStepCode.rightOuter a' b' z'' haz' hbw')

| outer_comm_inner :
    ∀ {a b z' a' b' y''}
      (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
      (hay' : (a', y'') ∈ matchingLeafGraftWitnesses x y)
      (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z),
      ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z →
      TwoStepEquiv x y z w
        (TwoStepCode.leftOuter a b z' haz hbw)
        (TwoStepCode.rightInner a' b' y'' hay' hbw')

| outer_comm_back_outer :
    ∀ {a b z' a' b' z''}
      (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
      (haz' : (a', z'') ∈ matchingLeafGraftWitnesses y z)
      (hbw' : (b', w) ∈ matchingLeafGraftWitnesses x z''),
      ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z →
      TwoStepEquiv x y z w
        (TwoStepCode.rightOuter a b z' haz hbw)
        (TwoStepCode.leftOuter a' b' z'' haz' hbw')

| outer_comm_back_inner :
    ∀ {a b z' a' b' y''}
      (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
      (hay' : (a', y'') ∈ matchingLeafGraftWitnesses y x)
      (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z),
      ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z →
      TwoStepEquiv x y z w
        (TwoStepCode.rightOuter a b z' haz hbw)
        (TwoStepCode.leftInner a' b' y'' hay' hbw')

theorem leftOuter_relates_to_some_rightCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      TwoStepEquiv x y z w
        (TwoStepCode.leftOuter a b z' haz hbw) c := by
  have hr : Nonempty (TwoStepWitnessRight x y z w) :=
    outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hr with ⟨r⟩
  cases r with
  | outer a' b' z'' haz'' hbw'' =>
      refine ⟨TwoStepCode.rightOuter a' b' z'' haz'' hbw'', ?_⟩
      exact TwoStepEquiv.outer_comm_outer haz hbw haz'' hbw'' (by
        rw [mem_twoStepAddrWitnessesRight_iff]
        exact Or.inl ⟨z'', haz'', hbw''⟩)
  | inner a' b' y'' hay'' hbw'' =>
      refine ⟨TwoStepCode.rightInner a' b' y'' hay'' hbw'', ?_⟩
      exact TwoStepEquiv.outer_comm_inner haz hbw hay'' hbw'' (by
        rw [mem_twoStepAddrWitnessesRight_iff]
        exact Or.inr ⟨y'', hay'', hbw''⟩)

theorem rightOuter_relates_to_some_leftCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      TwoStepEquiv x y z w
        (TwoStepCode.rightOuter a b z' haz hbw)
        c := by
  have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
    outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hl with ⟨l⟩
  cases l with
  | outer a' b' z'' haz'' hbw'' =>
      refine ⟨TwoStepCode.leftOuter a' b' z'' haz'' hbw'', ?_⟩
      exact TwoStepEquiv.outer_comm_back_outer haz hbw haz'' hbw'' (by
        rw [mem_twoStepAddrWitnessesLeft_iff]
        exact Or.inl ⟨z'', haz'', hbw''⟩)
  | inner a' b' y'' hay'' hbw'' =>
      refine ⟨TwoStepCode.leftInner a' b' y'' hay'' hbw'', ?_⟩
      exact TwoStepEquiv.outer_comm_back_inner haz hbw hay'' hbw'' (by
        rw [mem_twoStepAddrWitnessesLeft_iff]
        exact Or.inr ⟨y'', hay'', hbw''⟩)

/-- The setoid generated by `TwoStepEquiv` on fixed two-step codes. -/
def TwoStepSetoid (x y z w : PTree) : Setoid (TwoStepCode x y z w) where
  r := TwoStepEquiv x y z w
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact TwoStepEquiv.refl c
    · intro c d h
      exact TwoStepEquiv.symm h
    · intro c d e h₁ h₂
      exact TwoStepEquiv.trans h₁ h₂

/-- The quotient of two-step witness codes modulo bureaucratic equivalence. -/
def TwoStepQuotient (x y z w : PTree) :=
  Quot (TwoStepSetoid x y z w)

/-- The quotient class of a raw two-step code. -/
def codeClass {x y z w : PTree} (c : TwoStepCode x y z w) :
    TwoStepQuotient x y z w :=
  Quot.mk _ c

/-- Related codes define the same quotient class. -/
theorem codeClass_eq_of_equiv
    {x y z w : PTree}
    {c d : TwoStepCode x y z w}
    (h : TwoStepEquiv x y z w c d) :
    codeClass c = codeClass d := by
  exact Quot.sound h

/--
A left-outer raw code has the same quotient class as some right-side code.

This is the quotient-level form of `leftOuter_relates_to_some_rightCode`.
-/
theorem leftOuter_class_eq_some_rightCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      codeClass (TwoStepCode.leftOuter a b z' haz hbw) = codeClass c := by
  obtain ⟨c, hrel⟩ :=
    leftOuter_relates_to_some_rightCode x y z w a b z' haz hbw
  refine ⟨c, ?_⟩
  exact codeClass_eq_of_equiv hrel

/--
A right-outer raw code has the same quotient class as some left-side code.

This is the quotient-level form of `rightOuter_relates_to_some_leftCode`.
-/
theorem rightOuter_class_eq_some_leftCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      codeClass (TwoStepCode.rightOuter a b z' haz hbw) = codeClass c := by
  obtain ⟨c, hrel⟩ :=
    rightOuter_relates_to_some_leftCode x y z w a b z' haz hbw
  refine ⟨c, ?_⟩
  exact codeClass_eq_of_equiv hrel

/--
A left-outer raw code has the same quotient class as some right-shaped code.
-/
theorem leftOuter_class_eq_some_rightShapedCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      (match c with
       | TwoStepCode.rightOuter _ _ _ _ _ => True
       | TwoStepCode.rightInner _ _ _ _ _ => True
       | _ => False) ∧
      codeClass (TwoStepCode.leftOuter a b z' haz hbw) = codeClass c := by
  have hr : Nonempty (TwoStepWitnessRight x y z w) :=
    outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hr with ⟨r⟩
  cases r with
  | outer a' b' z'' haz'' hbw'' =>
      refine ⟨TwoStepCode.rightOuter a' b' z'' haz'' hbw'', ?_, ?_⟩
      · trivial
      · exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_outer haz hbw haz'' hbw'' (by
            rw [mem_twoStepAddrWitnessesRight_iff]
            exact Or.inl ⟨z'', haz'', hbw''⟩))
  | inner a' b' y'' hay'' hbw'' =>
      refine ⟨TwoStepCode.rightInner a' b' y'' hay'' hbw'', ?_, ?_⟩
      · trivial
      · exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_inner haz hbw hay'' hbw'' (by
            rw [mem_twoStepAddrWitnessesRight_iff]
            exact Or.inr ⟨y'', hay'', hbw''⟩))

/--
A right-outer raw code has the same quotient class as some left-shaped code.
-/
theorem rightOuter_class_eq_some_leftShapedCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      (match c with
       | TwoStepCode.leftOuter _ _ _ _ _ => True
       | TwoStepCode.leftInner _ _ _ _ _ => True
       | _ => False) ∧
      codeClass (TwoStepCode.rightOuter a b z' haz hbw) = codeClass c := by
  have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
    outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hl with ⟨l⟩
  cases l with
  | outer a' b' z'' haz'' hbw'' =>
      refine ⟨TwoStepCode.leftOuter a' b' z'' haz'' hbw'', ?_, ?_⟩
      · trivial
      · exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_back_outer haz hbw haz'' hbw'' (by
            rw [mem_twoStepAddrWitnessesLeft_iff]
            exact Or.inl ⟨z'', haz'', hbw''⟩))
  | inner a' b' y'' hay'' hbw'' =>
      refine ⟨TwoStepCode.leftInner a' b' y'' hay'' hbw'', ?_, ?_⟩
      · trivial
      · exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_back_inner haz hbw hay'' hbw'' (by
            rw [mem_twoStepAddrWitnessesLeft_iff]
            exact Or.inr ⟨y'', hay'', hbw''⟩))

/-- A two-step code is right-shaped if it is a right-outer or right-inner code. -/
def IsRightShapedCode
    (x y z w : PTree)
    (c : TwoStepCode x y z w) : Prop :=
  match c with
  | TwoStepCode.rightOuter _ _ _ _ _ => True
  | TwoStepCode.rightInner _ _ _ _ _ => True
  | _ => False

/-- A two-step code is left-shaped if it is a left-outer or left-inner code. -/
def IsLeftShapedCode
    (x y z w : PTree)
    (c : TwoStepCode x y z w) : Prop :=
  match c with
  | TwoStepCode.leftOuter _ _ _ _ _ => True
  | TwoStepCode.leftInner _ _ _ _ _ => True
  | _ => False

/--
Every left-outer quotient class admits a right-shaped representative.

This is the quotient-level outer-commutation statement: a raw left-outer
two-step derivation code can always be re-expressed, modulo `TwoStepEquiv`,
by some right-shaped code.
-/
theorem leftOuter_class_has_rightShaped_representative
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      IsRightShapedCode x y z w c ∧
      codeClass (TwoStepCode.leftOuter a b z' haz hbw) = codeClass c := by
  simpa [IsRightShapedCode] using
    leftOuter_class_eq_some_rightShapedCode x y z w a b z' haz hbw

/--
Every right-outer quotient class admits a left-shaped representative.

This is the left/right mirror of
`leftOuter_class_has_rightShaped_representative`.
-/
theorem rightOuter_class_has_leftShaped_representative
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      IsLeftShapedCode x y z w c ∧
      codeClass (TwoStepCode.rightOuter a b z' haz hbw) = codeClass c := by
  simpa [IsLeftShapedCode] using
    rightOuter_class_eq_some_leftShapedCode x y z w a b z' haz hbw

/--
Quotient-level outer support, left-to-right.

Any left-outer code has the same quotient class as some right-shaped code.
This is the first direct quotient-level sign that the raw associator mismatch
was bureaucratic rather than structural.
-/
theorem outer_support_quotient_left_to_right
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      IsRightShapedCode x y z w c ∧
      codeClass (TwoStepCode.leftOuter a b z' haz hbw) = codeClass c := by
  exact leftOuter_class_has_rightShaped_representative x y z w a b z' haz hbw

/--
Quotient-level outer support, right-to-left.

Any right-outer code has the same quotient class as some left-shaped code.
-/
theorem outer_support_quotient_right_to_left
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      IsLeftShapedCode x y z w c ∧
      codeClass (TwoStepCode.rightOuter a b z' haz hbw) = codeClass c := by
  exact rightOuter_class_has_leftShaped_representative x y z w a b z' haz hbw

/--
The quotient class of a raw left-outer two-step code.
-/
def classOfLeftOuter
    {x y z w : PTree}
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    TwoStepQuotient x y z w :=
  codeClass (TwoStepCode.leftOuter a b z' haz hbw)

/--
The quotient class of a raw right-outer two-step code.
-/
def classOfRightOuter
    {x y z w : PTree}
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    TwoStepQuotient x y z w :=
  codeClass (TwoStepCode.rightOuter a b z' haz hbw)

/--
Every left-outer quotient class is equal to the class of some right-shaped code.
-/
theorem classOfLeftOuter_eq_some_rightShaped
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      IsRightShapedCode x y z w c ∧
      classOfLeftOuter a b z' haz hbw = codeClass c := by
  exact outer_support_quotient_left_to_right x y z w a b z' haz hbw

/--
Every right-outer quotient class is equal to the class of some left-shaped code.
-/
theorem classOfRightOuter_eq_some_leftShaped
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      IsLeftShapedCode x y z w c ∧
      classOfRightOuter a b z' haz hbw = codeClass c := by
  exact outer_support_quotient_right_to_left x y z w a b z' haz hbw

/--
Outer commutation holds at the quotient level:
every left-outer derivation code and some right-shaped derivation code
represent the same two-step proof-composition class.
-/
theorem outer_commutation_on_classes
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      IsRightShapedCode x y z w c ∧
      classOfLeftOuter a b z' haz hbw = codeClass c := by
  exact classOfLeftOuter_eq_some_rightShaped x y z w a b z' haz hbw

/--
The quotient class of a raw left-inner two-step code.

This lives in `TwoStepQuotient x y z w`.
-/
def classOfLeftInner
    {x y z w : PTree}
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepQuotient x y z w :=
  codeClass (TwoStepCode.leftInner a b y' hay hbw)

/--
The quotient class of a raw right-inner two-step code.

This lives in `TwoStepQuotient y x z w`, reflecting the `x ↔ y` swap
in the inner/nested part of the associator.
-/
def classOfRightInner
    {x y z w : PTree}
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepQuotient y x z w :=
  codeClass (TwoStepCode.rightInner a b y' hay hbw)

/--
A left-inner raw code determines a right-inner raw code in the swapped
parameter quotient `(y,x,z,w)`.
-/
theorem leftInner_has_rightInner_code_swapped
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      (match c with
       | TwoStepCode.rightInner _ _ _ _ _ => True
       | _ => False) := by
  exact ⟨TwoStepCode.rightInner a b y' hay hbw, trivial⟩

/--
A right-inner raw code determines a left-inner raw code in the swapped
parameter quotient `(y,x,z,w)`.
-/
theorem rightInner_has_leftInner_code_swapped
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      (match c with
       | TwoStepCode.leftInner _ _ _ _ _ => True
       | _ => False) := by
  exact ⟨TwoStepCode.leftInner a b y' hay hbw, trivial⟩


/-! Next! swap / transport  map on codes / quotients:
note this may have some relevant to the tensor
twist map A cocommutative coalgebra is one for whichτ ◦∆ = ∆, whereτ:V ⊗ W →W ⊗ V given by the v ⊗ w 7→ w ⊗ v is the “twist map.
We need (I think) to define a map like TwoStepQuotient x y z w → TwoStepQuotient y x z w
-/

/--
The raw code determined by a left witness.
-/
def codeOfLeftWitness
    {x y z w : PTree} :
    TwoStepWitnessLeft x y z w → TwoStepCode x y z w
  | TwoStepWitnessLeft.outer a b z' haz hbw =>
      TwoStepCode.leftOuter a b z' haz hbw
  | TwoStepWitnessLeft.inner a b y' hay hbw =>
      TwoStepCode.leftInner a b y' hay hbw

/--
The raw code determined by a right witness.
-/
def codeOfRightWitness
    {x y z w : PTree} :
    TwoStepWitnessRight x y z w → TwoStepCode x y z w
  | TwoStepWitnessRight.outer a b z' haz hbw =>
      TwoStepCode.rightOuter a b z' haz hbw
  | TwoStepWitnessRight.inner a b y' hay hbw =>
      TwoStepCode.rightInner a b y' hay hbw

/--
The quotient class determined by a left witness.
-/
def classOfLeftWitness
    {x y z w : PTree} :
    TwoStepWitnessLeft x y z w → TwoStepQuotient x y z w :=
  fun h => codeClass (codeOfLeftWitness h)

/--
The quotient class determined by a right witness.
-/
def classOfRightWitness
    {x y z w : PTree} :
    TwoStepWitnessRight x y z w → TwoStepQuotient x y z w :=
  fun h => codeClass (codeOfRightWitness h)

/--
Every left-outer witness class is equal to the class of some right-shaped code.
-/
theorem leftOuterWitness_class_eq_some_rightShaped
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      IsRightShapedCode x y z w c ∧
      classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw) = codeClass c := by
  simpa [classOfLeftWitness, codeOfLeftWitness, classOfLeftOuter] using
    leftOuter_class_has_rightShaped_representative x y z w a b z' haz hbw


/--
A left-inner witness determines an inner-shaped code in the swapped quotient.
-/
theorem leftInnerWitness_has_swapped_innerRepresentative
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      match c with
      | TwoStepCode.rightInner _ _ _ _ _ => True
      | _ => False := by
  exact ⟨TwoStepCode.rightInner a b y' hay hbw, trivial⟩

/--
A right-inner witness determines an inner-shaped code in the swapped quotient.
-/
theorem rightInnerWitness_has_swapped_innerRepresentative
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ c : TwoStepCode y x z w,
      match c with
      | TwoStepCode.leftInner _ _ _ _ _ => True
      | _ => False := by
  exact ⟨TwoStepCode.leftInner a b y' hay hbw, trivial⟩


/--
Outer commutation is handled internally in the fixed quotient, while inner
reassociation is handled by swapping the first two parameters.

This is the structural quotient-level form of the pre-Lie associator symmetry.
-/
theorem twoStepQuotient_preLie_shape
    (x y z w : PTree) :
    (∀ a b z'
      (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z'),
      ∃ c : TwoStepCode x y z w,
        IsRightShapedCode x y z w c ∧
        classOfLeftOuter a b z' haz hbw = codeClass c)
    ∧
    (∀ a b y'
      (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z),
      ∃ c : TwoStepCode y x z w,
        match c with
        | TwoStepCode.rightInner _ _ _ _ _ => True
        | _ => False) := by
  constructor
  · intro a b z' haz hbw
    exact outer_support_quotient_left_to_right x y z w a b z' haz hbw
  · intro a b y' hay hbw
    exact leftInnerWitness_has_swapped_innerRepresentative x y z w a b y' hay hbw

/-
/--
A basic quotient-level swapped correspondence relation.

For now we only build in the inner/nested part explicitly. Outer commutation
is already handled internally in the fixed quotient, so this relation is the
first bridge between `TwoStepQuotient x y z w` and `TwoStepQuotient y x z w`.
-/
inductive SwappedTwoStepClass
    (x y z w : PTree) :
    TwoStepQuotient x y z w →
    TwoStepQuotient y x z w → Prop where

| leftInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (classOfLeftInner a b y' hay hbw)
      (classOfRightInner a b y' hay hbw)

| rightInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (codeClass (TwoStepCode.rightInner a b y' hay hbw))
      (codeClass (TwoStepCode.leftInner a b y' hay hbw))
-/

inductive SwappedTwoStepClass
    (x y z w : PTree) :
    TwoStepQuotient x y z w →
    TwoStepQuotient y x z w → Prop where

| leftOuter
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    SwappedTwoStepClass x y z w
      (classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw))
      (classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw))

| rightOuter
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    SwappedTwoStepClass x y z w
      (classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw))
      (classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw))

| leftInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (classOfLeftInner a b y' hay hbw)
      (classOfRightInner a b y' hay hbw)

| rightInner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (codeClass (TwoStepCode.rightInner a b y' hay hbw))
      (codeClass (TwoStepCode.leftInner a b y' hay hbw))

/--
Any raw left-inner code determines a swapped quotient-level partner.
-/
theorem leftInner_class_has_swapped_partner
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (classOfLeftInner a b y' hay hbw)
      (classOfRightInner a b y' hay hbw) := by
  exact SwappedTwoStepClass.leftInner a b y' hay hbw

/--
Any raw right-inner code determines a swapped quotient-level partner.
-/
theorem rightInner_class_has_swapped_partner
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    SwappedTwoStepClass x y z w
      (codeClass (TwoStepCode.rightInner a b y' hay hbw))
      (codeClass (TwoStepCode.leftInner a b y' hay hbw)) := by
  exact SwappedTwoStepClass.rightInner a b y' hay hbw

  /--
Quotient-level pre-Lie shape, first relational version.

- Outer commutation is handled internally in `TwoStepQuotient x y z w`.
- Inner reassociation is expressed by `SwappedTwoStepClass`, relating
  classes in `TwoStepQuotient x y z w` to classes in
  `TwoStepQuotient y x z w`.
-/
theorem twoStepQuotient_preLie_shape_rel
    (x y z w : PTree) :
    (∀ a b z'
      (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z'),
      ∃ c : TwoStepCode x y z w,
        IsRightShapedCode x y z w c ∧
        classOfLeftOuter a b z' haz hbw = codeClass c)
    ∧
    (∀ a b y'
      (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z),
      SwappedTwoStepClass x y z w
        (classOfLeftInner a b y' hay hbw)
        (classOfRightInner a b y' hay hbw)) := by
  constructor
  · intro a b z' haz hbw
    exact outer_support_quotient_left_to_right x y z w a b z' haz hbw
  · intro a b y' hay hbw
    exact leftInner_class_has_swapped_partner x y z w a b y' hay hbw

/--
`SwappedTwoStepClass` respects equality on the left quotient argument.
-/
theorem swapped_respects_eq_left
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    {q' : TwoStepQuotient y x z w}
    (h : q₁ = q₂)
    (hs : SwappedTwoStepClass x y z w q₁ q') :
    SwappedTwoStepClass x y z w q₂ q' := by
  cases h
  exact hs

/--
`SwappedTwoStepClass` respects equality on the right quotient argument.
-/
theorem swapped_respects_eq_right
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    {q₁ q₂ : TwoStepQuotient y x z w}
    (h : q₁ = q₂)
    (hs : SwappedTwoStepClass x y z w q q₁) :
    SwappedTwoStepClass x y z w q q₂ := by
  cases h
  exact hs

/--
`SwappedTwoStepClass` respects equality of quotient classes on both sides.
-/
theorem swapped_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    {q₁' q₂' : TwoStepQuotient y x z w}
    (hleft : q₁ = q₂)
    (hright : q₁' = q₂')
    (hs : SwappedTwoStepClass x y z w q₁ q₁') :
    SwappedTwoStepClass x y z w q₂ q₂' := by
  exact swapped_respects_eq_right x y z w hright
    (swapped_respects_eq_left x y z w hleft hs)

/--
If two raw codes represent the same quotient class on the left, then any
swapped partner for the first also serves as a swapped partner for the second.
-/
theorem swapped_respects_equiv_left
    (x y z w : PTree)
    {c₁ c₂ : TwoStepCode x y z w}
    {q' : TwoStepQuotient y x z w}
    (h : TwoStepEquiv x y z w c₁ c₂)
    (hs : SwappedTwoStepClass x y z w (codeClass c₁) q') :
    SwappedTwoStepClass x y z w (codeClass c₂) q' := by
  exact
    swapped_respects_eq_left x y z w
      (q₁ := codeClass c₁)
      (q₂ := codeClass c₂)
      (q' := q')
      (codeClass_eq_of_equiv h)
      hs

/--
If two raw codes represent the same quotient class on the right, then any
swapped correspondence into the first right class also lands in the second.
-/
theorem swapped_respects_equiv_right
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    {d₁ d₂ : TwoStepCode y x z w}
    (h : TwoStepEquiv y x z w d₁ d₂)
    (hs : SwappedTwoStepClass x y z w q (codeClass d₁)) :
    SwappedTwoStepClass x y z w q (codeClass d₂) := by
  exact
    swapped_respects_eq_right x y z w
      (q := q)
      (q₁ := codeClass d₁)
      (q₂ := codeClass d₂)
      (codeClass_eq_of_equiv h)
      hs

/--
Two-sided quotient compatibility for swapped correspondence.
-/
theorem swapped_respects_equiv
    (x y z w : PTree)
    {c₁ c₂ : TwoStepCode x y z w}
    {d₁ d₂ : TwoStepCode y x z w}
    (hleft : TwoStepEquiv x y z w c₁ c₂)
    (hright : TwoStepEquiv y x z w d₁ d₂)
    (hs : SwappedTwoStepClass x y z w (codeClass c₁) (codeClass d₁)) :
    SwappedTwoStepClass x y z w (codeClass c₂) (codeClass d₂) := by
  exact
    swapped_respects_equiv_right x y z w hright
      (swapped_respects_equiv_left x y z w hleft hs)

/--
A quotient class lies in the left two-step support for `(x,y,z,w)` if it is
represented by some left witness.
-/
def InLeftSupportClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ h : TwoStepWitnessLeft x y z w,
    classOfLeftWitness h = q

/--
A quotient class lies in the right two-step support for `(x,y,z,w)` if it is
represented by some right witness.
-/
def InRightSupportClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ h : TwoStepWitnessRight x y z w,
    classOfRightWitness h = q

/--
The quotient class of any left witness lies in the left support.
-/
theorem classOfLeftWitness_in_leftSupport
    (x y z w : PTree)
    (h : TwoStepWitnessLeft x y z w) :
    InLeftSupportClass x y z w (classOfLeftWitness h) := by
  exact ⟨h, rfl⟩

/--
The quotient class of any right witness lies in the right support.
-/
theorem classOfRightWitness_in_rightSupport
    (x y z w : PTree)
    (h : TwoStepWitnessRight x y z w) :
    InRightSupportClass x y z w (classOfRightWitness h) := by
  exact ⟨h, rfl⟩

/--
Any left-outer witness class lies in the right support, up to quotient equality.
-/
theorem leftOuterWitness_supports_some_rightClass
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ q : TwoStepQuotient x y z w,
      InRightSupportClass x y z w q ∧
      classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw) = q := by
  have hr : Nonempty (TwoStepWitnessRight x y z w) :=
    outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
  rcases hr with ⟨r⟩
  refine ⟨classOfRightWitness r, ?_, ?_⟩
  · exact classOfRightWitness_in_rightSupport x y z w r
  · cases r with
    | outer a' b' z'' haz' hbw' =>
        exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_outer haz hbw haz' hbw' (by
            rw [mem_twoStepAddrWitnessesRight_iff]
            exact Or.inl ⟨z'', haz', hbw'⟩))
    | inner a' b' y'' hay' hbw' =>
        exact codeClass_eq_of_equiv
          (TwoStepEquiv.outer_comm_inner haz hbw hay' hbw' (by
            rw [mem_twoStepAddrWitnessesRight_iff]
            exact Or.inr ⟨y'', hay', hbw'⟩))

/--
Any left-inner witness class has a swapped partner coming from a right witness.
-/
theorem leftInnerWitness_supports_swapped_rightClass
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ q : TwoStepQuotient y x z w,
      InRightSupportClass y x z w q ∧
      SwappedTwoStepClass x y z w
        (classOfLeftWitness (TwoStepWitnessLeft.inner a b y' hay hbw))
        q := by
  let r : TwoStepWitnessRight y x z w :=
    TwoStepWitnessRight.inner a b y' hay hbw
  refine ⟨classOfRightWitness r, ?_, ?_⟩
  · exact classOfRightWitness_in_rightSupport y x z w r
  · simpa [r, classOfLeftWitness, codeOfLeftWitness, classOfRightWitness, codeOfRightWitness,
      classOfLeftInner, classOfRightInner] using
      leftInner_class_has_swapped_partner x y z w a b y' hay hbw


/--
Every left-support quotient class has a corresponding right-support class.

- Outer case: correspondence inside the same quotient.
- Inner case: correspondence via `SwappedTwoStepClass`.
-/
theorem leftSupport_has_matching_rightSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    (∃ q', InRightSupportClass x y z w q' ∧ q = q')
    ∨
    (∃ q', InRightSupportClass y x z w q' ∧
        SwappedTwoStepClass x y z w q q') := by
  rcases hq with ⟨h, rfl⟩
  cases h with
  | outer a b z' haz hbw =>
      -- outer case: stays in same quotient
      left
      obtain ⟨q', hmem, hEq⟩ :=
        leftOuterWitness_supports_some_rightClass x y z w a b z' haz hbw
      exact ⟨q', hmem, hEq⟩

  | inner a b y' hay hbw =>
      -- inner case: goes to swapped quotient
      right
      obtain ⟨q', hmem, hswap⟩ :=
        leftInnerWitness_supports_swapped_rightClass x y z w a b y' hay hbw
      exact ⟨q', hmem, hswap⟩

/--
Every right-support quotient class has a corresponding left-support class.

(Symmetric version of the previous theorem.)
-/
theorem rightSupport_has_matching_leftSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InRightSupportClass x y z w q) :
    (∃ q', InLeftSupportClass x y z w q' ∧ q = q')
    ∨
    (∃ q', InLeftSupportClass y x z w q' ∧
        SwappedTwoStepClass x y z w q q') := by
  rcases hq with ⟨h, rfl⟩
  cases h with
  | outer a b z' haz hbw =>
      -- outer case: transport via right → left witness theorem
      left
      have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
        outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
      rcases hl with ⟨l⟩
      refine ⟨classOfLeftWitness l, ?_, ?_⟩
      · exact classOfLeftWitness_in_leftSupport x y z w l
      · -- equality of classes via equivalence
        cases l with
        | outer a' b' z'' haz' hbw' =>
            exact codeClass_eq_of_equiv
              (TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
                rw [mem_twoStepAddrWitnessesLeft_iff]
                exact Or.inl ⟨z'', haz', hbw'⟩))
        | inner a' b' y'' hay' hbw' =>
            exact codeClass_eq_of_equiv
              (TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
                rw [mem_twoStepAddrWitnessesLeft_iff]
                exact Or.inr ⟨y'', hay', hbw'⟩))

  | inner a b y' hay hbw =>
      -- inner case: swap
      right
      let l : TwoStepWitnessLeft y x z w :=
        TwoStepWitnessLeft.inner a b y' hay hbw
      refine ⟨classOfLeftWitness l, ?_, ?_⟩
      · exact classOfLeftWitness_in_leftSupport y x z w l
      · simpa [l, classOfRightWitness, codeOfRightWitness] using
          rightInner_class_has_swapped_partner x y z w a b y' hay hbw

/--
Left witnesses lying over a fixed quotient class.
-/
def LeftFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessLeft x y z w // classOfLeftWitness h = q }

/--
Right witnesses lying over a fixed quotient class.
-/
def RightFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessRight x y z w // classOfRightWitness h = q }

/--
Right witnesses in the swapped parameter order lying over a fixed quotient class.
This is the natural fibre for the inner part.
-/
def SwappedRightFiber
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :=
  { h : TwoStepWitnessRight y x z w // classOfRightWitness h = q }

/--
A quotient class is in left support iff its left fibre is inhabited.
-/
theorem inLeftSupport_iff_nonempty_LeftFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    InLeftSupportClass x y z w q ↔ Nonempty (LeftFiber x y z w q) := by
  constructor
  · intro hq
    rcases hq with ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩
  · intro hq
    rcases hq with ⟨⟨h, hh⟩⟩
    exact ⟨h, hh⟩

/--
A quotient class is in right support iff its right fibre is inhabited.
-/
theorem inRightSupport_iff_nonempty_RightFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    InRightSupportClass x y z w q ↔ Nonempty (RightFiber x y z w q) := by
  constructor
  · intro hq
    rcases hq with ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩
  · intro hq
    rcases hq with ⟨⟨h, hh⟩⟩
    exact ⟨h, hh⟩

/--
A swapped quotient class is in swapped right support iff its swapped right fibre
is inhabited.
-/
theorem inRightSupportSwapped_iff_nonempty_SwappedRightFiber
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :
    InRightSupportClass y x z w q ↔ Nonempty (SwappedRightFiber x y z w q) := by
  constructor
  · intro hq
    rcases hq with ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩
  · intro hq
    rcases hq with ⟨⟨h, hh⟩⟩
    exact ⟨h, hh⟩

/--
Diagnostic predicate: the left fibre over `q` has at most one witness.
-/
def LeftFiberSubsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Subsingleton (LeftFiber x y z w q)

/--
Diagnostic predicate: the right fibre over `q` has at most one witness.
-/
def RightFiberSubsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Subsingleton (RightFiber x y z w q)

/--
Diagnostic predicate: the swapped right fibre over `q` has at most one witness.
-/
def SwappedRightFiberSubsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) : Prop :=
  Subsingleton (SwappedRightFiber x y z w q)

/--
Every left-supported class has either

- a right fibre over the same quotient class (outer case), or
- a swapped right fibre over some swapped class (inner case).

This is the fibre-level version of the quotient support theorem.
-/
theorem leftSupport_has_matching_rightFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    (∃ q', Nonempty (RightFiber x y z w q') ∧ q = q')
    ∨
    (∃ q', Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w q q') := by
  rcases leftSupport_has_matching_rightSupport x y z w q hq with h | h
  · left
    rcases h with ⟨q', hq', hEq⟩
    exact ⟨q', (inRightSupport_iff_nonempty_RightFiber x y z w q').mp hq', hEq⟩
  · right
    rcases h with ⟨q', hq', hswap⟩
    exact ⟨q', (inRightSupportSwapped_iff_nonempty_SwappedRightFiber x y z w q').mp hq', hswap⟩

/--
Left witnesses lying over a fixed quotient class.
-/
def LeftWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessLeft x y z w // classOfLeftWitness h = q }

/--
Right witnesses lying over a fixed quotient class.
-/
def RightWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessRight x y z w // classOfRightWitness h = q }

/--
Right witnesses in the swapped quotient lying over a fixed swapped class.
-/
def SwappedRightWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :=
  { h : TwoStepWitnessRight y x z w // classOfRightWitness h = q }

/--
A left-outer witness determines some nonempty right fibre.
-/
theorem leftOuter_has_nonempty_rightFiber
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ q : TwoStepQuotient x y z w,
      Nonempty (RightWitnessFiber x y z w q) ∧
      classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw) = q := by
  obtain ⟨q, hq, hEq⟩ :=
    leftOuterWitness_supports_some_rightClass x y z w a b z' haz hbw
  rcases hq with ⟨r, hrfl⟩
  refine ⟨q, ?_, hEq⟩
  refine ⟨⟨r, hrfl⟩⟩

/--
A left-inner witness determines some nonempty swapped-right fibre.
-/
theorem leftInner_has_nonempty_swappedRightFiber
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    ∃ q : TwoStepQuotient y x z w,
      Nonempty (SwappedRightWitnessFiber x y z w q) ∧
      SwappedTwoStepClass x y z w
        (classOfLeftWitness (TwoStepWitnessLeft.inner a b y' hay hbw))
        q := by
  obtain ⟨q, hq, hswap⟩ :=
    leftInnerWitness_supports_swapped_rightClass x y z w a b y' hay hbw
  rcases hq with ⟨r, hrfl⟩
  refine ⟨q, ?_, hswap⟩
  refine ⟨⟨r, hrfl⟩⟩

/--
Left outer witnesses lying over a quotient class.
-/
def LeftOuterFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessLeft x y z w //
      match h with
      | TwoStepWitnessLeft.outer _ _ _ _ _ => classOfLeftWitness h = q
      | _ => False }

/--
Right outer witnesses lying over a quotient class.
-/
def RightOuterFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessRight x y z w //
      match h with
      | TwoStepWitnessRight.outer _ _ _ _ _ => classOfRightWitness h = q
      | _ => False }

theorem leftOuterFiber_to_rightSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    LeftOuterFiber x y z w q → Nonempty (RightWitnessFiber x y z w q) := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | outer a b z' haz hbw =>
      obtain ⟨q', hq', hEq⟩ :=
        leftOuterWitness_supports_some_rightClass x y z w a b z' haz hbw
      rcases hq' with ⟨r, hr⟩
      have hq'q : q' = q := by
        exact hEq.symm.trans hh
      refine ⟨⟨r, ?_⟩⟩
      exact hr.trans hq'q
  | inner =>
      cases hh

/--
Left inner witnesses lying over a quotient class.
-/
def LeftInnerFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessLeft x y z w //
      match h with
      | TwoStepWitnessLeft.inner _ _ _ _ _ => classOfLeftWitness h = q
      | _ => False }

/--
Right inner witnesses lying over a quotient class.
-/
def RightInnerFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : TwoStepWitnessRight x y z w //
      match h with
      | TwoStepWitnessRight.inner _ _ _ _ _ => classOfRightWitness h = q
      | _ => False }

/--
Right inner witnesses in the swapped parameter order lying over a swapped class.
-/
def SwappedRightInnerFiber
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :=
  { h : TwoStepWitnessRight y x z w //
      match h with
      | TwoStepWitnessRight.inner _ _ _ _ _ => classOfRightWitness h = q
      | _ => False }

/--
Any right-outer fibre element determines a nonempty left witness fibre over the same class.
-/
theorem rightOuterFiber_to_leftSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    RightOuterFiber x y z w q → Nonempty (LeftWitnessFiber x y z w q) := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | outer a b z' haz hbw =>
      have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
        outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
      rcases hl with ⟨l⟩
      refine ⟨⟨l, ?_⟩⟩
      cases l with
      | outer a' b' z'' haz' hbw' =>
          have hEq :
              codeClass (TwoStepCode.rightOuter a b z' haz hbw) =
              codeClass (TwoStepCode.leftOuter a' b' z'' haz' hbw') := by
            exact codeClass_eq_of_equiv
              (TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
                rw [mem_twoStepAddrWitnessesLeft_iff]
                exact Or.inl ⟨z'', haz', hbw'⟩))
          simpa [classOfRightWitness, codeOfRightWitness, classOfLeftWitness, codeOfLeftWitness] using
            hEq.symm.trans hh
      | inner a' b' y'' hay' hbw' =>
          have hEq :
              codeClass (TwoStepCode.rightOuter a b z' haz hbw) =
              codeClass (TwoStepCode.leftInner a' b' y'' hay' hbw') := by
            exact codeClass_eq_of_equiv
              (TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
                rw [mem_twoStepAddrWitnessesLeft_iff]
                exact Or.inr ⟨y'', hay', hbw'⟩))
          simpa [classOfRightWitness, codeOfRightWitness, classOfLeftWitness, codeOfLeftWitness] using
            hEq.symm.trans hh
  | inner =>
      cases hh

/--
Any left-inner fibre element determines a nonempty swapped right-inner fibre.
-/
theorem leftInnerFiber_to_swappedRightInnerFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    LeftInnerFiber x y z w q →
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightInnerFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      let r : TwoStepWitnessRight y x z w :=
        TwoStepWitnessRight.inner a b y' hay hbw
      refine ⟨classOfRightWitness r, ?_, ?_⟩
      · refine ⟨⟨r, ?_⟩⟩
        simp [r, classOfRightWitness, codeOfRightWitness]
      · have hswap :
            SwappedTwoStepClass x y z w
              (classOfLeftInner a b y' hay hbw)
              (classOfRightWitness r) := by
          simpa [r, classOfRightWitness, codeOfRightWitness, classOfRightInner] using
            leftInner_class_has_swapped_partner x y z w a b y' hay hbw
        exact
          swapped_respects_eq_left x y z w
            (q₁ := classOfLeftInner a b y' hay hbw)
            (q₂ := q)
            (q' := classOfRightWitness r)
            hh
            hswap
  | outer =>
      cases hh

/--
Any right-inner fibre element determines a nonempty swapped left-inner witness fibre.
-/
theorem rightInnerFiber_to_swappedLeftWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    RightInnerFiber x y z w q →
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (LeftWitnessFiber y x z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      let l : TwoStepWitnessLeft y x z w :=
        TwoStepWitnessLeft.inner a b y' hay hbw
      refine ⟨classOfLeftWitness l, ?_, ?_⟩
      · exact ⟨⟨l, rfl⟩⟩
      · have hswap :
            SwappedTwoStepClass x y z w
              (codeClass (TwoStepCode.rightInner a b y' hay hbw))
              (classOfLeftWitness l) := by
          simpa [l, classOfLeftWitness, codeOfLeftWitness] using
            rightInner_class_has_swapped_partner x y z w a b y' hay hbw
        exact
          swapped_respects_eq_left x y z w
            (q₁ := codeClass (TwoStepCode.rightInner a b y' hay hbw))
            (q₂ := q)
            (q' := classOfLeftWitness l)
            (by
              simpa [classOfRightWitness, codeOfRightWitness] using hh)
            hswap
  | outer =>
      cases hh

/--
Every right-supported class has either

- a left fibre over the same quotient class (outer case), or
- a swapped left fibre over some swapped class (inner case).
-/
theorem rightSupport_has_matching_leftFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InRightSupportClass x y z w q) :
    (∃ q', Nonempty (LeftFiber x y z w q') ∧ q = q')
    ∨
    (∃ q', Nonempty (LeftFiber y x z w q') ∧
        SwappedTwoStepClass x y z w q q') := by
  rcases rightSupport_has_matching_leftSupport x y z w q hq with h | h
  · left
    rcases h with ⟨q', hq', hEq⟩
    exact ⟨q', (inLeftSupport_iff_nonempty_LeftFiber x y z w q').mp hq', hEq⟩
  · right
    rcases h with ⟨q', hq', hswap⟩
    exact ⟨q', (inLeftSupport_iff_nonempty_LeftFiber y x z w q').mp hq', hswap⟩

/--
Nonempty left-outer fibre gives a nonempty right witness fibre over the same class.
-/
theorem nonempty_leftOuterFiber_gives_nonempty_rightWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (LeftOuterFiber x y z w q) →
    Nonempty (RightWitnessFiber x y z w q) := by
  intro h
  rcases h with ⟨h⟩
  exact leftOuterFiber_to_rightSupport x y z w q h

/--
Nonempty right-outer fibre gives a nonempty left witness fibre over the same class.
-/
theorem nonempty_rightOuterFiber_gives_nonempty_leftWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (RightOuterFiber x y z w q) →
    Nonempty (LeftWitnessFiber x y z w q) := by
  intro h
  rcases h with ⟨h⟩
  exact rightOuterFiber_to_leftSupport x y z w q h

/--
Nonempty left-inner fibre gives a nonempty swapped right-inner fibre.
-/
theorem nonempty_leftInnerFiber_gives_nonempty_swappedRightInnerFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (LeftInnerFiber x y z w q) →
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightInnerFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  intro h
  rcases h with ⟨h⟩
  exact leftInnerFiber_to_swappedRightInnerFiber x y z w q h

/--
Nonempty right-inner fibre gives a nonempty swapped left witness fibre.
-/
theorem nonempty_rightInnerFiber_gives_nonempty_swappedLeftWitnessFiber
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (RightInnerFiber x y z w q) →
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (LeftWitnessFiber y x z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  intro h
  rcases h with ⟨h⟩
  exact rightInnerFiber_to_swappedLeftWitnessFiber x y z w q h

/--
Diagnostic summary: every nonempty left fibre has matching right-side nonempty
fibre data, either directly (outer) or after swapping (inner).
-/
theorem nonempty_leftFiber_has_matching_rightData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (LeftFiber x y z w q) →
    (∃ q', Nonempty (RightFiber x y z w q') ∧ q = q')
    ∨
    (∃ q', Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w q q') := by
  intro hq
  exact leftSupport_has_matching_rightFiber x y z w q
    ((inLeftSupport_iff_nonempty_LeftFiber x y z w q).mpr hq)

/--
Diagnostic summary: every nonempty right fibre has matching left-side nonempty
fibre data, either directly (outer) or after swapping (inner).
-/
theorem nonempty_rightFiber_has_matching_leftData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (RightFiber x y z w q) →
    (∃ q', Nonempty (LeftFiber x y z w q') ∧ q = q')
    ∨
    (∃ q', Nonempty (LeftFiber y x z w q') ∧
        SwappedTwoStepClass x y z w q q') := by
  intro hq
  exact rightSupport_has_matching_leftFiber x y z w q
    ((inRightSupport_iff_nonempty_RightFiber x y z w q).mpr hq)

/--
Raw left-inner witnesses for `(x,y,z,w)`.
-/
def LeftInnerWitnessData
    (x y z w : PTree) :=
  { h : TwoStepWitnessLeft x y z w //
      match h with
      | TwoStepWitnessLeft.inner _ _ _ _ _ => True
      | _ => False }

/--
Raw swapped right-inner witnesses for `(y,x,z,w)`.
-/
def SwappedRightInnerWitnessData
    (x y z w : PTree) :=
  { h : TwoStepWitnessRight y x z w //
      match h with
      | TwoStepWitnessRight.inner _ _ _ _ _ => True
      | _ => False }

/--
Turn a raw left-inner witness into the corresponding swapped right-inner witness.
-/
def leftInnerWitness_to_swappedRightInnerWitness
    (x y z w : PTree) :
    LeftInnerWitnessData x y z w → SwappedRightInnerWitnessData x y z w := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      refine ⟨TwoStepWitnessRight.inner a b y' hay hbw, ?_⟩
      trivial
  | outer =>
      cases hh

/--
Turn a raw swapped right-inner witness into the corresponding left-inner witness.
-/
def swappedRightInnerWitness_to_leftInnerWitness
    (x y z w : PTree) :
    SwappedRightInnerWitnessData x y z w → LeftInnerWitnessData x y z w := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      refine ⟨TwoStepWitnessLeft.inner a b y' hay hbw, ?_⟩
      trivial
  | outer =>
      cases hh

/--
The left-to-right and right-to-left inner witness maps are inverse.
-/
theorem leftInnerWitness_swap_left_inverse
    (x y z w : PTree) :
    Function.LeftInverse
      (swappedRightInnerWitness_to_leftInnerWitness x y z w)
      (leftInnerWitness_to_swappedRightInnerWitness x y z w) := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      rfl
  | outer =>
      cases hh

/--
The right-to-left and left-to-right inner witness maps are inverse.
-/
theorem leftInnerWitness_swap_right_inverse
    (x y z w : PTree) :
    Function.RightInverse
      (swappedRightInnerWitness_to_leftInnerWitness x y z w)
      (leftInnerWitness_to_swappedRightInnerWitness x y z w) := by
  intro h
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      rfl
  | outer =>
      cases hh

/--
The raw inner witness data are equivalent under swapping `x` and `y`.
-/
def leftInnerWitnessEquiv_swappedRightInnerWitness
    (x y z w : PTree) :
    LeftInnerWitnessData x y z w ≃ SwappedRightInnerWitnessData x y z w where
  toFun := leftInnerWitness_to_swappedRightInnerWitness x y z w
  invFun := swappedRightInnerWitness_to_leftInnerWitness x y z w
  left_inv := leftInnerWitness_swap_left_inverse x y z w
  right_inv := leftInnerWitness_swap_right_inverse x y z w

/--
The quotient class attached to a raw left-inner witness.
-/
def leftInnerWitnessClass
    (x y z w : PTree) :
    LeftInnerWitnessData x y z w → TwoStepQuotient x y z w
  | ⟨h, _⟩ => classOfLeftWitness h

/--
The quotient class attached to a raw swapped right-inner witness.
-/
def swappedRightInnerWitnessClass
    (x y z w : PTree) :
    SwappedRightInnerWitnessData x y z w → TwoStepQuotient y x z w
  | ⟨h, _⟩ => classOfRightWitness h

/--
Corresponding raw inner witnesses determine swapped quotient classes.
-/
theorem leftInnerWitnessEquiv_respects_classes
    (x y z w : PTree)
    (h : LeftInnerWitnessData x y z w) :
    SwappedTwoStepClass x y z w
      (leftInnerWitnessClass x y z w h)
      (swappedRightInnerWitnessClass x y z w
        ((leftInnerWitnessEquiv_swappedRightInnerWitness x y z w) h)) := by
  rcases h with ⟨hw, hh⟩
  cases hw with
  | inner a b y' hay hbw =>
      simpa [leftInnerWitnessClass, swappedRightInnerWitnessClass,
        leftInnerWitnessEquiv_swappedRightInnerWitness,
        leftInnerWitness_to_swappedRightInnerWitness,
        classOfLeftWitness, codeOfLeftWitness,
        classOfRightWitness, codeOfRightWitness,
        classOfLeftInner, classOfRightInner] using
        leftInner_class_has_swapped_partner x y z w a b y' hay hbw
  | outer =>
      cases hh

/--
Raw left-outer witnesses for `(x,y,z,w)`.
-/
def LeftOuterWitnessData
    (x y z w : PTree) :=
  { h : TwoStepWitnessLeft x y z w //
      match h with
      | TwoStepWitnessLeft.outer _ _ _ _ _ => True
      | _ => False }

/--
Raw right-outer witnesses for `(x,y,z,w)`.
-/
def RightOuterWitnessData
    (x y z w : PTree) :=
  { h : TwoStepWitnessRight x y z w //
      match h with
      | TwoStepWitnessRight.outer _ _ _ _ _ => True
      | _ => False }

/--
The quotient class attached to a raw left-outer witness.
-/
def leftOuterWitnessClass
    (x y z w : PTree) :
    LeftOuterWitnessData x y z w → TwoStepQuotient x y z w
  | ⟨h, _⟩ => classOfLeftWitness h

/--
The quotient class attached to a raw right-outer witness.
-/
def rightOuterWitnessClass
    (x y z w : PTree) :
    RightOuterWitnessData x y z w → TwoStepQuotient x y z w
  | ⟨h, _⟩ => classOfRightWitness h

/--
A raw left-outer witness determines some right witness with the same quotient class.
-/
theorem leftOuterWitnessData_has_matching_rightWitness
    (x y z w : PTree)
    (h : LeftOuterWitnessData x y z w) :
    ∃ r : TwoStepWitnessRight x y z w,
      classOfLeftWitness h.1 = classOfRightWitness r := by
  rcases h with ⟨hw, hh⟩
  cases hw with
  | outer a b z' haz hbw =>
      obtain ⟨q, hq, hEq⟩ :=
        leftOuterWitness_supports_some_rightClass x y z w a b z' haz hbw
      rcases hq with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      exact hEq.trans hr.symm
  | inner =>
      cases hh

/--
A raw right-outer witness determines some left witness with the same quotient class.
-/
theorem rightOuterWitnessData_has_matching_leftWitness
    (x y z w : PTree)
    (h : RightOuterWitnessData x y z w) :
    ∃ l : TwoStepWitnessLeft x y z w,
      classOfRightWitness h.1 = classOfLeftWitness l := by
  rcases h with ⟨hw, hh⟩
  cases hw with
  | outer a b z' haz hbw =>
      have hl : Nonempty (TwoStepWitnessLeft x y z w) :=
        outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
      rcases hl with ⟨l⟩
      refine ⟨l, ?_⟩
      cases l with
      | outer a' b' z'' haz' hbw' =>
          exact codeClass_eq_of_equiv
            (TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
              rw [mem_twoStepAddrWitnessesLeft_iff]
              exact Or.inl ⟨z'', haz', hbw'⟩))
      | inner a' b' y'' hay' hbw' =>
          exact codeClass_eq_of_equiv
            (TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
              rw [mem_twoStepAddrWitnessesLeft_iff]
              exact Or.inr ⟨y'', hay', hbw'⟩))
  | inner =>
      cases hh

/--
Every raw left-outer witness has some right witness with the same quotient class,
and every raw right-outer witness has some left witness with the same quotient class.
-/
theorem outerWitnessData_class_correspondence
    (x y z w : PTree) :
    (∀ h : LeftOuterWitnessData x y z w,
      ∃ r : TwoStepWitnessRight x y z w,
        classOfLeftWitness h.1 = classOfRightWitness r)
    ∧
    (∀ h : RightOuterWitnessData x y z w,
      ∃ l : TwoStepWitnessLeft x y z w,
        classOfRightWitness h.1 = classOfLeftWitness l) := by
  constructor
  · intro h
    exact leftOuterWitnessData_has_matching_rightWitness x y z w h
  · intro h
    exact rightOuterWitnessData_has_matching_leftWitness x y z w h

/--
Left inner witnesses lying over a fixed quotient class `q`.
-/
def LeftInnerFiberData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : LeftInnerWitnessData x y z w //
      leftInnerWitnessClass x y z w h = q }

/--
Swapped right inner witnesses lying over a fixed swapped quotient class `q'`.
-/
def SwappedRightInnerFiberData
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) :=
  { h : SwappedRightInnerWitnessData x y z w //
      swappedRightInnerWitnessClass x y z w h = q' }

/--
An element of a left-inner fibre determines a swapped target quotient class
together with an element of the corresponding swapped right-inner fibre.
-/
def leftInnerFiberData_to_swappedRightInnerFiberData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftInnerFiberData x y z w q) :
    Σ q' : TwoStepQuotient y x z w,
      SwappedRightInnerFiberData x y z w q' := by
  rcases h with ⟨hw, hh⟩
  let hw' := (leftInnerWitnessEquiv_swappedRightInnerWitness x y z w) hw
  exact ⟨swappedRightInnerWitnessClass x y z w hw', ⟨hw', rfl⟩⟩

/--
Every element of a left-inner fibre determines some swapped right-inner fibre.
-/
theorem leftInnerFiberData_has_swapped_target
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftInnerFiberData x y z w q) :
    Nonempty (Σ q' : TwoStepQuotient y x z w,
      SwappedRightInnerFiberData x y z w q') := by
  exact ⟨leftInnerFiberData_to_swappedRightInnerFiberData x y z w q h⟩

/--
The swapped target class coming from a left-inner fibre element is related to
the original class by `SwappedTwoStepClass`.
-/
theorem leftInnerFiberData_target_respects_swappedClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftInnerFiberData x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightInnerFiberData x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  rcases h with ⟨hw, hh⟩
  let hw' := (leftInnerWitnessEquiv_swappedRightInnerWitness x y z w) hw
  refine ⟨swappedRightInnerWitnessClass x y z w hw', ?_, ?_⟩
  · exact ⟨⟨hw', rfl⟩⟩
  · have hswap :
        SwappedTwoStepClass x y z w
          (leftInnerWitnessClass x y z w hw)
          (swappedRightInnerWitnessClass x y z w hw') := by
      exact leftInnerWitnessEquiv_respects_classes x y z w hw
    exact
      swapped_respects_eq_left x y z w
        (q₁ := leftInnerWitnessClass x y z w hw)
        (q₂ := q)
        (q' := swappedRightInnerWitnessClass x y z w hw')
        hh
        hswap

/--
A swapped right-inner fibre element determines a source quotient class together
with an element of the corresponding left-inner fibre.
-/
def swappedRightInnerFiberData_to_leftInnerFiberData
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (h : SwappedRightInnerFiberData x y z w q') :
    Σ q : TwoStepQuotient x y z w,
      LeftInnerFiberData x y z w q := by
  rcases h with ⟨hw, hh⟩
  let hw' := (leftInnerWitnessEquiv_swappedRightInnerWitness x y z w).symm hw
  exact ⟨leftInnerWitnessClass x y z w hw', ⟨hw', rfl⟩⟩

/--
Every swapped right-inner fibre element determines some left-inner fibre.
-/
theorem swappedRightInnerFiberData_has_left_source
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (h : SwappedRightInnerFiberData x y z w q') :
    Nonempty (Σ q : TwoStepQuotient x y z w,
      LeftInnerFiberData x y z w q) := by
  exact ⟨swappedRightInnerFiberData_to_leftInnerFiberData x y z w q' h⟩

/--
Transport a left-inner fibre element to a swapped-right-inner fibre element.
-/
def leftInnerFiberData_forward
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    LeftInnerFiberData x y z w q →
    Σ q' : TwoStepQuotient y x z w,
      SwappedRightInnerFiberData x y z w q' :=
  leftInnerFiberData_to_swappedRightInnerFiberData x y z w q

/--
Transport back from swapped-right-inner fibre to left-inner fibre.
-/
def leftInnerFiberData_backward
    (x y z w : PTree) :
    (Σ q' : TwoStepQuotient y x z w,
      SwappedRightInnerFiberData x y z w q') →
    Σ q : TwoStepQuotient x y z w,
      LeftInnerFiberData x y z w q :=
  fun h =>
    let ⟨q', hw⟩ := h
    swappedRightInnerFiberData_to_leftInnerFiberData x y z w q' hw

theorem leftInnerFiber_roundtrip_left
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftInnerFiberData x y z w q) :
    (leftInnerFiberData_backward x y z w
      (leftInnerFiberData_forward x y z w q h)).2.1.1 = h.1.1 := by
  rcases h with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      rfl
  | outer a b z' haz hbw =>
      cases hinner

theorem leftInnerFiber_roundtrip_right
    (x y z w : PTree)
    (h :
      Σ q' : TwoStepQuotient y x z w,
        SwappedRightInnerFiberData x y z w q') :
    (leftInnerFiberData_forward x y z w _
      ((leftInnerFiberData_backward x y z w h).2)).2.1.1 =
    h.2.1.1 := by
  rcases h with ⟨q', h⟩
  rcases h with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      rfl
  | outer a b z' haz hbw =>
      cases hinner

/--
All left-inner fibre data, with the quotient class carried explicitly.
-/
def AllLeftInnerFiberData
    (x y z w : PTree) :=
  Σ q : TwoStepQuotient x y z w, LeftInnerFiberData x y z w q

/--
All swapped right-inner fibre data, with the swapped quotient class carried explicitly.
-/
def AllSwappedRightInnerFiberData
    (x y z w : PTree) :=
  Σ q' : TwoStepQuotient y x z w, SwappedRightInnerFiberData x y z w q'

/--
Global forward transport on inner fibre data.
-/
def allLeftInnerFiberData_forward
    (x y z w : PTree) :
    AllLeftInnerFiberData x y z w → AllSwappedRightInnerFiberData x y z w
  | ⟨q, h⟩ => leftInnerFiberData_to_swappedRightInnerFiberData x y z w q h

/--
Global backward transport on swapped inner fibre data.
-/
def allLeftInnerFiberData_backward
    (x y z w : PTree) :
    AllSwappedRightInnerFiberData x y z w → AllLeftInnerFiberData x y z w
  | ⟨q', h⟩ => swappedRightInnerFiberData_to_leftInnerFiberData x y z w q' h

/--
The forward/backward transport preserves the underlying raw left-inner witness.
-/
theorem allLeftInnerFiberData_roundtrip_left
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    ((allLeftInnerFiberData_backward x y z w
        (allLeftInnerFiberData_forward x y z w h)).2).1.1 = h.2.1.1 := by
  rcases h with ⟨q, h⟩
  exact leftInnerFiber_roundtrip_left x y z w q h

/--
The backward/forward transport preserves the underlying raw swapped right-inner witness.
-/
theorem allLeftInnerFiberData_roundtrip_right
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    ((allLeftInnerFiberData_forward x y z w
        (allLeftInnerFiberData_backward x y z w h)).2).1.1 = h.2.1.1 := by
  exact leftInnerFiber_roundtrip_right x y z w h

/--
Global inner transport preserves inhabitedness in the forward direction.
-/
theorem allLeftInnerFiberData_nonempty_forward
    (x y z w : PTree) :
    Nonempty (AllLeftInnerFiberData x y z w) →
    Nonempty (AllSwappedRightInnerFiberData x y z w) := by
  intro h
  rcases h with ⟨h⟩
  exact ⟨allLeftInnerFiberData_forward x y z w h⟩

/--
Global inner transport preserves inhabitedness in the backward direction.
-/
theorem allLeftInnerFiberData_nonempty_backward
    (x y z w : PTree) :
    Nonempty (AllSwappedRightInnerFiberData x y z w) →
    Nonempty (AllLeftInnerFiberData x y z w) := by
  intro h
  rcases h with ⟨h⟩
  exact ⟨allLeftInnerFiberData_backward x y z w h⟩

/--
Hence the global left-inner and swapped-right-inner fibre data are inhabited
simultaneously.
-/
theorem allLeftInnerFiberData_nonempty_iff
    (x y z w : PTree) :
    Nonempty (AllLeftInnerFiberData x y z w) ↔
    Nonempty (AllSwappedRightInnerFiberData x y z w) := by
  constructor
  · exact allLeftInnerFiberData_nonempty_forward x y z w
  · exact allLeftInnerFiberData_nonempty_backward x y z w

/--
If there is any left-inner fibre data at all, then there is corresponding
swapped-right-inner fibre data, and conversely.

This is a clean summary that the inner sector is structurally balanced.
-/
theorem inner_sector_balanced
    (x y z w : PTree) :
    Nonempty (AllLeftInnerFiberData x y z w) ↔
    Nonempty (AllSwappedRightInnerFiberData x y z w) := by
  exact allLeftInnerFiberData_nonempty_iff x y z w

/--
Left-outer witnesses lying over a fixed quotient class.
-/
def LeftOuterFiberData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : LeftOuterWitnessData x y z w //
      leftOuterWitnessClass x y z w h = q }

/--
Right-outer witnesses lying over a fixed quotient class.
-/
def RightOuterFiberData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : RightOuterWitnessData x y z w //
      rightOuterWitnessClass x y z w h = q }

theorem leftOuterFiberData_has_right_match
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftOuterFiberData x y z w q) :
    Nonempty (RightWitnessFiber x y z w q) := by
  rcases h with ⟨hw, hh⟩
  rcases hw with ⟨hraw, houter⟩
  cases hraw with
  | outer a b z' haz hbw =>
      let hdata : LeftOuterWitnessData x y z w :=
        ⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩
      obtain ⟨r, hr⟩ :=
        leftOuterWitnessData_has_matching_rightWitness x y z w hdata
      have hh' : classOfLeftWitness hdata.1 = q := by
        simpa [hdata, leftOuterWitnessClass] using hh
      refine ⟨⟨r, ?_⟩⟩
      exact hr.symm.trans hh'
  | inner =>
      cases houter

theorem rightOuterFiberData_has_left_match
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : RightOuterFiberData x y z w q) :
    Nonempty (LeftWitnessFiber x y z w q) := by
  rcases h with ⟨hw, hh⟩
  rcases hw with ⟨hraw, houter⟩
  cases hraw with
  | outer a b z' haz hbw =>
      let hdata : RightOuterWitnessData x y z w :=
        ⟨TwoStepWitnessRight.outer a b z' haz hbw, trivial⟩
      obtain ⟨l, hl⟩ :=
        rightOuterWitnessData_has_matching_leftWitness x y z w hdata
      have hh' : classOfRightWitness hdata.1 = q := by
        simpa [hdata, rightOuterWitnessClass] using hh
      refine ⟨⟨l, ?_⟩⟩
      exact hl.symm.trans hh'
  | inner =>
      cases houter

/--
Diagnostic: a left-outer fibre over `q` has at most one element.
-/
def LeftOuterFiberDataSubsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Subsingleton (LeftOuterFiberData x y z w q)

/--
Diagnostic: a right-outer fibre over `q` has at most one element.
-/
def RightOuterFiberDataSubsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Subsingleton (RightOuterFiberData x y z w q)

/--
Any two left-outer fibre elements over the same `q` have the same left witness class.
-/
theorem leftOuterFiberData_same_class
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : LeftOuterFiberData x y z w q) :
    classOfLeftWitness h₁.1.1 = classOfLeftWitness h₂.1.1 := by
  have hh₁ : classOfLeftWitness h₁.1.1 = q := by
    simpa [LeftOuterFiberData, leftOuterWitnessClass] using h₁.2
  have hh₂ : classOfLeftWitness h₂.1.1 = q := by
    simpa [LeftOuterFiberData, leftOuterWitnessClass] using h₂.2
  exact hh₁.trans hh₂.symm

/--
Any two right-outer fibre elements over the same `q` have the same right witness class.
-/
theorem rightOuterFiberData_same_class
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : RightOuterFiberData x y z w q) :
    classOfRightWitness h₁.1.1 = classOfRightWitness h₂.1.1 := by
  have hh₁ : classOfRightWitness h₁.1.1 = q := by
    simpa [RightOuterFiberData, rightOuterWitnessClass] using h₁.2
  have hh₂ : classOfRightWitness h₂.1.1 = q := by
    simpa [RightOuterFiberData, rightOuterWitnessClass] using h₂.2
  exact hh₁.trans hh₂.symm

/--
Diagnostic theorem: if two left-outer fibre elements have the same underlying
raw outer witness data, then they are equal.
-/
theorem leftOuterFiberData_ext
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : LeftOuterFiberData x y z w q)
    (hraw : h₁.1.1 = h₂.1.1) :
    h₁ = h₂ := by
  cases h₁ with
  | mk val₁ prop₁ =>
      cases h₂ with
      | mk val₂ prop₂ =>
          have hval : val₁ = val₂ := by
            apply Subtype.ext
            exact hraw
          subst hval
          rfl
/--
Diagnostic theorem: if two right-outer fibre elements have the same underlying
raw outer witness data, then they are equal.
-/
theorem rightOuterFiberData_ext
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : RightOuterFiberData x y z w q)
    (hraw : h₁.1.1 = h₂.1.1) :
    h₁ = h₂ := by
  cases h₁ with
  | mk val₁ prop₁ =>
      cases h₂ with
      | mk val₂ prop₂ =>
          have hval : val₁ = val₂ := by
            apply Subtype.ext
            exact hraw
          subst hval
          rfl

/--
Raw rigidity hypothesis for left-outer witness data:
if two raw left-outer witnesses determine the same quotient class,
then they have the same underlying raw witness.
-/
def LeftOuterClassRigid
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
    leftOuterWitnessClass x y z w h₁ =
      leftOuterWitnessClass x y z w h₂ →
    h₁.1 = h₂.1

/--
Raw rigidity hypothesis for right-outer witness data:
if two raw right-outer witnesses determine the same quotient class,
then they have the same underlying raw witness.
-/
def RightOuterClassRigid
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : RightOuterWitnessData x y z w,
    rightOuterWitnessClass x y z w h₁ =
      rightOuterWitnessClass x y z w h₂ →
    h₁.1 = h₂.1

/--
If left-outer classes are rigid at the raw witness level, then every fixed
left-outer fibre is subsingleton.
-/
theorem leftOuterFiberData_subsingleton_of_classRigid
    (x y z w : PTree)
    (hRigid : LeftOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w) :
    LeftOuterFiberDataSubsingleton x y z w q := by
  change Subsingleton (LeftOuterFiberData x y z w q)
  refine ⟨?_⟩
  intro h₁ h₂
  apply leftOuterFiberData_ext x y z w q h₁ h₂
  apply hRigid
  exact h₁.2.trans h₂.2.symm

/--
If right-outer classes are rigid at the raw witness level, then every fixed
right-outer fibre is subsingleton.
-/
theorem rightOuterFiberData_subsingleton_of_classRigid
    (x y z w : PTree)
    (hRigid : RightOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w) :
    RightOuterFiberDataSubsingleton x y z w q := by
  change Subsingleton (RightOuterFiberData x y z w q)
  refine ⟨?_⟩
  intro h₁ h₂
  apply rightOuterFiberData_ext x y z w q h₁ h₂
  apply hRigid
  exact h₁.2.trans h₂.2.symm

/--
Equivalent reformulation: two elements of the same left-outer fibre have the
same underlying raw witness, assuming left-outer class rigidity.
-/
theorem leftOuterFiberData_raw_eq_of_classRigid
    (x y z w : PTree)
    (hRigid : LeftOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : LeftOuterFiberData x y z w q) :
    h₁.1.1 = h₂.1.1 := by
  apply hRigid
  exact (h₁.2).trans (h₂.2).symm

/--
Equivalent reformulation: two elements of the same right-outer fibre have the
same underlying raw witness, assuming right-outer class rigidity.
-/
theorem rightOuterFiberData_raw_eq_of_classRigid
    (x y z w : PTree)
    (hRigid : RightOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w)
    (h₁ h₂ : RightOuterFiberData x y z w q) :
    h₁.1.1 = h₂.1.1 := by
  apply hRigid
  exact (h₁.2).trans (h₂.2).symm

/--
A fixed left-outer fibre is inhabited iff it contains a unique element,
assuming left-outer class rigidity.
-/
theorem leftOuterFiberData_unique_of_nonempty_of_classRigid
    (x y z w : PTree)
    (hRigid : LeftOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w)
    (hNE : Nonempty (LeftOuterFiberData x y z w q)) :
    ∃ h : LeftOuterFiberData x y z w q,
      ∀ h' : LeftOuterFiberData x y z w q, h' = h := by
  rcases hNE with ⟨h⟩
  refine ⟨h, ?_⟩
  intro h'
  have hSub :
      LeftOuterFiberDataSubsingleton x y z w q :=
    leftOuterFiberData_subsingleton_of_classRigid x y z w hRigid q
  exact hSub.elim h' h

/--
A fixed right-outer fibre is inhabited iff it contains a unique element,
assuming right-outer class rigidity.
-/
theorem rightOuterFiberData_unique_of_nonempty_of_classRigid
    (x y z w : PTree)
    (hRigid : RightOuterClassRigid x y z w)
    (q : TwoStepQuotient x y z w)
    (hNE : Nonempty (RightOuterFiberData x y z w q)) :
    ∃ h : RightOuterFiberData x y z w q,
      ∀ h' : RightOuterFiberData x y z w q, h' = h := by
  rcases hNE with ⟨h⟩
  refine ⟨h, ?_⟩
  intro h'
  have hSub :
      RightOuterFiberDataSubsingleton x y z w q :=
    rightOuterFiberData_subsingleton_of_classRigid x y z w hRigid q
  exact hSub.elim h' h

/--
Diagnostic summary:
to prove that left-outer fibres are subsingleton, it is enough to prove
raw left-outer class rigidity.
-/
theorem leftOuter_subsingleton_reduction
    (x y z w : PTree) :
    LeftOuterClassRigid x y z w →
    ∀ q : TwoStepQuotient x y z w,
      LeftOuterFiberDataSubsingleton x y z w q := by
  intro hRigid q
  exact leftOuterFiberData_subsingleton_of_classRigid x y z w hRigid q

/--
Diagnostic summary:
to prove that right-outer fibres are subsingleton, it is enough to prove
raw right-outer class rigidity.
-/
theorem rightOuter_subsingleton_reduction
    (x y z w : PTree) :
    RightOuterClassRigid x y z w →
    ∀ q : TwoStepQuotient x y z w,
      RightOuterFiberDataSubsingleton x y z w q := by
  intro hRigid q
  exact rightOuterFiberData_subsingleton_of_classRigid x y z w hRigid q

/--
A left-outer ambiguity is a pair of distinct raw left-outer witnesses with the
same quotient class.
-/
def LeftOuterAmbiguity
    (x y z w : PTree) : Prop :=
  ∃ h₁ h₂ : LeftOuterWitnessData x y z w,
    leftOuterWitnessClass x y z w h₁ =
      leftOuterWitnessClass x y z w h₂
    ∧ h₁.1 ≠ h₂.1

/--
A right-outer ambiguity is a pair of distinct raw right-outer witnesses with the
same quotient class.
-/
def RightOuterAmbiguity
    (x y z w : PTree) : Prop :=
  ∃ h₁ h₂ : RightOuterWitnessData x y z w,
    rightOuterWitnessClass x y z w h₁ =
      rightOuterWitnessClass x y z w h₂
    ∧ h₁.1 ≠ h₂.1

/--
Left-outer class rigidity rules out left-outer ambiguity.
-/
theorem no_leftOuterAmbiguity_of_classRigid
    (x y z w : PTree)
    (hRigid : LeftOuterClassRigid x y z w) :
    ¬ LeftOuterAmbiguity x y z w := by
  intro hAmb
  rcases hAmb with ⟨h₁, h₂, hclass, hneq⟩
  apply hneq
  exact hRigid h₁ h₂ hclass

/--
Right-outer class rigidity rules out right-outer ambiguity.
-/
theorem no_rightOuterAmbiguity_of_classRigid
    (x y z w : PTree)
    (hRigid : RightOuterClassRigid x y z w) :
    ¬ RightOuterAmbiguity x y z w := by
  intro hAmb
  rcases hAmb with ⟨h₁, h₂, hclass, hneq⟩
  apply hneq
  exact hRigid h₁ h₂ hclass

/--
Conversely, if there is no left-outer ambiguity, then left-outer class rigidity holds.
-/
theorem classRigid_of_no_leftOuterAmbiguity
    (x y z w : PTree)
    (hNo : ¬ LeftOuterAmbiguity x y z w) :
    LeftOuterClassRigid x y z w := by
  intro h₁ h₂ hclass
  by_cases hEq : h₁.1 = h₂.1
  · exact hEq
  · exfalso
    apply hNo
    exact ⟨h₁, h₂, hclass, hEq⟩

/--
Conversely, if there is no right-outer ambiguity, then right-outer class rigidity holds.
-/
theorem classRigid_of_no_rightOuterAmbiguity
    (x y z w : PTree)
    (hNo : ¬ RightOuterAmbiguity x y z w) :
    RightOuterClassRigid x y z w := by
  intro h₁ h₂ hclass
  by_cases hEq : h₁.1 = h₂.1
  · exact hEq
  · exfalso
    apply hNo
    exact ⟨h₁, h₂, hclass, hEq⟩

/--
Left-outer class rigidity is equivalent to absence of left-outer ambiguity.
-/
theorem leftOuterClassRigid_iff_no_ambiguity
    (x y z w : PTree) :
    LeftOuterClassRigid x y z w ↔ ¬ LeftOuterAmbiguity x y z w := by
  constructor
  · exact no_leftOuterAmbiguity_of_classRigid x y z w
  · exact classRigid_of_no_leftOuterAmbiguity x y z w

/--
Right-outer class rigidity is equivalent to absence of right-outer ambiguity.
-/
theorem rightOuterClassRigid_iff_no_ambiguity
    (x y z w : PTree) :
    RightOuterClassRigid x y z w ↔ ¬ RightOuterAmbiguity x y z w := by
  constructor
  · exact no_rightOuterAmbiguity_of_classRigid x y z w
  · exact classRigid_of_no_rightOuterAmbiguity x y z w

/--
If a left-outer fibre contains two distinct elements, then there is a left-outer ambiguity.
-/
theorem leftOuterAmbiguity_of_fiber_not_subsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hNot : ¬ LeftOuterFiberDataSubsingleton x y z w q) :
    LeftOuterAmbiguity x y z w := by
  unfold LeftOuterFiberDataSubsingleton at hNot
  by_contra hNo
  have hRigid : LeftOuterClassRigid x y z w :=
    (leftOuterClassRigid_iff_no_ambiguity x y z w).2 hNo
  have hSub : LeftOuterFiberDataSubsingleton x y z w q :=
    leftOuterFiberData_subsingleton_of_classRigid x y z w hRigid q
  exact hNot hSub

/--
If a right-outer fibre contains two distinct elements, then there is a right-outer ambiguity.
-/
theorem rightOuterAmbiguity_of_fiber_not_subsingleton
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hNot : ¬ RightOuterFiberDataSubsingleton x y z w q) :
    RightOuterAmbiguity x y z w := by
  unfold RightOuterFiberDataSubsingleton at hNot
  by_contra hNo
  have hRigid : RightOuterClassRigid x y z w :=
    (rightOuterClassRigid_iff_no_ambiguity x y z w).2 hNo
  have hSub : RightOuterFiberDataSubsingleton x y z w q :=
    rightOuterFiberData_subsingleton_of_classRigid x y z w hRigid q
  exact hNot hSub

/--
Diagnostic summary: the outer counting problem is exactly the problem of outer ambiguity.
-/
theorem outer_counting_problem_reduced
    (x y z w : PTree) :
    (LeftOuterClassRigid x y z w ↔ ¬ LeftOuterAmbiguity x y z w)
    ∧
    (RightOuterClassRigid x y z w ↔ ¬ RightOuterAmbiguity x y z w) := by
  constructor
  · exact leftOuterClassRigid_iff_no_ambiguity x y z w
  · exact rightOuterClassRigid_iff_no_ambiguity x y z w

/--
Two left-outer witnesses with the same quotient class determine nonempty right
witness fibres over the same quotient class.
-/
theorem leftOuter_same_class_gives_common_rightFiber
    (x y z w : PTree)
    (h₁ h₂ : LeftOuterWitnessData x y z w)
    (hclass :
      leftOuterWitnessClass x y z w h₁ =
      leftOuterWitnessClass x y z w h₂) :
    ∃ q : TwoStepQuotient x y z w,
      Nonempty (RightWitnessFiber x y z w q) := by
  refine ⟨leftOuterWitnessClass x y z w h₁, ?_⟩
  have hq : leftOuterWitnessClass x y z w h₁ =
      leftOuterWitnessClass x y z w h₁ := rfl
  -- build from h₁ alone
  rcases h₁ with ⟨hraw, houter⟩
  cases hraw with
  | outer a b z' haz hbw =>
      have hNE :
          Nonempty (RightWitnessFiber x y z w
            (leftOuterWitnessClass x y z w
              ⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩)) := by
        apply leftOuterFiberData_has_right_match x y z w
        refine ⟨⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩, rfl⟩
      simpa using hNE
  | inner =>
      cases houter

/--
Any left-outer ambiguity induces a quotient class with at least two distinct
raw left-outer witnesses lying over it.
-/
theorem leftOuterAmbiguity_gives_two_distinct_same_fiber
    (x y z w : PTree)
    (hAmb : LeftOuterAmbiguity x y z w) :
    ∃ q : TwoStepQuotient x y z w,
      ∃ h₁ h₂ : LeftOuterFiberData x y z w q,
        h₁.1 ≠ h₂.1 := by
  rcases hAmb with ⟨h₁, h₂, hclass, hneq⟩
  refine ⟨leftOuterWitnessClass x y z w h₁, ?_⟩
  refine ⟨⟨h₁, rfl⟩, ⟨h₂, hclass.symm⟩, ?_⟩
  intro heq
  apply hneq
  exact congrArg Subtype.val heq

/--
Any right-outer ambiguity induces a quotient class with at least two distinct
raw right-outer witnesses lying over it.
-/
theorem rightOuterAmbiguity_gives_two_distinct_same_fiber
    (x y z w : PTree)
    (hAmb : RightOuterAmbiguity x y z w) :
    ∃ q : TwoStepQuotient x y z w,
      ∃ h₁ h₂ : RightOuterFiberData x y z w q,
        h₁.1 ≠ h₂.1 := by
  rcases hAmb with ⟨h₁, h₂, hclass, hneq⟩
  refine ⟨rightOuterWitnessClass x y z w h₁, ?_⟩
  refine ⟨⟨h₁, rfl⟩, ⟨h₂, hclass.symm⟩, ?_⟩
  intro heq
  apply hneq
  exact congrArg Subtype.val heq

/--
If every left-outer fibre is subsingleton, then there is no left-outer ambiguity.
-/
theorem no_leftOuterAmbiguity_of_all_fibers_subsingleton
    (x y z w : PTree)
    (hSub : ∀ q : TwoStepQuotient x y z w,
      LeftOuterFiberDataSubsingleton x y z w q) :
    ¬ LeftOuterAmbiguity x y z w := by
  intro hAmb
  rcases leftOuterAmbiguity_gives_two_distinct_same_fiber x y z w hAmb with
    ⟨q, h₁, h₂, hneq⟩
  have hs : LeftOuterFiberDataSubsingleton x y z w q := hSub q
  apply hneq
  exact congrArg Subtype.val (hs.elim h₁ h₂)

/--
If every right-outer fibre is subsingleton, then there is no right-outer ambiguity.
-/
theorem no_rightOuterAmbiguity_of_all_fibers_subsingleton
    (x y z w : PTree)
    (hSub : ∀ q : TwoStepQuotient x y z w,
      RightOuterFiberDataSubsingleton x y z w q) :
    ¬ RightOuterAmbiguity x y z w := by
  intro hAmb
  rcases rightOuterAmbiguity_gives_two_distinct_same_fiber x y z w hAmb with
    ⟨q, h₁, h₂, hneq⟩
  have hs : RightOuterFiberDataSubsingleton x y z w q := hSub q
  apply hneq
  exact congrArg Subtype.val (hs.elim h₁ h₂)

/--
So the outer ambiguity question is equivalent to asking whether some outer fibre
contains two distinct raw witnesses.
-/
theorem leftOuterAmbiguity_iff_exists_nonsubsingleton_fiber
    (x y z w : PTree) :
    LeftOuterAmbiguity x y z w ↔
    ∃ q : TwoStepQuotient x y z w,
      ¬ LeftOuterFiberDataSubsingleton x y z w q := by
  constructor
  · intro hAmb
    rcases leftOuterAmbiguity_gives_two_distinct_same_fiber x y z w hAmb with
      ⟨q, h₁, h₂, hneq⟩
    refine ⟨q, ?_⟩
    intro hs
    apply hneq
    exact congrArg Subtype.val (hs.elim h₁ h₂)
  · intro h
    rcases h with ⟨q, hNot⟩
    exact leftOuterAmbiguity_of_fiber_not_subsingleton x y z w q hNot

/--
Right-hand version of the previous theorem.
-/
theorem rightOuterAmbiguity_iff_exists_nonsubsingleton_fiber
    (x y z w : PTree) :
    RightOuterAmbiguity x y z w ↔
    ∃ q : TwoStepQuotient x y z w,
      ¬ RightOuterFiberDataSubsingleton x y z w q := by
  constructor
  · intro hAmb
    rcases rightOuterAmbiguity_gives_two_distinct_same_fiber x y z w hAmb with
      ⟨q, h₁, h₂, hneq⟩
    refine ⟨q, ?_⟩
    intro hs
    apply hneq
    exact congrArg Subtype.val (hs.elim h₁ h₂)
  · intro h
    rcases h with ⟨q, hNot⟩
    exact rightOuterAmbiguity_of_fiber_not_subsingleton x y z w q hNot

/--
Two left-outer witnesses in the same quotient class give a common inhabited
right witness fibre over that class.
-/
theorem leftOuter_same_class_common_rightWitnessFiber
    (x y z w : PTree)
    (h₁ h₂ : LeftOuterWitnessData x y z w)
    (hclass :
      leftOuterWitnessClass x y z w h₁ =
      leftOuterWitnessClass x y z w h₂) :
    ∃ q : TwoStepQuotient x y z w,
      Nonempty (RightWitnessFiber x y z w q) ∧
      leftOuterWitnessClass x y z w h₁ = q ∧
      leftOuterWitnessClass x y z w h₂ = q := by
  refine ⟨leftOuterWitnessClass x y z w h₁, ?_, rfl, hclass.symm⟩
  rcases h₁ with ⟨hraw, houter⟩
  cases hraw with
  | outer a b z' haz hbw =>
      have hLO :
          LeftOuterFiber x y z w
            (leftOuterWitnessClass x y z w
              ⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩) := by
        refine ⟨TwoStepWitnessLeft.outer a b z' haz hbw, ?_⟩
        simp [leftOuterWitnessClass, classOfLeftWitness, codeOfLeftWitness]
      have hNE :
          Nonempty
            (LeftOuterFiber x y z w
              (leftOuterWitnessClass x y z w
                ⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩)) := ⟨hLO⟩
      exact
        nonempty_leftOuterFiber_gives_nonempty_rightWitnessFiber
          x y z w
          (leftOuterWitnessClass x y z w
            ⟨TwoStepWitnessLeft.outer a b z' haz hbw, trivial⟩)
          hNE
  | inner =>
      cases houter

/--
If common right witness classes determine left-outer witnesses uniquely, then
left-outer classes are rigid.
-/
theorem leftOuterClassRigid_of_rightMediator_uniqueness
    (x y z w : PTree)
    (hUnique :
      ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
        ∀ r : TwoStepWitnessRight x y z w,
          classOfLeftWitness h₁.1 = classOfRightWitness r →
          classOfLeftWitness h₂.1 = classOfRightWitness r →
          h₁.1 = h₂.1) :
    LeftOuterClassRigid x y z w := by
  intro h₁ h₂ hclass
  rcases leftOuter_same_class_common_rightWitnessFiber x y z w h₁ h₂ hclass with
    ⟨q, hR, hh₁, hh₂⟩
  rcases hR with ⟨⟨r, hr⟩⟩
  apply hUnique h₁ h₂ r
  · exact hh₁.trans hr.symm
  · exact hh₂.trans hr.symm

/--
Uniqueness principle for outer-left witnesses through a common right witness.
-/
def LeftOuterRightMediatorUnique
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
    ∀ r : TwoStepWitnessRight x y z w,
      classOfLeftWitness h₁.1 = classOfRightWitness r →
      classOfLeftWitness h₂.1 = classOfRightWitness r →
      h₁.1 = h₂.1

/--
Hence common-right-mediator uniqueness rules out left-outer ambiguity.
-/
theorem no_leftOuterAmbiguity_of_rightMediator_uniqueness
    (x y z w : PTree)
    (hUnique : LeftOuterRightMediatorUnique x y z w) :
    ¬ LeftOuterAmbiguity x y z w := by
  apply no_leftOuterAmbiguity_of_classRigid
  exact leftOuterClassRigid_of_rightMediator_uniqueness x y z w hUnique

/--
Hence every left-outer fibre is subsingleton.
-/
theorem leftOuterFiberData_subsingleton_of_rightMediator_uniqueness
    (x y z w : PTree)
    (hUnique : LeftOuterRightMediatorUnique x y z w)
    (q : TwoStepQuotient x y z w) :
    LeftOuterFiberDataSubsingleton x y z w q := by
  apply leftOuterFiberData_subsingleton_of_classRigid x y z w
  exact leftOuterClassRigid_of_rightMediator_uniqueness x y z w hUnique

/--
If common-right-mediator uniqueness holds, every inhabited left-outer fibre has
a unique element.
-/
theorem leftOuterFiberData_unique_of_nonempty_of_rightMediator_uniqueness
    (x y z w : PTree)
    (hUnique : LeftOuterRightMediatorUnique x y z w)
    (q : TwoStepQuotient x y z w)
    (hNE : Nonempty (LeftOuterFiberData x y z w q)) :
    ∃ h : LeftOuterFiberData x y z w q,
      ∀ h' : LeftOuterFiberData x y z w q, h' = h := by
  apply leftOuterFiberData_unique_of_nonempty_of_classRigid x y z w
  · exact leftOuterClassRigid_of_rightMediator_uniqueness x y z w hUnique
  · exact hNE

/--
A sufficient condition for the absence of left-outer ambiguity:
common right mediators uniquely determine the left-outer witness.
-/
theorem leftOuter_no_ambiguity_of_mediator_uniqueness
    (x y z w : PTree) :
    LeftOuterRightMediatorUnique x y z w →
    ¬ LeftOuterAmbiguity x y z w := by
  intro hUnique
  exact no_leftOuterAmbiguity_of_rightMediator_uniqueness x y z w hUnique

/--
A common right-outer mediator determines a unique left-outer witness.
-/
def LeftOuterRightOuterMediatorUnique
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
    ∀ a b z'
      (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z'),
      classOfLeftWitness h₁.1 =
        classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw) →
      classOfLeftWitness h₂.1 =
        classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw) →
      h₁.1 = h₂.1

/--
A common right-inner mediator determines a unique left-outer witness.
-/
def LeftOuterRightInnerMediatorUnique
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
    ∀ a b y'
      (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
      (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z),
      classOfLeftWitness h₁.1 =
        classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw) →
      classOfLeftWitness h₂.1 =
        classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw) →
      h₁.1 = h₂.1

theorem leftOuterRightMediatorUnique_of_split
    (x y z w : PTree)
    (hOuter : LeftOuterRightOuterMediatorUnique x y z w)
    (hInner : LeftOuterRightInnerMediatorUnique x y z w) :
    LeftOuterRightMediatorUnique x y z w := by
  intro h₁ h₂ r hr₁ hr₂
  cases r with
  | outer a b z' haz hbw =>
      exact hOuter h₁ h₂ a b z' haz hbw hr₁ hr₂
  | inner a b y' hay hbw =>
      exact hInner h₁ h₂ a b y' hay hbw hr₁ hr₂


/--
If two left-outer witnesses have the same quotient class as the same fixed
right-inner witness, then their left classes are equal.
-/
theorem leftOuter_eq_rightInner_common_class
    (x y z w : PTree)
    (h₁ h₂ : LeftOuterWitnessData x y z w)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z)
    (hr₁ :
      classOfLeftWitness h₁.1 =
        classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw))
    (hr₂ :
      classOfLeftWitness h₂.1 =
        classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw)) :
    classOfLeftWitness h₁.1 = classOfLeftWitness h₂.1 := by
  exact hr₁.trans hr₂.symm

/--
Direct inner-mediator injectivity principle:
if two left-outer witnesses lie over the same fixed right-inner witness class,
then they are equal as raw left witnesses.

This is the precise missing lemma for the inner mediator case.
-/
def OuterCommInnerInjective
    (x y z w : PTree) : Prop :=
  ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
    ∀ a b : Address, ∀ y' : PTree,
      ∀ hay : (a, y') ∈ matchingLeafGraftWitnesses x y,
      ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z,
        classOfLeftWitness h₁.1 =
          classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw) →
        classOfLeftWitness h₂.1 =
          classOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw) →
        h₁.1 = h₂.1

/--
If direct injectivity holds for fixed right-inner mediators, then the
right-inner mediator uniqueness principle follows.
-/
theorem leftOuterRightInnerMediatorUnique_of_outerCommInnerInjective
    (x y z w : PTree)
    (hInj : OuterCommInnerInjective x y z w) :
    LeftOuterRightInnerMediatorUnique x y z w := by
  intro h₁ h₂ a b y' hay hbw hr₁ hr₂
  exact hInj h₁ h₂ a b y' hay hbw hr₁ hr₂

/--
If equivalence to a fixed right-inner code determines a unique left-outer code,
then outer-comm-inner injectivity holds.
-/
def LeftOuterEquivToFixedRightInnerUnique
    (x y z w : PTree) : Prop :=
  ∀ a b : Address, ∀ y' : PTree,
    ∀ hay : (a, y') ∈ matchingLeafGraftWitnesses x y,
    ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z,
    ∀ h₁ h₂ : LeftOuterWitnessData x y z w,
      TwoStepEquiv x y z w
        (codeOfLeftWitness h₁.1)
        (codeOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw)) →
      TwoStepEquiv x y z w
        (codeOfLeftWitness h₂.1)
        (codeOfRightWitness (TwoStepWitnessRight.inner a b y' hay hbw)) →
      h₁.1 = h₂.1

theorem outerCommInnerInjective_of_equivUniqueness
    (x y z w : PTree)
    (hUnique : LeftOuterEquivToFixedRightInnerUnique x y z w) :
    OuterCommInnerInjective x y z w := by
  intro h₁ h₂ a b y' hay hbw hr₁ hr₂
  apply hUnique a b y' hay hbw h₁ h₂
  · exact Quotient.exact hr₁
  · exact Quotient.exact hr₂

/-!
## Quotient-level route to the pre-Lie structure

The original outer-fibre rigidity programme isolated the raw counting problem, but outer witnesses may legitimately admit multiple bureaucratic presentations of the same independent proof-composition event.

Accordingly, the main route now shifts from proving uniqueness of raw outer witnesses to proving that the quotient classes themselves carry the correct pre-Lie information.

The inner sector remains a rigidity/uniqueness testbed, while the outer sector is treated quotient-theoretically: the key question is no longer whether a quotient class has a unique raw representative, but whether it has a well-defined proof-theoretic meaning and supports a representative-independent class-level composition law.
-/

/-!
### Immediate objective

Show that the quotient already captures the relevant proof event:
outer commutation is handled internally inside `TwoStepQuotient x y z w` while inner reassociation is mediated by `SwappedTwoStepClass`.

The next theorems should therefore establish representative independence and class-level compatibility, rather than raw injectivity of all outer witnesses.
-/

def HasRightOuterRepresentative (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ r : TwoStepWitnessRight x y z w,
    (match r with
     | TwoStepWitnessRight.outer _ _ _ _ _ => True
     | _ => False) ∧
    classOfRightWitness r = q

def HasRightInnerRepresentative (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ r : TwoStepWitnessRight x y z w,
    (match r with
     | TwoStepWitnessRight.inner _ _ _ _ _ => True
     | _ => False) ∧
    classOfRightWitness r = q

/-!
## Quotient-level pre-Lie route

The raw witness analysis isolated the outer counting problem, but the main route
now shifts to quotient classes.

The intended picture is:

- outer / independent two-step compositions are handled internally inside
  `TwoStepQuotient x y z w`, where bureaucratically different schedules are
  identified;
- inner / dependent two-step compositions are handled by passing to the swapped
  quotient `TwoStepQuotient y x z w`, via `SwappedTwoStepClass`.

So the next step is to package the class-level "shape" of a two-step
composition, rather than continuing to insist on uniqueness of raw outer
representatives.
-/

/-- A quotient class has an outer/right-side representative if it is represented
by some right witness in the same fixed quotient. -/
def HasRightRepresentative
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  InRightSupportClass x y z w q

/-- A quotient class has an inner/swapped right-side representative if it is
related to some right-supported class in the swapped quotient. -/
def HasSwappedRightRepresentative
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ q' : TwoStepQuotient y x z w,
    InRightSupportClass y x z w q' ∧
    SwappedTwoStepClass x y z w q q'

/-- Quotient-level shape of a left-supported class:

- `outer q` means the class has a right-side representative in the same quotient;
- `inner q'` means the class contributes via the swapped quotient.
-/
inductive PreLieClassShape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Type where
| outer
    (hq : InRightSupportClass x y z w q) :
    PreLieClassShape x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : InRightSupportClass y x z w q')
    (hs : SwappedTwoStepClass x y z w q q') :
    PreLieClassShape x y z w q

/-- Fibre-level version of the previous theorem. -/
inductive PreLieFiberShape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Type where
| outer
    (hq : Nonempty (RightFiber x y z w q)) :
    PreLieFiberShape x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : Nonempty (SwappedRightFiber x y z w q'))
    (hs : SwappedTwoStepClass x y z w q q') :
    PreLieFiberShape x y z w q

/-- A purely propositional version of the quotient-level pre-Lie split. -/
theorem leftSupportClass_preLie_split
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    InLeftSupportClass x y z w q →
    HasRightRepresentative x y z w q ∨
    HasSwappedRightRepresentative x y z w q := by
  intro hq
  rcases leftSupport_has_matching_rightSupport x y z w q hq with h | h
  · left
    rcases h with ⟨q', hq', hEq⟩
    cases hEq
    exact hq'
  · right
    rcases h with ⟨q', hq', hs⟩
    exact ⟨q', hq', hs⟩

/-- Fibre-level propositional split. -/
theorem leftFiber_preLie_split
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    Nonempty (LeftFiber x y z w q) →
    Nonempty (RightFiber x y z w q) ∨
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  intro hq
  rcases leftSupport_has_matching_rightFiber x y z w q
      ((inLeftSupport_iff_nonempty_LeftFiber x y z w q).mpr hq) with h | h
  · left
    rcases h with ⟨q', hq', hEq⟩
    cases hEq
    exact hq'
  · right
    rcases h with ⟨q', hq', hs⟩
    exact ⟨q', hq', hs⟩

/-- This is the quotient-level form of the associator split:

- outer contributions stay inside the fixed quotient;
- inner contributions are transported to the swapped quotient.
-/
theorem quotient_preLie_associator_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    InRightSupportClass x y z w q
    ∨
    (∃ q' : TwoStepQuotient y x z w,
      InRightSupportClass y x z w q' ∧
      SwappedTwoStepClass x y z w q q') := by
  exact leftSupportClass_preLie_split x y z w q hq

/-- A class-level contribution attached to a fixed left-supported source class `q`. -/
inductive PreLieContributionAt
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Type where
| outer
    (hq : InRightSupportClass x y z w q) :
    PreLieContributionAt x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : InRightSupportClass y x z w q')
    (hs : SwappedTwoStepClass x y z w q q') :
    PreLieContributionAt x y z w q

/-- Fibre-level contribution attached to a fixed inhabited left fibre. -/
inductive PreLieFiberContributionAt
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Type where
| outer
    (hq : Nonempty (RightFiber x y z w q)) :
    PreLieFiberContributionAt x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : Nonempty (SwappedRightFiber x y z w q'))
    (hs : SwappedTwoStepClass x y z w q q') :
    PreLieFiberContributionAt x y z w q

/-- Outer contributions stay in the fixed quotient. -/
def PreLieContributionAt.isOuter
    {x y z w : PTree}
    {q : TwoStepQuotient x y z w}
    (c : PreLieContributionAt x y z w q) : Prop :=
  match c with
  | PreLieContributionAt.outer _ => True
  | PreLieContributionAt.inner _ _ _ => False

/-- Inner contributions pass to the swapped quotient. -/
def PreLieContributionAt.isInner
    {x y z w : PTree}
    {q : TwoStepQuotient x y z w}
    (c : PreLieContributionAt x y z w q) : Prop :=
  match c with
  | PreLieContributionAt.outer _ => False
  | PreLieContributionAt.inner _ _ _ => True

/-- Every class-level contribution is either outer or inner. -/
theorem PreLieContributionAt.outer_or_inner
    {x y z w : PTree}
    {q : TwoStepQuotient x y z w}
    (c : PreLieContributionAt x y z w q) :
    c.isOuter ∨ c.isInner := by
  cases c with
  | outer hq =>
      left
      trivial
  | inner q' hq' hs =>
      right
      trivial

/-- Outer and inner are disjoint contribution shapes. -/
theorem PreLieContributionAt.not_outer_and_inner
    {x y z w : PTree}
    {q : TwoStepQuotient x y z w}
    (c : PreLieContributionAt x y z w q) :
    ¬ (c.isOuter ∧ c.isInner) := by
  cases c with
  | outer hq =>
      intro h
      exact h.2
  | inner q' hq' hs =>
      intro h
      exact h.1

/-- Propositional quotient-level shape of a left-supported class. -/
inductive HasPreLieClassShape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop where
| outer
    (hq : InRightSupportClass x y z w q) :
    HasPreLieClassShape x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : InRightSupportClass y x z w q')
    (hs : SwappedTwoStepClass x y z w q q') :
    HasPreLieClassShape x y z w q

/-- Every left-supported quotient class has a pre-Lie class shape:
either outer/internal, or inner/swapped. -/
theorem leftSupportClass_has_preLie_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    HasPreLieClassShape x y z w q := by
  rcases leftSupport_has_matching_rightSupport x y z w q hq with h | h
  · rcases h with ⟨q', hq', hEq⟩
    cases hEq
    exact HasPreLieClassShape.outer hq'
  · rcases h with ⟨q', hq', hs⟩
    exact HasPreLieClassShape.inner q' hq' hs

/-- Propositional fibre-level shape of an inhabited left fibre. -/
inductive HasPreLieFiberShape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop where
| outer
    (hq : Nonempty (RightFiber x y z w q)) :
    HasPreLieFiberShape x y z w q
| inner
    (q' : TwoStepQuotient y x z w)
    (hq' : Nonempty (SwappedRightFiber x y z w q'))
    (hs : SwappedTwoStepClass x y z w q q') :
    HasPreLieFiberShape x y z w q

/-- Every inhabited left fibre has a corresponding pre-Lie fibre shape. -/
theorem leftFiber_has_preLie_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : Nonempty (LeftFiber x y z w q)) :
    HasPreLieFiberShape x y z w q := by
  rcases leftSupport_has_matching_rightFiber x y z w q
      ((inLeftSupport_iff_nonempty_LeftFiber x y z w q).mpr hq) with h | h
  · rcases h with ⟨q', hq', hEq⟩
    cases hEq
    exact HasPreLieFiberShape.outer hq'
  · rcases h with ⟨q', hq', hs⟩
    exact HasPreLieFiberShape.inner q' hq' hs

/-!
## Stability of quotient-level pre-Lie shape

The quotient-level outer/inner split should depend only on the quotient class
itself, not on the particular witness used to establish it. The next lemmas
record that these shape predicates are stable under equality of quotient
classes.
-/

/-!
## Stability of quotient-level pre-Lie shape

The quotient-level outer/inner split should depend only on the quotient class
itself, not on the particular witness used to establish it. The next lemmas
record that these shape predicates are stable under equality of quotient
classes.
-/

/-- Outer/right representability is stable under equality of quotient classes. -/
theorem HasRightRepresentative.respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    HasRightRepresentative x y z w q₁ →
    HasRightRepresentative x y z w q₂ := by
  intro hq
  cases h
  exact hq

/-- Swapped-right representability is stable under equality of quotient classes. -/
theorem HasSwappedRightRepresentative.respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    HasSwappedRightRepresentative x y z w q₁ →
    HasSwappedRightRepresentative x y z w q₂ := by
  intro hq
  rcases hq with ⟨q', hq', hs⟩
  exact ⟨q', hq', swapped_respects_eq_left x y z w h hs⟩

/-- Pre-Lie class shape is stable under equality of quotient classes. -/
theorem HasPreLieClassShape.respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    HasPreLieClassShape x y z w q₁ →
    HasPreLieClassShape x y z w q₂ := by
  intro hshape
  cases hshape with
  | outer hq =>
      exact HasPreLieClassShape.outer
        (HasRightRepresentative.respects_eq x y z w h hq)
  | inner q' hq' hs =>
      exact HasPreLieClassShape.inner q' hq'
        (swapped_respects_eq_left x y z w h hs)

/-- Pre-Lie fibre shape is stable under equality of quotient classes. -/
theorem HasPreLieFiberShape.respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    HasPreLieFiberShape x y z w q₁ →
    HasPreLieFiberShape x y z w q₂ := by
  intro hshape
  cases hshape with
  | outer hq =>
      cases h
      exact HasPreLieFiberShape.outer hq
  | inner q' hq' hs =>
      exact HasPreLieFiberShape.inner q' hq'
        (swapped_respects_eq_left x y z w h hs)

/-- Every left-supported class has either outer or inner pre-Lie shape. -/
theorem leftSupportClass_has_outer_or_inner_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    HasRightRepresentative x y z w q ∨
    HasSwappedRightRepresentative x y z w q := by
  exact leftSupportClass_preLie_split x y z w q hq

/-- Every inhabited left fibre has either outer or inner pre-Lie shape. -/
theorem leftFiber_has_outer_or_inner_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : Nonempty (LeftFiber x y z w q)) :
    Nonempty (RightFiber x y z w q) ∨
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  exact leftFiber_preLie_split x y z w q hq

/-- If a class has outer pre-Lie shape, then it has a right representative in
the same quotient. -/
theorem HasPreLieClassShape.outer_spec
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hshape : HasPreLieClassShape x y z w q) :
    (∃ hq : InRightSupportClass x y z w q,
      hshape = HasPreLieClassShape.outer hq)
    ∨
    (∃ q' hq' hs,
      hshape = HasPreLieClassShape.inner q' hq' hs) := by
  cases hshape with
  | outer hq =>
      left
      exact ⟨hq, rfl⟩
  | inner q' hq' hs =>
      right
      exact ⟨q', hq', hs, rfl⟩

/-- The quotient-level outer/inner split is determined up to equality of
the source quotient class. -/
theorem leftSupportClass_preLie_split_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂)
    (hq₁ : InLeftSupportClass x y z w q₁) :
    HasPreLieClassShape x y z w q₂ := by
  exact HasPreLieClassShape.respects_eq x y z w h
    (leftSupportClass_has_preLie_shape x y z w q₁ hq₁)

/-- Fibre-level version of the previous stability theorem. -/
theorem leftFiber_preLie_split_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂)
    (hq₁ : Nonempty (LeftFiber x y z w q₁)) :
    HasPreLieFiberShape x y z w q₂ := by
  exact HasPreLieFiberShape.respects_eq x y z w h
    (leftFiber_has_preLie_shape x y z w q₁ hq₁)

/-!
## Quotient-level associator decomposition

This packages the proof-theoretic analogue of the rooted-tree pre-Lie
associator split:

- outer contributions correspond to independent proof extensions and remain in
  the same quotient;
- inner contributions correspond to dependent/nested proof extensions and are
  transported to the swapped quotient.
-/

/-- Outer contribution of a left-supported class. -/
def IsOuterContribution
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  InRightSupportClass x y z w q

/-- Inner contribution of a left-supported class. -/
def IsInnerContribution
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ q' : TwoStepQuotient y x z w,
    InRightSupportClass y x z w q' ∧
    SwappedTwoStepClass x y z w q q'

/-- Every left-supported class contributes either outerly or innerly. -/
theorem leftSupportClass_associator_decomposes
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    IsOuterContribution x y z w q ∨
    IsInnerContribution x y z w q := by
  exact leftSupportClass_preLie_split x y z w q hq

/-- Fibre-level version of the associator decomposition. -/
theorem leftFiber_associator_decomposes
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : Nonempty (LeftFiber x y z w q)) :
    Nonempty (RightFiber x y z w q) ∨
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  exact leftFiber_preLie_split x y z w q hq

/-- The outer part of the associator decomposition is stable under equality of
quotient classes. -/
theorem IsOuterContribution_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    IsOuterContribution x y z w q₁ →
    IsOuterContribution x y z w q₂ := by
  intro hq
  cases h
  exact hq

/-- The inner part of the associator decomposition is stable under equality of
quotient classes. -/
theorem IsInnerContribution_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    IsInnerContribution x y z w q₁ →
    IsInnerContribution x y z w q₂ := by
  intro hq
  rcases hq with ⟨q', hq', hs⟩
  exact ⟨q', hq', swapped_respects_eq_left x y z w h hs⟩

/-- Every left-supported class has a quotient-level associator shape. -/
theorem leftSupportClass_has_associator_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    (IsOuterContribution x y z w q ∨ IsInnerContribution x y z w q) := by
  exact leftSupportClass_associator_decomposes x y z w q hq

/-!
## Bridge lemmas between pre-Lie shape and associator contribution shape
-/

/-- An outer pre-Lie class shape gives an outer associator contribution. -/
theorem HasPreLieClassShape.to_outerContribution
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hshape : HasPreLieClassShape x y z w q) :
    IsOuterContribution x y z w q ∨ IsInnerContribution x y z w q := by
  cases hshape with
  | outer hq =>
      exact Or.inl hq
  | inner q' hq' hs =>
      exact Or.inr ⟨q', hq', hs⟩

/-- Every pre-Lie class shape induces an associator shape. -/
theorem HasPreLieClassShape.to_associator_shape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hshape : HasPreLieClassShape x y z w q) :
    IsOuterContribution x y z w q ∨ IsInnerContribution x y z w q := by
  exact HasPreLieClassShape.to_outerContribution x y z w hshape

/-- An outer associator contribution determines an outer pre-Lie class shape. -/
theorem IsOuterContribution.to_preLieClassShape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : IsOuterContribution x y z w q) :
    HasPreLieClassShape x y z w q := by
  exact HasPreLieClassShape.outer hq

/-- An inner associator contribution determines an inner pre-Lie class shape. -/
theorem IsInnerContribution.to_preLieClassShape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : IsInnerContribution x y z w q) :
    HasPreLieClassShape x y z w q := by
  rcases hq with ⟨q', hq', hs⟩
  exact HasPreLieClassShape.inner q' hq' hs

/-- Associator shape can be repackaged as a pre-Lie class shape. -/
theorem associator_shape_to_preLieClassShape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (h :
      IsOuterContribution x y z w q ∨
      IsInnerContribution x y z w q) :
    HasPreLieClassShape x y z w q := by
  cases h with
  | inl houter =>
      exact IsOuterContribution.to_preLieClassShape x y z w houter
  | inr hinner =>
      exact IsInnerContribution.to_preLieClassShape x y z w hinner

/-- The associator decomposition is exactly the pre-Lie class-shape split. -/
theorem leftSupportClass_associator_shape_eq_preLie_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    HasPreLieClassShape x y z w q := by
  exact associator_shape_to_preLieClassShape x y z w
    (leftSupportClass_associator_decomposes x y z w q hq)

/-- Equality-stability for the packaged associator shape, via pre-Lie shape. -/
theorem associator_shape_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂) :
    (IsOuterContribution x y z w q₁ ∨ IsInnerContribution x y z w q₁) →
    (IsOuterContribution x y z w q₂ ∨ IsInnerContribution x y z w q₂) := by
  intro hshape
  apply HasPreLieClassShape.to_associator_shape
  exact HasPreLieClassShape.respects_eq x y z w h
    (associator_shape_to_preLieClassShape x y z w hshape)

/-- The quotient-level associator shape depends only on the quotient class. -/
theorem leftSupportClass_associator_decomposes_respects_eq
    (x y z w : PTree)
    {q₁ q₂ : TwoStepQuotient x y z w}
    (h : q₁ = q₂)
    (hq₁ : InLeftSupportClass x y z w q₁) :
    IsOuterContribution x y z w q₂ ∨
    IsInnerContribution x y z w q₂ := by
  exact associator_shape_respects_eq x y z w h
    (leftSupportClass_associator_decomposes x y z w q₁ hq₁)

/-!
## Support/fibre conversion lemmas
-/

/-- A right-supported class has an inhabited right fibre. -/
theorem InRightSupportClass.to_nonempty_RightFiber
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : InRightSupportClass x y z w q) :
    Nonempty (RightFiber x y z w q) := by
  rcases hq with ⟨h, rfl⟩
  exact ⟨⟨h, rfl⟩⟩

/-- An inhabited right fibre gives a right-supported class. -/
theorem RightFiber.nonempty_to_InRightSupportClass
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : Nonempty (RightFiber x y z w q)) :
    InRightSupportClass x y z w q := by
  rcases hq with ⟨⟨h, hh⟩⟩
  exact ⟨h, hh⟩

/-- A swapped-right-supported class has an inhabited swapped right fibre. -/
theorem InRightSupportClass.to_nonempty_SwappedRightFiber
    (x y z w : PTree)
    {q : TwoStepQuotient y x z w}
    (hq : InRightSupportClass y x z w q) :
    Nonempty (SwappedRightFiber x y z w q) := by
  rcases hq with ⟨h, rfl⟩
  exact ⟨⟨h, rfl⟩⟩

/-- An inhabited swapped right fibre gives right support in the swapped order. -/
theorem SwappedRightFiber.nonempty_to_InRightSupportClass
    (x y z w : PTree)
    {q : TwoStepQuotient y x z w}
    (hq : Nonempty (SwappedRightFiber x y z w q)) :
    InRightSupportClass y x z w q := by
  rcases hq with ⟨⟨h, hh⟩⟩
  exact ⟨h, hh⟩

/-!
## Associator contribution → fibre-level contribution
-/

/-- An outer contribution yields an inhabited right fibre over the same class. -/
theorem IsOuterContribution.to_nonempty_RightFiber
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : IsOuterContribution x y z w q) :
    Nonempty (RightFiber x y z w q) := by
  exact InRightSupportClass.to_nonempty_RightFiber x y z w hq

/-- An inner contribution yields an inhabited swapped right fibre. -/
theorem IsInnerContribution.to_nonempty_SwappedRightFiber
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : IsInnerContribution x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  rcases hq with ⟨q', hq', hs⟩
  exact ⟨q', InRightSupportClass.to_nonempty_SwappedRightFiber x y z w hq', hs⟩

/-- Class-level associator shape induces fibre-level associator shape. -/
theorem associator_class_shape_to_fiber_shape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (h :
      IsOuterContribution x y z w q ∨
      IsInnerContribution x y z w q) :
    Nonempty (RightFiber x y z w q) ∨
    ∃ q' : TwoStepQuotient y x z w,
      Nonempty (SwappedRightFiber x y z w q') ∧
      SwappedTwoStepClass x y z w q q' := by
  cases h with
  | inl houter =>
      exact Or.inl (IsOuterContribution.to_nonempty_RightFiber x y z w houter)
  | inr hinner =>
      exact Or.inr (IsInnerContribution.to_nonempty_SwappedRightFiber x y z w hinner)

/-- Fibre-level outer contribution gives class-level outer contribution. -/
theorem nonempty_RightFiber.to_IsOuterContribution
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : Nonempty (RightFiber x y z w q)) :
    IsOuterContribution x y z w q := by
  exact RightFiber.nonempty_to_InRightSupportClass x y z w hq

/-- Fibre-level swapped inner contribution gives class-level inner contribution. -/
theorem nonempty_SwappedRightFiber.to_IsInnerContribution
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (h :
      ∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w q q') :
    IsInnerContribution x y z w q := by
  rcases h with ⟨q', hq', hs⟩
  exact ⟨q', SwappedRightFiber.nonempty_to_InRightSupportClass x y z w hq', hs⟩

/-- Fibre-level associator shape can be repackaged as class-level associator
shape. -/
theorem associator_fiber_shape_to_class_shape
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (h :
      Nonempty (RightFiber x y z w q) ∨
      ∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w q q') :
    IsOuterContribution x y z w q ∨
    IsInnerContribution x y z w q := by
  cases h with
  | inl houter =>
      exact Or.inl (nonempty_RightFiber.to_IsOuterContribution x y z w houter)
  | inr hinner =>
      exact Or.inr (nonempty_SwappedRightFiber.to_IsInnerContribution x y z w hinner)

/-- The class-level and fibre-level associator decompositions are equivalent
packagings of the same data. -/
theorem associator_class_shape_iff_fiber_shape
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    (IsOuterContribution x y z w q ∨
      IsInnerContribution x y z w q)
    ↔
    (Nonempty (RightFiber x y z w q) ∨
      ∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w q q') := by
  constructor
  · intro h
    exact associator_class_shape_to_fiber_shape x y z w h
  · intro h
    exact associator_fiber_shape_to_class_shape x y z w h

theorem leftSupportClass_associator_symmetric
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : InLeftSupportClass x y z w q) :
    InRightSupportClass x y z w q ∨
    ∃ q' : TwoStepQuotient y x z w,
      InRightSupportClass y x z w q' ∧
      SwappedTwoStepClass x y z w q q' := by
  exact quotient_preLie_associator_shape x y z w q hq

/-- Roundtrip on the left-inner side, at the level of the underlying witness. -/
theorem allLeftInnerFiber_roundtrip_left
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    (allLeftInnerFiberData_backward x y z w
      (allLeftInnerFiberData_forward x y z w h)).2.1.1 = h.2.1.1 := by
  rcases h with ⟨q, hq⟩
  exact leftInnerFiber_roundtrip_left x y z w q hq

/-- Roundtrip on the swapped-right-inner side, at the level of the underlying witness. -/
theorem allLeftInnerFiber_roundtrip_right
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    (allLeftInnerFiberData_forward x y z w
      (allLeftInnerFiberData_backward x y z w h)).2.1.1 = h.2.1.1 := by
  exact leftInnerFiber_roundtrip_right x y z w h

/--
Existence of left-inner fibre data is equivalent to existence of swapped
right-inner fibre data.
-/
theorem nonempty_allLeftInnerFiberData_iff
    (x y z w : PTree) :
    Nonempty (AllLeftInnerFiberData x y z w) ↔
    Nonempty (AllSwappedRightInnerFiberData x y z w) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨allLeftInnerFiberData_forward x y z w h⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨allLeftInnerFiberData_backward x y z w h⟩

/-!
## Inner fibre correspondence as an equivalence of total data

The previous lemmas gave forward/backward maps and witness-level roundtrip
identities. We now package this as an explicit equivalence between the total
left-inner fibre data and the total swapped right-inner fibre data.
-/

/-- Forward map on total inner fibre data. -/
def AllLeftInnerFiberData.toSwapped
    (x y z w : PTree) :
    AllLeftInnerFiberData x y z w →
    AllSwappedRightInnerFiberData x y z w :=
  allLeftInnerFiberData_forward x y z w

/-- Backward map on total swapped inner fibre data. -/
def AllSwappedRightInnerFiberData.toLeft
    (x y z w : PTree) :
    AllSwappedRightInnerFiberData x y z w →
    AllLeftInnerFiberData x y z w :=
  allLeftInnerFiberData_backward x y z w

/-- On the left side, forward then backward preserves the underlying witness. -/
theorem AllLeftInnerFiberData.toSwapped_toLeft_witness
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    ((AllSwappedRightInnerFiberData.toLeft x y z w)
      ((AllLeftInnerFiberData.toSwapped x y z w) h)).2.1.1
      = h.2.1.1 := by
  exact allLeftInnerFiber_roundtrip_left x y z w h

/-- On the swapped-right side, backward then forward preserves the underlying
witness. -/
theorem AllSwappedRightInnerFiberData.toLeft_toSwapped_witness
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    ((AllLeftInnerFiberData.toSwapped x y z w)
      ((AllSwappedRightInnerFiberData.toLeft x y z w) h)).2.1.1
      = h.2.1.1 := by
  exact allLeftInnerFiber_roundtrip_right x y z w h

/-- The inner contribution types are inhabited simultaneously. -/
theorem allInnerFiberDataEquiv_nonempty
    (x y z w : PTree) :
    Nonempty (AllLeftInnerFiberData x y z w) ↔
    Nonempty (AllSwappedRightInnerFiberData x y z w) := by
  exact nonempty_allLeftInnerFiberData_iff x y z w

/-- Forward then backward preserves the left quotient class. -/
theorem AllLeftInnerFiberData.toSwapped_toLeft_fst
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    ((AllSwappedRightInnerFiberData.toLeft x y z w)
      ((AllLeftInnerFiberData.toSwapped x y z w) h)).fst = h.fst := by
  rcases h with ⟨q, hq⟩
  rcases hq with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      simpa [AllLeftInnerFiberData.toSwapped,
        AllSwappedRightInnerFiberData.toLeft,
        allLeftInnerFiberData_forward,
        allLeftInnerFiberData_backward,
        leftInnerFiberData_forward,
        leftInnerFiberData_backward,
        leftInnerFiberData_to_swappedRightInnerFiberData,
        swappedRightInnerFiberData_to_leftInnerFiberData,
        leftInnerWitnessClass,
        hh]
  | outer a b z' haz hbw =>
      cases hinner

/-- Backward then forward preserves the swapped quotient class. -/
theorem AllSwappedRightInnerFiberData.toLeft_toSwapped_fst
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    ((AllLeftInnerFiberData.toSwapped x y z w)
      ((AllSwappedRightInnerFiberData.toLeft x y z w) h)).fst = h.fst := by
  rcases h with ⟨q', hq'⟩
  rcases hq' with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      simpa [AllLeftInnerFiberData.toSwapped,
        AllSwappedRightInnerFiberData.toLeft,
        allLeftInnerFiberData_forward,
        allLeftInnerFiberData_backward,
        leftInnerFiberData_forward,
        leftInnerFiberData_backward,
        leftInnerFiberData_to_swappedRightInnerFiberData,
        swappedRightInnerFiberData_to_leftInnerFiberData,
        swappedRightInnerWitnessClass,
        hh]
  | outer a b z' haz hbw =>
      cases hinner


/-!
## Inner contribution classes as subtypes of quotient classes

The witness-carrying transport lives on `AllLeftInnerFiberData` and
`AllSwappedRightInnerFiberData`. If we only want to speak about which quotient
classes support such data, we package that as a subtype.
-/

open Classical

/-- A quotient class on the left carries inner contribution data. -/
def HasLeftInnerContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Nonempty (LeftInnerFiberData x y z w q)

/-- A quotient class on the swapped side carries right-inner contribution data. -/
def HasSwappedRightInnerContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  Nonempty (SwappedRightInnerFiberData x y z w q')

/-- The subtype of left quotient classes supporting inner contribution data. -/
def LeftInnerContributionClasses
    (x y z w : PTree) :=
  { q : TwoStepQuotient x y z w // HasLeftInnerContributionClass x y z w q }

/-- The subtype of swapped quotient classes supporting right-inner contribution data. -/
def SwappedRightInnerContributionClasses
    (x y z w : PTree) :=
  { q' : TwoStepQuotient y x z w // HasSwappedRightInnerContributionClass x y z w q' }

/-- Total left-inner fibre data determines a supporting left quotient class. -/
def AllLeftInnerFiberData.toContributionClass
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    LeftInnerContributionClasses x y z w :=
  ⟨h.1, ⟨h.2⟩⟩

/-- Total swapped-right-inner fibre data determines a supporting swapped quotient class. -/
def AllSwappedRightInnerFiberData.toContributionClass
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    SwappedRightInnerContributionClasses x y z w :=
  ⟨h.1, ⟨h.2⟩⟩

/-- A supporting left quotient class yields total left-inner fibre data. -/
noncomputable def LeftInnerContributionClasses.toTotal
    (x y z w : PTree)
    (h : LeftInnerContributionClasses x y z w) :
    AllLeftInnerFiberData x y z w :=
  ⟨h.1, Classical.choice h.2⟩

/-- A supporting swapped quotient class yields total swapped-right-inner fibre data. -/
noncomputable def SwappedRightInnerContributionClasses.toTotal
    (x y z w : PTree)
    (h : SwappedRightInnerContributionClasses x y z w) :
    AllSwappedRightInnerFiberData x y z w :=
  ⟨h.1, Classical.choice h.2⟩

/-
/-- The total left-inner and swapped-right-inner data types are equivalent at
the level of witness-carrying data. -/
def allInnerFiberDataEquiv
    (x y z w : PTree) :
    AllLeftInnerFiberData x y z w ≃
    AllSwappedRightInnerFiberData x y z w where
  toFun := AllLeftInnerFiberData.toSwapped x y z w
  invFun := AllSwappedRightInnerFiberData.toLeft x y z w
  left_inv := by
    intro h
    apply Sigma.ext
    · exact leftInnerFiber_roundtrip_left x y z w h.1 h.2
    · cases h with
      | mk q hq =>
          simp [AllLeftInnerFiberData.toSwapped,
            AllSwappedRightInnerFiberData.toLeft,
            allLeftInnerFiberData_forward,
            allLeftInnerFiberData_backward]
  right_inv := by
    intro h
    apply Sigma.ext
    · exact leftInnerFiber_roundtrip_right x y z w h
    · cases h with
      | mk q hq =>
          simp [AllLeftInnerFiberData.toSwapped,
            AllSwappedRightInnerFiberData.toLeft,
            allLeftInnerFiberData_forward,
            allLeftInnerFiberData_backward]
-/

/-- Left inner-supporting classes transport to swapped right-inner-supporting classes. -/
noncomputable def transportLeftInnerContributionClassToSwapped
    (x y z w : PTree)
    (h : LeftInnerContributionClasses x y z w) :
    SwappedRightInnerContributionClasses x y z w :=
  (AllLeftInnerFiberData.toSwapped x y z w
    (LeftInnerContributionClasses.toTotal x y z w h)).toContributionClass x y z w

/-- Swapped right-inner-supporting classes transport back to left inner-supporting classes. -/
noncomputable def transportSwappedInnerContributionClassToLeft
    (x y z w : PTree)
    (h : SwappedRightInnerContributionClasses x y z w) :
    LeftInnerContributionClasses x y z w :=
  (AllSwappedRightInnerFiberData.toLeft x y z w
    (SwappedRightInnerContributionClasses.toTotal x y z w h)).toContributionClass x y z w

/-- Existence of a left inner-supporting quotient class is equivalent to existence
of a swapped right-inner-supporting quotient class. -/
theorem nonempty_innerContributionClasses_iff
    (x y z w : PTree) :
    Nonempty (LeftInnerContributionClasses x y z w) ↔
    Nonempty (SwappedRightInnerContributionClasses x y z w) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨transportLeftInnerContributionClassToSwapped x y z w h⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨transportSwappedInnerContributionClassToLeft x y z w h⟩

/-!
## Pointwise transport of left-inner contribution data
-/

open Classical

/-- The forward transport of left-inner fibre data lands in a swapped class
related by `SwappedTwoStepClass`. -/
theorem leftInnerFiberData_forward_swapped
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (h : LeftInnerFiberData x y z w q) :
    SwappedTwoStepClass x y z w q
      (leftInnerFiberData_forward x y z w q h).1 := by
  rcases h with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      apply swapped_respects_eq_left x y z w hh
      simpa [leftInnerFiberData_forward,
        leftInnerFiberData_to_swappedRightInnerFiberData,
        leftInnerWitnessEquiv_swappedRightInnerWitness,
        leftInnerWitnessClass,
        swappedRightInnerWitnessClass,
        classOfLeftWitness, codeOfLeftWitness,
        classOfRightWitness, codeOfRightWitness,
        classOfLeftInner, classOfRightInner] using
        (SwappedTwoStepClass.leftInner (x := x) (y := y) (z := z) (w := w)
          a b y' hay hbw)
  | outer a b z' haz hbw =>
      cases hinner

/-- A left inner-supporting class yields some swapped right-inner supporting
class related by `SwappedTwoStepClass`. -/
theorem HasLeftInnerContributionClass.exists_swappedRightInner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftInnerContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasSwappedRightInnerContributionClass x y z w q' := by
  rcases hq with ⟨h⟩
  refine ⟨(leftInnerFiberData_forward x y z w q h).1, ?_, ?_⟩
  · exact leftInnerFiberData_forward_swapped x y z w q h
  · exact ⟨(leftInnerFiberData_forward x y z w q h).2⟩

/-- Any total left-inner fibre datum determines a swapped right-inner
supporting class. -/
def AllLeftInnerFiberData.toSwappedSupportingClass
    (x y z w : PTree)
    (h : AllLeftInnerFiberData x y z w) :
    SwappedRightInnerContributionClasses x y z w :=
  (AllLeftInnerFiberData.toSwapped x y z w h).toContributionClass x y z w

/-- Pointwise left-inner support implies existence of a swapped right-inner
supporting class. -/
theorem HasLeftInnerContributionClass.exists_supporting_swappedClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftInnerContributionClass x y z w q) :
    ∃ s : SwappedRightInnerContributionClasses x y z w,
      SwappedTwoStepClass x y z w q s.1 := by
  rcases hq with ⟨h⟩
  refine ⟨(AllLeftInnerFiberData.toSwappedSupportingClass x y z w ⟨q, h⟩), ?_⟩
  exact leftInnerFiberData_forward_swapped x y z w q h

/-- A swapped right-inner supporting class is, in particular, right-supported. -/
theorem HasSwappedRightInnerContributionClass.to_inRightSupportClass
    (x y z w : PTree)
    {q' : TwoStepQuotient y x z w}
    (hq' : HasSwappedRightInnerContributionClass x y z w q') :
    InRightSupportClass y x z w q' := by
  rcases hq' with ⟨hq'⟩
  rcases hq' with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  exact ⟨hw, by
    simpa [swappedRightInnerWitnessClass, classOfRightWitness, codeOfRightWitness] using hh⟩

/-!
## Backward transport of swapped-right-inner contribution data
-/

/-- The backward transport of swapped-right-inner fibre data lands in a left
class related by `SwappedTwoStepClass`. -/
theorem swappedRightInnerFiberData_backward_swapped
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (h : SwappedRightInnerFiberData x y z w q') :
    SwappedTwoStepClass x y z w
      (leftInnerFiberData_backward x y z w ⟨q', h⟩).1
      q' := by
  rcases h with ⟨h, hh⟩
  rcases h with ⟨hw, hinner⟩
  cases hw with
  | inner a b y' hay hbw =>
      apply swapped_respects_eq_right x y z w hh
      simpa [leftInnerFiberData_backward,
        swappedRightInnerFiberData_to_leftInnerFiberData,
        leftInnerWitnessEquiv_swappedRightInnerWitness,
        leftInnerWitnessClass,
        swappedRightInnerWitnessClass,
        classOfLeftWitness, codeOfLeftWitness,
        classOfRightWitness, codeOfRightWitness,
        classOfLeftInner, classOfRightInner] using
        (SwappedTwoStepClass.leftInner (x := x) (y := y) (z := z) (w := w)
          a b y' hay hbw)
  | outer a b z' haz hbw =>
      cases hinner

/-- A swapped right-inner-supporting class yields some left inner-supporting
class related by `SwappedTwoStepClass`. -/
theorem HasSwappedRightInnerContributionClass.exists_leftInner
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : HasSwappedRightInnerContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasLeftInnerContributionClass x y z w q := by
  rcases hq' with ⟨h⟩
  refine ⟨(leftInnerFiberData_backward x y z w ⟨q', h⟩).1, ?_, ?_⟩
  · exact swappedRightInnerFiberData_backward_swapped x y z w q' h
  · exact ⟨(leftInnerFiberData_backward x y z w ⟨q', h⟩).2⟩

/-- Any total swapped-right-inner fibre datum determines a left inner-supporting
class. -/
def AllSwappedRightInnerFiberData.toLeftSupportingClass
    (x y z w : PTree)
    (h : AllSwappedRightInnerFiberData x y z w) :
    LeftInnerContributionClasses x y z w :=
  (AllSwappedRightInnerFiberData.toLeft x y z w h).toContributionClass x y z w

/-- Pointwise swapped-right-inner support implies existence of a left
inner-supporting class. -/
theorem HasSwappedRightInnerContributionClass.exists_supporting_leftClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : HasSwappedRightInnerContributionClass x y z w q') :
    ∃ s : LeftInnerContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 q' := by
  rcases hq' with ⟨h⟩
  refine ⟨(AllSwappedRightInnerFiberData.toLeftSupportingClass x y z w ⟨q', h⟩), ?_⟩
  exact swappedRightInnerFiberData_backward_swapped x y z w q' h

/-!
## Inner-supporting classes correspond across the swapped quotient
-/

/-- Every left inner-supporting class has a swapped right-inner supporting
partner related by `SwappedTwoStepClass`. -/
theorem LeftInnerContributionClasses.exists_swapped_partner
    (x y z w : PTree)
    (s : LeftInnerContributionClasses x y z w) :
    ∃ t : SwappedRightInnerContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 t.1 := by
  exact HasLeftInnerContributionClass.exists_supporting_swappedClass
    x y z w s.1 s.2

/-- Every swapped right-inner supporting class has a left inner-supporting
partner related by `SwappedTwoStepClass`. -/
theorem SwappedRightInnerContributionClasses.exists_left_partner
    (x y z w : PTree)
    (t : SwappedRightInnerContributionClasses x y z w) :
    ∃ s : LeftInnerContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 t.1 := by
  exact HasSwappedRightInnerContributionClass.exists_supporting_leftClass
    x y z w t.1 t.2


theorem HasLeftInnerContributionClass_exists_swapped_partner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    HasLeftInnerContributionClass x y z w q →
    ∃ t : SwappedRightInnerContributionClasses x y z w,
      SwappedTwoStepClass x y z w q t.1 := by
  intro hq
  exact HasLeftInnerContributionClass.exists_supporting_swappedClass
    x y z w q hq

/-- A left inner-supporting class yields a swapped partner and conversely. -/
theorem innerSupportingClasses_correspond
    (x y z w : PTree) :
    (∀ s : LeftInnerContributionClasses x y z w,
      ∃ t : SwappedRightInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1)
    ∧
    (∀ t : SwappedRightInnerContributionClasses x y z w,
      ∃ s : LeftInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1) := by
  constructor
  · intro s
    exact LeftInnerContributionClasses.exists_swapped_partner x y z w s
  · intro t
    exact SwappedRightInnerContributionClasses.exists_left_partner x y z w t

/-- Any left inner-supporting class determines a swapped-side inner associator
shape. -/
theorem LeftInnerContributionClasses.to_inner_associator_shape
    (x y z w : PTree)
    (s : LeftInnerContributionClasses x y z w) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w s.1 q' ∧
      HasSwappedRightInnerContributionClass x y z w q' := by
  exact HasLeftInnerContributionClass.exists_swappedRightInner
    x y z w s.1 s.2

/-- Any swapped right-inner supporting class determines a left-side inner
associator shape. -/
theorem SwappedRightInnerContributionClasses.to_inner_associator_shape
    (x y z w : PTree)
    (t : SwappedRightInnerContributionClasses x y z w) :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q t.1 ∧
      HasLeftInnerContributionClass x y z w q := by
  exact HasSwappedRightInnerContributionClass.exists_leftInner
    x y z w t.1 t.2


/-!
## Outer-supporting classes
-/

/-- The quotient class determined by an outer-left witness. -/
def OuterLeftWitness.toClass
    {x y z w : PTree}
    (h : OuterLeftWitness x y z w) :
    TwoStepQuotient x y z w :=
  match h with
  | OuterLeftWitness.mk a b z' haz hbw =>
      classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw)

/-- The quotient class determined by an outer-right witness. -/
def OuterRightWitness.toClass
    {x y z w : PTree}
    (h : OuterRightWitness x y z w) :
    TwoStepQuotient x y z w :=
  match h with
  | OuterRightWitness.mk a b z' haz hbw =>
      classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw)

/-- The quotient class determined by an outer-left witness. -/
def outerLeftWitnessClass
    {x y z w : PTree}
    (h : OuterLeftWitness x y z w) :
    TwoStepQuotient x y z w :=
  match h with
  | OuterLeftWitness.mk a b z' haz hbw =>
      classOfLeftWitness (TwoStepWitnessLeft.outer a b z' haz hbw)

/-- The quotient class determined by an outer-right witness. -/
def outerRightWitnessClass
    {x y z w : PTree}
    (h : OuterRightWitness x y z w) :
    TwoStepQuotient x y z w :=
  match h with
  | OuterRightWitness.mk a b z' haz hbw =>
      classOfRightWitness (TwoStepWitnessRight.outer a b z' haz hbw)

/-- A left outer-supporting quotient class. -/
def HasLeftOuterContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ h : OuterLeftWitness x y z w, outerLeftWitnessClass h = q

/-- A right outer-supporting quotient class on the original side. -/
def HasRightOuterContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ h : OuterRightWitness x y z w, outerRightWitnessClass h = q

/-- A swapped-side right outer-supporting quotient class. -/
def HasSwappedRightOuterContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  ∃ h : OuterRightWitness y x z w, outerRightWitnessClass h = q'


/-- Every left outer-supporting class has a swapped right-outer partner. -/
theorem HasLeftOuterContributionClass.exists_rightOuter
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftOuterContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasSwappedRightOuterContributionClass x y z w q' := by
  rcases hq with ⟨h, hh⟩
  cases h with
  | mk a b z' haz hbw =>
      refine ⟨outerRightWitnessClass (OuterRightWitness.mk a b z' haz hbw), ?_, ?_⟩
      · apply swapped_respects_eq_left x y z w hh
        simpa [outerLeftWitnessClass, outerRightWitnessClass,
          classOfLeftWitness, codeOfLeftWitness,
          classOfRightWitness, codeOfRightWitness]
          using
            (SwappedTwoStepClass.leftOuter (x := x) (y := y) (z := z) (w := w)
              a b z' haz hbw)
      · refine ⟨OuterRightWitness.mk a b z' haz hbw, rfl⟩

/-- A swapped left-outer-supporting quotient class. -/
def HasSwappedLeftOuterContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  ∃ h : OuterLeftWitness y x z w,
    outerLeftWitnessClass h = q'

/-- Every right outer-supporting class has a swapped left-outer partner. -/
theorem HasRightOuterContributionClass.exists_leftOuter
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasRightOuterContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasSwappedLeftOuterContributionClass x y z w q' := by
  rcases hq with ⟨h, hh⟩
  cases h with
  | mk a b z' haz hbw =>
      refine ⟨outerLeftWitnessClass (OuterLeftWitness.mk a b z' haz hbw), ?_, ?_⟩
      · apply swapped_respects_eq_left x y z w hh
        simpa [outerLeftWitnessClass, outerRightWitnessClass,
          classOfLeftWitness, codeOfLeftWitness,
          classOfRightWitness, codeOfRightWitness]
          using
            (SwappedTwoStepClass.rightOuter (x := x) (y := y) (z := z) (w := w)
              a b z' haz hbw)
      · refine ⟨OuterLeftWitness.mk a b z' haz hbw, rfl⟩

/-- A contribution class is either an outer or inner supporting class. -/
def IsLeftContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  HasLeftOuterContributionClass x y z w q ∨
  HasLeftInnerContributionClass x y z w q

/-- Swapped-side contribution class. -/
def IsRightContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  HasSwappedRightOuterContributionClass x y z w q' ∨
  HasSwappedRightInnerContributionClass x y z w q'

/-- Any left contribution class transports to a swapped-side contribution class. -/
theorem IsLeftContributionClass.exists_right
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      IsRightContributionClass x y z w q' := by
  rcases hq with hq | hq
  · rcases HasLeftOuterContributionClass.exists_rightOuter x y z w q hq with
      ⟨q', hs, hq'⟩
    exact ⟨q', hs, Or.inl hq'⟩
  · rcases HasLeftInnerContributionClass.exists_swappedRightInner x y z w q hq with
      ⟨q', hs, hq'⟩
    exact ⟨q', hs, Or.inr hq'⟩

/-- Every swapped right-outer-supporting class has a left-outer partner. -/
theorem HasSwappedRightOuterContributionClass.exists_leftOuter
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : HasSwappedRightOuterContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasLeftOuterContributionClass x y z w q := by
  rcases hq' with ⟨h, hh⟩
  cases h with
  | mk a b z' haz hbw =>
      refine ⟨outerLeftWitnessClass (OuterLeftWitness.mk a b z' haz hbw), ?_, ?_⟩
      · apply swapped_respects_eq_right x y z w hh
        simpa [outerLeftWitnessClass, outerRightWitnessClass,
          classOfLeftWitness, codeOfLeftWitness,
          classOfRightWitness, codeOfRightWitness]
          using
            (SwappedTwoStepClass.leftOuter (x := x) (y := y) (z := z) (w := w)
              a b z' haz hbw)
      · refine ⟨OuterLeftWitness.mk a b z' haz hbw, rfl⟩

/-- Any swapped-side contribution class transports back to the left. -/
theorem IsRightContributionClass.exists_left
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : IsRightContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      IsLeftContributionClass x y z w q := by
  rcases hq' with hq' | hq'
  · rcases HasSwappedRightOuterContributionClass.exists_leftOuter x y z w q' hq' with
      ⟨q, hs, hq⟩
    exact ⟨q, hs, Or.inl hq⟩
  · rcases HasSwappedRightInnerContributionClass.exists_leftInner x y z w q' hq' with
      ⟨q, hs, hq⟩
    exact ⟨q, hs, Or.inr hq⟩


/-- Left and swapped-right contribution classes correspond across
`SwappedTwoStepClass`. -/
theorem contributionClasses_correspond
    (x y z w : PTree) :
    (∀ q : TwoStepQuotient x y z w,
      IsLeftContributionClass x y z w q →
      ∃ q' : TwoStepQuotient y x z w,
        SwappedTwoStepClass x y z w q q' ∧
        IsRightContributionClass x y z w q')
    ∧
    (∀ q' : TwoStepQuotient y x z w,
      IsRightContributionClass x y z w q' →
      ∃ q : TwoStepQuotient x y z w,
        SwappedTwoStepClass x y z w q q' ∧
        IsLeftContributionClass x y z w q) := by
  constructor
  · intro q hq
    exact IsLeftContributionClass.exists_right x y z w q hq
  · intro q' hq'
    exact IsRightContributionClass.exists_left x y z w q' hq'

/-- Existence of a left contribution class is equivalent to existence of a
swapped-right contribution class. -/
theorem nonempty_contributionClasses_iff
    (x y z w : PTree) :
    Nonempty {q : TwoStepQuotient x y z w // IsLeftContributionClass x y z w q} ↔
    Nonempty {q' : TwoStepQuotient y x z w // IsRightContributionClass x y z w q'} := by
  constructor
  · intro h
    rcases h with ⟨⟨q, hq⟩⟩
    rcases IsLeftContributionClass.exists_right x y z w q hq with
      ⟨q', hs, hq'⟩
    exact ⟨⟨q', hq'⟩⟩
  · intro h
    rcases h with ⟨⟨q', hq'⟩⟩
    rcases IsRightContributionClass.exists_left x y z w q' hq' with
      ⟨q, hs, hq⟩
    exact ⟨⟨q, hq⟩⟩

/-- Quotient classes contributing to the left-associated composite. -/
def LeftAssociatorSupport
    (x y z w : PTree) : Prop :=
  ∃ q : TwoStepQuotient x y z w, IsLeftContributionClass x y z w q

/-- Quotient classes contributing to the swapped right-associated composite. -/
def RightAssociatorSupport
    (x y z w : PTree) : Prop :=
  ∃ q' : TwoStepQuotient y x z w, IsRightContributionClass x y z w q'

theorem leftAssociatorSupport_iff_rightAssociatorSupport
    (x y z w : PTree) :
    LeftAssociatorSupport x y z w ↔ RightAssociatorSupport x y z w := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    rcases IsLeftContributionClass.exists_right x y z w q hq with
      ⟨q', hs, hq'⟩
    exact ⟨q', hq'⟩
  · intro h
    rcases h with ⟨q', hq'⟩
    rcases IsRightContributionClass.exists_left x y z w q' hq' with
      ⟨q, hs, hq⟩
    exact ⟨q, hq⟩

theorem IsLeftContributionClass.outer_or_inner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    HasLeftOuterContributionClass x y z w q ∨
    HasLeftInnerContributionClass x y z w q := by
  exact hq

theorem IsRightContributionClass.outer_or_inner
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : IsRightContributionClass x y z w q') :
    HasSwappedRightOuterContributionClass x y z w q' ∨
    HasSwappedRightInnerContributionClass x y z w q' := by
  exact hq'

theorem leftContribution_transport_by_cases
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    (HasLeftOuterContributionClass x y z w q →
      ∃ q' : TwoStepQuotient y x z w,
        SwappedTwoStepClass x y z w q q' ∧
        HasSwappedRightOuterContributionClass x y z w q')
    ∧
    (HasLeftInnerContributionClass x y z w q →
      ∃ q' : TwoStepQuotient y x z w,
        SwappedTwoStepClass x y z w q q' ∧
        HasSwappedRightInnerContributionClass x y z w q') := by
  constructor
  · intro hout
    exact HasLeftOuterContributionClass.exists_rightOuter x y z w q hout
  · intro hinn
    exact HasLeftInnerContributionClass.exists_swappedRightInner x y z w q hinn

  /-- `w` occurs as a quotient-level associator contribution on the left. -/
def InLeftAssociatorClass
    (x y z w : PTree) : Prop :=
  ∃ q : TwoStepQuotient x y z w, IsLeftContributionClass x y z w q

/-- `w` occurs as a quotient-level associator contribution on the swapped side. -/
def InRightAssociatorClass
    (x y z w : PTree) : Prop :=
  ∃ q' : TwoStepQuotient y x z w, IsRightContributionClass x y z w q'

theorem inLeftAssociatorClass_iff_inRightAssociatorClass
    (x y z w : PTree) :
    InLeftAssociatorClass x y z w ↔
    InRightAssociatorClass x y z w := by
  exact leftAssociatorSupport_iff_rightAssociatorSupport x y z w


/-!
## Total contribution classes
-/

open Classical

/-- The subtype of left quotient classes supporting total contribution data. -/
def LeftContributionClasses
    (x y z w : PTree) :=
  { q : TwoStepQuotient x y z w // IsLeftContributionClass x y z w q }

/-- The subtype of swapped-right quotient classes supporting total contribution data. -/
def RightContributionClasses
    (x y z w : PTree) :=
  { q' : TwoStepQuotient y x z w // IsRightContributionClass x y z w q' }

/-- Any left contribution class determines some swapped-right contribution class. -/
noncomputable def transportLeftContributionClassToRight
    (x y z w : PTree)
    (h : LeftContributionClasses x y z w) :
    RightContributionClasses x y z w :=
  let hx := IsLeftContributionClass.exists_right x y z w h.1 h.2
  ⟨Classical.choose hx, (Classical.choose_spec hx).2⟩

/-- Any swapped-right contribution class determines some left contribution class. -/
noncomputable def transportRightContributionClassToLeft
    (x y z w : PTree)
    (h : RightContributionClasses x y z w) :
    LeftContributionClasses x y z w :=
  let hx := IsRightContributionClass.exists_left x y z w h.1 h.2
  ⟨Classical.choose hx, (Classical.choose_spec hx).2⟩

/-- Existence of a left contribution class is equivalent to existence of a
swapped-right contribution class. -/
theorem nonempty_totalContributionClasses_iff
    (x y z w : PTree) :
    Nonempty (LeftContributionClasses x y z w) ↔
    Nonempty (RightContributionClasses x y z w) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨transportLeftContributionClassToRight x y z w h⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨transportRightContributionClassToLeft x y z w h⟩

/-- Every left contribution class has a swapped-right partner related by
`SwappedTwoStepClass`. -/
theorem LeftContributionClasses.exists_right_partner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ∃ t : RightContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 t.1 := by
  let hx := IsLeftContributionClass.exists_right x y z w s.1 s.2
  refine ⟨⟨Classical.choose hx, (Classical.choose_spec hx).2⟩, ?_⟩
  exact (Classical.choose_spec hx).1

/-- Every swapped-right contribution class has a left partner related by
`SwappedTwoStepClass`. -/
theorem RightContributionClasses.exists_left_partner
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ∃ s : LeftContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 t.1 := by
  let hx := IsRightContributionClass.exists_left x y z w t.1 t.2
  refine ⟨⟨Classical.choose hx, (Classical.choose_spec hx).2⟩, ?_⟩
  exact (Classical.choose_spec hx).1

/-- Any left contribution class determines a swapped-side associator shape. -/
theorem LeftContributionClasses.to_associator_shape
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w s.1 q' ∧
      IsRightContributionClass x y z w q' := by
  exact IsLeftContributionClass.exists_right x y z w s.1 s.2

/-- Any swapped-right contribution class determines a left-side associator shape. -/
theorem RightContributionClasses.to_associator_shape
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q t.1 ∧
      IsLeftContributionClass x y z w q := by
  exact IsRightContributionClass.exists_left x y z w t.1 t.2

/-- Left and swapped-right total contribution classes correspond in both directions. -/
theorem totalContributionClasses_correspond
    (x y z w : PTree) :
    (∀ s : LeftContributionClasses x y z w,
      ∃ t : RightContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1)
    ∧
    (∀ t : RightContributionClasses x y z w,
      ∃ s : LeftContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1) := by
  constructor
  · intro s
    exact LeftContributionClasses.exists_right_partner x y z w s
  · intro t
    exact RightContributionClasses.exists_left_partner x y z w t

/-!
## Swapped-side predicates are just ordinary left-side predicates on swapped inputs
-/

/-- A swapped right-outer class comes from some left-outer class. -/
theorem hasSwappedRightOuterContributionClass_exists_leftOuter
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : HasSwappedRightOuterContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasLeftOuterContributionClass x y z w q := by
  exact
    HasSwappedRightOuterContributionClass.exists_leftOuter
      x y z w q' hq'

/-- A swapped right-inner class comes from some left-inner class. -/
theorem hasSwappedRightInnerContributionClass_exists_leftInner
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : HasSwappedRightInnerContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasLeftInnerContributionClass x y z w q := by
  exact
    HasSwappedRightInnerContributionClass.exists_leftInner
      x y z w q' hq'

/-- A left-outer class determines some swapped right-outer class. -/
theorem hasLeftOuterContributionClass_exists_swappedRightOuter
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftOuterContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasSwappedRightOuterContributionClass x y z w q' := by
  exact
    HasLeftOuterContributionClass.exists_rightOuter
      x y z w q hq

/-- A left-inner class determines some swapped right-inner class. -/
theorem hasLeftInnerContributionClass_exists_swappedRightInner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftInnerContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      HasSwappedRightInnerContributionClass x y z w q' := by
  exact
    HasLeftInnerContributionClass.exists_swappedRightInner
      x y z w q hq

/-!
## Swap symmetry for left contribution classes via the swapped-right side
-/

/-!
## Correct swap orientation: right on swapped parameters = left on original parameters
-/

/-!
## Partner relation on total contribution classes
-/

open Classical

/-- Left/right total contribution classes are partners when their underlying
quotient classes are related by `SwappedTwoStepClass`. -/
def ContributionClassPartner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w) : Prop :=
  SwappedTwoStepClass x y z w s.1 t.1

/-- Choose some swapped-right partner for a left contribution class. -/
noncomputable def chooseRightContributionPartner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightContributionClasses x y z w :=
  Classical.choose (LeftContributionClasses.exists_right_partner x y z w s)

/-- The chosen swapped-right partner is related to the original left class. -/
theorem chooseRightContributionPartner_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ContributionClassPartner x y z w s
      (chooseRightContributionPartner x y z w s) := by
  exact (Classical.choose_spec
    (LeftContributionClasses.exists_right_partner x y z w s))

/-- Choose some left partner for a swapped-right contribution class. -/
noncomputable def chooseLeftContributionPartner
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftContributionClasses x y z w :=
  Classical.choose (RightContributionClasses.exists_left_partner x y z w t)

/-- The chosen left partner is related to the original swapped-right class. -/
theorem chooseLeftContributionPartner_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ContributionClassPartner x y z w
      (chooseLeftContributionPartner x y z w t) t := by
  exact (Classical.choose_spec
    (RightContributionClasses.exists_left_partner x y z w t))

/-- Every left contribution class has some partner on the swapped-right side. -/
theorem leftContributionClass_has_partner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ∃ t : RightContributionClasses x y z w,
      ContributionClassPartner x y z w s t := by
  exact ⟨chooseRightContributionPartner x y z w s,
    chooseRightContributionPartner_spec x y z w s⟩

/-- Every swapped-right contribution class has some partner on the left side. -/
theorem rightContributionClass_has_partner
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ∃ s : LeftContributionClasses x y z w,
      ContributionClassPartner x y z w s t := by
  exact ⟨chooseLeftContributionPartner x y z w t,
    chooseLeftContributionPartner_spec x y z w t⟩

/-- Nonemptiness of total contribution classes matches on both sides. -/
theorem nonempty_totalContributionClasses_iff'
    (x y z w : PTree) :
    Nonempty (LeftContributionClasses x y z w) ↔
    Nonempty (RightContributionClasses x y z w) := by
  constructor
  · intro h
    rcases h with ⟨s⟩
    exact ⟨chooseRightContributionPartner x y z w s⟩
  · intro h
    rcases h with ⟨t⟩
    exact ⟨chooseLeftContributionPartner x y z w t⟩

/-!
## Fibres of the partner relation

This is the cleanest next step before attempting full uniqueness:
define the partner fibres explicitly, show they are nonempty, and package the
chosen-partner maps as points in those fibres.

If the eventual uniqueness theorem is true, it should now become a theorem
that these fibres are subsingletons.
-/

open Classical

/-- Right partners of a fixed left contribution class. -/
def rightPartnerFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Set (RightContributionClasses x y z w) :=
  fun t => ContributionClassPartner x y z w s t

/-- Left partners of a fixed swapped-right contribution class. -/
def leftPartnerFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Set (LeftContributionClasses x y z w) :=
  fun s => ContributionClassPartner x y z w s t

/-- The chosen right partner lies in the right partner fibre. -/
theorem chooseRightContributionPartner_mem_rightPartnerFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    chooseRightContributionPartner x y z w s ∈ rightPartnerFiber x y z w s := by
  exact chooseRightContributionPartner_spec x y z w s

/-- The chosen left partner lies in the left partner fibre. -/
theorem chooseLeftContributionPartner_mem_leftPartnerFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    chooseLeftContributionPartner x y z w t ∈ leftPartnerFiber x y z w t := by
  exact chooseLeftContributionPartner_spec x y z w t

/-- Every right partner fibre is nonempty. -/
theorem rightPartnerFiber_nonempty
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    (rightPartnerFiber x y z w s).Nonempty := by
  refine ⟨chooseRightContributionPartner x y z w s, ?_⟩
  exact chooseRightContributionPartner_mem_rightPartnerFiber x y z w s

/-- Every left partner fibre is nonempty. -/
theorem leftPartnerFiber_nonempty
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    (leftPartnerFiber x y z w t).Nonempty := by
  refine ⟨chooseLeftContributionPartner x y z w t, ?_⟩
  exact chooseLeftContributionPartner_mem_leftPartnerFiber x y z w t

/-- Equality of left contribution classes preserves the right partner fibre. -/
theorem rightPartnerFiber_congr
    (x y z w : PTree)
    {s₁ s₂ : LeftContributionClasses x y z w}
    (hs : s₁ = s₂) :
    rightPartnerFiber x y z w s₁ = rightPartnerFiber x y z w s₂ := by
  subst hs
  rfl

/-- Equality of right contribution classes preserves the left partner fibre. -/
theorem leftPartnerFiber_congr
    (x y z w : PTree)
    {t₁ t₂ : RightContributionClasses x y z w}
    (ht : t₁ = t₂) :
    leftPartnerFiber x y z w t₁ = leftPartnerFiber x y z w t₂ := by
  subst ht
  rfl

/-- A convenient reformulation: a right class lies in the fibre of `s`
iff it is related to `s` by `SwappedTwoStepClass`. -/
theorem mem_rightPartnerFiber_iff
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w) :
    t ∈ rightPartnerFiber x y z w s ↔
      SwappedTwoStepClass x y z w s.1 t.1 := by
  rfl

/-- A convenient reformulation: a left class lies in the fibre of `t`
iff it is related to `t` by `SwappedTwoStepClass`. -/
theorem mem_leftPartnerFiber_iff
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w) :
    s ∈ leftPartnerFiber x y z w t ↔
      SwappedTwoStepClass x y z w s.1 t.1 := by
  rfl

/-!
## First uniqueness attempt for partner fibres
-/

/-!
## Chosen partner maps between fibres
-/

open Classical

/-- Send a left contribution class to one chosen right partner. -/
noncomputable def leftToRightPartner
    (x y z w : PTree) :
    LeftContributionClasses x y z w → RightContributionClasses x y z w :=
  chooseRightContributionPartner x y z w

/-- Send a right contribution class to one chosen left partner. -/
noncomputable def rightToLeftPartner
    (x y z w : PTree) :
    RightContributionClasses x y z w → LeftContributionClasses x y z w :=
  chooseLeftContributionPartner x y z w

/-- The chosen right partner is genuinely a partner. -/
theorem leftToRightPartner_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ContributionClassPartner x y z w s (leftToRightPartner x y z w s) := by
  exact chooseRightContributionPartner_spec x y z w s

/-- The chosen left partner is genuinely a partner. -/
theorem rightToLeftPartner_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ContributionClassPartner x y z w (rightToLeftPartner x y z w t) t := by
  exact chooseLeftContributionPartner_spec x y z w t

/-- Every left class has at least one right partner. -/
theorem exists_rightPartner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ∃ t : RightContributionClasses x y z w,
      ContributionClassPartner x y z w s t := by
  exact ⟨leftToRightPartner x y z w s, leftToRightPartner_spec x y z w s⟩

/-- Every right class has at least one left partner. -/
theorem exists_leftPartner
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ∃ s : LeftContributionClasses x y z w,
      ContributionClassPartner x y z w s t := by
  exact ⟨rightToLeftPartner x y z w t, rightToLeftPartner_spec x y z w t⟩

/-- A right partner fibre, viewed as a subtype. -/
def RightPartnerFiberType
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :=
  { t : RightContributionClasses x y z w // ContributionClassPartner x y z w s t }

/-- A left partner fibre, viewed as a subtype. -/
def LeftPartnerFiberType
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :=
  { s : LeftContributionClasses x y z w // ContributionClassPartner x y z w s t }

/-- Every left class has a nonempty right partner fibre. -/
theorem rightPartnerFiberType_nonempty
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (RightPartnerFiberType x y z w s) := by
  exact ⟨⟨leftToRightPartner x y z w s, leftToRightPartner_spec x y z w s⟩⟩

/-- Every right class has a nonempty left partner fibre. -/
theorem leftPartnerFiberType_nonempty
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Nonempty (LeftPartnerFiberType x y z w t) := by
  exact ⟨⟨rightToLeftPartner x y z w t, rightToLeftPartner_spec x y z w t⟩⟩


/-!
## Incidence objects for partner fibres

The right way to prepare for counting is to package *all partner relations*
as a single incidence type. Then each fibre is just the collection of incidences
above a fixed left or right class.

This avoids premature uniqueness assumptions and gives a clean bridge toward
cardinality / bijection arguments.
-/

open Classical

/-- A partner incidence is a left/right contribution-class pair related by
`SwappedTwoStepClass`. -/
def PartnerIncidence
    (x y z w : PTree) :=
  { p : LeftContributionClasses x y z w × RightContributionClasses x y z w //
      ContributionClassPartner x y z w p.1 p.2 }

/-- The left endpoint of a partner incidence. -/
def PartnerIncidence.left
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    LeftContributionClasses x y z w :=
  e.1.1

/-- The right endpoint of a partner incidence. -/
def PartnerIncidence.right
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    RightContributionClasses x y z w :=
  e.1.2

/-- The defining partner relation carried by an incidence. -/
theorem PartnerIncidence.rel
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    ContributionClassPartner x y z w
      (PartnerIncidence.left x y z w e)
      (PartnerIncidence.right x y z w e) := by
  exact e.2

/-- Build an incidence from a left class and a point in its right partner fibre. -/
def incidenceOfRightFiberElem
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightPartnerFiberType x y z w s) :
    PartnerIncidence x y z w :=
  ⟨(s, t.1), t.2⟩

/-- Build an incidence from a right class and a point in its left partner fibre. -/
def incidenceOfLeftFiberElem
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : LeftPartnerFiberType x y z w t) :
    PartnerIncidence x y z w :=
  ⟨(s.1, t), s.2⟩

/-- Recover a right-fibre element from an incidence and its left endpoint. -/
def rightFiberElemOfIncidence
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    RightPartnerFiberType x y z w (PartnerIncidence.left x y z w e) :=
  ⟨PartnerIncidence.right x y z w e, PartnerIncidence.rel x y z w e⟩

/-- Recover a left-fibre element from an incidence and its right endpoint. -/
def leftFiberElemOfIncidence
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    LeftPartnerFiberType x y z w (PartnerIncidence.right x y z w e) :=
  ⟨PartnerIncidence.left x y z w e, PartnerIncidence.rel x y z w e⟩

/-- Going from a right-fibre element to an incidence and back changes nothing. -/
theorem rightFiberElem_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightPartnerFiberType x y z w s) :
    rightFiberElemOfIncidence x y z w (incidenceOfRightFiberElem x y z w s t) = t := by
  cases t
  rfl

/-- Going from a left-fibre element to an incidence and back changes nothing. -/
theorem leftFiberElem_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : LeftPartnerFiberType x y z w t) :
    leftFiberElemOfIncidence x y z w (incidenceOfLeftFiberElem x y z w t s) = s := by
  cases s
  rfl

/-- For fixed left endpoint, right partner fibres are equivalent to incidences
with that left endpoint. -/
def rightPartnerFiberEquivIncidence
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightPartnerFiberType x y z w s ≃
      { e : PartnerIncidence x y z w // PartnerIncidence.left x y z w e = s } where
  toFun := fun t =>
    ⟨incidenceOfRightFiberElem x y z w s t, rfl⟩
  invFun := fun e =>
    match e with
    | ⟨e, he⟩ =>
        by
          cases e with
          | mk p hp =>
              cases p with
              | mk s' t =>
                  dsimp [PartnerIncidence.left] at he
                  subst he
                  exact ⟨t, hp⟩
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro e
    rcases e with ⟨e, he⟩
    cases e with
    | mk p hp =>
        cases p with
        | mk s' t =>
            dsimp [PartnerIncidence.left] at he
            subst he
            rfl

/-- For fixed right endpoint, left partner fibres are equivalent to incidences
with that right endpoint. -/
def leftPartnerFiberEquivIncidence
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftPartnerFiberType x y z w t ≃
      { e : PartnerIncidence x y z w // PartnerIncidence.right x y z w e = t } where
  toFun := fun s =>
    ⟨incidenceOfLeftFiberElem x y z w t s, rfl⟩
  invFun := fun e =>
    match e with
    | ⟨e, he⟩ =>
        by
          cases e with
          | mk p hp =>
              cases p with
              | mk s t' =>
                  dsimp [PartnerIncidence.right] at he
                  subst he
                  exact ⟨s, hp⟩
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro e
    rcases e with ⟨e, he⟩
    cases e with
    | mk p hp =>
        cases p with
        | mk s t' =>
            dsimp [PartnerIncidence.right] at he
            subst he
            rfl

/-- Every left class determines at least one incidence. -/
theorem PartnerIncidence.exists_of_left
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ∃ e : PartnerIncidence x y z w, PartnerIncidence.left x y z w e = s := by
  refine ⟨incidenceOfRightFiberElem x y z w s
    ⟨chooseRightContributionPartner x y z w s,
      chooseRightContributionPartner_spec x y z w s⟩, rfl⟩

/-- Every right class determines at least one incidence. -/
theorem PartnerIncidence.exists_of_right
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ∃ e : PartnerIncidence x y z w, PartnerIncidence.right x y z w e = t := by
  refine ⟨incidenceOfLeftFiberElem x y z w t
    ⟨chooseLeftContributionPartner x y z w t,
      chooseLeftContributionPartner_spec x y z w t⟩, rfl⟩

/-
Next natural targets after this block:

1. Prove that the subtype
     { e : PartnerIncidence x y z w // PartnerIncidence.left x y z w e = s }
   and the subtype
     { e : PartnerIncidence x y z w // PartnerIncidence.right x y z w e = t }
   have the same cardinality when linked by your witness-transport machinery.

2. Or, more concretely, define a transport on `PartnerIncidence` induced by your
   earlier forward/backward witness constructions, and show it preserves left/right
   endpoint fibres.

This is the clean setup for the actual counting theorem.
-/

/-!
## Endpoint fibres of incidences and their cardinalities

This packages the counting problem cleanly:
- right partner fibres are the same as incidences over a fixed left endpoint;
- left partner fibres are the same as incidences over a fixed right endpoint.

So any eventual counting theorem can be phrased either in terms of partner fibres
or in terms of endpoint fibres of `PartnerIncidence`.
-/

open Classical

/-- Incidences with fixed left endpoint `s`. -/
def IncidencesOverLeft
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :=
  { e : PartnerIncidence x y z w // PartnerIncidence.left x y z w e = s }

/-- Incidences with fixed right endpoint `t`. -/
def IncidencesOverRight
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :=
  { e : PartnerIncidence x y z w // PartnerIncidence.right x y z w e = t }

/-- Right partner fibres are equivalent to incidences over the corresponding left endpoint. -/
def rightPartnerFiberEquivIncidencesOverLeft
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightPartnerFiberType x y z w s ≃ IncidencesOverLeft x y z w s :=
  rightPartnerFiberEquivIncidence x y z w s

/-- Left partner fibres are equivalent to incidences over the corresponding right endpoint. -/
def leftPartnerFiberEquivIncidencesOverRight
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftPartnerFiberType x y z w t ≃ IncidencesOverRight x y z w t :=
  leftPartnerFiberEquivIncidence x y z w t

/-- Every left endpoint supports at least one incidence. -/
theorem incidencesOverLeft_nonempty
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (IncidencesOverLeft x y z w s) := by
  rcases PartnerIncidence.exists_of_left x y z w s with ⟨e, he⟩
  exact ⟨⟨e, he⟩⟩

/-- Every right endpoint supports at least one incidence. -/
theorem incidencesOverRight_nonempty
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Nonempty (IncidencesOverRight x y z w t) := by
  rcases PartnerIncidence.exists_of_right x y z w t with ⟨e, he⟩
  exact ⟨⟨e, he⟩⟩

/-- Cardinality of the right partner fibre of a fixed left contribution class. -/
noncomputable def rightPartnerFiberCard
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) : Cardinal :=
  Cardinal.lift (Cardinal.mk (RightPartnerFiberType x y z w s))

/-- Cardinality of the left partner fibre of a fixed right contribution class. -/
noncomputable def leftPartnerFiberCard
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) : Cardinal :=
  Cardinal.lift (Cardinal.mk (LeftPartnerFiberType x y z w t))

/-- Cardinality of incidences over a fixed left endpoint. -/
noncomputable def incidencesOverLeftCard
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) : Cardinal :=
  Cardinal.lift (Cardinal.mk (IncidencesOverLeft x y z w s))

/-- Cardinality of incidences over a fixed right endpoint. -/
noncomputable def incidencesOverRightCard
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) : Cardinal :=
  Cardinal.lift (Cardinal.mk (IncidencesOverRight x y z w t))

/-- Counting right partners is the same as counting incidences over the left endpoint. -/
theorem rightPartnerFiberCard_eq_incidencesOverLeftCard
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightPartnerFiberCard x y z w s = incidencesOverLeftCard x y z w s := by
  unfold rightPartnerFiberCard incidencesOverLeftCard
  exact congrArg Cardinal.lift (Cardinal.mk_congr
    (rightPartnerFiberEquivIncidencesOverLeft x y z w s))

/-- Counting left partners is the same as counting incidences over the right endpoint. -/
theorem leftPartnerFiberCard_eq_incidencesOverRightCard
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftPartnerFiberCard x y z w t = incidencesOverRightCard x y z w t := by
  unfold leftPartnerFiberCard incidencesOverRightCard
  exact congrArg Cardinal.lift (Cardinal.mk_congr
    (leftPartnerFiberEquivIncidencesOverRight x y z w t))

/-- A chosen incidence over a fixed left endpoint. -/
noncomputable def chosenIncidenceOverLeft
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IncidencesOverLeft x y z w s :=
  Classical.choice (incidencesOverLeft_nonempty x y z w s)

/-- A chosen incidence over a fixed right endpoint. -/
noncomputable def chosenIncidenceOverRight
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IncidencesOverRight x y z w t :=
  Classical.choice (incidencesOverRight_nonempty x y z w t)

/-- The chosen left-endpoint incidence really has the stated left endpoint. -/
theorem chosenIncidenceOverLeft_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    PartnerIncidence.left x y z w (chosenIncidenceOverLeft x y z w s).1 = s := by
  exact (chosenIncidenceOverLeft x y z w s).2

/-- The chosen right-endpoint incidence really has the stated right endpoint. -/
theorem chosenIncidenceOverRight_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    PartnerIncidence.right x y z w (chosenIncidenceOverRight x y z w t).1 = t := by
  exact (chosenIncidenceOverRight x y z w t).2

/-!
## Global decomposition of incidences by endpoint fibres

Having identified the fibres over fixed left/right endpoints, the next clean step
is to show that the total type of incidences is equivalent to:
- a sigma type of incidences over left endpoints, and
- a sigma type of incidences over right endpoints.

This is the standard “incidence object decomposes into endpoint fibres” package,
and it is the right setup for later cardinal-sum / double-counting arguments.
-/

/-- A partner incidence determines its left endpoint together with its position
in the fibre over that endpoint. -/
def partnerIncidenceEquivSigmaLeft
    (x y z w : PTree) :
    PartnerIncidence x y z w ≃
      Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s where
  toFun := fun e =>
    ⟨PartnerIncidence.left x y z w e, ⟨e, rfl⟩⟩
  invFun := fun p => p.2.1
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro p
    rcases p with ⟨s, e⟩
    rcases e with ⟨e, he⟩
    cases he
    rfl

/-- A partner incidence determines its right endpoint together with its position
in the fibre over that endpoint. -/
def partnerIncidenceEquivSigmaRight
    (x y z w : PTree) :
    PartnerIncidence x y z w ≃
      Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t where
  toFun := fun e =>
    ⟨PartnerIncidence.right x y z w e, ⟨e, rfl⟩⟩
  invFun := fun p => p.2.1
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro p
    rcases p with ⟨t, e⟩
    rcases e with ⟨e, he⟩
    cases he
    rfl

/-- The total incidence type is equivalent to the sigma of its left-endpoint fibres. -/
theorem Cardinal.mk_partnerIncidence_eq_sigma_left
    (x y z w : PTree) :
    Cardinal.mk (PartnerIncidence x y z w) =
      Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s) := by
  exact Cardinal.mk_congr (partnerIncidenceEquivSigmaLeft x y z w)

/-- The total incidence type is equivalent to the sigma of its right-endpoint fibres. -/
theorem Cardinal.mk_partnerIncidence_eq_sigma_right
    (x y z w : PTree) :
    Cardinal.mk (PartnerIncidence x y z w) =
      Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t) := by
  exact Cardinal.mk_congr (partnerIncidenceEquivSigmaRight x y z w)

/-- Lifted-cardinal version of the decomposition over left endpoints. -/
theorem Cardinal.lift_mk_partnerIncidence_eq_sigma_left
    (x y z w : PTree) :
    Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w)) =
      Cardinal.lift
        (Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s)) := by
  exact congrArg Cardinal.lift (Cardinal.mk_partnerIncidence_eq_sigma_left x y z w)

/-- Lifted-cardinal version of the decomposition over right endpoints. -/
theorem Cardinal.lift_mk_partnerIncidence_eq_sigma_right
    (x y z w : PTree) :
    Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w)) =
      Cardinal.lift
        (Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t)) := by
  exact congrArg Cardinal.lift (Cardinal.mk_partnerIncidence_eq_sigma_right x y z w)

/-- Re-express a left fibre as a subtype of all incidences with the chosen endpoint. -/
def sigmaLeftFiberEquivSubtype
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IncidencesOverLeft x y z w s ≃
      { e : PartnerIncidence x y z w // PartnerIncidence.left x y z w e = s } where
  toFun := fun e => e
  invFun := fun e => e
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro e
    rfl

/-- Re-express a right fibre as a subtype of all incidences with the chosen endpoint. -/
def sigmaRightFiberEquivSubtype
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IncidencesOverRight x y z w t ≃
      { e : PartnerIncidence x y z w // PartnerIncidence.right x y z w e = t } where
  toFun := fun e => e
  invFun := fun e => e
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro e
    rfl

/-- Every incidence appears in the left sigma decomposition with the expected endpoint. -/
theorem partnerIncidenceEquivSigmaLeft_fst
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    (partnerIncidenceEquivSigmaLeft x y z w e).1 = PartnerIncidence.left x y z w e := by
  rfl

/-- Every incidence appears in the right sigma decomposition with the expected endpoint. -/
theorem partnerIncidenceEquivSigmaRight_fst
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    (partnerIncidenceEquivSigmaRight x y z w e).1 = PartnerIncidence.right x y z w e := by
  rfl

/-- Forgetting the sigma packaging on the left returns the original incidence. -/
theorem partnerIncidenceEquivSigmaLeft_snd_val
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    (partnerIncidenceEquivSigmaLeft x y z w e).2.1 = e := by
  rfl

/-- Forgetting the sigma packaging on the right returns the original incidence. -/
theorem partnerIncidenceEquivSigmaRight_snd_val
    (x y z w : PTree)
    (e : PartnerIncidence x y z w) :
    (partnerIncidenceEquivSigmaRight x y z w e).2.1 = e := by
  rfl

/-!
## First actual double-counting theorem

The total incidence type can be decomposed either by left endpoints or by right
endpoints. Therefore the corresponding sigma-types have the same cardinality.
This is the abstract double-counting statement.
-/

open Classical

/-- The sigma decomposition over left endpoints and the sigma decomposition over
right endpoints have the same cardinality, because both classify the same
incidence type. -/
theorem Cardinal.mk_sigma_left_eq_mk_sigma_right
    (x y z w : PTree) :
    Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s) =
    Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t) := by
  calc
    Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s)
        = Cardinal.mk (PartnerIncidence x y z w) := by
            symm
            exact Cardinal.mk_congr (partnerIncidenceEquivSigmaLeft x y z w)
    _   = Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t) := by
            exact Cardinal.mk_congr (partnerIncidenceEquivSigmaRight x y z w)

/-- Lifted-cardinal version of the abstract double-counting theorem. -/
theorem Cardinal.lift_mk_sigma_left_eq_lift_mk_sigma_right
    (x y z w : PTree) :
    Cardinal.lift
      (Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s)) =
    Cardinal.lift
      (Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t)) := by
  exact congrArg Cardinal.lift (Cardinal.mk_sigma_left_eq_mk_sigma_right x y z w)

/-- The total incidence cardinal, expressed through left-endpoint fibres. -/
noncomputable def totalLeftIncidenceCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift
    (Cardinal.mk (Σ s : LeftContributionClasses x y z w, IncidencesOverLeft x y z w s))

/-- The total incidence cardinal, expressed through right-endpoint fibres. -/
noncomputable def totalRightIncidenceCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift
    (Cardinal.mk (Σ t : RightContributionClasses x y z w, IncidencesOverRight x y z w t))

/-- The total left- and right-fibre incidence cardinals agree. -/
theorem totalLeftIncidenceCard_eq_totalRightIncidenceCard
    (x y z w : PTree) :
    totalLeftIncidenceCard x y z w = totalRightIncidenceCard x y z w := by
  exact Cardinal.lift_mk_sigma_left_eq_lift_mk_sigma_right x y z w

/-- The total left incidence cardinal is the cardinal of the incidence type itself. -/
theorem totalLeftIncidenceCard_eq_partnerIncidence
    (x y z w : PTree) :
    totalLeftIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w)) := by
  unfold totalLeftIncidenceCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (partnerIncidenceEquivSigmaLeft x y z w)).symm

/-- The total right incidence cardinal is the cardinal of the incidence type itself. -/
theorem totalRightIncidenceCard_eq_partnerIncidence
    (x y z w : PTree) :
    totalRightIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w)) := by
  unfold totalRightIncidenceCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (partnerIncidenceEquivSigmaRight x y z w)).symm

/-- The two total-cardinality presentations agree because they are both equal to
the cardinality of the incidence type. -/
theorem totalIncidenceCard_double_count
    (x y z w : PTree) :
    totalLeftIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w))
    ∧
    totalRightIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (PartnerIncidence x y z w)) := by
  constructor
  · exact totalLeftIncidenceCard_eq_partnerIncidence x y z w
  · exact totalRightIncidenceCard_eq_partnerIncidence x y z w

/-!
## The underlying left-right incidence relation

The bundled type `PartnerIncidence x y z w` can be viewed as the edge set of a
bipartite incidence graph whose vertices are:
- left contribution classes, and
- right contribution classes.

The next step is to expose that underlying relation explicitly, and connect it
to the previously defined partner fibres.
-/

open Classical

/-- Left/right contribution classes are incident if they occur as the two
endpoints of some partner incidence. -/
def ArePartnerIncident
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w) : Prop :=
  ∃ e : PartnerIncidence x y z w,
    PartnerIncidence.left x y z w e = s ∧
    PartnerIncidence.right x y z w e = t

/-- The set of right endpoints incident to a fixed left endpoint. -/
def IncidentRights
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :=
  { t : RightContributionClasses x y z w // ArePartnerIncident x y z w s t }

/-- The set of left endpoints incident to a fixed right endpoint. -/
def IncidentLefts
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :=
  { s : LeftContributionClasses x y z w // ArePartnerIncident x y z w s t }

/-- Any right partner fibre element yields an incident right endpoint. -/
def incidentRightOfRightPartnerFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightPartnerFiberType x y z w s → IncidentRights x y z w s := by
  intro u
  rcases u with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  refine ⟨incidenceOfRightFiberElem x y z w s ⟨t, ht⟩, rfl, ?_⟩
  rfl

/-- Any left partner fibre element yields an incident left endpoint. -/
def incidentLeftOfLeftPartnerFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftPartnerFiberType x y z w t → IncidentLefts x y z w t := by
  intro u
  rcases u with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  refine ⟨incidenceOfLeftFiberElem x y z w t ⟨s, hs⟩, ?_, rfl⟩
  rfl

/-- Any incident pair gives an incidence whose left endpoint is the specified one. -/
theorem ArePartnerIncident.exists_incidence_left
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w)
    (h : ArePartnerIncident x y z w s t) :
    ∃ e : PartnerIncidence x y z w,
      PartnerIncidence.left x y z w e = s := by
  rcases h with ⟨e, hs, ht⟩
  exact ⟨e, hs⟩

/-- Any incident pair gives an incidence whose right endpoint is the specified one. -/
theorem ArePartnerIncident.exists_incidence_right
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : RightContributionClasses x y z w)
    (h : ArePartnerIncident x y z w s t) :
    ∃ e : PartnerIncidence x y z w,
      PartnerIncidence.right x y z w e = t := by
  rcases h with ⟨e, hs, ht⟩
  exact ⟨e, ht⟩

/-- A right partner fibre element witnesses incidence with its underlying right endpoint. -/
theorem rightPartnerFiber_implies_incident
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : RightPartnerFiberType x y z w s) :
    ArePartnerIncident x y z w s (incidentRightOfRightPartnerFiber x y z w s u).1 := by
  exact (incidentRightOfRightPartnerFiber x y z w s u).2

/-- A left partner fibre element witnesses incidence with its underlying left endpoint. -/
theorem leftPartnerFiber_implies_incident
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : LeftPartnerFiberType x y z w t) :
    ArePartnerIncident x y z w (incidentLeftOfLeftPartnerFiber x y z w t u).1 t := by
  exact (incidentLeftOfLeftPartnerFiber x y z w t u).2

/-- Every left endpoint has at least one incident right endpoint. -/
theorem IncidentRights.nonempty
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (IncidentRights x y z w s) := by
  let u : RightPartnerFiberType x y z w s :=
    ⟨chooseRightContributionPartner x y z w s,
      chooseRightContributionPartner_spec x y z w s⟩
  exact ⟨incidentRightOfRightPartnerFiber x y z w s u⟩

/-- Every right endpoint has at least one incident left endpoint. -/
theorem IncidentLefts.nonempty
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Nonempty (IncidentLefts x y z w t) := by
  let u : LeftPartnerFiberType x y z w t :=
    ⟨chooseLeftContributionPartner x y z w t,
      chooseLeftContributionPartner_spec x y z w t⟩
  exact ⟨incidentLeftOfLeftPartnerFiber x y z w t u⟩

/-- A chosen incident right endpoint for each left endpoint. -/
noncomputable def chosenIncidentRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IncidentRights x y z w s :=
  Classical.choice (IncidentRights.nonempty x y z w s)

/-- A chosen incident left endpoint for each right endpoint. -/
noncomputable def chosenIncidentLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IncidentLefts x y z w t :=
  Classical.choice (IncidentLefts.nonempty x y z w t)

/-- The chosen incident right endpoint is genuinely incident to the given left endpoint. -/
theorem chosenIncidentRight_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    ArePartnerIncident x y z w s (chosenIncidentRight x y z w s).1 := by
  exact (chosenIncidentRight x y z w s).2

/-- The chosen incident left endpoint is genuinely incident to the given right endpoint. -/
theorem chosenIncidentLeft_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    ArePartnerIncident x y z w (chosenIncidentLeft x y z w t).1 t := by
  exact (chosenIncidentLeft x y z w t).2


/-!
## Incident neighbour sets: forward maps and chosen representatives

Important: `ArePartnerIncident ... s t` is a proposition. So we may freely map
a concrete partner-fibre element to an incident neighbour, but we cannot in
general recover a concrete fibre element from mere incidence data by pattern
matching on the existential witness in `Prop`.

Accordingly, we construct:
- forward maps from partner fibres to incident neighbour sets;
- existence of fibre elements over any incident neighbour;
- noncomputable chosen representatives.
-/

open Classical


/-- Any incident right endpoint admits some right partner fibre element. -/
theorem exists_rightPartnerFiber_of_incidentRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : IncidentRights x y z w s) :
    ∃ v : RightPartnerFiberType x y z w s, v.1 = u.1 := by
  rcases u with ⟨t, hinc⟩
  rcases hinc with ⟨e, hs, ht⟩
  cases e with
  | mk p hp =>
      cases p with
      | mk s' t' =>
          dsimp [PartnerIncidence.left, PartnerIncidence.right] at hs ht
          subst hs
          subst ht
          exact ⟨⟨t', hp⟩, rfl⟩

/-- Any incident left endpoint admits some left partner fibre element. -/
theorem exists_leftPartnerFiber_of_incidentLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : IncidentLefts x y z w t) :
    ∃ v : LeftPartnerFiberType x y z w t, v.1 = u.1 := by
  rcases u with ⟨s, hinc⟩
  rcases hinc with ⟨e, hs, ht⟩
  cases e with
  | mk p hp =>
      cases p with
      | mk s' t' =>
          dsimp [PartnerIncidence.left, PartnerIncidence.right] at hs ht
          subst hs
          subst ht
          exact ⟨⟨s', hp⟩, rfl⟩

/-- A chosen right partner fibre element over an incident right endpoint. -/
noncomputable def chosenRightPartnerFiberOfIncidentRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : IncidentRights x y z w s) :
    RightPartnerFiberType x y z w s :=
  Classical.choose (exists_rightPartnerFiber_of_incidentRight x y z w s u)

/-- A chosen left partner fibre element over an incident left endpoint. -/
noncomputable def chosenLeftPartnerFiberOfIncidentLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : IncidentLefts x y z w t) :
    LeftPartnerFiberType x y z w t :=
  Classical.choose (exists_leftPartnerFiber_of_incidentLeft x y z w t u)

/-- The chosen right partner fibre element has the prescribed right endpoint. -/
theorem chosenRightPartnerFiberOfIncidentRight_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : IncidentRights x y z w s) :
    (chosenRightPartnerFiberOfIncidentRight x y z w s u).1 = u.1 := by
  exact Classical.choose_spec
    (exists_rightPartnerFiber_of_incidentRight x y z w s u)

/-- The chosen left partner fibre element has the prescribed left endpoint. -/
theorem chosenLeftPartnerFiberOfIncidentLeft_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : IncidentLefts x y z w t) :
    (chosenLeftPartnerFiberOfIncidentLeft x y z w t u).1 = u.1 := by
  exact Classical.choose_spec
    (exists_leftPartnerFiber_of_incidentLeft x y z w t u)

/-- Going from a right partner fibre element to an incident neighbour preserves
the underlying right endpoint. -/
theorem incidentRightOfRightPartnerFiber_fst
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : RightPartnerFiberType x y z w s) :
    (incidentRightOfRightPartnerFiber x y z w s u).1 = u.1 := by
  cases u
  rfl

/-- Going from a left partner fibre element to an incident neighbour preserves
the underlying left endpoint. -/
theorem incidentLeftOfLeftPartnerFiber_fst
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : LeftPartnerFiberType x y z w t) :
    (incidentLeftOfLeftPartnerFiber x y z w t u).1 = u.1 := by
  cases u
  rfl

/-- The incident-neighbour map on the right is surjective on underlying endpoints. -/
theorem incidentRightOfRightPartnerFiber_surj_on_endpoints
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : IncidentRights x y z w s) :
    ∃ v : RightPartnerFiberType x y z w s,
      (incidentRightOfRightPartnerFiber x y z w s v).1 = u.1 := by
  refine ⟨chosenRightPartnerFiberOfIncidentRight x y z w s u, ?_⟩
  rw [incidentRightOfRightPartnerFiber_fst, chosenRightPartnerFiberOfIncidentRight_spec]

/-- The incident-neighbour map on the left is surjective on underlying endpoints. -/
theorem incidentLeftOfLeftPartnerFiber_surj_on_endpoints
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : IncidentLefts x y z w t) :
    ∃ v : LeftPartnerFiberType x y z w t,
      (incidentLeftOfLeftPartnerFiber x y z w t v).1 = u.1 := by
  refine ⟨chosenLeftPartnerFiberOfIncidentLeft x y z w t u, ?_⟩
  rw [incidentLeftOfLeftPartnerFiber_fst, chosenLeftPartnerFiberOfIncidentLeft_spec]

/-!
## Local uniqueness of partner data over a fixed endpoint

A right partner over a fixed left endpoint is determined entirely by its
underlying right contribution class, and dually on the left.

Since the partner condition is a proposition, this is just subtype extensionality.
This is the key fact that lets us identify witness-bearing partner sets with
ordinary neighbour sets in the bipartite incidence graph.
-/

open Classical

/-- Two right partner fibre elements over the same left endpoint are equal if
their underlying right endpoints are equal. -/
theorem rightPartnerFiber_ext
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u v : RightPartnerFiberType x y z w s)
    (h : u.1 = v.1) :
    u = v := by
  exact Subtype.ext h

/-- Two left partner fibre elements over the same right endpoint are equal if
their underlying left endpoints are equal. -/
theorem leftPartnerFiber_ext
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u v : LeftPartnerFiberType x y z w t)
    (h : u.1 = v.1) :
    u = v := by
  exact Subtype.ext h

/-- Noncomputably recover a right partner fibre element from an incident right
endpoint. -/
noncomputable def rightPartnerFiberOfIncidentRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IncidentRights x y z w s → RightPartnerFiberType x y z w s :=
  fun u => chosenRightPartnerFiberOfIncidentRight x y z w s u

/-- Noncomputably recover a left partner fibre element from an incident left
endpoint. -/
noncomputable def leftPartnerFiberOfIncidentLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IncidentLefts x y z w t → LeftPartnerFiberType x y z w t :=
  fun u => chosenLeftPartnerFiberOfIncidentLeft x y z w t u

/-- Recovering a right partner from an incident right endpoint and then
forgetting back to the neighbourhood gives the original incident neighbour. -/
theorem incidentRight_rightPartnerFiber_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : IncidentRights x y z w s) :
    incidentRightOfRightPartnerFiber x y z w s
      (rightPartnerFiberOfIncidentRight x y z w s u) = u := by
  apply Subtype.ext
  exact chosenRightPartnerFiberOfIncidentRight_spec x y z w s u

/-- Recovering a left partner from an incident left endpoint and then
forgetting back to the neighbourhood gives the original incident neighbour. -/
theorem incidentLeft_leftPartnerFiber_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : IncidentLefts x y z w t) :
    incidentLeftOfLeftPartnerFiber x y z w t
      (leftPartnerFiberOfIncidentLeft x y z w t u) = u := by
  apply Subtype.ext
  exact chosenLeftPartnerFiberOfIncidentLeft_spec x y z w t u

/-- Forgetting a right partner fibre element to an incident neighbour and then
recovering a partner gives back the original partner. -/
theorem rightPartnerFiber_incidentRight_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u : RightPartnerFiberType x y z w s) :
    rightPartnerFiberOfIncidentRight x y z w s
      (incidentRightOfRightPartnerFiber x y z w s u) = u := by
  apply rightPartnerFiber_ext
  unfold rightPartnerFiberOfIncidentRight
  rw [chosenRightPartnerFiberOfIncidentRight_spec]
  exact incidentRightOfRightPartnerFiber_fst x y z w s u

/-- Forgetting a left partner fibre element to an incident neighbour and then
recovering a partner gives back the original partner. -/
theorem leftPartnerFiber_incidentLeft_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u : LeftPartnerFiberType x y z w t) :
    leftPartnerFiberOfIncidentLeft x y z w t
      (incidentLeftOfLeftPartnerFiber x y z w t u) = u := by
  apply leftPartnerFiber_ext
  unfold leftPartnerFiberOfIncidentLeft
  rw [chosenLeftPartnerFiberOfIncidentLeft_spec]
  exact incidentLeftOfLeftPartnerFiber_fst x y z w t u

/-- Over a fixed left endpoint, the right partner set is equivalent to the
ordinary set of incident right neighbours. -/
noncomputable def rightPartnerFiberEquivIncidentRights
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightPartnerFiberType x y z w s ≃ IncidentRights x y z w s where
  toFun := incidentRightOfRightPartnerFiber x y z w s
  invFun := rightPartnerFiberOfIncidentRight x y z w s
  left_inv := rightPartnerFiber_incidentRight_roundtrip x y z w s
  right_inv := incidentRight_rightPartnerFiber_roundtrip x y z w s

/-- Over a fixed right endpoint, the left partner set is equivalent to the
ordinary set of incident left neighbours. -/
noncomputable def leftPartnerFiberEquivIncidentLefts
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftPartnerFiberType x y z w t ≃ IncidentLefts x y z w t where
  toFun := incidentLeftOfLeftPartnerFiber x y z w t
  invFun := leftPartnerFiberOfIncidentLeft x y z w t
  left_inv := leftPartnerFiber_incidentLeft_roundtrip x y z w t
  right_inv := incidentLeft_leftPartnerFiber_roundtrip x y z w t

/-- Counting right partners is the same as counting incident right neighbours. -/
theorem rightPartnerFiberCard_eq_incidentRightsCard
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightPartnerFiberCard x y z w s =
      Cardinal.lift (Cardinal.mk (IncidentRights x y z w s)) := by
  unfold rightPartnerFiberCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (rightPartnerFiberEquivIncidentRights x y z w s))

/-- Counting left partners is the same as counting incident left neighbours. -/
theorem leftPartnerFiberCard_eq_incidentLeftsCard
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftPartnerFiberCard x y z w t =
      Cardinal.lift (Cardinal.mk (IncidentLefts x y z w t)) := by
  unfold leftPartnerFiberCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (leftPartnerFiberEquivIncidentLefts x y z w t))


/-!
## Reduce partner uniqueness to uniqueness of `SwappedTwoStepClass`

At this point, partner uniqueness is exactly the statement that
`SwappedTwoStepClass` is functional in each argument.
-/

#check (fun (x y z w : PTree) (s : LeftContributionClasses x y z w) => s.1)
#check (fun (x y z w : PTree) (t : RightContributionClasses x y z w) => t.1)

/-!
## Reduce partner uniqueness to uniqueness of `SwappedTwoStepClass`

Since
  ContributionClassPartner x y z w s t := SwappedTwoStepClass x y z w s.1 t.1,
partner uniqueness is exactly the statement that `SwappedTwoStepClass` is
functional in each argument.
-/

/-- If `SwappedTwoStepClass` is right-functional, then each fixed left class has
at most one right partner. -/
theorem rightPartnerFiber_subsingleton_of_swapped_right_unique
    (x y z w : PTree)
    (huniq :
      ∀ {q : TwoStepQuotient x y z w}
        {q₁ q₂ : TwoStepQuotient y x z w},
        SwappedTwoStepClass x y z w q q₁ →
        SwappedTwoStepClass x y z w q q₂ →
        q₁ = q₂)
    (s : LeftContributionClasses x y z w) :
    Subsingleton (RightPartnerFiberType x y z w s) := by
  constructor
  intro u v
  apply rightPartnerFiber_ext
  apply Subtype.ext
  exact huniq u.2 v.2

/-- If `SwappedTwoStepClass` is left-functional, then each fixed right class has
at most one left partner. -/
theorem leftPartnerFiber_subsingleton_of_swapped_left_unique
    (x y z w : PTree)
    (huniq :
      ∀ {q₁ q₂ : TwoStepQuotient x y z w}
        {q : TwoStepQuotient y x z w},
        SwappedTwoStepClass x y z w q₁ q →
        SwappedTwoStepClass x y z w q₂ q →
        q₁ = q₂)
    (t : RightContributionClasses x y z w) :
    Subsingleton (LeftPartnerFiberType x y z w t) := by
  constructor
  intro u v
  apply leftPartnerFiber_ext
  apply Subtype.ext
  exact huniq u.2 v.2


/-- If `SwappedTwoStepClass` is right-functional, then any two right partners of
a fixed left class are equal. -/
theorem rightPartnerFiber_unique_of_swapped_right_unique
    (x y z w : PTree)
    (huniq :
      ∀ {q : TwoStepQuotient x y z w}
        {q₁ q₂ : TwoStepQuotient y x z w},
        SwappedTwoStepClass x y z w q q₁ →
        SwappedTwoStepClass x y z w q q₂ →
        q₁ = q₂)
    (s : LeftContributionClasses x y z w)
    (u v : RightPartnerFiberType x y z w s) :
    u = v :=
  (rightPartnerFiber_subsingleton_of_swapped_right_unique x y z w huniq s).elim u v

/-- If `SwappedTwoStepClass` is left-functional, then any two left partners of
a fixed right class are equal. -/
theorem leftPartnerFiber_unique_of_swapped_left_unique
    (x y z w : PTree)
    (huniq :
      ∀ {q₁ q₂ : TwoStepQuotient x y z w}
        {q : TwoStepQuotient y x z w},
        SwappedTwoStepClass x y z w q₁ q →
        SwappedTwoStepClass x y z w q₂ q →
        q₁ = q₂)
    (t : RightContributionClasses x y z w)
    (u v : LeftPartnerFiberType x y z w t) :
    u = v :=
  (leftPartnerFiber_subsingleton_of_swapped_left_unique x y z w huniq t).elim u v









/-!
## Uniqueness of partners over a fixed endpoint

The chosen-partner maps can only be inverse if, for each fixed endpoint, there is
at most one partner on the opposite side.  So the real next target is to prove
that the partner fibres are subsingletons.
-/

open Classical

/-- Over a fixed left contribution class, there is at most one right partner. -/
theorem rightPartnerFiber_subsingleton
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Subsingleton (RightPartnerFiberType x y z w s) := by
  constructor
  intro u v
  apply rightPartnerFiber_ext
  /-
  Real proof needed here:
  show that `u.1 = v.1`, i.e. that two right contribution classes partnered with
  the same left contribution class must coincide.
  This should come from your earlier quotient/witness uniqueness machinery,
  not from incidence packaging.
  -/
  sorry

/-- Over a fixed right contribution class, there is at most one left partner. -/
theorem leftPartnerFiber_subsingleton
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Subsingleton (LeftPartnerFiberType x y z w t) := by
  constructor
  intro u v
  apply leftPartnerFiber_ext
  /-
  Real proof needed here:
  show that `u.1 = v.1`, i.e. that two left contribution classes partnered with
  the same right contribution class must coincide.
  Again, this should be proved from the quotient/witness theory.
  -/
  sorry

/-- Any two right partner fibre elements over the same left endpoint are equal. -/
theorem rightPartnerFiber_unique
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (u v : RightPartnerFiberType x y z w s) :
    u = v :=
  (rightPartnerFiber_subsingleton x y z w s).elim u v

/-- Any two left partner fibre elements over the same right endpoint are equal. -/
theorem leftPartnerFiber_unique
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (u v : LeftPartnerFiberType x y z w t) :
    u = v :=
  (leftPartnerFiber_subsingleton x y z w t).elim u v







/--
Inner reassociation is already canonical up to swapping `x` and `y`.

This is the quotient-level inner contribution to pre-Lie symmetry:
the nested case on the left with parameters `(x,y,z,w)` is literally the
nested case on the right with parameters `(y,x,z,w)`.
-/
theorem inner_symmetry_on_classes
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    classOfLeftInner a b y' hay hbw =
      classOfRightInner (x := x) (y := y) a b y' hay hbw := by
  rfl





/--
Inner reassociation is already canonical up to swapping `x` and `y`.

This is the quotient-level inner contribution to pre-Lie symmetry:
the nested case on the left with parameters `(x,y,z,w)` is literally the
nested case on the right with parameters `(y,x,z,w)`.
-/
theorem inner_symmetry_on_classes
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    classOfLeftInner a b y' hay hbw =
      classOfRightInner (x := x) (y := y) a b y' hay hbw := by
  rfl

/-!
## Canonicalisation maps

These maps send raw two-step witness codes to the more invariant
canonical two-step data. The intended meaning is that a raw derivation
history presents a canonical proof-composition pattern.
-/




/--
Canonicalisation of a raw left witness.

A witness for the left-bracketed two-step grafting
`x ▷ (y ▷ z)` determines canonical two-step data for the associator.
-/
def canonOfLeftWitness
    {x y z w : PTree} :
    TwoStepWitnessLeft x y z w → TwoStepCanonical x y z w
  | TwoStepWitnessLeft.outer a b z' haz hbw =>
      TwoStepCanonical.outer z'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)
  | TwoStepWitnessLeft.inner a b y' hay hbw =>
      TwoStepCanonical.inner y'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)

/--
Canonicalisation of a raw right witness.

A witness for the right-bracketed two-step grafting
`y ▷ (x ▷ z)` determines canonical two-step data for the associator,
with `x` and `y` swapped. This reflects symmetry of the associator,
not commutativity of grafting.
-/
def canonOfRightWitness
    {x y z w : PTree} :
    TwoStepWitnessRight x y z w → TwoStepCanonical y x z w
  | TwoStepWitnessRight.outer a b z' haz hbw =>
      TwoStepCanonical.outer z'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)
  | TwoStepWitnessRight.inner a b y' hay hbw =>
      TwoStepCanonical.inner y'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)

/-!
## Completeness back to witnesses

Canonical two-step data should also be realisable by raw witnesses.
These are the converse directions to the canonicalisation maps.
-/

/--
Canonical two-step data gives rise to a raw left witness presentation.
-/
theorem canonical_gives_left_witness
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical x y z w) →
    Nonempty (TwoStepWitnessLeft x y z w) := by
  intro h
  rcases h with ⟨hcanon⟩
  cases hcanon with
  | outer z₃ hxz hyw =>
      rw [twoStepWitnessLeft_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨z₃, hxz, hyw⟩
  | inner y' hxy hyw =>
      rw [twoStepWitnessLeft_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨y', hxy, hyw⟩

/--
Canonical two-step data gives rise to a raw right witness presentation,
with `x` and `y` swapped as appropriate for associator symmetry.
-/
theorem canonical_gives_right_witness
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical y x z w) →
    Nonempty (TwoStepWitnessRight x y z w) := by
  intro h
  rcases h with ⟨hcanon⟩
  cases hcanon with
  | outer z' hyz hxw =>
      rw [twoStepWitnessRight_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨z', hyz, hxw⟩
  | inner y' hyx hyw =>
      rw [twoStepWitnessRight_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨y', hyx, hyw⟩

/-!
## Support characterisation

These theorems express that raw witness support and canonical support
present the same underlying two-step proof-composition data.
-/

/--
A left raw witness exists iff canonical two-step data exists.
-/
theorem left_witness_iff_canonical
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessLeft x y z w) ↔
    Nonempty (TwoStepCanonical x y z w) := by
  constructor
  · intro h
    exact ⟨canonOfLeftWitness h.some⟩
  · intro h
    exact canonical_gives_left_witness x y z w h

/--
A right raw witness exists iff canonical two-step data exists,
with the canonical side written in the associator-symmetric order.
-/
theorem right_witness_iff_canonical
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessRight x y z w) ↔
    Nonempty (TwoStepCanonical y x z w) := by
  constructor
  · intro h
    exact ⟨canonOfRightWitness h.some⟩
  · intro h
    exact canonical_gives_right_witness x y z w h

/-!
## Symmetry at the canonical level

This is the first real pre-Lie-style target: once bureaucratic witness
history is forgotten, the associator should become symmetric in `x` and `y`.
-/

/--
Canonical symmetry of two-step proof-composition data.

This is the intended first “pre-Lie modulo proof identity” theorem:
the associator should be symmetric once raw address bookkeeping has been
collapsed to canonical two-step data.
-/
theorem canonical_symm
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical x y z w) ↔
    Nonempty (TwoStepCanonical y x z w) := by
  sorry

/-!
## 2. Bureaucratic equivalences
-/

/-! Placeholder: equivalence generated by commuting independent grafts
and identifying inner reassociation presentations. -/
-- inductive TwoStepWitnessEq : ... → ... → Prop
-- | ...

/-!
## 3. Left/right comparison
-/

/-! Placeholder: canonical left witnesses. -/
-- def canonicalLeftWitnesses ... := ...

/-! Placeholder: canonical right witnesses. -/
-- def canonicalRightWitnesses ... := ...

/-! Main target: left and right canonical witnesses agree. -/
-- theorem canonical_two_step_balance ... := by
--   ...

/-!
## 4. Corrected pre-Lie product
-/

/-- Placeholder: pre-Lie product built from canonical witness classes
rather than raw address multiplicities. -/
-- noncomputable def graftPreLieCanonical ... := ...

/-!
## 5. Toward the symmetric algebra / Hopf algebra
-/

-- Placeholder theorems here.

end PTree
