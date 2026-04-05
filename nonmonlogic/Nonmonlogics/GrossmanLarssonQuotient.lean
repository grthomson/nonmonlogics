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

/-
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
  -/
/-
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
-/



  /-!
NEXT PHASE: stop trying to prove uniqueness of partners.
`SwappedTwoStepClass` should now be treated as a many-valued correspondence on
quotient classes.

What to do next:
1. Define the right-neighbourhood of a left quotient class, and the left-
   neighbourhood of a right quotient class.
2. State nonemptiness transfer theorems for these neighbourhoods, using the
   witness-transport / support lemmas already proved earlier.
3. Then try to prove local cardinal/equinumerosity results for these
   neighbourhoods, rather than subsingleton/uniqueness.
-/

/-- Right neighbourhood of a left quotient class under `SwappedTwoStepClass`. -/
def swappedRightNeighbors
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { q' : TwoStepQuotient y x z w // SwappedTwoStepClass x y z w q q' }

/-- Left neighbourhood of a right quotient class under `SwappedTwoStepClass`. -/
def swappedLeftNeighbors
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :=
  { q' : TwoStepQuotient x y z w // SwappedTwoStepClass x y z w q' q }

/-!
## Swapped-neighbourhood nonemptiness

At this stage we stop treating swapped transport as functional.
Instead, we show that any contribution class has at least one neighbour
on the opposite side.
-/

open Classical


/-- Any left contribution class has a nonempty swapped-right neighbourhood. -/
theorem swappedRightNeighbors_nonempty
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    Nonempty (swappedRightNeighbors x y z w q) := by
  /-
  Replace `IsLeftContributionClass.exists_right` with the actual theorem name
  you already proved:
    from a left contribution class, obtain some swapped-right class that is a
    right contribution class.
  -/
  rcases IsLeftContributionClass.exists_right x y z w q hq with
    ⟨q', hs, hq'⟩
  exact ⟨⟨q', hs⟩⟩

/-- Any right contribution class has a nonempty swapped-left neighbourhood. -/
theorem swappedLeftNeighbors_nonempty
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    Nonempty (swappedLeftNeighbors x y z w q) := by
  /-
  Replace `IsRightContributionClass.exists_left` with the actual dual theorem
  name you already proved:
    from a right contribution class, obtain some swapped-left class that is a
    left contribution class.
  -/
  rcases IsRightContributionClass.exists_left x y z w q hq with
    ⟨q', hs, hq'⟩
  exact ⟨⟨q', hs⟩⟩

/-- A concrete chosen swapped-right neighbour of a left contribution class. -/
noncomputable def someSwappedRightNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    swappedRightNeighbors x y z w q :=
  Classical.choice (swappedRightNeighbors_nonempty x y z w q hq)

/-- A concrete chosen swapped-left neighbour of a right contribution class. -/
noncomputable def someSwappedLeftNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    swappedLeftNeighbors x y z w q :=
  Classical.choice (swappedLeftNeighbors_nonempty x y z w q hq)

/-- The chosen swapped-right neighbour really is related by `SwappedTwoStepClass`. -/
theorem someSwappedRightNeighbor_spec
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    SwappedTwoStepClass x y z w q
      (someSwappedRightNeighbor x y z w q hq).1 :=
  (someSwappedRightNeighbor x y z w q hq).2

/-- The chosen swapped-left neighbour really is related by `SwappedTwoStepClass`. -/
theorem someSwappedLeftNeighbor_spec
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    SwappedTwoStepClass x y z w
      (someSwappedLeftNeighbor x y z w q hq).1 q :=
  (someSwappedLeftNeighbor x y z w q hq).2


/-!
## Contribution-supporting swapped neighbourhoods

The raw swapped neighbourhoods are too broad for counting arguments.
What we really want are neighbours which are themselves contribution classes
on the opposite side.
-/

/-- Right contribution neighbours of a left contribution class. -/
def swappedRightContributionNeighbors
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { q' : TwoStepQuotient y x z w //
      SwappedTwoStepClass x y z w q q' ∧
      IsRightContributionClass x y z w q' }

/-- Left contribution neighbours of a right contribution class. -/
def swappedLeftContributionNeighbors
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w) :=
  { q' : TwoStepQuotient x y z w //
      SwappedTwoStepClass x y z w q' q ∧
      IsLeftContributionClass x y z w q' }

/-- Any left contribution class has a nonempty swapped-right contribution neighbourhood. -/
theorem swappedRightContributionNeighbors_nonempty
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    Nonempty (swappedRightContributionNeighbors x y z w q) := by
  rcases IsLeftContributionClass.exists_right x y z w q hq with
    ⟨q', hs, hq'⟩
  exact ⟨⟨q', hs, hq'⟩⟩

/-- Any right contribution class has a nonempty swapped-left contribution neighbourhood. -/
theorem swappedLeftContributionNeighbors_nonempty
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    Nonempty (swappedLeftContributionNeighbors x y z w q) := by
  rcases IsRightContributionClass.exists_left x y z w q hq with
    ⟨q', hs, hq'⟩
  exact ⟨⟨q', hs, hq'⟩⟩

/-- A chosen swapped-right contribution neighbour of a left contribution class. -/
noncomputable def someSwappedRightContributionNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    swappedRightContributionNeighbors x y z w q :=
  Classical.choice (swappedRightContributionNeighbors_nonempty x y z w q hq)

/-- A chosen swapped-left contribution neighbour of a right contribution class. -/
noncomputable def someSwappedLeftContributionNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    swappedLeftContributionNeighbors x y z w q :=
  Classical.choice (swappedLeftContributionNeighbors_nonempty x y z w q hq)

/-- The chosen swapped-right contribution neighbour is swapped-related. -/
theorem someSwappedRightContributionNeighbor_swapped
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    SwappedTwoStepClass x y z w q
      (someSwappedRightContributionNeighbor x y z w q hq).1 :=
  (someSwappedRightContributionNeighbor x y z w q hq).2.1

/-- The chosen swapped-right contribution neighbour is a right contribution class. -/
theorem someSwappedRightContributionNeighbor_isRight
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    IsRightContributionClass x y z w
      (someSwappedRightContributionNeighbor x y z w q hq).1 :=
  (someSwappedRightContributionNeighbor x y z w q hq).2.2

/-- The chosen swapped-left contribution neighbour is swapped-related. -/
theorem someSwappedLeftContributionNeighbor_swapped
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    SwappedTwoStepClass x y z w
      (someSwappedLeftContributionNeighbor x y z w q hq).1 q :=
  (someSwappedLeftContributionNeighbor x y z w q hq).2.1

/-- The chosen swapped-left contribution neighbour is a left contribution class. -/
theorem someSwappedLeftContributionNeighbor_isLeft
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    IsLeftContributionClass x y z w
      (someSwappedLeftContributionNeighbor x y z w q hq).1 :=
  (someSwappedLeftContributionNeighbor x y z w q hq).2.2


/-!
## Bundled neighbour transport

We now repackage contribution-supporting neighbours as actual bundled
`LeftContributionClasses` and `RightContributionClasses`.
This makes later comparison theorems cleaner.
-/

/-- Turn a swapped-right contribution neighbour into a bundled right contribution class. -/
def toRightContributionClassOfNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (r : swappedRightContributionNeighbors x y z w q) :
    RightContributionClasses x y z w :=
  ⟨r.1, r.2.2⟩

/-- Turn a swapped-left contribution neighbour into a bundled left contribution class. -/
def toLeftContributionClassOfNeighbor
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (r : swappedLeftContributionNeighbors x y z w q) :
    LeftContributionClasses x y z w :=
  ⟨r.1, r.2.2⟩

/-- The underlying quotient of the bundled right contribution class from a neighbour. -/
@[simp] theorem toRightContributionClassOfNeighbor_val
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (r : swappedRightContributionNeighbors x y z w q) :
    (toRightContributionClassOfNeighbor x y z w q r).1 = r.1 :=
  rfl

/-- The underlying quotient of the bundled left contribution class from a neighbour. -/
@[simp] theorem toLeftContributionClassOfNeighbor_val
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (r : swappedLeftContributionNeighbors x y z w q) :
    (toLeftContributionClassOfNeighbor x y z w q r).1 = r.1 :=
  rfl

/-- A swapped-right contribution neighbour yields swapped incidence with its bundled class. -/
theorem toRightContributionClassOfNeighbor_swapped
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (r : swappedRightContributionNeighbors x y z w q) :
    SwappedTwoStepClass x y z w q
      (toRightContributionClassOfNeighbor x y z w q r).1 :=
  r.2.1

/-- A swapped-left contribution neighbour yields swapped incidence with its bundled class. -/
theorem toLeftContributionClassOfNeighbor_swapped
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (r : swappedLeftContributionNeighbors x y z w q) :
    SwappedTwoStepClass x y z w
      (toLeftContributionClassOfNeighbor x y z w q r).1 q :=
  r.2.1

/-- Any bundled left contribution class has a bundled right contribution neighbour. -/
noncomputable def someRightContributionClassNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    RightContributionClasses x y z w :=
  toRightContributionClassOfNeighbor x y z w s.1
    (Classical.choice (swappedRightContributionNeighbors_nonempty x y z w s.1 s.2))

/-- Any bundled right contribution class has a bundled left contribution neighbour. -/
noncomputable def someLeftContributionClassNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    LeftContributionClasses x y z w :=
  toLeftContributionClassOfNeighbor x y z w t.1
    (Classical.choice (swappedLeftContributionNeighbors_nonempty x y z w t.1 t.2))

/-- The chosen bundled right neighbour is swapped-related to the original left class. -/
theorem someRightContributionClassNeighbor_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    SwappedTwoStepClass x y z w s.1
      (someRightContributionClassNeighbor x y z w s).1 := by
  unfold someRightContributionClassNeighbor
  let r : swappedRightContributionNeighbors x y z w s.1 :=
    Classical.choice (swappedRightContributionNeighbors_nonempty x y z w s.1 s.2)
  change SwappedTwoStepClass x y z w s.1
    (toRightContributionClassOfNeighbor x y z w s.1 r).1
  exact toRightContributionClassOfNeighbor_swapped x y z w s.1 r

/-- The chosen bundled left neighbour is swapped-related to the original right class. -/
theorem someLeftContributionClassNeighbor_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    SwappedTwoStepClass x y z w
      (someLeftContributionClassNeighbor x y z w t).1 t.1 := by
  unfold someLeftContributionClassNeighbor
  let r : swappedLeftContributionNeighbors x y z w t.1 :=
    Classical.choice (swappedLeftContributionNeighbors_nonempty x y z w t.1 t.2)
  change SwappedTwoStepClass x y z w
    (toLeftContributionClassOfNeighbor x y z w t.1 r).1 t.1
  exact toLeftContributionClassOfNeighbor_swapped x y z w t.1 r

/-- The chosen bundled right neighbour is indeed a right contribution class. -/
theorem someRightContributionClassNeighbor_isRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IsRightContributionClass x y z w
      (someRightContributionClassNeighbor x y z w s).1 :=
  (someRightContributionClassNeighbor x y z w s).2

/-- The chosen bundled left neighbour is indeed a left contribution class. -/
theorem someLeftContributionClassNeighbor_isLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IsLeftContributionClass x y z w
      (someLeftContributionClassNeighbor x y z w t).1 :=
  (someLeftContributionClassNeighbor x y z w t).2

/-!
## Bundled contribution-neighbour fibres

These are the local fibres we actually want to study:
for a fixed bundled contribution class on one side, the bundled contribution
classes on the other side which are swapped-related to it.
-/

/-- Bundled right contribution neighbours of a fixed left contribution class. -/
def rightContributionNeighborClasses
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :=
  { t : RightContributionClasses x y z w //
      SwappedTwoStepClass x y z w s.1 t.1 }

/-- Bundled left contribution neighbours of a fixed right contribution class. -/
def leftContributionNeighborClasses
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :=
  { s : LeftContributionClasses x y z w //
      SwappedTwoStepClass x y z w s.1 t.1 }

/-- Any left contribution class has a nonempty bundled right-neighbour fibre. -/
theorem rightContributionNeighborClasses_nonempty
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (rightContributionNeighborClasses x y z w s) := by
  refine ⟨⟨someRightContributionClassNeighbor x y z w s,
    someRightContributionClassNeighbor_swapped x y z w s⟩⟩

/-- Any right contribution class has a nonempty bundled left-neighbour fibre. -/
theorem leftContributionNeighborClasses_nonempty
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Nonempty (leftContributionNeighborClasses x y z w t) := by
  refine ⟨⟨someLeftContributionClassNeighbor x y z w t,
    someLeftContributionClassNeighbor_swapped x y z w t⟩⟩

/-- A chosen bundled right neighbour of a fixed left contribution class. -/
noncomputable def someRightContributionNeighborClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses x y z w s :=
  Classical.choice (rightContributionNeighborClasses_nonempty x y z w s)

/-- A chosen bundled left neighbour of a fixed right contribution class. -/
noncomputable def someLeftContributionNeighborClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses x y z w t :=
  Classical.choice (leftContributionNeighborClasses_nonempty x y z w t)

/-- The chosen bundled right neighbour is swapped-related to the fixed left class. -/
theorem someRightContributionNeighborClass_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    SwappedTwoStepClass x y z w s.1
      (someRightContributionNeighborClass x y z w s).1.1 :=
  (someRightContributionNeighborClass x y z w s).2

/-- The chosen bundled left neighbour is swapped-related to the fixed right class. -/
theorem someLeftContributionNeighborClass_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    SwappedTwoStepClass x y z w
      (someLeftContributionNeighborClass x y z w t).1.1 t.1 :=
  (someLeftContributionNeighborClass x y z w t).2




/-!
## Repackaging equivalences for local neighbour fibres

The raw neighbour subtypes and the bundled neighbour fibres contain the same
information; they are just packaged differently.
-/

/-- Repackage a raw swapped-right contribution neighbour as a bundled right neighbour fibre element. -/
def rightContributionNeighborClasses_of_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    swappedRightContributionNeighbors x y z w s.1 →
      rightContributionNeighborClasses x y z w s
  | r => ⟨⟨r.1, r.2.2⟩, r.2.1⟩

/-- Repackage a bundled right neighbour fibre element as a raw swapped-right contribution neighbour. -/
def swappedRightContributionNeighbors_of_rightClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses x y z w s →
      swappedRightContributionNeighbors x y z w s.1
  | t => ⟨t.1.1, t.2, t.1.2⟩

/-- Repackage a raw swapped-left contribution neighbour as a bundled left neighbour fibre element. -/
def leftContributionNeighborClasses_of_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    swappedLeftContributionNeighbors x y z w t.1 →
      leftContributionNeighborClasses x y z w t
  | s => ⟨⟨s.1, s.2.2⟩, s.2.1⟩

/-- Repackage a bundled left neighbour fibre element as a raw swapped-left contribution neighbour. -/
def swappedLeftContributionNeighbors_of_leftClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses x y z w t →
      swappedLeftContributionNeighbors x y z w t.1
  | s => ⟨s.1.1, s.2, s.1.2⟩

@[simp] theorem rightContributionNeighborClasses_of_swapped_val
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (r : swappedRightContributionNeighbors x y z w s.1) :
    (rightContributionNeighborClasses_of_swapped x y z w s r).1.1 = r.1 :=
  rfl

@[simp] theorem swappedRightContributionNeighbors_of_rightClass_val
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (swappedRightContributionNeighbors_of_rightClass x y z w s t).1 = t.1.1 :=
  rfl

@[simp] theorem leftContributionNeighborClasses_of_swapped_val
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (r : swappedLeftContributionNeighbors x y z w t.1) :
    (leftContributionNeighborClasses_of_swapped x y z w t r).1.1 = r.1 :=
  rfl

@[simp] theorem swappedLeftContributionNeighbors_of_leftClass_val
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (swappedLeftContributionNeighbors_of_leftClass x y z w t s).1 = s.1.1 :=
  rfl

@[simp] theorem rightContributionNeighborClasses_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (r : swappedRightContributionNeighbors x y z w s.1) :
    swappedRightContributionNeighbors_of_rightClass x y z w s
      (rightContributionNeighborClasses_of_swapped x y z w s r) = r := by
  cases r
  rfl

@[simp] theorem swappedRightContributionNeighbors_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    rightContributionNeighborClasses_of_swapped x y z w s
      (swappedRightContributionNeighbors_of_rightClass x y z w s t) = t := by
  cases t
  rfl

@[simp] theorem leftContributionNeighborClasses_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (r : swappedLeftContributionNeighbors x y z w t.1) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t
      (leftContributionNeighborClasses_of_swapped x y z w t r) = r := by
  cases r
  rfl

@[simp] theorem swappedLeftContributionNeighbors_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    leftContributionNeighborClasses_of_swapped x y z w t
      (swappedLeftContributionNeighbors_of_leftClass x y z w t s) = s := by
  cases s
  rfl

/-- The raw and bundled right neighbour presentations are equivalent. -/
def rightContributionNeighborClasses_equiv
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    swappedRightContributionNeighbors x y z w s.1 ≃
      rightContributionNeighborClasses x y z w s where
  toFun := rightContributionNeighborClasses_of_swapped x y z w s
  invFun := swappedRightContributionNeighbors_of_rightClass x y z w s
  left_inv := rightContributionNeighborClasses_roundtrip x y z w s
  right_inv := swappedRightContributionNeighbors_roundtrip x y z w s

/-- The raw and bundled left neighbour presentations are equivalent. -/
def leftContributionNeighborClasses_equiv
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    swappedLeftContributionNeighbors x y z w t.1 ≃
      leftContributionNeighborClasses x y z w t where
  toFun := leftContributionNeighborClasses_of_swapped x y z w t
  invFun := swappedLeftContributionNeighbors_of_leftClass x y z w t
  left_inv := leftContributionNeighborClasses_roundtrip x y z w t
  right_inv := swappedLeftContributionNeighbors_roundtrip x y z w t


/-!
## Transport across bundled neighbour fibres

A bundled neighbour on one side determines a nonempty bundled neighbour fibre
on the other side.  These are the first local transport maps for the swapped
correspondence.
-/

/-- A right neighbour of `s` determines a nonempty left neighbour fibre over itself. -/
theorem leftContributionNeighborClasses_nonempty_of_rightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    Nonempty (leftContributionNeighborClasses x y z w t.1) := by
  exact leftContributionNeighborClasses_nonempty x y z w t.1

/-- A left neighbour of `t` determines a nonempty right neighbour fibre over itself. -/
theorem rightContributionNeighborClasses_nonempty_of_leftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    Nonempty (rightContributionNeighborClasses x y z w s.1) := by
  exact rightContributionNeighborClasses_nonempty x y z w s.1

/-- Choose a left neighbour fibre element over a bundled right neighbour. -/
noncomputable def chooseLeftContributionNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses x y z w t.1 :=
  Classical.choice
    (leftContributionNeighborClasses_nonempty_of_rightNeighbor x y z w s t)

/-- Choose a right neighbour fibre element over a bundled left neighbour. -/
noncomputable def chooseRightContributionNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses x y z w s.1 :=
  Classical.choice
    (rightContributionNeighborClasses_nonempty_of_leftNeighbor x y z w t s)

/-- The chosen left neighbour of a right neighbour is swapped-related to that right class. -/
theorem chooseLeftContributionNeighborOfRightNeighbor_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w
      (chooseLeftContributionNeighborOfRightNeighbor x y z w s t).1.1
      t.1.1 :=
  (chooseLeftContributionNeighborOfRightNeighbor x y z w s t).2

/-- The chosen right neighbour of a left neighbour is swapped-related to that left class. -/
theorem chooseRightContributionNeighborOfLeftNeighbor_spec
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w
      s.1.1
      (chooseRightContributionNeighborOfLeftNeighbor x y z w t s).1.1 :=
  (chooseRightContributionNeighborOfLeftNeighbor x y z w t s).2

/-- Forgetting the proof, a bundled right neighbour of `s` gives a right contribution class. -/
def rightContributionNeighborClasses_to_rightClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses x y z w s → RightContributionClasses x y z w
  | t => t.1

/-- Forgetting the proof, a bundled left neighbour of `t` gives a left contribution class. -/
def leftContributionNeighborClasses_to_leftClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses x y z w t → LeftContributionClasses x y z w
  | s => s.1

@[simp] theorem rightContributionNeighborClasses_to_rightClass_val
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (rightContributionNeighborClasses_to_rightClass x y z w s t).1 = t.1.1 :=
  rfl

@[simp] theorem leftContributionNeighborClasses_to_leftClass_val
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (leftContributionNeighborClasses_to_leftClass x y z w t s).1 = s.1.1 :=
  rfl


/-!
## Basic projection lemmas for bundled neighbour fibres

These are the elementary facts we will use when extracting witness/support data
from local neighbour-fibre elements.
-/

/-- The underlying right contribution class of a bundled right neighbour fibre element. -/
def rightNeighborClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    RightContributionClasses x y z w :=
  t.1

/-- The underlying left contribution class of a bundled left neighbour fibre element. -/
def leftNeighborClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    LeftContributionClasses x y z w :=
  s.1

@[simp] theorem rightNeighborClass_val
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (rightNeighborClass x y z w s t).1 = t.1.1 :=
  rfl

@[simp] theorem leftNeighborClass_val
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (leftNeighborClass x y z w t s).1 = s.1.1 :=
  rfl

/-- A bundled right neighbour fibre element is swapped-related to its source left class. -/
theorem rightNeighborClass_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w s.1 (rightNeighborClass x y z w s t).1 :=
  t.2

/-- A bundled left neighbour fibre element is swapped-related to its source right class. -/
theorem leftNeighborClass_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w (leftNeighborClass x y z w t s).1 t.1 :=
  s.2

/-- A bundled right neighbour fibre element really determines a right contribution class. -/
theorem rightNeighborClass_isRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    IsRightContributionClass x y z w (rightNeighborClass x y z w s t).1 :=
  (rightNeighborClass x y z w s t).2

/-- A bundled left neighbour fibre element really determines a left contribution class. -/
theorem leftNeighborClass_isLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    IsLeftContributionClass x y z w (leftNeighborClass x y z w t s).1 :=
  (leftNeighborClass x y z w t s).2

/-- Extensionality for bundled right neighbour fibre elements via the underlying right class. -/
theorem rightContributionNeighborClasses_ext
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t₁ t₂ : rightContributionNeighborClasses x y z w s)
    (h : t₁.1 = t₂.1) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  cases h
  rfl

/-- Extensionality for bundled left neighbour fibre elements via the underlying left class. -/
theorem leftContributionNeighborClasses_ext
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s₁ s₂ : leftContributionNeighborClasses x y z w t)
    (h : s₁.1 = s₂.1) :
    s₁ = s₂ := by
  cases s₁
  cases s₂
  cases h
  rfl


open Classical

/-!
## Contribution classes lie in support
-/

/-- Any left-outer contribution class lies in left support. -/
theorem HasLeftOuterContributionClass.to_inLeftSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftOuterContributionClass x y z w q) :
    InLeftSupportClass x y z w q := by
  rcases hq with ⟨h, rfl⟩
  cases h with
  | mk a b z' haz hbw =>
      exact classOfLeftWitness_in_leftSupport x y z w
        (TwoStepWitnessLeft.outer a b z' haz hbw)

/-- Any swapped-right-outer contribution class lies in swapped right support. -/
theorem HasSwappedRightOuterContributionClass.to_inRightSupport
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : HasSwappedRightOuterContributionClass x y z w q) :
    InRightSupportClass y x z w q := by
  rcases hq with ⟨h, rfl⟩
  cases h with
  | mk a b z' haz hbw =>
      exact classOfRightWitness_in_rightSupport y x z w
        (TwoStepWitnessRight.outer a b z' haz hbw)

theorem HasLeftInnerContributionClass.to_inLeftSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : HasLeftInnerContributionClass x y z w q) :
    InLeftSupportClass x y z w q := by
  rcases hq with ⟨h⟩
  exact ⟨h.1.1, by
    simpa [leftInnerWitnessClass] using h.2⟩

theorem HasSwappedRightInnerContributionClass.to_inRightSupport
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : HasSwappedRightInnerContributionClass x y z w q) :
    InRightSupportClass y x z w q := by
  rcases hq with ⟨h⟩
  exact ⟨h.1.1, by
    simpa [swappedRightInnerWitnessClass] using h.2⟩

/-- Any right contribution class lies in swapped right support. -/
theorem IsRightContributionClass.to_inRightSupport
    (x y z w : PTree)
    (q : TwoStepQuotient y x z w)
    (hq : IsRightContributionClass x y z w q) :
    InRightSupportClass y x z w q := by
  rcases hq with hq | hq
  · exact HasSwappedRightOuterContributionClass.to_inRightSupport x y z w q hq
  · exact HasSwappedRightInnerContributionClass.to_inRightSupport x y z w q hq

/-- Any left contribution class lies in left support. -/
theorem IsLeftContributionClass.to_inLeftSupport
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    InLeftSupportClass x y z w q := by
  rcases hq with hq | hq
  · exact HasLeftOuterContributionClass.to_inLeftSupport x y z w q hq
  · exact HasLeftInnerContributionClass.to_inLeftSupport x y z w q hq

/-!
## First local bridge theorems
-/

/-- Any bundled right neighbour yields a left-fibre alternative. -/
theorem rightNeighbor_has_matching_leftFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    Nonempty (LeftFiber y x z w t.1.1)
    ∨
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (LeftFiber x y z w q') ∧
        SwappedTwoStepClass y x z w t.1.1 q') := by
  have ht_sup : InRightSupportClass y x z w t.1.1 :=
    IsRightContributionClass.to_inRightSupport x y z w t.1.1 t.1.2
  simpa using
    rightSupport_has_matching_leftFiber y x z w t.1.1 ht_sup

/-- Any bundled left neighbour yields a right-fibre alternative. -/
theorem leftNeighbor_has_matching_rightFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (RightFiber x y z w q') ∧
        s.1.1 = q')
    ∨
    (∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w s.1.1 q') := by
  have hs_sup : InLeftSupportClass x y z w s.1.1 :=
    IsLeftContributionClass.to_inLeftSupport x y z w s.1.1 s.1.2
  simpa [eq_comm] using
    leftSupport_has_matching_rightFiber x y z w s.1.1 hs_sup


/-- Choose some bundled right neighbour of a bundled left neighbour. -/
noncomputable def someRightContributionNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses x y z w s.1 :=
  Classical.choice <|
    rightContributionNeighborClasses_nonempty_of_leftNeighbor x y z w t s

/-- The chosen bundled right neighbour is swapped-related to the source
bundled left neighbour. -/
theorem someRightContributionNeighborOfLeftNeighbor_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w s.1.1
      (someRightContributionNeighborOfLeftNeighbor x y z w t s).1.1 :=
  (someRightContributionNeighborOfLeftNeighbor x y z w t s).2

/-- The underlying class of the chosen bundled right neighbour is indeed
a right contribution class. -/
theorem someRightContributionNeighborOfLeftNeighbor_isRight
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    IsRightContributionClass x y z w
      (someRightContributionNeighborOfLeftNeighbor x y z w t s).1.1 :=
  (someRightContributionNeighborOfLeftNeighbor x y z w t s).1.2

/-- Choose some bundled left neighbour of a bundled right neighbour. -/
noncomputable def someLeftContributionNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses x y z w t.1 :=
  Classical.choice <|
    leftContributionNeighborClasses_nonempty_of_rightNeighbor x y z w s t

/-- The chosen bundled left neighbour is swapped-related to the source
bundled right neighbour. -/
theorem someLeftContributionNeighborOfRightNeighbor_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w
      (someLeftContributionNeighborOfRightNeighbor x y z w s t).1.1 t.1.1 :=
  (someLeftContributionNeighborOfRightNeighbor x y z w s t).2

/-- The underlying class of the chosen bundled left neighbour is indeed
a left contribution class. -/
theorem someLeftContributionNeighborOfRightNeighbor_isLeft
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    IsLeftContributionClass x y z w
      (someLeftContributionNeighborOfRightNeighbor x y z w s t).1.1 :=
  (someLeftContributionNeighborOfRightNeighbor x y z w s t).1.2


@[simp] theorem rightContributionNeighborClasses_equiv_apply
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (r : swappedRightContributionNeighbors x y z w s.1) :
    rightContributionNeighborClasses_equiv x y z w s r =
      rightContributionNeighborClasses_of_swapped x y z w s r := rfl

@[simp] theorem rightContributionNeighborClasses_equiv_symm_apply
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (rightContributionNeighborClasses_equiv x y z w s).symm t =
      swappedRightContributionNeighbors_of_rightClass x y z w s t := rfl

@[simp] theorem leftContributionNeighborClasses_equiv_apply
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (r : swappedLeftContributionNeighbors x y z w t.1) :
    leftContributionNeighborClasses_equiv x y z w t r =
      leftContributionNeighborClasses_of_swapped x y z w t r := rfl

@[simp] theorem leftContributionNeighborClasses_equiv_symm_apply
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (leftContributionNeighborClasses_equiv x y z w t).symm s =
      swappedLeftContributionNeighbors_of_leftClass x y z w t s := rfl

/-- Nonemptiness transports from raw swapped-right neighbours
to bundled right neighbours. -/
theorem rightContributionNeighborClasses_nonempty_iff_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (rightContributionNeighborClasses x y z w s) ↔
      Nonempty (swappedRightContributionNeighbors x y z w s.1) := by
  constructor
  · intro h
    rcases h with ⟨t⟩
    exact ⟨(rightContributionNeighborClasses_equiv x y z w s).symm t⟩
  · intro h
    rcases h with ⟨r⟩
    exact ⟨(rightContributionNeighborClasses_equiv x y z w s) r⟩

/-- Nonemptiness transports from raw swapped-left neighbours
to bundled left neighbours. -/
theorem leftContributionNeighborClasses_nonempty_iff_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    Nonempty (leftContributionNeighborClasses x y z w t) ↔
      Nonempty (swappedLeftContributionNeighbors x y z w t.1) := by
  constructor
  · intro h
    rcases h with ⟨s⟩
    exact ⟨(leftContributionNeighborClasses_equiv x y z w t).symm s⟩
  · intro h
    rcases h with ⟨r⟩
    exact ⟨(leftContributionNeighborClasses_equiv x y z w t) r⟩

/-- Extensionality for bundled right neighbours can be checked
after transporting to the raw swapped presentation. -/
theorem rightContributionNeighborClasses_ext_of_symm
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t₁ t₂ : rightContributionNeighborClasses x y z w s)
    (h :
      swappedRightContributionNeighbors_of_rightClass x y z w s t₁ =
      swappedRightContributionNeighbors_of_rightClass x y z w s t₂) :
    t₁ = t₂ := by
  have h' := congrArg
    (rightContributionNeighborClasses_of_swapped x y z w s) h
  simpa using h'

/-- Extensionality for bundled left neighbours can be checked
after transporting to the raw swapped presentation. -/
theorem leftContributionNeighborClasses_ext_of_symm
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s₁ s₂ : leftContributionNeighborClasses x y z w t)
    (h :
      swappedLeftContributionNeighbors_of_leftClass x y z w t s₁ =
      swappedLeftContributionNeighbors_of_leftClass x y z w t s₂) :
    s₁ = s₂ := by
  have h' := congrArg
    (leftContributionNeighborClasses_of_swapped x y z w t) h
  simpa using h'



open Classical

/-!
## Chosen opposite-neighbour maps and roundtrips
-/

/-- Choose a bundled right neighbour of a bundled left neighbour. -/
noncomputable def chooseRightNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses x y z w s.1 :=
  Classical.choice <|
    rightContributionNeighborClasses_nonempty x y z w s.1

/-- Choose a bundled left neighbour of a bundled right neighbour. -/
noncomputable def chooseLeftNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses x y z w t.1 :=
  Classical.choice <|
    leftContributionNeighborClasses_nonempty x y z w t.1

/-- The chosen right neighbour of a left neighbour is swapped-related
to the source left neighbour. -/
theorem chooseRightNeighborOfLeftNeighbor_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w s.1.1
      (chooseRightNeighborOfLeftNeighbor x y z w t s).1.1 :=
  (chooseRightNeighborOfLeftNeighbor x y z w t s).2

/-- The chosen left neighbour of a right neighbour is swapped-related
to the source right neighbour. -/
theorem chooseLeftNeighborOfRightNeighbor_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w
      (chooseLeftNeighborOfRightNeighbor x y z w s t).1.1 t.1.1 :=
  (chooseLeftNeighborOfRightNeighbor x y z w s t).2

/-- The chosen right neighbour of a left neighbour is indeed right. -/
theorem chooseRightNeighborOfLeftNeighbor_isRight
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    IsRightContributionClass x y z w
      (chooseRightNeighborOfLeftNeighbor x y z w t s).1.1 :=
  (chooseRightNeighborOfLeftNeighbor x y z w t s).1.2

/-- The chosen left neighbour of a right neighbour is indeed left. -/
theorem chooseLeftNeighborOfRightNeighbor_isLeft
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    IsLeftContributionClass x y z w
      (chooseLeftNeighborOfRightNeighbor x y z w s t).1.1 :=
  (chooseLeftNeighborOfRightNeighbor x y z w s t).1.2

/-- Transport the chosen right neighbour back to the raw swapped presentation. -/
noncomputable def chooseSwappedRightNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    swappedRightContributionNeighbors x y z w s.1.1 :=
  swappedRightContributionNeighbors_of_rightClass x y z w s.1
    (chooseRightNeighborOfLeftNeighbor x y z w t s)

/-- Transport the chosen left neighbour back to the raw swapped presentation. -/
noncomputable def chooseSwappedLeftNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    swappedLeftContributionNeighbors x y z w t.1.1 :=
  swappedLeftContributionNeighbors_of_leftClass x y z w t.1
    (chooseLeftNeighborOfRightNeighbor x y z w s t)

@[simp] theorem chooseRightNeighborOfLeftNeighbor_eq_of_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses_of_swapped x y z w s.1
      (chooseSwappedRightNeighborOfLeftNeighbor x y z w t s)
      =
      chooseRightNeighborOfLeftNeighbor x y z w t s := by
  simp [chooseSwappedRightNeighborOfLeftNeighbor]

@[simp] theorem chooseLeftNeighborOfRightNeighbor_eq_of_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses_of_swapped x y z w t.1
      (chooseSwappedLeftNeighborOfRightNeighbor x y z w s t)
      =
      chooseLeftNeighborOfRightNeighbor x y z w s t := by
  simp [chooseSwappedLeftNeighborOfRightNeighbor]

@[simp] theorem chooseSwappedRightNeighborOfLeftNeighbor_eta
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    swappedRightContributionNeighbors_of_rightClass x y z w s.1
      (rightContributionNeighborClasses_of_swapped x y z w s.1
        (chooseSwappedRightNeighborOfLeftNeighbor x y z w t s))
      =
      chooseSwappedRightNeighborOfLeftNeighbor x y z w t s := by
  simp [chooseSwappedRightNeighborOfLeftNeighbor]

@[simp] theorem chooseSwappedLeftNeighborOfRightNeighbor_eta
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t.1
      (leftContributionNeighborClasses_of_swapped x y z w t.1
        (chooseSwappedLeftNeighborOfRightNeighbor x y z w s t))
      =
      chooseSwappedLeftNeighborOfRightNeighbor x y z w s t := by
  simp [chooseSwappedLeftNeighborOfRightNeighbor]


open Classical

/-!
## Canonical opposite-neighbour maps
-/

/-- The canonical bundled right neighbour attached to a left contribution class. -/
noncomputable def canonicalRightContributionNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses x y z w s :=
  ⟨someRightContributionClassNeighbor x y z w s,
    someRightContributionClassNeighbor_swapped x y z w s⟩

/-- The canonical bundled left neighbour attached to a right contribution class. -/
noncomputable def canonicalLeftContributionNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses x y z w t :=
  ⟨someLeftContributionClassNeighbor x y z w t,
    someLeftContributionClassNeighbor_swapped x y z w t⟩

@[simp] theorem canonicalRightContributionNeighbor_fst
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    (canonicalRightContributionNeighbor x y z w s).1 =
      someRightContributionClassNeighbor x y z w s := rfl

@[simp] theorem canonicalLeftContributionNeighbor_fst
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    (canonicalLeftContributionNeighbor x y z w t).1 =
      someLeftContributionClassNeighbor x y z w t := rfl

@[simp] theorem canonicalRightContributionNeighbor_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    SwappedTwoStepClass x y z w
      s.1 (canonicalRightContributionNeighbor x y z w s).1.1 :=
  (canonicalRightContributionNeighbor x y z w s).2

/-- The canonical right neighbour attached to a bundled left neighbour
depends only on its underlying left contribution class. -/
noncomputable def canonicalRightNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses x y z w s.1 :=
  canonicalRightContributionNeighbor x y z w s.1

/-- The canonical left neighbour attached to a bundled right neighbour
depends only on its underlying right contribution class. -/
noncomputable def canonicalLeftNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses x y z w t.1 :=
  canonicalLeftContributionNeighbor x y z w t.1


@[simp] theorem canonicalRightNeighborOfLeftNeighbor_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w
      s.1.1 ((canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1) := by
  let u : rightContributionNeighborClasses x y z w s.1 :=
    canonicalRightNeighborOfLeftNeighbor x y z w t s
  change SwappedTwoStepClass x y z w s.1.1 u.1.1
  exact u.2

@[simp] theorem canonicalLeftContributionNeighbor_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    SwappedTwoStepClass x y z w
      (canonicalLeftContributionNeighbor x y z w t).1.1 t.1 :=
  (canonicalLeftContributionNeighbor x y z w t).2

@[simp] theorem canonicalLeftNeighborOfRightNeighbor_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w
      (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 t.1.1 :=
  (canonicalLeftNeighborOfRightNeighbor x y z w s t).2

@[simp] theorem canonicalRightContributionNeighbor_isRight
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IsRightContributionClass x y z w
      (canonicalRightContributionNeighbor x y z w s).1.1 :=
  (canonicalRightContributionNeighbor x y z w s).1.2

@[simp] theorem canonicalLeftContributionNeighbor_isLeft
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IsLeftContributionClass x y z w
      (canonicalLeftContributionNeighbor x y z w t).1.1 :=
  (canonicalLeftContributionNeighbor x y z w t).1.2


@[simp] theorem canonicalRightNeighborOfLeftNeighbor_fst
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1 =
      someRightContributionClassNeighbor x y z w s.1 := rfl

@[simp] theorem canonicalLeftNeighborOfRightNeighbor_fst
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1 =
      someLeftContributionClassNeighbor x y z w t.1 := rfl


open Classical

/-!
## Canonical raw swapped neighbours
-/

/-- The canonical raw swapped-right neighbour attached to a left contribution class. -/
noncomputable def canonicalSwappedRightContributionNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    swappedRightContributionNeighbors x y z w s.1 :=
  swappedRightContributionNeighbors_of_rightClass x y z w s
    (canonicalRightContributionNeighbor x y z w s)

/-- The canonical raw swapped-left neighbour attached to a right contribution class. -/
noncomputable def canonicalSwappedLeftContributionNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    swappedLeftContributionNeighbors x y z w t.1 :=
  swappedLeftContributionNeighbors_of_leftClass x y z w t
    (canonicalLeftContributionNeighbor x y z w t)

@[simp] theorem canonicalSwappedRightContributionNeighbor_to_bundled
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses_of_swapped x y z w s
      (canonicalSwappedRightContributionNeighbor x y z w s)
      =
      canonicalRightContributionNeighbor x y z w s := by
  simp [canonicalSwappedRightContributionNeighbor]

@[simp] theorem canonicalSwappedLeftContributionNeighbor_to_bundled
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses_of_swapped x y z w t
      (canonicalSwappedLeftContributionNeighbor x y z w t)
      =
      canonicalLeftContributionNeighbor x y z w t := by
  simp [canonicalSwappedLeftContributionNeighbor]

@[simp] theorem canonicalRightContributionNeighbor_to_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    swappedRightContributionNeighbors_of_rightClass x y z w s
      (canonicalRightContributionNeighbor x y z w s)
      =
      canonicalSwappedRightContributionNeighbor x y z w s := by
  rfl

@[simp] theorem canonicalLeftContributionNeighbor_to_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t
      (canonicalLeftContributionNeighbor x y z w t)
      =
      canonicalSwappedLeftContributionNeighbor x y z w t := by
  rfl

/-- The canonical raw swapped-right neighbour attached to a bundled left neighbour
depends only on its underlying left contribution class. -/
noncomputable def canonicalSwappedRightNeighborOfLeftNeighbor
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    swappedRightContributionNeighbors x y z w s.1.1 :=
  canonicalSwappedRightContributionNeighbor x y z w s.1

/-- The canonical raw swapped-left neighbour attached to a bundled right neighbour
depends only on its underlying right contribution class. -/
noncomputable def canonicalSwappedLeftNeighborOfRightNeighbor
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    swappedLeftContributionNeighbors x y z w t.1.1 :=
  canonicalSwappedLeftContributionNeighbor x y z w t.1

@[simp] theorem canonicalSwappedRightNeighborOfLeftNeighbor_to_bundled
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses_of_swapped x y z w s.1
      (canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s)
      =
      canonicalRightNeighborOfLeftNeighbor x y z w t s := by
  rfl

@[simp] theorem canonicalSwappedLeftNeighborOfRightNeighbor_to_bundled
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses_of_swapped x y z w t.1
      (canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t)
      =
      canonicalLeftNeighborOfRightNeighbor x y z w s t := by
  rfl

@[simp] theorem canonicalRightNeighborOfLeftNeighbor_to_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    swappedRightContributionNeighbors_of_rightClass x y z w s.1
      (canonicalRightNeighborOfLeftNeighbor x y z w t s)
      =
      canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s := by
  rfl

@[simp] theorem canonicalLeftNeighborOfRightNeighbor_to_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t.1
      (canonicalLeftNeighborOfRightNeighbor x y z w s t)
      =
      canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t := by
  rfl


/-!
## Canonical neighbours inherit support and local fibre alternatives
-/

/-- The canonical right neighbour lies in right support. -/
theorem canonicalRightContributionNeighbor_inRightSupport
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    InRightSupportClass y x z w
      (canonicalRightContributionNeighbor x y z w s).1.1 := by
  exact IsRightContributionClass.to_inRightSupport x y z w
    (canonicalRightContributionNeighbor x y z w s).1.1
    (canonicalRightContributionNeighbor_isRight x y z w s)

/-- The canonical left neighbour lies in left support. -/
theorem canonicalLeftContributionNeighbor_inLeftSupport
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    InLeftSupportClass x y z w
      (canonicalLeftContributionNeighbor x y z w t).1.1 := by
  exact IsLeftContributionClass.to_inLeftSupport x y z w
    (canonicalLeftContributionNeighbor x y z w t).1.1
    (canonicalLeftContributionNeighbor_isLeft x y z w t)

/-- The canonical right neighbour of a bundled left neighbour lies in right support. -/
theorem canonicalRightNeighborOfLeftNeighbor_inRightSupport
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    InRightSupportClass y x z w
      (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 := by
  exact IsRightContributionClass.to_inRightSupport x y z w
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1
    (by
      simpa [canonicalRightNeighborOfLeftNeighbor] using
        canonicalRightContributionNeighbor_isRight x y z w s.1)

/-- The canonical left neighbour of a bundled right neighbour lies in left support. -/
theorem canonicalLeftNeighborOfRightNeighbor_inLeftSupport
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    InLeftSupportClass x y z w
      (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 := by
  exact IsLeftContributionClass.to_inLeftSupport x y z w
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1
    (by
      simpa [canonicalLeftNeighborOfRightNeighbor] using
        canonicalLeftContributionNeighbor_isLeft x y z w t.1)

/-- The canonical right neighbour enjoys the generic left-fibre alternative. -/
theorem canonicalRightContributionNeighbor_has_matching_leftFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    Nonempty (LeftFiber y x z w (canonicalRightContributionNeighbor x y z w s).1.1)
    ∨
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (LeftFiber x y z w q') ∧
        SwappedTwoStepClass y x z w
          (canonicalRightContributionNeighbor x y z w s).1.1 q') := by
  simpa using
    rightNeighbor_has_matching_leftFiber x y z w s
      (canonicalRightContributionNeighbor x y z w s)

/-- The canonical left neighbour enjoys the generic right-fibre alternative. -/
theorem canonicalLeftContributionNeighbor_has_matching_rightFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (RightFiber x y z w q') ∧
        (canonicalLeftContributionNeighbor x y z w t).1.1 = q')
    ∨
    (∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w
          (canonicalLeftContributionNeighbor x y z w t).1.1 q') := by
  simpa using
    leftNeighbor_has_matching_rightFiber x y z w t
      (canonicalLeftContributionNeighbor x y z w t)

/-- The canonical right neighbour of a bundled left neighbour
enjoys the generic left-fibre alternative. -/
theorem canonicalRightNeighborOfLeftNeighbor_has_matching_leftFiber
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    Nonempty (LeftFiber y x z w
      (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1)
    ∨
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (LeftFiber x y z w q') ∧
        SwappedTwoStepClass y x z w
          (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 q') := by
  simpa [canonicalRightNeighborOfLeftNeighbor] using
    canonicalRightContributionNeighbor_has_matching_leftFiber x y z w s.1

/-- The canonical left neighbour of a bundled right neighbour
enjoys the generic right-fibre alternative. -/
theorem canonicalLeftNeighborOfRightNeighbor_has_matching_rightFiber
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (∃ q' : TwoStepQuotient x y z w,
        Nonempty (RightFiber x y z w q') ∧
        (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 = q')
    ∨
    (∃ q' : TwoStepQuotient y x z w,
        Nonempty (SwappedRightFiber x y z w q') ∧
        SwappedTwoStepClass x y z w
          (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 q') := by
  simpa [canonicalLeftNeighborOfRightNeighbor] using
    canonicalLeftContributionNeighbor_has_matching_rightFiber x y z w t.1



/-!
## Canonical neighbours are stable under presentation change
-/

@[simp] theorem canonicalSwappedRightContributionNeighbor_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    swappedRightContributionNeighbors_of_rightClass x y z w s
      (rightContributionNeighborClasses_of_swapped x y z w s
        (canonicalSwappedRightContributionNeighbor x y z w s))
      =
      canonicalSwappedRightContributionNeighbor x y z w s := by
  exact rightContributionNeighborClasses_roundtrip x y z w s
    (canonicalSwappedRightContributionNeighbor x y z w s)

@[simp] theorem canonicalSwappedLeftContributionNeighbor_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t
      (leftContributionNeighborClasses_of_swapped x y z w t
        (canonicalSwappedLeftContributionNeighbor x y z w t))
      =
      canonicalSwappedLeftContributionNeighbor x y z w t := by
  exact leftContributionNeighborClasses_roundtrip x y z w t
    (canonicalSwappedLeftContributionNeighbor x y z w t)

@[simp] theorem canonicalRightContributionNeighbor_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses_of_swapped x y z w s
      (swappedRightContributionNeighbors_of_rightClass x y z w s
        (canonicalRightContributionNeighbor x y z w s))
      =
      canonicalRightContributionNeighbor x y z w s := by
  exact swappedRightContributionNeighbors_roundtrip x y z w s
    (canonicalRightContributionNeighbor x y z w s)

@[simp] theorem canonicalLeftContributionNeighbor_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses_of_swapped x y z w t
      (swappedLeftContributionNeighbors_of_leftClass x y z w t
        (canonicalLeftContributionNeighbor x y z w t))
      =
      canonicalLeftContributionNeighbor x y z w t := by
  exact swappedLeftContributionNeighbors_roundtrip x y z w t
    (canonicalLeftContributionNeighbor x y z w t)

@[simp] theorem canonicalSwappedRightNeighborOfLeftNeighbor_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    swappedRightContributionNeighbors_of_rightClass x y z w s.1
      (rightContributionNeighborClasses_of_swapped x y z w s.1
        (canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s))
      =
      canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s := by
  exact rightContributionNeighborClasses_roundtrip x y z w s.1
    (canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s)

@[simp] theorem canonicalSwappedLeftNeighborOfRightNeighbor_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    swappedLeftContributionNeighbors_of_leftClass x y z w t.1
      (leftContributionNeighborClasses_of_swapped x y z w t.1
        (canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t))
      =
      canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t := by
  exact leftContributionNeighborClasses_roundtrip x y z w t.1
    (canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t)

@[simp] theorem canonicalRightNeighborOfLeftNeighbor_roundtrip
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses_of_swapped x y z w s.1
      (swappedRightContributionNeighbors_of_rightClass x y z w s.1
        (canonicalRightNeighborOfLeftNeighbor x y z w t s))
      =
      canonicalRightNeighborOfLeftNeighbor x y z w t s := by
  exact swappedRightContributionNeighbors_roundtrip x y z w s.1
    (canonicalRightNeighborOfLeftNeighbor x y z w t s)

@[simp] theorem canonicalLeftNeighborOfRightNeighbor_roundtrip
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses_of_swapped x y z w t.1
      (swappedLeftContributionNeighbors_of_leftClass x y z w t.1
        (canonicalLeftNeighborOfRightNeighbor x y z w s t))
      =
      canonicalLeftNeighborOfRightNeighbor x y z w s t := by
  exact swappedLeftContributionNeighbors_roundtrip x y z w t.1
    (canonicalLeftNeighborOfRightNeighbor x y z w s t)




/-!
## Canonical transports across presentations
-/

@[simp] theorem canonicalSwappedRightContributionNeighbor_to_rightClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses_of_swapped x y z w s
      (canonicalSwappedRightContributionNeighbor x y z w s)
      =
      canonicalRightContributionNeighbor x y z w s := by
  rfl



@[simp] theorem canonicalSwappedLeftContributionNeighbor_to_leftClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses_of_swapped x y z w t
      (canonicalSwappedLeftContributionNeighbor x y z w t)
      =
      canonicalLeftContributionNeighbor x y z w t := by
  rfl


@[simp] theorem canonicalSwappedRightNeighborOfLeftNeighbor_to_rightClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses_of_swapped x y z w s.1
      (canonicalSwappedRightNeighborOfLeftNeighbor x y z w t s)
      =
      canonicalRightNeighborOfLeftNeighbor x y z w t s := by
  rfl



@[simp] theorem canonicalSwappedLeftNeighborOfRightNeighbor_to_leftClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses_of_swapped x y z w t.1
      (canonicalSwappedLeftNeighborOfRightNeighbor x y z w s t)
      =
      canonicalLeftNeighborOfRightNeighbor x y z w s t := by
  rfl




/-!
## First repeated-transport idempotence consequences
-/

@[simp] theorem canonicalRightContributionNeighbor_transport_twice
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    rightContributionNeighborClasses_of_swapped x y z w s
      (swappedRightContributionNeighbors_of_rightClass x y z w s
        (canonicalRightContributionNeighbor x y z w s))
      =
      canonicalRightContributionNeighbor x y z w s := by
  simp

@[simp] theorem canonicalLeftContributionNeighbor_transport_twice
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    leftContributionNeighborClasses_of_swapped x y z w t
      (swappedLeftContributionNeighbors_of_leftClass x y z w t
        (canonicalLeftContributionNeighbor x y z w t))
      =
      canonicalLeftContributionNeighbor x y z w t := by
  simp

@[simp] theorem canonicalRightNeighborOfLeftNeighbor_transport_twice
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    rightContributionNeighborClasses_of_swapped x y z w s.1
      (swappedRightContributionNeighbors_of_rightClass x y z w s.1
        (canonicalRightNeighborOfLeftNeighbor x y z w t s))
      =
      canonicalRightNeighborOfLeftNeighbor x y z w t s := by
  simp

@[simp] theorem canonicalLeftNeighborOfRightNeighbor_transport_twice
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    leftContributionNeighborClasses_of_swapped x y z w t.1
      (swappedLeftContributionNeighbors_of_leftClass x y z w t.1
        (canonicalLeftNeighborOfRightNeighbor x y z w s t))
      =
      canonicalLeftNeighborOfRightNeighbor x y z w s t := by
  simp



/-!
## Canonical opposite choice is presentation-independent
-/

@[simp] theorem canonicalRightContributionNeighbor_stable_under_repackaging
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    canonicalRightContributionNeighbor x y z w s =
      rightContributionNeighborClasses_of_swapped x y z w s
        (canonicalSwappedRightContributionNeighbor x y z w s) := by
  rfl

@[simp] theorem canonicalLeftContributionNeighbor_stable_under_repackaging
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    canonicalLeftContributionNeighbor x y z w t =
      leftContributionNeighborClasses_of_swapped x y z w t
        (canonicalSwappedLeftContributionNeighbor x y z w t) := by
  rfl

/-!
## Canonical transports preserve contribution/support predicates
-/

/-!
## Canonical transports preserve contribution predicates
-/

theorem canonicalRightContributionNeighbor_isRightContributionClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    IsRightContributionClass x y z w
      (canonicalRightContributionNeighbor x y z w s).1.1 := by
  exact (canonicalRightContributionNeighbor x y z w s).1.2

theorem canonicalLeftContributionNeighbor_isLeftContributionClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    IsLeftContributionClass x y z w
      (canonicalLeftContributionNeighbor x y z w t).1.1 := by
  exact (canonicalLeftContributionNeighbor x y z w t).1.2

theorem canonicalRightNeighborOfLeftNeighbor_isRightContributionClass
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    IsRightContributionClass x y z w
      (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 := by
  exact (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.2

theorem canonicalLeftNeighborOfRightNeighbor_isLeftContributionClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    IsLeftContributionClass x y z w
      (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 := by
  exact (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.2



/-!
## Neighbour bundles carry the swapped correspondence explicitly
-/

/-- A bundled left-neighbour of a right contribution class
is, by definition, swapped-related to that right class. -/
theorem leftContributionNeighborClasses_swapped
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w s.1.1 t.1 := by
  exact s.2

/-- A bundled right-neighbour of a left contribution class
is, by definition, swapped-related to that left class. -/
theorem rightContributionNeighborClasses_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w s.1 t.1.1 := by
  exact t.2


/-!
## Canonical neighbour-of-neighbour remains swapped-related
to the source presentation
-/

theorem canonicalRightNeighborOfLeftNeighbor_swapped_to_source
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    SwappedTwoStepClass x y z w
      s.1.1
      (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 := by
  -- This should be the defining witness carried by the canonical rebundling.
  -- If `rfl` does not close it, try:
  --   exact (canonicalRightNeighborOfLeftNeighbor x y z w t s).2
  exact (canonicalRightNeighborOfLeftNeighbor x y z w t s).2

theorem canonicalLeftNeighborOfRightNeighbor_swapped_to_source
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    SwappedTwoStepClass x y z w
      (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1
      t.1.1 := by
  -- As above: this should be the witness stored in the canonical rebundling.
  exact (canonicalLeftNeighborOfRightNeighbor x y z w s t).2



/-!
## Conditional recovery from neighbour-fibre subsingletonness
-/

/-- If the right-neighbour fibre over any left class is subsingleton,
then canonical right-neighbour reconstruction recovers the original target. -/
theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled_of_subsingleton
    (x y z w : PTree)
    (hsub :
      ∀ s : LeftContributionClasses x y z w,
        Subsingleton (rightContributionNeighborClasses x y z w s))
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1 = t := by
  have h :
      canonicalRightNeighborOfLeftNeighbor x y z w t s
        =
      ⟨t, s.2⟩ := by
    exact @Subsingleton.elim
      (rightContributionNeighborClasses x y z w s.1)
      (hsub s.1)
      (canonicalRightNeighborOfLeftNeighbor x y z w t s)
      ⟨t, s.2⟩
  exact congrArg Subtype.val h

/-- Dual conditional recovery on the left. -/
theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled_of_subsingleton
    (x y z w : PTree)
    (hsub :
      ∀ t : RightContributionClasses x y z w,
        Subsingleton (leftContributionNeighborClasses x y z w t))
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1 = s := by
  have h :
      canonicalLeftNeighborOfRightNeighbor x y z w s t
        =
      ⟨s, t.2⟩ := by
    exact @Subsingleton.elim
      (leftContributionNeighborClasses x y z w t.1)
      (hsub t.1)
      (canonicalLeftNeighborOfRightNeighbor x y z w s t)
      ⟨s, t.2⟩
  exact congrArg Subtype.val h

/-- Under the same hypothesis, recover the underlying right quotient. -/
theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_of_subsingleton
    (x y z w : PTree)
    (hsub :
      ∀ s : LeftContributionClasses x y z w,
        Subsingleton (rightContributionNeighborClasses x y z w s))
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 = t.1 := by
  simpa using congrArg Subtype.val
    (canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled_of_subsingleton
      x y z w hsub t s)

/-- Dual underlying recovery on the left. -/
theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_of_subsingleton
    (x y z w : PTree)
    (hsub :
      ∀ t : RightContributionClasses x y z w,
        Subsingleton (leftContributionNeighborClasses x y z w t))
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 = s.1 := by
  simpa using congrArg Subtype.val
    (canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled_of_subsingleton
      x y z w hsub s t)


/-!
## Abstract neighbour-fibre uniqueness hypotheses
-/

/-- Uniqueness of right-neighbour classes over a fixed left contribution class. -/
def RightNeighborFiberUnique
    (x y z w : PTree) : Prop :=
  ∀ s : LeftContributionClasses x y z w,
    ∀ u v : rightContributionNeighborClasses x y z w s,
      u.1 = v.1

/-- Uniqueness of left-neighbour classes over a fixed right contribution class. -/
def LeftNeighborFiberUnique
    (x y z w : PTree) : Prop :=
  ∀ t : RightContributionClasses x y z w,
    ∀ s₁ s₂ : leftContributionNeighborClasses x y z w t,
      s₁.1 = s₂.1


/-!
## Subsingleton consequences
-/

theorem rightContributionNeighborClasses_subsingleton_of_unique
    (x y z w : PTree)
    (hUnique : RightNeighborFiberUnique x y z w)
    (s : LeftContributionClasses x y z w) :
    Subsingleton (rightContributionNeighborClasses x y z w s) := by
  refine ⟨?_⟩
  intro u v
  apply rightContributionNeighborClasses_ext x y z w s u v
  exact hUnique s u v

theorem leftContributionNeighborClasses_subsingleton_of_unique
    (x y z w : PTree)
    (hUnique : LeftNeighborFiberUnique x y z w)
    (t : RightContributionClasses x y z w) :
    Subsingleton (leftContributionNeighborClasses x y z w t) := by
  refine ⟨?_⟩
  intro s₁ s₂
  apply leftContributionNeighborClasses_ext x y z w t s₁ s₂
  exact hUnique t s₁ s₂


/-!
## Recovery consequences
-/

theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled_of_unique
    (x y z w : PTree)
    (hUnique : RightNeighborFiberUnique x y z w)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1 = t := by
  have hsub :
      ∀ s : LeftContributionClasses x y z w,
        Subsingleton (rightContributionNeighborClasses x y z w s) :=
    rightContributionNeighborClasses_subsingleton_of_unique x y z w hUnique
  exact
    canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled_of_subsingleton
      x y z w hsub t s

theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled_of_unique
    (x y z w : PTree)
    (hUnique : LeftNeighborFiberUnique x y z w)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1 = s := by
  have hsub :
      ∀ t : RightContributionClasses x y z w,
        Subsingleton (leftContributionNeighborClasses x y z w t) :=
    leftContributionNeighborClasses_subsingleton_of_unique x y z w hUnique
  exact
    canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled_of_subsingleton
      x y z w hsub s t

theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_of_unique
    (x y z w : PTree)
    (hUnique : RightNeighborFiberUnique x y z w)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1.1 = t.1 := by
  simpa using congrArg Subtype.val
    (canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled_of_unique
      x y z w hUnique t s)

theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_of_unique
    (x y z w : PTree)
    (hUnique : LeftNeighborFiberUnique x y z w)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1.1 = s.1 := by
  simpa using congrArg Subtype.val
    (canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled_of_unique
      x y z w hUnique s t)


/-!
## Outer-fragment bridge data
-/

/-- A left contribution class whose underlying quotient is outer-supported. -/
def HasOuterSupportLeftContributionClass
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) : Prop :=
  HasLeftOuterContributionClass x y z w s.1

/-- Any outer-supported left contribution class has some swapped right-outer partner. -/
theorem HasOuterSupportLeftContributionClass.exists_swapped_rightOuter
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w s.1 q' ∧
      HasSwappedRightOuterContributionClass x y z w q' := by
  exact HasLeftOuterContributionClass.exists_rightOuter x y z w s.1 hs

/-- A canonical swapped right-outer partner quotient for an outer-supported left class. -/
noncomputable def canonicalSwappedRightOuterPartner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    TwoStepQuotient y x z w :=
  Classical.choose
    (HasOuterSupportLeftContributionClass.exists_swapped_rightOuter x y z w s hs)

/-- The canonical swapped right-outer partner is swapped-related to the source class. -/
theorem canonicalSwappedRightOuterPartner_swapped
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    SwappedTwoStepClass x y z w s.1
      (canonicalSwappedRightOuterPartner x y z w s hs) := by
  exact
    (Classical.choose_spec
      (HasOuterSupportLeftContributionClass.exists_swapped_rightOuter x y z w s hs)).1

/-- The canonical swapped right-outer partner is right-outer-supported. -/
theorem canonicalSwappedRightOuterPartner_has_rightOuter
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    HasSwappedRightOuterContributionClass x y z w
      (canonicalSwappedRightOuterPartner x y z w s hs) := by
  exact
    (Classical.choose_spec
      (HasOuterSupportLeftContributionClass.exists_swapped_rightOuter x y z w s hs)).2

/-- Outer-supported left classes admit at least one raw swapped right partner. -/
theorem HasOuterSupportLeftContributionClass.exists_swapped_rightPartner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w s.1 q' := by
  refine ⟨canonicalSwappedRightOuterPartner x y z w s hs, ?_⟩
  exact canonicalSwappedRightOuterPartner_swapped x y z w s hs


/-!
## Outer-fragment uniqueness hypotheses
-/

def RightOuterNeighborFiberUnique
    (x y z w : PTree) : Prop :=
  ∀ s : LeftContributionClasses x y z w,
    HasOuterSupportLeftContributionClass x y z w s →
    ∀ u v : RightContributionClasses x y z w,
      SwappedTwoStepClass x y z w s.1 u.1 →
      SwappedTwoStepClass x y z w s.1 v.1 →
      u = v

theorem rightContributionClass_eq_of_outerUnique
    (x y z w : PTree)
    (hUnique : RightOuterNeighborFiberUnique x y z w)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s)
    (u v : RightContributionClasses x y z w)
    (hu : SwappedTwoStepClass x y z w s.1 u.1)
    (hv : SwappedTwoStepClass x y z w s.1 v.1) :
    u = v := by
  exact hUnique s hs u v hu hv

/-!
## Outer-supported source classes: witness extraction
-/

/-- Unpack outer support of a left contribution class into an explicit outer-left witness. -/
theorem HasOuterSupportLeftContributionClass.exists_outerLeftWitness
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    ∃ h : OuterLeftWitness x y z w,
      outerLeftWitnessClass h = s.1 := by
  exact hs

/-- A canonical outer-left witness attached to an outer-supported left contribution class. -/
noncomputable def canonicalOuterLeftWitnessOfOuterSupport
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    OuterLeftWitness x y z w :=
  Classical.choose
    (HasOuterSupportLeftContributionClass.exists_outerLeftWitness x y z w s hs)

/-- The canonical outer-left witness has the expected class. -/
theorem canonicalOuterLeftWitnessOfOuterSupport_class
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    outerLeftWitnessClass
      (canonicalOuterLeftWitnessOfOuterSupport x y z w s hs) = s.1 := by
  exact
    Classical.choose_spec
      (HasOuterSupportLeftContributionClass.exists_outerLeftWitness x y z w s hs)

/-- Repackage the canonical outer-left witness as outer support again. -/
theorem canonicalOuterLeftWitnessOfOuterSupport_has_outerSupport
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    HasLeftOuterContributionClass x y z w s.1 := by
  refine ⟨canonicalOuterLeftWitnessOfOuterSupport x y z w s hs, ?_⟩
  exact canonicalOuterLeftWitnessOfOuterSupport_class x y z w s hs


/-!
## Canonical right-outer partner induced by the canonical outer-left witness
-/

/-- The canonical outer-left witness determines a swapped right-outer partner. -/
theorem canonicalOuterLeftWitnessOfOuterSupport_exists_rightOuter
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w s.1 q' ∧
      HasSwappedRightOuterContributionClass x y z w q' := by
  exact HasLeftOuterContributionClass.exists_rightOuter x y z w s.1
    (canonicalOuterLeftWitnessOfOuterSupport_has_outerSupport x y z w s hs)

/-- The canonical swapped right-outer partner may be recovered from the canonical outer-left witness. -/
theorem canonicalSwappedRightOuterPartner_spec
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    SwappedTwoStepClass x y z w s.1
      (canonicalSwappedRightOuterPartner x y z w s hs)
    ∧
    HasSwappedRightOuterContributionClass x y z w
      (canonicalSwappedRightOuterPartner x y z w s hs) := by
  exact Classical.choose_spec
    (HasOuterSupportLeftContributionClass.exists_swapped_rightOuter x y z w s hs)



def outerLeftToOuterRight
    (x y z w : PTree) :
    OuterLeftWitness x y z w → OuterRightWitness y x z w
| .mk a b z' haz hbw => .mk a b z' haz hbw

#check outerLeftToOuterRight

def outerRightToOuterLeft
    (x y z w : PTree) :
    OuterRightWitness y x z w → OuterLeftWitness x y z w
| .mk a b z' haz hbw => .mk a b z' haz hbw

@[simp] theorem outerRightToOuterLeft_outerLeftToOuterRight
    (x y z w : PTree)
    (h : OuterLeftWitness x y z w) :
    outerRightToOuterLeft x y z w (outerLeftToOuterRight x y z w h) = h := by
  cases h
  rfl

@[simp] theorem outerLeftToOuterRight_outerRightToOuterLeft
    (x y z w : PTree)
    (r : OuterRightWitness y x z w) :
    outerLeftToOuterRight x y z w (outerRightToOuterLeft x y z w r) = r := by
  cases r
  rfl

/-- Outer commutation is a bijection of witness data. -/
def outerCommute
    (x y z w : PTree) :
    OuterLeftWitness x y z w ≃ OuterRightWitness y x z w where
  toFun := outerLeftToOuterRight x y z w
  invFun := outerRightToOuterLeft x y z w
  left_inv := outerRightToOuterLeft_outerLeftToOuterRight x y z w
  right_inv := outerLeftToOuterRight_outerRightToOuterLeft x y z w

@[simp] theorem outerLeftToOuterRight_swapped
    (x y z w : PTree)
    (h : OuterLeftWitness x y z w) :
    SwappedTwoStepClass x y z w
      (outerLeftWitnessClass h)
      (outerRightWitnessClass (outerLeftToOuterRight x y z w h)) := by
  cases h with
  | mk a b z' haz hbw =>
      simpa [outerLeftWitnessClass, outerRightWitnessClass,
        outerLeftToOuterRight,
        classOfLeftWitness, classOfRightWitness,
        codeOfLeftWitness, codeOfRightWitness]
        using
          (SwappedTwoStepClass.leftOuter
            (x := x) (y := y) (z := z) (w := w)
            a b z' haz hbw)

@[simp] theorem outerRightToOuterLeft_swapped
    (x y z w : PTree)
    (r : OuterRightWitness y x z w) :
    SwappedTwoStepClass x y z w
      (outerLeftWitnessClass (outerRightToOuterLeft x y z w r))
      (outerRightWitnessClass r) := by
  cases r with
  | mk a b z' haz hbw =>
      simpa [outerLeftWitnessClass, outerRightWitnessClass,
        outerRightToOuterLeft,
        classOfLeftWitness, classOfRightWitness,
        codeOfLeftWitness, codeOfRightWitness]
        using
          (SwappedTwoStepClass.leftOuter
            (x := x) (y := y) (z := z) (w := w)
            a b z' haz hbw)

/--
An explicit outer-left witness determines its swapped right-outer class partner,
and that target class is visibly outer-supported on the swapped side.
-/
theorem outerLeftToOuterRight_class_spec
    (x y z w : PTree)
    (h : OuterLeftWitness x y z w) :
    SwappedTwoStepClass x y z w
      (outerLeftWitnessClass h)
      (outerRightWitnessClass (outerLeftToOuterRight x y z w h))
    ∧
    HasSwappedRightOuterContributionClass x y z w
      (outerRightWitnessClass (outerLeftToOuterRight x y z w h)) := by
  refine ⟨outerLeftToOuterRight_swapped x y z w h, ?_⟩
  exact ⟨outerLeftToOuterRight x y z w h, rfl⟩

/--
An explicit swapped right-outer witness determines its left-outer class partner,
and that source class is visibly outer-supported on the original side.
-/
theorem outerRightToOuterLeft_class_spec
    (x y z w : PTree)
    (r : OuterRightWitness y x z w) :
    SwappedTwoStepClass x y z w
      (outerLeftWitnessClass (outerRightToOuterLeft x y z w r))
      (outerRightWitnessClass r)
    ∧
    HasLeftOuterContributionClass x y z w
      (outerLeftWitnessClass (outerRightToOuterLeft x y z w r)) := by
  refine ⟨outerRightToOuterLeft_swapped x y z w r, ?_⟩
  exact ⟨outerRightToOuterLeft x y z w r, rfl⟩

/--
Swap the orientation of a raw two-step code by exchanging the left/right
presentation and simultaneously swapping the first two tree arguments.
-/
def swapTwoStepCode
    (x y z w : PTree) :
    TwoStepCode x y z w → TwoStepCode y x z w
  | TwoStepCode.leftOuter a b z' haz hbw =>
      TwoStepCode.rightOuter a b z' haz hbw
  | TwoStepCode.leftInner a b y' hay hbw =>
      TwoStepCode.rightInner a b y' hay hbw
  | TwoStepCode.rightOuter a b z' haz hbw =>
      TwoStepCode.leftOuter a b z' haz hbw
  | TwoStepCode.rightInner a b y' hay hbw =>
      TwoStepCode.leftInner a b y' hay hbw

@[simp] theorem swapTwoStepCode_involutive
    (x y z w : PTree)
    (c : TwoStepCode x y z w) :
    swapTwoStepCode y x z w (swapTwoStepCode x y z w c) = c := by
  cases c <;> rfl

/--
The raw code swap preserves the bureaucratic equivalence relation.
-/
theorem swapTwoStepCode_respects_equiv
    (x y z w : PTree)
    {c d : TwoStepCode x y z w}
    (h : TwoStepEquiv x y z w c d) :
    TwoStepEquiv y x z w
      (swapTwoStepCode x y z w c)
      (swapTwoStepCode x y z w d) := by
  induction h with
  | refl c =>
      exact TwoStepEquiv.refl _
  | symm h ih =>
      exact TwoStepEquiv.symm ih
  | trans h₁ h₂ ih₁ ih₂ =>
      exact TwoStepEquiv.trans ih₁ ih₂
  | outer_comm_outer haz hbw haz' hbw' haddr =>
      exact TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
        simpa [mem_twoStepAddrWitnessesRight_iff, mem_twoStepAddrWitnessesLeft_iff]
          using haddr)
  | outer_comm_inner haz hbw hay' hbw' haddr =>
      exact TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
        simpa [mem_twoStepAddrWitnessesRight_iff, mem_twoStepAddrWitnessesLeft_iff]
          using haddr)
  | outer_comm_back_outer haz hbw haz' hbw' haddr =>
      exact TwoStepEquiv.outer_comm_outer haz hbw haz' hbw' (by
        simpa [mem_twoStepAddrWitnessesLeft_iff, mem_twoStepAddrWitnessesRight_iff]
          using haddr)
  | outer_comm_back_inner haz hbw hay' hbw' haddr =>
      exact TwoStepEquiv.outer_comm_inner haz hbw hay' hbw' (by
        simpa [mem_twoStepAddrWitnessesLeft_iff, mem_twoStepAddrWitnessesRight_iff]
          using haddr)

/--
Equality of quotient classes is preserved by swapping the raw code
presentation.
-/
theorem swapTwoStepCode_respects_class
    (x y z w : PTree)
    {c d : TwoStepCode x y z w}
    (h : codeClass c = codeClass d) :
    codeClass (swapTwoStepCode x y z w c) =
      codeClass (swapTwoStepCode x y z w d) := by
  apply codeClass_eq_of_equiv
  exact
    swapTwoStepCode_respects_equiv x y z w
      (Quotient.exact h)

/--
The explicit outer transport descends to quotient classes on the left side.
-/
theorem outerLeftToOuterRight_respects_class
    (x y z w : PTree)
    (h₁ h₂ : OuterLeftWitness x y z w)
    (hh : outerLeftWitnessClass h₁ = outerLeftWitnessClass h₂) :
    outerRightWitnessClass (outerLeftToOuterRight x y z w h₁) =
      outerRightWitnessClass (outerLeftToOuterRight x y z w h₂) := by
  cases h₁ with
  | mk a₁ b₁ z₁ haz₁ hbw₁ =>
      cases h₂ with
      | mk a₂ b₂ z₂ haz₂ hbw₂ =>
          have hcode :
              codeClass (TwoStepCode.leftOuter a₁ b₁ z₁ haz₁ hbw₁) =
                codeClass (TwoStepCode.leftOuter a₂ b₂ z₂ haz₂ hbw₂) := by
            simpa [outerLeftWitnessClass, classOfLeftWitness, codeOfLeftWitness]
              using hh
          simpa [outerRightWitnessClass, outerLeftToOuterRight,
            swapTwoStepCode, classOfRightWitness, codeOfRightWitness]
            using
              (swapTwoStepCode_respects_class x y z w
                (c := TwoStepCode.leftOuter a₁ b₁ z₁ haz₁ hbw₁)
                (d := TwoStepCode.leftOuter a₂ b₂ z₂ haz₂ hbw₂)
                hcode)

/--
The inverse explicit outer transport descends to quotient classes on the
swapped right side.
-/
theorem outerRightToOuterLeft_respects_class
    (x y z w : PTree)
    (r₁ r₂ : OuterRightWitness y x z w)
    (hh : outerRightWitnessClass r₁ = outerRightWitnessClass r₂) :
    outerLeftWitnessClass (outerRightToOuterLeft x y z w r₁) =
      outerLeftWitnessClass (outerRightToOuterLeft x y z w r₂) := by
  cases r₁ with
  | mk a₁ b₁ z₁ haz₁ hbw₁ =>
      cases r₂ with
      | mk a₂ b₂ z₂ haz₂ hbw₂ =>
          have hcode :
              codeClass (TwoStepCode.rightOuter a₁ b₁ z₁ haz₁ hbw₁) =
                codeClass (TwoStepCode.rightOuter a₂ b₂ z₂ haz₂ hbw₂) := by
            simpa [outerRightWitnessClass, classOfRightWitness, codeOfRightWitness]
              using hh
          simpa [outerLeftWitnessClass, outerRightToOuterLeft,
            swapTwoStepCode, classOfLeftWitness, codeOfLeftWitness]
            using
              (swapTwoStepCode_respects_class y x z w
                (c := TwoStepCode.rightOuter a₁ b₁ z₁ haz₁ hbw₁)
                (d := TwoStepCode.rightOuter a₂ b₂ z₂ haz₂ hbw₂)
                hcode)

/-- Outer-supported left quotient classes. -/
def OuterLeftContributionClasses
    (x y z w : PTree) :=
  { q : TwoStepQuotient x y z w // HasLeftOuterContributionClass x y z w q }

/-- Swapped right-outer-supported quotient classes. -/
def SwappedRightOuterContributionClasses
    (x y z w : PTree) :=
  { q' : TwoStepQuotient y x z w //
      HasSwappedRightOuterContributionClass x y z w q' }

/--
Transport an outer-supported left class to its swapped right-outer class by
choosing any explicit outer-left witness and applying the witness-level
commutation bijection.
-/
noncomputable def transportOuterLeftContributionClass
    (x y z w : PTree) :
    OuterLeftContributionClasses x y z w →
      SwappedRightOuterContributionClasses x y z w
  | ⟨q, hq⟩ =>
      let h : OuterLeftWitness x y z w := Classical.choose hq
      ⟨outerRightWitnessClass (outerLeftToOuterRight x y z w h),
        ⟨outerLeftToOuterRight x y z w h, rfl⟩⟩

/--
Transport a swapped right-outer-supported class back to the original
left-outer side by applying the inverse witness-level commutation map.
-/
noncomputable def transportSwappedRightOuterContributionClass
    (x y z w : PTree) :
    SwappedRightOuterContributionClasses x y z w →
      OuterLeftContributionClasses x y z w
  | ⟨q', hq'⟩ =>
      let r : OuterRightWitness y x z w := Classical.choose hq'
      ⟨outerLeftWitnessClass (outerRightToOuterLeft x y z w r),
        ⟨outerRightToOuterLeft x y z w r, rfl⟩⟩

/--
The class-level outer transport is related to its source by
`SwappedTwoStepClass`.
-/
theorem transportOuterLeftContributionClass_swapped
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :
    SwappedTwoStepClass x y z w s.1
      (transportOuterLeftContributionClass x y z w s).1 := by
  rcases s with ⟨q, hq⟩
  let h : OuterLeftWitness x y z w := Classical.choose hq
  have hh : outerLeftWitnessClass h = q := Classical.choose_spec hq
  exact
    swapped_respects_eq_left x y z w hh
      (outerLeftToOuterRight_swapped x y z w h)

/--
The inverse class-level outer transport is related to its source by
`SwappedTwoStepClass`.
-/
theorem transportSwappedRightOuterContributionClass_swapped
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :
    SwappedTwoStepClass x y z w
      (transportSwappedRightOuterContributionClass x y z w t).1
      t.1 := by
  rcases t with ⟨q', hq'⟩
  let r : OuterRightWitness y x z w := Classical.choose hq'
  have hr : outerRightWitnessClass r = q' := Classical.choose_spec hq'
  exact
    swapped_respects_eq_right x y z w hr
      (outerRightToOuterLeft_swapped x y z w r)

/--
The class-level outer transport agrees with the explicit witness-level transport
for any chosen representative of the source class.
-/
theorem transportOuterLeftContributionClass_eq_of_witness
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w)
    (h : OuterLeftWitness x y z w)
    (hh : outerLeftWitnessClass h = s.1) :
    (transportOuterLeftContributionClass x y z w s).1 =
      outerRightWitnessClass (outerLeftToOuterRight x y z w h) := by
  rcases s with ⟨q, hq⟩
  let h₀ : OuterLeftWitness x y z w := Classical.choose hq
  have hh₀ : outerLeftWitnessClass h₀ = q := Classical.choose_spec hq
  exact
    outerLeftToOuterRight_respects_class x y z w h₀ h
      (hh₀.trans hh.symm)

/--
The inverse class-level outer transport agrees with the inverse witness-level
transport for any chosen representative of the swapped target class.
-/
theorem transportSwappedRightOuterContributionClass_eq_of_witness
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w)
    (r : OuterRightWitness y x z w)
    (hr : outerRightWitnessClass r = t.1) :
    (transportSwappedRightOuterContributionClass x y z w t).1 =
      outerLeftWitnessClass (outerRightToOuterLeft x y z w r) := by
  rcases t with ⟨q', hq'⟩
  let r₀ : OuterRightWitness y x z w := Classical.choose hq'
  have hr₀ : outerRightWitnessClass r₀ = q' := Classical.choose_spec hq'
  exact
    outerRightToOuterLeft_respects_class x y z w r₀ r
      (hr₀.trans hr.symm)

/--
The two class-level outer transports are inverse on outer-supported left
classes.
-/
theorem transportSwappedRightOuterContributionClass_left_inv
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :
    transportSwappedRightOuterContributionClass x y z w
      (transportOuterLeftContributionClass x y z w s) = s := by
  apply Subtype.ext
  rcases s with ⟨q, hq⟩
  let h : OuterLeftWitness x y z w := Classical.choose hq
  have hh : outerLeftWitnessClass h = q := Classical.choose_spec hq
  calc
    (transportSwappedRightOuterContributionClass x y z w
        (transportOuterLeftContributionClass x y z w ⟨q, hq⟩)).1
      = outerLeftWitnessClass
          (outerRightToOuterLeft x y z w (outerLeftToOuterRight x y z w h)) := by
            apply transportSwappedRightOuterContributionClass_eq_of_witness
            exact rfl
    _ = outerLeftWitnessClass h := by
          simp
    _ = q := hh

/--
The two class-level outer transports are inverse on swapped right-outer
supported classes.
-/
theorem transportOuterLeftContributionClass_right_inv
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :
    transportOuterLeftContributionClass x y z w
      (transportSwappedRightOuterContributionClass x y z w t) = t := by
  apply Subtype.ext
  rcases t with ⟨q', hq'⟩
  let r : OuterRightWitness y x z w := Classical.choose hq'
  have hr : outerRightWitnessClass r = q' := Classical.choose_spec hq'
  calc
    (transportOuterLeftContributionClass x y z w
        (transportSwappedRightOuterContributionClass x y z w ⟨q', hq'⟩)).1
      = outerRightWitnessClass
          (outerLeftToOuterRight x y z w (outerRightToOuterLeft x y z w r)) := by
            apply transportOuterLeftContributionClass_eq_of_witness
            exact rfl
    _ = outerRightWitnessClass r := by
          simp
    _ = q' := hr

/-- Outer-supported classes are equivalent across the swapped outer transport. -/
noncomputable def outerContributionCommute
    (x y z w : PTree) :
    OuterLeftContributionClasses x y z w ≃
      SwappedRightOuterContributionClasses x y z w where
  toFun := transportOuterLeftContributionClass x y z w
  invFun := transportSwappedRightOuterContributionClass x y z w
  left_inv := transportSwappedRightOuterContributionClass_left_inv x y z w
  right_inv := transportOuterLeftContributionClass_right_inv x y z w

/--
Any swapped right-outer-supported class mapping back to `s` must be the
canonical transported outer partner of `s`.
-/
theorem transportOuterLeftContributionClass_unique
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w)
    (t : SwappedRightOuterContributionClasses x y z w)
    (ht : transportSwappedRightOuterContributionClass x y z w t = s) :
    t = transportOuterLeftContributionClass x y z w s := by
  calc
    t = transportOuterLeftContributionClass x y z w
          (transportSwappedRightOuterContributionClass x y z w t) := by
            symm
            exact (outerContributionCommute x y z w).right_inv t
    _ = transportOuterLeftContributionClass x y z w s := by
          rw [ht]

/--
Any outer-supported left class mapping forward to `t` must be the canonical
inverse-transported source of `t`.
-/
theorem transportSwappedRightOuterContributionClass_unique
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w)
    (t : SwappedRightOuterContributionClasses x y z w)
    (hs : transportOuterLeftContributionClass x y z w s = t) :
    s = transportSwappedRightOuterContributionClass x y z w t := by
  calc
    s = transportSwappedRightOuterContributionClass x y z w
          (transportOuterLeftContributionClass x y z w s) := by
            symm
            exact (outerContributionCommute x y z w).left_inv s
    _ = transportSwappedRightOuterContributionClass x y z w t := by
          rw [hs]

/-- The outer right-partner fibre over an outer-supported left class. -/
def OuterRightContributionFiber
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :=
  { t : SwappedRightOuterContributionClasses x y z w //
      transportSwappedRightOuterContributionClass x y z w t = s }

/-- The outer left-partner fibre over a swapped right-outer-supported class. -/
def OuterLeftContributionFiber
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :=
  { s : OuterLeftContributionClasses x y z w //
      transportOuterLeftContributionClass x y z w s = t }

/-- The canonical outer right partner lies in the outer right fibre. -/
noncomputable def canonicalOuterRightContributionFiberPoint
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :
    OuterRightContributionFiber x y z w s :=
  ⟨transportOuterLeftContributionClass x y z w s,
    (outerContributionCommute x y z w).left_inv s⟩

/-- The canonical outer left partner lies in the outer left fibre. -/
noncomputable def canonicalOuterLeftContributionFiberPoint
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :
    OuterLeftContributionFiber x y z w t :=
  ⟨transportSwappedRightOuterContributionClass x y z w t,
    (outerContributionCommute x y z w).right_inv t⟩

/-- The outer right-partner fibre is degree 1. -/
theorem OuterRightContributionFiber_subsingleton
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :
    Subsingleton (OuterRightContributionFiber x y z w s) := by
  refine ⟨?_⟩
  intro u v
  apply Subtype.ext
  calc
    u.1 = transportOuterLeftContributionClass x y z w s := by
      exact transportOuterLeftContributionClass_unique x y z w s u.1 u.2
    _ = v.1 := by
      symm
      exact transportOuterLeftContributionClass_unique x y z w s v.1 v.2

/-- The outer left-partner fibre is degree 1. -/
theorem OuterLeftContributionFiber_subsingleton
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :
    Subsingleton (OuterLeftContributionFiber x y z w t) := by
  refine ⟨?_⟩
  intro s₁ s₂
  apply Subtype.ext
  calc
    s₁.1 = transportSwappedRightOuterContributionClass x y z w t := by
      exact transportSwappedRightOuterContributionClass_unique x y z w s₁.1 t s₁.2
    _ = s₂.1 := by
      symm
      exact transportSwappedRightOuterContributionClass_unique x y z w s₂.1 t s₂.2

/--
Outer-supported left classes have a unique swapped right-outer partner at the
class level.
-/
theorem outer_supported_left_class_has_unique_swapped_right_outer_partner
    (x y z w : PTree)
    (s : OuterLeftContributionClasses x y z w) :
    ∃! t : SwappedRightOuterContributionClasses x y z w,
      transportSwappedRightOuterContributionClass x y z w t = s := by
  refine ⟨transportOuterLeftContributionClass x y z w s, ?_, ?_⟩
  · exact (outerContributionCommute x y z w).left_inv s
  · intro t ht
    exact transportOuterLeftContributionClass_unique x y z w s t ht

/--
Swapped right-outer-supported classes have a unique outer-supported left partner
at the class level.
-/
theorem swapped_right_outer_class_has_unique_outer_left_partner
    (x y z w : PTree)
    (t : SwappedRightOuterContributionClasses x y z w) :
    ∃! s : OuterLeftContributionClasses x y z w,
      transportOuterLeftContributionClass x y z w s = t := by
  refine ⟨transportSwappedRightOuterContributionClass x y z w t, ?_, ?_⟩
  · exact (outerContributionCommute x y z w).right_inv t
  · intro s hs
    exact transportSwappedRightOuterContributionClass_unique x y z w s t hs

/--
Repackaged in the original left-contribution-class language: an outer-supported
left class has a canonical swapped right-outer partner, unique among outer
targets.
-/
theorem outer_supported_left_contribution_class_has_degree1_outer_partner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (hs : HasOuterSupportLeftContributionClass x y z w s) :
    ∃! t : SwappedRightOuterContributionClasses x y z w,
      transportSwappedRightOuterContributionClass x y z w t = ⟨s.1, hs⟩ := by
  exact
    outer_supported_left_class_has_unique_swapped_right_outer_partner
      x y z w ⟨s.1, hs⟩

/-!
## Global outer/inner decomposition of contribution classes
-/

/-- Total left contribution classes split into outer and inner sectors. -/
def LeftContributionClassDecomposition
    (x y z w : PTree) :=
  OuterLeftContributionClasses x y z w ⊕
    LeftInnerContributionClasses x y z w

/-- Total swapped-right contribution classes split into outer and inner sectors. -/
def RightContributionClassDecomposition
    (x y z w : PTree) :=
  SwappedRightOuterContributionClasses x y z w ⊕
    SwappedRightInnerContributionClasses x y z w

/-- Repackage a total left contribution class into its outer/inner sector. -/
noncomputable def leftContributionClass_decompose
    (x y z w : PTree) :
    LeftContributionClasses x y z w →
      LeftContributionClassDecomposition x y z w
  | ⟨q, hq⟩ =>
      if hout : HasLeftOuterContributionClass x y z w q then
        Sum.inl ⟨q, hout⟩
      else
        Sum.inr ⟨q, by
          rcases hq with hout' | hinn
          · exact False.elim (hout hout')
          · exact hinn⟩

/-- Reassemble a total left contribution class from its outer/inner sector. -/
def leftContributionClass_reassemble
    (x y z w : PTree) :
    LeftContributionClassDecomposition x y z w →
      LeftContributionClasses x y z w
  | Sum.inl s => ⟨s.1, Or.inl s.2⟩
  | Sum.inr s => ⟨s.1, Or.inr s.2⟩

/-- Repackage a total swapped-right contribution class into its outer/inner sector. -/
noncomputable def rightContributionClass_decompose
    (x y z w : PTree) :
    RightContributionClasses x y z w →
      RightContributionClassDecomposition x y z w
  | ⟨q', hq'⟩ =>
      if hout : HasSwappedRightOuterContributionClass x y z w q' then
        Sum.inl ⟨q', hout⟩
      else
        Sum.inr ⟨q', by
          rcases hq' with hout' | hinn
          · exact False.elim (hout hout')
          · exact hinn⟩

/-- Reassemble a total swapped-right contribution class from its outer/inner sector. -/
def rightContributionClass_reassemble
    (x y z w : PTree) :
    RightContributionClassDecomposition x y z w →
      RightContributionClasses x y z w
  | Sum.inl t => ⟨t.1, Or.inl t.2⟩
  | Sum.inr t => ⟨t.1, Or.inr t.2⟩

/--
Every total left contribution class admits an outer/inner decomposition.

This is not asserted to be unique: the same quotient class might, in principle,
support both kinds of data. The point here is to expose the two sectors cleanly.
-/
theorem leftContributionClass_outer_or_inner
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w) :
    HasOuterSupportLeftContributionClass x y z w s
    ∨
    HasLeftInnerContributionClass x y z w s.1 := by
  simpa [HasOuterSupportLeftContributionClass] using s.2

/--
Every total swapped-right contribution class admits an outer/inner
decomposition.

Again, this is a structural case split rather than a disjointness statement.
-/
theorem rightContributionClass_outer_or_inner
    (x y z w : PTree)
    (t : RightContributionClasses x y z w) :
    HasSwappedRightOuterContributionClass x y z w t.1
    ∨
    HasSwappedRightInnerContributionClass x y z w t.1 := by
  exact t.2

/-- The outer branch of total contribution classes is handled by strict canonical commutation. -/
noncomputable def outer_branch_solved_by_outerContributionCommute
    (x y z w : PTree) :
    OuterLeftContributionClasses x y z w ≃
      SwappedRightOuterContributionClasses x y z w :=
  outerContributionCommute x y z w

/-- The inner branch of total contribution classes is the genuinely contextual sector. -/
theorem inner_branch_is_contextual_sector
    (x y z w : PTree) :
    (∀ s : LeftInnerContributionClasses x y z w,
      ∃ t : SwappedRightInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1)
    ∧
    (∀ t : SwappedRightInnerContributionClasses x y z w,
      ∃ s : LeftInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1) := by
  exact innerSupportingClasses_correspond x y z w

/--
Global pre-Lie comparison strategy:

- total contribution classes split into outer and inner sectors;
- the outer sector is handled by strict canonical commutation;
- the inner sector is handled by the older swapped/fibre correspondence.
-/
theorem preLie_comparison_strategy
    (x y z w : PTree) :
    (∀ s : LeftContributionClasses x y z w,
      HasOuterSupportLeftContributionClass x y z w s
      ∨
      HasLeftInnerContributionClass x y z w s.1)
    ∧
    (∀ t : RightContributionClasses x y z w,
      HasSwappedRightOuterContributionClass x y z w t.1
      ∨
      HasSwappedRightInnerContributionClass x y z w t.1)
    ∧
    Nonempty
      (OuterLeftContributionClasses x y z w ≃
        SwappedRightOuterContributionClasses x y z w)
    ∧
    ((∀ s : LeftInnerContributionClasses x y z w,
      ∃ t : SwappedRightInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1)
    ∧
    (∀ t : SwappedRightInnerContributionClasses x y z w,
      ∃ s : LeftInnerContributionClasses x y z w,
        SwappedTwoStepClass x y z w s.1 t.1)) := by
  refine ⟨leftContributionClass_outer_or_inner x y z w, ?_⟩
  refine ⟨rightContributionClass_outer_or_inner x y z w, ?_⟩
  refine ⟨⟨outer_branch_solved_by_outerContributionCommute x y z w⟩, ?_⟩
  exact inner_branch_is_contextual_sector x y z w

/-!
## Outer sector counting collapse

The outer fragment is now rigid enough to contribute a clean degree-1 term to
the pre-Lie comparison: an outer-supported endpoint determines a unique outer
partner on the swapped side.
-/

/-- Outer incidences viewed from their left endpoints. -/
def OuterIncidencesOverLeft
    (x y z w : PTree) :=
  Σ s : OuterLeftContributionClasses x y z w,
    OuterRightContributionFiber x y z w s

/-- Outer incidences viewed from their swapped-right endpoints. -/
def OuterIncidencesOverRight
    (x y z w : PTree) :=
  Σ t : SwappedRightOuterContributionClasses x y z w,
    OuterLeftContributionFiber x y z w t

/--
Because the outer right-partner fibre over a fixed outer-supported left class is
degree 1, the sigma of outer incidences over left endpoints collapses to its
endpoint type.
-/
noncomputable def outerIncidencesOverLeft_equiv_endpoints
    (x y z w : PTree) :
    OuterIncidencesOverLeft x y z w ≃
      OuterLeftContributionClasses x y z w where
  toFun := fun p => p.1
  invFun := fun s => ⟨s, canonicalOuterRightContributionFiberPoint x y z w s⟩
  left_inv := by
    intro p
    rcases p with ⟨s, u⟩
    have hu :
        u = canonicalOuterRightContributionFiberPoint x y z w s :=
      (OuterRightContributionFiber_subsingleton x y z w s).elim u
        (canonicalOuterRightContributionFiberPoint x y z w s)
    cases hu
    rfl
  right_inv := by
    intro s
    rfl

/--
Because the outer left-partner fibre over a fixed swapped right-outer class is
degree 1, the sigma of outer incidences over right endpoints collapses to its
endpoint type.
-/
noncomputable def outerIncidencesOverRight_equiv_endpoints
    (x y z w : PTree) :
    OuterIncidencesOverRight x y z w ≃
      SwappedRightOuterContributionClasses x y z w where
  toFun := fun p => p.1
  invFun := fun t => ⟨t, canonicalOuterLeftContributionFiberPoint x y z w t⟩
  left_inv := by
    intro p
    rcases p with ⟨t, s⟩
    have hs :
        s = canonicalOuterLeftContributionFiberPoint x y z w t :=
      (OuterLeftContributionFiber_subsingleton x y z w t).elim s
        (canonicalOuterLeftContributionFiberPoint x y z w t)
    cases hs
    rfl
  right_inv := by
    intro t
    rfl

/-- Cardinal of outer incidences when grouped by left endpoints. -/
noncomputable def outerLeftIncidenceCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (OuterIncidencesOverLeft x y z w))

/-- Cardinal of outer incidences when grouped by swapped-right endpoints. -/
noncomputable def outerRightIncidenceCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (OuterIncidencesOverRight x y z w))

/-- The outer-left incidence cardinal is just the cardinal of outer-supported left classes. -/
theorem outerLeftIncidenceCard_eq_outerLeftClasses
    (x y z w : PTree) :
    outerLeftIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) := by
  unfold outerLeftIncidenceCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (outerIncidencesOverLeft_equiv_endpoints x y z w))

/-- The outer-right incidence cardinal is just the cardinal of swapped right-outer classes. -/
theorem outerRightIncidenceCard_eq_outerRightClasses
    (x y z w : PTree) :
    outerRightIncidenceCard x y z w =
      Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) := by
  unfold outerRightIncidenceCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (outerIncidencesOverRight_equiv_endpoints x y z w))

/--
The outer sectors contribute equally on the left and right: the outer incidence
cardinal is the same when grouped from either side.
-/
theorem outerLeftIncidenceCard_eq_outerRightIncidenceCard
    (x y z w : PTree) :
    outerLeftIncidenceCard x y z w = outerRightIncidenceCard x y z w := by
  calc
    outerLeftIncidenceCard x y z w
      = Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) := by
          exact outerLeftIncidenceCard_eq_outerLeftClasses x y z w
    _ = Cardinal.lift
          (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) := by
          exact congrArg Cardinal.lift
            (Cardinal.mk_congr (outerContributionCommute x y z w))
    _ = outerRightIncidenceCard x y z w := by
          symm
          exact outerRightIncidenceCard_eq_outerRightClasses x y z w

/--
Counting form of the solved outer branch: once the associator is restricted to
independent/outer contributions, the two sides are canonically equal.
-/
theorem outer_branch_contributes_equally
    (x y z w : PTree) :
    outerLeftIncidenceCard x y z w = outerRightIncidenceCard x y z w := by
  exact outerLeftIncidenceCard_eq_outerRightIncidenceCard x y z w

/-!
## Inner sector transport and counting

Unlike the outer sector, the inner branch is genuinely contextual.  But the
earlier fibre machinery already gives a class-level correspondence across the
swapped quotient, and therefore an equality of the inner contribution counts.
-/

/--
The explicit inner witness transport respects equality of left quotient
classes.
-/
theorem leftInnerWitnessToSwappedRight_respects_class
    (x y z w : PTree)
    (h₁ h₂ : LeftInnerWitnessData x y z w)
    (hh : leftInnerWitnessClass x y z w h₁ = leftInnerWitnessClass x y z w h₂) :
    swappedRightInnerWitnessClass x y z w
      (leftInnerWitness_to_swappedRightInnerWitness x y z w h₁) =
    swappedRightInnerWitnessClass x y z w
      (leftInnerWitness_to_swappedRightInnerWitness x y z w h₂) := by
  cases h₁ with
  | mk hw₁ hinner₁ =>
      cases hw₁ with
      | inner a₁ b₁ y₁ hay₁ hbw₁ =>
          cases h₂ with
          | mk hw₂ hinner₂ =>
              cases hw₂ with
              | inner a₂ b₂ y₂ hay₂ hbw₂ =>
                  have hcode :
                      codeClass (TwoStepCode.leftInner a₁ b₁ y₁ hay₁ hbw₁) =
                        codeClass (TwoStepCode.leftInner a₂ b₂ y₂ hay₂ hbw₂) := by
                    simpa [leftInnerWitnessClass, classOfLeftWitness, codeOfLeftWitness]
                      using hh
                  simpa [leftInnerWitness_to_swappedRightInnerWitness,
                    swappedRightInnerWitnessClass, swapTwoStepCode,
                    classOfRightWitness, codeOfRightWitness]
                    using
                      (swapTwoStepCode_respects_class x y z w
                        (c := TwoStepCode.leftInner a₁ b₁ y₁ hay₁ hbw₁)
                        (d := TwoStepCode.leftInner a₂ b₂ y₂ hay₂ hbw₂)
                        hcode)
              | outer =>
                  cases hinner₂
      | outer =>
          cases hinner₁

/--
The inverse explicit inner witness transport respects equality of swapped-right
quotient classes.
-/
theorem swappedRightInnerWitnessToLeft_respects_class
    (x y z w : PTree)
    (h₁ h₂ : SwappedRightInnerWitnessData x y z w)
    (hh : swappedRightInnerWitnessClass x y z w h₁ =
      swappedRightInnerWitnessClass x y z w h₂) :
    leftInnerWitnessClass x y z w
      (swappedRightInnerWitness_to_leftInnerWitness x y z w h₁) =
    leftInnerWitnessClass x y z w
      (swappedRightInnerWitness_to_leftInnerWitness x y z w h₂) := by
  cases h₁ with
  | mk hw₁ hinner₁ =>
      cases hw₁ with
      | inner a₁ b₁ y₁ hay₁ hbw₁ =>
          cases h₂ with
          | mk hw₂ hinner₂ =>
              cases hw₂ with
              | inner a₂ b₂ y₂ hay₂ hbw₂ =>
                  have hcode :
                      codeClass (TwoStepCode.rightInner a₁ b₁ y₁ hay₁ hbw₁) =
                        codeClass (TwoStepCode.rightInner a₂ b₂ y₂ hay₂ hbw₂) := by
                    simpa [swappedRightInnerWitnessClass, classOfRightWitness,
                      codeOfRightWitness] using hh
                  simpa [swappedRightInnerWitness_to_leftInnerWitness,
                    leftInnerWitnessClass, swapTwoStepCode,
                    classOfLeftWitness, codeOfLeftWitness]
                    using
                      (swapTwoStepCode_respects_class y x z w
                        (c := TwoStepCode.rightInner a₁ b₁ y₁ hay₁ hbw₁)
                        (d := TwoStepCode.rightInner a₂ b₂ y₂ hay₂ hbw₂)
                        hcode)
              | outer =>
                  cases hinner₂
      | outer =>
          cases hinner₁

/--
The class-level forward inner transport is determined by any chosen witness in
the supporting left inner fibre.
-/
theorem transportLeftInnerContributionClassToSwapped_eq_of_witness
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (h : LeftInnerFiberData x y z w q) :
    transportLeftInnerContributionClassToSwapped x y z w ⟨q, ⟨h⟩⟩ =
      ⟨(leftInnerFiberData_forward x y z w q h).1,
        ⟨(leftInnerFiberData_forward x y z w q h).2⟩⟩ := by
  apply Subtype.ext
  let h' : LeftInnerFiberData x y z w q :=
    Classical.choice (show Nonempty (LeftInnerFiberData x y z w q) from ⟨h⟩)
  have hh' : leftInnerWitnessClass x y z w h'.1 = q := h'.2
  have hh : leftInnerWitnessClass x y z w h'.1 =
      leftInnerWitnessClass x y z w h.1 := by
    exact hh'.trans h.2.symm
  simpa [transportLeftInnerContributionClassToSwapped,
    LeftInnerContributionClasses.toTotal,
    AllLeftInnerFiberData.toContributionClass,
    AllLeftInnerFiberData.toSwapped,
    allLeftInnerFiberData_forward,
    leftInnerFiberData_forward, h']
    using
      (leftInnerWitnessToSwappedRight_respects_class x y z w h'.1 h.1 hh)

/--
The class-level backward inner transport is determined by any chosen witness in
the supporting swapped-right inner fibre.
-/
theorem transportSwappedInnerContributionClassToLeft_eq_of_witness
    (x y z w : PTree)
    {q' : TwoStepQuotient y x z w}
    (h : SwappedRightInnerFiberData x y z w q') :
    transportSwappedInnerContributionClassToLeft x y z w ⟨q', ⟨h⟩⟩ =
      ⟨(leftInnerFiberData_backward x y z w ⟨q', h⟩).1,
        ⟨(leftInnerFiberData_backward x y z w ⟨q', h⟩).2⟩⟩ := by
  apply Subtype.ext
  let h' : SwappedRightInnerFiberData x y z w q' :=
    Classical.choice (show Nonempty (SwappedRightInnerFiberData x y z w q') from ⟨h⟩)
  have hh' : swappedRightInnerWitnessClass x y z w h'.1 = q' := h'.2
  have hh : swappedRightInnerWitnessClass x y z w h'.1 =
      swappedRightInnerWitnessClass x y z w h.1 := by
    exact hh'.trans h.2.symm
  simpa [transportSwappedInnerContributionClassToLeft,
    SwappedRightInnerContributionClasses.toTotal,
    AllSwappedRightInnerFiberData.toContributionClass,
    AllSwappedRightInnerFiberData.toLeft,
    allLeftInnerFiberData_backward,
    leftInnerFiberData_backward, h']
    using
      (swappedRightInnerWitnessToLeft_respects_class x y z w h'.1 h.1 hh)

/-- The inner transport is inverse to the backward inner transport on left classes. -/
theorem transportSwappedInnerContributionClassToLeft_left_inv
    (x y z w : PTree)
    (s : LeftInnerContributionClasses x y z w) :
    transportSwappedInnerContributionClassToLeft x y z w
      (transportLeftInnerContributionClassToSwapped x y z w s) = s := by
  apply Subtype.ext
  rcases s with ⟨q, hq⟩
  let h : LeftInnerFiberData x y z w q := Classical.choice hq
  have hs : (⟨q, hq⟩ : LeftInnerContributionClasses x y z w) = ⟨q, ⟨h⟩⟩ := by
    apply Subtype.ext
    rfl
  let k := leftInnerFiberData_forward x y z w q h
  calc
    (transportSwappedInnerContributionClassToLeft x y z w
        (transportLeftInnerContributionClassToSwapped x y z w ⟨q, hq⟩)).1
      = (transportSwappedInnerContributionClassToLeft x y z w
          (transportLeftInnerContributionClassToSwapped x y z w ⟨q, ⟨h⟩⟩)).1 := by
            rw [hs]
    _ = (transportSwappedInnerContributionClassToLeft x y z w
          ⟨k.1, ⟨k.2⟩⟩).1 := by
            exact congrArg
              (fun u => (transportSwappedInnerContributionClassToLeft x y z w u).1)
              (transportLeftInnerContributionClassToSwapped_eq_of_witness x y z w h)
    _ = (leftInnerFiberData_backward x y z w ⟨k.1, k.2⟩).1 := by
          exact congrArg Subtype.val
            (transportSwappedInnerContributionClassToLeft_eq_of_witness x y z w k.2)
    _ = q := by
          simpa [k, AllLeftInnerFiberData.toSwapped,
            AllSwappedRightInnerFiberData.toLeft]
            using (AllLeftInnerFiberData.toSwapped_toLeft_fst x y z w ⟨q, h⟩)

/-- The backward inner transport is inverse to the forward inner transport on swapped classes. -/
theorem transportLeftInnerContributionClassToSwapped_right_inv
    (x y z w : PTree)
    (t : SwappedRightInnerContributionClasses x y z w) :
    transportLeftInnerContributionClassToSwapped x y z w
      (transportSwappedInnerContributionClassToLeft x y z w t) = t := by
  apply Subtype.ext
  rcases t with ⟨q', hq'⟩
  let h : SwappedRightInnerFiberData x y z w q' := Classical.choice hq'
  have ht : (⟨q', hq'⟩ : SwappedRightInnerContributionClasses x y z w) = ⟨q', ⟨h⟩⟩ := by
    apply Subtype.ext
    rfl
  let k := leftInnerFiberData_backward x y z w ⟨q', h⟩
  calc
    (transportLeftInnerContributionClassToSwapped x y z w
        (transportSwappedInnerContributionClassToLeft x y z w ⟨q', hq'⟩)).1
      = (transportLeftInnerContributionClassToSwapped x y z w
          (transportSwappedInnerContributionClassToLeft x y z w ⟨q', ⟨h⟩⟩)).1 := by
            rw [ht]
    _ = (transportLeftInnerContributionClassToSwapped x y z w
          ⟨k.1, ⟨k.2⟩⟩).1 := by
            exact congrArg
              (fun s => (transportLeftInnerContributionClassToSwapped x y z w s).1)
              (transportSwappedInnerContributionClassToLeft_eq_of_witness x y z w h)
    _ = (AllLeftInnerFiberData.toSwapped x y z w ⟨k.1, k.2⟩).1 := by
          exact congrArg Subtype.val
            (transportLeftInnerContributionClassToSwapped_eq_of_witness x y z w k.2)
    _ = q' := by
          simpa [k, AllLeftInnerFiberData.toSwapped,
            AllSwappedRightInnerFiberData.toLeft]
            using (AllSwappedRightInnerFiberData.toLeft_toSwapped_fst x y z w ⟨q', h⟩)

/-- Inner-supported classes correspond across the swapped quotient. -/
noncomputable def innerContributionCommute
    (x y z w : PTree) :
    LeftInnerContributionClasses x y z w ≃
      SwappedRightInnerContributionClasses x y z w where
  toFun := transportLeftInnerContributionClassToSwapped x y z w
  invFun := transportSwappedInnerContributionClassToLeft x y z w
  left_inv := transportSwappedInnerContributionClassToLeft_left_inv x y z w
  right_inv := transportLeftInnerContributionClassToSwapped_right_inv x y z w

/-- Cardinal of the left inner contribution sector. -/
noncomputable def innerLeftContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (LeftInnerContributionClasses x y z w))

/-- Cardinal of the swapped-right inner contribution sector. -/
noncomputable def innerRightContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (SwappedRightInnerContributionClasses x y z w))

/-- The inner contribution sectors have the same cardinality across the swapped transport. -/
theorem innerLeftContributionCard_eq_innerRightContributionCard
    (x y z w : PTree) :
    innerLeftContributionCard x y z w = innerRightContributionCard x y z w := by
  unfold innerLeftContributionCard innerRightContributionCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr (innerContributionCommute x y z w))

/--
Counting form of the inner branch: once the outer sector is removed, the
remaining nested contribution classes are matched by the swapped inner
transport.
-/
theorem inner_branch_contributes_equally
    (x y z w : PTree) :
    innerLeftContributionCard x y z w = innerRightContributionCard x y z w := by
  exact innerLeftContributionCard_eq_innerRightContributionCard x y z w

/-!
## Global counting decomposition

At the level of total contribution classes, outer and inner support need not be
disjoint a priori.  So the honest global counting split is: total classes
decompose into the outer-supported sector and the residual non-outer sector.

If one later establishes a no-overlap theorem saying outer and inner support
cannot both occur at the same quotient class, then the residual sector is
equivalent to the inner sector and the full total cardinal equality follows by
combining the outer and inner equalities proved above.
-/

/-- Total left contribution cardinal. -/
noncomputable def totalLeftContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (LeftContributionClasses x y z w))

/-- Total swapped-right contribution cardinal. -/
noncomputable def totalRightContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (RightContributionClasses x y z w))

/-- Left total classes which are not outer-supported. -/
def LeftResidualContributionClasses
    (x y z w : PTree) :=
  { s : LeftContributionClasses x y z w //
      ¬ HasOuterSupportLeftContributionClass x y z w s }

/-- Swapped-right total classes which are not outer-supported. -/
def RightResidualContributionClasses
    (x y z w : PTree) :=
  { t : RightContributionClasses x y z w //
      ¬ HasSwappedRightOuterContributionClass x y z w t.1 }

/-- Cardinal of the residual non-outer left sector. -/
noncomputable def leftResidualContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (LeftResidualContributionClasses x y z w))

/-- Cardinal of the residual non-outer swapped-right sector. -/
noncomputable def rightResidualContributionCard
    (x y z w : PTree) : Cardinal :=
  Cardinal.lift (Cardinal.mk (RightResidualContributionClasses x y z w))

/-- A residual left contribution class is necessarily inner-supported. -/
theorem LeftResidualContributionClasses.has_inner_support
    (x y z w : PTree)
    (s : LeftResidualContributionClasses x y z w) :
    HasLeftInnerContributionClass x y z w s.1.1 := by
  rcases s with ⟨⟨q, hq⟩, hs⟩
  rcases hq with houter | hinner
  · exact False.elim (hs houter)
  · exact hinner

/-- A residual swapped-right contribution class is necessarily inner-supported. -/
theorem RightResidualContributionClasses.has_inner_support
    (x y z w : PTree)
    (t : RightResidualContributionClasses x y z w) :
    HasSwappedRightInnerContributionClass x y z w t.1.1 := by
  rcases t with ⟨⟨q', hq'⟩, ht⟩
  rcases hq' with houter | hinner
  · exact False.elim (ht houter)
  · exact hinner

/-- Total left contribution classes split into outer-supported and residual sectors. -/
noncomputable def leftContributionClasses_outerPlusResidual
    (x y z w : PTree) :
    LeftContributionClasses x y z w ≃
      OuterLeftContributionClasses x y z w ⊕
        LeftResidualContributionClasses x y z w where
  toFun := fun s =>
    if hs : HasOuterSupportLeftContributionClass x y z w s then
      Sum.inl ⟨s.1, hs⟩
    else
      Sum.inr ⟨s, hs⟩
  invFun := fun u =>
    Sum.elim
      (fun s => ⟨s.1, Or.inl s.2⟩)
      (fun s => s.1)
      u
  left_inv := by
    intro s
    by_cases hs : HasOuterSupportLeftContributionClass x y z w s
    · simp [hs]
    · simp [hs]
  right_inv := by
    intro u
    cases u with
    | inl s =>
        have hs : HasOuterSupportLeftContributionClass x y z w ⟨s.1, Or.inl s.2⟩ := s.2
        simp [hs]
    | inr s =>
        simp [s.2]

/-- Total swapped-right contribution classes split into outer-supported and residual sectors. -/
noncomputable def rightContributionClasses_outerPlusResidual
    (x y z w : PTree) :
    RightContributionClasses x y z w ≃
      SwappedRightOuterContributionClasses x y z w ⊕
        RightResidualContributionClasses x y z w where
  toFun := fun t =>
    if ht : HasSwappedRightOuterContributionClass x y z w t.1 then
      Sum.inl ⟨t.1, ht⟩
    else
      Sum.inr ⟨t, ht⟩
  invFun := fun u =>
    Sum.elim
      (fun t => ⟨t.1, Or.inl t.2⟩)
      (fun t => t.1)
      u
  left_inv := by
    intro t
    by_cases ht : HasSwappedRightOuterContributionClass x y z w t.1
    · simp [ht]
    · simp [ht]
  right_inv := by
    intro u
    cases u with
    | inl t =>
        have ht : HasSwappedRightOuterContributionClass x y z w t.1 := t.2
        simp [ht]
    | inr t =>
        simp [t.2]

/-- Counting decomposition of total left contribution classes. -/
theorem totalLeftContributionCard_eq_outer_plus_residual
    (x y z w : PTree) :
    totalLeftContributionCard x y z w =
      Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) +
      leftResidualContributionCard x y z w := by
  unfold totalLeftContributionCard leftResidualContributionCard
  calc
    Cardinal.lift (Cardinal.mk (LeftContributionClasses x y z w))
      = Cardinal.lift
          (Cardinal.mk
            (OuterLeftContributionClasses x y z w ⊕
              LeftResidualContributionClasses x y z w)) := by
          exact congrArg Cardinal.lift
            (Cardinal.mk_congr
              (leftContributionClasses_outerPlusResidual x y z w))
    _ = Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) +
          Cardinal.lift (Cardinal.mk (LeftResidualContributionClasses x y z w)) := by
          rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift,
            Cardinal.lift_lift]

/-- Counting decomposition of total swapped-right contribution classes. -/
theorem totalRightContributionCard_eq_outer_plus_residual
    (x y z w : PTree) :
    totalRightContributionCard x y z w =
      Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) +
      rightResidualContributionCard x y z w := by
  unfold totalRightContributionCard rightResidualContributionCard
  calc
    Cardinal.lift (Cardinal.mk (RightContributionClasses x y z w))
      = Cardinal.lift
          (Cardinal.mk
            (SwappedRightOuterContributionClasses x y z w ⊕
              RightResidualContributionClasses x y z w)) := by
          exact congrArg Cardinal.lift
            (Cardinal.mk_congr
              (rightContributionClasses_outerPlusResidual x y z w))
    _ = Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) +
          Cardinal.lift (Cardinal.mk (RightResidualContributionClasses x y z w)) := by
          rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift,
            Cardinal.lift_lift]

/--
Hypothesis schema asserting that no left quotient class carries both outer and
inner support.
-/
def NoLeftOuterInnerOverlap
    (x y z w : PTree) : Prop :=
  ∀ q : TwoStepQuotient x y z w,
    ¬ (HasLeftOuterContributionClass x y z w q ∧
      HasLeftInnerContributionClass x y z w q)

/--
Hypothesis schema asserting that no swapped-right quotient class carries both
outer and inner support.
-/
def NoRightOuterInnerOverlap
    (x y z w : PTree) : Prop :=
  ∀ q' : TwoStepQuotient y x z w,
    ¬ (HasSwappedRightOuterContributionClass x y z w q' ∧
      HasSwappedRightInnerContributionClass x y z w q')

/--
Under a no-overlap hypothesis, the residual left sector is exactly the inner
left sector.
-/
noncomputable def leftResidualContributionClasses_equiv_inner
    (x y z w : PTree)
    (hdisj : NoLeftOuterInnerOverlap x y z w) :
    LeftResidualContributionClasses x y z w ≃
      LeftInnerContributionClasses x y z w where
  toFun := fun s =>
    ⟨s.1.1, LeftResidualContributionClasses.has_inner_support x y z w s⟩
  invFun := fun s =>
    ⟨⟨s.1, Or.inr s.2⟩, by
      intro houter
      exact hdisj s.1 ⟨houter, s.2⟩⟩
  left_inv := by
    intro s
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

/--
Under a no-overlap hypothesis, the residual swapped-right sector is exactly the
inner swapped-right sector.
-/
noncomputable def rightResidualContributionClasses_equiv_inner
    (x y z w : PTree)
    (hdisj : NoRightOuterInnerOverlap x y z w) :
    RightResidualContributionClasses x y z w ≃
      SwappedRightInnerContributionClasses x y z w where
  toFun := fun t =>
    ⟨t.1.1, RightResidualContributionClasses.has_inner_support x y z w t⟩
  invFun := fun t =>
    ⟨⟨t.1, Or.inr t.2⟩, by
      intro houter
      exact hdisj t.1 ⟨houter, t.2⟩⟩
  left_inv := by
    intro t
    apply Subtype.ext
    rfl
  right_inv := by
    intro t
    apply Subtype.ext
    rfl

/-- Under no overlap, the residual left-sector cardinal is the inner left-sector cardinal. -/
theorem leftResidualContributionCard_eq_inner_of_no_overlap
    (x y z w : PTree)
    (hdisj : NoLeftOuterInnerOverlap x y z w) :
    leftResidualContributionCard x y z w = innerLeftContributionCard x y z w := by
  unfold leftResidualContributionCard innerLeftContributionCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr
      (leftResidualContributionClasses_equiv_inner x y z w hdisj))

/-- Under no overlap, the residual swapped-right-sector cardinal is the inner swapped-right-sector cardinal. -/
theorem rightResidualContributionCard_eq_inner_of_no_overlap
    (x y z w : PTree)
    (hdisj : NoRightOuterInnerOverlap x y z w) :
    rightResidualContributionCard x y z w = innerRightContributionCard x y z w := by
  unfold rightResidualContributionCard innerRightContributionCard
  exact congrArg Cardinal.lift
    (Cardinal.mk_congr
      (rightResidualContributionClasses_equiv_inner x y z w hdisj))

/--
Conditional global counting equality: once outer/inner overlap is excluded on
both sides, the total contribution cardinal is the sum of the solved outer and
inner sectors.
-/
theorem totalContributionCard_eq_of_no_overlap
    (x y z w : PTree)
    (hleft : NoLeftOuterInnerOverlap x y z w)
    (hright : NoRightOuterInnerOverlap x y z w) :
    totalLeftContributionCard x y z w = totalRightContributionCard x y z w := by
  have houter :
      Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) =
        Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) := by
    exact congrArg Cardinal.lift
      (Cardinal.mk_congr (outerContributionCommute x y z w))
  calc
    totalLeftContributionCard x y z w
      = Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) +
          leftResidualContributionCard x y z w := by
            exact totalLeftContributionCard_eq_outer_plus_residual x y z w
    _ = Cardinal.lift (Cardinal.mk (OuterLeftContributionClasses x y z w)) +
          innerLeftContributionCard x y z w := by
            rw [leftResidualContributionCard_eq_inner_of_no_overlap x y z w hleft]
    _ = Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) +
          innerRightContributionCard x y z w := by
            rw [houter, innerLeftContributionCard_eq_innerRightContributionCard x y z w]
    _ = Cardinal.lift (Cardinal.mk (SwappedRightOuterContributionClasses x y z w)) +
          rightResidualContributionCard x y z w := by
            rw [rightResidualContributionCard_eq_inner_of_no_overlap x y z w hright]
    _ = totalRightContributionCard x y z w := by
          symm
          exact totalRightContributionCard_eq_outer_plus_residual x y z w

/-!
## Proof-theoretic no-overlap criteria

The remaining question is whether a quotient class can simultaneously encode an
independent/outer compositional event and a nested/inner one.  The cleanest
sufficient criterion is that raw outer witness classes and raw inner witness
classes are disjoint.

An even stronger sufficient criterion is syntactic: there is no
`TwoStepEquiv`-chain connecting an outer raw code to an inner raw code on the
same side.  Either form is enough to discharge the overlap hypotheses used in
the global counting theorem above.
-/

/-- Raw outer-left and inner-left witness classes never coincide. -/
def LeftOuterInnerClassDisjoint
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterLeftWitness x y z w,
    ∀ hIn : LeftInnerWitnessData x y z w,
      outerLeftWitnessClass hOut ≠ leftInnerWitnessClass x y z w hIn

/-- Raw swapped-right outer and swapped-right inner witness classes never coincide. -/
def SwappedRightOuterInnerClassDisjoint
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterRightWitness y x z w,
    ∀ hIn : SwappedRightInnerWitnessData x y z w,
      outerRightWitnessClass hOut ≠ swappedRightInnerWitnessClass x y z w hIn

/--
Stronger code-level criterion: no left-outer raw code is `TwoStepEquiv` to a
left-inner raw code.
-/
def NoLeftOuterInnerCodeEquiv
    (x y z w : PTree) : Prop :=
  ∀ a b : Address, ∀ z' : PTree,
    ∀ haz : (a, z') ∈ matchingLeafGraftWitnesses y z,
    ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses x z',
    ∀ a' b' : Address, ∀ y' : PTree,
    ∀ hay : (a', y') ∈ matchingLeafGraftWitnesses y x,
    ∀ hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z,
      ¬ TwoStepEquiv x y z w
          (TwoStepCode.leftOuter a b z' haz hbw)
          (TwoStepCode.leftInner a' b' y' hay hbw')

/--
Stronger code-level criterion on the swapped-right side: no swapped-right outer
raw code is `TwoStepEquiv` to a swapped-right inner raw code.
-/
def NoSwappedRightOuterInnerCodeEquiv
    (x y z w : PTree) : Prop :=
  ∀ a b : Address, ∀ z' : PTree,
    ∀ haz : (a, z') ∈ matchingLeafGraftWitnesses y z,
    ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses x z',
    ∀ a' b' : Address, ∀ y' : PTree,
    ∀ hay : (a', y') ∈ matchingLeafGraftWitnesses y x,
    ∀ hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z,
      ¬ TwoStepEquiv y x z w
          (TwoStepCode.rightOuter a b z' haz hbw)
          (TwoStepCode.rightInner a' b' y' hay hbw')

/--
Code-level impossibility of outer-to-inner equivalence on the left implies
class-level disjointness of outer and inner witnesses.
-/
theorem leftOuterInnerClassDisjoint_of_noCodeEquiv
    (x y z w : PTree)
    (hNo : NoLeftOuterInnerCodeEquiv x y z w) :
    LeftOuterInnerClassDisjoint x y z w := by
  intro hOut hIn hEq
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              have hclass :
                  codeClass (TwoStepCode.leftOuter a b z' haz hbw) =
                    codeClass (TwoStepCode.leftInner a' b' y' hay hbw') := by
                simpa [outerLeftWitnessClass, leftInnerWitnessClass,
                  classOfLeftWitness, codeOfLeftWitness] using hEq
              exact hNo a b z' haz hbw a' b' y' hay hbw' (Quotient.exact hclass)
          | outer =>
              cases hh

/--
Code-level impossibility of outer-to-inner equivalence on the swapped-right
side implies class-level disjointness there.
-/
theorem swappedRightOuterInnerClassDisjoint_of_noCodeEquiv
    (x y z w : PTree)
    (hNo : NoSwappedRightOuterInnerCodeEquiv x y z w) :
    SwappedRightOuterInnerClassDisjoint x y z w := by
  intro hOut hIn hEq
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              have hclass :
                  codeClass (TwoStepCode.rightOuter a b z' haz hbw) =
                    codeClass (TwoStepCode.rightInner a' b' y' hay hbw') := by
                simpa [outerRightWitnessClass, swappedRightInnerWitnessClass,
                  classOfRightWitness, codeOfRightWitness] using hEq
              exact hNo a b z' haz hbw a' b' y' hay hbw' (Quotient.exact hclass)
          | outer =>
              cases hh

/--
Class-level disjointness of outer and inner left witnesses forces the left
no-overlap hypothesis.
-/
theorem noLeftOuterInnerOverlap_of_classDisjoint
    (x y z w : PTree)
    (hDisj : LeftOuterInnerClassDisjoint x y z w) :
    NoLeftOuterInnerOverlap x y z w := by
  intro q hBoth
  rcases hBoth with ⟨hOuter, hInner⟩
  rcases hOuter with ⟨hOut, hhOut⟩
  rcases hInner with ⟨hIn⟩
  exact hDisj hOut hIn.1 (hhOut.trans hIn.2.symm)

/--
Class-level disjointness of swapped-right outer and inner witnesses forces the
right no-overlap hypothesis.
-/
theorem noRightOuterInnerOverlap_of_classDisjoint
    (x y z w : PTree)
    (hDisj : SwappedRightOuterInnerClassDisjoint x y z w) :
    NoRightOuterInnerOverlap x y z w := by
  intro q' hBoth
  rcases hBoth with ⟨hOuter, hInner⟩
  rcases hOuter with ⟨hOut, hhOut⟩
  rcases hInner with ⟨hIn⟩
  exact hDisj hOut hIn.1 (hhOut.trans hIn.2.symm)

/--
If outer and inner witness classes are disjoint on both sides, then the global
total counting equality follows.
-/
theorem totalContributionCard_eq_of_classDisjoint
    (x y z w : PTree)
    (hleft : LeftOuterInnerClassDisjoint x y z w)
    (hright : SwappedRightOuterInnerClassDisjoint x y z w) :
    totalLeftContributionCard x y z w = totalRightContributionCard x y z w := by
  apply totalContributionCard_eq_of_no_overlap x y z w
  · exact noLeftOuterInnerOverlap_of_classDisjoint x y z w hleft
  · exact noRightOuterInnerOverlap_of_classDisjoint x y z w hright

/--
Code-level outer/inner separation is a sufficient proof-theoretic hypothesis
for the full total counting equality.
-/
theorem totalContributionCard_eq_of_noCodeEquiv
    (x y z w : PTree)
    (hleft : NoLeftOuterInnerCodeEquiv x y z w)
    (hright : NoSwappedRightOuterInnerCodeEquiv x y z w) :
    totalLeftContributionCard x y z w = totalRightContributionCard x y z w := by
  apply totalContributionCard_eq_of_classDisjoint x y z w
  · exact leftOuterInnerClassDisjoint_of_noCodeEquiv x y z w hleft
  · exact swappedRightOuterInnerClassDisjoint_of_noCodeEquiv x y z w hright

/-!
## Address-pattern layer

The raw `leftOuter`/`rightOuter` constructors are not themselves the invariant
outer fragment: they merely say the first graft happened on `z`. The true
independent-vs-nested distinction is carried by the address relation between the
first and second graft sites.

This section packages that as a small pattern classifier on raw codes. We do
not yet prove that `TwoStepEquiv` preserves this pattern globally; that would be
a strong disjointness theorem. But these lemmas isolate exactly the extra fact
still needed from the proof theory.
-/

/-- The dependency pattern of a raw two-step code. -/
inductive TwoStepPattern where
| independent
| dependent
deriving DecidableEq

/--
Classify a raw two-step code by address-pattern.

- `leftInner` and `rightInner` are definitionally nested/dependent;
- `leftOuter` and `rightOuter` are classified by address comparability.
-/
noncomputable def codePattern
    {x y z w : PTree} :
    TwoStepCode x y z w → TwoStepPattern
  | TwoStepCode.leftOuter a b _ _ _ =>
      if PTree.comparable a b then .dependent else .independent
  | TwoStepCode.rightOuter a b _ _ _ =>
      if PTree.comparable a b then .dependent else .independent
  | TwoStepCode.leftInner _ _ _ _ _ =>
      .dependent
  | TwoStepCode.rightInner _ _ _ _ _ =>
      .dependent

/-- Inner-presented left codes are always dependent. -/
@[simp] theorem codePattern_leftInner
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    codePattern (TwoStepCode.leftInner a b y' hay hbw) = TwoStepPattern.dependent := by
  rfl

/-- Inner-presented right codes are always dependent. -/
@[simp] theorem codePattern_rightInner
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    codePattern (TwoStepCode.rightInner a b y' hay hbw) = TwoStepPattern.dependent := by
  rfl

/-- An incomparable left-outer code is classified as independent. -/
@[simp] theorem codePattern_leftOuter_of_not_comparable
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (hcmp : ¬ PTree.comparable a b) :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) = TwoStepPattern.independent := by
  simp [codePattern, hcmp]

/-- A comparable left-outer code is classified as dependent. -/
@[simp] theorem codePattern_leftOuter_of_comparable
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (hcmp : PTree.comparable a b) :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) = TwoStepPattern.dependent := by
  simp [codePattern, hcmp]

/-- An incomparable right-outer code is classified as independent. -/
@[simp] theorem codePattern_rightOuter_of_not_comparable
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (hcmp : ¬ PTree.comparable a b) :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) = TwoStepPattern.independent := by
  simp [codePattern, hcmp]

/-- A comparable right-outer code is classified as dependent. -/
@[simp] theorem codePattern_rightOuter_of_comparable
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (hcmp : PTree.comparable a b) :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) = TwoStepPattern.dependent := by
  simp [codePattern, hcmp]

/--
For a successful left-outer code, being classified as dependent is equivalent
to the second address lying under the first.
-/
theorem codePattern_leftOuter_eq_dependent_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) = TwoStepPattern.dependent
      ↔ ∃ c, b = a ++ c := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hyz⟩
  rcases hbw with ⟨_, hxz'⟩
  constructor
  · intro hpat
    by_cases hcmp : PTree.comparable a b
    · exact
        (graftMatchingLeafAt_address_classification x y z a b z' w hyz hxz').resolve_right
          (by intro hn; exact hn hcmp)
    · simp [codePattern, hcmp] at hpat
  · intro hdep
    rcases hdep with ⟨c, hc⟩
    have hcmp : PTree.comparable a b := by
      apply PTree.comparable_of_isAncestorOf
      exact ⟨c, hc⟩
    simp [codePattern, hcmp]

/--
For a successful left-outer code, being classified as independent is
equivalent to incomparability of the two graft addresses.
-/
theorem codePattern_leftOuter_eq_independent_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) = TwoStepPattern.independent
      ↔ ¬ PTree.comparable a b := by
  by_cases hcmp : PTree.comparable a b
  · simp [codePattern, hcmp]
  · simp [codePattern, hcmp]

/--
For a successful right-outer code, being classified as dependent is equivalent
to the second address lying under the first.
-/
theorem codePattern_rightOuter_eq_dependent_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) = TwoStepPattern.dependent
      ↔ ∃ c, b = a ++ c := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hxz⟩
  rcases hbw with ⟨_, hyz'⟩
  constructor
  · intro hpat
    by_cases hcmp : PTree.comparable a b
    · exact
        (graftMatchingLeafAt_address_classification y x z a b z' w hxz hyz').resolve_right
          (by intro hn; exact hn hcmp)
    · simp [codePattern, hcmp] at hpat
  · intro hdep
    rcases hdep with ⟨c, hc⟩
    have hcmp : PTree.comparable a b := by
      apply PTree.comparable_of_isAncestorOf
      exact ⟨c, hc⟩
    simp [codePattern, hcmp]

/--
For a successful right-outer code, being classified as independent is
equivalent to incomparability of the two graft addresses.
-/
theorem codePattern_rightOuter_eq_independent_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) = TwoStepPattern.independent
      ↔ ¬ PTree.comparable a b := by
  by_cases hcmp : PTree.comparable a b
  · simp [codePattern, hcmp]
  · simp [codePattern, hcmp]

/-- A hypothesis saying `TwoStepEquiv` preserves the address-pattern classifier. -/
def CodePatternInvariant
    (x y z w : PTree) : Prop :=
  ∀ {c d : TwoStepCode x y z w},
    TwoStepEquiv x y z w c d →
    codePattern c = codePattern d

/--
If `TwoStepEquiv` preserves address-pattern, then an incomparable left-outer
code cannot be equivalent to a left-inner code.
-/
theorem noIndependentLeftOuterToLeftInnerEquiv_of_patternInvariant
    (x y z w : PTree)
    (hpat : CodePatternInvariant x y z w)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (hcmp : ¬ PTree.comparable a b)
    (a' b' : Address) (y' : PTree)
    (hay : (a', y') ∈ matchingLeafGraftWitnesses y x)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z) :
    ¬ TwoStepEquiv x y z w
        (TwoStepCode.leftOuter a b z' haz hbw)
        (TwoStepCode.leftInner a' b' y' hay hbw') := by
  intro hEq
  have hEqPat := hpat hEq
  simp [codePattern, hcmp] at hEqPat

/--
If `TwoStepEquiv` preserves address-pattern, then an incomparable swapped-right
outer code cannot be equivalent to a swapped-right inner code.
-/
theorem noIndependentRightOuterToRightInnerEquiv_of_patternInvariant
    (x y z w : PTree)
    (hpat : CodePatternInvariant y x z w)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (hcmp : ¬ PTree.comparable a b)
    (a' b' : Address) (y' : PTree)
    (hay : (a', y') ∈ matchingLeafGraftWitnesses y x)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z) :
    ¬ TwoStepEquiv y x z w
        (TwoStepCode.rightOuter a b z' haz hbw)
        (TwoStepCode.rightInner a' b' y' hay hbw') := by
  intro hEq
  have hEqPat := hpat hEq
  simp [codePattern, hcmp] at hEqPat

theorem comparable_symm {a b : Address}
    (h : PTree.comparable a b) :
    PTree.comparable b a := by
  cases h with
  | inl hab =>
      exact Or.inr hab
  | inr hba =>
      exact Or.inl hba

theorem not_comparable_symm {a b : Address}
    (h : ¬ PTree.comparable a b) :
    ¬ PTree.comparable b a := by
  intro h'
  exact h (comparable_symm h')

/--
The tree-level left-to-right transport generated from a left-outer witness can
always be chosen to preserve the dependency pattern.
-/
theorem leftOuter_has_pattern_preserving_rightCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ c : TwoStepCode x y z w,
      TwoStepEquiv x y z w
        (TwoStepCode.leftOuter a b z' haz hbw) c ∧
      codePattern (TwoStepCode.leftOuter a b z' haz hbw) = codePattern c := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hyz⟩
  rcases hbw with ⟨_, hxz'⟩
  have hdecomp := two_step_graft_decomposition_full x y z a b z' w hyz hxz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hxy, hy'z⟩
      have hay' : (c, y') ∈ matchingLeafGraftWitnesses x y := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxy⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x y c y' hxy
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            y (PTree.leaf x.conclusion) c
            ((PTree.IsGraftableLeafAt_iff x y c).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses y' z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hy'z⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z a w hy'z
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y'.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y' z a).mp hg)
      refine ⟨TwoStepCode.rightInner c a y' hay' hbw', ?_, ?_⟩
      · exact TwoStepEquiv.outer_comm_inner haz hbw hay' hbw' (by
          rw [mem_twoStepAddrWitnessesRight_iff]
          exact Or.inr ⟨y', hay', hbw'⟩)
      · have hcmp : PTree.comparable a b := by
          apply PTree.comparable_of_isAncestorOf
          exact ⟨c, hbEq⟩
        simp [codePattern, hcmp]
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hxz, hyz₃⟩
      have haz' : (b, z₃) ∈ matchingLeafGraftWitnesses x z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z b z₃ hxz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf x.conclusion) b
            ((PTree.IsGraftableLeafAt_iff x z b).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses y z₃ := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz₃⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z₃ a w hyz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf y.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y z₃ a).mp hg)
      refine ⟨TwoStepCode.rightOuter b a z₃ haz' hbw', ?_, ?_⟩
      · exact TwoStepEquiv.outer_comm_outer haz hbw haz' hbw' (by
          rw [mem_twoStepAddrWitnessesRight_iff]
          exact Or.inl ⟨z₃, haz', hbw'⟩)
      · have hnc' : ¬ PTree.comparable b a := not_comparable_symm hnc
        simp [codePattern, hnc, hnc']

/--
The tree-level right-to-left transport generated from a right-outer witness can
always be chosen to preserve the dependency pattern.
-/
theorem rightOuter_has_pattern_preserving_leftCode
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ c : TwoStepCode x y z w,
      TwoStepEquiv x y z w
        (TwoStepCode.rightOuter a b z' haz hbw) c ∧
      codePattern (TwoStepCode.rightOuter a b z' haz hbw) = codePattern c := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hxz⟩
  rcases hbw with ⟨_, hyz'⟩
  have hdecomp := two_step_graft_decomposition_full y x z a b z' w hxz hyz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hyx, hy'z⟩
      have hay' : (c, y') ∈ matchingLeafGraftWitnesses y x := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyx⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y x c y' hyx
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            x (PTree.leaf y.conclusion) c
            ((PTree.IsGraftableLeafAt_iff y x c).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses y' z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hy'z⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z a w hy'z
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y'.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y' z a).mp hg)
      refine ⟨TwoStepCode.leftInner c a y' hay' hbw', ?_, ?_⟩
      · exact TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
          rw [mem_twoStepAddrWitnessesLeft_iff]
          exact Or.inr ⟨y', hay', hbw'⟩)
      · have hcmp : PTree.comparable a b := by
          apply PTree.comparable_of_isAncestorOf
          exact ⟨c, hbEq⟩
        simp [codePattern, hcmp]
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hyz, hxz₃⟩
      have haz' : (b, z₃) ∈ matchingLeafGraftWitnesses y z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z b z₃ hyz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y.conclusion) b
            ((PTree.IsGraftableLeafAt_iff y z b).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses x z₃ := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz₃⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z₃ a w hxz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf x.conclusion) a
            ((PTree.IsGraftableLeafAt_iff x z₃ a).mp hg)
      refine ⟨TwoStepCode.leftOuter b a z₃ haz' hbw', ?_, ?_⟩
      · exact TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
          rw [mem_twoStepAddrWitnessesLeft_iff]
          exact Or.inl ⟨z₃, haz', hbw'⟩)
      · have hnc' : ¬ PTree.comparable b a := not_comparable_symm hnc
        simp [codePattern, hnc, hnc']

/-!
## Raw constructor targets versus canonical pattern-preserving transport

For each outer-presented source witness we now fix a canonical target code
chosen from the tree-generated, pattern-preserving transport above. Any raw
target appearing in a `TwoStepEquiv` constructor from that same source is then
equivalent to this canonical target.
-/

/-- Canonical right-side code attached to a left-outer source witness. -/
noncomputable def canonicalRightCodeOfLeftOuter
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    TwoStepCode x y z w :=
  Classical.choose (leftOuter_has_pattern_preserving_rightCode x y z w a b z' haz hbw)

/-- The canonical right-side code is equivalent to its left-outer source. -/
theorem canonicalRightCodeOfLeftOuter_equiv
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    TwoStepEquiv x y z w
      (TwoStepCode.leftOuter a b z' haz hbw)
      (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) := by
  exact (Classical.choose_spec
    (leftOuter_has_pattern_preserving_rightCode x y z w a b z' haz hbw)).1

/-- The canonical right-side code preserves the dependency pattern of its source. -/
theorem canonicalRightCodeOfLeftOuter_pattern
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
      codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) := by
  exact (Classical.choose_spec
    (leftOuter_has_pattern_preserving_rightCode x y z w a b z' haz hbw)).2

/-- Canonical left-side code attached to a right-outer source witness. -/
noncomputable def canonicalLeftCodeOfRightOuter
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    TwoStepCode x y z w :=
  Classical.choose (rightOuter_has_pattern_preserving_leftCode x y z w a b z' haz hbw)

/-- The canonical left-side code is equivalent to its right-outer source. -/
theorem canonicalLeftCodeOfRightOuter_equiv
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    TwoStepEquiv x y z w
      (TwoStepCode.rightOuter a b z' haz hbw)
      (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) := by
  exact (Classical.choose_spec
    (rightOuter_has_pattern_preserving_leftCode x y z w a b z' haz hbw)).1

/-- The canonical left-side code preserves the dependency pattern of its source. -/
theorem canonicalLeftCodeOfRightOuter_pattern
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
      codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) := by
  exact (Classical.choose_spec
    (rightOuter_has_pattern_preserving_leftCode x y z w a b z' haz hbw)).2

/-- Any raw `outer_comm_outer` target is equivalent to the canonical right target. -/
theorem outer_comm_outer_target_equiv_canonical
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses x z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y z'')
    (haddr : ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z) :
    TwoStepEquiv x y z w
      (TwoStepCode.rightOuter a' b' z'' haz' hbw')
      (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) := by
  exact TwoStepEquiv.trans
    (TwoStepEquiv.symm (TwoStepEquiv.outer_comm_outer haz hbw haz' hbw' haddr))
    (canonicalRightCodeOfLeftOuter_equiv x y z w a b z' haz hbw)

/-- Any raw `outer_comm_inner` target is equivalent to the canonical right target. -/
theorem outer_comm_inner_target_equiv_canonical
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses x y)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z)
    (haddr : ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z) :
    TwoStepEquiv x y z w
      (TwoStepCode.rightInner a' b' y'' hay' hbw')
      (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) := by
  exact TwoStepEquiv.trans
    (TwoStepEquiv.symm (TwoStepEquiv.outer_comm_inner haz hbw hay' hbw' haddr))
    (canonicalRightCodeOfLeftOuter_equiv x y z w a b z' haz hbw)

/-- Any raw `outer_comm_back_outer` target is equivalent to the canonical left target. -/
theorem outer_comm_back_outer_target_equiv_canonical
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses y z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses x z'')
    (haddr : ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z) :
    TwoStepEquiv x y z w
      (TwoStepCode.leftOuter a' b' z'' haz' hbw')
      (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) := by
  exact TwoStepEquiv.trans
    (TwoStepEquiv.symm (TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' haddr))
    (canonicalLeftCodeOfRightOuter_equiv x y z w a b z' haz hbw)

/-- Any raw `outer_comm_back_inner` target is equivalent to the canonical left target. -/
theorem outer_comm_back_inner_target_equiv_canonical
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses y x)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z)
    (haddr : ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z) :
    TwoStepEquiv x y z w
      (TwoStepCode.leftInner a' b' y'' hay' hbw')
      (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) := by
  exact TwoStepEquiv.trans
    (TwoStepEquiv.symm (TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' haddr))
    (canonicalLeftCodeOfRightOuter_equiv x y z w a b z' haz hbw)

/-!
## Constructor-level pattern preservation goals

This is the exact bottleneck for upgrading the address-pattern split to a
quotient-level theorem. The following lemmas describe what each nontrivial
constructor of `TwoStepEquiv` would need in order to preserve `codePattern`.
-/

/-- `outer_comm_outer` preserves pattern exactly when source and target have the same comparability behaviour. -/
theorem codePattern_preserved_by_outer_comm_outer_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses x z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y z'') :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
      codePattern (TwoStepCode.rightOuter a' b' z'' haz' hbw')
        ↔ (PTree.comparable a b ↔ PTree.comparable a' b') := by
  by_cases hab : PTree.comparable a b <;> by_cases hab' : PTree.comparable a' b' <;>
    simp [codePattern, hab, hab']

/-- `outer_comm_inner` preserves pattern exactly when the source outer presentation is already dependent. -/
theorem codePattern_preserved_by_outer_comm_inner_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses x y)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z) :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
      codePattern (TwoStepCode.rightInner a' b' y'' hay' hbw')
        ↔ PTree.comparable a b := by
  by_cases hab : PTree.comparable a b <;> simp [codePattern, hab]

/-- `outer_comm_back_outer` preserves pattern exactly when source and target have the same comparability behaviour. -/
theorem codePattern_preserved_by_outer_comm_back_outer_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses y z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses x z'') :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
      codePattern (TwoStepCode.leftOuter a' b' z'' haz' hbw')
        ↔ (PTree.comparable a b ↔ PTree.comparable a' b') := by
  by_cases hab : PTree.comparable a b <;> by_cases hab' : PTree.comparable a' b' <;>
    simp [codePattern, hab, hab']

/-- `outer_comm_back_inner` preserves pattern exactly when the source outer presentation is already dependent. -/
theorem codePattern_preserved_by_outer_comm_back_inner_iff
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses y x)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z) :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
      codePattern (TwoStepCode.leftInner a' b' y'' hay' hbw')
        ↔ PTree.comparable a b := by
  by_cases hab : PTree.comparable a b <;> simp [codePattern, hab]

/-- Convenient forward form of the previous `outer_comm_outer` criterion. -/
theorem codePattern_preserved_by_outer_comm_outer
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses x z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y z'')
    (hcmp : PTree.comparable a b ↔ PTree.comparable a' b') :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
      codePattern (TwoStepCode.rightOuter a' b' z'' haz' hbw') := by
  exact (codePattern_preserved_by_outer_comm_outer_iff
    x y z w a b z' haz hbw a' b' z'' haz' hbw').2 hcmp

/-- Convenient forward form of the previous `outer_comm_inner` criterion. -/
theorem codePattern_preserved_by_outer_comm_inner
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses x y)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z)
    (hcmp : PTree.comparable a b) :
    codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
      codePattern (TwoStepCode.rightInner a' b' y'' hay' hbw') := by
  exact (codePattern_preserved_by_outer_comm_inner_iff
    x y z w a b z' haz hbw a' b' y'' hay' hbw').2 hcmp

/-- Convenient forward form of the previous `outer_comm_back_outer` criterion. -/
theorem codePattern_preserved_by_outer_comm_back_outer
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (z'' : PTree)
    (haz' : (a', z'') ∈ matchingLeafGraftWitnesses y z)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses x z'')
    (hcmp : PTree.comparable a b ↔ PTree.comparable a' b') :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
      codePattern (TwoStepCode.leftOuter a' b' z'' haz' hbw') := by
  exact (codePattern_preserved_by_outer_comm_back_outer_iff
    x y z w a b z' haz hbw a' b' z'' haz' hbw').2 hcmp

/-- Convenient forward form of the previous `outer_comm_back_inner` criterion. -/
theorem codePattern_preserved_by_outer_comm_back_inner
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (a' b' : Address) (y'' : PTree)
    (hay' : (a', y'') ∈ matchingLeafGraftWitnesses y x)
    (hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z)
    (hcmp : PTree.comparable a b) :
    codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
      codePattern (TwoStepCode.leftInner a' b' y'' hay' hbw') := by
  exact (codePattern_preserved_by_outer_comm_back_inner_iff
    x y z w a b z' haz hbw a' b' y'' hay' hbw').2 hcmp

/-- Constructor-level obligation for `outer_comm_outer`. -/
def OuterCommOuterPatternPreserving
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses y z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses x z'}
    {a' b' : Address} {z'' : PTree}
    {haz' : (a', z'') ∈ matchingLeafGraftWitnesses x z}
    {hbw' : (b', w) ∈ matchingLeafGraftWitnesses y z''},
      ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z →
      codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
        codePattern (TwoStepCode.rightOuter a' b' z'' haz' hbw')

/-- Constructor-level obligation for `outer_comm_inner`. -/
def OuterCommInnerPatternPreserving
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses y z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses x z'}
    {a' b' : Address} {y'' : PTree}
    {hay' : (a', y'') ∈ matchingLeafGraftWitnesses x y}
    {hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z},
      ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z →
      codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
        codePattern (TwoStepCode.rightInner a' b' y'' hay' hbw')

/-- Constructor-level obligation for `outer_comm_back_outer`. -/
def OuterCommBackOuterPatternPreserving
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses x z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses y z'}
    {a' b' : Address} {z'' : PTree}
    {haz' : (a', z'') ∈ matchingLeafGraftWitnesses y z}
    {hbw' : (b', w) ∈ matchingLeafGraftWitnesses x z''},
      ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z →
      codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
        codePattern (TwoStepCode.leftOuter a' b' z'' haz' hbw')

/-- Constructor-level obligation for `outer_comm_back_inner`. -/
def OuterCommBackInnerPatternPreserving
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses x z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses y z'}
    {a' b' : Address} {y'' : PTree}
    {hay' : (a', y'') ∈ matchingLeafGraftWitnesses y x}
    {hbw' : (b', w) ∈ matchingLeafGraftWitnesses y'' z},
      ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z →
      codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
        codePattern (TwoStepCode.leftInner a' b' y'' hay' hbw')

/--
Local transport principle: any code equivalent to the canonical right code
chosen from a left-outer source has the same pattern as that canonical code.
-/
def CanonicalRightCodePatternTransport
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses y z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses x z'}
    {d : TwoStepCode x y z w},
      TwoStepEquiv x y z w d
        (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) →
      codePattern d =
        codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw)

/--
Local transport principle: any code equivalent to the canonical left code
chosen from a right-outer source has the same pattern as that canonical code.
-/
def CanonicalLeftCodePatternTransport
    (x y z w : PTree) : Prop :=
  ∀ {a b : Address} {z' : PTree}
    {haz : (a, z') ∈ matchingLeafGraftWitnesses x z}
    {hbw : (b, w) ∈ matchingLeafGraftWitnesses y z'}
    {d : TwoStepCode x y z w},
      TwoStepEquiv x y z w d
        (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) →
      codePattern d =
        codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw)

/--
The canonical-right transport principle immediately discharges the
`outer_comm_outer` constructor obligation.
-/
theorem outerCommOuterPatternPreserving_of_canonicalTransport
    (x y z w : PTree)
    (htrans : CanonicalRightCodePatternTransport x y z w) :
    OuterCommOuterPatternPreserving x y z w := by
  intro a b z' haz hbw a' b' z'' haz' hbw' haddr
  have h₁ :
      codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
        codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) :=
    canonicalRightCodeOfLeftOuter_pattern x y z w a b z' haz hbw
  have h₂ :
      codePattern (TwoStepCode.rightOuter a' b' z'' haz' hbw') =
        codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) :=
    htrans (outer_comm_outer_target_equiv_canonical
      x y z w a b z' haz hbw a' b' z'' haz' hbw' haddr)
  exact h₁.trans h₂.symm

/--
The canonical-right transport principle immediately discharges the
`outer_comm_inner` constructor obligation.
-/
theorem outerCommInnerPatternPreserving_of_canonicalTransport
    (x y z w : PTree)
    (htrans : CanonicalRightCodePatternTransport x y z w) :
    OuterCommInnerPatternPreserving x y z w := by
  intro a b z' haz hbw a' b' y'' hay' hbw' haddr
  have h₁ :
      codePattern (TwoStepCode.leftOuter a b z' haz hbw) =
        codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) :=
    canonicalRightCodeOfLeftOuter_pattern x y z w a b z' haz hbw
  have h₂ :
      codePattern (TwoStepCode.rightInner a' b' y'' hay' hbw') =
        codePattern (canonicalRightCodeOfLeftOuter x y z w a b z' haz hbw) :=
    htrans (outer_comm_inner_target_equiv_canonical
      x y z w a b z' haz hbw a' b' y'' hay' hbw' haddr)
  exact h₁.trans h₂.symm

/--
The canonical-left transport principle immediately discharges the
`outer_comm_back_outer` constructor obligation.
-/
theorem outerCommBackOuterPatternPreserving_of_canonicalTransport
    (x y z w : PTree)
    (htrans : CanonicalLeftCodePatternTransport x y z w) :
    OuterCommBackOuterPatternPreserving x y z w := by
  intro a b z' haz hbw a' b' z'' haz' hbw' haddr
  have h₁ :
      codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
        codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) :=
    canonicalLeftCodeOfRightOuter_pattern x y z w a b z' haz hbw
  have h₂ :
      codePattern (TwoStepCode.leftOuter a' b' z'' haz' hbw') =
        codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) :=
    htrans (outer_comm_back_outer_target_equiv_canonical
      x y z w a b z' haz hbw a' b' z'' haz' hbw' haddr)
  exact h₁.trans h₂.symm

/--
The canonical-left transport principle immediately discharges the
`outer_comm_back_inner` constructor obligation.
-/
theorem outerCommBackInnerPatternPreserving_of_canonicalTransport
    (x y z w : PTree)
    (htrans : CanonicalLeftCodePatternTransport x y z w) :
    OuterCommBackInnerPatternPreserving x y z w := by
  intro a b z' haz hbw a' b' y'' hay' hbw' haddr
  have h₁ :
      codePattern (TwoStepCode.rightOuter a b z' haz hbw) =
        codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) :=
    canonicalLeftCodeOfRightOuter_pattern x y z w a b z' haz hbw
  have h₂ :
      codePattern (TwoStepCode.leftInner a' b' y'' hay' hbw') =
        codePattern (canonicalLeftCodeOfRightOuter x y z w a b z' haz hbw) :=
    htrans (outer_comm_back_inner_target_equiv_canonical
      x y z w a b z' haz hbw a' b' y'' hay' hbw' haddr)
  exact h₁.trans h₂.symm

/--
If pattern is transportable along equivalences into the canonical right/left
targets, then all four constructor obligations follow.
-/
theorem constructorPatternPreservation_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w) :
    OuterCommOuterPatternPreserving x y z w ∧
    OuterCommInnerPatternPreserving x y z w ∧
    OuterCommBackOuterPatternPreserving x y z w ∧
    OuterCommBackInnerPatternPreserving x y z w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact outerCommOuterPatternPreserving_of_canonicalTransport x y z w hright
  · exact outerCommInnerPatternPreserving_of_canonicalTransport x y z w hright
  · exact outerCommBackOuterPatternPreserving_of_canonicalTransport x y z w hleft
  · exact outerCommBackInnerPatternPreserving_of_canonicalTransport x y z w hleft

/--
Full pattern invariance reduces exactly to the four nontrivial constructor
obligations above.
-/
theorem codePatternInvariant_of_constructor_preservation
    (x y z w : PTree)
    (houtOut : OuterCommOuterPatternPreserving x y z w)
    (houtIn : OuterCommInnerPatternPreserving x y z w)
    (hbackOut : OuterCommBackOuterPatternPreserving x y z w)
    (hbackIn : OuterCommBackInnerPatternPreserving x y z w) :
    CodePatternInvariant x y z w := by
  intro c d h
  induction h with
  | refl c =>
      rfl
  | symm h ih =>
      exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | outer_comm_outer haz hbw haz' hbw' haddr =>
      exact houtOut haddr
  | outer_comm_inner haz hbw hay' hbw' haddr =>
      exact houtIn haddr
  | outer_comm_back_outer haz hbw haz' hbw' haddr =>
      exact hbackOut haddr
  | outer_comm_back_inner haz hbw hay' hbw' haddr =>
      exact hbackIn haddr

/--
If pattern transports along equivalences into the canonical right/left targets,
then full `TwoStepEquiv`-pattern invariance follows.
-/
theorem codePatternInvariant_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w) :
    CodePatternInvariant x y z w := by
  rcases constructorPatternPreservation_of_canonicalTransport x y z w hright hleft with
    ⟨houtOut, houtIn, hbackOut, hbackIn⟩
  exact codePatternInvariant_of_constructor_preservation
    x y z w houtOut houtIn hbackOut hbackIn

/-- An outer-left witness is independent when its graft addresses are incomparable. -/
def OuterLeftWitnessIndependent
    {x y z w : PTree}
    (h : OuterLeftWitness x y z w) : Prop :=
  match h with
  | OuterLeftWitness.mk a b _ _ _ => ¬ PTree.comparable a b

/-- An outer-right witness is independent when its graft addresses are incomparable. -/
def OuterRightWitnessIndependent
    {x y z w : PTree}
    (h : OuterRightWitness x y z w) : Prop :=
  match h with
  | OuterRightWitness.mk a b _ _ _ => ¬ PTree.comparable a b

/--
Weak code-level separation criterion: independent left-outer codes do not
collapse to left-inner codes.
-/
def NoIndependentLeftOuterInnerCodeEquiv
    (x y z w : PTree) : Prop :=
  ∀ a b : Address, ∀ z' : PTree,
    ∀ haz : (a, z') ∈ matchingLeafGraftWitnesses y z,
    ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses x z',
    ¬ PTree.comparable a b →
    ∀ a' b' : Address, ∀ y' : PTree,
    ∀ hay : (a', y') ∈ matchingLeafGraftWitnesses y x,
    ∀ hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z,
      ¬ TwoStepEquiv x y z w
          (TwoStepCode.leftOuter a b z' haz hbw)
          (TwoStepCode.leftInner a' b' y' hay hbw')

/--
Weak swapped-right code-level separation criterion: independent swapped-right
outer codes do not collapse to swapped-right inner codes.
-/
def NoIndependentSwappedRightOuterInnerCodeEquiv
    (x y z w : PTree) : Prop :=
  ∀ a b : Address, ∀ z' : PTree,
    ∀ haz : (a, z') ∈ matchingLeafGraftWitnesses y z,
    ∀ hbw : (b, w) ∈ matchingLeafGraftWitnesses x z',
    ¬ PTree.comparable a b →
    ∀ a' b' : Address, ∀ y' : PTree,
    ∀ hay : (a', y') ∈ matchingLeafGraftWitnesses y x,
    ∀ hbw' : (b', w) ∈ matchingLeafGraftWitnesses y' z,
      ¬ TwoStepEquiv y x z w
          (TwoStepCode.rightOuter a b z' haz hbw)
          (TwoStepCode.rightInner a' b' y' hay hbw')

/-- An independent outer-left witness supports a quotient class. -/
def HasIndependentLeftOuterContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  ∃ h : OuterLeftWitness x y z w,
    OuterLeftWitnessIndependent h ∧ outerLeftWitnessClass h = q

/-- An independent swapped-right outer witness supports a swapped quotient class. -/
def HasIndependentSwappedRightOuterContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  ∃ h : OuterRightWitness y x z w,
    OuterRightWitnessIndependent h ∧ outerRightWitnessClass h = q'

/--
Canonical transport on the left implies the expected independent outer-to-inner
code-level separation.
-/
theorem noIndependentLeftOuterInnerCodeEquiv_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w) :
    NoIndependentLeftOuterInnerCodeEquiv x y z w := by
  intro a b z' haz hbw hcmp a' b' y' hay hbw'
  exact noIndependentLeftOuterToLeftInnerEquiv_of_patternInvariant
    x y z w
    (codePatternInvariant_of_canonicalTransport x y z w hright hleft)
    a b z' haz hbw hcmp a' b' y' hay hbw'

/--
Canonical transport on the swapped-right side implies the expected independent
outer-to-inner code-level separation there.
-/
theorem noIndependentSwappedRightOuterInnerCodeEquiv_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport y x z w)
    (hleft : CanonicalLeftCodePatternTransport y x z w) :
    NoIndependentSwappedRightOuterInnerCodeEquiv x y z w := by
  intro a b z' haz hbw hcmp a' b' y' hay hbw'
  exact noIndependentRightOuterToRightInnerEquiv_of_patternInvariant
    x y z w
    (codePatternInvariant_of_canonicalTransport y x z w hright hleft)
    a b z' haz hbw hcmp a' b' y' hay hbw'

/--
Under canonical transport, an independent outer-left witness class cannot
coincide with a left-inner witness class.
-/
theorem independent_outerLeftWitnessClass_ne_leftInnerWitnessClass_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w)
    (hOut : OuterLeftWitness x y z w)
    (hInd : OuterLeftWitnessIndependent hOut)
    (hIn : LeftInnerWitnessData x y z w) :
    outerLeftWitnessClass hOut ≠ leftInnerWitnessClass x y z w hIn := by
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              intro hEq
              have hclass :
                  codeClass (TwoStepCode.leftOuter a b z' haz hbw) =
                    codeClass (TwoStepCode.leftInner a' b' y' hay hbw') := by
                simpa [outerLeftWitnessClass, leftInnerWitnessClass,
                  classOfLeftWitness, codeOfLeftWitness] using hEq
              exact
                (noIndependentLeftOuterInnerCodeEquiv_of_canonicalTransport
                  x y z w hright hleft
                  a b z' haz hbw hInd a' b' y' hay hbw')
                  (Quotient.exact hclass)
          | outer =>
              cases hh

/--
Under canonical transport on the swapped-right side, an independent swapped
right-outer witness class cannot coincide with a swapped right-inner class.
-/
theorem independent_outerRightWitnessClass_ne_swappedRightInnerWitnessClass_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport y x z w)
    (hleft : CanonicalLeftCodePatternTransport y x z w)
    (hOut : OuterRightWitness y x z w)
    (hInd : OuterRightWitnessIndependent hOut)
    (hIn : SwappedRightInnerWitnessData x y z w) :
    outerRightWitnessClass hOut ≠ swappedRightInnerWitnessClass x y z w hIn := by
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              intro hEq
              have hclass :
                  codeClass (TwoStepCode.rightOuter a b z' haz hbw) =
                    codeClass (TwoStepCode.rightInner a' b' y' hay hbw') := by
                simpa [outerRightWitnessClass, swappedRightInnerWitnessClass,
                  classOfRightWitness, codeOfRightWitness] using hEq
              exact
                (noIndependentSwappedRightOuterInnerCodeEquiv_of_canonicalTransport
                  x y z w hright hleft
                  a b z' haz hbw hInd a' b' y' hay hbw')
                  (Quotient.exact hclass)
          | outer =>
              cases hh

/--
An independently supported outer-left class cannot also carry left-inner
support once canonical transport gives pattern invariance.
-/
theorem independent_leftOuter_support_not_leftInner_support_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w)
    (q : TwoStepQuotient x y z w)
    (hOut : HasIndependentLeftOuterContributionClass x y z w q)
    (hIn : HasLeftInnerContributionClass x y z w q) :
    False := by
  rcases hOut with ⟨hOut, hInd, hhOut⟩
  rcases hIn with ⟨hIn, hhIn⟩
  exact
    independent_outerLeftWitnessClass_ne_leftInnerWitnessClass_of_canonicalTransport
      x y z w hright hleft hOut hInd hIn (hhOut.trans hhIn.symm)

/--
An independently supported swapped-right outer class cannot also carry swapped
right-inner support once canonical transport gives pattern invariance.
-/
theorem independent_swappedRightOuter_support_not_swappedRightInner_support_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport y x z w)
    (hleft : CanonicalLeftCodePatternTransport y x z w)
    (q' : TwoStepQuotient y x z w)
    (hOut : HasIndependentSwappedRightOuterContributionClass x y z w q')
    (hIn : HasSwappedRightInnerContributionClass x y z w q') :
    False := by
  rcases hOut with ⟨hOut, hInd, hhOut⟩
  rcases hIn with ⟨hIn, hhIn⟩
  exact
    independent_outerRightWitnessClass_ne_swappedRightInnerWitnessClass_of_canonicalTransport
      x y z w hright hleft hOut hInd hIn (hhOut.trans hhIn.symm)

/--
Global pattern invariance immediately yields canonical-right transport into the
chosen left-to-right canonical targets.
-/
theorem canonicalRightCodePatternTransport_of_codePatternInvariant
    (x y z w : PTree)
    (hpat : CodePatternInvariant x y z w) :
    CanonicalRightCodePatternTransport x y z w := by
  intro a b z' haz hbw d hEq
  exact hpat hEq

/--
Global pattern invariance immediately yields canonical-left transport into the
chosen right-to-left canonical targets.
-/
theorem canonicalLeftCodePatternTransport_of_codePatternInvariant
    (x y z w : PTree)
    (hpat : CodePatternInvariant x y z w) :
    CanonicalLeftCodePatternTransport x y z w := by
  intro a b z' haz hbw d hEq
  exact hpat hEq

/--
Checkpoint 1 on the original orientation: once canonical transport is
available, the quotient does not collapse independent outer support into inner
support on the left.
-/
theorem independent_split_checkpoint_left_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport x y z w)
    (hleft : CanonicalLeftCodePatternTransport x y z w) :
    CodePatternInvariant x y z w ∧
    NoIndependentLeftOuterInnerCodeEquiv x y z w ∧
    (∀ q : TwoStepQuotient x y z w,
      HasIndependentLeftOuterContributionClass x y z w q →
      HasLeftInnerContributionClass x y z w q →
      False) := by
  refine ⟨?_, ?_, ?_⟩
  · exact codePatternInvariant_of_canonicalTransport x y z w hright hleft
  · exact noIndependentLeftOuterInnerCodeEquiv_of_canonicalTransport x y z w hright hleft
  · intro q hOut hIn
    exact
      independent_leftOuter_support_not_leftInner_support_of_canonicalTransport
        x y z w hright hleft q hOut hIn

/--
Checkpoint 1 on the swapped-right orientation: once canonical transport is
available there as well, the quotient does not collapse independent outer
support into inner support on the swapped-right side.
-/
theorem independent_split_checkpoint_right_of_canonicalTransport
    (x y z w : PTree)
    (hright : CanonicalRightCodePatternTransport y x z w)
    (hleft : CanonicalLeftCodePatternTransport y x z w) :
    CodePatternInvariant y x z w ∧
    NoIndependentSwappedRightOuterInnerCodeEquiv x y z w ∧
    (∀ q' : TwoStepQuotient y x z w,
      HasIndependentSwappedRightOuterContributionClass x y z w q' →
      HasSwappedRightInnerContributionClass x y z w q' →
      False) := by
  refine ⟨?_, ?_, ?_⟩
  · exact codePatternInvariant_of_canonicalTransport y x z w hright hleft
  · exact noIndependentSwappedRightOuterInnerCodeEquiv_of_canonicalTransport x y z w hright hleft
  · intro q' hOut hIn
    exact
      independent_swappedRightOuter_support_not_swappedRightInner_support_of_canonicalTransport
        x y z w hright hleft q' hOut hIn

/--
Checkpoint 1: if canonical transport exists in both orientations, then the
quotient respects the independent/dependent proof-theoretic split needed for
the pre-Lie story.
-/
theorem independent_split_checkpoint_of_canonicalTransport
    (x y z w : PTree)
    (hxy_right : CanonicalRightCodePatternTransport x y z w)
    (hxy_left : CanonicalLeftCodePatternTransport x y z w)
    (hyx_right : CanonicalRightCodePatternTransport y x z w)
    (hyx_left : CanonicalLeftCodePatternTransport y x z w) :
    CodePatternInvariant x y z w ∧
    CodePatternInvariant y x z w ∧
    NoIndependentLeftOuterInnerCodeEquiv x y z w ∧
    NoIndependentSwappedRightOuterInnerCodeEquiv x y z w ∧
    (∀ q : TwoStepQuotient x y z w,
      HasIndependentLeftOuterContributionClass x y z w q →
      HasLeftInnerContributionClass x y z w q →
      False) ∧
    (∀ q' : TwoStepQuotient y x z w,
      HasIndependentSwappedRightOuterContributionClass x y z w q' →
      HasSwappedRightInnerContributionClass x y z w q' →
      False) := by
  rcases independent_split_checkpoint_left_of_canonicalTransport
      x y z w hxy_right hxy_left with
    ⟨hpatxy, hnoLeft, hsepLeft⟩
  rcases independent_split_checkpoint_right_of_canonicalTransport
      x y z w hyx_right hyx_left with
    ⟨hpatyx, hnoRight, hsepRight⟩
  exact ⟨hpatxy, hpatyx, hnoLeft, hnoRight, hsepLeft, hsepRight⟩

/--
An independent left-outer source admits an explicit opposite right-outer
presentation.
-/
theorem independent_leftOuter_has_rightOuter_code
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z')
    (hinc : ¬ PTree.comparable a b) :
    ∃ z₃ : PTree,
      ∃ haz' : (b, z₃) ∈ matchingLeafGraftWitnesses x z,
        ∃ hbw' : (a, w) ∈ matchingLeafGraftWitnesses y z₃,
          TwoStepEquiv x y z w
            (TwoStepCode.leftOuter a b z' haz hbw)
            (TwoStepCode.rightOuter b a z₃ haz' hbw') := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hyz⟩
  rcases hbw with ⟨_, hxz'⟩
  have hdecomp := two_step_graft_decomposition_full x y z a b z' w hyz hxz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hxy, hy'z⟩
      have hcmp : PTree.comparable a b := by
        apply PTree.comparable_of_isAncestorOf
        exact ⟨c, hbEq⟩
      exact False.elim (hinc hcmp)
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hxz, hyz₃⟩
      have haz' : (b, z₃) ∈ matchingLeafGraftWitnesses x z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz⟩
        have hg := PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z b z₃ hxz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf x.conclusion) b
            ((PTree.IsGraftableLeafAt_iff x z b).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses y z₃ := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz₃⟩
        have hg := PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z₃ a w hyz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf y.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y z₃ a).mp hg)
      refine ⟨z₃, haz', hbw', ?_⟩
      exact TwoStepEquiv.outer_comm_outer haz hbw haz' hbw' (by
        rw [mem_twoStepAddrWitnessesRight_iff]
        exact Or.inl ⟨z₃, haz', hbw'⟩)

/--
An independent right-outer source admits an explicit opposite left-outer
presentation.
-/
theorem independent_rightOuter_has_leftOuter_code
    (x y z w : PTree)
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z')
    (hinc : ¬ PTree.comparable a b) :
    ∃ z₃ : PTree,
      ∃ haz' : (b, z₃) ∈ matchingLeafGraftWitnesses y z,
        ∃ hbw' : (a, w) ∈ matchingLeafGraftWitnesses x z₃,
          TwoStepEquiv x y z w
            (TwoStepCode.rightOuter a b z' haz hbw)
            (TwoStepCode.leftOuter b a z₃ haz' hbw') := by
  rw [mem_matchingLeafGraftWitnesses_iff] at haz hbw
  rcases haz with ⟨_, hxz⟩
  rcases hbw with ⟨_, hyz'⟩
  have hdecomp := two_step_graft_decomposition_full y x z a b z' w hxz hyz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hyx, hy'z⟩
      have hcmp : PTree.comparable a b := by
        apply PTree.comparable_of_isAncestorOf
        exact ⟨c, hbEq⟩
      exact False.elim (hinc hcmp)
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hyz, hxz₃⟩
      have haz' : (b, z₃) ∈ matchingLeafGraftWitnesses y z := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz⟩
        have hg := PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z b z₃ hyz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y.conclusion) b
            ((PTree.IsGraftableLeafAt_iff y z b).mp hg)
      have hbw' : (a, w) ∈ matchingLeafGraftWitnesses x z₃ := by
        rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz₃⟩
        have hg := PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z₃ a w hxz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf x.conclusion) a
            ((PTree.IsGraftableLeafAt_iff x z₃ a).mp hg)
      refine ⟨z₃, haz', hbw', ?_⟩
      exact TwoStepEquiv.outer_comm_back_outer haz hbw haz' hbw' (by
        rw [mem_twoStepAddrWitnessesLeft_iff]
        exact Or.inl ⟨z₃, haz', hbw'⟩)

/--
Witness-level packaging of the previous theorem: an independent outer-left
source has an explicit opposite outer-right witness.
-/
theorem independent_outerLeft_gives_rightOuterWitness
    (x y z w : PTree)
    (h : OuterLeftWitness x y z w)
    (hInd : OuterLeftWitnessIndependent h) :
    Nonempty (OuterRightWitness x y z w) := by
  cases h with
  | mk a b z' haz hbw =>
      rcases independent_leftOuter_has_rightOuter_code x y z w a b z' haz hbw hInd with
        ⟨z₃, haz', hbw', hEq⟩
      exact ⟨OuterRightWitness.mk b a z₃ haz' hbw'⟩

/--
Witness-level packaging of the previous theorem: an independent outer-right
source has an explicit opposite outer-left witness.
-/
theorem independent_outerRight_gives_leftOuterWitness
    (x y z w : PTree)
    (h : OuterRightWitness x y z w)
    (hInd : OuterRightWitnessIndependent h) :
    Nonempty (OuterLeftWitness x y z w) := by
  cases h with
  | mk a b z' haz hbw =>
      rcases independent_rightOuter_has_leftOuter_code x y z w a b z' haz hbw hInd with
        ⟨z₃, haz', hbw', hEq⟩
      exact ⟨OuterLeftWitness.mk b a z₃ haz' hbw'⟩

/-- Raw right-inner witnesses in the original `(x,y,z,w)` orientation. -/
def RightInnerWitnessData
    (x y z w : PTree) :=
  { h : TwoStepWitnessRight x y z w //
      match h with
      | TwoStepWitnessRight.inner _ _ _ _ _ => True
      | _ => False }

/--
No outer/inner branch overlap on the right: a final tree `w` cannot admit both
an outer-right witness and an inner-right witness presentation.
-/
def RightWitnessBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterRightWitness x y z w,
    ∀ hIn : RightInnerWitnessData x y z w,
      False

/--
No outer/inner branch overlap on the left: a final tree `w` cannot admit both
an outer-left witness and a left-inner witness presentation.
-/
def LeftWitnessBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterLeftWitness x y z w,
    ∀ hIn : LeftInnerWitnessData x y z w,
      False

/--
Geometric left-side branch exclusivity at the canonical level: the same final
tree `w` is not simultaneously realised by an outer and an inner canonical
two-step decomposition on the left orientation.
-/
def LeftCanonicalBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ z₃ : PTree,
    z₃ ∈ PTree.matchingLeafGraftings y z →
    w ∈ PTree.matchingLeafGraftings x z₃ →
    ∀ y' : PTree,
      y' ∈ PTree.matchingLeafGraftings y x →
      w ∈ PTree.matchingLeafGraftings y' z →
      False

/--
Geometric right-side branch exclusivity at the canonical level: the same final
tree `w` is not simultaneously realised by an outer and an inner canonical
two-step decomposition on the right orientation.
-/
def RightCanonicalBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ z₃ : PTree,
    z₃ ∈ PTree.matchingLeafGraftings x z →
    w ∈ PTree.matchingLeafGraftings y z₃ →
    ∀ y' : PTree,
      y' ∈ PTree.matchingLeafGraftings x y →
      w ∈ PTree.matchingLeafGraftings y' z →
      False

/--
Canonical left-side branch exclusivity implies raw witness branch exclusivity
on the left.
-/
theorem leftWitnessBranchExclusive_of_leftCanonicalBranchExclusive
    (x y z w : PTree)
    (hExcl : LeftCanonicalBranchExclusive x y z w) :
    LeftWitnessBranchExclusive x y z w := by
  intro hOut hIn
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              have hz' : z' ∈ PTree.matchingLeafGraftings y z := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩
              have hwz' : w ∈ PTree.matchingLeafGraftings x z' := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩
              have hy' : y' ∈ PTree.matchingLeafGraftings y x := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(a', y'), hay, rfl⟩
              have hwy' : w ∈ PTree.matchingLeafGraftings y' z := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(b', w), hbw', rfl⟩
              exact hExcl z' hz' hwz' y' hy' hwy'
          | outer =>
              cases hh

/--
Canonical right-side branch exclusivity implies raw witness branch exclusivity
on the right.
-/
theorem rightWitnessBranchExclusive_of_rightCanonicalBranchExclusive
    (x y z w : PTree)
    (hExcl : RightCanonicalBranchExclusive x y z w) :
    RightWitnessBranchExclusive x y z w := by
  intro hOut hIn
  cases hOut with
  | mk a b z' haz hbw =>
      cases hIn with
      | mk hw hh =>
          cases hw with
          | inner a' b' y' hay hbw' =>
              have hz' : z' ∈ PTree.matchingLeafGraftings x z := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩
              have hwz' : w ∈ PTree.matchingLeafGraftings y z' := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩
              have hy' : y' ∈ PTree.matchingLeafGraftings x y := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(a', y'), hay, rfl⟩
              have hwy' : w ∈ PTree.matchingLeafGraftings y' z := by
                rw [← map_snd_matchingLeafGraftWitnesses]
                exact List.mem_map.2 ⟨(b', w), hbw', rfl⟩
              exact hExcl z' hz' hwz' y' hy' hwy'
          | outer =>
              cases hh

/--
Raw left witness branch exclusivity already implies canonical left-side branch
exclusivity.
-/
theorem leftCanonicalBranchExclusive_of_leftWitnessBranchExclusive
    (x y z w : PTree)
    (hExcl : LeftWitnessBranchExclusive x y z w) :
    LeftCanonicalBranchExclusive x y z w := by
  intro z₃ hz₃ hwz₃ y' hy' hwy'
  rw [← map_snd_matchingLeafGraftWitnesses] at hz₃ hwz₃ hy' hwy'
  simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz₃ hwz₃ hy' hwy'
  rcases hz₃ with ⟨a, haz⟩
  rcases hwz₃ with ⟨b, hbw⟩
  rcases hy' with ⟨a', hay⟩
  rcases hwy' with ⟨b', hbw'⟩
  exact hExcl
    (OuterLeftWitness.mk a b z₃ haz hbw)
    ⟨TwoStepWitnessLeft.inner a' b' y' hay hbw', trivial⟩

/--
Raw right witness branch exclusivity already implies canonical right-side
branch exclusivity.
-/
theorem rightCanonicalBranchExclusive_of_rightWitnessBranchExclusive
    (x y z w : PTree)
    (hExcl : RightWitnessBranchExclusive x y z w) :
    RightCanonicalBranchExclusive x y z w := by
  intro z₃ hz₃ hwz₃ y' hy' hwy'
  rw [← map_snd_matchingLeafGraftWitnesses] at hz₃ hwz₃ hy' hwy'
  simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz₃ hwz₃ hy' hwy'
  rcases hz₃ with ⟨a, haz⟩
  rcases hwz₃ with ⟨b, hbw⟩
  rcases hy' with ⟨a', hay⟩
  rcases hwy' with ⟨b', hbw'⟩
  exact hExcl
    (OuterRightWitness.mk a b z₃ haz hbw)
    ⟨TwoStepWitnessRight.inner a' b' y' hay hbw', trivial⟩

/--
The raw and canonical formulations of left-side branch exclusivity are
equivalent.
-/
theorem leftBranchExclusivity_iff_leftCanonicalBranchExclusivity
    (x y z w : PTree) :
    LeftWitnessBranchExclusive x y z w ↔
      LeftCanonicalBranchExclusive x y z w := by
  constructor
  · exact leftCanonicalBranchExclusive_of_leftWitnessBranchExclusive x y z w
  · exact leftWitnessBranchExclusive_of_leftCanonicalBranchExclusive x y z w

/--
The raw and canonical formulations of right-side branch exclusivity are
equivalent.
-/
theorem rightBranchExclusivity_iff_rightCanonicalBranchExclusivity
    (x y z w : PTree) :
    RightWitnessBranchExclusive x y z w ↔
      RightCanonicalBranchExclusive x y z w := by
  constructor
  · exact rightCanonicalBranchExclusive_of_rightWitnessBranchExclusive x y z w
  · exact rightWitnessBranchExclusive_of_rightCanonicalBranchExclusive x y z w

/--
Bare `PTree` geometry does not force right-side canonical branch exclusivity:
a single matching leaf can realize both the outer and inner branches at once.
-/
theorem exists_not_rightCanonicalBranchExclusive :
    ∃ t : PTree, ¬ RightCanonicalBranchExclusive t t t t := by
  let t : PTree := PTree.leaf (MultiSequent.mk 0 0)
  have hmem : t ∈ PTree.matchingLeafGraftings t t := by
    apply PTree.root_matchingLeafGrafting_mem
    simp [t, PTree.subtreeAt, PTree.conclusion]
  refine ⟨t, ?_⟩
  intro hExcl
  exact hExcl t hmem hmem t hmem hmem

/--
Bare `PTree` geometry does not force left-side canonical branch exclusivity
either.
-/
theorem exists_not_leftCanonicalBranchExclusive :
    ∃ t : PTree, ¬ LeftCanonicalBranchExclusive t t t t := by
  let t : PTree := PTree.leaf (MultiSequent.mk 0 0)
  have hmem : t ∈ PTree.matchingLeafGraftings t t := by
    apply PTree.root_matchingLeafGrafting_mem
    simp [t, PTree.subtreeAt, PTree.conclusion]
  refine ⟨t, ?_⟩
  intro hExcl
  exact hExcl t hmem hmem t hmem hmem

/--
So right-side raw witness branch exclusivity is not a theorem of bare `PTree`
geometry alone.
-/
theorem exists_not_rightWitnessBranchExclusive :
    ∃ t : PTree, ¬ RightWitnessBranchExclusive t t t t := by
  rcases exists_not_rightCanonicalBranchExclusive with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro hraw
  exact ht ((rightBranchExclusivity_iff_rightCanonicalBranchExclusivity t t t t).1 hraw)

/--
And left-side raw witness branch exclusivity is not a theorem of bare `PTree`
geometry alone.
-/
theorem exists_not_leftWitnessBranchExclusive :
    ∃ t : PTree, ¬ LeftWitnessBranchExclusive t t t t := by
  rcases exists_not_leftCanonicalBranchExclusive with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro hraw
  exact ht ((leftBranchExclusivity_iff_leftCanonicalBranchExclusivity t t t t).1 hraw)

/-!
## Proper-address restricted grafting layer

The unrestricted geometry admits a degenerate root self-grafting case where the
outer and inner canonical branches coexist.  We therefore introduce a parallel
restricted layer in which every primitive graft occurs at a proper address.
This leaves the original development untouched while isolating the intended
"genuine subproof insertion" fragment.
-/

/-- A proper graft address is any non-root address. -/
def IsProperAddress (a : Address) : Prop := a ≠ []

/-- Matching-leaf graft witnesses restricted to proper addresses. -/
noncomputable def properMatchingLeafGraftWitnesses
    (u t : PTree) : List (Address × PTree) :=
  (matchingLeafGraftWitnesses u t).filter (fun aw => IsProperAddress aw.1)

/-- The corresponding proper-address graftings, forgetting witness addresses. -/
noncomputable def properMatchingLeafGraftings
    (u t : PTree) : List PTree :=
  (properMatchingLeafGraftWitnesses u t).map Prod.snd

/-- Proper-address two-step address witnesses on the left orientation. -/
noncomputable def properTwoStepAddrWitnessesLeft
    (x y z : PTree) : List ((Address × Address) × PTree) :=
  (((properMatchingLeafGraftWitnesses y z).flatMap
      (fun aw =>
        let a := aw.1
        let z' := aw.2
        (properMatchingLeafGraftWitnesses x z').map
          (fun bw => ((a, bw.1), bw.2))))
    ++
    ((properMatchingLeafGraftWitnesses y x).flatMap
      (fun aw =>
        let a := aw.1
        let y' := aw.2
        (properMatchingLeafGraftWitnesses y' z).map
          (fun bw => ((a, bw.1), bw.2)))))

/-- Proper-address two-step address witnesses on the right orientation. -/
noncomputable def properTwoStepAddrWitnessesRight
    (x y z : PTree) : List ((Address × Address) × PTree) :=
  (((properMatchingLeafGraftWitnesses x z).flatMap
      (fun aw =>
        let a := aw.1
        let z' := aw.2
        (properMatchingLeafGraftWitnesses y z').map
          (fun bw => ((a, bw.1), bw.2))))
    ++
    ((properMatchingLeafGraftWitnesses x y).flatMap
      (fun aw =>
        let a := aw.1
        let y' := aw.2
        (properMatchingLeafGraftWitnesses y' z).map
          (fun bw => ((a, bw.1), bw.2)))))

@[simp] theorem mem_properMatchingLeafGraftWitnesses_iff
    (u t : PTree) (a : Address) (t' : PTree) :
    (a, t') ∈ properMatchingLeafGraftWitnesses u t ↔
      (a, t') ∈ matchingLeafGraftWitnesses u t ∧ IsProperAddress a := by
  unfold properMatchingLeafGraftWitnesses IsProperAddress
  simp

@[simp] theorem map_snd_properMatchingLeafGraftWitnesses
    (u t : PTree) :
    (properMatchingLeafGraftWitnesses u t).map Prod.snd =
      properMatchingLeafGraftings u t := by
  rfl

/-- Proper-address grafting into a leaf host is impossible. -/
@[simp] theorem properMatchingLeafGraftWitnesses_leaf
    (u : PTree) (s : MultiSequent) :
    properMatchingLeafGraftWitnesses u (PTree.leaf s) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro aw haw
  rcases aw with ⟨a, t'⟩
  rw [mem_properMatchingLeafGraftWitnesses_iff] at haw
  rcases haw with ⟨hm, hproper⟩
  rw [mem_matchingLeafGraftWitnesses_iff] at hm
  rcases hm with ⟨ha, _⟩
  simp [PTree.allAddresses, PTree.allAddressesGo, PTree.size] at ha
  exact hproper ha

/-- Hence proper-address graftings into a leaf host are empty. -/
@[simp] theorem properMatchingLeafGraftings_leaf
    (u : PTree) (s : MultiSequent) :
    properMatchingLeafGraftings u (PTree.leaf s) = [] := by
  simp [properMatchingLeafGraftings]

/--
Proper right-side canonical branch exclusivity: outer and inner canonical
branches cannot coexist when every primitive graft address is required to be
proper.
-/
def RightProperCanonicalBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ z₃ : PTree,
    z₃ ∈ properMatchingLeafGraftings x z →
    w ∈ properMatchingLeafGraftings y z₃ →
    ∀ y' : PTree,
      y' ∈ properMatchingLeafGraftings x y →
      w ∈ properMatchingLeafGraftings y' z →
      False

/--
Proper left-side canonical branch exclusivity: outer and inner canonical
branches cannot coexist when every primitive graft address is required to be
proper.
-/
def LeftProperCanonicalBranchExclusive
    (x y z w : PTree) : Prop :=
  ∀ z₃ : PTree,
    z₃ ∈ properMatchingLeafGraftings y z →
    w ∈ properMatchingLeafGraftings x z₃ →
    ∀ y' : PTree,
      y' ∈ properMatchingLeafGraftings y x →
      w ∈ properMatchingLeafGraftings y' z →
      False

/--
The root self-grafting counterexample disappears on the proper right-side
fragment.
-/
theorem rightProperCanonicalBranchExclusive_leaf_self
    (s : MultiSequent) :
    RightProperCanonicalBranchExclusive
      (PTree.leaf s) (PTree.leaf s) (PTree.leaf s) (PTree.leaf s) := by
  intro z₃ hz₃
  simpa using hz₃

/--
The same holds on the proper left-side fragment.
-/
theorem leftProperCanonicalBranchExclusive_leaf_self
    (s : MultiSequent) :
    LeftProperCanonicalBranchExclusive
      (PTree.leaf s) (PTree.leaf s) (PTree.leaf s) (PTree.leaf s) := by
  intro z₃ hz₃
  simpa using hz₃

/--
A concrete nontrivial tree used to test whether the proper-address restriction
really removes outer/inner branch overlap.
-/
def properOverlapSeq : MultiSequent := MultiSequent.mk 0 0

/-- A single matching leaf. -/
def properOverlapLeaf : PTree := PTree.leaf properOverlapSeq

/-- A one-step nontrivial tree with a proper graftable leaf at address `[0]`. -/
def properOverlapTree0 : PTree :=
  PTree.node RuleTag.baseAx properOverlapSeq [properOverlapLeaf]

/-- Grafting `properOverlapTree0` into itself at `[0]`. -/
def properOverlapTree1 : PTree :=
  PTree.node RuleTag.baseAx properOverlapSeq [properOverlapTree0]

/-- One more proper graft step. -/
def properOverlapTree2 : PTree :=
  PTree.node RuleTag.baseAx properOverlapSeq [properOverlapTree1]

theorem properOverlapTree1_mem_properMatchingLeafGraftings_self :
    properOverlapTree1 ∈
      properMatchingLeafGraftings properOverlapTree0 properOverlapTree0 := by
  rw [← map_snd_properMatchingLeafGraftWitnesses]
  refine List.mem_map.2 ?_
  refine ⟨([0], properOverlapTree1), ?_, rfl⟩
  rw [mem_properMatchingLeafGraftWitnesses_iff]
  constructor
  · rw [mem_matchingLeafGraftWitnesses_iff]
    constructor
    · have hleaf :
          PTree.subtreeAt properOverlapTree0 [0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
    · have hleaf :
          PTree.subtreeAt properOverlapTree0 [0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      have hmatch : properOverlapTree0.conclusion = properOverlapSeq := by
        simp [properOverlapTree0, properOverlapSeq, PTree.conclusion]
      rw [PTree.graftMatchingLeafAt_eq_some_of_match
        properOverlapTree0 properOverlapTree0 [0] properOverlapSeq hleaf hmatch]
      simp [properOverlapTree0, properOverlapTree1, properOverlapLeaf,
        PTree.modifyAt, PTree.replaceNth]
  · simp [IsProperAddress]

theorem properOverlapTree2_mem_properMatchingLeafGraftings_outer :
    properOverlapTree2 ∈
      properMatchingLeafGraftings properOverlapTree0 properOverlapTree1 := by
  rw [← map_snd_properMatchingLeafGraftWitnesses]
  refine List.mem_map.2 ?_
  refine ⟨([0, 0], properOverlapTree2), ?_, rfl⟩
  rw [mem_properMatchingLeafGraftWitnesses_iff]
  constructor
  · rw [mem_matchingLeafGraftWitnesses_iff]
    constructor
    · have hleaf :
          PTree.subtreeAt properOverlapTree1 [0, 0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree1, properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
    · have hleaf :
          PTree.subtreeAt properOverlapTree1 [0, 0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree1, properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      have hmatch : properOverlapTree0.conclusion = properOverlapSeq := by
        simp [properOverlapTree0, properOverlapSeq, PTree.conclusion]
      rw [PTree.graftMatchingLeafAt_eq_some_of_match
        properOverlapTree0 properOverlapTree1 [0, 0] properOverlapSeq hleaf hmatch]
      simp [properOverlapTree0, properOverlapTree1, properOverlapTree2,
        properOverlapLeaf, PTree.modifyAt, PTree.replaceNth]
  · simp [IsProperAddress]

theorem properOverlapTree2_mem_properMatchingLeafGraftings_inner :
    properOverlapTree2 ∈
      properMatchingLeafGraftings properOverlapTree1 properOverlapTree0 := by
  rw [← map_snd_properMatchingLeafGraftWitnesses]
  refine List.mem_map.2 ?_
  refine ⟨([0], properOverlapTree2), ?_, rfl⟩
  rw [mem_properMatchingLeafGraftWitnesses_iff]
  constructor
  · rw [mem_matchingLeafGraftWitnesses_iff]
    constructor
    · have hleaf :
          PTree.subtreeAt properOverlapTree0 [0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
    · have hleaf :
          PTree.subtreeAt properOverlapTree0 [0] =
            some (PTree.leaf properOverlapSeq) := by
          simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
      have hmatch : properOverlapTree1.conclusion = properOverlapSeq := by
        simp [properOverlapTree1, properOverlapSeq, PTree.conclusion]
      rw [PTree.graftMatchingLeafAt_eq_some_of_match
        properOverlapTree1 properOverlapTree0 [0] properOverlapSeq hleaf hmatch]
      simp [properOverlapTree0, properOverlapTree1, properOverlapTree2,
        properOverlapLeaf, PTree.modifyAt, PTree.replaceNth]
  · simp [IsProperAddress]

/--
The proper-address restriction is still not enough in full generality: a
nontrivial tree can still realize both proper outer and proper inner canonical
branches.
-/
theorem exists_not_rightProperCanonicalBranchExclusive :
    ¬ RightProperCanonicalBranchExclusive
      properOverlapTree0 properOverlapTree0 properOverlapTree0 properOverlapTree2 := by
  intro hExcl
  exact hExcl
    properOverlapTree1
    properOverlapTree1_mem_properMatchingLeafGraftings_self
    properOverlapTree2_mem_properMatchingLeafGraftings_outer
    properOverlapTree1
    properOverlapTree1_mem_properMatchingLeafGraftings_self
    properOverlapTree2_mem_properMatchingLeafGraftings_inner

/--
The same nontrivial counterexample defeats left-side proper canonical branch
exclusivity as well.
-/
theorem exists_not_leftProperCanonicalBranchExclusive :
    ¬ LeftProperCanonicalBranchExclusive
      properOverlapTree0 properOverlapTree0 properOverlapTree0 properOverlapTree2 := by
  intro hExcl
  exact hExcl
    properOverlapTree1
    properOverlapTree1_mem_properMatchingLeafGraftings_self
    properOverlapTree2_mem_properMatchingLeafGraftings_outer
    properOverlapTree1
    properOverlapTree1_mem_properMatchingLeafGraftings_self
    properOverlapTree2_mem_properMatchingLeafGraftings_inner

/--
The nontrivial proper-fragment overlap comes from explicit raw witness data:
grafting `properOverlapTree0` into itself at `[0]` yields `properOverlapTree1`.
-/
theorem properOverlap_self_matchingWitness :
    ([0], properOverlapTree1) ∈
      matchingLeafGraftWitnesses properOverlapTree0 properOverlapTree0 := by
  rw [mem_matchingLeafGraftWitnesses_iff]
  constructor
  · have hleaf :
        PTree.subtreeAt properOverlapTree0 [0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
  · have hleaf :
        PTree.subtreeAt properOverlapTree0 [0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    have hmatch : properOverlapTree0.conclusion = properOverlapSeq := by
      simp [properOverlapTree0, properOverlapSeq, PTree.conclusion]
    rw [PTree.graftMatchingLeafAt_eq_some_of_match
      properOverlapTree0 properOverlapTree0 [0] properOverlapSeq hleaf hmatch]
    simp [properOverlapTree0, properOverlapTree1, properOverlapLeaf,
      PTree.modifyAt, PTree.replaceNth]

/--
The corresponding second-step outer witness is also explicit.
-/
theorem properOverlap_outer_matchingWitness :
    ([0, 0], properOverlapTree2) ∈
      matchingLeafGraftWitnesses properOverlapTree0 properOverlapTree1 := by
  rw [mem_matchingLeafGraftWitnesses_iff]
  constructor
  · have hleaf :
        PTree.subtreeAt properOverlapTree1 [0, 0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree1, properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
  · have hleaf :
        PTree.subtreeAt properOverlapTree1 [0, 0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree1, properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    have hmatch : properOverlapTree0.conclusion = properOverlapSeq := by
      simp [properOverlapTree0, properOverlapSeq, PTree.conclusion]
    rw [PTree.graftMatchingLeafAt_eq_some_of_match
      properOverlapTree0 properOverlapTree1 [0, 0] properOverlapSeq hleaf hmatch]
    simp [properOverlapTree0, properOverlapTree1, properOverlapTree2,
      properOverlapLeaf, PTree.modifyAt, PTree.replaceNth]

/--
The competing inner second-step witness is explicit too.
-/
theorem properOverlap_inner_matchingWitness :
    ([0], properOverlapTree2) ∈
      matchingLeafGraftWitnesses properOverlapTree1 properOverlapTree0 := by
  rw [mem_matchingLeafGraftWitnesses_iff]
  constructor
  · have hleaf :
        PTree.subtreeAt properOverlapTree0 [0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    exact PTree.subtreeAt_some_implies_mem_allAddresses _ _ _ hleaf
  · have hleaf :
        PTree.subtreeAt properOverlapTree0 [0] =
          some (PTree.leaf properOverlapSeq) := by
        simp [properOverlapTree0, properOverlapLeaf, PTree.subtreeAt]
    have hmatch : properOverlapTree1.conclusion = properOverlapSeq := by
      simp [properOverlapTree1, properOverlapSeq, PTree.conclusion]
    rw [PTree.graftMatchingLeafAt_eq_some_of_match
      properOverlapTree1 properOverlapTree0 [0] properOverlapSeq hleaf hmatch]
    simp [properOverlapTree0, properOverlapTree1, properOverlapTree2,
      properOverlapLeaf, PTree.modifyAt, PTree.replaceNth]

/--
The nontrivial overlap already lies inside the intended quotient: the explicit
left-outer presentation is equivalent to the explicit right-inner one.
-/
theorem properOverlap_leftOuter_rightInner_equiv :
    TwoStepEquiv
      properOverlapTree0 properOverlapTree0 properOverlapTree0 properOverlapTree2
      (TwoStepCode.leftOuter
        [0] [0, 0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_outer_matchingWitness)
      (TwoStepCode.rightInner
        [0] [0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_inner_matchingWitness) := by
  refine TwoStepEquiv.outer_comm_inner
    properOverlap_self_matchingWitness
    properOverlap_outer_matchingWitness
    properOverlap_self_matchingWitness
    properOverlap_inner_matchingWitness
    ?_
  rw [mem_twoStepAddrWitnessesRight_iff]
  exact Or.inr ⟨properOverlapTree1, properOverlap_self_matchingWitness,
    properOverlap_inner_matchingWitness⟩

/--
Dually, the explicit right-outer presentation is equivalent to the explicit
left-inner one.
-/
theorem properOverlap_rightOuter_leftInner_equiv :
    TwoStepEquiv
      properOverlapTree0 properOverlapTree0 properOverlapTree0 properOverlapTree2
      (TwoStepCode.rightOuter
        [0] [0, 0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_outer_matchingWitness)
      (TwoStepCode.leftInner
        [0] [0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_inner_matchingWitness) := by
  refine TwoStepEquiv.outer_comm_back_inner
    properOverlap_self_matchingWitness
    properOverlap_outer_matchingWitness
    properOverlap_self_matchingWitness
    properOverlap_inner_matchingWitness
    ?_
  rw [mem_twoStepAddrWitnessesLeft_iff]
  exact Or.inr ⟨properOverlapTree1, properOverlap_self_matchingWitness,
    properOverlap_inner_matchingWitness⟩

/--
So the new nontrivial overlap counterexample is already quotient-controlled on
the left-to-right comparison.
-/
theorem properOverlap_leftOuter_rightInner_sameClass :
    codeClass
      (TwoStepCode.leftOuter
        [0] [0, 0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_outer_matchingWitness)
      =
    codeClass
      (TwoStepCode.rightInner
        [0] [0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_inner_matchingWitness) := by
  exact codeClass_eq_of_equiv properOverlap_leftOuter_rightInner_equiv

/--
And likewise on the right-to-left comparison.
-/
theorem properOverlap_rightOuter_leftInner_sameClass :
    codeClass
      (TwoStepCode.rightOuter
        [0] [0, 0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_outer_matchingWitness)
      =
    codeClass
      (TwoStepCode.leftInner
        [0] [0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_inner_matchingWitness) := by
  exact codeClass_eq_of_equiv properOverlap_rightOuter_leftInner_equiv

/--
The quotient class of any left-outer witness coincides with the quotient class
of any right-inner witness in the same `(x,y,z,w)` geometry.

This is the general overlap-to-same-class form of `outer_comm_inner`.
-/
theorem outerLeftWitnessClass_eq_rightInnerWitnessClass
    (x y z w : PTree)
    (hOut : OuterLeftWitness x y z w)
    (hIn : RightInnerWitnessData x y z w) :
    outerLeftWitnessClass hOut = classOfRightWitness hIn.1 := by
  rcases hOut with ⟨a, b, z', haz, hbw⟩
  rcases hIn with ⟨h, hh⟩
  cases h with
  | inner a' b' y' hay' hbw' =>
      exact codeClass_eq_of_equiv
        (TwoStepEquiv.outer_comm_inner haz hbw hay' hbw' (by
          rw [mem_twoStepAddrWitnessesRight_iff]
          exact Or.inr ⟨y', hay', hbw'⟩))
  | outer =>
      cases hh

/--
The quotient class of any right-outer witness coincides with the quotient class
of any left-inner witness in the same `(x,y,z,w)` geometry.

This is the general overlap-to-same-class form of `outer_comm_back_inner`.
-/
theorem outerRightWitnessClass_eq_leftInnerWitnessClass
    (x y z w : PTree)
    (hOut : OuterRightWitness x y z w)
    (hIn : LeftInnerWitnessData x y z w) :
    outerRightWitnessClass hOut = leftInnerWitnessClass x y z w hIn := by
  rcases hOut with ⟨a, b, z', haz, hbw⟩
  rcases hIn with ⟨h, hh⟩
  cases h with
  | inner a' b' y' hay' hbw' =>
      exact codeClass_eq_of_equiv
        (TwoStepEquiv.outer_comm_back_inner haz hbw hay' hbw' (by
          rw [mem_twoStepAddrWitnessesLeft_iff]
          exact Or.inr ⟨y', hay', hbw'⟩))
  | outer =>
      cases hh

/-- The quotient class attached to a raw right-inner witness. -/
def rightInnerWitnessClass
    (x y z w : PTree) :
    RightInnerWitnessData x y z w → TwoStepQuotient x y z w
  | ⟨h, _⟩ => classOfRightWitness h

/-- Right-inner witnesses lying over a fixed quotient class `q`. -/
def RightInnerFiberData
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :=
  { h : RightInnerWitnessData x y z w //
      rightInnerWitnessClass x y z w h = q }

/-- A quotient class on the right/original orientation carries inner data. -/
def HasRightInnerContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  Nonempty (RightInnerFiberData x y z w q)

/--
Raw overlap is controlled by the quotient on the left-to-right comparison:
every left-outer witness and every right-inner witness determine the same class.
-/
def LeftToRightOverlapControlled
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterLeftWitness x y z w,
    ∀ hIn : RightInnerWitnessData x y z w,
      outerLeftWitnessClass hOut = rightInnerWitnessClass x y z w hIn

/--
Raw overlap is controlled by the quotient on the right-to-left comparison:
every right-outer witness and every left-inner witness determine the same class.
-/
def RightToLeftOverlapControlled
    (x y z w : PTree) : Prop :=
  ∀ hOut : OuterRightWitness x y z w,
    ∀ hIn : LeftInnerWitnessData x y z w,
      outerRightWitnessClass hOut = leftInnerWitnessClass x y z w hIn

/-- The left-to-right overlap control theorem holds in full generality. -/
theorem leftToRightOverlapControlled
    (x y z w : PTree) :
    LeftToRightOverlapControlled x y z w := by
  intro hOut hIn
  exact outerLeftWitnessClass_eq_rightInnerWitnessClass x y z w hOut hIn

/-- The right-to-left overlap control theorem holds in full generality. -/
theorem rightToLeftOverlapControlled
    (x y z w : PTree) :
    RightToLeftOverlapControlled x y z w := by
  intro hOut hIn
  exact outerRightWitnessClass_eq_leftInnerWitnessClass x y z w hOut hIn

/--
Class-level form of left-to-right overlap control: any outer-left-supported
class and any right-inner-supported class must coincide.
-/
theorem HasLeftOuterContributionClass.eq_rightInnerContributionClass
    (x y z w : PTree)
    (q q' : TwoStepQuotient x y z w)
    (hq : HasLeftOuterContributionClass x y z w q)
    (hq' : HasRightInnerContributionClass x y z w q') :
    q = q' := by
  rcases hq with ⟨hOut, rfl⟩
  rcases hq' with ⟨⟨hIn, hhIn⟩⟩
  exact (outerLeftWitnessClass_eq_rightInnerWitnessClass x y z w hOut hIn).trans hhIn

/--
Class-level form of right-to-left overlap control: any right-outer-supported
class and any left-inner-supported class must coincide.
-/
theorem HasRightOuterContributionClass.eq_leftInnerContributionClass
    (x y z w : PTree)
    (q q' : TwoStepQuotient x y z w)
    (hq : HasRightOuterContributionClass x y z w q)
    (hq' : HasLeftInnerContributionClass x y z w q') :
    q = q' := by
  rcases hq with ⟨hOut, rfl⟩
  rcases hq' with ⟨⟨hIn, hhIn⟩⟩
  exact (outerRightWitnessClass_eq_leftInnerWitnessClass x y z w hOut hIn).trans hhIn

/--
Checkpoint 1, restated at the right level:
all outer/inner overlaps that occur in the geometry are already controlled by
the quotient at class level.
-/
def ClassLevelCheckpoint1
    (x y z w : PTree) : Prop :=
  (∀ q q' : TwoStepQuotient x y z w,
      HasLeftOuterContributionClass x y z w q →
      HasRightInnerContributionClass x y z w q' →
      q = q')
  ∧
  (∀ q q' : TwoStepQuotient x y z w,
      HasRightOuterContributionClass x y z w q →
      HasLeftInnerContributionClass x y z w q' →
      q = q')

/--
Checkpoint 1: the quotient accounts for outer/inner overlap rather than
leaving it as uncontrolled raw ambiguity.
-/
theorem classLevelCheckpoint1
    (x y z w : PTree) :
    ClassLevelCheckpoint1 x y z w := by
  constructor
  · intro q q' hq hq'
    exact HasLeftOuterContributionClass.eq_rightInnerContributionClass x y z w q q' hq hq'
  · intro q q' hq hq'
    exact HasRightOuterContributionClass.eq_leftInnerContributionClass x y z w q q' hq hq'

/--
Minimal provisional outer-visibility predicate on quotient classes in the
original orientation.
-/
def ClassHasOuterRepresentative
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  HasLeftOuterContributionClass x y z w q ∨
    HasRightOuterContributionClass x y z w q

/--
Minimal provisional inner-visibility predicate on quotient classes in the
original orientation.
-/
def ClassHasInnerRepresentative
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  HasLeftInnerContributionClass x y z w q ∨
    HasRightInnerContributionClass x y z w q

/--
Left-to-right overlap noise: a class simultaneously admits a left-outer and a
right-inner presentation, and this coincidence is quotient-trivial by the new
overlap-control theorem.
-/
def LeftToRightOverlapNoiseClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  HasLeftOuterContributionClass x y z w q ∧
    HasRightInnerContributionClass x y z w q

/--
Right-to-left overlap noise: a class simultaneously admits a right-outer and a
left-inner presentation, again in a quotient-trivial way.
-/
def RightToLeftOverlapNoiseClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  HasRightOuterContributionClass x y z w q ∧
    HasLeftInnerContributionClass x y z w q

/--
Residual left contribution classes are those left contribution classes left
over after quotient-trivial overlap noise is removed.
-/
def ResidualLeftContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  IsLeftContributionClass x y z w q ∧
    ¬ LeftToRightOverlapNoiseClass x y z w q ∧
    ¬ RightToLeftOverlapNoiseClass x y z w q

/-- Any left-outer supporting class is outer-visible. -/
theorem HasLeftOuterContributionClass.to_outerVisible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : HasLeftOuterContributionClass x y z w q) :
    ClassHasOuterRepresentative x y z w q := by
  exact Or.inl hq

/-- Any right-outer supporting class is outer-visible. -/
theorem HasRightOuterContributionClass.to_outerVisible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : HasRightOuterContributionClass x y z w q) :
    ClassHasOuterRepresentative x y z w q := by
  exact Or.inr hq

/-- Any left-inner supporting class is inner-visible. -/
theorem HasLeftInnerContributionClass.to_innerVisible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : HasLeftInnerContributionClass x y z w q) :
    ClassHasInnerRepresentative x y z w q := by
  exact Or.inl hq

/-- Any right-inner supporting class is inner-visible. -/
theorem HasRightInnerContributionClass.to_innerVisible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : HasRightInnerContributionClass x y z w q) :
    ClassHasInnerRepresentative x y z w q := by
  exact Or.inr hq

/-- Left-to-right overlap noise classes are simultaneously outer- and inner-visible. -/
theorem LeftToRightOverlapNoiseClass.visible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : LeftToRightOverlapNoiseClass x y z w q) :
    ClassHasOuterRepresentative x y z w q ∧
      ClassHasInnerRepresentative x y z w q := by
  exact ⟨hq.1.to_outerVisible x y z w, hq.2.to_innerVisible x y z w⟩

/-- Right-to-left overlap noise classes are simultaneously outer- and inner-visible. -/
theorem RightToLeftOverlapNoiseClass.visible
    (x y z w : PTree)
    {q : TwoStepQuotient x y z w}
    (hq : RightToLeftOverlapNoiseClass x y z w q) :
    ClassHasOuterRepresentative x y z w q ∧
      ClassHasInnerRepresentative x y z w q := by
  exact ⟨hq.1.to_outerVisible x y z w, hq.2.to_innerVisible x y z w⟩

/--
The left-to-right overlap noise floor has degree at most one class.
-/
theorem LeftToRightOverlapNoiseClass_subsingleton
    (x y z w : PTree) :
    Subsingleton { q : TwoStepQuotient x y z w //
      LeftToRightOverlapNoiseClass x y z w q } := by
  refine ⟨?_⟩
  intro u v
  apply Subtype.ext
  exact HasLeftOuterContributionClass.eq_rightInnerContributionClass
    x y z w u.1 v.1 u.2.1 v.2.2

/--
The right-to-left overlap noise floor also has degree at most one class.
-/
theorem RightToLeftOverlapNoiseClass_subsingleton
    (x y z w : PTree) :
    Subsingleton { q : TwoStepQuotient x y z w //
      RightToLeftOverlapNoiseClass x y z w q } := by
  refine ⟨?_⟩
  intro u v
  apply Subtype.ext
  exact HasRightOuterContributionClass.eq_leftInnerContributionClass
    x y z w u.1 v.1 u.2.1 v.2.2

/--
Every left contribution class is either quotient-trivial overlap noise in one
of the two controlled senses, or else belongs to the residual sector.
-/
theorem leftContributionClass_overlapNoise_or_residual
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : IsLeftContributionClass x y z w q) :
    LeftToRightOverlapNoiseClass x y z w q ∨
      RightToLeftOverlapNoiseClass x y z w q ∨
      ResidualLeftContributionClass x y z w q := by
  classical
  by_cases hLR : LeftToRightOverlapNoiseClass x y z w q
  · exact Or.inl hLR
  · by_cases hRL : RightToLeftOverlapNoiseClass x y z w q
    · exact Or.inr (Or.inl hRL)
    · exact Or.inr (Or.inr ⟨hq, hLR, hRL⟩)

/--
The explicit nontrivial proper-overlap counterexample lands in the
left-to-right overlap noise floor.
-/
theorem properOverlap_class_is_leftToRightOverlapNoise :
    LeftToRightOverlapNoiseClass
      properOverlapTree0 properOverlapTree0 properOverlapTree0 properOverlapTree2
      (codeClass
        (TwoStepCode.leftOuter
          [0] [0, 0] properOverlapTree1
          properOverlap_self_matchingWitness
          properOverlap_outer_matchingWitness)) := by
  constructor
  · refine ⟨OuterLeftWitness.mk [0] [0, 0] properOverlapTree1
      properOverlap_self_matchingWitness
      properOverlap_outer_matchingWitness, rfl⟩
  · refine ⟨⟨?_, ?_⟩⟩
    · exact ⟨TwoStepWitnessRight.inner
        [0] [0] properOverlapTree1
        properOverlap_self_matchingWitness
        properOverlap_inner_matchingWitness, trivial⟩
    · simpa [rightInnerWitnessClass, classOfRightWitness, codeOfRightWitness]
        using properOverlap_leftOuter_rightInner_sameClass.symm

/--
If an independent left-outer source had an opposite right-inner witness, then
the right side would necessarily admit both outer and inner witness branches.

This isolates the exact extra hypothesis still missing if one wants a direct
contradiction from the current decomposition machinery alone.
-/
theorem independent_leftOuter_with_rightInner_forces_rightBranchOverlap
    (x y z w : PTree)
    (hOut : OuterLeftWitness x y z w)
    (hInd : OuterLeftWitnessIndependent hOut)
    (hIn : RightInnerWitnessData x y z w) :
    ¬ RightWitnessBranchExclusive x y z w := by
  intro hExcl
  rcases independent_outerLeft_gives_rightOuterWitness x y z w hOut hInd with ⟨hOutR⟩
  exact hExcl hOutR hIn

/--
Under right-branch exclusivity, an independent left-outer source cannot also
admit an opposite right-inner witness.
-/
theorem independent_leftOuter_excludes_rightInner_of_rightBranchExclusive
    (x y z w : PTree)
    (hExcl : RightWitnessBranchExclusive x y z w)
    (hOut : OuterLeftWitness x y z w)
    (hInd : OuterLeftWitnessIndependent hOut)
    (hIn : RightInnerWitnessData x y z w) :
    False := by
  exact
    (independent_leftOuter_with_rightInner_forces_rightBranchOverlap
      x y z w hOut hInd hIn) hExcl

/--
If an independent right-outer source had an opposite left-inner witness, then
the left side would necessarily admit both outer and inner witness branches.
-/
theorem independent_rightOuter_with_leftInner_forces_leftBranchOverlap
    (x y z w : PTree)
    (hOut : OuterRightWitness x y z w)
    (hInd : OuterRightWitnessIndependent hOut)
    (hIn : LeftInnerWitnessData x y z w) :
    ¬ LeftWitnessBranchExclusive x y z w := by
  intro hExcl
  rcases independent_outerRight_gives_leftOuterWitness x y z w hOut hInd with ⟨hOutL⟩
  exact hExcl hOutL hIn

/--
Under left-branch exclusivity, an independent right-outer source cannot also
admit an opposite left-inner witness.
-/
theorem independent_rightOuter_excludes_leftInner_of_leftBranchExclusive
    (x y z w : PTree)
    (hExcl : LeftWitnessBranchExclusive x y z w)
    (hOut : OuterRightWitness x y z w)
    (hInd : OuterRightWitnessIndependent hOut)
    (hIn : LeftInnerWitnessData x y z w) :
    False := by
  exact
    (independent_rightOuter_with_leftInner_forces_leftBranchOverlap
      x y z w hOut hInd hIn) hExcl

/--
Geometric right-side canonical branch exclusivity is sufficient to exclude an
opposite right-inner witness from an independent left-outer source.
-/
theorem independent_leftOuter_excludes_rightInner_of_rightCanonicalBranchExclusive
    (x y z w : PTree)
    (hExcl : RightCanonicalBranchExclusive x y z w)
    (hOut : OuterLeftWitness x y z w)
    (hInd : OuterLeftWitnessIndependent hOut)
    (hIn : RightInnerWitnessData x y z w) :
    False := by
  exact
    independent_leftOuter_excludes_rightInner_of_rightBranchExclusive
      x y z w
      (rightWitnessBranchExclusive_of_rightCanonicalBranchExclusive x y z w hExcl)
      hOut hInd hIn

/--
Geometric left-side canonical branch exclusivity is sufficient to exclude an
opposite left-inner witness from an independent right-outer source.
-/
theorem independent_rightOuter_excludes_leftInner_of_leftCanonicalBranchExclusive
    (x y z w : PTree)
    (hExcl : LeftCanonicalBranchExclusive x y z w)
    (hOut : OuterRightWitness x y z w)
    (hInd : OuterRightWitnessIndependent hOut)
    (hIn : LeftInnerWitnessData x y z w) :
    False := by
  exact
    independent_rightOuter_excludes_leftInner_of_leftBranchExclusive
      x y z w
      (leftWitnessBranchExclusive_of_leftCanonicalBranchExclusive x y z w hExcl)
      hOut hInd hIn














/-!
## Bundled recovery forms
-/

theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1 = t := by
  cases t
  cases canonicalRightNeighborOfLeftNeighbor x y z w t s
  simp at *
  aesop

theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1 = s := by
  cases s
  cases canonicalLeftNeighborOfRightNeighbor x y z w s t
  simp at *
  aesop




/-- Placeholder: local counting theorem.
Likely target: the neighbour sets on the two sides are equinumerous, or both
are controlled by the same witness/support data.
-/
theorem swappedNeighbors_cardinal_balance
    (x y z w : PTree)
    (qL : TwoStepQuotient x y z w)
    (qR : TwoStepQuotient y x z w) :
    True := by
  /-
  Replace `True` with the correct statement once you decide whether the right
  theorem is:
  - equality of cardinalities,
  - existence of a surjection each way,
  - or equivalence with previously-defined witness-support fibres.
  -/
  trivial




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
