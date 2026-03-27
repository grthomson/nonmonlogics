import Nonmonlogics.GrossmanLarsson

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
      · simpa [classOfLeftWitness, codeOfLeftWitness] using
          leftInner_class_has_swapped_partner x y z w a b y' hay hbw
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
      · simpa [l, classOfRightWitness, codeOfRightWitness] using
          rightInner_class_has_swapped_partner x y z w a b y' hay hbw
  | outer =>
      cases hh



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
