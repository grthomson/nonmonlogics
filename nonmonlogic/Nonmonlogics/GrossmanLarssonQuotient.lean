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
