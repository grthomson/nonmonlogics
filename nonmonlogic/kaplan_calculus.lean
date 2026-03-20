import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.List.Basic

#check List

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

--variable {A B : MyProp}
--variable {Γ Θ : Multiset MyProp}

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
    {Γ Θ : Multiset MyProp}
    (h : base Γ Θ) :
    NMMS base (Γ ∣∼ Θ)

| imp_l
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : NMMS base (Γ ∣∼ A ::ₘ Θ))
    (d₂ : NMMS base (B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A ⇒ B) ::ₘ Γ ∣∼ Θ)

| imp_r
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS base (A ::ₘ Γ ∣∼ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A ⇒ B) ::ₘ Θ)

| conj_l
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS base (A ::ₘ B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A & B) ::ₘ Γ ∣∼ Θ)

| conj_r
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : NMMS base (Γ ∣∼ A ::ₘ Θ))
    (d₂ : NMMS base (Γ ∣∼ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A & B) ::ₘ Θ)

| disj_l
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : NMMS base (A ::ₘ Γ ∣∼ Θ))
    (d₂ : NMMS base (B ::ₘ Γ ∣∼ Θ)) :
    NMMS base ((A ∨ B) ::ₘ Γ ∣∼ Θ)

| disj_r
    {A B : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS base (Γ ∣∼ A ::ₘ B ::ₘ Θ)) :
    NMMS base (Γ ∣∼ (A ∨ B) ::ₘ Θ)

| neg_l
    {A : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS base (Γ ∣∼ A ::ₘ Θ)) :
    NMMS base ((¬A) ::ₘ Γ ∣∼ Θ)

| neg_r
    {A : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS base (A ::ₘ Γ ∣∼ Θ)) :
    NMMS base (Γ ∣∼ (¬A) ::ₘ Θ)

/-! ## Proof-tree structure for Paper 2 -/

/--
Tags for the logical rule used at a proof-tree node.

`baseAx` is included for uniformity, though base leaves are represented
as `PTree.leaf`.
-/
inductive RuleTag where
| baseAx
| imp_l
| imp_r
| conj_l
| conj_r
| disj_l
| disj_r
| neg_l
| neg_r
deriving DecidableEq, Repr

/--
A plain rooted proof-tree type, separated from the dependent derivation
family `NMMS`.

* `leaf s` represents a leaf labelled by the sequent `s`
* `node r s cs` represents an internal node:
  - `r` is the rule applied at the node
  - `s` is the conclusion sequent at that node
  - `cs` is the list of immediate subproofs / children

For the current calculus, all nodes have arity 0, 1, or 2.
-/
inductive PTree : Type where
| leaf : MultiSequent → PTree
| node : RuleTag → MultiSequent → List PTree → PTree
deriving instance DecidableEq for Syntax.MultiSequent
-- deriving instance Repr for Syntax.MultiSequent
-- Multiset has no Repr instance - would have to define an alternative

namespace PTree

/-- The sequent decorating the root of a proof tree. -/
def conclusion : PTree → MultiSequent
| leaf s      => s
| node _ s _  => s

/-- Number of nodes in a proof tree. -/
def size : PTree → Nat
| leaf _      => 1
| node _ _ cs => 1 + cs.foldr (fun t n => size t + n) 0

/-- Height of a proof tree. -/
def height : PTree → Nat
| leaf _      => 1
| node _ _ [] => 1
| node _ _ cs => 1 + (cs.foldr (fun t n => max (height t) n) 0)

/--
Immediate subtrees of a proof tree.
For a leaf this is empty; for a node it is just its child list.
-/
def children : PTree → List PTree
| leaf _      => []
| node _ _ cs => cs

/--
A very simple recursive list of all subtrees.
This includes the tree itself as the first element.
-/
def subtrees : PTree → List PTree
| t@(leaf _)      => [t]
| t@(node _ _ cs) => t :: (cs.flatMap subtrees)

end PTree

/-! ## Forgetful map from derivations to plain proof trees -/

namespace NMMS

/--
Forget the dependent derivation object and retain only its rooted tree shape,
rule labels, and node sequents.


-/
def toTree {base : BaseRel} {s : MultiSequent} (d : NMMS base s) : PTree :=
  match d with
  | @NMMS.baseAx _ Γ Θ h =>
      PTree.leaf (Γ ∣∼ Θ)

  | @NMMS.imp_l _ A B Γ Θ d₁ d₂ =>
      PTree.node RuleTag.imp_l (((A ⇒ B) ::ₘ Γ) ∣∼ Θ) [toTree d₁, toTree d₂]

  | @NMMS.imp_r _ A B Γ Θ d =>
      PTree.node RuleTag.imp_r (Γ ∣∼ ((A ⇒ B) ::ₘ Θ)) [toTree d]

  | @NMMS.conj_l _ A B Γ Θ d =>
      PTree.node RuleTag.conj_l (((A & B) ::ₘ Γ) ∣∼ Θ) [toTree d]

  | @NMMS.conj_r _ A B Γ Θ d₁ d₂ =>
      PTree.node RuleTag.conj_r (Γ ∣∼ ((A & B) ::ₘ Θ)) [toTree d₁, toTree d₂]

  | @NMMS.disj_l _ A B Γ Θ d₁ d₂ =>
      PTree.node RuleTag.disj_l (((A ∨ B) ::ₘ Γ) ∣∼ Θ) [toTree d₁, toTree d₂]

  | @NMMS.disj_r _ A B Γ Θ d =>
      PTree.node RuleTag.disj_r (Γ ∣∼ ((A ∨ B) ::ₘ Θ)) [toTree d]

  | @NMMS.neg_l _ A Γ Θ d =>
      PTree.node RuleTag.neg_l (((¬A) ::ₘ Γ) ∣∼ Θ) [toTree d]

  | @NMMS.neg_r _ A Γ Θ d =>
      PTree.node RuleTag.neg_r (Γ ∣∼ ((¬A) ::ₘ Θ)) [toTree d]

end NMMS

/-! ## Early target statements for Paper 2 -/

/--
Target theorem: converting a derivation to a plain proof tree preserves
the end-sequent at the root.
-/
theorem toTree_conclusion {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    (NMMS.toTree d).conclusion = s := by
  induction d with
  | baseAx h =>
      rfl
  | imp_l d₁ d₂ ih₁ ih₂ =>
      rfl
  | imp_r d ih =>
      rfl
  | conj_l d ih =>
      rfl
  | conj_r d₁ d₂ ih₁ ih₂ =>
      rfl
  | disj_l d₁ d₂ ih₁ ih₂ =>
      rfl
  | disj_r d ih =>
      rfl
  | neg_l d ih =>
      rfl
  | neg_r d ih =>
      rfl

/--
A subtree is an immediate premise-tree of a node in the proof tree.

This is a first-step notion toward the stronger "logically meaningful
subproof decomposition" theorem we want later.
-/
def IsImmediateSubtree (t u : PTree) : Prop :=
  u ∈ t.children

/--
Target theorem: every immediate child in `toTree d` arises from a genuine
premise derivation of the final rule of `d`.

This is written only as a placeholder target for now. The exact final form
may be refined once we decide how to state "subproof correspondence".
-/
theorem immediate_subtree_correspondence
    {base : BaseRel} {s : MultiSequent} (d : NMMS base s) :
    ∀ u, IsImmediateSubtree (NMMS.toTree d) u →
      ∃ s' : MultiSequent, u.conclusion = s' := by
  intro u hu
  exact ⟨u.conclusion, rfl⟩

/--
A more ambitious future target: every subtree of `toTree d` corresponds to
some genuine subderivation.

For now this is only a placeholder theorem statement.
-/
theorem subtree_correspondence
    {base : BaseRel} {s : MultiSequent} (d : NMMS base s) :
    ∀ u, u ∈ (NMMS.toTree d).subtrees →
      ∃ s' : MultiSequent, u.conclusion = s' := by
  intro u hu
  exact ⟨u.conclusion, rfl⟩

/--
Another useful target for later CK-style recursion:
every immediate child has strictly smaller size than the parent.
-/
theorem child_size_lt_parent
    (t u : PTree) :
    IsImmediateSubtree t u → u.size < t.size := by
  sorry

end Syntax
