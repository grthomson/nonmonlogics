import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.List.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
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
  intro h
  unfold IsImmediateSubtree at h
  cases t with
  | leaf s =>
      simp [PTree.children] at h
  | node r s cs =>
      simp [PTree.children] at h
      simp [PTree.size]
      induction cs with
      | nil => simp at h
      | cons c rest ih =>
          simp only [List.foldr]
          simp [List.mem_cons] at h
          cases h with
          | inl heq =>
              subst heq
              omega
          | inr hmem =>
              have := ih hmem
              omega

/-! ## CK-oriented combinatorial layer on proof trees -/

/--
A forest is just a list of proof trees.
This is the natural container for the "pruned" part of a CK cut.
-/
abbrev Forest := List PTree

/--
A node address is a path of child indices from the root.

Examples:
* `[]`       = the root
* `[0]`      = the first child of the root
* `[1, 0]`   = second child, then first child
-/
abbrev Address := List Nat

namespace PTree

/--
Retrieve the subtree at a given address, if it exists.

* `[]` returns the whole tree
* descending past a leaf fails
* descending via an out-of-bounds child index fails
-/
def subtreeAt : PTree → Address → Option PTree
  | t, [] => some t
  | leaf _, _ :: _ => none
  | node _ _ cs, i :: rest =>
      if h : i < cs.length then
        subtreeAt (cs[i]) rest
      else
        none

/--
Boolean test for whether an address is valid in a given tree.
-/
def validAddress (t : PTree) (a : Address) : Bool :=
  Option.isSome (subtreeAt t a)

/--
Propositional version of address validity.
This is usually easier to use in theorem statements.
-/
def ValidAddress (t : PTree) (a : Address) : Prop :=
  validAddress t a = true

/--
An address `a` is an ancestor of address `b` if `a` is a prefix of `b`.
This includes the case `a = b`.
-/
def isAncestorOf (a b : Address) : Prop :=
  ∃ c : Address, b = a ++ c

/--
Two addresses are comparable if one lies on the path to the other.
Equivalently, one is an ancestor of the other.
-/
def comparable (a b : Address) : Prop :=
  isAncestorOf a b ∨ isAncestorOf b a

/--
A cut is admissible if:

1. every address in it is valid in the tree, and
2. no two distinct addresses are comparable.

So the cut addresses form an antichain in the tree order.
-/
structure IsAdmissibleCut (t : PTree) where
  nodes : List Address
  valid : ∀ a, a ∈ nodes → ValidAddress t a
  antichain :
    ∀ a, a ∈ nodes →
    ∀ b, b ∈ nodes →
    a ≠ b → ¬ comparable a b

end PTree

/-! ## Small sanity lemmas / targets -/

namespace PTree

theorem subtreeAt_root (t : PTree) :
    subtreeAt t [] = some t := by
  rfl

theorem validAddress_root (t : PTree) :
    validAddress t [] = true := by
  simp [validAddress, subtreeAt]

/--
If `subtreeAt t a = some u`, then `a` is a valid address in `t`.
-/
theorem subtreeAt_some_implies_valid
    (t u : PTree) (a : Address)
    (h : subtreeAt t a = some u) :
    ValidAddress t a := by
  unfold ValidAddress validAddress
  simp [h]

/--
A useful converse target: valid addresses are exactly those with a subtree.
You can prove this later if needed.
-/
theorem valid_iff_exists_subtree
    (t : PTree) (a : Address) :
    ValidAddress t a ↔ ∃ u, subtreeAt t a = some u := by
  unfold ValidAddress validAddress
  constructor
  · intro h
    cases hsub : subtreeAt t a with
    | none =>
        simp [hsub] at h
    | some u =>
        use u
  · intro hex
    rcases hex with ⟨u, hu⟩
    simp [hu]

/--
Reflexivity of the ancestor relation.
-/
theorem isAncestorOf_refl (a : Address) :
    isAncestorOf a a := by
  refine ⟨[], ?_⟩
  simp

/--
Every address is comparable with itself.
-/
theorem comparable_refl (a : Address) :
    comparable a a := by
  left
  exact isAncestorOf_refl a

/--
The root address is an ancestor of every address.
-/
theorem root_isAncestorOf (a : Address) :
    isAncestorOf [] a := by
  refine ⟨a, ?_⟩
  simp

/--
If `a` is an ancestor of `b`, then `a` and `b` are comparable.
-/
theorem comparable_of_isAncestorOf {a b : Address}
    (h : isAncestorOf a b) :
    comparable a b := by
  exact Or.inl h

/--
Replace every node at a cut address with a leaf (carrying its sequent),
retaining everything above the cut. This is the "remainder" — the part
containing the root.
-/

def remainderGo (c : List Address) (addr : Address) (t : PTree) : PTree :=
  match t with
  | PTree.leaf s => PTree.leaf s
  | PTree.node r s cs =>
      if addr ∈ c then PTree.leaf s
      else PTree.node r s (cs.attach.mapIdx (fun i ⟨child, hmem⟩ =>
        remainderGo c (addr ++ [i]) child))
termination_by t.size
decreasing_by
  have hlt := child_size_lt_parent (PTree.node r s cs) child (by
    unfold IsImmediateSubtree PTree.children
    exact hmem)
  unfold PTree.size at *
  exact hlt

def remainder (t : PTree) (cut : IsAdmissibleCut t) : PTree :=
  remainderGo cut.nodes [] t

/--
Collect the subtrees rooted at each cut node.
These are the "pruned off" pieces — the forest above the cut
(in the CK convention where the root is at the bottom).
-/
def pruned (t : PTree) (cut : IsAdmissibleCut t) : Forest :=
  cut.nodes.filterMap (subtreeAt t)
end PTree

namespace PTree

/--
Computable prefix check — `a` is a prefix of `b`.
-/
def isPrefixOf : Address → Address → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => a == b && isPrefixOf as bs

/--
Computable comparability check.
Two addresses are comparable if one is a prefix of the other.
-/
def comparableBool (a b : Address) : Bool :=
  isPrefixOf a b || isPrefixOf b a

/--
All valid addresses in a tree, represented as a list.
We track the full path from the root as we descend.
-/
def allAddressesGo : Nat → PTree → Address → List Address
  | 0, _, _ => []
  | n + 1, leaf _, addr => [addr]
  | n + 1, node _ _ cs, addr =>
      let childResults := cs.mapIdx (fun i child =>
        allAddressesGo n child (addr ++ [i]))
      addr :: childResults.flatten

def allAddresses (t : PTree) : List Address :=
  allAddressesGo t.size t []

/--
Check if a list of addresses is an antichain:
no two distinct addresses are comparable.
-/

def isAntichainBool (addrs : List Address) : Bool :=
  addrs.mapIdx (fun i a =>
    addrs.mapIdx (fun j b =>
      i == j || !comparableBool a b)
    |>.all id)
  |>.all id

/--
All sublists of a list.
-/
def sublists : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let rest := sublists xs
      rest ++ rest.map (x :: ·)

/--
All admissible cuts of a tree.
An admissible cut is an antichain of valid addresses in the tree.
-/
def allAdmissibleCuts (t : PTree) : List (List Address) :=
  (sublists (allAddresses t)).filter (fun cut =>
    cut.all (fun a => validAddress t a) &&
    isAntichainBool cut)

/--
A single coproduct term: a (Forest, PTree) pair
corresponding to one admissible cut.
-/
def coproductTerm (t : PTree) (cut : List Address) : Forest × PTree :=
  (cut.filterMap (subtreeAt t), remainderGo cut [] t)

/--
The Connes-Kreimer coproduct on a proof tree.

Returns a list of (Forest × PTree) pairs, one per admissible cut.
This is the combinatorial coproduct before lifting to the algebra.

In the full algebraic treatment this lifts to
ForestAlgebra k ⊗[k] ForestAlgebra k.
-/
def coproduct (t : PTree) : List (Forest × PTree) :=
  (allAdmissibleCuts t).map (coproductTerm t)

namespace Syntax
namespace PTree

/-- `[]` is always one of the sublists of a list. -/
theorem nil_mem_sublists {α : Type} (xs : List α) :
    [] ∈ sublists xs := by
  induction xs with
  | nil =>
      simp [sublists]
  | cons x xs ih =>
      simp [sublists, ih]

/-- The empty cut always passes the boolean antichain/validity test. -/
theorem empty_cut_mem_allAdmissibleCuts (t : PTree) :
    [] ∈ allAdmissibleCuts t := by
  unfold allAdmissibleCuts
  refine List.mem_filter.2 ?_
  constructor
  · exact nil_mem_sublists (allAddresses t)
  · unfold isAntichainBool
    simp

/-- If the function ignores the index, `mapIdx` is just `map`. -/
theorem mapIdx_const {α β : Type} (f : α → β) (xs : List α) :
    xs.mapIdx (fun _ x => f x) = xs.map f := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.mapIdx_cons]
      simp [ih]

/-- Mapping `Subtype.val` over `attach.mapIdx` gives back the original list. -/
theorem attach_mapIdx_val_eq (cs : List PTree) :
    cs.attach.mapIdx (fun _ x => x.1) = cs := by
  rw [mapIdx_const (fun x => x.1) cs.attach]
  simp

/--
If the cut is empty, `remainderGo` does nothing.
We prove this by strong induction on tree size.
-/
theorem remainderGo_nil (t : PTree) (addr : Address) :
    remainderGo [] addr t = t := by
  let P : Nat → Prop :=
    fun n => ∀ t : PTree, t.size = n → ∀ addr, remainderGo [] addr t = t

  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih t hsize addr
    cases t with
    | leaf s =>
        simp [remainderGo]
    | node r s cs =>
        simp [remainderGo]
        have hchild :
            ∀ (i : Nat) (x : {x // x ∈ cs}),
              remainderGo [] (addr ++ [i]) x.1 = x.1 := by
          intro i x
          have hlt : x.1.size < (PTree.node r s cs).size := by
            exact child_size_lt_parent (PTree.node r s cs) x.1 (by
              unfold IsImmediateSubtree PTree.children
              exact x.2)
          have hx : P x.1.size := ih x.1.size (by simpa [hsize] using hlt)
          exact hx x.1 rfl (addr ++ [i])
        simpa [hchild] using attach_mapIdx_val_eq cs

  have hstrong : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    exact hP n ih

  exact hstrong t.size t rfl addr

/-- The coproduct term for the empty cut is exactly `([], t)`. -/
theorem coproductTerm_nil (t : PTree) :
    coproductTerm t [] = ([], t) := by
  unfold coproductTerm
  simp [remainderGo_nil]

/-- Sanity check: the empty cut always appears, giving `([], t)`. -/
theorem coproduct_contains_unit_term (t : PTree) :
    ([], t) ∈ coproduct t := by
  unfold coproduct
  apply List.mem_map.2
  refine ⟨[], ?_, ?_⟩
  · exact empty_cut_mem_allAdmissibleCuts t
  · simpa [coproductTerm_nil]

/-- The coproduct is never empty. -/
theorem coproduct_nonempty (t : PTree) :
    0 < (coproduct t).length := by
  exact List.length_pos_of_mem (coproduct_contains_unit_term t)

end PTree

theorem subtreeAt_toTree_is_toTree
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) (a : Address) (u : PTree) :
    subtreeAt (NMMS.toTree d) a = some u →
    ∃ (s' : MultiSequent) (d' : NMMS base s'),
      u = NMMS.toTree d' := by
  induction a generalizing d s u with
  | nil =>
      intro h
      simp [subtreeAt] at h
      exact ⟨s, d, h.symm⟩
  | cons i rest ih =>
      intro h
      cases d with
      | baseAx hb =>
          simp [NMMS.toTree, subtreeAt] at h
      | imp_l d₁ d₂ =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | imp_r d =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | conj_l d =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | conj_r d₁ d₂ =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | disj_l d₁ d₂ =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | disj_r d =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | neg_l d =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | neg_r d =>
          simp [NMMS.toTree, subtreeAt] at h
          obtain ⟨hi, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega

/-! ## Base admissibility and the remainder theorem -/

/--
A cut is base-admissible with respect to a derivation if every sequent
at a cut node is already validated by the base relation.

This ensures that when `remainderGo` replaces a cut subtree with a leaf,
that leaf can be justified as a `baseAx` node — the leaf's sequent is
primitive in the base relation, not merely derived.

The condition is meaningful in the nonmonotonic setting: it says that
the sequents at cut nodes can be treated as primitive assumptions in a
subsequent reasoning step. This corresponds to the nonmonotonic operation
of "cashing out" a subproof as a defeasible assumption — a derived
conclusion becomes a new axiom for further reasoning.
-/
def IsBaseAdmissible (base : BaseRel) (t : PTree)
    (cut : List Address) : Prop :=
  ∀ addr ∈ cut, ∀ u : PTree,
    subtreeAt t addr = some u →
    base u.conclusion.lhs u.conclusion.rhs

/--
A base relation is derivably closed if every sequent derivable from it
is already in the base relation.

This is a fixed-point condition on the base relation: the consequence
operator generated by `NMMS` maps `base` back into itself. In the
semantics of nonmonotonic reasoning, this corresponds to a stable
extension — a set of beliefs that is closed under the inference rules
and cannot be further extended by applying those rules.
-/
def IsDerivablyClosed (base : BaseRel) : Prop :=
  ∀ s : MultiSequent, Nonempty (NMMS base s) →
    base s.lhs s.rhs

/--
If the base relation is derivably closed, then every cut on a genuine
derivation tree is automatically base-admissible.
-/
theorem derivablyClosed_isBaseAdmissible
    {base : BaseRel} (hclosed : IsDerivablyClosed base)
    {s : MultiSequent} (d : NMMS base s) (cut : List Address) :
    IsBaseAdmissible base (NMMS.toTree d) cut := by
  intro addr _ u hsubt
  obtain ⟨s', d', hd'⟩ := subtreeAt_toTree_is_toTree d addr u hsubt
  have hu : u.conclusion = s' := by
    simpa [hd'] using toTree_conclusion d'
  rw [hu]
  apply hclosed
  exact ⟨d'⟩

/-! ## Cut restriction and the remainder theorem -/

/--
Restrict a cut to the subtree rooted at child index `i`,
stripping the leading index from each address.

For example, if the cut contains `[0, 1]` and `[1, 0]`,
then `restrictCut cut 0 = [[1]]` and `restrictCut cut 1 = [[0]]`.
-/
def restrictCut (cut : List Address) (i : Nat) : List Address :=
  cut.filterMap (fun addr =>
    match addr with
    | [] => none
    | j :: rest => if j = i then some rest else none)

/--
Restrict a cut by an arbitrary address prefix.
-/
def restrictCutAt : List Address → Address → List Address
  | cut, [] => cut
  | cut, i :: rest => restrictCutAt (restrictCut cut i) rest

@[simp] theorem mem_restrictCut_iff
    {cut : List Address} {i : Nat} {addr : Address} :
    addr ∈ restrictCut cut i ↔ (i :: addr) ∈ cut := by
  unfold restrictCut
  constructor
  · intro h
    simp [List.mem_filterMap] at h
    rcases h with ⟨a, ha, hm⟩
    cases a with
    | nil =>
        simp at hm
    | cons j rest =>
        by_cases hji : j = i
        · simp [hji] at hm
          subst hji
          subst hm
          simpa using ha
        · simp [hji] at hm
  · intro h
    simp [List.mem_filterMap]
    exact ⟨i :: addr, h, by simp⟩

@[simp] theorem mem_restrictCutAt_iff
    {cut : List Address} {pfx addr : Address} :
    addr ∈ restrictCutAt cut pfx ↔ pfx ++ addr ∈ cut := by
  induction pfx generalizing cut with
  | nil =>
      simp [restrictCutAt]
  | cons i rest ih =>
      simp [restrictCutAt, ih, List.cons_append]

@[simp] theorem nil_mem_restrictCut_iff
    {cut : List Address} {i : Nat} :
    [] ∈ restrictCut cut i ↔ [i] ∈ cut := by
  simpa using (mem_restrictCut_iff (cut := cut) (i := i) (addr := []))

@[simp] theorem nil_mem_restrictCutAt_iff
    {cut : List Address} {pfx : Address} :
    [] ∈ restrictCutAt cut pfx ↔ pfx ∈ cut := by
  simpa using
    (mem_restrictCutAt_iff (cut := cut) (pfx := pfx) (addr := []))

/--
Base admissibility is preserved when we restrict a cut to a subtree.

If the original cut is base-admissible for the parent node,
then the restricted cut is base-admissible for the `i`-th child.
-/
theorem isBaseAdmissible_restrictCut
    {base : BaseRel} {s : MultiSequent} {r : RuleTag}
    {cs : List PTree} {cut : List Address}
    (i : Nat) (hi : i < cs.length)
    (hbase : IsBaseAdmissible base (PTree.node r s cs) cut) :
    IsBaseAdmissible base cs[i] (restrictCut cut i) := by
  intro addr haddr u hsubt
  apply hbase (i :: addr)
  · simpa using haddr
  · simp [PTree.subtreeAt, hi, hsubt]

/--
Congruence for the internal accumulator-based worker used by `List.mapIdx`.
-/
private theorem mapIdx_go_congr'
    {α β : Type _} :
    ∀ (xs : List α) (acc : Array β) (f g : Nat → α → β),
      (∀ i x, x ∈ xs → f (acc.size + i) x = g (acc.size + i) x) →
      List.mapIdx.go f xs acc = List.mapIdx.go g xs acc
  | [], acc, f, g, h => by
      simp [List.mapIdx.go]
  | x :: xs, acc, f, g, h => by
      have hx : f acc.size x = g acc.size x := by
        simpa using h 0 x (by simp)
      simp [List.mapIdx.go, hx]
      apply mapIdx_go_congr' xs (acc.push (g acc.size x)) f g
      intro i y hy
      have hy' : f (acc.size + (i + 1)) y = g (acc.size + (i + 1)) y := by
        exact h (i + 1) y (by simp [hy])
      simpa [Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy'

#check @List.mapIdx
#check @List.attach

/--
A small congruence lemma for `List.mapIdx`.
-/
private theorem mapIdx_congr'
    {α β : Type _} (xs : List α) (f g : Nat → α → β)
    (h : ∀ i x, x ∈ xs → f i x = g i x) :
    xs.mapIdx f = xs.mapIdx g := by
  simpa [List.mapIdx] using
    mapIdx_go_congr' xs #[] f g (by
      intro i x hx
      simpa using h i x hx)

/--
General form of the cut-restriction lemma for `remainderGo`.

Starting `remainderGo` on `t` with the cut restricted to `pfx`
and current address `addr` is the same as starting with the original cut
at address `pfx ++ addr`.
-/
theorem remainderGo_restrictCutAt_eq
    (cut : List Address) (pfx addr : Address) (t : PTree) :
    remainderGo (restrictCutAt cut pfx) addr t =
    remainderGo cut (pfx ++ addr) t := by
  cases t with
  | leaf s =>
      simp [remainderGo]
  | node r s cs =>
      by_cases hcut : addr ∈ restrictCutAt cut pfx
      · have hcut' : pfx ++ addr ∈ cut := by
          simpa using hcut
        simp [remainderGo, hcut, hcut']
      · have hcut' : pfx ++ addr ∉ cut := by
          intro hmem
          apply hcut
          simpa using hmem
        simp [remainderGo, hcut, hcut']
        have hmaps :
            List.mapIdx
              (fun i x => remainderGo (restrictCutAt cut pfx) (addr ++ [i]) x.1)
              cs.attach =
            List.mapIdx
              (fun i x => remainderGo cut (pfx ++ (addr ++ [i])) x.1)
              cs.attach := by
          apply mapIdx_congr'
          intro i x hx
          simpa [List.append_assoc] using
            remainderGo_restrictCutAt_eq cut pfx (addr ++ [i]) x.1
        exact hmaps
termination_by t.size
decreasing_by
  have hlt : x.1.size < (PTree.node r s cs).size := by
    apply child_size_lt_parent (PTree.node r s cs) x.1
    unfold IsImmediateSubtree PTree.children
    simpa using x.2
  simpa [PTree.size] using hlt

/--
`remainderGo` with a restricted cut at child `i` equals
`remainderGo` with the original cut starting at address `[i]`.
-/
theorem remainderGo_restrictCut_eq
    (cut : List Address) (i : Nat) (t : PTree) :
    remainderGo (restrictCut cut i) [] t =
    remainderGo cut [i] t := by
  simpa [restrictCutAt] using
    remainderGo_restrictCutAt_eq cut [i] [] t

private theorem mapIdx_attach_singleton (f : Nat → PTree → PTree) (t : PTree) :
    List.mapIdx (fun i (x : {x // x ∈ [t]}) => f i x.1) [t].attach = [f 0 t] := by
  rfl

private theorem mapIdx_attach_pair (f : Nat → PTree → PTree) (t u : PTree) :
    List.mapIdx (fun i (x : {x // x ∈ [t, u]}) => f i x.1) [t, u].attach = [f 0 t, f 1 u] := by
  rfl

theorem remainderGo_toTree_is_toTree
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) (cut : List Address)
    (hbase : IsBaseAdmissible base (NMMS.toTree d) cut) :
    ∃ d' : NMMS base s,
      remainderGo cut [] (NMMS.toTree d) = NMMS.toTree d' := by
  by_cases hroot : [] ∈ cut
  · have hb : base s.lhs s.rhs := by
      have hsubt : subtreeAt (NMMS.toTree d) [] =
          some (NMMS.toTree d) := by
        simp [subtreeAt]
      have hconc := toTree_conclusion d
      have := hbase [] hroot (NMMS.toTree d) hsubt
      rwa [hconc] at this
    have hrem : remainderGo cut [] (NMMS.toTree d) =
        PTree.leaf s := by
      cases d with
      | baseAx h     => simp [NMMS.toTree, remainderGo, hroot]
      | imp_l d₁ d₂  => simp [NMMS.toTree, remainderGo, hroot]
      | imp_r d      => simp [NMMS.toTree, remainderGo, hroot]
      | conj_l d     => simp [NMMS.toTree, remainderGo, hroot]
      | conj_r d₁ d₂ => simp [NMMS.toTree, remainderGo, hroot]
      | disj_l d₁ d₂ => simp [NMMS.toTree, remainderGo, hroot]
      | disj_r d     => simp [NMMS.toTree, remainderGo, hroot]
      | neg_l d      => simp [NMMS.toTree, remainderGo, hroot]
      | neg_r d      => simp [NMMS.toTree, remainderGo, hroot]
    exact ⟨NMMS.baseAx hb, by rw [hrem]; simp [NMMS.toTree]⟩
  · cases d with
    | baseAx h =>
        simp [NMMS.toTree, remainderGo, hroot]
        exact ⟨NMMS.baseAx h, rfl⟩
    | imp_l d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (restrictCut cut 1) hbase₂
        refine ⟨NMMS.imp_l d₁' d₂', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | imp_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (restrictCut cut 0) hbase₁
        refine ⟨NMMS.imp_r d', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | conj_l d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (restrictCut cut 0) hbase₁
        refine ⟨NMMS.conj_l d', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | conj_r d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (restrictCut cut 1) hbase₂
        refine ⟨NMMS.conj_r d₁' d₂', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | disj_l d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (restrictCut cut 1) hbase₂
        refine ⟨NMMS.disj_l d₁' d₂', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | disj_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (restrictCut cut 0) hbase₁
        refine ⟨NMMS.disj_r d', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | neg_l d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (restrictCut cut 0) hbase₁
        refine ⟨NMMS.neg_l d', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | neg_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (restrictCut cut 0) hbase₁
        refine ⟨NMMS.neg_r d', ?_⟩
        simp only [NMMS.toTree, remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

/--
Every component appearing in the Connes-Kreimer coproduct of a proof tree `toTree d` corresponds to a genuine subderivation of `d`, provided the cut is base-admissible.
-/
theorem coproduct_terms_are_subderivations
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s)
    (hbase : ∀ cut, IsBaseAdmissible base (NMMS.toTree d) cut) :
    ∀ (f : Forest) (r : PTree),
      (f, r) ∈ coproduct (NMMS.toTree d) →
      (∃ (s' : MultiSequent) (d' : NMMS base s'),
        r = NMMS.toTree d') ∧
      (∀ t ∈ f, ∃ (s'' : MultiSequent) (d'' : NMMS base s''),
        t = NMMS.toTree d'') := by
  intro f r hmem
  unfold coproduct at hmem
  simp [List.mem_map] at hmem
  obtain ⟨cut, hcut, hterm⟩ := hmem
  unfold coproductTerm at hterm
  obtain ⟨hf, hr⟩ := Prod.mk.inj hterm
  constructor
  · rw [← hr]
    obtain ⟨d', hd'⟩ := remainderGo_toTree_is_toTree d cut (hbase cut)
    exact ⟨s, d', by simpa [eq_comm] using hd'⟩
  · intro t ht
    rw [← hf] at ht
    simp [List.mem_filterMap] at ht
    obtain ⟨addr, haddr, hsubt⟩ := ht
    exact subtreeAt_toTree_is_toTree d addr t hsubt

open scoped TensorProduct
open Classical

/-! ## Hopf algebra carrier (commutative CK-style) -/

abbrev ProofForest := Multiset PTree
abbrev HopfCarrier := AddMonoidAlgebra ℤ (Multiset PTree)

noncomputable instance : Ring (HopfCarrier ⊗[ℤ] HopfCarrier) :=
  Algebra.TensorProduct.instRing

noncomputable instance : Semiring (HopfCarrier ⊗[ℤ] HopfCarrier) :=
  inferInstanceAs (Semiring (HopfCarrier ⊗[ℤ] HopfCarrier))

def forestToProofForest (f : Forest) : ProofForest :=
  (f : Multiset PTree)

noncomputable def treeGen (t : PTree) : HopfCarrier :=
  Finsupp.single ({t} : Multiset PTree) 1

noncomputable def forestMon (f : Forest) : HopfCarrier :=
  Finsupp.single (forestToProofForest f) 1

noncomputable def oneForest : HopfCarrier :=
  forestMon []

noncomputable def deltaTree (t : PTree) :
    HopfCarrier ⊗[ℤ] HopfCarrier :=
  (coproduct t).foldr
    (fun fr acc =>
      let (f, r) := fr
      (forestMon f ⊗ₜ[ℤ] treeGen r) + acc)
    0

noncomputable def epsilonWord (f : Multiset PTree) : ℤ :=
  if f = 0 then 1 else 0

noncomputable def epsilon : HopfCarrier →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ epsilonWord

open TensorProduct in

#check (inferInstance : AddCommMonoid ProofForest)
#check (inferInstance : CommRing HopfCarrier)
#check (inferInstance : Algebra ℤ HopfCarrier)
#check (inferInstance : Ring (HopfCarrier ⊗[ℤ] HopfCarrier))
#check (inferInstance : Semiring (HopfCarrier ⊗[ℤ] HopfCarrier))

/-! ## Coproduct on forests and linear extension -/

noncomputable def deltaForest (f : Forest) : HopfCarrier ⊗[ℤ] HopfCarrier :=
  f.foldr (fun t acc => deltaTree t * acc) 1

@[simp] theorem deltaForest_nil :
    deltaForest [] = 1 := by
  simp [deltaForest]

@[simp] theorem deltaForest_cons (t : PTree) (f : Forest) :
    deltaForest (t :: f) = deltaTree t * deltaForest f := by
  simp [deltaForest]

@[simp] theorem deltaForest_singleton (t : PTree) :
    deltaForest [t] = deltaTree t := by
  simp [deltaForest]
  exact mul_one (deltaTree t)

noncomputable def delta : HopfCarrier →ₗ[ℤ] (HopfCarrier ⊗[ℤ] HopfCarrier) :=
  Finsupp.linearCombination ℤ (fun f : Multiset PTree => deltaForest f.toList)

@[simp] theorem epsilon_treeGen (t : PTree) :
    epsilon (treeGen t) = 0 := by
  change (Finsupp.linearCombination ℤ epsilonWord) (Finsupp.single ({t} : Multiset PTree) 1) = 0
  simp [epsilonWord, Multiset.singleton_ne_zero]

@[simp] theorem epsilon_oneForest :
    epsilon oneForest = 1 := by
  change (Finsupp.linearCombination ℤ epsilonWord) (Finsupp.single (0 : Multiset PTree) 1) = 1
  simp [epsilonWord]

/-! ## Counit axioms -/

open scoped TensorProduct

lemma epsilon_single_empty :
    (Finsupp.linearCombination ℤ epsilonWord)
      (Finsupp.single (0 : Multiset PTree) 1) = 1 := by
  simp [Finsupp.linearCombination_single, epsilonWord]

lemma epsilon_single_nonempty (f : Forest) (h : f ≠ []) :
    (Finsupp.linearCombination ℤ epsilonWord)
      (Finsupp.single (forestToProofForest f) 1) = 0 := by
  simp [Finsupp.linearCombination_single, epsilonWord, forestToProofForest, h]

@[simp] lemma epsilon_forestMon (f : Forest) :
    epsilon (forestMon f) = if f = [] then 1 else 0 := by
  by_cases h : f = []
  · subst h
    change (Finsupp.linearCombination ℤ epsilonWord)
      (Finsupp.single (0 : Multiset PTree) 1) = 1
    exact epsilon_single_empty
  · simp [h]
    change (Finsupp.linearCombination ℤ epsilonWord)
      (Finsupp.single (forestToProofForest f) 1) = 0
    exact epsilon_single_nonempty f h

lemma epsilon_forestMon_eq_one_iff (f : Forest) :
    epsilon (forestMon f) = 1 ↔ f = [] := by
  by_cases h : f = []
  · subst h
    simp
  · simp [epsilon_forestMon, h]

private theorem mapIdx_go_eq_map_append
    {α β : Type _} (f : α → β) :
    ∀ (xs : List α) (acc : Array β),
      List.mapIdx.go (fun _ x => f x) xs acc = acc.toList ++ xs.map f := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp [List.mapIdx.go]
  | cons x xs ih =>
      intro acc
      simp only [List.mapIdx.go, List.map]
      simpa [List.append_assoc] using ih (acc.push (f x))

private theorem mapIdx_eq_map
    {α β : Type _} (xs : List α) (f : α → β) :
    List.mapIdx (fun _ x => f x) xs = xs.map f := by
  simpa [List.mapIdx] using
    mapIdx_go_eq_map_append f xs (#[] : Array β)

private theorem map_attach_val (cs : List PTree) :
    cs.attach.map (fun x => x.1) = cs := by
  induction cs with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [ih]

private theorem mapIdx_attach_val (cs : List PTree) :
    List.mapIdx (fun _ (x : {x // x ∈ cs}) => x.1) cs.attach = cs := by
  calc
    List.mapIdx (fun _ (x : {x // x ∈ cs}) => x.1) cs.attach
        = cs.attach.map (fun x => x.1) := by
            simpa using mapIdx_eq_map cs.attach (fun x : {x // x ∈ cs} => x.1)
    _ = cs := map_attach_val cs

@[simp] theorem remainderGo_nil (addr : Address) (t : PTree) :
    remainderGo [] addr t = t := by
  have hmain :
      ∀ n : Nat, ∀ t : PTree, t.size = n → ∀ addr : Address,
        remainderGo [] addr t = t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t hsize addr
        cases t with
        | leaf s =>
            simp [remainderGo]
        | node r s cs =>
            have hcut : addr ∉ ([] : List Address) := by
              simp
            simp [remainderGo, hcut]
            have hmap :
                List.mapIdx
                  (fun i x => remainderGo [] (addr ++ [i]) x.1)
                  cs.attach =
                List.mapIdx
                  (fun _ x => x.1)
                  cs.attach := by
              apply mapIdx_congr' cs.attach
                (fun i x => remainderGo [] (addr ++ [i]) x.1)
                (fun _ x => x.1)
              intro i x hx
              have hlt_node : x.1.size < (PTree.node r s cs).size := by
                apply child_size_lt_parent (PTree.node r s cs) x.1
                unfold IsImmediateSubtree PTree.children
                simpa using x.2
              have hlt : x.1.size < n := by
                simpa [hsize] using hlt_node
              simpa using ih x.1.size hlt x.1 rfl (addr ++ [i])
            have hmaps :
                List.mapIdx
                  (fun i x => remainderGo [] (addr ++ [i]) x.1)
                  cs.attach = cs := by
              calc
                List.mapIdx
                  (fun i x => remainderGo [] (addr ++ [i]) x.1)
                  cs.attach
                    =
                List.mapIdx
                  (fun _ x => x.1)
                  cs.attach := hmap
                _ = cs := mapIdx_attach_val cs
            simpa [hmaps]
  exact hmain t.size t rfl addr

@[simp] lemma coproductTerm_fst_nil (t : PTree) :
    (coproductTerm t []).1 = [] := by
  simp [coproductTerm]

@[simp] lemma coproductTerm_nil (t : PTree) :
    coproductTerm t [] = ([], t) := by
  simp [coproductTerm, remainderGo_nil]

@[simp] lemma coproductTerm_snd_nil (t : PTree) :
    (coproductTerm t []).2 = t := by
  simp [coproductTerm, remainderGo_nil]

lemma coproductTerm_fst_eq_nil_iff
    (t : PTree) (cut : List Address)
    (hcut : cut ∈ allAdmissibleCuts t) :
    (coproductTerm t cut).1 = [] ↔ cut = [] := by
  unfold coproductTerm
  constructor
  · intro h
    cases cut with
    | nil =>
        rfl
    | cons a cut =>
        -- from admissibility, a is valid
        have hvalid :
            ValidAddress t a := by
          -- extract from filter
          have hmem := List.mem_filter.mp hcut
          have hcond := hmem.2
          -- manually unpack the boolean
          rw [Bool.and_eq_true] at hcond
          have hall : (a :: cut).all (fun a => validAddress t a) = true := hcond.1
          have := List.all_eq_true.mp hall
          exact this a (by simp)

        -- get actual subtree
        rcases (valid_iff_exists_subtree t a).mp hvalid with ⟨u, hu⟩

        -- contradiction: nonempty list = []
        simp [List.filterMap, hu] at h
  · intro h
    subst h
    simp

private theorem sublists_eq_nil_cons_not_mem {α : Type} (xs : List α) :
    ∃ rest, sublists xs = [] :: rest ∧ [] ∉ rest := by
  induction xs with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [sublists]
      · simp
  | cons x xs ih =>
      rcases ih with ⟨rest, hrest, hnot⟩
      refine ⟨rest ++ ([] :: rest).map (fun ys => x :: ys), ?_, ?_⟩
      · simp [sublists, hrest, List.append_assoc]
      · intro hmem
        rw [List.mem_append] at hmem
        cases hmem with
        | inl hmem_rest =>
            exact hnot hmem_rest
        | inr hmem_map =>
            rw [List.mem_map] at hmem_map
            rcases hmem_map with ⟨ys, hy, hEq⟩
            cases hEq

private theorem allAdmissibleCuts_eq_nil_cons_not_mem (t : PTree) :
    ∃ rest, allAdmissibleCuts t = [] :: rest ∧ [] ∉ rest := by
  rcases sublists_eq_nil_cons_not_mem (allAddresses t) with ⟨rest, hrest, hnot⟩
  refine ⟨rest.filter (fun cut =>
      cut.all (fun a => validAddress t a) &&
      isAntichainBool cut), ?_, ?_⟩
  · unfold allAdmissibleCuts
    rw [hrest]
    simp [isAntichainBool]
  · intro hmem
    apply hnot
    exact List.mem_of_mem_filter hmem

private theorem foldr_add_eq_zero
    {α β : Type _} [AddMonoid β] (f : α → β) :
    ∀ (L : List α), (∀ x, x ∈ L → f x = 0) →
      L.foldr (fun x acc => f x + acc) 0 = 0 := by
  intro L hL
  induction L with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x = 0 := hL x (by simp)
      have hxs : ∀ y, y ∈ xs → f y = 0 := by
        intro y hy
        exact hL y (by simp [hy])
      simp [hx, ih hxs]

/-- Left counit: (ε ⊗ id) ∘ Δ = id on generators -/
theorem counit_left (t : PTree) :
    (TensorProduct.lid ℤ HopfCarrier)
      ((LinearMap.rTensor HopfCarrier epsilon) (deltaTree t)) =
    treeGen t := by
  classical
  rcases allAdmissibleCuts_eq_nil_cons_not_mem t with ⟨rest, hcuts, hnot⟩
  unfold deltaTree coproduct
  rw [hcuts]
  simp only [List.map_cons, List.foldr_cons, map_add,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

  have hhead :
      epsilon (forestMon (coproductTerm t []).1) • treeGen (coproductTerm t []).2 =
      treeGen t := by
    simpa [coproductTerm_nil] using (one_smul ℤ (treeGen t))

  have hzero :
      ∀ cut, cut ∈ rest →
        epsilon (forestMon (coproductTerm t cut).1) • treeGen (coproductTerm t cut).2 = 0 := by
    intro cut hmem
    have hmem' : cut ∈ allAdmissibleCuts t := by
      rw [hcuts]
      simp [hmem]
    have hne : cut ≠ [] := by
      intro hc
      exact hnot (hc ▸ hmem)
    have hfstne : (coproductTerm t cut).1 ≠ [] := by
      intro hf
      exact hne ((coproductTerm_fst_eq_nil_iff t cut hmem').mp hf)
    simp [epsilon_forestMon, hfstne]

  have htail_aux :
      ∀ L : List (List Address),
        (∀ cut ∈ L,
          epsilon (forestMon (coproductTerm t cut).1) • treeGen (coproductTerm t cut).2 = 0) →
        (TensorProduct.lid ℤ HopfCarrier)
          ((LinearMap.rTensor HopfCarrier epsilon)
            (List.foldr (fun fr acc => forestMon fr.1 ⊗ₜ[ℤ] treeGen fr.2 + acc) 0
              (List.map (coproductTerm t) L))) = 0 := by
    intro L hL
    induction L with
    | nil =>
        simp
    | cons cut rest ih =>
        simp only [List.map_cons, List.foldr_cons, map_add,
          LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        have hz :
            epsilon (forestMon (coproductTerm t cut).1) •
              treeGen (coproductTerm t cut).2 = 0 := by
          exact hL cut (by simp)
        have hz' :
            (if (coproductTerm t cut).1 = [] then
               1 • treeGen (coproductTerm t cut).2
             else
               0 • treeGen (coproductTerm t cut).2) = 0 := by
          simpa [epsilon_forestMon] using hz
        have hrest :
            ∀ cut' ∈ rest,
              epsilon (forestMon (coproductTerm t cut').1) • treeGen (coproductTerm t cut').2 = 0 := by
          intro cut' hmem
          exact hL cut' (by simp [hmem])
        have ih' :
            (TensorProduct.lid ℤ HopfCarrier)
              ((LinearMap.rTensor HopfCarrier epsilon)
                (List.foldr (fun fr acc => forestMon fr.1 ⊗ₜ[ℤ] treeGen fr.2 + acc) 0
                  (List.map (coproductTerm t) rest))) = 0 := by
          exact ih hrest
        simpa [hz', ih']

  have htail' :
      (TensorProduct.lid ℤ HopfCarrier)
        ((LinearMap.rTensor HopfCarrier epsilon)
          (List.foldr (fun fr acc => forestMon fr.1 ⊗ₜ[ℤ] treeGen fr.2 + acc) 0
            (List.map (coproductTerm t) rest))) = 0 := by
    apply htail_aux rest
    intro cut hmem
    exact hzero cut hmem

  calc
    epsilon (forestMon (coproductTerm t []).1) • treeGen (coproductTerm t []).2 +
        (TensorProduct.lid ℤ HopfCarrier)
          ((LinearMap.rTensor HopfCarrier epsilon)
            (List.foldr (fun fr acc => forestMon fr.1 ⊗ₜ[ℤ] treeGen fr.2 + acc) 0
              (List.map (coproductTerm t) rest)))
        =
      treeGen t + 0 := by rw [hhead, htail']
    _ = treeGen t := by simp


end Syntax
