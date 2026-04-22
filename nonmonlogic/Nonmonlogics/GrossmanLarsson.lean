import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Finsupp.Basic

--#check Finsupp.sum
--#check Finsupp.linearCombination
namespace Syntax

universe u

/-! ## Atomic symbols and formulas -/

inductive Atomic : Type
| Int : Atomic
| String : Atomic
deriving DecidableEq, Repr

--falsum here is our "incompatibility detector"
--do not yet assume anything re A, B, C ⊢ ⊥ or
-- ⊢ A ∧ B ∧ C ⇒ ⊥ , indeed we don't
-- want to assume Deduction Thm for ⇒ at all
-- I think! think of our logical vocab as unconstrained,
-- defining only trees with arities and types?
-- almost like an AST where semantics come from base consequence relation
inductive MyProp : Type u
| atom : Atomic → MyProp
| falsum : MyProp
| imp  : MyProp → MyProp → MyProp
| conj : MyProp → MyProp → MyProp
| disj : MyProp → MyProp → MyProp
| neg  : MyProp → MyProp
| mon  : MyProp → MyProp  -- monotonicity modality: M A holds in all context extensions
deriving DecidableEq, Repr

notation "⊥" => MyProp.falsum

infixr:60 " ⇒ " => MyProp.imp
infixr:55 " & " => MyProp.conj
infixr:50 " ∨ " => MyProp.disj
prefix:max "¬" => MyProp.neg

/-! ## Multi-succedent sequents -/

structure MultiSequent : Type u where
  lhs : Multiset MyProp
  rhs : Multiset MyProp
deriving DecidableEq

notation:55 Γ " ∣∼ " Δ => MultiSequent.mk Γ Δ

/-! ## Base relation and derivations -/

/-- The prelogical fragment consists only of atoms and the incompatibility marker. -/
def IsBaseFormula : MyProp → Prop
| MyProp.atom _   => True
| MyProp.falsum   => True
| _               => False

/-- A multiset lies in the prelogical fragment when all of its formulas do. -/
def IsBaseMultiset (Γ : Multiset MyProp) : Prop :=
  ∀ p, p ∈ Γ → IsBaseFormula p

/--
Primitive consequence may only hold on the prelogical fragment, but we package it
as a callable relation on multisets of `MyProp` so the downstream derivation and
tree machinery can remain unchanged.
-/
structure BaseRel where
  rel : Multiset MyProp → Multiset MyProp → Prop
  lhs_base : ∀ {Γ Θ}, rel Γ Θ → IsBaseMultiset Γ
  rhs_base : ∀ {Γ Θ}, rel Γ Θ → IsBaseMultiset Θ

instance : CoeFun BaseRel (fun _ => Multiset MyProp → Multiset MyProp → Prop) where
  coe b := b.rel

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

/-! ## Plain proof trees -/

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

inductive PTree : Type where
| leaf : MultiSequent → PTree
| node : RuleTag → MultiSequent → List PTree → PTree

open Classical
noncomputable instance : DecidableEq PTree := Classical.decEq _

abbrev Forest := List PTree
abbrev Address := List Nat
/-- Addresses serve as root-to-node paths in a proof tree. -/
abbrev Path := Address

namespace PTree

def conclusion : PTree → MultiSequent
| leaf s      => s
| node _ s _  => s

def size : PTree → Nat
| leaf _      => 1
| node _ _ cs => 1 + cs.foldr (fun t n => size t + n) 0

def height : PTree → Nat
| leaf _      => 1
| node _ _ [] => 1
| node _ _ cs => 1 + cs.foldr (fun t n => max (height t) n) 0

def children : PTree → List PTree
| leaf _      => []
| node _ _ cs => cs

def subtrees : PTree → List PTree
| t@(leaf _)      => [t]
| t@(node _ _ cs) => t :: (cs.flatMap subtrees)

def rootRule? : PTree → Option RuleTag
| leaf _      => none
| node r _ _  => some r

def rootChildren : PTree → Forest
| leaf _      => []
| node _ _ cs => cs

/-- Leaves are the endpoints of proof trees. -/
def IsLeaf : PTree → Prop
| leaf _      => True
| node _ _ _  => False

/-- Smullyan-style synonym for a leaf/end node. -/
abbrev IsEndPoint : PTree → Prop := IsLeaf

/-- A simple point has exactly one immediate child. -/
def IsSimplePoint : PTree → Prop
| leaf _      => False
| node _ _ cs => cs.length = 1

/-- A junction point has at least two immediate children. -/
def IsJunctionPoint : PTree → Prop
| leaf _      => False
| node _ _ cs => 2 ≤ cs.length

/-- The left child of a node, when present. -/
def leftChild? : PTree → Option PTree
| leaf _         => none
| node _ _ []    => none
| node _ _ (c::_) => some c

/-- The right child of a node, when present. -/
def rightChild? : PTree → Option PTree
| leaf _            => none
| node _ _ (_::c::_) => some c
| node _ _ _        => none

/--
Dyadic proof trees: every node has at most two children, and every child
subtree is itself dyadic.
-/
def IsDyadic : PTree → Prop
| leaf _      => True
| node _ _ cs => cs.length ≤ 2 ∧ ∀ c, c ∈ cs → IsDyadic c

@[simp] theorem isLeaf_leaf (s : MultiSequent) :
    IsLeaf (leaf s) := by
  trivial

@[simp] theorem not_isLeaf_node (r : RuleTag) (s : MultiSequent) (cs : List PTree) :
    ¬ IsLeaf (node r s cs) := by
  simp [IsLeaf]

@[simp] theorem leftChild?_leaf (s : MultiSequent) :
    leftChild? (leaf s) = none := by
  rfl

@[simp] theorem rightChild?_leaf (s : MultiSequent) :
    rightChild? (leaf s) = none := by
  rfl

@[simp] theorem isDyadic_leaf (s : MultiSequent) :
    IsDyadic (leaf s) := by
  simp [IsDyadic]

end PTree

/-! ## Forgetful map from derivations to proof trees -/

namespace NMMS

def toTree {base : BaseRel} {s : MultiSequent} (d : NMMS base s) : PTree :=
  match d with
  | @NMMS.baseAx _ Γ Θ _ =>
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

theorem toTree_conclusion {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    (NMMS.toTree d).conclusion = s := by
  induction d <;> rfl

/-- Proof trees coming from `NMMS` derivations are dyadic. -/
theorem toTree_isDyadic {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    PTree.IsDyadic (NMMS.toTree d) := by
  induction d <;> simp [NMMS.toTree, PTree.IsDyadic, *]

def IsImmediateSubtree (t u : PTree) : Prop :=
  u ∈ t.children

theorem immediate_subtree_correspondence
    {base : BaseRel} {s : MultiSequent} (d : NMMS base s) :
    ∀ u, IsImmediateSubtree (NMMS.toTree d) u →
      ∃ s' : MultiSequent, u.conclusion = s' := by
  intro u _
  exact ⟨u.conclusion, rfl⟩

theorem subtree_correspondence
    {base : BaseRel} {s : MultiSequent} (d : NMMS base s) :
    ∀ u, u ∈ (NMMS.toTree d).subtrees →
      ∃ s' : MultiSequent, u.conclusion = s' := by
  intro u _
  exact ⟨u.conclusion, rfl⟩

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
      | nil =>
          simp at h
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

/-! ## Subtree navigation and address machinery -/

namespace PTree

def subtreeAt : PTree → Address → Option PTree
  | t, [] => some t
  | leaf _, _ :: _ => none
  | node _ _ cs, i :: rest =>
      if h : i < cs.length then
        subtreeAt (cs[i]) rest
      else
        none

def validAddress (t : PTree) (a : Address) : Bool :=
  Option.isSome (subtreeAt t a)

def ValidAddress (t : PTree) (a : Address) : Prop :=
  validAddress t a = true

def isAncestorOf (a b : Address) : Prop :=
  ∃ c : Address, b = a ++ c

def comparable (a b : Address) : Prop :=
  isAncestorOf a b ∨ isAncestorOf b a

/-- Address-level domination relation on nodes of a proof tree. -/
abbrev Dominates (a b : Address) : Prop := isAncestorOf a b

/-- Alias for `Dominates`, matching standard rooted-tree terminology. -/
abbrev AncestorOf (a b : Address) : Prop := Dominates a b

/-- Strict domination means domination by a proper extension of addresses. -/
def StrictDominates (a b : Address) : Prop :=
  ∃ c : Address, c ≠ [] ∧ b = a ++ c

/-- Address-level incomparability. -/
def Incomparable (a b : Address) : Prop :=
  ¬ comparable a b

/--
`z` separates the incomparable addresses `a` and `b` if they split
immediately below `z` into two different child directions.
-/
def IsSeparator (z a b : Address) : Prop :=
  ∃ i j : Nat, ∃ ra rb : Address,
    i ≠ j ∧ a = z ++ i :: ra ∧ b = z ++ j :: rb

theorem subtreeAt_root (t : PTree) :
    subtreeAt t [] = some t := by
  rfl

theorem validAddress_root (t : PTree) :
    validAddress t [] = true := by
  simp [validAddress, subtreeAt]

theorem subtreeAt_some_implies_valid
    (t u : PTree) (a : Address)
    (h : subtreeAt t a = some u) :
    ValidAddress t a := by
  unfold ValidAddress validAddress
  simp [h]

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
        exact ⟨u, rfl⟩
  · intro h
    rcases h with ⟨u, hu⟩
    simp [hu]

theorem isAncestorOf_refl (a : Address) :
    isAncestorOf a a := by
  refine ⟨[], ?_⟩
  simp

theorem comparable_refl (a : Address) :
    comparable a a := by
  exact Or.inl (isAncestorOf_refl a)

theorem root_isAncestorOf (a : Address) :
    isAncestorOf [] a := by
  refine ⟨a, ?_⟩
  simp

theorem comparable_of_isAncestorOf {a b : Address}
    (h : isAncestorOf a b) :
    comparable a b := by
  exact Or.inl h

theorem dominates_refl (a : Address) :
    Dominates a a := by
  exact isAncestorOf_refl a

theorem comparable_of_dominates {a b : Address}
    (h : Dominates a b) :
    comparable a b := by
  exact comparable_of_isAncestorOf h

theorem comparable_symm {a b : Address}
    (h : comparable a b) :
    comparable b a := by
  cases h with
  | inl hab => exact Or.inr hab
  | inr hba => exact Or.inl hba

theorem incomparable_symm {a b : Address}
    (h : Incomparable a b) :
    Incomparable b a := by
  intro h'
  exact h (comparable_symm h')

theorem address_append_left_cancel
    {s t u : Address}
    (h : s ++ t = s ++ u) :
    t = u := by
  rw [List.append_cancel_left_eq] at h
  exact h

theorem IsSeparator.strictDominates_left
    {z a b : Address}
    (h : IsSeparator z a b) :
    StrictDominates z a := by
  rcases h with ⟨i, j, ra, rb, _, ha, _⟩
  refine ⟨i :: ra, by simp, ?_⟩
  simpa [ha, List.append_assoc]

theorem IsSeparator.strictDominates_right
    {z a b : Address}
    (h : IsSeparator z a b) :
    StrictDominates z b := by
  rcases h with ⟨i, j, ra, rb, _, _, hb⟩
  refine ⟨j :: rb, by simp, ?_⟩
  simpa [hb, List.append_assoc]

theorem IsSeparator.incomparable
    {z a b : Address}
    (h : IsSeparator z a b) :
    Incomparable a b := by
  intro hcomp
  rcases h with ⟨i, j, ra, rb, hij, ha, hb⟩
  cases hcomp with
  | inl hab =>
      rcases hab with ⟨c, hbc⟩
      rw [ha, hb] at hbc
      have hbc' : z ++ (j :: rb) = z ++ ((i :: ra) ++ c) := by
        simpa [List.append_assoc] using hbc
      rw [List.append_cancel_left_eq] at hbc'
      have hcancel : j :: rb = (i :: ra) ++ c := by
        exact hbc'
      cases c with
      | nil =>
          simp at hcancel
          exact hij hcancel.1.symm
      | cons k cs =>
          simp at hcancel
          exact hij hcancel.1.symm
  | inr hba =>
      rcases hba with ⟨c, hac⟩
      rw [ha, hb] at hac
      have hac' : z ++ (i :: ra) = z ++ ((j :: rb) ++ c) := by
        simpa [List.append_assoc] using hac
      rw [List.append_cancel_left_eq] at hac'
      have hcancel : i :: ra = (j :: rb) ++ c := by
        exact hac'
      cases c with
      | nil =>
          simp at hcancel
          exact hij hcancel.1
      | cons k cs =>
          simp at hcancel
          exact hij hcancel.1

theorem exists_separator_of_incomparable :
    ∀ a b : Address, Incomparable a b → ∃ z, IsSeparator z a b := by
  intro a
  induction a with
  | nil =>
      intro b h
      exact False.elim <| h (Or.inl ⟨b, by simp⟩)
  | cons i as ih =>
      intro b h
      cases b with
      | nil =>
          exact False.elim <| h (Or.inr ⟨i :: as, by simp⟩)
      | cons j bs =>
          by_cases hij : i = j
          · subst hij
            have htail : Incomparable as bs := by
              intro hcomp
              exact h <|
                match hcomp with
                | Or.inl hab =>
                    Or.inl <| by
                      rcases hab with ⟨c, hc⟩
                      exact ⟨c, by simpa [isAncestorOf, hc]⟩
                | Or.inr hba =>
                    Or.inr <| by
                      rcases hba with ⟨c, hc⟩
                      exact ⟨c, by simpa [isAncestorOf, hc]⟩
            rcases ih bs htail with ⟨z, hz⟩
            rcases hz with ⟨i', j', ra, rb, hneq, ha, hb⟩
            refine ⟨i :: z, ⟨i', j', ra, rb, hneq, ?_, ?_⟩⟩
            · simpa [ha, List.cons_append, List.append_assoc]
            · simpa [hb, List.cons_append, List.append_assoc]
          · refine ⟨[], ⟨i, j, as, bs, hij, ?_, ?_⟩⟩
            · simp
            · simp

theorem incomparable_has_separator_data
    (a b : Address)
    (h : Incomparable a b) :
    ∃ z i j ra rb,
      i ≠ j ∧
      a = z ++ i :: ra ∧
      b = z ++ j :: rb := by
  rcases exists_separator_of_incomparable a b h with ⟨z, hz⟩
  rcases hz with ⟨i, j, ra, rb, hij, ha, hb⟩
  exact ⟨z, i, j, ra, rb, hij, ha, hb⟩

def isPrefixOf : Address → Address → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => a == b && isPrefixOf as bs

def comparableBool (a b : Address) : Bool :=
  isPrefixOf a b || isPrefixOf b a

def allAddressesGo : Nat → PTree → Address → List Address
  | 0, _, _ => []
  | n + 1, leaf _, addr => [addr]
  | n + 1, node _ _ cs, addr =>
      let childResults := cs.mapIdx (fun i child =>
        allAddressesGo n child (addr ++ [i]))
      addr :: childResults.flatten

def allAddresses (t : PTree) : List Address :=
  allAddressesGo t.size t []

theorem size_ne_zero (t : PTree) : t.size ≠ 0 := by
  cases t <;> simp [PTree.size]

theorem root_mem_allAddressesGo_of_pos
    (n : Nat) (t : PTree) (addr : Address) (h : n ≠ 0) :
    addr ∈ allAddressesGo n t addr := by
  cases n with
  | zero =>
      cases h rfl
  | succ n =>
      cases t with
      | leaf s =>
          simp [allAddressesGo]
      | node r s cs =>
          simp [allAddressesGo]

theorem root_mem_allAddresses (t : PTree) :
    [] ∈ allAddresses t := by
  unfold allAddresses
  apply root_mem_allAddressesGo_of_pos
  exact size_ne_zero t

end PTree

/-! ## Subtree correspondence with derivations -/

theorem subtreeAt_toTree_is_toTree
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) (a : Address) (u : PTree) :
    PTree.subtreeAt (NMMS.toTree d) a = some u →
    ∃ (s' : MultiSequent) (d' : NMMS base s'),
      u = NMMS.toTree d' := by
  induction a generalizing d s u with
  | nil =>
      intro h
      simp [PTree.subtreeAt] at h
      exact ⟨s, d, h.symm⟩
  | cons i rest ih =>
      intro h
      cases d with
      | baseAx hb =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | imp_l d₁ d₂ =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | imp_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | conj_l d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | conj_r d₁ d₂ =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | disj_l d₁ d₂ =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _ | _
          · exact ih d₁ u hget
          · exact ih d₂ u hget
          · omega
      | disj_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | neg_l d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega
      | neg_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
          obtain ⟨_, hget⟩ := h
          rcases i with _ | _
          · exact ih d u hget
          · omega

/-! ## Base admissibility retained as useful proof-theoretic structure -/

-- Compatibility may be used to detect where non-logical
-- atoms are not mutually assertible -- and so further grafting
-- must fail via Admissibility conditions
def AntecedentCompatible (base : BaseRel) (Γ : Multiset MyProp) : Prop :=
  ¬ base Γ ({⊥} : Multiset MyProp)

def SequentCompatible (base : BaseRel) (s : MultiSequent) : Prop :=
  AntecedentCompatible base s.lhs

def IsBaseAdmissible (base : BaseRel) (t : PTree)
    (cut : List Address) : Prop :=
  ∀ addr ∈ cut, ∀ u : PTree,
    PTree.subtreeAt t addr = some u →
    base u.conclusion.lhs u.conclusion.rhs ∧
    SequentCompatible base u.conclusion

def IsDerivablyClosed (base : BaseRel) : Prop :=
  ∀ s : MultiSequent, Nonempty (NMMS base s) →
    base s.lhs s.rhs

def IsDerivablyClosedCompatible (base : BaseRel) : Prop :=
  ∀ s : MultiSequent, Nonempty (NMMS base s) →
    base s.lhs s.rhs ∧ SequentCompatible base s

theorem derivablyClosedCompatible_isBaseAdmissible
    {base : BaseRel} (hclosed : IsDerivablyClosedCompatible base)
    {s : MultiSequent} (d : NMMS base s) (cut : List Address) :
    IsBaseAdmissible base (NMMS.toTree d) cut := by
  intro addr _ u hsubt
  obtain ⟨s', d', hd'⟩ := subtreeAt_toTree_is_toTree d addr u hsubt
  have hu : u.conclusion = s' := by
    simpa [hd'] using toTree_conclusion d'
  rw [hu]
  exact hclosed s' ⟨d'⟩

/-! ## GL-style grafting preliminaries -/

namespace PTree

/--
Replace the `i`-th entry of a list if it exists; otherwise leave the list unchanged.
This is enough for our recursive address-based tree editing.
-/
def replaceNth : List α → Nat → α → List α
  | [], _, y => []
  | _ :: xs, 0, y => y :: xs
  | x :: xs, n + 1, y => x :: replaceNth xs n y

/--
A local insertion operation at a node.

Interpretation: the proof `u` is added as a secured immediate subproof
of the current node.

For leaves we promote the leaf to a node tagged `baseAx`.
This is a provisional GL-style choice, intended only as a first pass.
-/
def insertChildAtRoot (u : PTree) : PTree → PTree
  | leaf s      => node RuleTag.baseAx s [u]
  | node r s cs => node r s (u :: cs)

/--
Generic address-based modification of a tree.
-/
def modifyAt : PTree → Address → (PTree → PTree) → Option PTree
  | t, [], f => some (f t)
  | leaf _, _ :: _, _ => none
  | node r s cs, i :: rest, f =>
      if h : i < cs.length then
        match modifyAt (cs[i]) rest f with
        | none => none
        | some child' =>
            some (node r s (replaceNth cs i child'))
      else
        none

/--
Graft `u` into `t` at address `a`, by adding `u` as an immediate child
of the subtree rooted at `a`.
-/
def graftAt (u t : PTree) (a : Address) : Option PTree :=
  modifyAt t a (insertChildAtRoot u)

/--
All one-step graftings of `u` into `t`, obtained by ranging over
all valid addresses of `t`.
-/
def graftings (u t : PTree) : List PTree :=
  (allAddresses t).filterMap (graftAt u t)

/--
A more restrictive leaf-substitution variant: only graft at leaves.
This is likely closer to “conclusion becomes a secured premise”.
-/
def graftIntoLeafAt (u t : PTree) (a : Address) : Option PTree :=
  match subtreeAt t a with
  | some (leaf _) => modifyAt t a (fun _ => u)
  | _             => none

def leafGraftings (u t : PTree) : List PTree :=
  (allAddresses t).filterMap (graftIntoLeafAt u t)

/--
A leaf at address `a` is graftable by `u` if it is labelled by exactly
the conclusion of `u`.
-/
def IsGraftableLeafAt (u t : PTree) (a : Address) : Prop :=
  subtreeAt t a = some (PTree.leaf u.conclusion)

/--
Proof-theoretically meaningful grafting:
replace a leaf at address `a` by `u`, but only when that leaf is labelled
by the conclusion of `u`.
-/
def graftMatchingLeafAt (u t : PTree) (a : Address) : Option PTree :=
  match subtreeAt t a with
  | some (PTree.leaf s) =>
      if h : u.conclusion = s then
        modifyAt t a (fun _ => u)
      else
        none
  | _ => none

/--
All matching leaf-graftings of `u` into `t`.
-/
def matchingLeafGraftings (u t : PTree) : List PTree :=
  (allAddresses t).filterMap (graftMatchingLeafAt u t)

@[simp] theorem IsGraftableLeafAt_iff
    (u t : PTree) (a : Address) :
    IsGraftableLeafAt u t a ↔ subtreeAt t a = some (PTree.leaf u.conclusion) := by
  rfl

@[simp] theorem graftMatchingLeafAt_eq_none_of_subtreeAt_none
    (u t : PTree) (a : Address)
    (h : subtreeAt t a = none) :
    graftMatchingLeafAt u t a = none := by
  unfold graftMatchingLeafAt
  simp [h]

@[simp] theorem graftMatchingLeafAt_eq_none_of_subtreeAt_node
    (u t : PTree) (a : Address) (r : RuleTag) (s : MultiSequent) (cs : List PTree)
    (h : subtreeAt t a = some (PTree.node r s cs)) :
    graftMatchingLeafAt u t a = none := by
  unfold graftMatchingLeafAt
  simp [h]

@[simp] theorem graftMatchingLeafAt_eq_some_of_match
    (u t : PTree) (a : Address) (s : MultiSequent)
    (hleaf : subtreeAt t a = some (PTree.leaf s))
    (hmatch : u.conclusion = s) :
    graftMatchingLeafAt u t a = modifyAt t a (fun _ => u) := by
  unfold graftMatchingLeafAt
  simp [hleaf, hmatch]

@[simp] theorem graftMatchingLeafAt_eq_none_of_mismatch
    (u t : PTree) (a : Address) (s : MultiSequent)
    (hleaf : subtreeAt t a = some (PTree.leaf s))
    (hmismatch : u.conclusion ≠ s) :
    graftMatchingLeafAt u t a = none := by
  unfold graftMatchingLeafAt
  simp [hleaf, hmismatch]

@[simp] theorem graftMatchingLeafAt_root_of_match
    (u : PTree) (s : MultiSequent)
    (h : u.conclusion = s) :
    graftMatchingLeafAt u (PTree.leaf s) [] = some u := by
  unfold graftMatchingLeafAt
  simp [subtreeAt, modifyAt, h]

@[simp] theorem graftMatchingLeafAt_root_of_mismatch
    (u : PTree) (s : MultiSequent)
    (h : u.conclusion ≠ s) :
    graftMatchingLeafAt u (PTree.leaf s) [] = none := by
  unfold graftMatchingLeafAt
  simp [subtreeAt, h]

theorem root_matchingLeafGrafting_mem
    (u t : PTree)
    (h : subtreeAt t [] = some (PTree.leaf u.conclusion)) :
    u ∈ matchingLeafGraftings u t := by
  unfold matchingLeafGraftings
  refine List.mem_filterMap.2 ?_
  refine ⟨[], root_mem_allAddresses t, ?_⟩
  have : graftMatchingLeafAt u t [] = some u := by
    cases t with
    | leaf s =>
        simp [subtreeAt] at h
        subst h
        simp [graftMatchingLeafAt_root_of_match]
    | node r s cs =>
        simp [subtreeAt] at h
  simpa using this

/--
A useful reformulation of matching graftability.
-/
theorem isGraftableLeafAt_of_eq
    (u t : PTree) (a : Address)
    (h : subtreeAt t a = some (PTree.leaf u.conclusion)) :
    IsGraftableLeafAt u t a := by
  exact h

theorem modifyAt_of_subtreeAt_some
    (t u : PTree) (a : Address) (f : PTree → PTree)
    (h : PTree.subtreeAt t a = some u) :
    ∃ t', PTree.modifyAt t a f = some t' := by
  induction a generalizing t with
  | nil =>
      simp [PTree.modifyAt]
  | cons i rest ih =>
      cases t with
      | leaf s =>
          simp [PTree.subtreeAt] at h
      | node r s cs =>
          simp [PTree.subtreeAt] at h
          obtain ⟨hi, hsub⟩ := h
          obtain ⟨t', ht'⟩ := ih (cs[i]) hsub
          refine ⟨PTree.node r s (PTree.replaceNth cs i t'), ?_⟩
          simp [PTree.modifyAt, hi]
          rw [ht']

/--
If a matching graft succeeds, the resulting tree is obtained by replacing
that leaf by `u`.
-/
theorem graftMatchingLeafAt_spec
    (u t : PTree) (a : Address)
    (h : IsGraftableLeafAt u t a) :
    ∃ t', graftMatchingLeafAt u t a = some t' := by
  unfold IsGraftableLeafAt at h
  unfold graftMatchingLeafAt
  simp [h]
  exact modifyAt_of_subtreeAt_some t (PTree.leaf u.conclusion) a (fun _ => u) h

/--
A convenient root-address special case.
-/
theorem graftMatchingLeafAt_root_iff
    (u t : PTree) :
    graftMatchingLeafAt u t [] = some u ↔ t = PTree.leaf u.conclusion := by
  cases t with
  | leaf s =>
      constructor
      · intro h
        unfold graftMatchingLeafAt at h
        simp [subtreeAt, modifyAt] at h
        cases h
        rfl
      · intro h
        cases h
        simp [graftMatchingLeafAt_root_of_match]
  | node r s cs =>
      constructor
      · intro h
        unfold graftMatchingLeafAt at h
        simp [subtreeAt] at h
      · intro h
        cases h

theorem graftMatchingLeafAt_cons_of_child
    (u : PTree) (r : RuleTag) (s : MultiSequent) (cs : List PTree)
    (i : Nat) (rest : Address) (hi : i < cs.length)
    (hleaf : PTree.subtreeAt cs[i] rest = some (PTree.leaf u.conclusion))
    (t' : PTree)
    (hgraft : PTree.graftMatchingLeafAt u cs[i] rest = some t') :
    PTree.graftMatchingLeafAt u (PTree.node r s cs) (i :: rest) =
      some (PTree.node r s (PTree.replaceNth cs i t')) := by
  unfold PTree.graftMatchingLeafAt at hgraft ⊢
  simp [PTree.subtreeAt, hi, hleaf] at hgraft ⊢
  simp [PTree.modifyAt, hi, hgraft]

@[simp] theorem modifyAt_root (f : PTree → PTree) (t : PTree) :
    modifyAt t [] f = some (f t) := by
  rfl

@[simp] theorem graftAt_root (u t : PTree) :
    graftAt u t [] = some (insertChildAtRoot u t) := by
  rfl

@[simp] theorem graftIntoLeafAt_root_of_leaf (u : PTree) (s : MultiSequent) :
    graftIntoLeafAt u (leaf s) [] = some u := by
  simp [graftIntoLeafAt, subtreeAt, modifyAt]

theorem insertChildAtRoot_size_strict (u t : PTree) :
    t.size < (insertChildAtRoot u t).size := by
  cases t with
  | leaf s =>
      simp [insertChildAtRoot, PTree.size]
      exact Nat.pos_of_ne_zero (size_ne_zero u)
  | node r s cs =>
      simp [insertChildAtRoot, PTree.size]
      exact Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (size_ne_zero u))

theorem root_grafting_mem_graftings (u t : PTree) :
    insertChildAtRoot u t ∈ graftings u t := by
  unfold graftings
  refine List.mem_filterMap.2 ?_
  exact ⟨[], root_mem_allAddresses t, by simp [graftAt_root]⟩

theorem graftings_nonempty (u t : PTree) :
    graftings u t ≠ [] := by
  intro h
  have hm : insertChildAtRoot u t ∈ graftings u t :=
    root_grafting_mem_graftings u t
  simpa [h] using hm

/--
A very weak size bound for a root grafting.
-/
theorem size_lt_of_root_grafting (u t : PTree) :
    t.size < (insertChildAtRoot u t).size := by
  exact insertChildAtRoot_size_strict u t

theorem replaceNth_foldr_size_lt
    (cs : List PTree) (i : Nat) (new : PTree)
    (hi : i < cs.length)
    (hsize : (cs[i]).size < new.size) :
    cs.foldr (fun t n => t.size + n) 0 <
      (PTree.replaceNth cs i new).foldr (fun t n => t.size + n) 0 := by
  induction cs generalizing i with
  | nil =>
      cases hi
  | cons c cs ih =>
      cases i with
      | zero =>
          simp [PTree.replaceNth, List.foldr] at hsize ⊢
          exact hsize
      | succ i =>
          simp [PTree.replaceNth, List.foldr] at hi ⊢
          have htail :
              (cs[i]).size < new.size := by
            simpa using hsize
          have ih' := ih i (by simpa using hi) htail
          exact ih'

theorem modifyAt_increases_size_of_local_increase
    (t t' : PTree) (a : Address) (f : PTree → PTree)
    (hmod : PTree.modifyAt t a f = some t')
    (hinc : ∀ u, PTree.subtreeAt t a = some u → u.size < (f u).size) :
    t.size < t'.size := by
  induction a generalizing t t' with
  | nil =>
      simp [PTree.modifyAt] at hmod
      cases hmod
      have hroot : t.size < (f t).size := by
        exact hinc t (by simp [PTree.subtreeAt])
      simpa using hroot
  | cons i rest ih =>
      cases t with
      | leaf s =>
          simp [PTree.modifyAt] at hmod
      | node r s cs =>
          by_cases hi : i < cs.length
          · simp [PTree.modifyAt, hi] at hmod
            cases hrec : PTree.modifyAt (cs[i]) rest f with
            | none =>
                simp [hrec] at hmod
            | some child' =>
                simp [hrec] at hmod
                cases hmod
                have hinc_child :
                    ∀ u, PTree.subtreeAt (cs[i]) rest = some u → u.size < (f u).size := by
                  intro u hu
                  apply hinc u
                  simp [PTree.subtreeAt, hi, hu]
                have hchild_lt : (cs[i]).size < child'.size := by
                  exact ih (t := cs[i]) (t' := child') hrec hinc_child
                have hsum_lt :
                    cs.foldr (fun t n => t.size + n) 0 <
                      (PTree.replaceNth cs i child').foldr (fun t n => t.size + n) 0 := by
                  exact replaceNth_foldr_size_lt cs i child' hi hchild_lt
                simpa [PTree.size] using hsum_lt
          · simp [PTree.modifyAt, hi] at hmod

/--
Future target: characterise precisely which graftings preserve derivability.
-/
theorem grafting_preserves_toTree_shape
    {base : BaseRel} {s : MultiSequent} (d : NMMS base s) (u : PTree) :
    ∀ t, t ∈ graftings u (NMMS.toTree d) → t.size > (NMMS.toTree d).size := by
  intro t ht
  unfold graftings at ht
  rcases List.mem_filterMap.1 ht with ⟨a, ha, hgraft⟩
  have hmod :
      PTree.modifyAt (NMMS.toTree d) a (PTree.insertChildAtRoot u) = some t := by
    simpa [PTree.graftAt] using hgraft
  have hlt :
      (NMMS.toTree d).size < t.size := by
    apply modifyAt_increases_size_of_local_increase
      (t := NMMS.toTree d) (t' := t) (a := a) (f := PTree.insertChildAtRoot u)
      hmod
    intro sub hsub
    simpa using PTree.insertChildAtRoot_size_strict u sub
  exact hlt

end PTree

/-! ## GL-style carrier: formal ℤ-linear combinations of proof trees -/

abbrev GLCarrier := PTree →₀ ℤ

noncomputable def treeGen (t : PTree) : GLCarrier :=
  Finsupp.single t 1

/-
Tree-level grafting product, as a formal sum of all one-step graftings.
This is our first GL-style noncommutative product candidate.

noncomputable def graftProductTree (u t : PTree) : GLCarrier :=
  (PTree.graftings u t).foldr (fun x acc => treeGen x + acc) 0


Leaf-substitution variant of the tree-level product.
This may turn out to be closer to the proof-theoretic use case.

noncomputable def leafGraftProductTree (u t : PTree) : GLCarrier :=
  (PTree.leafGraftings u t).foldr (fun x acc => treeGen x + acc) 0
-/

@[simp] theorem treeGen_ne_zero (t : PTree) :
    treeGen t ≠ 0 := by
  intro h
  have := congrArg (fun f => f t) h
  simp [treeGen] at this

/-! ## Auxiliary cut layer retained for possible future coproduct work -/

namespace PTree

structure IsAdmissibleCut (t : PTree) where
  nodes : List Address
  valid : ∀ a, a ∈ nodes → ValidAddress t a
  antichain :
    ∀ a, a ∈ nodes →
    ∀ b, b ∈ nodes →
    a ≠ b → ¬ comparable a b

def remainderGo (c : List Address) (addr : Address) (t : PTree) : PTree :=
  match t with
  | leaf s => leaf s
  | node r s cs =>
      if addr ∈ c then leaf s
      else
        node r s (cs.attach.mapIdx (fun i ⟨child, hmem⟩ =>
          remainderGo c (addr ++ [i]) child))
termination_by t.size
decreasing_by
  have hlt := child_size_lt_parent (PTree.node r s cs) child (by
    unfold IsImmediateSubtree PTree.children
    exact hmem)
  simpa [PTree.size] using hlt

def remainder (t : PTree) (cut : IsAdmissibleCut t) : PTree :=
  remainderGo cut.nodes [] t

def pruned (t : PTree) (cut : IsAdmissibleCut t) : Forest :=
  cut.nodes.filterMap (subtreeAt t)

def sublists : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      let rest := sublists xs
      rest ++ rest.map (x :: ·)

def isAntichainBool (addrs : List Address) : Bool :=
  addrs.mapIdx (fun i a =>
    addrs.mapIdx (fun j b =>
      i == j || !comparableBool a b)
    |>.all id)
  |>.all id

def allAdmissibleCuts (t : PTree) : List (List Address) :=
  (sublists (allAddresses t)).filter (fun cut =>
    cut.all (fun a => validAddress t a) &&
    isAntichainBool cut)

def coproductTerm (t : PTree) (cut : List Address) : Forest × PTree :=
  (cut.filterMap (subtreeAt t), remainderGo cut [] t)

def coproductData (t : PTree) : List (Forest × PTree) :=
  (allAdmissibleCuts t).map (coproductTerm t)

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

/-- Restrict a cut to the subtree rooted at child index `i`. -/
def restrictCut (cut : List Address) (i : Nat) : List Address :=
  cut.filterMap (fun addr =>
    match addr with
    | [] => none
    | j :: rest => if j = i then some rest else none)

/-- Restrict a cut by an arbitrary address prefix. -/
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

/-- Base admissibility is preserved when we restrict a cut to a subtree. -/
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

private theorem mapIdx_congr'
    {α β : Type _} (xs : List α) (f g : Nat → α → β)
    (h : ∀ i x, x ∈ xs → f i x = g i x) :
    xs.mapIdx f = xs.mapIdx g := by
  simpa [List.mapIdx] using
    mapIdx_go_congr' xs #[] f g (by
      intro i x hx
      simpa using h i x hx)

/-- If the cut is empty, `remainderGo` does nothing. -/
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

theorem remainderGo_restrictCut_eq
    (cut : List Address) (i : Nat) (t : PTree) :
    remainderGo (restrictCut cut i) [] t =
    remainderGo cut [i] t := by
  simpa [restrictCutAt] using
    remainderGo_restrictCutAt_eq cut [i] [] t

private theorem mapIdx_map
    {α β γ : Type _} (xs : List α) :
    ∀ (h : α → β) (f : Nat → β → γ),
      List.mapIdx f (xs.map h) =
        xs.mapIdx (fun i x => f i (h x)) := by
  induction xs with
  | nil =>
      intro h f
      rfl
  | cons x xs ih =>
      intro h f
      simp only [List.map, List.mapIdx_cons]
      congr 1
      simpa using ih h (fun i y => f (i + 1) y)

private theorem mapIdx_attach_eq_mapIdx_from
    {α β : Type _} (xs : List α) (n : Nat) (f : Nat → α → β) :
    xs.attach.mapIdx (fun i x => f (n + i) x.1) =
      xs.mapIdx (fun i x => f (n + i) x) := by
  induction xs generalizing n with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.attach_cons, List.mapIdx_cons]
      congr 1
      calc
        List.mapIdx
            (fun i (x_1 : {x_1 // x_1 ∈ x :: xs}) => f (n + (i + 1)) x_1.1)
            (List.map
              (fun x_1 : {x_1 // x_1 ∈ xs} =>
                (⟨x_1.1, by simp [x_1.2]⟩ : {x_1 // x_1 ∈ x :: xs}))
              xs.attach)
            =
        List.mapIdx
            (fun i (x_1 : {x_1 // x_1 ∈ xs}) => f (n + (i + 1)) x_1.1)
            xs.attach := by
              simpa using
                (mapIdx_map xs.attach
                  (fun x_1 : {x_1 // x_1 ∈ xs} =>
                    (⟨x_1.1, by simp [x_1.2]⟩ : {x_1 // x_1 ∈ x :: xs}))
                  (fun i (x_1 : {x_1 // x_1 ∈ x :: xs}) =>
                    f (n + (i + 1)) x_1.1))
        _ =
        xs.mapIdx (fun i x => f (n + (i + 1)) x) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (n + 1)

private theorem mapIdx_attach_eq_mapIdx
    {α β : Type _} (xs : List α) (f : Nat → α → β) :
    xs.attach.mapIdx (fun i x => f i x.1) = xs.mapIdx f := by
  simpa using mapIdx_attach_eq_mapIdx_from xs 0 f

private theorem mapIdx_mapIdx_from
    {α β γ : Type _} (xs : List α) (n : Nat)
    (f : Nat → α → β) (g : Nat → β → γ) :
    (xs.mapIdx (fun i x => f (n + i) x)).mapIdx (fun i y => g (n + i) y) =
      xs.mapIdx (fun i x => g (n + i) (f (n + i) x)) := by
  induction xs generalizing n with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.mapIdx_cons]
      congr 1
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ih (n + 1))

private theorem mapIdx_mapIdx
    {α β γ : Type _} (xs : List α)
    (f : Nat → α → β) (g : Nat → β → γ) :
    (xs.mapIdx f).mapIdx g = xs.mapIdx (fun i x => g i (f i x)) := by
  simpa using mapIdx_mapIdx_from xs 0 f g

theorem remainderGo_remainderGo_eq
    (cut₁ cut₂ : List Address) (addr : Address) (t : PTree) :
    remainderGo cut₂ addr (remainderGo cut₁ addr t) =
    remainderGo (cut₁ ++ cut₂) addr t := by
  let P : Nat → Prop :=
    fun n =>
      ∀ t : PTree, t.size = n → ∀ addr : Address,
        remainderGo cut₂ addr (remainderGo cut₁ addr t) =
        remainderGo (cut₁ ++ cut₂) addr t

  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih t hsize addr
    cases t with
    | leaf s =>
        simp [remainderGo]
    | node r s cs =>
        by_cases h₁ : addr ∈ cut₁
        · have h₁' : addr ∈ cut₁ ++ cut₂ := by
            simp [h₁]
          simp [remainderGo, h₁, h₁']
        · by_cases h₂ : addr ∈ cut₂
          · have h₁₂ : addr ∈ cut₁ ++ cut₂ := by
              simp [h₁, h₂]
            simp [remainderGo, h₁, h₂, h₁₂]
          · have h₁₂ : addr ∉ cut₁ ++ cut₂ := by
              simp [h₁, h₂]
            have hchildren :
                List.mapIdx
                    (fun i
                      (x :
                        {x //
                          x ∈ List.mapIdx
                            (fun i (x : {x // x ∈ cs}) =>
                              remainderGo cut₁ (addr ++ [i]) x.1)
                            cs.attach}) =>
                      remainderGo cut₂ (addr ++ [i]) x.1)
                    (List.mapIdx
                      (fun i (x : {x // x ∈ cs}) =>
                        remainderGo cut₁ (addr ++ [i]) x.1)
                      cs.attach).attach
                  =
                List.mapIdx
                    (fun i (x : {x // x ∈ cs}) =>
                      remainderGo (cut₁ ++ cut₂) (addr ++ [i]) x.1)
                    cs.attach := by
              calc
                List.mapIdx
                    (fun i
                      (x :
                        {x //
                          x ∈ List.mapIdx
                            (fun i (x : {x // x ∈ cs}) =>
                              remainderGo cut₁ (addr ++ [i]) x.1)
                            cs.attach}) =>
                      remainderGo cut₂ (addr ++ [i]) x.1)
                    (List.mapIdx
                      (fun i (x : {x // x ∈ cs}) =>
                        remainderGo cut₁ (addr ++ [i]) x.1)
                      cs.attach).attach
                    =
                List.mapIdx
                    (fun i child =>
                      remainderGo cut₂ (addr ++ [i]) child)
                    (List.mapIdx
                      (fun i (x : {x // x ∈ cs}) =>
                        remainderGo cut₁ (addr ++ [i]) x.1)
                      cs.attach) := by
                      simpa using
                        (mapIdx_attach_eq_mapIdx
                          (List.mapIdx
                            (fun i (x : {x // x ∈ cs}) =>
                              remainderGo cut₁ (addr ++ [i]) x.1)
                            cs.attach)
                          (fun i child =>
                            remainderGo cut₂ (addr ++ [i]) child))
                _ =
                List.mapIdx
                    (fun i child =>
                      remainderGo cut₂ (addr ++ [i])
                        (remainderGo cut₁ (addr ++ [i]) child))
                    cs := by
                      rw [mapIdx_attach_eq_mapIdx]
                      rw [mapIdx_mapIdx]
                _ =
                List.mapIdx
                    (fun i (x : {x // x ∈ cs}) =>
                      remainderGo cut₂ (addr ++ [i])
                        (remainderGo cut₁ (addr ++ [i]) x.1))
                    cs.attach := by
                      symm
                      simpa using
                        (mapIdx_attach_eq_mapIdx cs
                          (fun i child =>
                            remainderGo cut₂ (addr ++ [i])
                              (remainderGo cut₁ (addr ++ [i]) child)))
                _ =
                List.mapIdx
                    (fun i (x : {x // x ∈ cs}) =>
                      remainderGo (cut₁ ++ cut₂) (addr ++ [i]) x.1)
                    cs.attach := by
                      apply mapIdx_congr' cs.attach
                        (fun i x =>
                          remainderGo cut₂ (addr ++ [i])
                            (remainderGo cut₁ (addr ++ [i]) x.1))
                        (fun i x =>
                          remainderGo (cut₁ ++ cut₂) (addr ++ [i]) x.1)
                      intro i x hx
                      have hlt_node : x.1.size < (PTree.node r s cs).size := by
                        apply child_size_lt_parent (PTree.node r s cs) x.1
                        unfold IsImmediateSubtree PTree.children
                        simpa using x.2
                      have hlt : x.1.size < n := by
                        simpa [hsize] using hlt_node
                      exact ih x.1.size hlt x.1 rfl (addr ++ [i])
            simpa [remainderGo, h₁, h₂, h₁₂] using
              congrArg (PTree.node r s) hchildren

  have hstrong : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    exact hP n ih

  exact hstrong t.size t rfl addr

@[simp] theorem remainder_remainder_eq
    (cut₁ cut₂ : List Address) (t : PTree) :
    remainderGo cut₂ [] (remainderGo cut₁ [] t) =
    remainderGo (cut₁ ++ cut₂) [] t := by
  simpa using remainderGo_remainderGo_eq cut₁ cut₂ [] t

@[simp] theorem coproductTerm_snd_remainderGo
    (t : PTree) (cut₁ cut₂ : List Address) :
    (coproductTerm (coproductTerm t cut₁).2 cut₂).2 =
      (coproductTerm t (cut₁ ++ cut₂)).2 := by
  simp [coproductTerm, remainderGo_remainderGo_eq]

@[simp] theorem coproductTerm_snd_append
    (t : PTree) (cut₁ cut₂ : List Address) :
    (coproductTerm (remainderGo cut₁ [] t) cut₂).2 =
      remainderGo (cut₁ ++ cut₂) [] t := by
  simp [coproductTerm, remainderGo_remainderGo_eq]

theorem remainderGo_append_self
    (cut : List Address) (addr : Address) (t : PTree) :
    remainderGo (cut ++ cut) addr t = remainderGo cut addr t := by
  let P : Nat → Prop :=
    fun n =>
      ∀ t : PTree, t.size = n → ∀ addr : Address,
        remainderGo (cut ++ cut) addr t = remainderGo cut addr t

  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih t hsize addr
    cases t with
    | leaf s =>
        simp [remainderGo]
    | node r s cs =>
        by_cases h : addr ∈ cut
        · have h' : addr ∈ cut ++ cut := by
            simp [h]
          simp [remainderGo, h, h']
        · have h' : addr ∉ cut ++ cut := by
            simp [h]
          simp only [remainderGo, h, h']
          congr 2
          apply mapIdx_congr' cs.attach
            (fun i x => remainderGo (cut ++ cut) (addr ++ [i]) x.1)
            (fun i x => remainderGo cut (addr ++ [i]) x.1)
          intro i x hx
          have hlt_node : x.1.size < (PTree.node r s cs).size := by
            apply child_size_lt_parent (PTree.node r s cs) x.1
            unfold IsImmediateSubtree PTree.children
            simpa using x.2
          have hlt : x.1.size < n := by
            simpa [hsize] using hlt_node
          exact ih x.1.size hlt x.1 rfl (addr ++ [i])

  have hstrong : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    exact hP n ih

  exact hstrong t.size t rfl addr

@[simp] theorem remainderGo_idempotent
    (cut : List Address) (addr : Address) (t : PTree) :
    remainderGo cut addr (remainderGo cut addr t) =
    remainderGo cut addr t := by
  rw [remainderGo_remainderGo_eq cut cut addr t]
  exact remainderGo_append_self cut addr t

@[simp] theorem remainder_idempotent
    (cut : List Address) (t : PTree) :
    remainderGo cut [] (remainderGo cut [] t) =
    remainderGo cut [] t := by
  simpa using remainderGo_idempotent cut [] t

@[simp] theorem coproductTerm_snd_two_stage
    (t : PTree) (cut₁ cut₂ : List Address) :
    (coproductTerm (coproductTerm t cut₁).2 cut₂).2 =
      (coproductTerm t (cut₁ ++ cut₂)).2 := by
  simp [coproductTerm, remainderGo_remainderGo_eq]

@[simp] lemma coproductTerm_fst_nil (t : PTree) :
    (coproductTerm t []).1 = [] := by
  simp [coproductTerm]

@[simp] lemma coproductTerm_nil (t : PTree) :
    coproductTerm t [] = ([], t) := by
  simp [coproductTerm, remainderGo_nil]

@[simp] lemma coproductTerm_snd_nil (t : PTree) :
    (coproductTerm t []).2 = t := by
  simp [coproductTerm, remainderGo_nil]

theorem coproduct_nonempty (t : PTree) :
    0 < (coproductData t).length := by
  unfold coproductData
  have hmem : ([], t) ∈ (allAdmissibleCuts t).map (coproductTerm t) := by
    apply List.mem_map.2
    refine ⟨[], empty_cut_mem_allAdmissibleCuts t, ?_⟩
    simpa [coproductTerm_nil]
  exact List.length_pos_of_mem hmem

end PTree

theorem mapIdx_attach_singleton (f : Nat → PTree → PTree) (t : PTree) :
    List.mapIdx (fun i (x : {x // x ∈ [t]}) => f i x.1) [t].attach = [f 0 t] := by
  rfl

theorem mapIdx_attach_pair (f : Nat → PTree → PTree) (t u : PTree) :
    List.mapIdx (fun i (x : {x // x ∈ [t, u]}) => f i x.1) [t, u].attach = [f 0 t, f 1 u] := by
  rfl

theorem remainderGo_toTree_is_toTree
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) (cut : List Address)
    (hbase : IsBaseAdmissible base (NMMS.toTree d) cut) :
    ∃ d' : NMMS base s,
      PTree.remainderGo cut [] (NMMS.toTree d) = NMMS.toTree d' := by
  by_cases hroot : [] ∈ cut
  · have hb : base s.lhs s.rhs := by
      have hsubt : PTree.subtreeAt (NMMS.toTree d) [] =
          some (NMMS.toTree d) := by
        simp [PTree.subtreeAt]
      have hconc := toTree_conclusion d
      have hrootbase :
          base (NMMS.toTree d).conclusion.lhs (NMMS.toTree d).conclusion.rhs ∧
          SequentCompatible base (NMMS.toTree d).conclusion :=
        hbase [] hroot (NMMS.toTree d) hsubt
      have : base (NMMS.toTree d).conclusion.lhs (NMMS.toTree d).conclusion.rhs :=
        hrootbase.1
      simpa [hconc] using this
    have hrem : PTree.remainderGo cut [] (NMMS.toTree d) =
        PTree.leaf s := by
      cases d <;> simp [NMMS.toTree, PTree.remainderGo, hroot]
    exact ⟨NMMS.baseAx hb, by rw [hrem]; simp [NMMS.toTree]⟩
  · cases d with
    | baseAx h =>
        simp [NMMS.toTree, PTree.remainderGo, hroot]
        exact ⟨NMMS.baseAx h, rfl⟩

    | imp_l d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (PTree.restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (PTree.restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (PTree.restrictCut cut 1) hbase₂
        refine ⟨NMMS.imp_l d₁' d₂', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← PTree.remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | imp_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (PTree.restrictCut cut 0) hbase₁
        refine ⟨NMMS.imp_r d', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← PTree.remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | conj_l d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (PTree.restrictCut cut 0) hbase₁
        refine ⟨NMMS.conj_l d', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← PTree.remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | conj_r d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (PTree.restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (PTree.restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (PTree.restrictCut cut 1) hbase₂
        refine ⟨NMMS.conj_r d₁' d₂', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← PTree.remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | disj_l d₁ d₂ =>
        have hbase₁ : IsBaseAdmissible base d₁.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        have hbase₂ : IsBaseAdmissible base d₂.toTree
            (PTree.restrictCut cut 1) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d₁.toTree, d₂.toTree])
              1 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d₁', hd₁⟩ :=
          remainderGo_toTree_is_toTree d₁ (PTree.restrictCut cut 0) hbase₁
        obtain ⟨d₂', hd₂⟩ :=
          remainderGo_toTree_is_toTree d₂ (PTree.restrictCut cut 1) hbase₂
        refine ⟨NMMS.disj_l d₁' d₂', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_pair, ← PTree.remainderGo_restrictCut_eq]
        simpa [hd₁, hd₂]

    | disj_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (PTree.restrictCut cut 0) hbase₁
        refine ⟨NMMS.disj_r d', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← PTree.remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | neg_l d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (PTree.restrictCut cut 0) hbase₁
        refine ⟨NMMS.neg_l d', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← PTree.remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

    | neg_r d =>
        have hbase₁ : IsBaseAdmissible base d.toTree
            (PTree.restrictCut cut 0) := by
          simpa [NMMS.toTree] using
            PTree.isBaseAdmissible_restrictCut (cs := [d.toTree])
              0 (by simp) (by simpa [NMMS.toTree] using hbase)
        obtain ⟨d', hd⟩ :=
          remainderGo_toTree_is_toTree d (PTree.restrictCut cut 0) hbase₁
        refine ⟨NMMS.neg_r d', ?_⟩
        simp only [NMMS.toTree, PTree.remainderGo, hroot, ite_false, List.nil_append,
          mapIdx_attach_singleton, ← PTree.remainderGo_restrictCut_eq]
        congr 1
        exact congrArg List.singleton hd

theorem coproduct_terms_are_subderivations
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s)
    (hbase : ∀ cut, IsBaseAdmissible base (NMMS.toTree d) cut) :
    ∀ (f : Forest) (r : PTree),
      (f, r) ∈ PTree.coproductData (NMMS.toTree d) →
      (∃ (s' : MultiSequent) (d' : NMMS base s'),
        r = NMMS.toTree d') ∧
      (∀ t ∈ f, ∃ (s'' : MultiSequent) (d'' : NMMS base s''),
        t = NMMS.toTree d'') := by
  intro f r hmem
  unfold PTree.coproductData at hmem
  simp [List.mem_map] at hmem
  obtain ⟨cut, hcut, hterm⟩ := hmem
  unfold PTree.coproductTerm at hterm
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

theorem graftMatchingLeafAt_toTree_is_toTree
    {base : BaseRel} {s_outer s_inner : MultiSequent}
    (d_outer : NMMS base s_outer)
    (d_inner : NMMS base s_inner)
    (a : Address)
    (h :
      PTree.IsGraftableLeafAt
        (NMMS.toTree d_inner)
        (NMMS.toTree d_outer)
        a) :
    ∃ d' : NMMS base s_outer,
      PTree.graftMatchingLeafAt
        (NMMS.toTree d_inner)
        (NMMS.toTree d_outer)
        a
      = some (NMMS.toTree d') := by
  induction a generalizing d_outer s_outer with
  | nil =>
      rw [PTree.IsGraftableLeafAt_iff] at h
      cases d_outer with
      | baseAx hb =>
          have hs :
              s_inner = (NMMS.toTree (NMMS.baseAx hb)).conclusion := by
            have hleaf :
                PTree.leaf s_inner =
                  PTree.leaf ((NMMS.toTree (NMMS.baseAx hb)).conclusion) := by
              simpa [NMMS.toTree, PTree.subtreeAt, toTree_conclusion d_inner] using h.symm
            injection hleaf with hseq
          cases hs
          refine ⟨d_inner, ?_⟩
          unfold PTree.graftMatchingLeafAt
          simp [NMMS.toTree, PTree.subtreeAt, PTree.modifyAt]
          refine ⟨?_, rfl⟩
          simpa [NMMS.toTree, PTree.conclusion] using toTree_conclusion d_inner

      | imp_l d1 d2 =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | imp_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | conj_l d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | conj_r d1 d2 =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | disj_l d1 d2 =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | disj_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | neg_l d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h
      | neg_r d =>
          simp [NMMS.toTree, PTree.subtreeAt] at h

  | cons i rest ih =>
      rw [PTree.IsGraftableLeafAt_iff] at h
      cases d_outer with
      | baseAx hb =>
          simp [NMMS.toTree, PTree.subtreeAt] at h

      | imp_l d1 d2 =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d1)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d1', hd1'⟩ := ih d1 hchild
            refine ⟨NMMS.imp_l d1' d2, ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d1) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.imp_l
                (NMMS.toTree (NMMS.imp_l d1 d2)).conclusion
                [NMMS.toTree d1, NMMS.toTree d2]
                0 rest (by simp) hleaf
                (NMMS.toTree d1') hd1')
          · rcases i with _ | i
            · have hchild :
                  PTree.IsGraftableLeafAt
                    (NMMS.toTree d_inner)
                    (NMMS.toTree d2)
                    rest := by
                rw [PTree.IsGraftableLeafAt_iff]
                simpa [PTree.subtreeAt] using h
              obtain ⟨d2', hd2'⟩ := ih d2 hchild
              refine ⟨NMMS.imp_l d1 d2', ?_⟩
              have hleaf :
                  PTree.subtreeAt (NMMS.toTree d2) rest =
                    some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
                rw [PTree.IsGraftableLeafAt_iff] at hchild
                exact hchild
              simpa [NMMS.toTree] using
                (PTree.graftMatchingLeafAt_cons_of_child
                  (NMMS.toTree d_inner)
                  RuleTag.imp_l
                  (NMMS.toTree (NMMS.imp_l d1 d2)).conclusion
                  [NMMS.toTree d1, NMMS.toTree d2]
                  1 rest (by simp) hleaf
                  (NMMS.toTree d2') hd2')
            · simp [PTree.subtreeAt] at h

      | imp_r d =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d', hd'⟩ := ih d hchild
            refine ⟨NMMS.imp_r d', ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.imp_r
                (NMMS.toTree (NMMS.imp_r d)).conclusion
                [NMMS.toTree d]
                0 rest (by simp) hleaf
                (NMMS.toTree d') hd')
          · simp [PTree.subtreeAt] at h

      | conj_l d =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d', hd'⟩ := ih d hchild
            refine ⟨NMMS.conj_l d', ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.conj_l
                (NMMS.toTree (NMMS.conj_l d)).conclusion
                [NMMS.toTree d]
                0 rest (by simp) hleaf
                (NMMS.toTree d') hd')
          · simp [PTree.subtreeAt] at h

      | conj_r d1 d2 =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d1)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d1', hd1'⟩ := ih d1 hchild
            refine ⟨NMMS.conj_r d1' d2, ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d1) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.conj_r
                (NMMS.toTree (NMMS.conj_r d1 d2)).conclusion
                [NMMS.toTree d1, NMMS.toTree d2]
                0 rest (by simp) hleaf
                (NMMS.toTree d1') hd1')
          · rcases i with _ | i
            · have hchild :
                  PTree.IsGraftableLeafAt
                    (NMMS.toTree d_inner)
                    (NMMS.toTree d2)
                    rest := by
                rw [PTree.IsGraftableLeafAt_iff]
                simpa [PTree.subtreeAt] using h
              obtain ⟨d2', hd2'⟩ := ih d2 hchild
              refine ⟨NMMS.conj_r d1 d2', ?_⟩
              have hleaf :
                  PTree.subtreeAt (NMMS.toTree d2) rest =
                    some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
                rw [PTree.IsGraftableLeafAt_iff] at hchild
                exact hchild
              simpa [NMMS.toTree] using
                (PTree.graftMatchingLeafAt_cons_of_child
                  (NMMS.toTree d_inner)
                  RuleTag.conj_r
                  (NMMS.toTree (NMMS.conj_r d1 d2)).conclusion
                  [NMMS.toTree d1, NMMS.toTree d2]
                  1 rest (by simp) hleaf
                  (NMMS.toTree d2') hd2')
            · simp [PTree.subtreeAt] at h

      | disj_l d1 d2 =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d1)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d1', hd1'⟩ := ih d1 hchild
            refine ⟨NMMS.disj_l d1' d2, ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d1) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.disj_l
                (NMMS.toTree (NMMS.disj_l d1 d2)).conclusion
                [NMMS.toTree d1, NMMS.toTree d2]
                0 rest (by simp) hleaf
                (NMMS.toTree d1') hd1')
          · rcases i with _ | i
            · have hchild :
                  PTree.IsGraftableLeafAt
                    (NMMS.toTree d_inner)
                    (NMMS.toTree d2)
                    rest := by
                rw [PTree.IsGraftableLeafAt_iff]
                simpa [PTree.subtreeAt] using h
              obtain ⟨d2', hd2'⟩ := ih d2 hchild
              refine ⟨NMMS.disj_l d1 d2', ?_⟩
              have hleaf :
                  PTree.subtreeAt (NMMS.toTree d2) rest =
                    some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
                rw [PTree.IsGraftableLeafAt_iff] at hchild
                exact hchild
              simpa [NMMS.toTree] using
                (PTree.graftMatchingLeafAt_cons_of_child
                  (NMMS.toTree d_inner)
                  RuleTag.disj_l
                  (NMMS.toTree (NMMS.disj_l d1 d2)).conclusion
                  [NMMS.toTree d1, NMMS.toTree d2]
                  1 rest (by simp) hleaf
                  (NMMS.toTree d2') hd2')
            · simp [PTree.subtreeAt] at h

      | disj_r d =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d', hd'⟩ := ih d hchild
            refine ⟨NMMS.disj_r d', ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.disj_r
                (NMMS.toTree (NMMS.disj_r d)).conclusion
                [NMMS.toTree d]
                0 rest (by simp) hleaf
                (NMMS.toTree d') hd')
          · simp [PTree.subtreeAt] at h

      | neg_l d =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d', hd'⟩ := ih d hchild
            refine ⟨NMMS.neg_l d', ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.neg_l
                (NMMS.toTree (NMMS.neg_l d)).conclusion
                [NMMS.toTree d]
                0 rest (by simp) hleaf
                (NMMS.toTree d') hd')
          · simp [PTree.subtreeAt] at h

      | neg_r d =>
          simp only [NMMS.toTree, PTree.subtreeAt] at h
          rcases i with _ | i
          · have hchild :
                PTree.IsGraftableLeafAt
                  (NMMS.toTree d_inner)
                  (NMMS.toTree d)
                  rest := by
              rw [PTree.IsGraftableLeafAt_iff]
              simpa [PTree.subtreeAt] using h
            obtain ⟨d', hd'⟩ := ih d hchild
            refine ⟨NMMS.neg_r d', ?_⟩
            have hleaf :
                PTree.subtreeAt (NMMS.toTree d) rest =
                  some (PTree.leaf (NMMS.toTree d_inner).conclusion) := by
              rw [PTree.IsGraftableLeafAt_iff] at hchild
              exact hchild
            simpa [NMMS.toTree] using
              (PTree.graftMatchingLeafAt_cons_of_child
                (NMMS.toTree d_inner)
                RuleTag.neg_r
                (NMMS.toTree (NMMS.neg_r d)).conclusion
                [NMMS.toTree d]
                0 rest (by simp) hleaf
                (NMMS.toTree d') hd')
          · simp [PTree.subtreeAt] at h

/-! ###########################################################################
## GL / pre-Lie direction on proof trees

At this stage we treat individual proof trees as the primitive objects, and
their matching-leaf grafting operation
 as the candidate pre-Lie product.

The ambient linear space of primitives is the formal ℤ-linear span of proof trees.
Later, the commutative forest algebra `HopfCarrier` should play the role of the
symmetric algebra `S(g)` in the Oudom–Guin construction.

The cut-based coproduct machinery defined earlier is retained as a proof-theoretic
comparison object, but the present section follows the GL / Oudom–Guin route.
############################################################################ -/

/-- The primitive linear space: formal ℤ-linear combinations of proof trees. -/
abbrev PreLieCarrier := GLCarrier

namespace PTree

/--
Tree-level matching grafting product.

This is the candidate primitive pre-Lie product:
we sum all proof trees obtained by replacing a matching leaf of `t`
by the tree `u`.
-/
noncomputable def graftPreLieTree (u t : PTree) : PreLieCarrier :=
  (matchingLeafGraftings u t).foldr (fun x acc => treeGen x + acc) 0

theorem isGraftableLeafAt_of_graftMatchingLeafAt_eq_some
    (u t : PTree) (a : Address) (t' : PTree)
    (h : graftMatchingLeafAt u t a = some t') :
    IsGraftableLeafAt u t a := by
  unfold graftMatchingLeafAt at h
  cases hsub : subtreeAt t a with
  | none =>
      simp [hsub] at h
  | some sub =>
      cases sub with
      | leaf s =>
          by_cases hmatch : u.conclusion = s
          · simp [hsub, hmatch] at h
            exact isGraftableLeafAt_of_eq (u := u) (t := t) (a := a) (by
              simpa [hmatch] using hsub)
          · simp [hsub, hmatch] at h
      | node r s cs =>
          simp [hsub] at h

/--
If there is a matching graftable leaf, then the tree-level grafting product
is nonzero.

This is the primitive analogue of the fact that the GL grafting product is
nontrivial whenever there is at least one admissible grafting site.
-/
@[simp] theorem foldr_treeGen_apply
    (xs : List PTree) (t : PTree) :
    (xs.foldr (fun x acc => treeGen x + acc) 0) t = (xs.count t : ℤ) := by
  induction xs with
  | nil =>
      simp [treeGen]
  | cons x xs ih =>
      by_cases hxt : x = t
      · subst hxt
        have h := congrArg (fun z : ℤ => 1 + z) ih
        simpa [treeGen, add_comm, add_left_comm, add_assoc] using h
      · simp [treeGen, hxt]
        exact ih

theorem subtreeAt_some_implies_mem_allAddressesGo
    (n : Nat) (t u : PTree) (addr a : Address)
    (hn : t.size ≤ n)
    (h : subtreeAt t a = some u) :
    addr ++ a ∈ allAddressesGo n t addr := by
  induction n generalizing t addr a with
  | zero =>
      exfalso
      exact size_ne_zero t (Nat.eq_zero_of_le_zero hn)
  | succ n ih =>
      cases a with
      | nil =>
          cases t with
          | leaf s =>
              simp [subtreeAt, allAddressesGo]
          | node r s cs =>
              simp [subtreeAt, allAddressesGo]
      | cons i rest =>
          cases t with
          | leaf s =>
              simp [subtreeAt] at h
          | node r s cs =>
              simp [subtreeAt] at h
              obtain ⟨hi, hsub⟩ := h
              have hchild_size : (cs[i]).size ≤ n := by
                have himm : IsImmediateSubtree (PTree.node r s cs) (cs[i]) := by
                  unfold IsImmediateSubtree PTree.children
                  simp [hi]
                have hlt : (cs[i]).size < (PTree.node r s cs).size :=
                  child_size_lt_parent (PTree.node r s cs) (cs[i]) himm
                have hlt' : (cs[i]).size < n + 1 := lt_of_lt_of_le hlt hn
                exact Nat.lt_succ_iff.mp hlt'
              have hmem_child :
                  (addr ++ [i]) ++ rest ∈ allAddressesGo n (cs[i]) (addr ++ [i]) := by
                exact ih (cs[i]) (addr ++ [i]) rest hchild_size hsub
              simp [allAddressesGo]
              refine ⟨i, hi, ?_⟩
              simpa [List.append_assoc] using hmem_child

theorem subtreeAt_some_implies_mem_allAddresses
    (t u : PTree) (a : Address)
    (h : subtreeAt t a = some u) :
    a ∈ allAddresses t := by
  unfold allAddresses
  simpa using
    subtreeAt_some_implies_mem_allAddressesGo t.size t u [] a (by rfl) h

theorem graftPreLieTree_nonzero_of_exists_graftable
    (u t : PTree)
    (h : ∃ a, IsGraftableLeafAt u t a) :
    graftPreLieTree u t ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨t', ht'⟩ := graftMatchingLeafAt_spec u t a ha

  have haAddr : a ∈ allAddresses t := by
    simpa [IsGraftableLeafAt_iff] using
      (subtreeAt_some_implies_mem_allAddresses
        (t := t) (a := a) (u := PTree.leaf u.conclusion) ha)

  have hmem : t' ∈ matchingLeafGraftings u t := by
    unfold matchingLeafGraftings
    exact List.mem_filterMap.2 ⟨a, haAddr, ht'⟩

  intro hz

  have hcoeff_zero : graftPreLieTree u t t' = 0 := by
    simpa [hz]

  have hcount_zero :
      ((List.count t' (matchingLeafGraftings u t) : Nat) : ℤ) = 0 := by
    simpa [graftPreLieTree, foldr_treeGen_apply] using hcoeff_zero

  have hcount_nat_ne :
      List.count t' (matchingLeafGraftings u t) ≠ 0 := by
    intro hc
    apply List.count_eq_zero.mp hc
    exact hmem

  have hcount_ne :
      ((List.count t' (matchingLeafGraftings u t) : Nat) : ℤ) ≠ 0 := by
    exact_mod_cast hcount_nat_ne

  exact hcount_ne hcount_zero

/--
Conversely, if there are no matching leaf graftings, the primitive grafting
product should vanish.

This is useful later for support calculations and for characterising when
the pre-Lie product is zero.
-/
@[simp] theorem graftMatchingLeafAt_eq_none_of_not_graftable
    (u t : PTree) (a : Address)
    (h : ¬ IsGraftableLeafAt u t a) :
    graftMatchingLeafAt u t a = none := by
  cases hg : graftMatchingLeafAt u t a with
  | none =>
      rfl
  | some t' =>
      exfalso
      exact h (isGraftableLeafAt_of_graftMatchingLeafAt_eq_some u t a t' hg)

theorem graftPreLieTree_eq_zero_of_no_graftable
    (u t : PTree)
    (h : ∀ a, ¬ IsGraftableLeafAt u t a) :
    graftPreLieTree u t = 0 := by
  unfold graftPreLieTree matchingLeafGraftings
  have hfm :
      List.filterMap (graftMatchingLeafAt u t) (allAddresses t) = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro a ha
    exact graftMatchingLeafAt_eq_none_of_not_graftable u t a (h a)
  simp [hfm]

end PTree

/--
Every tree occurring in the matching-leaf grafting product of two derivation trees
is again the tree of a derivation of the same outer sequent.

This is the closure statement needed to justify restricting attention to the
proof-tree fragment inside the ambient rooted-tree space.
-/
theorem matchingLeafGraftings_toTree_are_toTree
    {base : BaseRel} {s_outer s_inner : MultiSequent}
    (d_outer : NMMS base s_outer)
    (d_inner : NMMS base s_inner) :
    ∀ t ∈ PTree.matchingLeafGraftings (NMMS.toTree d_inner) (NMMS.toTree d_outer),
      ∃ d' : NMMS base s_outer, t = NMMS.toTree d' := by
  intro t ht
  unfold PTree.matchingLeafGraftings at ht
  simp [List.mem_filterMap] at ht
  obtain ⟨a, ha, hg⟩ := ht
  have hGraftable :
      PTree.IsGraftableLeafAt (NMMS.toTree d_inner) (NMMS.toTree d_outer) a := by
    exact PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some
      (u := NMMS.toTree d_inner)
      (t := NMMS.toTree d_outer)
      (a := a)
      (t' := t)
      hg
  obtain ⟨d', hd'⟩ :=
    graftMatchingLeafAt_toTree_is_toTree d_outer d_inner a hGraftable
  exact ⟨d', Option.some.inj (hg.symm.trans hd')⟩

/--
Bilinear extension of the primitive matching-leaf grafting product.

This is the candidate pre-Lie product on the linear span of proof trees.
-/
noncomputable def graftPreLieRight (u : PTree) :
    PreLieCarrier →ₗ[ℤ] PreLieCarrier :=
  Finsupp.linearCombination ℤ (fun t => PTree.graftPreLieTree u t)

/-
tree × tree → tree
   ↓ linearise in right
tree → (linear map)
   ↓ linearise in left
linear × linear → linear
-/

noncomputable def graftPreLie :
    PreLieCarrier →ₗ[ℤ] PreLieCarrier →ₗ[ℤ] PreLieCarrier :=
  Finsupp.linearCombination ℤ graftPreLieRight

/--
On tree generators, the bilinear extension agrees with the underlying
tree-level grafting product.
-/
theorem graftPreLieRight_on_generator
    (u t : PTree) :
    graftPreLieRight u (treeGen t) = PTree.graftPreLieTree u t := by
  simp [graftPreLieRight, treeGen]

theorem graftPreLie_on_generators
    (u t : PTree) :
    graftPreLie (treeGen u) (treeGen t) = PTree.graftPreLieTree u t := by
  simp [graftPreLie, graftPreLieRight, treeGen]

@[simp] theorem replaceNth_length
    (xs : List α) (i : Nat) (y : α) :
    (PTree.replaceNth xs i y).length = xs.length := by
  induction xs generalizing i with
  | nil =>
      cases i <;> simp [PTree.replaceNth]
  | cons x xs ih =>
      cases i <;> simp [PTree.replaceNth, ih]

theorem mem_replaceNth
    (xs : List α) (i : Nat) (y z : α)
    (hz : z ∈ PTree.replaceNth xs i y) :
    z = y ∨ z ∈ xs := by
  induction xs generalizing i z with
  | nil =>
      cases i <;> simp [PTree.replaceNth] at hz
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [PTree.replaceNth] at hz
          rcases hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (by simp [hz])
      | succ i =>
          simp [PTree.replaceNth] at hz
          rcases hz with rfl | hz
          · exact Or.inr (by simp)
          · rcases ih i z hz with rfl | hmem
            · exact Or.inl rfl
            · exact Or.inr (by simp [hmem])

theorem isDyadic_of_mem_replaceNth
    {cs : List PTree} {i : Nat} {new c : PTree}
    (hcs : ∀ t, t ∈ cs → PTree.IsDyadic t)
    (hnew : PTree.IsDyadic new)
    (hc : c ∈ PTree.replaceNth cs i new) :
    PTree.IsDyadic c := by
  rcases mem_replaceNth cs i new c hc with rfl | hmem
  · exact hnew
  · exact hcs c hmem

theorem modifyAt_preserves_IsDyadic
    (t : PTree) (a : Address) (f : PTree → PTree)
    (hdy : PTree.IsDyadic t)
    (hf : ∀ s, PTree.IsDyadic s → PTree.IsDyadic (f s))
    (t' : PTree)
    (hmod : PTree.modifyAt t a f = some t') :
    PTree.IsDyadic t' := by
  induction a generalizing t t' with
  | nil =>
      simp [PTree.modifyAt] at hmod
      cases hmod
      exact hf t hdy
  | cons i rest ih =>
      cases t with
      | leaf s =>
          simp [PTree.modifyAt] at hmod
      | node r s cs =>
          simp [PTree.IsDyadic] at hdy
          rcases hdy with ⟨hlen, hchildren⟩
          by_cases hi : i < cs.length
          · cases hrec : PTree.modifyAt (cs[i]) rest f with
            | none =>
                simp [PTree.modifyAt, hi, hrec] at hmod
            | some child' =>
                simp [PTree.modifyAt, hi, hrec] at hmod
                cases hmod
                have hchildDy : PTree.IsDyadic (cs[i]) := by
                  exact hchildren (cs[i]) (by simpa using List.getElem_mem (l := cs) hi)
                have hchild'Dy : PTree.IsDyadic child' := by
                  exact ih (t := cs[i]) (t' := child') hchildDy hrec
                have hlen' : (PTree.replaceNth cs i child').length ≤ 2 := by
                  simpa [replaceNth_length] using hlen
                have hchildren' : ∀ c, c ∈ PTree.replaceNth cs i child' → PTree.IsDyadic c := by
                  intro c hc
                  exact isDyadic_of_mem_replaceNth hchildren hchild'Dy hc
                simpa [PTree.IsDyadic] using And.intro hlen' hchildren'
          · simp [PTree.modifyAt, hi] at hmod

theorem graftMatchingLeafAt_preserves_IsDyadic
    (u t t' : PTree) (a : Address)
    (hu : PTree.IsDyadic u)
    (ht : PTree.IsDyadic t)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    PTree.IsDyadic t' := by
  unfold PTree.graftMatchingLeafAt at h
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at h
  | some sub =>
      cases sub with
      | node r s cs =>
          simp [hsub] at h
      | leaf s =>
          by_cases hmatch : u.conclusion = s
          · simp [hsub, hmatch] at h
            exact modifyAt_preserves_IsDyadic t a (fun _ => u) ht (fun _ _ => hu) t' h
          · simp [hsub, hmatch] at h

theorem matchingLeafGraftings_preserve_IsDyadic
    (u t t' : PTree)
    (hu : PTree.IsDyadic u)
    (ht : PTree.IsDyadic t)
    (hmem : t' ∈ PTree.matchingLeafGraftings u t) :
    PTree.IsDyadic t' := by
  unfold PTree.matchingLeafGraftings at hmem
  rcases List.mem_filterMap.1 hmem with ⟨a, _, hgraft⟩
  exact graftMatchingLeafAt_preserves_IsDyadic u t t' a hu ht hgraft

theorem matchingLeafGraftings_toTree_preserve_IsDyadic
    {base : BaseRel} {s_outer s_inner : MultiSequent}
    (d_outer : NMMS base s_outer)
    (d_inner : NMMS base s_inner)
    {t' : PTree}
    (hmem : t' ∈ PTree.matchingLeafGraftings (NMMS.toTree d_inner) (NMMS.toTree d_outer)) :
    PTree.IsDyadic t' := by
  exact matchingLeafGraftings_preserve_IsDyadic
    (NMMS.toTree d_inner) (NMMS.toTree d_outer) t'
    (toTree_isDyadic d_inner) (toTree_isDyadic d_outer) hmem

@[simp] theorem getElem_replaceNth_self
    (xs : List α) (i : Nat) (y : α) (h : i < (PTree.replaceNth xs i y).length) :
    (PTree.replaceNth xs i y)[i] = y := by
  have hi : i < xs.length := by
    simpa [replaceNth_length] using h
  induction xs generalizing i y with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp [PTree.replaceNth]
      | succ i =>
          simp [PTree.replaceNth] at h hi ⊢
          exact ih i y (by simpa [replaceNth_length] using hi) hi

theorem subtreeAt_modifyAt_append
    (t u : PTree) (a c : Address) (t' : PTree)
    (h : PTree.modifyAt t a (fun _ => u) = some t') :
    PTree.subtreeAt t' (a ++ c) = PTree.subtreeAt u c := by
  induction a generalizing t t' with
  | nil =>
      simp [PTree.modifyAt] at h
      cases h
      simp [PTree.subtreeAt]
  | cons i rest ih =>
      cases t with
      | leaf s =>
          simp [PTree.modifyAt] at h
      | node r s cs =>
          by_cases hi : i < cs.length
          · simp [PTree.modifyAt, hi] at h
            cases hrec : PTree.modifyAt (cs[i]) rest (fun _ => u) with
            | none =>
                simp [hrec] at h
            | some child' =>
                simp [hrec] at h
                cases h
                simp [PTree.subtreeAt, hi]
                have hih :
                    PTree.subtreeAt child' (rest ++ c) = PTree.subtreeAt u c := by
                  exact ih (cs[i]) child' hrec
                simpa [PTree.replaceNth, hi] using hih
          · simp [PTree.modifyAt, hi] at h

theorem subtreeAt_graftMatchingLeafAt_append
    (u t : PTree) (a c : Address) (t' : PTree)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    PTree.subtreeAt t' (a ++ c) = PTree.subtreeAt u c := by
  unfold PTree.graftMatchingLeafAt at h
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at h
  | some sub =>
      cases sub with
      | node r s cs =>
          simp [hsub] at h
      | leaf s =>
          simp [hsub] at h
          exact subtreeAt_modifyAt_append t u a c t' h.2

theorem addresses_after_graft_split
    (u t : PTree) (a c : Address) (t' : PTree)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    PTree.subtreeAt t' (a ++ c) = PTree.subtreeAt u c := by
  exact subtreeAt_graftMatchingLeafAt_append u t a c t' h

theorem subtreeAt_graftMatchingLeafAt_self
    (u t : PTree) (a : Address) (t' : PTree)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    PTree.subtreeAt t' a = some u := by
  simpa using subtreeAt_graftMatchingLeafAt_append u t a [] t' h

theorem graftable_after_graft_split_inner
    (x y z : PTree) (a c : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z')
    (hb : PTree.IsGraftableLeafAt x z' (a ++ c)) :
    PTree.IsGraftableLeafAt x y c := by
  rw [PTree.IsGraftableLeafAt_iff] at hb ⊢
  have hs :
      PTree.subtreeAt z' (a ++ c) = PTree.subtreeAt y c := by
    exact subtreeAt_graftMatchingLeafAt_append y z a c z' h
  rw [hs] at hb
  exact hb

theorem graftable_after_graft_split
    (x y z : PTree) (a c : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z')
    (hb : PTree.IsGraftableLeafAt x z' (a ++ c)) :
    PTree.IsGraftableLeafAt x y c := by
  exact graftable_after_graft_split_inner x y z a c z' h hb

@[simp] theorem getElem_replaceNth_of_ne
    (xs : List α) (i j : Nat) (y : α)
    (hj : j < xs.length) (hij : j ≠ i) :
    (PTree.replaceNth xs i y)[j]'(by simpa [replaceNth_length] using hj) = xs[j] := by
  induction xs generalizing i j with
  | nil =>
      cases hj
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              cases (hij rfl)
          | succ j =>
              simp [PTree.replaceNth]
      | succ i =>
          cases j with
          | zero =>
              simp [PTree.replaceNth]
          | succ j =>
              simp [PTree.replaceNth] at hj ⊢
              exact ih i j hj (by
                intro hji
                apply hij
                simpa [hji])

theorem comparable_cons_cons_of_comparable
    {i : Nat} {a b : Address}
    (h : PTree.comparable a b) :
    PTree.comparable (i :: a) (i :: b) := by
  cases h with
  | inl ha =>
      left
      rcases ha with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simp [PTree.isAncestorOf, hc]
  | inr hb =>
      right
      rcases hb with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simp [PTree.isAncestorOf, hc]

theorem subtreeAt_modifyAt_of_not_comparable
    (t u : PTree) (a b : Address) (t' : PTree)
    (h : PTree.modifyAt t a (fun _ => u) = some t')
    (hb : ¬ PTree.comparable a b) :
    PTree.subtreeAt t' b = PTree.subtreeAt t b := by
  induction a generalizing t t' b with
  | nil =>
      exfalso
      apply hb
      exact Or.inl (PTree.root_isAncestorOf b)

  | cons i rest ih =>
      cases b with
      | nil =>
          exfalso
          apply hb
          exact Or.inr (PTree.root_isAncestorOf (i :: rest))

      | cons j brest =>
          cases t with
          | leaf s =>
              simp [PTree.modifyAt] at h

          | node r s cs =>
              by_cases hi : i < cs.length
              · simp [PTree.modifyAt, hi] at h
                cases hrec : PTree.modifyAt (cs[i]) rest (fun _ => u) with
                | none =>
                    simp [hrec] at h
                | some child' =>
                    simp [hrec] at h
                    cases h
                    by_cases hij : j = i
                    · subst hij
                      have hb' : ¬ PTree.comparable rest brest := by
                        intro hcomp
                        apply hb
                        exact comparable_cons_cons_of_comparable hcomp
                      simp [PTree.subtreeAt, hi]
                      exact ih (t := cs[j]) (b := brest) (t' := child') hrec hb'

                    · by_cases hj : j < cs.length
                      · have hlen : j < (PTree.replaceNth cs i child').length := by
                          simpa [replaceNth_length] using hj
                        have hget :
                            (PTree.replaceNth cs i child')[j] = cs[j] := by
                          simpa using getElem_replaceNth_of_ne cs i j child' hj hij
                        simp [PTree.subtreeAt, hj, hlen, hget]

                      · have hlen : ¬ j < (PTree.replaceNth cs i child').length := by
                          simpa [replaceNth_length] using hj
                        simp [PTree.subtreeAt, hj, hlen]

              · simp [PTree.modifyAt, hi] at h

theorem subtreeAt_graftMatchingLeafAt_of_not_comparable
    (u t : PTree) (a b : Address) (t' : PTree)
    (h : PTree.graftMatchingLeafAt u t a = some t')
    (hb : ¬ PTree.comparable a b) :
    PTree.subtreeAt t' b = PTree.subtreeAt t b := by
  unfold PTree.graftMatchingLeafAt at h
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at h
  | some sub =>
      cases sub with
      | node r s cs =>
          simp [hsub] at h
      | leaf s =>
          simp [hsub] at h
          exact subtreeAt_modifyAt_of_not_comparable t u a b t' h.2 hb

theorem graftable_after_graft_split_outer
    (x y z : PTree) (a b : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z')
    (hb : ¬ PTree.comparable a b)
    (hg : PTree.IsGraftableLeafAt x z' b) :
    PTree.IsGraftableLeafAt x z b := by
  rw [PTree.IsGraftableLeafAt_iff] at hg ⊢
  rw [subtreeAt_graftMatchingLeafAt_of_not_comparable y z a b z' h hb] at hg
  exact hg

/-
###############################################################################
## Next structural lemmas toward the tree-level pre-Lie identity

These lemmas isolate the two fundamental behaviours of double grafting:

1. Inner exchange:
   grafting inside the newly inserted subtree is the same as first grafting
   inside that subtree, then inserting the result.

2. Incomparable commutation:
   graftings at incomparable addresses commute.

Once these are established, the tree-level pre-Lie identity should follow by
splitting two-step graftings into:
- inner terms, corresponding to (x ▷ y) ▷ z;
- outer/incomparable terms, symmetric in x and y.
###############################################################################
-/

/-- If a graft of `y` into `z` at `a` succeeds, then every subtree below `a`
is exactly read from `y` with the prefix `a` removed. This is the already-proved
inner-address lemma, restated here for convenience. -/
theorem graftMatchingLeafAt_inner_subtree
    (y z : PTree) (a c : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z') :
    PTree.subtreeAt z' (a ++ c) = PTree.subtreeAt y c := by
  exact subtreeAt_graftMatchingLeafAt_append y z a c z' h

/-- Inner graftability transport:
if `x` is graftable into the result of grafting `y` into `z` at an address
of the form `a ++ c`, then `x` was already graftable into `y` at `c`. -/
theorem graftMatchingLeafAt_inner_graftable
    (x y z : PTree) (a c : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z')
    (hg : PTree.IsGraftableLeafAt x z' (a ++ c)) :
    PTree.IsGraftableLeafAt x y c := by
  exact graftable_after_graft_split_inner x y z a c z' h hg

/-- Outer graftability transport:
if `x` is graftable at an address incomparable with `a` after grafting `y`
into `z` at `a`, then it was already graftable there in the original `z`. -/
theorem graftMatchingLeafAt_outer_graftable
    (x y z : PTree) (a b : Address) (z' : PTree)
    (h : PTree.graftMatchingLeafAt y z a = some z')
    (hb : ¬ PTree.comparable a b)
    (hg : PTree.IsGraftableLeafAt x z' b) :
    PTree.IsGraftableLeafAt x z b := by
  exact graftable_after_graft_split_outer x y z a b z' h hb hg

/-- Successful matching-leaf grafting preserves the overall root conclusion. -/
theorem graftMatchingLeafAt_preserves_conclusion
    (u t t' : PTree) (a : Address)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    t'.conclusion = t.conclusion := by
  cases a with
  | nil =>
      cases t with
      | leaf s =>
          unfold PTree.graftMatchingLeafAt at h
          by_cases hmatch : u.conclusion = s
          · simp [PTree.subtreeAt, PTree.modifyAt, hmatch] at h
            cases h
            simpa [PTree.conclusion] using hmatch
          · simp [PTree.subtreeAt, PTree.modifyAt, hmatch] at h
      | node r s cs =>
          unfold PTree.graftMatchingLeafAt at h
          simp [PTree.subtreeAt] at h

  | cons i rest =>
      cases t with
      | leaf s =>
          unfold PTree.graftMatchingLeafAt at h
          simp [PTree.subtreeAt] at h

      | node r s cs =>
          unfold PTree.graftMatchingLeafAt at h
          by_cases hi : i < cs.length
          · cases hsub : PTree.subtreeAt cs[i] rest with
            | none =>
                simp [PTree.subtreeAt, hi, hsub] at h
            | some sub =>
                cases sub with
                | node r' s' cs' =>
                    simp [PTree.subtreeAt, hi, hsub] at h
                | leaf s' =>
                    by_cases hmatch : u.conclusion = s'
                    · simp [PTree.subtreeAt, hi, hsub, hmatch] at h
                      cases hmod : PTree.modifyAt cs[i] rest (fun _ => u) with
                      | none =>
                          simp [PTree.modifyAt, hi, hmod] at h
                      | some child' =>
                          simp [PTree.modifyAt, hi, hmod] at h
                          cases h
                          simp [PTree.conclusion]
                    · simp [PTree.subtreeAt, hi, hsub, hmatch] at h
          · simp [PTree.subtreeAt, hi] at h

@[simp] theorem replaceNth_replaceNth_same
    (xs : List α) (i : Nat) (y z : α) :
    PTree.replaceNth (PTree.replaceNth xs i y) i z =
      PTree.replaceNth xs i z := by
  induction xs generalizing i with
  | nil =>
      cases i <;> simp [PTree.replaceNth]
  | cons x xs ih =>
      cases i <;> simp [PTree.replaceNth, ih]

/-- If we first replace the subtree at `a` by `u`, and then replace the subtree
at `a ++ c` by `x`, this is the same as first replacing inside `u` at `c`
and then putting the resulting tree back at `a`. -/
theorem modifyAt_append_exchange
    (t u x : PTree) (a c : Address)
    (t' u' : PTree)
    (ht : PTree.modifyAt t a (fun _ => u) = some t')
    (hu : PTree.modifyAt u c (fun _ => x) = some u') :
    PTree.modifyAt t' (a ++ c) (fun _ => x) =
      PTree.modifyAt t a (fun _ => u') := by
  induction a generalizing t t' with
  | nil =>
      simp [PTree.modifyAt] at ht ⊢
      cases ht
      simpa [PTree.modifyAt] using hu
  | cons i rest ih =>
      cases t with
      | leaf s =>
          simp [PTree.modifyAt] at ht
      | node r s cs =>
          by_cases hi : i < cs.length
          · simp [PTree.modifyAt, hi] at ht ⊢
            cases hrec : PTree.modifyAt (cs[i]) rest (fun _ => u) with
            | none =>
                simp [hrec] at ht
            | some child' =>
                simp [hrec] at ht
                cases ht
                have hih :
                    PTree.modifyAt child' (rest ++ c) (fun _ => x) =
                      PTree.modifyAt (cs[i]) rest (fun _ => u') := by
                  exact ih (t := cs[i]) (t' := child') hrec
                cases hright : PTree.modifyAt (cs[i]) rest (fun _ => u') with
                | none =>
                    have hchild :
                        PTree.modifyAt child' (rest ++ c) (fun _ => x) = none := by
                      rw [hih]
                      exact hright
                    simpa [PTree.modifyAt, hi, hchild]
                | some child'' =>
                    have hchild :
                        PTree.modifyAt child' (rest ++ c) (fun _ => x) = some child'' := by
                      rw [hih]
                      exact hright
                    simpa [PTree.modifyAt, hi, hchild, replaceNth_replaceNth_same]
          · simp [PTree.modifyAt, hi] at ht

/-- Inner exchange for successful grafts.

If grafting `y` into `z` at `a` succeeds, and grafting `x` into `y` at `c`
succeeds, then grafting `x` into the already-grafted tree at `a ++ c`
is the same as first forming the grafted version of `y` and then inserting
that at `a`.
-/
theorem graftMatchingLeafAt_inner_exchange
    (x y z : PTree) (a c : Address)
    (z' y' : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxy : PTree.graftMatchingLeafAt x y c = some y') :
    PTree.graftMatchingLeafAt x z' (a ++ c) = PTree.graftMatchingLeafAt y' z a := by
  have hs1 : PTree.subtreeAt z' (a ++ c) = PTree.subtreeAt y c := by
    exact subtreeAt_graftMatchingLeafAt_append y z a c z' hyz

  have hs2 : PTree.subtreeAt y c = some (PTree.leaf x.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff x y c).mp
      (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x y c y' hxy)

  have hs : PTree.subtreeAt z' (a ++ c) = some (PTree.leaf x.conclusion) := by
    rw [hs1, hs2]

  have hyroot : PTree.subtreeAt z a = some (PTree.leaf y.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff y z a).mp
      (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z a z' hyz)

  have hconc : y'.conclusion = y.conclusion := by
    exact graftMatchingLeafAt_preserves_conclusion x y y' c hxy

  have hmod_yz : PTree.modifyAt z a (fun _ => y) = some z' := by
    unfold PTree.graftMatchingLeafAt at hyz
    simp [hyroot] at hyz
    exact hyz

  have hmod_xy : PTree.modifyAt y c (fun _ => x) = some y' := by
    unfold PTree.graftMatchingLeafAt at hxy
    simp [hs2] at hxy
    exact hxy

  have hmod_exch :
      PTree.modifyAt z' (a ++ c) (fun _ => x) =
        PTree.modifyAt z a (fun _ => y') := by
    exact modifyAt_append_exchange z y x a c z' y' hmod_yz hmod_xy

  unfold PTree.graftMatchingLeafAt
  simp [hs, hyroot, hconc, hmod_exch]

/-- Replacing different indices commutes. -/
theorem replaceNth_replaceNth_of_ne
    (xs : List α) (i j : Nat) (x y : α)
    (hij : i ≠ j) :
    PTree.replaceNth (PTree.replaceNth xs i x) j y =
      PTree.replaceNth (PTree.replaceNth xs j y) i x := by
  induction xs generalizing i j with
  | nil =>
      cases i <;> cases j <;> simp [PTree.replaceNth]
  | cons z zs ih =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              exfalso
              exact hij rfl
          | succ j =>
              simp [PTree.replaceNth]
      | succ i =>
          cases j with
          | zero =>
              simp [PTree.replaceNth]
          | succ j =>
              simp [PTree.replaceNth]
              apply ih
              intro h
              apply hij
              simpa [h]

/-- If we modify at incomparable addresses, the two modifications commute. -/
theorem modifyAt_incomparable_commute
    (t x y : PTree) (a b : Address)
    (hb : ¬ PTree.comparable a b)
    (t₁ t₂ t₃ : PTree)
    (h1 : PTree.modifyAt t a (fun _ => y) = some t₁)
    (h2 : PTree.modifyAt t₁ b (fun _ => x) = some t₂)
    (h3 : PTree.modifyAt t b (fun _ => x) = some t₃) :
    PTree.modifyAt t₃ a (fun _ => y) = some t₂ := by
  induction a generalizing t t₁ t₂ t₃ b with
  | nil =>
      exfalso
      apply hb
      exact Or.inl (PTree.root_isAncestorOf b)

  | cons i rest ih =>
      cases b with
      | nil =>
          exfalso
          apply hb
          exact Or.inr (PTree.root_isAncestorOf (i :: rest))

      | cons j brest =>
          cases t with
          | leaf s =>
              simp [PTree.modifyAt] at h1

          | node r s cs =>
              by_cases hi : i < cs.length
              · by_cases hj : j < cs.length
                · cases h1c : PTree.modifyAt (cs[i]) rest (fun _ => y) with
                  | none =>
                      simp [PTree.modifyAt, hi, h1c] at h1
                  | some ci =>
                      simp [PTree.modifyAt, hi, h1c] at h1
                      cases h1

                      cases h3c : PTree.modifyAt (cs[j]) brest (fun _ => x) with
                      | none =>
                          simp [PTree.modifyAt, hj, h3c] at h3
                      | some cj =>
                          simp [PTree.modifyAt, hj, h3c] at h3
                          cases h3

                          by_cases hij : i = j
                          · subst hij
                            have hb' : ¬ PTree.comparable rest brest := by
                              intro hcomp
                              apply hb
                              exact comparable_cons_cons_of_comparable hcomp

                            cases h2c : PTree.modifyAt ci brest (fun _ => x) with
                            | none =>
                                simp [PTree.modifyAt, hi, h2c] at h2
                            | some cix =>
                                simp [PTree.modifyAt, hi, h2c] at h2
                                cases h2

                                have hcomm_child :
                                    PTree.modifyAt cj rest (fun _ => y) = some cix := by
                                  exact ih
                                    (t := cs[i]) (b := brest) hb'
                                    (t₁ := ci) (t₂ := cix) (t₃ := cj)
                                    h1c h2c h3c

                                simpa [PTree.modifyAt, hi, hcomm_child,
                                  replaceNth_replaceNth_same]

                          · have hj' : j < (PTree.replaceNth cs i ci).length := by
                              simpa [replaceNth_length] using hj

                            have hgetj :
                                (PTree.replaceNth cs i ci)[j]'hj' = cs[j] := by
                              simpa using
                                (getElem_replaceNth_of_ne cs i j ci hj (by
                                  intro hEq
                                  apply hij
                                  exact hEq.symm))

                            cases h2c :
                                PTree.modifyAt ((PTree.replaceNth cs i ci)[j]'hj')
                                  brest (fun _ => x) with
                            | none =>
                                have h2none :
                                    PTree.modifyAt (cs[j]) brest (fun _ => x) = none := by
                                  simpa [hgetj] using h2c
                                rw [h3c] at h2none
                                simp at h2none
                            | some cix =>
                                have h2c' :
                                    PTree.modifyAt (cs[j]) brest (fun _ => x) = some cix := by
                                  simpa [hgetj] using h2c

                                have hc : cj = cix := by
                                  apply Option.some.inj
                                  exact h3c.symm.trans h2c'
                                subst cj

                                have h2node :
                                    some
                                      (PTree.node r s
                                        (PTree.replaceNth (PTree.replaceNth cs i ci) j cix))
                                      = some t₂ := by
                                  have h2' :
                                      j < cs.length ∧
                                        (match cs[j].modifyAt brest (fun _ => x) with
                                          | none => none
                                          | some child' =>
                                              some (PTree.node r s
                                                (PTree.replaceNth
                                                  (PTree.replaceNth cs i ci) j child')))
                                        = some t₂ := by
                                    simpa [PTree.modifyAt, hj', hgetj, h2c] using h2
                                  have : some
                                      (PTree.node r s
                                        (PTree.replaceNth (PTree.replaceNth cs i ci) j cix))
                                      = some t₂ := by
                                    simpa [h2c'] using h2'.2
                                  exact this

                                have hi' : i < (PTree.replaceNth cs j cix).length := by
                                  simpa [replaceNth_length] using hi

                                have hgeti :
                                    (PTree.replaceNth cs j cix)[i]'hi' = cs[i] := by
                                  simpa using
                                    (getElem_replaceNth_of_ne cs j i cix hi (by
                                      intro hEq
                                      apply hij
                                      exact hEq))

                                have hcomm :
                                    PTree.replaceNth (PTree.replaceNth cs i ci) j cix =
                                      PTree.replaceNth (PTree.replaceNth cs j cix) i ci := by
                                  apply replaceNth_replaceNth_of_ne
                                  intro hEq
                                  apply hij
                                  exact hEq

                                have htarget :
                                    PTree.modifyAt
                                      (PTree.node r s (PTree.replaceNth cs j cix))
                                      (i :: rest) (fun _ => y) =
                                      some
                                        (PTree.node r s
                                          (PTree.replaceNth (PTree.replaceNth cs j cix) i ci)) := by
                                  simpa [PTree.modifyAt, hi, replaceNth_length, hgeti, h1c]

                                have hrhs :
                                    some
                                      (PTree.node r s
                                        (PTree.replaceNth (PTree.replaceNth cs j cix) i ci))
                                      = some t₂ := by
                                  simpa [hcomm] using h2node

                                exact htarget.trans hrhs

                · have h3none : PTree.modifyAt (PTree.node r s cs) (j :: brest) (fun _ => x) = none := by
                    simp [PTree.modifyAt, hj]
                  rw [h3none] at h3
                  simp at h3

              · have h1none : PTree.modifyAt (PTree.node r s cs) (i :: rest) (fun _ => y) = none := by
                  simp [PTree.modifyAt, hi]
                rw [h1none] at h1
                simp at h1

/-- Incomparable successful grafts commute. -/
theorem graftMatchingLeafAt_incomparable_commute
    (x y z : PTree) (a b : Address)
    (hb : ¬ PTree.comparable a b)
    (z₁ z₂ z₃ : PTree)
    (h1 : PTree.graftMatchingLeafAt y z a = some z₁)
    (h2 : PTree.graftMatchingLeafAt x z₁ b = some z₂)
    (h3 : PTree.graftMatchingLeafAt x z b = some z₃) :
    PTree.graftMatchingLeafAt y z₃ a = some z₂ := by
  have hg1 : PTree.IsGraftableLeafAt y z a := by
    exact PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z a z₁ h1

  have hg3 : PTree.IsGraftableLeafAt x z b := by
    exact PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z b z₃ h3

  have hg2 : PTree.IsGraftableLeafAt y z₃ a := by
    rw [PTree.IsGraftableLeafAt_iff] at hg1 ⊢
    rw [subtreeAt_graftMatchingLeafAt_of_not_comparable x z b a z₃ h3]
    · exact hg1
    · intro hcomp
      apply hb
      exact Or.elim hcomp Or.inr Or.inl

  have hs1 : PTree.subtreeAt z a = some (PTree.leaf y.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff y z a).mp hg1

  have hs2 : PTree.subtreeAt z₃ a = some (PTree.leaf y.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff y z₃ a).mp hg2

  have hs3 : PTree.subtreeAt z b = some (PTree.leaf x.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff x z b).mp hg3

  have hs4 : PTree.subtreeAt z₁ b = some (PTree.leaf x.conclusion) := by
    exact (PTree.IsGraftableLeafAt_iff x z₁ b).mp
      (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z₁ b z₂ h2)

  have hmod1 : PTree.modifyAt z a (fun _ => y) = some z₁ := by
    unfold PTree.graftMatchingLeafAt at h1
    simp [hs1] at h1
    exact h1

  have hmod2 : PTree.modifyAt z₁ b (fun _ => x) = some z₂ := by
    unfold PTree.graftMatchingLeafAt at h2
    simp [hs4] at h2
    exact h2

  have hmod3 : PTree.modifyAt z b (fun _ => x) = some z₃ := by
    unfold PTree.graftMatchingLeafAt at h3
    simp [hs3] at h3
    exact h3

  have hmod :
      PTree.modifyAt z₃ a (fun _ => y) = some z₂ := by
    exact modifyAt_incomparable_commute z x y a b hb z₁ z₂ z₃ hmod1 hmod2 hmod3

  unfold PTree.graftMatchingLeafAt
  simp [hs2, hmod]

/-- Inner two-step grafts can be re-expressed by first grafting inside the
inserted tree, then inserting the result back into the outer tree. -/
theorem two_step_graft_inner
    (x y z : PTree) (a c : Address)
    (z' y' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxy : PTree.graftMatchingLeafAt x y c = some y')
    (hw  : PTree.graftMatchingLeafAt x z' (a ++ c) = some w) :
    PTree.graftMatchingLeafAt y' z a = some w := by
  have hexch :
      PTree.graftMatchingLeafAt x z' (a ++ c) =
        PTree.graftMatchingLeafAt y' z a := by
    exact graftMatchingLeafAt_inner_exchange x y z a c z' y' hyz hxy
  simpa [hexch] using hw

/-- Outer two-step grafts at incomparable addresses commute. -/
theorem two_step_graft_outer
    (x y z : PTree) (a b : Address)
    (z' z₃ w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hb  : ¬ PTree.comparable a b)
    (hxz': PTree.graftMatchingLeafAt x z' b = some w)
    (hxz : PTree.graftMatchingLeafAt x z b = some z₃) :
    PTree.graftMatchingLeafAt y z₃ a = some w := by
  exact graftMatchingLeafAt_incomparable_commute
    x y z a b hb z' w z₃ hyz hxz' hxz

/-- Structural two-step decomposition, assuming the second graft site has already
been classified as either inner (`b = a ++ c`) or outer (`¬ comparable a b`).

This is the Lean-friendly form of the decomposition behind the pre-Lie identity.
The remaining work is to prove the address-classification lemma saying that every
successful second graft falls into one of these two cases. -/
theorem two_step_graft_decomposition
    (x y z : PTree) (a b : Address)
    (z' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxz' : PTree.graftMatchingLeafAt x z' b = some w)
    (hclass : (∃ c, b = a ++ c) ∨ ¬ PTree.comparable a b) :
    (∃ c y',
        b = a ++ c ∧
        PTree.graftMatchingLeafAt x y c = some y' ∧
        PTree.graftMatchingLeafAt y' z a = some w)
    ∨
    (∃ z₃,
        ¬ PTree.comparable a b ∧
        PTree.graftMatchingLeafAt x z b = some z₃ ∧
        PTree.graftMatchingLeafAt y z₃ a = some w) := by
  cases hclass with
  | inl hinner =>
      rcases hinner with ⟨c, rfl⟩
      have hg_inner : PTree.IsGraftableLeafAt x y c := by
        exact graftMatchingLeafAt_inner_graftable x y z a c z' hyz
          (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' (a ++ c) w hxz')
      obtain ⟨y', hxy⟩ := PTree.graftMatchingLeafAt_spec x y c hg_inner
      left
      refine ⟨c, y', rfl, hxy, ?_⟩
      exact two_step_graft_inner x y z a c z' y' w hyz hxy hxz'

  | inr hout =>
      have hg_outer : PTree.IsGraftableLeafAt x z b := by
        exact graftMatchingLeafAt_outer_graftable x y z a b z' hyz hout
          (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' b w hxz')
      obtain ⟨z₃, hxz⟩ := PTree.graftMatchingLeafAt_spec x z b hg_outer
      right
      refine ⟨z₃, hout, hxz, ?_⟩
      exact two_step_graft_outer x y z a b z' z₃ w hyz hout hxz' hxz

/-- If `a` points to a leaf, then any strict extension of `a` is invalid. -/
theorem subtreeAt_eq_leaf_append_none
    (t : PTree) (a c : Address) (s : MultiSequent)
    (h : PTree.subtreeAt t a = some (PTree.leaf s))
    (hc : c ≠ []) :
    PTree.subtreeAt t (a ++ c) = none := by
  induction a generalizing t with
  | nil =>
      cases t with
      | leaf s' =>
          simp [PTree.subtreeAt] at h
          cases h
          cases c with
          | nil =>
              cases hc rfl
          | cons i rest =>
              simp [PTree.subtreeAt]
      | node r s' cs =>
          simp [PTree.subtreeAt] at h

  | cons i rest ih =>
      cases t with
      | leaf s' =>
          simp [PTree.subtreeAt] at h
      | node r s' cs =>
          by_cases hi : i < cs.length
          · simp [PTree.subtreeAt, hi] at h ⊢
            exact ih (cs[i]) h
          · simp [PTree.subtreeAt, hi] at h

/-- After grafting `y` into `z` at address `a`, any successful second graft
address `b` is either inside the newly inserted subtree (`b = a ++ c`) or
incomparable with `a`. -/
theorem graftMatchingLeafAt_address_classification
    (x y z : PTree) (a b : Address)
    (z' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxz' : PTree.graftMatchingLeafAt x z' b = some w) :
    (∃ c, b = a ++ c) ∨ ¬ PTree.comparable a b := by
  by_cases hcomp : PTree.comparable a b
  · cases hcomp with
    | inl hab =>
        rcases hab with ⟨c, hc⟩
        exact Or.inl ⟨c, hc⟩
    | inr hba =>
        rcases hba with ⟨d, hd⟩
        cases d with
        | nil =>
            left
            refine ⟨[], ?_⟩
            simpa using hd.symm
        | cons j rest =>
            have hbLeaf : PTree.subtreeAt z' b = some (PTree.leaf x.conclusion) := by
              exact (PTree.IsGraftableLeafAt_iff x z' b).mp
                (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' b w hxz')

            have haY : PTree.subtreeAt z' a = some y := by
              exact subtreeAt_graftMatchingLeafAt_self y z a z' hyz

            have hnone : PTree.subtreeAt z' (b ++ (j :: rest)) = none := by
              exact subtreeAt_eq_leaf_append_none z' b (j :: rest) x.conclusion hbLeaf (by simp)

            rw [hd] at haY
            rw [hnone] at haY
            simp at haY
  · exact Or.inr hcomp

/--
Conceptual restatement of the previous theorem in rooted-tree language:
after grafting at `a`, any successful second graft address `b` either lies on
or below the inserted branch, or else is genuinely incomparable with it.
-/
theorem graftMatchingLeafAt_address_regime
    (x y z : PTree) (a b : Address)
    (z' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxz' : PTree.graftMatchingLeafAt x z' b = some w) :
    PTree.Dominates a b ∨ PTree.Incomparable a b := by
  rcases graftMatchingLeafAt_address_classification x y z a b z' w hyz hxz' with h | h
  · rcases h with ⟨c, hc⟩
    exact Or.inl ⟨c, hc⟩
  · exact Or.inr h

/--
If the second successful graft address is not on or below the first graft
address, then the two addresses are separated by a branching node.
-/
theorem graftMatchingLeafAt_address_has_separator_of_incomparable
    (x y z : PTree) (a b : Address)
    (z' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxz' : PTree.graftMatchingLeafAt x z' b = some w)
    (hinc : PTree.Incomparable a b) :
    ∃ s : Address, PTree.IsSeparator s a b := by
  exact PTree.exists_separator_of_incomparable a b hinc

/-- Tree-level pre-Lie identity.

At this point the remaining ingredient is the address-classification lemma:
every successful second graft after grafting at `a` is either at an address
of the form `a ++ c`, or at an address incomparable with `a`.

Once that bookkeeping lemma is in place, the proof should proceed by:
1. expanding both sides on generators;
2. splitting two-step grafts using `two_step_graft_decomposition`;
3. using `two_step_graft_inner` for inner terms;
4. using `two_step_graft_outer` for outer terms.
-/

theorem two_step_graft_decomposition_full
    (x y z : PTree) (a b : Address)
    (z' w : PTree)
    (hyz : PTree.graftMatchingLeafAt y z a = some z')
    (hxz' : PTree.graftMatchingLeafAt x z' b = some w) :
    (∃ c y',
        b = a ++ c ∧
        PTree.graftMatchingLeafAt x y c = some y' ∧
        PTree.graftMatchingLeafAt y' z a = some w)
    ∨
    (∃ z₃,
        ¬ PTree.comparable a b ∧
        PTree.graftMatchingLeafAt x z b = some z₃ ∧
        PTree.graftMatchingLeafAt y z₃ a = some w) := by
  apply two_step_graft_decomposition x y z a b z' w hyz hxz'
  exact graftMatchingLeafAt_address_classification x y z a b z' w hyz hxz'

theorem graftPreLie_tree_tree_apply
    (u t w : PTree) :
    graftPreLie (treeGen u) (PTree.graftPreLieTree t w)
      =
    (PTree.matchingLeafGraftings t w).foldr
      (fun z' acc => graftPreLie (treeGen u) (treeGen z') + acc) 0 := by
  let xs := PTree.matchingLeafGraftings t w
  change graftPreLie (treeGen u) (xs.foldr (fun x acc => treeGen x + acc) 0) =
    xs.foldr (fun z' acc => graftPreLie (treeGen u) (treeGen z') + acc) 0
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldr]
      change
        graftPreLie (treeGen u)
          (treeGen x + xs.foldr (fun x acc => treeGen x + acc) 0)
        =
        graftPreLie (treeGen u) (treeGen x) +
          xs.foldr (fun z' acc => graftPreLie (treeGen u) (treeGen z') + acc) 0
      rw [map_add, ih]

theorem graftPreLie_foldr_apply_eq_flatMap_count_right
    (x w : PTree) (xs : List PTree) :
    ((xs.foldr
        (fun z' acc => graftPreLie (treeGen x) (treeGen z') + acc) 0) w)
      =
    (((xs.flatMap (fun z' => PTree.matchingLeafGraftings x z')).count w : Nat) : ℤ) := by
  induction xs with
  | nil =>
      simp
  | cons z' xs ih =>
      simp only [List.foldr, List.flatMap_cons, Finsupp.add_apply, Finsupp.zero_apply]
      rw [graftPreLie_on_generators]
      rw [PTree.graftPreLieTree]
      rw [PTree.foldr_treeGen_apply]
      rw [ih]
      rw [List.count_append]
      norm_num

theorem graftPreLie_foldr_apply_eq_flatMap_count_left
    (z w : PTree) (xs : List PTree) :
    ((xs.foldr
        (fun y' acc => graftPreLie (treeGen y') (treeGen z) + acc) 0) w)
      =
    (((xs.flatMap (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) : ℤ) := by
  induction xs with
  | nil =>
      simp
  | cons y' xs ih =>
      simp only [List.foldr, List.flatMap_cons, Finsupp.add_apply, Finsupp.zero_apply]
      rw [graftPreLie_on_generators]
      rw [PTree.graftPreLieTree]
      rw [PTree.foldr_treeGen_apply]
      rw [ih]
      rw [List.count_append]
      norm_num

theorem graftPreLie_coeff_x_on_yz
    (x y z w : PTree) :
    (graftPreLie (treeGen x) (PTree.graftPreLieTree y z)) w =
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : ℤ) := by
  rw [graftPreLie_tree_tree_apply]
  exact graftPreLie_foldr_apply_eq_flatMap_count_right x w
    (PTree.matchingLeafGraftings y z)

theorem graftPreLie_tree_tree_apply_left
    (u t w : PTree) :
    graftPreLie (PTree.graftPreLieTree u t) (treeGen w)
      =
    (PTree.matchingLeafGraftings u t).foldr
      (fun y' acc => graftPreLie (treeGen y') (treeGen w) + acc) 0 := by
  let xs := PTree.matchingLeafGraftings u t
  change graftPreLie (xs.foldr (fun x acc => treeGen x + acc) 0) (treeGen w) =
    xs.foldr (fun y' acc => graftPreLie (treeGen y') (treeGen w) + acc) 0
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldr]
      rw [LinearMap.map_add]
      simp only [LinearMap.add_apply]
      rw [ih]

theorem graftPreLie_coeff_xy_on_z
    (x y z w : PTree) :
    (graftPreLie (PTree.graftPreLieTree x y) (treeGen z)) w =
      (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : ℤ) := by
  rw [graftPreLie_tree_tree_apply_left]
  exact graftPreLie_foldr_apply_eq_flatMap_count_left z w
    (PTree.matchingLeafGraftings x y)

lemma count_flatMap_eq_sum
    (l : List α) (f : α → List β) (w : β) :
    (l.flatMap f).count w =
      (l.map (fun x => (f x).count w)).sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [List.count_append, ih]


/-- Every successful two-step graft on the `y ▷ z` side landing at `w`
corresponds to exactly one successful witness on one of the two right-hand
parametrisations. -/
theorem two_step_graft_witness_balance
    (x y z w : PTree) :
    (∀ z',
        z' ∈ PTree.matchingLeafGraftings y z →
        w ∈ PTree.matchingLeafGraftings x z' →
        (∃ z₃,
            z₃ ∈ PTree.matchingLeafGraftings x z ∧
            w ∈ PTree.matchingLeafGraftings y z₃)
        ∨
        (∃ y',
            y' ∈ PTree.matchingLeafGraftings x y ∧
            w ∈ PTree.matchingLeafGraftings y' z))
    ∧
    (∀ z₃,
        z₃ ∈ PTree.matchingLeafGraftings x z →
        w ∈ PTree.matchingLeafGraftings y z₃ →
        (∃ z',
            z' ∈ PTree.matchingLeafGraftings y z ∧
            w ∈ PTree.matchingLeafGraftings x z')
        ∨
        (∃ y',
            y' ∈ PTree.matchingLeafGraftings y x ∧
            w ∈ PTree.matchingLeafGraftings y' z))
    := by
  constructor
  · intro z' hz' hwx
    unfold PTree.matchingLeafGraftings at hz' hwx
    simp [List.mem_filterMap] at hz' hwx
    rcases hz' with ⟨a, ha, hyz⟩
    rcases hwx with ⟨b, hb, hxz'⟩
    have hdecomp :=
      two_step_graft_decomposition_full x y z a b z' w hyz hxz'
    cases hdecomp with
    | inl hinner =>
        rcases hinner with ⟨c, y', hb_eq, hxy, hy'z⟩
        right
        refine ⟨y', ?_, ?_⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨c, by
            have hs : PTree.subtreeAt y c = some (PTree.leaf x.conclusion) := by
              exact (PTree.IsGraftableLeafAt_iff x y c).mp
                (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x y c y' hxy)
            exact PTree.subtreeAt_some_implies_mem_allAddresses y (PTree.leaf x.conclusion) c hs
          , hxy⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨a, by
            have hs : PTree.subtreeAt z a = some (PTree.leaf y'.conclusion) := by
              have hs0 : PTree.subtreeAt z a = some (PTree.leaf y.conclusion) := by
                exact (PTree.IsGraftableLeafAt_iff y z a).mp
                  (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z a z' hyz)
              have hconc : y'.conclusion = y.conclusion := by
                exact graftMatchingLeafAt_preserves_conclusion x y y' c hxy
              simpa [hconc] using hs0
            exact PTree.subtreeAt_some_implies_mem_allAddresses z (PTree.leaf y'.conclusion) a hs
          , hy'z⟩
    | inr hout =>
        rcases hout with ⟨z₃, hinc, hxz, hyz₃⟩
        left
        refine ⟨z₃, ?_, ?_⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨b, by
            have hs : PTree.subtreeAt z b = some (PTree.leaf x.conclusion) := by
              exact graftMatchingLeafAt_outer_graftable x y z a b z' hyz hinc
                ((PTree.IsGraftableLeafAt_iff x z' b).mp
                  (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' b w hxz'))
            exact PTree.subtreeAt_some_implies_mem_allAddresses z (PTree.leaf x.conclusion) b hs
          , hxz⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨a, by
            have hs : PTree.subtreeAt z₃ a = some (PTree.leaf y.conclusion) := by
              exact (PTree.IsGraftableLeafAt_iff y z₃ a).mp
                (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z₃ a w hyz₃)
            exact PTree.subtreeAt_some_implies_mem_allAddresses z₃ (PTree.leaf y.conclusion) a hs
          , hyz₃⟩
  · intro z₃ hz₃ hwy
    unfold PTree.matchingLeafGraftings at hz₃ hwy
    simp [List.mem_filterMap] at hz₃ hwy
    rcases hz₃ with ⟨a, ha, hxz⟩
    rcases hwy with ⟨b, hb, hyz₃⟩
    have hdecomp :=
      two_step_graft_decomposition_full y x z a b z₃ w hxz hyz₃
    cases hdecomp with
    | inl hinner =>
        rcases hinner with ⟨c, y', hb_eq, hyx, hy'z⟩
        right
        refine ⟨y', ?_, ?_⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨c, by
            have hs : PTree.subtreeAt x c = some (PTree.leaf y.conclusion) := by
              exact (PTree.IsGraftableLeafAt_iff y x c).mp
                (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y x c y' hyx)
            exact PTree.subtreeAt_some_implies_mem_allAddresses x (PTree.leaf y.conclusion) c hs
          , hyx⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨a, by
            have hs : PTree.subtreeAt z a = some (PTree.leaf y'.conclusion) := by
              have hs0 : PTree.subtreeAt z a = some (PTree.leaf x.conclusion) := by
                exact (PTree.IsGraftableLeafAt_iff x z a).mp
                  (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z a z₃ hxz)
              have hconc : y'.conclusion = x.conclusion := by
                exact graftMatchingLeafAt_preserves_conclusion y x y' c hyx
              simpa [hconc] using hs0
            exact PTree.subtreeAt_some_implies_mem_allAddresses z (PTree.leaf y'.conclusion) a hs, hy'z⟩
    | inr hout =>
        rcases hout with ⟨z', hinc, hyz, hxz'⟩
        left
        refine ⟨z', ?_, ?_⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨b, by
            have hs : PTree.subtreeAt z b = some (PTree.leaf y.conclusion) := by
              exact graftMatchingLeafAt_outer_graftable y x z a b z₃ hxz hinc
                ((PTree.IsGraftableLeafAt_iff y z₃ b).mp
                  (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z₃ b w hyz₃))
            exact PTree.subtreeAt_some_implies_mem_allAddresses z (PTree.leaf y.conclusion) b hs
          , hyz⟩
        · unfold PTree.matchingLeafGraftings
          exact List.mem_filterMap.2 ⟨a, by
            have hs : PTree.subtreeAt z' a = some (PTree.leaf x.conclusion) := by
              exact (PTree.IsGraftableLeafAt_iff x z' a).mp
                (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' a w hxz')
            exact PTree.subtreeAt_some_implies_mem_allAddresses z' (PTree.leaf x.conclusion) a hs
          , hxz'⟩

lemma count_flatMap_eq_count_filterMap_witnesses
    (xs : List α) (f : α → List β) (w : β) :
    ((xs.flatMap f).count w : ℤ) =
      ((xs.map (fun a => (f a).count w)).sum : ℤ) := by
  rw [count_flatMap_eq_sum]


def twoStepWitnessesLeft (x y z : PTree) : List (PTree × PTree) :=
  (((PTree.matchingLeafGraftings y z).flatMap
      (fun z' => (PTree.matchingLeafGraftings x z').map (fun w => (z', w))))
   ++
   ((PTree.matchingLeafGraftings y x).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).map (fun w => (y', w)))))

def twoStepWitnessesRight (x y z : PTree) : List (PTree × PTree) :=
  (((PTree.matchingLeafGraftings x z).flatMap
      (fun z' => (PTree.matchingLeafGraftings y z').map (fun w => (z', w))))
   ++
   ((PTree.matchingLeafGraftings x y).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).map (fun w => (y', w)))))

@[simp] theorem map_snd_map_pair
    (a : PTree) (xs : List PTree) :
    (xs.map (fun w => (a, w))).map Prod.snd = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

@[simp] theorem map_fst_map_pair
    (a : PTree) (xs : List PTree) :
    (xs.map (fun w => (a, w))).map Prod.fst = xs.map (fun _ => a) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

@[simp] theorem map_snd_flatMap_map_pair
    (xs : List PTree) (f : PTree → List PTree) :
    (List.flatMap (fun a => (f a).map (fun w => (a, w))) xs).map Prod.snd
      =
    List.flatMap f xs := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.map_append, map_snd_map_pair, ih]

@[simp] theorem map_snd_twoStepWitnessesLeft
    (x y z : PTree) :
    (twoStepWitnessesLeft x y z).map Prod.snd =
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
       ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  unfold twoStepWitnessesLeft
  simp [List.map_append]

@[simp] theorem map_snd_twoStepWitnessesRight
    (x y z : PTree) :
    (twoStepWitnessesRight x y z).map Prod.snd =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
       ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  unfold twoStepWitnessesRight
  simp [List.map_append]

theorem mem_twoStepWitnessesLeft_iff
    (x y z z' w : PTree) :
    (z', w) ∈ twoStepWitnessesLeft x y z ↔
      (z' ∈ PTree.matchingLeafGraftings y z ∧
       w ∈ PTree.matchingLeafGraftings x z')
      ∨
      (z' ∈ PTree.matchingLeafGraftings y x ∧
       w ∈ PTree.matchingLeafGraftings z' z) := by
  unfold twoStepWitnessesLeft
  simp [List.mem_flatMap]

theorem mem_twoStepWitnessesRight_iff
    (x y z z' w : PTree) :
    (z', w) ∈ twoStepWitnessesRight x y z ↔
      (z' ∈ PTree.matchingLeafGraftings x z ∧
       w ∈ PTree.matchingLeafGraftings y z')
      ∨
      (z' ∈ PTree.matchingLeafGraftings x y ∧
       w ∈ PTree.matchingLeafGraftings z' z) := by
  unfold twoStepWitnessesRight
  simp [List.mem_flatMap]

def matchingLeafGraftWitnesses (u t : PTree) : List (Address × PTree) :=
  (PTree.allAddresses t).filterMap (fun a =>
    match PTree.graftMatchingLeafAt u t a with
    | some t' => some (a, t')
    | none    => none)

@[simp] theorem map_snd_filterMap_pair
    (xs : List Address) (f : Address → Option PTree) :
    (xs.filterMap (fun a =>
      match f a with
      | some t' => some (a, t')
      | none    => none)).map Prod.snd
    =
    xs.filterMap f := by
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      cases h : f a with
      | none =>
          simp [List.filterMap_cons, h, ih]
      | some t' =>
          simp [List.filterMap_cons, h, ih]

@[simp] theorem map_snd_matchingLeafGraftWitnesses
    (u t : PTree) :
    (matchingLeafGraftWitnesses u t).map Prod.snd = PTree.matchingLeafGraftings u t := by
  unfold matchingLeafGraftWitnesses PTree.matchingLeafGraftings
  simpa using
    (map_snd_filterMap_pair
      (xs := PTree.allAddresses t)
      (f := PTree.graftMatchingLeafAt u t))

def twoStepAddrWitnessesLeft (x y z : PTree) : List ((Address × Address) × PTree) :=
  (((matchingLeafGraftWitnesses y z).flatMap
      (fun aw =>
        let a  := aw.1
        let z' := aw.2
        (matchingLeafGraftWitnesses x z').map
          (fun bw => ((a, bw.1), bw.2))))
    ++
   ((matchingLeafGraftWitnesses y x).flatMap
      (fun aw =>
        let a  := aw.1
        let y' := aw.2
        (matchingLeafGraftWitnesses y' z).map
          (fun bw => ((a, bw.1), bw.2)))))

def twoStepAddrWitnessesRight (x y z : PTree) : List ((Address × Address) × PTree) :=
  (((matchingLeafGraftWitnesses x z).flatMap
      (fun aw =>
        let a  := aw.1
        let z' := aw.2
        (matchingLeafGraftWitnesses y z').map
          (fun bw => ((a, bw.1), bw.2))))
    ++
   ((matchingLeafGraftWitnesses x y).flatMap
      (fun aw =>
        let a  := aw.1
        let y' := aw.2
        (matchingLeafGraftWitnesses y' z).map
          (fun bw => ((a, bw.1), bw.2)))))

@[simp] theorem map_snd_map_addr_pair
    (p : Address × PTree) (xs : List (Address × PTree)) :
    (xs.map (fun q => ((p.1, q.1), q.2))).map Prod.snd = xs.map Prod.snd := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

@[simp] theorem map_snd_flatMap_addr_pair
    (xs : List (Address × PTree))
    (f : (Address × PTree) → List (Address × PTree)) :
    (List.flatMap (fun p => (f p).map (fun q => ((p.1, q.1), q.2))) xs).map Prod.snd
      =
    List.flatMap (fun p => (f p).map Prod.snd) xs := by
  induction xs with
  | nil =>
      rfl
  | cons p xs ih =>
      simp only [List.flatMap_cons, List.map_append, map_snd_map_addr_pair, ih]

@[simp] theorem flatMap_fstsnd_eq_of_map_snd
    (xs : List (Address × PTree)) (f : PTree → List PTree) :
    List.flatMap (fun p => f p.2) xs =
      List.flatMap f (xs.map Prod.snd) := by
  induction xs with
  | nil =>
      rfl
  | cons p xs ih =>
      simp [ih]

@[simp] theorem flatMap_snd_eq_flatMap_map_snd
    (xs : List (Address × PTree)) (f : PTree → List PTree) :
    List.flatMap (fun p => f p.2) xs =
      List.flatMap f (xs.map Prod.snd) := by
  induction xs with
  | nil =>
      rfl
  | cons p xs ih =>
      simp [ih]

@[simp] theorem map_snd_twoStepAddrWitnessesLeft
    (x y z : PTree) :
    (twoStepAddrWitnessesLeft x y z).map Prod.snd =
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
       ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  unfold twoStepAddrWitnessesLeft
  simp [List.map_append]
  have h2 :
      List.flatMap (fun p => PTree.matchingLeafGraftings p.2 z)
        (matchingLeafGraftWitnesses y x)
      =
      List.flatMap (fun t => PTree.matchingLeafGraftings t z)
        ((matchingLeafGraftWitnesses y x).map Prod.snd) := by
    exact flatMap_snd_eq_flatMap_map_snd
      (xs := matchingLeafGraftWitnesses y x)
      (f := fun t => PTree.matchingLeafGraftings t z)
  rw [h2]
  simp

@[simp] theorem map_snd_twoStepAddrWitnessesRight
    (x y z : PTree) :
    (twoStepAddrWitnessesRight x y z).map Prod.snd =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
       ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  unfold twoStepAddrWitnessesRight
  simp [List.map_append]
  have h2 :
      List.flatMap (fun p => PTree.matchingLeafGraftings p.2 z)
        (matchingLeafGraftWitnesses x y)
      =
      List.flatMap (fun t => PTree.matchingLeafGraftings t z)
        ((matchingLeafGraftWitnesses x y).map Prod.snd) := by
    exact flatMap_snd_eq_flatMap_map_snd
      (xs := matchingLeafGraftWitnesses x y)
      (f := fun t => PTree.matchingLeafGraftings t z)
  rw [h2]
  simp

theorem twoStepAddrWitnessesLeft_length
    (x y z : PTree) :
    (twoStepAddrWitnessesLeft x y z).length =
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length
        +
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) := by
  rw [← List.length_map (f := Prod.snd) (as := twoStepAddrWitnessesLeft x y z)]
  rw [map_snd_twoStepAddrWitnessesLeft]
  simp [List.length_flatMap]

theorem twoStepAddrWitnessesRight_length
    (x y z : PTree) :
    (twoStepAddrWitnessesRight x y z).length =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).length
        +
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) := by
  rw [← List.length_map (f := Prod.snd) (as := twoStepAddrWitnessesRight x y z)]
  rw [map_snd_twoStepAddrWitnessesRight]
  simp [List.length_flatMap]

theorem mem_twoStepAddrWitnessesLeft_iff
    (x y z : PTree) (a b : Address) (w : PTree) :
    (((a, b), w) ∈ twoStepAddrWitnessesLeft x y z) ↔
      (∃ z',
        (a, z') ∈ matchingLeafGraftWitnesses y z ∧
        (b, w) ∈ matchingLeafGraftWitnesses x z')
      ∨
      (∃ y',
        (a, y') ∈ matchingLeafGraftWitnesses y x ∧
        (b, w) ∈ matchingLeafGraftWitnesses y' z) := by
  unfold twoStepAddrWitnessesLeft
  constructor
  · intro h
    simp [List.mem_flatMap] at h
    rcases h with h | h
    · rcases h with ⟨z', haz', hbw⟩
      exact Or.inl ⟨z', haz', hbw⟩
    · rcases h with ⟨y', hay', hbw⟩
      exact Or.inr ⟨y', hay', hbw⟩
  · intro h
    simp [List.mem_flatMap]
    rcases h with h | h
    · rcases h with ⟨z', haz', hbw⟩
      left
      exact ⟨z', haz', hbw⟩
    · rcases h with ⟨y', hay', hbw⟩
      right
      exact ⟨y', hay', hbw⟩

theorem mem_twoStepAddrWitnessesRight_iff
    (x y z : PTree) (a b : Address) (w : PTree) :
    (((a, b), w) ∈ twoStepAddrWitnessesRight x y z) ↔
      (∃ z',
        (a, z') ∈ matchingLeafGraftWitnesses x z ∧
        (b, w) ∈ matchingLeafGraftWitnesses y z')
      ∨
      (∃ y',
        (a, y') ∈ matchingLeafGraftWitnesses x y ∧
        (b, w) ∈ matchingLeafGraftWitnesses y' z) := by
  unfold twoStepAddrWitnessesRight
  constructor
  · intro h
    simp [List.mem_flatMap] at h
    rcases h with h | h
    · rcases h with ⟨z', haz', hbw⟩
      exact Or.inl ⟨z', haz', hbw⟩
    · rcases h with ⟨y', hay', hbw⟩
      exact Or.inr ⟨y', hay', hbw⟩
  · intro h
    simp [List.mem_flatMap]
    rcases h with h | h
    · rcases h with ⟨z', haz', hbw⟩
      left
      exact ⟨z', haz', hbw⟩
    · rcases h with ⟨y', hay', hbw⟩
      right
      exact ⟨y', hay', hbw⟩

theorem mem_matchingLeafGraftWitnesses_iff
    (u t : PTree) (a : Address) (t' : PTree) :
    (a, t') ∈ matchingLeafGraftWitnesses u t ↔
      a ∈ PTree.allAddresses t ∧
      PTree.graftMatchingLeafAt u t a = some t' := by
  unfold matchingLeafGraftWitnesses
  constructor
  · intro h
    simp [List.mem_filterMap] at h
    rcases h with ⟨a', ha', hpair⟩
    cases hg : PTree.graftMatchingLeafAt u t a' with
    | none =>
        simp [hg] at hpair
    | some s =>
        simp [hg] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        exact ⟨ha', hg⟩
  · intro h
    rcases h with ⟨ha, hg⟩
    simp [List.mem_filterMap]
    exact ⟨a, ha, by simp [hg]⟩

theorem twoStepAddrWitnesses_main_left_to_right
    (x y z : PTree) (a b : Address) (w : PTree)
    (h : ∃ z',
      (a, z') ∈ matchingLeafGraftWitnesses y z ∧
      (b, w) ∈ matchingLeafGraftWitnesses x z') :
    ∃ a' b', ((a', b'), w) ∈ twoStepAddrWitnessesRight x y z := by
  rcases h with ⟨z', haz', hbw⟩
  rw [mem_matchingLeafGraftWitnesses_iff] at haz' hbw
  rcases haz' with ⟨haAddr, hyz⟩
  rcases hbw with ⟨hbAddr, hxz'⟩
  have hdecomp :=
    two_step_graft_decomposition_full x y z a b z' w hyz hxz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hxy, hy'z⟩
      refine ⟨c, a, ?_⟩
      rw [mem_twoStepAddrWitnessesRight_iff]
      right
      refine ⟨y', ?_, ?_⟩
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxy⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x y c y' hxy
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            y (PTree.leaf x.conclusion) c
            ((PTree.IsGraftableLeafAt_iff x y c).mp hg)
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hy'z⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z a w hy'z
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y'.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y' z a).mp hg)
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hxz, hyz₃⟩
      refine ⟨b, a, ?_⟩
      rw [mem_twoStepAddrWitnessesRight_iff]
      left
      refine ⟨z₃, ?_, ?_⟩
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z b z₃ hxz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf x.conclusion) b
            ((PTree.IsGraftableLeafAt_iff x z b).mp hg)
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz₃⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z₃ a w hyz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf y.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y z₃ a).mp hg)

theorem twoStepAddrWitnesses_main_right_to_left
    (x y z : PTree) (a b : Address) (w : PTree)
    (h : ∃ z',
      (a, z') ∈ matchingLeafGraftWitnesses x z ∧
      (b, w) ∈ matchingLeafGraftWitnesses y z') :
    ∃ a' b', ((a', b'), w) ∈ twoStepAddrWitnessesLeft x y z := by
  rcases h with ⟨z', haz', hbw⟩
  rw [mem_matchingLeafGraftWitnesses_iff] at haz' hbw
  rcases haz' with ⟨haAddr, hxz⟩
  rcases hbw with ⟨hbAddr, hyz'⟩
  have hdecomp :=
    two_step_graft_decomposition_full y x z a b z' w hxz hyz'
  cases hdecomp with
  | inl hinner =>
      rcases hinner with ⟨c, y', hbEq, hyx, hy'z⟩
      refine ⟨c, a, ?_⟩
      rw [mem_twoStepAddrWitnessesLeft_iff]
      right
      refine ⟨y', ?_, ?_⟩
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyx⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y x c y' hyx
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            x (PTree.leaf y.conclusion) c
            ((PTree.IsGraftableLeafAt_iff y x c).mp hg)
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hy'z⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z a w hy'z
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y'.conclusion) a
            ((PTree.IsGraftableLeafAt_iff y' z a).mp hg)
  | inr hout =>
      rcases hout with ⟨z₃, hnc, hyz, hxz₃⟩
      refine ⟨b, a, ?_⟩
      rw [mem_twoStepAddrWitnessesLeft_iff]
      left
      refine ⟨z₃, ?_, ?_⟩
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hyz⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z b z₃ hyz
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z (PTree.leaf y.conclusion) b
            ((PTree.IsGraftableLeafAt_iff y z b).mp hg)
      · rw [mem_matchingLeafGraftWitnesses_iff]
        refine ⟨?_, hxz₃⟩
        have hg :=
          PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z₃ a w hxz₃
        exact
          PTree.subtreeAt_some_implies_mem_allAddresses
            z₃ (PTree.leaf x.conclusion) a
            ((PTree.IsGraftableLeafAt_iff x z₃ a).mp hg)

lemma count_map_snd_twoStepAddrWitnessesLeft
    (x y z w : PTree) :
    (((twoStepAddrWitnessesLeft x y z).map Prod.snd).count w : ℤ) =
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')
        ++
        (PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : ℤ) := by
  simp

lemma count_map_snd_twoStepAddrWitnessesRight
    (x y z w : PTree) :
    (((twoStepAddrWitnessesRight x y z).map Prod.snd).count w : ℤ) =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')
        ++
        (PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : ℤ) := by
  simp

/--
If the output multiplicities agree pointwise, then the two raw address-witness
output lists are permutations of each other.
-/
theorem twoStepAddrWitnesses_map_snd_perm_of_count_balance
    (x y z : PTree)
    (hcount : ∀ w : PTree,
      (((twoStepAddrWitnessesLeft x y z).map Prod.snd).count w : ℤ) =
        (((twoStepAddrWitnessesRight x y z).map Prod.snd).count w : ℤ)) :
    List.Perm
      ((twoStepAddrWitnessesLeft x y z).map Prod.snd)
      ((twoStepAddrWitnessesRight x y z).map Prod.snd) := by
  have hsub :
      List.Subperm
        ((twoStepAddrWitnessesLeft x y z).map Prod.snd)
        ((twoStepAddrWitnessesRight x y z).map Prod.snd) := by
    rw [List.subperm_iff_count]
    intro w
    exact le_of_eq (Int.ofNat.inj (hcount w))
  have hsub' :
      List.Subperm
        ((twoStepAddrWitnessesRight x y z).map Prod.snd)
        ((twoStepAddrWitnessesLeft x y z).map Prod.snd) := by
    rw [List.subperm_iff_count]
    intro w
    exact le_of_eq (Int.ofNat.inj (hcount w).symm)
  exact hsub.antisymm hsub'

/--
Pointwise equality of output multiplicities already forces equality of the total
numbers of raw address witnesses on the two sides.
-/
theorem twoStepAddrWitnesses_length_eq_of_count_balance
    (x y z : PTree)
    (hcount : ∀ w : PTree,
      (((twoStepAddrWitnessesLeft x y z).map Prod.snd).count w : ℤ) =
        (((twoStepAddrWitnessesRight x y z).map Prod.snd).count w : ℤ)) :
    (twoStepAddrWitnessesLeft x y z).length =
      (twoStepAddrWitnessesRight x y z).length := by
  have hperm :=
    twoStepAddrWitnesses_map_snd_perm_of_count_balance x y z hcount
  calc
    (twoStepAddrWitnessesLeft x y z).length
        = ((twoStepAddrWitnessesLeft x y z).map Prod.snd).length := by
            simpa using
              (List.length_map (f := Prod.snd)
                (as := twoStepAddrWitnessesLeft x y z)).symm
    _ = ((twoStepAddrWitnessesRight x y z).map Prod.snd).length := by
          exact hperm.length_eq
    _ = (twoStepAddrWitnessesRight x y z).length := by
          simpa using
            (List.length_map (f := Prod.snd)
              (as := twoStepAddrWitnessesRight x y z))

theorem mem_twoStepFlatmapsLeft_iff
    (x y z w : PTree) :
    w ∈
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)))
    ↔
    ∃ a b, (((a, b), w) ∈ twoStepAddrWitnessesLeft x y z) := by
  constructor
  · intro hw
    simp only [List.mem_append, List.mem_flatMap] at hw
    cases hw with
    | inl h =>
        rcases h with ⟨z', hz', hzw⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hz' hzw
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hzw
        rcases hz' with ⟨a, haz⟩
        rcases hzw with ⟨b, hbw⟩
        exact ⟨a, b, by
          rw [mem_twoStepAddrWitnessesLeft_iff]
          left
          exact ⟨z', haz, hbw⟩⟩
    | inr h =>
        rcases h with ⟨y', hyx, hyz⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hyx hyz
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hyx hyz
        rcases hyx with ⟨a, hay⟩
        rcases hyz with ⟨b, hbw⟩
        exact ⟨a, b, by
          rw [mem_twoStepAddrWitnessesLeft_iff]
          right
          exact ⟨y', hay, hbw⟩⟩
  · intro hw
    rcases hw with ⟨a, b, habw⟩
    rw [mem_twoStepAddrWitnessesLeft_iff] at habw
    simp only [List.mem_append, List.mem_flatMap]
    cases habw with
    | inl h =>
        rcases h with ⟨z', haz, hbw⟩
        left
        exact ⟨z', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
    | inr h =>
        rcases h with ⟨y', hay, hbw⟩
        right
        exact ⟨y', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩

theorem mem_twoStepFlatmapsRight_iff
    (x y z w : PTree) :
    w ∈
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)))
    ↔
    ∃ a b, (((a, b), w) ∈ twoStepAddrWitnessesRight x y z) := by
  constructor
  · intro hw
    simp only [List.mem_append, List.mem_flatMap] at hw
    cases hw with
    | inl h =>
        rcases h with ⟨z', hz', hzw⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hz' hzw
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hzw
        rcases hz' with ⟨a, haz⟩
        rcases hzw with ⟨b, hbw⟩
        exact ⟨a, b, by
          rw [mem_twoStepAddrWitnessesRight_iff]
          left
          exact ⟨z', haz, hbw⟩⟩
    | inr h =>
        rcases h with ⟨y', hyx, hyz⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hyx hyz
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hyx hyz
        rcases hyx with ⟨a, hay⟩
        rcases hyz with ⟨b, hbw⟩
        exact ⟨a, b, by
          rw [mem_twoStepAddrWitnessesRight_iff]
          right
          exact ⟨y', hay, hbw⟩⟩
  · intro hw
    rcases hw with ⟨a, b, habw⟩
    rw [mem_twoStepAddrWitnessesRight_iff] at habw
    simp only [List.mem_append, List.mem_flatMap]
    cases habw with
    | inl h =>
        rcases h with ⟨z', haz, hbw⟩
        left
        exact ⟨z', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
    | inr h =>
        rcases h with ⟨y', hay, hbw⟩
        right
        exact ⟨y', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩

theorem mem_firstFlatmap_left_to_right_sum
    (x y z w z' : PTree)
    (hz' : z' ∈ PTree.matchingLeafGraftings y z)
    (hw  : w ∈ PTree.matchingLeafGraftings x z') :
    w ∈
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  have hbal := (two_step_graft_witness_balance x y z w).1 z' hz' hw
  simp only [List.mem_append, List.mem_flatMap]
  cases hbal with
  | inl h =>
      rcases h with ⟨z₃, hz₃, hwz₃⟩
      exact Or.inl ⟨z₃, hz₃, hwz₃⟩
  | inr h =>
      rcases h with ⟨y', hxy, hwy'⟩
      exact Or.inr ⟨y', hxy, hwy'⟩

theorem mem_firstFlatmap_right_to_left_sum
    (x y z w z₃ : PTree)
    (hz₃ : z₃ ∈ PTree.matchingLeafGraftings x z)
    (hw  : w ∈ PTree.matchingLeafGraftings y z₃) :
    w ∈
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  have hbal := (two_step_graft_witness_balance x y z w).2 z₃ hz₃ hw
  simp only [List.mem_append, List.mem_flatMap]
  cases hbal with
  | inl h =>
      rcases h with ⟨z', hz', hwz'⟩
      exact Or.inl ⟨z', hz', hwz'⟩
  | inr h =>
      rcases h with ⟨y', hyx, hwy'⟩
      exact Or.inr ⟨y', hyx, hwy'⟩

def LeftWitnessFiber (x y z w : PTree) :=
  {p : ((Address × Address) × PTree) // p ∈ twoStepAddrWitnessesLeft x y z ∧ p.2 = w}

def RightWitnessFiber (x y z w : PTree) :=
  {p : ((Address × Address) × PTree) // p ∈ twoStepAddrWitnessesRight x y z ∧ p.2 = w}

inductive TwoStepWitnessLeft (x y z w : PTree) : Type where
| outer
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    TwoStepWitnessLeft x y z w
| inner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepWitnessLeft x y z w

inductive TwoStepWitnessRight (x y z w : PTree) : Type where
| outer
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    TwoStepWitnessRight x y z w
| inner
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses x y)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    TwoStepWitnessRight x y z w

theorem twoStepWitnessLeft_iff
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessLeft x y z w)
    ↔
    w ∈
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    cases h with
    | outer a b z' haz hbw =>
        simp [List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨z', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
    | inner a b y' hay hbw =>
        simp [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨y', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
  · intro hw
    simp only [List.mem_append, List.mem_flatMap] at hw
    cases hw with
    | inl h =>
        rcases h with ⟨z', hz', hwz'⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hz' hwz'
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hwz'
        rcases hz' with ⟨a, haz⟩
        rcases hwz' with ⟨b, hbw⟩
        exact ⟨TwoStepWitnessLeft.outer a b z' haz hbw⟩
    | inr h =>
        rcases h with ⟨y', hyx, hwy'⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hyx hwy'
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hyx hwy'
        rcases hyx with ⟨a, hay⟩
        rcases hwy' with ⟨b, hbw⟩
        exact ⟨TwoStepWitnessLeft.inner a b y' hay hbw⟩

theorem twoStepWitnessRight_iff
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessRight x y z w)
    ↔
    w ∈
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    cases h with
    | outer a b z' haz hbw =>
        simp [List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨z', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
    | inner a b y' hay hbw =>
        simp [List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨y', by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩, by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩⟩
  · intro hw
    simp only [List.mem_append, List.mem_flatMap] at hw
    cases hw with
    | inl h =>
        rcases h with ⟨z', hz', hwz'⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hz' hwz'
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hwz'
        rcases hz' with ⟨a, haz⟩
        rcases hwz' with ⟨b, hbw⟩
        exact ⟨TwoStepWitnessRight.outer a b z' haz hbw⟩
    | inr h =>
        rcases h with ⟨y', hxy, hwy'⟩
        rw [← map_snd_matchingLeafGraftWitnesses] at hxy hwy'
        simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hxy hwy'
        rcases hxy with ⟨a, hay⟩
        rcases hwy' with ⟨b, hbw⟩
        exact ⟨TwoStepWitnessRight.inner a b y' hay hbw⟩

theorem outer_left_gives_right_witness
    (x y z w : PTree) :
    (∃ a b z',
      (a, z') ∈ matchingLeafGraftWitnesses y z ∧
      (b, w) ∈ matchingLeafGraftWitnesses x z') →
    Nonempty (TwoStepWitnessRight x y z w) := by
  intro h
  rcases h with ⟨a, b, z', haz, hbw⟩
  obtain ⟨a', b', habw⟩ :=
    twoStepAddrWitnesses_main_left_to_right x y z a b w ⟨z', haz, hbw⟩
  rw [mem_twoStepAddrWitnessesRight_iff] at habw
  cases habw with
  | inl h =>
      rcases h with ⟨z'', haz'', hbw''⟩
      exact ⟨TwoStepWitnessRight.outer a' b' z'' haz'' hbw''⟩
  | inr h =>
      rcases h with ⟨y', hay', hbw''⟩
      exact ⟨TwoStepWitnessRight.inner a' b' y' hay' hbw''⟩

theorem outer_right_gives_left_witness
    (x y z w : PTree) :
    (∃ a b z',
      (a, z') ∈ matchingLeafGraftWitnesses x z ∧
      (b, w) ∈ matchingLeafGraftWitnesses y z') →
    Nonempty (TwoStepWitnessLeft x y z w) := by
  intro h
  rcases h with ⟨a, b, z', haz, hbw⟩
  obtain ⟨a', b', habw⟩ :=
    twoStepAddrWitnesses_main_right_to_left x y z a b w ⟨z', haz, hbw⟩
  rw [mem_twoStepAddrWitnessesLeft_iff] at habw
  cases habw with
  | inl h =>
      rcases h with ⟨z'', haz'', hbw''⟩
      exact ⟨TwoStepWitnessLeft.outer a' b' z'' haz'' hbw''⟩
  | inr h =>
      rcases h with ⟨y', hay', hbw''⟩
      exact ⟨TwoStepWitnessLeft.inner a' b' y' hay' hbw''⟩

/--
An inner left witness can be converted into an outer right witness by first
regrafting the intermediate tree into `z` and then using inner-exchange.
-/
theorem inner_left_gives_right_witness
    (x y z w : PTree) :
    (∃ a b y',
      (a, y') ∈ matchingLeafGraftWitnesses y x ∧
      (b, w) ∈ matchingLeafGraftWitnesses y' z) →
    Nonempty (TwoStepWitnessRight x y z w) := by
  intro h
  rcases h with ⟨a, b, y', hay, hbw⟩
  rw [mem_matchingLeafGraftWitnesses_iff] at hay hbw
  rcases hay with ⟨haAddr, hyx⟩
  rcases hbw with ⟨hbAddr, hy'z⟩
  have hconc : y'.conclusion = x.conclusion := by
    exact graftMatchingLeafAt_preserves_conclusion y x y' a hyx
  have hgx : PTree.IsGraftableLeafAt x z b := by
    rw [PTree.IsGraftableLeafAt_iff]
    have hs : PTree.subtreeAt z b = some (PTree.leaf y'.conclusion) := by
      exact (PTree.IsGraftableLeafAt_iff y' z b).mp
        (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z b w hy'z)
    simpa [hconc] using hs
  obtain ⟨z', hxz⟩ := PTree.graftMatchingLeafAt_spec x z b hgx
  have hyz' : PTree.graftMatchingLeafAt y z' (b ++ a) = some w := by
    rw [graftMatchingLeafAt_inner_exchange y x z b a z' y' hxz hyx]
    exact hy'z
  have haz : (b, z') ∈ matchingLeafGraftWitnesses x z := by
    rw [mem_matchingLeafGraftWitnesses_iff]
    exact ⟨hbAddr, hxz⟩
  have hbw' : (b ++ a, w) ∈ matchingLeafGraftWitnesses y z' := by
    rw [mem_matchingLeafGraftWitnesses_iff]
    refine ⟨?_, hyz'⟩
    have hg :=
      PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y z' (b ++ a) w hyz'
    exact
      PTree.subtreeAt_some_implies_mem_allAddresses
        z' (PTree.leaf y.conclusion) (b ++ a)
        ((PTree.IsGraftableLeafAt_iff y z' (b ++ a)).mp hg)
  exact ⟨TwoStepWitnessRight.outer b (b ++ a) z' haz hbw'⟩

/--
An inner right witness can be converted into an outer left witness by the same
inner-exchange argument with `x` and `y` swapped.
-/
theorem inner_right_gives_left_witness
    (x y z w : PTree) :
    (∃ a b y',
      (a, y') ∈ matchingLeafGraftWitnesses x y ∧
      (b, w) ∈ matchingLeafGraftWitnesses y' z) →
    Nonempty (TwoStepWitnessLeft x y z w) := by
  intro h
  rcases h with ⟨a, b, y', hay, hbw⟩
  rw [mem_matchingLeafGraftWitnesses_iff] at hay hbw
  rcases hay with ⟨haAddr, hxy⟩
  rcases hbw with ⟨hbAddr, hy'z⟩
  have hconc : y'.conclusion = y.conclusion := by
    exact graftMatchingLeafAt_preserves_conclusion x y y' a hxy
  have hgy : PTree.IsGraftableLeafAt y z b := by
    rw [PTree.IsGraftableLeafAt_iff]
    have hs : PTree.subtreeAt z b = some (PTree.leaf y'.conclusion) := by
      exact (PTree.IsGraftableLeafAt_iff y' z b).mp
        (PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some y' z b w hy'z)
    simpa [hconc] using hs
  obtain ⟨z', hyz⟩ := PTree.graftMatchingLeafAt_spec y z b hgy
  have hxz' : PTree.graftMatchingLeafAt x z' (b ++ a) = some w := by
    rw [graftMatchingLeafAt_inner_exchange x y z b a z' y' hyz hxy]
    exact hy'z
  have haz : (b, z') ∈ matchingLeafGraftWitnesses y z := by
    rw [mem_matchingLeafGraftWitnesses_iff]
    exact ⟨hbAddr, hyz⟩
  have hbw' : (b ++ a, w) ∈ matchingLeafGraftWitnesses x z' := by
    rw [mem_matchingLeafGraftWitnesses_iff]
    refine ⟨?_, hxz'⟩
    have hg :=
      PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some x z' (b ++ a) w hxz'
    exact
      PTree.subtreeAt_some_implies_mem_allAddresses
        z' (PTree.leaf x.conclusion) (b ++ a)
        ((PTree.IsGraftableLeafAt_iff x z' (b ++ a)).mp hg)
  exact ⟨TwoStepWitnessLeft.outer b (b ++ a) z' haz hbw'⟩

/--
Deterministic transport of a left two-step witness to a right-hand witness.
This packages the existing outer/inner exchange lemmas as an actual function.
-/
noncomputable def twoStepWitnessLeftToRight
    (x y z w : PTree) :
    TwoStepWitnessLeft x y z w → TwoStepWitnessRight x y z w
  | .outer a b z' haz hbw =>
      Classical.choice <|
        outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
  | .inner a b y' hay hbw =>
      Classical.choice <|
        inner_left_gives_right_witness x y z w ⟨a, b, y', hay, hbw⟩

/--
Deterministic transport of a right two-step witness to a left-hand witness.
This is the symmetric companion to `twoStepWitnessLeftToRight`.
-/
noncomputable def twoStepWitnessRightToLeft
    (x y z w : PTree) :
    TwoStepWitnessRight x y z w → TwoStepWitnessLeft x y z w
  | .outer a b z' haz hbw =>
      Classical.choice <|
        outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
  | .inner a b y' hay hbw =>
      Classical.choice <|
        inner_right_gives_left_witness x y z w ⟨a, b, y', hay, hbw⟩

/--
The two witness presentations for a two-step graft landing at `w` have the same
nonemptiness behaviour.
-/
theorem twoStepWitness_balance
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessLeft x y z w) ↔
    Nonempty (TwoStepWitnessRight x y z w) := by
  constructor
  · intro h
    rcases h with ⟨hw⟩
    cases hw with
    | outer a b z' haz hbw =>
        exact outer_left_gives_right_witness x y z w ⟨a, b, z', haz, hbw⟩
    | inner a b y' hay hbw =>
        exact inner_left_gives_right_witness x y z w ⟨a, b, y', hay, hbw⟩
  · intro h
    rcases h with ⟨hw⟩
    cases hw with
    | outer a b z' haz hbw =>
        exact outer_right_gives_left_witness x y z w ⟨a, b, z', haz, hbw⟩
    | inner a b y' hay hbw =>
        exact inner_right_gives_left_witness x y z w ⟨a, b, y', hay, hbw⟩

/--
Support-level balance between the two concrete two-step flatmap presentations.
-/
theorem twoStepFlatmaps_balance
    (x y z w : PTree) :
    w ∈
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)))
    ↔
    w ∈
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  rw [← twoStepWitnessLeft_iff, ← twoStepWitnessRight_iff]
  exact twoStepWitness_balance x y z w

inductive OuterLeftWitness (x y z w : PTree) : Type where
| mk
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses y z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses x z') :
    OuterLeftWitness x y z w

inductive OuterRightWitness (x y z w : PTree) : Type where
| mk
    (a b : Address) (z' : PTree)
    (haz : (a, z') ∈ matchingLeafGraftWitnesses x z)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y z') :
    OuterRightWitness x y z w

theorem outer_support_left_to_right
    (x y z w : PTree) :
    w ∈ ((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')) →
    w ∈
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  intro h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨z', hz', hw⟩
  exact mem_firstFlatmap_left_to_right_sum x y z w z' hz' hw

end Syntax
