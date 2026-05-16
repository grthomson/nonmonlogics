import Nonmonlogics.Hypersequent

/-!
# Derivable proof-labelled hypersequents

This file is a proof-theoretic bridge between the raw hypersequent carrier in
`Hypersequent.lean` and the actual NMMS derivation trees defined in
`GrossmanLarsson.lean`.

The ambient Hopf carrier uses `Hypersequent = Multiset PTree`.  That is useful
algebraically, but a bare `PTree` is only labelled tree syntax.  The intended
proof-theoretic sector consists of those components that arise from genuine
`NMMS` derivations over a material base relation.

The first goal of this file is therefore small and foundational:

* define derivable hypersequents;
* prove closure under empty hypersequent, singleton, external union, forests,
  and explicit base extension;
* bring internal matching-leaf grafting back into the derivable sector.

The final grafting theorem below is intentionally local.  It does not say that
external product is grafting.  It says that contextual internal grafting
preserves the proof-theoretic sector when the inserted proof tree and host
component are genuine NMMS proof trees.
-/

open Syntax

namespace QuotientConnected
namespace HypersequentRoute

/-! ## Structurally labelled proof traces -/

/--
Tags for structural or interface-level rule applications.

These are deliberately separate from `RuleTag`, whose constructors label the
logical NMMS rules appearing inside ordinary `PTree` nodes.
-/
inductive StructuralRuleTag where
| hyperRoot
| interfaceFill
| externalWeakening
| externalContraction
| externalPermutation
| externalSplit
| internalGraft
deriving DecidableEq, Repr

/--
A proof-step label can be either a logical rule label from the underlying NMMS
calculus or a structural/interface label from the surrounding hypersequent and
grafting discipline.
-/
inductive ProofStepLabel where
| logical : RuleTag -> ProofStepLabel
| structural : StructuralRuleTag -> ProofStepLabel
deriving DecidableEq, Repr

/--
Proof traces with both logical and structural labels.

This is an enriched bookkeeping tree, not a replacement for `PTree`.  Pure
NMMS derivations embed by turning each `RuleTag` into a logical
`ProofStepLabel`; structural/interface steps can be recorded without pretending
that the old `PTree` carrier had a corresponding logical node.
-/
inductive ProofTraceTree where
| leaf : MultiSequent -> ProofTraceTree
| node : ProofStepLabel -> MultiSequent -> List ProofTraceTree -> ProofTraceTree

namespace ProofTraceTree

/-- The sequent decorating the root of a structurally labelled proof trace. -/
def conclusion : ProofTraceTree -> MultiSequent
| leaf s => s
| node _ s _ => s

/-- Embed an ordinary proof tree as a trace containing only logical labels. -/
def ofPTree : PTree -> ProofTraceTree
| PTree.leaf s => leaf s
| PTree.node r s cs => node (ProofStepLabel.logical r) s (cs.map ofPTree)

/--
Package an ordered forest as one planted trace tree.

The new root is structural: it records the hypersequent/forest packaging
operation, not a logical NMMS inference and not a material-base axiom.
-/
def Bplus (root : MultiSequent) (f : Forest) : ProofTraceTree :=
  node (ProofStepLabel.structural StructuralRuleTag.hyperRoot)
    root (f.map ofPTree)

@[simp]
theorem conclusion_ofPTree (t : PTree) :
    conclusion (ofPTree t) = t.conclusion := by
  cases t <;> simp [ofPTree, conclusion, PTree.conclusion]

@[simp]
theorem conclusion_Bplus (root : MultiSequent) (f : Forest) :
    conclusion (Bplus root f) = root := by
  rfl

@[simp]
theorem Bplus_nil (root : MultiSequent) :
    Bplus root ([] : Forest) =
      node (ProofStepLabel.structural StructuralRuleTag.hyperRoot)
        root [] := by
  rfl

@[simp]
theorem Bplus_cons (root : MultiSequent) (t : PTree) (f : Forest) :
    Bplus root (t :: f) =
      node (ProofStepLabel.structural StructuralRuleTag.hyperRoot)
        root (ofPTree t :: f.map ofPTree) := by
  rfl

end ProofTraceTree

/-! ## Planted hyperforests

`PlantedHyperforest` is the conservative single-carrier candidate suggested by
the classical `B+` operation on rooted-tree Hopf algebras.  It keeps the
existing forest/hypersequent carrier intact, but also gives it one structural
root so the object can be read as a single labelled trace tree.
-/

/-- A forest packaged with a structural root label. -/
structure PlantedHyperforest where
  rootLabel : MultiSequent
  forest : Forest

namespace PlantedHyperforest

/-- The `B+` constructor from a root/interface label and a forest. -/
def Bplus (root : MultiSequent) (f : Forest) : PlantedHyperforest where
  rootLabel := root
  forest := f

/-- Remove the structural root and recover the underlying ordered forest. -/
def Bminus (P : PlantedHyperforest) : Forest :=
  P.forest

/-- Forget ordering and view the planted forest as a proof-labelled hypersequent. -/
def toHypersequent (P : PlantedHyperforest) : Hypersequent :=
  HQ.ofForest P.forest

/-- View the planted forest as one structurally rooted proof trace. -/
def toTraceTree (P : PlantedHyperforest) : ProofTraceTree :=
  ProofTraceTree.Bplus P.rootLabel P.forest

@[simp]
theorem rootLabel_Bplus (root : MultiSequent) (f : Forest) :
    (Bplus root f).rootLabel = root := by
  rfl

@[simp]
theorem Bminus_Bplus (root : MultiSequent) (f : Forest) :
    Bminus (Bplus root f) = f := by
  rfl

@[simp]
theorem forest_Bplus (root : MultiSequent) (f : Forest) :
    (Bplus root f).forest = f := by
  rfl

@[simp]
theorem toHypersequent_Bplus (root : MultiSequent) (f : Forest) :
    toHypersequent (Bplus root f) = HQ.ofForest f := by
  rfl

@[simp]
theorem toTraceTree_Bplus (root : MultiSequent) (f : Forest) :
    toTraceTree (Bplus root f) = ProofTraceTree.Bplus root f := by
  rfl

@[simp]
theorem toHypersequent_nil (root : MultiSequent) :
    toHypersequent (Bplus root ([] : Forest)) = (0 : Hypersequent) := by
  rfl

@[simp]
theorem toHypersequent_cons
    (root : MultiSequent) (t : PTree) (f : Forest) :
    toHypersequent (Bplus root (t :: f)) =
      HQ.singleton t + HQ.ofForest f := by
  simp [toHypersequent, Bplus]

@[simp]
theorem toTraceTree_conclusion (P : PlantedHyperforest) :
    P.toTraceTree.conclusion = P.rootLabel := by
  cases P
  rfl

end PlantedHyperforest

/-! ## Derivable hypersequents -/

/--
A proof-labelled hypersequent is derivable over `base` when every proof-tree
component is the forgetful tree of some actual `NMMS base` derivation.
-/
def DerivableHypersequent (base : BaseRel) (G : Hypersequent) : Prop :=
  ∀ t : PTree, t ∈ G → DerivableTree base t

/-- Subtype of genuine closed proof trees over a fixed material base. -/
abbrev DerivableProofTree (base : BaseRel) :=
  { t : PTree // DerivableTree base t }

/-- Subtype of proof-labelled hypersequents whose components are derivable. -/
abbrev DerivableProofHypersequent (base : BaseRel) :=
  { G : Hypersequent // DerivableHypersequent base G }

@[simp]
theorem derivableHypersequent_zero (base : BaseRel) :
    DerivableHypersequent base (0 : Hypersequent) := by
  intro t ht
  simp at ht

theorem derivableHypersequent_singleton
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    DerivableHypersequent base (HQ.singleton t) := by
  intro u hu
  simp [HQ.singleton] at hu
  subst u
  exact ht

@[simp]
theorem derivableHypersequent_singleton_iff
    {base : BaseRel} {t : PTree} :
    DerivableHypersequent base (HQ.singleton t) ↔ DerivableTree base t := by
  constructor
  · intro h
    exact h t (by simp [HQ.singleton])
  · exact derivableHypersequent_singleton

theorem derivableHypersequent_add
    {base : BaseRel} {G H : Hypersequent}
    (hG : DerivableHypersequent base G)
    (hH : DerivableHypersequent base H) :
    DerivableHypersequent base (G + H) := by
  intro t ht
  rw [Multiset.mem_add] at ht
  rcases ht with ht | ht
  · exact hG t ht
  · exact hH t ht

theorem derivableHypersequent_left_of_add
    {base : BaseRel} {G H : Hypersequent}
    (hGH : DerivableHypersequent base (G + H)) :
    DerivableHypersequent base G := by
  intro t ht
  exact hGH t (by
    rw [Multiset.mem_add]
    exact Or.inl ht)

theorem derivableHypersequent_right_of_add
    {base : BaseRel} {G H : Hypersequent}
    (hGH : DerivableHypersequent base (G + H)) :
    DerivableHypersequent base H := by
  intro t ht
  exact hGH t (by
    rw [Multiset.mem_add]
    exact Or.inr ht)

theorem derivableHypersequent_ofForest
    {base : BaseRel} {f : Forest}
    (hf : DerivableForest base f) :
    DerivableHypersequent base (HQ.ofForest f) := by
  intro t ht
  simp [HQ.ofForest] at ht
  exact hf t ht

/--
A planted hyperforest is derivable when every component below its structural
root is an actual NMMS proof tree over the current material base.
-/
def DerivablePlantedHyperforest
    (base : BaseRel) (P : PlantedHyperforest) : Prop :=
  DerivableForest base P.forest

theorem derivablePlantedHyperforest_Bplus
    {base : BaseRel} {root : MultiSequent} {f : Forest}
    (hf : DerivableForest base f) :
    DerivablePlantedHyperforest base
      (PlantedHyperforest.Bplus root f) := by
  exact hf

theorem derivablePlantedHyperforest_toHypersequent
    {base : BaseRel} {P : PlantedHyperforest}
    (hP : DerivablePlantedHyperforest base P) :
    DerivableHypersequent base P.toHypersequent := by
  cases P with
  | mk root f =>
      exact derivableHypersequent_ofForest hP

theorem derivablePlantedHyperforest_iff_toHypersequent
    {base : BaseRel} {P : PlantedHyperforest} :
    DerivablePlantedHyperforest base P ↔
      DerivableHypersequent base P.toHypersequent := by
  constructor
  · exact derivablePlantedHyperforest_toHypersequent
  · intro hP t ht
    exact hP t (by
      cases P
      simpa [PlantedHyperforest.toHypersequent, HQ.ofForest] using ht)

theorem derivableHypersequent_mono
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {G : Hypersequent}
    (hG : DerivableHypersequent base G) :
    DerivableHypersequent base' G := by
  intro t ht
  exact derivableTree_mono hbase (hG t ht)

theorem derivableHypersequent_not_of_mem_nonderivable
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (htG : t ∈ G) (ht : ¬ DerivableTree base t) :
    ¬ DerivableHypersequent base G := by
  intro hG
  exact ht (hG t htG)

/-! ## Constructors for the derivable sector -/

def DerivableProofHypersequent.empty (base : BaseRel) :
    DerivableProofHypersequent base :=
  ⟨0, derivableHypersequent_zero base⟩

def DerivableProofHypersequent.singleton
    {base : BaseRel} (t : DerivableProofTree base) :
    DerivableProofHypersequent base :=
  ⟨HQ.singleton t.1, derivableHypersequent_singleton t.2⟩

def DerivableProofHypersequent.add
    {base : BaseRel}
    (G H : DerivableProofHypersequent base) :
    DerivableProofHypersequent base :=
  ⟨G.1 + H.1, derivableHypersequent_add G.2 H.2⟩

def DerivableProofHypersequent.ofForest
    {base : BaseRel} {f : Forest}
    (hf : DerivableForest base f) :
    DerivableProofHypersequent base :=
  ⟨HQ.ofForest f, derivableHypersequent_ofForest hf⟩

def DerivableProofHypersequent.mapBase
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    (G : DerivableProofHypersequent base) :
    DerivableProofHypersequent base' :=
  ⟨G.1, derivableHypersequent_mono hbase G.2⟩

/-- Subtype of planted hyperforests whose components are derivable. -/
abbrev DerivableProofPlantedHyperforest (base : BaseRel) :=
  { P : PlantedHyperforest // DerivablePlantedHyperforest base P }

def DerivableProofPlantedHyperforest.Bplus
    {base : BaseRel} {root : MultiSequent} {f : Forest}
    (hf : DerivableForest base f) :
    DerivableProofPlantedHyperforest base :=
  ⟨PlantedHyperforest.Bplus root f,
    derivablePlantedHyperforest_Bplus hf⟩

def DerivableProofPlantedHyperforest.toProofHypersequent
    {base : BaseRel}
    (P : DerivableProofPlantedHyperforest base) :
    DerivableProofHypersequent base :=
  ⟨P.1.toHypersequent,
    derivablePlantedHyperforest_toHypersequent P.2⟩

def DerivableProofPlantedHyperforest.mapBase
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    (P : DerivableProofPlantedHyperforest base) :
    DerivableProofPlantedHyperforest base' :=
  ⟨P.1, fun t ht => derivableTree_mono hbase (P.2 t ht)⟩

def DerivableProofTree.mapBase
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    (t : DerivableProofTree base) :
    DerivableProofTree base' :=
  ⟨t.1, derivableTree_mono hbase t.2⟩

/-! ## Grafting inside the derivable sector -/

/--
Internal matching-leaf grafting preserves closed derivability.

This is the proof-theoretic re-entry point for grafting.  If `u` and `t` are
actual NMMS proof trees over the same base, and `v` is obtained by grafting
`u` into a matching leaf of `t`, then `v` is again an actual NMMS proof tree.
-/
theorem internalGraft_preserves_derivable
    {base : BaseRel} {u t v : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t)
    (hg : InternalGraft u t v) :
    DerivableTree base v := by
  rcases hu with ⟨s_inner, d_inner, rfl⟩
  rcases ht with ⟨s_outer, d_outer, rfl⟩
  rcases hg with ⟨a, ha⟩
  have hgraftable :
      PTree.IsGraftableLeafAt
        (NMMS.toTree d_inner)
        (NMMS.toTree d_outer)
        a :=
    PTree.isGraftableLeafAt_of_graftMatchingLeafAt_eq_some
      (NMMS.toTree d_inner) (NMMS.toTree d_outer) a v ha
  rcases graftMatchingLeafAt_toTree_is_toTree
      d_outer d_inner a hgraftable with ⟨d', hd'⟩
  have hv : NMMS.toTree d' = v := by
    rw [hd'] at ha
    simpa using Option.some.inj ha
  exact ⟨s_outer, d', hv⟩

/--
Contextual internal grafting preserves derivable hypersequents.

If `G` is a hypersequent of genuine proof trees, `u` is a genuine inserted
proof tree, and `H` is obtained from `G` by one contextual internal graft of
`u`, then `H` is again a hypersequent of genuine proof trees.
-/
theorem contextualInternalGraft_preserves_derivableHypersequent
    {base : BaseRel} {u : PTree} {G H : Hypersequent}
    (hu : DerivableTree base u)
    (hG : DerivableHypersequent base G)
    (hg : ContextualInternalGraft u G H) :
    DerivableHypersequent base H := by
  rcases hg with ⟨C, t, v, rfl, rfl, htv⟩
  apply derivableHypersequent_add
  · exact derivableHypersequent_left_of_add hG
  · apply derivableHypersequent_singleton
    have ht : DerivableTree base t := hG t (by
      rw [Multiset.mem_add]
      exact Or.inr (by simp [HQ.singleton]))
    exact internalGraft_preserves_derivable hu ht htv

/--
Subtype form of contextual grafting preservation.
-/
def DerivableProofHypersequent.contextualInternalGraft
    {base : BaseRel} {u : PTree}
    (hu : DerivableTree base u)
    (G : DerivableProofHypersequent base)
    {H : Hypersequent}
    (hg : ContextualInternalGraft u G.1 H) :
    DerivableProofHypersequent base :=
  ⟨H, contextualInternalGraft_preserves_derivableHypersequent hu G.2 hg⟩

/-! ## Planted contextual grafting -/

/--
Internal grafting transported to the planted `B+` carrier.

The structural root is held fixed.  After forgetting that root with
`toHypersequent`, this is exactly the existing contextual hypersequent graft.
-/
def PlantedContextualInternalGraft
    (u : PTree) (P Q : PlantedHyperforest) : Prop :=
  P.rootLabel = Q.rootLabel ∧
    ContextualInternalGraft u P.toHypersequent Q.toHypersequent

theorem plantedContextualInternalGraft_to_contextual
    {u : PTree} {P Q : PlantedHyperforest}
    (h : PlantedContextualInternalGraft u P Q) :
    ContextualInternalGraft u P.toHypersequent Q.toHypersequent :=
  h.2

theorem plantedContextualInternalGraft_rootLabel
    {u : PTree} {P Q : PlantedHyperforest}
    (h : PlantedContextualInternalGraft u P Q) :
    P.rootLabel = Q.rootLabel :=
  h.1

theorem plantedContextualInternalGraft_preserves_conclusions
    {u : PTree} {P Q : PlantedHyperforest}
    (h : PlantedContextualInternalGraft u P Q) :
    HQ.conclusions Q.toHypersequent =
      HQ.conclusions P.toHypersequent :=
  contextualInternalGraft_preserves_conclusions h.2

theorem plantedContextualInternalGraft_preserves_trace_root
    {u : PTree} {P Q : PlantedHyperforest}
    (h : PlantedContextualInternalGraft u P Q) :
    Q.toTraceTree.conclusion = P.toTraceTree.conclusion := by
  rw [PlantedHyperforest.toTraceTree_conclusion,
    PlantedHyperforest.toTraceTree_conclusion]
  exact h.1.symm

theorem plantedContextualInternalGraft_preserves_derivable
    {base : BaseRel} {u : PTree} {P Q : PlantedHyperforest}
    (hu : DerivableTree base u)
    (hP : DerivablePlantedHyperforest base P)
    (hg : PlantedContextualInternalGraft u P Q) :
    DerivablePlantedHyperforest base Q := by
  rw [derivablePlantedHyperforest_iff_toHypersequent]
  exact contextualInternalGraft_preserves_derivableHypersequent
    hu
    (derivablePlantedHyperforest_toHypersequent hP)
    hg.2

def DerivableProofPlantedHyperforest.contextualInternalGraft
    {base : BaseRel} {u : PTree}
    (hu : DerivableTree base u)
    (P : DerivableProofPlantedHyperforest base)
    {Q : PlantedHyperforest}
    (hg : PlantedContextualInternalGraft u P.1 Q) :
    DerivableProofPlantedHyperforest base :=
  ⟨Q, plantedContextualInternalGraft_preserves_derivable hu P.2 hg⟩

/-! ## Proof-theoretic grafting support -/

/--
Ambient one-step grafting support: `v` is one of the matching-leaf graftings of
`u` into `t`.

This is the pointwise support of the primitive pre-Lie product already
developed in the quotient/OG files.
-/
def AmbientGraftingSupport (u t v : PTree) : Prop :=
  v ∈ PTree.matchingLeafGraftings u t

@[simp]
theorem ambientGraftingSupport_iff_classLevelProduct
    (u t v : PTree) :
    AmbientGraftingSupport u t v ↔ InClassLevelProduct u t v := by
  rfl

theorem ambientGraftingSupport_iff_pointwisePreLieSupport
    (u t v : PTree) :
    AmbientGraftingSupport u t v ↔
      proofTreePointwisePreLieSupport.productSupport u t v := by
  simp [AmbientGraftingSupport, proofTreePointwisePreLieSupport,
    classLevelProductSupport, InClassLevelProduct]
  constructor <;> intro h <;> exact h

/--
Membership in the list of matching-leaf graftings is the same kind of witness
as `InternalGraft`: there is an address at which the graft succeeds.
-/
theorem internalGraft_of_mem_matchingLeafGraftings
    {u t v : PTree}
    (hv : v ∈ PTree.matchingLeafGraftings u t) :
    InternalGraft u t v := by
  unfold PTree.matchingLeafGraftings at hv
  rcases List.mem_filterMap.1 hv with ⟨a, _ha, hg⟩
  exact ⟨a, hg⟩

/--
Proof-theoretic one-step grafting support.

This is the grafting-side analogue of `ProofTheoreticSplittingSupport`: the
ambient product support is retained only together with closed proof provenance
for the inserted proof, host proof, and output proof.
-/
def ProofTheoreticGraftingSupport
    (base : BaseRel) (u t v : PTree) : Prop :=
  DerivableTree base u ∧
    DerivableTree base t ∧
      AmbientGraftingSupport u t v ∧
        DerivableTree base v

/--
The same proof-theoretic grafting support, but expressed entirely inside the
hypersequent carrier by using one-component hypersequents.

This is the algebra-side singleton case of the hypersequent picture: a proof
composition step can be read as a hypersequent-level operation whose active
source, host, and output are all singleton hypersequents.  General
hypersequents then remain available for external context and for detached
forests on the coproduct side.
-/
def ProofTheoreticSingletonHypersequentGraftingSupport
    (base : BaseRel) (U T V : Hypersequent) : Prop :=
  ∃ u t v : PTree,
    U = HQ.singleton u ∧
      T = HQ.singleton t ∧
        V = HQ.singleton v ∧
          ProofTheoreticGraftingSupport base u t v

/-- A one-component planted hyperforest. -/
def PlantedHyperforest.singleton
    (root : MultiSequent) (t : PTree) : PlantedHyperforest :=
  PlantedHyperforest.Bplus root [t]

@[simp]
theorem PlantedHyperforest.toHypersequent_singleton
    (root : MultiSequent) (t : PTree) :
    (PlantedHyperforest.singleton root t).toHypersequent =
      HQ.singleton t := by
  simp [PlantedHyperforest.singleton,
    PlantedHyperforest.toHypersequent]

@[simp]
theorem PlantedHyperforest.Bminus_singleton
    (root : MultiSequent) (t : PTree) :
    (PlantedHyperforest.singleton root t).Bminus = [t] := by
  rfl

/--
The singleton product-side support on the planted carrier.

The inserted proof, host proof, and output proof are all singleton planted
hyperforests.  The host and output share the same structural root; the inserted
proof may carry its own structural/interface root.
-/
def ProofTheoreticSingletonPlantedGraftingSupport
    (base : BaseRel)
    (U T V : PlantedHyperforest) : Prop :=
  ∃ (rootU rootT : MultiSequent) (u t v : PTree),
    U = PlantedHyperforest.singleton rootU u ∧
      T = PlantedHyperforest.singleton rootT t ∧
        V = PlantedHyperforest.singleton rootT v ∧
          ProofTheoreticGraftingSupport base u t v

theorem proofTheoreticSingletonPlantedGraftingSupport_to_hypersequent
    {base : BaseRel} {U T V : PlantedHyperforest}
    (h : ProofTheoreticSingletonPlantedGraftingSupport base U T V) :
    ProofTheoreticSingletonHypersequentGraftingSupport base
      U.toHypersequent T.toHypersequent V.toHypersequent := by
  rcases h with ⟨rootU, rootT, u, t, v, rfl, rfl, rfl, hpt⟩
  simpa using
    proofTheoreticSingletonHypersequentGraftingSupport_of_tree_support hpt

theorem proofTheoreticSingletonPlantedGraftingSupport_derivable
    {base : BaseRel} {U T V : PlantedHyperforest}
    (h : ProofTheoreticSingletonPlantedGraftingSupport base U T V) :
    DerivablePlantedHyperforest base U ∧
      DerivablePlantedHyperforest base T ∧
        DerivablePlantedHyperforest base V := by
  rcases h with ⟨rootU, rootT, u, t, v, rfl, rfl, rfl, hpt⟩
  exact
    ⟨derivablePlantedHyperforest_Bplus
        (by intro w hw; simp at hw; subst w; exact hpt.1),
      derivablePlantedHyperforest_Bplus
        (by intro w hw; simp at hw; subst w; exact hpt.2.1),
      derivablePlantedHyperforest_Bplus
        (by intro w hw; simp at hw; subst w; exact hpt.2.2.2)⟩

theorem proofTheoreticSingletonPlantedGraftingSupport_contextual
    {base : BaseRel} {U T V : PlantedHyperforest}
    (h : ProofTheoreticSingletonPlantedGraftingSupport base U T V) :
    ∃ u t v : PTree,
      U.toHypersequent = HQ.singleton u ∧
        T.toHypersequent = HQ.singleton t ∧
          V.toHypersequent = HQ.singleton v ∧
            PlantedContextualInternalGraft u T V := by
  rcases h with ⟨rootU, rootT, u, t, v, rfl, rfl, rfl, hpt⟩
  have hg : InternalGraft u t v :=
    internalGraft_of_mem_matchingLeafGraftings hpt.2.2.1
  exact
    ⟨u, t, v, by simp, by simp, by simp,
      rfl, contextualInternalGraft_singleton hg⟩

theorem proofTheoreticSingletonPlantedGraftingSupport_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {U T V : PlantedHyperforest}
    (h : ProofTheoreticSingletonPlantedGraftingSupport base U T V) :
    ProofTheoreticSingletonPlantedGraftingSupport base' U T V := by
  rcases h with ⟨rootU, rootT, u, t, v, hU, hT, hV, hpt⟩
  exact
    ⟨rootU, rootT, u, t, v, hU, hT, hV,
      ⟨derivableTree_mono hbase hpt.1,
        derivableTree_mono hbase hpt.2.1,
        hpt.2.2.1,
        derivableTree_mono hbase hpt.2.2.2⟩⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_of_tree_support
    {base : BaseRel} {u t v : PTree}
    (h : ProofTheoreticGraftingSupport base u t v) :
    ProofTheoreticSingletonHypersequentGraftingSupport base
      (HQ.singleton u) (HQ.singleton t) (HQ.singleton v) := by
  exact ⟨u, t, v, rfl, rfl, rfl, h⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_derivable
    {base : BaseRel} {U T V : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    DerivableHypersequent base U ∧
      DerivableHypersequent base T ∧
        DerivableHypersequent base V := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  exact
    ⟨derivableHypersequent_singleton hpt.1,
      derivableHypersequent_singleton hpt.2.1,
      derivableHypersequent_singleton hpt.2.2.2⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_contextual
    {base : BaseRel} {U T V : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    ∃ u t v : PTree,
      U = HQ.singleton u ∧
        T = HQ.singleton t ∧
          V = HQ.singleton v ∧
            ContextualInternalGraft u T V := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  have hg : InternalGraft u t v :=
    internalGraft_of_mem_matchingLeafGraftings hpt.2.2.1
  exact ⟨u, t, v, rfl, rfl, rfl, contextualInternalGraft_singleton hg⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_preserves_shadow
    {base : BaseRel} {U T V : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    HQ.conclusions V = HQ.conclusions T := by
  rcases proofTheoreticSingletonHypersequentGraftingSupport_contextual h with
    ⟨u, t, v, _hU, hT, hV, hctx⟩
  subst T
  subst V
  exact contextualInternalGraft_preserves_conclusions hctx

theorem proofTheoreticGraftingSupport_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {u t v : PTree}
    (h : ProofTheoreticGraftingSupport base u t v) :
    ProofTheoreticGraftingSupport base' u t v := by
  exact
    ⟨derivableTree_mono hbase h.1,
      derivableTree_mono hbase h.2.1,
      h.2.2.1,
      derivableTree_mono hbase h.2.2.2⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {U T V : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    ProofTheoreticSingletonHypersequentGraftingSupport base' U T V := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  exact
    proofTheoreticSingletonHypersequentGraftingSupport_of_tree_support
      (proofTheoreticGraftingSupport_mono_base hbase hpt)

theorem proofTheoreticSingletonHypersequentGraftingSupport_add_context
    {base : BaseRel} {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V)
    (hC : DerivableHypersequent base C) :
    ∃ u : PTree,
      DerivableHypersequent base U ∧
        DerivableHypersequent base (C + T) ∧
          ContextualInternalGraft u (C + T) (C + V) ∧
            DerivableHypersequent base (C + V) ∧
              HQ.conclusions (C + V) = HQ.conclusions (C + T) := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  have hg : InternalGraft u t v :=
    internalGraft_of_mem_matchingLeafGraftings hpt.2.2.1
  have hctx : ContextualInternalGraft u
      (C + HQ.singleton t) (C + HQ.singleton v) :=
    contextualInternalGraft_of_added_component C hg
  exact
    ⟨u,
      derivableHypersequent_singleton hpt.1,
      derivableHypersequent_add hC
        (derivableHypersequent_singleton hpt.2.1),
      hctx,
      derivableHypersequent_add hC
        (derivableHypersequent_singleton hpt.2.2.2),
      contextualInternalGraft_preserves_conclusions hctx⟩

theorem proofTheoreticSingletonHypersequentGraftingSupport_add_context_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V)
    (hC : DerivableHypersequent base C) :
    ∃ u : PTree,
      DerivableHypersequent base' U ∧
        DerivableHypersequent base' (C + T) ∧
          ContextualInternalGraft u (C + T) (C + V) ∧
            DerivableHypersequent base' (C + V) ∧
              HQ.conclusions (C + V) = HQ.conclusions (C + T) := by
  exact
    proofTheoreticSingletonHypersequentGraftingSupport_add_context
      (proofTheoreticSingletonHypersequentGraftingSupport_mono_base
        hbase h)
      (derivableHypersequent_mono hbase hC)

/--
The proof-theoretic grafting support is closed under matching-leaf grafting:
if the inserted and host trees are closed derivations, every matching-leaf
grafting output is again a closed derivation.
-/
theorem proofTheoreticGraftingSupport_of_derivable_mem
    {base : BaseRel} {u t v : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t)
    (hv : AmbientGraftingSupport u t v) :
    ProofTheoreticGraftingSupport base u t v := by
  have hg : InternalGraft u t v :=
    internalGraft_of_mem_matchingLeafGraftings hv
  exact ⟨hu, ht, hv, internalGraft_preserves_derivable hu ht hg⟩

theorem derivable_of_proofTheoreticGraftingSupport
    {base : BaseRel} {u t v : PTree}
    (h : ProofTheoreticGraftingSupport base u t v) :
    DerivableTree base v :=
  h.2.2.2

/--
The existing pointwise pre-Lie support preserves closed derivability on
closed inputs.

This is the immediate proof-theoretic bridge to the OG/GL side: the primitive
pre-Lie support is not merely ambient tree grafting once its inputs are
genuine NMMS proof trees.
-/
theorem pointwisePreLieSupport_preserves_derivable_outputs
    {base : BaseRel} {u t v : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t)
    (hv : proofTreePointwisePreLieSupport.productSupport u t v) :
    DerivableTree base v := by
  apply derivable_of_proofTheoreticGraftingSupport
  apply proofTheoreticGraftingSupport_of_derivable_mem hu ht
  exact (ambientGraftingSupport_iff_pointwisePreLieSupport u t v).2 hv

/--
The quotient/OG pointwise pre-Lie identity is available on the same primitive
support that preserves derivability above.

This is not yet the Oudom-Guin Hopf algebra.  It is the proof-theoretic
pre-Lie input from which that Hopf algebra should be completed.
-/
theorem proofTheoreticGraftingSupport_has_pointwise_preLie_identity
    (x y z : PTree) :
    ClassLevelPreLieIdentity x y z :=
  classLevelPreLieIdentity_from_pointwise x y z

/--
A finite formal sum of generators of derivable trees belongs to the
derivable-tree submodule.
-/
theorem foldr_treeGen_mem_derivableTreeSubmodule
    {base : BaseRel} {xs : List PTree}
    (hxs : ∀ v : PTree, v ∈ xs → DerivableTree base v) :
    xs.foldr (fun v acc => treeGen v + acc) 0 ∈
      derivableTreeSubmodule base := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldr_cons]
      apply Submodule.add_mem
      · exact treeGen_mem_derivableTreeSubmodule (hxs x (by simp))
      · apply ih
        intro v hv
        exact hxs v (by simp [hv])

/--
The primitive tree-level pre-Lie grafting product of two closed derivation
trees lands in the span of closed derivation trees.

This is the first linear grafting-side closure theorem.  It is weaker than a
full Oudom-Guin Hopf algebra, but it is exactly the preservation statement the
future OG product must extend.
-/
theorem graftPreLieTree_mem_derivableTreeSubmodule
    {base : BaseRel} {u t : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t) :
    PTree.graftPreLieTree u t ∈ derivableTreeSubmodule base := by
  unfold PTree.graftPreLieTree
  apply foldr_treeGen_mem_derivableTreeSubmodule
  intro v hv
  exact internalGraft_preserves_derivable hu ht
    (internalGraft_of_mem_matchingLeafGraftings hv)

/--
Generator-level linear form: the raw bilinear pre-Lie product sends
derivable tree generators to the derivable-tree submodule.
-/
theorem graftPreLie_generators_mem_derivableTreeSubmodule
    {base : BaseRel} {u t : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t) :
    graftPreLie (treeGen u) (treeGen t) ∈
      derivableTreeSubmodule base := by
  rw [graftPreLie_on_generators]
  exact graftPreLieTree_mem_derivableTreeSubmodule hu ht

@[simp]
theorem graftPreLie_left_generator
    (u : PTree) :
    graftPreLie (treeGen u) = graftPreLieRight u := by
  simp [graftPreLie, treeGen]

/--
For a closed inserted proof tree `u`, right-grafting by `u` preserves the
linear span of closed derivation trees.
-/
theorem graftPreLieRight_mem_derivableTreeSubmodule
    {base : BaseRel} {u : PTree}
    (hu : DerivableTree base u)
    {x : PreLieCarrier}
    (hx : x ∈ derivableTreeSubmodule base) :
    graftPreLieRight u x ∈ derivableTreeSubmodule base := by
  change x ∈ Submodule.span ℤ (derivableTreeGeneratorSet base) at hx
  refine Submodule.span_induction
    (s := derivableTreeGeneratorSet base)
    (p := fun x _ => graftPreLieRight u x ∈ derivableTreeSubmodule base)
    ?gen ?zero ?add ?smul hx
  · intro a ha
    rcases ha with ⟨t, ht, rfl⟩
    rw [graftPreLieRight_on_generator]
    exact graftPreLieTree_mem_derivableTreeSubmodule hu ht
  · simp
  · intro x y _hx _hy ihx ihy
    simpa using Submodule.add_mem (derivableTreeSubmodule base) ihx ihy
  · intro c x _hx ihx
    simpa using Submodule.smul_mem (derivableTreeSubmodule base) c ihx

/--
The raw bilinear pre-Lie product preserves the derivable-tree submodule in both
arguments.

This is the cleanest current proof-theoretic grafting algebra statement:
although the full Oudom-Guin Hopf algebra is not yet completed, its primitive
pre-Lie product is already closed on the linear span of genuine NMMS proof
trees.
-/
theorem graftPreLie_mem_derivableTreeSubmodule
    {base : BaseRel} {x y : PreLieCarrier}
    (hx : x ∈ derivableTreeSubmodule base)
    (hy : y ∈ derivableTreeSubmodule base) :
    graftPreLie x y ∈ derivableTreeSubmodule base := by
  change x ∈ Submodule.span ℤ (derivableTreeGeneratorSet base) at hx
  refine Submodule.span_induction
    (s := derivableTreeGeneratorSet base)
    (p := fun x _ => graftPreLie x y ∈ derivableTreeSubmodule base)
    ?gen ?zero ?add ?smul hx
  · intro a ha
    rcases ha with ⟨u, hu, rfl⟩
    rw [graftPreLie_left_generator]
    exact graftPreLieRight_mem_derivableTreeSubmodule hu hy
  · simp
  · intro x₁ x₂ _hx₁ _hx₂ ih₁ ih₂
    change graftPreLie (x₁ + x₂) y ∈ derivableTreeSubmodule base
    rw [map_add]
    exact Submodule.add_mem (derivableTreeSubmodule base) ih₁ ih₂
  · intro c x _hx ih
    change graftPreLie (c • x) y ∈ derivableTreeSubmodule base
    rw [map_smul]
    exact Submodule.smul_mem (derivableTreeSubmodule base) c ih

/-! ## The restricted proof-theoretic pre-Lie carrier -/

/--
The linear carrier of closed proof trees over a fixed material base.

This is the proof-theoretic subspace of the ambient raw pre-Lie carrier.
-/
abbrev DerivablePreLieCarrier (base : BaseRel) :=
  derivableTreeSubmodule base

/-- The generator attached to a closed derivation tree. -/
noncomputable def derivableTreeGen
    {base : BaseRel} (t : DerivableProofTree base) :
    DerivablePreLieCarrier base :=
  ⟨treeGen t.1, treeGen_mem_derivableTreeSubmodule t.2⟩

@[simp]
theorem derivableTreeGen_val
    {base : BaseRel} (t : DerivableProofTree base) :
    (derivableTreeGen t : PreLieCarrier) = treeGen t.1 := rfl

/--
Right multiplication for the restricted proof-theoretic pre-Lie product.

For fixed `x`, this is the ambient map `graftPreLie x` restricted to the
derivable-tree submodule.
-/
noncomputable def derivableGraftPreLieRight
    (base : BaseRel) (x : DerivablePreLieCarrier base) :
    DerivablePreLieCarrier base →ₗ[ℤ] DerivablePreLieCarrier base where
  toFun y :=
    ⟨graftPreLie x.1 y.1,
      graftPreLie_mem_derivableTreeSubmodule x.2 y.2⟩
  map_add' y z := by
    apply Subtype.ext
    simp
  map_smul' c y := by
    apply Subtype.ext
    simp

@[simp]
theorem derivableGraftPreLieRight_apply_val
    {base : BaseRel}
    (x y : DerivablePreLieCarrier base) :
    (derivableGraftPreLieRight base x y : PreLieCarrier) =
      graftPreLie x.1 y.1 := rfl

/--
The restricted proof-theoretic pre-Lie product on the closed linear sector.

This is the concrete pre-Lie-side algebraic object currently available for the
future Oudom-Guin completion.
-/
noncomputable def derivableGraftPreLie
    (base : BaseRel) :
    DerivablePreLieCarrier base →ₗ[ℤ]
      DerivablePreLieCarrier base →ₗ[ℤ] DerivablePreLieCarrier base where
  toFun x := derivableGraftPreLieRight base x
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change graftPreLie (x.1 + y.1) z.1 =
      graftPreLie x.1 z.1 + graftPreLie y.1 z.1
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change graftPreLie (c • x.1) z.1 =
      c • graftPreLie x.1 z.1
    simp

@[simp]
theorem derivableGraftPreLie_apply_val
    {base : BaseRel}
    (x y : DerivablePreLieCarrier base) :
    (derivableGraftPreLie base x y : PreLieCarrier) =
      graftPreLie x.1 y.1 := rfl

/--
On closed proof-tree generators, the restricted product is the same primitive
matching-leaf grafting sum as the ambient product.
-/
theorem derivableGraftPreLie_treeGen
    {base : BaseRel}
    (u t : DerivableProofTree base) :
    (derivableGraftPreLie base
        (derivableTreeGen u) (derivableTreeGen t) : PreLieCarrier) =
      PTree.graftPreLieTree u.1 t.1 := by
  simp only [derivableGraftPreLie_apply_val, derivableTreeGen_val]
  exact graftPreLie_on_generators u.1 t.1

/-! ## Pre-Lie law targets for the derivable grafting carrier -/

/--
The associator of the restricted proof-theoretic grafting product.

This is the expression whose right symmetry is needed before the closed
derivable sector can be used as the pre-Lie input for an Oudom-Guin style
Hopf algebra.
-/
noncomputable def derivableGraftAssociator
    (base : BaseRel)
    (x y z : DerivablePreLieCarrier base) :
    DerivablePreLieCarrier base :=
  derivableGraftPreLie base (derivableGraftPreLie base x y) z -
    derivableGraftPreLie base x (derivableGraftPreLie base y z)

@[simp]
theorem derivableGraftAssociator_val
    {base : BaseRel}
    (x y z : DerivablePreLieCarrier base) :
    (derivableGraftAssociator base x y z : PreLieCarrier) =
      graftPreLie (graftPreLie x.1 y.1) z.1 -
        graftPreLie x.1 (graftPreLie y.1 z.1) := by
  rfl

/--
Right pre-Lie symmetry for the restricted derivable grafting product.

This is the exact algebraic law needed on the proof-theoretic carrier before
one can build the corresponding Oudom-Guin/enveloping Hopf algebra there.
-/
def DerivableRightPreLieLaw (base : BaseRel) : Prop :=
  ∀ x y z : DerivablePreLieCarrier base,
    derivableGraftAssociator base x y z =
      derivableGraftAssociator base x z y

/--
Generator-level version of the right pre-Lie law on genuine proof trees.

This is often the most usable theorem target: the old GL/OG files prove and
transport pre-Lie identities from tree generators, and trilinearity then
extends them to the whole linear carrier.
-/
def DerivableGeneratorRightPreLieLaw (base : BaseRel) : Prop :=
  ∀ x y z : DerivableProofTree base,
    derivableGraftAssociator base
        (derivableTreeGen x) (derivableTreeGen y) (derivableTreeGen z) =
      derivableGraftAssociator base
        (derivableTreeGen x) (derivableTreeGen z) (derivableTreeGen y)

theorem DerivableRightPreLieLaw.generator
    {base : BaseRel}
    (h : DerivableRightPreLieLaw base) :
    DerivableGeneratorRightPreLieLaw base := by
  intro x y z
  exact h (derivableTreeGen x) (derivableTreeGen y) (derivableTreeGen z)

/--
If the ambient raw grafting product satisfies the right pre-Lie law everywhere,
then its restriction to the closed derivable sector also satisfies it.

This separates the proof-theoretic closure theorem above from the remaining
algebraic theorem needed for the OG construction.
-/
theorem derivableRightPreLieLaw_of_ambient_everywhere
    {base : BaseRel}
    (h :
      ∀ x y z : PreLieCarrier,
        graftPreLie (graftPreLie x y) z -
            graftPreLie x (graftPreLie y z) =
          graftPreLie (graftPreLie x z) y -
            graftPreLie x (graftPreLie z y)) :
    DerivableRightPreLieLaw base := by
  intro x y z
  apply Subtype.ext
  simpa only [derivableGraftAssociator_val] using h x.1 y.1 z.1

/--
A bundled GL/OG generator-compatible product whose multiplication is the raw
grafting product supplies the full pre-Lie law on the derivable sector.

This is the clean adapter from the old algebraic development to the new
proof-theoretic carrier: once the ambient generator-compatible product is
identified with `graftPreLie`, the closed NMMS sector inherits the right
pre-Lie law.
-/
theorem derivableRightPreLieLaw_of_generatorCompatibleTreeProduct
    {base : BaseRel}
    (p : GeneratorCompatibleTreeProduct)
    (hp : p.mul = graftPreLie) :
    DerivableRightPreLieLaw base := by
  apply derivableRightPreLieLaw_of_ambient_everywhere
  intro x y z
  have h := p.rightPreLie_everywhere x y z
  simpa [hp] using h

/--
Generator-level transport from the ambient GL/OG theorem shape to the
proof-theoretic derivable carrier.

This theorem is a bridge, not the whole Hopf algebra: it says that an ambient
generator-level pre-Lie identity for `graftPreLie` immediately becomes the
same identity on closed NMMS proof-tree generators.
-/
theorem derivableGeneratorRightPreLieLaw_of_ambient
    {base : BaseRel}
    (h : GeneratorRightPreLieLaw graftPreLie) :
    DerivableGeneratorRightPreLieLaw base := by
  intro x y z
  apply Subtype.ext
  simpa only [derivableGraftAssociator_val, derivableTreeGen_val] using
    h x.1 y.1 z.1

/--
Bundled pre-Lie input for the proof-theoretic Oudom-Guin completion.

The project now has the carrier and restricted grafting product.  Supplying
this law is the remaining algebraic datum needed before constructing the
grafting-side Hopf algebra over genuine closed proof trees.
-/
structure DerivableOGPreLieInput (base : BaseRel) where
  rightPreLie_on_generators : DerivableGeneratorRightPreLieLaw base

namespace DerivableOGPreLieInput

/--
Build the proof-theoretic OG input from an ambient generator-level pre-Lie law.
-/
def ofAmbientGeneratorLaw
    {base : BaseRel}
    (h : GeneratorRightPreLieLaw graftPreLie) :
    DerivableOGPreLieInput base where
  rightPreLie_on_generators :=
    derivableGeneratorRightPreLieLaw_of_ambient h

end DerivableOGPreLieInput

/-! ## Structural-rule probes -/

/--
External weakening by a single component preserves the derivable sector exactly
when the added component is itself derivable.

This is deliberately weaker than saying external weakening is a valid logical
rule.  It only records the closure property of the derivable sector.  Whether
the added component is licensed proof-theoretically is controlled by separate
policies such as graft-controlled weakening or splitting.
-/
theorem external_add_component_preserves_derivableHypersequent
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hG : DerivableHypersequent base G)
    (ht : DerivableTree base t) :
    DerivableHypersequent base (G + HQ.singleton t) :=
  derivableHypersequent_add hG (derivableHypersequent_singleton ht)

/--
If a component is externally added to a derivable hypersequent and the result
is derivable, then the added component is derivable.

This is the formal shadow of the nonmonotonic warning: arbitrary external
weakening is not licensed by the hypersequent structure itself.  The new
component must already carry genuine derivational provenance, or be supplied
by a separate structural witness.
-/
theorem derivable_of_external_add_component_derivable
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hGt : DerivableHypersequent base (G + HQ.singleton t)) :
    DerivableTree base t := by
  exact hGt t (by
    rw [Multiset.mem_add]
    exact Or.inr (by simp [HQ.singleton]))

/-! ## The two turnstiles: material base versus logical closure -/

/--
The primitive material consequence relation, corresponding to the paper's
subscript-zero turnstile.

This is not the full logical derivability relation.  It is the fixed material
base over which `NMMS` derivations are generated.
-/
def MaterialEntails
    (base : BaseRel) (Γ Θ : Multiset MyProp) : Prop :=
  base Γ Θ

/--
The logical derivability relation generated over a material base, corresponding
to the paper's ordinary NMMS turnstile.
-/
def LogicalEntails
    (base : BaseRel) (Γ Θ : Multiset MyProp) : Prop :=
  DerivableSequent base (Γ ∣∼ Θ)

/--
Every primitive material consequence is available as a logical derivation by
the base-axiom rule.
-/
theorem materialEntails_logicalEntails
    {base : BaseRel} {Γ Θ : Multiset MyProp}
    (h : MaterialEntails base Γ Θ) :
    LogicalEntails base Γ Θ := by
  exact derivableSequent_of_derivation (NMMS.baseAx h)

/-- An identity/initial sequent has the same formula on both sides. -/
def IdentityAxiomSequent (s : MultiSequent) : Prop :=
  ∃ A Γ Θ, s = (A ::ₘ Γ ∣∼ A ::ₘ Θ)

/--
The full logical identity axiom schema.

This is stated as an admissibility property, not assumed for the current NMMS
calculus.  If added, it is the usual sequent-calculus axiom
`Γ, A ⊢ A, Θ`, with order suppressed by multisets.
-/
def LogicalIdentityAxiomAdmissible (base : BaseRel) : Prop :=
  ∀ A Γ Θ, LogicalEntails base (A ::ₘ Γ) (A ::ₘ Θ)

/--
Material identity restricted to the primitive/base fragment.

Because `BaseRel` only licenses prelogical/base formulas, a material identity
schema can only be stated for base-formula contexts.  The unrestricted identity
axiom, if desired, belongs to the logical/sequent layer above the material
turnstile.
-/
def MaterialBaseIdentityAxiomAdmissible (base : BaseRel) : Prop :=
  ∀ A Γ Θ,
    IsBaseFormula A →
      IsBaseMultiset Γ →
        IsBaseMultiset Θ →
          MaterialEntails base (A ::ₘ Γ) (A ::ₘ Θ)

/--
Material identity in the base fragment gives logical identity sequents in the
same fragment by the `baseAx` rule.
-/
theorem materialBaseIdentity_logicalEntails_base_identity
    {base : BaseRel}
    (h : MaterialBaseIdentityAxiomAdmissible base)
    {A : MyProp} {Γ Θ : Multiset MyProp}
    (hA : IsBaseFormula A)
    (hΓ : IsBaseMultiset Γ)
    (hΘ : IsBaseMultiset Θ) :
    LogicalEntails base (A ::ₘ Γ) (A ::ₘ Θ) := by
  exact materialEntails_logicalEntails (h A Γ Θ hA hΓ hΘ)

/-- A logical identity axiom schema proves every identity-shaped sequent. -/
theorem logicalIdentityAxiom_derivable
    {base : BaseRel}
    (h : LogicalIdentityAxiomAdmissible base)
    {s : MultiSequent}
    (hs : IdentityAxiomSequent s) :
    DerivableSequent base s := by
  rcases hs with ⟨A, Γ, Θ, rfl⟩
  exact h A Γ Θ

/--
Forward comma/implication residuation at the sequent level.

This is the direction already built into the calculus by `imp_r`:
from `α, β ⊢ γ` we infer `β ⊢ α ⇒ γ`.
-/
def LogicalCommaResiduationForwardAt
    (base : BaseRel) (α β γ : MyProp) : Prop :=
  LogicalEntails base (α ::ₘ β ::ₘ (0 : Multiset MyProp))
      (γ ::ₘ (0 : Multiset MyProp)) →
    LogicalEntails base (β ::ₘ (0 : Multiset MyProp))
      ((α ⇒ γ) ::ₘ (0 : Multiset MyProp))

/--
Reverse comma/implication residuation at the sequent level.

This is the direction that normally needs identity plus a suitable
composition/cut principle: from `β ⊢ α ⇒ γ`, recover `α, β ⊢ γ`.
-/
def LogicalCommaResiduationReverseAt
    (base : BaseRel) (α β γ : MyProp) : Prop :=
  LogicalEntails base (β ::ₘ (0 : Multiset MyProp))
      ((α ⇒ γ) ::ₘ (0 : Multiset MyProp)) →
    LogicalEntails base (α ::ₘ β ::ₘ (0 : Multiset MyProp))
      (γ ::ₘ (0 : Multiset MyProp))

/-- The full residuation equivalence for comma and implication. -/
def LogicalCommaResiduationAt
    (base : BaseRel) (α β γ : MyProp) : Prop :=
  LogicalEntails base (α ::ₘ β ::ₘ (0 : Multiset MyProp))
      (γ ::ₘ (0 : Multiset MyProp)) ↔
    LogicalEntails base (β ::ₘ (0 : Multiset MyProp))
      ((α ⇒ γ) ::ₘ (0 : Multiset MyProp))

/-- The forward residuation direction is a theorem of the current calculus. -/
theorem logicalCommaResiduation_forward
    {base : BaseRel} {α β γ : MyProp} :
    LogicalCommaResiduationForwardAt base α β γ := by
  rintro ⟨d⟩
  exact ⟨NMMS.imp_r d⟩

/-- Reverse residuation as an admissibility schema. -/
def LogicalCommaResiduationReverseAdmissible (base : BaseRel) : Prop :=
  ∀ α β γ, LogicalCommaResiduationReverseAt base α β γ

/-- Full comma/implication residuation as an admissibility schema. -/
def LogicalCommaResiduationAdmissible (base : BaseRel) : Prop :=
  ∀ α β γ, LogicalCommaResiduationAt base α β γ

/--
The full residuation law is reduced to the reverse direction, because the
forward direction is already supplied by `imp_r`.
-/
theorem logicalCommaResiduation_of_reverse
    {base : BaseRel}
    (hrev : LogicalCommaResiduationReverseAdmissible base) :
    LogicalCommaResiduationAdmissible base := by
  intro α β γ
  constructor
  · exact logicalCommaResiduation_forward
  · exact hrev α β γ

/-! ### Structural comma and abstract fusion -/

/--
The two-formula antecedent comma, represented at the structural level as
multiset union of singleton antecedents.

This deliberately treats comma as punctuation/structure, not yet as an
object-language connective.
-/
def AntecedentComma₂ (α β : MyProp) : Multiset MyProp :=
  (α ::ₘ (0 : Multiset MyProp)) + (β ::ₘ (0 : Multiset MyProp))

/--
Single-succedent cut, stated only in the shape needed for the comma/fusion
bridge.
-/
def LogicalSingleSuccedentCutAdmissible (base : BaseRel) : Prop :=
  ∀ Γ Δ A γ,
    LogicalEntails base Γ (A ::ₘ (0 : Multiset MyProp)) →
      LogicalEntails base (A ::ₘ Δ) (γ ::ₘ (0 : Multiset MyProp)) →
        LogicalEntails base (Γ + Δ) (γ ::ₘ (0 : Multiset MyProp))

/--
Left fusion rule for an abstract connective `fusion`.

If the structural comma `A, B` suffices in an antecedent context, then the
single formula `fusion A B` suffices in that context.
-/
def LogicalFusionLeftRuleAdmissible
    (base : BaseRel) (fusion : MyProp → MyProp → MyProp) : Prop :=
  ∀ A B Γ γ,
    LogicalEntails base (AntecedentComma₂ A B + Γ)
        (γ ::ₘ (0 : Multiset MyProp)) →
      LogicalEntails base ((fusion A B) ::ₘ Γ)
        (γ ::ₘ (0 : Multiset MyProp))

/--
Right fusion rule for an abstract connective `fusion`.

If `A` follows from one antecedent context and `B` follows from another, then
`fusion A B` follows from the structural combination of the contexts.
-/
def LogicalFusionRightRuleAdmissible
    (base : BaseRel) (fusion : MyProp → MyProp → MyProp) : Prop :=
  ∀ A B Γ Δ,
    LogicalEntails base Γ (A ::ₘ (0 : Multiset MyProp)) →
      LogicalEntails base Δ (B ::ₘ (0 : Multiset MyProp)) →
        LogicalEntails base (Γ + Δ)
          ((fusion A B) ::ₘ (0 : Multiset MyProp))

/--
Fusion faithfully represents a two-place antecedent comma for a particular
triple of formulas.
-/
def LogicalFusionRepresentsCommaAt
    (base : BaseRel) (fusion : MyProp → MyProp → MyProp)
    (α β γ : MyProp) : Prop :=
  LogicalEntails base (AntecedentComma₂ α β)
      (γ ::ₘ (0 : Multiset MyProp)) ↔
    LogicalEntails base ((fusion α β) ::ₘ (0 : Multiset MyProp))
      (γ ::ₘ (0 : Multiset MyProp))

/--
Fusion represents structural comma when the fusion rules, single-succedent cut,
and logical identity axioms are available.

This is the sequent-calculus content behind the usual theorem that comma can
be represented conservatively by multiplicative conjunction/fusion.
-/
theorem logicalFusionRepresentsComma_of_rules_cut_identity
    {base : BaseRel} {fusion : MyProp → MyProp → MyProp}
    (hL : LogicalFusionLeftRuleAdmissible base fusion)
    (hR : LogicalFusionRightRuleAdmissible base fusion)
    (hCut : LogicalSingleSuccedentCutAdmissible base)
    (hId : LogicalIdentityAxiomAdmissible base)
    (α β γ : MyProp) :
    LogicalFusionRepresentsCommaAt base fusion α β γ := by
  constructor
  · intro hcomma
    simpa using hL α β (0 : Multiset MyProp) γ (by
      simpa [AntecedentComma₂] using hcomma)
  · intro hfusion
    have hmake :
        LogicalEntails base (AntecedentComma₂ α β)
          ((fusion α β) ::ₘ (0 : Multiset MyProp)) := by
      simpa [AntecedentComma₂] using
        hR α β
          (α ::ₘ (0 : Multiset MyProp))
          (β ::ₘ (0 : Multiset MyProp))
          (hId α (0 : Multiset MyProp) (0 : Multiset MyProp))
          (hId β (0 : Multiset MyProp) (0 : Multiset MyProp))
    have hcut :=
      hCut (AntecedentComma₂ α β) (0 : Multiset MyProp)
        (fusion α β) γ hmake hfusion
    simpa using hcut

/--
Logical consequence is monotone under explicit extension of the material base.

This is not antecedent weakening inside a fixed base.  It is persistence of
already-built derivations when the primitive material relation itself is
extended.
-/
theorem logicalEntails_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {Γ Θ : Multiset MyProp}
    (h : LogicalEntails base Γ Θ) :
    LogicalEntails base' Γ Θ :=
  derivableSequent_mono hbase h

/--
A logical entailment is destroyed by a base update when it is derivable before
the update but not after it.

This is the external/nonmonotonic phenomenon from the paper: the primitive
material base changes, and the logical closure generated over that base changes
with it.
-/
def LogicalEntailmentDestroyedByUpdate
    (U : AdmissibleBaseUpdate) (base : BaseRel)
    (Γ Θ : Multiset MyProp) : Prop :=
  ∃ base' : BaseRel,
    U base base' ∧
      LogicalEntails base Γ Θ ∧
        ¬ LogicalEntails base' Γ Θ

/--
No ordinary monotone base extension can destroy an already established logical
entailment.
-/
theorem not_destroyed_under_monotoneBaseUpdate
    {base : BaseRel} {Γ Θ : Multiset MyProp}
    (h : LogicalEntails base Γ Θ) :
    ¬ LogicalEntailmentDestroyedByUpdate
      monotoneBaseUpdate base Γ Θ := by
  rintro ⟨base', hbase, _hold, hnew⟩
  exact hnew (logicalEntails_mono_base hbase h)

/--
If an update destroys a logical entailment, then that update is not just a
monotone extension of the primitive material base.
-/
theorem destroyed_update_not_base_extension
    {U : AdmissibleBaseUpdate} {base : BaseRel} {Γ Θ : Multiset MyProp}
    (h : LogicalEntailmentDestroyedByUpdate U base Γ Θ) :
    ∃ base' : BaseRel, U base base' ∧ ¬ BaseRelExtends base base' := by
  rcases h with ⟨base', hU, hold, hnew⟩
  refine ⟨base', hU, ?_⟩
  intro hbase
  exact hnew (logicalEntails_mono_base hbase hold)

/--
A proof tree is destroyed by a base update when it was an actual derivation
tree over the old material base but is no longer derivable over some updated
base.

This is the tree-level version of `LogicalEntailmentDestroyedByUpdate`, and it
is the relevant notion for the Hopf side because the algebraic generators are
proof trees rather than bare sequents.
-/
def DerivableTreeDestroyedByUpdate
    (U : AdmissibleBaseUpdate) (base : BaseRel) (t : PTree) : Prop :=
  ∃ base' : BaseRel,
    U base base' ∧
      DerivableTree base t ∧
        ¬ DerivableTree base' t

/--
Monotone base extension cannot destroy a previously derivable proof tree.
-/
theorem not_derivableTree_destroyed_under_monotoneBaseUpdate
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ¬ DerivableTreeDestroyedByUpdate monotoneBaseUpdate base t := by
  rintro ⟨base', hbase, _hold, hnew⟩
  exact hnew (derivableTree_mono hbase ht)

/--
If an update destroys a derivable proof tree, then the update is not merely a
monotone extension of the primitive material base.
-/
theorem derivableTree_destroyed_update_not_base_extension
    {U : AdmissibleBaseUpdate} {base : BaseRel} {t : PTree}
    (h : DerivableTreeDestroyedByUpdate U base t) :
    ∃ base' : BaseRel, U base base' ∧ ¬ BaseRelExtends base base' := by
  rcases h with ⟨base', hU, ht, hnew⟩
  refine ⟨base', hU, ?_⟩
  intro hbase
  exact hnew (derivableTree_mono hbase ht)

theorem proofTheoreticGraftingSupport_not_of_insert_nonderivable
    {base : BaseRel} {u t v : PTree}
    (hu : ¬ DerivableTree base u) :
    ¬ ProofTheoreticGraftingSupport base u t v := by
  intro h
  exact hu h.1

theorem proofTheoreticGraftingSupport_not_of_host_nonderivable
    {base : BaseRel} {u t v : PTree}
    (ht : ¬ DerivableTree base t) :
    ¬ ProofTheoreticGraftingSupport base u t v := by
  intro h
  exact ht h.2.1

theorem proofTheoreticGraftingSupport_not_of_output_nonderivable
    {base : BaseRel} {u t v : PTree}
    (hv : ¬ DerivableTree base v) :
    ¬ ProofTheoreticGraftingSupport base u t v := by
  intro h
  exact hv h.2.2.2

theorem proofTheoreticSingletonHypersequentGraftingSupport_not_of_insert_nonderivable
    {base : BaseRel} {u : PTree} {T V : Hypersequent}
    (hu : ¬ DerivableTree base u) :
    ¬ ProofTheoreticSingletonHypersequentGraftingSupport base
        (HQ.singleton u) T V := by
  intro h
  have hU : DerivableHypersequent base (HQ.singleton u) :=
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable h).1
  exact hu (derivableHypersequent_singleton_iff.mp hU)

theorem proofTheoreticSingletonHypersequentGraftingSupport_not_of_host_nonderivable
    {base : BaseRel} {t : PTree} {U V : Hypersequent}
    (ht : ¬ DerivableTree base t) :
    ¬ ProofTheoreticSingletonHypersequentGraftingSupport base U
        (HQ.singleton t) V := by
  intro h
  have hT : DerivableHypersequent base (HQ.singleton t) :=
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable h).2.1
  exact ht (derivableHypersequent_singleton_iff.mp hT)

theorem proofTheoreticSingletonHypersequentGraftingSupport_not_of_output_nonderivable
    {base : BaseRel} {v : PTree} {U T : Hypersequent}
    (hv : ¬ DerivableTree base v) :
    ¬ ProofTheoreticSingletonHypersequentGraftingSupport base U T
        (HQ.singleton v) := by
  intro h
  have hV : DerivableHypersequent base (HQ.singleton v) :=
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable h).2.2
  exact hv (derivableHypersequent_singleton_iff.mp hV)

theorem derivableTreeDestroyedByUpdate_blocks_grafting_support_as_host
    {U : AdmissibleBaseUpdate} {base : BaseRel} {t : PTree}
    (h : DerivableTreeDestroyedByUpdate U base t) :
    ∃ base' : BaseRel,
      U base base' ∧
        DerivableTree base t ∧
          ¬ DerivableTree base' t ∧
            ∀ u v : PTree,
              ¬ ProofTheoreticGraftingSupport base' u t v := by
  rcases h with ⟨base', hU, ht, hnew⟩
  exact
    ⟨base', hU, ht, hnew, by
      intro u v
      exact proofTheoreticGraftingSupport_not_of_host_nonderivable hnew⟩

theorem derivableTreeDestroyedByUpdate_blocks_singleton_grafting_support_as_host
    {U : AdmissibleBaseUpdate} {base : BaseRel} {t : PTree}
    (h : DerivableTreeDestroyedByUpdate U base t) :
    ∃ base' : BaseRel,
      U base base' ∧
        DerivableTree base t ∧
          ¬ DerivableTree base' t ∧
            ∀ U V : Hypersequent,
              ¬ ProofTheoreticSingletonHypersequentGraftingSupport
                base' U (HQ.singleton t) V := by
  rcases h with ⟨base', hU, ht, hnew⟩
  exact
    ⟨base', hU, ht, hnew, by
      intro U V
      exact
        proofTheoreticSingletonHypersequentGraftingSupport_not_of_host_nonderivable
          hnew⟩

/-! ## Terminal leaves of closed and open proof trees -/

namespace PTree

/--
All terminal leaves of a proof tree satisfy a sequent predicate.

For closed proof trees, the predicate will be "is a base/material axiom".
For open proof contexts, the predicate will be "is either a base/material axiom
or an exposed boundary/interface sequent".
-/
def LeafSequentsSatisfy (P : MultiSequent → Prop) : PTree → Prop
| PTree.leaf s => P s
| PTree.node _ _ cs => ∀ c : PTree, c ∈ cs → LeafSequentsSatisfy P c

@[simp]
theorem leafSequentsSatisfy_leaf
    (P : MultiSequent → Prop) (s : MultiSequent) :
    LeafSequentsSatisfy P (PTree.leaf s) ↔ P s := by
  simp [LeafSequentsSatisfy]

@[simp]
theorem leafSequentsSatisfy_node
    (P : MultiSequent → Prop) (r : RuleTag)
    (s : MultiSequent) (cs : List PTree) :
    LeafSequentsSatisfy P (PTree.node r s cs) ↔
      ∀ c : PTree, c ∈ cs → LeafSequentsSatisfy P c := by
  simp [LeafSequentsSatisfy]

@[simp]
theorem remainderGo_singleton_child_same
    (i : Nat) (rest : Address) (t : PTree) :
    PTree.remainderGo [i :: rest] [i] t =
      PTree.remainderGo [rest] [] t := by
  rw [← PTree.remainderGo_restrictCut_eq
    (cut := [i :: rest]) (i := i) (t := t)]
  simp [PTree.restrictCut]

@[simp]
theorem remainderGo_singleton_child_ne
    {i j : Nat} (rest : Address) (t : PTree)
    (hji : j ≠ i) :
    PTree.remainderGo [i :: rest] [j] t = t := by
  rw [← PTree.remainderGo_restrictCut_eq
    (cut := [i :: rest]) (i := j) (t := t)]
  have hij : ¬ i = j := by
    intro h
    exact hji h.symm
  simp [PTree.restrictCut, hij, PTree.remainderGo_nil]

end PTree

/-- A terminal sequent is closed when it is licensed by the material base. -/
def MaterialTerminalSequent
    (base : BaseRel) (s : MultiSequent) : Prop :=
  MaterialEntails base s.lhs s.rhs

/--
An open terminal sequent is either a material/base axiom or one of the
declared boundary sequents.
-/
def OpenTerminalSequent
    (base : BaseRel) (B : Multiset MultiSequent) (s : MultiSequent) : Prop :=
  MaterialTerminalSequent base s ∨ s ∈ B

/--
Every terminal leaf of a closed NMMS proof tree is a material/base axiom.

This is the formal version of the proof-theoretic frontier condition: a closed
derivation may end only in primitive material axioms.
-/
theorem nmms_toTree_leafSequents_material
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    PTree.LeafSequentsSatisfy
      (MaterialTerminalSequent base) (NMMS.toTree d) := by
  induction d <;>
    simp [NMMS.toTree, PTree.LeafSequentsSatisfy,
      MaterialTerminalSequent, MaterialEntails, *]

theorem derivableTree_leafSequents_material
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    PTree.LeafSequentsSatisfy
      (MaterialTerminalSequent base) t := by
  rcases ht with ⟨s, d, rfl⟩
  exact nmms_toTree_leafSequents_material d

/-! ## Base-managed external weakening policies -/

/--
A raw external weakening move: add one component according to a policy.

This isolates the weakening constructor from the other external structural
steps such as contraction and splitting.
-/
def ExternalWeakeningMove
    (W : ExternalWeakeningPolicy) (G H : Hypersequent) : Prop :=
  ∃ t : PTree, W.admissible t ∧ H = G + HQ.singleton t

/--
External structural steps indexed by their structural-rule label.

This is a labelled refinement of `ExternalStep`: the carrier-level operation is
unchanged, but the proof-theoretic trace records whether the external move was
weakening, contraction, permutation, or splitting.
-/
inductive LabelledExternalStep (W : ExternalWeakeningPolicy) :
    StructuralRuleTag → Hypersequent → Hypersequent → Prop where
| perm
    {G H : Hypersequent}
    (h : G = H) :
    LabelledExternalStep W StructuralRuleTag.externalPermutation G H
| contraction
    (G : Hypersequent)
    (t : PTree) :
    LabelledExternalStep W StructuralRuleTag.externalContraction
      (G + HQ.singleton t + HQ.singleton t)
      (G + HQ.singleton t)
| weakening
    (G : Hypersequent)
    (t : PTree)
    (ht : W.admissible t) :
    LabelledExternalStep W StructuralRuleTag.externalWeakening
      G (G + HQ.singleton t)
| split
    (G : Hypersequent)
    (t : PTree)
    (Γ : Hypersequent)
    (r : PTree)
    (hs : SplitsTo t Γ r) :
    LabelledExternalStep W StructuralRuleTag.externalSplit
      (G + HQ.singleton t)
      (G + Γ + HQ.singleton r)

namespace LabelledExternalStep

/-- Forget the structural label on a labelled external step. -/
theorem toExternalStep
    {W : ExternalWeakeningPolicy} {tag : StructuralRuleTag}
    {G H : Hypersequent}
    (h : LabelledExternalStep W tag G H) :
    ExternalStep W G H := by
  cases h with
  | perm h => exact ExternalStep.perm h
  | contraction G t => exact ExternalStep.contraction G t
  | weakening G t ht => exact ExternalStep.weakening G t ht
  | split G t Γ r hs => exact ExternalStep.split G t Γ r hs

/-- A labelled external weakening step is exactly an external weakening move. -/
theorem weakening_to_move
    {W : ExternalWeakeningPolicy} {G H : Hypersequent}
    (h : LabelledExternalStep W StructuralRuleTag.externalWeakening G H) :
    ExternalWeakeningMove W G H := by
  cases h with
  | weakening G t ht => exact ⟨t, ht, rfl⟩

/-- Any external weakening move can be viewed as the labelled weakening step. -/
theorem weakening_of_move
    {W : ExternalWeakeningPolicy} {G H : Hypersequent}
    (h : ExternalWeakeningMove W G H) :
    LabelledExternalStep W StructuralRuleTag.externalWeakening G H := by
  rcases h with ⟨t, ht, rfl⟩
  exact LabelledExternalStep.weakening G t ht

@[simp]
theorem labelled_externalWeakening_iff_move
    {W : ExternalWeakeningPolicy} {G H : Hypersequent} :
    LabelledExternalStep W StructuralRuleTag.externalWeakening G H ↔
      ExternalWeakeningMove W G H :=
  ⟨weakening_to_move, weakening_of_move⟩

end LabelledExternalStep

/--
The minimal NMMS external weakening policy admits no weakening moves.
-/
theorem no_nmmsExternalWeakeningMove
    (G H : Hypersequent) :
    ¬ ExternalWeakeningMove nmmsWeakeningPolicy G H := by
  rintro ⟨t, ht, _⟩
  exact nmmsWeakeningPolicy_no_admissible t ht

/--
The base-derivable external weakening policy allows adding a component only
when that component already carries closed derivational provenance over the
material base.

This still does not make external weakening a logical rule of NMMS.  It is a
controlled policy for the proof-labelled hypersequent layer.
-/
def baseDerivableWeakeningPolicy (base : BaseRel) :
    ExternalWeakeningPolicy where
  admissible t := DerivableTree base t

@[simp]
theorem baseDerivableWeakeningPolicy_admissible
    (base : BaseRel) (t : PTree) :
    (baseDerivableWeakeningPolicy base).admissible t ↔
      DerivableTree base t := by
  rfl

/--
Weakening by a base-derivable component preserves the derivable hypersequent
sector.
-/
theorem externalWeakeningMove_baseDerivable_preserves_derivable
    {base : BaseRel} {G H : Hypersequent}
    (hG : DerivableHypersequent base G)
    (hW : ExternalWeakeningMove (baseDerivableWeakeningPolicy base) G H) :
    DerivableHypersequent base H := by
  rcases hW with ⟨t, ht, rfl⟩
  exact external_add_component_preserves_derivableHypersequent hG ht

/--
Every component of a proof-theoretic singleton graft is admissible for
base-managed external weakening.

This is the explicit structural-rule reading: the inserted proof, host proof,
and output proof may be externally juxtaposed with any hypersequent context
only because they already carry derivational provenance over the current base.
-/
theorem proofTheoreticSingletonHypersequentGraftingSupport_externalWeakening_components
    {base : BaseRel} {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    ExternalWeakeningMove (baseDerivableWeakeningPolicy base) C (C + U) ∧
      ExternalWeakeningMove (baseDerivableWeakeningPolicy base) C (C + T) ∧
        ExternalWeakeningMove (baseDerivableWeakeningPolicy base) C (C + V) := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  exact
    ⟨⟨u, hpt.1, rfl⟩,
      ⟨t, hpt.2.1, rfl⟩,
      ⟨v, hpt.2.2.2, rfl⟩⟩

/--
A proof-theoretic hypersequent graft-composition step.

This is the two-component algebra-side proof operation stated at the
hypersequent level: in an external context `C`, a derivable inserted singleton
`U` and a derivable host singleton `T` are composed by proof-tree grafting and
replaced by the grafted singleton `V`.

Unlike ordinary external product, this operation is not mere juxtaposition.
It uses the derivational data in
`ProofTheoreticSingletonHypersequentGraftingSupport base U T V`.
-/
def ProofTheoreticHypersequentGraftCompositionStep
    (base : BaseRel) (G H : Hypersequent) : Prop :=
  ∃ C U T V : Hypersequent,
    ProofTheoreticSingletonHypersequentGraftingSupport base U T V ∧
      G = C + U + T ∧
        H = C + V

/--
The fixed-inserted-component form of proof-theoretic hypersequent graft
composition.

This relation says that the particular hypersequent component `U` is the
inserted proof component consumed by the composition step.  It is useful for
nonmonotonic update theorems, because an update may destroy the derivability
of exactly this inserted proof component.
-/
def FixedInsertedProofTheoreticHypersequentGraftCompositionStep
    (base : BaseRel) (U : Hypersequent) (G H : Hypersequent) : Prop :=
  ∃ C T V : Hypersequent,
    ProofTheoreticSingletonHypersequentGraftingSupport base U T V ∧
      G = C + U + T ∧
        H = C + V

/--
The general proof-theoretic hypersequent graft-composition step is exactly the
existence of some fixed inserted proof component.
-/
theorem proofTheoreticHypersequentGraftCompositionStep_iff_exists_fixed_inserted
    {base : BaseRel} {G H : Hypersequent} :
    ProofTheoreticHypersequentGraftCompositionStep base G H ↔
      ∃ U : Hypersequent,
        FixedInsertedProofTheoreticHypersequentGraftCompositionStep
          base U G H := by
  constructor
  · intro hstep
    rcases hstep with ⟨C, U, T, V, hgraft, hG, hH⟩
    exact ⟨U, C, T, V, hgraft, hG, hH⟩
  · rintro ⟨U, C, T, V, hgraft, hG, hH⟩
    exact ⟨C, U, T, V, hgraft, hG, hH⟩

/--
Every proof-theoretic hypersequent graft-composition step contains genuine
proof-tree data.

This theorem is the formal guard against confusing the sequent shadow with the
derivation.  A step `G --> H` is witnessed by an external context `C`, an
inserted proof tree `u`, a host proof tree `t`, and an output proof tree `v`.
The inserted, host, and output trees are all derivable over the current base,
and `v` is obtained from `u` and `t` by the ambient matching-leaf grafting
support.
-/
theorem proofTheoreticHypersequentGraftCompositionStep_tree_witnesses
    {base : BaseRel} {G H : Hypersequent}
    (hstep : ProofTheoreticHypersequentGraftCompositionStep base G H) :
    ∃ C : Hypersequent, ∃ u t v : PTree,
      G = C + HQ.singleton u + HQ.singleton t ∧
        H = C + HQ.singleton v ∧
          DerivableTree base u ∧
            DerivableTree base t ∧
              AmbientGraftingSupport u t v ∧
                DerivableTree base v := by
  rcases hstep with ⟨C, U, T, V, hgraft, rfl, rfl⟩
  rcases hgraft with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  exact
    ⟨C, u, t, v, rfl, rfl,
      hpt.1, hpt.2.1, hpt.2.2.1, hpt.2.2.2⟩

theorem proofTheoreticHypersequentGraftCompositionStep_of_singleton_support
    {base : BaseRel} {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    ProofTheoreticHypersequentGraftCompositionStep base
      (C + U + T) (C + V) := by
  exact ⟨C, U, T, V, h, rfl, rfl⟩

theorem fixedInsertedProofTheoreticHypersequentGraftCompositionStep_of_singleton_support
    {base : BaseRel} {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V) :
    FixedInsertedProofTheoreticHypersequentGraftCompositionStep base U
      (C + U + T) (C + V) := by
  exact ⟨C, T, V, h, rfl, rfl⟩

/--
Proof-theoretic hypersequent graft composition is stable under genuine
extension of the material base consequence relation.

This is the monotone half of the nonmonotonicity diagnostic.  If every old
base consequence remains available, then a previously licensed composition of
derivable proof components is still licensed.  Arbitrary base update is not
covered by this theorem.
-/
theorem proofTheoreticHypersequentGraftCompositionStep_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {G H : Hypersequent}
    (hstep : ProofTheoreticHypersequentGraftCompositionStep base G H) :
    ProofTheoreticHypersequentGraftCompositionStep base' G H := by
  rcases hstep with ⟨C, U, T, V, hgraft, rfl, rfl⟩
  exact
    ⟨C, U, T, V,
      proofTheoreticSingletonHypersequentGraftingSupport_mono_base
        hbase hgraft,
      rfl, rfl⟩

/--
The fixed-inserted proof-theoretic composition step is stable under genuine
extension of the material base relation.
-/
theorem fixedInsertedProofTheoreticHypersequentGraftCompositionStep_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {U G H : Hypersequent}
    (hstep :
      FixedInsertedProofTheoreticHypersequentGraftCompositionStep
        base U G H) :
    FixedInsertedProofTheoreticHypersequentGraftCompositionStep
      base' U G H := by
  rcases hstep with ⟨C, T, V, hgraft, rfl, rfl⟩
  exact
    ⟨C, T, V,
      proofTheoreticSingletonHypersequentGraftingSupport_mono_base
        hbase hgraft,
      rfl, rfl⟩

/--
Proof-theoretic hypersequent graft composition preserves the closed derivable
sector.

The input closedness supplies the derivability of the surrounding context,
while the singleton graft support supplies the derivability of the grafted
output component.  Thus the composition is an admissible proof operation, not
an arbitrary operation on sequent shadows.
-/
theorem proofTheoreticHypersequentGraftCompositionStep_preserves_derivable
    {base : BaseRel} {G H : Hypersequent}
    (hstep :
      ProofTheoreticHypersequentGraftCompositionStep base G H)
    (hG : DerivableHypersequent base G) :
    DerivableHypersequent base H := by
  rcases hstep with ⟨C, U, T, V, hgraft, rfl, rfl⟩
  have hCU : DerivableHypersequent base (C + U) :=
    derivableHypersequent_left_of_add
      (G := C + U) (H := T) hG
  have hC : DerivableHypersequent base C :=
    derivableHypersequent_left_of_add
      (G := C) (H := U) hCU
  have hV : DerivableHypersequent base V :=
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable
      hgraft).2.2
  exact derivableHypersequent_add hC hV

/--
The fixed-inserted version also preserves the closed derivable sector.
-/
theorem fixedInsertedProofTheoreticHypersequentGraftCompositionStep_preserves_derivable
    {base : BaseRel} {U G H : Hypersequent}
    (hstep :
      FixedInsertedProofTheoreticHypersequentGraftCompositionStep
        base U G H)
    (hG : DerivableHypersequent base G) :
    DerivableHypersequent base H := by
  rcases hstep with ⟨C, T, V, hgraft, rfl, rfl⟩
  exact
    proofTheoreticHypersequentGraftCompositionStep_preserves_derivable
      (⟨C, U, T, V, hgraft, rfl, rfl⟩) hG

/--
A fixed-inserted composition step cannot exist if the inserted component is
not derivable over the current material base.
-/
theorem fixedInsertedProofTheoreticHypersequentGraftCompositionStep_not_of_insert_nonderivable
    {base : BaseRel} {U G H : Hypersequent}
    (hU : ¬ DerivableHypersequent base U) :
    ¬ FixedInsertedProofTheoreticHypersequentGraftCompositionStep
        base U G H := by
  intro hstep
  rcases hstep with ⟨C, T, V, hgraft, _hG, _hH⟩
  exact hU
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable
      hgraft).1

/--
If a nonmonotonic update destroys the inserted proof tree `u`, then no
two-component proof-theoretic hypersequent composition step can use
`HQ.singleton u` as its fixed inserted component over the updated base.
-/
theorem derivableTreeDestroyedByUpdate_blocks_fixed_inserted_hypersequent_graft_composition
    {U : AdmissibleBaseUpdate} {base : BaseRel} {u : PTree}
    (h : DerivableTreeDestroyedByUpdate U base u) :
    ∃ base' : BaseRel,
      U base base' ∧
        DerivableTree base u ∧
          ¬ DerivableTree base' u ∧
            ∀ G H : Hypersequent,
              ¬ FixedInsertedProofTheoreticHypersequentGraftCompositionStep
                  base' (HQ.singleton u) G H := by
  rcases h with ⟨base', hU, hu, hnew⟩
  have hsingleton :
      ¬ DerivableHypersequent base' (HQ.singleton u) := by
    intro hder
    exact hnew (derivableHypersequent_singleton_iff.mp hder)
  exact
    ⟨base', hU, hu, hnew, by
      intro G H
      exact
        fixedInsertedProofTheoreticHypersequentGraftCompositionStep_not_of_insert_nonderivable
          hsingleton⟩

/--
The sequent-level shadow of a proof-theoretic graft composition balances by
the consumed inserted proof component.

The operation replaces `C + U + T` by `C + V`, and grafting preserves the
ordinary conclusion shadow of the host component: `V` has the same conclusion
shadow as `T`.  Therefore the output shadow together with the consumed
inserted-proof shadow recovers the input shadow.

This theorem deliberately does not say that the sequent shadow determines the
graft.  It only records what remains visible after forgetting the proof-tree
structure.
-/
theorem proofTheoreticHypersequentGraftCompositionStep_shadow_balance
    {base : BaseRel} {G H : Hypersequent}
    (hstep :
      ProofTheoreticHypersequentGraftCompositionStep base G H) :
    ∃ U : Hypersequent,
      DerivableHypersequent base U ∧
        HQ.conclusions H + HQ.conclusions U =
          HQ.conclusions G := by
  rcases hstep with ⟨C, U, T, V, hgraft, rfl, rfl⟩
  have hU : DerivableHypersequent base U :=
    (proofTheoreticSingletonHypersequentGraftingSupport_derivable
      hgraft).1
  have hshadow : HQ.conclusions V = HQ.conclusions T :=
    proofTheoreticSingletonHypersequentGraftingSupport_preserves_shadow
      hgraft
  refine ⟨U, hU, ?_⟩
  simp [HQ.conclusions_add, hshadow, add_comm, add_left_comm]

/-! ## Closed-sector behavior of ordinary external structural rules -/

/--
External permutation is harmless for closed derivable hypersequents.

Since the current carrier is a multiset, permutation appears as equality.
-/
theorem external_perm_preserves_derivable
    {base : BaseRel} {G H : Hypersequent}
    (hGH : G = H)
    (hG : DerivableHypersequent base G) :
    DerivableHypersequent base H := by
  subst H
  exact hG

/--
External contraction is harmless for closed derivable hypersequents.

This is only the contraction direction that removes a duplicate component.
-/
theorem external_contraction_preserves_derivable
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hGtt : DerivableHypersequent base
      (G + HQ.singleton t + HQ.singleton t)) :
    DerivableHypersequent base (G + HQ.singleton t) := by
  apply derivableHypersequent_add
  · exact derivableHypersequent_left_of_add
      (derivableHypersequent_left_of_add
        (G := G + HQ.singleton t) (H := HQ.singleton t) hGtt)
  · exact derivableHypersequent_right_of_add
      (derivableHypersequent_left_of_add
        (G := G + HQ.singleton t) (H := HQ.singleton t) hGtt)

/--
The weakening constructor of `ExternalStep` preserves closed derivability under
the base-derivable weakening policy.

This is not free external weakening.  The policy assumption is exactly the
derivability of the added component over the material base.
-/
theorem externalStep_weakening_baseDerivable_preserves_derivable
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hG : DerivableHypersequent base G)
    (ht : (baseDerivableWeakeningPolicy base).admissible t) :
    DerivableHypersequent base (G + HQ.singleton t) := by
  exact external_add_component_preserves_derivableHypersequent hG ht

/--
A base-sensitive graft-controlled weakening policy.

The old `graftControlledWeakeningPolicy u` only asks whether `t` supplies a
matching graft target for `u`.  This strengthened policy also requires both
the probe `u` and the added component `t` to live in the derivable sector over
the same material base.
-/
def baseGraftControlledWeakeningPolicy
    (base : BaseRel) (u : DerivableProofTree base) :
    ExternalWeakeningPolicy where
  admissible t := DerivableTree base t ∧ ∃ v : PTree, InternalGraft u.1 t v

theorem baseGraftControlledWeakeningPolicy_admissible_iff
    {base : BaseRel} (u : DerivableProofTree base) (t : PTree) :
    (baseGraftControlledWeakeningPolicy base u).admissible t ↔
      DerivableTree base t ∧ ∃ v : PTree, InternalGraft u.1 t v := by
  rfl

theorem baseGraftControlledWeakeningPolicy_admissible_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    (u : DerivableProofTree base) {t : PTree}
    (hW : (baseGraftControlledWeakeningPolicy base u).admissible t) :
    (baseGraftControlledWeakeningPolicy base'
        (DerivableProofTree.mapBase hbase u)).admissible t := by
  rw [baseGraftControlledWeakeningPolicy_admissible_iff] at hW ⊢
  exact ⟨derivableTree_mono hbase hW.1, hW.2⟩

theorem baseGraftControlledWeakeningPolicy_not_admissible_of_nonderivable
    {base : BaseRel} (u : DerivableProofTree base) {t : PTree}
    (ht : ¬ DerivableTree base t) :
    ¬ (baseGraftControlledWeakeningPolicy base u).admissible t := by
  intro hW
  exact ht ((baseGraftControlledWeakeningPolicy_admissible_iff u t).mp hW).1

/--
If a base update destroys the derivability of a proof tree, then that tree
cannot be used as a controlled external-weakening component over the updated
base, even if it still matches some graft site syntactically.
-/
theorem derivableTreeDestroyedByUpdate_blocks_controlled_weakening
    {U : AdmissibleBaseUpdate} {base : BaseRel} {t : PTree}
    (h : DerivableTreeDestroyedByUpdate U base t) :
    ∃ base' : BaseRel,
      U base base' ∧
      DerivableTree base t ∧
      ¬ DerivableTree base' t ∧
      ∀ u : DerivableProofTree base',
        ¬ (baseGraftControlledWeakeningPolicy base' u).admissible t := by
  rcases h with ⟨base', hU, ht, hnew⟩
  refine ⟨base', hU, ht, hnew, ?_⟩
  intro u
  exact baseGraftControlledWeakeningPolicy_not_admissible_of_nonderivable
    u hnew

/--
Base-sensitive graft-controlled weakening preserves derivability and creates
an actual derivable contextual graft step.
-/
theorem baseGraftControlledWeakening_supplies_derivable_contextual_graft
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (u : DerivableProofTree base)
    (hG : DerivableHypersequent base G)
    (hW : (baseGraftControlledWeakeningPolicy base u).admissible t) :
    ∃ H : Hypersequent,
      DerivableHypersequent base (G + HQ.singleton t) ∧
      ContextualInternalGraft u.1 (G + HQ.singleton t) H ∧
      DerivableHypersequent base H := by
  rcases hW with ⟨ht, v, hg⟩
  let H := G + HQ.singleton v
  have hGt : DerivableHypersequent base (G + HQ.singleton t) :=
    external_add_component_preserves_derivableHypersequent hG ht
  have hctx : ContextualInternalGraft u.1 (G + HQ.singleton t) H :=
    contextualInternalGraft_of_added_component G hg
  exact ⟨H, hGt, hctx,
    contextualInternalGraft_preserves_derivableHypersequent u.2 hGt hctx⟩

/--
Controlled weakening/grafting is stable under monotone extension of the
primitive material base.

This is the base-sensitive version of the intended proof-theoretic picture:
when the base relation is extended in the monotone sense, an already
admissible added proof component remains admissible, and the same matching
graft yields a derivable contextual graft over the larger base.
-/
theorem baseGraftControlledWeakening_supplies_derivable_contextual_graft_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {G : Hypersequent} {t : PTree}
    (u : DerivableProofTree base)
    (hG : DerivableHypersequent base G)
    (hW : (baseGraftControlledWeakeningPolicy base u).admissible t) :
    ∃ H : Hypersequent,
      DerivableHypersequent base' (G + HQ.singleton t) ∧
      ContextualInternalGraft u.1 (G + HQ.singleton t) H ∧
      DerivableHypersequent base' H := by
  let u' : DerivableProofTree base' := DerivableProofTree.mapBase hbase u
  have hG' : DerivableHypersequent base' G :=
    derivableHypersequent_mono hbase hG
  have hW' :
      (baseGraftControlledWeakeningPolicy base' u').admissible t :=
    baseGraftControlledWeakeningPolicy_admissible_mono_base
      hbase u hW
  rcases
    baseGraftControlledWeakening_supplies_derivable_contextual_graft
      u' hG' hW' with
  ⟨H, hGt, hctx, hH⟩
  exact ⟨H, hGt, hctx, hH⟩

/-! ## Open derivations and boundary leaves -/

/--
An open NMMS derivation is an ordinary NMMS derivation with additional
boundary leaves.

The boundary set `B` is a multiset of sequents that may be used as open
interfaces.  A boundary leaf is not a base axiom and should not be read as a
closed proof.  This is the first formal distinction needed for the
hypersequent splitting story: cuts of a closed proof may produce a remainder
tree with interface leaves.
-/
inductive OpenNMMS (base : BaseRel) (B : Multiset MultiSequent) :
    MultiSequent → Type u
| boundary
    {s : MultiSequent}
    (h : s ∈ B) :
    OpenNMMS base B s

| baseAx
    {Γ Θ : Multiset MyProp}
    (h : base Γ Θ) :
    OpenNMMS base B (Γ ∣∼ Θ)

| imp_l
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : OpenNMMS base B (Γ ∣∼ A ::ₘ Θ))
    (d₂ : OpenNMMS base B (B' ::ₘ Γ ∣∼ Θ)) :
    OpenNMMS base B ((A ⇒ B') ::ₘ Γ ∣∼ Θ)

| imp_r
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d : OpenNMMS base B (A ::ₘ Γ ∣∼ B' ::ₘ Θ)) :
    OpenNMMS base B (Γ ∣∼ (A ⇒ B') ::ₘ Θ)

| conj_l
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d : OpenNMMS base B (A ::ₘ B' ::ₘ Γ ∣∼ Θ)) :
    OpenNMMS base B ((A & B') ::ₘ Γ ∣∼ Θ)

| conj_r
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : OpenNMMS base B (Γ ∣∼ A ::ₘ Θ))
    (d₂ : OpenNMMS base B (Γ ∣∼ B' ::ₘ Θ)) :
    OpenNMMS base B (Γ ∣∼ (A & B') ::ₘ Θ)

| disj_l
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d₁ : OpenNMMS base B (A ::ₘ Γ ∣∼ Θ))
    (d₂ : OpenNMMS base B (B' ::ₘ Γ ∣∼ Θ)) :
    OpenNMMS base B ((A ∨ B') ::ₘ Γ ∣∼ Θ)

| disj_r
    {A B' : MyProp} {Γ Θ : Multiset MyProp}
    (d : OpenNMMS base B (Γ ∣∼ A ::ₘ B' ::ₘ Θ)) :
    OpenNMMS base B (Γ ∣∼ (A ∨ B') ::ₘ Θ)

| neg_l
    {A : MyProp} {Γ Θ : Multiset MyProp}
    (d : OpenNMMS base B (Γ ∣∼ A ::ₘ Θ)) :
    OpenNMMS base B ((¬A) ::ₘ Γ ∣∼ Θ)

| neg_r
    {A : MyProp} {Γ Θ : Multiset MyProp}
    (d : OpenNMMS base B (A ::ₘ Γ ∣∼ Θ)) :
    OpenNMMS base B (Γ ∣∼ (¬A) ::ₘ Θ)

namespace OpenNMMS

/-- Forget an open derivation to its labelled proof tree. -/
def toTree {base : BaseRel} {B : Multiset MultiSequent}
    {s : MultiSequent} (d : OpenNMMS base B s) : PTree :=
  match d with
  | @OpenNMMS.boundary _ _ s h => PTree.leaf s
  | @OpenNMMS.baseAx _ _ Γ Θ _ => PTree.leaf (Γ ∣∼ Θ)
  | @OpenNMMS.imp_l _ _ A B' Γ Θ d₁ d₂ =>
      PTree.node RuleTag.imp_l (((A ⇒ B') ::ₘ Γ) ∣∼ Θ) [toTree d₁, toTree d₂]
  | @OpenNMMS.imp_r _ _ A B' Γ Θ d =>
      PTree.node RuleTag.imp_r (Γ ∣∼ ((A ⇒ B') ::ₘ Θ)) [toTree d]
  | @OpenNMMS.conj_l _ _ A B' Γ Θ d =>
      PTree.node RuleTag.conj_l (((A & B') ::ₘ Γ) ∣∼ Θ) [toTree d]
  | @OpenNMMS.conj_r _ _ A B' Γ Θ d₁ d₂ =>
      PTree.node RuleTag.conj_r (Γ ∣∼ ((A & B') ::ₘ Θ)) [toTree d₁, toTree d₂]
  | @OpenNMMS.disj_l _ _ A B' Γ Θ d₁ d₂ =>
      PTree.node RuleTag.disj_l (((A ∨ B') ::ₘ Γ) ∣∼ Θ) [toTree d₁, toTree d₂]
  | @OpenNMMS.disj_r _ _ A B' Γ Θ d =>
      PTree.node RuleTag.disj_r (Γ ∣∼ ((A ∨ B') ::ₘ Θ)) [toTree d]
  | @OpenNMMS.neg_l _ _ A Γ Θ d =>
      PTree.node RuleTag.neg_l (((¬A) ::ₘ Γ) ∣∼ Θ) [toTree d]
  | @OpenNMMS.neg_r _ _ A Γ Θ d =>
      PTree.node RuleTag.neg_r (Γ ∣∼ ((¬A) ::ₘ Θ)) [toTree d]

@[simp]
theorem toTree_boundary
    {base : BaseRel} {B : Multiset MultiSequent} {s : MultiSequent}
    (h : s ∈ B) :
    toTree (OpenNMMS.boundary (base := base) (B := B) h) = PTree.leaf s :=
  rfl

/-- Closed derivations embed into open derivations with any boundary set. -/
def ofNMMS {base : BaseRel} {B : Multiset MultiSequent}
    {s : MultiSequent} : NMMS base s → OpenNMMS base B s
| NMMS.baseAx h => OpenNMMS.baseAx h
| NMMS.imp_l d₁ d₂ => OpenNMMS.imp_l (ofNMMS d₁) (ofNMMS d₂)
| NMMS.imp_r d => OpenNMMS.imp_r (ofNMMS d)
| NMMS.conj_l d => OpenNMMS.conj_l (ofNMMS d)
| NMMS.conj_r d₁ d₂ => OpenNMMS.conj_r (ofNMMS d₁) (ofNMMS d₂)
| NMMS.disj_l d₁ d₂ => OpenNMMS.disj_l (ofNMMS d₁) (ofNMMS d₂)
| NMMS.disj_r d => OpenNMMS.disj_r (ofNMMS d)
| NMMS.neg_l d => OpenNMMS.neg_l (ofNMMS d)
| NMMS.neg_r d => OpenNMMS.neg_r (ofNMMS d)

@[simp]
theorem toTree_ofNMMS
    {base : BaseRel} {B : Multiset MultiSequent}
    {s : MultiSequent} (d : NMMS base s) :
    OpenNMMS.toTree (OpenNMMS.ofNMMS (B := B) d) = NMMS.toTree d := by
  induction d <;> simp [OpenNMMS.ofNMMS, OpenNMMS.toTree, NMMS.toTree, *]

/--
A realization of open boundary sequents by closed NMMS derivations.

Proof-theoretically, this is the substitution data needed to close an open
remainder produced by a coproduct split.
-/
def BoundaryRealization
    (base : BaseRel) (B : Multiset MultiSequent) : Type u :=
  ∀ s : MultiSequent, s ∈ B → NMMS base s

/--
Close an open derivation by replacing each boundary leaf with the closed
derivation supplied by a boundary realization.
-/
def close
    {base : BaseRel} {B : Multiset MultiSequent}
    (ρ : BoundaryRealization base B) :
    {s : MultiSequent} → OpenNMMS base B s → NMMS base s
| _, boundary h => ρ _ h
| _, baseAx h => NMMS.baseAx h
| _, imp_l d₁ d₂ => NMMS.imp_l (close ρ d₁) (close ρ d₂)
| _, imp_r d => NMMS.imp_r (close ρ d)
| _, conj_l d => NMMS.conj_l (close ρ d)
| _, conj_r d₁ d₂ => NMMS.conj_r (close ρ d₁) (close ρ d₂)
| _, disj_l d₁ d₂ => NMMS.disj_l (close ρ d₁) (close ρ d₂)
| _, disj_r d => NMMS.disj_r (close ρ d)
| _, neg_l d => NMMS.neg_l (close ρ d)
| _, neg_r d => NMMS.neg_r (close ρ d)

/--
The closed proof tree obtained by realizing all boundary leaves in an open
derivation.
-/
def closeTree
    {base : BaseRel} {B : Multiset MultiSequent}
    (ρ : BoundaryRealization base B)
    {s : MultiSequent} (d : OpenNMMS base B s) : PTree :=
  NMMS.toTree (close ρ d)

theorem closeTree_derivable
    {base : BaseRel} {B : Multiset MultiSequent}
    (ρ : BoundaryRealization base B)
    {s : MultiSequent} (d : OpenNMMS base B s) :
    DerivableTree base (closeTree ρ d) := by
  exact ⟨s, close ρ d, rfl⟩

/-- Boundary inclusion lets us widen the set of open interfaces. -/
def mapBoundary
    {base : BaseRel} {B B' : Multiset MultiSequent}
    (hB : ∀ s, s ∈ B → s ∈ B') :
    {s : MultiSequent} → OpenNMMS base B s → OpenNMMS base B' s
| _, boundary h => boundary (hB _ h)
| _, baseAx h => baseAx h
| _, imp_l d₁ d₂ => imp_l (mapBoundary hB d₁) (mapBoundary hB d₂)
| _, imp_r d => imp_r (mapBoundary hB d)
| _, conj_l d => conj_l (mapBoundary hB d)
| _, conj_r d₁ d₂ => conj_r (mapBoundary hB d₁) (mapBoundary hB d₂)
| _, disj_l d₁ d₂ => disj_l (mapBoundary hB d₁) (mapBoundary hB d₂)
| _, disj_r d => disj_r (mapBoundary hB d)
| _, neg_l d => neg_l (mapBoundary hB d)
| _, neg_r d => neg_r (mapBoundary hB d)

@[simp]
theorem toTree_mapBoundary
    {base : BaseRel} {B B' : Multiset MultiSequent}
    (hB : ∀ s, s ∈ B → s ∈ B')
    {s : MultiSequent} (d : OpenNMMS base B s) :
    OpenNMMS.toTree (OpenNMMS.mapBoundary hB d) = OpenNMMS.toTree d := by
  induction d <;> simp [OpenNMMS.mapBoundary, OpenNMMS.toTree, *]

/-- Lift an open derivation across an extension of the material base. -/
def mapBase
    {base base' : BaseRel} {B : Multiset MultiSequent}
    (hbase : BaseRelExtends base base') :
    {s : MultiSequent} → OpenNMMS base B s → OpenNMMS base' B s
| _, boundary h => boundary h
| _, baseAx h => baseAx (hbase h)
| _, imp_l d₁ d₂ => imp_l (mapBase hbase d₁) (mapBase hbase d₂)
| _, imp_r d => imp_r (mapBase hbase d)
| _, conj_l d => conj_l (mapBase hbase d)
| _, conj_r d₁ d₂ => conj_r (mapBase hbase d₁) (mapBase hbase d₂)
| _, disj_l d₁ d₂ => disj_l (mapBase hbase d₁) (mapBase hbase d₂)
| _, disj_r d => disj_r (mapBase hbase d)
| _, neg_l d => neg_l (mapBase hbase d)
| _, neg_r d => neg_r (mapBase hbase d)

@[simp]
theorem toTree_mapBase
    {base base' : BaseRel} {B : Multiset MultiSequent}
    (hbase : BaseRelExtends base base')
    {s : MultiSequent} (d : OpenNMMS base B s) :
    OpenNMMS.toTree (OpenNMMS.mapBase hbase d) = OpenNMMS.toTree d := by
  induction d <;> simp [OpenNMMS.mapBase, OpenNMMS.toTree, *]

/--
Every terminal leaf of an open derivation is either a material/base axiom or a
declared boundary/interface sequent.
-/
theorem toTree_leafSequents_base_or_boundary
    {base : BaseRel} {B : Multiset MultiSequent} {s : MultiSequent}
    (d : OpenNMMS base B s) :
    PTree.LeafSequentsSatisfy
      (OpenTerminalSequent base B) (OpenNMMS.toTree d) := by
  induction d <;>
    simp [OpenNMMS.toTree, PTree.LeafSequentsSatisfy,
      OpenTerminalSequent, MaterialTerminalSequent, MaterialEntails, *]

/--
Cutting out one occurrence of a closed derivation yields an open derivation
whose new boundary is the conclusion sequent of the extracted subderivation.

This is the constructor-preserving form of the proof-context theorem: the
surrounding rule applications remain the same, and only the selected
subderivation is replaced by a boundary leaf.
-/
theorem remainderGo_singleton_of_subtreeAt_toTree
    {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) {a : Address} {u : PTree}
    (hsub : PTree.subtreeAt (NMMS.toTree d) a = some u) :
    ∃ dopen : OpenNMMS base ({u.conclusion} : Multiset MultiSequent) s,
      OpenNMMS.toTree dopen =
        PTree.remainderGo [a] [] (NMMS.toTree d) := by
  induction d generalizing a u with
  | baseAx h =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | imp_l d₁ d₂ ih₁ ih₂ =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d₁) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih₁ hchild with ⟨dopen₁, hopen₁⟩
              refine ⟨OpenNMMS.imp_l dopen₁ (OpenNMMS.ofNMMS d₂), ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                PTree.remainderGo, PTree.restrictCut, hopen₁]
          | succ i =>
              cases i with
              | zero =>
                  have hchild :
                      PTree.subtreeAt (NMMS.toTree d₂) rest = some u := by
                    simpa [NMMS.toTree, PTree.subtreeAt] using hsub
                  rcases ih₂ hchild with ⟨dopen₂, hopen₂⟩
                  refine ⟨OpenNMMS.imp_l (OpenNMMS.ofNMMS d₁) dopen₂, ?_⟩
                  simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                    PTree.remainderGo, PTree.restrictCut, hopen₂]
              | succ j =>
                  simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | imp_r d ih =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih hchild with ⟨dopen, hopen⟩
              refine ⟨OpenNMMS.imp_r dopen, ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree,
                PTree.remainderGo, PTree.restrictCut, hopen]
          | succ i =>
              simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | conj_l d ih =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih hchild with ⟨dopen, hopen⟩
              refine ⟨OpenNMMS.conj_l dopen, ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree,
                PTree.remainderGo, PTree.restrictCut, hopen]
          | succ i =>
              simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | conj_r d₁ d₂ ih₁ ih₂ =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d₁) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih₁ hchild with ⟨dopen₁, hopen₁⟩
              refine ⟨OpenNMMS.conj_r dopen₁ (OpenNMMS.ofNMMS d₂), ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                PTree.remainderGo, PTree.restrictCut, hopen₁]
          | succ i =>
              cases i with
              | zero =>
                  have hchild :
                      PTree.subtreeAt (NMMS.toTree d₂) rest = some u := by
                    simpa [NMMS.toTree, PTree.subtreeAt] using hsub
                  rcases ih₂ hchild with ⟨dopen₂, hopen₂⟩
                  refine ⟨OpenNMMS.conj_r (OpenNMMS.ofNMMS d₁) dopen₂, ?_⟩
                  simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                    PTree.remainderGo, PTree.restrictCut, hopen₂]
              | succ j =>
                  simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | disj_l d₁ d₂ ih₁ ih₂ =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d₁) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih₁ hchild with ⟨dopen₁, hopen₁⟩
              refine ⟨OpenNMMS.disj_l dopen₁ (OpenNMMS.ofNMMS d₂), ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                PTree.remainderGo, PTree.restrictCut, hopen₁]
          | succ i =>
              cases i with
              | zero =>
                  have hchild :
                      PTree.subtreeAt (NMMS.toTree d₂) rest = some u := by
                    simpa [NMMS.toTree, PTree.subtreeAt] using hsub
                  rcases ih₂ hchild with ⟨dopen₂, hopen₂⟩
                  refine ⟨OpenNMMS.disj_l (OpenNMMS.ofNMMS d₁) dopen₂, ?_⟩
                  simp [NMMS.toTree, OpenNMMS.toTree, OpenNMMS.toTree_ofNMMS,
                    PTree.remainderGo, PTree.restrictCut, hopen₂]
              | succ j =>
                  simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | disj_r d ih =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih hchild with ⟨dopen, hopen⟩
              refine ⟨OpenNMMS.disj_r dopen, ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree,
                PTree.remainderGo, PTree.restrictCut, hopen]
          | succ i =>
              simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | neg_l d ih =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih hchild with ⟨dopen, hopen⟩
              refine ⟨OpenNMMS.neg_l dopen, ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree,
                PTree.remainderGo, PTree.restrictCut, hopen]
          | succ i =>
              simp [NMMS.toTree, PTree.subtreeAt] at hsub
  | neg_r d ih =>
      cases a with
      | nil =>
          simp [NMMS.toTree, PTree.subtreeAt] at hsub
          cases hsub
          refine ⟨OpenNMMS.boundary ?_, ?_⟩
          · simp [PTree.conclusion]
          · simp [NMMS.toTree, OpenNMMS.toTree, PTree.remainderGo]
      | cons i rest =>
          cases i with
          | zero =>
              have hchild :
                  PTree.subtreeAt (NMMS.toTree d) rest = some u := by
                simpa [NMMS.toTree, PTree.subtreeAt] using hsub
              rcases ih hchild with ⟨dopen, hopen⟩
              refine ⟨OpenNMMS.neg_r dopen, ?_⟩
              simp [NMMS.toTree, OpenNMMS.toTree,
                PTree.remainderGo, PTree.restrictCut, hopen]
          | succ i =>
              simp [NMMS.toTree, PTree.subtreeAt] at hsub

end OpenNMMS

/--
An open proof tree over boundary set `B`.

This is the first approximation to a cut remainder: it is a tree that may be
derived using explicit boundary/interface leaves from `B`.
-/
def OpenDerivableTree
    (base : BaseRel) (B : Multiset MultiSequent) (t : PTree) : Prop :=
  ∃ s : MultiSequent, ∃ d : OpenNMMS base B s, OpenNMMS.toTree d = t

theorem openDerivableTree_singleton_remainder_of_subtreeAt
    {base : BaseRel} {t u : PTree} {a : Address}
    (ht : DerivableTree base t)
    (hsub : PTree.subtreeAt t a = some u) :
    OpenDerivableTree base ({u.conclusion} : Multiset MultiSequent)
      (PTree.remainderGo [a] [] t) := by
  rcases ht with ⟨s, d, rfl⟩
  rcases OpenNMMS.remainderGo_singleton_of_subtreeAt_toTree d hsub with
    ⟨dopen, hdopen⟩
  exact ⟨s, dopen, hdopen⟩

theorem openDerivableTree_leafSequents_base_or_boundary
    {base : BaseRel} {B : Multiset MultiSequent} {t : PTree}
    (ht : OpenDerivableTree base B t) :
    PTree.LeafSequentsSatisfy
      (OpenTerminalSequent base B) t := by
  rcases ht with ⟨s, d, rfl⟩
  exact OpenNMMS.toTree_leafSequents_base_or_boundary d

theorem openDerivableTree_of_derivableTree
    {base : BaseRel} {B : Multiset MultiSequent} {t : PTree}
    (ht : DerivableTree base t) :
    OpenDerivableTree base B t := by
  rcases ht with ⟨s, d, rfl⟩
  exact ⟨s, OpenNMMS.ofNMMS (B := B) d, OpenNMMS.toTree_ofNMMS d⟩

theorem openDerivableTree_boundary
    {base : BaseRel} {B : Multiset MultiSequent} {s : MultiSequent}
    (hs : s ∈ B) :
    OpenDerivableTree base B (PTree.leaf s) := by
  exact ⟨s, OpenNMMS.boundary hs, rfl⟩

theorem openDerivableTree_mono_boundary
    {base : BaseRel} {B B' : Multiset MultiSequent} {t : PTree}
    (hB : ∀ s, s ∈ B → s ∈ B')
    (ht : OpenDerivableTree base B t) :
    OpenDerivableTree base B' t := by
  rcases ht with ⟨s, d, rfl⟩
  exact ⟨s, OpenNMMS.mapBoundary hB d, OpenNMMS.toTree_mapBoundary hB d⟩

theorem openDerivableTree_mono_base
    {base base' : BaseRel} (hbase : BaseRelExtends base base')
    {B : Multiset MultiSequent} {t : PTree}
    (ht : OpenDerivableTree base B t) :
    OpenDerivableTree base' B t := by
  rcases ht with ⟨s, d, rfl⟩
  exact ⟨s, OpenNMMS.mapBase hbase d, OpenNMMS.toTree_mapBase hbase d⟩

/--
The closed tree obtained by realizing the boundaries of a particular open tree.

The source tree records the open proof context; the target tree records the
closed proof obtained after replacing boundary leaves by actual derivations.
-/
def FilledByBoundaryRealization
    (base : BaseRel) (B : Multiset MultiSequent)
    (openTree filledTree : PTree) : Prop :=
  ∃ s : MultiSequent,
    ∃ d : OpenNMMS base B s,
      ∃ ρ : OpenNMMS.BoundaryRealization base B,
        OpenNMMS.toTree d = openTree ∧
          OpenNMMS.closeTree ρ d = filledTree

/--
Fixed-realization version of `FilledByBoundaryRealization`.

This keeps track of which boundary-realization function was used.  That is
important for cut/graft duality: canonical reconstruction should use the
proofs detached by the coproduct split, not arbitrary proofs of the same
boundary sequents.
-/
def FilledByBoundaryRealizationWith
    {base : BaseRel} {B : Multiset MultiSequent}
    (ρ : OpenNMMS.BoundaryRealization base B)
    (openTree filledTree : PTree) : Prop :=
  ∃ s : MultiSequent,
    ∃ d : OpenNMMS base B s,
      OpenNMMS.toTree d = openTree ∧
        OpenNMMS.closeTree ρ d = filledTree

theorem filledByBoundaryRealization_of_with
    {base : BaseRel} {B : Multiset MultiSequent}
    {ρ : OpenNMMS.BoundaryRealization base B}
    {openTree filledTree : PTree}
    (hfill : FilledByBoundaryRealizationWith ρ openTree filledTree) :
    FilledByBoundaryRealization base B openTree filledTree := by
  rcases hfill with ⟨s, d, hopen, hclosed⟩
  exact ⟨s, d, ρ, hopen, hclosed⟩

theorem filledByBoundaryRealization_derivable
    {base : BaseRel} {B : Multiset MultiSequent}
    {openTree filledTree : PTree}
    (hfill : FilledByBoundaryRealization base B openTree filledTree) :
    DerivableTree base filledTree := by
  rcases hfill with ⟨s, d, ρ, _hopen, hclosed⟩
  exact ⟨s, OpenNMMS.close ρ d, by
    simpa [OpenNMMS.closeTree] using hclosed⟩

theorem filledByBoundaryRealizationWith_derivable
    {base : BaseRel} {B : Multiset MultiSequent}
    {ρ : OpenNMMS.BoundaryRealization base B}
    {openTree filledTree : PTree}
    (hfill : FilledByBoundaryRealizationWith ρ openTree filledTree) :
    DerivableTree base filledTree :=
  filledByBoundaryRealization_derivable
    (filledByBoundaryRealization_of_with hfill)

/--
There is a closed derivation whose proof tree is exactly `t`, indexed by the
tree's own conclusion sequent.
-/
def ClosedProofAtConclusion
    (base : BaseRel) (t : PTree) : Prop :=
  ∃ d : NMMS base t.conclusion, NMMS.toTree d = t

theorem closedProofAtConclusion_of_derivableTree
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ClosedProofAtConclusion base t := by
  rcases ht with ⟨s, d, hd⟩
  have hs : s = t.conclusion := by
    rw [← toTree_conclusion d, hd]
  subst s
  exact ⟨d, hd⟩

/--
A specific closed proof realizes the singleton boundary containing its own
conclusion.
-/
def singletonBoundaryRealization_of_closedProof
    {base : BaseRel} {t : PTree}
    (d : NMMS base t.conclusion) :
    OpenNMMS.BoundaryRealization base
      ({t.conclusion} : Multiset MultiSequent) := by
  intro s hs
  have hs' : s = t.conclusion := by
    simpa using hs
  subst s
  exact d

/--
The root open boundary leaf closes back to the original proof tree when its
singleton boundary is realized by that proof.
-/
theorem root_boundary_filledByBoundaryRealization
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    FilledByBoundaryRealization base
      ({t.conclusion} : Multiset MultiSequent)
      (PTree.leaf t.conclusion) t := by
  rcases closedProofAtConclusion_of_derivableTree ht with ⟨d, hd⟩
  let ρ := singletonBoundaryRealization_of_closedProof d
  refine ⟨t.conclusion, OpenNMMS.boundary (by simp), ρ, rfl, ?_⟩
  exact hd

/--
A boundary set is closed-realizable when each boundary sequent has an NMMS
derivation over the same material base.

This is the sequent-level shadow of a derivable detached hypersequent.
-/
def BoundarySequentsDerivable
    (base : BaseRel) (B : Multiset MultiSequent) : Prop :=
  ∀ s : MultiSequent, s ∈ B → DerivableSequent base s

/--
If all boundary sequents are derivable, then any open derivable tree over that
boundary has some closed realization.

This is the general proof-theoretic substitution principle behind the
cut/graft round-trip target.  It does not yet say the realization reconstructs
the original tree; it says the open remainder can be closed by genuine proofs
whenever its boundary is genuinely derivable.
-/
theorem openDerivableTree_has_closed_boundary_realization
    {base : BaseRel} {B : Multiset MultiSequent} {openTree : PTree}
    (hB : BoundarySequentsDerivable base B)
    (hopen : OpenDerivableTree base B openTree) :
    ∃ filledTree : PTree,
      FilledByBoundaryRealization base B openTree filledTree ∧
        DerivableTree base filledTree := by
  classical
  rcases hopen with ⟨s, d, hd⟩
  let ρ : OpenNMMS.BoundaryRealization base B :=
    fun s hs => Classical.choice (hB s hs)
  refine ⟨OpenNMMS.closeTree ρ d, ?_, OpenNMMS.closeTree_derivable ρ d⟩
  exact ⟨s, d, ρ, hd, rfl⟩

/--
An open proof-labelled hypersequent over a boundary set `B`.

Every component is either a closed derivation, or a derivation relative to the
explicit interface sequents in `B`.
-/
def OpenDerivableHypersequent
    (base : BaseRel) (B : Multiset MultiSequent) (G : Hypersequent) : Prop :=
  ∀ t : PTree, t ∈ G → OpenDerivableTree base B t

theorem openDerivableHypersequent_zero
    (base : BaseRel) (B : Multiset MultiSequent) :
    OpenDerivableHypersequent base B (0 : Hypersequent) := by
  intro t ht
  simp at ht

theorem openDerivableHypersequent_singleton
    {base : BaseRel} {B : Multiset MultiSequent} {t : PTree}
    (ht : OpenDerivableTree base B t) :
    OpenDerivableHypersequent base B (HQ.singleton t) := by
  intro u hu
  simp [HQ.singleton] at hu
  subst u
  exact ht

theorem openDerivableHypersequent_add
    {base : BaseRel} {B : Multiset MultiSequent} {G H : Hypersequent}
    (hG : OpenDerivableHypersequent base B G)
    (hH : OpenDerivableHypersequent base B H) :
    OpenDerivableHypersequent base B (G + H) := by
  intro t ht
  rw [Multiset.mem_add] at ht
  rcases ht with ht | ht
  · exact hG t ht
  · exact hH t ht

theorem openDerivableHypersequent_of_derivableHypersequent
    {base : BaseRel} {B : Multiset MultiSequent} {G : Hypersequent}
    (hG : DerivableHypersequent base G) :
    OpenDerivableHypersequent base B G := by
  intro t ht
  exact openDerivableTree_of_derivableTree (hG t ht)

theorem openDerivableHypersequent_boundarySingleton
    {base : BaseRel} {B : Multiset MultiSequent} {s : MultiSequent}
    (hs : s ∈ B) :
    OpenDerivableHypersequent base B (HQ.singleton (PTree.leaf s)) := by
  exact openDerivableHypersequent_singleton (openDerivableTree_boundary hs)

theorem openDerivableHypersequent_mono_boundary
    {base : BaseRel} {B B' : Multiset MultiSequent} {G : Hypersequent}
    (hB : ∀ s, s ∈ B → s ∈ B')
    (hG : OpenDerivableHypersequent base B G) :
    OpenDerivableHypersequent base B' G := by
  intro t ht
  exact openDerivableTree_mono_boundary hB (hG t ht)

theorem openDerivableHypersequent_mono_base
    {base base' : BaseRel} (hbase : BaseRelExtends base base')
    {B : Multiset MultiSequent} {G : Hypersequent}
    (hG : OpenDerivableHypersequent base B G) :
    OpenDerivableHypersequent base' B G := by
  intro t ht
  exact openDerivableTree_mono_base hbase (hG t ht)

/-! ## Cut detaches genuine subproofs -/

/--
Every component pruned by an admissible cut of a closed derivable tree is a
closed derivable proof tree.

This is the first general proof-theoretic interpretation of splitting:
detached components are genuine subderivations.  The subtle part of splitting
is therefore not the detached forest, but the remainder, which may be open.
-/
theorem derivableForest_pruned_of_derivableTree
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t)
    (cut : PTree.IsAdmissibleCut t) :
    DerivableForest base (PTree.pruned t cut) := by
  rcases ht with ⟨s, d, rfl⟩
  intro u hu
  unfold PTree.pruned at hu
  rcases List.mem_filterMap.1 hu with ⟨addr, _haddr, hsub⟩
  rcases subtreeAt_toTree_is_toTree d addr u hsub with ⟨s', d', hu_eq⟩
  exact ⟨s', d', hu_eq.symm⟩

/--
The detached hypersequent of an admissible cut of a closed proof tree is a
closed derivable hypersequent.
-/
theorem derivableHypersequent_pruned_of_derivableTree
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t)
    (cut : PTree.IsAdmissibleCut t) :
    DerivableHypersequent base (HQ.ofForest (PTree.pruned t cut)) :=
  derivableHypersequent_ofForest
    (derivableForest_pruned_of_derivableTree ht cut)

/--
For an explicit split of a closed proof tree, the detached side is a closed
derivable hypersequent.
-/
theorem derivableHypersequent_detached_of_splitsTo
    {base : BaseRel} {t : PTree} {Γ : Hypersequent} {r : PTree}
    (ht : DerivableTree base t)
    (hs : SplitsTo t Γ r) :
    DerivableHypersequent base Γ := by
  rcases hs with ⟨cut, hΓ, _hr⟩
  rw [← hΓ]
  exact derivableHypersequent_pruned_of_derivableTree ht cut

/--
The boundary sequents exposed by a detached hypersequent.

For a split term `(Γ, r)`, the intended boundary for the open remainder `r` is
the sequent-level shadow of the detached forest `Γ`.
-/
def SplitBoundary (Γ : Hypersequent) : Multiset MultiSequent :=
  HQ.conclusions Γ

/--
A sequent-indexed boundary realization is supported by a detached
hypersequent when every boundary proof it supplies is one of the detached proof
trees with the matching conclusion.

This deliberately records a limitation: because `SplitBoundary Γ` remembers
only conclusion sequents, this notion is still sequent-indexed.  It is strong
enough to say the realization comes from the detached side, but not yet a full
occurrence-sensitive matching between individual boundary leaves and
individual detached components when equal sequents occur more than once.
-/
def BoundaryRealizationSupportedByDetached
    (base : BaseRel) (Γ : Hypersequent)
    (_ρ : OpenNMMS.BoundaryRealization base (SplitBoundary Γ)) : Prop :=
  ∀ s : MultiSequent, ∀ _hs : s ∈ SplitBoundary Γ,
    ∃ u : PTree,
      u ∈ Γ ∧ u.conclusion = s ∧ ClosedProofAtConclusion base u

/--
A derivable detached hypersequent realizes its boundary sequents.

For every sequent appearing in the conclusion shadow of `Γ`, there is an
actual closed NMMS derivation of that sequent, supplied by some proof-tree
component of `Γ`.
-/
theorem boundarySequentsDerivable_of_derivableHypersequent
    {base : BaseRel} {Γ : Hypersequent}
    (hΓ : DerivableHypersequent base Γ) :
    BoundarySequentsDerivable base (SplitBoundary Γ) := by
  intro s hs
  simp [SplitBoundary, HQ.conclusions] at hs ⊢
  rcases hs with ⟨t, htΓ, hts⟩
  have ht : DerivableTree base t := hΓ t htΓ
  rcases closedProofAtConclusion_of_derivableTree ht with ⟨d, _hd⟩
  subst s
  exact derivableSequent_of_derivation d

/--
A derivable detached hypersequent supplies a boundary realization supported by
its own proof-tree components.

This is the bridge from the coproduct's detached forest to the grafting /
substitution side.
-/
theorem supportedBoundaryRealization_exists_of_derivableHypersequent
    {base : BaseRel} {Γ : Hypersequent}
    (hΓ : DerivableHypersequent base Γ) :
    ∃ ρ : OpenNMMS.BoundaryRealization base (SplitBoundary Γ),
      BoundaryRealizationSupportedByDetached base Γ ρ := by
  classical
  let component :
      ∀ s : MultiSequent, s ∈ SplitBoundary Γ →
        { u : PTree // u ∈ Γ ∧ u.conclusion = s } := by
    intro s hs
    have h : ∃ u : PTree, u ∈ Γ ∧ u.conclusion = s := by
      simpa [SplitBoundary, HQ.conclusions] using hs
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let ρ : OpenNMMS.BoundaryRealization base (SplitBoundary Γ) := by
    intro s hs
    exact Classical.choice
      (boundarySequentsDerivable_of_derivableHypersequent hΓ s hs)
  refine ⟨ρ, ?_⟩
  intro s hs
  refine ⟨(component s hs).1, (component s hs).2.1,
    (component s hs).2.2, ?_⟩
  exact closedProofAtConclusion_of_derivableTree
    (hΓ (component s hs).1 (component s hs).2.1)

/--
The proof-theoretic target for a split of a closed proof tree.

The detached side should be closed derivable, while the remainder should be
open derivable over the boundary exposed by the detached side.
-/
def SplitProofTheoreticShape
    (base : BaseRel) (Γ : Hypersequent) (r : PTree) : Prop :=
  DerivableHypersequent base Γ ∧
    OpenDerivableTree base (SplitBoundary Γ) r

theorem splitProofTheoreticShape_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {Γ : Hypersequent} {r : PTree}
    (hshape : SplitProofTheoreticShape base Γ r) :
    SplitProofTheoreticShape base' Γ r :=
  ⟨derivableHypersequent_mono hbase hshape.1,
    openDerivableTree_mono_base hbase hshape.2⟩

theorem splitProofTheoreticShape_not_of_detached_nonderivable
    {base : BaseRel} {Γ : Hypersequent} {r t : PTree}
    (htΓ : t ∈ Γ) (ht : ¬ DerivableTree base t) :
    ¬ SplitProofTheoreticShape base Γ r := by
  intro hshape
  exact derivableHypersequent_not_of_mem_nonderivable htΓ ht hshape.1

/--
Any selected occurrence of a closed derivable proof tree has the expected
singleton proof-theoretic split shape: the selected subtree is a closed
subderivation, and the remainder is an open derivation over that subtree's
conclusion sequent.

This does not assert CK support membership or antichain admissibility; it is
the local proof-theoretic shape theorem for one occurrence.
-/
theorem singleton_occurrence_splitProofTheoreticShape
    {base : BaseRel} {t u : PTree} {a : Address}
    (ht : DerivableTree base t)
    (hsub : PTree.subtreeAt t a = some u) :
    SplitProofTheoreticShape base
      (HQ.singleton u) (PTree.remainderGo [a] [] t) := by
  rcases ht with ⟨s, d, rfl⟩
  have hu : DerivableTree base u := by
    rcases subtreeAt_toTree_is_toTree d a u hsub with ⟨s', d', hu_eq⟩
    exact ⟨s', d', hu_eq.symm⟩
  constructor
  · exact derivableHypersequent_singleton hu
  · simpa [SplitBoundary, HQ.singleton, HQ.conclusions] using
      openDerivableTree_singleton_remainder_of_subtreeAt
        (base := base)
        (t := NMMS.toTree d) (u := u) (a := a)
        ⟨s, d, rfl⟩ hsub

/--
A split term from the ambient coproduct support, read proof-theoretically.

The first conjunct says the term actually occurs in the CK/GL splitting
support of `t`.  The second conjunct says its output has the intended
proof-theoretic shape: closed extracted proofs plus an open remainder.
-/
def ProofTheoreticSplittingSupport
    (base : BaseRel) (t : PTree) (p : Hypersequent × PTree) : Prop :=
  p ∈ splittingSupport t ∧ SplitProofTheoreticShape base p.1 p.2

theorem proofTheoreticSplittingSupport_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {t : PTree} {p : Hypersequent × PTree}
    (hp : ProofTheoreticSplittingSupport base t p) :
    ProofTheoreticSplittingSupport base' t p :=
  ⟨hp.1, splitProofTheoreticShape_mono_base hbase hp.2⟩

theorem proofTheoreticSplittingSupport_not_of_detached_nonderivable
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree} {u : PTree}
    (huΓ : u ∈ p.1) (hu : ¬ DerivableTree base u) :
    ¬ ProofTheoreticSplittingSupport base t p := by
  intro hp
  exact splitProofTheoreticShape_not_of_detached_nonderivable
    huΓ hu hp.2

/--
If a base update destroys a proof tree that occurs on the detached side of a
CK split term, then that ambient split term is no longer proof-theoretic over
the updated base.

The CK cut term still exists as a combinatorial term of the ambient
coalgebra; what fails is the interpretation of the detached forest as a forest
of closed NMMS subderivations over the new material base.
-/
theorem derivableTreeDestroyedByUpdate_blocks_detached_split_shape
    {U : AdmissibleBaseUpdate} {base : BaseRel} {u : PTree}
    (h : DerivableTreeDestroyedByUpdate U base u)
    {Γ : Hypersequent} {r : PTree}
    (huΓ : u ∈ Γ) :
    ∃ base' : BaseRel,
      U base base' ∧
      DerivableTree base u ∧
      ¬ DerivableTree base' u ∧
      ¬ SplitProofTheoreticShape base' Γ r ∧
      ∀ t : PTree, ¬ ProofTheoreticSplittingSupport base' t (Γ, r) := by
  rcases h with ⟨base', hU, hu, hnew⟩
  refine ⟨base', hU, hu, hnew, ?_, ?_⟩
  · exact splitProofTheoreticShape_not_of_detached_nonderivable huΓ hnew
  · intro t
    exact proofTheoreticSplittingSupport_not_of_detached_nonderivable
      (p := (Γ, r)) huΓ hnew

/--
A split remainder can be closed back to `filled` by realizing the boundary
exposed by the detached hypersequent.

This is the substitution/grafting side of the cut-graft duality, stated at the
same level as `ProofTheoreticSplittingSupport`.
-/
def SplitRemainderClosesTo
    (base : BaseRel) (p : Hypersequent × PTree) (filled : PTree) : Prop :=
  FilledByBoundaryRealization base (SplitBoundary p.1) p.2 filled

/--
A proof-theoretic round trip for a coproduct split: the split is admissible and
proof-theoretically shaped, and its open remainder can be closed back to the
original proof by realizing the exposed boundary.
-/
def ProofTheoreticCutGraftRoundTrip
    (base : BaseRel) (t : PTree) (p : Hypersequent × PTree) : Prop :=
  ProofTheoreticSplittingSupport base t p ∧ SplitRemainderClosesTo base p t

/--
Supported cut/graft round trip.

This strengthens `ProofTheoreticCutGraftRoundTrip` by remembering a particular
boundary realization and requiring that it be supported by the detached
hypersequent of the split.  This is the current best formulation of the
duality target before moving to fully occurrence-indexed boundaries.
-/
def SupportedCutGraftRoundTrip
    (base : BaseRel) (t : PTree) (p : Hypersequent × PTree) : Prop :=
  ProofTheoreticSplittingSupport base t p ∧
    ∃ ρ : OpenNMMS.BoundaryRealization base (SplitBoundary p.1),
      BoundaryRealizationSupportedByDetached base p.1 ρ ∧
        FilledByBoundaryRealizationWith ρ p.2 t

/--
A supported round trip is, in particular, an ordinary proof-theoretic
cut/graft round trip.
-/
theorem SupportedCutGraftRoundTrip.to_roundTrip
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (h : SupportedCutGraftRoundTrip base t p) :
    ProofTheoreticCutGraftRoundTrip base t p := by
  rcases h with ⟨hsplit, ρ, _hsupp, hfill⟩
  exact ⟨hsplit, filledByBoundaryRealization_of_with hfill⟩

/--
Every proof-theoretic split has a closed realization of its open remainder.

This is the general closure half of the cut/graft story: the detached forest
supplies derivable boundary sequents, and the open remainder can be closed by
realizing those sequents.  The stronger duality theorem will identify when
that closed realization is the original input tree.
-/
theorem proofTheoreticSplittingSupport_has_closed_remainder_realization
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (hp : ProofTheoreticSplittingSupport base t p) :
    ∃ filledTree : PTree,
      SplitRemainderClosesTo base p filledTree ∧
        DerivableTree base filledTree := by
  rcases hp.2 with ⟨hΓ, hr⟩
  rcases openDerivableTree_has_closed_boundary_realization
      (boundarySequentsDerivable_of_derivableHypersequent hΓ) hr with
    ⟨filledTree, hfill, hder⟩
  exact ⟨filledTree, hfill, hder⟩

/--
A closed proof-theoretic split term: the input tree is itself a genuine closed
NMMS derivation, not merely an ambient labelled tree.
-/
def ClosedProofTheoreticSplittingSupport
    (base : BaseRel) (t : PTree) (p : Hypersequent × PTree) : Prop :=
  DerivableTree base t ∧ ProofTheoreticSplittingSupport base t p

theorem closedProofTheoreticSplittingSupport_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {t : PTree} {p : Hypersequent × PTree}
    (hp : ClosedProofTheoreticSplittingSupport base t p) :
    ClosedProofTheoreticSplittingSupport base' t p :=
  ⟨derivableTree_mono hbase hp.1,
    proofTheoreticSplittingSupport_mono_base hbase hp.2⟩

theorem proofTheoreticSplittingSupport_splitsTo
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (hp : ProofTheoreticSplittingSupport base t p) :
    SplitsTo t p.1 p.2 :=
  splitsTo_of_mem_splittingSupport hp.1

theorem proofTheoreticSplittingSupport_shape
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (hp : ProofTheoreticSplittingSupport base t p) :
    SplitProofTheoreticShape base p.1 p.2 :=
  hp.2

/--
If an ambient support term is taken from a genuine closed proof tree, its
detached side is automatically a closed derivable hypersequent.

The only remaining proof-theoretic obligation for a general coproduct support
term is therefore the open-remainder judgment.
-/
theorem detached_derivable_of_mem_splittingSupport
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (ht : DerivableTree base t)
    (hp : p ∈ splittingSupport t) :
    DerivableHypersequent base p.1 :=
  derivableHypersequent_detached_of_splitsTo ht
    (splitsTo_of_mem_splittingSupport hp)

/--
Promote an ambient split-support term to a proof-theoretic support term once
the remainder has been identified as an open proof context over the exposed
boundary.
-/
theorem proofTheoreticSplittingSupport_of_open_remainder
    {base : BaseRel} {t : PTree} {p : Hypersequent × PTree}
    (ht : DerivableTree base t)
    (hp : p ∈ splittingSupport t)
    (hr : OpenDerivableTree base (SplitBoundary p.1) p.2) :
    ProofTheoreticSplittingSupport base t p := by
  exact ⟨hp, ⟨detached_derivable_of_mem_splittingSupport ht hp, hr⟩⟩

/--
Identity support term: the empty cut says a closed proof is an open proof
context with no extra boundary assumptions.
-/
theorem identity_mem_proofTheoreticSplittingSupport
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ProofTheoreticSplittingSupport base t (0, t) := by
  apply proofTheoreticSplittingSupport_of_open_remainder ht
  · exact splittingSupport_contains_identity t
  · exact openDerivableTree_of_derivableTree ht

/--
If a split has the expected proof-theoretic shape, then adding its target to a
closed external context gives an open derivable hypersequent.
-/
theorem external_split_target_openDerivable_of_shape
    {base : BaseRel} {G Γ : Hypersequent} {r : PTree}
    (hG : DerivableHypersequent base G)
    (hshape : SplitProofTheoreticShape base Γ r) :
    OpenDerivableHypersequent base (SplitBoundary Γ)
      (G + Γ + HQ.singleton r) := by
  rcases hshape with ⟨hΓ, hr⟩
  apply openDerivableHypersequent_add
  · apply openDerivableHypersequent_add
    · exact openDerivableHypersequent_of_derivableHypersequent hG
    · exact openDerivableHypersequent_of_derivableHypersequent hΓ
  · exact openDerivableHypersequent_singleton hr

/--
The terminal leaves of a proof-theoretic split remainder are exactly of the
right kind: base/material axiom leaves or boundary/interface leaves exposed by
the detached forest.
-/
theorem splitProofTheoreticShape_remainder_leafSequents
    {base : BaseRel} {Γ : Hypersequent} {r : PTree}
    (hshape : SplitProofTheoreticShape base Γ r) :
    PTree.LeafSequentsSatisfy
      (OpenTerminalSequent base (SplitBoundary Γ)) r :=
  openDerivableTree_leafSequents_base_or_boundary hshape.2

/--
The closed detached side of a split supplies the first half of the expected
proof-theoretic split shape.
-/
theorem splitProofTheoreticShape_detached
    {base : BaseRel} {t : PTree} {Γ : Hypersequent} {r : PTree}
    (ht : DerivableTree base t)
    (hs : SplitsTo t Γ r) :
    DerivableHypersequent base Γ :=
  derivableHypersequent_detached_of_splitsTo ht hs

/-- The root split remainder is open over the boundary containing the root sequent. -/
theorem root_split_remainder_openDerivable
    {base : BaseRel} {t : PTree}
    (_ht : DerivableTree base t) :
    OpenDerivableTree base ({t.conclusion} : Multiset MultiSequent)
      (PTree.leaf t.conclusion) := by
  exact openDerivableTree_boundary (by simp)

/--
Root splitting has the full expected proof-theoretic split shape.
-/
theorem root_split_proofTheoreticShape
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    SplitProofTheoreticShape base
      (HQ.singleton t)
      (PTree.leaf t.conclusion) := by
  constructor
  · exact derivableHypersequent_singleton ht
  · simpa [SplitBoundary] using root_split_remainder_openDerivable ht

/--
Root support term: the top split detaches the whole closed proof and leaves
its conclusion as a boundary leaf.
-/
theorem root_mem_proofTheoreticSplittingSupport
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ProofTheoreticSplittingSupport base t
      (HQ.singleton t, PTree.leaf t.conclusion) := by
  exact ⟨splittingSupport_contains_root t, root_split_proofTheoreticShape ht⟩

/--
Closed root support term: the same root split, with the derivability of the
input recorded explicitly.
-/
theorem root_mem_closedProofTheoreticSplittingSupport
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ClosedProofTheoreticSplittingSupport base t
      (HQ.singleton t, PTree.leaf t.conclusion) :=
  ⟨ht, root_mem_proofTheoreticSplittingSupport ht⟩

/--
The root split closes back to the original proof by realizing its singleton
boundary with that proof.
-/
theorem root_split_remainder_closesTo
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    SplitRemainderClosesTo base
      (HQ.singleton t, PTree.leaf t.conclusion) t := by
  simpa [SplitRemainderClosesTo, SplitBoundary] using
    root_boundary_filledByBoundaryRealization ht

/--
The root split is the first proof-theoretic cut/graft round trip.

The coproduct detaches the whole proof and leaves its conclusion as an open
boundary leaf; realizing that boundary by the detached proof reconstructs the
original closed derivation.
-/
theorem root_proofTheoreticCutGraftRoundTrip
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    ProofTheoreticCutGraftRoundTrip base t
      (HQ.singleton t, PTree.leaf t.conclusion) := by
  exact ⟨root_mem_proofTheoreticSplittingSupport ht,
    root_split_remainder_closesTo ht⟩

/--
The root split is also a supported cut/graft round trip: the realization of the
single exposed boundary is supported by the detached proof itself.
-/
theorem root_supportedCutGraftRoundTrip
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    SupportedCutGraftRoundTrip base t
      (HQ.singleton t, PTree.leaf t.conclusion) := by
  rcases closedProofAtConclusion_of_derivableTree ht with ⟨d, hd⟩
  let ρ := singletonBoundaryRealization_of_closedProof d
  refine ⟨root_mem_proofTheoreticSplittingSupport ht, ρ, ?_, ?_⟩
  · intro s hs
    have hs' : s = t.conclusion := by
      simpa [SplitBoundary] using hs
    subst s
    refine ⟨t, by simp [HQ.singleton], rfl, ?_⟩
    exact closedProofAtConclusion_of_derivableTree ht
  · refine ⟨t.conclusion, OpenNMMS.boundary (by simp [SplitBoundary]), rfl, ?_⟩
    simpa [ρ, OpenNMMS.closeTree,
      singletonBoundaryRealization_of_closedProof] using hd

/-! ## Occurrence-marked proof contexts -/

/--
A marked sequent occurrence.

The address records where the occurrence came from in the original proof tree;
the sequent is the conclusion of the subderivation extracted there.
-/
structure MarkedSequentOccurrence where
  address : Address
  sequent : MultiSequent

/--
Proof-context trees: ordinary proof-tree syntax, but with explicit marked
sequent occurrences.

This is the proof-theoretic replacement for treating coproduct remainders as
plain `PTree` leaves.  A marked occurrence is not a base axiom leaf; it is a
remembered place where an extracted subderivation may later be filled back in.
-/
inductive ProofContextTree where
| leaf : MultiSequent → ProofContextTree
| mark : MarkedSequentOccurrence → ProofContextTree
| node : RuleTag → MultiSequent → List ProofContextTree → ProofContextTree

namespace ProofContextTree

/-- The conclusion sequent of a proof-context tree. -/
def conclusion : ProofContextTree → MultiSequent
| leaf s => s
| mark occ => occ.sequent
| node _ s _ => s

/--
Forget marked occurrences, turning them back into ordinary leaves.

This is intentionally lossy: it recovers the old `PTree` remainder view.
-/
def forget : ProofContextTree → PTree
| leaf s => PTree.leaf s
| mark occ => PTree.leaf occ.sequent
| node r s cs => PTree.node r s (cs.map forget)

/-- Regard an ordinary proof tree as a context tree with no marked occurrences. -/
def ofPTree : PTree → ProofContextTree
| PTree.leaf s => leaf s
| PTree.node r s cs => node r s (cs.map ofPTree)

@[simp]
theorem conclusion_ofPTree (t : PTree) :
    conclusion (ofPTree t) = t.conclusion := by
  cases t <;> simp [ofPTree, conclusion, PTree.conclusion]

/--
Mark the subtree occurrence at address `target`.

The marked occurrence remembers `origin`, which is usually the same address as
`target` when the context is produced by a decomposition cut.  Keeping these
separate is useful when addresses are transported or normalized later.
-/
def markAt (origin : Address) : PTree → Address → Option ProofContextTree
| t, [] =>
    some (mark { address := origin, sequent := t.conclusion })
| PTree.leaf _, _ :: _ =>
    none
| PTree.node r s cs, i :: rest =>
    if h : i < cs.length then
      match markAt origin cs[i] rest with
      | some child' =>
          some (node r s (PTree.replaceNth (cs.map ofPTree) i child'))
      | none => none
    else
      none

/--
Fill the marked occurrence at address `target` with a proof tree whose
conclusion matches the marked sequent.

This is the inverse operation to occurrence marking, stated as proof-context
substitution rather than as a logical cut rule.
-/
def fillAt (u : PTree) : ProofContextTree → Address → Option ProofContextTree
| mark occ, [] =>
    if h : u.conclusion = occ.sequent then
      some (ofPTree u)
    else
      none
| leaf _, [] =>
    none
| node _ _ _, [] =>
    none
| node r s cs, i :: rest =>
    if h : i < cs.length then
      match fillAt u cs[i] rest with
      | some child' => some (node r s (PTree.replaceNth cs i child'))
      | none => none
    else
      none
| _, _ :: _ =>
    none

/--
An interface policy says when a proof with conclusion `target` may fill a
marked occurrence labelled by `source`.

This is where exact matching, controlled internal weakening, external
weakening, or base/material consequence assumptions should be parameterized.
The reflexivity field keeps ordinary same-sequent grafting always available.
-/
structure InterfacePolicy (base : BaseRel) where
  mayFill : MultiSequent → MultiSequent → Prop
  refl : ∀ s : MultiSequent, mayFill s s

/-- The strict policy: a marked occurrence can only be filled by the same sequent. -/
def exactInterfacePolicy (base : BaseRel) : InterfacePolicy base where
  mayFill source target := source = target
  refl := by
    intro s
    rfl

/-- The ambient/free policy: any conclusion may fill any marked occurrence. -/
def freeInterfacePolicy (base : BaseRel) : InterfacePolicy base where
  mayFill _ _ := True
  refl := by
    intro _
    trivial

/--
A policy is base-sound when every permitted fill can be read backwards as
preserving derivability of the marked interface sequent.

This is a proof-theoretic diagnostic: exact matching is base-sound immediately,
while nontrivial weakening or material-consequence policies must prove this
property from the chosen base relation or structural rule assumptions.
-/
def InterfacePolicy.BaseSound {base : BaseRel} (P : InterfacePolicy base) : Prop :=
  ∀ ⦃source target : MultiSequent⦄,
    P.mayFill source target →
      DerivableSequent base target →
        DerivableSequent base source

/--
Policy extension: `P` allows every interface fill that `Q` allows.

This is the structural-rule preorder on algebra-side composition policies.
-/
def InterfacePolicy.Extends {base : BaseRel}
    (P Q : InterfacePolicy base) : Prop :=
  ∀ ⦃source target : MultiSequent⦄,
    Q.mayFill source target → P.mayFill source target

theorem InterfacePolicy.Extends.refl
    {base : BaseRel} (P : InterfacePolicy base) :
    P.Extends P := by
  intro source target h
  exact h

theorem InterfacePolicy.Extends.trans
    {base : BaseRel} {P Q R : InterfacePolicy base}
    (hPQ : P.Extends Q) (hQR : Q.Extends R) :
    P.Extends R := by
  intro source target h
  exact hPQ (hQR h)

theorem exactInterfacePolicy_baseSound (base : BaseRel) :
    (exactInterfacePolicy base).BaseSound := by
  intro source target h ht
  subst source
  exact ht

/--
A schematic material/interface schema over an arbitrary base relation.

The schema does not choose a specific material consequence relation.  Instead,
for the current `base`, it supplies the interface changes that are licensed
and a soundness proof saying that every licensed fill preserves ordinary
derivability of the interface sequent.
-/
structure MaterialInterfaceSchema (base : BaseRel) where
  mayFill : MultiSequent -> MultiSequent -> Prop
  refl : forall s : MultiSequent, mayFill s s
  sound :
    forall {source target : MultiSequent},
      mayFill source target ->
        DerivableSequent base target ->
          DerivableSequent base source

namespace MaterialInterfaceSchema

/-- Forget a schematic material/interface schema to the existing policy API. -/
def toPolicy {base : BaseRel}
    (S : MaterialInterfaceSchema base) : InterfacePolicy base where
  mayFill := S.mayFill
  refl := S.refl

@[simp]
theorem toPolicy_mayFill {base : BaseRel}
    (S : MaterialInterfaceSchema base) (source target : MultiSequent) :
    S.toPolicy.mayFill source target <-> S.mayFill source target := by
  rfl

/-- The policy extracted from a material/interface schema is base-sound. -/
theorem toPolicy_baseSound {base : BaseRel}
    (S : MaterialInterfaceSchema base) :
    S.toPolicy.BaseSound := by
  intro source target hfill htarget
  exact S.sound hfill htarget

/-- Exact same-sequent matching as the minimal schematic interface schema. -/
def exact (base : BaseRel) : MaterialInterfaceSchema base where
  mayFill source target := source = target
  refl := by
    intro s
    rfl
  sound := by
    intro source target h htarget
    subst source
    exact htarget

@[simp]
theorem exact_toPolicy (base : BaseRel) :
    (exact base).toPolicy = exactInterfacePolicy base := by
  rfl

/--
Cross-base extension of schematic interface permissions.

`S'.Extends S` says that every interface fill licensed over `base` by `S` is
also licensed over `base'` by `S'`.  The bases may differ; this is the
right notion for transporting schematic structural traces across a monotone
base extension without requiring a particular material consequence relation.
-/
def Extends {base base' : BaseRel}
    (S' : MaterialInterfaceSchema base')
    (S : MaterialInterfaceSchema base) : Prop :=
  forall {source target : MultiSequent},
    S.mayFill source target -> S'.mayFill source target

theorem Extends.refl {base : BaseRel}
    (S : MaterialInterfaceSchema base) :
    S.Extends S := by
  intro source target h
  exact h

theorem Extends.trans {base base' base'' : BaseRel}
    {S : MaterialInterfaceSchema base}
    {S' : MaterialInterfaceSchema base'}
    {S'' : MaterialInterfaceSchema base''}
    (h₂ : S''.Extends S') (h₁ : S'.Extends S) :
    S''.Extends S := by
  intro source target h
  exact h₂ (h₁ h)

/-- Exact matching permissions are stable across arbitrary base changes. -/
theorem exact_extends_exact
    (base base' : BaseRel) :
    (exact base').Extends (exact base) := by
  intro source target h
  exact h

end MaterialInterfaceSchema

/-- Decidable core for policy-mediated filling. -/
private def fillAtWithDecidable {base : BaseRel} (P : InterfacePolicy base)
    [∀ source target, Decidable (P.mayFill source target)]
    (u : PTree) :
    ProofContextTree → Address → Option ProofContextTree
| mark occ, [] =>
    if h : P.mayFill occ.sequent u.conclusion then
      some (ofPTree u)
    else
      none
| leaf _, [] =>
    none
| node _ _ _, [] =>
    none
| node r s cs, i :: rest =>
    if h : i < cs.length then
      match fillAtWithDecidable P u cs[i] rest with
      | some child' => some (node r s (PTree.replaceNth cs i child'))
      | none => none
    else
      none
| _, _ :: _ =>
    none

/--
Policy-mediated filling of a marked occurrence.

The strict `fillAt` above is recovered by using `exactInterfacePolicy`.  This
version is the one to use for proof-theoretic experiments with controlled
weakening, material entailment, and admissible structural rules.  It is
noncomputable because an arbitrary admissibility policy is a proposition, not
necessarily a decidable test.
-/
noncomputable def fillAtWith {base : BaseRel} (P : InterfacePolicy base) (u : PTree) :
    ProofContextTree → Address → Option ProofContextTree := by
  classical
  exact fillAtWithDecidable P u

/-- A compact existential support predicate for policy-mediated grafting. -/
def PolicyFillSupport {base : BaseRel}
    (P : InterfacePolicy base) (u : PTree)
    (ctx filled : ProofContextTree) : Prop :=
  ∃ a : Address, fillAtWith P u ctx a = some filled

theorem fillAtWith_root_mark_of_mayFill
    {base : BaseRel} (P : InterfacePolicy base)
    (u : PTree) (origin : Address) {source : MultiSequent}
    (h : P.mayFill source u.conclusion) :
    fillAtWith P u
        (mark { address := origin, sequent := source })
        [] =
      some (ofPTree u) := by
  classical
  simp [fillAtWith, fillAtWithDecidable, h]

@[simp]
theorem fillAtWith_root_mark
    {base : BaseRel} (P : InterfacePolicy base)
    (u : PTree) (origin : Address) :
    fillAtWith P u
        (mark { address := origin, sequent := u.conclusion })
        [] =
      some (ofPTree u) := by
  exact fillAtWith_root_mark_of_mayFill P u origin (P.refl u.conclusion)

theorem policyFillSupport_root
    {base : BaseRel} (P : InterfacePolicy base)
    (t : PTree) :
    PolicyFillSupport P t
      (mark { address := ([] : Address), sequent := t.conclusion })
      (ofPTree t) := by
  refine ⟨[], ?_⟩
  simp

@[simp]
theorem markAt_root (origin : Address) (t : PTree) :
    markAt origin t [] =
      some (mark { address := origin, sequent := t.conclusion }) := by
  cases t <;> rfl

@[simp]
theorem fillAt_root_mark
    (u : PTree) (origin : Address) :
    fillAt u
        (mark { address := origin, sequent := u.conclusion })
        [] =
      some (ofPTree u) := by
  simp [fillAt]

/--
Root occurrence reconstruction: mark the whole proof tree as an occurrence and
then fill that occurrence with the same proof tree.

This is the first occurrence-sensitive version of the cut/graft round trip.
-/
theorem root_mark_fill_reconstructs
    (t : PTree) :
    ∃ ctx filled : ProofContextTree,
      markAt ([] : Address) t [] = some ctx ∧
        fillAt t ctx [] = some filled ∧
          filled = ofPTree t := by
  refine ⟨mark { address := ([] : Address), sequent := t.conclusion },
    ofPTree t, ?_, ?_, ?_⟩
  · simp
  · simp
  · rfl

/--
Policy version of root occurrence reconstruction.

This is quantified over every interface policy, so it covers exact grafting,
base-controlled grafting, and structural-rule-controlled grafting uniformly.
-/
theorem root_mark_fillWith_reconstructs
    {base : BaseRel} (P : InterfacePolicy base)
    (t : PTree) :
    ∃ ctx filled : ProofContextTree,
      markAt ([] : Address) t [] = some ctx ∧
        fillAtWith P t ctx [] = some filled ∧
          filled = ofPTree t := by
  refine ⟨mark { address := ([] : Address), sequent := t.conclusion },
    ofPTree t, ?_, ?_, ?_⟩
  · simp
  · simp
  · rfl

theorem exists_policyFillSupport_for_marked_root
    {base : BaseRel} (P : InterfacePolicy base)
    (t : PTree) :
    ∃ ctx : ProofContextTree,
      markAt ([] : Address) t [] = some ctx ∧
        PolicyFillSupport P t ctx (ofPTree t) := by
  refine ⟨mark { address := ([] : Address), sequent := t.conclusion }, ?_, ?_⟩
  · simp
  · exact policyFillSupport_root P t

end ProofContextTree

/-! ## Schematic structural proof traces -/

/--
Proof traces generated from ordinary NMMS derivations plus schematic
interface-fill steps.

The parameter `S` is intentionally schematic: it is any base-sound interface
schema for the current material base.  Thus this records structural rule
applications without fixing one particular material consequence relation.
-/
inductive SchematicProof (base : BaseRel)
    (S : ProofContextTree.MaterialInterfaceSchema base) :
    MultiSequent -> Type where
| logical {s : MultiSequent}
    (d : NMMS base s) :
    SchematicProof base S s
| interfaceFill {source target : MultiSequent}
    (hfill : S.mayFill source target)
    (d : SchematicProof base S target) :
    SchematicProof base S source

namespace SchematicProof

/-- Forget a schematic proof to its structurally labelled proof trace. -/
def toTraceTree {base : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {s : MultiSequent}
    (d : SchematicProof base S s) : ProofTraceTree :=
  match d with
  | logical nd => ProofTraceTree.ofPTree (NMMS.toTree nd)
  | interfaceFill (source := source) _ d' =>
      ProofTraceTree.node
        (ProofStepLabel.structural StructuralRuleTag.interfaceFill)
        source
        [toTraceTree d']

/--
The trace root remembers the sequent proved by the schematic proof.
-/
theorem toTraceTree_conclusion {base : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {s : MultiSequent}
    (d : SchematicProof base S s) :
    (toTraceTree d).conclusion = s := by
  induction d with
  | logical nd =>
      simpa [toTraceTree] using
        (ProofTraceTree.conclusion_ofPTree (NMMS.toTree nd)).trans
          (toTree_conclusion nd)
  | interfaceFill hfill d ih =>
      simp [toTraceTree, ProofTraceTree.conclusion]

/--
Base-sound schematic structural traces are conservative over ordinary NMMS
sequent derivability.

This is the main anti-ad-hoc guardrail: adding structural labels does not
create arbitrary consequences; every structural fill must be justified by the
schema's soundness proof over the current material base.
-/
theorem derivableSequent {base : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {s : MultiSequent}
    (d : SchematicProof base S s) :
    DerivableSequent base s := by
  induction d with
  | logical nd =>
      exact derivableSequent_of_derivation nd
  | interfaceFill hfill d ih =>
      exact S.sound hfill ih

/-- Every ordinary NMMS derivation is a schematic proof with no structural fill. -/
def ofNMMS {base : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {s : MultiSequent}
    (d : NMMS base s) :
    SchematicProof base S s :=
  logical d

/--
An allowed interface fill gives a structurally labelled one-step extension of
any schematic proof of the target sequent.
-/
def interfaceFillStep {base : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {source target : MultiSequent}
    (hfill : S.mayFill source target)
    (d : SchematicProof base S target) :
    SchematicProof base S source :=
  interfaceFill hfill d

/--
Transport schematic structural proofs across a monotone base extension, provided
the target schema includes the source schema's interface permissions.
-/
def mapBase {base base' : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {S' : ProofContextTree.MaterialInterfaceSchema base'}
    (hbase : BaseRelExtends base base')
    (hS : S'.Extends S)
    {s : MultiSequent} :
    SchematicProof base S s -> SchematicProof base' S' s
| logical d => logical (NMMS.mapBase hbase d)
| interfaceFill hfill d => interfaceFill (hS hfill) (mapBase hbase hS d)

/-- Transporting a schematic proof across base extension preserves its trace. -/
theorem toTraceTree_mapBase {base base' : BaseRel}
    {S : ProofContextTree.MaterialInterfaceSchema base}
    {S' : ProofContextTree.MaterialInterfaceSchema base'}
    (hbase : BaseRelExtends base base')
    (hS : S'.Extends S)
    {s : MultiSequent}
    (d : SchematicProof base S s) :
    toTraceTree (mapBase hbase hS d) = toTraceTree d := by
  induction d with
  | logical nd =>
      simp [mapBase, toTraceTree, NMMS.toTree_mapBase]
  | interfaceFill hfill d ih =>
      simp [mapBase, toTraceTree, ih]

/--
Monotone base extension preserves exact schematic proofs.

This is the default transport theorem when the structural layer is only exact
same-sequent matching.
-/
def mapBaseExact {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {s : MultiSequent} :
    SchematicProof base (ProofContextTree.MaterialInterfaceSchema.exact base) s ->
      SchematicProof base'
        (ProofContextTree.MaterialInterfaceSchema.exact base') s :=
  mapBase hbase
    (ProofContextTree.MaterialInterfaceSchema.exact_extends_exact base base')

/--
If a base update destroys a logical entailment, then no sound schematic
interface schema over the updated base can produce a schematic proof of that
same sequent.

Structural labels cannot resurrect a sequent whose ordinary derivability over
the updated material base has failed, because every schema carries its own
soundness proof.
-/
theorem destroyed_logical_entailment_blocks_schematic_proofs
    {U : AdmissibleBaseUpdate} {base : BaseRel}
    {Gamma Theta : Multiset MyProp}
    (h : LogicalEntailmentDestroyedByUpdate U base Gamma Theta) :
    exists base' : BaseRel,
      U base base' /\
        LogicalEntails base Gamma Theta /\
          forall S' : ProofContextTree.MaterialInterfaceSchema base',
            SchematicProof base' S' (Gamma ∣∼ Theta) -> False := by
  rcases h with ⟨base', hU, hold, hnew⟩
  refine ⟨base', hU, hold, ?_⟩
  intro S' d
  exact hnew (SchematicProof.derivableSequent d)

end SchematicProof

/-! ## Policy-mediated grafting support -/

/--
Policy-mediated matching-leaf grafting.

The old `PTree.graftMatchingLeafAt` is the exact/same-sequent case.  This
version makes the algebra side sensitive to structural-rule policy: a leaf
labelled by `source` may be replaced by a proof tree whose conclusion is
`target` precisely when `P.mayFill source target`.
-/
noncomputable def policyGraftMatchingLeafAt
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address) : Option PTree := by
  classical
  exact
    match PTree.subtreeAt t a with
    | some (PTree.leaf source) =>
        if h : P.mayFill source u.conclusion then
          PTree.modifyAt t a (fun _ => u)
        else
          none
    | _ => none

/-- All policy-mediated leaf graftings of `u` into `t`. -/
noncomputable def policyMatchingLeafGraftings
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) : List PTree :=
  (PTree.allAddresses t).filterMap (policyGraftMatchingLeafAt P u t)

/-- A named address-level policy graft witness. -/
def PolicyInternalGraftAt
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address) (v : PTree) : Prop :=
  policyGraftMatchingLeafAt P u t a = some v

/-- Policy-mediated internal proof composition support. -/
def PolicyInternalGraft
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) : Prop :=
  ∃ a : Address, PolicyInternalGraftAt P u t a v

/--
The labelled occurrence data behind a policy-mediated graft.

This records the address, the sequent label of the replaced leaf, the policy
permission used at that interface, and the resulting tree modification.  It is
the bookkeeping layer needed to remember where a structural/logical
composition happened.
-/
structure PolicyGraftOccurrence
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) where
  address : Address
  source : MultiSequent
  leafAt : PTree.subtreeAt t address = some (PTree.leaf source)
  allowed : P.mayFill source u.conclusion
  result : PTree.modifyAt t address (fun _ => u) = some v

theorem PolicyGraftOccurrence.toInternalGraft
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree}
    (o : PolicyGraftOccurrence P u t v) :
    PolicyInternalGraft P u t v := by
  classical
  refine ⟨o.address, ?_⟩
  rw [PolicyInternalGraftAt]
  unfold policyGraftMatchingLeafAt
  simp [o.leafAt, o.allowed, o.result]

/--
An existential policy graft witness is equivalent to a labelled occurrence
witness.
-/
theorem policyInternalGraft_iff_nonempty_occurrence
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) :
    PolicyInternalGraft P u t v ↔
      Nonempty (PolicyGraftOccurrence P u t v) := by
  classical
  constructor
  · rintro ⟨a, hg⟩
    unfold PolicyInternalGraftAt policyGraftMatchingLeafAt at hg
    cases hsub : PTree.subtreeAt t a with
    | none =>
        simp [hsub] at hg
    | some st =>
        cases st with
        | leaf source =>
            by_cases hfill : P.mayFill source u.conclusion
            · have hmod : PTree.modifyAt t a (fun _ => u) = some v := by
                simpa [hsub, hfill] using hg
              exact ⟨{
                address := a
                source := source
                leafAt := hsub
                allowed := hfill
                result := hmod
              }⟩
            · simp [hsub, hfill] at hg
        | node r s cs =>
            simp [hsub] at hg
  · rintro ⟨o⟩
    exact o.toInternalGraft

/--
Membership in the policy grafting support list is exactly the existential
policy graft witness.
-/
theorem mem_policyMatchingLeafGraftings_iff
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) :
    v ∈ policyMatchingLeafGraftings P u t ↔
      PolicyInternalGraft P u t v := by
  classical
  unfold policyMatchingLeafGraftings PolicyInternalGraft PolicyInternalGraftAt
  constructor
  · intro hv
    rcases List.mem_filterMap.1 hv with ⟨a, _ha, hg⟩
    exact ⟨a, hg⟩
  · rintro ⟨a, hg⟩
    refine List.mem_filterMap.2 ?_
    have haddr : a ∈ PTree.allAddresses t := by
      unfold policyGraftMatchingLeafAt at hg
      cases hsub : PTree.subtreeAt t a with
      | none =>
          simp [hsub] at hg
      | some st =>
          exact PTree.subtreeAt_some_implies_mem_allAddresses t st a hsub
    exact ⟨a, haddr, hg⟩

theorem policyGraftMatchingLeafAt_eq_some_of_mayFill
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address) (source : MultiSequent)
    (hleaf : PTree.subtreeAt t a = some (PTree.leaf source))
    (hfill : P.mayFill source u.conclusion) :
    policyGraftMatchingLeafAt P u t a =
      PTree.modifyAt t a (fun _ => u) := by
  classical
  simp [policyGraftMatchingLeafAt, hleaf, hfill]

theorem policyGraftMatchingLeafAt_eq_none_of_not_mayFill
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address) (source : MultiSequent)
    (hleaf : PTree.subtreeAt t a = some (PTree.leaf source))
    (hfill : ¬ P.mayFill source u.conclusion) :
    policyGraftMatchingLeafAt P u t a = none := by
  classical
  simp [policyGraftMatchingLeafAt, hleaf, hfill]

theorem policyGraftMatchingLeafAt_eq_none_of_subtreeAt_none
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address)
    (h : PTree.subtreeAt t a = none) :
    policyGraftMatchingLeafAt P u t a = none := by
  classical
  simp [policyGraftMatchingLeafAt, h]

theorem policyGraftMatchingLeafAt_eq_none_of_subtreeAt_node
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) (a : Address)
    (r : RuleTag) (s : MultiSequent) (cs : List PTree)
    (h : PTree.subtreeAt t a = some (PTree.node r s cs)) :
    policyGraftMatchingLeafAt P u t a = none := by
  classical
  simp [policyGraftMatchingLeafAt, h]

theorem policyInternalGraft_of_mayFill_at
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) (a : Address) (source : MultiSequent)
    (hleaf : PTree.subtreeAt t a = some (PTree.leaf source))
    (hfill : P.mayFill source u.conclusion)
    (hmod : PTree.modifyAt t a (fun _ => u) = some v) :
    PolicyInternalGraft P u t v := by
  refine ⟨a, ?_⟩
  rw [PolicyInternalGraftAt]
  rw [policyGraftMatchingLeafAt_eq_some_of_mayFill P u t a source hleaf hfill]
  exact hmod

theorem policyInternalGraft_root_leaf_of_mayFill
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u : PTree) (source : MultiSequent)
    (hfill : P.mayFill source u.conclusion) :
    PolicyInternalGraft P u (PTree.leaf source) u := by
  refine ⟨[], ?_⟩
  classical
  rw [PolicyInternalGraftAt]
  unfold policyGraftMatchingLeafAt
  simp only [PTree.subtreeAt]
  simp [hfill]

theorem policyInternalGraft_root_leaf
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u : PTree) :
    PolicyInternalGraft P u (PTree.leaf u.conclusion) u :=
  policyInternalGraft_root_leaf_of_mayFill P u u.conclusion (P.refl u.conclusion)

/--
Exact policy grafting recovers the old matching-leaf grafting relation at the
root leaf.  This is the local bridge from the policy-parametric algebra side
back to the original GL/pre-Lie product.
-/
theorem exactPolicyInternalGraft_root_leaf
    {base : BaseRel} (u : PTree) :
    PolicyInternalGraft (ProofContextTree.exactInterfacePolicy base)
      u (PTree.leaf u.conclusion) u :=
  policyInternalGraft_root_leaf
    (ProofContextTree.exactInterfacePolicy base) u

theorem exactPolicyInternalGraftAt_of_graftMatchingLeafAt
    {base : BaseRel} {u t v : PTree} {a : Address}
    (hg : PTree.graftMatchingLeafAt u t a = some v) :
    PolicyInternalGraftAt
      (ProofContextTree.exactInterfacePolicy base) u t a v := by
  classical
  unfold PTree.graftMatchingLeafAt at hg
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at hg
  | some st =>
      cases st with
      | leaf source =>
          by_cases hmatch : u.conclusion = source
          · have hsource : source = u.conclusion := hmatch.symm
            have hmod : PTree.modifyAt t a (fun _ => u) = some v := by
              simpa [hsub, hmatch] using hg
            rw [PolicyInternalGraftAt]
            simpa [policyGraftMatchingLeafAt, hsub,
              ProofContextTree.exactInterfacePolicy, hsource] using hmod
          · simp [hsub, hmatch] at hg
      | node r s cs =>
          simp [hsub] at hg

/--
Every old exact matching-leaf graft is a policy-mediated graft for the exact
interface policy.
-/
theorem exactPolicyInternalGraft_of_InternalGraft
    {base : BaseRel} {u t v : PTree}
    (hg : InternalGraft u t v) :
    PolicyInternalGraft
      (ProofContextTree.exactInterfacePolicy base) u t v := by
  rcases hg with ⟨a, ha⟩
  exact ⟨a, exactPolicyInternalGraftAt_of_graftMatchingLeafAt ha⟩

/--
Every member of the original pre-Lie matching support is a policy-mediated
graft for the exact policy.
-/
theorem exactPolicyInternalGraft_of_mem_matchingLeafGraftings
    {base : BaseRel} {u t v : PTree}
    (hv : v ∈ PTree.matchingLeafGraftings u t) :
    PolicyInternalGraft
      (ProofContextTree.exactInterfacePolicy base) u t v :=
  exactPolicyInternalGraft_of_InternalGraft
    (internalGraft_of_mem_matchingLeafGraftings hv)

theorem policyGraftMatchingLeafAt_mono
    {base : BaseRel}
    {P Q : ProofContextTree.InterfacePolicy base}
    (hPQ : P.Extends Q)
    {u t v : PTree} {a : Address}
    (hg : policyGraftMatchingLeafAt Q u t a = some v) :
    policyGraftMatchingLeafAt P u t a = some v := by
  classical
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [policyGraftMatchingLeafAt, hsub] at hg
  | some st =>
      cases st with
      | leaf source =>
          by_cases hQ : Q.mayFill source u.conclusion
          · have hP : P.mayFill source u.conclusion := hPQ hQ
            have hmod : PTree.modifyAt t a (fun _ => u) = some v := by
              simpa [policyGraftMatchingLeafAt, hsub, hQ] using hg
            simpa [policyGraftMatchingLeafAt, hsub, hP] using hmod
          · simp [policyGraftMatchingLeafAt, hsub, hQ] at hg
      | node r s cs =>
          simp [policyGraftMatchingLeafAt, hsub] at hg

/--
Extending the structural/interface policy can only enlarge one-step graft
support.
-/
theorem policyInternalGraft_mono
    {base : BaseRel}
    {P Q : ProofContextTree.InterfacePolicy base}
    (hPQ : P.Extends Q)
    {u t v : PTree}
    (hg : PolicyInternalGraft Q u t v) :
    PolicyInternalGraft P u t v := by
  rcases hg with ⟨a, ha⟩
  exact ⟨a, policyGraftMatchingLeafAt_mono hPQ ha⟩

/--
Replacing a non-root occurrence preserves the root sequent label and root rule
label of the surrounding proof tree.
-/
theorem modifyAt_nonroot_preserves_root_labels
    (t u v : PTree) {a : Address}
    (hane : a ≠ [])
    (hmod : PTree.modifyAt t a (fun _ => u) = some v) :
    v.conclusion = t.conclusion ∧
      v.rootRule? = t.rootRule? := by
  cases a with
  | nil =>
      exact False.elim (hane rfl)
  | cons i rest =>
      cases t with
      | leaf s =>
          simp [PTree.modifyAt] at hmod
      | node r s cs =>
          by_cases hi : i < cs.length
          · simp [PTree.modifyAt, hi] at hmod
            cases hrec : PTree.modifyAt cs[i] rest (fun _ => u) with
            | none =>
                simp [hrec] at hmod
            | some child' =>
                simp [hrec] at hmod
                cases hmod
                simp [PTree.conclusion, PTree.rootRule?]
          · simp [PTree.modifyAt, hi] at hmod

/-- Successful policy grafting is, underneath, a successful `modifyAt`. -/
theorem modifyAt_eq_some_of_policyGraftMatchingLeafAt_eq_some
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree} {a : Address}
    (hg : policyGraftMatchingLeafAt P u t a = some v) :
    PTree.modifyAt t a (fun _ => u) = some v := by
  classical
  unfold policyGraftMatchingLeafAt at hg
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at hg
  | some st =>
      cases st with
      | leaf source =>
          by_cases hfill : P.mayFill source u.conclusion
          · simpa [hsub, hfill] using hg
          · simp [hsub, hfill] at hg
      | node r s cs =>
          simp [hsub] at hg

/--
Policy grafting installs the inserted proof tree at the selected address,
preserving all labels internal to the inserted tree below that address.
-/
theorem policyGraftMatchingLeafAt_subtreeAt_append
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree} {a c : Address}
    (hg : policyGraftMatchingLeafAt P u t a = some v) :
    PTree.subtreeAt v (a ++ c) = PTree.subtreeAt u c := by
  exact subtreeAt_modifyAt_append t u a c v
    (modifyAt_eq_some_of_policyGraftMatchingLeafAt_eq_some hg)

theorem policyGraftMatchingLeafAt_subtreeAt_self
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree} {a : Address}
    (hg : policyGraftMatchingLeafAt P u t a = some v) :
    PTree.subtreeAt v a = some u := by
  simpa using
    policyGraftMatchingLeafAt_subtreeAt_append
      (P := P) (u := u) (t := t) (v := v) (a := a) (c := []) hg

/--
Policy grafting below the root preserves the outer root sequent and rule
labels.  Thus the surrounding logical-rule label is not lost by the algebraic
composition.
-/
theorem policyGraftMatchingLeafAt_nonroot_preserves_root_labels
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree} {a : Address}
    (hane : a ≠ [])
    (hg : policyGraftMatchingLeafAt P u t a = some v) :
    v.conclusion = t.conclusion ∧
      v.rootRule? = t.rootRule? := by
  exact modifyAt_nonroot_preserves_root_labels t u v hane
    (modifyAt_eq_some_of_policyGraftMatchingLeafAt_eq_some hg)

theorem policyInternalGraft_has_labelled_occurrence
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree}
    (hg : PolicyInternalGraft P u t v) :
    Nonempty (PolicyGraftOccurrence P u t v) :=
  (policyInternalGraft_iff_nonempty_occurrence P u t v).1 hg

/--
For the exact policy, policy-mediated address grafting is the old
matching-leaf grafting operation.
-/
theorem exactPolicyGraftMatchingLeafAt_eq
    {base : BaseRel} (u t : PTree) (a : Address) :
    policyGraftMatchingLeafAt
        (ProofContextTree.exactInterfacePolicy base) u t a =
      PTree.graftMatchingLeafAt u t a := by
  classical
  unfold policyGraftMatchingLeafAt PTree.graftMatchingLeafAt
  cases hsub : PTree.subtreeAt t a with
  | none =>
      rfl
  | some st =>
      cases st with
      | leaf source =>
          dsimp [ProofContextTree.exactInterfacePolicy]
          by_cases hsource : source = u.conclusion
          · have htarget : u.conclusion = source := hsource.symm
            rw [if_pos hsource, if_pos htarget]
          · have htarget : u.conclusion ≠ source := by
              intro h
              exact hsource h.symm
            rw [if_neg hsource, if_neg htarget]
      | node r s cs =>
          rfl

theorem internalGraft_of_exactPolicyInternalGraft
    {base : BaseRel} {u t v : PTree}
    (hg : PolicyInternalGraft
      (ProofContextTree.exactInterfacePolicy base) u t v) :
    InternalGraft u t v := by
  rcases hg with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [← exactPolicyGraftMatchingLeafAt_eq (base := base) u t a]
  exact ha

/--
A structural/interface policy preserves the genuine proof sector when every
permitted graft of derivable proof trees is again derivable.
-/
def ProofContextTree.InterfacePolicy.PreservesDerivableGrafting
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) : Prop :=
  ∀ ⦃u t v : PTree⦄,
    DerivableTree base u →
      DerivableTree base t →
        PolicyInternalGraft P u t v →
          DerivableTree base v

/--
A structural/interface policy escapes the genuine proof sector when it licenses
a graft of genuine derivations whose result is not a genuine derivation.

This is the direct formal version of the diagnostic slogan: inadmissible
structural composition is detected by leaving the derivable sector.
-/
def ProofContextTree.InterfacePolicy.EscapesDerivableGrafting
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) : Prop :=
  ∃ u t v : PTree,
    DerivableTree base u ∧
      DerivableTree base t ∧
        PolicyInternalGraft P u t v ∧
          ¬ DerivableTree base v

theorem preservesDerivableGrafting_iff_not_escapes
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base} :
    P.PreservesDerivableGrafting ↔
      ¬ P.EscapesDerivableGrafting := by
  classical
  constructor
  · intro hP hesc
    rcases hesc with ⟨u, t, v, hu, ht, hg, hv⟩
    exact hv (hP hu ht hg)
  · intro hno u t v hu ht hg
    by_cases hv : DerivableTree base v
    · exact hv
    · exact False.elim (hno ⟨u, t, v, hu, ht, hg, hv⟩)

theorem exactInterfacePolicy_preservesDerivableGrafting
    (base : BaseRel) :
    (ProofContextTree.exactInterfacePolicy base).PreservesDerivableGrafting := by
  intro u t v hu ht hg
  exact internalGraft_preserves_derivable hu ht
    (internalGraft_of_exactPolicyInternalGraft hg)

theorem exactInterfacePolicy_no_derivableGrafting_escape
    (base : BaseRel) :
    ¬ (ProofContextTree.exactInterfacePolicy base).EscapesDerivableGrafting :=
  preservesDerivableGrafting_iff_not_escapes.1
    (exactInterfacePolicy_preservesDerivableGrafting base)

/--
For the exact policy, the policy-sensitive graft support list is exactly the
old GL matching-leaf graft support list.
-/
theorem exactPolicyMatchingLeafGraftings_eq
    {base : BaseRel} (u t : PTree) :
    policyMatchingLeafGraftings
        (ProofContextTree.exactInterfacePolicy base) u t =
      PTree.matchingLeafGraftings u t := by
  unfold policyMatchingLeafGraftings PTree.matchingLeafGraftings
  exact List.filterMap_congr (by
    intro a _ha
    exact exactPolicyGraftMatchingLeafAt_eq (base := base) u t a)

/--
Generator-level policy-sensitive graft product: sum the tree generators of all
policy-allowed grafting outputs.
-/
noncomputable def policyGraftPreLieTree
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) : PreLieCarrier :=
  (policyMatchingLeafGraftings P u t).foldr
    (fun x acc => treeGen x + acc) 0

@[simp]
theorem policyGraftPreLieTree_apply
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) :
    policyGraftPreLieTree P u t v =
      ((policyMatchingLeafGraftings P u t).count v : ℤ) := by
  simp [policyGraftPreLieTree, PTree.foldr_treeGen_apply]

theorem policyGraftPreLieTree_coeff_ne_zero_of_internalGraft
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree}
    (hg : PolicyInternalGraft P u t v) :
    policyGraftPreLieTree P u t v ≠ 0 := by
  have hmem : v ∈ policyMatchingLeafGraftings P u t :=
    (mem_policyMatchingLeafGraftings_iff P u t v).2 hg
  have hcount : (policyMatchingLeafGraftings P u t).count v ≠ 0 := by
    intro hc
    exact (List.count_eq_zero.mp hc) hmem
  have hcountInt :
      ((policyMatchingLeafGraftings P u t).count v : ℤ) ≠ 0 := by
    exact_mod_cast hcount
  simpa [policyGraftPreLieTree_apply] using hcountInt

theorem policyInternalGraft_of_policyGraftPreLieTree_coeff_ne_zero
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    {u t v : PTree}
    (hcoeff : policyGraftPreLieTree P u t v ≠ 0) :
    PolicyInternalGraft P u t v := by
  by_contra hng
  have hnotmem : v ∉ policyMatchingLeafGraftings P u t := by
    intro hmem
    exact hng ((mem_policyMatchingLeafGraftings_iff P u t v).1 hmem)
  have hcount : (policyMatchingLeafGraftings P u t).count v = 0 :=
    List.count_eq_zero.mpr hnotmem
  exact hcoeff (by simp [policyGraftPreLieTree_apply, hcount])

/--
The policy-sensitive product coefficient is nonzero exactly when there is a
policy-mediated internal graft producing that tree.
-/
theorem policyGraftPreLieTree_coeff_ne_zero_iff
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) :
    policyGraftPreLieTree P u t v ≠ 0 ↔
      PolicyInternalGraft P u t v := by
  constructor
  · exact policyInternalGraft_of_policyGraftPreLieTree_coeff_ne_zero
  · exact policyGraftPreLieTree_coeff_ne_zero_of_internalGraft

/--
The algebraic support of the policy-sensitive generator product is exactly
the proof-theoretic policy grafting relation.

This is the main representation theorem for one-step constrained composition:
`v` appears in the product of `u` with `t` precisely when the structural/base
interface policy permits grafting `u` into `t` to obtain `v`.
-/
theorem mem_support_policyGraftPreLieTree_iff
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t v : PTree) :
    v ∈ (policyGraftPreLieTree P u t).support ↔
      PolicyInternalGraft P u t v := by
  rw [Finsupp.mem_support_iff]
  exact policyGraftPreLieTree_coeff_ne_zero_iff P u t v

/-- The set of outputs licensed by a policy-sensitive graft product. -/
def PolicyGraftProductSupport
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) : Set PTree :=
  { v | PolicyInternalGraft P u t v }

theorem support_policyGraftPreLieTree_eq_policyGraftProductSupport
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) :
    { v | v ∈ (policyGraftPreLieTree P u t).support } =
      PolicyGraftProductSupport P u t := by
  ext v
  exact mem_support_policyGraftPreLieTree_iff P u t v

/--
For the exact policy, algebraic support recovers ordinary exact matching-leaf
internal grafting.
-/
theorem mem_support_exactPolicyGraftPreLieTree_iff_internalGraft
    {base : BaseRel} (u t v : PTree) :
    v ∈
        (policyGraftPreLieTree
          (ProofContextTree.exactInterfacePolicy base) u t).support ↔
      InternalGraft u t v := by
  constructor
  · intro hv
    exact internalGraft_of_exactPolicyInternalGraft
      ((mem_support_policyGraftPreLieTree_iff
        (ProofContextTree.exactInterfacePolicy base) u t v).1 hv)
  · intro hv
    exact (mem_support_policyGraftPreLieTree_iff
      (ProofContextTree.exactInterfacePolicy base) u t v).2
        (exactPolicyInternalGraft_of_InternalGraft (base := base) hv)

/--
Support-level version of admissibility: on derivable inputs, every output in
the algebraic product support is again derivable.
-/
def ProofContextTree.InterfacePolicy.SupportPreservesDerivable
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) : Prop :=
  ∀ ⦃u t v : PTree⦄,
    DerivableTree base u →
      DerivableTree base t →
        v ∈ (policyGraftPreLieTree P u t).support →
          DerivableTree base v

theorem supportPreservesDerivable_iff_preservesDerivableGrafting
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base} :
    P.SupportPreservesDerivable ↔ P.PreservesDerivableGrafting := by
  constructor
  · intro hP u t v hu ht hg
    exact hP hu ht
      ((mem_support_policyGraftPreLieTree_iff P u t v).2 hg)
  · intro hP u t v hu ht hv
    exact hP hu ht
      ((mem_support_policyGraftPreLieTree_iff P u t v).1 hv)

theorem exactInterfacePolicy_supportPreservesDerivable
    (base : BaseRel) :
    (ProofContextTree.exactInterfacePolicy base).SupportPreservesDerivable :=
  supportPreservesDerivable_iff_preservesDerivableGrafting.2
    (exactInterfacePolicy_preservesDerivableGrafting base)

/--
Algebraic version of escaping the genuine proof sector: two derivable
generators have a nonzero policy-product coefficient at a non-derivable tree.
-/
def ProofContextTree.InterfacePolicy.CoefficientEscapesDerivable
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) : Prop :=
  ∃ u t v : PTree,
    DerivableTree base u ∧
      DerivableTree base t ∧
        policyGraftPreLieTree P u t v ≠ 0 ∧
          ¬ DerivableTree base v

theorem coefficientEscapesDerivable_iff_escapesDerivableGrafting
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base} :
    P.CoefficientEscapesDerivable ↔
      P.EscapesDerivableGrafting := by
  constructor
  · intro h
    rcases h with ⟨u, t, v, hu, ht, hcoeff, hv⟩
    exact ⟨u, t, v, hu, ht,
      (policyGraftPreLieTree_coeff_ne_zero_iff P u t v).1 hcoeff, hv⟩
  · intro h
    rcases h with ⟨u, t, v, hu, ht, hg, hv⟩
    exact ⟨u, t, v, hu, ht,
      (policyGraftPreLieTree_coeff_ne_zero_iff P u t v).2 hg, hv⟩

theorem preservesDerivableGrafting_iff_no_coefficient_escape
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base} :
    P.PreservesDerivableGrafting ↔
      ¬ P.CoefficientEscapesDerivable := by
  rw [preservesDerivableGrafting_iff_not_escapes]
  exact not_congr coefficientEscapesDerivable_iff_escapesDerivableGrafting.symm

theorem exactInterfacePolicy_no_coefficient_escape
    (base : BaseRel) :
    ¬ (ProofContextTree.exactInterfacePolicy base).CoefficientEscapesDerivable :=
  preservesDerivableGrafting_iff_no_coefficient_escape.1
    (exactInterfacePolicy_preservesDerivableGrafting base)

theorem policyGraftPreLieTree_coeff_ne_zero_mono
    {base : BaseRel}
    {P Q : ProofContextTree.InterfacePolicy base}
    (hPQ : P.Extends Q)
    {u t v : PTree}
    (hcoeff : policyGraftPreLieTree Q u t v ≠ 0) :
    policyGraftPreLieTree P u t v ≠ 0 := by
  have hgQ : PolicyInternalGraft Q u t v :=
    policyInternalGraft_of_policyGraftPreLieTree_coeff_ne_zero hcoeff
  exact policyGraftPreLieTree_coeff_ne_zero_of_internalGraft
    (policyInternalGraft_mono hPQ hgQ)

/--
If a policy preserves derivable grafting, then its generator-level product
stays inside the derivable tree submodule on derivable generators.
-/
theorem policyGraftPreLieTree_mem_derivableTreeSubmodule_of_preserves
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    {u t : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t) :
    policyGraftPreLieTree P u t ∈ derivableTreeSubmodule base := by
  unfold policyGraftPreLieTree
  apply foldr_treeGen_mem_derivableTreeSubmodule
  intro v hv
  exact hP hu ht ((mem_policyMatchingLeafGraftings_iff P u t v).1 hv)

theorem exactPolicyGraftPreLieTree_mem_derivableTreeSubmodule
    {base : BaseRel} {u t : PTree}
    (hu : DerivableTree base u)
    (ht : DerivableTree base t) :
    policyGraftPreLieTree
        (ProofContextTree.exactInterfacePolicy base) u t ∈
      derivableTreeSubmodule base :=
  policyGraftPreLieTree_mem_derivableTreeSubmodule_of_preserves
    (exactInterfacePolicy_preservesDerivableGrafting base) hu ht

theorem exactPolicyGraftPreLieTree_eq
    {base : BaseRel} (u t : PTree) :
    policyGraftPreLieTree
        (ProofContextTree.exactInterfacePolicy base) u t =
      PTree.graftPreLieTree u t := by
  simp [policyGraftPreLieTree, PTree.graftPreLieTree,
    exactPolicyMatchingLeafGraftings_eq]

/-- Linear extension of policy-sensitive grafting in the right argument. -/
noncomputable def policyGraftPreLieRight
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u : PTree) : PreLieCarrier →ₗ[ℤ] PreLieCarrier :=
  Finsupp.linearCombination ℤ (fun t => policyGraftPreLieTree P u t)

/-- Bilinear extension of policy-sensitive grafting. -/
noncomputable def policyGraftPreLie
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) :
    PreLieCarrier →ₗ[ℤ] PreLieCarrier →ₗ[ℤ] PreLieCarrier :=
  Finsupp.linearCombination ℤ (policyGraftPreLieRight P)

@[simp]
theorem policyGraftPreLie_left_generator
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u : PTree) :
    policyGraftPreLie P (treeGen u) = policyGraftPreLieRight P u := by
  simp [policyGraftPreLie, treeGen]

theorem policyGraftPreLieRight_on_generator
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) :
    policyGraftPreLieRight P u (treeGen t) =
      policyGraftPreLieTree P u t := by
  simp [policyGraftPreLieRight, treeGen]

theorem policyGraftPreLie_on_generators
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (u t : PTree) :
    policyGraftPreLie P (treeGen u) (treeGen t) =
      policyGraftPreLieTree P u t := by
  simp [policyGraftPreLie, policyGraftPreLieRight, treeGen]

/--
For an admissible structural/interface policy, grafting a closed inserted proof
tree into a linear combination of closed proof trees stays in the closed
derivable sector.
-/
theorem policyGraftPreLieRight_mem_derivableTreeSubmodule_of_preserves
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    {u : PTree}
    (hu : DerivableTree base u)
    {x : PreLieCarrier}
    (hx : x ∈ derivableTreeSubmodule base) :
    policyGraftPreLieRight P u x ∈ derivableTreeSubmodule base := by
  change x ∈ Submodule.span ℤ (derivableTreeGeneratorSet base) at hx
  refine Submodule.span_induction
    (s := derivableTreeGeneratorSet base)
    (p := fun x _ => policyGraftPreLieRight P u x ∈
      derivableTreeSubmodule base)
    ?gen ?zero ?add ?smul hx
  · intro a ha
    rcases ha with ⟨t, ht, rfl⟩
    rw [policyGraftPreLieRight_on_generator]
    exact policyGraftPreLieTree_mem_derivableTreeSubmodule_of_preserves
      hP hu ht
  · simp
  · intro x y _hx _hy ihx ihy
    simpa using Submodule.add_mem (derivableTreeSubmodule base) ihx ihy
  · intro c x _hx ihx
    simpa using Submodule.smul_mem (derivableTreeSubmodule base) c ihx

/--
For an admissible structural/interface policy, the full bilinear
policy-grafting product restricts to the linear span of genuine closed proof
trees.

This is the policy-sensitive analogue of
`graftPreLie_mem_derivableTreeSubmodule`: the algebra side changes with the
chosen structural policy, but it is a genuine proof-theoretic algebra exactly
when the policy preserves derivable grafting.
-/
theorem policyGraftPreLie_mem_derivableTreeSubmodule_of_preserves
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    {x y : PreLieCarrier}
    (hx : x ∈ derivableTreeSubmodule base)
    (hy : y ∈ derivableTreeSubmodule base) :
    policyGraftPreLie P x y ∈ derivableTreeSubmodule base := by
  change x ∈ Submodule.span ℤ (derivableTreeGeneratorSet base) at hx
  refine Submodule.span_induction
    (s := derivableTreeGeneratorSet base)
    (p := fun x _ => policyGraftPreLie P x y ∈
      derivableTreeSubmodule base)
    ?gen ?zero ?add ?smul hx
  · intro a ha
    rcases ha with ⟨u, hu, rfl⟩
    rw [policyGraftPreLie_left_generator]
    exact policyGraftPreLieRight_mem_derivableTreeSubmodule_of_preserves
      hP hu hy
  · simp
  · intro x₁ x₂ _hx₁ _hx₂ ih₁ ih₂
    change policyGraftPreLie P (x₁ + x₂) y ∈ derivableTreeSubmodule base
    rw [map_add]
    exact Submodule.add_mem (derivableTreeSubmodule base) ih₁ ih₂
  · intro c x _hx ih
    change policyGraftPreLie P (c • x) y ∈ derivableTreeSubmodule base
    rw [map_smul]
    exact Submodule.smul_mem (derivableTreeSubmodule base) c ih

/--
Right policy grafting as an operation on the proof-theoretic carrier itself.
The proof argument is the structural-rule admissibility certificate.
-/
noncomputable def policyDerivableGraftPreLieRight
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (hP : P.PreservesDerivableGrafting)
    (x : DerivablePreLieCarrier base) :
    DerivablePreLieCarrier base →ₗ[ℤ] DerivablePreLieCarrier base where
  toFun y :=
    ⟨policyGraftPreLie P x.1 y.1,
      policyGraftPreLie_mem_derivableTreeSubmodule_of_preserves
        hP x.2 y.2⟩
  map_add' y z := by
    apply Subtype.ext
    simp
  map_smul' c y := by
    apply Subtype.ext
    simp

@[simp]
theorem policyDerivableGraftPreLieRight_apply_val
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    (x y : DerivablePreLieCarrier base) :
    (policyDerivableGraftPreLieRight P hP x y : PreLieCarrier) =
      policyGraftPreLie P x.1 y.1 := rfl

/--
The policy-sensitive grafting product restricted to genuine proof trees.

This is the clean carrier-level form of the slogan: a structural rule/policy
becomes an algebraic product on proof trees precisely after we prove it
preserves the derivable sector.
-/
noncomputable def policyDerivableGraftPreLie
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (hP : P.PreservesDerivableGrafting) :
    DerivablePreLieCarrier base →ₗ[ℤ]
      DerivablePreLieCarrier base →ₗ[ℤ] DerivablePreLieCarrier base where
  toFun x := policyDerivableGraftPreLieRight P hP x
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change policyGraftPreLie P (x.1 + y.1) z.1 =
      policyGraftPreLie P x.1 z.1 + policyGraftPreLie P y.1 z.1
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change policyGraftPreLie P (c • x.1) z.1 =
      c • policyGraftPreLie P x.1 z.1
    simp

@[simp]
theorem policyDerivableGraftPreLie_apply_val
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    (x y : DerivablePreLieCarrier base) :
    (policyDerivableGraftPreLie P hP x y : PreLieCarrier) =
      policyGraftPreLie P x.1 y.1 := rfl

/--
On genuine proof-tree generators, the restricted policy product computes as
the policy-sensitive grafting support sum.
-/
theorem policyDerivableGraftPreLie_treeGen
    {base : BaseRel} {P : ProofContextTree.InterfacePolicy base}
    (hP : P.PreservesDerivableGrafting)
    (u t : DerivableProofTree base) :
    (policyDerivableGraftPreLie P hP
        (derivableTreeGen u) (derivableTreeGen t) : PreLieCarrier) =
      policyGraftPreLieTree P u.1 t.1 := by
  simp only [policyDerivableGraftPreLie_apply_val, derivableTreeGen_val]
  exact policyGraftPreLie_on_generators P u.1 t.1

theorem exactPolicyGraftPreLie_on_generators
    {base : BaseRel} (u t : PTree) :
    policyGraftPreLie
        (ProofContextTree.exactInterfacePolicy base)
        (treeGen u) (treeGen t) =
      graftPreLie (treeGen u) (treeGen t) := by
  rw [policyGraftPreLie_on_generators, graftPreLie_on_generators,
    exactPolicyGraftPreLieTree_eq]

/--
Exact policy right grafting is the original right grafting map.

This lifts `exactPolicyGraftPreLieTree_eq` from individual tree pairs to the
linear right action.
-/
theorem exactPolicyGraftPreLieRight_eq
    {base : BaseRel} (u : PTree) :
    policyGraftPreLieRight
        (ProofContextTree.exactInterfacePolicy base) u =
      graftPreLieRight u := by
  apply LinearMap.ext
  intro y
  induction y using Finsupp.induction_linear with
  | zero =>
      simp [policyGraftPreLieRight, graftPreLieRight]
  | add y₁ y₂ hy₁ hy₂ =>
      rw [map_add, map_add, hy₁, hy₂]
  | single t n =>
      calc
        policyGraftPreLieRight
            (ProofContextTree.exactInterfacePolicy base) u
            (Finsupp.single t n)
            = n • policyGraftPreLieTree
                (ProofContextTree.exactInterfacePolicy base) u t := by
              simp [policyGraftPreLieRight]
        _ = n • PTree.graftPreLieTree u t := by
              rw [exactPolicyGraftPreLieTree_eq]
        _ = graftPreLieRight u (Finsupp.single t n) := by
              simp [graftPreLieRight]

/--
Exact policy grafting is the original Grossman-Larsson matching-leaf grafting
product on the whole ambient linear carrier.

The policy-sensitive layer therefore strictly extends the old exact grafting
product instead of replacing it.
-/
theorem exactPolicyGraftPreLie_eq_graftPreLie
    {base : BaseRel} :
    policyGraftPreLie
        (ProofContextTree.exactInterfacePolicy base) =
      graftPreLie := by
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero =>
      simp [policyGraftPreLie, graftPreLie]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, map_add, hx₁, hx₂]
  | single u n =>
      apply LinearMap.ext
      intro y
      calc
        (policyGraftPreLie
            (ProofContextTree.exactInterfacePolicy base)
            (Finsupp.single u n)) y
            = n • policyGraftPreLieRight
                (ProofContextTree.exactInterfacePolicy base) u y := by
              simp [policyGraftPreLie]
        _ = n • graftPreLieRight u y := by
              rw [exactPolicyGraftPreLieRight_eq]
        _ = (graftPreLie (Finsupp.single u n)) y := by
              simp [graftPreLie]

/--
On the proof-theoretic carrier, exact policy grafting is exactly the restricted
derivable grafting product already used as the OG/pre-Lie input.
-/
theorem exactPolicyDerivableGraftPreLie_eq_derivableGraftPreLie
    {base : BaseRel}
    (x y : DerivablePreLieCarrier base) :
    policyDerivableGraftPreLie
        (ProofContextTree.exactInterfacePolicy base)
        (exactInterfacePolicy_preservesDerivableGrafting base) x y =
      derivableGraftPreLie base x y := by
  apply Subtype.ext
  simpa [policyDerivableGraftPreLie_apply_val,
    derivableGraftPreLie_apply_val,
    exactPolicyGraftPreLie_eq_graftPreLie]

/--
The associator of a policy-sensitive grafting product on the derivable carrier.

This is the place where structural/interface policies can be tested
algebraically: changing the policy may change this associator even when the
ambient CK cut support is unchanged.
-/
noncomputable def policyDerivableGraftAssociator
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (hP : P.PreservesDerivableGrafting)
    (x y z : DerivablePreLieCarrier base) :
    DerivablePreLieCarrier base :=
  policyDerivableGraftPreLie P hP
      (policyDerivableGraftPreLie P hP x y) z -
    policyDerivableGraftPreLie P hP x
      (policyDerivableGraftPreLie P hP y z)

/--
Right pre-Lie symmetry for a policy-sensitive product on genuine proof trees.

For exact matching this is the old GL/OG pre-Lie law.  For stronger structural
policies, it becomes a diagnostic: does the added structural freedom preserve
the pre-Lie associator symmetry or break it?
-/
def PolicyDerivableRightPreLieLaw
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (hP : P.PreservesDerivableGrafting) : Prop :=
  ∀ x y z : DerivablePreLieCarrier base,
    policyDerivableGraftAssociator P hP x y z =
      policyDerivableGraftAssociator P hP x z y

/--
For exact matching, the policy-sensitive derivable associator is the original
restricted derivable grafting associator.
-/
theorem exactPolicyDerivableGraftAssociator_eq_derivableGraftAssociator
    {base : BaseRel}
    (x y z : DerivablePreLieCarrier base) :
    policyDerivableGraftAssociator
        (ProofContextTree.exactInterfacePolicy base)
        (exactInterfacePolicy_preservesDerivableGrafting base) x y z =
      derivableGraftAssociator base x y z := by
  unfold policyDerivableGraftAssociator derivableGraftAssociator
  rw [exactPolicyDerivableGraftPreLie_eq_derivableGraftPreLie]
  rw [exactPolicyDerivableGraftPreLie_eq_derivableGraftPreLie]
  rw [exactPolicyDerivableGraftPreLie_eq_derivableGraftPreLie]
  rw [exactPolicyDerivableGraftPreLie_eq_derivableGraftPreLie]

/--
Exact matching satisfies the policy-sensitive pre-Lie law whenever the original
restricted derivable grafting product satisfies it.
-/
theorem exactPolicyDerivableRightPreLieLaw_of_derivable
    {base : BaseRel}
    (h : DerivableRightPreLieLaw base) :
    PolicyDerivableRightPreLieLaw
      (ProofContextTree.exactInterfacePolicy base)
      (exactInterfacePolicy_preservesDerivableGrafting base) := by
  intro x y z
  rw [exactPolicyDerivableGraftAssociator_eq_derivableGraftAssociator]
  rw [exactPolicyDerivableGraftAssociator_eq_derivableGraftAssociator]
  exact h x y z

/--
One side of the policy-sensitive pre-Lie associator support:
first graft `x` into `y`, then graft the result into `z`.
-/
def PolicyAssociatorSequentialSupport
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (x y z w : PTree) : Prop :=
  ∃ y' : PTree, PolicyInternalGraft P x y y' ∧
    PolicyInternalGraft P y' z w

/--
The nested side of the policy-sensitive pre-Lie associator support:
first graft `y` into `z`, then graft `x` into the result.
-/
def PolicyAssociatorNestedSupport
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (x y z w : PTree) : Prop :=
  ∃ z' : PTree, PolicyInternalGraft P y z z' ∧
    PolicyInternalGraft P x z' w

/--
A support-level obstruction to associativity for a chosen structural policy.

This is intentionally weaker than the coefficient-level pre-Lie identity.  It
records that the structural policy creates a two-step composition on one side
without a matching two-step composition on the other side.
-/
def PolicyAssociatorSupportObstruction
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base)
    (x y z w : PTree) : Prop :=
  (PolicyAssociatorSequentialSupport P x y z w ∧
      ¬ PolicyAssociatorNestedSupport P x y z w) ∨
    (PolicyAssociatorNestedSupport P x y z w ∧
      ¬ PolicyAssociatorSequentialSupport P x y z w)

/--
Support-level right pre-Lie symmetry for a policy: any associator-support
obstruction is invariant under swapping the two inserted arguments.

The old GL/OG theorem proves the coefficient-level version for exact matching
on the stable quotient.  For stronger structural policies, this becomes a
concrete diagnostic: the algebra side may change when weakening/filling
policies change, even if the CK address coalgebra is unchanged.
-/
def PolicySupportRightPreLieSymmetric
    {base : BaseRel} (P : ProofContextTree.InterfacePolicy base) : Prop :=
  ∀ x y z w : PTree,
    PolicyAssociatorSupportObstruction P x y z w ↔
      PolicyAssociatorSupportObstruction P x z y w

/--
The root external split preserves proof-theoretic meaning in the open sector.

Starting from a closed derivable context `G` and a closed component `t`, the
root split target

`G + {t} + {leaf t.conclusion}`

is open-derivable over the singleton boundary containing `t.conclusion`.
The final leaf is an interface, not a new closed base proof.
-/
theorem root_external_split_target_openDerivableHypersequent
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hG : DerivableHypersequent base G)
    (ht : DerivableTree base t) :
    OpenDerivableHypersequent base ({t.conclusion} : Multiset MultiSequent)
      (G + HQ.singleton t + HQ.singleton (PTree.leaf t.conclusion)) := by
  apply openDerivableHypersequent_add
  · apply openDerivableHypersequent_add
    · exact openDerivableHypersequent_of_derivableHypersequent hG
    · exact openDerivableHypersequent_of_derivableHypersequent
        (derivableHypersequent_singleton ht)
  · exact openDerivableHypersequent_boundarySingleton (by simp)

/--
The previous theorem as an instance of the general split-shape assembly
principle.
-/
theorem root_external_split_target_openDerivableHypersequent_via_shape
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hG : DerivableHypersequent base G)
    (ht : DerivableTree base t) :
    OpenDerivableHypersequent base (SplitBoundary (HQ.singleton t))
      (G + HQ.singleton t + HQ.singleton (PTree.leaf t.conclusion)) := by
  exact external_split_target_openDerivable_of_shape hG
    (root_split_proofTheoreticShape ht)

/--
Root splitting is a valid minimal-NMMS external step whose target is
open-derivable over the exposed root interface.

This theorem packages the structural-rule fact with its proof-theoretic
reading.
-/
theorem nmms_root_split_step_openDerivable
    {base : BaseRel} {G : Hypersequent} {t : PTree}
    (hG : DerivableHypersequent base G)
    (ht : DerivableTree base t) :
    NMMSExternalStep
        (G + HQ.singleton t)
        (G + HQ.singleton t + HQ.singleton (PTree.leaf t.conclusion)) ∧
      OpenDerivableHypersequent base ({t.conclusion} : Multiset MultiSequent)
        (G + HQ.singleton t + HQ.singleton (PTree.leaf t.conclusion)) := by
  exact ⟨externalStep_split_root nmmsWeakeningPolicy G t,
    root_external_split_target_openDerivableHypersequent hG ht⟩

/-! ## Weakening-mediated graftability -/

/--
An internal weakening policy between sequents.

`W s target` means that a leaf labelled by `s` may be treated, for the purpose
of grafting, as an interface for a proof whose conclusion is `target`.

In NMMS this policy should usually be exact or base-controlled.  In an
ordinary monotone sequent setting it can be much freer: internal weakening can
turn a smaller leaf context into the larger context demanded by the inserted
proof.
-/
def SequentWeakeningPolicy := MultiSequent → MultiSequent → Prop

/-- Exact internal matching: no weakening-mediated change of interface. -/
def exactInternalWeakeningPolicy : SequentWeakeningPolicy :=
  fun s target => s = target

/--
Whole-sequent interface matching.

This is the current proof-tree grafting notion: the leaf sequent must be the
inserted proof's conclusion sequent, including both antecedent and succedent.
-/
def WholeSequentInterfaceMatch : SequentWeakeningPolicy :=
  exactInternalWeakeningPolicy

/--
Antecedent-side interface matching.

This is not the default grafting criterion.  It is a named probe for later
structural-rule experiments where only the left context of a leaf is relevant.
-/
def AntecedentInterfaceMatch : SequentWeakeningPolicy :=
  fun s target => s.lhs = target.lhs

/--
Succedent-side interface matching.

This is not the default grafting criterion.  It is a named probe for later
experiments where compatibility is tested on the right side of sequents.
-/
def SuccedentInterfaceMatch : SequentWeakeningPolicy :=
  fun s target => s.rhs = target.rhs

/--
Sidewise exact interface matching.

This spells out that exact sequent matching is equivalent to matching both
the antecedent multiset and the succedent multiset.
-/
def SidewiseExactInterfaceMatch : SequentWeakeningPolicy :=
  fun s target => s.lhs = target.lhs ∧ s.rhs = target.rhs

/-- Free internal weakening, modelling the structural monotone extreme. -/
def freeInternalWeakeningPolicy : SequentWeakeningPolicy :=
  fun _ _ => True

/-- A tree has a leaf labelled by some sequent at address `a`. -/
def LeafAt (t : PTree) (a : Address) : Prop :=
  ∃ s : MultiSequent, PTree.subtreeAt t a = some (PTree.leaf s)

/--
Grafting is possible at `a` after applying an internal weakening policy to the
leaf found there.

The exact NMMS grafting condition is the special case where `W` is equality.
The free monotone case is much larger: every leaf address can serve as a graft
site for every inserted proof.
-/
def WeakeningMediatedGraftableAt
    (W : SequentWeakeningPolicy) (u t : PTree) (a : Address) : Prop :=
  ∃ s : MultiSequent,
    PTree.subtreeAt t a = some (PTree.leaf s) ∧ W s u.conclusion

/-- Some address in `t` is graftable for `u` after weakening-mediated matching. -/
def WeakeningMediatedGraftable
    (W : SequentWeakeningPolicy) (u t : PTree) : Prop :=
  ∃ a : Address, WeakeningMediatedGraftableAt W u t a

@[simp]
theorem exactInternalWeakeningPolicy_apply
    (s target : MultiSequent) :
    exactInternalWeakeningPolicy s target ↔ s = target := by
  rfl

@[simp]
theorem wholeSequentInterfaceMatch_apply
    (s target : MultiSequent) :
    WholeSequentInterfaceMatch s target ↔ s = target := by
  rfl

theorem sidewiseExactInterfaceMatch_iff_eq
    (s target : MultiSequent) :
    SidewiseExactInterfaceMatch s target ↔ s = target := by
  constructor
  · intro h
    cases s
    cases target
    simp [SidewiseExactInterfaceMatch] at h ⊢
    exact h
  · intro h
    subst target
    simp [SidewiseExactInterfaceMatch]

theorem wholeSequentInterfaceMatch_implies_sides
    {s target : MultiSequent}
    (h : WholeSequentInterfaceMatch s target) :
    AntecedentInterfaceMatch s target ∧ SuccedentInterfaceMatch s target := by
  subst target
  simp [AntecedentInterfaceMatch, SuccedentInterfaceMatch]

@[simp]
theorem freeInternalWeakeningPolicy_apply
    (s target : MultiSequent) :
    freeInternalWeakeningPolicy s target := by
  trivial

/--
Exact NMMS leaf matching is precisely weakening-mediated graftability with the
exact internal policy.
-/
theorem weakeningMediatedGraftableAt_exact_iff
    (u t : PTree) (a : Address) :
    WeakeningMediatedGraftableAt exactInternalWeakeningPolicy u t a ↔
      PTree.IsGraftableLeafAt u t a := by
  constructor
  · rintro ⟨s, hs, hEq⟩
    rw [hEq] at hs
    simpa [PTree.IsGraftableLeafAt] using hs
  · intro h
    exact ⟨u.conclusion, by simpa [PTree.IsGraftableLeafAt] using h, rfl⟩

/--
Any exact graft site remains graftable under any reflexive internal weakening
policy.
-/
theorem exactGraftable_weakeningMediated_of_refl
    {W : SequentWeakeningPolicy} {u t : PTree} {a : Address}
    (hW : ∀ s : MultiSequent, W s s)
    (h : PTree.IsGraftableLeafAt u t a) :
    WeakeningMediatedGraftableAt W u t a := by
  exact ⟨u.conclusion, by simpa [PTree.IsGraftableLeafAt] using h, hW _⟩

/--
In the free monotone policy, every leaf address is a possible graft interface
for every inserted proof.
-/
theorem weakeningMediatedGraftableAt_free_of_leaf
    {u t : PTree} {a : Address}
    (h : LeafAt t a) :
    WeakeningMediatedGraftableAt freeInternalWeakeningPolicy u t a := by
  rcases h with ⟨s, hs⟩
  exact ⟨s, hs, trivial⟩

/-- Free external weakening: the structurally monotone hypersequent extreme. -/
def freeExternalWeakeningPolicy : ExternalWeakeningPolicy where
  admissible _ := True

@[simp]
theorem freeExternalWeakeningPolicy_admissible
    (t : PTree) :
    freeExternalWeakeningPolicy.admissible t := by
  trivial

/--
Under free external weakening, any component can be externally added.

This is the monotone contrast to `no_nmmsExternalWeakeningMove`: NMMS does not
license arbitrary new proof components, while a freely weakening external
structural regime does.
-/
theorem freeExternalWeakeningMove
    (G : Hypersequent) (t : PTree) :
    ExternalWeakeningMove freeExternalWeakeningPolicy
      G (G + HQ.singleton t) := by
  exact ⟨t, trivial, rfl⟩

/-! ## Chain-free CK cuts as proof decomposition -/

/--
The CK/GL admissible cuts used by the coproduct are chain-free cuts.

The underlying code stores them as lists of addresses, but membership in
`PTree.allAdmissibleCuts t` means: all addresses are valid addresses of `t`,
there are no duplicates, and no two distinct selected addresses lie on the
same root-to-leaf chain.
-/
def ChainFreeCut (t : PTree) (cut : List Address) : Prop :=
  cut ∈ PTree.allAdmissibleCuts t

theorem chainFreeCut_valid
    {t : PTree} {cut : List Address}
    (hcut : ChainFreeCut t cut) :
    ∀ a, a ∈ cut → PTree.ValidAddress t a := by
  let C : PTree.IsAdmissibleCut t :=
    PTree.isAdmissibleCut_of_mem_allAdmissibleCuts hcut
  exact C.valid

theorem chainFreeCut_nodup
    {t : PTree} {cut : List Address}
    (hcut : ChainFreeCut t cut) :
    cut.Nodup :=
  PTree.nodup_of_mem_allAdmissibleCuts hcut

/--
A chain-free cut cannot select two distinct comparable addresses.

Proof-theoretically: the coproduct decomposition is a simultaneous antichain
split, not a sequence of multiple cuts along one branch to the root.
-/
theorem chainFreeCut_antichain
    {t : PTree} {cut : List Address}
    (hcut : ChainFreeCut t cut) :
    ∀ a, a ∈ cut →
      ∀ b, b ∈ cut →
        a ≠ b → ¬ PTree.comparable a b := by
  let C : PTree.IsAdmissibleCut t :=
    PTree.isAdmissibleCut_of_mem_allAdmissibleCuts hcut
  exact C.antichain

/-! ## Boundary filling as the proof-theoretic reading of grafting -/

/--
For now, boundary filling is represented by the existing internal grafting
relation.  The name records the intended proof-theoretic reading: grafting
fills a compatible interface in an open proof context.
-/
abbrev BoundaryFill (u ctx filled : PTree) : Prop :=
  InternalGraft u ctx filled

/--
One extracted component of a split fills one boundary/interface of the
remainder.

This is only the one-step version of cut-graft reconstruction.  General
antichain splits should eventually use an iterated/folded version that fills
all exposed boundary leaves.
-/
def OneStepBoundaryFillFrom
    (Γ : Hypersequent) (ctx filled : PTree) : Prop :=
  ∃ u : PTree, u ∈ Γ ∧ BoundaryFill u ctx filled

/--
The root boundary leaf is filled by grafting back the proof it exposed.
-/
theorem boundaryFill_root
    (t : PTree) :
    BoundaryFill t (PTree.leaf t.conclusion) t := by
  unfold BoundaryFill InternalGraft
  exact ⟨[], by simp [PTree.graftMatchingLeafAt_root_of_match]⟩

/--
The root split has the expected one-step cut-graft round trip.

It exposes `t` and leaves the open context `leaf t.conclusion`; grafting `t`
back into that boundary leaf reconstructs `t`.
-/
theorem root_split_oneStepBoundaryFill
    (t : PTree) :
    OneStepBoundaryFillFrom
      (HQ.singleton t) (PTree.leaf t.conclusion) t := by
  exact ⟨t, by simp [HQ.singleton], boundaryFill_root t⟩

/--
Closed boundary filling preserves closed derivability.

This is the pre-Lie/grafting idea in its proof-theoretic form: compatible
interface filling turns a closed inserted proof and a closed host proof into a
closed proof.
-/
theorem boundaryFill_preserves_derivable
    {base : BaseRel} {u ctx filled : PTree}
    (hu : DerivableTree base u)
    (hctx : DerivableTree base ctx)
    (hfill : BoundaryFill u ctx filled) :
    DerivableTree base filled :=
  internalGraft_preserves_derivable hu hctx hfill

/-! ## Structural-rule diagnostics -/

/--
A hypersequent-level structural rule preserves the closed proof sector when it
maps closed derivable hypersequents to closed derivable hypersequents.
-/
def PreservesClosedSector
    (base : BaseRel) (R : Hypersequent → Hypersequent → Prop) : Prop :=
  ∀ ⦃G H : Hypersequent⦄,
    R G H → DerivableHypersequent base G → DerivableHypersequent base H

/--
A hypersequent-level structural rule escapes the closed proof sector when it
has a closed input but a non-closed output.

This is the diagnostic shape for inadmissible structural behavior such as
unlicensed external weakening.
-/
def EscapesClosedSector
    (base : BaseRel) (R : Hypersequent → Hypersequent → Prop) : Prop :=
  ∃ G H : Hypersequent,
    R G H ∧ DerivableHypersequent base G ∧ ¬ DerivableHypersequent base H

theorem preservesClosedSector_iff_not_escapes
    {base : BaseRel} {R : Hypersequent → Hypersequent → Prop} :
    PreservesClosedSector base R ↔ ¬ EscapesClosedSector base R := by
  classical
  constructor
  · intro hR hesc
    rcases hesc with ⟨G, H, hstep, hG, hH⟩
    exact hH (hR hstep hG)
  · intro hno G H hstep hG
    by_cases hH : DerivableHypersequent base H
    · exact hH
    · exact False.elim (hno ⟨G, H, hstep, hG, hH⟩)

/--
One proof-theoretic internal grafting step on hypersequents.

This is not arbitrary raw grafting: the inserted proof tree must be a genuine
closed derivation over the same material base.  The host component is supplied
by the input hypersequent, so its derivability is checked by the closed-sector
assumption on the input.
-/
def FixedDerivableContextualInternalGraftStep
    (base : BaseRel) (u : PTree) (G H : Hypersequent) : Prop :=
  DerivableTree base u ∧ ContextualInternalGraft u G H

def DerivableContextualInternalGraftStep
    (base : BaseRel) (G H : Hypersequent) : Prop :=
  ∃ u : PTree,
    FixedDerivableContextualInternalGraftStep base u G H

theorem fixedDerivableContextualInternalGraftStep_preservesClosedSector
    (base : BaseRel) (u : PTree) :
    PreservesClosedSector base
      (FixedDerivableContextualInternalGraftStep base u) := by
  intro G H hstep hG
  exact contextualInternalGraft_preserves_derivableHypersequent
    hstep.1 hG hstep.2

theorem fixedDerivableContextualInternalGraftStep_no_escape
    (base : BaseRel) (u : PTree) :
    ¬ EscapesClosedSector base
      (FixedDerivableContextualInternalGraftStep base u) :=
  preservesClosedSector_iff_not_escapes.1
    (fixedDerivableContextualInternalGraftStep_preservesClosedSector base u)

theorem fixedDerivableContextualInternalGraftStep_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {u : PTree} {G H : Hypersequent}
    (hstep : FixedDerivableContextualInternalGraftStep base u G H) :
    FixedDerivableContextualInternalGraftStep base' u G H := by
  exact ⟨derivableTree_mono hbase hstep.1, hstep.2⟩

theorem derivableTreeDestroyedByUpdate_blocks_fixed_internal_grafting_step
    {U : AdmissibleBaseUpdate} {base : BaseRel} {u : PTree}
    (h : DerivableTreeDestroyedByUpdate U base u) :
    ∃ base' : BaseRel,
      U base base' ∧
        DerivableTree base u ∧
          ¬ DerivableTree base' u ∧
            ∀ G H : Hypersequent,
              ¬ FixedDerivableContextualInternalGraftStep base' u G H := by
  rcases h with ⟨base', hU, hu, hnew⟩
  exact
    ⟨base', hU, hu, hnew, by
      intro G H hstep
      exact hnew hstep.1⟩

/--
Proof-theoretic internal grafting preserves the closed hypersequent sector.

This is the structural-rule diagnostic for the algebra-side grafting
operation: grafting is admissible as a hypersequent-level transformation when
the inserted tree is a genuine proof and the host hypersequent is closed.
-/
theorem derivableContextualInternalGraftStep_preservesClosedSector
    (base : BaseRel) :
    PreservesClosedSector base
      (DerivableContextualInternalGraftStep base) := by
  intro G H hstep hG
  rcases hstep with ⟨u, hu, hctx⟩
  exact contextualInternalGraft_preserves_derivableHypersequent hu hG hctx

theorem derivableContextualInternalGraftStep_no_escape
    (base : BaseRel) :
    ¬ EscapesClosedSector base
      (DerivableContextualInternalGraftStep base) :=
  preservesClosedSector_iff_not_escapes.1
    (derivableContextualInternalGraftStep_preservesClosedSector base)

theorem derivableContextualInternalGraftStep_mono_base
    {base base' : BaseRel}
    (hbase : BaseRelExtends base base')
    {G H : Hypersequent}
    (hstep : DerivableContextualInternalGraftStep base G H) :
    DerivableContextualInternalGraftStep base' G H := by
  rcases hstep with ⟨u, hu, hctx⟩
  exact ⟨u, derivableTree_mono hbase hu, hctx⟩

/--
A proof-theoretic singleton graft in an external context is an instance of the
safe fixed-inserted-proof internal grafting rule.

This is the direct algebra/proof-theory bridge: the singleton hypersequent
formulation supplies a derivable inserted proof tree, and therefore the
contextual graft is not merely ambient tree surgery but an admissible
closed-sector hypersequent step.
-/
theorem proofTheoreticSingletonHypersequentGraftingSupport_add_context_step
    {base : BaseRel} {U T V C : Hypersequent}
    (h : ProofTheoreticSingletonHypersequentGraftingSupport base U T V)
    (hC : DerivableHypersequent base C) :
    ∃ u : PTree,
      DerivableHypersequent base U ∧
        DerivableHypersequent base (C + T) ∧
          FixedDerivableContextualInternalGraftStep base u (C + T) (C + V) ∧
            DerivableHypersequent base (C + V) ∧
              HQ.conclusions (C + V) = HQ.conclusions (C + T) := by
  rcases h with ⟨u, t, v, rfl, rfl, rfl, hpt⟩
  have hg : InternalGraft u t v :=
    internalGraft_of_mem_matchingLeafGraftings hpt.2.2.1
  have hctx : ContextualInternalGraft u
      (C + HQ.singleton t) (C + HQ.singleton v) :=
    contextualInternalGraft_of_added_component C hg
  exact
    ⟨u,
      derivableHypersequent_singleton hpt.1,
      derivableHypersequent_add hC
        (derivableHypersequent_singleton hpt.2.1),
      ⟨hpt.1, hctx⟩,
      derivableHypersequent_add hC
        (derivableHypersequent_singleton hpt.2.2.2),
      contextualInternalGraft_preserves_conclusions hctx⟩

/--
Base-derivable external weakening preserves the closed sector.

This is the controlled version of external weakening: adding a component is
allowed only when the added component already carries proof provenance over
the material base.
-/
theorem baseDerivableExternalWeakening_preservesClosedSector
    (base : BaseRel) :
    PreservesClosedSector base
      (ExternalWeakeningMove (baseDerivableWeakeningPolicy base)) := by
  intro G H hW hG
  exact externalWeakeningMove_baseDerivable_preserves_derivable hG hW

theorem baseDerivableExternalWeakening_no_escape
    (base : BaseRel) :
    ¬ EscapesClosedSector base
      (ExternalWeakeningMove (baseDerivableWeakeningPolicy base)) :=
  preservesClosedSector_iff_not_escapes.1
    (baseDerivableExternalWeakening_preservesClosedSector base)

/--
The labelled external-weakening rule is closed-sector preserving under the
base-derivable policy.

The label is bookkeeping; the proof-theoretic content is still supplied by the
material admissibility predicate on the added component.
-/
theorem labelledBaseDerivableExternalWeakening_preservesClosedSector
    (base : BaseRel) :
    PreservesClosedSector base
      (LabelledExternalStep
        (baseDerivableWeakeningPolicy base)
        StructuralRuleTag.externalWeakening) := by
  intro G H hW hG
  exact
    externalWeakeningMove_baseDerivable_preserves_derivable hG
      (LabelledExternalStep.weakening_to_move hW)

theorem labelledBaseDerivableExternalWeakening_no_escape
    (base : BaseRel) :
    ¬ EscapesClosedSector base
      (LabelledExternalStep
        (baseDerivableWeakeningPolicy base)
        StructuralRuleTag.externalWeakening) :=
  preservesClosedSector_iff_not_escapes.1
    (labelledBaseDerivableExternalWeakening_preservesClosedSector base)

/--
Free external weakening escapes the closed proof sector as soon as there is a
tree that is not derivable over the current material base.

This theorem is the sharp formal contrast with the base-derivable policy:
arbitrary external weakening is exactly the operation that can add proof labels
without proof provenance.
-/
theorem freeExternalWeakening_escapesClosedSector_of_nonderivable_tree
    {base : BaseRel} {t : PTree}
    (ht : ¬ DerivableTree base t) :
    EscapesClosedSector base
      (ExternalWeakeningMove freeExternalWeakeningPolicy) := by
  refine ⟨0, HQ.singleton t, ?_, derivableHypersequent_zero base, ?_⟩
  · exact ⟨t, freeExternalWeakeningPolicy_admissible t, by simp⟩
  · intro hH
    exact ht ((derivableHypersequent_singleton_iff).1 hH)

theorem freeExternalWeakening_escapesClosedSector_iff_exists_nonderivable_tree
    {base : BaseRel} :
    EscapesClosedSector base
      (ExternalWeakeningMove freeExternalWeakeningPolicy) ↔
      ∃ t : PTree, ¬ DerivableTree base t := by
  constructor
  · intro hesc
    rcases hesc with ⟨G, H, hW, _hG, hH⟩
    rcases hW with ⟨t, _ht, rfl⟩
    refine ⟨t, ?_⟩
    intro ht
    apply hH
    exact derivableHypersequent_add _hG
      (derivableHypersequent_singleton ht)
  · rintro ⟨t, ht⟩
    exact freeExternalWeakening_escapesClosedSector_of_nonderivable_tree ht

/--
Free external weakening is the comparison policy for ordinary monotone
structural behavior.  It preserves the closed sector exactly when every
externally addable component in the move happens to be closed derivable.

Thus the policy itself is not proof-theoretically safe for NMMS; safety comes
from the output-side derivability condition.
-/
theorem freeExternalWeakening_preservesClosedSector_of_output_derivable
    {base : BaseRel} :
    PreservesClosedSector base
      (fun G H =>
        ExternalWeakeningMove freeExternalWeakeningPolicy G H ∧
          DerivableHypersequent base H) := by
  intro G H hW _hG
  exact hW.2

/--
An external split with proof-theoretic output shape preserves meaning in the
open sector: the detached pieces are closed, and the remainder is open over
their exposed boundary.
-/
theorem externalSplit_preserves_openSector_of_shape
    {base : BaseRel} {G : Hypersequent} {t : PTree} {p : Hypersequent × PTree}
    (hG : DerivableHypersequent base G)
    (_ht : DerivableTree base t)
    (hp : ProofTheoreticSplittingSupport base t p) :
    OpenDerivableHypersequent base (SplitBoundary p.1)
      (G + p.1 + HQ.singleton p.2) := by
  exact external_split_target_openDerivable_of_shape hG hp.2

end HypersequentRoute
end QuotientConnected
