import Nonmonlogics.GrossmanLarsson
import Nonmonlogics.GrossmanLarssonQuotient
import Nonmonlogics.ProofTreeCutGraftDuality

open Syntax

/-!
# Main Theorems

This file is a compressed interface to the project.

It does not reprove anything. Instead, it re-exports the definitions and
theorems that carry the mathematical story, while leaving behind the local Lean
plumbing used to build them.

The intended narrative is:

1. define the nonmonotonic proof-theoretic base and its proof trees;
2. define matching-leaf grafting on proof trees;
3. prove the structural two-step decomposition behind the pre-Lie analysis;
4. obtain the raw tree-level pre-Lie and coproduct structure;
5. pass to the quotient/canonical two-step layer to remove bureaucratic noise;
6. isolate noise from genuine residual geometry;
7. prove the class-level pre-Lie identity on quotient contribution classes.

The later proof-theoretic Hopf layer keeps that algebraic backbone but moves
the public theorem surface to the derivable, base-indexed carrier:

8. isolate actual NMMS proof trees and derivable hypersequents;
9. distinguish logical proof-tree labels from structural/interface labels;
10. treat weakening/grafting permissions schematically over an arbitrary
    material base relation;
11. package the CK cut/graft bridge, nonmonotonic structural diagnostics, and
    direct derivable UEA primitive coalgebra laws as the current main theorem.
-/

namespace MainTheorems

/-! ## Logical Base And Proof Trees

These are the proof-theoretic primitives: a base consequence relation, its
derivations, plain proof trees, and the forgetful map from derivations to proof
trees.
-/

export Syntax
  (BaseRel BaseRelExtends AdmissibleBaseUpdate monotoneBaseUpdate
   MyProp MultiSequent NMMS RuleTag PTree Forest Address
   DerivableSequent DerivableTree toTree_conclusion)

export Syntax.NMMS
  (toTree)

/-! ## Primitive Grafting Geometry

These are the proof-tree grafting operations and the main structural lemmas
governing independent versus nested two-step insertions.
-/

export Syntax.PTree
  (graftMatchingLeafAt matchingLeafGraftings)

export Syntax
  (graftMatchingLeafAt_toTree_is_toTree
   matchingLeafGraftings_toTree_are_toTree
   graftMatchingLeafAt_incomparable_commute
   two_step_graft_decomposition_full)

/-! ## Raw Tree-Level Pre-Lie And Coproduct Structure

This is the unquotiented Grossman-Larson style algebra on proof trees.
-/

export Syntax
  (treeGen graftPreLie graftPreLie_on_generators
   graftPreLie_tree_tree_apply
   graftPreLie_foldr_apply_eq_flatMap_count_right
   graftPreLie_foldr_apply_eq_flatMap_count_left
   graftPreLie_coeff_x_on_yz
   graftPreLie_coeff_xy_on_z)

export Syntax.PTree
  (graftPreLieTree coproductData coproduct_nonempty)

/-! ## Quotient And Canonical Two-Step Layer

These objects encode the quotient/canonical witness layer used to identify
bureaucratically equivalent two-step proof presentations.
-/

export _root_
  (TwoStepEquiv TwoStepQuotient codeClass SwappedTwoStepClass
   outerContributionCommute innerContributionCommute)

/-! ## Structural Repair: Noise Versus Residual Geometry

These theorems express the decisive repair of the raw witness-counting story:
quotient-trivial overlap becomes noise, the genuinely mixed residual sector
disappears, and the residual sector becomes pure and typed.
-/

export _root_
  (LeftNoiseContributionClass
   PureResidualLeftContributionClass
   PureResidualSwappedRightContributionClass
   openMixedLeftContributionClass_false
   mixedResidualLeftContributionClass_false
   residualLeftContributionClass_is_pure
   residualLeftContributionClass_has_unique_typedPureSwappedRightPartner
   residualSwappedRightContributionClass_has_pureLeftPartner)

/-! ## Class-Level Associator Shape

At the quotient level, every contribution class is decomposed into the three
sectors that matter mathematically:

- quotient-trivial noise;
- pure outer residual classes;
- pure inner residual classes.
-/

export _root_
  (ClassLevelAssociatorShape classLevelAssociatorShape
   pureOuterResidualAssociatorComparison
   pureInnerResidualAssociatorComparison
   noiseContributionClass_irrelevantForAssociator)

/-! ## Class-Level Pre-Lie Structure

These are the final quotient-level objects: the primitive class-level product,
the class-level associator, and the resulting pre-Lie identity.
-/

export _root_
  (InClassLevelProduct ClassLevelProduct
   ClassLevelPreLieComparison classLevel_preLieComparison
   ClassLevelAssociatorAt ClassLevelAssociator
   ClassLevelPreLieIdentity classLevel_preLie_identity)

/-! ## Derivable Hypersequents And Structural Labels

These are the proof-theoretic carrier refinements used by the current Hopf
main theorems.  `PTree` remains the ambient rooted-tree syntax; these names
identify the derivable sector and the structurally labelled trace layer.
-/

export QuotientConnected.HypersequentRoute
  (Hypersequent
   DerivableHypersequent DerivableProofTree DerivableProofHypersequent
   PlantedHyperforest DerivablePlantedHyperforest
   DerivableProofPlantedHyperforest
   DerivableTreeDestroyedByUpdate LogicalEntailmentDestroyedByUpdate
   StructuralRuleTag ProofStepLabel ProofTraceTree
   LabelledExternalStep ExternalWeakeningMove baseDerivableWeakeningPolicy
   freeExternalWeakeningPolicy baseDerivableExternalWeakening_no_escape
   labelledBaseDerivableExternalWeakening_no_escape SchematicProof)

export QuotientConnected.HypersequentRoute.ProofTraceTree
  (ofPTree Bplus conclusion)

export QuotientConnected.HypersequentRoute.PlantedHyperforest
  (Bplus Bminus toHypersequent toTraceTree)

export QuotientConnected.HypersequentRoute.DerivableProofPlantedHyperforest
  (Bplus toProofHypersequent mapBase)

export QuotientConnected.HypersequentRoute.LabelledExternalStep
  (toExternalStep weakening_to_move weakening_of_move
   labelled_externalWeakening_iff_move)

export QuotientConnected.HypersequentRoute.ProofContextTree
  (InterfacePolicy MaterialInterfaceSchema exactInterfacePolicy
   freeInterfacePolicy)

export QuotientConnected.HypersequentRoute.ProofContextTree.MaterialInterfaceSchema
  (toPolicy Extends exact exact_extends_exact)

export QuotientConnected.HypersequentRoute.SchematicProof
  (toTraceTree toTraceTree_conclusion derivableSequent ofNMMS
   interfaceFillStep mapBase toTraceTree_mapBase mapBaseExact
   destroyed_logical_entailment_blocks_schematic_proofs)

/-! ## Oudom-Guin Hopf Target Interface

This is the GL/OG side of the two-Hopf picture: the carrier-correct
proof-tree coalgebra, the full UEA Hopf target, and the named compatibility
obligation that remains when the carrier has been fixed.
-/

export QuotientConnected.CoproductSupport
  (OudomGuinUEAHopfCarrierTarget
   OudomGuinUEAHopfAlgebraTarget
   CompatibleStableUEAHopfData
   oudomGuinUEAHopfAlgebraTarget_exists_iff_compatible_hopf_data
   oudomGuinUEAHopfAlgebraTarget_exists_of_compatibleStableUEAHopfData
   oudomGuinUEAHopfAlgebraTarget_exists_iff_exists_compatibleStableUEAHopfData)

export QuotientConnected.CoproductSupport.OudomGuinUEAHopfAlgebraTarget
  (toCarrier toHopfData toBialgebraData ofCompatibleHopfData)

/-! ## Current Proof-Theoretic Hopf Main Theorems

These are the high-level theorem packets currently driving the project: CK
cut/graft reconstruction, nonmonotonic weakening/grafting diagnostics, the
direct derivable UEA primitive theorem, and the local addressed NMMS graft
bridge.
-/

export QuotientConnected.HypersequentRoute.CutGraftDuality
  (CutGraftDualityMarqueeTarget
   StructuralPolicyDiagnosticMarquee
   MaterialInterfaceSchemaMarquee
   NonmonotonicWeakeningGraftingMarquee
   ExactGraftingMarquee
   CompletedForestHopfSide
   OudomGuinGraftingPreLieSide
   OudomGuinGraftingCoalgebraSide
   OudomGuinGraftingHopfSide
   TwoHopfCutGraftDualityMarquee
   ProofTheoreticHopfMainResult
   DirectProofTheoreticHopfPrimitiveMainResult
   directProofTheoreticHopf_primitive_mainResult
   completed_forest_hopf_side_exists
   oudomGuin_grafting_preLie_side_exists
   oudomGuin_grafting_coalgebra_side_exists
   two_hopf_cut_graft_duality_marquee_iff_og_hopf
   two_hopf_cut_graft_duality_marquee_iff_og_target
   directProofTheoreticHopf_sequentMatching_local_hopf_bridge
   directProofTheoreticHopf_sequentMatching_local_hopf_bridge_nmms_witnesses
   directProofTheoreticHopf_nmms_address_graft_local_hopf_bridge
   directProofTheoreticHopf_nmms_address_graft_singleton_hypersequent_bridge
   directProofTheoreticHopf_nmms_address_graft_singleton_bridge_mono_base
   directProofTheoreticHopf_nmms_address_graft_base_update_diagnostic
   labelled_base_derivable_external_weakening_has_no_escape)

export QuotientConnected.HypersequentRoute.CutGraftDuality.ProofTheoreticHopfMainResult
  (completed_three_main_goals
   two_hopf_cut_graft_duality
   completed_forest_hopf_side
   og_grafting_hopf_side
   ck_cut_graft_duality
   nonmonotonic_structural_diagnostic
   schematic_material_interface_diagnostic
   schematic_proof_nonempty_after_base_extension
   destroyed_entailment_blocks_schematic_proofs
   external_weakening_contrast
   labelled_external_weakening_no_escape
   internal_grafting_contrast)

export QuotientConnected.HypersequentRoute.CutGraftDuality.DirectProofTheoreticHopfPrimitiveMainResult
  (completed_forest_hopf_side
   og_grafting_preLie_side
   og_grafting_coalgebra_side
   ck_cut_graft_duality structural_diagnostic direct_derivable_og
   schematic_material_interface_diagnostic
   schematic_proof_nonempty_after_base_extension
   destroyed_entailment_blocks_schematic_proofs
   derivable_tree_coalgebra_laws
   nmms_derivation_generator_formula
   external_weakening_contrast
   labelled_external_weakening_no_escape
   internal_grafting_contrast
   controlled_weakening_supplies_contextual_graft
   controlled_weakening_after_base_extension
   destroyed_tree_update_blocks_controlled_weakening
   decomposition_after_base_extension
   destroyed_tree_update_blocks_decomposition)

end MainTheorems

/-!
## Source Statements For Writing

This appendix is intentionally kept inside a comment block.

Its purpose is documentary: it collects the source-level statements of the
definitions and theorems re-exported above, so they can be lifted more easily
into prose without reopening the larger development files.

Proof bodies are omitted. For definitions, the actual defining equation is
included when it carries mathematical content.

```lean
inductive MyProp : Type u
| atom : Atomic → MyProp
| falsum : MyProp
| imp  : MyProp → MyProp → MyProp
| conj : MyProp → MyProp → MyProp
| disj : MyProp → MyProp → MyProp
| neg  : MyProp → MyProp

structure MultiSequent : Type u where
  lhs : Multiset MyProp
  rhs : Multiset MyProp

abbrev BaseRel := Multiset MyProp → Multiset MyProp → Prop

inductive NMMS (base : BaseRel) : MultiSequent → Type u
| baseAx {Γ Θ : Multiset MyProp} (h : base Γ Θ) :
    NMMS base (Γ ∣∼ Θ)
| imp_l  ...
| imp_r  ...
| conj_l ...
| conj_r ...
| disj_l ...
| disj_r ...
| neg_l  ...
| neg_r  ...

inductive RuleTag where
| baseAx | imp_l | imp_r | conj_l | conj_r | disj_l | disj_r | neg_l | neg_r

inductive PTree : Type where
| leaf : MultiSequent → PTree
| node : RuleTag → MultiSequent → List PTree → PTree

abbrev Forest := List PTree
abbrev Address := List Nat

def NMMS.toTree {base : BaseRel} {s : MultiSequent} (d : NMMS base s) : PTree := ...

theorem toTree_conclusion {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    (NMMS.toTree d).conclusion = s
```

```lean
def PTree.graftMatchingLeafAt (u t : PTree) (a : Address) : Option PTree :=
  match subtreeAt t a with
  | some (PTree.leaf s) =>
      if h : u.conclusion = s then
        modifyAt t a (fun _ => u)
      else
        none
  | _ => none

def PTree.matchingLeafGraftings (u t : PTree) : List PTree :=
  (allAddresses t).filterMap (graftMatchingLeafAt u t)

theorem graftMatchingLeafAt_toTree_is_toTree
    {base : BaseRel} {s_outer s_inner : MultiSequent}
    (d_outer : NMMS base s_outer)
    (d_inner : NMMS base s_inner)
    (a : Address)
    (h : d_inner.toTree.IsGraftableLeafAt d_outer.toTree a) :
    ∃ d', d_inner.toTree.graftMatchingLeafAt d_outer.toTree a = some d'.toTree

theorem matchingLeafGraftings_toTree_are_toTree
    {base : BaseRel} {s_outer s_inner : MultiSequent}
    (d_outer : NMMS base s_outer)
    (d_inner : NMMS base s_inner) (t : PTree) :
    t ∈ d_inner.toTree.matchingLeafGraftings d_outer.toTree →
      ∃ d', t = d'.toTree

theorem graftMatchingLeafAt_incomparable_commute
    (x y z : PTree) (a b : Address)
    (hb : ¬ PTree.comparable a b)
    (z₁ z₂ z₃ : PTree)
    (h1 : y.graftMatchingLeafAt z a = some z₁)
    (h2 : x.graftMatchingLeafAt z₁ b = some z₂)
    (h3 : x.graftMatchingLeafAt z b = some z₃) :
    y.graftMatchingLeafAt z₃ a = some z₂

theorem two_step_graft_decomposition_full
    (x y z : PTree) (a b : Address) (z' w : PTree)
    (hyz : y.graftMatchingLeafAt z a = some z')
    (hxz' : x.graftMatchingLeafAt z' b = some w) :
    (∃ c y', b = a ++ c ∧
        x.graftMatchingLeafAt y c = some y' ∧
        y'.graftMatchingLeafAt z a = some w)
    ∨
    (∃ z₃, ¬ PTree.comparable a b ∧
        x.graftMatchingLeafAt z b = some z₃ ∧
        y.graftMatchingLeafAt z₃ a = some w)
```

```lean
noncomputable def treeGen (t : PTree) : GLCarrier :=
  Finsupp.single t 1

noncomputable def PTree.graftPreLieTree (u t : PTree) : PreLieCarrier :=
  (matchingLeafGraftings u t).foldr (fun x acc => treeGen x + acc) 0

noncomputable def graftPreLie :
    PreLieCarrier →ₗ[ℤ] PreLieCarrier →ₗ[ℤ] PreLieCarrier := ...

theorem graftPreLie_on_generators
    (u t : PTree) :
    graftPreLie (treeGen u) (treeGen t) = PTree.graftPreLieTree u t

theorem graftPreLie_tree_tree_apply
    (u t w : PTree) :
    (graftPreLie (treeGen u)) (t.graftPreLieTree w) =
      List.foldr
        (fun z' acc => (graftPreLie (treeGen u)) (treeGen z') + acc)
        0
        (t.matchingLeafGraftings w)

theorem graftPreLie_foldr_apply_eq_flatMap_count_right
    (x w : PTree) (xs : List PTree) :
    (List.foldr
      (fun z' acc => (graftPreLie (treeGen x)) (treeGen z') + acc)
      0 xs) w
    =
    ↑(List.count w (List.flatMap (fun z' => x.matchingLeafGraftings z') xs))

theorem graftPreLie_foldr_apply_eq_flatMap_count_left
    (z w : PTree) (xs : List PTree) :
    (List.foldr
      (fun y' acc => (graftPreLie (treeGen y')) (treeGen z) + acc)
      0 xs) w
    =
    ↑(List.count w (List.flatMap (fun y' => y'.matchingLeafGraftings z) xs))

theorem graftPreLie_coeff_x_on_yz
    (x y z w : PTree) :
    ((graftPreLie (treeGen x)) (y.graftPreLieTree z)) w
    =
    ↑(List.count w
        (List.flatMap (fun z' => x.matchingLeafGraftings z')
          (y.matchingLeafGraftings z)))

theorem graftPreLie_coeff_xy_on_z
    (x y z w : PTree) :
    ((graftPreLie (x.graftPreLieTree y)) (treeGen z)) w
    =
    ↑(List.count w
        (List.flatMap (fun y' => y'.matchingLeafGraftings z)
          (x.matchingLeafGraftings y)))

def PTree.coproductData (t : PTree) : List (Forest × PTree) :=
  (allAdmissibleCuts t).map (coproductTerm t)

theorem PTree.coproduct_nonempty
    (t : PTree) :
    0 < t.coproductData.length
```

```lean
inductive TwoStepEquiv (x y z w : PTree) :
    TwoStepCode x y z w → TwoStepCode x y z w → Prop where
| refl : ∀ c, TwoStepEquiv x y z w c c
| symm : ∀ {c d}, TwoStepEquiv x y z w c d → TwoStepEquiv x y z w d c
| trans : ∀ {c d e},
    TwoStepEquiv x y z w c d →
    TwoStepEquiv x y z w d e →
    TwoStepEquiv x y z w c e
| outer_comm_outer : ...
| outer_comm_inner : ...
| outer_comm_back_outer : ...
| outer_comm_back_inner : ...

def TwoStepQuotient (x y z w : PTree) :=
  Quot (TwoStepSetoid x y z w)

def codeClass {x y z w : PTree} (c : TwoStepCode x y z w) :
    TwoStepQuotient x y z w :=
  Quot.mk _ c

inductive SwappedTwoStepClass
    (x y z w : PTree) :
    TwoStepQuotient x y z w → TwoStepQuotient y x z w → Prop where
| leftOuter  : ...
| rightOuter : ...
| inner      : ...

def outerContributionCommute
    (x y z w : PTree) :
    OuterLeftContributionClasses x y z w ≃
      SwappedRightOuterContributionClasses x y z w

def innerContributionCommute
    (x y z w : PTree) :
    LeftInnerContributionClasses x y z w ≃
      SwappedRightInnerContributionClasses x y z w
```

```lean
def LeftNoiseContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  LeftToRightOverlapNoiseClass x y z w q ∨
    RightToLeftOverlapNoiseClass x y z w q

def PureResidualLeftContributionClass
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) : Prop :=
  PureOuterResidualLeftContributionClass x y z w q ∨
    PureInnerResidualLeftContributionClass x y z w q

def PureResidualSwappedRightContributionClass
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w) : Prop :=
  OuterResidualSwappedRightContributionClass x y z w q' ∨
    InnerResidualSwappedRightContributionClass x y z w q'

theorem openMixedLeftContributionClass_false
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hOpen : OpenMixedLeftContributionClass x y z w q) :
    False

theorem mixedResidualLeftContributionClass_false
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    ¬ MixedResidualLeftContributionClass x y z w q

theorem residualLeftContributionClass_is_pure
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : ResidualLeftContributionClass x y z w q) :
    PureResidualLeftContributionClass x y z w q

theorem residualLeftContributionClass_has_unique_typedPureSwappedRightPartner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : ResidualLeftContributionClass x y z w q) :
    (∃ hs : HasLeftOuterContributionClass x y z w q,
        ∃! t : SwappedRightOuterContributionClasses x y z w,
          transportSwappedRightOuterContributionClass x y z w t = ⟨q, hs⟩ ∧
          ResidualSwappedRightContributionClass x y z w t.1)
    ∨
    (∃ hs : HasLeftInnerContributionClass x y z w q,
        ∃! t : SwappedRightInnerContributionClasses x y z w,
          transportSwappedInnerContributionClassToLeft x y z w t = ⟨q, hs⟩ ∧
          ResidualSwappedRightContributionClass x y z w t.1)

theorem residualSwappedRightContributionClass_has_pureLeftPartner
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : ResidualSwappedRightContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      PureResidualLeftContributionClass x y z w q
```

```lean
def ClassLevelAssociatorShape
    (x y z w : PTree) : Prop :=
  (∀ q : TwoStepQuotient x y z w,
      IsLeftContributionClass x y z w q →
      LeftNoiseContributionClass x y z w q ∨
        PureOuterResidualLeftContributionClass x y z w q ∨
        PureInnerResidualLeftContributionClass x y z w q)
  ∧
  (∀ q : TwoStepQuotient x y z w,
      LeftNoiseContributionClass x y z w q →
      ∃ q' : TwoStepQuotient y x z w,
        SwappedTwoStepClass x y z w q q' ∧
        SwappedRightNoiseContributionClass x y z w q')
  ∧
  (∀ q' : TwoStepQuotient y x z w,
      IsRightContributionClass x y z w q' →
      SwappedRightNoiseContributionClass x y z w q' ∨
        ∃ q : TwoStepQuotient x y z w,
          SwappedTwoStepClass x y z w q q' ∧
          PureResidualLeftContributionClass x y z w q)

theorem classLevelAssociatorShape
    (x y z w : PTree) :
    ClassLevelAssociatorShape x y z w

theorem pureOuterResidualAssociatorComparison
    (x y z w : PTree)
    (s : PureOuterResidualAssociatorLeftClasses x y z w) :
    ∃! t : SwappedRightOuterContributionClasses x y z w,
      transportSwappedRightOuterContributionClass x y z w t = ⟨s.1, s.2.2.1⟩ ∧
      ResidualSwappedRightContributionClass x y z w t.1

theorem pureInnerResidualAssociatorComparison
    (x y z w : PTree)
    (s : PureInnerResidualAssociatorLeftClasses x y z w) :
    ∃! t : SwappedRightInnerContributionClasses x y z w,
      transportSwappedInnerContributionClassToLeft x y z w t = ⟨s.1, s.2.2.1⟩ ∧
      ResidualSwappedRightContributionClass x y z w t.1

theorem noiseContributionClass_irrelevantForAssociator
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : LeftNoiseContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      SwappedRightNoiseContributionClass x y z w q'
```

```lean
def InClassLevelProduct
    (x y w : PTree) : Prop :=
  w ∈ PTree.matchingLeafGraftings x y

def ClassLevelProduct
    (x y : PTree) :=
  { w : PTree // InClassLevelProduct x y w }

def ClassLevelPreLieComparison
    (x y z w : PTree) : Prop :=
  ∀ q : TwoStepQuotient x y z w,
    IsLeftContributionClass x y z w q →
    (LeftNoiseContributionClass x y z w q ∧
      ∃ q' : TwoStepQuotient y x z w,
        SwappedTwoStepClass x y z w q q' ∧
        SwappedRightNoiseContributionClass x y z w q')
    ∨
    (∃ hOut : PureOuterResidualLeftContributionClass x y z w q,
      ∃! t : SwappedRightOuterContributionClasses x y z w,
        transportSwappedRightOuterContributionClass x y z w t = ⟨q, hOut.2.1⟩ ∧
        ResidualSwappedRightContributionClass x y z w t.1)
    ∨
    (∃ hIn : PureInnerResidualLeftContributionClass x y z w q,
      ∃! t : SwappedRightInnerContributionClasses x y z w,
        transportSwappedInnerContributionClassToLeft x y z w t = ⟨q, hIn.2.1⟩ ∧
        ResidualSwappedRightContributionClass x y z w t.1)

theorem classLevel_preLieComparison
    (x y z w : PTree) :
    ClassLevelPreLieComparison x y z w

def ClassLevelAssociatorAt
    (x y z w : PTree) : Prop :=
  ClassLevelPreLieComparison x y z w

def ClassLevelAssociator
    (x y z : PTree) : Prop :=
  ∀ w : PTree, ClassLevelAssociatorAt x y z w

def ClassLevelPreLieIdentity
    (x y z : PTree) : Prop :=
  ClassLevelAssociator x y z ∧
    ClassLevelAssociator y x z

theorem classLevel_preLie_identity
    (x y z : PTree) :
    ClassLevelPreLieIdentity x y z
```
-/

/-!
## Selected Full Lean Proof Scripts

This second appendix records the actual Lean proof terms for the most useful
high-level results. These are the parts most likely to help when rewriting the
formal development into ordinary mathematical prose.

For very long inductive proofs, the previous appendix still gives the full
statement, while this appendix focuses on the shorter proof scripts that expose
the real mathematical structure of the argument.

```lean
theorem toTree_conclusion {base : BaseRel} {s : MultiSequent}
    (d : NMMS base s) :
    (NMMS.toTree d).conclusion = s := by
  induction d <;> rfl
```

```lean
theorem PTree.coproduct_nonempty (t : PTree) :
    0 < (coproductData t).length := by
  unfold coproductData
  have hmem : ([], t) ∈ (allAdmissibleCuts t).map (coproductTerm t) := by
    apply List.mem_map.2
    refine ⟨[], empty_cut_mem_allAdmissibleCuts t, ?_⟩
    simpa [coproductTerm_nil]
  exact List.length_pos_of_mem hmem
```

```lean
noncomputable def graftPreLie :
    PreLieCarrier →ₗ[ℤ] PreLieCarrier →ₗ[ℤ] PreLieCarrier :=
  Finsupp.linearCombination ℤ graftPreLieRight

theorem graftPreLie_on_generators
    (u t : PTree) :
    graftPreLie (treeGen u) (treeGen t) = PTree.graftPreLieTree u t := by
  simp [graftPreLie, graftPreLieRight, treeGen]
```

```lean
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
```

```lean
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
```

```lean
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
```

```lean
def TwoStepQuotient (x y z w : PTree) :=
  Quot (TwoStepSetoid x y z w)

def codeClass {x y z w : PTree} (c : TwoStepCode x y z w) :
    TwoStepQuotient x y z w :=
  Quot.mk _ c
```

```lean
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

noncomputable def outerContributionCommute
    (x y z w : PTree) :
    OuterLeftContributionClasses x y z w ≃
      SwappedRightOuterContributionClasses x y z w where
  toFun := transportOuterLeftContributionClass x y z w
  invFun := transportSwappedRightOuterContributionClass x y z w
  left_inv := transportSwappedRightOuterContributionClass_left_inv x y z w
  right_inv := transportOuterLeftContributionClass_right_inv x y z w
```

```lean
theorem transportSwappedInnerContributionClassToLeft_left_inv
    (x y z w : PTree)
    (s : LeftInnerContributionClasses x y z w) :
    transportSwappedInnerContributionClassToLeft x y z w
      (transportLeftInnerContributionClassToSwapped x y z w s) = s := by
  apply Subtype.ext
  rcases s with ⟨q, hq⟩
  let h : LeftInnerFiberData x y z w q := Classical.choice hq
  let k := leftInnerFiberData_forward x y z w q h
  calc
    (transportSwappedInnerContributionClassToLeft x y z w
        (transportLeftInnerContributionClassToSwapped x y z w ⟨q, hq⟩)).1
      = (transportSwappedInnerContributionClassToLeft x y z w
          ⟨k.1, ⟨k.2⟩⟩).1 := by
            exact congrArg
              (fun t => (transportSwappedInnerContributionClassToLeft x y z w t).1)
              (transportLeftInnerContributionClassToSwapped_eq_of_witness x y z w h)
    _ = (AllSwappedRightInnerFiberData.toLeft x y z w ⟨k.1, k.2⟩).1 := by
          exact congrArg Subtype.val
            (transportSwappedInnerContributionClassToLeft_eq_of_witness x y z w k.2)
    _ = q := by
          simpa [k, AllLeftInnerFiberData.toSwapped,
            AllSwappedRightInnerFiberData.toLeft]
            using (AllLeftInnerFiberData.toSwapped_toLeft_fst x y z w ⟨q, h⟩)

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

noncomputable def innerContributionCommute
    (x y z w : PTree) :
    LeftInnerContributionClasses x y z w ≃
      SwappedRightInnerContributionClasses x y z w where
  toFun := transportLeftInnerContributionClassToSwapped x y z w
  invFun := transportSwappedInnerContributionClassToLeft x y z w
  left_inv := transportSwappedInnerContributionClassToLeft_left_inv x y z w
  right_inv := transportLeftInnerContributionClassToSwapped_right_inv x y z w
```

```lean
theorem openMixedLeftContributionClass_false
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hOpen : OpenMixedLeftContributionClass x y z w q) :
    False := by
  rcases openMixedLeftContributionClass_to_dependentOverlapRegime x y z w q hOpen with
    ⟨hDep, hNoExcl⟩
  rcases hOpen with ⟨hOut, hIn, _, _⟩
  rcases hOut with ⟨hOutW, hqOut⟩
  have hComp : OuterLeftWitnessComparable hOutW := hDep hOutW hqOut
  exact hOpen.2.2
    ⟨hOut, comparable_outerLeftWitnessClass_has_rightInnerSupport x y z w hOutW hqOut hComp⟩

theorem mixedResidualLeftContributionClass_false
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w) :
    ¬ MixedResidualLeftContributionClass x y z w q := by
  intro hMixed
  exact openMixedLeftContributionClass_false x y z w q
    ((mixedResidualLeftContributionClass_iff_openMixed x y z w q).mp hMixed)

theorem residualLeftContributionClass_is_pure
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : ResidualLeftContributionClass x y z w q) :
    PureResidualLeftContributionClass x y z w q := by
  exact residualLeftContributionClass_pure_dichotomy x y z w q hq
```

```lean
theorem residualLeftContributionClass_has_unique_typedPureSwappedRightPartner
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : ResidualLeftContributionClass x y z w q) :
    (∃ hs : HasLeftOuterContributionClass x y z w q,
        ∃! t : SwappedRightOuterContributionClasses x y z w,
          transportSwappedRightOuterContributionClass x y z w t = ⟨q, hs⟩ ∧
          ResidualSwappedRightContributionClass x y z w t.1)
    ∨
    (∃ hs : HasLeftInnerContributionClass x y z w q,
        ∃! t : SwappedRightInnerContributionClasses x y z w,
          transportSwappedInnerContributionClassToLeft x y z w t = ⟨q, hs⟩ ∧
          ResidualSwappedRightContributionClass x y z w t.1) := by
  rcases residualLeftContributionClass_pure_dichotomy x y z w q hq with hOut | hIn
  · exact Or.inl ⟨hOut.2.1,
      pureOuterResidualLeft_has_unique_outerResidualSwappedRightPartner
        x y z w q hOut⟩
  · exact Or.inr ⟨hIn.2.1,
      pureInnerResidualLeft_has_unique_innerResidualSwappedRightPartner
        x y z w q hIn⟩

theorem residualSwappedRightContributionClass_has_pureLeftPartner
    (x y z w : PTree)
    (q' : TwoStepQuotient y x z w)
    (hq' : ResidualSwappedRightContributionClass x y z w q') :
    ∃ q : TwoStepQuotient x y z w,
      SwappedTwoStepClass x y z w q q' ∧
      PureResidualLeftContributionClass x y z w q := by
  rcases ResidualSwappedRightContributionClass.exists_leftResidual x y z w q' hq' with
    ⟨q, hs, hq⟩
  exact ⟨q, hs, residualLeftContributionClass_is_pure x y z w q hq⟩
```

```lean
theorem classLevelAssociatorShape
    (x y z w : PTree) :
    ClassLevelAssociatorShape x y z w := by
  constructor
  · intro q hq
    exact leftContributionClass_noise_or_pureOuter_or_pureInner x y z w q hq
  constructor
  · intro q hq
    exact noiseLeftContributionClass_has_swappedRightNoisePartner x y z w q hq
  · intro q' hq'
    exact rightContributionClass_noise_or_has_pureLeftResidualPartner x y z w q' hq'

theorem pureOuterResidualAssociatorComparison
    (x y z w : PTree)
    (s : PureOuterResidualAssociatorLeftClasses x y z w) :
    ∃! t : SwappedRightOuterContributionClasses x y z w,
      transportSwappedRightOuterContributionClass x y z w t = ⟨s.1, s.2.2.1⟩ ∧
      ResidualSwappedRightContributionClass x y z w t.1 := by
  exact pureOuterResidualLeft_has_unique_outerResidualSwappedRightPartner
    x y z w s.1 s.2

theorem pureInnerResidualAssociatorComparison
    (x y z w : PTree)
    (s : PureInnerResidualAssociatorLeftClasses x y z w) :
    ∃! t : SwappedRightInnerContributionClasses x y z w,
      transportSwappedInnerContributionClassToLeft x y z w t = ⟨s.1, s.2.2.1⟩ ∧
      ResidualSwappedRightContributionClass x y z w t.1 := by
  exact pureInnerResidualLeft_has_unique_innerResidualSwappedRightPartner
    x y z w s.1 s.2

theorem noiseContributionClass_irrelevantForAssociator
    (x y z w : PTree)
    (q : TwoStepQuotient x y z w)
    (hq : LeftNoiseContributionClass x y z w q) :
    ∃ q' : TwoStepQuotient y x z w,
      SwappedTwoStepClass x y z w q q' ∧
      SwappedRightNoiseContributionClass x y z w q' := by
  exact noiseLeftContributionClass_has_swappedRightNoisePartner x y z w q hq
```

```lean
theorem classLevel_preLieComparison
    (x y z w : PTree) :
    ClassLevelPreLieComparison x y z w := by
  intro q hq
  rcases classLevelAssociatorShape x y z w with ⟨hleft, hnoise, _⟩
  rcases hleft q hq with hNoise | hOut | hIn
  · left
    refine ⟨hNoise, ?_⟩
    exact noiseContributionClass_irrelevantForAssociator x y z w q hNoise
  · right
    left
    refine ⟨hOut, ?_⟩
    exact pureOuterResidualAssociatorComparison x y z w ⟨q, hOut⟩
  · right
    right
    refine ⟨hIn, ?_⟩
    exact pureInnerResidualAssociatorComparison x y z w ⟨q, hIn⟩

def InClassLevelProduct
    (x y w : PTree) : Prop :=
  w ∈ PTree.matchingLeafGraftings x y

def ClassLevelProduct
    (x y : PTree) :=
  { w : PTree // InClassLevelProduct x y w }

def ClassLevelAssociatorAt
    (x y z w : PTree) : Prop :=
  ClassLevelPreLieComparison x y z w

def ClassLevelAssociator
    (x y z : PTree) : Prop :=
  ∀ w : PTree, ClassLevelAssociatorAt x y z w

def ClassLevelPreLieIdentity
    (x y z : PTree) : Prop :=
  ClassLevelAssociator x y z ∧
    ClassLevelAssociator y x z

theorem classLevel_preLie_identity
    (x y z : PTree) :
    ClassLevelPreLieIdentity x y z := by
  constructor
  · exact classLevelAssociator_spec x y z
  · exact classLevelAssociator_spec y x z
```
-/
