import Nonmonlogics.GrossmanLarsson
import Nonmonlogics.GrossmanLarssonQuotient

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
-/

namespace MainTheorems

/-! ## Logical Base And Proof Trees

These are the proof-theoretic primitives: a base consequence relation, its
derivations, plain proof trees, and the forgetful map from derivations to proof
trees.
-/

export Syntax
  (BaseRel MyProp MultiSequent NMMS RuleTag PTree Forest Address toTree_conclusion)

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

end MainTheorems
