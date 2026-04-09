import Nonmonlogics.GrossmanLarssonQuotient

open Syntax

/-!
# Connected quotient-side algebra notes

This file is intentionally conservative.

It does not attempt the full Oudom-Guin construction yet. Instead, it packages
the part of the algebraic story that is already proved in the quotient
development and keeps it visibly attached to the actual proof-tree objects.

The basic data we really have now is:

- a carrier of proof trees `PTree`,
- a one-step product support relation `InClassLevelProduct`,
- finiteness of each one-step output set,
- and a pointwise quotient-level pre-Lie comparison
  `ClassLevelAssociatorAt x y z w`.

This is the right place to stand before choosing a linear carrier or Hopf
extension.
-/

namespace QuotientConnected

/-- The one-step product support set determined by matching-leaf grafting. -/
def classLevelProductSupport (x y : PTree) : Set PTree :=
  { w | InClassLevelProduct x y w }

@[simp] theorem mem_classLevelProductSupport
    (x y w : PTree) :
    w ∈ classLevelProductSupport x y ↔ InClassLevelProduct x y w := by
  rfl

/-- The one-step output support is finite because it is represented by a list. -/
theorem classLevelProductSupport_finite
    (x y : PTree) :
    Set.Finite (classLevelProductSupport x y) := by
  classical
  refine (List.toFinset (PTree.matchingLeafGraftings x y)).finite_toSet.subset ?_
  intro w hw
  exact List.mem_toFinset.mpr (by
    simpa [classLevelProductSupport, InClassLevelProduct] using hw)

/--
Bundled form of the currently proved support-level product data on proof trees.

This is not yet a bilinear algebra. It is the proof-tree support object that
any later linearisation must respect.
-/
structure PointwisePreLieSupport where
  productSupport : PTree -> PTree -> Set PTree
  productSupport_finite : forall x y, Set.Finite (productSupport x y)
  associatorAt : PTree -> PTree -> PTree -> PTree -> Prop
  associator_law : forall x y z w, associatorAt x y z w

/-- The concrete quotient-side support object coming from the current development. -/
def proofTreePointwisePreLieSupport : PointwisePreLieSupport where
  productSupport := classLevelProductSupport
  productSupport_finite := classLevelProductSupport_finite
  associatorAt := ClassLevelAssociatorAt
  associator_law := classLevelAssociatorAt_spec

/--
The already-proved quotient theorem can be read as saying that the support-level
associator comparison holds at every output tree.
-/
theorem proofTreePointwisePreLieSupport_law
    (x y z w : PTree) :
    proofTreePointwisePreLieSupport.associatorAt x y z w := by
  exact proofTreePointwisePreLieSupport.associator_law x y z w

/--
The global class-level pre-Lie identity is exactly the pointwise support law
packaged over all outputs.
-/
theorem classLevelPreLieIdentity_from_pointwise
    (x y z : PTree) :
    ClassLevelPreLieIdentity x y z := by
  exact classLevel_preLie_identity x y z

end QuotientConnected
