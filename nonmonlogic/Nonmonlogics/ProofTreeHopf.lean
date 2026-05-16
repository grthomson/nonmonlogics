import Nonmonlogics.Hypersequent

/-!
# The normalized Hopf algebra of proof-tree forests

This file is the theorem-facing entry point for the Hopf algebra constructed in
`Hypersequent.lean`.

The carrier is the free `K`-algebra on proof-tree hypersequents,

`HypersequentAlgebra K = AddMonoidAlgebra K (Multiset PTree)`.

Thus the raw proof trees `PTree` are basis generators, embedded as
`treeMonomial K t`; finite forests of proof trees are the multiplicative
hypersequent basis.
-/

noncomputable section

namespace QuotientConnected
namespace HypersequentRoute

section NormalizedProofTreeHopf

variable (K : Type) [CommRing K]
variable
  [LeftDistribClass
    (TensorProduct K (HypersequentAlgebra K) (HypersequentAlgebra K))]
variable
  [RightDistribClass
    (TensorProduct K (HypersequentAlgebra K) (HypersequentAlgebra K))]

/-- The proof-tree type used by the hypersequent construction. -/
abbrev ProofTree :=
  _root_.Syntax.PTree

/-- Ordered proof-tree forests used before quotienting to hypersequents. -/
abbrev ProofForest :=
  _root_.Syntax.Forest

/-- The algebraic carrier of the proof-tree Hopf algebra. -/
abbrev ProofTreeHopfCarrier :=
  HypersequentAlgebra K

/-- The normalized coproduct on proof-tree forests. -/
def proofTreeHopfComul :
    ProofTreeHopfCarrier K →ₗ[K]
      TensorProduct K (ProofTreeHopfCarrier K) (ProofTreeHopfCarrier K) :=
  hypersequentCoalgebraComulTensorLinearMap K

/-- The normalized counit on proof-tree forests. -/
def proofTreeHopfCounit :
    ProofTreeHopfCarrier K →ₗ[K] K :=
  (hypersequentCounitAlgHom K).toLinearMap

/-- The recursive normalized antipode on proof-tree forests. -/
def proofTreeHopfAntipode :
    ProofTreeHopfCarrier K →ₗ[K] ProofTreeHopfCarrier K :=
  HypersequentNormalizedHopfTarget.antipode K
    (normalizedHopfTarget_direct K)

/--
Main theorem: finite `K`-linear combinations of proof-tree forests carry the
normalized Connes-Kreimer/Grossman-Larson style Hopf algebra whose coproduct is
defined by admissible proof-tree cuts.
-/
noncomputable def proofTreeHopfAlgebra :
    HopfAlgebra K (ProofTreeHopfCarrier K) :=
  proofTreeNormalizedHopfAlgebra K

/-- Existence form of the main theorem. -/
theorem proofTreeHopfAlgebra_exists :
    Nonempty (HopfAlgebra K (ProofTreeHopfCarrier K)) :=
  ⟨proofTreeHopfAlgebra K⟩

/-- The normalized coproduct is coassociative. -/
theorem proofTreeHopf_coassoc :
    (TensorProduct.assoc K
        (ProofTreeHopfCarrier K)
        (ProofTreeHopfCarrier K)
        (ProofTreeHopfCarrier K)).toLinearMap ∘ₗ
        LinearMap.rTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfComul K) ∘ₗ
          proofTreeHopfComul K =
      LinearMap.lTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfComul K) ∘ₗ
        proofTreeHopfComul K := by
  exact HypersequentNormalizedHopfTarget.coassoc K
    (normalizedHopfTarget_direct K)

/-- The normalized coproduct is compatible with the right counit. -/
theorem proofTreeHopf_rightCounit :
    LinearMap.rTensor (ProofTreeHopfCarrier K)
        (proofTreeHopfCounit K) ∘ₗ
        proofTreeHopfComul K =
      (TensorProduct.mk K K (ProofTreeHopfCarrier K)) 1 := by
  exact HypersequentNormalizedHopfTarget.rightCounit K
    (normalizedHopfTarget_direct K)

/-- The normalized coproduct is compatible with the left counit. -/
theorem proofTreeHopf_leftCounit :
    LinearMap.lTensor (ProofTreeHopfCarrier K)
        (proofTreeHopfCounit K) ∘ₗ
        proofTreeHopfComul K =
      ((TensorProduct.mk K (ProofTreeHopfCarrier K) K).flip 1) := by
  exact HypersequentNormalizedHopfTarget.leftCounit K
    (normalizedHopfTarget_direct K)

/-- The normalized coproduct preserves the algebra unit. -/
theorem proofTreeHopf_comul_one :
    proofTreeHopfComul K (1 : ProofTreeHopfCarrier K) =
      (1 :
        TensorProduct K (ProofTreeHopfCarrier K) (ProofTreeHopfCarrier K)) := by
  exact (normalizedHopfTarget_direct K).bialgebraAxioms.comul_one

/-- The normalized coproduct preserves multiplication. -/
theorem proofTreeHopf_comul_mul
    (x y : ProofTreeHopfCarrier K) :
    proofTreeHopfComul K (x * y) =
      proofTreeHopfComul K x * proofTreeHopfComul K y := by
  exact HypersequentNormalizedHopfTarget.comul_mul K
    (normalizedHopfTarget_direct K) x y

/-- On hypersequent basis vectors, multiplication is external forest union. -/
@[simp]
theorem proofTreeHopf_hseq_mul_hseq
    (G H : Hypersequent) :
    (hseqMonomial K G : ProofTreeHopfCarrier K) *
        hseqMonomial K H =
      hseqMonomial K (G + H) := by
  exact hseqMonomial_mul K G H

/-- A product of two proof-tree generators is the two-component forest basis vector. -/
@[simp]
theorem proofTreeHopf_tree_mul_tree
    (s t : ProofTree) :
    (treeMonomial K s : ProofTreeHopfCarrier K) * treeMonomial K t =
      hseqMonomial K (HQ.singleton s + HQ.singleton t) := by
  exact treeMonomial_mul_treeMonomial K s t

/-- On forest basis vectors, the normalized coproduct is multiplicative. -/
theorem proofTreeHopf_comul_hseq_add
    (G H : Hypersequent) :
    proofTreeHopfComul K (hseqMonomial K (G + H)) =
      proofTreeHopfComul K (hseqMonomial K G) *
        proofTreeHopfComul K (hseqMonomial K H) := by
  rw [← hseqMonomial_mul (R := K) G H]
  exact proofTreeHopf_comul_mul K
    (hseqMonomial K G) (hseqMonomial K H)

/-- On two proof-tree generators, the normalized coproduct multiplies componentwise. -/
theorem proofTreeHopf_comul_tree_mul_tree
    (s t : ProofTree) :
    proofTreeHopfComul K (treeMonomial K s * treeMonomial K t) =
      proofTreeHopfComul K (treeMonomial K s) *
        proofTreeHopfComul K (treeMonomial K t) := by
  exact proofTreeHopf_comul_mul K (treeMonomial K s) (treeMonomial K t)

/-- The coproduct of one proof-tree generator is the cut-splitting tensor sum. -/
@[simp]
theorem proofTreeHopf_comul_tree
    (t : ProofTree) :
    proofTreeHopfComul K (treeMonomial K t) =
      hypersequentTensorAlgToTensorProductLinearMap K
        (coalgebraTreeSplittingTensorElement K t) := by
  exact hypersequentCoalgebraComulTensorLinearMap_tree K t

/-- The counit sends the empty forest/unit to `1`. -/
@[simp]
theorem proofTreeHopf_counit_one :
    proofTreeHopfCounit K (1 : ProofTreeHopfCarrier K) = 1 := by
  exact hypersequentCounitAlgHom_one K

/-- On a forest basis vector, the counit is exactly the augmentation coefficient. -/
@[simp]
theorem proofTreeHopf_counit_hseq
    (G : Hypersequent) :
    proofTreeHopfCounit K (hseqMonomial K G) =
      hypersequentCounitCoeff K G := by
  change hypersequentCounitAlgHom K (hseqMonomial K G) =
    hypersequentCounitCoeff K G
  rw [hseqMonomial]
  exact hypersequentCounitAlgHom_single K G

/-- The counit kills every nonempty forest basis vector. -/
theorem proofTreeHopf_counit_hseq_eq_zero_of_ne_zero
    {G : Hypersequent} (hG : G ≠ 0) :
    proofTreeHopfCounit K (hseqMonomial K G) = 0 := by
  rw [proofTreeHopf_counit_hseq]
  exact hypersequentCounitCoeff_eq_zero_of_not_support K hG

/-- The counit is multiplicative. -/
theorem proofTreeHopf_counit_mul
    (x y : ProofTreeHopfCarrier K) :
    proofTreeHopfCounit K (x * y) =
      proofTreeHopfCounit K x * proofTreeHopfCounit K y := by
  exact hypersequentCounitAlgHom_mul K x y

/-- A nonempty one-tree forest has counit zero. -/
@[simp]
theorem proofTreeHopf_counit_tree
    (t : ProofTree) :
    proofTreeHopfCounit K (treeMonomial K t) = 0 := by
  exact hypersequentCounitAlgHom_tree K t

/-- A nonempty ordered proof-tree forest has counit zero. -/
@[simp]
theorem proofTreeHopf_counit_ofForest_cons
    (t : ProofTree) (f : ProofForest) :
    proofTreeHopfCounit K (hseqMonomial K (HQ.ofForest (t :: f))) = 0 := by
  rw [proofTreeHopf_counit_hseq]
  exact hypersequentCounitCoeff_ofForest_cons K t f

/-- A two-component proof-tree forest also has counit zero. -/
@[simp]
theorem proofTreeHopf_counit_tree_mul_tree
    (s t : ProofTree) :
    proofTreeHopfCounit K (treeMonomial K s * treeMonomial K t) = 0 := by
  rw [proofTreeHopf_counit_mul K]
  simp [proofTreeHopf_counit_tree]

/-- The left antipode convolution is the unit-counit map. -/
theorem proofTreeHopf_left_antipode_cancellation :
    LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.lTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K =
      Algebra.linearMap K (ProofTreeHopfCarrier K) ∘ₗ
        proofTreeHopfCounit K := by
  exact normalizedHopfTarget_direct_left_cancellation K

/-- The right antipode convolution is the unit-counit map. -/
theorem proofTreeHopf_right_antipode_cancellation :
    LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.rTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K =
      Algebra.linearMap K (ProofTreeHopfCarrier K) ∘ₗ
        proofTreeHopfCounit K := by
  exact normalizedHopfTarget_direct_right_cancellation K

/-- On one proof-tree generator, the antipode is the stable cut recursion. -/
@[simp]
theorem proofTreeHopf_antipode_tree
    (t : ProofTree) :
    proofTreeHopfAntipode K (treeMonomial K t) =
      normalizedAntipodeTreeApprox K t.size t :=
  normalizedHopfTarget_direct_antipode_tree K t

/-- The public antipode is the stable tree-recursion algebra map. -/
theorem proofTreeHopf_antipode_eq_stableAlgHom :
    proofTreeHopfAntipode K =
      (normalizedStableAntipodeAlgHom K
        (normalizedStableTreeAntipodeOfSize K)).toLinearMap := by
  rfl

/-- The antipode fixes the empty forest/unit. -/
@[simp]
theorem proofTreeHopf_antipode_one :
    proofTreeHopfAntipode K (1 : ProofTreeHopfCarrier K) = 1 := by
  rw [proofTreeHopf_antipode_eq_stableAlgHom]
  exact map_one
    (normalizedStableAntipodeAlgHom K
      (normalizedStableTreeAntipodeOfSize K))

/--
The normalized antipode is multiplicative for the external forest product.
Since this Hopf algebra is commutative, this is also the usual antipode
anti-homomorphism law.
-/
theorem proofTreeHopf_antipode_mul
    (x y : ProofTreeHopfCarrier K) :
    proofTreeHopfAntipode K (x * y) =
      proofTreeHopfAntipode K x * proofTreeHopfAntipode K y := by
  rw [proofTreeHopf_antipode_eq_stableAlgHom]
  exact map_mul
    (normalizedStableAntipodeAlgHom K
      (normalizedStableTreeAntipodeOfSize K)) x y

/-- Antipode anti-multiplicativity, written in the conventional order. -/
theorem proofTreeHopf_antipode_anti_mul
    (x y : ProofTreeHopfCarrier K) :
    proofTreeHopfAntipode K (x * y) =
      proofTreeHopfAntipode K y * proofTreeHopfAntipode K x := by
  rw [proofTreeHopf_antipode_mul]
  exact mul_comm _ _

/-- On a forest basis vector, the antipode is the product of stable tree antipodes. -/
@[simp]
theorem proofTreeHopf_antipode_hseq
    (G : Hypersequent) :
    proofTreeHopfAntipode K (hseqMonomial K G) =
      normalizedStableAntipodeHypersequent K
        (normalizedStableTreeAntipodeOfSize K) G := by
  rw [proofTreeHopf_antipode_eq_stableAlgHom]
  change
    normalizedStableAntipodeAlgHom K
        (normalizedStableTreeAntipodeOfSize K) (hseqMonomial K G) =
      normalizedStableAntipodeHypersequent K
        (normalizedStableTreeAntipodeOfSize K) G
  rw [hseqMonomial]
  exact normalizedStableAntipodeAlgHom_single K
    (normalizedStableTreeAntipodeOfSize K) G

/-- On an ordered forest, the antipode is the product of the stabilized tree recursion. -/
@[simp]
theorem proofTreeHopf_antipode_ofForest
    (f : ProofForest) :
    proofTreeHopfAntipode K (hseqMonomial K (HQ.ofForest f)) =
      normalizedAntipodeForestFromTree K
        (fun t => normalizedAntipodeTreeApprox K t.size t) f := by
  rw [proofTreeHopf_antipode_eq_stableAlgHom]
  simpa [NormalizedStableTreeAntipode.value,
    normalizedStableTreeAntipodeOfSize] using
    normalizedStableAntipodeAlgHom_ofForest K
      (normalizedStableTreeAntipodeOfSize K) f

/-- On a product of two tree generators, the antipode multiplies the two stable values. -/
@[simp]
theorem proofTreeHopf_antipode_tree_mul_tree
    (s t : ProofTree) :
    proofTreeHopfAntipode K (treeMonomial K s * treeMonomial K t) =
      normalizedAntipodeTreeApprox K s.size s *
        normalizedAntipodeTreeApprox K t.size t := by
  rw [proofTreeHopf_antipode_mul]
  simp [proofTreeHopf_antipode_tree]

/-- Left antipode cancellation specialized to one proof-tree generator. -/
theorem proofTreeHopf_left_antipode_cancellation_tree
    (t : ProofTree) :
    (LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.lTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K) (treeMonomial K t) =
      (Algebra.linearMap K (ProofTreeHopfCarrier K) ∘ₗ
        proofTreeHopfCounit K) (treeMonomial K t) := by
  exact congrArg (fun f => f (treeMonomial K t))
    (proofTreeHopf_left_antipode_cancellation K)

/-- On a single proof-tree generator, the left antipode convolution vanishes. -/
@[simp]
theorem proofTreeHopf_left_antipode_cancellation_tree_eq_zero
    (t : ProofTree) :
    (LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.lTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K) (treeMonomial K t) = 0 := by
  rw [proofTreeHopf_left_antipode_cancellation_tree K t]
  change Algebra.linearMap K (ProofTreeHopfCarrier K)
      ((hypersequentCounitAlgHom K).toLinearMap (treeMonomial K t)) = 0
  rw [show
      (hypersequentCounitAlgHom K).toLinearMap (treeMonomial K t) = 0
    from hypersequentCounitAlgHom_tree K t]
  exact (Algebra.linearMap K (ProofTreeHopfCarrier K)).map_zero

/-- Right antipode cancellation specialized to one proof-tree generator. -/
theorem proofTreeHopf_right_antipode_cancellation_tree
    (t : ProofTree) :
    (LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.rTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K) (treeMonomial K t) =
      (Algebra.linearMap K (ProofTreeHopfCarrier K) ∘ₗ
        proofTreeHopfCounit K) (treeMonomial K t) := by
  exact congrArg (fun f => f (treeMonomial K t))
    (proofTreeHopf_right_antipode_cancellation K)

/-- On a single proof-tree generator, the right antipode convolution vanishes. -/
@[simp]
theorem proofTreeHopf_right_antipode_cancellation_tree_eq_zero
    (t : ProofTree) :
    (LinearMap.mul' K (ProofTreeHopfCarrier K) ∘ₗ
        LinearMap.rTensor (ProofTreeHopfCarrier K)
          (proofTreeHopfAntipode K) ∘ₗ
          proofTreeHopfComul K) (treeMonomial K t) = 0 := by
  rw [proofTreeHopf_right_antipode_cancellation_tree K t]
  change Algebra.linearMap K (ProofTreeHopfCarrier K)
      ((hypersequentCounitAlgHom K).toLinearMap (treeMonomial K t)) = 0
  rw [show
      (hypersequentCounitAlgHom K).toLinearMap (treeMonomial K t) = 0
    from hypersequentCounitAlgHom_tree K t]
  exact (Algebra.linearMap K (ProofTreeHopfCarrier K)).map_zero

end NormalizedProofTreeHopf

end HypersequentRoute
end QuotientConnected
