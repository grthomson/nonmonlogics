import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.Quotient.Defs
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
  productSupport : PTree → PTree → Set PTree
  productSupport_finite : ∀ x y, Set.Finite (productSupport x y)
  associatorAt : PTree → PTree → PTree → PTree → Prop
  associator_law : ∀ x y z w, associatorAt x y z w

/--
Pointwise pre-Lie support data together with an additive tree grading respected
by one-step product outputs.
-/
structure WeightedPointwisePreLieSupport extends PointwisePreLieSupport where
  weight : PTree → Nat
  support_weighted :
    ∀ {x y w : PTree}, productSupport x y w → weight w = weight x + weight y

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

/--
The ambient linear carrier from the raw proof-tree development.

This is already present in `GrossmanLarsson.lean`; we record it here only to
make the bridge with the quotient-side support layer explicit.
-/
abbrev linearProofTreeCarrier := PreLieCarrier

/--
On tree generators, the support of the existing raw linear grafting product is
exactly the class-level one-step support relation.

This is the first genuine bridge to a standard Mathlib linear carrier: the raw
product on `PTree →₀ ℤ` already has the correct one-step support.
-/
theorem mem_support_graftPreLie_generators_iff
    (x y w : PTree) :
    w ∈ (graftPreLie (treeGen x) (treeGen y)).support ↔
      InClassLevelProduct x y w := by
  rw [graftPreLie_on_generators]
  constructor
  · intro hw
    have hne : PTree.graftPreLieTree x y w ≠ 0 :=
      Finsupp.mem_support_iff.mp hw
    have hcount_ne : ((PTree.matchingLeafGraftings x y).count w : ℤ) ≠ 0 := by
      simpa [PTree.graftPreLieTree, PTree.foldr_treeGen_apply] using hne
    have hcount_nat_ne : (PTree.matchingLeafGraftings x y).count w ≠ 0 := by
      exact_mod_cast hcount_ne
    by_contra hnot
    apply hcount_nat_ne
    exact List.count_eq_zero_of_not_mem hnot
  · intro hw
    have hcount_nat_ne : (PTree.matchingLeafGraftings x y).count w ≠ 0 := by
      intro hc
      exact (List.count_eq_zero.mp hc) hw
    have hcount_ne : ((PTree.matchingLeafGraftings x y).count w : ℤ) ≠ 0 := by
      exact_mod_cast hcount_nat_ne
    have hne : PTree.graftPreLieTree x y w ≠ 0 := by
      simpa [PTree.graftPreLieTree, PTree.foldr_treeGen_apply] using hcount_ne
    exact Finsupp.mem_support_iff.mpr hne

/--
Set-theoretic reformulation of the previous theorem: the support set attached
to the raw generator product is exactly the quotient-side class-level support.
-/
theorem support_graftPreLie_generators_eq_classLevelProductSupport
    (x y : PTree) :
    { w | w ∈ (graftPreLie (treeGen x) (treeGen y)).support } =
      classLevelProductSupport x y := by
  ext w
  exact mem_support_graftPreLie_generators_iff x y w

/--
The raw generator product and the quotient-side support package agree at the
level of one-step output support.

So the remaining algebraic problem is not the underlying support set, but the
correct quotient-sensitive associator law on a linear carrier.
-/
theorem raw_linear_product_support_matches_pointwise_support
    (x y : PTree) :
    { w | w ∈ (graftPreLie (treeGen x) (treeGen y)).support } =
      proofTreePointwisePreLieSupport.productSupport x y := by
  simpa [proofTreePointwisePreLieSupport] using
    support_graftPreLie_generators_eq_classLevelProductSupport x y

namespace PTree

/--
A graft-compatible weight on proof trees.

This is the grading naturally adapted to matching-leaf substitution: leaves
carry weight `0`, and every immediate child contributes its own weight together
with one extra unit for the edge by which it hangs from its parent.
-/
def graftWeight : PTree → Nat
  | PTree.leaf _ => 0
  | PTree.node _ _ cs => cs.foldr (fun t n => graftWeight t + 1 + n) 0

@[simp] theorem graftWeight_leaf (s : MultiSequent) :
    graftWeight (PTree.leaf s) = 0 := by
  simp [graftWeight]

@[simp] theorem graftWeight_node (r : RuleTag) (s : MultiSequent) (cs : List PTree) :
    graftWeight (PTree.node r s cs) =
      cs.foldr (fun t n => graftWeight t + 1 + n) 0 := by
  simp [graftWeight]

theorem replaceNth_foldr_graftWeight_add
    (cs : List PTree) (i : Nat) (new : PTree)
    (hi : i < cs.length) (k : Nat)
    (hdelta : graftWeight new = k + graftWeight (cs[i])) :
    (PTree.replaceNth cs i new).foldr (fun t n => graftWeight t + 1 + n) 0 =
      k + cs.foldr (fun t n => graftWeight t + 1 + n) 0 := by
  induction cs generalizing i with
  | nil =>
      cases hi
  | cons c cs ih =>
      cases i with
      | zero =>
          simp [PTree.replaceNth, List.foldr] at hdelta ⊢
          simp [hdelta, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      | succ i =>
          simp [PTree.replaceNth, List.foldr] at hi ⊢
          have hdelta' : graftWeight new = k + graftWeight (cs[i]) := by
            simpa using hdelta
          have ih' := ih i (by simpa using hi) hdelta'
          rw [ih']
          omega

theorem modifyAt_replaceLeaf_graftWeight
    (u t t' : PTree) (a : Address) (s : MultiSequent)
    (hleaf : PTree.subtreeAt t a = some (PTree.leaf s))
    (hmod : PTree.modifyAt t a (fun _ => u) = some t') :
    graftWeight t' = graftWeight u + graftWeight t := by
  induction a generalizing t t' with
  | nil =>
      cases t with
      | leaf s' =>
          simp [PTree.subtreeAt] at hleaf
          cases hleaf
          simp [PTree.modifyAt] at hmod
          cases hmod
          simp [graftWeight]
      | node r s' cs =>
          simp [PTree.subtreeAt] at hleaf
  | cons i rest ih =>
      cases t with
      | leaf s' =>
          simp [PTree.subtreeAt] at hleaf
      | node r s' cs =>
          by_cases hi : i < cs.length
          · simp [PTree.subtreeAt, hi] at hleaf
            simp [PTree.modifyAt, hi] at hmod
            cases hrec : PTree.modifyAt (cs[i]) rest (fun _ => u) with
            | none =>
                simp [hrec] at hmod
            | some child' =>
                simp [hrec] at hmod
                cases hmod
                have hchild :
                    graftWeight child' = graftWeight u + graftWeight (cs[i]) := by
                  exact ih (t := cs[i]) (t' := child') hleaf hrec
                have hsum :
                    (PTree.replaceNth cs i child').foldr
                        (fun t n => graftWeight t + 1 + n) 0 =
                      graftWeight u +
                        cs.foldr (fun t n => graftWeight t + 1 + n) 0 := by
                  exact replaceNth_foldr_graftWeight_add
                    cs i child' hi (graftWeight u) hchild
                simpa [graftWeight] using hsum
          · simp [PTree.subtreeAt, hi] at hleaf

/--
Successful matching-leaf grafting is additive for `graftWeight`.
-/
theorem graftMatchingLeafAt_graftWeight
    (u t t' : PTree) (a : Address)
    (h : PTree.graftMatchingLeafAt u t a = some t') :
    graftWeight t' = graftWeight u + graftWeight t := by
  unfold PTree.graftMatchingLeafAt at h
  cases hsub : PTree.subtreeAt t a with
  | none =>
      simp [hsub] at h
  | some sub =>
      cases sub with
      | leaf s =>
          by_cases hmatch : u.conclusion = s
          · simp [hsub, hmatch] at h
            exact modifyAt_replaceLeaf_graftWeight u t t' a s hsub h
          · simp [hsub, hmatch] at h
      | node r s cs =>
          simp [hsub] at h

end PTree

/-- Trees of a fixed graft-compatible weight. -/
def treesOfWeight (n : Nat) : Set PTree :=
  { t | PTree.graftWeight t = n }

/--
Every class-level one-step product output has the expected additive weight.
-/
theorem inClassLevelProduct_graftWeight
    {x y w : PTree}
    (hw : InClassLevelProduct x y w) :
    PTree.graftWeight w = PTree.graftWeight x + PTree.graftWeight y := by
  unfold InClassLevelProduct PTree.matchingLeafGraftings at hw
  rcases List.mem_filterMap.mp hw with ⟨a, _, hgraft⟩
  exact PTree.graftMatchingLeafAt_graftWeight x y w a hgraft

/--
The primitive class-level product support is concentrated in a single weight.
-/
theorem classLevelProductSupport_weighted
    (x y : PTree) :
    classLevelProductSupport x y ⊆
      treesOfWeight (PTree.graftWeight x + PTree.graftWeight y) := by
  intro w hw
  exact inClassLevelProduct_graftWeight hw

/--
The raw generator product support is concentrated in the same additive weight.
-/
theorem support_graftPreLie_generators_weighted
    (x y : PTree) :
    { w | w ∈ (graftPreLie (treeGen x) (treeGen y)).support } ⊆
      treesOfWeight (PTree.graftWeight x + PTree.graftWeight y) := by
  intro w hw
  exact inClassLevelProduct_graftWeight
    ((mem_support_graftPreLie_generators_iff x y w).mp hw)

/--
The concrete proof-tree support object already carries the graft-compatible
weight grading needed for the standard tree-algebra perspective.
-/
def proofTreeWeightedPointwisePreLieSupport : WeightedPointwisePreLieSupport where
  toPointwisePreLieSupport := proofTreePointwisePreLieSupport
  weight := PTree.graftWeight
  support_weighted := by
    intro x y w hw
    exact inClassLevelProduct_graftWeight hw

/--
Elements of the linear proof-tree carrier whose support is concentrated in a
single graft-compatible weight.

This gives the natural graded pieces suggested by the classical Hopf-algebraic
tree constructions, but on the actual proof-tree carrier used here.
-/
def supportedInWeight (n : Nat) (a : linearProofTreeCarrier) : Prop :=
  ∀ t, t ∈ a.support → PTree.graftWeight t = n

/--
The degree-`n` part of the linear proof-tree carrier.

This is the most conservative graded carrier currently justified by the formal
development: it remembers actual proof trees and imposes only a homogeneous
support condition.
-/
def weightSubmodule (n : Nat) : Submodule ℤ linearProofTreeCarrier where
  carrier := { a | supportedInWeight n a }
  zero_mem' := by
    intro t ht
    simpa using ht
  add_mem' := by
    intro a b ha hb t ht
    by_cases hta : t ∈ a.support
    · exact ha t hta
    · have htb : t ∈ b.support := by
        by_contra htb
        have ha0 : a t = 0 := by
          simpa [Finsupp.mem_support_iff] using hta
        have hb0 : b t = 0 := by
          simpa [Finsupp.mem_support_iff] using htb
        have hab0 : (a + b) t = 0 := by simp [ha0, hb0]
        exact (Finsupp.mem_support_iff.mp ht) hab0
      exact hb t htb
  smul_mem' := by
    intro z a ha t ht
    have hta : t ∈ a.support := by
      by_contra hta
      have ha0 : a t = 0 := by
        simpa [Finsupp.mem_support_iff] using hta
      have hz0 : (z • a) t = 0 := by simp [ha0]
      exact (Finsupp.mem_support_iff.mp ht) hz0
    exact ha t hta

@[simp] theorem mem_weightSubmodule
    (n : Nat) (a : linearProofTreeCarrier) :
    a ∈ weightSubmodule n ↔ supportedInWeight n a := by
  rfl

theorem treeGen_supportedInWeight
    (x : PTree) :
    supportedInWeight (PTree.graftWeight x) (treeGen x) := by
  intro t ht
  have ht' : t = x := by
    by_contra htx
    have hzero : treeGen x t = 0 := by
      simp [treeGen, htx]
    exact (Finsupp.mem_support_iff.mp ht) hzero
  simpa [ht']

theorem treeGen_mem_weightSubmodule
    (x : PTree) :
    treeGen x ∈ weightSubmodule (PTree.graftWeight x) := by
  exact treeGen_supportedInWeight x

/--
The tree generator `treeGen x`, viewed as an explicit element of its
homogeneous weight piece.
-/
noncomputable def weightedTreeGen (x : PTree) :
    weightSubmodule (PTree.graftWeight x) :=
  ⟨treeGen x, treeGen_mem_weightSubmodule x⟩

@[simp] theorem weightedTreeGen_val
    (x : PTree) :
    ((weightedTreeGen x :
      weightSubmodule (PTree.graftWeight x)) :
      linearProofTreeCarrier) = treeGen x := rfl

/--
The raw one-step grafting product on tree generators is homogeneous of the
expected additive degree.
-/
theorem graftPreLie_generators_mem_weightSubmodule
    (x y : PTree) :
    graftPreLie (treeGen x) (treeGen y) ∈
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y) := by
  intro w hw
  exact support_graftPreLie_generators_weighted x y hw

/--
The raw grafting product of two tree generators, regarded as an explicit element
of the homogeneous piece of additive graft weight.
-/
noncomputable def weightedGraftPreLieGenerators (x y : PTree) :
    weightSubmodule (PTree.graftWeight x + PTree.graftWeight y) :=
  ⟨graftPreLie (treeGen x) (treeGen y),
    graftPreLie_generators_mem_weightSubmodule x y⟩

@[simp] theorem weightedGraftPreLieGenerators_val
    (x y : PTree) :
    ((weightedGraftPreLieGenerators x y :
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y)) :
      linearProofTreeCarrier) =
      graftPreLie (treeGen x) (treeGen y) := rfl

/--
Generator-level multiplication respects the graft-compatible grading.

This is the precise graded statement currently available before any descended
quotient multiplication is installed.
-/
theorem generator_product_respects_weight
    (x y : PTree) :
    graftPreLie (treeGen x) (treeGen y) ∈
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y) := by
  exact graftPreLie_generators_mem_weightSubmodule x y

/-- Tree generators whose underlying proof tree has weight `n`. -/
def treeGensOfWeight (n : Nat) : Set linearProofTreeCarrier :=
  treeGen '' treesOfWeight n

theorem treeGen_mem_treeGensOfWeight
    {x : PTree} {n : Nat}
    (hx : PTree.graftWeight x = n) :
    treeGen x ∈ treeGensOfWeight n := by
  refine ⟨x, ?_, rfl⟩
  simpa [treesOfWeight] using hx

theorem treeGensOfWeight_subset_weightSubmodule
    (n : Nat) :
    treeGensOfWeight n ⊆ weightSubmodule n := by
  intro a ha
  rcases ha with ⟨x, hx, rfl⟩
  have hwt : PTree.graftWeight x = n := by
    simpa [treesOfWeight] using hx
  simpa [hwt] using treeGen_mem_weightSubmodule x

theorem span_treeGensOfWeight_le_weightSubmodule
    (n : Nat) :
    Submodule.span ℤ (treeGensOfWeight n) ≤ weightSubmodule n := by
  refine Submodule.span_le.mpr ?_
  exact treeGensOfWeight_subset_weightSubmodule n

theorem weightSubmodule_le_span_treeGensOfWeight
    (n : Nat) :
    weightSubmodule n ≤ Submodule.span ℤ (treeGensOfWeight n) := by
  intro a ha
  rw [← Finsupp.sum_single a]
  exact Submodule.sum_mem _ (fun t ht => by
    have hwt : PTree.graftWeight t = n := ha t (by simpa using ht)
    have hgen : treeGen t ∈ Submodule.span ℤ (treeGensOfWeight n) := by
      exact Submodule.subset_span (treeGen_mem_treeGensOfWeight hwt)
    simpa [treeGen] using
      Submodule.smul_mem (Submodule.span ℤ (treeGensOfWeight n)) (a t) hgen)

/--
The degree-`n` homogeneous piece is exactly the span of tree generators of that
degree.
-/
theorem weightSubmodule_eq_span_treeGensOfWeight
    (n : Nat) :
    weightSubmodule n = Submodule.span ℤ (treeGensOfWeight n) := by
  exact le_antisymm
    (weightSubmodule_le_span_treeGensOfWeight n)
    (span_treeGensOfWeight_le_weightSubmodule n)

/--
Generator-level weight additivity for a bilinear product on the linear proof-tree
carrier.
-/
def GeneratorWeightLaw
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    : Prop :=
  ∀ x y : PTree,
    mul (treeGen x) (treeGen y) ∈
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y)

/--
If a bilinear product is weight-additive on tree generators, then it respects
the grading on all homogeneous elements.
-/
theorem generatorWeightLaw_extends
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (hgen : GeneratorWeightLaw mul) :
    ∀ {m n : Nat} {a b : linearProofTreeCarrier},
      a ∈ weightSubmodule m →
      b ∈ weightSubmodule n →
      mul a b ∈ weightSubmodule (m + n) := by
  intro m n a b ha hb
  have ha' : a ∈ Submodule.span ℤ (treeGensOfWeight m) := by
    simpa [weightSubmodule_eq_span_treeGensOfWeight m] using ha
  have hb' : b ∈ Submodule.span ℤ (treeGensOfWeight n) := by
    simpa [weightSubmodule_eq_span_treeGensOfWeight n] using hb
  let P :
      (x : linearProofTreeCarrier) →
      (y : linearProofTreeCarrier) →
      x ∈ Submodule.span ℤ (treeGensOfWeight m) →
      y ∈ Submodule.span ℤ (treeGensOfWeight n) →
      Prop :=
    fun x y _ _ => mul x y ∈ weightSubmodule (m + n)
  change P a b ha' hb'
  refine Submodule.span_induction₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha' hb'
  · intro x y hx hy
    rcases hx with ⟨tx, htx, rfl⟩
    rcases hy with ⟨ty, hty, rfl⟩
    have htx' : PTree.graftWeight tx = m := by
      simpa [treesOfWeight] using htx
    have hty' : PTree.graftWeight ty = n := by
      simpa [treesOfWeight] using hty
    simpa [htx', hty'] using hgen tx ty
  · intro y hy
    intro t ht
    simpa using ht
  · intro x hx
    intro t ht
    simpa using ht
  · intro x y z hx hy hz hxy hyz
    simpa [P, LinearMap.map_add] using
      (weightSubmodule (m + n)).add_mem hxy hyz
  · intro x y z hx hy hz hxy hyz
    simpa [P, LinearMap.map_add] using
      (weightSubmodule (m + n)).add_mem hxy hyz
  · intro r x y hx hy hxy
    simpa [P, LinearMap.map_smul] using
      (weightSubmodule (m + n)).smul_mem r hxy
  · intro r x y hx hy hxy
    simpa [P, LinearMap.map_smul] using
      (weightSubmodule (m + n)).smul_mem r hxy

theorem graftPreLie_generatorWeightLaw :
    GeneratorWeightLaw graftPreLie := by
  intro x y
  exact graftPreLie_generators_mem_weightSubmodule x y

/--
The existing raw grafting product is graded on homogeneous elements of the
linear proof-tree carrier.
-/
theorem graftPreLie_respects_weight_everywhere
    {m n : Nat} {a b : linearProofTreeCarrier} :
    a ∈ weightSubmodule m →
    b ∈ weightSubmodule n →
    graftPreLie a b ∈ weightSubmodule (m + n) := by
  exact generatorWeightLaw_extends graftPreLie graftPreLie_generatorWeightLaw

/--
The associator attached to a bilinear product on the free abelian group on
proof trees.

This is the exact expression appearing in Mathlib's `RightPreLieRing` axiom,
but written before a multiplication has actually been installed as an instance.
-/
local notation "assoc[" mul "]" =>
  (fun a b c : linearProofTreeCarrier => mul (mul a b) c - mul a (mul b c))

@[simp] theorem bilinearAssociator_zero_left
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (b c : linearProofTreeCarrier) :
    assoc[mul] 0 b c = 0 := by
  simp

@[simp] theorem bilinearAssociator_zero_middle
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (a c : linearProofTreeCarrier) :
    assoc[mul] a 0 c = 0 := by
  simp

@[simp] theorem bilinearAssociator_zero_right
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (a b : linearProofTreeCarrier) :
    assoc[mul] a b 0 = 0 := by
  simp

theorem bilinearAssociator_add_left
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (a1 a2 b c : linearProofTreeCarrier) :
    assoc[mul] (a1 + a2) b c =
      assoc[mul] a1 b c + assoc[mul] a2 b c := by
  change mul (mul (a1 + a2) b) c - mul (a1 + a2) (mul b c) =
    (mul (mul a1 b) c - mul a1 (mul b c)) +
      (mul (mul a2 b) c - mul a2 (mul b c))
  simp only [LinearMap.map_add, LinearMap.add_apply]
  exact (sub_add_sub_comm _ _ _ _).symm

theorem bilinearAssociator_smul_left
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    assoc[mul] (n • a) b c = n • assoc[mul] a b c := by
  change mul (mul (n • a) b) c - mul (n • a) (mul b c) =
    n • (mul (mul a b) c - mul a (mul b c))
  simp only [LinearMap.map_smul, LinearMap.smul_apply]
  rw [smul_sub]

theorem bilinearAssociator_add_middle
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (a b1 b2 c : linearProofTreeCarrier) :
    assoc[mul] a (b1 + b2) c =
      assoc[mul] a b1 c + assoc[mul] a b2 c := by
  change mul (mul a (b1 + b2)) c - mul a (mul (b1 + b2) c) =
    (mul (mul a b1) c - mul a (mul b1 c)) +
      (mul (mul a b2) c - mul a (mul b2 c))
  simp only [LinearMap.map_add, LinearMap.add_apply]
  exact (sub_add_sub_comm _ _ _ _).symm

theorem bilinearAssociator_smul_middle
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    assoc[mul] a (n • b) c = n • assoc[mul] a b c := by
  change mul (mul a (n • b)) c - mul a (mul (n • b) c) =
    n • (mul (mul a b) c - mul a (mul b c))
  simp only [LinearMap.map_smul, LinearMap.smul_apply]
  rw [smul_sub]

theorem bilinearAssociator_add_right
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (a b c1 c2 : linearProofTreeCarrier) :
    assoc[mul] a b (c1 + c2) =
      assoc[mul] a b c1 + assoc[mul] a b c2 := by
  change mul (mul a b) (c1 + c2) - mul a (mul b (c1 + c2)) =
    (mul (mul a b) c1 - mul a (mul b c1)) +
      (mul (mul a b) c2 - mul a (mul b c2))
  simp only [LinearMap.map_add, LinearMap.add_apply]
  exact (sub_add_sub_comm _ _ _ _).symm

theorem bilinearAssociator_smul_right
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    assoc[mul] a b (n • c) = n • assoc[mul] a b c := by
  change mul (mul a b) (n • c) - mul a (mul b (n • c)) =
    n • (mul (mul a b) c - mul a (mul b c))
  simp only [LinearMap.map_smul, LinearMap.smul_apply]
  rw [smul_sub]

/--
Generator-level right pre-Lie law for a bilinear product on the free abelian
group on proof trees.

This is the exact bridge one needs from the quotient theorem to a Mathlib
`RightPreLieRing`: once a bilinear product on the linear carrier has been
constructed, it is enough to prove the pre-Lie identity on tree generators.
-/
def GeneratorRightPreLieLaw
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    : Prop :=
  ∀ x y z : PTree,
    assoc[mul] (treeGen x) (treeGen y) (treeGen z) =
      assoc[mul] (treeGen x) (treeGen z) (treeGen y)

/--
Any generator-level right pre-Lie law extends to the whole free abelian group
on proof trees by trilinearity.

This is the precise mathematical reason the current quotient theorem is strong
enough to support a later Mathlib `RightPreLieRing` structure, once the correct
bilinear quotient product has been defined.
-/
theorem generatorRightPreLieLaw_extends
    (mul :
      linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (hgen : GeneratorRightPreLieLaw mul) :
    ∀ a b c : linearProofTreeCarrier,
      assoc[mul] a b c = assoc[mul] a c b := by
  let P : linearProofTreeCarrier → Prop :=
    fun a => ∀ b c, assoc[mul] a b c = assoc[mul] a c b
  have hP_gen : ∀ x : PTree, P (treeGen x) := by
    intro x
    let Q : linearProofTreeCarrier → Prop :=
      fun b => ∀ c, assoc[mul] (treeGen x) b c = assoc[mul] (treeGen x) c b
    have hQ_gen : ∀ y : PTree, Q (treeGen y) := by
      intro y
      let R : linearProofTreeCarrier → Prop :=
        fun c => assoc[mul] (treeGen x) (treeGen y) c = assoc[mul] (treeGen x) c (treeGen y)
      have hR_gen : ∀ z : PTree, R (treeGen z) := by
        intro z
        simpa [R] using hgen x y z
      have hR : ∀ c : linearProofTreeCarrier, R c := by
        intro c
        refine Finsupp.induction_linear c ?_ ?_ ?_
        · simp [R]
        · intro c1 c2 hc1 hc2
          change assoc[mul] (treeGen x) (treeGen y) (c1 + c2) =
              assoc[mul] (treeGen x) (c1 + c2) (treeGen y)
          rw [bilinearAssociator_add_right, bilinearAssociator_add_middle, hc1, hc2]
        · intro z n
          have hz : R (n • treeGen z) := by
            change assoc[mul] (treeGen x) (treeGen y) (n • treeGen z) =
                assoc[mul] (treeGen x) (n • treeGen z) (treeGen y)
            rw [bilinearAssociator_smul_right, bilinearAssociator_smul_middle]
            exact congrArg (fun t => n • t) (hR_gen z)
          simpa [treeGen] using hz
      exact hR
    have hQ : ∀ b : linearProofTreeCarrier, Q b := by
      intro b
      refine Finsupp.induction_linear b ?_ ?_ ?_
      · simp [Q]
      · intro b1 b2 hb1 hb2
        intro c
        change assoc[mul] (treeGen x) (b1 + b2) c =
            assoc[mul] (treeGen x) c (b1 + b2)
        rw [bilinearAssociator_add_middle, hb1 c, hb2 c, bilinearAssociator_add_right]
      · intro y n
        have hy : Q (treeGen y) := hQ_gen y
        have hyn : Q (n • treeGen y) := by
          intro c
          change assoc[mul] (treeGen x) (n • treeGen y) c =
              assoc[mul] (treeGen x) c (n • treeGen y)
          rw [bilinearAssociator_smul_middle, bilinearAssociator_smul_right]
          exact congrArg (fun t => n • t) (hy c)
        simpa [treeGen] using hyn
    exact hQ
  have hP : ∀ a : linearProofTreeCarrier, P a := by
    intro a
    refine Finsupp.induction_linear a ?_ ?_ ?_
    · simp [P]
    · intro a1 a2 ha1 ha2
      intro b c
      change assoc[mul] (a1 + a2) b c = assoc[mul] (a1 + a2) c b
      rw [bilinearAssociator_add_left, ha1 b c, ha2 b c, bilinearAssociator_add_left]
    · intro x n
      have hx : P (treeGen x) := hP_gen x
      have hxn : P (n • treeGen x) := by
        intro b c
        change assoc[mul] (n • treeGen x) b c = assoc[mul] (n • treeGen x) c b
        rw [bilinearAssociator_smul_left, bilinearAssociator_smul_left]
        exact congrArg (fun t => n • t) (hx b c)
      simpa [treeGen] using hxn
  exact hP

/--
Bundled form of the exact algebraic datum now needed for the next stage.

To proceed from the quotient theorem to a Mathlib pre-Lie structure, we still
need a bilinear product on the existing linear carrier whose generator-level
associator matches the quotient law.
-/
structure GeneratorCompatibleTreeProduct where
  mul :
    linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier
  rightPreLie_on_generators : GeneratorRightPreLieLaw mul

/--
Any generator-compatible tree product satisfies the full right pre-Lie axiom on
the linear proof-tree carrier.

This is exactly the `assoc_symm'` field one would use to instantiate
Mathlib's `RightPreLieRing`, once the multiplication itself has been installed
as the carrier multiplication.
-/
theorem GeneratorCompatibleTreeProduct.rightPreLie_everywhere
    (p : GeneratorCompatibleTreeProduct) :
    ∀ a b c : linearProofTreeCarrier,
      assoc[p.mul] a b c = assoc[p.mul] a c b := by
  exact generatorRightPreLieLaw_extends p.mul p.rightPreLie_on_generators

/--
Bundled form of the graded pre-Lie input now supported by the existing
proof-tree development.

Such an object is not yet a full Hopf algebra or even a descended quotient
product, but it records exactly the two generator-level facts that the later
Mathlib packaging will need:

- right pre-Lie symmetry on tree generators;
- additive compatibility with the graft-compatible grading on tree generators.
-/
structure GeneratorCompatibleWeightedTreeProduct extends GeneratorCompatibleTreeProduct where
  weight_on_generators : GeneratorWeightLaw mul

/--
Any generator-compatible weighted tree product is right pre-Lie on the whole
linear proof-tree carrier.
-/
theorem GeneratorCompatibleWeightedTreeProduct.rightPreLie_everywhere
    (p : GeneratorCompatibleWeightedTreeProduct) :
    ∀ a b c : linearProofTreeCarrier,
      assoc[p.mul] a b c = assoc[p.mul] a c b := by
  exact generatorRightPreLieLaw_extends p.mul p.rightPreLie_on_generators

/--
Any generator-compatible weighted tree product respects the grading on all
homogeneous elements of the linear proof-tree carrier.
-/
theorem GeneratorCompatibleWeightedTreeProduct.respects_weight_everywhere
    (p : GeneratorCompatibleWeightedTreeProduct) :
    ∀ {m n : Nat} {a b : linearProofTreeCarrier},
      a ∈ weightSubmodule m →
      b ∈ weightSubmodule n →
      p.mul a b ∈ weightSubmodule (m + n) := by
  exact generatorWeightLaw_extends p.mul p.weight_on_generators

/--
Any generator-compatible weighted tree product therefore carries the full
graded pre-Lie package on the ambient linear proof-tree carrier.

This is exactly the level of abstraction appropriate at the current stage:
the quotient-side development gives the generator laws, while this file shows
how those laws automatically extend to the full linear carrier once the correct
bilinear product has been supplied.
-/
theorem GeneratorCompatibleWeightedTreeProduct.full_package
    (p : GeneratorCompatibleWeightedTreeProduct) :
    (∀ a b c : linearProofTreeCarrier,
      assoc[p.mul] a b c = assoc[p.mul] a c b) ∧
    (∀ {m n : Nat} {a b : linearProofTreeCarrier},
      a ∈ weightSubmodule m →
      b ∈ weightSubmodule n →
      p.mul a b ∈ weightSubmodule (m + n)) := by
  constructor
  · exact p.rightPreLie_everywhere
  · exact p.respects_weight_everywhere

/--
The minimal graded linear-algebra package needed before any pre-Lie theorem is
installed: a bilinear product on the linear proof-tree carrier which respects
the graft-compatible grading.

This is the right level for the existing raw grafting product, whose graded
behavior is already proved even though the trusted pre-Lie theorem presently
lives on the quotient side.
-/
structure WeightedLinearProduct where
  mul :
    linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier
  respectsWeight :
    ∀ {m n : Nat} {a b : linearProofTreeCarrier},
      a ∈ weightSubmodule m →
      b ∈ weightSubmodule n →
      mul a b ∈ weightSubmodule (m + n)

/--
The existing raw grafting product on the free `ℤ`-module of proof trees,
packaged only with the grading information that has already been established.
-/
noncomputable def graftWeightedLinearProduct : WeightedLinearProduct where
  mul := graftPreLie
  respectsWeight := graftPreLie_respects_weight_everywhere

namespace WeightedLinearProduct

/--
The multiplication of a graded linear product restricts to a bilinear map
between the homogeneous weight pieces.
-/
def weightPieceMul
    (p : WeightedLinearProduct) (m n : Nat) :
    weightSubmodule m →ₗ[ℤ] weightSubmodule n →ₗ[ℤ] weightSubmodule (m + n) where
  toFun a :=
    { toFun := fun b => ⟨p.mul a.1 b.1, p.respectsWeight a.2 b.2⟩
      map_add' := by
        intro b1 b2
        apply Subtype.ext
        ext t
        simp [LinearMap.map_add]
      map_smul' := by
        intro z b
        apply Subtype.ext
        ext t
        simp [LinearMap.map_smul]
    }
  map_add' := by
    intro a1 a2
    ext b t
    simp [LinearMap.map_add]
  map_smul' := by
    intro z a
    ext b t
    simp [LinearMap.map_smul]

@[simp] theorem weightPieceMul_apply
    (p : WeightedLinearProduct) (m n : Nat)
    (a : weightSubmodule m) (b : weightSubmodule n) :
    ((p.weightPieceMul m n a b : weightSubmodule (m + n)) :
      linearProofTreeCarrier) = p.mul a.1 b.1 := rfl

end WeightedLinearProduct

/--
The graded raw grafting product on homogeneous pieces of the proof-tree
carrier.
-/
noncomputable def graftWeightPieceMul (m n : Nat) :
    weightSubmodule m →ₗ[ℤ] weightSubmodule n →ₗ[ℤ] weightSubmodule (m + n) :=
  (graftWeightedLinearProduct.weightPieceMul m n)

@[simp] theorem graftWeightPieceMul_apply
    (m n : Nat) (a : weightSubmodule m) (b : weightSubmodule n) :
    ((graftWeightPieceMul m n a b : weightSubmodule (m + n)) :
      linearProofTreeCarrier) = graftPreLie a.1 b.1 := rfl

@[simp] theorem graftWeightPieceMul_weightedTreeGen
    (x y : PTree) :
    graftWeightPieceMul (PTree.graftWeight x) (PTree.graftWeight y)
      (weightedTreeGen x) (weightedTreeGen y) =
    weightedGraftPreLieGenerators x y := by
  apply Subtype.ext
  rfl

@[simp] theorem support_graftWeightPieceMul_weightedTreeGen_iff
    (x y w : PTree) :
    w ∈ (((graftWeightPieceMul (PTree.graftWeight x) (PTree.graftWeight y)
      (weightedTreeGen x) (weightedTreeGen y) :
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y)) :
      linearProofTreeCarrier).support) ↔
      InClassLevelProduct x y w := by
  change w ∈ (graftPreLie (treeGen x) (treeGen y)).support ↔
      InClassLevelProduct x y w
  exact mem_support_graftPreLie_generators_iff x y w

/--
The finite set of output proof trees appearing in the raw generator product of
`x` and `y`, viewed through the graded multiplication on homogeneous pieces.
-/
noncomputable def graftGeneratorOutputs (x y : PTree) : Finset PTree :=
  (((graftWeightPieceMul (PTree.graftWeight x) (PTree.graftWeight y)
    (weightedTreeGen x) (weightedTreeGen y) :
    weightSubmodule (PTree.graftWeight x + PTree.graftWeight y)) :
    linearProofTreeCarrier).support)

@[simp] theorem mem_graftGeneratorOutputs_iff
    (x y w : PTree) :
    w ∈ graftGeneratorOutputs x y ↔ InClassLevelProduct x y w := by
  exact support_graftWeightPieceMul_weightedTreeGen_iff x y w

@[simp] theorem mem_graftGeneratorOutputs_iff_matchingLeafGraftings
    (x y w : PTree) :
    w ∈ graftGeneratorOutputs x y ↔ w ∈ PTree.matchingLeafGraftings x y := by
  simp [InClassLevelProduct]

theorem mem_graftGeneratorOutputs_weight
    {x y w : PTree}
    (hw : w ∈ graftGeneratorOutputs x y) :
    PTree.graftWeight w = PTree.graftWeight x + PTree.graftWeight y := by
  exact inClassLevelProduct_graftWeight
    ((mem_graftGeneratorOutputs_iff x y w).mp hw)

/--
The coefficient of an output tree in the raw generator product is exactly the
number of matching-leaf graftings producing it.
-/
theorem graftPreLie_generators_apply_eq_count
    (x y w : PTree) :
    graftPreLie (treeGen x) (treeGen y) w =
      ((PTree.matchingLeafGraftings x y).count w : ℤ) := by
  rw [graftPreLie_on_generators]
  rw [PTree.graftPreLieTree]
  exact PTree.foldr_treeGen_apply (PTree.matchingLeafGraftings x y) w

/--
An output tree appears in the graded raw generator product exactly when it
occurs with nonzero multiplicity in the matching-leaf grafting list.
-/
@[simp] theorem mem_graftGeneratorOutputs_iff_count_ne_zero
    (x y w : PTree) :
    w ∈ graftGeneratorOutputs x y ↔
      ((PTree.matchingLeafGraftings x y).count w : ℤ) ≠ 0 := by
  rw [mem_graftGeneratorOutputs_iff_matchingLeafGraftings]
  constructor
  · intro hw
    have hpos : 0 < (PTree.matchingLeafGraftings x y).count w := by
      exact List.count_pos_iff.mpr hw
    have hnat : (PTree.matchingLeafGraftings x y).count w ≠ 0 := Nat.ne_of_gt hpos
    exact_mod_cast hnat
  · intro hcount
    by_contra hnot
    have hzero : (PTree.matchingLeafGraftings x y).count w = 0 := by
      exact List.count_eq_zero_of_not_mem hnot
    exact hcount (by exact_mod_cast hzero)

/--
The finite output support of the left bracketing `x ▷ (y ▷ z)` on tree
generators.
-/
noncomputable def leftBracketingGeneratorOutputs
    (x y z : PTree) : Finset PTree :=
  (graftPreLie (treeGen x) (PTree.graftPreLieTree y z)).support

/--
The finite output support of the right bracketing `(x ▷ y) ▷ z` on tree
generators.
-/
noncomputable def rightBracketingGeneratorOutputs
    (x y z : PTree) : Finset PTree :=
  (graftPreLie (PTree.graftPreLieTree x y) (treeGen z)).support

/--
Coefficient formula for the left bracketing `x ▷ (y ▷ z)` on tree generators.
-/
theorem leftBracketingGenerator_apply_eq_count
    (x y z w : PTree) :
    (graftPreLie (treeGen x) (PTree.graftPreLieTree y z)) w =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : Nat) : ℤ) := by
  exact graftPreLie_coeff_x_on_yz x y z w

/--
Coefficient formula for the right bracketing `(x ▷ y) ▷ z` on tree generators.
-/
theorem rightBracketingGenerator_apply_eq_count
    (x y z w : PTree) :
    (graftPreLie (PTree.graftPreLieTree x y) (treeGen z)) w =
      ((((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) : ℤ) := by
  exact graftPreLie_coeff_xy_on_z x y z w

@[simp] theorem mem_leftBracketingGeneratorOutputs_iff_count_ne_zero
    (x y z w : PTree) :
    w ∈ leftBracketingGeneratorOutputs x y z ↔
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : Nat) : ℤ) ≠ 0 := by
  rw [leftBracketingGeneratorOutputs, Finsupp.mem_support_iff,
    leftBracketingGenerator_apply_eq_count]

@[simp] theorem mem_rightBracketingGeneratorOutputs_iff_count_ne_zero
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs x y z ↔
      ((((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) : ℤ) ≠ 0 := by
  rw [rightBracketingGeneratorOutputs, Finsupp.mem_support_iff,
    rightBracketingGenerator_apply_eq_count]

@[simp] theorem mem_leftBracketingGeneratorOutputs_iff_exists
    (x y z w : PTree) :
    w ∈ leftBracketingGeneratorOutputs x y z ↔
      ∃ z', z' ∈ PTree.matchingLeafGraftings y z ∧
        w ∈ PTree.matchingLeafGraftings x z' := by
  rw [mem_leftBracketingGeneratorOutputs_iff_count_ne_zero]
  constructor
  · intro hcount
    have hnat :
        (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : Nat) ≠ 0 := by
      intro hzero
      exact hcount (by exact_mod_cast hzero)
    have hpos :
        0 < ((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w := Nat.pos_of_ne_zero hnat
    have hmem :
        w ∈ (PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z') := by
      exact List.count_pos_iff.mp hpos
    simpa only [List.mem_flatMap]
      using hmem
  · rintro ⟨z', hz', hw⟩
    have hmem :
        w ∈ (PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z') := by
      simpa only [List.mem_flatMap] using ⟨z', hz', hw⟩
    have hpos :
        0 < ((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w := by
      exact List.count_pos_iff.mpr hmem
    exact_mod_cast (Nat.ne_of_gt hpos)

@[simp] theorem mem_rightBracketingGeneratorOutputs_iff_exists
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs x y z ↔
      ∃ y', y' ∈ PTree.matchingLeafGraftings x y ∧
        w ∈ PTree.matchingLeafGraftings y' z := by
  rw [mem_rightBracketingGeneratorOutputs_iff_count_ne_zero]
  constructor
  · intro hcount
    have hnat :
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) ≠ 0 := by
      intro hzero
      exact hcount (by exact_mod_cast hzero)
    have hpos :
        0 < ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w := Nat.pos_of_ne_zero hnat
    have hmem :
        w ∈ (PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z) := by
      exact List.count_pos_iff.mp hpos
    simpa only [List.mem_flatMap]
      using hmem
  · rintro ⟨y', hy', hw⟩
    have hmem :
        w ∈ (PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z) := by
      simpa only [List.mem_flatMap] using ⟨y', hy', hw⟩
    have hpos :
        0 < ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w := by
      exact List.count_pos_iff.mpr hmem
    exact_mod_cast (Nat.ne_of_gt hpos)

theorem mem_leftBracketingGeneratorOutputs_weight
    {x y z w : PTree}
    (hw : w ∈ leftBracketingGeneratorOutputs x y z) :
    PTree.graftWeight w =
      PTree.graftWeight x + (PTree.graftWeight y + PTree.graftWeight z) := by
  rcases (mem_leftBracketingGeneratorOutputs_iff_exists x y z w).mp hw with
    ⟨z', hz', hw'⟩
  calc
    PTree.graftWeight w = PTree.graftWeight x + PTree.graftWeight z' := by
      exact inClassLevelProduct_graftWeight hw'
    _ = PTree.graftWeight x + (PTree.graftWeight y + PTree.graftWeight z) := by
      rw [inClassLevelProduct_graftWeight hz']

theorem mem_rightBracketingGeneratorOutputs_weight
    {x y z w : PTree}
    (hw : w ∈ rightBracketingGeneratorOutputs x y z) :
    PTree.graftWeight w =
      (PTree.graftWeight x + PTree.graftWeight y) + PTree.graftWeight z := by
  rcases (mem_rightBracketingGeneratorOutputs_iff_exists x y z w).mp hw with
    ⟨y', hy', hw'⟩
  calc
    PTree.graftWeight w = PTree.graftWeight y' + PTree.graftWeight z := by
      exact inClassLevelProduct_graftWeight hw'
    _ = (PTree.graftWeight x + PTree.graftWeight y) + PTree.graftWeight z := by
      rw [inClassLevelProduct_graftWeight hy']

/--
The finite raw support of the left bracketing `x ▷ (y ▷ z)` is exactly the
outer-left witness sector of the quotient analysis.
-/
@[simp] theorem mem_leftBracketingGeneratorOutputs_iff_nonempty_outerLeftWitness
    (x y z w : PTree) :
    w ∈ leftBracketingGeneratorOutputs x y z ↔
      Nonempty (OuterLeftWitness x y z w) := by
  constructor
  · intro hw
    rcases (mem_leftBracketingGeneratorOutputs_iff_exists x y z w).mp hw with
      ⟨z', hz', hw'⟩
    rw [← map_snd_matchingLeafGraftWitnesses] at hz' hw'
    simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hw'
    rcases hz' with ⟨a, haz⟩
    rcases hw' with ⟨b, hbw⟩
    exact ⟨OuterLeftWitness.mk a b z' haz hbw⟩
  · intro hw
    rcases hw with ⟨h⟩
    cases h with
    | mk a b z' haz hbw =>
        apply (mem_leftBracketingGeneratorOutputs_iff_exists x y z w).2
        refine ⟨z', ?_, ?_⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩

/--
The finite raw support of the right bracketing `(x ▷ y) ▷ z` is exactly the
right-inner witness sector of the quotient analysis.
-/
@[simp] theorem mem_rightBracketingGeneratorOutputs_iff_nonempty_rightInnerWitnessData
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs x y z ↔
      Nonempty (RightInnerWitnessData x y z w) := by
  constructor
  · intro hw
    rcases (mem_rightBracketingGeneratorOutputs_iff_exists x y z w).mp hw with
      ⟨y', hy', hw'⟩
    rw [← map_snd_matchingLeafGraftWitnesses] at hy' hw'
    simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hy' hw'
    rcases hy' with ⟨a, hay⟩
    rcases hw' with ⟨b, hbw⟩
    exact ⟨⟨TwoStepWitnessRight.inner a b y' hay hbw, trivial⟩⟩
  · intro hw
    rcases hw with ⟨h⟩
    rcases h with ⟨h, hh⟩
    cases h with
    | inner a b y' hay hbw =>
        apply (mem_rightBracketingGeneratorOutputs_iff_exists x y z w).2
        refine ⟨y', ?_, ?_⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩
    | outer =>
        cases hh

/--
An output tree occurs in the concrete left bracketing iff it supports some
left outer contribution class in the quotient analysis.
-/
@[simp] theorem mem_leftBracketingGeneratorOutputs_iff_exists_leftOuterContributionClass
    (x y z w : PTree) :
    w ∈ leftBracketingGeneratorOutputs x y z ↔
      ∃ q : TwoStepQuotient x y z w,
        HasLeftOuterContributionClass x y z w q := by
  rw [mem_leftBracketingGeneratorOutputs_iff_nonempty_outerLeftWitness]
  constructor
  · intro hw
    rcases hw with ⟨h⟩
    exact ⟨outerLeftWitnessClass h, ⟨h, rfl⟩⟩
  · rintro ⟨q, hq⟩
    rcases hq with ⟨h, _⟩
    exact ⟨h⟩

/--
An output tree occurs in the concrete right bracketing iff it supports some
right inner contribution class in the quotient analysis.
-/
@[simp] theorem mem_rightBracketingGeneratorOutputs_iff_exists_rightInnerContributionClass
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs x y z ↔
      ∃ q : TwoStepQuotient x y z w,
        HasRightInnerContributionClass x y z w q := by
  rw [mem_rightBracketingGeneratorOutputs_iff_nonempty_rightInnerWitnessData]
  constructor
  · intro hw
    rcases hw with ⟨h⟩
    exact ⟨rightInnerWitnessClass x y z w h, ⟨⟨h, rfl⟩⟩⟩
  · rintro ⟨q, hq⟩
    rcases hq with ⟨h, _⟩
    exact ⟨h⟩

/--
If an output tree occurs in both two-step raw bracketings, then the quotient
identifies both occurrences with one common contribution class.
-/
theorem twoStepGeneratorOutput_overlap_has_commonContributionClass
    (x y z w : PTree)
    (hL : w ∈ leftBracketingGeneratorOutputs x y z)
    (hR : w ∈ rightBracketingGeneratorOutputs x y z) :
    ∃ q : TwoStepQuotient x y z w,
      HasLeftOuterContributionClass x y z w q ∧
      HasRightInnerContributionClass x y z w q := by
  rcases (mem_leftBracketingGeneratorOutputs_iff_exists_leftOuterContributionClass
      x y z w).mp hL with ⟨qL, hqL⟩
  rcases (mem_rightBracketingGeneratorOutputs_iff_exists_rightInnerContributionClass
      x y z w).mp hR with ⟨qR, hqR⟩
  have hEq : qL = qR := by
    exact HasLeftOuterContributionClass.eq_rightInnerContributionClass
      x y z w qL qR hqL hqR
  exact ⟨qL, hqL, by simpa [hEq] using hqR⟩

/--
The concrete right bracketing on swapped inputs is exactly the raw left-inner
witness sector for `(x,y,z,w)`.
-/
@[simp] theorem mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_leftInnerWitnessData
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs y x z ↔
      Nonempty (LeftInnerWitnessData x y z w) := by
  constructor
  · intro hw
    rcases (mem_rightBracketingGeneratorOutputs_iff_exists y x z w).mp hw with
      ⟨y', hy', hw'⟩
    rw [← map_snd_matchingLeafGraftWitnesses] at hy' hw'
    simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hy' hw'
    rcases hy' with ⟨a, hay⟩
    rcases hw' with ⟨b, hbw⟩
    exact ⟨⟨TwoStepWitnessLeft.inner a b y' hay hbw, trivial⟩⟩
  · intro hw
    rcases hw with ⟨h⟩
    rcases h with ⟨h, hh⟩
    cases h with
    | inner a b y' hay hbw =>
        apply (mem_rightBracketingGeneratorOutputs_iff_exists y x z w).2
        refine ⟨y', ?_, ?_⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩
    | outer =>
        cases hh

/--
The concrete left bracketing is exactly the swapped right-outer witness sector
appearing in the quotient comparison.
-/
@[simp] theorem mem_leftBracketingGeneratorOutputs_iff_nonempty_swappedRightOuterWitness
    (x y z w : PTree) :
    w ∈ leftBracketingGeneratorOutputs x y z ↔
      Nonempty (OuterRightWitness y x z w) := by
  constructor
  · intro hw
    rcases (mem_leftBracketingGeneratorOutputs_iff_exists x y z w).mp hw with
      ⟨z', hz', hw'⟩
    rw [← map_snd_matchingLeafGraftWitnesses] at hz' hw'
    simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hz' hw'
    rcases hz' with ⟨a, haz⟩
    rcases hw' with ⟨b, hbw⟩
    exact ⟨OuterRightWitness.mk a b z' haz hbw⟩
  · intro hw
    rcases hw with ⟨h⟩
    cases h with
    | mk a b z' haz hbw =>
        apply (mem_leftBracketingGeneratorOutputs_iff_exists x y z w).2
        refine ⟨z', ?_, ?_⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩

/--
The concrete right bracketing on swapped inputs is exactly the swapped
right-inner witness sector from the quotient comparison.
-/
@[simp] theorem mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_swappedRightInnerWitnessData
    (x y z w : PTree) :
    w ∈ rightBracketingGeneratorOutputs y x z ↔
      Nonempty (SwappedRightInnerWitnessData x y z w) := by
  constructor
  · intro hw
    rcases (mem_rightBracketingGeneratorOutputs_iff_exists y x z w).mp hw with
      ⟨y', hy', hw'⟩
    rw [← map_snd_matchingLeafGraftWitnesses] at hy' hw'
    simp only [List.mem_map, Prod.exists, exists_and_left, exists_eq_right] at hy' hw'
    rcases hy' with ⟨a, hay⟩
    rcases hw' with ⟨b, hbw⟩
    exact ⟨⟨TwoStepWitnessRight.inner a b y' hay hbw, trivial⟩⟩
  · intro hw
    rcases hw with ⟨h⟩
    rcases h with ⟨h, hh⟩
    cases h with
    | inner a b y' hay hbw =>
        apply (mem_rightBracketingGeneratorOutputs_iff_exists y x z w).2
        refine ⟨y', ?_, ?_⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩
        · rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩
    | outer =>
        cases hh

/--
The quotient left associator-support predicate is exactly the concrete union of
the two raw bracketings that contribute to the left associator.
-/
@[simp] theorem inLeftAssociatorClass_iff_mem_associatorUnion
    (x y z w : PTree) :
    InLeftAssociatorClass x y z w ↔
      Or
        (w ∈ leftBracketingGeneratorOutputs x y z)
        (w ∈ rightBracketingGeneratorOutputs y x z) := by
  constructor
  · rintro ⟨q, hq⟩
    rcases hq with hq | hq
    · rcases hq with ⟨hOut, _⟩
      exact Or.inl ((mem_leftBracketingGeneratorOutputs_iff_nonempty_outerLeftWitness
        x y z w).2 ⟨hOut⟩)
    · rcases hq with ⟨h, _⟩
      exact Or.inr
        ((mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_leftInnerWitnessData
          x y z w).2 ⟨h⟩)
  · intro hw
    cases hw with
    | inl hL =>
        rcases (mem_leftBracketingGeneratorOutputs_iff_exists_leftOuterContributionClass
          x y z w).mp hL with ⟨q, hq⟩
        exact ⟨q, Or.inl hq⟩
    | inr hR =>
        rcases (mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_leftInnerWitnessData
          x y z w).mp hR with ⟨h⟩
        exact ⟨leftInnerWitnessClass x y z w h, Or.inr ⟨⟨h, rfl⟩⟩⟩

/--
The quotient swapped-right associator-support predicate is exactly the same
concrete union of raw bracketings.
-/
@[simp] theorem inRightAssociatorClass_iff_mem_associatorUnion
    (x y z w : PTree) :
    InRightAssociatorClass x y z w ↔
      Or
        (w ∈ leftBracketingGeneratorOutputs x y z)
        (w ∈ rightBracketingGeneratorOutputs y x z) := by
  constructor
  · rintro ⟨q', hq'⟩
    rcases hq' with hq' | hq'
    · rcases hq' with ⟨hOut, _⟩
      exact Or.inl
        ((mem_leftBracketingGeneratorOutputs_iff_nonempty_swappedRightOuterWitness
          x y z w).2 ⟨hOut⟩)
    · rcases hq' with ⟨h, _⟩
      exact Or.inr
        ((mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_swappedRightInnerWitnessData
          x y z w).2 ⟨h⟩)
  · intro hw
    cases hw with
    | inl hL =>
        rcases (mem_leftBracketingGeneratorOutputs_iff_nonempty_swappedRightOuterWitness
          x y z w).mp hL with ⟨hOut⟩
        exact ⟨outerRightWitnessClass hOut, Or.inl ⟨hOut, rfl⟩⟩
    | inr hR =>
        rcases (mem_rightBracketingGeneratorOutputs_swapped_iff_nonempty_swappedRightInnerWitnessData
          x y z w).mp hR with ⟨h⟩
        exact ⟨swappedRightInnerWitnessClass x y z w h, Or.inr ⟨⟨h, rfl⟩⟩⟩

/--
Finite concrete output support for the quotient associator comparison.
-/
noncomputable def associatorGeneratorOutputs
    (x y z : PTree) : Finset PTree :=
  leftBracketingGeneratorOutputs x y z ∪
    rightBracketingGeneratorOutputs y x z

@[simp] theorem mem_associatorGeneratorOutputs_iff
    (x y z w : PTree) :
    w ∈ associatorGeneratorOutputs x y z ↔
      Or
        (w ∈ leftBracketingGeneratorOutputs x y z)
        (w ∈ rightBracketingGeneratorOutputs y x z) := by
  simpa [associatorGeneratorOutputs] using
    (Finset.mem_union : w ∈ leftBracketingGeneratorOutputs x y z ∪
      rightBracketingGeneratorOutputs y x z ↔
        w ∈ leftBracketingGeneratorOutputs x y z ∨
        w ∈ rightBracketingGeneratorOutputs y x z)

/--
The concrete finite associator-output set computes the quotient left
associator-support predicate.
-/
@[simp] theorem mem_associatorGeneratorOutputs_iff_inLeftAssociatorClass
    (x y z w : PTree) :
    w ∈ associatorGeneratorOutputs x y z ↔ InLeftAssociatorClass x y z w := by
  rw [mem_associatorGeneratorOutputs_iff, inLeftAssociatorClass_iff_mem_associatorUnion]

/--
The same concrete finite associator-output set computes the quotient swapped
right associator-support predicate.
-/
@[simp] theorem mem_associatorGeneratorOutputs_iff_inRightAssociatorClass
    (x y z w : PTree) :
    w ∈ associatorGeneratorOutputs x y z ↔ InRightAssociatorClass x y z w := by
  rw [mem_associatorGeneratorOutputs_iff, inRightAssociatorClass_iff_mem_associatorUnion]

/--
Every concrete associator output has the expected total additive weight.
-/
theorem mem_associatorGeneratorOutputs_weight
    {x y z w : PTree}
    (hw : w ∈ associatorGeneratorOutputs x y z) :
    PTree.graftWeight w =
      PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
  rcases (mem_associatorGeneratorOutputs_iff x y z w).mp hw with h | h
  · calc
      PTree.graftWeight w =
          PTree.graftWeight x + (PTree.graftWeight y + PTree.graftWeight z) := by
        exact mem_leftBracketingGeneratorOutputs_weight h
      _ = PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
        omega
  · calc
      PTree.graftWeight w =
          (PTree.graftWeight y + PTree.graftWeight x) + PTree.graftWeight z := by
        exact mem_rightBracketingGeneratorOutputs_weight h
      _ = PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
        omega

/--
The concrete linear combination on the `A + D` side of the rearranged pre-Lie
comparison:

- `A = x ▷ (y ▷ z)`,
- `D = (y ▷ x) ▷ z`.

Its support is the finite quotient associator-output set computed above.
-/
noncomputable def comparisonSideGenerators
    (x y z : PTree) : linearProofTreeCarrier :=
  graftPreLie (treeGen x) (PTree.graftPreLieTree y z) +
    graftPreLie (PTree.graftPreLieTree y x) (treeGen z)

/--
Coefficient formula for the concrete `A + D` comparison side on tree
generators.
-/
theorem comparisonSideGenerators_apply_eq_sum_counts
    (x y z w : PTree) :
    comparisonSideGenerators x y z w =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : Nat) : ℤ)
      +
      ((((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) : ℤ) := by
  simp [comparisonSideGenerators, leftBracketingGenerator_apply_eq_count,
    rightBracketingGenerator_apply_eq_count]

/--
The same coefficient, rewritten as one total natural-number multiplicity.
-/
theorem comparisonSideGenerators_apply_eq_total_count
    (x y z w : PTree) :
    comparisonSideGenerators x y z w =
      Int.ofNat ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w)
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w)) := by
  rw [comparisonSideGenerators_apply_eq_sum_counts]
  norm_num

/--
Finite concrete output support of the `A + D` side of the rearranged pre-Lie
comparison.
-/
noncomputable def comparisonSideGeneratorOutputs
    (x y z : PTree) : Finset PTree :=
  (comparisonSideGenerators x y z).support

/--
Since the coefficients on the comparison side are sums of two natural-number
counts, its support is exactly the union of the two concrete raw bracketings.
-/
@[simp] theorem mem_comparisonSideGeneratorOutputs_iff
    (x y z w : PTree) :
    w ∈ comparisonSideGeneratorOutputs x y z ↔
      w ∈ associatorGeneratorOutputs x y z := by
  rw [comparisonSideGeneratorOutputs, Finsupp.mem_support_iff,
    comparisonSideGenerators_apply_eq_total_count,
    mem_associatorGeneratorOutputs_iff]
  let a :=
    ((PTree.matchingLeafGraftings y z).flatMap
      (fun z' => PTree.matchingLeafGraftings x z')).count w
  let d :=
    ((PTree.matchingLeafGraftings y x).flatMap
      (fun y' => PTree.matchingLeafGraftings y' z)).count w
  have hcast : Int.ofNat (a + d) = (a : ℤ) + (d : ℤ) := by
    simpa using (Nat.cast_add a d : ((a + d : Nat) : ℤ) = (a : ℤ) + (d : ℤ))
  rw [hcast]
  constructor
  · intro hsum
    have hnat : a + d ≠ 0 := by
      intro hzero
      exact hsum (by exact_mod_cast hzero)
    by_cases ha : a = 0
    · have hd : d ≠ 0 := by
        intro hd
        exact hnat (by simp [a, d, ha, hd])
      exact Or.inr ((mem_rightBracketingGeneratorOutputs_iff_count_ne_zero y x z w).2
        (by exact_mod_cast hd))
    · exact Or.inl ((mem_leftBracketingGeneratorOutputs_iff_count_ne_zero x y z w).2
        (by exact_mod_cast ha))
  · intro hw
    rcases hw with hL | hR
    · have ha : (a : ℤ) ≠ 0 := by
        simpa [a] using
          (mem_leftBracketingGeneratorOutputs_iff_count_ne_zero x y z w).mp hL
      have hnat : a ≠ 0 := by
        exact_mod_cast ha
      have hsum_nat : a + d ≠ 0 := by
        omega
      exact_mod_cast hsum_nat
    · have hd : (d : ℤ) ≠ 0 := by
        simpa [d] using
          (mem_rightBracketingGeneratorOutputs_iff_count_ne_zero y x z w).mp hR
      have hnat : d ≠ 0 := by
        exact_mod_cast hd
      have hsum_nat : a + d ≠ 0 := by
        omega
      exact_mod_cast hsum_nat

/--
The support of the concrete `A + D` comparison side is exactly the finite
quotient associator-output set.
-/
theorem comparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs
    (x y z : PTree) :
    comparisonSideGeneratorOutputs x y z = associatorGeneratorOutputs x y z := by
  ext w
  simp [mem_comparisonSideGeneratorOutputs_iff]

/--
Every output occurring on the concrete `A + D` comparison side has the expected
total additive weight.
-/
theorem mem_comparisonSideGeneratorOutputs_weight
    {x y z w : PTree}
    (hw : w ∈ comparisonSideGeneratorOutputs x y z) :
    PTree.graftWeight w =
      PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
  rw [comparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs] at hw
  exact mem_associatorGeneratorOutputs_weight hw

/--
The concrete `A + D` comparison-side element is homogeneous of the expected
total additive graft weight.
-/
theorem comparisonSideGenerators_mem_weightSubmodule
    (x y z : PTree) :
    comparisonSideGenerators x y z ∈
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) := by
  intro w hw
  exact mem_comparisonSideGeneratorOutputs_weight hw

/--
The `A + D` comparison-side element, regarded as an explicit element of the
corresponding homogeneous weight piece.
-/
noncomputable def weightedComparisonSideGenerators
    (x y z : PTree) :
    weightSubmodule
      (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) :=
  ⟨comparisonSideGenerators x y z,
    comparisonSideGenerators_mem_weightSubmodule x y z⟩

@[simp] theorem weightedComparisonSideGenerators_val
    (x y z : PTree) :
    ((weightedComparisonSideGenerators x y z :
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z)) :
      linearProofTreeCarrier) =
      comparisonSideGenerators x y z := rfl

/--
The concrete linear combination on the swapped `C + B` side of the rearranged
pre-Lie comparison:

- `C = y ▷ (x ▷ z)`,
- `B = (x ▷ y) ▷ z`.
-/
noncomputable def swappedComparisonSideGenerators
    (x y z : PTree) : linearProofTreeCarrier :=
  graftPreLie (treeGen y) (PTree.graftPreLieTree x z) +
    graftPreLie (PTree.graftPreLieTree x y) (treeGen z)

/--
Coefficient formula for the concrete `C + B` comparison side on tree
generators.
-/
theorem swappedComparisonSideGenerators_apply_eq_sum_counts
    (x y z w : PTree) :
    swappedComparisonSideGenerators x y z w =
      ((((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).count w : Nat) : ℤ)
      +
      ((((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Nat) : ℤ) := by
  simp [swappedComparisonSideGenerators, leftBracketingGenerator_apply_eq_count,
    rightBracketingGenerator_apply_eq_count]

/--
The same coefficient, rewritten as one total natural-number multiplicity.
-/
theorem swappedComparisonSideGenerators_apply_eq_total_count
    (x y z w : PTree) :
    swappedComparisonSideGenerators x y z w =
      Int.ofNat ((((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).count w)
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w)) := by
  rw [swappedComparisonSideGenerators_apply_eq_sum_counts]
  norm_num

/--
Finite concrete output support of the `C + B` side of the rearranged pre-Lie
comparison.
-/
noncomputable def swappedComparisonSideGeneratorOutputs
    (x y z : PTree) : Finset PTree :=
  (swappedComparisonSideGenerators x y z).support

/--
Since the coefficients on the swapped comparison side are sums of two natural
counts, its support is exactly the finite swapped associator-output set.
-/
@[simp] theorem mem_swappedComparisonSideGeneratorOutputs_iff
    (x y z w : PTree) :
    w ∈ swappedComparisonSideGeneratorOutputs x y z ↔
      w ∈ associatorGeneratorOutputs y x z := by
  rw [swappedComparisonSideGeneratorOutputs, Finsupp.mem_support_iff,
    swappedComparisonSideGenerators_apply_eq_total_count,
    mem_associatorGeneratorOutputs_iff]
  let c :=
    ((PTree.matchingLeafGraftings x z).flatMap
      (fun z' => PTree.matchingLeafGraftings y z')).count w
  let b :=
    ((PTree.matchingLeafGraftings x y).flatMap
      (fun y' => PTree.matchingLeafGraftings y' z)).count w
  have hcast : Int.ofNat (c + b) = (c : ℤ) + (b : ℤ) := by
    simpa using (Nat.cast_add c b : ((c + b : Nat) : ℤ) = (c : ℤ) + (b : ℤ))
  rw [hcast]
  constructor
  · intro hsum
    have hnat : c + b ≠ 0 := by
      intro hzero
      exact hsum (by exact_mod_cast hzero)
    by_cases hc : c = 0
    · have hb : b ≠ 0 := by
        intro hb
        exact hnat (by simp [c, b, hc, hb])
      exact Or.inr ((mem_rightBracketingGeneratorOutputs_iff_count_ne_zero x y z w).2
        (by exact_mod_cast hb))
    · exact Or.inl ((mem_leftBracketingGeneratorOutputs_iff_count_ne_zero y x z w).2
        (by exact_mod_cast hc))
  · intro hw
    rcases hw with hL | hR
    · have hc : (c : ℤ) ≠ 0 := by
        simpa [c] using
          (mem_leftBracketingGeneratorOutputs_iff_count_ne_zero y x z w).mp hL
      have hnat : c ≠ 0 := by
        exact_mod_cast hc
      have hsum_nat : c + b ≠ 0 := by
        omega
      exact_mod_cast hsum_nat
    · have hb : (b : ℤ) ≠ 0 := by
        simpa [b] using
          (mem_rightBracketingGeneratorOutputs_iff_count_ne_zero x y z w).mp hR
      have hnat : b ≠ 0 := by
        exact_mod_cast hb
      have hsum_nat : c + b ≠ 0 := by
        omega
      exact_mod_cast hsum_nat

/--
The support of the concrete `C + B` comparison side is exactly the finite
swapped associator-output set.
-/
theorem swappedComparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs
    (x y z : PTree) :
    swappedComparisonSideGeneratorOutputs x y z = associatorGeneratorOutputs y x z := by
  ext w
  simp [mem_swappedComparisonSideGeneratorOutputs_iff]

/--
Every output occurring on the concrete `C + B` comparison side has the expected
total additive weight.
-/
theorem mem_swappedComparisonSideGeneratorOutputs_weight
    {x y z w : PTree}
    (hw : w ∈ swappedComparisonSideGeneratorOutputs x y z) :
    PTree.graftWeight w =
      PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
  rw [swappedComparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs] at hw
  calc
    PTree.graftWeight w =
        PTree.graftWeight y + PTree.graftWeight x + PTree.graftWeight z := by
      exact mem_associatorGeneratorOutputs_weight hw
    _ = PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
      omega

/--
The concrete `C + B` comparison-side element is homogeneous of the expected
total additive graft weight.
-/
theorem swappedComparisonSideGenerators_mem_weightSubmodule
    (x y z : PTree) :
    swappedComparisonSideGenerators x y z ∈
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) := by
  intro w hw
  exact mem_swappedComparisonSideGeneratorOutputs_weight hw

/--
The `C + B` comparison-side element, regarded as an explicit element of the
corresponding homogeneous weight piece.
-/
noncomputable def weightedSwappedComparisonSideGenerators
    (x y z : PTree) :
    weightSubmodule
      (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) :=
  ⟨swappedComparisonSideGenerators x y z,
    swappedComparisonSideGenerators_mem_weightSubmodule x y z⟩

@[simp] theorem weightedSwappedComparisonSideGenerators_val
    (x y z : PTree) :
    ((weightedSwappedComparisonSideGenerators x y z :
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z)) :
      linearProofTreeCarrier) =
      swappedComparisonSideGenerators x y z := rfl

/--
The concrete difference between the two rearranged sides of the generator-level
pre-Lie comparison.

This is the linear combination
`(A + D) - (C + B)` in the notation used around the quotient associator
comparison.
-/
noncomputable def preLieDifferenceGenerators
    (x y z : PTree) : linearProofTreeCarrier :=
  comparisonSideGenerators x y z - swappedComparisonSideGenerators x y z

/--
The concrete pre-Lie comparison difference is exactly the difference of the two
standard associators
`assoc[graftPreLie] (treeGen y) (treeGen x) (treeGen z)` and
`assoc[graftPreLie] (treeGen x) (treeGen y) (treeGen z)`.

So the finite quotient comparison already has a direct shadow on the ordinary
linear associator expressions on tree generators.
-/
theorem preLieDifferenceGenerators_eq_associator_difference
    (x y z : PTree) :
    preLieDifferenceGenerators x y z =
      assoc[graftPreLie] (treeGen y) (treeGen x) (treeGen z) -
        assoc[graftPreLie] (treeGen x) (treeGen y) (treeGen z) := by
  ext w
  simp [preLieDifferenceGenerators, comparisonSideGenerators,
    swappedComparisonSideGenerators, graftPreLie_on_generators,
    sub_eq_add_neg]
  abel_nf

/--
Every support point of the concrete pre-Lie comparison difference comes from
one of the two finite comparison-side output sets.
-/
theorem mem_preLieDifferenceGenerators_support_implies
    {x y z w : PTree}
    (hw : w ∈ (preLieDifferenceGenerators x y z).support) :
    w ∈ comparisonSideGeneratorOutputs x y z ∪
      swappedComparisonSideGeneratorOutputs x y z := by
  rw [Finsupp.mem_support_iff] at hw
  by_cases hcomp : comparisonSideGenerators x y z w = 0
  · have hswap : swappedComparisonSideGenerators x y z w ≠ 0 := by
      intro hzero
      apply hw
      simp [preLieDifferenceGenerators, hcomp, hzero]
    exact Finset.mem_union.mpr <| Or.inr <|
      by simpa [swappedComparisonSideGeneratorOutputs, Finsupp.mem_support_iff] using hswap
  · exact Finset.mem_union.mpr <| Or.inl <|
      by simpa [comparisonSideGeneratorOutputs, Finsupp.mem_support_iff] using hcomp

/--
Every support point of the concrete pre-Lie comparison difference has the
expected total additive graft weight.
-/
theorem mem_preLieDifferenceGenerators_support_weight
    {x y z w : PTree}
    (hw : w ∈ (preLieDifferenceGenerators x y z).support) :
    PTree.graftWeight w =
      PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z := by
  have hmem := mem_preLieDifferenceGenerators_support_implies hw
  rcases Finset.mem_union.mp hmem with hcomp | hswap
  · exact mem_comparisonSideGeneratorOutputs_weight hcomp
  · exact mem_swappedComparisonSideGeneratorOutputs_weight hswap

/--
The concrete pre-Lie comparison difference is homogeneous of the expected total
additive graft weight.
-/
theorem preLieDifferenceGenerators_mem_weightSubmodule
    (x y z : PTree) :
    preLieDifferenceGenerators x y z ∈
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) := by
  intro w hw
  exact mem_preLieDifferenceGenerators_support_weight hw

/--
The concrete pre-Lie comparison difference, regarded as an explicit element of
the corresponding homogeneous weight piece.
-/
noncomputable def weightedPreLieDifferenceGenerators
    (x y z : PTree) :
    weightSubmodule
      (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z) :=
  ⟨preLieDifferenceGenerators x y z,
    preLieDifferenceGenerators_mem_weightSubmodule x y z⟩

@[simp] theorem weightedPreLieDifferenceGenerators_val
    (x y z : PTree) :
    ((weightedPreLieDifferenceGenerators x y z :
      weightSubmodule
        (PTree.graftWeight x + PTree.graftWeight y + PTree.graftWeight z)) :
      linearProofTreeCarrier) =
      preLieDifferenceGenerators x y z := rfl

/--
A finite quotient-side support bound for the concrete pre-Lie comparison
difference on tree generators.

Its support can only occur among the quotient associator outputs for `(x,y,z)`
or for the swapped triple `(y,x,z)`.
-/
noncomputable def preLieDifferenceGeneratorOutputBound
    (x y z : PTree) : Finset PTree :=
  associatorGeneratorOutputs x y z ∪ associatorGeneratorOutputs y x z

/--
Every support point of the concrete pre-Lie comparison difference lies in the
finite quotient-side output bound.
-/
theorem mem_preLieDifferenceGenerators_support_implies_mem_outputBound
    {x y z w : PTree}
    (hw : w ∈ (preLieDifferenceGenerators x y z).support) :
    w ∈ preLieDifferenceGeneratorOutputBound x y z := by
  rcases Finset.mem_union.mp
      (mem_preLieDifferenceGenerators_support_implies hw) with hcomp | hswap
  · apply Finset.mem_union.mpr
    left
    rwa [comparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs] at hcomp
  · apply Finset.mem_union.mpr
    right
    rwa [swappedComparisonSideGeneratorOutputs_eq_associatorGeneratorOutputs] at hswap

/--
Set-theoretic support containment form of the same bound.
-/
theorem preLieDifferenceGenerators_support_subset_outputBound
    (x y z : PTree) :
    (preLieDifferenceGenerators x y z).support ⊆
      preLieDifferenceGeneratorOutputBound x y z := by
  intro w hw
  exact mem_preLieDifferenceGenerators_support_implies_mem_outputBound hw

/--
Inside the common homogeneous weight piece, the concrete pre-Lie comparison
difference is literally the difference of the two rearranged comparison-side
elements.
-/
theorem weightedPreLieDifferenceGenerators_eq_sub
    (x y z : PTree) :
    weightedPreLieDifferenceGenerators x y z =
      weightedComparisonSideGenerators x y z -
        weightedSwappedComparisonSideGenerators x y z := by
  apply Subtype.ext
  ext w
  simp [preLieDifferenceGenerators]

/--
The set of concrete generator-level pre-Lie comparison defects.

This is the most direct linear shadow of the quotient associator theorem on the
existing proof-tree carrier.
-/
def preLieDifferenceGeneratorSet : Set linearProofTreeCarrier :=
  { a | ∃ x y z : PTree, a = preLieDifferenceGenerators x y z }

/--
The submodule generated by all concrete generator-level pre-Lie comparison
defects.

Quotienting by this submodule is the most conservative linear quotient one can
form from the currently explicit associator-defect elements.
-/
def preLieDifferenceSubmodule : Submodule ℤ linearProofTreeCarrier :=
  Submodule.span ℤ preLieDifferenceGeneratorSet

/--
Every concrete generator-level pre-Lie comparison defect lies in the defect
submodule.
-/
theorem preLieDifferenceGenerators_mem_preLieDifferenceSubmodule
    (x y z : PTree) :
    preLieDifferenceGenerators x y z ∈ preLieDifferenceSubmodule := by
  exact Submodule.subset_span ⟨x, y, z, rfl⟩

/--
The quotient of the raw linear proof-tree carrier by the concrete generator
defect submodule.

This is a candidate linear carrier on which the generator-level pre-Lie defect
has been forced to vanish.
-/
abbrev PreLieDifferenceQuotient :=
  linearProofTreeCarrier ⧸ preLieDifferenceSubmodule

/--
The canonical quotient map from the raw linear proof-tree carrier to the defect
quotient.
-/
def mkPreLieDifferenceQuotient :
    linearProofTreeCarrier →ₗ[ℤ] PreLieDifferenceQuotient :=
  Submodule.mkQ preLieDifferenceSubmodule

/--
The degree-`n` homogeneous piece of the concrete pre-Lie defect quotient,
obtained by pushing forward the existing weight-`n` submodule of the raw linear
proof-tree carrier.
-/
def preLieDifferenceWeightSubmodule (n : Nat) : Submodule ℤ PreLieDifferenceQuotient :=
  (weightSubmodule n).map mkPreLieDifferenceQuotient

@[simp] theorem mkPreLieDifferenceQuotient_mem_preLieDifferenceWeightSubmodule
    {n : Nat} {a : linearProofTreeCarrier}
    (ha : a ∈ weightSubmodule n) :
    mkPreLieDifferenceQuotient a ∈ preLieDifferenceWeightSubmodule n := by
  exact Submodule.mem_map_of_mem ha

theorem mkPreLieDifferenceQuotient_treeGen_mem_preLieDifferenceWeightSubmodule
    (x : PTree) :
    mkPreLieDifferenceQuotient (treeGen x) ∈
      preLieDifferenceWeightSubmodule (PTree.graftWeight x) := by
  exact mkPreLieDifferenceQuotient_mem_preLieDifferenceWeightSubmodule
    (treeGen_mem_weightSubmodule x)

/--
Every concrete generator-level pre-Lie comparison defect vanishes in the defect
quotient.
-/
theorem mkQ_preLieDifferenceGenerators_eq_zero
    (x y z : PTree) :
    mkPreLieDifferenceQuotient (preLieDifferenceGenerators x y z) = 0 := by
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceSubmodule).2
      (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z)

/--
Equivalently, the two concrete rearranged comparison sides become equal in the
defect quotient.
-/
theorem mkQ_comparisonSideGenerators_eq_mkQ_swappedComparisonSideGenerators
    (x y z : PTree) :
    mkPreLieDifferenceQuotient (comparisonSideGenerators x y z) =
      mkPreLieDifferenceQuotient (swappedComparisonSideGenerators x y z) := by
  have hzero := mkQ_preLieDifferenceGenerators_eq_zero x y z
  change mkPreLieDifferenceQuotient
      (comparisonSideGenerators x y z - swappedComparisonSideGenerators x y z) = 0 at hzero
  rw [LinearMap.map_sub] at hzero
  exact sub_eq_zero.mp hzero

/--
So the two standard raw associators on tree generators also become equal in the
same quotient.
-/
theorem mkQ_associator_generators_eq
    (x y z : PTree) :
    mkPreLieDifferenceQuotient
      (assoc[graftPreLie] (treeGen y) (treeGen x) (treeGen z)) =
    mkPreLieDifferenceQuotient
      (assoc[graftPreLie] (treeGen x) (treeGen y) (treeGen z)) := by
  have h :=
    mkQ_preLieDifferenceGenerators_eq_zero x y z
  rw [preLieDifferenceGenerators_eq_associator_difference] at h
  rw [LinearMap.map_sub] at h
  exact sub_eq_zero.mp h

/--
The raw grafting product, viewed in the concrete pre-Lie defect quotient.

This is still the original product on the existing linear proof-tree carrier,
but with output recorded modulo the generator-level pre-Lie defect submodule.
-/
noncomputable def graftPreLieModPreLieDifferenceQuotient :
    linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] PreLieDifferenceQuotient where
  toFun := fun a => mkPreLieDifferenceQuotient.comp (graftPreLie a)
  map_add' := by
    intro a₁ a₂
    apply LinearMap.ext
    intro b
    simp [LinearMap.comp_apply, LinearMap.map_add]
  map_smul' := by
    intro n a
    apply LinearMap.ext
    intro b
    change mkPreLieDifferenceQuotient ((graftPreLie (n • a)) b) =
      (n • mkPreLieDifferenceQuotient.comp (graftPreLie a)) b
    calc
      mkPreLieDifferenceQuotient ((graftPreLie (n • a)) b)
          = mkPreLieDifferenceQuotient (((n • graftPreLie a) b)) := by
              rw [LinearMap.map_smul]
      _ = n • mkPreLieDifferenceQuotient ((graftPreLie a) b) := by
            rw [LinearMap.smul_apply, LinearMap.map_smul]
      _ = (n • mkPreLieDifferenceQuotient.comp (graftPreLie a)) b := by
            rfl

/--
Compatibility hypothesis saying that left grafting by a tree generator sends
every concrete generator-level pre-Lie defect back into the defect submodule.
-/
def GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators : Prop :=
  ∀ u x y z : PTree,
    graftPreLie (treeGen u) (preLieDifferenceGenerators x y z) ∈
      preLieDifferenceSubmodule

/--
Compatibility hypothesis saying that right grafting by a tree generator sends
every concrete generator-level pre-Lie defect back into the defect submodule.
-/
def GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators : Prop :=
  ∀ u x y z : PTree,
    graftPreLie (preLieDifferenceGenerators x y z) (treeGen u) ∈
      preLieDifferenceSubmodule

/--
Under generator-level left compatibility, grafting by a fixed tree generator
preserves the whole concrete pre-Lie defect submodule.
-/
theorem graftPreLie_treeGen_left_preserves_preLieDifferenceSubmodule
    (h :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    graftPreLie (treeGen u) a ∈ preLieDifferenceSubmodule := by
  change a ∈ Submodule.span ℤ preLieDifferenceGeneratorSet at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro a ha
    rcases ha with ⟨x, y, z, rfl⟩
    exact h u x y z
  · simpa using (preLieDifferenceSubmodule.zero_mem :
      (0 : linearProofTreeCarrier) ∈ preLieDifferenceSubmodule)
  · intro a b _ _ ha hb
    simpa [LinearMap.map_add] using preLieDifferenceSubmodule.add_mem ha hb
  · intro n a _ ha
    simpa [LinearMap.map_smul] using preLieDifferenceSubmodule.smul_mem n ha

/--
Under generator-level right compatibility, grafting on the right by a fixed
tree generator preserves the whole concrete pre-Lie defect submodule.
-/
theorem graftPreLie_treeGen_right_preserves_preLieDifferenceSubmodule
    (h :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    graftPreLie a (treeGen u) ∈ preLieDifferenceSubmodule := by
  change a ∈ Submodule.span ℤ preLieDifferenceGeneratorSet at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro a ha
    rcases ha with ⟨x, y, z, rfl⟩
    exact h u x y z
  · simpa using (preLieDifferenceSubmodule.zero_mem :
      (0 : linearProofTreeCarrier) ∈ preLieDifferenceSubmodule)
  · intro a b _ _ ha hb
    simpa [LinearMap.map_add] using preLieDifferenceSubmodule.add_mem ha hb
  · intro n a _ ha
    simpa [LinearMap.map_smul] using preLieDifferenceSubmodule.smul_mem n ha

/--
Generator-level left compatibility extends to arbitrary left inputs by
linearity of the raw grafting product on the existing `ℤ`-module carrier.
-/
theorem graftPreLie_left_preserves_preLieDifferenceSubmodule
    (h :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    {a b : linearProofTreeCarrier}
    (hb : b ∈ preLieDifferenceSubmodule) :
    graftPreLie a b ∈ preLieDifferenceSubmodule := by
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simpa using (preLieDifferenceSubmodule.zero_mem :
      (0 : linearProofTreeCarrier) ∈ preLieDifferenceSubmodule)
  · intro a₁ a₂ ha₁ ha₂
    simpa [LinearMap.map_add] using preLieDifferenceSubmodule.add_mem ha₁ ha₂
  · intro u n
    have hu : graftPreLie (treeGen u) b ∈ preLieDifferenceSubmodule :=
      graftPreLie_treeGen_left_preserves_preLieDifferenceSubmodule h u hb
    have hs : graftPreLie (n • treeGen u) b ∈ preLieDifferenceSubmodule := by
      rw [LinearMap.map_smul]
      exact preLieDifferenceSubmodule.smul_mem n hu
    simpa [treeGen] using hs

/--
Generator-level right compatibility extends to arbitrary right inputs by
linearity of the raw grafting product on the existing `ℤ`-module carrier.
-/
theorem graftPreLie_right_preserves_preLieDifferenceSubmodule
    (h :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    {a b : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    graftPreLie a b ∈ preLieDifferenceSubmodule := by
  refine Finsupp.induction_linear b ?_ ?_ ?_
  · simpa using (preLieDifferenceSubmodule.zero_mem :
      (0 : linearProofTreeCarrier) ∈ preLieDifferenceSubmodule)
  · intro b₁ b₂ hb₁ hb₂
    simpa [LinearMap.map_add] using preLieDifferenceSubmodule.add_mem hb₁ hb₂
  · intro u n
    have hu : graftPreLie a (treeGen u) ∈ preLieDifferenceSubmodule :=
      graftPreLie_treeGen_right_preserves_preLieDifferenceSubmodule h u ha
    have hs : graftPreLie a (n • treeGen u) ∈ preLieDifferenceSubmodule := by
      rw [LinearMap.map_smul]
      exact preLieDifferenceSubmodule.smul_mem n hu
    simpa [treeGen] using hs

/--
Right compatibility makes the concrete defect submodule lie in the kernel of
the raw quotient-valued product as a linear map in its first variable.
-/
theorem preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient
    (h :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceSubmodule).2
      (graftPreLie_right_preserves_preLieDifferenceSubmodule h ha)

/--
The right compatibility hypothesis is equivalent to the exact kernel
containment needed for descent in the first variable.
-/
theorem preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_iff :
    preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.ker ↔
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators := by
  constructor
  · intro h u x y z
    have hker :
        preLieDifferenceGenerators x y z ∈
          graftPreLieModPreLieDifferenceQuotient.ker :=
      h (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z)
    have hzero :=
      LinearMap.congr_fun (show graftPreLieModPreLieDifferenceQuotient
        (preLieDifferenceGenerators x y z) = 0 from hker) (treeGen u)
    change
      mkPreLieDifferenceQuotient
        (graftPreLie (preLieDifferenceGenerators x y z) (treeGen u)) = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero preLieDifferenceSubmodule).1 hzero
  · intro h
    exact preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient h

/--
Left compatibility makes the concrete defect submodule lie in the kernel of the
flipped raw quotient-valued product as a linear map in its first variable.
-/
theorem preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip
    (h :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators) :
    preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.flip.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceSubmodule).2
      (graftPreLie_left_preserves_preLieDifferenceSubmodule h ha)

/--
The left compatibility hypothesis is equivalent to the exact kernel
containment needed for descent in the second variable.
-/
theorem preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip_iff :
    preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.flip.ker ↔
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators := by
  constructor
  · intro h u x y z
    have hker :
        preLieDifferenceGenerators x y z ∈
          graftPreLieModPreLieDifferenceQuotient.flip.ker :=
      h (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z)
    have hzero :=
      LinearMap.congr_fun (show graftPreLieModPreLieDifferenceQuotient.flip
        (preLieDifferenceGenerators x y z) = 0 from hker) (treeGen u)
    change
      mkPreLieDifferenceQuotient
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero preLieDifferenceSubmodule).1 hzero
  · intro h
    exact
      preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip h

/--
The raw grafting product descends to the original concrete defect quotient
exactly when the two generator-level preservation hypotheses hold.
-/
theorem preLieDifferenceQuotientMul_descends_iff :
    (preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.ker ∧
      preLieDifferenceSubmodule ≤
        graftPreLieModPreLieDifferenceQuotient.flip.ker) ↔
      (GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators ∧
        GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) := by
  constructor
  · rintro ⟨hR, hL⟩
    constructor
    · exact
        (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip_iff).1 hL
    · exact
        (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_iff).1 hR
  · rintro ⟨hL, hR⟩
    constructor
    · exact
        (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_iff).2 hR
    · exact
        (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip_iff).2 hL

/--
If the concrete defect submodule is stable under raw grafting in both
variables, then the raw grafting product descends to a bilinear multiplication
on the concrete defect quotient.
-/
noncomputable def preLieDifferenceQuotientMul
    (hL :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    PreLieDifferenceQuotient →ₗ[ℤ] PreLieDifferenceQuotient →ₗ[ℤ]
      PreLieDifferenceQuotient :=
  graftPreLieModPreLieDifferenceQuotient.liftQ₂
    preLieDifferenceSubmodule
    preLieDifferenceSubmodule
    (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient hR)
    (preLieDifferenceSubmodule_le_ker_graftPreLieModPreLieDifferenceQuotient_flip hL)

@[simp] theorem preLieDifferenceQuotientMul_mk
    (hL :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b : linearProofTreeCarrier) :
    preLieDifferenceQuotientMul hL hR
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      mkPreLieDifferenceQuotient (graftPreLie a b) := by
  rfl

/--
Under the two descent hypotheses, the quotient multiplication inherits the
generator-level associator symmetry already proved for the trusted quotient
comparison theorem.
-/
theorem preLieDifferenceQuotientMul_associator_generators_eq
    (hL :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (x y z : PTree) :
    preLieDifferenceQuotientMul hL hR
      (preLieDifferenceQuotientMul hL hR
        (mkPreLieDifferenceQuotient (treeGen y))
        (mkPreLieDifferenceQuotient (treeGen x)))
      (mkPreLieDifferenceQuotient (treeGen z))
      -
      preLieDifferenceQuotientMul hL hR
        (mkPreLieDifferenceQuotient (treeGen y))
        (preLieDifferenceQuotientMul hL hR
          (mkPreLieDifferenceQuotient (treeGen x))
          (mkPreLieDifferenceQuotient (treeGen z)))
    =
    preLieDifferenceQuotientMul hL hR
      (preLieDifferenceQuotientMul hL hR
        (mkPreLieDifferenceQuotient (treeGen x))
        (mkPreLieDifferenceQuotient (treeGen y)))
      (mkPreLieDifferenceQuotient (treeGen z))
      -
      preLieDifferenceQuotientMul hL hR
        (mkPreLieDifferenceQuotient (treeGen x))
        (preLieDifferenceQuotientMul hL hR
          (mkPreLieDifferenceQuotient (treeGen y))
          (mkPreLieDifferenceQuotient (treeGen z))) := by
  simpa [preLieDifferenceQuotientMul_mk]
    using mkQ_associator_generators_eq x y z

/--
Under the two descent hypotheses, the descended quotient multiplication
respects the graft-weight grading inherited from the raw linear proof-tree
carrier.
-/
theorem preLieDifferenceQuotientMul_respects_weight
    (hL :
      GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR :
      GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    {m n : Nat}
    {a b : PreLieDifferenceQuotient}
    (ha : a ∈ preLieDifferenceWeightSubmodule m)
    (hb : b ∈ preLieDifferenceWeightSubmodule n) :
    preLieDifferenceQuotientMul hL hR a b ∈
      preLieDifferenceWeightSubmodule (m + n) := by
  rcases Submodule.mem_map.mp ha with ⟨a0, ha0, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨b0, hb0, rfl⟩
  simpa [preLieDifferenceQuotientMul_mk]
    using
      (mkPreLieDifferenceQuotient_mem_preLieDifferenceWeightSubmodule
        (graftPreLie_respects_weight_everywhere ha0 hb0))

/--
A submodule of the raw linear proof-tree carrier is stable if left and right
grafting by tree generators both preserve it.

This is the exact algebraic closure property needed for the bilinear raw
grafting product to descend to the corresponding quotient.
-/
def TreeGeneratorStableSubmodule
    (N : Submodule ℤ linearProofTreeCarrier) : Prop :=
  (∀ u : PTree, ∀ {a : linearProofTreeCarrier}, a ∈ N →
      graftPreLie (treeGen u) a ∈ N)
  ∧
  (∀ u : PTree, ∀ {a : linearProofTreeCarrier}, a ∈ N →
      graftPreLie a (treeGen u) ∈ N)

/--
The generator-level preservation hypotheses are exactly the statement that the
concrete pre-Lie defect submodule is stable under grafting by tree generators
on both sides.
-/
theorem treeGeneratorStable_preLieDifferenceSubmodule_iff :
    TreeGeneratorStableSubmodule preLieDifferenceSubmodule ↔
      (GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators ∧
        GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) := by
  constructor
  · intro h
    constructor
    · intro u x y z
      exact h.1 u
        (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z)
    · intro u x y z
      exact h.2 u
        (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z)
  · rintro ⟨hL, hR⟩
    constructor
    · intro u a ha
      exact
        graftPreLie_treeGen_left_preserves_preLieDifferenceSubmodule
          hL u ha
    · intro u a ha
      exact
        graftPreLie_treeGen_right_preserves_preLieDifferenceSubmodule
          hR u ha

/--
Any submodule stable under left grafting by tree generators is stable under left
grafting by arbitrary finite linear combinations of trees.
-/
theorem graftPreLie_left_preserves_of_treeGeneratorStable
    {N : Submodule ℤ linearProofTreeCarrier}
    (hN : TreeGeneratorStableSubmodule N)
    {a b : linearProofTreeCarrier}
    (hb : b ∈ N) :
    graftPreLie a b ∈ N := by
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simpa using (N.zero_mem : (0 : linearProofTreeCarrier) ∈ N)
  · intro a₁ a₂ ha₁ ha₂
    simpa [LinearMap.map_add] using N.add_mem ha₁ ha₂
  · intro u n
    have hu : graftPreLie (treeGen u) b ∈ N := hN.1 u hb
    have hs : graftPreLie (n • treeGen u) b ∈ N := by
      rw [LinearMap.map_smul]
      exact N.smul_mem n hu
    simpa [treeGen] using hs

/--
Any submodule stable under right grafting by tree generators is stable under
right grafting by arbitrary finite linear combinations of trees.
-/
theorem graftPreLie_right_preserves_of_treeGeneratorStable
    {N : Submodule ℤ linearProofTreeCarrier}
    (hN : TreeGeneratorStableSubmodule N)
    {a b : linearProofTreeCarrier}
    (ha : a ∈ N) :
    graftPreLie a b ∈ N := by
  refine Finsupp.induction_linear b ?_ ?_ ?_
  · simpa using (N.zero_mem : (0 : linearProofTreeCarrier) ∈ N)
  · intro b₁ b₂ hb₁ hb₂
    simpa [LinearMap.map_add] using N.add_mem hb₁ hb₂
  · intro u n
    have hu : graftPreLie a (treeGen u) ∈ N := hN.2 u ha
    have hs : graftPreLie a (n • treeGen u) ∈ N := by
      rw [LinearMap.map_smul]
      exact N.smul_mem n hu
    simpa [treeGen] using hs

/--
The family of submodules containing the concrete pre-Lie defect submodule and
stable under grafting by tree generators on both sides.
-/
def preLieDifferenceStableSubmoduleFamily :
    Set (Submodule ℤ linearProofTreeCarrier) :=
  { N | preLieDifferenceSubmodule ≤ N ∧ TreeGeneratorStableSubmodule N }

/--
The smallest stable submodule containing the concrete generator-level pre-Lie
defects.

This is the exact closure of the current defect quotient under the raw grafting
product. If the original defect submodule already admits descent, this closure
collapses back to `preLieDifferenceSubmodule`.
-/
def preLieDifferenceStableSubmodule : Submodule ℤ linearProofTreeCarrier :=
  sInf preLieDifferenceStableSubmoduleFamily

/--
The concrete defect submodule sits inside its smallest stable closure.
-/
theorem preLieDifferenceSubmodule_le_preLieDifferenceStableSubmodule :
    preLieDifferenceSubmodule ≤ preLieDifferenceStableSubmodule := by
  refine le_sInf ?_
  intro N hN
  exact hN.1

/--
The stable closure is itself stable under left grafting by tree generators.
-/
theorem graftPreLie_treeGen_left_preserves_preLieDifferenceStableSubmodule
    (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    graftPreLie (treeGen u) a ∈ preLieDifferenceStableSubmodule := by
  change graftPreLie (treeGen u) a ∈ sInf preLieDifferenceStableSubmoduleFamily
  rw [Submodule.mem_sInf]
  intro N hN
  have ha' : a ∈ sInf preLieDifferenceStableSubmoduleFamily := ha
  exact hN.2.1 u ((Submodule.mem_sInf.mp ha') N hN)

/--
The stable closure is itself stable under right grafting by tree generators.
-/
theorem graftPreLie_treeGen_right_preserves_preLieDifferenceStableSubmodule
    (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    graftPreLie a (treeGen u) ∈ preLieDifferenceStableSubmodule := by
  change graftPreLie a (treeGen u) ∈ sInf preLieDifferenceStableSubmoduleFamily
  rw [Submodule.mem_sInf]
  intro N hN
  have ha' : a ∈ sInf preLieDifferenceStableSubmoduleFamily := ha
  exact hN.2.2 u ((Submodule.mem_sInf.mp ha') N hN)

/--
The stable closure is stable under generator grafting on both sides.
-/
theorem preLieDifferenceStableSubmodule_isStable :
    TreeGeneratorStableSubmodule preLieDifferenceStableSubmodule := by
  constructor
  · intro u a ha
    exact
      graftPreLie_treeGen_left_preserves_preLieDifferenceStableSubmodule
        u ha
  · intro u a ha
    exact
      graftPreLie_treeGen_right_preserves_preLieDifferenceStableSubmodule
        u ha

/--
Hence the stable closure is preserved by arbitrary left raw grafting.
-/
theorem graftPreLie_left_preserves_preLieDifferenceStableSubmodule
    {a b : linearProofTreeCarrier}
    (hb : b ∈ preLieDifferenceStableSubmodule) :
    graftPreLie a b ∈ preLieDifferenceStableSubmodule := by
  exact
    graftPreLie_left_preserves_of_treeGeneratorStable
      preLieDifferenceStableSubmodule_isStable hb

/--
Hence the stable closure is preserved by arbitrary right raw grafting.
-/
theorem graftPreLie_right_preserves_preLieDifferenceStableSubmodule
    {a b : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    graftPreLie a b ∈ preLieDifferenceStableSubmodule := by
  exact
    graftPreLie_right_preserves_of_treeGeneratorStable
      preLieDifferenceStableSubmodule_isStable ha

/--
The concrete stable quotient carrier.
-/
abbrev PreLieDifferenceStableQuotient :=
  linearProofTreeCarrier ⧸ preLieDifferenceStableSubmodule

/--
The canonical quotient map to the smallest stable quotient.
-/
def mkPreLieDifferenceStableQuotient :
    linearProofTreeCarrier →ₗ[ℤ] PreLieDifferenceStableQuotient :=
  Submodule.mkQ preLieDifferenceStableSubmodule

/--
The degree-`n` homogeneous piece of the stable quotient, obtained by pushing
forward the existing weight-`n` submodule of the raw linear proof-tree carrier.
-/
def preLieDifferenceStableWeightSubmodule
    (n : Nat) : Submodule ℤ PreLieDifferenceStableQuotient :=
  (weightSubmodule n).map mkPreLieDifferenceStableQuotient

@[simp] theorem mkPreLieDifferenceStableQuotient_mem_preLieDifferenceStableWeightSubmodule
    {n : Nat} {a : linearProofTreeCarrier}
    (ha : a ∈ weightSubmodule n) :
    mkPreLieDifferenceStableQuotient a ∈
      preLieDifferenceStableWeightSubmodule n := by
  exact Submodule.mem_map_of_mem ha

theorem mkPreLieDifferenceStableQuotient_treeGen_mem_preLieDifferenceStableWeightSubmodule
    (x : PTree) :
    mkPreLieDifferenceStableQuotient (treeGen x) ∈
      preLieDifferenceStableWeightSubmodule (PTree.graftWeight x) := by
  exact mkPreLieDifferenceStableQuotient_mem_preLieDifferenceStableWeightSubmodule
    (treeGen_mem_weightSubmodule x)

/--
The raw grafting product, viewed in the smallest stable quotient.
-/
noncomputable def graftPreLieModPreLieDifferenceStableQuotient :
    linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ]
      PreLieDifferenceStableQuotient where
  toFun := fun a =>
    mkPreLieDifferenceStableQuotient.comp (graftPreLie a)
  map_add' := by
    intro a1 a2
    apply LinearMap.ext
    intro b
    simp [LinearMap.comp_apply, LinearMap.map_add]
  map_smul' := by
    intro n a
    apply LinearMap.ext
    intro b
    change
      mkPreLieDifferenceStableQuotient ((graftPreLie (n • a)) b) =
        (n • mkPreLieDifferenceStableQuotient.comp (graftPreLie a)) b
    calc
      mkPreLieDifferenceStableQuotient ((graftPreLie (n • a)) b)
          = mkPreLieDifferenceStableQuotient (((n • graftPreLie a) b)) := by
              rw [LinearMap.map_smul]
      _ = n • mkPreLieDifferenceStableQuotient ((graftPreLie a) b) := by
            rw [LinearMap.smul_apply, LinearMap.map_smul]
      _ = (n • mkPreLieDifferenceStableQuotient.comp (graftPreLie a)) b := by
            rfl

/--
The stable closure lies in the kernel of the stable quotient-valued raw
grafting product as a linear map in its first variable.
-/
theorem preLieDifferenceStableSubmodule_le_ker_graftPreLieModPreLieDifferenceStableQuotient :
    preLieDifferenceStableSubmodule ≤
      graftPreLieModPreLieDifferenceStableQuotient.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceStableSubmodule).2
      (graftPreLie_right_preserves_preLieDifferenceStableSubmodule ha)

/--
The stable closure also lies in the kernel of the flipped quotient-valued raw
grafting product.
-/
theorem preLieDifferenceStableSubmodule_le_ker_graftPreLieModPreLieDifferenceStableQuotient_flip :
    preLieDifferenceStableSubmodule ≤
      graftPreLieModPreLieDifferenceStableQuotient.flip.ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  ext b
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceStableSubmodule).2
      (graftPreLie_left_preserves_preLieDifferenceStableSubmodule ha)

/--
The raw grafting product descends unconditionally to the smallest stable
quotient.
-/
noncomputable def preLieDifferenceStableQuotientMul :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        PreLieDifferenceStableQuotient :=
  graftPreLieModPreLieDifferenceStableQuotient.liftQ₂
    preLieDifferenceStableSubmodule
    preLieDifferenceStableSubmodule
    preLieDifferenceStableSubmodule_le_ker_graftPreLieModPreLieDifferenceStableQuotient
    preLieDifferenceStableSubmodule_le_ker_graftPreLieModPreLieDifferenceStableQuotient_flip

@[simp] theorem preLieDifferenceStableQuotientMul_mk
    (a b : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientMul
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      mkPreLieDifferenceStableQuotient (graftPreLie a b) := by
  rfl

/--
The unconditional descended product on the stable quotient respects the
graft-weight grading inherited from the raw linear proof-tree carrier.
-/
theorem preLieDifferenceStableQuotientMul_respects_weight
    {m n : Nat}
    {a b : PreLieDifferenceStableQuotient}
    (ha : a ∈ preLieDifferenceStableWeightSubmodule m)
    (hb : b ∈ preLieDifferenceStableWeightSubmodule n) :
    preLieDifferenceStableQuotientMul a b ∈
      preLieDifferenceStableWeightSubmodule (m + n) := by
  rcases Submodule.mem_map.mp ha with ⟨a0, ha0, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨b0, hb0, rfl⟩
  simpa [preLieDifferenceStableQuotientMul_mk]
    using
      (mkPreLieDifferenceStableQuotient_mem_preLieDifferenceStableWeightSubmodule
        (graftPreLie_respects_weight_everywhere ha0 hb0))

/--
Every generator-level pre-Lie defect already vanishes in the smallest stable
quotient.
-/
theorem mkPreLieDifferenceStableQuotient_preLieDifferenceGenerators_eq_zero
    (x y z : PTree) :
    mkPreLieDifferenceStableQuotient (preLieDifferenceGenerators x y z) = 0 := by
  exact
    (Submodule.Quotient.mk_eq_zero preLieDifferenceStableSubmodule).2
      (preLieDifferenceSubmodule_le_preLieDifferenceStableSubmodule
        (preLieDifferenceGenerators_mem_preLieDifferenceSubmodule x y z))

/--
So the two generator-level associators are already equal in the smallest stable
quotient.
-/
theorem mkPreLieDifferenceStableQuotient_associator_generators_eq
    (x y z : PTree) :
    mkPreLieDifferenceStableQuotient
      (assoc[graftPreLie] (treeGen y) (treeGen x) (treeGen z)) =
    mkPreLieDifferenceStableQuotient
      (assoc[graftPreLie] (treeGen x) (treeGen y) (treeGen z)) := by
  have h :=
    mkPreLieDifferenceStableQuotient_preLieDifferenceGenerators_eq_zero x y z
  rw [preLieDifferenceGenerators_eq_associator_difference] at h
  rw [LinearMap.map_sub] at h
  exact sub_eq_zero.mp h

/--
The descended product on the smallest stable quotient inherits the trusted
generator-level associator symmetry.
-/
theorem preLieDifferenceStableQuotientMul_associator_generators_eq
    (x y z : PTree) :
    preLieDifferenceStableQuotientMul
      (preLieDifferenceStableQuotientMul
        (mkPreLieDifferenceStableQuotient (treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen x)))
      (mkPreLieDifferenceStableQuotient (treeGen z))
      -
      preLieDifferenceStableQuotientMul
        (mkPreLieDifferenceStableQuotient (treeGen y))
        (preLieDifferenceStableQuotientMul
          (mkPreLieDifferenceStableQuotient (treeGen x))
          (mkPreLieDifferenceStableQuotient (treeGen z)))
    =
    preLieDifferenceStableQuotientMul
      (preLieDifferenceStableQuotientMul
        (mkPreLieDifferenceStableQuotient (treeGen x))
        (mkPreLieDifferenceStableQuotient (treeGen y)))
      (mkPreLieDifferenceStableQuotient (treeGen z))
      -
      preLieDifferenceStableQuotientMul
        (mkPreLieDifferenceStableQuotient (treeGen x))
        (preLieDifferenceStableQuotientMul
          (mkPreLieDifferenceStableQuotient (treeGen y))
          (mkPreLieDifferenceStableQuotient (treeGen z))) := by
  simpa [preLieDifferenceStableQuotientMul_mk]
    using mkPreLieDifferenceStableQuotient_associator_generators_eq x y z

/--
The raw associator, projected to the smallest stable quotient.
-/
noncomputable def stableProjectedAssociator
    (a b c : linearProofTreeCarrier) : PreLieDifferenceStableQuotient :=
  mkPreLieDifferenceStableQuotient (assoc[graftPreLie] a b c)

@[simp] theorem stableProjectedAssociator_zero_left
    (b c : linearProofTreeCarrier) :
    stableProjectedAssociator 0 b c = 0 := by
  simp [stableProjectedAssociator, bilinearAssociator_zero_left]

@[simp] theorem stableProjectedAssociator_zero_middle
    (a c : linearProofTreeCarrier) :
    stableProjectedAssociator a 0 c = 0 := by
  simp [stableProjectedAssociator, bilinearAssociator_zero_middle]

@[simp] theorem stableProjectedAssociator_zero_right
    (a b : linearProofTreeCarrier) :
    stableProjectedAssociator a b 0 = 0 := by
  simp [stableProjectedAssociator, bilinearAssociator_zero_right]

theorem stableProjectedAssociator_add_left
    (a1 a2 b c : linearProofTreeCarrier) :
    stableProjectedAssociator (a1 + a2) b c =
      stableProjectedAssociator a1 b c + stableProjectedAssociator a2 b c := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_add_left, LinearMap.map_add]

theorem stableProjectedAssociator_smul_left
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    stableProjectedAssociator (n • a) b c =
      n • stableProjectedAssociator a b c := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_smul_left, LinearMap.map_smul]

theorem stableProjectedAssociator_add_middle
    (a b1 b2 c : linearProofTreeCarrier) :
    stableProjectedAssociator a (b1 + b2) c =
      stableProjectedAssociator a b1 c + stableProjectedAssociator a b2 c := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_add_middle, LinearMap.map_add]

theorem stableProjectedAssociator_smul_middle
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    stableProjectedAssociator a (n • b) c =
      n • stableProjectedAssociator a b c := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_smul_middle, LinearMap.map_smul]

theorem stableProjectedAssociator_add_right
    (a b c1 c2 : linearProofTreeCarrier) :
    stableProjectedAssociator a b (c1 + c2) =
      stableProjectedAssociator a b c1 + stableProjectedAssociator a b c2 := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_add_right, LinearMap.map_add]

theorem stableProjectedAssociator_smul_right
    (n : ℤ) (a b c : linearProofTreeCarrier) :
    stableProjectedAssociator a b (n • c) =
      n • stableProjectedAssociator a b c := by
  unfold stableProjectedAssociator
  rw [bilinearAssociator_smul_right, LinearMap.map_smul]

/--
The trusted generator-level associator symmetry extends from tree generators to
all representatives in the smallest stable quotient.
-/
theorem stableProjectedAssociator_swap_left_everywhere
    (a b c : linearProofTreeCarrier) :
    stableProjectedAssociator a b c = stableProjectedAssociator b a c := by
  let P : linearProofTreeCarrier → Prop :=
    fun a => ∀ b c, stableProjectedAssociator a b c = stableProjectedAssociator b a c
  have hP_gen : ∀ x : PTree, P (treeGen x) := by
    intro x
    let Q : linearProofTreeCarrier → Prop :=
      fun b => ∀ c,
        stableProjectedAssociator (treeGen x) b c =
          stableProjectedAssociator b (treeGen x) c
    have hQ_gen : ∀ y : PTree, Q (treeGen y) := by
      intro y
      let R : linearProofTreeCarrier → Prop :=
        fun c =>
          stableProjectedAssociator (treeGen x) (treeGen y) c =
            stableProjectedAssociator (treeGen y) (treeGen x) c
      have hR_gen : ∀ z : PTree, R (treeGen z) := by
        intro z
        simpa [R] using
          preLieDifferenceStableQuotientMul_associator_generators_eq y x z
      have hR : ∀ c : linearProofTreeCarrier, R c := by
        intro c
        refine Finsupp.induction_linear c ?_ ?_ ?_
        · simp [R]
        · intro c1 c2 hc1 hc2
          change
            stableProjectedAssociator (treeGen x) (treeGen y) (c1 + c2) =
              stableProjectedAssociator (treeGen y) (treeGen x) (c1 + c2)
          rw [stableProjectedAssociator_add_right, hc1, hc2,
            stableProjectedAssociator_add_right]
        · intro z n
          have hz : R (n • treeGen z) := by
            change
              stableProjectedAssociator (treeGen x) (treeGen y) (n • treeGen z) =
                stableProjectedAssociator (treeGen y) (treeGen x) (n • treeGen z)
            rw [stableProjectedAssociator_smul_right,
              stableProjectedAssociator_smul_right]
            exact congrArg (fun t => n • t) (hR_gen z)
          simpa [treeGen] using hz
      exact hR
    have hQ : ∀ b : linearProofTreeCarrier, Q b := by
      intro b
      refine Finsupp.induction_linear b ?_ ?_ ?_
      · simp [Q]
      · intro b1 b2 hb1 hb2
        intro c
        change
          stableProjectedAssociator (treeGen x) (b1 + b2) c =
            stableProjectedAssociator (b1 + b2) (treeGen x) c
        rw [stableProjectedAssociator_add_middle, hb1 c, hb2 c,
          stableProjectedAssociator_add_left]
      · intro y n
        have hy : Q (treeGen y) := hQ_gen y
        have hyn : Q (n • treeGen y) := by
          intro c
          change
            stableProjectedAssociator (treeGen x) (n • treeGen y) c =
              stableProjectedAssociator (n • treeGen y) (treeGen x) c
          rw [stableProjectedAssociator_smul_middle,
            stableProjectedAssociator_smul_left]
          exact congrArg (fun t => n • t) (hy c)
        simpa [treeGen] using hyn
    exact hQ
  have hP : ∀ a : linearProofTreeCarrier, P a := by
    intro a
    refine Finsupp.induction_linear a ?_ ?_ ?_
    · simp [P]
    · intro a1 a2 ha1 ha2
      intro b c
      change
        stableProjectedAssociator (a1 + a2) b c =
          stableProjectedAssociator b (a1 + a2) c
      rw [stableProjectedAssociator_add_left, ha1 b c, ha2 b c,
        stableProjectedAssociator_add_middle]
    · intro x n
      have hx : P (treeGen x) := hP_gen x
      have hxn : P (n • treeGen x) := by
        intro b c
        change
          stableProjectedAssociator (n • treeGen x) b c =
            stableProjectedAssociator b (n • treeGen x) c
        rw [stableProjectedAssociator_smul_left,
          stableProjectedAssociator_smul_middle]
        exact congrArg (fun t => n • t) (hx b c)
      simpa [treeGen] using hxn
  exact hP a b c

/--
The associator of the unconditional stable quotient product.
-/
noncomputable def preLieDifferenceStableQuotientAssociator
    (a b c : PreLieDifferenceStableQuotient) :
    PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientMul
      (preLieDifferenceStableQuotientMul a b) c
    -
    preLieDifferenceStableQuotientMul a
      (preLieDifferenceStableQuotientMul b c)

@[simp] theorem preLieDifferenceStableQuotientAssociator_mk
    (a b c : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientAssociator
      (mkPreLieDifferenceStableQuotient a)
      (mkPreLieDifferenceStableQuotient b)
      (mkPreLieDifferenceStableQuotient c)
    =
    stableProjectedAssociator a b c := by
  change
    preLieDifferenceStableQuotientAssociator
      (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk b)
      (Submodule.Quotient.mk c)
    =
    stableProjectedAssociator a b c
  unfold preLieDifferenceStableQuotientAssociator
    stableProjectedAssociator
  rw [preLieDifferenceStableQuotientMul_mk,
    preLieDifferenceStableQuotientMul_mk]
  change
    preLieDifferenceStableQuotientMul
        (Submodule.Quotient.mk (graftPreLie a b))
        (Submodule.Quotient.mk c)
      -
      preLieDifferenceStableQuotientMul
        (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk (graftPreLie b c))
    =
    mkPreLieDifferenceStableQuotient (assoc[graftPreLie] a b c)
  rw [preLieDifferenceStableQuotientMul_mk, preLieDifferenceStableQuotientMul_mk]
  rw [← LinearMap.map_sub]

/--
The unconditional stable quotient product satisfies the full associator
symmetry present in the quotient proof-theoretic comparison: swapping the first
two inputs leaves the associator unchanged.
-/
theorem preLieDifferenceStableQuotientMul_associator_swap_left
    (a b c : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientAssociator a b c =
      preLieDifferenceStableQuotientAssociator b a c := by
  refine Quotient.inductionOn₃' a b c ?_
  intro a0 b0 c0
  simpa [preLieDifferenceStableQuotientAssociator_mk]
    using stableProjectedAssociator_swap_left_everywhere a0 b0 c0

/--
If the original concrete defect quotient already admits descent, then its
defect submodule is exactly the smallest stable closure.
-/
theorem preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    preLieDifferenceStableSubmodule = preLieDifferenceSubmodule := by
  apply le_antisymm
  · refine sInf_le ?_
    refine ⟨le_rfl, ?_⟩
    constructor
    · intro u a ha
      exact
        graftPreLie_treeGen_left_preserves_preLieDifferenceSubmodule
          hL u ha
    · intro u a ha
      exact
        graftPreLie_treeGen_right_preserves_preLieDifferenceSubmodule
          hR u ha
  · exact preLieDifferenceSubmodule_le_preLieDifferenceStableSubmodule

/--
The smallest stable closure adds nothing new exactly when the original defect
submodule is already stable under grafting by tree generators on both sides.
-/
theorem preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule_iff :
    preLieDifferenceStableSubmodule = preLieDifferenceSubmodule ↔
      (GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators ∧
        GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) := by
  constructor
  · intro hEq
    have hStable : TreeGeneratorStableSubmodule preLieDifferenceSubmodule := by
      rw [← hEq]
      exact preLieDifferenceStableSubmodule_isStable
    exact (treeGeneratorStable_preLieDifferenceSubmodule_iff).1 hStable
  · rintro ⟨hL, hR⟩
    exact preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule hL hR

/--
Equivalently: the stable closure collapses back to the original concrete defect
submodule exactly when raw grafting descends to the original defect quotient.
-/
theorem preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule_iff_descends :
    preLieDifferenceStableSubmodule = preLieDifferenceSubmodule ↔
      (preLieDifferenceSubmodule ≤ graftPreLieModPreLieDifferenceQuotient.ker ∧
        preLieDifferenceSubmodule ≤
          graftPreLieModPreLieDifferenceQuotient.flip.ker) := by
  rw [preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule_iff,
    preLieDifferenceQuotientMul_descends_iff]

/--
The canonical quotient map from the original concrete defect quotient to the
smallest stable quotient.
-/
def preLieDifferenceQuotientToStableQuotient :
    PreLieDifferenceQuotient →ₗ[ℤ] PreLieDifferenceStableQuotient :=
  Submodule.mapQ preLieDifferenceSubmodule preLieDifferenceStableSubmodule
    (LinearMap.id : linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier)
    (by
      simpa using preLieDifferenceSubmodule_le_preLieDifferenceStableSubmodule)

@[simp] theorem preLieDifferenceQuotientToStableQuotient_mk
    (a : linearProofTreeCarrier) :
    preLieDifferenceQuotientToStableQuotient
      (mkPreLieDifferenceQuotient a) =
      mkPreLieDifferenceStableQuotient a := by
  rfl

/--
Under the original compatibility hypotheses, the stable descended product is
the image of the conditional product on the original defect quotient.
-/
theorem preLieDifferenceQuotientToStableQuotient_mul
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientToStableQuotient
      (preLieDifferenceQuotientMul hL hR a b) =
    preLieDifferenceStableQuotientMul
      (preLieDifferenceQuotientToStableQuotient a)
      (preLieDifferenceQuotientToStableQuotient b) := by
  refine Quotient.inductionOn₂' a b ?_
  intro a0 b0
  rfl

/--
The associator of the conditional product on the original defect quotient.
-/
noncomputable def preLieDifferenceQuotientAssociator
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    PreLieDifferenceQuotient :=
  preLieDifferenceQuotientMul hL hR
      (preLieDifferenceQuotientMul hL hR a b) c
    -
    preLieDifferenceQuotientMul hL hR a
      (preLieDifferenceQuotientMul hL hR b c)

/--
Under the original compatibility hypotheses, the quotient associator maps to
the stable quotient associator.
-/
theorem preLieDifferenceQuotientToStableQuotient_associator
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientToStableQuotient
      (preLieDifferenceQuotientAssociator hL hR a b c) =
    preLieDifferenceStableQuotientAssociator
      (preLieDifferenceQuotientToStableQuotient a)
      (preLieDifferenceQuotientToStableQuotient b)
      (preLieDifferenceQuotientToStableQuotient c) := by
  refine Quotient.inductionOn₃' a b c ?_
  intro a0 b0 c0
  simp [preLieDifferenceQuotientAssociator,
    preLieDifferenceStableQuotientAssociator,
    preLieDifferenceQuotientToStableQuotient_mul,
    preLieDifferenceQuotientToStableQuotient_mk,
    preLieDifferenceQuotientMul_mk,
    preLieDifferenceStableQuotientAssociator_mk]

/--
So the image of the conditional quotient associator is already symmetric under
swapping the first two inputs.
-/
theorem preLieDifferenceQuotientAssociator_maps_swap_left
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientToStableQuotient
      (preLieDifferenceQuotientAssociator hL hR a b c) =
    preLieDifferenceQuotientToStableQuotient
      (preLieDifferenceQuotientAssociator hL hR b a c) := by
  rw [preLieDifferenceQuotientToStableQuotient_associator hL hR,
    preLieDifferenceQuotientToStableQuotient_associator hL hR]
  exact preLieDifferenceStableQuotientMul_associator_swap_left _ _ _

/--
Under the original compatibility hypotheses, the smallest stable closure lies
inside the original defect submodule, hence equality holds.
-/
theorem preLieDifferenceStableSubmodule_le_preLieDifferenceSubmodule
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    preLieDifferenceStableSubmodule ≤ preLieDifferenceSubmodule := by
  simpa [preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule hL hR]

/--
Under the original compatibility hypotheses, the original concrete defect
quotient is canonically equivalent to the stable quotient.
-/
noncomputable def preLieDifferenceQuotientEquivStableQuotient
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    PreLieDifferenceQuotient ≃ₗ[ℤ] PreLieDifferenceStableQuotient :=
  Submodule.quotEquivOfEq
    preLieDifferenceSubmodule
    preLieDifferenceStableSubmodule
    (preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule hL hR).symm

@[simp] theorem preLieDifferenceQuotientEquivStableQuotient_mk
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : linearProofTreeCarrier) :
    preLieDifferenceQuotientEquivStableQuotient hL hR
      (mkPreLieDifferenceQuotient a) =
    mkPreLieDifferenceStableQuotient a := by
  rfl

/--
Under the original compatibility hypotheses, the canonical map to the stable
quotient agrees with the quotient equivalence induced by equality of
submodules.
-/
theorem preLieDifferenceQuotientEquivStableQuotient_apply_eq
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientEquivStableQuotient hL hR a =
      preLieDifferenceQuotientToStableQuotient a := by
  refine Quotient.inductionOn' a ?_
  intro x
  rfl

/--
So once the original left/right preservation hypotheses are proved, the
conditional quotient product already satisfies the required swap-left
associator symmetry on the original defect quotient itself.
-/
theorem preLieDifferenceQuotientAssociator_swap_left
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientAssociator hL hR a b c =
      preLieDifferenceQuotientAssociator hL hR b a c := by
  apply (preLieDifferenceQuotientEquivStableQuotient hL hR).injective
  rw [preLieDifferenceQuotientEquivStableQuotient_apply_eq hL hR,
    preLieDifferenceQuotientEquivStableQuotient_apply_eq hL hR]
  exact preLieDifferenceQuotientAssociator_maps_swap_left hL hR a b c

/--
The opposite multiplication on the unconditional stable quotient.

This is the version compatible with Mathlib's `RightPreLieRing` convention:
our proved associator symmetry is swap-left, so reversing the multiplication
turns it into the usual swap-right pre-Lie law.
-/
noncomputable def preLieDifferenceStableQuotientOppMul
    (a b : PreLieDifferenceStableQuotient) :
    PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientMul b a

@[simp] theorem preLieDifferenceStableQuotientOppMul_def
    (a b : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul a b =
      preLieDifferenceStableQuotientMul b a := rfl

@[simp] theorem preLieDifferenceStableQuotientOppMul_zero_left
    (a : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul 0 a = 0 := by
  change preLieDifferenceStableQuotientMul a 0 = 0
  simpa using LinearMap.map_zero (preLieDifferenceStableQuotientMul a)

@[simp] theorem preLieDifferenceStableQuotientOppMul_zero_right
    (a : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul a 0 = 0 := by
  change preLieDifferenceStableQuotientMul 0 a = 0
  exact LinearMap.congr_fun
    (LinearMap.map_zero preLieDifferenceStableQuotientMul) a

theorem preLieDifferenceStableQuotientOppMul_left_distrib
    (a b c : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul a (b + c) =
      preLieDifferenceStableQuotientOppMul a b +
        preLieDifferenceStableQuotientOppMul a c := by
  change preLieDifferenceStableQuotientMul (b + c) a =
    preLieDifferenceStableQuotientMul b a +
      preLieDifferenceStableQuotientMul c a
  simpa using LinearMap.congr_fun
    (LinearMap.map_add preLieDifferenceStableQuotientMul b c) a

theorem preLieDifferenceStableQuotientOppMul_right_distrib
    (a b c : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul (a + b) c =
      preLieDifferenceStableQuotientOppMul a c +
        preLieDifferenceStableQuotientOppMul b c := by
  change preLieDifferenceStableQuotientMul c (a + b) =
    preLieDifferenceStableQuotientMul c a +
      preLieDifferenceStableQuotientMul c b
  simpa using LinearMap.map_add (preLieDifferenceStableQuotientMul c) a b

/--
The opposite multiplication on the stable quotient satisfies Mathlib's
right pre-Lie identity.
-/
theorem preLieDifferenceStableQuotientOppMul_assoc_symm
    (a b c : PreLieDifferenceStableQuotient) :
    preLieDifferenceStableQuotientOppMul
        (preLieDifferenceStableQuotientOppMul a b) c
      -
      preLieDifferenceStableQuotientOppMul a
        (preLieDifferenceStableQuotientOppMul b c)
    =
    preLieDifferenceStableQuotientOppMul
        (preLieDifferenceStableQuotientOppMul a c) b
      -
      preLieDifferenceStableQuotientOppMul a
        (preLieDifferenceStableQuotientOppMul c b) := by
  have h := preLieDifferenceStableQuotientMul_associator_swap_left c b a
  unfold preLieDifferenceStableQuotientAssociator at h
  have hneg := congrArg Neg.neg h
  simpa [preLieDifferenceStableQuotientOppMul, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hneg

/--
Hence the unconditional stable quotient already carries an official Mathlib
`RightPreLieRing` structure, using the opposite multiplication.
-/
theorem preLieDifferenceStableQuotient_admitsMathlibRightPreLieRing :
    ∃ _inst : RightPreLieRing PreLieDifferenceStableQuotient, True := by
  letI : Mul PreLieDifferenceStableQuotient :=
    ⟨preLieDifferenceStableQuotientOppMul⟩
  letI : NonUnitalNonAssocRing PreLieDifferenceStableQuotient := {
    mul := preLieDifferenceStableQuotientOppMul
    left_distrib := preLieDifferenceStableQuotientOppMul_left_distrib
    right_distrib := preLieDifferenceStableQuotientOppMul_right_distrib
    zero_mul := preLieDifferenceStableQuotientOppMul_zero_left
    mul_zero := preLieDifferenceStableQuotientOppMul_zero_right
  }
  letI : RightPreLieRing PreLieDifferenceStableQuotient := {
    assoc_symm' := preLieDifferenceStableQuotientOppMul_assoc_symm
  }
  exact ⟨inferInstance, trivial⟩

/--
Consequently the unconditional stable quotient also admits the induced Mathlib
`LieRing` structure.
-/
theorem preLieDifferenceStableQuotient_admitsMathlibLieRing :
    ∃ _inst : LieRing PreLieDifferenceStableQuotient, True := by
  rcases preLieDifferenceStableQuotient_admitsMathlibRightPreLieRing with
    ⟨hpre, -⟩
  letI : RightPreLieRing PreLieDifferenceStableQuotient := hpre
  exact ⟨inferInstance, trivial⟩

/--
The opposite multiplication on the original concrete defect quotient, assuming
the raw grafting product descends there.
-/
noncomputable def preLieDifferenceQuotientOppMul
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b : PreLieDifferenceQuotient) :
    PreLieDifferenceQuotient :=
  preLieDifferenceQuotientMul hL hR b a

@[simp] theorem preLieDifferenceQuotientOppMul_zero_left
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientOppMul hL hR 0 a = 0 := by
  change preLieDifferenceQuotientMul hL hR a 0 = 0
  simpa using LinearMap.map_zero (preLieDifferenceQuotientMul hL hR a)

@[simp] theorem preLieDifferenceQuotientOppMul_zero_right
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientOppMul hL hR a 0 = 0 := by
  change preLieDifferenceQuotientMul hL hR 0 a = 0
  exact LinearMap.congr_fun
    (LinearMap.map_zero (preLieDifferenceQuotientMul hL hR)) a

theorem preLieDifferenceQuotientOppMul_left_distrib
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientOppMul hL hR a (b + c) =
      preLieDifferenceQuotientOppMul hL hR a b +
        preLieDifferenceQuotientOppMul hL hR a c := by
  change preLieDifferenceQuotientMul hL hR (b + c) a =
    preLieDifferenceQuotientMul hL hR b a +
      preLieDifferenceQuotientMul hL hR c a
  simpa using LinearMap.congr_fun
    (LinearMap.map_add (preLieDifferenceQuotientMul hL hR) b c) a

theorem preLieDifferenceQuotientOppMul_right_distrib
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientOppMul hL hR (a + b) c =
      preLieDifferenceQuotientOppMul hL hR a c +
        preLieDifferenceQuotientOppMul hL hR b c := by
  change preLieDifferenceQuotientMul hL hR c (a + b) =
    preLieDifferenceQuotientMul hL hR c a +
      preLieDifferenceQuotientMul hL hR c b
  simpa using LinearMap.map_add (preLieDifferenceQuotientMul hL hR c) a b

/--
Under the preservation hypotheses, the opposite multiplication on the original
defect quotient satisfies Mathlib's right pre-Lie identity.
-/
theorem preLieDifferenceQuotientOppMul_assoc_symm
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b c : PreLieDifferenceQuotient) :
    preLieDifferenceQuotientOppMul hL hR
        (preLieDifferenceQuotientOppMul hL hR a b) c
      -
      preLieDifferenceQuotientOppMul hL hR a
        (preLieDifferenceQuotientOppMul hL hR b c)
    =
    preLieDifferenceQuotientOppMul hL hR
        (preLieDifferenceQuotientOppMul hL hR a c) b
      -
      preLieDifferenceQuotientOppMul hL hR a
        (preLieDifferenceQuotientOppMul hL hR c b) := by
  have h := preLieDifferenceQuotientAssociator_swap_left hL hR c b a
  have hneg := congrArg Neg.neg h
  simpa [preLieDifferenceQuotientOppMul, preLieDifferenceQuotientAssociator,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

/--
If the original defect quotient really does admit the descended grafting
product, then it carries an official Mathlib `RightPreLieRing` structure via
the opposite multiplication.
-/
theorem preLieDifferenceQuotient_admitsMathlibRightPreLieRing
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    ∃ _inst : RightPreLieRing PreLieDifferenceQuotient, True := by
  letI : Mul PreLieDifferenceQuotient :=
    ⟨preLieDifferenceQuotientOppMul hL hR⟩
  letI : NonUnitalNonAssocRing PreLieDifferenceQuotient := {
    mul := preLieDifferenceQuotientOppMul hL hR
    left_distrib := preLieDifferenceQuotientOppMul_left_distrib hL hR
    right_distrib := preLieDifferenceQuotientOppMul_right_distrib hL hR
    zero_mul := preLieDifferenceQuotientOppMul_zero_left hL hR
    mul_zero := preLieDifferenceQuotientOppMul_zero_right hL hR
  }
  letI : RightPreLieRing PreLieDifferenceQuotient := {
    assoc_symm' := preLieDifferenceQuotientOppMul_assoc_symm hL hR
  }
  exact ⟨inferInstance, trivial⟩

/--
Under the preservation hypotheses, the original defect quotient also admits the
induced Mathlib `LieRing` structure.
-/
theorem preLieDifferenceQuotient_admitsMathlibLieRing
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    ∃ _inst : LieRing PreLieDifferenceQuotient, True := by
  rcases preLieDifferenceQuotient_admitsMathlibRightPreLieRing hL hR with
    ⟨hpre, -⟩
  letI : RightPreLieRing PreLieDifferenceQuotient := hpre
  exact ⟨inferInstance, trivial⟩

/--
The full algebraic consequence package extracted from a future quotient
product, once its generator laws have been proved.

This is intentionally weaker than a direct Mathlib typeclass instance. It keeps
the connection to the current proof-tree development explicit and avoids
introducing global multiplication instances before the descended quotient
product has actually been defined.
-/
structure WeightedPreLieLinearProduct where
  mul :
    linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier →ₗ[ℤ] linearProofTreeCarrier
  rightPreLie :
    ∀ a b c : linearProofTreeCarrier,
      assoc[mul] a b c = assoc[mul] a c b
  respectsWeight :
    ∀ {m n : Nat} {a b : linearProofTreeCarrier},
      a ∈ weightSubmodule m →
      b ∈ weightSubmodule n →
      mul a b ∈ weightSubmodule (m + n)

/--
Any generator-compatible weighted tree product yields the full linear graded
pre-Lie package on the existing proof-tree carrier.
-/
def GeneratorCompatibleWeightedTreeProduct.toWeightedPreLieLinearProduct
    (p : GeneratorCompatibleWeightedTreeProduct) :
    WeightedPreLieLinearProduct where
  mul := p.mul
  rightPreLie := p.rightPreLie_everywhere
  respectsWeight := p.respects_weight_everywhere

namespace WeightedPreLieLinearProduct

/--
If two weight indices are equal, the corresponding homogeneous pieces of the
linear proof-tree carrier are canonically isomorphic.
-/
def weightSubmoduleCongr {m n : Nat} (h : m = n) :
    weightSubmodule m ≃ₗ[ℤ] weightSubmodule n where
  toFun a := ⟨a.1, by simpa [h] using a.2⟩
  invFun a := ⟨a.1, by simpa [h] using a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
A conservative type synonym for the existing linear proof-tree carrier, equipped
later with the multiplication coming from a bundled weighted pre-Lie product.

This lets us connect to Mathlib's official `RightPreLieRing` and
`RightPreLieAlgebra` classes without changing the ambient carrier used by the
current proof-tree development.
-/
abbrev Carrier (_p : WeightedPreLieLinearProduct) := linearProofTreeCarrier

instance instMul (p : WeightedPreLieLinearProduct) : Mul p.Carrier where
  mul a b := p.mul a b

@[simp] theorem mul_def
    (p : WeightedPreLieLinearProduct)
    (a b : p.Carrier) :
    a * b = p.mul a b := rfl

/--
The multiplication induced by a bundled weighted pre-Lie product restricts to a
bilinear map between the homogeneous weight pieces.
-/
def weightPieceMul
    (p : WeightedPreLieLinearProduct) (m n : Nat) :
    weightSubmodule m →ₗ[ℤ] weightSubmodule n →ₗ[ℤ] weightSubmodule (m + n) where
  toFun a :=
    { toFun := fun b => ⟨p.mul a.1 b.1, p.respectsWeight a.2 b.2⟩
      map_add' := by
        intro b1 b2
        apply Subtype.ext
        ext t
        simp [LinearMap.map_add]
      map_smul' := by
        intro z b
        apply Subtype.ext
        ext t
        simp [LinearMap.map_smul]
    }
  map_add' := by
    intro a1 a2
    ext b t
    simp [LinearMap.map_add]
  map_smul' := by
    intro z a
    ext b t
    simp [LinearMap.map_smul]

@[simp] theorem weightPieceMul_apply
    (p : WeightedPreLieLinearProduct) (m n : Nat)
    (a : weightSubmodule m) (b : weightSubmodule n) :
    ((p.weightPieceMul m n a b : weightSubmodule (m + n)) :
      linearProofTreeCarrier) = p.mul a.1 b.1 := rfl

/--
Any bundled weighted pre-Lie product on the linear proof-tree carrier can be
realized as an official Mathlib `RightPreLieRing` on the same underlying
additive group, after equipping the carrier with the corresponding
multiplication.

We state this as an existence theorem rather than a global instance to keep the
connection to the existing proof-tree carrier explicit and to avoid polluting
instance search on the ambient `Finsupp` type.
-/
theorem admitsMathlibRightPreLieRing
    (p : WeightedPreLieLinearProduct) :
    ∃ _inst : RightPreLieRing p.Carrier, True := by
  letI : Mul p.Carrier := ⟨fun a b => p.mul a b⟩
  letI : NonUnitalNonAssocRing p.Carrier := {
    mul := fun a b => p.mul a b
    left_distrib a b c := by
      show p.mul a (b + c) = p.mul a b + p.mul a c
      simp
    right_distrib a b c := by
      show p.mul (a + b) c = p.mul a c + p.mul b c
      simp
    zero_mul a := by
      show p.mul 0 a = 0
      simp
    mul_zero a := by
      show p.mul a 0 = 0
      simp
  }
  letI : RightPreLieRing p.Carrier := {
    assoc_symm' a b c := by
      show p.mul (p.mul a b) c - p.mul a (p.mul b c) =
        p.mul (p.mul a c) b - p.mul a (p.mul c b)
      exact p.rightPreLie a b c
  }
  exact ⟨inferInstance, trivial⟩

/--
Consequently, the same data also yields Mathlib's canonical Lie ring obtained
by antisymmetrizing the pre-Lie multiplication.
-/
theorem admitsMathlibLieRing
    (p : WeightedPreLieLinearProduct) :
    ∃ _inst : LieRing p.Carrier, True := by
  rcases admitsMathlibRightPreLieRing p with ⟨hpre, -⟩
  letI : RightPreLieRing p.Carrier := hpre
  exact ⟨inferInstance, trivial⟩

/-!
### Universal enveloping algebra from a bundled weighted pre-Lie product

This packages the standard UEA interface once a specific Mathlib Lie ring
instance has been chosen from the existence theorem above.
-/

noncomputable def lieRing (p : WeightedPreLieLinearProduct) :
    LieRing p.Carrier :=
  Classical.choose (admitsMathlibLieRing p)

noncomputable local instance (p : WeightedPreLieLinearProduct) : LieRing p.Carrier :=
  p.lieRing

/-- The universal enveloping algebra attached to a bundled weighted pre-Lie product. -/
noncomputable abbrev UEA (p : WeightedPreLieLinearProduct) :=
  UniversalEnvelopingAlgebra ℤ p.Carrier

/-- The canonical Lie algebra morphism into the UEA. -/
noncomputable abbrev UEA_ι (p : WeightedPreLieLinearProduct) :
    p.Carrier →ₗ⁅ℤ⁆ p.UEA :=
  UniversalEnvelopingAlgebra.ι ℤ (L := p.Carrier)

/-- The underlying map from the carrier into its UEA. -/
noncomputable def toUEA (p : WeightedPreLieLinearProduct) (a : p.Carrier) :
    p.UEA :=
  p.UEA_ι a

@[simp] theorem toUEA_eq_ι
    (p : WeightedPreLieLinearProduct) (a : p.Carrier) :
    p.toUEA a = p.UEA_ι a := rfl

section

variable {A : Type*} [Ring A] [Algebra ℤ A]
local instance (priority := 1000) : LieAlgebra ℤ A :=
  LieAlgebra.ofAssociativeAlgebra

/-- The universal enveloping algebra lift for any bundled weighted pre-Lie product. -/
noncomputable def UEA_lift
    (p : WeightedPreLieLinearProduct) (f : p.Carrier →ₗ⁅ℤ⁆ A) :
    p.UEA →ₐ[ℤ] A :=
  UniversalEnvelopingAlgebra.lift ℤ f

@[simp] theorem UEA_ι_comp_lift
    (p : WeightedPreLieLinearProduct) (f : p.Carrier →ₗ⁅ℤ⁆ A) :
    p.UEA_lift f ∘ p.UEA_ι = f := by
  ext x
  change
      (UniversalEnvelopingAlgebra.lift ℤ f)
        (UniversalEnvelopingAlgebra.ι ℤ x) = f x
  exact UniversalEnvelopingAlgebra.lift_ι_apply (R := ℤ) (f := f) (x := x)

end

end WeightedPreLieLinearProduct

/--
Any generator-compatible weighted tree product therefore admits a realization as
an official Mathlib `RightPreLieRing` on the existing linear proof-tree carrier.

This is the cleanest point at which the current quotient-side proof theory
connects to Mathlib's standard pre-Lie hierarchy.
-/
theorem GeneratorCompatibleWeightedTreeProduct.admitsMathlibRightPreLieRing
    (p : GeneratorCompatibleWeightedTreeProduct) :
    ∃ _inst :
      RightPreLieRing
        (WeightedPreLieLinearProduct.Carrier
          (p.toWeightedPreLieLinearProduct)),
      True := by
  exact WeightedPreLieLinearProduct.admitsMathlibRightPreLieRing
    (p.toWeightedPreLieLinearProduct)

/--
By antisymmetrization, the same generator-compatible weighted tree product also
admits the induced Mathlib `LieRing` structure on the same underlying additive
group.
-/
theorem GeneratorCompatibleWeightedTreeProduct.admitsMathlibLieRing
    (p : GeneratorCompatibleWeightedTreeProduct) :
    ∃ _inst :
        LieRing
        (WeightedPreLieLinearProduct.Carrier
          (p.toWeightedPreLieLinearProduct)),
      True := by
  exact WeightedPreLieLinearProduct.admitsMathlibLieRing
    (p.toWeightedPreLieLinearProduct)

/-!
### Universal enveloping algebra for generator-compatible products

This records the UEA interface once we pick the canonical Lie ring instance
coming from the bundled weighted pre-Lie product.
-/

namespace GeneratorCompatibleWeightedTreeProduct

-- Use the bundled carrier to avoid requiring a global `LieRing` instance on
-- `linearProofTreeCarrier` in the wrapper signatures.
abbrev Carrier (p : GeneratorCompatibleWeightedTreeProduct) :=
  (p.toWeightedPreLieLinearProduct).Carrier

noncomputable instance instLieRing
    (p : GeneratorCompatibleWeightedTreeProduct) :
    LieRing p.Carrier :=
  (p.toWeightedPreLieLinearProduct).lieRing

/-- The universal enveloping algebra attached to a generator-compatible product. -/
noncomputable abbrev UEA (p : GeneratorCompatibleWeightedTreeProduct) :=
  (p.toWeightedPreLieLinearProduct).UEA

/-- The canonical Lie algebra morphism into the UEA. -/
noncomputable def UEA_ι (p : GeneratorCompatibleWeightedTreeProduct) :
    p.Carrier →ₗ⁅ℤ⁆ p.UEA :=
  (p.toWeightedPreLieLinearProduct).UEA_ι

/-- The underlying map from the carrier into its UEA. -/
noncomputable def toUEA (p : GeneratorCompatibleWeightedTreeProduct)
    (a : p.Carrier) : p.UEA :=
  (p.toWeightedPreLieLinearProduct).toUEA a

@[simp] theorem toUEA_eq_ι
    (p : GeneratorCompatibleWeightedTreeProduct) (a : p.Carrier) :
    p.toUEA a = p.UEA_ι a := rfl

section

variable {A : Type*} [Ring A] [Algebra ℤ A]
local instance (priority := 1000) : LieAlgebra ℤ A :=
  LieAlgebra.ofAssociativeAlgebra

/-- The universal enveloping algebra lift for a generator-compatible product. -/
noncomputable def UEA_lift
    (p : GeneratorCompatibleWeightedTreeProduct)
    (f : p.Carrier →ₗ⁅ℤ⁆ A) :
    p.UEA →ₐ[ℤ] A :=
  (p.toWeightedPreLieLinearProduct).UEA_lift f

@[simp] theorem UEA_ι_comp_lift
    (p : GeneratorCompatibleWeightedTreeProduct)
    (f : p.Carrier →ₗ⁅ℤ⁆ A) :
    p.UEA_lift f ∘ p.UEA_ι = f := by
  exact (p.toWeightedPreLieLinearProduct).UEA_ι_comp_lift f

end

end GeneratorCompatibleWeightedTreeProduct

/--
For any future generator-compatible weighted product, the multiplication of two
tree generators canonically lands in the homogeneous piece of additive degree.
-/
noncomputable def GeneratorCompatibleWeightedTreeProduct.weightedMulGenerators
    (p : GeneratorCompatibleWeightedTreeProduct) (x y : PTree) :
    weightSubmodule (PTree.graftWeight x + PTree.graftWeight y) :=
  (p.toWeightedPreLieLinearProduct).weightPieceMul
    (PTree.graftWeight x) (PTree.graftWeight y)
    (weightedTreeGen x) (weightedTreeGen y)

@[simp] theorem GeneratorCompatibleWeightedTreeProduct.weightedMulGenerators_val
    (p : GeneratorCompatibleWeightedTreeProduct) (x y : PTree) :
    ((p.weightedMulGenerators x y :
      weightSubmodule (PTree.graftWeight x + PTree.graftWeight y)) :
      linearProofTreeCarrier) =
      p.mul (treeGen x) (treeGen y) := rfl

/--
For a generator-compatible weighted tree product, the multiplication on the
ambient linear carrier restricts to a bilinear map on homogeneous pieces.
-/
def GeneratorCompatibleWeightedTreeProduct.weightPieceMul
    (p : GeneratorCompatibleWeightedTreeProduct) (m n : Nat) :
    weightSubmodule m →ₗ[ℤ] weightSubmodule n →ₗ[ℤ] weightSubmodule (m + n) :=
  (p.toWeightedPreLieLinearProduct).weightPieceMul m n

@[simp] theorem GeneratorCompatibleWeightedTreeProduct.weightPieceMul_apply
    (p : GeneratorCompatibleWeightedTreeProduct) (m n : Nat)
    (a : weightSubmodule m) (b : weightSubmodule n) :
    ((p.weightPieceMul m n a b : weightSubmodule (m + n)) :
      linearProofTreeCarrier) = p.mul a.1 b.1 := rfl

/-!
### Universal enveloping algebra for the stable quotient

This is the first place where we can safely hook into Mathlib's standard
universal enveloping algebra, because the smallest stable quotient already
carries a verified Lie ring structure.
-/

noncomputable section UniversalEnvelopingStable

noncomputable def preLieDifferenceStableQuotientLieRing :
    LieRing PreLieDifferenceStableQuotient := by
  letI : Mul PreLieDifferenceStableQuotient :=
    ⟨preLieDifferenceStableQuotientOppMul⟩
  letI : RightPreLieRing PreLieDifferenceStableQuotient := {
    toNonUnitalNonAssocRing := {
      toAddCommGroup := Submodule.Quotient.addCommGroup
        preLieDifferenceStableSubmodule
      mul := preLieDifferenceStableQuotientOppMul
      left_distrib := preLieDifferenceStableQuotientOppMul_left_distrib
      right_distrib := preLieDifferenceStableQuotientOppMul_right_distrib
      zero_mul := preLieDifferenceStableQuotientOppMul_zero_left
      mul_zero := preLieDifferenceStableQuotientOppMul_zero_right
    }
    assoc_symm' := preLieDifferenceStableQuotientOppMul_assoc_symm
  }
  exact LieAdmissibleRing.instLieRing

local instance : LieRing PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientLieRing

/-- The universal enveloping algebra of the stable quotient Lie ring. -/
noncomputable abbrev preLieDifferenceStableQuotientUEA :=
  UniversalEnvelopingAlgebra ℤ PreLieDifferenceStableQuotient

/-- The canonical Lie algebra morphism into the stable universal enveloping algebra. -/
noncomputable abbrev preLieDifferenceStableQuotientUEA_ι :
    PreLieDifferenceStableQuotient →ₗ⁅ℤ⁆ preLieDifferenceStableQuotientUEA :=
  UniversalEnvelopingAlgebra.ι ℤ (L := PreLieDifferenceStableQuotient)

/-- The underlying linear map of the stable quotient UEA insertion. -/
noncomputable abbrev preLieDifferenceStableQuotientUEA_ι_linear :
    PreLieDifferenceStableQuotient →ₗ[ℤ] preLieDifferenceStableQuotientUEA :=
  preLieDifferenceStableQuotientUEA_ι.toLinearMap

/-- The composite map from the raw linear carrier to the stable UEA. -/
noncomputable def preLieDifferenceStableQuotientToUEA
    (a : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientUEA :=
  preLieDifferenceStableQuotientUEA_ι (mkPreLieDifferenceStableQuotient a)

@[simp] theorem preLieDifferenceStableQuotientToUEA_zero :
    preLieDifferenceStableQuotientToUEA 0 = 0 := by
  let f : PreLieDifferenceStableQuotient →+ preLieDifferenceStableQuotientUEA :=
    preLieDifferenceStableQuotientUEA_ι.toLinearMap.toAddMonoidHom
  change f (mkPreLieDifferenceStableQuotient 0) = 0
  rw [show mkPreLieDifferenceStableQuotient (0 : linearProofTreeCarrier) = 0 by simp]
  exact f.map_zero

@[simp] theorem preLieDifferenceStableQuotientToUEA_add
    (a b : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientToUEA (a + b) =
      preLieDifferenceStableQuotientToUEA a +
        preLieDifferenceStableQuotientToUEA b := by
  let f : PreLieDifferenceStableQuotient →+ preLieDifferenceStableQuotientUEA :=
    preLieDifferenceStableQuotientUEA_ι.toLinearMap.toAddMonoidHom
  change f (mkPreLieDifferenceStableQuotient (a + b)) =
      f (mkPreLieDifferenceStableQuotient a) +
        f (mkPreLieDifferenceStableQuotient b)
  rw [show mkPreLieDifferenceStableQuotient (a + b) =
      mkPreLieDifferenceStableQuotient a + mkPreLieDifferenceStableQuotient b by
        simpa using (mkPreLieDifferenceStableQuotient.map_add a b)]
  exact f.map_add _ _

@[simp] theorem preLieDifferenceStableQuotientToUEA_smul
    (n : Int) (a : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientToUEA (n • a) =
      n • preLieDifferenceStableQuotientToUEA a := by
  let f : PreLieDifferenceStableQuotient →+ preLieDifferenceStableQuotientUEA :=
    preLieDifferenceStableQuotientUEA_ι.toLinearMap.toAddMonoidHom
  change f (mkPreLieDifferenceStableQuotient (n • a)) =
      n • f (mkPreLieDifferenceStableQuotient a)
  rw [show mkPreLieDifferenceStableQuotient (n • a) =
      n • mkPreLieDifferenceStableQuotient a by
        simpa using
          (AddMonoidHom.map_zsmul
            (mkPreLieDifferenceStableQuotient.toAddMonoidHom) a n)]
  exact f.map_zsmul (mkPreLieDifferenceStableQuotient a) n

-- Note: the linear map packaging is postponed because the module structure
-- induced by the `LieRing` instance is not definitionally equal to the
-- quotient module used by `mkPreLieDifferenceStableQuotient`.

@[simp] theorem preLieDifferenceStableQuotientToUEA_preLieDifferenceGenerators_eq_zero
    (x y z : PTree) :
    preLieDifferenceStableQuotientToUEA
        (preLieDifferenceGenerators x y z) =
      preLieDifferenceStableQuotientUEA_ι 0 := by
  have hzero :
      mkPreLieDifferenceStableQuotient
        (preLieDifferenceGenerators x y z) = 0 := by
    simpa using
      mkPreLieDifferenceStableQuotient_preLieDifferenceGenerators_eq_zero x y z
  simpa [preLieDifferenceStableQuotientToUEA, hzero]

section

variable {A : Type*} [Ring A] [Algebra ℤ A]
local instance (priority := 1000) : LieAlgebra ℤ A :=
  LieAlgebra.ofAssociativeAlgebra

/-- The universal enveloping algebra lift for the stable quotient. -/
noncomputable def preLieDifferenceStableQuotientUEA_lift
    (f : PreLieDifferenceStableQuotient →ₗ⁅ℤ⁆ A) :
    preLieDifferenceStableQuotientUEA →ₐ[ℤ] A :=
  (UniversalEnvelopingAlgebra.lift ℤ f)

@[simp] theorem preLieDifferenceStableQuotientUEA_ι_comp_lift
    (f : PreLieDifferenceStableQuotient →ₗ⁅ℤ⁆ A) :
    preLieDifferenceStableQuotientUEA_lift f ∘
        preLieDifferenceStableQuotientUEA_ι = f := by
  ext x
  change
      (UniversalEnvelopingAlgebra.lift ℤ f)
        (UniversalEnvelopingAlgebra.ι ℤ x) = f x
  exact UniversalEnvelopingAlgebra.lift_ι_apply (R := ℤ) (f := f) (x := x)

end

end UniversalEnvelopingStable

/-!
### Universal enveloping algebra for the original defect quotient (conditional)

This section records the same Mathlib interface for the original defect
quotient, provided the generator-level preservation hypotheses hold.
-/

noncomputable section UniversalEnvelopingDefect

variable (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
variable (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)

noncomputable def preLieDifferenceQuotientLieRing :
    LieRing PreLieDifferenceQuotient := by
  letI : Mul PreLieDifferenceQuotient :=
    ⟨preLieDifferenceQuotientOppMul hL hR⟩
  letI : RightPreLieRing PreLieDifferenceQuotient := {
    toNonUnitalNonAssocRing := {
      toAddCommGroup := Submodule.Quotient.addCommGroup preLieDifferenceSubmodule
      mul := preLieDifferenceQuotientOppMul hL hR
      left_distrib := preLieDifferenceQuotientOppMul_left_distrib hL hR
      right_distrib := preLieDifferenceQuotientOppMul_right_distrib hL hR
      zero_mul := preLieDifferenceQuotientOppMul_zero_left hL hR
      mul_zero := preLieDifferenceQuotientOppMul_zero_right hL hR
    }
    assoc_symm' := preLieDifferenceQuotientOppMul_assoc_symm hL hR
  }
  exact LieAdmissibleRing.instLieRing

-- Note: the conditional defect quotient UEA interface is postponed for now.
-- The stable UEA is available unconditionally and supports the downstream
-- constructions we need.

end UniversalEnvelopingDefect

/-!
### Comparing the defect quotient with the stable UEA target

The stable UEA is available unconditionally, so we can always post-compose the
canonical defect-to-stable quotient map to land in the stable UEA.
-/

section DefectToStableUEA

variable (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
variable (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)

noncomputable local instance : LieRing PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientLieRing

/-- The defect quotient map followed by the stable UEA insertion. -/
noncomputable def preLieDifferenceQuotientToStableUEA
    (x : PreLieDifferenceQuotient) : preLieDifferenceStableQuotientUEA :=
  preLieDifferenceStableQuotientUEA_ι (preLieDifferenceQuotientToStableQuotient x)

@[simp] theorem preLieDifferenceQuotientToStableUEA_mk
    (a : linearProofTreeCarrier) :
    preLieDifferenceQuotientToStableUEA (mkPreLieDifferenceQuotient a) =
      preLieDifferenceStableQuotientToUEA a := by
  simp [preLieDifferenceQuotientToStableUEA,
    preLieDifferenceStableQuotientToUEA,
    preLieDifferenceQuotientToStableQuotient_mk]

@[simp] theorem preLieDifferenceQuotientToStableUEA_preLieDifferenceGenerators_eq_zero
    (x y z : PTree) :
    preLieDifferenceQuotientToStableUEA
        (mkPreLieDifferenceQuotient (preLieDifferenceGenerators x y z)) =
      preLieDifferenceStableQuotientUEA_ι 0 := by
  simpa [preLieDifferenceQuotientToStableUEA_mk] using
    (preLieDifferenceStableQuotientToUEA_preLieDifferenceGenerators_eq_zero x y z)

end DefectToStableUEA

/-!
### Stable UEA images of tree generators

These are lightweight conveniences for later OG-style constructions.
-/

section StableUEATreeGenerators

/-- The stable UEA image of a tree generator. -/
noncomputable def stableUEA_treeGen (x : PTree) :
    preLieDifferenceStableQuotientUEA :=
  preLieDifferenceStableQuotientToUEA (treeGen x)

@[simp] theorem stableUEA_treeGen_eq_ι (x : PTree) :
    stableUEA_treeGen x =
      preLieDifferenceStableQuotientUEA_ι
        (mkPreLieDifferenceStableQuotient (treeGen x)) := rfl

@[simp] theorem preLieDifferenceQuotientToStableUEA_treeGen (x : PTree) :
    preLieDifferenceQuotientToStableUEA
        (mkPreLieDifferenceQuotient (treeGen x)) =
      stableUEA_treeGen x := by
  simp [stableUEA_treeGen, preLieDifferenceQuotientToStableUEA_mk]

end StableUEATreeGenerators

-- Note: the UEA-lift-on-generators lemma is postponed to avoid instance
-- resolution noise in goals; it is a convenience rather than a blocker.

/-!
### The stable UEA span of tree generators

This is a minimal linear submodule capturing the images of all tree generators
inside the stable universal enveloping algebra.
-/

section StableUEASpan

/-- The set of stable UEA images of tree generators. -/
def stableUEA_treeGenSet : Set preLieDifferenceStableQuotientUEA :=
  { w | ∃ x : PTree, w = stableUEA_treeGen x }

/-- The ℤ-submodule spanned by the stable UEA tree-generator images. -/
def stableUEA_treeGenSpan : Submodule ℤ preLieDifferenceStableQuotientUEA :=
  Submodule.span ℤ stableUEA_treeGenSet

@[simp] theorem stableUEA_treeGen_mem_span (x : PTree) :
    stableUEA_treeGen x ∈ stableUEA_treeGenSpan := by
  exact Submodule.subset_span ⟨x, rfl⟩

end StableUEASpan

/-!
### Oudom–Guin coproduct interface (stable UEA)

We record the coproduct data for the stable UEA as a linear map into the tensor
product, leaving axioms (coassociativity, etc.) to later stages.
-/

section StableUEAComultiplication

abbrev stableUEATensor :=
  TensorProduct ℤ preLieDifferenceStableQuotientUEA preLieDifferenceStableQuotientUEA

structure StableUEAComultiplication where
  comul :
    preLieDifferenceStableQuotientUEA →ₗ[ℤ]
      TensorProduct ℤ preLieDifferenceStableQuotientUEA preLieDifferenceStableQuotientUEA
  counit : preLieDifferenceStableQuotientUEA →ₗ[ℤ] ℤ

def StableUEAComulOnGenerators (Δ : StableUEAComultiplication) : Prop :=
  ∀ x : PTree,
    Δ.comul (stableUEA_treeGen x) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)

def StableUEACounitOnGenerators (Δ : StableUEAComultiplication) : Prop :=
  ∀ x : PTree, Δ.counit (stableUEA_treeGen x) = 0

def StableUEAComulOne (Δ : StableUEAComultiplication) : Prop :=
  Δ.comul 1 =
    TensorProduct.tmul ℤ (1 : preLieDifferenceStableQuotientUEA)
      (1 : preLieDifferenceStableQuotientUEA)

def StableUEACounitOne (Δ : StableUEAComultiplication) : Prop :=
  Δ.counit 1 = 1

structure StableUEAComultiplicationAxioms (Δ : StableUEAComultiplication) : Prop where
  comul_on_generators : StableUEAComulOnGenerators Δ
  counit_on_generators : StableUEACounitOnGenerators Δ
  comul_one : StableUEAComulOne Δ
  counit_one : StableUEACounitOne Δ

structure StableUEAComultiplicationData where
  Δ : StableUEAComultiplication
  axioms : StableUEAComultiplicationAxioms Δ

def StableUEAComultiplicationData.comul (D : StableUEAComultiplicationData) :=
  D.Δ.comul

def StableUEAComultiplicationData.counit (D : StableUEAComultiplicationData) :=
  D.Δ.counit

@[simp] theorem StableUEAComultiplicationData.comul_on_generators
    (D : StableUEAComultiplicationData) :
    StableUEAComulOnGenerators D.Δ :=
  D.axioms.comul_on_generators

@[simp] theorem StableUEAComultiplicationData.counit_on_generators
    (D : StableUEAComultiplicationData) :
    StableUEACounitOnGenerators D.Δ :=
  D.axioms.counit_on_generators

def StableUEAAntipodeOnGenerators (S : preLieDifferenceStableQuotientUEA →ₗ[ℤ]
    preLieDifferenceStableQuotientUEA) : Prop :=
  ∀ x : PTree, S (stableUEA_treeGen x) = -stableUEA_treeGen x

structure StableUEACoalgebraAxioms (Δ : StableUEAComultiplication) : Prop where
  coassoc :
    (TensorProduct.assoc ℤ
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA).toLinearMap ∘ₗ
        (Δ.comul.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ Δ.comul =
      (Δ.comul.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ Δ.comul
  rTensor_counit_comp_comul :
    (Δ.counit.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ Δ.comul =
      TensorProduct.mk ℤ _ _ 1
  lTensor_counit_comp_comul :
    (Δ.counit.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ Δ.comul =
      (TensorProduct.mk ℤ _ _).flip 1

structure StableUEACoalgebraData where
  Δ : StableUEAComultiplication
  axioms : StableUEACoalgebraAxioms Δ

def StableUEACoalgebraData.comul (D : StableUEACoalgebraData) :=
  D.Δ.comul

def StableUEACoalgebraData.counit (D : StableUEACoalgebraData) :=
  D.Δ.counit

@[simp] theorem StableUEACoalgebraData.coassoc
    (D : StableUEACoalgebraData) :
    (TensorProduct.assoc ℤ
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA).toLinearMap ∘ₗ
        (D.Δ.comul.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ D.Δ.comul =
      (D.Δ.comul.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ D.Δ.comul :=
  D.axioms.coassoc

@[simp] theorem StableUEACoalgebraData.rTensor_counit_comp_comul
    (D : StableUEACoalgebraData) :
    (D.Δ.counit.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ D.Δ.comul =
      TensorProduct.mk ℤ _ _ 1 :=
  D.axioms.rTensor_counit_comp_comul

@[simp] theorem StableUEACoalgebraData.lTensor_counit_comp_comul
    (D : StableUEACoalgebraData) :
    (D.Δ.counit.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ D.Δ.comul =
      (TensorProduct.mk ℤ _ _).flip 1 :=
  D.axioms.lTensor_counit_comp_comul

section StableUEACoalgebraCompatibility

variable [Coalgebra ℤ preLieDifferenceStableQuotientUEA]

noncomputable def stableUEAComultiplication_ofCoalgebra :
    StableUEAComultiplication where
  comul := Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
  counit := Coalgebra.counit (R := ℤ) (A := preLieDifferenceStableQuotientUEA)

noncomputable def stableUEACoalgebraAxioms_ofCoalgebra :
    StableUEACoalgebraAxioms stableUEAComultiplication_ofCoalgebra := by
  refine
    { coassoc := ?_
      rTensor_counit_comp_comul := ?_
      lTensor_counit_comp_comul := ?_ }
  · simpa using
      (Coalgebra.coassoc (R := ℤ) (A := preLieDifferenceStableQuotientUEA))
  · simpa using
      (Coalgebra.rTensor_counit_comp_comul
        (R := ℤ) (A := preLieDifferenceStableQuotientUEA))
  · simpa using
      (Coalgebra.lTensor_counit_comp_comul
        (R := ℤ) (A := preLieDifferenceStableQuotientUEA))

noncomputable def stableUEACoalgebraData_ofCoalgebra :
    StableUEACoalgebraData :=
  ⟨stableUEAComultiplication_ofCoalgebra, stableUEACoalgebraAxioms_ofCoalgebra⟩

end StableUEACoalgebraCompatibility

section StableUEABialgebra

variable [Semiring stableUEATensor]
variable [Algebra ℤ stableUEATensor]

structure StableUEABialgebraData where
  coalgebra : StableUEACoalgebraData
  comulAlgHom : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor
  counitAlgHom : preLieDifferenceStableQuotientUEA →ₐ[ℤ] ℤ
  comulAlgHom_apply :
    ∀ x, comulAlgHom x = coalgebra.Δ.comul x
  counitAlgHom_apply :
    ∀ x, counitAlgHom x = coalgebra.Δ.counit x

def StableUEABialgebraData.comul (D : StableUEABialgebraData) :=
  D.coalgebra.Δ.comul

def StableUEABialgebraData.counit (D : StableUEABialgebraData) :=
  D.coalgebra.Δ.counit

@[simp] theorem StableUEABialgebraData.comulAlgHom_apply_simp
    (D : StableUEABialgebraData) (x : preLieDifferenceStableQuotientUEA) :
    D.comulAlgHom x = D.comul x :=
  D.comulAlgHom_apply x

@[simp] theorem StableUEABialgebraData.counitAlgHom_apply_simp
    (D : StableUEABialgebraData) (x : preLieDifferenceStableQuotientUEA) :
    D.counitAlgHom x = D.counit x :=
  D.counitAlgHom_apply x

section StableUEABialgebraCompatibility

open Bialgebra

-- The compatibility construction is postponed because the module structures
-- induced by the `Bialgebra` instance are not definitionally equal to the
-- ones used by the coalgebra wrapper on the stable UEA.

end StableUEABialgebraCompatibility

end StableUEABialgebra

-- Note: a concrete OG comultiplication candidate should ultimately provide
-- `StableUEABialgebraData` (and then an antipode), but this requires the
-- tensor product semiring/algebra instances that are not yet available in
-- the local snapshot.

end StableUEAComultiplication

/-!
### Left and right pre-Lie conventions (minimal, algebra-agnostic)

These are lightweight laws used only to align our right-pre-Lie development
with the left-pre-Lie conventions in Guin–Oudom style statements.
-/

section PreLieConventions

variable {A : Type*} [AddCommGroup A] [Semigroup A]

def LeftPreLieLaw (A : Type*) [AddCommGroup A] [Mul A] : Prop :=
  ∀ x y z : A, x * (y * z) - (x * y) * z = y * (x * z) - (y * x) * z

def RightPreLieLaw (A : Type*) [AddCommGroup A] [Mul A] : Prop :=
  ∀ x y z : A, (x * y) * z - x * (y * z) = (x * z) * y - x * (z * y)

theorem associative_leftPreLieLaw : LeftPreLieLaw A := by
  intro x y z
  have h1 : x * (y * z) = (x * y) * z := by
    simpa using (mul_assoc x y z).symm
  have h2 : y * (x * z) = (y * x) * z := by
    simpa using (mul_assoc y x z).symm
  calc
    x * (y * z) - (x * y) * z = 0 := by
      simp [h1]
    _ = y * (x * z) - (y * x) * z := by
      simp [h2]

theorem associative_rightPreLieLaw : RightPreLieLaw A := by
  intro x y z
  have h1 : (x * y) * z = x * (y * z) := by
    simpa using (mul_assoc x y z)
  have h2 : (x * z) * y = x * (z * y) := by
    simpa using (mul_assoc x z y)
  calc
    (x * y) * z - x * (y * z) = 0 := by
      simp [h1]
    _ = (x * z) * y - x * (z * y) := by
      simp [h2]

end PreLieConventions

/-!
### Hopf-style axioms on the stable UEA (linear form)

These axioms mirror Mathlib's Hopf algebra laws, but are formulated purely in
terms of linear maps so they remain meaningful before we have the full tensor
product algebra instances.
-/

section StableUEAHopfAxioms

variable [Semiring stableUEATensor]
variable [Algebra ℤ stableUEATensor]

variable (Δ : StableUEAComultiplication)

abbrev stableUEATensorToUEA :=
  stableUEATensor →ₗ[ℤ] preLieDifferenceStableQuotientUEA

abbrev stableUEAUnitLinear :=
  ℤ →ₗ[ℤ] preLieDifferenceStableQuotientUEA

abbrev stableUEAAntipode :=
  preLieDifferenceStableQuotientUEA →ₗ[ℤ] preLieDifferenceStableQuotientUEA

def StableUEAAntipodeAxioms
    (mulTensor : stableUEATensorToUEA)
    (unitLinear : stableUEAUnitLinear)
    (S : stableUEAAntipode) :
    Prop :=
  mulTensor ∘ₗ
      (LinearMap.rTensor preLieDifferenceStableQuotientUEA S) ∘ₗ Δ.comul =
    unitLinear ∘ₗ Δ.counit
  ∧
  mulTensor ∘ₗ
      (LinearMap.lTensor preLieDifferenceStableQuotientUEA S) ∘ₗ Δ.comul =
    unitLinear ∘ₗ Δ.counit

section StableUEAHopfAxiomsStd

-- The canonical choice `mulTensor = LinearMap.mul'` and
-- `unitLinear = Algebra.linearMap` requires extra scalar-tower instances,
-- so we postpone it to avoid instance-search failures.

end StableUEAHopfAxiomsStd

structure StableUEAHopfData where
  bialgebra : StableUEABialgebraData
  mulTensor : stableUEATensorToUEA
  unitLinear : stableUEAUnitLinear
  antipode : stableUEAAntipode
  antipode_on_generators : StableUEAAntipodeOnGenerators antipode
  antipode_axioms :
    StableUEAAntipodeAxioms bialgebra.coalgebra.Δ mulTensor unitLinear antipode

def StableUEAHopfData.comul (H : StableUEAHopfData) :=
  H.bialgebra.coalgebra.Δ.comul

def StableUEAHopfData.counit (H : StableUEAHopfData) :=
  H.bialgebra.coalgebra.Δ.counit

@[simp] theorem StableUEAHopfData.antipode_axioms_left
    (H : StableUEAHopfData) :
    H.mulTensor ∘ₗ
        (LinearMap.rTensor preLieDifferenceStableQuotientUEA H.antipode) ∘ₗ
        H.comul =
      H.unitLinear ∘ₗ H.counit :=
  H.antipode_axioms.1

@[simp] theorem StableUEAHopfData.antipode_axioms_right
    (H : StableUEAHopfData) :
    H.mulTensor ∘ₗ
        (LinearMap.lTensor preLieDifferenceStableQuotientUEA H.antipode) ∘ₗ
        H.comul =
      H.unitLinear ∘ₗ H.counit :=
  H.antipode_axioms.2

end StableUEAHopfAxioms

/-!
### Generator-level comultiplication data (stable UEA)

This is the concrete interface we can use now: a linear map determined on tree
generators, with the expected primitive-grouplike formula.
-/

section StableUEAGeneratorComul

structure StableUEAGeneratorComulData where
  comulGen : PTree → stableUEATensor
  counitGen : PTree → ℤ
  comulGen_eq :
    ∀ x : PTree,
      comulGen x =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)
  counitGen_eq : ∀ x : PTree, counitGen x = 0

def StableUEAGeneratorComulData.comul_on_treeGen
    (D : StableUEAGeneratorComulData) (x : PTree) :
    stableUEATensor := D.comulGen x

def StableUEAGeneratorComulData.counit_on_treeGen
    (D : StableUEAGeneratorComulData) (x : PTree) : ℤ := D.counitGen x

@[simp] theorem StableUEAGeneratorComulData.comul_on_treeGen_eq
    (D : StableUEAGeneratorComulData) (x : PTree) :
    D.comul_on_treeGen x =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  D.comulGen_eq x

@[simp] theorem StableUEAGeneratorComulData.counit_on_treeGen_eq
    (D : StableUEAGeneratorComulData) (x : PTree) :
    D.counit_on_treeGen x = 0 :=
  D.counitGen_eq x

end StableUEAGeneratorComul

/-!
### Linear extension of generator-level comultiplication

We can at least extend the generator data linearly to the free `ℤ`-module on
trees (the raw proof-tree carrier). This does not yet descend to the stable
quotient, but it enables concrete computations on sums of tree generators.
-/

section StableUEAGeneratorComulLinear

/-- Linear extension of a generator-level comultiplication to the free carrier. -/
noncomputable def stableUEA_comul_linear
    (D : StableUEAGeneratorComulData) :
    linearProofTreeCarrier →ₗ[ℤ] stableUEATensor :=
  Finsupp.lsum ℤ (fun x : PTree =>
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (D.comulGen x))

/-- Linear extension of the generator-level counit to the free carrier. -/
noncomputable def stableUEA_counit_linear
    (D : StableUEAGeneratorComulData) :
    linearProofTreeCarrier →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ (fun x : PTree =>
    (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (D.counitGen x))

@[simp] theorem stableUEA_comul_linear_treeGen
    (D : StableUEAGeneratorComulData) (x : PTree) :
    stableUEA_comul_linear D (treeGen x) = D.comulGen x := by
  classical
  simp [stableUEA_comul_linear, treeGen]

@[simp] theorem stableUEA_counit_linear_treeGen
    (D : StableUEAGeneratorComulData) (x : PTree) :
    stableUEA_counit_linear D (treeGen x) = D.counitGen x := by
  classical
  simp [stableUEA_counit_linear, treeGen]

theorem stableUEA_comul_linear_apply
    (D : StableUEAGeneratorComulData) (a : linearProofTreeCarrier) :
    stableUEA_comul_linear D a = a.sum (fun x c => c • D.comulGen x) := by
  classical
  simp [stableUEA_comul_linear, Finsupp.lsum_apply]

theorem stableUEA_counit_linear_apply
    (D : StableUEAGeneratorComulData) (a : linearProofTreeCarrier) :
    stableUEA_counit_linear D a = a.sum (fun x c => c • D.counitGen x) := by
  classical
  simp [stableUEA_counit_linear, Finsupp.lsum_apply]

@[simp] theorem stableUEA_comul_linear_add
    (D : StableUEAGeneratorComulData) (a b : linearProofTreeCarrier) :
    stableUEA_comul_linear D (a + b) =
      stableUEA_comul_linear D a + stableUEA_comul_linear D b := by
  simpa using (stableUEA_comul_linear D).map_add a b

@[simp] theorem stableUEA_counit_linear_add
    (D : StableUEAGeneratorComulData) (a b : linearProofTreeCarrier) :
    stableUEA_counit_linear D (a + b) =
      stableUEA_counit_linear D a + stableUEA_counit_linear D b := by
  simpa using (stableUEA_counit_linear D).map_add a b

@[simp] theorem stableUEA_comul_linear_smul
    (D : StableUEAGeneratorComulData) (z : ℤ) (a : linearProofTreeCarrier) :
    stableUEA_comul_linear D (z • a) = z • stableUEA_comul_linear D a := by
  simpa using (stableUEA_comul_linear D).map_smul z a

@[simp] theorem stableUEA_counit_linear_smul
    (D : StableUEAGeneratorComulData) (z : ℤ) (a : linearProofTreeCarrier) :
    stableUEA_counit_linear D (z • a) = z • stableUEA_counit_linear D a := by
  simpa using (stableUEA_counit_linear D).map_smul z a

end StableUEAGeneratorComulLinear

/-!
### Quotient-compatibility interface for generator comultiplication

This is the minimal condition we need to descend the linear extensions to the
stable quotient of proof trees.
-/

section StableUEAComulDescend

structure StableQuotientComultiplication where
  comul : PreLieDifferenceStableQuotient →ₗ[ℤ] stableUEATensor
  counit : PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ

def StableUEAGeneratorComulRespectsStableQuotient
    (D : StableUEAGeneratorComulData) : Prop :=
  ∀ a : linearProofTreeCarrier,
    a ∈ preLieDifferenceStableSubmodule →
      stableUEA_comul_linear D a = 0
    ∧ stableUEA_counit_linear D a = 0

noncomputable def stableUEA_comul_descend
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] stableUEATensor :=
  Submodule.liftQ
    preLieDifferenceStableSubmodule
    (stableUEA_comul_linear D)
    (by
      intro a ha
      exact (h a ha).1)

noncomputable def stableUEA_counit_descend
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  Submodule.liftQ
    preLieDifferenceStableSubmodule
    (stableUEA_counit_linear D)
    (by
      intro a ha
      exact (h a ha).2)

@[simp] theorem stableUEA_comul_descend_mk
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_comul_descend D h (mkPreLieDifferenceStableQuotient a) =
      stableUEA_comul_linear D a := by
  simpa [stableUEA_comul_descend, mkPreLieDifferenceStableQuotient]
    using (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := stableUEA_comul_linear D)
      (h := by
        intro a ha
        exact (h a ha).1)
      (x := a))

@[simp] theorem stableUEA_counit_descend_mk
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_counit_descend D h (mkPreLieDifferenceStableQuotient a) =
      stableUEA_counit_linear D a := by
  simpa [stableUEA_counit_descend, mkPreLieDifferenceStableQuotient]
    using (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := stableUEA_counit_linear D)
      (h := by
        intro a ha
        exact (h a ha).2)
      (x := a))

noncomputable def stableUEA_comultiplication_descend
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    StableQuotientComultiplication :=
  { comul := stableUEA_comul_descend D h
    counit := stableUEA_counit_descend D h }

theorem stableUEA_comultiplication_descend_comul_on_generators
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x : PTree) :
    (stableUEA_comultiplication_descend D h).comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      D.comulGen x := by
  simpa [stableUEA_comultiplication_descend]
    using (stableUEA_comul_descend_mk D h (treeGen x))

theorem stableUEA_comultiplication_descend_counit_on_generators
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x : PTree) :
    (stableUEA_comultiplication_descend D h).counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      D.counitGen x := by
  simpa [stableUEA_comultiplication_descend]
    using (stableUEA_counit_descend_mk D h (treeGen x))

@[simp] theorem stableUEA_comul_descend_treeGen_add
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      D.comulGen x + D.comulGen y := by
  simp [stableUEA_comul_descend_mk, stableUEA_comul_linear_add,
    stableUEA_comul_linear_treeGen]

@[simp] theorem stableUEA_counit_descend_treeGen_add
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      D.counitGen x + D.counitGen y := by
  simp [stableUEA_counit_descend_mk, stableUEA_counit_linear_add,
    stableUEA_counit_linear_treeGen]

@[simp] theorem stableUEA_comul_descend_treeGen_smul
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (z : ℤ) (x : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) =
      z • D.comulGen x := by
  simp [stableUEA_comul_descend_mk, stableUEA_comul_linear_smul,
    stableUEA_comul_linear_treeGen]

@[simp] theorem stableUEA_counit_descend_treeGen_smul
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (z : ℤ) (x : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) =
      z • D.counitGen x := by
  simp [stableUEA_counit_descend_mk, stableUEA_counit_linear_smul,
    stableUEA_counit_linear_treeGen]

theorem stableUEA_comul_descend_treeGen_sum_two
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) := by
  have hx : D.comulGen x =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := D.comulGen_eq x
  have hy : D.comulGen y =
      TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y) := D.comulGen_eq y
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      D.comulGen x + D.comulGen y := by
        simpa using (stableUEA_comul_descend_treeGen_add D h x y)
    _ =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) := by
        -- rewrite by the generator formulas, then reassociate
        calc
          D.comulGen x + D.comulGen y =
              (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
                TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) +
              (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
                TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) := by
            simpa [hx, hy]
          _ =
              TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
                TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) +
              (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
                TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) := by
            -- just reassociate once
            simp [add_assoc]

theorem stableUEA_counit_descend_treeGen_sum_two
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) = 0 := by
  simp [stableUEA_counit_descend_treeGen_add, D.counitGen_eq x, D.counitGen_eq y]

theorem stableUEA_comul_descend_apply
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_comul_descend D h (mkPreLieDifferenceStableQuotient a) =
      a.sum (fun x c => c • D.comulGen x) := by
  simpa [stableUEA_comul_descend_mk, stableUEA_comul_linear_apply]

theorem stableUEA_counit_descend_apply
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_counit_descend D h (mkPreLieDifferenceStableQuotient a) =
      a.sum (fun x c => c • D.counitGen x) := by
  simpa [stableUEA_counit_descend_mk, stableUEA_counit_linear_apply]

@[simp] theorem stableUEA_comul_descend_zero
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient 0) = 0 := by
  simpa using (stableUEA_comul_descend_mk D h 0)

@[simp] theorem stableUEA_counit_descend_zero
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient 0) = 0 := by
  simpa using (stableUEA_counit_descend_mk D h 0)

theorem stableUEA_comul_descend_treeGen_eq
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      D.comulGen x := by
        simpa using
          (stableUEA_comultiplication_descend_comul_on_generators D h x)
    _ =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := D.comulGen_eq x

theorem stableUEA_counit_descend_treeGen_eq
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  calc
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      D.counitGen x := by
        simpa using
          (stableUEA_comultiplication_descend_counit_on_generators D h x)
    _ = 0 := D.counitGen_eq x

theorem stableUEA_comul_descend_treeGen_smul_eq
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (z : ℤ) (x : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) =
      z • (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) =
      z • D.comulGen x := by
        simpa using (stableUEA_comul_descend_treeGen_smul D h z x)
    _ =
      z • (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) := by
        simp [D.comulGen_eq x]

theorem stableUEA_counit_descend_treeGen_smul_eq
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (z : ℤ) (x : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) = 0 := by
  calc
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (z • treeGen x)) =
      z • D.counitGen x := by
        simpa using (stableUEA_counit_descend_treeGen_smul D h z x)
    _ = 0 := by
        simp [D.counitGen_eq x]

structure StableQuotientComultiplicationData where
  Δ : StableQuotientComultiplication
  comul_on_generators :
    ∀ x : PTree,
      Δ.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)
  counit_on_generators :
    ∀ x : PTree,
      Δ.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0

def StableQuotientComultiplicationData.comul (D : StableQuotientComultiplicationData) :=
  D.Δ.comul

def StableQuotientComultiplicationData.counit (D : StableQuotientComultiplicationData) :=
  D.Δ.counit

@[simp] theorem StableQuotientComultiplicationData.comul_on_treeGen
    (D : StableQuotientComultiplicationData) (x : PTree) :
    D.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  D.comul_on_generators x

@[simp] theorem StableQuotientComultiplicationData.counit_on_treeGen
    (D : StableQuotientComultiplicationData) (x : PTree) :
    D.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 :=
  D.counit_on_generators x

noncomputable def stableUEA_comultiplication_descend_data
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    StableQuotientComultiplicationData :=
  { Δ := stableUEA_comultiplication_descend D h
    comul_on_generators := by
      intro x
      have hgen :=
        stableUEA_comultiplication_descend_comul_on_generators D h x
      calc
        (stableUEA_comultiplication_descend D h).comul
            (mkPreLieDifferenceStableQuotient (treeGen x)) =
          D.comulGen x := hgen
        _ =
          TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
            TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
          D.comulGen_eq x
    counit_on_generators := by
      intro x
      have hgen :=
        stableUEA_comultiplication_descend_counit_on_generators D h x
      calc
        (stableUEA_comultiplication_descend D h).counit
            (mkPreLieDifferenceStableQuotient (treeGen x)) =
          D.counitGen x := hgen
        _ = 0 := D.counitGen_eq x }

end StableUEAComulDescend

/-!
### Lifting quotient comultiplication into the stable UEA

This is a lightweight interface: once a linear lift from the stable quotient
into the UEA is chosen, we can transport quotient-level comultiplication data
to the UEA. This keeps the dependency explicit and avoids committing to a
specific universal-property proof in this file.
-/

section StableUEALiftInterface

structure StableUEALiftData where
  lift : PreLieDifferenceStableQuotient → preLieDifferenceStableQuotientUEA
  lift_treeGen :
    ∀ x : PTree,
      lift (mkPreLieDifferenceStableQuotient (treeGen x)) = stableUEA_treeGen x

@[simp] theorem StableUEALiftData.lift_treeGen_eq
    (L : StableUEALiftData) (x : PTree) :
    L.lift (mkPreLieDifferenceStableQuotient (treeGen x)) = stableUEA_treeGen x :=
  L.lift_treeGen x

noncomputable def stableUEA_canonicalLiftData : StableUEALiftData := by
  classical
  letI : LieRing PreLieDifferenceStableQuotient :=
    preLieDifferenceStableQuotientLieRing
  refine
    { lift := fun q => preLieDifferenceStableQuotientUEA_ι q
      lift_treeGen := ?_ }
  intro x
  simpa [stableUEA_treeGen_eq_ι]

@[simp] theorem stableUEA_canonicalLiftData_treeGen
    (x : PTree) :
    stableUEA_canonicalLiftData.lift
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      stableUEA_treeGen x := by
  simpa using (stableUEA_canonicalLiftData.lift_treeGen x)

-- Note: a linear-lift structure can be added later once the module structures
-- on the stable quotient and the UEA are definitionally aligned. For now we
-- keep only the function-level lift to avoid instance mismatch noise.

theorem StableQuotientComultiplicationData.comul_on_treeGen_via
    (D : StableQuotientComultiplicationData) (L : StableUEALiftData) (x : PTree) :
    D.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (L.lift (mkPreLieDifferenceStableQuotient (treeGen x))) 1 +
        TensorProduct.tmul ℤ 1 (L.lift (mkPreLieDifferenceStableQuotient (treeGen x))) := by
  simpa [L.lift_treeGen_eq] using D.comul_on_treeGen x

theorem StableQuotientComultiplicationData.counit_on_treeGen_via
    (D : StableQuotientComultiplicationData) (L : StableUEALiftData) (x : PTree) :
    D.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simpa using D.counit_on_treeGen x

-- Note: Once a concrete lift `ι` is fixed, we will compose it with the
-- quotient comultiplication data to obtain an OG-style comultiplication
-- on the UEA. This section only records the intended interface.

end StableUEALiftInterface

/-!
### Quotient-level computation helpers

These are small corollaries that let us compute quotient comultiplication data
on concrete finite sums without unfolding the entire construction.
-/

section StableQuotientComulHelpers

theorem finsupp_sum_eq_sum_support
    {α M N : Type*} [Zero M] [AddCommMonoid N]
    (a : α →₀ M) (f : α → M → N) :
    a.sum f = (a.support).sum (fun x => f x (a x)) := rfl

theorem stableUEA_comul_descend_treeGen_sum_three
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y z : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (D.comulGen x + D.comulGen y) + D.comulGen z := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient ((treeGen x + treeGen y) + treeGen z)) := by
        simp [add_assoc]
    _ =
      D.comulGen x + D.comulGen y + D.comulGen z := by
        simp [stableUEA_comul_descend_treeGen_add, add_assoc]

theorem stableUEA_counit_descend_treeGen_sum_three
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y z : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) = 0 := by
  calc
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient ((treeGen x + treeGen y) + treeGen z)) := by
        simp [add_assoc]
    _ =
      D.counitGen x + D.counitGen y + D.counitGen z := by
        simp [stableUEA_counit_descend_treeGen_add, add_assoc]
    _ = 0 := by
        simp [D.counitGen_eq x, D.counitGen_eq y, D.counitGen_eq z]

theorem stableUEA_comul_descend_treeGen_sum_three_expanded
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (x y z : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen z) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen z)) := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      D.comulGen x + D.comulGen y + D.comulGen z := by
        simpa using (stableUEA_comul_descend_treeGen_sum_three D h x y z)
    _ =
      (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen z) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen z)) := by
        -- expand each generator formula in order
        simp [D.comulGen_eq x, D.comulGen_eq y, D.comulGen_eq z, add_assoc]

theorem stableUEA_comul_descend_treeGen_sum_four
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (w x y z : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (D.comulGen w + D.comulGen x) + (D.comulGen y + D.comulGen z) := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient ((treeGen w + treeGen x) +
          (treeGen y + treeGen z))) := by
        simp [add_assoc]
    _ =
      (D.comulGen w + D.comulGen x) + (D.comulGen y + D.comulGen z) := by
        simp [stableUEA_comul_descend_treeGen_add, add_assoc]

theorem stableUEA_counit_descend_treeGen_sum_four
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (w x y z : PTree) :
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  calc
    stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      stableUEA_counit_descend D h
        (mkPreLieDifferenceStableQuotient ((treeGen w + treeGen x) +
          (treeGen y + treeGen z))) := by
        simp [add_assoc]
    _ =
      (D.counitGen w + D.counitGen x) + (D.counitGen y + D.counitGen z) := by
        simp [stableUEA_counit_descend_treeGen_add, add_assoc]
    _ = 0 := by
        simp [D.counitGen_eq w, D.counitGen_eq x, D.counitGen_eq y, D.counitGen_eq z]

theorem stableUEA_comul_descend_treeGen_sum_four_expanded
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (w x y z : PTree) :
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul ℤ (stableUEA_treeGen w) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen z) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen z)) := by
  calc
    stableUEA_comul_descend D h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (D.comulGen w + D.comulGen x) + (D.comulGen y + D.comulGen z) := by
        simpa using (stableUEA_comul_descend_treeGen_sum_four D h w x y z)
    _ =
      (TensorProduct.tmul ℤ (stableUEA_treeGen w) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen y) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul ℤ (stableUEA_treeGen z) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen z)) := by
        simp [D.comulGen_eq w, D.comulGen_eq x, D.comulGen_eq y, D.comulGen_eq z, add_assoc]

theorem stableUEA_comul_descend_sum_support
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_comul_descend D h (mkPreLieDifferenceStableQuotient a) =
      (a.support).sum (fun x => a x • D.comulGen x) := by
  classical
  have hsum :=
    stableUEA_comul_descend_apply (D := D) (h := h) (a := a)
  simpa [finsupp_sum_eq_sum_support] using hsum

theorem stableUEA_counit_descend_sum_support
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D)
    (a : linearProofTreeCarrier) :
    stableUEA_counit_descend D h (mkPreLieDifferenceStableQuotient a) =
      (a.support).sum (fun x => a x • D.counitGen x) := by
  classical
  have hsum :=
    stableUEA_counit_descend_apply (D := D) (h := h) (a := a)
  simpa [finsupp_sum_eq_sum_support] using hsum

structure StableQuotientComultiplicationAxioms
    (Δ : StableQuotientComultiplication) : Prop where
  comul_on_generators :
    ∀ x : PTree,
      Δ.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)
  counit_on_generators :
    ∀ x : PTree,
      Δ.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0

structure StableQuotientComultiplicationPack where
  Δ : StableQuotientComultiplication
  axioms : StableQuotientComultiplicationAxioms Δ

def StableQuotientComultiplicationPack.comul (D : StableQuotientComultiplicationPack) :=
  D.Δ.comul

def StableQuotientComultiplicationPack.counit (D : StableQuotientComultiplicationPack) :=
  D.Δ.counit

@[simp] theorem StableQuotientComultiplicationPack.comul_on_treeGen
    (D : StableQuotientComultiplicationPack) (x : PTree) :
    D.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  D.axioms.comul_on_generators x

@[simp] theorem StableQuotientComultiplicationPack.counit_on_treeGen
    (D : StableQuotientComultiplicationPack) (x : PTree) :
    D.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 :=
  D.axioms.counit_on_generators x

theorem StableQuotientComultiplicationPack_comul_on_treeGen_via
    (D : StableQuotientComultiplicationPack) (L : StableUEALiftData) (x : PTree) :
    D.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (L.lift (mkPreLieDifferenceStableQuotient (treeGen x))) 1 +
        TensorProduct.tmul ℤ 1 (L.lift (mkPreLieDifferenceStableQuotient (treeGen x))) := by
  simpa [L.lift_treeGen_eq] using (D.axioms.comul_on_generators x)

theorem StableQuotientComultiplicationPack_counit_on_treeGen_via
    (D : StableQuotientComultiplicationPack) (L : StableUEALiftData) (x : PTree) :
    D.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simpa using (D.axioms.counit_on_generators x)

noncomputable def stableUEA_comultiplication_descend_pack
    (D : StableUEAGeneratorComulData)
    (h : StableUEAGeneratorComulRespectsStableQuotient D) :
    StableQuotientComultiplicationPack :=
  { Δ := stableUEA_comultiplication_descend D h
    axioms :=
      { comul_on_generators := by
          intro x
          have hgen :=
            stableUEA_comultiplication_descend_comul_on_generators D h x
          calc
            (stableUEA_comultiplication_descend D h).comul
                (mkPreLieDifferenceStableQuotient (treeGen x)) =
              D.comulGen x := hgen
            _ =
              TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
                TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := D.comulGen_eq x
        counit_on_generators := by
          intro x
          have hgen :=
            stableUEA_comultiplication_descend_counit_on_generators D h x
          calc
            (stableUEA_comultiplication_descend D h).counit
                (mkPreLieDifferenceStableQuotient (treeGen x)) =
              D.counitGen x := hgen
            _ = 0 := D.counitGen_eq x } }

end StableQuotientComulHelpers

/-!
### Cut-based coproduct support (raw trees)

We keep the coproduct data computed on `PTree` as a finitary support set of
forest–tree pairs. This stays close to the concrete combinatorics while we
decide how much of the Hopf structure to descend to quotients.
-/

section CoproductSupport

/-- Total graft weight of a forest. -/
def forestWeight : Forest → Nat
  | [] => 0
  | t :: ts => PTree.graftWeight t + forestWeight ts

@[simp] theorem forestWeight_nil : forestWeight ([] : Forest) = 0 := rfl

@[simp] theorem forestWeight_cons (t : PTree) (ts : Forest) :
    forestWeight (t :: ts) = PTree.graftWeight t + forestWeight ts := rfl

@[simp] theorem forestWeight_singleton (t : PTree) :
    forestWeight [t] = PTree.graftWeight t := by
  simp [forestWeight]

theorem forestWeight_append (f g : Forest) :
    forestWeight (f ++ g) = forestWeight f + forestWeight g := by
  induction f with
  | nil =>
      simp [forestWeight]
  | cons t ts ih =>
      simp [forestWeight, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem forestWeight_eq_sum_map (f : Forest) :
    forestWeight f = (f.map PTree.graftWeight).sum := by
  induction f with
  | nil =>
      simp [forestWeight]
  | cons t ts ih =>
      simp [forestWeight, ih]

/-- The raw coproduct support set of forest–tree pairs. -/
def coproductSupport (t : PTree) : Set (Forest × PTree) :=
  { p | p ∈ PTree.coproductData t }

@[simp] theorem mem_coproductSupport (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupport t ↔ p ∈ PTree.coproductData t := by
  rfl

theorem coproductSupport_finite (t : PTree) :
    Set.Finite (coproductSupport t) := by
  classical
  refine (List.toFinset (PTree.coproductData t)).finite_toSet.subset ?_
  intro p hp
  exact List.mem_toFinset.mpr hp

theorem coproductSupport_contains_trivial (t : PTree) :
    ([], t) ∈ coproductSupport t := by
  classical
  unfold coproductSupport PTree.coproductData
  refine List.mem_map.2 ?_
  refine ⟨[], PTree.empty_cut_mem_allAdmissibleCuts t, ?_⟩
  simpa [PTree.coproductTerm_nil]

def coproductForestsList (t : PTree) : List Forest :=
  (PTree.coproductData t).map Prod.fst

def coproductRemaindersList (t : PTree) : List PTree :=
  (PTree.coproductData t).map Prod.snd

theorem mem_coproductForestsList_iff (t : PTree) (f : Forest) :
    f ∈ coproductForestsList t ↔ ∃ r : PTree, (f, r) ∈ PTree.coproductData t := by
  constructor
  · intro hf
    rcases List.mem_map.1 hf with ⟨p, hp, hpf⟩
    cases p with
    | mk f' r =>
        cases hpf
        exact ⟨r, hp⟩
  · rintro ⟨r, hr⟩
    exact List.mem_map.2 ⟨(f, r), hr, rfl⟩

theorem mem_coproductRemaindersList_iff (t : PTree) (r : PTree) :
    r ∈ coproductRemaindersList t ↔ ∃ f : Forest, (f, r) ∈ PTree.coproductData t := by
  constructor
  · intro hr
    rcases List.mem_map.1 hr with ⟨p, hp, hpr⟩
    cases p with
    | mk f r' =>
        cases hpr
        exact ⟨f, hp⟩
  · rintro ⟨f, hf⟩
    exact List.mem_map.2 ⟨(f, r), hf, rfl⟩

theorem coproductForestsList_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ PTree.coproductData t) :
    f ∈ coproductForestsList t := by
  exact (mem_coproductForestsList_iff t f).2 ⟨r, h⟩

theorem coproductRemaindersList_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ PTree.coproductData t) :
    r ∈ coproductRemaindersList t := by
  exact (mem_coproductRemaindersList_iff t r).2 ⟨f, h⟩

@[simp] theorem coproductForestsList_contains_nil (t : PTree) :
    [] ∈ coproductForestsList t := by
  have h : ([], t) ∈ PTree.coproductData t := by
    simpa [coproductSupport] using coproductSupport_contains_trivial t
  exact (mem_coproductForestsList_iff t []).2 ⟨t, h⟩

@[simp] theorem coproductRemaindersList_contains_root (t : PTree) :
    t ∈ coproductRemaindersList t := by
  have h : ([], t) ∈ PTree.coproductData t := by
    simpa [coproductSupport] using coproductSupport_contains_trivial t
  exact (mem_coproductRemaindersList_iff t t).2 ⟨[], h⟩

theorem coproductForestsList_nonempty (t : PTree) :
    (coproductForestsList t).length > 0 := by
  cases h : coproductForestsList t with
  | nil =>
      have hmem : ([] : Forest) ∈ ([] : List Forest) := by
        simpa [h] using coproductForestsList_contains_nil t
      cases hmem
  | cons a l =>
      simp [h]

theorem coproductRemaindersList_nonempty (t : PTree) :
    (coproductRemaindersList t).length > 0 := by
  cases h : coproductRemaindersList t with
  | nil =>
      have hmem : t ∈ ([] : List PTree) := by
        simpa [h] using coproductRemaindersList_contains_root t
      cases hmem
  | cons a l =>
      simp [h]

theorem coproductForestsList_length_pos (t : PTree) :
    0 < (coproductForestsList t).length := by
  exact coproductForestsList_nonempty t

theorem coproductRemaindersList_length_pos (t : PTree) :
    0 < (coproductRemaindersList t).length := by
  exact coproductRemaindersList_nonempty t

theorem coproductForestsList_map_length (t : PTree) :
    (coproductForestsList t).map List.length =
      (PTree.coproductData t).map (fun p => (p.1).length) := by
  simp [coproductForestsList, List.map_map]

theorem coproductRemaindersList_map_id (t : PTree) :
    (coproductRemaindersList t).map (fun r => r) =
      (PTree.coproductData t).map (fun p => p.2) := by
  simp [coproductRemaindersList]

theorem coproductForestsList_mem_map_fst
    (t : PTree) (f : Forest) :
    f ∈ (PTree.coproductData t).map Prod.fst ↔
      f ∈ coproductForestsList t := by
  rfl

theorem coproductRemaindersList_mem_map_snd
    (t : PTree) (r : PTree) :
    r ∈ (PTree.coproductData t).map Prod.snd ↔
      r ∈ coproductRemaindersList t := by
  rfl

def coproductForests (t : PTree) : Set Forest :=
  { f | ∃ r : PTree, (f, r) ∈ coproductSupport t }

def coproductRemainders (t : PTree) : Set PTree :=
  { r | ∃ f : Forest, (f, r) ∈ coproductSupport t }

def coproductForestsListSet (t : PTree) : Set Forest :=
  { f | f ∈ coproductForestsList t }

def coproductRemaindersListSet (t : PTree) : Set PTree :=
  { r | r ∈ coproductRemaindersList t }

@[simp] theorem mem_coproductForestsListSet_iff
    (t : PTree) (f : Forest) :
    f ∈ coproductForestsListSet t ↔ f ∈ coproductForestsList t := by
  rfl

@[simp] theorem mem_coproductRemaindersListSet_iff
    (t : PTree) (r : PTree) :
    r ∈ coproductRemaindersListSet t ↔ r ∈ coproductRemaindersList t := by
  rfl


theorem mem_coproductForestsList_iff_mem_coproductForests
    (t : PTree) (f : Forest) :
    f ∈ coproductForestsList t ↔ f ∈ coproductForests t := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro hf
    have hf' := (mem_coproductForestsList_iff t f).1 hf
    cases hf' with
    | intro r hr =>
        exact Exists.intro r hr
  case mpr =>
    intro hf
    cases hf with
    | intro r hr =>
        exact (mem_coproductForestsList_iff t f).2 (Exists.intro r hr)

theorem mem_coproductRemaindersList_iff_mem_coproductRemainders
    (t : PTree) (r : PTree) :
    r ∈ coproductRemaindersList t ↔ r ∈ coproductRemainders t := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro hr
    have hr' := (mem_coproductRemaindersList_iff t r).1 hr
    cases hr' with
    | intro f hf =>
        exact Exists.intro f hf
  case mpr =>
    intro hr
    cases hr with
    | intro f hf =>
        exact (mem_coproductRemaindersList_iff t r).2 (Exists.intro f hf)

theorem coproductForestsListSet_eq (t : PTree) :
    coproductForestsListSet t = coproductForests t := by
  ext f
  exact mem_coproductForestsList_iff_mem_coproductForests t f

theorem coproductRemaindersListSet_eq (t : PTree) :
    coproductRemaindersListSet t = coproductRemainders t := by
  ext r
  exact mem_coproductRemaindersList_iff_mem_coproductRemainders t r


theorem mem_coproductForests_iff (t : PTree) (f : Forest) :
    f ∈ coproductForests t ↔ ∃ r : PTree, (f, r) ∈ coproductSupport t := by
  rfl

theorem mem_coproductRemainders_iff (t : PTree) (r : PTree) :
    r ∈ coproductRemainders t ↔ ∃ f : Forest, (f, r) ∈ coproductSupport t := by
  rfl

noncomputable def coproductSupportFinset (t : PTree) : Finset (Forest × PTree) :=
  (PTree.coproductData t).toFinset

@[simp] theorem mem_coproductSupportFinset (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportFinset t ↔ p ∈ t.coproductData := by
  classical
  simpa [coproductSupportFinset] using
    (List.mem_toFinset : p ∈ (PTree.coproductData t).toFinset ↔ p ∈ PTree.coproductData t)

theorem coproductSupportFinset_coe (t : PTree) :
    (coproductSupportFinset t : Set (Forest × PTree)) = coproductSupport t := by
  classical
  ext p
  constructor
  · intro hp
    have hp' : p ∈ coproductSupportFinset t := by
      exact hp
    have hp'' : p ∈ PTree.coproductData t :=
      (mem_coproductSupportFinset t p).1 hp'
    exact (mem_coproductSupport t p).2 hp''
  · intro hp
    have hp' : p ∈ PTree.coproductData t := by
      simpa [coproductSupport] using hp
    have hp'' : p ∈ coproductSupportFinset t :=
      (mem_coproductSupportFinset t p).2 hp'
    exact (show p ∈ (coproductSupportFinset t : Set (Forest × PTree)) from hp'')

noncomputable def coproductForestsFinset (t : PTree) : Finset Forest :=
  (coproductSupportFinset t).image Prod.fst

noncomputable def coproductRemaindersFinset (t : PTree) : Finset PTree :=
  (coproductSupportFinset t).image Prod.snd

theorem mem_coproductForestsFinset (t : PTree) (f : Forest) :
    f ∈ coproductForestsFinset t ↔ ∃ r : PTree, (f, r) ∈ coproductSupportFinset t := by
  classical
  constructor
  · intro hf
    rcases Finset.mem_image.1 hf with ⟨p, hp, hpf⟩
    cases p with
    | mk f' r =>
        cases hpf
        exact ⟨r, hp⟩
  · rintro ⟨r, hr⟩
    exact Finset.mem_image.2 ⟨(f, r), hr, rfl⟩

theorem mem_coproductRemaindersFinset (t : PTree) (r : PTree) :
    r ∈ coproductRemaindersFinset t ↔ ∃ f : Forest, (f, r) ∈ coproductSupportFinset t := by
  classical
  constructor
  · intro hr
    rcases Finset.mem_image.1 hr with ⟨p, hp, hpr⟩
    cases p with
    | mk f r' =>
        cases hpr
        exact ⟨f, hp⟩
  · rintro ⟨f, hf⟩
    exact Finset.mem_image.2 ⟨(f, r), hf, rfl⟩

theorem coproductSupportFinset_card_le_length (t : PTree) :
    (coproductSupportFinset t).card ≤ (PTree.coproductData t).length := by
  simpa [coproductSupportFinset] using
    (List.toFinset_card_le (PTree.coproductData t))

theorem coproductForestsFinset_card_le_support (t : PTree) :
    (coproductForestsFinset t).card ≤ (coproductSupportFinset t).card := by
  classical
  simpa [coproductForestsFinset] using
    (Finset.card_image_le (s := coproductSupportFinset t) (f := Prod.fst))

theorem coproductRemaindersFinset_card_le_support (t : PTree) :
    (coproductRemaindersFinset t).card ≤ (coproductSupportFinset t).card := by
  classical
  simpa [coproductRemaindersFinset] using
    (Finset.card_image_le (s := coproductSupportFinset t) (f := Prod.snd))

theorem coproductForestsFinset_card_le_length (t : PTree) :
    (coproductForestsFinset t).card ≤ (PTree.coproductData t).length := by
  exact le_trans (coproductForestsFinset_card_le_support t)
    (coproductSupportFinset_card_le_length t)

theorem coproductRemaindersFinset_card_le_length (t : PTree) :
    (coproductRemaindersFinset t).card ≤ (PTree.coproductData t).length := by
  exact le_trans (coproductRemaindersFinset_card_le_support t)
    (coproductSupportFinset_card_le_length t)

@[simp] theorem coproductSupportFinset_contains_trivial (t : PTree) :
    ([], t) ∈ coproductSupportFinset t := by
  have hlist : ([], t) ∈ PTree.coproductData t := by
    simpa [coproductSupport] using coproductSupport_contains_trivial t
  exact (mem_coproductSupportFinset t ([], t)).2 hlist

@[simp] theorem coproductForestsFinset_contains_nil (t : PTree) :
    [] ∈ coproductForestsFinset t := by
  exact (mem_coproductForestsFinset t []).2 ⟨t, coproductSupportFinset_contains_trivial t⟩

@[simp] theorem coproductRemaindersFinset_contains_root (t : PTree) :
    t ∈ coproductRemaindersFinset t := by
  exact (mem_coproductRemaindersFinset t t).2 ⟨[], coproductSupportFinset_contains_trivial t⟩

theorem coproductSupportFinset_card_pos (t : PTree) :
    0 < (coproductSupportFinset t).card := by
  classical
  exact Finset.card_pos.mpr ⟨([], t), coproductSupportFinset_contains_trivial t⟩

theorem coproductForestsFinset_card_pos (t : PTree) :
    0 < (coproductForestsFinset t).card := by
  classical
  exact Finset.card_pos.mpr ⟨[], coproductForestsFinset_contains_nil t⟩

theorem coproductRemaindersFinset_card_pos (t : PTree) :
    0 < (coproductRemaindersFinset t).card := by
  classical
  exact Finset.card_pos.mpr ⟨t, coproductRemaindersFinset_contains_root t⟩

theorem coproductForestsFinset_coe (t : PTree) :
    (coproductForestsFinset t : Set Forest) = coproductForests t := by
  classical
  ext f
  constructor
  · intro hf
    have hf' := (mem_coproductForestsFinset t f).1 hf
    rcases hf' with ⟨r, hr⟩
    have hr' : (f, r) ∈ coproductSupport t := by
      simpa [mem_coproductSupportFinset] using hr
    exact ⟨r, hr'⟩
  · intro hf
    rcases hf with ⟨r, hr⟩
    have hr' : (f, r) ∈ coproductSupportFinset t := by
      simpa [mem_coproductSupportFinset] using hr
    exact (mem_coproductForestsFinset t f).2 ⟨r, hr'⟩

theorem coproductRemaindersFinset_coe (t : PTree) :
    (coproductRemaindersFinset t : Set PTree) = coproductRemainders t := by
  classical
  ext r
  constructor
  · intro hr
    have hr' := (mem_coproductRemaindersFinset t r).1 hr
    rcases hr' with ⟨f, hf⟩
    have hf' : (f, r) ∈ coproductSupport t := by
      simpa [mem_coproductSupportFinset] using hf
    exact ⟨f, hf'⟩
  · intro hr
    rcases hr with ⟨f, hf⟩
    have hf' : (f, r) ∈ coproductSupportFinset t := by
      simpa [mem_coproductSupportFinset] using hf
    exact (mem_coproductRemaindersFinset t r).2 ⟨f, hf'⟩

theorem coproductForestsListSet_eq_finset (t : PTree) :
    coproductForestsListSet t = (coproductForestsFinset t : Set Forest) := by
  classical
  ext f
  constructor
  · intro hf
    have hf' : f ∈ coproductForestsList t := hf
    rcases (mem_coproductForestsList_iff t f).1 hf' with ⟨r, hr⟩
    have hr' : (f, r) ∈ coproductSupportFinset t :=
      (mem_coproductSupportFinset t (f, r)).2 hr
    have hf'' : f ∈ coproductForestsFinset t :=
      (mem_coproductForestsFinset t f).2 ⟨r, hr'⟩
    simpa using hf''
  · intro hf
    have hf' : f ∈ coproductForestsFinset t := by
      simpa using hf
    rcases (mem_coproductForestsFinset t f).1 hf' with ⟨r, hr⟩
    have hr' : (f, r) ∈ PTree.coproductData t :=
      (mem_coproductSupportFinset t (f, r)).1 hr
    exact (mem_coproductForestsList_iff t f).2 ⟨r, hr'⟩

theorem coproductRemaindersListSet_eq_finset (t : PTree) :
    coproductRemaindersListSet t = (coproductRemaindersFinset t : Set PTree) := by
  classical
  ext r
  constructor
  · intro hr
    have hr' : r ∈ coproductRemaindersList t := hr
    rcases (mem_coproductRemaindersList_iff t r).1 hr' with ⟨f, hf⟩
    have hf' : (f, r) ∈ coproductSupportFinset t :=
      (mem_coproductSupportFinset t (f, r)).2 hf
    have hr'' : r ∈ coproductRemaindersFinset t :=
      (mem_coproductRemaindersFinset t r).2 ⟨f, hf'⟩
    simpa using hr''
  · intro hr
    have hr' : r ∈ coproductRemaindersFinset t := by
      simpa using hr
    rcases (mem_coproductRemaindersFinset t r).1 hr' with ⟨f, hf⟩
    have hf' : (f, r) ∈ PTree.coproductData t :=
      (mem_coproductSupportFinset t (f, r)).1 hf
    exact (mem_coproductRemaindersList_iff t r).2 ⟨f, hf'⟩

@[simp] theorem coproductForests_contains_nil (t : PTree) :
    [] ∈ coproductForests t := by
  refine ⟨t, ?_⟩
  simpa using coproductSupport_contains_trivial t

@[simp] theorem coproductRemainders_contains_root (t : PTree) :
    t ∈ coproductRemainders t := by
  refine ⟨[], ?_⟩
  simpa using coproductSupport_contains_trivial t

theorem coproductSupport_nonempty (t : PTree) :
    (coproductSupport t).Nonempty := by
  refine ⟨([], t), coproductSupport_contains_trivial t⟩

theorem coproductForests_eq_image_fst (t : PTree) :
    coproductForests t = Prod.fst '' coproductSupport t := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨r, hr⟩
    exact ⟨(f, r), hr, rfl⟩
  · intro hf
    rcases hf with ⟨p, hp, hpf⟩
    cases p with
    | mk f' r =>
        cases hpf
        exact ⟨r, hp⟩

theorem coproductRemainders_eq_image_snd (t : PTree) :
    coproductRemainders t = Prod.snd '' coproductSupport t := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨f, hf⟩
    exact ⟨(f, r), hf, rfl⟩
  · intro hr
    rcases hr with ⟨p, hp, hps⟩
    cases p with
    | mk f r' =>
        cases hps
        exact ⟨f, hp⟩

theorem coproductForests_finite (t : PTree) :
    Set.Finite (coproductForests t) := by
  classical
  simpa [coproductForests_eq_image_fst] using
    (coproductSupport_finite t).image Prod.fst

theorem coproductRemainders_finite (t : PTree) :
    Set.Finite (coproductRemainders t) := by
  classical
  simpa [coproductRemainders_eq_image_snd] using
    (coproductSupport_finite t).image Prod.snd

theorem coproductForests_nonempty (t : PTree) :
    (coproductForests t).Nonempty := by
  rcases coproductSupport_nonempty t with ⟨p, hp⟩
  exact ⟨p.1, ⟨p.2, hp⟩⟩

theorem coproductRemainders_nonempty (t : PTree) :
    (coproductRemainders t).Nonempty := by
  rcases coproductSupport_nonempty t with ⟨p, hp⟩
  exact ⟨p.2, ⟨p.1, hp⟩⟩

theorem coproductForests_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ coproductSupport t) :
    f ∈ coproductForests t := by
  exact ⟨r, h⟩

theorem coproductRemainders_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ coproductSupport t) :
    r ∈ coproductRemainders t := by
  exact ⟨f, h⟩

theorem coproductForests_mem_iff_support
    (t : PTree) (f : Forest) :
    f ∈ coproductForests t ↔ ∃ r : PTree, (f, r) ∈ coproductSupport t := by
  rfl

theorem coproductRemainders_mem_iff_support
    (t : PTree) (r : PTree) :
    r ∈ coproductRemainders t ↔ ∃ f : Forest, (f, r) ∈ coproductSupport t := by
  rfl

theorem coproductSupport_mem_iff
    (t : PTree) (f : Forest) (r : PTree) :
    (f, r) ∈ coproductSupport t ↔ (f, r) ∈ PTree.coproductData t := by
  rfl

theorem coproductSupport_subset_product
    (t : PTree) :
    coproductSupport t ⊆
      (coproductForests t ×ˢ coproductRemainders t) := by
  intro p hp
  rcases p with ⟨f, r⟩
  exact ⟨coproductForests_mem_of_support (t := t) hp,
    coproductRemainders_mem_of_support (t := t) hp⟩

theorem coproductSupportFinset_subset_product
    (t : PTree) :
    (coproductSupportFinset t : Set (Forest × PTree)) ⊆
      (coproductForests t ×ˢ coproductRemainders t) := by
  intro p hp
  have hp' : p ∈ coproductSupport t := by
    have hp' : p ∈ (coproductSupportFinset t : Set (Forest × PTree)) := hp
    simpa [coproductSupportFinset_coe] using hp'
  exact coproductSupport_subset_product t hp'

theorem coproductSupportFinset_nonempty (t : PTree) :
    (coproductSupportFinset t : Set (Forest × PTree)).Nonempty := by
  have h : (coproductSupport t).Nonempty := coproductSupport_nonempty t
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  simpa [coproductSupportFinset_coe] using hp

theorem coproductForestsFinset_nonempty (t : PTree) :
    (coproductForestsFinset t : Set Forest).Nonempty := by
  rcases coproductSupportFinset_nonempty t with ⟨p, hp⟩
  refine ⟨p.1, ?_⟩
  have hp' : p.1 ∈ coproductForests t := by
    have hp'' : p ∈ coproductSupport t := by
      simpa [coproductSupportFinset_coe] using hp
    exact coproductForests_mem_of_support (t := t) hp''
  simpa [coproductForestsFinset_coe] using hp'

theorem coproductRemaindersFinset_nonempty (t : PTree) :
    (coproductRemaindersFinset t : Set PTree).Nonempty := by
  rcases coproductSupportFinset_nonempty t with ⟨p, hp⟩
  refine ⟨p.2, ?_⟩
  have hp' : p.2 ∈ coproductRemainders t := by
    have hp'' : p ∈ coproductSupport t := by
      simpa [coproductSupportFinset_coe] using hp
    exact coproductRemainders_mem_of_support (t := t) hp''
  simpa [coproductRemaindersFinset_coe] using hp'

theorem coproductForestsFinset_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ coproductSupportFinset t) :
    f ∈ coproductForestsFinset t := by
  exact (mem_coproductForestsFinset t f).2 ⟨r, h⟩

theorem coproductRemaindersFinset_mem_of_support
    {t : PTree} {f : Forest} {r : PTree}
    (h : (f, r) ∈ coproductSupportFinset t) :
    r ∈ coproductRemaindersFinset t := by
  exact (mem_coproductRemaindersFinset t r).2 ⟨f, h⟩

theorem coproductSupportFinset_image_fst_subset
    (t : PTree) :
    (coproductSupportFinset t).image Prod.fst ⊆
      coproductForestsFinset t := by
  intro f hf
  exact hf

theorem coproductSupportFinset_image_snd_subset
    (t : PTree) :
    (coproductSupportFinset t).image Prod.snd ⊆
      coproductRemaindersFinset t := by
  intro r hr
  exact hr

theorem coproductForestsFinset_eq_image_fst
    (t : PTree) :
    coproductForestsFinset t = (coproductSupportFinset t).image Prod.fst := by
  rfl

theorem coproductRemaindersFinset_eq_image_snd
    (t : PTree) :
    coproductRemaindersFinset t = (coproductSupportFinset t).image Prod.snd := by
  rfl

theorem coproductSupportFinset_sum_pair
    {α : Type*} [AddCommMonoid α]
    (t : PTree) (g : Forest × PTree → α) :
    (coproductSupportFinset t).sum g =
      (coproductSupportFinset t).sum (fun p => g (p.1, p.2)) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro p hp
  rfl

theorem coproductSupportFinset_sum_ext
    {α : Type*} [AddCommMonoid α]
    (t : PTree) (g h : Forest × PTree → α)
    (hgh : ∀ p ∈ coproductSupportFinset t, g p = h p) :
    (coproductSupportFinset t).sum g =
      (coproductSupportFinset t).sum h := by
  classical
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact hgh p hp

theorem coproductSupportFinset_sum_subtype
    {α : Type*} [AddCommMonoid α]
    (t : PTree) (g : {p // p ∈ coproductSupportFinset t} → α) :
    (Finset.univ : Finset {p // p ∈ coproductSupportFinset t}).sum g =
      (coproductSupportFinset t).sum
        (fun p => if h : p ∈ coproductSupportFinset t then g ⟨p, h⟩ else 0) := by
  classical
  let s := coproductSupportFinset t
  let f : Forest × PTree → α :=
    fun p => if h : p ∈ s then g ⟨p, h⟩ else 0
  have hsum :
      (Finset.univ : Finset {p // p ∈ s}).sum g = s.sum f := by
    classical
    refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x hx
      exact x.2
    · intro x hx y hy hxy
      exact Subtype.ext (by simpa using hxy)
    · intro y hy
      refine ⟨⟨y, hy⟩, by simp, rfl⟩
    · intro x hx
      have hx' : x.1 ∈ s := x.2
      simp [f, hx', Subtype.ext_iff]
  simpa [s, f] using hsum

end CoproductSupport

end QuotientConnected

namespace QuotientConnected
namespace CoproductSupport

/-- The raw coproduct list itself, recorded under the support namespace. -/
def coproductSupportList (t : PTree) : List (Forest × PTree) :=
  PTree.coproductData t

@[simp] theorem mem_coproductSupportList_iff
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportList t ↔ p ∈ coproductSupport t := by
  rfl

@[simp] theorem coproductSupportList_contains_trivial (t : PTree) :
    ([], t) ∈ coproductSupportList t := by
  simpa [coproductSupportList] using coproductSupport_contains_trivial t

theorem coproductSupportList_nonempty (t : PTree) :
    (coproductSupportList t).length > 0 := by
  cases h : coproductSupportList t with
  | nil =>
      have hmem : ([], t) ∈ ([] : List (Forest × PTree)) := by
        simpa [h] using coproductSupportList_contains_trivial t
      cases hmem
  | cons a l =>
      simp [h]

theorem coproductSupportList_length_pos (t : PTree) :
    0 < (coproductSupportList t).length := by
  exact coproductSupportList_nonempty t

@[simp] theorem coproductSupportList_length_eq_data (t : PTree) :
    (coproductSupportList t).length = (PTree.coproductData t).length := by
  rfl

@[simp] theorem coproductSupportList_map_fst (t : PTree) :
    (coproductSupportList t).map Prod.fst = coproductForestsList t := by
  rfl

@[simp] theorem coproductSupportList_map_snd (t : PTree) :
    (coproductSupportList t).map Prod.snd = coproductRemaindersList t := by
  rfl

@[simp] theorem coproductForestsList_length_eq_support (t : PTree) :
    (coproductForestsList t).length = (coproductSupportList t).length := by
  simp [coproductForestsList, coproductSupportList]

@[simp] theorem coproductRemaindersList_length_eq_support (t : PTree) :
    (coproductRemaindersList t).length = (coproductSupportList t).length := by
  simp [coproductRemaindersList, coproductSupportList]

theorem coproductSupportList_mem_fst
    {t : PTree} {p : Forest × PTree}
    (hp : p ∈ coproductSupportList t) :
    p.1 ∈ coproductForestsList t := by
  exact coproductForestsList_mem_of_support (t := t) (f := p.1) (r := p.2) hp

theorem coproductSupportList_mem_snd
    {t : PTree} {p : Forest × PTree}
    (hp : p ∈ coproductSupportList t) :
    p.2 ∈ coproductRemaindersList t := by
  exact coproductRemaindersList_mem_of_support (t := t) (f := p.1) (r := p.2) hp

def coproductSupportListSet (t : PTree) : Set (Forest × PTree) :=
  { p | p ∈ coproductSupportList t }

@[simp] theorem mem_coproductSupportListSet_iff
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportListSet t ↔ p ∈ coproductSupportList t := by
  rfl

theorem coproductSupportListSet_eq (t : PTree) :
    coproductSupportListSet t = coproductSupport t := by
  ext p
  rfl

theorem coproductSupportListSet_eq_finset (t : PTree) :
    coproductSupportListSet t = (coproductSupportFinset t : Set (Forest × PTree)) := by
  calc
    coproductSupportListSet t = coproductSupport t := coproductSupportListSet_eq t
    _ = (coproductSupportFinset t : Set (Forest × PTree)) := (coproductSupportFinset_coe t).symm

theorem coproductSupportListSet_nonempty (t : PTree) :
    (coproductSupportListSet t).Nonempty := by
  rcases coproductSupport_nonempty t with ⟨p, hp⟩
  exact ⟨p, (mem_coproductSupportListSet_iff t p).2 (by
    simpa [coproductSupportList, coproductSupport] using hp)⟩

theorem coproductSupportListSet_finite (t : PTree) :
    Set.Finite (coproductSupportListSet t) := by
  classical
  simpa [coproductSupportListSet_eq t] using coproductSupport_finite t

theorem coproductSupportListSet_subset_product (t : PTree) :
    Set.Subset (coproductSupportListSet t)
      (Set.prod (coproductForests t) (coproductRemainders t)) := by
  simpa [coproductSupportListSet_eq t] using coproductSupport_subset_product t

theorem coproductSupportListSet_contains_trivial (t : PTree) :
    ([], t) ∈ coproductSupportListSet t := by
  simpa using coproductSupportList_contains_trivial t

theorem coproductSupportListSet_card_pos (t : PTree) :
    (coproductSupportListSet t).Nonempty := by
  exact coproductSupportListSet_nonempty t

theorem coproductSupportListSet_image_fst
    (t : PTree) :
    Set.image Prod.fst (coproductSupportListSet t) = coproductForests t := by
  calc
    Set.image Prod.fst (coproductSupportListSet t)
        = Set.image Prod.fst (coproductSupport t) := by
          simpa [coproductSupportListSet_eq t]
    _ = coproductForests t := (coproductForests_eq_image_fst t).symm

theorem coproductSupportListSet_image_snd
    (t : PTree) :
    Set.image Prod.snd (coproductSupportListSet t) = coproductRemainders t := by
  calc
    Set.image Prod.snd (coproductSupportListSet t)
        = Set.image Prod.snd (coproductSupport t) := by
          simpa [coproductSupportListSet_eq t]
    _ = coproductRemainders t := (coproductRemainders_eq_image_snd t).symm

theorem coproductSupportListSet_image_fst_subset
    (t : PTree) :
    Set.image Prod.fst (coproductSupportListSet t) ⊆ coproductForests t := by
  intro f hf
  rcases hf with ⟨p, hp, rfl⟩
  have hp' : p ∈ coproductSupport t := by
    simpa [coproductSupportListSet_eq t] using hp
  exact coproductForests_mem_of_support (t := t) hp'

theorem coproductSupportListSet_image_snd_subset
    (t : PTree) :
    Set.image Prod.snd (coproductSupportListSet t) ⊆ coproductRemainders t := by
  intro r hr
  rcases hr with ⟨p, hp, rfl⟩
  have hp' : p ∈ coproductSupport t := by
    simpa [coproductSupportListSet_eq t] using hp
  exact coproductRemainders_mem_of_support (t := t) hp'

-- old version (disabled; contained mojibake bullets)
theorem coproductSupportList_mem_iff_finset
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportList t ↔ p ∈ coproductSupportFinset t := by
  constructor
  · intro hp
    exact (mem_coproductSupportFinset t p).2 hp
  · intro hp
    exact (mem_coproductSupportFinset t p).1 hp

--
theorem coproductSupportListSet_eq_finset_coe (t : PTree) :
    coproductSupportListSet t = (coproductSupportFinset t : Set (Forest × PTree)) := by
  exact coproductSupportListSet_eq_finset t

/- A bundled, list-based summary of coproduct support. -/
structure CoproductSupportSummary where
  supportList : List (Forest × PTree)
  forestsList : List Forest
  remaindersList : List PTree
  forestsList_eq : forestsList = supportList.map Prod.fst
  remaindersList_eq : remaindersList = supportList.map Prod.snd

/- The concrete summary for `PTree.coproductData`. -/
def coproductSupportSummary (t : PTree) : CoproductSupportSummary :=
  { supportList := PTree.coproductData t
    forestsList := coproductForestsList t
    remaindersList := coproductRemaindersList t
    forestsList_eq := rfl
    remaindersList_eq := rfl }

@[simp] theorem coproductSupportSummary_supportList (t : PTree) :
    (coproductSupportSummary t).supportList = PTree.coproductData t := by
  rfl

@[simp] theorem coproductSupportSummary_forestsList (t : PTree) :
    (coproductSupportSummary t).forestsList = coproductForestsList t := by
  rfl

@[simp] theorem coproductSupportSummary_remaindersList (t : PTree) :
    (coproductSupportSummary t).remaindersList = coproductRemaindersList t := by
  rfl

theorem coproductSupportSummary_forestsList_eq (t : PTree) :
    (coproductSupportSummary t).forestsList =
      (coproductSupportSummary t).supportList.map Prod.fst := by
  simpa using (coproductSupportSummary t).forestsList_eq

theorem coproductSupportSummary_remaindersList_eq (t : PTree) :
    (coproductSupportSummary t).remaindersList =
      (coproductSupportSummary t).supportList.map Prod.snd := by
  simpa using (coproductSupportSummary t).remaindersList_eq

def coproductSupportSummary_supportSet (t : PTree) : Set (Forest × PTree) :=
  { p | p ∈ (coproductSupportSummary t).supportList }

def coproductSupportSummary_forestsSet (t : PTree) : Set Forest :=
  { f | f ∈ (coproductSupportSummary t).forestsList }

def coproductSupportSummary_remaindersSet (t : PTree) : Set PTree :=
  { r | r ∈ (coproductSupportSummary t).remaindersList }

@[simp] theorem mem_coproductSupportSummary_supportSet
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportSummary_supportSet t ↔
      p ∈ (coproductSupportSummary t).supportList := by
  rfl

@[simp] theorem mem_coproductSupportSummary_forestsSet
    (t : PTree) (f : Forest) :
    f ∈ coproductSupportSummary_forestsSet t ↔
      f ∈ (coproductSupportSummary t).forestsList := by
  rfl

@[simp] theorem mem_coproductSupportSummary_remaindersSet
    (t : PTree) (r : PTree) :
    r ∈ coproductSupportSummary_remaindersSet t ↔
      r ∈ (coproductSupportSummary t).remaindersList := by
  rfl

theorem coproductSupportSummary_supportSet_eq (t : PTree) :
    coproductSupportSummary_supportSet t = coproductSupportListSet t := by
  rfl

theorem coproductSupportSummary_forestsSet_eq (t : PTree) :
    coproductSupportSummary_forestsSet t = coproductForestsListSet t := by
  rfl

theorem coproductSupportSummary_remaindersSet_eq (t : PTree) :
    coproductSupportSummary_remaindersSet t = coproductRemaindersListSet t := by
  rfl

theorem coproductSupportSummary_supportSet_eq_finset (t : PTree) :
    coproductSupportSummary_supportSet t =
      (coproductSupportFinset t : Set (Forest × PTree)) := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_eq_finset t

theorem coproductSupportSummary_supportSet_eq_support (t : PTree) :
    coproductSupportSummary_supportSet t = coproductSupport t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    (coproductSupportListSet_eq t)

theorem coproductSupportSummary_supportSet_nonempty (t : PTree) :
    Set.Nonempty (coproductSupportSummary_supportSet t) := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_nonempty t

theorem coproductForestsListSet_nonempty (t : PTree) :
    (coproductForestsListSet t).Nonempty := by
  refine ⟨([] : Forest), ?_⟩
  exact (mem_coproductForestsListSet_iff t []).2 (coproductForestsList_contains_nil t)

theorem coproductRemaindersListSet_nonempty (t : PTree) :
    (coproductRemaindersListSet t).Nonempty := by
  refine ⟨t, ?_⟩
  exact (mem_coproductRemaindersListSet_iff t t).2 (coproductRemaindersList_contains_root t)

theorem coproductSupportSummary_forestsSet_nonempty (t : PTree) :
    Set.Nonempty (coproductSupportSummary_forestsSet t) := by
  simpa [coproductSupportSummary_forestsSet_eq] using
    coproductForestsListSet_nonempty t

theorem coproductSupportSummary_remaindersSet_nonempty (t : PTree) :
    Set.Nonempty (coproductSupportSummary_remaindersSet t) := by
  simpa [coproductSupportSummary_remaindersSet_eq] using
    coproductRemaindersListSet_nonempty t

theorem coproductSupportSummary_supportSet_finite (t : PTree) :
    Set.Finite (coproductSupportSummary_supportSet t) := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_finite t

theorem coproductForestsListSet_finite (t : PTree) :
    Set.Finite (coproductForestsListSet t) := by
  classical
  refine (List.toFinset (coproductForestsList t)).finite_toSet.subset ?_
  intro f hf
  exact List.mem_toFinset.mpr (by
    simpa [coproductForestsListSet] using hf)

theorem coproductRemaindersListSet_finite (t : PTree) :
    Set.Finite (coproductRemaindersListSet t) := by
  classical
  refine (List.toFinset (coproductRemaindersList t)).finite_toSet.subset ?_
  intro r hr
  exact List.mem_toFinset.mpr (by
    simpa [coproductRemaindersListSet] using hr)

theorem coproductSupportSummary_forestsSet_finite (t : PTree) :
    Set.Finite (coproductSupportSummary_forestsSet t) := by
  simpa [coproductSupportSummary_forestsSet_eq] using
    coproductForestsListSet_finite t

theorem coproductSupportSummary_remaindersSet_finite (t : PTree) :
    Set.Finite (coproductSupportSummary_remaindersSet t) := by
  simpa [coproductSupportSummary_remaindersSet_eq] using
    coproductRemaindersListSet_finite t

theorem coproductSupportSummary_supportSet_contains_trivial (t : PTree) :
    ([], t) ∈ coproductSupportSummary_supportSet t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_contains_trivial t

theorem coproductSupportListSet_subset_product_list (t : PTree) :
    Set.Subset (coproductSupportListSet t)
      (Set.prod (coproductForestsListSet t) (coproductRemaindersListSet t)) := by
  intro p hp
  have hp' : p ∈ coproductSupportList t := by
    simpa [coproductSupportListSet] using hp
  have hf : p.1 ∈ coproductForestsList t :=
    coproductSupportList_mem_fst (t := t) hp'
  have hr : p.2 ∈ coproductRemaindersList t :=
    coproductSupportList_mem_snd (t := t) hp'
  exact And.intro
    ((mem_coproductForestsListSet_iff t p.1).2 hf)
    ((mem_coproductRemaindersListSet_iff t p.2).2 hr)

theorem coproductSupportSummary_supportSet_subset_product_list (t : PTree) :
    Set.Subset (coproductSupportSummary_supportSet t)
      (Set.prod (coproductSupportSummary_forestsSet t)
        (coproductSupportSummary_remaindersSet t)) := by
  simpa [coproductSupportSummary_supportSet_eq,
    coproductSupportSummary_forestsSet_eq,
    coproductSupportSummary_remaindersSet_eq] using
    coproductSupportListSet_subset_product_list t

theorem coproductSupportListSet_subset_product_finset (t : PTree) :
    Set.Subset (coproductSupportListSet t)
      (Set.prod (coproductForestsFinset t : Set Forest)
        (coproductRemaindersFinset t : Set PTree)) := by
  intro p hp
  have hp' : p ∈ coproductSupport t := by
    simpa [coproductSupportListSet_eq t] using hp
  have hf : p.1 ∈ coproductForests t :=
    coproductForests_mem_of_support (t := t) hp'
  have hr : p.2 ∈ coproductRemainders t :=
    coproductRemainders_mem_of_support (t := t) hp'
  have hf' : p.1 ∈ (coproductForestsFinset t : Set Forest) := by
    simpa [coproductForestsFinset_coe] using hf
  have hr' : p.2 ∈ (coproductRemaindersFinset t : Set PTree) := by
    simpa [coproductRemaindersFinset_coe] using hr
  exact And.intro hf' hr'

theorem coproductSupportSummary_supportSet_subset_product_finset (t : PTree) :
    Set.Subset (coproductSupportSummary_supportSet t)
      (Set.prod (coproductForestsFinset t : Set Forest)
        (coproductRemaindersFinset t : Set PTree)) := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_subset_product_finset t

theorem coproductSupportSummary_supportSet_image_fst (t : PTree) :
    Set.image Prod.fst (coproductSupportSummary_supportSet t) = coproductForests t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_image_fst t

theorem coproductSupportSummary_supportSet_image_snd (t : PTree) :
    Set.image Prod.snd (coproductSupportSummary_supportSet t) = coproductRemainders t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_image_snd t

theorem coproductSupportListSet_image_fst_list (t : PTree) :
    Set.image Prod.fst (coproductSupportListSet t) = coproductForestsListSet t := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨p, hp, rfl⟩
    have hp' : p ∈ coproductSupportList t := by
      simpa [coproductSupportListSet] using hp
    exact (mem_coproductForestsListSet_iff t p.1).2
      (coproductSupportList_mem_fst (t := t) hp')
  · intro hf
    have hf' : f ∈ coproductForestsList t := by
      simpa [coproductForestsListSet] using hf
    rcases (mem_coproductForestsList_iff t f).1 hf' with ⟨r, hr⟩
    refine ⟨(f, r), ?_, rfl⟩
    exact (mem_coproductSupportListSet_iff t (f, r)).2 hr

theorem coproductSupportListSet_image_snd_list (t : PTree) :
    Set.image Prod.snd (coproductSupportListSet t) = coproductRemaindersListSet t := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨p, hp, rfl⟩
    have hp' : p ∈ coproductSupportList t := by
      simpa [coproductSupportListSet] using hp
    exact (mem_coproductRemaindersListSet_iff t p.2).2
      (coproductSupportList_mem_snd (t := t) hp')
  · intro hr
    have hr' : r ∈ coproductRemaindersList t := by
      simpa [coproductRemaindersListSet] using hr
    rcases (mem_coproductRemaindersList_iff t r).1 hr' with ⟨f, hf⟩
    refine ⟨(f, r), ?_, rfl⟩
    exact (mem_coproductSupportListSet_iff t (f, r)).2 hf


theorem coproductSupportSummary_supportSet_image_fst_list (t : PTree) :
    Set.image Prod.fst (coproductSupportSummary_supportSet t) =
      coproductForestsListSet t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_image_fst_list t

theorem coproductSupportSummary_supportSet_image_snd_list (t : PTree) :
    Set.image Prod.snd (coproductSupportSummary_supportSet t) =
      coproductRemaindersListSet t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    coproductSupportListSet_image_snd_list t

theorem coproductSupportListSet_mem_iff_finset
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportListSet t ↔ p ∈ coproductSupportFinset t := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    intro hp
    have hp' : p ∈ coproductSupportList t := by
      simpa [coproductSupportListSet] using hp
    exact (mem_coproductSupportFinset t p).2 hp'
  case mpr =>
    intro hp
    have hp' : p ∈ coproductSupportList t :=
      (mem_coproductSupportFinset t p).1 hp
    exact (mem_coproductSupportListSet_iff t p).2 hp'

theorem coproductForestsListSet_eq_image_fst_list (t : PTree) :
    coproductForestsListSet t = Set.image Prod.fst (coproductSupportListSet t) := by
  simpa [coproductSupportListSet_image_fst_list] using
    (coproductSupportListSet_image_fst_list t).symm

theorem coproductRemaindersListSet_eq_image_snd_list (t : PTree) :
    coproductRemaindersListSet t = Set.image Prod.snd (coproductSupportListSet t) := by
  simpa [coproductSupportListSet_image_snd_list] using
    (coproductSupportListSet_image_snd_list t).symm

theorem coproductSupportSummary_supportSet_mem_iff_finset
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportSummary_supportSet t ↔ p ∈ coproductSupportFinset t := by
  simpa [coproductSupportSummary_supportSet_eq] using
    (coproductSupportListSet_mem_iff_finset t p)

theorem coproductSupportSummary_supportList_toFinset (t : PTree) :
    (coproductSupportSummary t).supportList.toFinset = coproductSupportFinset t := by
  rfl

theorem coproductSupportSummary_forestsList_toFinset (t : PTree) :
    (coproductSupportSummary t).forestsList.toFinset =
      (coproductSupportFinset t).image Prod.fst := by
  classical
  ext f
  constructor
  · intro hf
    have hf' : f ∈ coproductForestsList t := (List.mem_toFinset).1 hf
    obtain ⟨r, hr⟩ := (mem_coproductForestsList_iff t f).1 hf'
    exact Finset.mem_image.2 ⟨(f, r), (mem_coproductSupportFinset t (f, r)).2 hr, rfl⟩
  · intro hf
    obtain ⟨p, hp, hpf⟩ := Finset.mem_image.1 hf
    have hdata := (mem_coproductSupportFinset t p).1 hp
    have hflist : f ∈ coproductForestsList t := by
      refine (mem_coproductForestsList_iff t f).2 ⟨p.2, ?_⟩
      have heq : p = (f, p.2) := Prod.ext hpf rfl
      rwa [← heq]
    exact (List.mem_toFinset).2 hflist

theorem coproductSupportSummary_remaindersList_toFinset (t : PTree) :
    (coproductSupportSummary t).remaindersList.toFinset =
      (coproductSupportFinset t).image Prod.snd := by
  classical
  ext r
  constructor
  · intro hr
    have hr' : r ∈ coproductRemaindersList t := (List.mem_toFinset).1 hr
    obtain ⟨f, hf⟩ := (mem_coproductRemaindersList_iff t r).1 hr'
    exact Finset.mem_image.2 ⟨(f, r), (mem_coproductSupportFinset t (f, r)).2 hf, rfl⟩
  · intro hr
    obtain ⟨p, hp, hpr⟩ := Finset.mem_image.1 hr
    have hdata := (mem_coproductSupportFinset t p).1 hp
    have hrlist : r ∈ coproductRemaindersList t := by
      refine (mem_coproductRemaindersList_iff t r).2 ⟨p.1, ?_⟩
      have heq : p = (p.1, r) := Prod.ext rfl hpr
      rwa [← heq]
    exact (List.mem_toFinset).2 hrlist

theorem coproductSupportSummary_supportList_length_pos (t : PTree) :
    (coproductSupportSummary t).supportList.length > 0 := by
  simpa using coproductSupportList_nonempty t

theorem coproductSupportSummary_forestsList_length_pos (t : PTree) :
    (coproductSupportSummary t).forestsList.length > 0 := by
  simpa using coproductForestsList_nonempty t

theorem coproductSupportSummary_remaindersList_length_pos (t : PTree) :
    (coproductSupportSummary t).remaindersList.length > 0 := by
  simpa using coproductRemaindersList_nonempty t

noncomputable def coproductSupportSummary_supportFinset (t : PTree) : Finset (Forest × PTree) :=
  (coproductSupportSummary t).supportList.toFinset

noncomputable def coproductSupportSummary_forestsFinset (t : PTree) : Finset Forest :=
  (coproductSupportSummary_supportFinset t).image Prod.fst

noncomputable def coproductSupportSummary_remaindersFinset (t : PTree) : Finset PTree :=
  (coproductSupportSummary_supportFinset t).image Prod.snd

@[simp] theorem coproductSupportSummary_supportFinset_eq (t : PTree) :
    coproductSupportSummary_supportFinset t = coproductSupportFinset t := by
  simpa [coproductSupportSummary_supportFinset] using
    (coproductSupportSummary_supportList_toFinset t)

@[simp] theorem coproductSupportSummary_forestsFinset_eq (t : PTree) :
    coproductSupportSummary_forestsFinset t = coproductForestsFinset t := by
  simpa [coproductSupportSummary_forestsFinset,
    coproductSupportSummary_supportFinset_eq] using
    (coproductForestsFinset_eq_image_fst t)

@[simp] theorem coproductSupportSummary_remaindersFinset_eq (t : PTree) :
    coproductSupportSummary_remaindersFinset t = coproductRemaindersFinset t := by
  simpa [coproductSupportSummary_remaindersFinset,
    coproductSupportSummary_supportFinset_eq] using
    (coproductRemaindersFinset_eq_image_snd t)

theorem coproductSupportSummary_forestsSet_eq_image_fst_supportSet (t : PTree) :
    coproductSupportSummary_forestsSet t =
      Set.image Prod.fst (coproductSupportSummary_supportSet t) := by
  simpa [coproductSupportSummary_forestsSet_eq,
    coproductSupportSummary_supportSet_eq] using
    (coproductForestsListSet_eq_image_fst_list t)

theorem coproductSupportSummary_remaindersSet_eq_image_snd_supportSet (t : PTree) :
    coproductSupportSummary_remaindersSet t =
      Set.image Prod.snd (coproductSupportSummary_supportSet t) := by
  simpa [coproductSupportSummary_remaindersSet_eq,
    coproductSupportSummary_supportSet_eq] using
    (coproductRemaindersListSet_eq_image_snd_list t)

theorem coproductSupportSummary_forestsSet_eq_finset (t : PTree) :
    coproductSupportSummary_forestsSet t = (coproductForestsFinset t : Set Forest) := by
  simpa [coproductSupportSummary_forestsSet_eq] using
    (coproductForestsListSet_eq_finset t)

theorem coproductSupportSummary_remaindersSet_eq_finset (t : PTree) :
    coproductSupportSummary_remaindersSet t = (coproductRemaindersFinset t : Set PTree) := by
  simpa [coproductSupportSummary_remaindersSet_eq] using
    (coproductRemaindersListSet_eq_finset t)

@[simp] theorem mem_coproductSupportSummary_supportFinset
    (t : PTree) (p : Forest × PTree) :
    p ∈ coproductSupportSummary_supportFinset t ↔
      p ∈ (coproductSupportSummary t).supportList := by
  classical
  simp [coproductSupportSummary_supportFinset]


theorem coproductSupportSummary_supportFinset_coe (t : PTree) :
    (coproductSupportSummary_supportFinset t : Set (Forest × PTree)) =
      coproductSupportSummary_supportSet t := by
  classical
  ext p
  simp [coproductSupportSummary_supportFinset, coproductSupportSummary_supportSet]

theorem coproductSupportSummary_forestsFinset_coe (t : PTree) :
    (coproductSupportSummary_forestsFinset t : Set Forest) =
      coproductSupportSummary_forestsSet t := by
  classical
  ext f
  -- reduce to finset coercions directly
  simp [coproductSupportSummary_forestsFinset_eq,
        coproductSupportSummary_forestsSet_eq,
        coproductForestsFinset_coe,
        coproductForestsListSet_eq_finset]

theorem coproductSupportSummary_remaindersFinset_coe (t : PTree) :
    (coproductSupportSummary_remaindersFinset t : Set PTree) =
      coproductSupportSummary_remaindersSet t := by
  classical
  ext r
  simp [coproductSupportSummary_remaindersFinset_eq,
        coproductSupportSummary_remaindersSet_eq,
        coproductRemaindersFinset_coe,
        coproductRemaindersListSet_eq_finset]

/-!
### Support-level coproduct packaging

The list/finset summaries above are enough to define finitary sums over the
coproduct support without committing to any algebraic structure.  We package
just the support-layer information we currently have, and provide a canonical
finitary summation operator that will later be reused in linearization.
-/

structure CoproductSupportData where
  support : PTree -> Set (Prod Forest PTree)
  support_finite : forall t : PTree, Set.Finite (support t)
  forests : PTree -> Set Forest
  remainders : PTree -> Set PTree
  support_subset_product :
    forall t : PTree,
      Set.Subset (support t) (Set.prod (forests t) (remainders t))
  forests_eq_image_fst :
    forall t : PTree, forests t = Set.image Prod.fst (support t)
  remainders_eq_image_snd :
    forall t : PTree, remainders t = Set.image Prod.snd (support t)
  support_nonempty : forall t : PTree, Set.Nonempty (support t)

def coproductSupportSummaryData : CoproductSupportData where
  support := coproductSupportSummary_supportSet
  support_finite := coproductSupportSummary_supportSet_finite
  forests := coproductSupportSummary_forestsSet
  remainders := coproductSupportSummary_remaindersSet
  support_subset_product := coproductSupportSummary_supportSet_subset_product_list
  forests_eq_image_fst := coproductSupportSummary_forestsSet_eq_image_fst_supportSet
  remainders_eq_image_snd := coproductSupportSummary_remaindersSet_eq_image_snd_supportSet
  support_nonempty := coproductSupportSummary_supportSet_nonempty

/-!
We now define a purely finitary summation operator over the coproduct support.
This is the cleanest point to attach later linear and algebraic structure.
-/

noncomputable def coproductSupportSummary_sum
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f : Prod Forest PTree -> alpha) : alpha :=
  (coproductSupportSummary_supportFinset t).sum f

@[simp] theorem coproductSupportSummary_sum_eq
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductSupportSummary_sum t f =
      (coproductSupportSummary_supportFinset t).sum f := by
  rfl

theorem coproductSupportSummary_sum_congr
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f g : Prod Forest PTree -> alpha)
    (h : forall p, p ∈ coproductSupportSummary_supportFinset t -> f p = g p) :
    coproductSupportSummary_sum t f = coproductSupportSummary_sum t g := by
  classical
  unfold coproductSupportSummary_sum
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact h p hp

theorem coproductSupportSummary_sum_eq_supportFinset
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductSupportSummary_sum t f =
      (coproductSupportFinset t).sum f := by
  classical
  simp [coproductSupportSummary_sum, coproductSupportSummary_supportFinset_eq]

theorem coproductSupportSummary_sum_eq_supportList
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductSupportSummary_sum t f =
      (coproductSupportSummary t).supportList.toFinset.sum f := by
  rfl

theorem coproductSupportSummary_sum_one_eq_card (t : PTree) :
    coproductSupportSummary_sum t (fun _ => (1 : Nat)) =
      (coproductSupportSummary_supportFinset t).card := by
  classical
  simp [coproductSupportSummary_sum]

theorem coproductSupportSummary_sum_eq_card (t : PTree) :
    coproductSupportSummary_sum t (fun _ => (1 : Nat)) =
      (coproductSupportFinset t).card := by
  classical
  simpa [coproductSupportSummary_supportFinset_eq,
    coproductSupportSummary_sum] using
    (coproductSupportSummary_sum_one_eq_card t)

theorem coproductSupportSummary_sum_zero
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) :
    coproductSupportSummary_sum t (fun _ => (0 : alpha)) = 0 := by
  classical
  simp [coproductSupportSummary_sum]

theorem coproductSupportSummary_sum_add
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f g : Prod Forest PTree -> alpha) :
    coproductSupportSummary_sum t (fun p => f p + g p) =
      coproductSupportSummary_sum t f + coproductSupportSummary_sum t g := by
  classical
  simp [coproductSupportSummary_sum, Finset.sum_add_distrib]

theorem coproductSupportSummary_sum_congr_supportSet
    {alpha : Type*} [AddCommMonoid alpha]
    (t : PTree) (f g : Prod Forest PTree -> alpha)
    (h : forall p, p ∈ coproductSupportSummary_supportSet t -> f p = g p) :
    coproductSupportSummary_sum t f = coproductSupportSummary_sum t g := by
  classical
  refine coproductSupportSummary_sum_congr t f g ?_
  intro p hp
  have hp_list : p ∈ (coproductSupportSummary t).supportList := by
    exact (mem_coproductSupportSummary_supportFinset t p).1 hp
  have hp_set : p ∈ coproductSupportSummary_supportSet t := by
    exact (mem_coproductSupportSummary_supportSet t p).2 hp_list
  exact h p hp_set

@[simp] theorem coproductSupportSummary_forestsFinset_eq_image_fst_supportFinset
    (t : PTree) :
    coproductSupportSummary_forestsFinset t =
      (coproductSupportSummary_supportFinset t).image Prod.fst := by
  rfl

@[simp] theorem coproductSupportSummary_remaindersFinset_eq_image_snd_supportFinset
    (t : PTree) :
    coproductSupportSummary_remaindersFinset t =
      (coproductSupportSummary_supportFinset t).image Prod.snd := by
  rfl

theorem coproductSupportSummary_supportFinset_nonempty (t : PTree) :
    (coproductSupportSummary_supportFinset t).Nonempty := by
  classical
  rcases coproductSupportSummary_supportSet_nonempty t with ⟨p, hp⟩
  have hp_list : p ∈ (coproductSupportSummary t).supportList := by
    exact (mem_coproductSupportSummary_supportSet t p).1 hp
  exact ⟨p, (mem_coproductSupportSummary_supportFinset t p).2 hp_list⟩

theorem coproductSupportSummary_forestsFinset_nonempty (t : PTree) :
    (coproductSupportSummary_forestsFinset t).Nonempty := by
  classical
  refine ⟨[], ?_⟩
  simpa [coproductSupportSummary_forestsFinset_eq] using
    (coproductForestsFinset_contains_nil t)

theorem coproductSupportSummary_remaindersFinset_nonempty (t : PTree) :
    (coproductSupportSummary_remaindersFinset t).Nonempty := by
  classical
  refine ⟨t, ?_⟩
  simpa [coproductSupportSummary_remaindersFinset_eq] using
    (coproductRemaindersFinset_contains_root t)

theorem coproductSupportSummary_supportFinset_card_pos (t : PTree) :
    0 < (coproductSupportSummary_supportFinset t).card := by
  classical
  exact Finset.card_pos.mpr (coproductSupportSummary_supportFinset_nonempty t)

theorem coproductSupportSummary_forestsFinset_card_pos (t : PTree) :
    0 < (coproductSupportSummary_forestsFinset t).card := by
  classical
  exact Finset.card_pos.mpr (coproductSupportSummary_forestsFinset_nonempty t)

theorem coproductSupportSummary_remaindersFinset_card_pos (t : PTree) :
    0 < (coproductSupportSummary_remaindersFinset t).card := by
  classical
  exact Finset.card_pos.mpr (coproductSupportSummary_remaindersFinset_nonempty t)

theorem coproductSupportSummary_supportFinset_subset_product_finset (t : PTree) :
    Set.Subset (coproductSupportSummary_supportFinset t : Set (Forest × PTree))
      (Set.prod (coproductSupportSummary_forestsFinset t : Set Forest)
        (coproductSupportSummary_remaindersFinset t : Set PTree)) := by
  intro p hp
  have hp1 : p ∈ (coproductSupportFinset t : Set (Forest × PTree)) := by
    simpa [coproductSupportSummary_supportFinset_eq] using hp
  have hp2 : p ∈ coproductSupport t := by
    simpa [coproductSupportFinset_coe] using hp1
  have hp3 : p ∈ coproductSupportSummary_supportSet t := by
    simpa [coproductSupportSummary_supportSet_eq_support] using hp2
  have hprod :
      p ∈ Set.prod (coproductSupportSummary_forestsSet t)
            (coproductSupportSummary_remaindersSet t) :=
    (coproductSupportSummary_supportSet_subset_product_list t) hp3
  simpa [coproductSupportSummary_forestsSet_eq_finset,
    coproductSupportSummary_remaindersSet_eq_finset] using hprod



/-!
### Linear extension of support-level sums

We can linearly extend any support-level assignment to the free carrier
`linearProofTreeCarrier` by summing coefficients against the tree generators.
This is the exact shape needed later for a coproduct linear map.
-/

section CoproductSupportLinear

noncomputable def coproductSupportSummary_sum_linear
    {alpha : Type*} [AddCommMonoid alpha] [Module Int alpha]
    (f : Prod Forest PTree -> alpha) :
    LinearMap (RingHom.id Int) linearProofTreeCarrier alpha :=
  Finsupp.lsum Int (fun x : PTree =>
    (LinearMap.id : LinearMap (RingHom.id Int) Int Int).smulRight
      (coproductSupportSummary_sum x f))

@[simp] theorem coproductSupportSummary_sum_linear_treeGen
    {alpha : Type*} [AddCommMonoid alpha] [Module Int alpha]
    (f : Prod Forest PTree -> alpha) (x : PTree) :
    coproductSupportSummary_sum_linear f (treeGen x) =
      coproductSupportSummary_sum x f := by
  classical
  simp only [coproductSupportSummary_sum_linear, treeGen, Finsupp.lsum_single,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  exact one_smul ℤ _



theorem coproductSupportSummary_sum_linear_apply
    {alpha : Type*} [AddCommMonoid alpha] [Module Int alpha]
    (f : Prod Forest PTree -> alpha) (a : linearProofTreeCarrier) :
    coproductSupportSummary_sum_linear f a =
      a.sum (fun x c => c • coproductSupportSummary_sum x f) := by
  simp [coproductSupportSummary_sum_linear, Finsupp.lsum_apply]

@[simp] theorem coproductSupportSummary_sum_linear_add
    {alpha : Type*} [AddCommMonoid alpha] [Module Int alpha]
    (f : Prod Forest PTree -> alpha) (a b : linearProofTreeCarrier) :
    coproductSupportSummary_sum_linear f (a + b) =
      coproductSupportSummary_sum_linear f a +
        coproductSupportSummary_sum_linear f b := by
  simpa using (coproductSupportSummary_sum_linear f).map_add a b

@[simp] theorem coproductSupportSummary_sum_linear_smul
    {alpha : Type*} [AddCommMonoid alpha] [Module Int alpha]
    (f : Prod Forest PTree -> alpha) (z : Int) (a : linearProofTreeCarrier) :
    coproductSupportSummary_sum_linear f (z • a) =
      z • coproductSupportSummary_sum_linear f a := by
  simpa using (coproductSupportSummary_sum_linear f).map_smul z a

end CoproductSupportLinear

/-!
### Forest generators and a raw linear coproduct

We now introduce a simple "forest generator" map that sums tree generators
over a list. This lets us define a raw linear coproduct valued in the tensor
product of the free carrier with itself, still purely at the support level.
-/

section CoproductSupportTensor

noncomputable def forestGen : Forest -> linearProofTreeCarrier
  | [] => 0
  | t :: ts => treeGen t + forestGen ts

@[simp] theorem forestGen_nil :
    forestGen ([] : Forest) = 0 := by
  rfl

@[simp] theorem forestGen_cons (t : PTree) (ts : Forest) :
    forestGen (t :: ts) = treeGen t + forestGen ts := by
  rfl

theorem forestGen_append (xs ys : Forest) :
    forestGen (xs ++ ys) = forestGen xs + forestGen ys := by
  induction xs with
  | nil =>
      simp [forestGen]
  | cons t ts ih =>
      simp [forestGen, ih, add_assoc, add_left_comm, add_comm]

noncomputable def coproductSupportSummary_tensorGen
    (p : Prod Forest PTree) :
    TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier :=
  TensorProduct.tmul Int (forestGen p.1) (treeGen p.2)

noncomputable def coproductSupportSummary_comul_linear :
    LinearMap (RingHom.id Int) linearProofTreeCarrier
      (TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier) :=
  coproductSupportSummary_sum_linear
    (alpha := TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier)
    coproductSupportSummary_tensorGen

noncomputable def coproductSupportSummary_counit_linear :
    LinearMap (RingHom.id Int) linearProofTreeCarrier Int :=
  coproductSupportSummary_sum_linear
    (alpha := Int)
    (fun p => if p.1 = [] then 0 else 0)

@[simp] theorem coproductSupportSummary_comul_linear_treeGen (x : PTree) :
    coproductSupportSummary_comul_linear (treeGen x) =
      coproductSupportSummary_sum x coproductSupportSummary_tensorGen := by
  simp [coproductSupportSummary_comul_linear,
    coproductSupportSummary_sum_linear_treeGen]

theorem coproductSupportSummary_comul_linear_apply (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_linear a =
      a.sum (fun x c => c •
        coproductSupportSummary_sum x coproductSupportSummary_tensorGen) := by
  simp [coproductSupportSummary_comul_linear,
    coproductSupportSummary_sum_linear_apply]

@[simp] theorem coproductSupportSummary_comul_linear_add
    (a b : linearProofTreeCarrier) :
    coproductSupportSummary_comul_linear (a + b) =
      coproductSupportSummary_comul_linear a +
        coproductSupportSummary_comul_linear b := by
  simpa using (coproductSupportSummary_comul_linear).map_add a b

@[simp] theorem coproductSupportSummary_comul_linear_smul
    (z : Int) (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_linear (z • a) =
      z • coproductSupportSummary_comul_linear a := by
  simpa using (coproductSupportSummary_comul_linear).map_smul z a

@[simp] theorem coproductSupportSummary_counit_linear_treeGen (x : PTree) :
    coproductSupportSummary_counit_linear (treeGen x) = 0 := by
  classical
  -- the chosen counit is zero on generators at this stage
  simp [coproductSupportSummary_counit_linear,
    coproductSupportSummary_sum_linear_treeGen]

theorem coproductSupportSummary_counit_linear_apply (a : linearProofTreeCarrier) :
    coproductSupportSummary_counit_linear a =
      a.sum (fun x c =>
        c • coproductSupportSummary_sum x (fun p => if p.1 = [] then 0 else 0)) := by
  simp [coproductSupportSummary_counit_linear,
    coproductSupportSummary_sum_linear_apply]

@[simp] theorem coproductSupportSummary_counit_linear_add
    (a b : linearProofTreeCarrier) :
    coproductSupportSummary_counit_linear (a + b) =
      coproductSupportSummary_counit_linear a +
        coproductSupportSummary_counit_linear b := by
  simpa using (coproductSupportSummary_counit_linear).map_add a b

@[simp] theorem coproductSupportSummary_counit_linear_smul
    (z : Int) (a : linearProofTreeCarrier) :
    coproductSupportSummary_counit_linear (z • a) =
      z • coproductSupportSummary_counit_linear a := by
  simpa using (coproductSupportSummary_counit_linear).map_smul z a

/-!
### Raw support-level coalgebra data

At this stage we package the linear comultiplication and counit maps without
asserting any axioms.  This is a convenient target for quotient descent.
-/

structure CoproductSupportCoalgebraData where
  comul : LinearMap (RingHom.id Int) linearProofTreeCarrier
    (TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier)
  counit : LinearMap (RingHom.id Int) linearProofTreeCarrier Int

noncomputable def coproductSupportSummary_coalgebraData : CoproductSupportCoalgebraData where
  comul := coproductSupportSummary_comul_linear
  counit := coproductSupportSummary_counit_linear

@[simp] theorem coproductSupportSummary_coalgebraData_comul (a : linearProofTreeCarrier) :
    coproductSupportSummary_coalgebraData.comul a =
      coproductSupportSummary_comul_linear a := by
  rfl

@[simp] theorem coproductSupportSummary_coalgebraData_counit (a : linearProofTreeCarrier) :
    coproductSupportSummary_coalgebraData.counit a =
      coproductSupportSummary_counit_linear a := by
  rfl

/-!
### Descent to the stable quotient

To descend the raw support-level coalgebra data to the stable quotient, we ask
that the comultiplication and counit kill the stable submodule.
-/

def CoproductSupportCoalgebraRespectsStableQuotient
    (D : CoproductSupportCoalgebraData) : Prop :=
  forall a : linearProofTreeCarrier,
    a ∈ preLieDifferenceStableSubmodule ->
      D.comul a = 0 ∧ D.counit a = 0

noncomputable def coproductSupportSummary_comul_descend
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier) :=
  Submodule.liftQ
    preLieDifferenceStableSubmodule
    coproductSupportSummary_comul_linear
    (by
      intro a ha
      exact (h a ha).1)

noncomputable def coproductSupportSummary_counit_descend
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient Int :=
  Submodule.liftQ
    preLieDifferenceStableSubmodule
    coproductSupportSummary_counit_linear
    (by
      intro a ha
      exact (h a ha).2)

@[simp] theorem coproductSupportSummary_comul_descend_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_descend h
        (mkPreLieDifferenceStableQuotient a) =
      coproductSupportSummary_comul_linear a := by
  simpa [coproductSupportSummary_comul_descend,
    mkPreLieDifferenceStableQuotient] using
    (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := coproductSupportSummary_comul_linear)
      (h := by
        intro a ha
        exact (h a ha).1)
      (x := a))

@[simp] theorem coproductSupportSummary_counit_descend_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_counit_descend h
        (mkPreLieDifferenceStableQuotient a) =
      coproductSupportSummary_counit_linear a := by
  simpa [coproductSupportSummary_counit_descend,
    mkPreLieDifferenceStableQuotient] using
    (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := coproductSupportSummary_counit_linear)
      (h := by
        intro a ha
        exact (h a ha).2)
      (x := a))

structure CoproductSupportQuotientCoalgebraData where
  comul : LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
    (TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier)
  counit : LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient Int

noncomputable def coproductSupportSummary_quotientCoalgebraData
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    CoproductSupportQuotientCoalgebraData where
  comul := coproductSupportSummary_comul_descend h
  counit := coproductSupportSummary_counit_descend h

@[simp] theorem coproductSupportSummary_quotientCoalgebraData_comul
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : PreLieDifferenceStableQuotient) :
    (coproductSupportSummary_quotientCoalgebraData h).comul a =
      coproductSupportSummary_comul_descend h a := by
  rfl

@[simp] theorem coproductSupportSummary_quotientCoalgebraData_counit
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : PreLieDifferenceStableQuotient) :
    (coproductSupportSummary_quotientCoalgebraData h).counit a =
      coproductSupportSummary_counit_descend h a := by
  rfl

/-!
### Mapping the tensor factors to the stable quotient

The quotient comultiplication currently lands in the tensor of the raw carrier.
We can post-compose with the tensor map induced by the quotient map on each
factor to obtain a candidate comultiplication into
`PreLieDifferenceStableQuotient ⊗ PreLieDifferenceStableQuotient`.
-/

noncomputable def mkPreLieDifferenceStableQuotient_tensor :
    LinearMap (RingHom.id Int)
      (TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier)
      (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient) :=
  TensorProduct.map mkPreLieDifferenceStableQuotient mkPreLieDifferenceStableQuotient

@[simp] theorem mkPreLieDifferenceStableQuotient_tensor_apply
    (t : TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient_tensor t =
      TensorProduct.map mkPreLieDifferenceStableQuotient
        mkPreLieDifferenceStableQuotient t := by
  rfl

@[simp] theorem mkPreLieDifferenceStableQuotient_tensor_tmul
    (a b : linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient_tensor
        (TensorProduct.tmul Int a b) =
      TensorProduct.tmul Int
        (mkPreLieDifferenceStableQuotient a)
        (mkPreLieDifferenceStableQuotient b) := by
  dsimp [mkPreLieDifferenceStableQuotient_tensor]
  exact TensorProduct.map_tmul
    (mkPreLieDifferenceStableQuotient)
    (mkPreLieDifferenceStableQuotient) a b


@[simp] theorem mkPreLieDifferenceStableQuotient_tensor_add
    (a b : TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient_tensor (a + b) =
      mkPreLieDifferenceStableQuotient_tensor a +
        mkPreLieDifferenceStableQuotient_tensor b := by
  simpa using (mkPreLieDifferenceStableQuotient_tensor.map_add a b)

@[simp] theorem mkPreLieDifferenceStableQuotient_tensor_smul
    (z : Int)
    (a : TensorProduct Int linearProofTreeCarrier linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient_tensor (z • a) =
      z • mkPreLieDifferenceStableQuotient_tensor a := by
  simpa using (mkPreLieDifferenceStableQuotient_tensor.map_smul z a)

noncomputable def coproductSupportSummary_comul_quot
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient) :=
  mkPreLieDifferenceStableQuotient_tensor.comp
    (coproductSupportSummary_comul_descend h)

@[simp] theorem coproductSupportSummary_comul_quot_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_quot h (mkPreLieDifferenceStableQuotient a) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear a) := by
  simp [coproductSupportSummary_comul_quot,
    mkPreLieDifferenceStableQuotient_tensor,
    coproductSupportSummary_comul_descend_mk,
    LinearMap.comp_apply]

/-!
### Quotient-level coalgebra axioms (structure only)

We now state the axioms using the quotient-level comultiplication and counit.
These are placeholders for the eventual proofs once the coproduct is shown to
respect the stable quotient and satisfies coassociativity and counit laws.
-/

structure CoproductSupportQuotientCoalgebraAxioms
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) : Prop where
  coassoc :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc Int
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot h)))
        (coproductSupportSummary_comul_quot h) =
      LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
        (coproductSupportSummary_comul_quot h)
  rTensor_counit_comp_comul :
    LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h))
        (coproductSupportSummary_comul_quot h) =
      TensorProduct.mk Int
        Int
        PreLieDifferenceStableQuotient 1
  lTensor_counit_comp_comul :
    LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h))
        (coproductSupportSummary_comul_quot h) =
      (TensorProduct.mk Int
        PreLieDifferenceStableQuotient
        Int).flip 1

structure CoproductSupportQuotientCoalgebra where
  h : CoproductSupportCoalgebraRespectsStableQuotient
    coproductSupportSummary_coalgebraData
  axioms : CoproductSupportQuotientCoalgebraAxioms h

noncomputable def CoproductSupportQuotientCoalgebra.comul
    (H : CoproductSupportQuotientCoalgebra) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient) :=
  coproductSupportSummary_comul_quot H.h

noncomputable def CoproductSupportQuotientCoalgebra.counit
    (H : CoproductSupportQuotientCoalgebra) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient Int :=
  coproductSupportSummary_counit_descend H.h

@[simp] theorem CoproductSupportQuotientCoalgebra.comul_apply
    (H : CoproductSupportQuotientCoalgebra) (a : PreLieDifferenceStableQuotient) :
    H.comul a = coproductSupportSummary_comul_quot H.h a := by
  rfl

@[simp] theorem CoproductSupportQuotientCoalgebra.counit_apply
    (H : CoproductSupportQuotientCoalgebra) (a : PreLieDifferenceStableQuotient) :
    H.counit a = coproductSupportSummary_counit_descend H.h a := by
  rfl

@[simp] theorem CoproductSupportQuotientCoalgebra.comul_mk
    (H : CoproductSupportQuotientCoalgebra) (a : linearProofTreeCarrier) :
    H.comul (mkPreLieDifferenceStableQuotient a) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear a) := by
  simp [CoproductSupportQuotientCoalgebra.comul,
    coproductSupportSummary_comul_quot_mk]

@[simp] theorem CoproductSupportQuotientCoalgebra.counit_mk
    (H : CoproductSupportQuotientCoalgebra) (a : linearProofTreeCarrier) :
    H.counit (mkPreLieDifferenceStableQuotient a) =
      coproductSupportSummary_counit_linear a := by
  simp [CoproductSupportQuotientCoalgebra.counit,
    coproductSupportSummary_counit_descend_mk]

@[simp] theorem CoproductSupportQuotientCoalgebra.coassoc
    (H : CoproductSupportQuotientCoalgebra) :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc Int
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot H.h)))
        (coproductSupportSummary_comul_quot H.h) =
      LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot H.h))
        (coproductSupportSummary_comul_quot H.h) :=
  H.axioms.coassoc

@[simp] theorem CoproductSupportQuotientCoalgebra.rTensor_counit_comp_comul
    (H : CoproductSupportQuotientCoalgebra) :
    LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h) =
      TensorProduct.mk Int
        Int
        PreLieDifferenceStableQuotient 1 :=
  H.axioms.rTensor_counit_comp_comul

@[simp] theorem CoproductSupportQuotientCoalgebra.lTensor_counit_comp_comul
    (H : CoproductSupportQuotientCoalgebra) :
    LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h) =
      (TensorProduct.mk Int
        PreLieDifferenceStableQuotient
        Int).flip 1 :=
  H.axioms.lTensor_counit_comp_comul

theorem CoproductSupportQuotientCoalgebra.rTensor_counit_comp_comul_apply
    (H : CoproductSupportQuotientCoalgebra)
    (a : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h)) a =
      (TensorProduct.mk Int
        Int
        PreLieDifferenceStableQuotient 1) a := by
  simpa using congrArg (fun f => f a) H.rTensor_counit_comp_comul

theorem CoproductSupportQuotientCoalgebra.lTensor_counit_comp_comul_apply
    (H : CoproductSupportQuotientCoalgebra)
    (a : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h)) a =
      ((TensorProduct.mk Int
        PreLieDifferenceStableQuotient
        Int).flip 1) a := by
  simpa using congrArg (fun f => f a) H.lTensor_counit_comp_comul

theorem CoproductSupportQuotientCoalgebra.coassoc_apply
    (H : CoproductSupportQuotientCoalgebra)
    (a : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc Int
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot H.h)))
        (coproductSupportSummary_comul_quot H.h)) a =
      (LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot H.h))
        (coproductSupportSummary_comul_quot H.h)) a := by
  simpa using congrArg (fun f => f a) H.coassoc

theorem CoproductSupportQuotientCoalgebra.rTensor_counit_comp_comul_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    (LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h))
      (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (TensorProduct.mk Int Int PreLieDifferenceStableQuotient 1)
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa using
    (H.rTensor_counit_comp_comul_apply
      (mkPreLieDifferenceStableQuotient (treeGen x)))

theorem CoproductSupportQuotientCoalgebra.lTensor_counit_comp_comul_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    (LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend H.h))
        (coproductSupportSummary_comul_quot H.h))
      (mkPreLieDifferenceStableQuotient (treeGen x)) =
      ((TensorProduct.mk Int PreLieDifferenceStableQuotient Int).flip 1)
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa using
    (H.lTensor_counit_comp_comul_apply
      (mkPreLieDifferenceStableQuotient (treeGen x)))

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    (LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc Int
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot H.h)))
        (coproductSupportSummary_comul_quot H.h))
      (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot H.h))
        (coproductSupportSummary_comul_quot H.h))
      (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa using
    (H.coassoc_apply
      (mkPreLieDifferenceStableQuotient (treeGen x)))

theorem CoproductSupportQuotientCoalgebra.comul_add_mk
    (H : CoproductSupportQuotientCoalgebra)
    (a b : linearProofTreeCarrier) :
    H.comul (mkPreLieDifferenceStableQuotient (a + b)) =
      H.comul (mkPreLieDifferenceStableQuotient a) +
        H.comul (mkPreLieDifferenceStableQuotient b) := by
  simpa using
    (H.comul.map_add
      (mkPreLieDifferenceStableQuotient a)
      (mkPreLieDifferenceStableQuotient b))

theorem CoproductSupportQuotientCoalgebra.comul_smul_mk
    (H : CoproductSupportQuotientCoalgebra)
    (z : Int) (a : linearProofTreeCarrier) :
    H.comul (mkPreLieDifferenceStableQuotient (z • a)) =
      z • H.comul (mkPreLieDifferenceStableQuotient a) := by
  simpa using
    (H.comul.map_smul z (mkPreLieDifferenceStableQuotient a))

theorem CoproductSupportQuotientCoalgebra.counit_add_mk
    (H : CoproductSupportQuotientCoalgebra)
    (a b : linearProofTreeCarrier) :
    H.counit (mkPreLieDifferenceStableQuotient (a + b)) =
      H.counit (mkPreLieDifferenceStableQuotient a) +
        H.counit (mkPreLieDifferenceStableQuotient b) := by
  simpa using
    (H.counit.map_add
      (mkPreLieDifferenceStableQuotient a)
      (mkPreLieDifferenceStableQuotient b))

theorem CoproductSupportQuotientCoalgebra.counit_smul_mk
    (H : CoproductSupportQuotientCoalgebra)
    (z : Int) (a : linearProofTreeCarrier) :
    H.counit (mkPreLieDifferenceStableQuotient (z • a)) =
      z • H.counit (mkPreLieDifferenceStableQuotient a) := by
  simpa using
    (H.counit.map_smul z (mkPreLieDifferenceStableQuotient a))

@[simp] theorem CoproductSupportQuotientCoalgebra.comul_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) := by
  simpa using (H.comul_mk (treeGen x))

@[simp] theorem CoproductSupportQuotientCoalgebra.counit_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    H.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simp [H.counit_mk, coproductSupportSummary_counit_linear_treeGen]

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_add
    (H : CoproductSupportQuotientCoalgebra) (x y : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) := by
  simpa using
    (H.comul_add_mk (treeGen x) (treeGen y))

theorem CoproductSupportQuotientCoalgebra.counit_treeGen_add
    (H : CoproductSupportQuotientCoalgebra) (x y : PTree) :
    H.counit (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      H.counit (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen y)) := by
  simpa using
    (H.counit_add_mk (treeGen x) (treeGen y))

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_three
    (H : CoproductSupportQuotientCoalgebra) (x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have hxy :
      H.comul (mkPreLieDifferenceStableQuotient ((treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) +
          H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk (treeGen x + treeGen y) (treeGen z))
  simpa [add_assoc, H.comul_treeGen_add] using hxy

theorem CoproductSupportQuotientCoalgebra.counit_treeGen_sum_three
    (H : CoproductSupportQuotientCoalgebra) (x y z : PTree) :
    H.counit (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      H.counit (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have hxy :
      H.counit (mkPreLieDifferenceStableQuotient ((treeGen x + treeGen y) + treeGen z)) =
        H.counit (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) +
          H.counit (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.counit_add_mk (treeGen x + treeGen y) (treeGen z))
  simpa [add_assoc, H.counit_treeGen_add] using hxy

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_four
    (H : CoproductSupportQuotientCoalgebra) (w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient ((treeGen w + treeGen x) + (treeGen y + treeGen z))) =
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) +
          H.comul (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) := by
    simpa using
      (H.comul_add_mk (treeGen w + treeGen x) (treeGen y + treeGen z))
  have h2 :
      H.comul (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) =
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
          H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) := by
    simpa using
      (H.comul_treeGen_add w x)
  have h3 :
      H.comul (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
          H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_treeGen_add y z)
  -- rearrange
  simpa [add_assoc, add_left_comm, add_comm, h2, h3] using h1

theorem CoproductSupportQuotientCoalgebra.counit_treeGen_sum_four
    (H : CoproductSupportQuotientCoalgebra) (w x y z : PTree) :
    H.counit (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.counit (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.counit (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.counit (mkPreLieDifferenceStableQuotient ((treeGen w + treeGen x) + (treeGen y + treeGen z))) =
        H.counit (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) +
          H.counit (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) := by
    simpa using
      (H.counit_add_mk (treeGen w + treeGen x) (treeGen y + treeGen z))
  have h2 :
      H.counit (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) =
        H.counit (mkPreLieDifferenceStableQuotient (treeGen w)) +
          H.counit (mkPreLieDifferenceStableQuotient (treeGen x)) := by
    simpa using
      (H.counit_treeGen_add w x)
  have h3 :
      H.counit (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) =
        H.counit (mkPreLieDifferenceStableQuotient (treeGen y)) +
          H.counit (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.counit_treeGen_add y z)
  simpa [add_assoc, add_left_comm, add_comm, h2, h3] using h1

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_two_tensor
    (H : CoproductSupportQuotientCoalgebra) (x y : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) := by
  simp [H.comul_treeGen_add]

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_three_tensor
    (H : CoproductSupportQuotientCoalgebra) (x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_three, H.comul_treeGen]

theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_four_tensor
    (H : CoproductSupportQuotientCoalgebra) (w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_four, H.comul_treeGen]

noncomputable def coproductSupportSummary_comul_quot_left
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int PreLieDifferenceStableQuotient
        (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient)) :=
  LinearMap.comp
    (LinearMap.lTensor
      PreLieDifferenceStableQuotient (coproductSupportSummary_comul_quot h))
    (coproductSupportSummary_comul_quot h)

noncomputable def coproductSupportSummary_comul_quot_right
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int
        (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient)
        PreLieDifferenceStableQuotient) :=
  LinearMap.comp
    (LinearMap.rTensor
      PreLieDifferenceStableQuotient (coproductSupportSummary_comul_quot h))
    (coproductSupportSummary_comul_quot h)

noncomputable def coproductSupportSummary_comul_quot_left_assoc
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData) :
    LinearMap (RingHom.id Int) PreLieDifferenceStableQuotient
      (TensorProduct Int PreLieDifferenceStableQuotient
        (TensorProduct Int PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient)) :=
  LinearMap.comp
    (TensorProduct.assoc Int
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient).toLinearMap
    (coproductSupportSummary_comul_quot_right h)

@[simp] theorem coproductSupportSummary_comul_quot_left_apply
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left h a =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (coproductSupportSummary_comul_quot h a) := by
  rfl

@[simp] theorem coproductSupportSummary_comul_quot_right_apply
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_right h a =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (coproductSupportSummary_comul_quot h a) := by
  rfl

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_apply
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left_assoc h a =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        (coproductSupportSummary_comul_quot_right h a) := by
  rfl

theorem CoproductSupportQuotientCoalgebra.coassoc_shorthand_apply
    (H : CoproductSupportQuotientCoalgebra)
    (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left_assoc H.h a =
      coproductSupportSummary_comul_quot_left H.h a := by
  simpa [coproductSupportSummary_comul_quot_left_assoc,
    coproductSupportSummary_comul_quot_left,
    coproductSupportSummary_comul_quot_right,
    LinearMap.comp_apply] using
    (H.coassoc_apply a)

theorem CoproductSupportQuotientCoalgebra.coassoc_shorthand
    (H : CoproductSupportQuotientCoalgebra) :
    coproductSupportSummary_comul_quot_left_assoc H.h =
      coproductSupportSummary_comul_quot_left H.h := by
  apply LinearMap.ext
  intro a
  simpa using H.coassoc_shorthand_apply a

theorem CoproductSupportQuotientCoalgebra.coassoc_shorthand_treeGen
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient (treeGen x)))

-- This is the next reduction target: expand the left-associated comultiplication
-- on a generator in terms of the raw tensor-level comul.
theorem CoproductSupportQuotientCoalgebra.coassoc_left_expansion
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.comp
        (TensorProduct.assoc Int
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot H.h)))
        (coproductSupportSummary_comul_quot H.h
          (mkPreLieDifferenceStableQuotient (treeGen x))) := by
  rfl

theorem CoproductSupportQuotientCoalgebra.coassoc_right_expansion
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot H.h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_comul_linear (treeGen x))) := by
  rfl

@[simp] theorem coproductSupportSummary_comul_quot_left_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_quot_left h (mkPreLieDifferenceStableQuotient a) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_comul_linear a)) := by
  dsimp [coproductSupportSummary_comul_quot_left, LinearMap.comp_apply]
  exact congrArg
    (LinearMap.lTensor
      PreLieDifferenceStableQuotient
      (coproductSupportSummary_comul_quot h))
    (coproductSupportSummary_comul_quot_mk h a)

@[simp] theorem coproductSupportSummary_comul_quot_right_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_quot_right h (mkPreLieDifferenceStableQuotient a) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_comul_linear a)) := by
  dsimp [coproductSupportSummary_comul_quot_right, LinearMap.comp_apply]
  exact congrArg
    (LinearMap.rTensor
      PreLieDifferenceStableQuotient
      (coproductSupportSummary_comul_quot h))
    (coproductSupportSummary_comul_quot_mk h a)

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_mk
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_quot_left_assoc h (mkPreLieDifferenceStableQuotient a) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        (coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient a)) := by
  rfl

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_mk_tensor
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a : linearProofTreeCarrier) :
    coproductSupportSummary_comul_quot_left_assoc h (mkPreLieDifferenceStableQuotient a) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_comul_linear a))) := by
  simpa [coproductSupportSummary_comul_quot_right_mk] using
    (coproductSupportSummary_comul_quot_left_assoc_mk h a)

@[simp] theorem coproductSupportSummary_comul_quot_left_treeGen
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_comul_linear (treeGen x))) := by
  simpa using
    (coproductSupportSummary_comul_quot_left_mk h (treeGen x))

@[simp] theorem coproductSupportSummary_comul_quot_right_treeGen
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_comul_linear (treeGen x))) := by
  simpa using
    (coproductSupportSummary_comul_quot_right_mk h (treeGen x))

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_treeGen
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_comul_linear (treeGen x)))) := by
  simpa using
    (coproductSupportSummary_comul_quot_left_assoc_mk_tensor h (treeGen x))

@[simp] theorem coproductSupportSummary_comul_quot_left_treeGen_sum
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) := by
  simpa [coproductSupportSummary_comul_linear_treeGen] using
    (coproductSupportSummary_comul_quot_left_treeGen h x)

@[simp] theorem coproductSupportSummary_comul_quot_right_treeGen_sum
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) := by
  simpa [coproductSupportSummary_comul_linear_treeGen] using
    (coproductSupportSummary_comul_quot_right_treeGen h x)

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) := by
  simpa [coproductSupportSummary_comul_linear_treeGen] using
    (coproductSupportSummary_comul_quot_left_assoc_treeGen h x)

@[simp] theorem coproductSupportSummary_comul_quot_left_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a b : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left h (a + b) =
      coproductSupportSummary_comul_quot_left h a +
        coproductSupportSummary_comul_quot_left h b := by
  simpa using
    (coproductSupportSummary_comul_quot_left h).map_add a b

@[simp] theorem coproductSupportSummary_comul_quot_left_smul
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (z : Int) (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left h (z • a) =
      z • coproductSupportSummary_comul_quot_left h a := by
  simpa using
    (coproductSupportSummary_comul_quot_left h).map_smul z a

@[simp] theorem coproductSupportSummary_comul_quot_right_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a b : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_right h (a + b) =
      coproductSupportSummary_comul_quot_right h a +
        coproductSupportSummary_comul_quot_right h b := by
  simpa using
    (coproductSupportSummary_comul_quot_right h).map_add a b

@[simp] theorem coproductSupportSummary_comul_quot_right_smul
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (z : Int) (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_right h (z • a) =
      z • coproductSupportSummary_comul_quot_right h a := by
  simpa using
    (coproductSupportSummary_comul_quot_right h).map_smul z a

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (a b : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left_assoc h (a + b) =
      coproductSupportSummary_comul_quot_left_assoc h a +
        coproductSupportSummary_comul_quot_left_assoc h b := by
  simpa using
    (coproductSupportSummary_comul_quot_left_assoc h).map_add a b

@[simp] theorem coproductSupportSummary_comul_quot_left_assoc_smul
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (z : Int) (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left_assoc h (z • a) =
      z • coproductSupportSummary_comul_quot_left_assoc h a := by
  simpa using
    (coproductSupportSummary_comul_quot_left_assoc h).map_smul z a

@[simp] theorem mkPreLieDifferenceStableQuotient_add
    (a b : linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient (a + b) =
      mkPreLieDifferenceStableQuotient a +
        mkPreLieDifferenceStableQuotient b := by
  simpa using (mkPreLieDifferenceStableQuotient.map_add a b)

theorem coproductSupportSummary_comul_quot_left_treeGen_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen y)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient (treeGen x + treeGen y) =
        mkPreLieDifferenceStableQuotient (treeGen x) +
          mkPreLieDifferenceStableQuotient (treeGen y) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add (treeGen x) (treeGen y))
  simpa [hmk] using
    (coproductSupportSummary_comul_quot_left_add h
      (mkPreLieDifferenceStableQuotient (treeGen x))
      (mkPreLieDifferenceStableQuotient (treeGen y)))

theorem coproductSupportSummary_comul_quot_right_treeGen_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen y)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient (treeGen x + treeGen y) =
        mkPreLieDifferenceStableQuotient (treeGen x) +
          mkPreLieDifferenceStableQuotient (treeGen y) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add (treeGen x) (treeGen y))
  simpa [hmk] using
    (coproductSupportSummary_comul_quot_right_add h
      (mkPreLieDifferenceStableQuotient (treeGen x))
      (mkPreLieDifferenceStableQuotient (treeGen y)))

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_add
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x)) +
      coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen y)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient (treeGen x + treeGen y) =
        mkPreLieDifferenceStableQuotient (treeGen x) +
          mkPreLieDifferenceStableQuotient (treeGen y) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add (treeGen x) (treeGen y))
  simpa [hmk] using
    (coproductSupportSummary_comul_quot_left_assoc_add h
      (mkPreLieDifferenceStableQuotient (treeGen x))
      (mkPreLieDifferenceStableQuotient (treeGen y)))

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_two
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) := by
  simpa [coproductSupportSummary_comul_quot_left_treeGen_sum] using
    (coproductSupportSummary_comul_quot_left_treeGen_add h x y)

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_two
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) := by
  simpa [coproductSupportSummary_comul_quot_right_treeGen_sum] using
    (coproductSupportSummary_comul_quot_right_treeGen_add h x y)

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_two
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y
              coproductSupportSummary_tensorGen))) := by
  simpa [coproductSupportSummary_comul_quot_left_assoc_treeGen_sum] using
    (coproductSupportSummary_comul_quot_left_assoc_treeGen_add h x y)

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_three
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have hxy :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            ((treeGen x + treeGen y) + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (coproductSupportSummary_comul_quot_left_treeGen_add h
        (treeGen x + treeGen y) z)
  simpa [add_assoc, coproductSupportSummary_comul_quot_left_treeGen_sum_two,
    coproductSupportSummary_comul_quot_left_treeGen_sum] using hxy

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_three
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have hxy :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            ((treeGen x + treeGen y) + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (coproductSupportSummary_comul_quot_right_treeGen_add h
        (treeGen x + treeGen y) z)
  simpa [add_assoc, coproductSupportSummary_comul_quot_right_treeGen_sum_two,
    coproductSupportSummary_comul_quot_right_treeGen_sum] using hxy

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_three
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z
              coproductSupportSummary_tensorGen))) := by
  have hxyz :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient (treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add (treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [hxyz,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_two,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_four
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have h1 :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            ((treeGen w + treeGen x) + (treeGen y + treeGen z))) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) := by
    simpa using
      (coproductSupportSummary_comul_quot_left_treeGen_add h
        (treeGen w + treeGen x) (treeGen y + treeGen z))
  simpa [add_assoc, coproductSupportSummary_comul_quot_left_treeGen_sum_two,
    add_left_comm, add_comm] using h1

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_four
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have h1 :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            ((treeGen w + treeGen x) + (treeGen y + treeGen z))) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen y + treeGen z)) := by
    simpa using
      (coproductSupportSummary_comul_quot_right_treeGen_add h
        (treeGen w + treeGen x) (treeGen y + treeGen z))
  simpa [add_assoc, coproductSupportSummary_comul_quot_right_treeGen_sum_two,
    add_left_comm, add_comm] using h1

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_four
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z
              coproductSupportSummary_tensorGen))) := by
  have hwxyz :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient (treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [hwxyz,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_three,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_five
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum v
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have hvwxyz :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hvwxyz
    _ = _ := by
      simp [coproductSupportSummary_comul_quot_left_treeGen_sum_four,
        coproductSupportSummary_comul_quot_left_treeGen_sum,
        add_assoc, add_left_comm, add_comm]

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_five
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (v w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum v
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have hvwxyz :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_right_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hvwxyz
    _ = _ := by
      simp [coproductSupportSummary_comul_quot_right_treeGen_sum_four,
        coproductSupportSummary_comul_quot_right_treeGen_sum,
        add_assoc, add_left_comm, add_comm]

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_five
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z
              coproductSupportSummary_tensorGen))) := by
  have hvwxyz :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [hvwxyz,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_four,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_six
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum u
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum v
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have huvwyz :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using huvwyz
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_left_treeGen_sum_five,
        coproductSupportSummary_comul_quot_left_treeGen_sum]
      -- goal closed by rewriting

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_six
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum u
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum v
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum w
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum y
            coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum z
            coproductSupportSummary_tensorGen)) := by
  have huvwyz :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_right_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using huvwyz
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_right_treeGen_sum_five,
        coproductSupportSummary_comul_quot_right_treeGen_sum]
      -- goal closed by rewriting

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_six
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y
              coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc Int
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z
              coproductSupportSummary_tensorGen))) := by
  have huvwyz :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [huvwyz,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_five,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_explicit
    (H : CoproductSupportQuotientCoalgebra) (x : PTree) :
    (TensorProduct.assoc Int
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient).toLinearMap
      ((LinearMap.rTensor
        PreLieDifferenceStableQuotient
        (coproductSupportSummary_comul_quot H.h))
        (mkPreLieDifferenceStableQuotient_tensor
          (coproductSupportSummary_sum x
            coproductSupportSummary_tensorGen))) =
    (LinearMap.lTensor
      PreLieDifferenceStableQuotient
      (coproductSupportSummary_comul_quot H.h))
      (mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_sum x
          coproductSupportSummary_tensorGen)) := by
  simpa [coproductSupportSummary_comul_quot_left_assoc_treeGen_sum,
    coproductSupportSummary_comul_quot_left_treeGen_sum] using
    (H.coassoc_shorthand_treeGen x)

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_two_explicit
    (H : CoproductSupportQuotientCoalgebra) (x y : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)))

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_three_explicit
    (H : CoproductSupportQuotientCoalgebra) (x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)))

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_four_explicit
    (H : CoproductSupportQuotientCoalgebra) (w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen w + treeGen x + treeGen y + treeGen z)))

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_five_explicit
    (H : CoproductSupportQuotientCoalgebra) (v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)))

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_six_explicit
    (H : CoproductSupportQuotientCoalgebra) (u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)))



end CoproductSupportTensor

end CoproductSupport
end QuotientConnected
