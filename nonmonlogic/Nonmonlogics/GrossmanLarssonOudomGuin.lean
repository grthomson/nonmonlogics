import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
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

end QuotientConnected
