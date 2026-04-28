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
import Nonmonlogics.GrossmanLarssonOudomGuin
import Nonmonlogics.GrossmanLarssonOudomGuinComputable

/-!
# Coalgebra descent for the Oudom–Guin / Grossman–Larsson construction

This file proves that `coproductSupportSummary_coalgebraData` respects the
stable quotient, giving a genuine descended coalgebra on
`PreLieDifferenceStableQuotient`, and then works toward the bialgebra and
Hopf algebra structure.

## Main steps

1. The counit linear map is identically zero (trivial — both branches of the
   defining `if` return `0`).
2. The kernel of `comul_linear` belongs to `preLieDifferenceStableSubmoduleFamily`.
   This requires two sub-results:
   * `comul_linear` kills every pre-Lie difference generator (the deep
     combinatorial identity — marked `sorry` pending proof).
   * The kernel is stable under grafting by tree generators (requires a
     coaction formula — also `sorry` for now).
3. From (2) we derive `CoproductSupportCoalgebraRespectsStableQuotient`.
4. We then instantiate the descended coalgebra maps and prove the
   coassociativity axiom using the concrete `_sum_N` expansion lemmas.
-/

namespace QuotientConnected.CoproductSupport

open Syntax

/-! ## 0. Oudom-Guin primitive generator interface -/

section OudomGuinPrimitiveGenerators

/-!
The Grossman-Larsson/pre-Lie route should feed the Oudom-Guin construction
through primitive generators in the UEA.  The CK-style cut support remains a
useful combinatorial comparison object, but this is the proof-theoretically
meaningful coalgebra datum for the quotient-first construction.
-/

/-- The primitive generator-level comultiplication/counit data for the stable UEA. -/
noncomputable def stableUEA_OGPrimitiveGeneratorComulData :
    StableUEAGeneratorComulData where
  comulGen := fun x =>
    TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
      TensorProduct.tmul Int 1 (stableUEA_treeGen x)
  counitGen := fun _ => 0
  comulGen_eq := by
    intro x
    rfl
  counitGen_eq := by
    intro x
    rfl

@[simp] theorem stableUEA_OGPrimitiveGeneratorComulData_comulGen
    (x : PTree) :
    stableUEA_OGPrimitiveGeneratorComulData.comulGen x =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  rfl

@[simp] theorem stableUEA_OGPrimitiveGeneratorComulData_counitGen
    (x : PTree) :
    stableUEA_OGPrimitiveGeneratorComulData.counitGen x = 0 := by
  rfl

@[simp] theorem stableUEA_OGPrimitive_comul_linear_treeGen
    (x : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  rw [stableUEA_comul_linear_treeGen]
  rfl

@[simp] theorem stableUEA_OGPrimitive_counit_linear_treeGen
    (x : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x) = 0 := by
  rw [stableUEA_counit_linear_treeGen]
  rfl

/--
The primitive UEA comultiplication already factors through the stable quotient.

This is the quotient-level linear map
`q ↦ ι(q) ⊗ 1 + 1 ⊗ ι(q)`.  Proving the raw generator-linear map factors
through this map is what makes the primitive OG coalgebra live on the correct
quotient carrier rather than on arbitrary raw proof-tree combinations.
-/
noncomputable def stableUEA_OGPrimitiveComulFromStableQuotient :
    PreLieDifferenceStableQuotient →ₗ[ℤ] stableUEATensor where
  toFun := fun q =>
    TensorProduct.tmul ℤ (preLieDifferenceStableQuotientUEA_ι_linear q) 1 +
      TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientUEA_ι_linear q)
  map_add' := by
    intro q r
    simp [LinearMap.map_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
      add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro z q
    simp only [LinearMap.map_smul, RingHom.id_apply]
    let v := preLieDifferenceStableQuotientUEA_ι_linear q
    change
      (z • v) ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA) +
          (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] (z • v) =
        z •
          (v ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA) +
            (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v)
    have hleft :
        (z • v) ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA) =
          z • (v ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA)) := by
      exact (TensorProduct.smul_tmul' (R := ℤ) z v
        (1 : preLieDifferenceStableQuotientUEA)).symm
    have hright :
        (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] (z • v) =
          z • ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v) := by
      calc
        (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] (z • v)
            = (z • (1 : preLieDifferenceStableQuotientUEA)) ⊗ₜ[ℤ] v := by
              rw [TensorProduct.tmul_smul]
              exact (TensorProduct.smul_tmul' (R := ℤ) z
                (1 : preLieDifferenceStableQuotientUEA) v)
        _ = z • ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v) := by
              exact (TensorProduct.smul_tmul' (R := ℤ) z
                (1 : preLieDifferenceStableQuotientUEA) v).symm
    calc
      (z • v) ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA) +
          (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] (z • v) =
        z • (v ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA)) +
          z • ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v) := by
          rw [hleft, hright]
      _ =
        z •
          (v ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA) +
            (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v) := by
          exact (smul_add z
            (v ⊗ₜ[ℤ] (1 : preLieDifferenceStableQuotientUEA))
            ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] v)).symm

@[simp] theorem stableUEA_OGPrimitiveComulFromStableQuotient_mk_treeGen
    (x : PTree) :
    stableUEA_OGPrimitiveComulFromStableQuotient
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  rw [stableUEA_treeGen_eq_ι]
  rfl

/--
The raw primitive generator-linear comultiplication is exactly the quotient
primitive comultiplication after applying the stable quotient map.
-/
theorem stableUEA_OGPrimitive_comul_linear_factor
    (a : linearProofTreeCarrier) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      stableUEA_OGPrimitiveComulFromStableQuotient
        (mkPreLieDifferenceStableQuotient a) := by
  classical
  refine Finsupp.induction_linear a ?_ ?_ ?_
  · simp [stableUEA_OGPrimitiveComulFromStableQuotient]
  · intro a b ha hb
    calc
      stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (a + b) =
          stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a +
            stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData b := by
            simp
      _ =
          stableUEA_OGPrimitiveComulFromStableQuotient
              (mkPreLieDifferenceStableQuotient a) +
            stableUEA_OGPrimitiveComulFromStableQuotient
              (mkPreLieDifferenceStableQuotient b) := by
            rw [ha, hb]
      _ =
          stableUEA_OGPrimitiveComulFromStableQuotient
            (mkPreLieDifferenceStableQuotient (a + b)) := by
            simp
  · intro x n
    have htree :
        stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
            (treeGen x) =
          stableUEA_OGPrimitiveComulFromStableQuotient
            (mkPreLieDifferenceStableQuotient (treeGen x)) := by
      simp
    have hn :
        stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
            (n • treeGen x) =
          stableUEA_OGPrimitiveComulFromStableQuotient
            (mkPreLieDifferenceStableQuotient (n • treeGen x)) := by
      calc
        stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
            (n • treeGen x) =
          n • stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
            (treeGen x) := by
            simp
        _ =
          n • stableUEA_OGPrimitiveComulFromStableQuotient
            (mkPreLieDifferenceStableQuotient (treeGen x)) := by
            rw [htree]
        _ =
          stableUEA_OGPrimitiveComulFromStableQuotient
            (mkPreLieDifferenceStableQuotient (n • treeGen x)) := by
            simp
    simpa [treeGen] using hn

theorem stableUEA_OGPrimitive_counit_linear_eq_zero :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData = 0 := by
  apply LinearMap.ext
  intro a
  rw [stableUEA_counit_linear_apply, LinearMap.zero_apply]
  simp [stableUEA_OGPrimitiveGeneratorComulData]

/--
The actual quotient descent obligation for the Oudom-Guin primitive coalgebra.
This is intentionally named as the gate: proving this is the next substantive
well-definedness result, and it keeps us from pretending the raw CK product is
the main Hopf-algebraic structure.
-/
def stableUEA_OGPrimitiveRespectsStableQuotient : Prop :=
  StableUEAGeneratorComulRespectsStableQuotient
    stableUEA_OGPrimitiveGeneratorComulData

theorem stableUEA_OGPrimitiveRespectsStableQuotient_iff :
    stableUEA_OGPrimitiveRespectsStableQuotient ↔
      StableUEAGeneratorComulRespectsStableQuotient
        stableUEA_OGPrimitiveGeneratorComulData := by
  rfl

/--
The primitive Oudom-Guin comultiplication respects the stable quotient.

The proof is structural rather than combinatorial: the primitive formula factors
through `mkPreLieDifferenceStableQuotient`, so every element of the stable
submodule maps to zero.  This is exactly why the UEA carrier is the right
coalgebra carrier.
-/
theorem stableUEA_OGPrimitiveRespectsStableQuotient_proof :
    stableUEA_OGPrimitiveRespectsStableQuotient := by
  intro a ha
  constructor
  · rw [stableUEA_OGPrimitive_comul_linear_factor]
    have hq : mkPreLieDifferenceStableQuotient a = 0 := by
      change
        (Submodule.Quotient.mk a :
          linearProofTreeCarrier ⧸ preLieDifferenceStableSubmodule) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (p := preLieDifferenceStableSubmodule)).2 ha
    rw [hq]
    simp [stableUEA_OGPrimitiveComulFromStableQuotient]
  · have hzero :=
      congrFun
        (congrArg DFunLike.coe stableUEA_OGPrimitive_counit_linear_eq_zero) a
    simpa using hzero

/-- The descended primitive comultiplication, conditional on the quotient gate. -/
noncomputable def stableUEA_OGPrimitiveComultiplication
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) :
    StableQuotientComultiplication :=
  stableUEA_comultiplication_descend
    stableUEA_OGPrimitiveGeneratorComulData h

/-- The packaged descended primitive comultiplication, conditional on the quotient gate. -/
noncomputable def stableUEA_OGPrimitiveComultiplicationPack
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) :
    StableQuotientComultiplicationPack :=
  stableUEA_comultiplication_descend_pack
    stableUEA_OGPrimitiveGeneratorComulData h

/-- The descended primitive comultiplication using the proved quotient gate. -/
noncomputable def stableUEA_OGPrimitiveComultiplicationCanonical :
    StableQuotientComultiplication :=
  stableUEA_OGPrimitiveComultiplication
    stableUEA_OGPrimitiveRespectsStableQuotient_proof

/-- The packaged descended primitive comultiplication using the proved quotient gate. -/
noncomputable def stableUEA_OGPrimitiveComultiplicationPackCanonical :
    StableQuotientComultiplicationPack :=
  stableUEA_OGPrimitiveComultiplicationPack
    stableUEA_OGPrimitiveRespectsStableQuotient_proof

@[simp] theorem stableUEA_OGPrimitiveComultiplication_comul_treeGen
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) (x : PTree) :
    (stableUEA_OGPrimitiveComultiplication h).comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  simpa [stableUEA_OGPrimitiveComultiplication,
    stableUEA_OGPrimitiveGeneratorComulData] using
    (stableUEA_comultiplication_descend_comul_on_generators
      stableUEA_OGPrimitiveGeneratorComulData h x)

@[simp] theorem stableUEA_OGPrimitiveComultiplication_counit_treeGen
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) (x : PTree) :
    (stableUEA_OGPrimitiveComultiplication h).counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simpa [stableUEA_OGPrimitiveComultiplication,
    stableUEA_OGPrimitiveGeneratorComulData] using
    (stableUEA_comultiplication_descend_counit_on_generators
      stableUEA_OGPrimitiveGeneratorComulData h x)

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_treeGen
    (x : PTree) :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_comul_treeGen
      stableUEA_OGPrimitiveRespectsStableQuotient_proof x

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_treeGen
    (x : PTree) :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_counit_treeGen
      stableUEA_OGPrimitiveRespectsStableQuotient_proof x

@[simp] theorem stableUEA_OGPrimitiveComultiplication_comul_mk
    (h : stableUEA_OGPrimitiveRespectsStableQuotient)
    (a : linearProofTreeCarrier) :
    (stableUEA_OGPrimitiveComultiplication h).comul
        (mkPreLieDifferenceStableQuotient a) =
      stableUEA_OGPrimitiveComulFromStableQuotient
        (mkPreLieDifferenceStableQuotient a) := by
  simp [stableUEA_OGPrimitiveComultiplication,
    stableUEA_comultiplication_descend,
    stableUEA_OGPrimitive_comul_linear_factor]

@[simp] theorem stableUEA_OGPrimitiveComultiplication_counit_mk
    (h : stableUEA_OGPrimitiveRespectsStableQuotient)
    (a : linearProofTreeCarrier) :
    (stableUEA_OGPrimitiveComultiplication h).counit
        (mkPreLieDifferenceStableQuotient a) = 0 := by
  simp [stableUEA_OGPrimitiveComultiplication,
    stableUEA_comultiplication_descend,
    stableUEA_OGPrimitive_counit_linear_eq_zero]

theorem stableUEA_OGPrimitiveComultiplication_comul_eq_fromStableQuotient
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) :
    (stableUEA_OGPrimitiveComultiplication h).comul =
      stableUEA_OGPrimitiveComulFromStableQuotient := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H a =>
      exact stableUEA_OGPrimitiveComultiplication_comul_mk h a

theorem stableUEA_OGPrimitiveComultiplication_counit_eq_zero
    (h : stableUEA_OGPrimitiveRespectsStableQuotient) :
    (stableUEA_OGPrimitiveComultiplication h).counit = 0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H a =>
      exact stableUEA_OGPrimitiveComultiplication_counit_mk h a

theorem stableUEA_OGPrimitiveComultiplication_comul_apply
    (h : stableUEA_OGPrimitiveRespectsStableQuotient)
    (q : PreLieDifferenceStableQuotient) :
    (stableUEA_OGPrimitiveComultiplication h).comul q =
      TensorProduct.tmul ℤ
          (preLieDifferenceStableQuotientUEA_ι_linear q) 1 +
        TensorProduct.tmul ℤ 1
          (preLieDifferenceStableQuotientUEA_ι_linear q) := by
  rw [stableUEA_OGPrimitiveComultiplication_comul_eq_fromStableQuotient h]
  rfl

@[simp] theorem stableUEA_OGPrimitiveComultiplication_counit_apply
    (h : stableUEA_OGPrimitiveRespectsStableQuotient)
    (q : PreLieDifferenceStableQuotient) :
    (stableUEA_OGPrimitiveComultiplication h).counit q = 0 := by
  rw [stableUEA_OGPrimitiveComultiplication_counit_eq_zero h]
  rfl

theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_eq_fromStableQuotient :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul =
      stableUEA_OGPrimitiveComulFromStableQuotient := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_comul_eq_fromStableQuotient
      stableUEA_OGPrimitiveRespectsStableQuotient_proof

theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_eq_zero :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit = 0 := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_counit_eq_zero
      stableUEA_OGPrimitiveRespectsStableQuotient_proof

theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_apply
    (q : PreLieDifferenceStableQuotient) :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul q =
      TensorProduct.tmul ℤ
          (preLieDifferenceStableQuotientUEA_ι_linear q) 1 +
        TensorProduct.tmul ℤ 1
          (preLieDifferenceStableQuotientUEA_ι_linear q) := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_comul_apply
      stableUEA_OGPrimitiveRespectsStableQuotient_proof q

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_apply
    (q : PreLieDifferenceStableQuotient) :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit q = 0 := by
  simpa [stableUEA_OGPrimitiveComultiplicationCanonical] using
    stableUEA_OGPrimitiveComultiplication_counit_apply
      stableUEA_OGPrimitiveRespectsStableQuotient_proof q

end OudomGuinPrimitiveGenerators

/-! ## 1. The counit is the zero map -/

section CounitZero

/-- The counit function `fun p => if p.1 = [] then 0 else 0` is identically zero. -/
@[simp] theorem counit_support_fn_eq_zero (p : Forest × PTree) :
    (fun q : Forest × PTree => if q.1 = [] then (0 : ℤ) else 0) p = 0 := by
  by_cases h : p.1 = []
  · simp [h]
  · simp [h]

/--
The support-level counit linear map is identically zero.

Both branches of the defining `if` return `0`, so the function is
`fun _ => 0`, and its linear extension is the zero map.
-/
theorem coproductSupportSummary_counit_linear_eq_zero :
    coproductSupportSummary_counit_linear = 0 := by
  apply LinearMap.ext
  intro a
  rw [coproductSupportSummary_counit_linear_apply, LinearMap.zero_apply]
  simp [Finsupp.sum, coproductSupportSummary_sum]

end CounitZero

/-! ## 2. The comultiplication kills the stable submodule -/

section ComulKillsStable

/-!
### 2a. Key combinatorial lemma: comul kills each pre-Lie difference generator

This is the central theorem of the GL/OG construction: the GL coproduct (sum
over admissible cuts) vanishes on the pre-Lie associator difference

  `preLieDifferenceGenerators x y z
     = assoc[graftPreLie] (treeGen y) (treeGen x) (treeGen z)
       - assoc[graftPreLie] (treeGen x) (treeGen y) (treeGen z)`.

Concretely, this requires showing that the multisets of admissible-cut
(forest, remainder) pairs produced by the `A + D` side and by the `B + C` side
coincide.  The proof is a combinatorial bijection on addresses and is the
mathematical heart of the paper; it is `sorry`'d here pending a formal
address-level proof.
-/

/--
The GL coproduct kills every pre-Lie difference generator.
(Pending proof of the underlying combinatorial bijection on addresses.)
-/
def CoproductSupportNodeCutDecompositionClaim : Prop :=
  ∀ (r : RuleTag) (s : MultiSequent) (cs : List PTree)
      (cut : List Address),
    cut ∈ PTree.allAdmissibleCuts (PTree.node r s cs) →
      ([] ∈ cut) ∨
        ([] ∉ cut ∧
          ∀ i (hi : i < cs.length),
            PTree.restrictCut cut i ∈ PTree.allAdmissibleCuts cs[i])

/--
The validity component of node-cut decomposition.

If `cut` is an admissible cut of a node and an address survives restriction to
child `i`, then that restricted address is valid in child `i`.  This is the
first formal part of the full admissible-cut decomposition; the remaining
pieces are preservation of the `sublists` order witness and the antichain
condition under `restrictCut`.
-/
def CoproductSupportNodeCutValidityDecompositionClaim : Prop :=
  ∀ (r : RuleTag) (s : MultiSequent) (cs : List PTree)
      (cut : List Address),
    cut ∈ PTree.allAdmissibleCuts (PTree.node r s cs) →
      ∀ i (hi : i < cs.length) addr,
        addr ∈ PTree.restrictCut cut i →
          PTree.ValidAddress cs[i] addr

/-- The validity component of node-cut decomposition is already provable. -/
theorem CoproductSupportNodeCutValidityDecompositionClaim.proof :
    CoproductSupportNodeCutValidityDecompositionClaim := by
  intro r s cs cut hcut i hi addr haddr
  unfold PTree.allAdmissibleCuts at hcut
  rcases List.mem_filter.mp hcut with ⟨_hsub, hbool⟩
  have hall :
      cut.all (fun a => PTree.validAddress (PTree.node r s cs) a) = true :=
    by
      cases hvalid :
          cut.all (fun a => PTree.validAddress (PTree.node r s cs) a) <;>
        simp [hvalid] at hbool
      rfl
  have hparentMem : i :: addr ∈ cut := by
    simpa using
      (PTree.mem_restrictCut_iff (cut := cut) (i := i) (addr := addr)).mp haddr
  have hparentValid :
      PTree.validAddress (PTree.node r s cs) (i :: addr) = true :=
    List.all_eq_true.mp hall (i :: addr) hparentMem
  unfold PTree.ValidAddress PTree.validAddress at hparentValid ⊢
  simpa [PTree.subtreeAt, hi] using hparentValid

/--
Prop-level node-cut decomposition.

This is the induction-ready form of the admissible-cut step.  Unlike the
finite boolean enumeration in `allAdmissibleCuts`, it directly states the
mathematical invariant used in the height induction: an admissible cut of a
rule node restricts to admissible cuts of each premise subtree.
-/
def CoproductSupportNodeCutPropDecompositionClaim : Type :=
  ∀ (r : RuleTag) (s : MultiSequent) (cs : List PTree)
      (cut : PTree.IsAdmissibleCut (PTree.node r s cs)),
    ∀ i (hi : i < cs.length),
      PTree.IsAdmissibleCut cs[i]

/-- The Prop-level node decomposition follows from address-prefix preservation. -/
def CoproductSupportNodeCutPropDecompositionClaim.proof :
    CoproductSupportNodeCutPropDecompositionClaim := by
  intro r s cs cut i hi
  exact PTree.isAdmissibleCut_restrictCut cut i hi

/--
Derivation-level cut decomposition target.

This is the proof-theoretic version of the node decomposition claim: for an
actual `NMMS` derivation tree, either the admissible cut removes the root, or it
restricts to admissible cuts of the immediate premise subderivations.  The
children are therefore not arbitrary examples: their number and labels come
from the inference rule constructor used at the root.
-/
def NMMSDerivationCutDecompositionClaim (base : BaseRel) : Prop :=
  ∀ (s : MultiSequent) (d : NMMS base s) (cut : List Address),
    cut ∈ PTree.allAdmissibleCuts (NMMS.toTree d) →
      IsBaseAdmissible base (NMMS.toTree d) cut →
        ([] ∈ cut) ∨
          ([] ∉ cut ∧
            ∀ i (hi : i < (NMMS.toTree d).children.length),
              PTree.restrictCut cut i ∈
                PTree.allAdmissibleCuts ((NMMS.toTree d).children[i]))

/--
The generic node decomposition claim specializes to derivation trees.  The leaf
case is vacuous; each non-leaf case is one of the labelled `NMMS` rule
constructors, with the corresponding child list.
-/
theorem NMMSDerivationCutDecompositionClaim.of_node_claim
    {base : BaseRel}
    (hnode : CoproductSupportNodeCutDecompositionClaim) :
    NMMSDerivationCutDecompositionClaim base := by
  intro s d cut hcut _hbase
  cases htree : NMMS.toTree d with
  | leaf s0 =>
      by_cases hroot : [] ∈ cut
      · exact Or.inl hroot
      · refine Or.inr ⟨hroot, ?_⟩
        intro i hi
        simp [PTree.children] at hi
  | node r s0 cs =>
      simpa [htree, PTree.children] using
        hnode r s0 cs cut (by simpa [htree] using hcut)

/--
For derivation trees whose admissible cuts are base-compatible, every term in
the GL coproduct is again proof-theoretic: the trunk is a derivation tree and
each branch in the forest is a derivation tree.
-/
def NMMSCoproductTermsDerivable (base : BaseRel) : Prop :=
  ∀ (s : MultiSequent) (d : NMMS base s),
    (∀ cut, IsBaseAdmissible base (NMMS.toTree d) cut) →
      ∀ (f : Forest) (r : PTree),
        (f, r) ∈ PTree.coproductData (NMMS.toTree d) →
          DerivableForest base f ∧ DerivableTree base r

/-- Existing subtree/remainder lemmas prove the coproduct terms are derivable. -/
theorem NMMSCoproductTermsDerivable.proof {base : BaseRel} :
    NMMSCoproductTermsDerivable base := by
  intro s d hbase f r hmem
  have h := coproduct_terms_are_subderivations d hbase f r hmem
  constructor
  · intro t ht
    rcases h.2 t ht with ⟨s'', d'', ht'⟩
    rw [ht']
    exact derivableTree_of_derivation d''
  · rcases h.1 with ⟨s', d', hr⟩
    rw [hr]
    exact derivableTree_of_derivation d'

/--
Height-bounded form of the main GL/pre-Lie compatibility theorem.

The induction parameter is the total height of the three trees in the
pre-Lie associator difference.  This is the theorem shape we want to prove
by decomposing admissible cuts of a node into cuts of its child subtrees.
-/
def CoproductKillsPreLieDifferenceHeightClaim (n : Nat) : Prop :=
  ∀ x y z : PTree,
    PTree.height x + PTree.height y + PTree.height z ≤ n →
      coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators x y z) = 0

/--
Rule-arity-respecting version of the same height-bounded target.

This is the proof-theoretically honest induction domain: every node's child
list has the arity dictated by its rule tag.  Arbitrary `PTree.node r s cs`
values remain useful as combinatorial test data, but actual `NMMS` proof trees
land in this class.
-/
def CoproductKillsPreLieDifferenceRuleArityHeightClaim (n : Nat) : Prop :=
  ∀ x y z : PTree,
    PTree.RespectsRuleArity x →
      PTree.RespectsRuleArity y →
        PTree.RespectsRuleArity z →
          PTree.height x + PTree.height y + PTree.height z ≤ n →
            coproductSupportSummary_comul_linear
              (preLieDifferenceGenerators x y z) = 0

/--
Derivable-tree specialization of the height-bounded target.  This is the
version closest to proof theory: the arity invariant is inherited from
`NMMS.toTree`.
-/
def CoproductKillsPreLieDifferenceDerivableHeightClaim
    (base : BaseRel) (n : Nat) : Prop :=
  ∀ x y z : PTree,
    DerivableTree base x →
      DerivableTree base y →
        DerivableTree base z →
          PTree.height x + PTree.height y + PTree.height z ≤ n →
            coproductSupportSummary_comul_linear
              (preLieDifferenceGenerators x y z) = 0

/-- Every proof tree has positive height. -/
theorem pTree_height_pos (t : PTree) : 0 < PTree.height t := by
  cases t with
  | leaf _ =>
      simp [PTree.height]
  | node _ _ cs =>
      cases cs with
      | nil =>
          simp [PTree.height]
      | cons _ _ =>
          simp [PTree.height]

/-- Every proof tree has height at least one. -/
theorem pTree_one_le_height (t : PTree) : 1 ≤ PTree.height t :=
  Nat.succ_le_of_lt (pTree_height_pos t)

/-- The total height of any triple of proof trees is at least three. -/
theorem pTree_total_height_ge_three (x y z : PTree) :
    3 ≤ PTree.height x + PTree.height y + PTree.height z := by
  have hx : 1 ≤ PTree.height x := pTree_one_le_height x
  have hy : 1 ≤ PTree.height y := pTree_one_le_height y
  have hz : 1 ≤ PTree.height z := pTree_one_le_height z
  omega

/-- The total height of any triple of derivation trees is at least three. -/
theorem NMMS_toTree_total_height_ge_three
    {base : BaseRel} {sx sy sz : MultiSequent}
    (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz) :
    3 ≤
      PTree.height (NMMS.toTree dx) +
        PTree.height (NMMS.toTree dy) +
          PTree.height (NMMS.toTree dz) := by
  exact pTree_total_height_ge_three
    (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)

/--
The total height of three proof trees is never below three, so the bounded
coproduct/pre-Lie compatibility claim is vacuous for `n < 3`.
-/
theorem CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three
    {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceHeightClaim n := by
  intro x y z hheight
  have hx : 1 ≤ PTree.height x := pTree_one_le_height x
  have hy : 1 ≤ PTree.height y := pTree_one_le_height y
  have hz : 1 ≤ PTree.height z := pTree_one_le_height z
  exfalso
  omega

/-- Rule-arity version of the vacuous small-height claim. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.vacuous_of_lt_three
    {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceRuleArityHeightClaim n := by
  intro x y z _hx _hy _hz hheight
  exact
    CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three hn
      x y z hheight

/-- Derivable-tree version of the vacuous small-height claim. -/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.vacuous_of_lt_three
    {base : BaseRel} {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceDerivableHeightClaim base n := by
  intro x y z _hx _hy _hz hheight
  exact
    CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three hn
      x y z hheight

/-- Height-zero specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceHeightClaim.zero :
    CoproductKillsPreLieDifferenceHeightClaim 0 :=
  CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three (by norm_num)

/-- Height-one specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceHeightClaim.one :
    CoproductKillsPreLieDifferenceHeightClaim 1 :=
  CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three (by norm_num)

/-- Height-two specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceHeightClaim.two :
    CoproductKillsPreLieDifferenceHeightClaim 2 :=
  CoproductKillsPreLieDifferenceHeightClaim.vacuous_of_lt_three (by norm_num)

/-- Rule-arity height-zero specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.zero :
    CoproductKillsPreLieDifferenceRuleArityHeightClaim 0 :=
  CoproductKillsPreLieDifferenceRuleArityHeightClaim.vacuous_of_lt_three
    (by norm_num)

/-- Rule-arity height-one specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.one :
    CoproductKillsPreLieDifferenceRuleArityHeightClaim 1 :=
  CoproductKillsPreLieDifferenceRuleArityHeightClaim.vacuous_of_lt_three
    (by norm_num)

/-- Rule-arity height-two specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.two :
    CoproductKillsPreLieDifferenceRuleArityHeightClaim 2 :=
  CoproductKillsPreLieDifferenceRuleArityHeightClaim.vacuous_of_lt_three
    (by norm_num)

/-- Derivable-tree height-zero specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.zero
    {base : BaseRel} :
    CoproductKillsPreLieDifferenceDerivableHeightClaim base 0 :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.vacuous_of_lt_three
    (by norm_num)

/-- Derivable-tree height-one specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.one
    {base : BaseRel} :
    CoproductKillsPreLieDifferenceDerivableHeightClaim base 1 :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.vacuous_of_lt_three
    (by norm_num)

/-- Derivable-tree height-two specialization of the vacuous bound. -/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.two
    {base : BaseRel} :
    CoproductKillsPreLieDifferenceDerivableHeightClaim base 2 :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.vacuous_of_lt_three
    (by norm_num)

/--
The unrestricted height statement immediately implies the rule-arity
specialization.  Keeping this as a theorem lets us later reverse the dependency
if the actual proof is carried out on rule-correct proof trees first.
-/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_unrestricted
    (n : Nat)
    (h : CoproductKillsPreLieDifferenceHeightClaim n) :
    CoproductKillsPreLieDifferenceRuleArityHeightClaim n := by
  intro x y z _hx _hy _hz hheight
  exact h x y z hheight

/--
Derivable proof trees are rule-arity-respecting, so any arity-aware height
claim applies to trees produced by the sequent calculus.
-/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.to_derivable
    {base : BaseRel} {n : Nat}
    (h : CoproductKillsPreLieDifferenceRuleArityHeightClaim n) :
    CoproductKillsPreLieDifferenceDerivableHeightClaim base n := by
  intro x y z hx hy hz hheight
  exact h x y z
    (derivableTree_respectsRuleArity hx)
    (derivableTree_respectsRuleArity hy)
    (derivableTree_respectsRuleArity hz)
    hheight

/-- Apply an arity-aware height claim directly to three `NMMS` derivations. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.apply_toTree
    {base : BaseRel} {n : Nat}
    (h : CoproductKillsPreLieDifferenceRuleArityHeightClaim n)
    {sx sy sz : MultiSequent}
    (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz)
    (hheight :
      PTree.height (NMMS.toTree dx) +
          PTree.height (NMMS.toTree dy) +
            PTree.height (NMMS.toTree dz) ≤ n) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators
          (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0 := by
  exact h (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)
    (toTree_respectsRuleArity dx)
    (toTree_respectsRuleArity dy)
    (toTree_respectsRuleArity dz)
    hheight

/-- Apply a derivable-tree height claim directly to three `NMMS` derivations. -/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.apply_toTree
    {base : BaseRel} {n : Nat}
    (h : CoproductKillsPreLieDifferenceDerivableHeightClaim base n)
    {sx sy sz : MultiSequent}
    (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz)
    (hheight :
      PTree.height (NMMS.toTree dx) +
          PTree.height (NMMS.toTree dy) +
            PTree.height (NMMS.toTree dz) ≤ n) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators
          (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0 := by
  exact h (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)
    (derivableTree_of_derivation dx)
    (derivableTree_of_derivation dy)
    (derivableTree_of_derivation dz)
    hheight

/--
The intended strong-induction step for the main coproduct compatibility proof.

For a fixed total height `n`, every smaller triple is assumed already known.
The node case should use `CoproductSupportNodeCutDecompositionClaim` to
rewrite cuts of a parent tree as root/empty cuts plus cuts of child subtrees.
-/
def CoproductKillsPreLieDifferenceHeightStep (n : Nat) : Prop :=
  (∀ x y z : PTree,
      PTree.height x + PTree.height y + PTree.height z < n →
        coproductSupportSummary_comul_linear
          (preLieDifferenceGenerators x y z) = 0) →
    ∀ x y z : PTree,
      PTree.height x + PTree.height y + PTree.height z = n →
        coproductSupportSummary_comul_linear
          (preLieDifferenceGenerators x y z) = 0

/--
Strong-induction step restricted to rule-correct proof trees.  This is the
step we ultimately want to discharge from the cut decomposition plus the
rule-specific child arities.
-/
def CoproductKillsPreLieDifferenceRuleArityHeightStep (n : Nat) : Prop :=
  (∀ x y z : PTree,
      PTree.RespectsRuleArity x →
        PTree.RespectsRuleArity y →
          PTree.RespectsRuleArity z →
            PTree.height x + PTree.height y + PTree.height z < n →
              coproductSupportSummary_comul_linear
                (preLieDifferenceGenerators x y z) = 0) →
    ∀ x y z : PTree,
      PTree.RespectsRuleArity x →
        PTree.RespectsRuleArity y →
          PTree.RespectsRuleArity z →
            PTree.height x + PTree.height y + PTree.height z = n →
              coproductSupportSummary_comul_linear
                (preLieDifferenceGenerators x y z) = 0

/--
Strong-induction step over actual `NMMS` derivations.

This is stricter than the rule-arity tree step: the immediate subtrees are not
merely arity-correct, but are the premise derivations of a labelled inference
rule.  Its height measure is `NMMS.derivationHeight`, proved equal to
`PTree.height (NMMS.toTree d)` in `GrossmanLarsson.lean`.
-/
def CoproductKillsPreLieDifferenceNMMSHeightStep
    (base : BaseRel) (n : Nat) : Prop :=
  (∀ (sx sy sz : MultiSequent)
      (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz),
      NMMS.derivationHeight dx +
          NMMS.derivationHeight dy +
            NMMS.derivationHeight dz < n →
        coproductSupportSummary_comul_linear
          (preLieDifferenceGenerators
            (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0) →
    ∀ (sx sy sz : MultiSequent)
      (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz),
      NMMS.derivationHeight dx +
          NMMS.derivationHeight dy +
            NMMS.derivationHeight dz = n →
        coproductSupportSummary_comul_linear
          (preLieDifferenceGenerators
            (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0

/--
For total heights below three, the exact-height induction step is vacuous.
This keeps the eventual induction proof focused on the first real cases.
-/
theorem CoproductKillsPreLieDifferenceHeightStep.vacuous_of_lt_three
    {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceHeightStep n := by
  intro _ih x y z hheight
  have hx : 1 ≤ PTree.height x := pTree_one_le_height x
  have hy : 1 ≤ PTree.height y := pTree_one_le_height y
  have hz : 1 ≤ PTree.height z := pTree_one_le_height z
  exfalso
  omega

/-- Rule-arity version of the vacuous small exact-height induction step. -/
theorem CoproductKillsPreLieDifferenceRuleArityHeightStep.vacuous_of_lt_three
    {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceRuleArityHeightStep n := by
  intro _ih x y z _hx _hy _hz hheight
  have hx : 1 ≤ PTree.height x := pTree_one_le_height x
  have hy : 1 ≤ PTree.height y := pTree_one_le_height y
  have hz : 1 ≤ PTree.height z := pTree_one_le_height z
  exfalso
  omega

/-- NMMS-derivation version of the vacuous small exact-height induction step. -/
theorem CoproductKillsPreLieDifferenceNMMSHeightStep.vacuous_of_lt_three
    {base : BaseRel} {n : Nat} (hn : n < 3) :
    CoproductKillsPreLieDifferenceNMMSHeightStep base n := by
  intro _ih sx sy sz dx dy dz hheight
  have hge : 3 ≤
      NMMS.derivationHeight dx +
        NMMS.derivationHeight dy +
          NMMS.derivationHeight dz := by
    rw [← NMMS.height_toTree_eq_derivationHeight dx,
      ← NMMS.height_toTree_eq_derivationHeight dy,
      ← NMMS.height_toTree_eq_derivationHeight dz]
    exact NMMS_toTree_total_height_ge_three dx dy dz
  exfalso
  omega

/--
Strong induction wrapper for the unrestricted height statement.

This proves the induction boilerplate once and for all: after the genuine
node/leaf step is proved for every total height, the bounded theorem follows
for all triples.  The only remaining mathematical content is therefore the
`CoproductKillsPreLieDifferenceHeightStep` proof.
-/
theorem CoproductKillsPreLieDifferenceHeightClaim.of_steps
    (hstep : ∀ n : Nat, CoproductKillsPreLieDifferenceHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceHeightClaim n := by
  have h_exact :
      ∀ n : Nat, ∀ x y z : PTree,
        PTree.height x + PTree.height y + PTree.height z = n →
          coproductSupportSummary_comul_linear
            (preLieDifferenceGenerators x y z) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih x y z hheight
    exact hstep n
      (fun x' y' z' hlt =>
        ih (PTree.height x' + PTree.height y' + PTree.height z') hlt
          x' y' z' rfl)
      x y z hheight
  intro _n x y z _hheight
  exact h_exact
    (PTree.height x + PTree.height y + PTree.height z) x y z rfl

/--
Strong induction wrapper for the rule-arity-respecting height statement.

This is the proof-theoretic version of the induction spine: the recursive
calls stay inside `PTree.RespectsRuleArity`, exactly matching proof trees
coming from the sequent calculus.
-/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_steps
    (hstep : ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightClaim n := by
  have h_exact :
      ∀ n : Nat, ∀ x y z : PTree,
        PTree.RespectsRuleArity x →
          PTree.RespectsRuleArity y →
            PTree.RespectsRuleArity z →
              PTree.height x + PTree.height y + PTree.height z = n →
                coproductSupportSummary_comul_linear
                  (preLieDifferenceGenerators x y z) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih x y z hx hy hz hheight
    exact hstep n
      (fun x' y' z' hx' hy' hz' hlt =>
        ih (PTree.height x' + PTree.height y' + PTree.height z') hlt
          x' y' z' hx' hy' hz' rfl)
      x y z hx hy hz hheight
  intro _n x y z hx hy hz _hheight
  exact h_exact
    (PTree.height x + PTree.height y + PTree.height z)
    x y z hx hy hz rfl

/--
It suffices to prove the unrestricted induction step from total height three
onward; the smaller exact-height steps are impossible.
-/
theorem CoproductKillsPreLieDifferenceHeightClaim.of_nonvacuous_steps
    (hstep :
      ∀ n : Nat, 3 ≤ n → CoproductKillsPreLieDifferenceHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceHeightClaim n :=
  CoproductKillsPreLieDifferenceHeightClaim.of_steps
    (fun n => by
      by_cases hn : n < 3
      · exact CoproductKillsPreLieDifferenceHeightStep.vacuous_of_lt_three hn
      · exact hstep n (by omega))

/--
It suffices to prove the rule-arity induction step from total height three
onward; the smaller exact-height steps are impossible.
-/
theorem CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_nonvacuous_steps
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightClaim n :=
  CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_steps
    (fun n => by
      by_cases hn : n < 3
      · exact
          CoproductKillsPreLieDifferenceRuleArityHeightStep.vacuous_of_lt_three
            hn
      · exact hstep n (by omega))

/--
Derivable-tree height theorem obtained from the rule-correct induction steps.
This is the form that should be fed by an actual induction over `NMMS.toTree`.
-/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.of_ruleArity_steps
    {base : BaseRel}
    (hstep : ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n := by
  intro n
  exact
    CoproductKillsPreLieDifferenceRuleArityHeightClaim.to_derivable
      (CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_steps hstep n)

/--
Derivable-tree height theorem obtained from nonvacuous rule-correct induction
steps.  This is the most precise current target for the proof-theoretic route:
prove the genuine node/leaf step only for total height at least three.
-/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.of_ruleArity_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n := by
  intro n
  exact
    CoproductKillsPreLieDifferenceRuleArityHeightClaim.to_derivable
      (CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_nonvacuous_steps
        hstep n)

/--
Derivable-tree height theorem obtained directly from induction steps over
`NMMS` derivations.  This is the route that treats height-one as base axioms and
height-two-plus cases as labelled inference-rule applications with fixed arity.
-/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, CoproductKillsPreLieDifferenceNMMSHeightStep base n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n := by
  have h_exact :
      ∀ n : Nat,
        ∀ (sx sy sz : MultiSequent)
          (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz),
          NMMS.derivationHeight dx +
              NMMS.derivationHeight dy +
                NMMS.derivationHeight dz = n →
            coproductSupportSummary_comul_linear
              (preLieDifferenceGenerators
                (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih sx sy sz dx dy dz hheight
    exact hstep n
      (fun sx' sy' sz' dx' dy' dz' hlt =>
        ih
          (NMMS.derivationHeight dx' +
            NMMS.derivationHeight dy' +
              NMMS.derivationHeight dz')
          hlt sx' sy' sz' dx' dy' dz' rfl)
      sx sy sz dx dy dz hheight
  intro _n x y z hx hy hz _hheight
  rcases hx with ⟨sx, dx, hx⟩
  rcases hy with ⟨sy, dy, hy⟩
  rcases hz with ⟨sz, dz, hz⟩
  rw [← hx, ← hy, ← hz]
  exact h_exact
    (NMMS.derivationHeight dx +
      NMMS.derivationHeight dy +
        NMMS.derivationHeight dz)
    sx sy sz dx dy dz rfl

/--
It is enough to prove the `NMMS` derivation step from total derivation height
three onward; smaller exact-height triples are impossible.
-/
theorem CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceNMMSHeightStep base n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_steps
    (fun n => by
      by_cases hn : n < 3
      · exact CoproductKillsPreLieDifferenceNMMSHeightStep.vacuous_of_lt_three hn
      · exact hstep n (by omega))

/--
The actual general-induction target for the GL coproduct compatibility theorem.

This is deliberately the new home of the remaining combinatorial `sorry`:
the proof should be a strong induction on total height, with the node case
discharging the cut bijection by child-cut decomposition rather than by
accumulating finite examples.
-/
theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_height_induction :
    ∀ n : Nat, CoproductKillsPreLieDifferenceHeightClaim n := by
  exact
    CoproductKillsPreLieDifferenceHeightClaim.of_steps
      (fun _n => by
        -- Remaining hard case: decompose admissible cuts of a node into
        -- root cuts and child cuts, then match the two pre-Lie associator
        -- sides by the address-level bijection.
        sorry)

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_ruleArity_height_induction
    (hstep : ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightClaim n :=
  CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_steps hstep

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_derivable_height_induction
    {base : BaseRel}
    (hstep : ∀ n : Nat, CoproductKillsPreLieDifferenceRuleArityHeightStep n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.of_ruleArity_steps hstep

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_nmms_height_induction
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, CoproductKillsPreLieDifferenceNMMSHeightStep base n) :
    ∀ n : Nat, CoproductKillsPreLieDifferenceDerivableHeightClaim base n :=
  CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_steps hstep

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_ruleArity_of_nonvacuous_steps
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceRuleArityHeightStep n)
    (x y z : PTree)
    (hx : PTree.RespectsRuleArity x)
    (hy : PTree.RespectsRuleArity y)
    (hz : PTree.RespectsRuleArity z) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators x y z) = 0 := by
  exact
    CoproductKillsPreLieDifferenceRuleArityHeightClaim.of_nonvacuous_steps
      hstep
      (PTree.height x + PTree.height y + PTree.height z)
      x y z hx hy hz le_rfl

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_toTree_of_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceRuleArityHeightStep n)
    {sx sy sz : MultiSequent}
    (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators
          (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0 := by
  exact
    coproductSupportSummary_comul_linear_preLieDifferenceGenerators_ruleArity_of_nonvacuous_steps
      hstep
      (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)
      (toTree_respectsRuleArity dx)
      (toTree_respectsRuleArity dy)
      (toTree_respectsRuleArity dz)

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_derivable_of_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceRuleArityHeightStep n)
    (x y z : PTree)
    (hx : DerivableTree base x)
    (hy : DerivableTree base y)
    (hz : DerivableTree base z) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators x y z) = 0 := by
  exact
    CoproductKillsPreLieDifferenceDerivableHeightClaim.of_ruleArity_nonvacuous_steps
      hstep
    (PTree.height x + PTree.height y + PTree.height z)
    x y z hx hy hz le_rfl

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_toTree_of_nmms_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceNMMSHeightStep base n)
    {sx sy sz : MultiSequent}
    (dx : NMMS base sx) (dy : NMMS base sy) (dz : NMMS base sz) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators
          (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)) = 0 := by
  exact
    CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_nonvacuous_steps
      hstep
      (PTree.height (NMMS.toTree dx) +
        PTree.height (NMMS.toTree dy) +
          PTree.height (NMMS.toTree dz))
      (NMMS.toTree dx) (NMMS.toTree dy) (NMMS.toTree dz)
      (derivableTree_of_derivation dx)
      (derivableTree_of_derivation dy)
      (derivableTree_of_derivation dz)
      le_rfl

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_derivable_of_nmms_nonvacuous_steps
    {base : BaseRel}
    (hstep :
      ∀ n : Nat, 3 ≤ n →
        CoproductKillsPreLieDifferenceNMMSHeightStep base n)
    (x y z : PTree)
    (hx : DerivableTree base x)
    (hy : DerivableTree base y)
    (hz : DerivableTree base z) :
    coproductSupportSummary_comul_linear
        (preLieDifferenceGenerators x y z) = 0 := by
  exact
    CoproductKillsPreLieDifferenceDerivableHeightClaim.of_nmms_nonvacuous_steps
      hstep
      (PTree.height x + PTree.height y + PTree.height z)
      x y z hx hy hz le_rfl

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators_of_height_induction
    (x y z : PTree) :
    coproductSupportSummary_comul_linear
      (preLieDifferenceGenerators x y z) = 0 := by
  exact
    coproductSupportSummary_comul_linear_preLieDifferenceGenerators_height_induction
      (PTree.height x + PTree.height y + PTree.height z) x y z le_rfl

theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators
    (x y z : PTree) :
    coproductSupportSummary_comul_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact
    coproductSupportSummary_comul_linear_preLieDifferenceGenerators_of_height_induction
      x y z

/-!
### 2b. Stability: the kernel of comul_linear is stable under grafting

For any `u : PTree`, if `comul_linear a = 0` then
`comul_linear (graftPreLie (treeGen u) a) = 0`.

This follows from a "coaction" formula

  `comul_linear (u ▷ a) = (id ⊗ (u ▷ -)) (comul_linear a)
                          + ((u ▷ -) ⊗ id) (comul_linear a)`

which expresses how the coproduct distributes over the pre-Lie product.
Proving this formula requires understanding how admissible cuts of a grafted
tree decompose; it is `sorry`'d pending the formal development.
-/

/--
The kernel of `comul_linear` is stable under left-grafting by any tree generator.
-/
theorem comul_linear_ker_stable_left (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : coproductSupportSummary_comul_linear a = 0) :
    coproductSupportSummary_comul_linear (graftPreLie (treeGen u) a) = 0 := by
  sorry

/--
The kernel of `comul_linear` is stable under right-grafting by any tree generator.
-/
theorem comul_linear_ker_stable_right (u : PTree)
    {a : linearProofTreeCarrier}
    (ha : coproductSupportSummary_comul_linear a = 0) :
    coproductSupportSummary_comul_linear (graftPreLie a (treeGen u)) = 0 := by
  sorry

/-!
### 2c. The kernel belongs to `preLieDifferenceStableSubmoduleFamily`
-/

/--
Abstract witness packaging the three genuinely non-trivial inputs needed to
show that the raw Grossman-Larsson coproduct descends to the stable quotient.

This isolates the remaining hard combinatorics from the later quotient-level
infrastructure.
-/
structure ComulLinearStableKernelWitness where
  kills_preLieDifferenceGenerators :
    ∀ x y z : PTree,
      coproductSupportSummary_comul_linear (preLieDifferenceGenerators x y z) = 0
  stable_left :
    ∀ u : PTree, ∀ {a : linearProofTreeCarrier},
      coproductSupportSummary_comul_linear a = 0 →
        coproductSupportSummary_comul_linear (graftPreLie (treeGen u) a) = 0
  stable_right :
    ∀ u : PTree, ∀ {a : linearProofTreeCarrier},
      coproductSupportSummary_comul_linear a = 0 →
        coproductSupportSummary_comul_linear (graftPreLie a (treeGen u)) = 0

/--
The current theorem-level API supplies a `ComulLinearStableKernelWitness`.

This is just a packaging lemma; the mathematical difficulty still sits in the
three component theorems above.
-/
def comulLinearStableKernelWitnessCurrent :
    ComulLinearStableKernelWitness where
  kills_preLieDifferenceGenerators :=
    coproductSupportSummary_comul_linear_preLieDifferenceGenerators
  stable_left := comul_linear_ker_stable_left
  stable_right := comul_linear_ker_stable_right

/--
If the three deep generator/stability inputs are available, then the kernel of
`coproductSupportSummary_comul_linear` belongs to
`preLieDifferenceStableSubmoduleFamily`.
-/
theorem comul_linear_ker_mem_stableFamily_of_witness
    (hw : ComulLinearStableKernelWitness) :
    (coproductSupportSummary_comul_linear).ker ∈ preLieDifferenceStableSubmoduleFamily := by
  refine ⟨?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨x, y, z, rfl⟩
    exact LinearMap.mem_ker.mpr (hw.kills_preLieDifferenceGenerators x y z)
  · intro u a ha
    exact LinearMap.mem_ker.mpr (hw.stable_left u (LinearMap.mem_ker.mp ha))
  · intro u a ha
    exact LinearMap.mem_ker.mpr (hw.stable_right u (LinearMap.mem_ker.mp ha))

/--
The kernel of `coproductSupportSummary_comul_linear` is a member of
`preLieDifferenceStableSubmoduleFamily`:
* it contains `preLieDifferenceSubmodule` (by (2a)), and
* it is stable under generator grafting (by (2b)).
-/
theorem comul_linear_ker_mem_stableFamily :
    (coproductSupportSummary_comul_linear).ker ∈ preLieDifferenceStableSubmoduleFamily := by
  exact comul_linear_ker_mem_stableFamily_of_witness
    comulLinearStableKernelWitnessCurrent

/--
Assumption-driven form of `comul_linear_kills_stableSubmodule`.

This is the exact descent argument needed later; only the witness `hw` carries
the genuinely difficult mathematics.
-/
theorem comul_linear_kills_stableSubmodule_of_witness
    (hw : ComulLinearStableKernelWitness)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    coproductSupportSummary_comul_linear a = 0 := by
  have hmem : a ∈ (coproductSupportSummary_comul_linear).ker :=
    Submodule.mem_sInf.mp ha _ (comul_linear_ker_mem_stableFamily_of_witness hw)
  exact LinearMap.mem_ker.mp hmem

/--
`comul_linear` kills every element of `preLieDifferenceStableSubmodule`.

Since `preLieDifferenceStableSubmodule = sInf preLieDifferenceStableSubmoduleFamily`
and `ker(comul_linear) ∈ preLieDifferenceStableSubmoduleFamily`, every element
of the sInf lies in the kernel.
-/
theorem comul_linear_kills_stableSubmodule
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    coproductSupportSummary_comul_linear a = 0 := by
  exact comul_linear_kills_stableSubmodule_of_witness
    comulLinearStableKernelWitnessCurrent ha

end ComulKillsStable

/-! ## 3. The coalgebra data respects the stable quotient -/

section RespectsStableQuotient

/--
The main descent theorem: `coproductSupportSummary_coalgebraData` kills every
element of `preLieDifferenceStableSubmodule` in both components.

* Comul: follows from `comul_linear_kills_stableSubmodule`.
* Counit: the counit is the zero map, so it kills everything.
-/
theorem coproductSupportSummary_respectsStableQuotient :
    CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData := by
  intro a ha
  refine ⟨?_, ?_⟩
  · -- comul kills a
    simpa using comul_linear_kills_stableSubmodule ha
  · -- counit kills a (counit is zero)
    have : coproductSupportSummary_coalgebraData.counit =
           coproductSupportSummary_counit_linear := rfl
    simp [this, coproductSupportSummary_counit_linear_eq_zero]

/--
Assumption-driven descent theorem: once the raw coproduct kills the stable
submodule, the packaged coalgebra data respects the stable quotient.
-/
theorem coproductSupportSummary_respectsStableQuotient_of_witness
    (hw : ComulLinearStableKernelWitness) :
    CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData := by
  intro a ha
  refine ⟨?_, ?_⟩
  · simpa using comul_linear_kills_stableSubmodule_of_witness hw ha
  · have : coproductSupportSummary_coalgebraData.counit =
           coproductSupportSummary_counit_linear := rfl
    simp [this, coproductSupportSummary_counit_linear_eq_zero]

end RespectsStableQuotient

/-! ## 4. Descended coalgebra maps and basic lemmas -/

section DescendedCoalgebra

/-- The hypothesis alias — this is now a theorem, not just an assumption. -/
noncomputable abbrev h_respects :
    CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData :=
  coproductSupportSummary_respectsStableQuotient

/-- The descended comultiplication on the stable quotient. -/
noncomputable abbrev Δ_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient :=
  coproductSupportSummary_comul_quot h_respects

/-- On generators: the descended comul equals the mk-tensor of the GL coproduct. -/
@[simp] theorem Δ_quot_mk_treeGen (x : PTree) :
    Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) := by
  simp [Δ_quot, coproductSupportSummary_comul_quot_mk]

/-- Linearity: the descended comul distributes over addition. -/
@[simp] theorem Δ_quot_add (a b : PreLieDifferenceStableQuotient) :
    Δ_quot (a + b) = Δ_quot a + Δ_quot b :=
  map_add _ _ _

/-- Linearity: the descended comul commutes with scalar multiplication. -/
@[simp] theorem Δ_quot_smul (n : ℤ) (a : PreLieDifferenceStableQuotient) :
    Δ_quot (n • a) = n • Δ_quot a :=
  map_smul _ _ _

end DescendedCoalgebra

/-! ## 5. Coassociativity axiom

We prove `coproductSupportSummary_comul_quot_left h_respects =
coproductSupportSummary_comul_quot_left_assoc h_respects` by reducing to
generators and expanding via the `_sum_N` lemmas.

The key step is showing that for each admissible cut `(f, r)` of a tree `x`,
the two iterated-coproduct paths agree:

  `mk(fg f) ⊗ Δ(mk(tg r))  =  assoc (Δ(mk(fg f)) ⊗ mk(tg r))`.

This reduces to the coassociativity of the raw coproduct at the cut level,
which is the statement that "two-level cuts" of `x` are the same regardless
of whether we cut the remainder or the forest first.  The formal proof is
`sorry`'d pending the address-level bijection.
-/

section Coassociativity

/--
Applying a linear map after a support-summary sum is the same as summing the
pointwise images.
-/
theorem linearMap_coproductSupportSummary_sum
    {α β : Type*} [AddCommMonoid α] [Module Int α]
    [AddCommMonoid β] [Module Int β]
    (L : α →ₗ[Int] β)
    (t : PTree)
    (f : Forest × PTree → α) :
    L (coproductSupportSummary_sum t f) =
      coproductSupportSummary_sum t (fun p => L (f p)) := by
  classical
  unfold coproductSupportSummary_sum
  simpa using map_sum L f (coproductSupportSummary_supportFinset t)

/--
Pointwise cut-tensor coassociativity for the descended quotient coproduct.

This is the actual remaining cut-bijection theorem.  The higher tree-level and
global coassociativity statements are routine consequences of this definition.
-/
def CutTensorCoassociative : Prop :=
  ∀ f : Forest, ∀ r : PTree,
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r))))

/--
The named pointwise cut-tensor coassociativity proposition is exactly the
statement of `comul_quot_coassoc_tensor`.
-/
theorem cutTensorCoassociative_iff :
    CutTensorCoassociative ↔
      ∀ f : Forest, ∀ r : PTree,
        (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
          (TensorProduct.assoc ℤ
              PreLieDifferenceStableQuotient
              PreLieDifferenceStableQuotient
              PreLieDifferenceStableQuotient).toLinearMap
            ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
              (mkPreLieDifferenceStableQuotient_tensor
                (TensorProduct.tmul ℤ (forestGen f) (treeGen r)))) := by
  rfl

/--
Singleton-forest form of the cut-tensor coassociativity statement.

This is the genuinely local reduction target: once it is known on singleton
forests, linearity in the forest variable upgrades it to arbitrary forests.
-/
def SingleTreeCutTensorCoassociative : Prop :=
  ∀ t r : PTree,
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r))))

/--
Pointwise cut-tensor coassociativity immediately implies its singleton-forest
specialisation.
-/
theorem singleTreeCutTensorCoassociative_of_cutTensorCoassociative
    (hcut : CutTensorCoassociative) :
    SingleTreeCutTensorCoassociative := by
  intro t r
  simpa using hcut [t] r

/--
The cut-tensor coassociativity statement is trivial on the empty forest.
-/
theorem comul_quot_coassoc_tensor_nil (r : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen ([] : Forest)) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen ([] : Forest)) (treeGen r)))) := by
  rw [show forestGen ([] : Forest) = 0 by simp]
  have hmk :
      mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ 0 (treeGen r)) = 0 := by
    simp
  rw [hmk]
  rw [LinearMap.map_zero, LinearMap.map_zero]
  exact
    (TensorProduct.assoc ℤ
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient
      PreLieDifferenceStableQuotient).map_zero.symm

/--
Linearity in the forest variable: if cut-tensor coassociativity holds for the
head singleton forest and for the tail forest, then it also holds for their
cons-combination.
-/
theorem comul_quot_coassoc_tensor_cons_of_singleton_and_tail
    (t : PTree) (ts : Forest) (r : PTree)
    (hhead :
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r))) =
        (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r)))))
    (htail :
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen ts) (treeGen r))) =
        (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ts) (treeGen r))))) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen (t :: ts)) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen (t :: ts)) (treeGen r)))) := by
  calc
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen (t :: ts)) (treeGen r))) =
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r))) +
        (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen ts) (treeGen r))) := by
      simp [forestGen_cons, TensorProduct.add_tmul]
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r)))) +
        (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ts) (treeGen r)))) := by
      rw [hhead, htail]
      rfl
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        (((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen [t]) (treeGen r)))) +
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ts) (treeGen r))))) := by
      exact (LinearMap.map_add
        (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        _ _).symm
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen (t :: ts)) (treeGen r)))) := by
      simp [forestGen_cons, TensorProduct.add_tmul]

/--
Equivalent append-style linearity in the forest variable.
-/
theorem comul_quot_coassoc_tensor_append_of_parts
    (xs ys : Forest) (r : PTree)
    (hxs :
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen xs) (treeGen r))) =
        (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen xs) (treeGen r)))))
    (hys :
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen ys) (treeGen r))) =
        (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ys) (treeGen r))))) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen (xs ++ ys)) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen (xs ++ ys)) (treeGen r)))) := by
  calc
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen (xs ++ ys)) (treeGen r))) =
      (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen xs) (treeGen r))) +
        (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen ys) (treeGen r))) := by
      simp [forestGen_append, TensorProduct.add_tmul]
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen xs) (treeGen r)))) +
        (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ys) (treeGen r)))) := by
      rw [hxs, hys]
      rfl
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        (((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen xs) (treeGen r)))) +
          ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
            (mkPreLieDifferenceStableQuotient_tensor
              (TensorProduct.tmul ℤ (forestGen ys) (treeGen r))))) := by
      exact (LinearMap.map_add
        (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        _ _).symm
    _ =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen (xs ++ ys)) (treeGen r)))) := by
      simp [forestGen_append, TensorProduct.add_tmul]

/--
The singleton-forest theorem already implies the full cut-tensor coassociative
statement by induction on the forest variable.
-/
theorem cutTensorCoassociative_of_singleTreeCutTensorCoassociative
    (hsing : SingleTreeCutTensorCoassociative) :
    CutTensorCoassociative := by
  intro f r
  induction f with
  | nil =>
      exact comul_quot_coassoc_tensor_nil r
  | cons t ts ih =>
      exact comul_quot_coassoc_tensor_cons_of_singleton_and_tail
        t ts r (hsing t r) ih

/--
Thus the arbitrary-forest and singleton-forest cut-tensor coassociativity
statements are equivalent.
-/
theorem cutTensorCoassociative_iff_singleTreeCutTensorCoassociative :
    CutTensorCoassociative ↔ SingleTreeCutTensorCoassociative := by
  constructor
  · exact singleTreeCutTensorCoassociative_of_cutTensorCoassociative
  · exact cutTensorCoassociative_of_singleTreeCutTensorCoassociative

/--
Package the reduced coassociativity input at the singleton-forest level.

This is the genuinely minimal combinatorial hypothesis needed for all later
coassociativity consequences in the quotient layer.
-/
structure SingleTreeCutTensorCoassociativeWitness where
  singleTreeCutTensorCoassociative : SingleTreeCutTensorCoassociative

/--
Promote a singleton-cut witness to the full forest-level cut-tensor
coassociativity statement.
-/
def SingleTreeCutTensorCoassociativeWitness.toCutTensorCoassociative
    (hw : SingleTreeCutTensorCoassociativeWitness) :
    CutTensorCoassociative :=
  cutTensorCoassociative_of_singleTreeCutTensorCoassociative
    hw.singleTreeCutTensorCoassociative

/--
The singleton witness directly implies the pointwise forest-level cut-tensor
coassociativity theorem.
-/
theorem SingleTreeCutTensorCoassociativeWitness.tensor
    (hw : SingleTreeCutTensorCoassociativeWitness)
    (f : Forest) (r : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r)))) := by
  exact hw.toCutTensorCoassociative f r

/--
Assumption-driven tensor-level coassociativity: a full forest-level cut-tensor
coassociativity hypothesis immediately yields the concrete tensor identity.
-/
theorem comul_quot_coassoc_tensor_of_cutTensorCoassociative
    (hcut : CutTensorCoassociative) (f : Forest) (r : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r)))) := by
  exact hcut f r

/--
Assumption-driven tensor-level coassociativity from the reduced singleton-tree
input.

This packages the conceptual route used throughout the file: first prove the
local singleton case, then upgrade to arbitrary forests by linearity.
-/
theorem comul_quot_coassoc_tensor_of_singleTreeCutTensorCoassociative
    (hsing : SingleTreeCutTensorCoassociative)
    (f : Forest) (r : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r)))) := by
  exact
    comul_quot_coassoc_tensor_of_cutTensorCoassociative
      (cutTensorCoassociative_of_singleTreeCutTensorCoassociative hsing) f r

/--
Coassociativity at the level of a single admissible-cut tensor `mk(fg f) ⊗ mk(tg r)`:
applying `lTensor Δ` (id ⊗ Δ) gives the same result as applying
`assoc ∘ rTensor Δ` (assoc ∘ (Δ ⊗ id)).
-/
theorem comul_quot_coassoc_tensor (f : Forest) (r : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r)))) := by
  sorry

/--
Assumption-driven reduction from the cut-tensor theorem to generator-level
coassociativity.
-/
theorem comul_quot_coassoc_treeGen_of_cutTensorCoassociative
    (hcut : CutTensorCoassociative) (x : PTree) :
    coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  classical
  simp only [coproductSupportSummary_comul_quot_left_treeGen_sum,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  change
    (((LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot).comp
      mkPreLieDifferenceStableQuotient_tensor)
        (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) =
      ((((TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap).comp
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot).comp
          mkPreLieDifferenceStableQuotient_tensor))
          (coproductSupportSummary_sum x coproductSupportSummary_tensorGen))
  rw [linearMap_coproductSupportSummary_sum
      (((LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot).comp
        mkPreLieDifferenceStableQuotient_tensor))
      x coproductSupportSummary_tensorGen]
  rw [linearMap_coproductSupportSummary_sum
      (((TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap).comp
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot).comp
          mkPreLieDifferenceStableQuotient_tensor))
      x coproductSupportSummary_tensorGen]
  apply coproductSupportSummary_sum_congr
  intro p hp
  rcases p with ⟨f, r⟩
  change
    (LinearMap.lTensor PreLieDifferenceStableQuotient Δ_quot)
        (mkPreLieDifferenceStableQuotient_tensor
          (TensorProduct.tmul ℤ (forestGen f) (treeGen r))) =
      (TensorProduct.assoc ℤ
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient).toLinearMap
        ((LinearMap.rTensor PreLieDifferenceStableQuotient Δ_quot)
          (mkPreLieDifferenceStableQuotient_tensor
            (TensorProduct.tmul ℤ (forestGen f) (treeGen r))))
  exact hcut f r

/--
Coassociativity on a single generator `treeGen x`:
`(id ⊗ Δ)(Δ(mk(tg x))) = assoc((Δ ⊗ id)(Δ(mk(tg x))))`.
This follows from `comul_quot_coassoc_tensor` by summing over the admissible cuts of `x`.
-/
theorem comul_quot_coassoc_treeGen (x : PTree) :
    coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  exact comul_quot_coassoc_treeGen_of_cutTensorCoassociative
    (fun f r => comul_quot_coassoc_tensor f r) x

/--
Assumption-driven global coassociativity: once the pointwise cut-tensor theorem
is known, the descended quotient coproduct is coassociative as a linear map.
-/
theorem coproductSupportSummary_comul_quot_coassoc_of_cutTensorCoassociative
    (hcut : CutTensorCoassociative) :
    coproductSupportSummary_comul_quot_left h_respects =
      coproductSupportSummary_comul_quot_left_assoc h_respects := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction a using Finsupp.induction_linear with
    | zero =>
        simp [map_zero]
    | add f g hf hg =>
        simpa [mkPreLieDifferenceStableQuotient, map_add, hf, hg]
    | single x n =>
        have hq :
            preLieDifferenceStableSubmodule.mkQ (Finsupp.single x n) =
              n • preLieDifferenceStableSubmodule.mkQ (treeGen x) := by
          simpa [treeGen] using
            (preLieDifferenceStableSubmodule.mkQ.map_smul n (treeGen x))
        change
          (coproductSupportSummary_comul_quot_left h_respects)
              (preLieDifferenceStableSubmodule.mkQ (Finsupp.single x n)) =
            (coproductSupportSummary_comul_quot_left_assoc h_respects)
              (preLieDifferenceStableSubmodule.mkQ (Finsupp.single x n))
        rw [hq, LinearMap.map_smul, LinearMap.map_smul]
        exact congrArg (fun q => n • q)
          (comul_quot_coassoc_treeGen_of_cutTensorCoassociative hcut x)

/--
The singleton witness already suffices for generator-level quotient
coassociativity.
-/
theorem comul_quot_coassoc_treeGen_of_singleTreeCutTensorCoassociative
    (hsing : SingleTreeCutTensorCoassociative) (x : PTree) :
    coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  exact comul_quot_coassoc_treeGen_of_cutTensorCoassociative
    (cutTensorCoassociative_of_singleTreeCutTensorCoassociative hsing) x

/--
Witness-packaged generator-level quotient coassociativity.
-/
theorem SingleTreeCutTensorCoassociativeWitness.treeGen
    (hw : SingleTreeCutTensorCoassociativeWitness) (x : PTree) :
    coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  exact comul_quot_coassoc_treeGen_of_singleTreeCutTensorCoassociative
    hw.singleTreeCutTensorCoassociative x

/--
The singleton witness also suffices for the global quotient coassociativity
axiom.
-/
theorem coproductSupportSummary_comul_quot_coassoc_of_singleTreeCutTensorCoassociative
    (hsing : SingleTreeCutTensorCoassociative) :
    coproductSupportSummary_comul_quot_left h_respects =
      coproductSupportSummary_comul_quot_left_assoc h_respects := by
  exact coproductSupportSummary_comul_quot_coassoc_of_cutTensorCoassociative
    (cutTensorCoassociative_of_singleTreeCutTensorCoassociative hsing)

/--
Witness-packaged global quotient coassociativity.
-/
theorem SingleTreeCutTensorCoassociativeWitness.coassoc
    (hw : SingleTreeCutTensorCoassociativeWitness) :
    coproductSupportSummary_comul_quot_left h_respects =
      coproductSupportSummary_comul_quot_left_assoc h_respects := by
  exact
    coproductSupportSummary_comul_quot_coassoc_of_singleTreeCutTensorCoassociative
      hw.singleTreeCutTensorCoassociative

/--
Coassociativity of the descended comultiplication:
`(id ⊗ Δ) ∘ Δ = assoc ∘ (Δ ⊗ id) ∘ Δ`
as linear maps `PreLieDifferenceStableQuotient → Q ⊗ Q ⊗ Q`.
-/
theorem coproductSupportSummary_comul_quot_coassoc :
    coproductSupportSummary_comul_quot_left h_respects =
      coproductSupportSummary_comul_quot_left_assoc h_respects := by
  exact coproductSupportSummary_comul_quot_coassoc_of_cutTensorCoassociative
    (fun f r => comul_quot_coassoc_tensor f r)

end Coassociativity

/-! ## 6. Honest coassociative quotient-comultiplication package

At this stage of the development, the comultiplication side is much further
along than the counit side:

- the quotient comultiplication is defined;
- its coassociativity reduces to the cut-tensor theorem, and can therefore be
  packaged under explicit witnesses;
- the currently bundled counit is still the placeholder zero map, so the full
  coalgebra laws are not yet honestly available.

To avoid over-packaging, we isolate the part that is already mathematically
sound: a descended quotient comultiplication together with its coassociativity.
-/

section CoassociativeComulPackage

/--
Minimal honest package currently available in the quotient-first development:
the descended quotient comultiplication together with its coassociativity.

This avoids claiming counit axioms before the counit definition is repaired.
-/
structure CoproductSupportQuotientCoassociativeComul where
  h : CoproductSupportCoalgebraRespectsStableQuotient
    coproductSupportSummary_coalgebraData
  coassoc :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc ℤ
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

noncomputable def CoproductSupportQuotientCoassociativeComul.comul
    (H : CoproductSupportQuotientCoassociativeComul) :
    LinearMap (RingHom.id ℤ) PreLieDifferenceStableQuotient
      (TensorProduct ℤ PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient) :=
  coproductSupportSummary_comul_quot H.h

@[simp] theorem CoproductSupportQuotientCoassociativeComul.comul_apply
    (H : CoproductSupportQuotientCoassociativeComul)
    (a : PreLieDifferenceStableQuotient) :
    H.comul a = coproductSupportSummary_comul_quot H.h a := by
  rfl

@[simp] theorem CoproductSupportQuotientCoassociativeComul.comul_mk
    (H : CoproductSupportQuotientCoassociativeComul)
    (a : linearProofTreeCarrier) :
    H.comul (mkPreLieDifferenceStableQuotient a) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear a) := by
  simp [CoproductSupportQuotientCoassociativeComul.comul,
    coproductSupportSummary_comul_quot_mk]

theorem CoproductSupportQuotientCoassociativeComul.coassoc_apply
    (H : CoproductSupportQuotientCoassociativeComul)
    (a : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc ℤ
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

theorem CoproductSupportQuotientCoassociativeComul.coassoc_shorthand_apply
    (H : CoproductSupportQuotientCoassociativeComul)
    (a : PreLieDifferenceStableQuotient) :
    coproductSupportSummary_comul_quot_left_assoc H.h a =
      coproductSupportSummary_comul_quot_left H.h a := by
  simpa [coproductSupportSummary_comul_quot_left_assoc,
    coproductSupportSummary_comul_quot_left,
    coproductSupportSummary_comul_quot_right,
    LinearMap.comp_apply] using
    (H.coassoc_apply a)

theorem CoproductSupportQuotientCoassociativeComul.coassoc_shorthand
    (H : CoproductSupportQuotientCoassociativeComul) :
    coproductSupportSummary_comul_quot_left_assoc H.h =
      coproductSupportSummary_comul_quot_left H.h := by
  apply LinearMap.ext
  intro a
  simpa using H.coassoc_shorthand_apply a

theorem CoproductSupportQuotientCoassociativeComul.coassoc_treeGen
    (H : CoproductSupportQuotientCoassociativeComul)
    (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient (treeGen x)))

/--
Assumption-driven coassociativity axiom for the quotient comultiplication,
under the full forest-level cut-tensor theorem.
-/
theorem coproductSupportSummary_quotientComulCoassoc_of_cutTensorCoassociative
    (hcut : CutTensorCoassociative) :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot h_respects)))
        (coproductSupportSummary_comul_quot h_respects) =
      LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h_respects))
        (coproductSupportSummary_comul_quot h_respects) := by
  change coproductSupportSummary_comul_quot_left_assoc h_respects =
    coproductSupportSummary_comul_quot_left h_respects
  exact
    (coproductSupportSummary_comul_quot_coassoc_of_cutTensorCoassociative hcut).symm

/--
Singleton-tree witness version of the same honest coassociativity package.
-/
theorem coproductSupportSummary_quotientComulCoassoc_of_singleTreeCutTensorCoassociative
    (hsing : SingleTreeCutTensorCoassociative) :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot h_respects)))
        (coproductSupportSummary_comul_quot h_respects) =
      LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h_respects))
        (coproductSupportSummary_comul_quot h_respects) := by
  exact
    coproductSupportSummary_quotientComulCoassoc_of_cutTensorCoassociative
      (cutTensorCoassociative_of_singleTreeCutTensorCoassociative hsing)

/--
Construct the honest quotient-level coassociative-comultiplication package from
a singleton-tree cut-tensor witness.
-/
noncomputable def SingleTreeCutTensorCoassociativeWitness.toQuotientCoassociativeComul
    (hw : SingleTreeCutTensorCoassociativeWitness) :
    CoproductSupportQuotientCoassociativeComul where
  h := h_respects
  coassoc :=
    coproductSupportSummary_quotientComulCoassoc_of_singleTreeCutTensorCoassociative
      hw.singleTreeCutTensorCoassociative

/--
If a full quotient coalgebra bundle is available, it forgets to the honest
coassociative-comultiplication package defined above.
-/
noncomputable def CoproductSupportQuotientCoalgebra.toCoassociativeComul
    (H : CoproductSupportQuotientCoalgebra) :
    CoproductSupportQuotientCoassociativeComul where
  h := H.h
  coassoc := H.coassoc

end CoassociativeComulPackage

/-! ## 7. Oudom-Guin bridge target

The quotient GL comultiplication is useful combinatorial evidence, but the
Hopf carrier should be the stable UEA.  The theorem shape below records the
missing Oudom-Guin bridge explicitly: after applying the UEA inclusion on both
tensor factors, the GL coproduct should agree with the primitive UEA
comultiplication.
-/

section OudomGuinBridgeTarget

/-- The canonical linear inclusion of the stable quotient into its UEA. -/
noncomputable abbrev stableUEACanonicalIota :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA :=
  preLieDifferenceStableQuotientUEA_ι_linear

/-! ### Proof-theoretic stable quotients -/

/--
The stable pre-Lie relation restricted to the submodule generated by proof trees
derivable over a fixed primitive base relation.

This is the quotient relation for the proof-theoretic carrier: we first restrict
to reachable proof trees, then impose exactly the stable pre-Lie equations
visible inside that reachable submodule.
-/
def derivablePreLieStableRelation (base : BaseRel) :
    Submodule ℤ (derivableTreeSubmodule base) :=
  preLieDifferenceStableSubmodule.comap
    (derivableTreeSubmodule base).subtype

/-- Quotients by submodules of the reachable proof-tree carrier. -/
instance derivableTreeSubmoduleHasQuotient
    (base : BaseRel) :
    HasQuotient (derivableTreeSubmodule base)
      (Submodule ℤ (derivableTreeSubmodule base)) :=
  Submodule.hasQuotient

/--
The proof-theoretic stable quotient over a primitive base relation.

Unlike `PreLieDifferenceStableQuotient`, this remembers that the carrier was
generated by actual `NMMS` proof trees over `base`.
-/
abbrev DerivablePreLieStableQuotient (base : BaseRel) :=
  derivableTreeSubmodule base ⧸ derivablePreLieStableRelation base

/-- The canonical quotient map from reachable proof-tree combinations. -/
noncomputable def mkDerivablePreLieStableQuotient (base : BaseRel) :
    derivableTreeSubmodule base →ₗ[ℤ]
      DerivablePreLieStableQuotient base :=
  Submodule.mkQ (derivablePreLieStableRelation base)

/-- The class of a derivable tree generator in the proof-theoretic quotient. -/
noncomputable def derivableStableTreeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    DerivablePreLieStableQuotient base :=
  mkDerivablePreLieStableQuotient base
    ⟨treeGen t, treeGen_mem_derivableTreeSubmodule ht⟩

/--
The canonical map from the proof-theoretic stable quotient into the global
stable quotient.
-/
noncomputable def derivableStableQuotientToStableQuotient
    (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ]
      PreLieDifferenceStableQuotient :=
  Submodule.mapQ
    (derivablePreLieStableRelation base)
    preLieDifferenceStableSubmodule
    (derivableTreeSubmodule base).subtype
    (by
      intro x hx
      exact hx)

@[simp] theorem derivableStableQuotientToStableQuotient_mk
    (base : BaseRel) (a : derivableTreeSubmodule base) :
    derivableStableQuotientToStableQuotient base
        (mkDerivablePreLieStableQuotient base a) =
      mkPreLieDifferenceStableQuotient a.1 := by
  rfl

@[simp] theorem derivableStableQuotientToStableQuotient_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    derivableStableQuotientToStableQuotient base
        (derivableStableTreeGen ht) =
      mkPreLieDifferenceStableQuotient (treeGen t) := by
  rfl

/--
Base extension functorially maps proof-theoretic stable quotients.
-/
noncomputable def derivableStableQuotientMapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base') :
    DerivablePreLieStableQuotient base →ₗ[ℤ]
      DerivablePreLieStableQuotient base' :=
  Submodule.mapQ
    (derivablePreLieStableRelation base)
    (derivablePreLieStableRelation base')
    (derivableTreeSubmoduleInclusion h)
    (by
      intro x hx
      change ((derivableTreeSubmoduleInclusion h x).1) ∈
        preLieDifferenceStableSubmodule
      simpa [derivableTreeSubmoduleInclusion_apply,
        derivablePreLieStableRelation] using hx)

@[simp] theorem derivableStableQuotientMapBase_treeGen
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    {t : PTree}
    (ht : DerivableTree base t) :
    derivableStableQuotientMapBase h (derivableStableTreeGen ht) =
      derivableStableTreeGen (derivableTree_mono h ht) := by
  rfl

/--
The global stable-quotient image is invariant under base-extension transport.
-/
theorem derivableStableQuotientToStableQuotient_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    derivableStableQuotientToStableQuotient base'
        (derivableStableQuotientMapBase h q) =
      derivableStableQuotientToStableQuotient base q := by
  induction q using Submodule.Quotient.induction_on with
  | H a =>
      rfl

/--
The proof-theoretic stable quotient inserted into the stable UEA.
-/
noncomputable def derivableStableUEAIota (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA :=
  stableUEACanonicalIota.comp
    (derivableStableQuotientToStableQuotient base)

@[simp] theorem derivableStableUEAIota_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    derivableStableUEAIota base (derivableStableTreeGen ht) =
      stableUEA_treeGen t := by
  rfl

theorem derivableStableUEAIota_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    derivableStableUEAIota base'
        (derivableStableQuotientMapBase h q) =
      derivableStableUEAIota base q := by
  simp [derivableStableUEAIota,
    derivableStableQuotientToStableQuotient_mapBase h q]

theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_derivable
    {base : BaseRel}
    (q : DerivablePreLieStableQuotient base) :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q) =
      TensorProduct.tmul ℤ (derivableStableUEAIota base q) 1 +
        TensorProduct.tmul ℤ 1 (derivableStableUEAIota base q) := by
  simpa [derivableStableUEAIota, stableUEACanonicalIota] using
    stableUEA_OGPrimitiveComultiplicationCanonical_comul_apply
      (derivableStableQuotientToStableQuotient base q)

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_derivable
    {base : BaseRel}
    (q : DerivablePreLieStableQuotient base) :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base q) = 0 := by
  simpa using
    stableUEA_OGPrimitiveComultiplicationCanonical_counit_apply
      (derivableStableQuotientToStableQuotient base q)

theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_derivable_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base
          (derivableStableTreeGen ht)) =
      TensorProduct.tmul ℤ
          (derivableStableUEAIota base (derivableStableTreeGen ht)) 1 +
        TensorProduct.tmul ℤ 1
          (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  exact stableUEA_OGPrimitiveComultiplicationCanonical_comul_derivable
    (derivableStableTreeGen ht)

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_derivable_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base
          (derivableStableTreeGen ht)) = 0 := by
  exact stableUEA_OGPrimitiveComultiplicationCanonical_counit_derivable
    (derivableStableTreeGen ht)

theorem stableUEA_OGPrimitiveComultiplicationCanonical_comul_derivable_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base'
          (derivableStableQuotientMapBase h q)) =
      stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q) := by
  rw [derivableStableQuotientToStableQuotient_mapBase h q]

@[simp] theorem stableUEA_OGPrimitiveComultiplicationCanonical_counit_derivable_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base'
          (derivableStableQuotientMapBase h q)) =
      stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base q) := by
  rw [derivableStableQuotientToStableQuotient_mapBase h q]

/--
The UEA-valued primitive comultiplication carried by the proof-theoretic stable
quotient over a base relation.

This is the fiberwise coalgebra shadow: the source remembers derivability over
`base`, while the target is the stable UEA tensor where the actual coalgebra
carrier lives.
-/
noncomputable def derivableStableOGPrimitiveComul (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ] stableUEATensor :=
  stableUEA_OGPrimitiveComultiplicationCanonical.comul.comp
    (derivableStableQuotientToStableQuotient base)

/-- The induced primitive counit on the proof-theoretic stable quotient. -/
noncomputable def derivableStableOGPrimitiveCounit (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ] ℤ :=
  stableUEA_OGPrimitiveComultiplicationCanonical.counit.comp
    (derivableStableQuotientToStableQuotient base)

/-- A named pair of UEA-valued primitive maps on the derivable quotient fiber. -/
structure DerivableStableOGPrimitiveComultiplication (base : BaseRel) where
  comul : DerivablePreLieStableQuotient base →ₗ[ℤ] stableUEATensor
  counit : DerivablePreLieStableQuotient base →ₗ[ℤ] ℤ

/-- The canonical primitive maps on the derivable quotient fiber. -/
noncomputable def derivableStableOGPrimitiveComultiplication
    (base : BaseRel) :
    DerivableStableOGPrimitiveComultiplication base where
  comul := derivableStableOGPrimitiveComul base
  counit := derivableStableOGPrimitiveCounit base

@[simp] theorem derivableStableOGPrimitiveComultiplication_comul
    (base : BaseRel) :
    (derivableStableOGPrimitiveComultiplication base).comul =
      derivableStableOGPrimitiveComul base := by
  rfl

@[simp] theorem derivableStableOGPrimitiveComultiplication_counit
    (base : BaseRel) :
    (derivableStableOGPrimitiveComultiplication base).counit =
      derivableStableOGPrimitiveCounit base := by
  rfl

theorem derivableStableOGPrimitiveComul_apply
    {base : BaseRel}
    (q : DerivablePreLieStableQuotient base) :
    derivableStableOGPrimitiveComul base q =
      TensorProduct.tmul ℤ (derivableStableUEAIota base q) 1 +
        TensorProduct.tmul ℤ 1 (derivableStableUEAIota base q) := by
  exact stableUEA_OGPrimitiveComultiplicationCanonical_comul_derivable q

@[simp] theorem derivableStableOGPrimitiveCounit_apply
    {base : BaseRel}
    (q : DerivablePreLieStableQuotient base) :
    derivableStableOGPrimitiveCounit base q = 0 := by
  exact stableUEA_OGPrimitiveComultiplicationCanonical_counit_derivable q

theorem derivableStableOGPrimitiveComul_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    derivableStableOGPrimitiveComul base (derivableStableTreeGen ht) =
      TensorProduct.tmul ℤ (stableUEA_treeGen t) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen t) := by
  simpa using
    derivableStableOGPrimitiveComul_apply
      (base := base) (derivableStableTreeGen ht)

@[simp] theorem derivableStableOGPrimitiveCounit_treeGen
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    derivableStableOGPrimitiveCounit base (derivableStableTreeGen ht) = 0 := by
  exact derivableStableOGPrimitiveCounit_apply
    (base := base) (derivableStableTreeGen ht)

theorem derivableStableOGPrimitiveComul_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    derivableStableOGPrimitiveComul base'
        (derivableStableQuotientMapBase h q) =
      derivableStableOGPrimitiveComul base q := by
  change
    stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base'
          (derivableStableQuotientMapBase h q)) =
      stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q)
  rw [derivableStableQuotientToStableQuotient_mapBase h q]

@[simp] theorem derivableStableOGPrimitiveCounit_mapBase
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    derivableStableOGPrimitiveCounit base'
        (derivableStableQuotientMapBase h q) =
      derivableStableOGPrimitiveCounit base q := by
  change
    stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base'
          (derivableStableQuotientMapBase h q)) =
      stableUEA_OGPrimitiveComultiplicationCanonical.counit
        (derivableStableQuotientToStableQuotient base q)
  rw [derivableStableQuotientToStableQuotient_mapBase h q]

/-- Tensoring a quotient-to-UEA linear map with itself. -/
noncomputable def stableUEATensorMapFromStableQuotient
    (iota : PreLieDifferenceStableQuotient →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA) :
    TensorProduct ℤ PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient →ₗ[ℤ] stableUEATensor :=
  TensorProduct.map iota iota

/--
Generator-level primitive formula expected of the UEA-side Oudom-Guin
comultiplication.
-/
def OudomGuinPrimitiveUEAComultiplicationOnGenerators
    (DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor) : Prop :=
  ∀ x : PTree,
    DeltaOG (stableUEA_treeGen x) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)

/--
The UEA-side Oudom-Guin comultiplication extends the quotient-level primitive
map, not merely the named tree-generator cases.

This is the quotient-wide bridge between the proof-tree quotient and the actual
UEA coalgebra carrier.
-/
def OudomGuinUEAExtendsStableQuotientPrimitive
    (DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor) : Prop :=
  ∀ q : PreLieDifferenceStableQuotient,
    DeltaOG (stableUEACanonicalIota q) =
      stableUEA_OGPrimitiveComulFromStableQuotient q

theorem OudomGuinUEAExtendsStableQuotientPrimitive_iff_linearMap
    (DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor) :
    OudomGuinUEAExtendsStableQuotientPrimitive DeltaOG ↔
      LinearMap.comp DeltaOG stableUEACanonicalIota =
        stableUEA_OGPrimitiveComulFromStableQuotient := by
  constructor
  · intro h
    apply LinearMap.ext
    intro q
    simpa [LinearMap.comp_apply] using h q
  · intro h q
    have happ := congrArg (fun f => f q) h
    simpa [LinearMap.comp_apply] using happ

theorem OudomGuinUEAExtendsStableQuotientPrimitive.apply
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (h : OudomGuinUEAExtendsStableQuotientPrimitive DeltaOG)
    (q : PreLieDifferenceStableQuotient) :
    DeltaOG (stableUEACanonicalIota q) =
      TensorProduct.tmul ℤ (stableUEACanonicalIota q) 1 +
        TensorProduct.tmul ℤ 1 (stableUEACanonicalIota q) := by
  rw [h q]
  rfl

theorem OudomGuinUEAExtendsStableQuotientPrimitive.apply_derivable
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (h : OudomGuinUEAExtendsStableQuotientPrimitive DeltaOG)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    DeltaOG (derivableStableUEAIota base q) =
      stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q) := by
  rw [show derivableStableUEAIota base q =
      stableUEACanonicalIota
        (derivableStableQuotientToStableQuotient base q) by rfl]
  rw [h]
  rw [stableUEA_OGPrimitiveComultiplicationCanonical_comul_eq_fromStableQuotient]

theorem OudomGuinUEAExtendsStableQuotientPrimitive.apply_derivable_formula
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (h : OudomGuinUEAExtendsStableQuotientPrimitive DeltaOG)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    DeltaOG (derivableStableUEAIota base q) =
      TensorProduct.tmul ℤ (derivableStableUEAIota base q) 1 +
        TensorProduct.tmul ℤ 1 (derivableStableUEAIota base q) := by
  rw [show derivableStableUEAIota base q =
      stableUEACanonicalIota
        (derivableStableQuotientToStableQuotient base q) by rfl]
  exact h.apply (derivableStableQuotientToStableQuotient base q)

/--
The left-hand GL side of the GL/OG bridge already agrees with the quotient-level
primitive map after inserting both tensor factors into the UEA.

This isolates the remaining unit-completed GL obligation from the UEA
coalgebra-extension obligation.
-/
def GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
    (DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient) : Prop :=
  LinearMap.comp
      (stableUEATensorMapFromStableQuotient stableUEACanonicalIota)
      DeltaGL =
    stableUEA_OGPrimitiveComulFromStableQuotient

theorem GrossmanLarssonUnitCompletedAgreesWithOGPrimitive.apply
    {DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient}
    (h : GrossmanLarssonUnitCompletedAgreesWithOGPrimitive DeltaGL)
    (q : PreLieDifferenceStableQuotient) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (DeltaGL q) =
      stableUEA_OGPrimitiveComulFromStableQuotient q := by
  have happ := congrArg (fun f => f q) h
  simpa [GrossmanLarssonUnitCompletedAgreesWithOGPrimitive,
    LinearMap.comp_apply] using happ

/--
The precise GL/OG intertwining statement.

This is the target theorem:
`(iota ⊗ iota) ∘ DeltaGL = DeltaOG ∘ iota`.
The final `DeltaGL` should be the unit-completed GL coproduct; the current
`Delta_quot` remains useful as the quotient-level diagnostic approximation.
-/
def OudomGuinGrossmanLarssonIntertwiningTarget
    (DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (iota : PreLieDifferenceStableQuotient →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA)
    (DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor) : Prop :=
  LinearMap.comp (stableUEATensorMapFromStableQuotient iota) DeltaGL =
    LinearMap.comp DeltaOG iota

theorem OudomGuinGrossmanLarssonIntertwiningTarget.apply_mk
    {DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient}
    {iota : PreLieDifferenceStableQuotient →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA}
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (h :
      OudomGuinGrossmanLarssonIntertwiningTarget DeltaGL iota DeltaOG)
    (a : linearProofTreeCarrier) :
    stableUEATensorMapFromStableQuotient iota
        (DeltaGL (mkPreLieDifferenceStableQuotient a)) =
      DeltaOG (iota (mkPreLieDifferenceStableQuotient a)) := by
  have happ := congrArg
    (fun f => f (mkPreLieDifferenceStableQuotient a)) h
  simpa [OudomGuinGrossmanLarssonIntertwiningTarget,
    LinearMap.comp_apply] using happ

/--
The GL/OG bridge pulled back along the proof-theoretic stable quotient.

This is the carrier-correct version of the intertwining equation: start with an
actual derivable proof-tree class, forget only to the global stable quotient, and
then compare with the UEA primitive coproduct.
-/
theorem OudomGuinGrossmanLarssonIntertwiningTarget.apply_derivable
    {DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient}
    {iota : PreLieDifferenceStableQuotient →ₗ[ℤ]
      preLieDifferenceStableQuotientUEA}
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (h :
      OudomGuinGrossmanLarssonIntertwiningTarget DeltaGL iota DeltaOG)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    stableUEATensorMapFromStableQuotient iota
        (DeltaGL (derivableStableQuotientToStableQuotient base q)) =
      DeltaOG
        (iota (derivableStableQuotientToStableQuotient base q)) := by
  have happ := congrArg
    (fun f => f (derivableStableQuotientToStableQuotient base q)) h
  simpa [OudomGuinGrossmanLarssonIntertwiningTarget,
    LinearMap.comp_apply] using happ

theorem OudomGuinGrossmanLarssonIntertwiningTarget.extendsStableQuotientPrimitive
    {DeltaGL :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient}
    {DeltaOG :
      preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor}
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL stableUEACanonicalIota DeltaOG)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive DeltaGL) :
    OudomGuinUEAExtendsStableQuotientPrimitive DeltaOG := by
  rw [OudomGuinUEAExtendsStableQuotientPrimitive_iff_linearMap]
  have hcomp :
      LinearMap.comp DeltaOG stableUEACanonicalIota =
        LinearMap.comp
          (stableUEATensorMapFromStableQuotient stableUEACanonicalIota)
          DeltaGL := by
    simpa [OudomGuinGrossmanLarssonIntertwiningTarget] using hintertwining.symm
  exact hcomp.trans hleft

/--
The UEA-side Hopf carrier target.  This is intentionally not a structure on
`PreLieDifferenceStableQuotient`: the missing unit and counit live naturally in
the UEA, while the quotient appears through the inclusion `stableUEACanonicalIota`.
-/
structure OudomGuinUEAHopfCarrierTarget where
  DeltaGL_unitCompleted :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient
        PreLieDifferenceStableQuotient
  DeltaOG :
    preLieDifferenceStableQuotientUEA →ₗ[ℤ] stableUEATensor
  epsilonOG :
    preLieDifferenceStableQuotientUEA →ₗ[ℤ] ℤ
  primitive_on_treeGen :
    OudomGuinPrimitiveUEAComultiplicationOnGenerators DeltaOG
  counit_on_treeGen :
    ∀ x : PTree, epsilonOG (stableUEA_treeGen x) = 0
  counit_one :
    epsilonOG (1 : preLieDifferenceStableQuotientUEA) = 1
  uea_coalgebra_axioms :
    StableUEACoalgebraAxioms
      ({ comul := DeltaOG, counit := epsilonOG } :
        StableUEAComultiplication)
  gl_og_intertwining :
    OudomGuinGrossmanLarssonIntertwiningTarget
      DeltaGL_unitCompleted stableUEACanonicalIota DeltaOG

/-- Forget the bridge data and keep the actual UEA coalgebra. -/
noncomputable def OudomGuinUEAHopfCarrierTarget.toCoalgebraData
    (H : OudomGuinUEAHopfCarrierTarget) :
    StableUEACoalgebraData where
  Δ := { comul := H.DeltaOG, counit := H.epsilonOG }
  axioms := H.uea_coalgebra_axioms

/--
Build the carrier-correct UEA target from honest UEA coalgebra data, together
with the two proof-theoretic compatibility obligations we still care about:
primitive generators and the GL/OG intertwining equation.
-/
noncomputable def OudomGuinUEAHopfCarrierTarget.ofCoalgebraData
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (D : StableUEACoalgebraData)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators D.Δ.comul)
    (hcounit_on_treeGen :
      ∀ x : PTree, D.Δ.counit (stableUEA_treeGen x) = 0)
    (hcounit_one :
      D.Δ.counit (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota D.Δ.comul) :
    OudomGuinUEAHopfCarrierTarget where
  DeltaGL_unitCompleted := DeltaGL_unitCompleted
  DeltaOG := D.Δ.comul
  epsilonOG := D.Δ.counit
  primitive_on_treeGen := hprim
  counit_on_treeGen := hcounit_on_treeGen
  counit_one := hcounit_one
  uea_coalgebra_axioms := D.axioms
  gl_og_intertwining := hintertwining

@[simp] theorem OudomGuinUEAHopfCarrierTarget.ofCoalgebraData_DeltaOG
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (D : StableUEACoalgebraData)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators D.Δ.comul)
    (hcounit_on_treeGen :
      ∀ x : PTree, D.Δ.counit (stableUEA_treeGen x) = 0)
    (hcounit_one :
      D.Δ.counit (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota D.Δ.comul) :
    (OudomGuinUEAHopfCarrierTarget.ofCoalgebraData
      DeltaGL_unitCompleted D hprim hcounit_on_treeGen hcounit_one
      hintertwining).DeltaOG = D.Δ.comul := by
  rfl

@[simp] theorem OudomGuinUEAHopfCarrierTarget.ofCoalgebraData_epsilonOG
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (D : StableUEACoalgebraData)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators D.Δ.comul)
    (hcounit_on_treeGen :
      ∀ x : PTree, D.Δ.counit (stableUEA_treeGen x) = 0)
    (hcounit_one :
      D.Δ.counit (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota D.Δ.comul) :
    (OudomGuinUEAHopfCarrierTarget.ofCoalgebraData
      DeltaGL_unitCompleted D hprim hcounit_on_treeGen hcounit_one
      hintertwining).epsilonOG = D.Δ.counit := by
  rfl

theorem oudomGuinUEAHopfCarrierTarget_exists_of_coalgebraData
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (D : StableUEACoalgebraData)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators D.Δ.comul)
    (hcounit_on_treeGen :
      ∀ x : PTree, D.Δ.counit (stableUEA_treeGen x) = 0)
    (hcounit_one :
      D.Δ.counit (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota D.Δ.comul) :
    ∃ H : OudomGuinUEAHopfCarrierTarget,
      H.DeltaOG = D.Δ.comul ∧ H.epsilonOG = D.Δ.counit := by
  refine ⟨
    OudomGuinUEAHopfCarrierTarget.ofCoalgebraData
      DeltaGL_unitCompleted D hprim hcounit_on_treeGen hcounit_one
      hintertwining, ?_, ?_⟩
  · rfl
  · rfl

/--
Turn the project-level UEA coalgebra bundle into mathlib's actual coalgebra
class.  This is the formal handoff point from our quotient/UEA construction to
the standard algebraic API.
-/
noncomputable def StableUEACoalgebraData.toMathlibCoalgebra
    (D : StableUEACoalgebraData) :
    Coalgebra ℤ preLieDifferenceStableQuotientUEA where
  comul := D.Δ.comul
  counit := D.Δ.counit
  coassoc := D.axioms.coassoc
  rTensor_counit_comp_comul := D.axioms.rTensor_counit_comp_comul
  lTensor_counit_comp_comul := D.axioms.lTensor_counit_comp_comul

@[simp] theorem StableUEACoalgebraData.toMathlibCoalgebra_comul
    (D : StableUEACoalgebraData) :
    (StableUEACoalgebraData.toMathlibCoalgebra D).comul = D.Δ.comul := by
  rfl

@[simp] theorem StableUEACoalgebraData.toMathlibCoalgebra_counit
    (D : StableUEACoalgebraData) :
    (StableUEACoalgebraData.toMathlibCoalgebra D).counit = D.Δ.counit := by
  rfl

/--
The UEA Hopf-carrier target therefore supplies an honest mathlib coalgebra on
the UEA carrier, not merely a bespoke record of maps.
-/
noncomputable def OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra
    (H : OudomGuinUEAHopfCarrierTarget) :
    Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
  StableUEACoalgebraData.toMathlibCoalgebra H.toCoalgebraData

@[simp] theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    H.toMathlibCoalgebra.comul = H.DeltaOG := by
  change (StableUEACoalgebraData.toMathlibCoalgebra H.toCoalgebraData).comul = H.DeltaOG
  rw [StableUEACoalgebraData.toMathlibCoalgebra_comul]
  rfl

@[simp] theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_counit
    (H : OudomGuinUEAHopfCarrierTarget) :
    H.toMathlibCoalgebra.counit = H.epsilonOG := by
  change (StableUEACoalgebraData.toMathlibCoalgebra H.toCoalgebraData).counit = H.epsilonOG
  rw [StableUEACoalgebraData.toMathlibCoalgebra_counit]
  rfl

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA) =
      H.DeltaOG := by
  simp

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_counit
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    Coalgebra.counit (R := ℤ) (A := preLieDifferenceStableQuotientUEA) =
      H.epsilonOG := by
  simp

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_primitive_treeGen
    (H : OudomGuinUEAHopfCarrierTarget) (x : PTree) :
    H.toMathlibCoalgebra.comul (stableUEA_treeGen x) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  simpa using H.primitive_on_treeGen x

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_counit_treeGen
    (H : OudomGuinUEAHopfCarrierTarget) (x : PTree) :
    H.toMathlibCoalgebra.counit (stableUEA_treeGen x) = 0 := by
  simpa using H.counit_on_treeGen x

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_counit_one
    (H : OudomGuinUEAHopfCarrierTarget) :
    H.toMathlibCoalgebra.counit
        (1 : preLieDifferenceStableQuotientUEA) = 1 := by
  simpa using H.counit_one

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_primitive_treeGen
    (H : OudomGuinUEAHopfCarrierTarget) (x : PTree) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (stableUEA_treeGen x) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  simpa using H.toMathlibCoalgebra_primitive_treeGen x

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_counit_treeGen
    (H : OudomGuinUEAHopfCarrierTarget) (x : PTree) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    Coalgebra.counit (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (stableUEA_treeGen x) = 0 := by
  simpa using H.toMathlibCoalgebra_counit_treeGen x

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_counit_one
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    Coalgebra.counit (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (1 : preLieDifferenceStableQuotientUEA) = 1 := by
  simpa using H.toMathlibCoalgebra_counit_one

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_primitive_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    H.toMathlibCoalgebra.comul
        (derivableStableUEAIota base (derivableStableTreeGen ht)) =
      TensorProduct.tmul ℤ
          (derivableStableUEAIota base (derivableStableTreeGen ht)) 1 +
        TensorProduct.tmul ℤ 1
          (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  simpa using H.toMathlibCoalgebra_primitive_treeGen t

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_counit_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    H.toMathlibCoalgebra.counit
        (derivableStableUEAIota base (derivableStableTreeGen ht)) = 0 := by
  simpa using H.toMathlibCoalgebra_counit_treeGen t

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_primitive_derivableStableTreeGen_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    {t : PTree}
    (ht : DerivableTree base t) :
    H.toMathlibCoalgebra.comul
        (derivableStableUEAIota base'
          (derivableStableQuotientMapBase h (derivableStableTreeGen ht))) =
      TensorProduct.tmul ℤ
          (derivableStableUEAIota base'
            (derivableStableQuotientMapBase h (derivableStableTreeGen ht))) 1 +
        TensorProduct.tmul ℤ 1
          (derivableStableUEAIota base'
            (derivableStableQuotientMapBase h (derivableStableTreeGen ht))) := by
  simpa using
    H.toMathlibCoalgebra_primitive_derivableStableTreeGen
      (derivableTree_mono h ht)

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_counit_derivableStableTreeGen_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    {t : PTree}
    (ht : DerivableTree base t) :
    H.toMathlibCoalgebra.counit
        (derivableStableUEAIota base'
          (derivableStableQuotientMapBase h (derivableStableTreeGen ht))) = 0 := by
  simpa using
    H.toMathlibCoalgebra_counit_derivableStableTreeGen
      (derivableTree_mono h ht)

theorem OudomGuinUEAHopfCarrierTarget.intertwining_mk
    (H : OudomGuinUEAHopfCarrierTarget)
    (a : linearProofTreeCarrier) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted (mkPreLieDifferenceStableQuotient a)) =
      H.DeltaOG
        (stableUEACanonicalIota (mkPreLieDifferenceStableQuotient a)) := by
  exact
    OudomGuinGrossmanLarssonIntertwiningTarget.apply_mk
      H.gl_og_intertwining a

/-- The GL/OG bridge for an arbitrary element of a derivable stable quotient. -/
theorem OudomGuinUEAHopfCarrierTarget.intertwining_derivable
    (H : OudomGuinUEAHopfCarrierTarget)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base q)) =
      H.DeltaOG (derivableStableUEAIota base q) := by
  simpa [derivableStableUEAIota] using
    OudomGuinGrossmanLarssonIntertwiningTarget.apply_derivable
      H.gl_og_intertwining base q

/--
The bridge equation specialized to an actual derivable tree generator.
This is the theorem shape we should use when threading proof trees into the UEA
coalgebra, instead of dropping back to arbitrary raw trees.
-/
theorem OudomGuinUEAHopfCarrierTarget.intertwining_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (mkPreLieDifferenceStableQuotient (treeGen t))) =
      H.DeltaOG
        (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  simpa using
    H.intertwining_derivable base (derivableStableTreeGen ht)

/--
The derivable bridge is invariant under extension of the primitive base
relation.
-/
theorem OudomGuinUEAHopfCarrierTarget.intertwining_derivable_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base'
            (derivableStableQuotientMapBase h q))) =
      H.DeltaOG
        (derivableStableUEAIota base'
          (derivableStableQuotientMapBase h q)) := by
  exact H.intertwining_derivable base'
    (derivableStableQuotientMapBase h q)

/--
Once the unit-completed GL side is known to match the quotient primitive map,
the UEA-side comultiplication extends that primitive map on every stable
quotient class.
-/
theorem OudomGuinUEAHopfCarrierTarget.extendsStableQuotientPrimitive
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted) :
    OudomGuinUEAExtendsStableQuotientPrimitive H.DeltaOG :=
  OudomGuinGrossmanLarssonIntertwiningTarget.extendsStableQuotientPrimitive
    H.gl_og_intertwining hleft

theorem OudomGuinUEAHopfCarrierTarget.extendsStableQuotientPrimitive_apply
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted)
    (q : PreLieDifferenceStableQuotient) :
    H.DeltaOG (stableUEACanonicalIota q) =
      stableUEA_OGPrimitiveComulFromStableQuotient q :=
  H.extendsStableQuotientPrimitive hleft q

theorem OudomGuinUEAHopfCarrierTarget.extendsStableQuotientPrimitive_derivable
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    H.DeltaOG (derivableStableUEAIota base q) =
      stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q) :=
  OudomGuinUEAExtendsStableQuotientPrimitive.apply_derivable
    (H.extendsStableQuotientPrimitive hleft) base q

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_extendsStableQuotientPrimitive_derivable
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    H.toMathlibCoalgebra.comul (derivableStableUEAIota base q) =
      stableUEA_OGPrimitiveComultiplicationCanonical.comul
        (derivableStableQuotientToStableQuotient base q) := by
  simpa using
    H.extendsStableQuotientPrimitive_derivable hleft base q

/--
The UEA coalgebra target induces a UEA-valued comultiplication on each
proof-theoretic derivable quotient fiber.
-/
noncomputable def OudomGuinUEAHopfCarrierTarget.derivableComul
    (H : OudomGuinUEAHopfCarrierTarget)
    (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ] stableUEATensor :=
  H.DeltaOG.comp (derivableStableUEAIota base)

/--
The UEA coalgebra target induces a counit on each proof-theoretic derivable
quotient fiber.
-/
noncomputable def OudomGuinUEAHopfCarrierTarget.derivableCounit
    (H : OudomGuinUEAHopfCarrierTarget)
    (base : BaseRel) :
    DerivablePreLieStableQuotient base →ₗ[ℤ] ℤ :=
  H.epsilonOG.comp (derivableStableUEAIota base)

theorem OudomGuinUEAHopfCarrierTarget.derivableComul_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    H.derivableComul base' (derivableStableQuotientMapBase h q) =
      H.derivableComul base q := by
  simp [OudomGuinUEAHopfCarrierTarget.derivableComul,
    derivableStableUEAIota_mapBase h q]

theorem OudomGuinUEAHopfCarrierTarget.derivableCounit_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    H.derivableCounit base' (derivableStableQuotientMapBase h q) =
      H.derivableCounit base q := by
  simp [OudomGuinUEAHopfCarrierTarget.derivableCounit,
    derivableStableUEAIota_mapBase h q]

theorem OudomGuinUEAHopfCarrierTarget.derivableComul_eq_primitive
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted)
    (base : BaseRel) :
    H.derivableComul base =
      derivableStableOGPrimitiveComul base := by
  apply LinearMap.ext
  intro q
  exact H.extendsStableQuotientPrimitive_derivable hleft base q

theorem OudomGuinUEAHopfCarrierTarget.derivableComul_apply
    (H : OudomGuinUEAHopfCarrierTarget)
    (hleft :
      GrossmanLarssonUnitCompletedAgreesWithOGPrimitive
        H.DeltaGL_unitCompleted)
    {base : BaseRel}
    (q : DerivablePreLieStableQuotient base) :
    H.derivableComul base q =
      TensorProduct.tmul ℤ (derivableStableUEAIota base q) 1 +
        TensorProduct.tmul ℤ 1 (derivableStableUEAIota base q) := by
  rw [H.derivableComul_eq_primitive hleft base]
  exact derivableStableOGPrimitiveComul_apply q

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_intertwining_mk
    (H : OudomGuinUEAHopfCarrierTarget)
    (a : linearProofTreeCarrier) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted (mkPreLieDifferenceStableQuotient a)) =
      H.toMathlibCoalgebra.comul
        (stableUEACanonicalIota (mkPreLieDifferenceStableQuotient a)) := by
  simpa using H.intertwining_mk a

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_intertwining_derivable
    (H : OudomGuinUEAHopfCarrierTarget)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base q)) =
      H.toMathlibCoalgebra.comul (derivableStableUEAIota base q) := by
  simpa using H.intertwining_derivable base q

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_intertwining_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (mkPreLieDifferenceStableQuotient (treeGen t))) =
      H.toMathlibCoalgebra.comul
        (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  simpa using H.intertwining_derivableStableTreeGen ht

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_intertwining_derivable_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base'
            (derivableStableQuotientMapBase h q))) =
      H.toMathlibCoalgebra.comul
        (derivableStableUEAIota base'
          (derivableStableQuotientMapBase h q)) := by
  simpa using H.intertwining_derivable_mapBase h q

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_intertwining_mk
    (H : OudomGuinUEAHopfCarrierTarget)
    (a : linearProofTreeCarrier) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted (mkPreLieDifferenceStableQuotient a)) =
      Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (stableUEACanonicalIota (mkPreLieDifferenceStableQuotient a)) := by
  simpa using H.toMathlibCoalgebra_intertwining_mk a

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_intertwining_derivable
    (H : OudomGuinUEAHopfCarrierTarget)
    (base : BaseRel)
    (q : DerivablePreLieStableQuotient base) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base q)) =
      Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (derivableStableUEAIota base q) := by
  simpa using H.toMathlibCoalgebra_intertwining_derivable base q

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_intertwining_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (mkPreLieDifferenceStableQuotient (treeGen t))) =
      Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  simpa using H.toMathlibCoalgebra_intertwining_derivableStableTreeGen ht

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_intertwining_derivable_mapBase
    (H : OudomGuinUEAHopfCarrierTarget)
    {base base' : BaseRel}
    (h : BaseRelExtends base base')
    (q : DerivablePreLieStableQuotient base) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    stableUEATensorMapFromStableQuotient stableUEACanonicalIota
        (H.DeltaGL_unitCompleted
          (derivableStableQuotientToStableQuotient base'
            (derivableStableQuotientMapBase h q))) =
      Coalgebra.comul (R := ℤ) (A := preLieDifferenceStableQuotientUEA)
        (derivableStableUEAIota base'
          (derivableStableQuotientMapBase h q)) := by
  simpa using H.toMathlibCoalgebra_intertwining_derivable_mapBase h q

theorem OudomGuinUEAHopfCarrierTarget.primitive_treeGen
    (H : OudomGuinUEAHopfCarrierTarget) (x : PTree) :
    H.DeltaOG (stableUEA_treeGen x) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  H.primitive_on_treeGen x

theorem OudomGuinUEAHopfCarrierTarget.primitive_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    H.DeltaOG (derivableStableUEAIota base (derivableStableTreeGen ht)) =
      TensorProduct.tmul ℤ
          (derivableStableUEAIota base (derivableStableTreeGen ht)) 1 +
        TensorProduct.tmul ℤ 1
          (derivableStableUEAIota base (derivableStableTreeGen ht)) := by
  simpa using H.primitive_treeGen t

theorem OudomGuinUEAHopfCarrierTarget.counit_derivableStableTreeGen
    (H : OudomGuinUEAHopfCarrierTarget)
    {base : BaseRel} {t : PTree}
    (ht : DerivableTree base t) :
    H.epsilonOG (derivableStableUEAIota base (derivableStableTreeGen ht)) = 0 := by
  simpa using H.counit_on_treeGen t

theorem OudomGuinUEAHopfCarrierTarget.coassoc
    (H : OudomGuinUEAHopfCarrierTarget) :
    (TensorProduct.assoc ℤ
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA).toLinearMap ∘ₗ
        (H.DeltaOG.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ
          H.DeltaOG =
      (H.DeltaOG.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ
        H.DeltaOG :=
  H.uea_coalgebra_axioms.coassoc

theorem OudomGuinUEAHopfCarrierTarget.rTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    (H.epsilonOG.rTensor preLieDifferenceStableQuotientUEA) ∘ₗ
        H.DeltaOG =
      TensorProduct.mk ℤ _ _ 1 :=
  H.uea_coalgebra_axioms.rTensor_counit_comp_comul

theorem OudomGuinUEAHopfCarrierTarget.lTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    (H.epsilonOG.lTensor preLieDifferenceStableQuotientUEA) ∘ₗ
        H.DeltaOG =
      (TensorProduct.mk ℤ _ _).flip 1 :=
  H.uea_coalgebra_axioms.lTensor_counit_comp_comul

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_coassoc
    (H : OudomGuinUEAHopfCarrierTarget) :
    (TensorProduct.assoc ℤ
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA).toLinearMap ∘ₗ
        (H.toMathlibCoalgebra.comul.rTensor
          preLieDifferenceStableQuotientUEA) ∘ₗ
          H.toMathlibCoalgebra.comul =
      (H.toMathlibCoalgebra.comul.lTensor
          preLieDifferenceStableQuotientUEA) ∘ₗ
        H.toMathlibCoalgebra.comul := by
  simpa using H.coassoc

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_rTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    (H.toMathlibCoalgebra.counit.rTensor
        preLieDifferenceStableQuotientUEA) ∘ₗ
        H.toMathlibCoalgebra.comul =
      TensorProduct.mk ℤ _ _ 1 := by
  simpa using H.rTensor_counit_comp_comul

theorem OudomGuinUEAHopfCarrierTarget.toMathlibCoalgebra_lTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    (H.toMathlibCoalgebra.counit.lTensor
        preLieDifferenceStableQuotientUEA) ∘ₗ
        H.toMathlibCoalgebra.comul =
      (TensorProduct.mk ℤ _ _).flip 1 := by
  simpa using H.lTensor_counit_comp_comul

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_coassoc
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    (TensorProduct.assoc ℤ
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA
        preLieDifferenceStableQuotientUEA).toLinearMap ∘ₗ
        ((Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)).rTensor
          preLieDifferenceStableQuotientUEA) ∘ₗ
          Coalgebra.comul (R := ℤ)
            (A := preLieDifferenceStableQuotientUEA) =
      ((Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)).lTensor
          preLieDifferenceStableQuotientUEA) ∘ₗ
        Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA) := by
  simpa using H.toMathlibCoalgebra_coassoc

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_rTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    ((Coalgebra.counit (R := ℤ)
        (A := preLieDifferenceStableQuotientUEA)).rTensor
        preLieDifferenceStableQuotientUEA) ∘ₗ
        Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA) =
      TensorProduct.mk ℤ _ _ 1 := by
  simpa using H.toMathlibCoalgebra_rTensor_counit_comp_comul

theorem OudomGuinUEAHopfCarrierTarget.asMathlibCoalgebra_lTensor_counit_comp_comul
    (H : OudomGuinUEAHopfCarrierTarget) :
    letI : Coalgebra ℤ preLieDifferenceStableQuotientUEA :=
      H.toMathlibCoalgebra
    ((Coalgebra.counit (R := ℤ)
        (A := preLieDifferenceStableQuotientUEA)).lTensor
        preLieDifferenceStableQuotientUEA) ∘ₗ
        Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA) =
      (TensorProduct.mk ℤ _ _).flip 1 := by
  simpa using H.toMathlibCoalgebra_lTensor_counit_comp_comul

/--
Construct the UEA Hopf-carrier target from an actual mathlib coalgebra
instance on the UEA carrier, plus the primitive-generator and GL/OG bridge
conditions.  This is the cleanest endpoint for the coalgebra part: the carrier
is the UEA, and the remaining proof-theoretic information is explicit data.
-/
noncomputable def OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra
    [Coalgebra ℤ preLieDifferenceStableQuotientUEA]
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)))
    (hcounit_on_treeGen :
      ∀ x : PTree,
        Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (stableUEA_treeGen x) = 0)
    (hcounit_one :
      Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA))) :
    OudomGuinUEAHopfCarrierTarget :=
  OudomGuinUEAHopfCarrierTarget.ofCoalgebraData
    DeltaGL_unitCompleted
    stableUEACoalgebraData_ofCoalgebra
    (by
      simpa [stableUEACoalgebraData_ofCoalgebra,
        stableUEAComultiplication_ofCoalgebra] using hprim)
    (by
      simpa [stableUEACoalgebraData_ofCoalgebra,
        stableUEAComultiplication_ofCoalgebra] using hcounit_on_treeGen)
    (by
      simpa [stableUEACoalgebraData_ofCoalgebra,
        stableUEAComultiplication_ofCoalgebra] using hcounit_one)
    (by
      simpa [stableUEACoalgebraData_ofCoalgebra,
        stableUEAComultiplication_ofCoalgebra] using hintertwining)

@[simp] theorem OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra_DeltaOG
    [Coalgebra ℤ preLieDifferenceStableQuotientUEA]
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)))
    (hcounit_on_treeGen :
      ∀ x : PTree,
        Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (stableUEA_treeGen x) = 0)
    (hcounit_one :
      Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA))) :
    (OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra
      DeltaGL_unitCompleted hprim hcounit_on_treeGen hcounit_one
      hintertwining).DeltaOG =
        Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA) := by
  rfl

@[simp] theorem OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra_epsilonOG
    [Coalgebra ℤ preLieDifferenceStableQuotientUEA]
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)))
    (hcounit_on_treeGen :
      ∀ x : PTree,
        Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (stableUEA_treeGen x) = 0)
    (hcounit_one :
      Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA))) :
    (OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra
      DeltaGL_unitCompleted hprim hcounit_on_treeGen hcounit_one
      hintertwining).epsilonOG =
        Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA) := by
  rfl

theorem oudomGuinUEAHopfCarrierTarget_exists_of_mathlibCoalgebra
    [Coalgebra ℤ preLieDifferenceStableQuotientUEA]
    (DeltaGL_unitCompleted :
      PreLieDifferenceStableQuotient →ₗ[ℤ]
        TensorProduct ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient)
    (hprim :
      OudomGuinPrimitiveUEAComultiplicationOnGenerators
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)))
    (hcounit_on_treeGen :
      ∀ x : PTree,
        Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (stableUEA_treeGen x) = 0)
    (hcounit_one :
      Coalgebra.counit (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA)
          (1 : preLieDifferenceStableQuotientUEA) = 1)
    (hintertwining :
      OudomGuinGrossmanLarssonIntertwiningTarget
        DeltaGL_unitCompleted stableUEACanonicalIota
        (Coalgebra.comul (R := ℤ)
          (A := preLieDifferenceStableQuotientUEA))) :
    ∃ H : OudomGuinUEAHopfCarrierTarget,
      H.DeltaOG =
          Coalgebra.comul (R := ℤ)
            (A := preLieDifferenceStableQuotientUEA) ∧
        H.epsilonOG =
          Coalgebra.counit (R := ℤ)
            (A := preLieDifferenceStableQuotientUEA) := by
  refine ⟨
    OudomGuinUEAHopfCarrierTarget.ofMathlibCoalgebra
      DeltaGL_unitCompleted hprim hcounit_on_treeGen hcounit_one
      hintertwining, ?_, ?_⟩
  · rfl
  · rfl

/--
Main UEA Hopf-carrier existence target.  This is the architectural replacement
for further quotient-counit obstruction examples.
-/
theorem oudomGuinUEAHopfCarrierTarget_exists :
    ∃ _H : OudomGuinUEAHopfCarrierTarget, True := by
  sorry

end OudomGuinBridgeTarget

/-! ## 7. Instantiation of the coalgebra axioms structure

We package the coassociativity result (and placeholder counit axioms) into
`CoproductSupportQuotientCoalgebraAxioms`.
-/

section CoalgebraAxioms

/--
The coassociativity axiom for the descended coalgebra, expressed as an
equality of linear maps.
-/
theorem coproductSupportSummary_quotientCoalgebraAxioms_coassoc :
    LinearMap.comp
        (LinearMap.comp
          (TensorProduct.assoc ℤ
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient
            PreLieDifferenceStableQuotient).toLinearMap
          (LinearMap.rTensor
            PreLieDifferenceStableQuotient
            (coproductSupportSummary_comul_quot h_respects)))
        (coproductSupportSummary_comul_quot h_respects) =
      LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h_respects))
        (coproductSupportSummary_comul_quot h_respects) := by
  -- This is exactly `left_assoc = left` unfolded.
  change coproductSupportSummary_comul_quot_left_assoc h_respects =
         coproductSupportSummary_comul_quot_left h_respects
  exact coproductSupportSummary_comul_quot_coassoc.symm

end CoalgebraAxioms

/-! ## 7. Counit descent is zero -/

section CounitDescentZero

/--
Since `coproductSupportSummary_counit_linear` is identically zero, so is the
descended counit on the quotient.
-/
theorem coproductSupportSummary_counit_descend_eq_zero :
    coproductSupportSummary_counit_descend h_respects = 0 := by
  apply LinearMap.ext
  intro a
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    change
      coproductSupportSummary_counit_descend h_respects
          (mkPreLieDifferenceStableQuotient a) = 0
    rw [coproductSupportSummary_counit_descend_mk]
    exact congrFun (congrArg DFunLike.coe coproductSupportSummary_counit_linear_eq_zero) a

end CounitDescentZero

/-! ## 8. Counit axioms
Note: the counit axioms (`rTensor_counit_comp_comul`, `lTensor_counit_comp_comul`)
require the counit to be the map `ε(t) = 1` on the identity cut `([], t)`.
The current placeholder definition has both branches returning `0`, making the
counit identically zero and the standard coalgebra counit laws false as stated.
These are therefore `sorry`'d pending a correction of the counit definition in
`GrossmanLarssonOudomGuin.lean`.
-/

section CounitAxioms

/--
With the current placeholder counit, the right counit composite is literally
the zero map.
-/
theorem coproductSupportSummary_rTensor_counit_comp_comul_eq_zero :
    LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h_respects))
        (coproductSupportSummary_comul_quot h_respects) = 0 := by
  rw [coproductSupportSummary_counit_descend_eq_zero]
  simp

/--
With the current placeholder counit, the left counit composite is literally
the zero map.
-/
theorem coproductSupportSummary_lTensor_counit_comp_comul_eq_zero :
    LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h_respects))
        (coproductSupportSummary_comul_quot h_respects) = 0 := by
  rw [coproductSupportSummary_counit_descend_eq_zero]
  simp

/--
Right counit law: `(ε ⊗ id) ∘ Δ = (1 ⊗ -)`.
`sorry`'d: requires the counit to pick out the `1` on the empty-forest cut
rather than returning `0`.
-/
theorem coproductSupportSummary_rTensor_counit_comp_comul :
    LinearMap.comp
        (LinearMap.rTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h_respects))
        (coproductSupportSummary_comul_quot h_respects) =
      TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1 := by
  sorry

/--
Left counit law: `(id ⊗ ε) ∘ Δ = (- ⊗ 1)`.
`sorry`'d: same reason as `coproductSupportSummary_rTensor_counit_comp_comul`.
-/
theorem coproductSupportSummary_lTensor_counit_comp_comul :
    LinearMap.comp
        (LinearMap.lTensor
          PreLieDifferenceStableQuotient
          (coproductSupportSummary_counit_descend h_respects))
        (coproductSupportSummary_comul_quot h_respects) =
      (TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1 := by
  sorry

end CounitAxioms

/-! ## 9. Full quotient coalgebra instance -/

section CoalgebraInstance

/--
The full bundle of quotient coalgebra axioms for `coproductSupportSummary_coalgebraData`.
- `coassoc` is proved in Section 6 (modulo the two sorry'd combinatorial
  bijections in Section 5).
- The counit laws are `sorry`'d pending a correct counit definition.
-/
noncomputable def coproductSupportSummary_quotientCoalgebraAxiomsFull :
    CoproductSupportQuotientCoalgebraAxioms h_respects where
  coassoc := coproductSupportSummary_quotientCoalgebraAxioms_coassoc
  rTensor_counit_comp_comul := coproductSupportSummary_rTensor_counit_comp_comul
  lTensor_counit_comp_comul := coproductSupportSummary_lTensor_counit_comp_comul

/--
The full descended quotient coalgebra: the free pre-Lie module quotiented by
the stable pre-Lie defect submodule, equipped with the Grossman–Larsson
coproduct and counit.
-/
noncomputable def coproductSupportQuotientCoalgebraInst :
    CoproductSupportQuotientCoalgebra where
  h := h_respects
  axioms := coproductSupportSummary_quotientCoalgebraAxiomsFull

end CoalgebraInstance

/-! ## 10. Concrete sum-7 and sum-8 expansion lemmas

We continue the pattern from `GrossmanLarssonOudomGuin.lean` (which goes up to
N = 6) for the three families of iterated-coproduct expansion lemmas.
-/

section SumExpansions

/-! ### sum_seven -/

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_seven
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have htuv6z :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
          (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using htuv6z
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_left_treeGen_sum_six,
        coproductSupportSummary_comul_quot_left_treeGen_sum]

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_seven
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have htuv6z :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
          (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_right_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using htuv6z
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_right_treeGen_sum_six,
        coproductSupportSummary_comul_quot_right_treeGen_sum]

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_seven
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum t coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum u coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum v coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum w coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum x coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum y coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum z coproductSupportSummary_tensorGen))) := by
  have htuv6z :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
          (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [htuv6z,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_six,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

/-! ### coassoc sum_seven (from instance) -/

theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_seven_explicit
    (H : CoproductSupportQuotientCoalgebra) (t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)))

end SumExpansions

/-! ## 11. `comul_treeGen_sum_N` for N = 5, 6 via our instance

The main file only provides `comul_treeGen_sum_four`; we extend the pattern.
-/

section ComulTreeGenSumN

/-- Linearity of `comul` on a sum of five tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_five
    (H : CoproductSupportQuotientCoalgebra) (v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen v)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient
          ((treeGen v + treeGen w + treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk (treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
  simpa [add_assoc, H.comul_treeGen_sum_four] using h1

/-- Linearity of `comul` on a sum of six tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_six
    (H : CoproductSupportQuotientCoalgebra) (u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen u)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen v)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient
          ((treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
  simpa [add_assoc, H.comul_treeGen_sum_five] using h1

/-- Linearity of `comul` on a sum of seven tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_seven
    (H : CoproductSupportQuotientCoalgebra) (t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen t + treeGen u + treeGen v + treeGen w +
         treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen t)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen u)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen v)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient
          ((treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
           treeGen x + treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [add_assoc, H.comul_treeGen_sum_six] using h1

end ComulTreeGenSumN

/-! ## 12. Concrete consequences via `coproductSupportQuotientCoalgebraInst`

Instantiate the `coassoc` and `comul` results using our specific instance.
-/

section ConcreteConsequences

/-- The coassociativity of our specific instance (unfolds to `coassoc_shorthand`). -/
theorem instance_coassoc_shorthand :
    coproductSupportSummary_comul_quot_left_assoc h_respects =
      coproductSupportSummary_comul_quot_left h_respects :=
  coproductSupportQuotientCoalgebraInst.coassoc_shorthand

/-- The coassociativity on a tree generator via our specific instance. -/
theorem instance_coassoc_treeGen (x : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) :=
  coproductSupportQuotientCoalgebraInst.coassoc_shorthand_treeGen x

/-- The comultiplication on tree generators via our specific instance. -/
theorem instance_comul_treeGen (x : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) :=
  coproductSupportQuotientCoalgebraInst.comul_treeGen x

/-- The counit is zero on all generators via our specific instance. -/
theorem instance_counit_treeGen_zero (x : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 :=
  coproductSupportQuotientCoalgebraInst.counit_treeGen x

/-- Coassociativity sum-seven via our specific instance. -/
theorem instance_coassoc_sum_seven (t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
           treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
           treeGen x + treeGen y + treeGen z)) :=
  coproductSupportQuotientCoalgebraInst.coassoc_treeGen_sum_seven_explicit t u v w x y z

end ConcreteConsequences

/-! ## 13. `comul_treeGen_sum_N_tensor` forms and sum_eight expansions -/

section SumEightExpansions

/-- Tensor form of `comul` on a sum of five tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_five_tensor
    (H : CoproductSupportQuotientCoalgebra) (v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen v)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_five, H.comul_treeGen]

/-- Tensor form of `comul` on a sum of six tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_six_tensor
    (H : CoproductSupportQuotientCoalgebra) (u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen u)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen v)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_six, H.comul_treeGen]

/-- Tensor form of `comul` on a sum of seven tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_seven_tensor
    (H : CoproductSupportQuotientCoalgebra) (t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen t + treeGen u + treeGen v + treeGen w +
         treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen t)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen u)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen v)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_seven, H.comul_treeGen]

/-- Linearity of `comul` on a sum of eight tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_eight
    (H : CoproductSupportQuotientCoalgebra) (s t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen s)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen t)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen u)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen v)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient
          ((treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [add_assoc, H.comul_treeGen_sum_seven] using h1

/-! ### sum_eight for the three expansion families -/

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_eight
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum s coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have hstuvwxyz :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hstuvwxyz
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_left_treeGen_sum_seven,
        coproductSupportSummary_comul_quot_left_treeGen_sum]

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_eight
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum s coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have hstuvwxyz :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_right_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hstuvwxyz
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_right_treeGen_sum_seven,
        coproductSupportSummary_comul_quot_right_treeGen_sum]

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_eight
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum s coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum t coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum u coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum v coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum w coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum x coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum y coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum z coproductSupportSummary_tensorGen))) := by
  have hstuvwxyz :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [hstuvwxyz,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_seven,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

/-- Coassociativity on a sum of eight generators via our instance. -/
theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_eight_explicit
    (H : CoproductSupportQuotientCoalgebra) (s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)))

end SumEightExpansions

/-! ## 14. Corrected counit

The counit `coproductSupportSummary_counit_linear` in the main file has a bug:
both branches of its defining `if` return `0`, making it the zero map.  The
*correct* GL counit should map every tree generator to `0` (trees are primitive,
not the unit) — but more precisely, in the Finsupp encoding the correct counit
is the one that picks out the coefficient of the trivial cut `([], t)`, which
is `1` per tree generator.

We define the corrected counit here as the "sum of all coefficients" map on
`linearProofTreeCarrier = PTree →₀ ℤ`, i.e. the unique linear extension of
`treeGen t ↦ 1`.  We show it kills every pre-Lie difference generator (by a
symmetric leaf-count identity) and every element of `preLieDifferenceSubmodule`,
then descend it to the stable quotient.

### Why the leaf-count argument works

For trees `x y z`, write `a = |leaves x|`, `b = |leaves y|`, `c = |leaves z|`.
The total coefficient of `comparisonSideGenerators x y z` in the PTree basis
equals `c(b+c-1)(a+b+c-2) + ac(a+b+c-2)`, and that of
`swappedComparisonSideGenerators x y z` equals `c(a+c-1)(a+b+c-2) + bc(a+b+c-2)`.
The difference is `(a+b+c-2)·c·[(b+c-1)+a-(a+c-1)-b] = (a+b+c-2)·c·0 = 0`.
-/

section CorrectedCounit

/--
The corrected counit: the unique `ℤ`-linear map extending `treeGen t ↦ 1`.

Equivalently this is the "sum of all coefficients in the PTree basis" map.
It differs from `coproductSupportSummary_counit_linear`, which is identically
zero due to a bug in the main file's definition.
-/
noncomputable def correctedCounit_linear : linearProofTreeCarrier →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ (fun _ : PTree => LinearMap.id)

/-- The corrected counit maps every tree generator to `1`. -/
@[simp] theorem correctedCounit_linear_treeGen (t : PTree) :
    correctedCounit_linear (treeGen t) = 1 := by
  simp [correctedCounit_linear, treeGen, Finsupp.lsum_single, LinearMap.id_apply]

@[simp] theorem correctedCounit_linear_add (a b : linearProofTreeCarrier) :
    correctedCounit_linear (a + b) = correctedCounit_linear a + correctedCounit_linear b :=
  map_add _ _ _

@[simp] theorem correctedCounit_linear_sub (a b : linearProofTreeCarrier) :
    correctedCounit_linear (a - b) = correctedCounit_linear a - correctedCounit_linear b :=
  map_sub _ _ _

@[simp] theorem correctedCounit_linear_smul (n : ℤ) (a : linearProofTreeCarrier) :
    correctedCounit_linear (n • a) = n * correctedCounit_linear a := by
  have := correctedCounit_linear.map_smul n a
  simpa [smul_eq_mul] using this

/-- The corrected counit is the sum of all coefficients of `a` in the PTree basis. -/
theorem correctedCounit_linear_apply (a : linearProofTreeCarrier) :
    correctedCounit_linear a = Finsupp.sum a (fun _ c => c) := by
  simp [correctedCounit_linear, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.id_apply]

/-- The corrected counit is zero on the zero element. -/
@[simp] theorem correctedCounit_linear_zero :
    correctedCounit_linear (0 : linearProofTreeCarrier) = 0 :=
  map_zero _

/-- The corrected counit counts generators in any explicit tree-sum fold. -/
theorem correctedCounit_linear_foldr_treeGen_length
    (xs : List PTree) :
    correctedCounit_linear (xs.foldr (fun x acc => treeGen x + acc) 0) =
      (xs.length : Int) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [correctedCounit_linear_add, add_comm] using
        congrArg (fun n : Int => 1 + n) ih

/--
The corrected counit of the tree-level grafting product counts matching
leaf-grafting sites.
-/
theorem correctedCounit_linear_graftPreLieTree
    (u t : PTree) :
    correctedCounit_linear (PTree.graftPreLieTree u t) =
      (PTree.matchingLeafGraftings u t).length := by
  simp [PTree.graftPreLieTree, correctedCounit_linear_foldr_treeGen_length]

/-- Folding graftings on the right counts the total number of resulting trees. -/
theorem correctedCounit_linear_foldr_graftPreLieTree_right_length
    (x : PTree) (zs : List PTree) :
    correctedCounit_linear (zs.foldr (fun z' acc => PTree.graftPreLieTree x z' + acc) 0) =
      ((zs.map (fun z' => (PTree.matchingLeafGraftings x z').length)).sum : Int) := by
  induction zs with
  | nil =>
      simp
  | cons z' zs ih =>
      simp [correctedCounit_linear_add, correctedCounit_linear_graftPreLieTree, ih]

/-- Folding graftings on the left counts the total number of resulting trees. -/
theorem correctedCounit_linear_foldr_graftPreLieTree_left_length
    (z : PTree) (ys : List PTree) :
    correctedCounit_linear (ys.foldr (fun y' acc => PTree.graftPreLieTree y' z + acc) 0) =
      ((ys.map (fun y' => (PTree.matchingLeafGraftings y' z).length)).sum : Int) := by
  induction ys with
  | nil =>
      simp
  | cons y' ys ih =>
      simp [correctedCounit_linear_add, correctedCounit_linear_graftPreLieTree, ih]

/--
On a generator grafted onto a tree-level grafting product, the corrected
counit counts the resulting two-step graft list.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_graftPreLieTree
    (x y z : PTree) :
    correctedCounit_linear (graftPreLie (treeGen x) (PTree.graftPreLieTree y z)) =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length : Nat) : Int) := by
  rw [graftPreLie_tree_tree_apply]
  simp only [graftPreLie_on_generators]
  simpa using
    correctedCounit_linear_foldr_graftPreLieTree_right_length
      x (PTree.matchingLeafGraftings y z)

/--
On a tree-level grafting product grafted onto a generator, the corrected
counit counts the corresponding two-step graft list.
-/
theorem correctedCounit_linear_graftPreLie_graftPreLieTree_treeGen
    (x y z : PTree) :
    correctedCounit_linear (graftPreLie (PTree.graftPreLieTree x y) (treeGen z)) =
      ((((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length : Nat) : Int) := by
  rw [graftPreLie_tree_tree_apply_left]
  simp only [graftPreLie_on_generators]
  simpa using
    correctedCounit_linear_foldr_graftPreLieTree_left_length
      z (PTree.matchingLeafGraftings x y)

/--
Left-grafting a generator onto a fold of tree-level grafting products counts
all resulting two-stage outputs from the right-grafting family.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_foldr_graftPreLieTree_right_length
    (u x : PTree) (zs : List PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u)
          (zs.foldr (fun z' acc => PTree.graftPreLieTree x z' + acc) 0)) =
      ((zs.map (fun z' =>
          ((PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t)).length)).sum : Int) := by
  induction zs with
  | nil =>
      simp
  | cons z' zs ih =>
      simp [correctedCounit_linear_add,
        correctedCounit_linear_graftPreLie_treeGen_graftPreLieTree, ih]

/--
Left-grafting a generator onto a fold of tree-level grafting products counts
all resulting two-stage outputs from the left-grafting family.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_foldr_graftPreLieTree_left_length
    (u z : PTree) (ys : List PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u)
          (ys.foldr (fun y' acc => PTree.graftPreLieTree y' z + acc) 0)) =
      ((ys.map (fun y' =>
          ((PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t)).length)).sum : Int) := by
  induction ys with
  | nil =>
      simp
  | cons y' ys ih =>
      simp [correctedCounit_linear_add,
        correctedCounit_linear_graftPreLie_treeGen_graftPreLieTree, ih]

/--
Applying one more left graft to `x ▷ (y ▷ z)` counts the corresponding
three-stage raw graft list.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_graftPreLie_treeGen_graftPreLieTree
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u)
          (graftPreLie (treeGen x) (PTree.graftPreLieTree y z))) =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length : Nat) : Int) := by
  rw [graftPreLie_tree_tree_apply]
  simp only [graftPreLie_on_generators]
  simpa [List.length_flatMap] using
    correctedCounit_linear_graftPreLie_treeGen_foldr_graftPreLieTree_right_length
      u x (PTree.matchingLeafGraftings y z)

/--
Applying one more left graft to `(x ▷ y) ▷ z` counts the corresponding
three-stage raw graft list.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_graftPreLie_graftPreLieTree_treeGen
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u)
          (graftPreLie (PTree.graftPreLieTree x y) (treeGen z))) =
      ((((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length : Nat) : Int) := by
  rw [graftPreLie_tree_tree_apply_left]
  simp only [graftPreLie_on_generators]
  simpa [List.length_flatMap] using
    correctedCounit_linear_graftPreLie_treeGen_foldr_graftPreLieTree_left_length
      u z (PTree.matchingLeafGraftings x y)

/--
The corrected counit on the concrete `A + D` comparison side is the total
length of its two contributing two-step graft lists.
-/
theorem correctedCounit_linear_comparisonSideGenerators
    (x y z : PTree) :
    correctedCounit_linear (comparisonSideGenerators x y z) =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat) : Int) := by
  simp [comparisonSideGenerators,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLieTree,
    correctedCounit_linear_graftPreLie_graftPreLieTree_treeGen,
    Nat.cast_add]

/--
The corrected counit on the swapped `B + C` comparison side is the total
length of its two contributing two-step graft lists.
-/
theorem correctedCounit_linear_swappedComparisonSideGenerators
    (x y z : PTree) :
    correctedCounit_linear (swappedComparisonSideGenerators x y z) =
      ((((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat) : Int) := by
  simp [swappedComparisonSideGenerators,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLieTree,
    correctedCounit_linear_graftPreLie_graftPreLieTree_treeGen,
    Nat.cast_add]

/--
The corrected counit on `u ▷ (A + D)` is the total length of the two concrete
three-stage graft lists obtained from the comparison side.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_comparisonSideGenerators
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (comparisonSideGenerators x y z)) =
      ((((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat) : Int) := by
  simp [comparisonSideGenerators,
    correctedCounit_linear_add,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLie_treeGen_graftPreLieTree,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLie_graftPreLieTree_treeGen,
    Nat.cast_add]

/--
The corrected counit on `u ▷ (C + B)` is the total length of the two concrete
three-stage graft lists obtained from the swapped comparison side.
-/
theorem correctedCounit_linear_graftPreLie_treeGen_swappedComparisonSideGenerators
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (swappedComparisonSideGenerators x y z)) =
      ((((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat) : Int) := by
  simp [swappedComparisonSideGenerators,
    correctedCounit_linear_add,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLie_treeGen_graftPreLieTree,
    correctedCounit_linear_graftPreLie_treeGen_graftPreLie_graftPreLieTree_treeGen,
    Nat.cast_add]

/--
The raw two-step output list on the `A + D` side of the generator-level
comparison.
-/
def preLieDifferenceGeneratorFlatmapLeft (x y z : PTree) : List PTree :=
  ((PTree.matchingLeafGraftings y z).flatMap
      (fun z' => PTree.matchingLeafGraftings x z'))
    ++
    ((PTree.matchingLeafGraftings y x).flatMap
      (fun y' => PTree.matchingLeafGraftings y' z))

/--
The raw two-step output list on the `C + B` side of the generator-level
comparison.
-/
def preLieDifferenceGeneratorFlatmapRight (x y z : PTree) : List PTree :=
  ((PTree.matchingLeafGraftings x z).flatMap
      (fun z' => PTree.matchingLeafGraftings y z'))
    ++
    ((PTree.matchingLeafGraftings x y).flatMap
      (fun y' => PTree.matchingLeafGraftings y' z))

/--
The raw three-step output list on the left side after grafting once more by a
tree generator.
-/
def graftPreLieDifferenceGeneratorFlatmapLeft
    (u x y z : PTree) : List PTree :=
  ((PTree.matchingLeafGraftings y z).flatMap
      (fun z' => (PTree.matchingLeafGraftings x z').flatMap
        (fun t => PTree.matchingLeafGraftings u t)))
    ++
    ((PTree.matchingLeafGraftings y x).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
        (fun t => PTree.matchingLeafGraftings u t)))

/--
The raw three-step output list on the right side after grafting once more by a
tree generator.
-/
def graftPreLieDifferenceGeneratorFlatmapRight
    (u x y z : PTree) : List PTree :=
  ((PTree.matchingLeafGraftings x z).flatMap
      (fun z' => (PTree.matchingLeafGraftings y z').flatMap
        (fun t => PTree.matchingLeafGraftings u t)))
    ++
    ((PTree.matchingLeafGraftings x y).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
        (fun t => PTree.matchingLeafGraftings u t)))

/--
Pointwise multiplicity balance for the two named raw two-step output lists.
-/
def PreLieDifferenceGeneratorFlatmapCountBalanced
    (x y z : PTree) : Prop :=
  ∀ w : PTree,
    (((preLieDifferenceGeneratorFlatmapLeft x y z).count w : Nat) : Int) =
      (((preLieDifferenceGeneratorFlatmapRight x y z).count w : Nat) : Int)

/--
Permutation balance for the two named raw two-step output lists.
-/
def PreLieDifferenceGeneratorFlatmapPermBalanced
    (x y z : PTree) : Prop :=
  (preLieDifferenceGeneratorFlatmapLeft x y z).Perm
    (preLieDifferenceGeneratorFlatmapRight x y z)

/--
Total-length balance for the two named raw two-step output lists.
-/
def PreLieDifferenceGeneratorFlatmapLengthBalanced
    (x y z : PTree) : Prop :=
  (preLieDifferenceGeneratorFlatmapLeft x y z).length =
    (preLieDifferenceGeneratorFlatmapRight x y z).length

/--
Pointwise multiplicity balance for the two named raw three-step output lists.
-/
def GraftPreLieDifferenceGeneratorFlatmapCountBalanced
    (u x y z : PTree) : Prop :=
  ∀ w : PTree,
    (((graftPreLieDifferenceGeneratorFlatmapLeft u x y z).count w : Nat) : Int) =
      (((graftPreLieDifferenceGeneratorFlatmapRight u x y z).count w : Nat) : Int)

/--
Permutation balance for the two named raw three-step output lists.
-/
def GraftPreLieDifferenceGeneratorFlatmapPermBalanced
    (u x y z : PTree) : Prop :=
  (graftPreLieDifferenceGeneratorFlatmapLeft u x y z).Perm
    (graftPreLieDifferenceGeneratorFlatmapRight u x y z)

/--
Total-length balance for the two named raw three-step output lists.
-/
def GraftPreLieDifferenceGeneratorFlatmapLengthBalanced
    (u x y z : PTree) : Prop :=
  (graftPreLieDifferenceGeneratorFlatmapLeft u x y z).length =
    (graftPreLieDifferenceGeneratorFlatmapRight u x y z).length

/--
Pointwise multiplicity balance for the two named raw two-step output lists,
formulated directly in `Nat` rather than after coercion to `Int`.
-/
def PreLieDifferenceGeneratorFlatmapNatCountBalanced
    (x y z : PTree) : Prop :=
  ∀ w : PTree,
    (preLieDifferenceGeneratorFlatmapLeft x y z).count w =
      (preLieDifferenceGeneratorFlatmapRight x y z).count w

/--
Pointwise multiplicity balance for the two named raw three-step output lists,
formulated directly in `Nat`.
-/
def GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced
    (u x y z : PTree) : Prop :=
  ∀ w : PTree,
    (graftPreLieDifferenceGeneratorFlatmapLeft u x y z).count w =
      (graftPreLieDifferenceGeneratorFlatmapRight u x y z).count w

/--
The named two-step count-balance proposition is definitionally the same as the
older additive count identity on the two raw comparison sides.
-/
theorem preLieDifferenceGeneratorFlatmapCountBalanced_iff
    (x y z : PTree) :
    PreLieDifferenceGeneratorFlatmapCountBalanced x y z ↔
      ∀ w : PTree,
        (((PTree.matchingLeafGraftings y z).flatMap
            (fun z' => PTree.matchingLeafGraftings x z')).count w : Int)
          +
        (((PTree.matchingLeafGraftings y x).flatMap
            (fun y' => PTree.matchingLeafGraftings y' z)).count w : Int)
        =
        (((PTree.matchingLeafGraftings x z).flatMap
            (fun z' => PTree.matchingLeafGraftings y z')).count w : Int)
          +
        (((PTree.matchingLeafGraftings x y).flatMap
            (fun y' => PTree.matchingLeafGraftings y' z)).count w : Int) := by
  constructor
  · intro hcount w
    simpa [PreLieDifferenceGeneratorFlatmapCountBalanced,
      preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
      List.count_append, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using hcount w
  · intro hcount w
    simpa [PreLieDifferenceGeneratorFlatmapCountBalanced,
      preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
      List.count_append, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using hcount w

/--
The named three-step count-balance proposition is definitionally the same as
the older additive count identity on the two raw comparison sides.
-/
theorem graftPreLieDifferenceGeneratorFlatmapCountBalanced_iff
    (u x y z : PTree) :
    GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z ↔
      ∀ w : PTree,
        (((PTree.matchingLeafGraftings y z).flatMap
            (fun z' => (PTree.matchingLeafGraftings x z').flatMap
              (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
          +
        (((PTree.matchingLeafGraftings y x).flatMap
            (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
              (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
        =
        (((PTree.matchingLeafGraftings x z).flatMap
            (fun z' => (PTree.matchingLeafGraftings y z').flatMap
              (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
          +
        (((PTree.matchingLeafGraftings x y).flatMap
            (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
              (fun t => PTree.matchingLeafGraftings u t))).count w : Int) := by
  constructor
  · intro hcount w
    simpa [GraftPreLieDifferenceGeneratorFlatmapCountBalanced,
      graftPreLieDifferenceGeneratorFlatmapLeft,
      graftPreLieDifferenceGeneratorFlatmapRight, List.count_append,
      Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using hcount w
  · intro hcount w
    simpa [GraftPreLieDifferenceGeneratorFlatmapCountBalanced,
      graftPreLieDifferenceGeneratorFlatmapLeft,
      graftPreLieDifferenceGeneratorFlatmapRight, List.count_append,
      Int.add_assoc, Int.add_left_comm, Int.add_comm]
      using hcount w

/--
The `Nat`-valued and `Int`-valued formulations of the two-step pointwise
multiplicity balance are equivalent.
-/
theorem preLieDifferenceGeneratorFlatmapNatCountBalanced_iff
    (x y z : PTree) :
    PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z ↔
      PreLieDifferenceGeneratorFlatmapCountBalanced x y z := by
  constructor
  · intro hcount w
    exact congrArg Int.ofNat (hcount w)
  · intro hcount w
    exact Int.ofNat.inj (hcount w)

/--
The `Nat`-valued and `Int`-valued formulations of the three-step pointwise
multiplicity balance are equivalent.
-/
theorem graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_iff
    (u x y z : PTree) :
    GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z ↔
      GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z := by
  constructor
  · intro hcount w
    exact congrArg Int.ofNat (hcount w)
  · intro hcount w
    exact Int.ofNat.inj (hcount w)

/--
The original `Int`-valued base flatmap balance follows from its `Nat`-valued
version.
-/
theorem preLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapCountBalanced x y z :=
  (preLieDifferenceGeneratorFlatmapNatCountBalanced_iff x y z).mp hcount

/--
Conversely, the `Nat`-valued base flatmap balance follows from the original
`Int`-valued formulation.
-/
theorem preLieDifferenceGeneratorFlatmapNatCountBalanced_of_countBalanced
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z :=
  (preLieDifferenceGeneratorFlatmapNatCountBalanced_iff x y z).mpr hcount

/--
The original `Int`-valued higher flatmap balance follows from its `Nat`-valued
version.
-/
theorem graftPreLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z :=
  (graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_iff u x y z).mp hcount

/--
Conversely, the `Nat`-valued higher flatmap balance follows from the original
`Int`-valued formulation.
-/
theorem graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_countBalanced
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z :=
  (graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_iff u x y z).mpr hcount

/--
The named two-step permutation-balance proposition is definitionally the same
as the older permutation statement on the two raw comparison-side lists.
-/
theorem preLieDifferenceGeneratorFlatmapPermBalanced_iff
    (x y z : PTree) :
    PreLieDifferenceGeneratorFlatmapPermBalanced x y z ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))).Perm
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))) := by
  rfl

/--
The named two-step length-balance proposition is definitionally the same as the
older additive length identity on the two raw comparison sides.
-/
theorem preLieDifferenceGeneratorFlatmapLengthBalanced_iff
    (x y z : PTree) :
    PreLieDifferenceGeneratorFlatmapLengthBalanced x y z ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat) := by
  simp [PreLieDifferenceGeneratorFlatmapLengthBalanced,
    preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
    List.length_append]

/--
Support-level equality for the named two-step raw output lists.

This is the already-proved witness-balance statement, restated in the compact
named-list language used by the corrected-counit reductions.
-/
theorem mem_preLieDifferenceGeneratorFlatmapLeft_iff
    (x y z w : PTree) :
    w ∈ preLieDifferenceGeneratorFlatmapLeft x y z ↔
      w ∈ preLieDifferenceGeneratorFlatmapRight x y z := by
  simpa [preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight]
    using twoStepFlatmaps_balance x y z w

/--
Consequently the underlying finite output sets of the two named two-step raw
lists agree.
-/
theorem preLieDifferenceGeneratorFlatmapLeft_toFinset_eq
    (x y z : PTree) :
    (preLieDifferenceGeneratorFlatmapLeft x y z).toFinset =
      (preLieDifferenceGeneratorFlatmapRight x y z).toFinset := by
  ext w
  simp [mem_preLieDifferenceGeneratorFlatmapLeft_iff]

/--
Pointwise multiplicity balance on the named two-step lists upgrades to a
permutation of those lists.
-/
theorem preLieDifferenceGeneratorFlatmap_perm_of_count_balance
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapPermBalanced x y z := by
  have hsub :
      List.Subperm
        (preLieDifferenceGeneratorFlatmapLeft x y z)
        (preLieDifferenceGeneratorFlatmapRight x y z) := by
    rw [List.subperm_iff_count]
    intro a
    exact le_of_eq (Int.ofNat.inj (hcount a))
  have hsub' :
      List.Subperm
        (preLieDifferenceGeneratorFlatmapRight x y z)
        (preLieDifferenceGeneratorFlatmapLeft x y z) := by
    rw [List.subperm_iff_count]
    intro a
    exact le_of_eq (Int.ofNat.inj (hcount a).symm)
  exact hsub.antisymm hsub'

/--
Pointwise multiplicity balance on the named two-step lists also forces equality
of their total lengths.
-/
theorem preLieDifferenceGeneratorFlatmap_length_eq_of_count_balance
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapLengthBalanced x y z := by
  exact (preLieDifferenceGeneratorFlatmap_perm_of_count_balance x y z hcount).length_eq

/--
Permutation balance on the named two-step lists also forces equality of their
total lengths.
-/
theorem preLieDifferenceGeneratorFlatmap_length_eq_of_perm_balance
    (x y z : PTree)
    (hperm : PreLieDifferenceGeneratorFlatmapPermBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapLengthBalanced x y z := by
  exact hperm.length_eq

/--
The corrected counit kills a pre-Lie difference generator once the total
two-step graft lengths on the two comparison sides agree.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_length_balance
    (x y z : PTree)
    (hbal :
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length) : Nat)) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  rw [preLieDifferenceGenerators, correctedCounit_linear_sub,
    correctedCounit_linear_comparisonSideGenerators,
    correctedCounit_linear_swappedComparisonSideGenerators]
  apply sub_eq_zero.mpr
  simpa [List.length_flatMap, Nat.cast_add] using
    congrArg (fun n : Nat => (n : Int)) hbal

/--
The generator-level corrected-counit vanishing is exactly equivalent to the
equality of the two total two-step raw graft lengths.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_iff_length_balance
    (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).length
        +
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).length
        +
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).length : Nat) := by
  rw [preLieDifferenceGenerators, correctedCounit_linear_sub,
    correctedCounit_linear_comparisonSideGenerators,
    correctedCounit_linear_swappedComparisonSideGenerators]
  constructor
  · intro hzero
    exact Int.ofNat.inj (sub_eq_zero.mp hzero)
  · intro hbal
    apply sub_eq_zero.mpr
    simpa [List.length_flatMap, Nat.cast_add] using
      congrArg (fun n : Nat => (n : Int)) hbal

/--
Equivalent reformulation using the named raw two-step output lists.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_iff_flatmap_length_balance
    (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 ↔
      PreLieDifferenceGeneratorFlatmapLengthBalanced x y z := by
  simpa [PreLieDifferenceGeneratorFlatmapLengthBalanced,
    preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
    List.length_append, List.length_flatMap]
    using correctedCounit_linear_preLieDifferenceGenerators_iff_length_balance x y z

/--
The same corrected-counit vanishing criterion can be stated using the total
number of raw two-step address witnesses on the two sides.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_addrWitness_length_balance
    (x y z : PTree)
    (hbal :
      (twoStepAddrWitnessesLeft x y z).length =
        (twoStepAddrWitnessesRight x y z).length) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_length_balance
  rw [← twoStepAddrWitnessesLeft_length, ← twoStepAddrWitnessesRight_length]
  exact hbal

/--
The same corrected-counit vanishing criterion can also be discharged from
pointwise equality of the output multiplicities in the raw address-witness
lists.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_addrWitness_count_balance
    (x y z : PTree)
    (hcount : ∀ w : PTree,
      (((twoStepAddrWitnessesLeft x y z).map Prod.snd).count w : Int) =
        (((twoStepAddrWitnessesRight x y z).map Prod.snd).count w : Int)) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_addrWitness_length_balance
  exact twoStepAddrWitnesses_length_eq_of_count_balance x y z hcount

/--
The corrected counit also vanishes on a generator as soon as the two raw
two-step flatmap presentations have equal output multiplicities pointwise.

This is the exact shape of the remaining combinatorial theorem in the
`GrossmanLarsson` development, expressed without the auxiliary address-witness
lists.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_flatmap_count_balance
    (x y z : PTree)
    (hcount : ∀ w : PTree,
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z')).count w : Int)
        +
      (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Int)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z')).count w : Int)
        +
      (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)).count w : Int)) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_addrWitness_count_balance
  intro w
  rw [count_map_snd_twoStepAddrWitnessesLeft, count_map_snd_twoStepAddrWitnessesRight]
  simpa [Int.add_left_comm, Int.add_assoc] using hcount w

/--
A stronger but often convenient sufficient criterion: if the two concrete
two-step flatmap lists are permutations of each other, then the corrected
counit already kills the pre-Lie difference generator.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_flatmap_perm
    (x y z : PTree)
    (hperm :
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => PTree.matchingLeafGraftings x z'))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z))).Perm
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => PTree.matchingLeafGraftings y z'))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => PTree.matchingLeafGraftings y' z)))) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_length_balance
  simpa [List.length_append] using hperm.length_eq

/--
Named-list version of the generator-level multiplicity criterion.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_named_flatmap_count_balance
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_flatmap_count_balance
  intro w
  simpa [preLieDifferenceGeneratorFlatmapLeft,
    preLieDifferenceGeneratorFlatmapRight, List.count_append, Int.add_assoc,
    Int.add_left_comm, Int.add_comm] using hcount w

/--
Named-list version of the generator-level permutation criterion.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_named_flatmap_perm
    (x y z : PTree)
    (hperm : PreLieDifferenceGeneratorFlatmapPermBalanced x y z) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  apply correctedCounit_linear_preLieDifferenceGenerators_of_flatmap_perm
  simpa [preLieDifferenceGeneratorFlatmapLeft,
    preLieDifferenceGeneratorFlatmapRight] using hperm

/--
The generator-level corrected counit vanishes under the compact named
count-balance proposition.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_countBalanced
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact correctedCounit_linear_preLieDifferenceGenerators_of_named_flatmap_count_balance
    x y z hcount

/--
Compact named-length form of the generator-level corrected-counit criterion.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_iff_lengthBalanced
    (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 ↔
      PreLieDifferenceGeneratorFlatmapLengthBalanced x y z := by
  exact correctedCounit_linear_preLieDifferenceGenerators_iff_flatmap_length_balance x y z

/--
The higher corrected-counit vanishing reduces to equality of the two concrete
three-stage raw graft lengths.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_length_balance
    (u x y z : PTree)
    (hbal :
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat)) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  rw [preLieDifferenceGenerators, map_sub, correctedCounit_linear_sub,
    correctedCounit_linear_graftPreLie_treeGen_comparisonSideGenerators,
    correctedCounit_linear_graftPreLie_treeGen_swappedComparisonSideGenerators]
  apply sub_eq_zero.mpr
  simpa [Nat.cast_add] using congrArg (fun n : Nat => (n : Int)) hbal

/--
The higher corrected-counit vanishing is exactly equivalent to equality of
the two concrete three-stage raw graft lengths.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_iff_length_balance
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat) := by
  rw [preLieDifferenceGenerators, map_sub, correctedCounit_linear_sub,
    correctedCounit_linear_graftPreLie_treeGen_comparisonSideGenerators,
    correctedCounit_linear_graftPreLie_treeGen_swappedComparisonSideGenerators]
  constructor
  · intro hzero
    exact Int.ofNat.inj (sub_eq_zero.mp hzero)
  · intro hbal
    apply sub_eq_zero.mpr
    simpa [Nat.cast_add] using congrArg (fun n : Nat => (n : Int)) hbal

/--
Equivalent reformulation using the named raw three-step output lists.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_iff_flatmap_length_balance
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 ↔
      (graftPreLieDifferenceGeneratorFlatmapLeft u x y z).length =
        (graftPreLieDifferenceGeneratorFlatmapRight u x y z).length := by
  simpa [graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.length_append]
    using
      correctedCounit_linear_graft_preLieDifferenceGenerators_iff_length_balance
        u x y z

/--
For finite lists, pointwise equality of element counts already forces equality
of total lengths.
-/
theorem list_perm_of_count_balance
    {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α)
    (hcount : ∀ a : α, (l₁.count a : Int) = (l₂.count a : Int)) :
    l₁.Perm l₂ := by
  have hsub : List.Subperm l₁ l₂ := by
    rw [List.subperm_iff_count]
    intro a
    exact le_of_eq (Int.ofNat.inj (hcount a))
  have hsub' : List.Subperm l₂ l₁ := by
    rw [List.subperm_iff_count]
    intro a
    exact le_of_eq (Int.ofNat.inj (hcount a).symm)
  exact hsub.antisymm hsub'

/--
For finite lists, pointwise equality of element counts already forces equality
of total lengths.
-/
theorem list_length_eq_of_count_balance
    {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α)
    (hcount : ∀ a : α, (l₁.count a : Int) = (l₂.count a : Int)) :
    l₁.length = l₂.length := by
  exact (list_perm_of_count_balance l₁ l₂ hcount).length_eq

/--
`Nat`-valued count balance is already enough to recover a list permutation.
-/
theorem list_perm_of_natCount_balance
    {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α)
    (hcount : ∀ a : α, l₁.count a = l₂.count a) :
    l₁.Perm l₂ := by
  apply list_perm_of_count_balance
  intro a
  exact congrArg Int.ofNat (hcount a)

/--
`Nat`-valued count balance also forces equality of list lengths.
-/
theorem list_length_eq_of_natCount_balance
    {α : Type*} [DecidableEq α]
    (l₁ l₂ : List α)
    (hcount : ∀ a : α, l₁.count a = l₂.count a) :
    l₁.length = l₂.length := by
  exact (list_perm_of_natCount_balance l₁ l₂ hcount).length_eq

/--
The `Nat`-valued base flatmap balance upgrades to a permutation of the two
named raw output lists.
-/
theorem preLieDifferenceGeneratorFlatmap_perm_of_natCount_balance
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapPermBalanced x y z := by
  exact list_perm_of_natCount_balance
    (preLieDifferenceGeneratorFlatmapLeft x y z)
    (preLieDifferenceGeneratorFlatmapRight x y z)
    hcount

/--
The `Nat`-valued base flatmap balance also forces equality of the total output
lengths.
-/
theorem preLieDifferenceGeneratorFlatmap_length_eq_of_natCount_balance
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    PreLieDifferenceGeneratorFlatmapLengthBalanced x y z := by
  exact
    (preLieDifferenceGeneratorFlatmap_perm_of_natCount_balance
      x y z hcount).length_eq

/--
The `Nat`-valued higher flatmap balance upgrades to a permutation of the two
named three-step output lists.
-/
theorem graftPreLieDifferenceGeneratorFlatmap_perm_of_natCount_balance
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z := by
  exact list_perm_of_natCount_balance
    (graftPreLieDifferenceGeneratorFlatmapLeft u x y z)
    (graftPreLieDifferenceGeneratorFlatmapRight u x y z)
    hcount

/--
The `Nat`-valued higher flatmap balance also forces equality of the total
three-step output lengths.
-/
theorem graftPreLieDifferenceGeneratorFlatmap_length_eq_of_natCount_balance
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapLengthBalanced u x y z := by
  exact
    (graftPreLieDifferenceGeneratorFlatmap_perm_of_natCount_balance
      u x y z hcount).length_eq

/--
The corrected counit already kills a base pre-Lie difference generator under
the stronger `Nat`-valued flatmap balance hypothesis.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_natCountBalanced
    (x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact correctedCounit_linear_preLieDifferenceGenerators_of_countBalanced x y z
    (preLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced x y z hcount)

/--
Likewise for the one-step-grafted generator-level corrected counit.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_natCountBalanced
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact
    (correctedCounit_linear_graft_preLieDifferenceGenerators_iff_flatmap_length_balance
      u x y z).2
      (graftPreLieDifferenceGeneratorFlatmap_length_eq_of_natCount_balance
        u x y z hcount)

/--
Base `Nat`-count balance propagates through one more fixed grafting step to a
named three-step permutation balance.
-/
theorem graftPreLieDifferenceGeneratorFlatmapPermBalanced_of_preLieDifferenceGeneratorFlatmapNatCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z := by
  simpa [PreLieDifferenceGeneratorFlatmapPermBalanced,
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced,
    preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
    graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.flatMap_append,
    List.flatMap_assoc] using
    (preLieDifferenceGeneratorFlatmap_perm_of_natCount_balance x y z hcount).flatMap
      (fun t _ => List.Perm.refl (PTree.matchingLeafGraftings u t))

/--
Base `Nat`-count balance propagates through one more fixed grafting step to the
named three-step `Nat`-count balance.
-/
theorem graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_preLieDifferenceGeneratorFlatmapNatCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z := by
  have hperm :
      GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z :=
    graftPreLieDifferenceGeneratorFlatmapPermBalanced_of_preLieDifferenceGeneratorFlatmapNatCountBalanced
      u x y z hcount
  intro w
  exact (List.perm_iff_count.mp hperm) w

/--
Base `Int`-count balance propagates through one more fixed grafting step to the
named three-step `Nat`-count balance.
-/
theorem graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_preLieDifferenceGeneratorFlatmapCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z := by
  exact
    graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_preLieDifferenceGeneratorFlatmapNatCountBalanced
      u x y z
      (preLieDifferenceGeneratorFlatmapNatCountBalanced_of_countBalanced
        x y z hcount)

/--
Base `Int`-count balance therefore also propagates to the named three-step
`Int`-count balance.
-/
theorem graftPreLieDifferenceGeneratorFlatmapCountBalanced_of_preLieDifferenceGeneratorFlatmapCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z := by
  exact
    graftPreLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
      u x y z
      (graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_preLieDifferenceGeneratorFlatmapCountBalanced
        u x y z hcount)

/--
The higher corrected-counit vanishing also follows from pointwise equality of
the two concrete three-stage flatmap multiplicities.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_flatmap_count_balance
    (u x y z : PTree)
    (hcount : ∀ w : PTree,
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
        +
      (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).count w : Int)
        +
      (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).count w : Int)) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  let l1 :=
    (PTree.matchingLeafGraftings y z).flatMap
      (fun z' => (PTree.matchingLeafGraftings x z').flatMap
        (fun t => PTree.matchingLeafGraftings u t))
  let l2 :=
    (PTree.matchingLeafGraftings y x).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
        (fun t => PTree.matchingLeafGraftings u t))
  let r1 :=
    (PTree.matchingLeafGraftings x z).flatMap
      (fun z' => (PTree.matchingLeafGraftings y z').flatMap
        (fun t => PTree.matchingLeafGraftings u t))
  let r2 :=
    (PTree.matchingLeafGraftings x y).flatMap
      (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
        (fun t => PTree.matchingLeafGraftings u t))
  have happ : ∀ w : PTree, (((l1 ++ l2).count w : Nat) : Int) = (((r1 ++ r2).count w : Nat) : Int) := by
    intro w
    rw [List.count_append, List.count_append]
    norm_num
    exact hcount w
  have hlen : (l1.length + l2.length : Nat) = (r1.length + r2.length : Nat) := by
    simpa [List.length_append] using
      (list_length_eq_of_count_balance (l1 ++ l2) (r1 ++ r2) happ)
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_length_balance
  simpa [l1, l2, r1, r2] using hlen

/--
Permutation form of the higher corrected-counit criterion: a permutation of the
two concrete three-stage flatmap lists is already enough to force vanishing.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_flatmap_perm
    (u x y z : PTree)
    (hperm :
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t)))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t)))).Perm
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t)))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))))) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_length_balance
  simpa [List.length_append] using hperm.length_eq

/--
Named-list version of the higher multiplicity criterion.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_named_flatmap_count_balance
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_flatmap_count_balance
  intro w
  simpa [graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.count_append, Int.add_assoc,
    Int.add_left_comm, Int.add_comm] using hcount w

/--
Named-list version of the higher permutation criterion.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_named_flatmap_perm
    (u x y z : PTree)
    (hperm : GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_flatmap_perm
  simpa [graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight] using hperm

/--
The higher corrected counit vanishes under the compact named count-balance
proposition.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_countBalanced
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact
    correctedCounit_linear_graft_preLieDifferenceGenerators_of_named_flatmap_count_balance
      u x y z hcount

/--
Compact named-length form of the higher corrected-counit criterion.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_iff_lengthBalanced
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 ↔
      GraftPreLieDifferenceGeneratorFlatmapLengthBalanced u x y z := by
  exact
    correctedCounit_linear_graft_preLieDifferenceGenerators_iff_flatmap_length_balance
      u x y z

/--
If the base two-step named flatmaps are permutation-balanced, then the higher
corrected counit already vanishes after grafting once more by a fixed tree
generator.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapPermBalanced
    (u x y z : PTree)
    (hperm : PreLieDifferenceGeneratorFlatmapPermBalanced x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_named_flatmap_perm
  simpa [PreLieDifferenceGeneratorFlatmapPermBalanced,
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced,
    preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
    graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.flatMap_append,
    List.flatMap_assoc] using
    hperm.flatMap (fun t _ => List.Perm.refl (PTree.matchingLeafGraftings u t))

/--
Likewise, base two-step count balance is already enough to force the higher
corrected-counit vanishing after one more grafting step.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  apply correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapPermBalanced
  exact preLieDifferenceGeneratorFlatmap_perm_of_count_balance x y z hcount

/--
Pointwise multiplicity balance on the named three-step lists upgrades to a
permutation of those lists.
-/
theorem graftPreLieDifferenceGeneratorFlatmap_perm_of_count_balance
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z := by
  exact list_perm_of_count_balance
    (graftPreLieDifferenceGeneratorFlatmapLeft u x y z)
    (graftPreLieDifferenceGeneratorFlatmapRight u x y z)
    hcount

/--
Pointwise multiplicity balance on the named three-step lists also forces
equality of their total lengths.
-/
theorem graftPreLieDifferenceGeneratorFlatmap_length_eq_of_count_balance
    (u x y z : PTree)
    (hcount : GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapLengthBalanced u x y z := by
  exact
    (graftPreLieDifferenceGeneratorFlatmap_perm_of_count_balance
      u x y z hcount).length_eq

/--
Permutation balance on the named three-step lists also forces equality of
their total lengths.
-/
theorem graftPreLieDifferenceGeneratorFlatmap_length_eq_of_perm_balance
    (u x y z : PTree)
    (hperm : GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z) :
    GraftPreLieDifferenceGeneratorFlatmapLengthBalanced u x y z := by
  exact hperm.length_eq

/--
The named three-step permutation-balance proposition is definitionally the same
as the older permutation statement on the two raw comparison-side lists.
-/
theorem graftPreLieDifferenceGeneratorFlatmapPermBalanced_iff
    (u x y z : PTree) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t)))
        ++
        ((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t)))).Perm
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t)))
        ++
        ((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t)))) := by
  rfl

/--
The named three-step length-balance proposition is definitionally the same as
the older additive length identity on the two raw comparison sides.
-/
theorem graftPreLieDifferenceGeneratorFlatmapLengthBalanced_iff
    (u x y z : PTree) :
    GraftPreLieDifferenceGeneratorFlatmapLengthBalanced u x y z ↔
      (((PTree.matchingLeafGraftings y z).flatMap
          (fun z' => (PTree.matchingLeafGraftings x z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings y x).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat)
      =
      (((PTree.matchingLeafGraftings x z).flatMap
          (fun z' => (PTree.matchingLeafGraftings y z').flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length
        +
        (((PTree.matchingLeafGraftings x y).flatMap
          (fun y' => (PTree.matchingLeafGraftings y' z).flatMap
            (fun t => PTree.matchingLeafGraftings u t))).length) : Nat) := by
  simp [GraftPreLieDifferenceGeneratorFlatmapLengthBalanced,
    graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.length_append]

/--
If the two-step named raw output lists are already permutation-balanced, then
grafting once more by a fixed tree generator preserves that permutation
balance.
-/
theorem graftPreLieDifferenceGeneratorFlatmapPermBalanced_of_preLieDifferenceGeneratorFlatmapPermBalanced
    (u x y z : PTree)
    (hperm : PreLieDifferenceGeneratorFlatmapPermBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z := by
  simpa [PreLieDifferenceGeneratorFlatmapPermBalanced,
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced,
    preLieDifferenceGeneratorFlatmapLeft, preLieDifferenceGeneratorFlatmapRight,
    graftPreLieDifferenceGeneratorFlatmapLeft,
    graftPreLieDifferenceGeneratorFlatmapRight, List.flatMap_append,
    List.flatMap_assoc] using
    hperm.flatMap (fun t _ => List.Perm.refl (PTree.matchingLeafGraftings u t))

/--
Consequently, two-step count balance already implies higher three-step
permutation balance after grafting once more by a fixed generator.
-/
theorem graftPreLieDifferenceGeneratorFlatmapPermBalanced_of_preLieDifferenceGeneratorFlatmapCountBalanced
    (u x y z : PTree)
    (hcount : PreLieDifferenceGeneratorFlatmapCountBalanced x y z) :
    GraftPreLieDifferenceGeneratorFlatmapPermBalanced u x y z := by
  exact
    graftPreLieDifferenceGeneratorFlatmapPermBalanced_of_preLieDifferenceGeneratorFlatmapPermBalanced
      u x y z
      (preLieDifferenceGeneratorFlatmap_perm_of_count_balance x y z hcount)

/-!
### The corrected counit kills pre-Lie difference generators

The key identity is that `comparisonSideGenerators x y z` and
`swappedComparisonSideGenerators x y z` have equal total coefficient sums in
the PTree basis.  Concretely (with `a = |leaves x|`, `b = |leaves y|`,
`c = |leaves z|`):

  total(comparison) = c(b+c-1)(a+b+c-2) + ac(a+b+c-2)
                    = c(a+b+c-2)(a+b+c-1)

  total(swapped)    = c(a+c-1)(a+b+c-2) + bc(a+b+c-2)
                    = c(a+b+c-2)(a+b+c-1)

So the difference is zero.  The formal Lean proof requires lemmas relating
`|leaves|` of grafted trees; these are sorry'd pending that development.
-/

/--
Global form of the remaining base combinatorial input: every concrete two-step
comparison pair of raw flatmaps has matching output multiplicities.
-/
def AllPreLieDifferenceGeneratorFlatmapsCountBalanced : Prop :=
  ∀ x y z : PTree, PreLieDifferenceGeneratorFlatmapCountBalanced x y z

/--
Global `Nat`-valued version of the remaining base combinatorial input.
-/
def AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced : Prop :=
  ∀ x y z : PTree, PreLieDifferenceGeneratorFlatmapNatCountBalanced x y z

/--
Global `Int`-valued higher flatmap balance.
-/
def AllGraftPreLieDifferenceGeneratorFlatmapsCountBalanced : Prop :=
  ∀ u x y z : PTree, GraftPreLieDifferenceGeneratorFlatmapCountBalanced u x y z

/--
Global `Nat`-valued higher flatmap balance.
-/
def AllGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced : Prop :=
  ∀ u x y z : PTree, GraftPreLieDifferenceGeneratorFlatmapNatCountBalanced u x y z

/--
The global `Nat`- and `Int`-valued base balance hypotheses are equivalent.
-/
theorem allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced :
    AllPreLieDifferenceGeneratorFlatmapsCountBalanced ↔
      AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced := by
  constructor
  · intro hbal x y z
    exact preLieDifferenceGeneratorFlatmapNatCountBalanced_of_countBalanced
      x y z (hbal x y z)
  · intro hbal x y z
    exact preLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
      x y z (hbal x y z)

/--
The global `Nat`- and `Int`-valued higher balance hypotheses are equivalent.
-/
theorem allGraftPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced :
    AllGraftPreLieDifferenceGeneratorFlatmapsCountBalanced ↔
      AllGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced := by
  constructor
  · intro hbal u x y z
    exact graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_countBalanced
      u x y z (hbal u x y z)
  · intro hbal u x y z
    exact graftPreLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
      u x y z (hbal u x y z)

/--
Base global count balance automatically propagates to the one-more-graft global
higher count balance.
-/
theorem allGraftPreLieDifferenceGeneratorFlatmapsCountBalanced_of_allPreLieDifferenceGeneratorFlatmapsCountBalanced
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced) :
    AllGraftPreLieDifferenceGeneratorFlatmapsCountBalanced := by
  intro u x y z
  exact
    graftPreLieDifferenceGeneratorFlatmapCountBalanced_of_preLieDifferenceGeneratorFlatmapCountBalanced
      u x y z (hbal x y z)

/--
Likewise in the `Nat`-valued formulation.
-/
theorem allGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced_of_allPreLieDifferenceGeneratorFlatmapsNatCountBalanced
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced) :
    AllGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced := by
  intro u x y z
  exact
    graftPreLieDifferenceGeneratorFlatmapNatCountBalanced_of_preLieDifferenceGeneratorFlatmapNatCountBalanced
      u x y z (hbal x y z)

/--
The corrected counit kills every pre-Lie difference generator.

Proof outline: `preLieDifferenceGenerators x y z = comparison - swapped`
where both sides have the same total coefficient in the PTree basis, by a
two-step output-multiplicity balance. The reduction lemmas immediately above
show that it is enough to prove the named raw balance proposition
`PreLieDifferenceGeneratorFlatmapCountBalanced x y z`.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  suffices PreLieDifferenceGeneratorFlatmapCountBalanced x y z by
    exact correctedCounit_linear_preLieDifferenceGenerators_of_countBalanced x y z this
  sorry

/--
Under the global two-step multiplicity-balance hypothesis, the corrected counit
vanishes on every concrete pre-Lie difference generator.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_globalCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced) (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact correctedCounit_linear_preLieDifferenceGenerators_of_countBalanced x y z
    (hbal x y z)

/--
Under the global `Nat`-valued two-step multiplicity-balance hypothesis, the
corrected counit vanishes on every concrete pre-Lie difference generator.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators_of_globalNatCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact correctedCounit_linear_preLieDifferenceGenerators_of_globalCountBalance
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal)
    x y z

/--
The corrected counit kills every element of `preLieDifferenceSubmodule`.
-/
theorem correctedCounit_linear_kills_preLieDifferenceSubmodule
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    correctedCounit_linear a = 0 := by
  change a ∈ Submodule.span ℤ preLieDifferenceGeneratorSet at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro b hb
    rcases hb with ⟨x, y, z, rfl⟩
    exact correctedCounit_linear_preLieDifferenceGenerators x y z
  · simpa [correctedCounit_linear]
  · intro x y _ _ hx hy
    simp [correctedCounit_linear_add, hx, hy]
  · intro n x _ hx
    simpa [correctedCounit_linear_smul, hx]

/--
Under the global two-step multiplicity-balance hypothesis, the corrected
counit kills the whole concrete pre-Lie defect submodule.
-/
theorem correctedCounit_linear_kills_preLieDifferenceSubmodule_of_globalCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    correctedCounit_linear a = 0 := by
  change a ∈ Submodule.span ℤ preLieDifferenceGeneratorSet at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro b hb
    rcases hb with ⟨x, y, z, rfl⟩
    exact correctedCounit_linear_preLieDifferenceGenerators_of_globalCountBalance hbal x y z
  · simpa [correctedCounit_linear]
  · intro x y _ _ hx hy
    simp [correctedCounit_linear_add, hx, hy]
  · intro n x _ hx
    simpa [correctedCounit_linear_smul, hx]

/--
The global `Nat`-valued balance hypothesis is also enough to kill the concrete
pre-Lie defect submodule.
-/
theorem correctedCounit_linear_kills_preLieDifferenceSubmodule_of_globalNatCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_preLieDifferenceSubmodule_of_globalCountBalance
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal) ha

/--
If the stable closure coincides with the concrete pre-Lie defect submodule,
then the corrected counit also kills the stable closure.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_eq
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  have ha' : a ∈ preLieDifferenceSubmodule := by
    simpa [hEq] using ha
  exact correctedCounit_linear_kills_preLieDifferenceSubmodule ha'

/--
In particular, the corrected counit kills the stable closure whenever the raw
pre-Lie defect submodule is already stable under grafting by tree generators on
both sides.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_preserves
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_stableSubmodule_of_eq
    (preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule hL hR) ha

/--
Higher-order leaf-count identity: the corrected counit also kills
`graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)`.

By the propagation theorems immediately above, it is now enough to prove the
base two-step balance proposition
`PreLieDifferenceGeneratorFlatmapCountBalanced x y z`; no separate three-stage
combinatorics are needed anymore.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  suffices PreLieDifferenceGeneratorFlatmapCountBalanced x y z by
    exact
      correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapCountBalanced
        u x y z this
  sorry

/--
Under the same global two-step multiplicity-balance hypothesis, the higher
one-step-grafted corrected-counit vanishing theorem follows automatically.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_globalCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact
    correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapCountBalanced
      u x y z (hbal x y z)

/--
Global `Nat`-valued base balance automatically implies the higher one-step
grafted corrected-counit vanishing theorem.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_globalNatCountBalance
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact
    correctedCounit_linear_graft_preLieDifferenceGenerators_of_preLieDifferenceGeneratorFlatmapCountBalanced
      u x y z
      (preLieDifferenceGeneratorFlatmapCountBalanced_of_natCountBalanced
        x y z (hbal x y z))

/--
Global higher `Int`-count balance gives the one-step-grafted corrected-counit
vanishing theorem directly.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_globalGraftCountBalance
    (hbal : AllGraftPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact correctedCounit_linear_graft_preLieDifferenceGenerators_of_countBalanced
    u x y z (hbal u x y z)

/--
Global higher `Nat`-count balance gives the one-step-grafted corrected-counit
vanishing theorem directly.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators_of_globalGraftNatCountBalance
    (hbal : AllGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact correctedCounit_linear_graft_preLieDifferenceGenerators_of_natCountBalanced
    u x y z (hbal u x y z)

/--
The corrected counit kills every element of `preLieDifferenceStableSubmodule`.

At this point the remaining genuinely mathematical input is that the stable
closure collapses back to the concrete pre-Lie defect submodule; the theorem
`correctedCounit_linear_kills_stableSubmodule_of_eq` above would then finish
the argument immediately.
-/
theorem correctedCounit_linear_kills_stableSubmodule
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  suffices preLieDifferenceStableSubmodule = preLieDifferenceSubmodule by
    exact correctedCounit_linear_kills_stableSubmodule_of_eq this ha
  sorry

/--
If the global two-step multiplicity-balance theorem is available and the stable
closure collapses to the concrete defect submodule, then the corrected counit
kills the whole stable closure.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_eq
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  have ha' : a ∈ preLieDifferenceSubmodule := by
    simpa [hEq] using ha
  exact correctedCounit_linear_kills_preLieDifferenceSubmodule_of_globalCountBalance hbal ha'

/--
The same stable-submodule vanishing theorem under the stronger global
`Nat`-valued balance hypothesis.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_globalNatCountBalance_and_eq
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_eq
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal)
    hEq ha

/--
If the global two-step multiplicity-balance theorem is available and the stable
closure already agrees with the concrete defect submodule, then the corrected
counit descends to the stable quotient.
-/
noncomputable def correctedCounit_quot_of_globalCountBalance_and_eq
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  preLieDifferenceStableSubmodule.liftQ correctedCounit_linear
    (fun a ha =>
      correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_eq
        hbal hEq ha)

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_eq_mk
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (a : linearProofTreeCarrier) :
    correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_linear a := by
  simpa
    [correctedCounit_quot_of_globalCountBalance_and_eq,
      mkPreLieDifferenceStableQuotient]
    using (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := correctedCounit_linear)
      (h := by
        intro a ha
        exact
          correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_eq
            hbal hEq ha)
      (x := a))

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_eq_treeGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (t : PTree) :
    correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp [correctedCounit_quot_of_globalCountBalance_and_eq_mk]

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_eq_forestGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (f : Forest) :
    correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      (f.length : ℤ) := by
  induction f with
  | nil =>
      simp [correctedCounit_quot_of_globalCountBalance_and_eq_mk]
  | cons t ts ih =>
      simp [forestGen_cons, correctedCounit_quot_of_globalCountBalance_and_eq_mk,
        ih, add_comm]

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_eq_zero
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule) :
    correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq 0 = 0 :=
  map_zero _

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_eq_add
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (a b : PreLieDifferenceStableQuotient) :
    correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq (a + b) =
      correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq a +
        correctedCounit_quot_of_globalCountBalance_and_eq hbal hEq b :=
  map_add _ _ _

/--
Nat-count-balance variant of the descended corrected counit under an equality
presentation of the stable submodule.
-/
noncomputable def correctedCounit_quot_of_globalNatCountBalance_and_eq
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  correctedCounit_quot_of_globalCountBalance_and_eq
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal)
    hEq

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_eq_mk
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (a : linearProofTreeCarrier) :
    correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_linear a := by
  simp [correctedCounit_quot_of_globalNatCountBalance_and_eq]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_eq_treeGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (t : PTree) :
    correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp [correctedCounit_quot_of_globalNatCountBalance_and_eq_mk]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_eq_forestGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (f : Forest) :
    correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      (f.length : ℤ) := by
  induction f with
  | nil =>
      simp [correctedCounit_quot_of_globalNatCountBalance_and_eq_mk]
  | cons t ts ih =>
      simp [forestGen_cons,
        correctedCounit_quot_of_globalNatCountBalance_and_eq_mk, ih, add_comm]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_eq_zero
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule) :
    correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq 0 = 0 :=
  map_zero _

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_eq_add
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hEq : preLieDifferenceStableSubmodule = preLieDifferenceSubmodule)
    (a b : PreLieDifferenceStableQuotient) :
    correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq (a + b) =
      correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq a +
        correctedCounit_quot_of_globalNatCountBalance_and_eq hbal hEq b :=
  map_add _ _ _

/--
Likewise, if the global two-step multiplicity-balance theorem is available and
the concrete defect submodule is already stable under generator grafting on
both sides, then the corrected counit kills the whole stable closure.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_preserves
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_eq
    hbal (preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule hL hR) ha

/--
Nat-count-balance version of the same preservation-based stable-submodule
vanishing theorem.
-/
theorem correctedCounit_linear_kills_stableSubmodule_of_globalNatCountBalance_and_preserves
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_preserves
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal)
    hL hR ha

/--
If the global two-step multiplicity-balance theorem is available and the
concrete defect submodule is already stable under generator grafting on both
sides, then the corrected counit descends to the stable quotient.
-/
noncomputable def correctedCounit_quot_of_globalCountBalance_and_preserves
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  preLieDifferenceStableSubmodule.liftQ correctedCounit_linear
    (fun a ha =>
      correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_preserves
        hbal hL hR ha)

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_preserves_mk
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : linearProofTreeCarrier) :
    correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_linear a := by
  simpa
    [correctedCounit_quot_of_globalCountBalance_and_preserves,
      mkPreLieDifferenceStableQuotient]
    using (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := correctedCounit_linear)
      (h := by
        intro a ha
        exact
          correctedCounit_linear_kills_stableSubmodule_of_globalCountBalance_and_preserves
            hbal hL hR ha)
      (x := a))

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_preserves_treeGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (t : PTree) :
    correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp [correctedCounit_quot_of_globalCountBalance_and_preserves_mk]

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_preserves_forestGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (f : Forest) :
    correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      (f.length : ℤ) := by
  induction f with
  | nil =>
      simp [correctedCounit_quot_of_globalCountBalance_and_preserves_mk]
  | cons t ts ih =>
      simp [forestGen_cons,
        correctedCounit_quot_of_globalCountBalance_and_preserves_mk, ih, add_comm]

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_preserves_zero
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR 0 = 0 :=
  map_zero _

@[simp] theorem correctedCounit_quot_of_globalCountBalance_and_preserves_add
    (hbal : AllPreLieDifferenceGeneratorFlatmapsCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b : PreLieDifferenceStableQuotient) :
    correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR (a + b) =
      correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR a +
        correctedCounit_quot_of_globalCountBalance_and_preserves hbal hL hR b :=
  map_add _ _ _

/--
Nat-count-balance variant of the descended corrected counit under the standard
generator-preservation hypotheses.
-/
noncomputable def correctedCounit_quot_of_globalNatCountBalance_and_preserves
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  correctedCounit_quot_of_globalCountBalance_and_preserves
    ((allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2 hbal)
    hL hR

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_preserves_mk
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a : linearProofTreeCarrier) :
    correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_linear a := by
  simp [correctedCounit_quot_of_globalNatCountBalance_and_preserves]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_preserves_treeGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (t : PTree) :
    correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp [correctedCounit_quot_of_globalNatCountBalance_and_preserves_mk]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_preserves_forestGen
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (f : Forest) :
    correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      (f.length : ℤ) := by
  induction f with
  | nil =>
      simp [correctedCounit_quot_of_globalNatCountBalance_and_preserves_mk]
  | cons t ts ih =>
      simp [forestGen_cons,
        correctedCounit_quot_of_globalNatCountBalance_and_preserves_mk, ih, add_comm]

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_preserves_zero
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators) :
    correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR 0 = 0 :=
  map_zero _

@[simp] theorem correctedCounit_quot_of_globalNatCountBalance_and_preserves_add
    (hbal : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced)
    (hL : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators)
    (hR : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators)
    (a b : PreLieDifferenceStableQuotient) :
    correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR (a + b) =
      correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR a +
        correctedCounit_quot_of_globalNatCountBalance_and_preserves hbal hL hR b :=
  map_add _ _ _

/--
Convenient package for a global `Nat`-count-balance witness.
-/
structure CorrectedCounitGlobalNatBalanceWitness where
  flatmapNatCountBalanced : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced

/--
Convert a packaged global `Nat`-count-balance witness to the original
`Int`-valued hypothesis.
-/
def CorrectedCounitGlobalNatBalanceWitness.toGlobalCountBalance
    (hw : CorrectedCounitGlobalNatBalanceWitness) :
    AllPreLieDifferenceGeneratorFlatmapsCountBalanced :=
  (allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2
    hw.flatmapNatCountBalanced

/--
The induced global higher `Nat`-count-balance witness obtained by graft
propagation.
-/
def CorrectedCounitGlobalNatBalanceWitness.toGlobalGraftNatCountBalance
    (hw : CorrectedCounitGlobalNatBalanceWitness) :
    AllGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced :=
  allGraftPreLieDifferenceGeneratorFlatmapsNatCountBalanced_of_allPreLieDifferenceGeneratorFlatmapsNatCountBalanced
    hw.flatmapNatCountBalanced

/--
The packaged witness immediately implies generator-level corrected-counit
vanishing.
-/
theorem CorrectedCounitGlobalNatBalanceWitness.generator_vanishes
    (hw : CorrectedCounitGlobalNatBalanceWitness)
    (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  exact correctedCounit_linear_preLieDifferenceGenerators_of_globalNatCountBalance
    hw.flatmapNatCountBalanced x y z

/--
The packaged witness also implies the one-step-grafted generator-level
vanishing theorem.
-/
theorem CorrectedCounitGlobalNatBalanceWitness.grafted_generator_vanishes
    (hw : CorrectedCounitGlobalNatBalanceWitness)
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  exact correctedCounit_linear_graft_preLieDifferenceGenerators_of_globalNatCountBalance
    hw.flatmapNatCountBalanced u x y z

/--
The packaged witness kills the entire concrete pre-Lie defect submodule.
-/
theorem CorrectedCounitGlobalNatBalanceWitness.kills_preLieDifferenceSubmodule
    (hw : CorrectedCounitGlobalNatBalanceWitness)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_preLieDifferenceSubmodule_of_globalNatCountBalance
    hw.flatmapNatCountBalanced ha

/--
Convenient package for the full assumption set needed to descend the corrected
counit to the stable quotient via the already-proved quotient-equality theorem.
-/
structure CorrectedCounitStableDescentWitness where
  flatmapNatCountBalanced : AllPreLieDifferenceGeneratorFlatmapsNatCountBalanced
  preserveLeft : GraftPreLiePreservesPreLieDifferenceLeftOnTreeGenerators
  preserveRight : GraftPreLiePreservesPreLieDifferenceRightOnTreeGenerators

/--
Extract the original `Int`-valued base balance hypothesis from a stable-descent
witness.
-/
def CorrectedCounitStableDescentWitness.toGlobalCountBalance
    (hw : CorrectedCounitStableDescentWitness) :
    AllPreLieDifferenceGeneratorFlatmapsCountBalanced :=
  (allPreLieDifferenceGeneratorFlatmapsCountBalanced_iff_natCountBalanced).2
    hw.flatmapNatCountBalanced

/--
The stable-descent witness identifies the stable closure with the concrete
pre-Lie defect submodule.
-/
theorem CorrectedCounitStableDescentWitness.stable_eq
    (hw : CorrectedCounitStableDescentWitness) :
    preLieDifferenceStableSubmodule = preLieDifferenceSubmodule := by
  exact preLieDifferenceStableSubmodule_eq_preLieDifferenceSubmodule
    hw.preserveLeft hw.preserveRight

/--
Under the packaged assumptions, the corrected counit kills the stable
submodule.
-/
theorem CorrectedCounitStableDescentWitness.kills_stableSubmodule
    (hw : CorrectedCounitStableDescentWitness)
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  exact correctedCounit_linear_kills_stableSubmodule_of_globalNatCountBalance_and_preserves
    hw.flatmapNatCountBalanced hw.preserveLeft hw.preserveRight ha

/--
The descended corrected counit obtained from a stable-descent witness.
-/
noncomputable def CorrectedCounitStableDescentWitness.quot
    (hw : CorrectedCounitStableDescentWitness) :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  correctedCounit_quot_of_globalNatCountBalance_and_preserves
    hw.flatmapNatCountBalanced hw.preserveLeft hw.preserveRight

@[simp] theorem CorrectedCounitStableDescentWitness.quot_mk
    (hw : CorrectedCounitStableDescentWitness)
    (a : linearProofTreeCarrier) :
    hw.quot (mkPreLieDifferenceStableQuotient a) = correctedCounit_linear a := by
  simp [CorrectedCounitStableDescentWitness.quot]

@[simp] theorem CorrectedCounitStableDescentWitness.quot_treeGen
    (hw : CorrectedCounitStableDescentWitness)
    (t : PTree) :
    hw.quot (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp [CorrectedCounitStableDescentWitness.quot]

@[simp] theorem CorrectedCounitStableDescentWitness.quot_forestGen
    (hw : CorrectedCounitStableDescentWitness)
    (f : Forest) :
    hw.quot (mkPreLieDifferenceStableQuotient (forestGen f)) = (f.length : ℤ) := by
  induction f with
  | nil =>
      simp [CorrectedCounitStableDescentWitness.quot_mk]
  | cons t ts ih =>
      simp [forestGen_cons, CorrectedCounitStableDescentWitness.quot_mk, ih, add_comm]

@[simp] theorem CorrectedCounitStableDescentWitness.quot_zero
    (hw : CorrectedCounitStableDescentWitness) :
    hw.quot 0 = 0 := by
  simp [CorrectedCounitStableDescentWitness.quot]

@[simp] theorem CorrectedCounitStableDescentWitness.quot_add
    (hw : CorrectedCounitStableDescentWitness)
    (a b : PreLieDifferenceStableQuotient) :
    hw.quot (a + b) = hw.quot a + hw.quot b := by
  simp [CorrectedCounitStableDescentWitness.quot]

/-- The corrected counit descends to the stable quotient. -/
noncomputable def correctedCounit_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ] ℤ :=
  preLieDifferenceStableSubmodule.liftQ correctedCounit_linear
    (fun a ha => correctedCounit_linear_kills_stableSubmodule ha)

@[simp] theorem correctedCounit_quot_mk (a : linearProofTreeCarrier) :
    correctedCounit_quot (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_linear a := by
  simpa [correctedCounit_quot, mkPreLieDifferenceStableQuotient]
    using (Submodule.liftQ_apply
      (p := preLieDifferenceStableSubmodule)
      (f := correctedCounit_linear)
      (h := by
        intro a ha
        exact correctedCounit_linear_kills_stableSubmodule ha)
      (x := a))

@[simp] theorem correctedCounit_quot_treeGen (t : PTree) :
    correctedCounit_quot (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
  simp

@[simp] theorem correctedCounit_quot_zero :
    correctedCounit_quot 0 = 0 := map_zero _

@[simp] theorem correctedCounit_quot_add (a b : PreLieDifferenceStableQuotient) :
    correctedCounit_quot (a + b) = correctedCounit_quot a + correctedCounit_quot b :=
  map_add _ _ _

/-!
### Forest-level computation of the corrected counit

Since `forestGen [] = 0` and `forestGen (t :: ts) = treeGen t + forestGen ts`,
and `correctedCounit_linear (treeGen t) = 1` for all t, we get:
`correctedCounit_linear (forestGen f) = f.length` by induction on f.

This is a *provable* theorem (no sorry required) that gives a clean
interpretation: the corrected counit counts the number of trees in the forest.
-/

/--
The corrected counit on `forestGen f` equals the length of the forest `f`.

Proof: by induction on f, using `correctedCounit_linear_treeGen` and linearity.
-/
theorem correctedCounit_linear_forestGen (f : Forest) :
    correctedCounit_linear (forestGen f) = (f.length : ℤ) := by
  induction f with
  | nil => simp
  | cons t ts ih =>
      simp [forestGen_cons, ih, add_comm]

/--
The corrected counit on `mk(forestGen f)` equals `f.length`.
-/
theorem correctedCounit_quot_forestGen (f : Forest) :
    correctedCounit_quot (mkPreLieDifferenceStableQuotient (forestGen f)) =
      (f.length : ℤ) := by
  simp [correctedCounit_quot_mk, correctedCounit_linear_forestGen]

/--
The trivial-cut contribution: `correctedCounit_linear (forestGen []) = 0`,
consistent with `forestGen [] = 0`.
-/
@[simp] theorem correctedCounit_linear_forestGen_nil :
    correctedCounit_linear (forestGen ([] : Forest)) = 0 := by
  simp [correctedCounit_linear_forestGen]

/--
Single-tree forest: `correctedCounit_linear (forestGen [t]) = 1`.
-/
@[simp] theorem correctedCounit_linear_forestGen_singleton (t : PTree) :
    correctedCounit_linear (forestGen [t]) = 1 := by
  simp [correctedCounit_linear_forestGen]

/--
Two-tree forest: `correctedCounit_linear (forestGen [t, u]) = 2`.
-/
@[simp] theorem correctedCounit_linear_forestGen_pair (t u : PTree) :
    correctedCounit_linear (forestGen [t, u]) = 2 := by
  simp [correctedCounit_linear_forestGen]

/--
The corrected counit distributes over forest concatenation:
`correctedCounit_linear (forestGen (xs ++ ys))
  = correctedCounit_linear (forestGen xs) + correctedCounit_linear (forestGen ys)`.
-/
theorem correctedCounit_linear_forestGen_append (xs ys : Forest) :
    correctedCounit_linear (forestGen (xs ++ ys)) =
      correctedCounit_linear (forestGen xs) + correctedCounit_linear (forestGen ys) := by
  simp [correctedCounit_linear_forestGen, List.length_append, Nat.cast_add]

end CorrectedCounit

/-! ## 15. Corrected counit axioms

With the corrected counit `correctedCounit_quot`, we can now state (and
partially prove) the counit laws.  These are:

  `(correctedCounit_quot ⊗ id) ∘ Δ_quot = (1 ⊗ -)` (right counit)
  `(id ⊗ correctedCounit_quot) ∘ Δ_quot = (- ⊗ 1)` (left counit)

On a tree generator `treeGen t`:
  `Δ_quot(mk(tg t)) = mkQ_tensor(Σ_{(f,r)} forestGen(f) ⊗ treeGen(r))`

The trivial cut `([], t)` contributes `forestGen([]) ⊗ treeGen(t) = 0 ⊗ tg t = 0`.
Note: this is still zero because `forestGen([]) = 0` in `linearProofTreeCarrier`.
The counit law therefore requires summing the corrected counit over all cuts and
recovering `1 ⊗ mk(tg t)`.

This derivation requires the fact that exactly one cut `(f, r)` satisfies
`correctedCounit_linear(forestGen(f)) = 1`, namely the cut `([t], t)` where
the forest is `[t]` itself and the remainder is also `t` — but this is the
full-cut case.  Actually: the cut `(f, r)` with `f = [t]` and `r` = root
corresponds to cutting all edges, giving `forestGen([t]) = treeGen(t)` with
`correctedCounit_linear = 1`.  But the "remainder" in that cut is the root
vertex.  The details depend on the combinatorics of `coproductData`.

Small explicit computations show how the corrected counit behaves on low-depth
trees. They also reveal an obstruction: the naive global left/right counit
laws are already false on `nodeLeaf`.
-/

section CorrectedCounitAxioms

/--
The right profile of the corrected counit on a cut term: each remainder is
weighted by the number of trees in the cut forest.
-/
noncomputable def correctedCounit_rTensor_profileGen
    (p : Forest × PTree) :
    TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  TensorProduct.tmul ℤ (p.1.length : ℤ)
    (mkPreLieDifferenceStableQuotient (treeGen p.2))

/--
The left profile of the corrected counit on a cut term: each cut forest is
carried across unchanged, while each remainder contributes counit `1`.
-/
noncomputable def correctedCounit_lTensor_profileGen
    (p : Forest × PTree) :
    TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  TensorProduct.tmul ℤ
    (mkPreLieDifferenceStableQuotient (forestGen p.1)) 1

/-- The linear right profile induced from the support-summary cut expansion. -/
noncomputable def correctedCounit_rTensor_profile_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  coproductSupportSummary_sum_linear correctedCounit_rTensor_profileGen

/-- The linear left profile induced from the support-summary cut expansion. -/
noncomputable def correctedCounit_lTensor_profile_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  coproductSupportSummary_sum_linear correctedCounit_lTensor_profileGen

@[simp] theorem correctedCounit_rTensor_profile_linear_treeGen
    (t : PTree) :
    correctedCounit_rTensor_profile_linear (treeGen t) =
      coproductSupportSummary_sum t correctedCounit_rTensor_profileGen := by
  simp [correctedCounit_rTensor_profile_linear]

@[simp] theorem correctedCounit_lTensor_profile_linear_treeGen
    (t : PTree) :
    correctedCounit_lTensor_profile_linear (treeGen t) =
      coproductSupportSummary_sum t correctedCounit_lTensor_profileGen := by
  simp [correctedCounit_lTensor_profile_linear]

theorem correctedCounit_rTensor_profile_linear_apply
    (a : linearProofTreeCarrier) :
    correctedCounit_rTensor_profile_linear a =
      a.sum (fun x c => c •
        coproductSupportSummary_sum x correctedCounit_rTensor_profileGen) := by
  simp [correctedCounit_rTensor_profile_linear,
    coproductSupportSummary_sum_linear_apply]

theorem correctedCounit_lTensor_profile_linear_apply
    (a : linearProofTreeCarrier) :
    correctedCounit_lTensor_profile_linear a =
      a.sum (fun x c => c •
        coproductSupportSummary_sum x correctedCounit_lTensor_profileGen) := by
  simp [correctedCounit_lTensor_profile_linear,
    coproductSupportSummary_sum_linear_apply]

/--
The naive right counit target on raw terms: tensoring `1` on the left after
passing to the stable quotient.
-/
noncomputable def correctedCounit_rTensor_unit_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  (TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1).comp
    mkPreLieDifferenceStableQuotient

/--
The naive left counit target on raw terms: tensoring `1` on the right after
passing to the stable quotient.
-/
noncomputable def correctedCounit_lTensor_unit_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  ((TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1).comp
    mkPreLieDifferenceStableQuotient

@[simp] theorem correctedCounit_rTensor_unit_linear_treeGen
    (t : PTree) :
    correctedCounit_rTensor_unit_linear (treeGen t) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  change (TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1)
      (mkPreLieDifferenceStableQuotient (treeGen t)) =
    TensorProduct.tmul ℤ 1
      (mkPreLieDifferenceStableQuotient (treeGen t))
  simp [correctedCounit_rTensor_unit_linear, LinearMap.comp_apply,
    TensorProduct.mk_apply]

@[simp] theorem correctedCounit_lTensor_unit_linear_treeGen
    (t : PTree) :
    correctedCounit_lTensor_unit_linear (treeGen t) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen t)) 1 := by
  change ((TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1)
      (mkPreLieDifferenceStableQuotient (treeGen t)) =
    TensorProduct.tmul ℤ
      (mkPreLieDifferenceStableQuotient (treeGen t)) 1
  simp [correctedCounit_lTensor_unit_linear, LinearMap.comp_apply,
    TensorProduct.mk_apply]

/--
The right error profile measures the failure of the corrected counit to satisfy
the naive right counit law on raw terms.
-/
noncomputable def correctedCounit_rTensor_error_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  correctedCounit_rTensor_profile_linear - correctedCounit_rTensor_unit_linear

/--
The left error profile measures the failure of the corrected counit to satisfy
the naive left counit law on raw terms.
-/
noncomputable def correctedCounit_lTensor_error_linear :
    linearProofTreeCarrier →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  correctedCounit_lTensor_profile_linear - correctedCounit_lTensor_unit_linear

@[simp] theorem correctedCounit_rTensor_error_linear_treeGen
    (t : PTree) :
    correctedCounit_rTensor_error_linear (treeGen t) =
      correctedCounit_rTensor_profile_linear (treeGen t) -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  simp [correctedCounit_rTensor_error_linear]

@[simp] theorem correctedCounit_lTensor_error_linear_treeGen
    (t : PTree) :
    correctedCounit_lTensor_error_linear (treeGen t) =
      correctedCounit_lTensor_profile_linear (treeGen t) -
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen t)) 1 := by
  simp [correctedCounit_lTensor_error_linear]

/--
On an arbitrary raw linear combination, the corrected right counit after
`Δ_quot` is exactly the right profile linear map.
-/
theorem correctedCounit_rTensor_comp_comul_mk
    (a : linearProofTreeCarrier) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) =
      correctedCounit_rTensor_profile_linear a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp
  | add f g hf hg =>
      rw [mkPreLieDifferenceStableQuotient.map_add, Δ_quot_add]
      rw [LinearMap.map_add]
      rw [hf, hg]
      simpa using
        (correctedCounit_rTensor_profile_linear.map_add f g)
  | single x n =>
      have hgen :
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) =
            correctedCounit_rTensor_profile_linear (treeGen x) := by
        rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_treeGen,
          correctedCounit_rTensor_profile_linear_treeGen]
        simp [correctedCounit_rTensor_profileGen, coproductSupportSummary_tensorGen,
          correctedCounit_quot_mk, correctedCounit_linear_forestGen]
      have hq :
          mkPreLieDifferenceStableQuotient (Finsupp.single x n) =
            n • mkPreLieDifferenceStableQuotient (treeGen x) := by
        simpa [treeGen] using
          (mkPreLieDifferenceStableQuotient.map_smul n (treeGen x))
      have hmap :
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              (n • Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) =
            n •
              (LinearMap.rTensor
                PreLieDifferenceStableQuotient correctedCounit_quot)
                (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) := by
        simpa using
          ((LinearMap.rTensor
            PreLieDifferenceStableQuotient correctedCounit_quot).map_smul n
              (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))))
      have hprofile :
          correctedCounit_rTensor_profile_linear (Finsupp.single x n) =
            n • correctedCounit_rTensor_profile_linear (treeGen x) := by
        calc
          correctedCounit_rTensor_profile_linear (Finsupp.single x n) =
              correctedCounit_rTensor_profile_linear (n • treeGen x) := by
            simp [treeGen]
          _ = n • correctedCounit_rTensor_profile_linear (treeGen x) := by
            simp
      rw [hq, Δ_quot_smul, hmap, hprofile]
      exact congrArg (fun q => n • q) hgen

/--
On an arbitrary raw linear combination, the corrected left counit after
`Δ_quot` is exactly the left profile linear map.
-/
theorem correctedCounit_lTensor_comp_comul_mk
    (a : linearProofTreeCarrier) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) =
      correctedCounit_lTensor_profile_linear a := by
  induction a using Finsupp.induction_linear with
  | zero =>
      simp
  | add f g hf hg =>
      rw [mkPreLieDifferenceStableQuotient.map_add, Δ_quot_add]
      rw [LinearMap.map_add]
      rw [hf, hg]
      simpa using
        (correctedCounit_lTensor_profile_linear.map_add f g)
  | single x n =>
      have hgen :
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) =
            correctedCounit_lTensor_profile_linear (treeGen x) := by
        rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_treeGen,
          correctedCounit_lTensor_profile_linear_treeGen]
        simp [correctedCounit_lTensor_profileGen, coproductSupportSummary_tensorGen,
          correctedCounit_quot_treeGen]
      have hq :
          mkPreLieDifferenceStableQuotient (Finsupp.single x n) =
            n • mkPreLieDifferenceStableQuotient (treeGen x) := by
        simpa [treeGen] using
          (mkPreLieDifferenceStableQuotient.map_smul n (treeGen x))
      have hmap :
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              (n • Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) =
            n •
              (LinearMap.lTensor
                PreLieDifferenceStableQuotient correctedCounit_quot)
                (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))) := by
        simpa using
          ((LinearMap.lTensor
            PreLieDifferenceStableQuotient correctedCounit_quot).map_smul n
              (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen x))))
      have hprofile :
          correctedCounit_lTensor_profile_linear (Finsupp.single x n) =
            n • correctedCounit_lTensor_profile_linear (treeGen x) := by
        calc
          correctedCounit_lTensor_profile_linear (Finsupp.single x n) =
              correctedCounit_lTensor_profile_linear (n • treeGen x) := by
            simp [treeGen]
          _ = n • correctedCounit_lTensor_profile_linear (treeGen x) := by
            simp
      rw [hq, Δ_quot_smul, hmap, hprofile]
      exact congrArg (fun q => n • q) hgen

/--
On raw terms, the corrected right counit composite splits as the naive unit
term plus an explicit right error profile.
-/
theorem correctedCounit_rTensor_comp_comul_mk_eq_unit_add_error
    (a : linearProofTreeCarrier) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) =
      correctedCounit_rTensor_unit_linear a +
        correctedCounit_rTensor_error_linear a := by
  rw [correctedCounit_rTensor_comp_comul_mk]
  change correctedCounit_rTensor_profile_linear a =
    correctedCounit_rTensor_unit_linear a +
      (correctedCounit_rTensor_profile_linear a -
        correctedCounit_rTensor_unit_linear a)
  abel

/--
On raw terms, the corrected left counit composite splits as the naive unit
term plus an explicit left error profile.
-/
theorem correctedCounit_lTensor_comp_comul_mk_eq_unit_add_error
    (a : linearProofTreeCarrier) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) =
      correctedCounit_lTensor_unit_linear a +
        correctedCounit_lTensor_error_linear a := by
  rw [correctedCounit_lTensor_comp_comul_mk]
  change correctedCounit_lTensor_profile_linear a =
    correctedCounit_lTensor_unit_linear a +
      (correctedCounit_lTensor_profile_linear a -
        correctedCounit_lTensor_unit_linear a)
  abel

/--
The naive right counit target viewed directly on the stable quotient.
Proof-theoretically, this is the "no detached subproofs" structural term.
-/
noncomputable def correctedCounit_rTensor_unit_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1

/--
The naive left counit target viewed directly on the stable quotient.
-/
noncomputable def correctedCounit_lTensor_unit_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  (TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1

@[simp] theorem correctedCounit_rTensor_unit_quot_mk
    (a : linearProofTreeCarrier) :
    correctedCounit_rTensor_unit_quot (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_rTensor_unit_linear a := by
  rfl

@[simp] theorem correctedCounit_lTensor_unit_quot_mk
    (a : linearProofTreeCarrier) :
    correctedCounit_lTensor_unit_quot (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_lTensor_unit_linear a := by
  rfl

/--
The quotient-level right error map: the actual corrected-counit composite minus
the naive structural unit term.
-/
noncomputable def correctedCounit_rTensor_error_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ ℤ PreLieDifferenceStableQuotient :=
  { toFun := fun q =>
      (LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q -
        correctedCounit_rTensor_unit_quot q
    map_add' := by
      intro q r
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro n q
      change
        (LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) (n • q) -
          correctedCounit_rTensor_unit_quot (n • q) =
        n •
          ((LinearMap.comp
              (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              Δ_quot) q -
            correctedCounit_rTensor_unit_quot q)
      rw [LinearMap.map_smul, correctedCounit_rTensor_unit_quot.map_smul]
      exact (smul_sub n
        ((LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q)
        (correctedCounit_rTensor_unit_quot q)).symm }

/--
The quotient-level left error map.
-/
noncomputable def correctedCounit_lTensor_error_quot :
    PreLieDifferenceStableQuotient →ₗ[ℤ]
      TensorProduct ℤ PreLieDifferenceStableQuotient ℤ :=
  { toFun := fun q =>
      (LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q -
        correctedCounit_lTensor_unit_quot q
    map_add' := by
      intro q r
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro n q
      change
        (LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) (n • q) -
          correctedCounit_lTensor_unit_quot (n • q) =
        n •
          ((LinearMap.comp
              (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
              Δ_quot) q -
            correctedCounit_lTensor_unit_quot q)
      rw [LinearMap.map_smul, correctedCounit_lTensor_unit_quot.map_smul]
      exact (smul_sub n
        ((LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q)
        (correctedCounit_lTensor_unit_quot q)).symm }

@[simp] theorem correctedCounit_rTensor_error_quot_mk
    (a : linearProofTreeCarrier) :
    correctedCounit_rTensor_error_quot (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_rTensor_error_linear a := by
  change
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) -
      correctedCounit_rTensor_unit_quot (mkPreLieDifferenceStableQuotient a) =
    correctedCounit_rTensor_error_linear a
  rw [correctedCounit_rTensor_comp_comul_mk, correctedCounit_rTensor_unit_quot_mk]
  rfl

@[simp] theorem correctedCounit_lTensor_error_quot_mk
    (a : linearProofTreeCarrier) :
    correctedCounit_lTensor_error_quot (mkPreLieDifferenceStableQuotient a) =
      correctedCounit_lTensor_error_linear a := by
  change
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient a)) -
      correctedCounit_lTensor_unit_quot (mkPreLieDifferenceStableQuotient a) =
    correctedCounit_lTensor_error_linear a
  rw [correctedCounit_lTensor_comp_comul_mk, correctedCounit_lTensor_unit_quot_mk]
  rfl

/--
On the quotient, the corrected right counit composite splits into the naive
structural unit term plus an explicit quotient-level error.
-/
theorem correctedCounit_rTensor_comp_comul_eq_unit_add_error :
    ∀ q : PreLieDifferenceStableQuotient,
      (LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q =
        correctedCounit_rTensor_unit_quot q +
          correctedCounit_rTensor_error_quot q := by
  intro q
  simp [correctedCounit_rTensor_error_quot]

/--
On the quotient, the corrected left counit composite splits into the naive
structural unit term plus an explicit quotient-level error.
-/
theorem correctedCounit_lTensor_comp_comul_eq_unit_add_error :
    ∀ q : PreLieDifferenceStableQuotient,
      (LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q =
        correctedCounit_lTensor_unit_quot q +
          correctedCounit_lTensor_error_quot q := by
  intro q
  simp [correctedCounit_lTensor_error_quot]

/--
Linear-map form of the quotient-level right counit decomposition.
-/
theorem correctedCounit_rTensor_comp_comul_eq_unit_add_error_linearMap :
    LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      correctedCounit_rTensor_unit_quot + correctedCounit_rTensor_error_quot := by
  apply LinearMap.ext
  intro q
  exact correctedCounit_rTensor_comp_comul_eq_unit_add_error q

/--
Linear-map form of the quotient-level left counit decomposition.
-/
theorem correctedCounit_lTensor_comp_comul_eq_unit_add_error_linearMap :
    LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      correctedCounit_lTensor_unit_quot + correctedCounit_lTensor_error_quot := by
  apply LinearMap.ext
  intro q
  exact correctedCounit_lTensor_comp_comul_eq_unit_add_error q

/--
Applying the corrected right counit to `Δ_quot` on a generator evaluates the
support-sum cut formula by collapsing each cut forest with `correctedCounit_quot`.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_cutFormula
    (t : PTree) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      coproductSupportSummary_sum t
        (fun p =>
          TensorProduct.tmul ℤ
            (correctedCounit_quot
              (mkPreLieDifferenceStableQuotient (forestGen p.1)))
            (mkPreLieDifferenceStableQuotient (treeGen p.2))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_treeGen]
  simp [coproductSupportSummary_tensorGen]

/--
Applying the corrected right counit to `Δ_quot` on a generator weights each
remainder by the number of trees in the corresponding cut forest.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_lengthWeighted
    (t : PTree) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      coproductSupportSummary_sum t
        (fun p =>
          TensorProduct.tmul ℤ (p.1.length : ℤ)
            (mkPreLieDifferenceStableQuotient (treeGen p.2))) := by
  rw [correctedCounit_rTensor_comp_comul_treeGen_cutFormula]
  unfold coproductSupportSummary_sum
  refine Finset.sum_congr rfl ?_
  intro p hp
  simp [correctedCounit_quot_mk, correctedCounit_linear_forestGen]

/--
Applying the corrected left counit to `Δ_quot` on a generator evaluates the
support-sum cut formula by sending every remainder generator to `1`.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_cutFormula
    (t : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      coproductSupportSummary_sum t
        (fun p =>
          TensorProduct.tmul ℤ
            (mkPreLieDifferenceStableQuotient (forestGen p.1))
            (correctedCounit_quot
              (mkPreLieDifferenceStableQuotient (treeGen p.2)))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_treeGen]
  simp [coproductSupportSummary_tensorGen]

/--
Applying the corrected left counit to `Δ_quot` on a generator simply sums the
quotient classes of the cut forests, since every remainder tree has counit `1`.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_forestSum
    (t : PTree) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      coproductSupportSummary_sum t
        (fun p =>
          TensorProduct.tmul ℤ
            (mkPreLieDifferenceStableQuotient (forestGen p.1)) 1) := by
  rw [correctedCounit_lTensor_comp_comul_treeGen_cutFormula]
  simp

/--
On generators, the right defect is exactly the length-weighted cut profile
minus the naive structural unit term.
-/
theorem correctedCounit_rTensor_error_linear_treeGen_cutFormula
    (t : PTree) :
    correctedCounit_rTensor_error_linear (treeGen t) =
      coproductSupportSummary_sum t correctedCounit_rTensor_profileGen -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    correctedCounit_rTensor_profile_linear_treeGen]

/--
On generators, the left defect is exactly the forest-sum cut profile minus the
naive structural unit term.
-/
theorem correctedCounit_lTensor_error_linear_treeGen_cutFormula
    (t : PTree) :
    correctedCounit_lTensor_error_linear (treeGen t) =
      coproductSupportSummary_sum t correctedCounit_lTensor_profileGen -
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen t)) 1 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    correctedCounit_lTensor_profile_linear_treeGen]

/--
Quotient-level generator form of the right defect cut formula.
-/
theorem correctedCounit_rTensor_error_quot_treeGen_cutFormula
    (t : PTree) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen t)) =
      coproductSupportSummary_sum t correctedCounit_rTensor_profileGen -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_cutFormula]

/--
Quotient-level generator form of the left defect cut formula.
-/
theorem correctedCounit_lTensor_error_quot_treeGen_cutFormula
    (t : PTree) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen t)) =
      coproductSupportSummary_sum t correctedCounit_lTensor_profileGen -
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen t)) 1 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_cutFormula]

/--
On a leaf generator, the corrected right counit computation is explicit.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_leaf
    (s : MultiSequent) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_leaf,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp

/--
On a leaf generator, the corrected left counit computation is also explicit.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_leaf
    (s : MultiSequent) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) 1 := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_leaf,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp

/--
On a stump, applying the corrected right counit to the first tensor factor
returns the leaf remainder explicitly.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (stump r s)))) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_stump,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp

/--
On a stump, applying the corrected left counit to the second tensor factor
returns the stump generator explicitly.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (stump r s)))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) 1 := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_stump,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp

/--
The naive right counit target is exact on leaves.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_leaf_eq_unit
    (s : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) =
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  change
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))
  simpa using correctedCounit_rTensor_comp_comul_treeGen_leaf s

/--
The naive left counit target is exact on leaves.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_leaf_eq_unit
    (s : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) =
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  change
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) 1
  simpa using correctedCounit_lTensor_comp_comul_treeGen_leaf s

/--
The naive left counit target is also exact on stumps.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_stump_eq_unit
    (r : RuleTag) (s : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) =
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) := by
  change
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (stump r s)))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) 1
  simpa using correctedCounit_lTensor_comp_comul_treeGen_stump r s

/--
For a one-leaf-child tree, the corrected right counit produces the two explicit
right-side terms coming from the non-zero admissible cuts.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeLeaf,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/--
For a one-leaf-child tree, the corrected left counit produces the two explicit
left-side terms coming from the non-zero admissible cuts.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) 1 := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeLeaf,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/--
For a one-stump-child tree, the corrected right counit produces the two
explicit right-side terms coming from the non-zero admissible cuts.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s')))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeStump,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/--
For a one-stump-child tree, the corrected left counit produces the two
explicit left-side terms coming from the non-zero admissible cuts.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s')))) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (stump r' s'))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) 1 := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeStump,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/--
For a depth-2 tree with a `nodeLeaf` child, the corrected right counit
produces the three explicit right-side terms from the non-zero admissible cuts.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient
            (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s₁))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeNodeLeaf,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/--
For a depth-2 tree with a `nodeLeaf` child, the corrected left counit
produces the three explicit left-side terms from the non-zero admissible cuts.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)))) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s₂))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r₁ s₁ s₂))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient
            (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) 1 := by
  rw [Δ_quot_mk_treeGen, coproductSupportSummary_comul_linear_nodeNodeLeaf,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_add,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul,
    mkPreLieDifferenceStableQuotient_tensor_tmul]
  simp [add_assoc]

/-- The right error term vanishes on leaf generators. -/
theorem correctedCounit_rTensor_error_linear_treeGen_leaf
    (s : MultiSequent) :
    correctedCounit_rTensor_error_linear (treeGen (PTree.leaf s)) = 0 := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    ← correctedCounit_rTensor_comp_comul_mk (treeGen (PTree.leaf s)),
    correctedCounit_rTensor_comp_comul_treeGen_leaf]
  abel

/-- The left error term vanishes on leaf generators. -/
theorem correctedCounit_lTensor_error_linear_treeGen_leaf
    (s : MultiSequent) :
    correctedCounit_lTensor_error_linear (treeGen (PTree.leaf s)) = 0 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    ← correctedCounit_lTensor_comp_comul_mk (treeGen (PTree.leaf s)),
    correctedCounit_lTensor_comp_comul_treeGen_leaf]
  abel

/--
On a stump, the right error term is the difference between the leaf remainder
and the naive unit term on the stump itself.
-/
theorem correctedCounit_rTensor_error_linear_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    correctedCounit_rTensor_error_linear (treeGen (stump r s)) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    ← correctedCounit_rTensor_comp_comul_mk (treeGen (stump r s)),
    correctedCounit_rTensor_comp_comul_treeGen_stump]

/-- The left error term still vanishes on stump generators. -/
theorem correctedCounit_lTensor_error_linear_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    correctedCounit_lTensor_error_linear (treeGen (stump r s)) = 0 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    ← correctedCounit_lTensor_comp_comul_mk (treeGen (stump r s)),
    correctedCounit_lTensor_comp_comul_treeGen_stump]
  abel

/--
For `nodeLeaf`, the right error term is exactly the extra root-leaf contribution.
-/
theorem correctedCounit_rTensor_error_linear_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_rTensor_error_linear (treeGen (nodeLeaf r s s')) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    ← correctedCounit_rTensor_comp_comul_mk (treeGen (nodeLeaf r s s')),
    correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf]
  abel

/--
For `nodeLeaf`, the left error term is exactly the extra child-leaf contribution.
-/
theorem correctedCounit_lTensor_error_linear_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_lTensor_error_linear (treeGen (nodeLeaf r s s')) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) 1 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    ← correctedCounit_lTensor_comp_comul_mk (treeGen (nodeLeaf r s s')),
    correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf]
  abel

/--
For `nodeStump`, the right error term consists of the `nodeLeaf` remainder and
the extra root-leaf contribution, minus the naive unit term.
-/
theorem correctedCounit_rTensor_error_linear_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_rTensor_error_linear (treeGen (nodeStump r s r' s')) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    ← correctedCounit_rTensor_comp_comul_mk (treeGen (nodeStump r s r' s')),
    correctedCounit_rTensor_comp_comul_treeGen_nodeStump]

/--
For `nodeStump`, the left error term is exactly the extra child-stump
contribution.
-/
theorem correctedCounit_lTensor_error_linear_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_lTensor_error_linear (treeGen (nodeStump r s r' s')) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (stump r' s'))) 1 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    ← correctedCounit_lTensor_comp_comul_mk (treeGen (nodeStump r s r' s')),
    correctedCounit_lTensor_comp_comul_treeGen_nodeStump]
  abel

/--
For `nodeNodeLeaf`, the right error term is the sum of the intermediate
`nodeLeaf` remainder and the extra root-leaf contribution.
-/
theorem correctedCounit_rTensor_error_linear_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_rTensor_error_linear
        (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s₁))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [correctedCounit_rTensor_error_linear_treeGen,
    ← correctedCounit_rTensor_comp_comul_mk
      (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)),
    correctedCounit_rTensor_comp_comul_treeGen_nodeNodeLeaf]
  abel

/--
For `nodeNodeLeaf`, the left error term is the sum of the child-leaf and
intermediate `nodeLeaf` contributions.
-/
theorem correctedCounit_lTensor_error_linear_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_lTensor_error_linear
        (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s₂))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r₁ s₁ s₂))) 1 := by
  rw [correctedCounit_lTensor_error_linear_treeGen,
    ← correctedCounit_lTensor_comp_comul_mk
      (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)),
    correctedCounit_lTensor_comp_comul_treeGen_nodeNodeLeaf]
  abel

@[simp] theorem correctedCounit_rTensor_error_quot_treeGen_leaf
    (s : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 0 := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_leaf]

@[simp] theorem correctedCounit_lTensor_error_quot_treeGen_leaf
    (s : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 0 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_leaf]

@[simp] theorem correctedCounit_rTensor_error_quot_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_stump]

@[simp] theorem correctedCounit_lTensor_error_quot_treeGen_stump
    (r : RuleTag) (s : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) = 0 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_stump]

@[simp] theorem correctedCounit_rTensor_error_quot_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) =
      TensorProduct.tmul ℤ 1
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_nodeLeaf]

@[simp] theorem correctedCounit_lTensor_error_quot_treeGen_nodeLeaf
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) 1 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_nodeLeaf]

@[simp] theorem correctedCounit_rTensor_error_quot_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) -
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_nodeStump]

@[simp] theorem correctedCounit_lTensor_error_quot_treeGen_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) =
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (stump r' s'))) 1 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_nodeStump]

@[simp] theorem correctedCounit_rTensor_error_quot_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) =
      TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s₁))) +
        TensorProduct.tmul ℤ 1
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) := by
  rw [correctedCounit_rTensor_error_quot_mk,
    correctedCounit_rTensor_error_linear_treeGen_nodeNodeLeaf]

@[simp] theorem correctedCounit_lTensor_error_quot_treeGen_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s₂))) 1 +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r₁ s₁ s₂))) 1 := by
  rw [correctedCounit_lTensor_error_quot_mk,
    correctedCounit_lTensor_error_linear_treeGen_nodeNodeLeaf]

/-- The right defect is already nonzero on `nodeLeaf`. -/
theorem correctedCounit_rTensor_error_quot_treeGen_nodeLeaf_ne_zero
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_rTensor_error_quot_treeGen_nodeLeaf r s s'
  rw [h] at hEq
  have hq :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
    simpa using (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s)
  rw [hq, correctedCounit_quot_zero] at hone
  norm_num at hone

/-- The left defect is already nonzero on `nodeLeaf`. -/
theorem correctedCounit_lTensor_error_quot_treeGen_nodeLeaf_ne_zero
    (r : RuleTag) (s s' : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_lTensor_error_quot_treeGen_nodeLeaf r s s'
  rw [h] at hEq
  have hq :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s')) = 0 := by
    simpa using (congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s')
  rw [hq, correctedCounit_quot_zero] at hone
  norm_num at hone

/-- The right defect remains nonzero on `nodeStump`. -/
theorem correctedCounit_rTensor_error_quot_treeGen_nodeStump_ne_zero
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_rTensor_error_quot_treeGen_nodeStump r s r' s'
  rw [h] at hEq
  have hq := (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hcount : (1 : ℤ) = 0 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg correctedCounit_quot hq
  norm_num at hcount

/-- The left defect remains nonzero on `nodeStump`. -/
theorem correctedCounit_lTensor_error_quot_treeGen_nodeStump_ne_zero
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_lTensor_error_quot_treeGen_nodeStump r s r' s'
  rw [h] at hEq
  have hq :
      mkPreLieDifferenceStableQuotient (treeGen (stump r' s')) = 0 := by
    simpa using (congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (stump r' s'))) = 1 := by
    simpa using correctedCounit_quot_treeGen (stump r' s')
  rw [hq, correctedCounit_quot_zero] at hone
  norm_num at hone

/-- The right defect remains nonzero on `nodeNodeLeaf`. -/
theorem correctedCounit_rTensor_error_quot_treeGen_nodeNodeLeaf_ne_zero
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_rTensor_error_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_rTensor_error_quot_treeGen_nodeNodeLeaf r s r₁ s₁ s₂
  rw [h] at hEq
  have hq :
      mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s₁)) +
        mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
    simpa using (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hcount : (2 : ℤ) = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using congrArg correctedCounit_quot hq
  norm_num at hcount

/-- The left defect remains nonzero on `nodeNodeLeaf`. -/
theorem correctedCounit_lTensor_error_quot_treeGen_nodeNodeLeaf_ne_zero
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    correctedCounit_lTensor_error_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) ≠ 0 := by
  intro h
  have hEq := correctedCounit_lTensor_error_quot_treeGen_nodeNodeLeaf r s r₁ s₁ s₂
  rw [h] at hEq
  have hq :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s₂)) +
        mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r₁ s₁ s₂)) = 0 := by
    simpa using (congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hEq).symm
  have hcount : (2 : ℤ) = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using congrArg correctedCounit_quot hq
  norm_num at hcount

/--
Pointwise form of the right corrected-counit obstruction: at a specific quotient
element, the naive unit law holds exactly when the right defect vanishes there.
-/
theorem correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at
    (q : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot) q =
      correctedCounit_rTensor_unit_quot q ↔
    correctedCounit_rTensor_error_quot q = 0 := by
  constructor
  · intro h
    calc
      correctedCounit_rTensor_error_quot q
          =
        (LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q -
          correctedCounit_rTensor_unit_quot q := by
            simp [correctedCounit_rTensor_error_quot]
      _ = correctedCounit_rTensor_unit_quot q - correctedCounit_rTensor_unit_quot q := by
            rw [h]
      _ = 0 := sub_self _
  · intro h
    calc
      (LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q
          =
        correctedCounit_rTensor_unit_quot q + correctedCounit_rTensor_error_quot q := by
            exact correctedCounit_rTensor_comp_comul_eq_unit_add_error q
      _ = correctedCounit_rTensor_unit_quot q + 0 := by rw [h]
      _ = correctedCounit_rTensor_unit_quot q := by simp

/--
Pointwise form of the left corrected-counit obstruction: at a specific quotient
element, the naive unit law holds exactly when the left defect vanishes there.
-/
theorem correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at
    (q : PreLieDifferenceStableQuotient) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot) q =
      correctedCounit_lTensor_unit_quot q ↔
    correctedCounit_lTensor_error_quot q = 0 := by
  constructor
  · intro h
    calc
      correctedCounit_lTensor_error_quot q
          =
        (LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q -
          correctedCounit_lTensor_unit_quot q := by
            simp [correctedCounit_lTensor_error_quot]
      _ = correctedCounit_lTensor_unit_quot q - correctedCounit_lTensor_unit_quot q := by
            rw [h]
      _ = 0 := sub_self _
  · intro h
    calc
      (LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q
          =
        correctedCounit_lTensor_unit_quot q + correctedCounit_lTensor_error_quot q := by
            exact correctedCounit_lTensor_comp_comul_eq_unit_add_error q
      _ = correctedCounit_lTensor_unit_quot q + 0 := by rw [h]
      _ = correctedCounit_lTensor_unit_quot q := by simp

/-- Every generator class is nonzero in the quotient, since the corrected counit
evaluates to `1` on it. -/
theorem mkPreLieDifferenceStableQuotient_treeGen_ne_zero
    (t : PTree) :
    mkPreLieDifferenceStableQuotient (treeGen t) ≠ 0 := by
  intro h
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen t)) = 1 := by
    simpa using correctedCounit_quot_treeGen t
  rw [h, correctedCounit_quot_zero] at hone
  norm_num at hone

/--
The naive right counit law on a stump holds exactly when the stump class agrees
with the corresponding leaf class in the quotient.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_stump_eq_unit_iff
    (r : RuleTag) (s : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) =
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) ↔
    mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) =
      mkPreLieDifferenceStableQuotient (treeGen (stump r s)) := by
  constructor
  · intro h
    have herr :
        correctedCounit_rTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (stump r s))) = 0 := by
      exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h
    have hEq := correctedCounit_rTensor_error_quot_treeGen_stump r s
    rw [herr] at hEq
    have hsub :
        mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) -
          mkPreLieDifferenceStableQuotient (treeGen (stump r s)) = 0 := by
      simpa using
        (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
    exact sub_eq_zero.mp hsub
  · intro hEq
    exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).2 <| by
      simpa [hEq] using correctedCounit_rTensor_error_quot_treeGen_stump r s

/--
The naive right counit law on `nodeLeaf` holds exactly when the extra leaf term
vanishes in the quotient.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf_eq_unit_iff
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) =
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ↔
    mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
  constructor
  · intro h
    have herr :
        correctedCounit_rTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) = 0 := by
      exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h
    have hEq := correctedCounit_rTensor_error_quot_treeGen_nodeLeaf r s s'
    rw [herr] at hEq
    simpa using
      (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
  · intro hEq
    exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).2 <| by
      rw [correctedCounit_rTensor_error_quot_treeGen_nodeLeaf, hEq]
      exact
        (TensorProduct.tmul_zero
          (R := ℤ) (M := ℤ) (N := PreLieDifferenceStableQuotient) (1 : ℤ))

/--
The naive left counit law on `nodeLeaf` holds exactly when the extra child-leaf
term vanishes in the quotient.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf_eq_unit_iff
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) =
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ↔
    mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s')) = 0 := by
  constructor
  · intro h
    have herr :
        correctedCounit_lTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) = 0 := by
      exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h
    have hEq := correctedCounit_lTensor_error_quot_treeGen_nodeLeaf r s s'
    rw [herr] at hEq
    simpa using
      (congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hEq).symm
  · intro hEq
    exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).2 <| by
      rw [correctedCounit_lTensor_error_quot_treeGen_nodeLeaf, hEq]
      exact
        (TensorProduct.zero_tmul
          (R := ℤ) (M := PreLieDifferenceStableQuotient) (N := ℤ) (1 : ℤ))

/--
The naive left counit law on `nodeStump` holds exactly when the child stump
class vanishes in the quotient.
-/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeStump_eq_unit_iff
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) =
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ↔
    mkPreLieDifferenceStableQuotient (treeGen (stump r' s')) = 0 := by
  constructor
  · intro h
    have herr :
        correctedCounit_lTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) = 0 := by
      exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h
    have hEq := correctedCounit_lTensor_error_quot_treeGen_nodeStump r s r' s'
    rw [herr] at hEq
    simpa using
      (congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hEq).symm
  · intro hEq
    exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).2 <| by
      rw [correctedCounit_lTensor_error_quot_treeGen_nodeStump, hEq]
      exact
        (TensorProduct.zero_tmul
          (R := ℤ) (M := PreLieDifferenceStableQuotient) (N := ℤ) (1 : ℤ))

/--
The naive right counit law on `nodeStump` holds exactly when the quotient
identifies the stump with the sum of its two visible right-side residues.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeStump_eq_unit_iff
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) =
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ↔
    mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) +
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) =
        mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s')) := by
  constructor
  · intro h
    have herr :
        correctedCounit_rTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) = 0 := by
      exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h
    have hEq := correctedCounit_rTensor_error_quot_treeGen_nodeStump r s r' s'
    rw [herr] at hEq
    have hsub :
        mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) +
          mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) -
          mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s')) = 0 := by
      simpa using
        (congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hEq).symm
    exact sub_eq_zero.mp hsub
  · intro hEq
    exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).2 <| by
      rw [correctedCounit_rTensor_error_quot_treeGen_nodeStump,
        ← TensorProduct.tmul_add, hEq]
      simp

/-- The naive right counit law already fails on `nodeLeaf`. -/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf_ne_unit
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ≠
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) := by
  intro h
  exact correctedCounit_rTensor_error_quot_treeGen_nodeLeaf_ne_zero r s s'
    ((correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/-- The naive left counit law already fails on `nodeLeaf`. -/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf_ne_unit
    (r : RuleTag) (s s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) ≠
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) := by
  intro h
  exact correctedCounit_lTensor_error_quot_treeGen_nodeLeaf_ne_zero r s s'
    ((correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/-- The naive right counit law also fails on `nodeStump`. -/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeStump_ne_unit
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ≠
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) := by
  intro h
  exact correctedCounit_rTensor_error_quot_treeGen_nodeStump_ne_zero r s r' s'
    ((correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/-- The naive left counit law also fails on `nodeStump`. -/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeStump_ne_unit
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) ≠
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient (treeGen (nodeStump r s r' s'))) := by
  intro h
  exact correctedCounit_lTensor_error_quot_treeGen_nodeStump_ne_zero r s r' s'
    ((correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/-- The naive right counit law also fails on `nodeNodeLeaf`. -/
theorem correctedCounit_rTensor_comp_comul_treeGen_nodeNodeLeaf_ne_unit
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) ≠
      correctedCounit_rTensor_unit_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) := by
  intro h
  exact correctedCounit_rTensor_error_quot_treeGen_nodeNodeLeaf_ne_zero r s r₁ s₁ s₂
    ((correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/-- The naive left counit law also fails on `nodeNodeLeaf`. -/
theorem correctedCounit_lTensor_comp_comul_treeGen_nodeNodeLeaf_ne_unit
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) ≠
      correctedCounit_lTensor_unit_quot
        (mkPreLieDifferenceStableQuotient
          (treeGen (nodeNodeLeaf r s r₁ s₁ s₂))) := by
  intro h
  exact correctedCounit_lTensor_error_quot_treeGen_nodeNodeLeaf_ne_zero r s r₁ s₁ s₂
    ((correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at _).1 h)

/--
The naive right corrected-counit law holds exactly when the right error map
vanishes.
-/
theorem correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero :
    LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      correctedCounit_rTensor_unit_quot ↔
    correctedCounit_rTensor_error_quot = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro q
    calc
      correctedCounit_rTensor_error_quot q
          =
        (LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q -
          correctedCounit_rTensor_unit_quot q := by
            simp [correctedCounit_rTensor_error_quot]
      _ = correctedCounit_rTensor_unit_quot q - correctedCounit_rTensor_unit_quot q := by
            rw [congrArg (fun f => f q) h]
            rfl
      _ = 0 := sub_self _
  · intro h
    calc
      LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot =
        correctedCounit_rTensor_unit_quot + correctedCounit_rTensor_error_quot :=
          correctedCounit_rTensor_comp_comul_eq_unit_add_error_linearMap
      _ = correctedCounit_rTensor_unit_quot + 0 := by rw [h]
      _ = correctedCounit_rTensor_unit_quot := by simp

/--
The naive left corrected-counit law holds exactly when the left error map
vanishes.
-/
theorem correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero :
    LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      correctedCounit_lTensor_unit_quot ↔
    correctedCounit_lTensor_error_quot = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro q
    calc
      correctedCounit_lTensor_error_quot q
          =
        (LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q -
          correctedCounit_lTensor_unit_quot q := by
            simp [correctedCounit_lTensor_error_quot]
      _ = correctedCounit_lTensor_unit_quot q - correctedCounit_lTensor_unit_quot q := by
            rw [congrArg (fun f => f q) h]
            rfl
      _ = 0 := sub_self _
  · intro h
    calc
      LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot =
        correctedCounit_lTensor_unit_quot + correctedCounit_lTensor_error_quot :=
          correctedCounit_lTensor_comp_comul_eq_unit_add_error_linearMap
      _ = correctedCounit_lTensor_unit_quot + 0 := by rw [h]
      _ = correctedCounit_lTensor_unit_quot := by simp

/--
Pointwise form of the right corrected-counit obstruction:
the naive right unit law holds on every quotient element exactly when the right
defect vanishes everywhere.
-/
theorem correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_forall :
    (∀ q,
        (LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q =
          correctedCounit_rTensor_unit_quot q) ↔
      ∀ q, correctedCounit_rTensor_error_quot q = 0 := by
  constructor
  · intro h q
    exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at q).1 (h q)
  · intro h q
    exact (correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero_at q).2 (h q)

/--
Pointwise form of the left corrected-counit obstruction:
the naive left unit law holds on every quotient element exactly when the left
defect vanishes everywhere.
-/
theorem correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_forall :
    (∀ q,
        (LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q =
          correctedCounit_lTensor_unit_quot q) ↔
      ∀ q, correctedCounit_lTensor_error_quot q = 0 := by
  constructor
  · intro h q
    exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at q).1 (h q)
  · intro h q
    exact (correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero_at q).2 (h q)

/--
There is a concrete quotient element on which the naive right corrected-counit
law fails.
-/
theorem correctedCounit_rTensor_comp_comul_exists_ne_unit :
    ∃ q : PreLieDifferenceStableQuotient,
      (LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q ≠
        correctedCounit_rTensor_unit_quot q := by
  let s : MultiSequent := ⟨0, 0⟩
  refine ⟨mkPreLieDifferenceStableQuotient
      (treeGen (nodeLeaf RuleTag.baseAx s s)), ?_⟩
  exact correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf_ne_unit RuleTag.baseAx s s

/--
There is a concrete quotient element on which the naive left corrected-counit
law fails.
-/
theorem correctedCounit_lTensor_comp_comul_exists_ne_unit :
    ∃ q : PreLieDifferenceStableQuotient,
      (LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot) q ≠
        correctedCounit_lTensor_unit_quot q := by
  let s : MultiSequent := ⟨0, 0⟩
  refine ⟨mkPreLieDifferenceStableQuotient
      (treeGen (nodeLeaf RuleTag.baseAx s s)), ?_⟩
  exact correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf_ne_unit RuleTag.baseAx s s

/--
The naive right corrected-counit law does not hold pointwise on all quotient
elements.
-/
theorem correctedCounit_rTensor_comp_comul_not_forall_eq_unit :
    ¬ ∀ q : PreLieDifferenceStableQuotient,
        (LinearMap.comp
            (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q =
          correctedCounit_rTensor_unit_quot q := by
  intro h
  rcases correctedCounit_rTensor_comp_comul_exists_ne_unit with ⟨q, hq⟩
  exact hq (h q)

/--
The naive left corrected-counit law does not hold pointwise on all quotient
elements.
-/
theorem correctedCounit_lTensor_comp_comul_not_forall_eq_unit :
    ¬ ∀ q : PreLieDifferenceStableQuotient,
        (LinearMap.comp
            (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
            Δ_quot) q =
          correctedCounit_lTensor_unit_quot q := by
  intro h
  rcases correctedCounit_lTensor_comp_comul_exists_ne_unit with ⟨q, hq⟩
  exact hq (h q)

/-- The right error map is genuinely non-zero. -/
theorem correctedCounit_rTensor_error_quot_ne_zero :
    correctedCounit_rTensor_error_quot ≠ 0 := by
  let s : MultiSequent := ⟨0, 0⟩
  intro h
  have hzeroTensor :
      TensorProduct.tmul ℤ (1 : ℤ)
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 0 := by
    have hEval :
        correctedCounit_rTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf RuleTag.baseAx s s))) = 0 := by
      simpa using congrArg
        (fun f =>
          f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf RuleTag.baseAx s s)))) h
    rw [correctedCounit_rTensor_error_quot_treeGen_nodeLeaf RuleTag.baseAx s s] at hEval
    exact hEval
  have hzero :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
    simpa using congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hzeroTensor
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s)
  rw [hzero, correctedCounit_quot_zero] at hone
  norm_num at hone

/-- The left error map is genuinely non-zero. -/
theorem correctedCounit_lTensor_error_quot_ne_zero :
    correctedCounit_lTensor_error_quot ≠ 0 := by
  let s : MultiSequent := ⟨0, 0⟩
  intro h
  have hzeroTensor :
      TensorProduct.tmul ℤ
        (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) (1 : ℤ) = 0 := by
    have hEval :
        correctedCounit_lTensor_error_quot
            (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf RuleTag.baseAx s s))) = 0 := by
      simpa using congrArg
        (fun f =>
          f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf RuleTag.baseAx s s)))) h
    rw [correctedCounit_lTensor_error_quot_treeGen_nodeLeaf RuleTag.baseAx s s] at hEval
    exact hEval
  have hzero :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
    simpa using congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hzeroTensor
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s)
  rw [hzero, correctedCounit_quot_zero] at hone
  norm_num at hone

/--
The proposed global corrected right counit law is already obstructed on
`nodeLeaf`: it would force the extra `leaf s` term to vanish.
-/
theorem correctedCounit_rTensor_comp_comul_obstructed
    (r : (RuleTag : Type)) (s s' : (MultiSequent : Type)) :
    LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot ≠
      TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1 := by
  intro h
  have hEq :
      LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot =
        correctedCounit_rTensor_unit_quot := by
    simpa [correctedCounit_rTensor_unit_quot] using h
  exact correctedCounit_rTensor_error_quot_ne_zero
    ((correctedCounit_rTensor_comp_comul_eq_unit_iff_error_eq_zero).1 hEq)

/--
The proposed global corrected left counit law is likewise obstructed on
`nodeLeaf`: it would force the extra child-leaf term to vanish.
-/
theorem correctedCounit_lTensor_comp_comul_obstructed
    (r : (RuleTag : Type)) (s s' : (MultiSequent : Type)) :
    LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot ≠
      (TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1 := by
  intro h
  have hEq :
      LinearMap.comp
          (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot =
        correctedCounit_lTensor_unit_quot := by
    simpa [correctedCounit_lTensor_unit_quot] using h
  exact correctedCounit_lTensor_error_quot_ne_zero
    ((correctedCounit_lTensor_comp_comul_eq_unit_iff_error_eq_zero).1 hEq)

/--
The naive global right counit law for the corrected counit is false:
`nodeLeaf` already produces an extra `leaf` term.
-/
theorem correctedCounit_rTensor_comp_comul :
    LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot ≠
      TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1 := by
  let s : MultiSequent := ⟨0, 0⟩
  intro h
  exact correctedCounit_rTensor_comp_comul_obstructed RuleTag.baseAx s s h

/--
The naive global left counit law for the corrected counit is likewise false:
`nodeLeaf` already produces an extra child-leaf term.
-/
theorem correctedCounit_lTensor_comp_comul :
    LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot ≠
      (TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1 := by
  let s : MultiSequent := ⟨0, 0⟩
  intro h
  exact correctedCounit_lTensor_comp_comul_obstructed RuleTag.baseAx s s h

/--
Conditional generator form of the naive right counit law.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen
    (h :
      LinearMap.comp
          (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          Δ_quot =
        TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1)
    (t : PTree) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      TensorProduct.tmul ℤ 1 (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  change
    (LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot)
        (mkPreLieDifferenceStableQuotient (treeGen t)) =
      (TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1)
        (mkPreLieDifferenceStableQuotient (treeGen t))
  exact
    congrArg
      (fun f =>
        f (mkPreLieDifferenceStableQuotient (treeGen t)))
      h

end CorrectedCounitAxioms

/-! ## 16. Sum-nine expansions

Continuing the pattern from sections 10–13.
-/

section SumNineExpansions

/-! ### Linearity on sum of nine tree generators -/

/-- Linearity of `comul` on a sum of nine tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_nine
    (H : CoproductSupportQuotientCoalgebra) (r s t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)) =
      H.comul (mkPreLieDifferenceStableQuotient (treeGen r)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen s)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen t)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen u)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen v)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen w)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen x)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
  have h1 :
      H.comul (mkPreLieDifferenceStableQuotient
          ((treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y) + treeGen z)) =
        H.comul (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
        H.comul (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    simpa using
      (H.comul_add_mk
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [add_assoc, H.comul_treeGen_sum_eight] using h1

/-- Tensor form of `comul` on a sum of eight tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_eight_tensor
    (H : CoproductSupportQuotientCoalgebra) (s t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen s)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen t)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen u)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen v)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_eight, H.comul_treeGen]

/-- Tensor form of `comul` on a sum of nine tree generators. -/
theorem CoproductSupportQuotientCoalgebra.comul_treeGen_sum_nine_tensor
    (H : CoproductSupportQuotientCoalgebra) (r s t u v w x y z : PTree) :
    H.comul (mkPreLieDifferenceStableQuotient
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen r)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen s)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen t)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen u)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen v)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) := by
  simp [H.comul_treeGen_sum_nine, H.comul_treeGen]

/-! ### `comul_quot_left_treeGen_sum_nine` -/

theorem coproductSupportSummary_comul_quot_left_treeGen_sum_nine
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (r s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum r coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum s coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.lTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have hrsuvwxyz8z :
      coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_left h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hrsuvwxyz8z
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_left_treeGen_sum_eight,
        coproductSupportSummary_comul_quot_left_treeGen_sum]

/-! ### `comul_quot_right_treeGen_sum_nine` -/

theorem coproductSupportSummary_comul_quot_right_treeGen_sum_nine
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (r s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum r coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum s coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum t coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum u coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum v coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum w coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum x coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum y coproductSupportSummary_tensorGen)) +
      (LinearMap.rTensor PreLieDifferenceStableQuotient
          (coproductSupportSummary_comul_quot h))
          (mkPreLieDifferenceStableQuotient_tensor
            (coproductSupportSummary_sum z coproductSupportSummary_tensorGen)) := by
  have hrsuvwxyz8z :
      coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_right h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_right_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  calc
    coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y)) +
      coproductSupportSummary_comul_quot_right h
        (mkPreLieDifferenceStableQuotient (treeGen z)) := by
      simpa [add_assoc] using hrsuvwxyz8z
    _ = _ := by
      rw [coproductSupportSummary_comul_quot_right_treeGen_sum_eight,
        coproductSupportSummary_comul_quot_right_treeGen_sum]

/-! ### `comul_quot_left_assoc_treeGen_sum_nine` -/

theorem coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_nine
    (h : CoproductSupportCoalgebraRespectsStableQuotient
      coproductSupportSummary_coalgebraData)
    (r s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum r coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum s coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum t coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum u coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum v coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum w coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum x coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum y coproductSupportSummary_tensorGen))) +
      (TensorProduct.assoc ℤ PreLieDifferenceStableQuotient
          PreLieDifferenceStableQuotient PreLieDifferenceStableQuotient).toLinearMap
          ((LinearMap.rTensor PreLieDifferenceStableQuotient
              (coproductSupportSummary_comul_quot h))
            (mkPreLieDifferenceStableQuotient_tensor
              (coproductSupportSummary_sum z coproductSupportSummary_tensorGen))) := by
  have hrsuvwxyz8z :
      coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z)) =
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y)) +
        coproductSupportSummary_comul_quot_left_assoc h
          (mkPreLieDifferenceStableQuotient (treeGen z)) := by
    have hmk :
        mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y + treeGen z) =
          mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
             treeGen w + treeGen x + treeGen y) +
            mkPreLieDifferenceStableQuotient (treeGen z) := by
      simpa using
        (mkPreLieDifferenceStableQuotient.map_add
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y) (treeGen z))
    simpa [hmk] using
      (coproductSupportSummary_comul_quot_left_assoc_add h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y))
        (mkPreLieDifferenceStableQuotient (treeGen z)))
  simp only [hrsuvwxyz8z,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum_eight,
    coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  rfl

/-- Coassociativity on a sum of nine generators via our instance. -/
theorem CoproductSupportQuotientCoalgebra.coassoc_treeGen_sum_nine_explicit
    (H : CoproductSupportQuotientCoalgebra) (r s t u v w x y z : PTree) :
    coproductSupportSummary_comul_quot_left_assoc H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) =
      coproductSupportSummary_comul_quot_left H.h
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
           treeGen w + treeGen x + treeGen y + treeGen z)) := by
  simpa using
    (H.coassoc_shorthand_apply
      (mkPreLieDifferenceStableQuotient
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
         treeGen w + treeGen x + treeGen y + treeGen z)))

end SumNineExpansions

/-! Section 17 onward now lives in Nonmonlogics.GrossmanLarssonOudomGuinHopfRigidity. -/
