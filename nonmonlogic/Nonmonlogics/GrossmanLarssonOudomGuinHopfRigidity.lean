import Mathlib.RingTheory.TensorProduct.Basic
import Nonmonlogics.GrossmanLarssonOudomGuinCoalgebra

namespace QuotientConnected.CoproductSupport

open Syntax

/-! ## 17. Oudom–Guin isomorphism scaffolding

The Oudom–Guin theorem states that the Grossman–Larsson Hopf algebra on rooted
forests is isomorphic to the universal enveloping algebra of the free pre-Lie
algebra on one generator (in the graded/completed sense).

In our setting this translates to: the descended comultiplication on
`PreLieDifferenceStableQuotient` corresponds exactly to the primitive-element
comultiplication `Δ_OG(x) = x ⊗ 1 + 1 ⊗ x` in the stable UEA.

The main gate theorem `stableUEA_OGPrimitiveRespectsStableQuotient` (from
Section 0) expresses the well-definedness of this descended comultiplication.
In this section we build the associated scaffolding.
-/

section OudomGuinScaffolding

/--
For the OG primitive generator data, the only genuine descent problem is the
comultiplication. The counit part is automatic, since the primitive generator
counit is identically zero.
-/
def stableUEA_OGPrimitiveComulRespectsStableQuotient : Prop :=
  ∀ a : linearProofTreeCarrier,
    a ∈ preLieDifferenceStableSubmodule →
      stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a = 0

/--
Hence the OG primitive counit kills the stable submodule without any further
combinatorics.
-/
theorem stableUEA_OGPrimitive_counit_kills_stableSubmodule
    (a : linearProofTreeCarrier)
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  exact congrFun (congrArg DFunLike.coe stableUEA_OGPrimitive_counit_linear_eq_zero) a

noncomputable def stableUEA_rawToUEALinear :
    LinearMap (RingHom.id Int) linearProofTreeCarrier
      preLieDifferenceStableQuotientUEA :=
  Finsupp.lsum Int (fun x : PTree =>
    (LinearMap.id : LinearMap (RingHom.id Int) Int Int).smulRight
      (stableUEA_treeGen x))

@[simp] theorem stableUEA_rawToUEALinear_treeGen
    (x : PTree) :
    stableUEA_rawToUEALinear (treeGen x) = stableUEA_treeGen x := by
  classical
  simp only [stableUEA_rawToUEALinear, treeGen, Finsupp.lsum_single,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  exact one_smul Int _

theorem stableUEA_rawToUEALinear_apply
    (a : linearProofTreeCarrier) :
    stableUEA_rawToUEALinear a =
      a.sum (fun x c => c • stableUEA_treeGen x) := by
  change
      Finsupp.sum a (fun x c =>
        ((LinearMap.id : LinearMap (RingHom.id Int) Int Int).smulRight
          (stableUEA_treeGen x)) c) =
    Finsupp.sum a (fun x c => c • stableUEA_treeGen x)
  simp [LinearMap.smulRight_apply, LinearMap.id_apply]
  rfl

@[simp] theorem stableUEA_rawToUEALinear_zero :
    stableUEA_rawToUEALinear 0 = 0 := by
  simpa using stableUEA_rawToUEALinear.map_zero

@[simp] theorem stableUEA_rawToUEALinear_add
    (a b : linearProofTreeCarrier) :
    stableUEA_rawToUEALinear (a + b) =
      stableUEA_rawToUEALinear a + stableUEA_rawToUEALinear b := by
  simpa using stableUEA_rawToUEALinear.map_add a b

@[simp] theorem stableUEA_rawToUEALinear_smul
    (n : Int) (a : linearProofTreeCarrier) :
    stableUEA_rawToUEALinear (n • a) =
      n • stableUEA_rawToUEALinear a := by
  simpa using stableUEA_rawToUEALinear.map_smul n a

theorem stableUEA_OGPrimitive_comul_linear_formula_linear
    (a : linearProofTreeCarrier) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      TensorProduct.tmul Int (stableUEA_rawToUEALinear a) 1 +
        TensorProduct.tmul Int 1 (stableUEA_rawToUEALinear a) := by
  classical
  rw [stableUEA_comul_linear_apply, stableUEA_rawToUEALinear_apply]
  simp only [stableUEA_OGPrimitiveGeneratorComulData_comulGen]
  have hsplit :
      (a.sum fun x c =>
        c • (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen x))) =
        a.sum (fun x c =>
          c • TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
            c • TensorProduct.tmul Int 1 (stableUEA_treeGen x)) := by
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact smul_add (a x)
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1)
      (TensorProduct.tmul Int 1 (stableUEA_treeGen x))
  rw [hsplit]
  simp only [Finsupp.sum, Finset.sum_add_distrib]
  congr 1
  · simpa using
      (TensorProduct.sum_tmul
        (R := Int)
        (s := a.support)
        (m := fun x => a x • stableUEA_treeGen x)
        (n := (1 : preLieDifferenceStableQuotientUEA))).symm
  · have hright :
        ∑ x ∈ a.support, a x •
            ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] stableUEA_treeGen x) =
          ∑ x ∈ a.support, (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ]
            (a x • stableUEA_treeGen x) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact
          (TensorProduct.tmul_smul
            (R := Int)
            (r := a x)
            (x := (1 : preLieDifferenceStableQuotientUEA))
            (y := stableUEA_treeGen x)).symm
    calc
      ∑ x ∈ a.support, a x •
          ((1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ] stableUEA_treeGen x)
          =
        ∑ x ∈ a.support, (1 : preLieDifferenceStableQuotientUEA) ⊗ₜ[ℤ]
          (a x • stableUEA_treeGen x) := hright
      _ = TensorProduct.tmul Int (1 : preLieDifferenceStableQuotientUEA)
            (∑ x ∈ a.support, a x • stableUEA_treeGen x) := by
          simpa using
            (TensorProduct.tmul_sum
              (R := Int)
              (m := (1 : preLieDifferenceStableQuotientUEA))
              (s := a.support)
              (n := fun x => a x • stableUEA_treeGen x)).symm

/--
The explicit linear raw-to-UEA map agrees with the older quotient-then-UEA
function on all raw tree combinations.
-/

theorem stableUEA_rawToUEALinear_eq_preLieDifferenceStableQuotientToUEA
    (a : linearProofTreeCarrier) :
    stableUEA_rawToUEALinear a = preLieDifferenceStableQuotientToUEA a := by
  classical
  induction a using Finsupp.induction_linear with
  | zero =>
      rw [stableUEA_rawToUEALinear_zero, preLieDifferenceStableQuotientToUEA_zero]
  | add f g hf hg =>
      rw [stableUEA_rawToUEALinear_add, hf, hg, ← preLieDifferenceStableQuotientToUEA_add]
  | single x n =>
      rw [show (Finsupp.single x n : linearProofTreeCarrier) = n • treeGen x by
        simp [treeGen]]
      rw [stableUEA_rawToUEALinear_smul, stableUEA_rawToUEALinear_treeGen,
        preLieDifferenceStableQuotientToUEA_smul, stableUEA_treeGen]

@[simp] theorem preLieDifferenceStableQuotientToUEA_treeGen
    (x : PTree) :
    preLieDifferenceStableQuotientToUEA (treeGen x) = stableUEA_treeGen x := by
  simp [preLieDifferenceStableQuotientToUEA, stableUEA_treeGen]

/--
For the OG primitive datum, the raw linear comultiplication depends only on the
quotient class of the input, mapped into the stable UEA.
-/
theorem stableUEA_OGPrimitive_comul_linear_formula_quot
    (a : linearProofTreeCarrier) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  rw [stableUEA_OGPrimitive_comul_linear_formula_linear a]
  simp_rw [stableUEA_rawToUEALinear_eq_preLieDifferenceStableQuotientToUEA]

/--
For the OG primitive datum, the raw linear comultiplication depends only on the
linear image of the input combination in the stable UEA.

This is the clean formula available without any further quotient-to-UEA
coherence lemmas.
-/
theorem stableUEA_OGPrimitive_comul_linear_formula
    (a : linearProofTreeCarrier) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      TensorProduct.tmul Int (stableUEA_rawToUEALinear a) 1 +
        TensorProduct.tmul Int 1 (stableUEA_rawToUEALinear a) := by
  exact stableUEA_OGPrimitive_comul_linear_formula_linear a

/--
The full OG quotient-respect condition is equivalent to the comultiplication
descent condition alone, because the counit half is already zero.
-/
theorem stableUEA_OGPrimitiveRespectsStableQuotient_iff_comul :
    stableUEA_OGPrimitiveRespectsStableQuotient ↔
      stableUEA_OGPrimitiveComulRespectsStableQuotient := by
  constructor
  · intro h a ha
    exact (h a ha).1
  · intro h
    intro a ha
    exact ⟨h a ha, stableUEA_OGPrimitive_counit_kills_stableSubmodule a ha⟩

/--
The OG primitive comultiplication data defines a map on the stable quotient
IF it respects the stable submodule.  The gate theorem certifies this.

This is now discharged directly from the explicit primitive formula:
if `a` lies in the stable submodule, then `mkPreLieDifferenceStableQuotient a = 0`,
so its image in the stable UEA is also zero, and the primitive tensor formula
collapses to zero.
-/
theorem stableUEA_OGPrimitive_comul_respectsStableQuotient_axiom :
    stableUEA_OGPrimitiveComulRespectsStableQuotient := by
  intro a ha
  have hmk : mkPreLieDifferenceStableQuotient a = 0 := by
    exact
      (Submodule.Quotient.mk_eq_zero preLieDifferenceStableSubmodule).2 ha
  have hUEA : preLieDifferenceStableQuotientToUEA a = 0 := by
    calc
      preLieDifferenceStableQuotientToUEA a
          = preLieDifferenceStableQuotientToUEA 0 := by
              simp [preLieDifferenceStableQuotientToUEA, hmk]
      _ = 0 := preLieDifferenceStableQuotientToUEA_zero
  rw [stableUEA_OGPrimitive_comul_linear_formula_quot, hUEA]
  simp

theorem stableUEA_OGPrimitive_respectsStableQuotient_axiom :
    stableUEA_OGPrimitiveRespectsStableQuotient := by
  rw [stableUEA_OGPrimitiveRespectsStableQuotient_iff_comul]
  exact stableUEA_OGPrimitive_comul_respectsStableQuotient_axiom

theorem stableUEA_OGPrimitive_respectsStableQuotient_axiom_apply
    (a : linearProofTreeCarrier)
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 ∧
      stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  exact stableUEA_OGPrimitive_respectsStableQuotient_axiom a ha

theorem stableUEA_OGPrimitive_respectsStableQuotient_axiom_comul
    (a : linearProofTreeCarrier)
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  exact (stableUEA_OGPrimitive_respectsStableQuotient_axiom a ha).1

theorem stableUEA_OGPrimitive_respectsStableQuotient_axiom_counit
    (a : linearProofTreeCarrier)
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  exact (stableUEA_OGPrimitive_respectsStableQuotient_axiom a ha).2

theorem stableUEA_OGPrimitive_respectsStableQuotient_axiom_iff :
    stableUEA_OGPrimitiveRespectsStableQuotient ↔
      stableUEA_OGPrimitiveComulRespectsStableQuotient := by
  exact stableUEA_OGPrimitiveRespectsStableQuotient_iff_comul

theorem stableUEA_OGPrimitive_remaining_goal :
    stableUEA_OGPrimitiveComulRespectsStableQuotient := by
  exact stableUEA_OGPrimitive_comul_respectsStableQuotient_axiom

/-- The descended OG primitive comultiplication (from the gate theorem). -/
noncomputable def OGPrimitiveComul :
    StableQuotientComultiplication :=
  stableUEA_OGPrimitiveComultiplication stableUEA_OGPrimitive_respectsStableQuotient_axiom

/-- The descended OG primitive comultiplication pack. -/
noncomputable def OGPrimitiveComulPack :
    StableQuotientComultiplicationPack :=
  stableUEA_OGPrimitiveComultiplicationPack
    stableUEA_OGPrimitive_respectsStableQuotient_axiom

/--
On an arbitrary raw linear combination of proof trees, the descended OG
primitive comultiplication is the standard primitive formula after mapping into
the stable UEA.
-/
theorem OGPrimitiveComul_comul_mk
    (a : linearProofTreeCarrier) :
    OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient a) =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  calc
    OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient a)
        =
      stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a := by
          change
            stableUEA_comul_descend
                stableUEA_OGPrimitiveGeneratorComulData
                stableUEA_OGPrimitive_respectsStableQuotient_axiom
                (mkPreLieDifferenceStableQuotient a) =
              stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a
          simpa [OGPrimitiveComul, stableUEA_OGPrimitiveComultiplication] using
            (stableUEA_comul_descend_mk
              stableUEA_OGPrimitiveGeneratorComulData
              stableUEA_OGPrimitive_respectsStableQuotient_axiom a)
    _ =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) :=
          stableUEA_OGPrimitive_comul_linear_formula_quot a

/--
On an arbitrary raw linear combination of proof trees, the descended OG
primitive counit vanishes.
-/
theorem OGPrimitiveComul_counit_mk
    (a : linearProofTreeCarrier) :
    OGPrimitiveComul.counit (mkPreLieDifferenceStableQuotient a) = 0 := by
  have hzero :
      stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
    exact congrFun
      (congrArg DFunLike.coe stableUEA_OGPrimitive_counit_linear_eq_zero) a
  simpa [OGPrimitiveComul, stableUEA_OGPrimitiveComultiplication] using
    (stableUEA_counit_descend_mk
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom a).trans hzero

/--
The packaged OG primitive comultiplication has the expected primitive formula
when viewed through the canonical quotient-to-UEA lift.
-/
theorem OGPrimitiveComulPack_comul_on_treeGen_via_canonicalLift
    (x : PTree) :
    OGPrimitiveComulPack.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int
        (stableUEA_canonicalLiftData.lift
          (mkPreLieDifferenceStableQuotient (treeGen x))) 1 +
        TensorProduct.tmul Int 1
          (stableUEA_canonicalLiftData.lift
            (mkPreLieDifferenceStableQuotient (treeGen x))) := by
  simpa using
    (StableQuotientComultiplicationPack_comul_on_treeGen_via
      OGPrimitiveComulPack stableUEA_canonicalLiftData x)

/--
Likewise, the packaged OG primitive counit is zero on generators when viewed
through the canonical lift interface.
-/
theorem OGPrimitiveComulPack_counit_on_treeGen_via_canonicalLift
    (x : PTree) :
    OGPrimitiveComulPack.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  simpa using
    (StableQuotientComultiplicationPack_counit_on_treeGen_via
      OGPrimitiveComulPack stableUEA_canonicalLiftData x)

/--
On tree generators, the OG comultiplication gives the primitive formula
`Δ(mk(tg x)) = stableUEA_treeGen x ⊗ 1 + 1 ⊗ stableUEA_treeGen x`.
-/
@[simp] theorem OGPrimitiveComul_comul_treeGen (x : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
        TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  stableUEA_OGPrimitiveComultiplication_comul_treeGen
    stableUEA_OGPrimitive_respectsStableQuotient_axiom x

/--
On tree generators, the OG counit is zero.
-/
@[simp] theorem OGPrimitiveComul_counit_treeGen (x : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 :=
  stableUEA_OGPrimitiveComultiplication_counit_treeGen
    stableUEA_OGPrimitive_respectsStableQuotient_axiom x

/--
Linear maps out of `PreLieDifferenceStableQuotient` are determined by their
values on the tree-generator classes.
-/
theorem PreLieDifferenceStableQuotient_linearMap_ext_treeGen
    {M : Type*} [AddCommMonoid M] [Module Int M]
    {f g : PreLieDifferenceStableQuotient →ₗ[Int] M}
    (hgen : ∀ x : PTree,
      f (mkPreLieDifferenceStableQuotient (treeGen x)) =
        g (mkPreLieDifferenceStableQuotient (treeGen x))) :
    f = g := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H a =>
      induction a using Finsupp.induction_linear with
      | zero =>
          simp
      | add a b ha hb =>
          simpa [mkPreLieDifferenceStableQuotient.map_add] using congrArg₂ (· + ·) ha hb
      | single x n =>
          have hq :
              mkPreLieDifferenceStableQuotient (Finsupp.single x n) =
                n • mkPreLieDifferenceStableQuotient (treeGen x) := by
            simpa [treeGen] using
              (mkPreLieDifferenceStableQuotient.map_smul n (treeGen x))
          change
            f (mkPreLieDifferenceStableQuotient (Finsupp.single x n)) =
              g (mkPreLieDifferenceStableQuotient (Finsupp.single x n))
          rw [hq, LinearMap.map_smul, LinearMap.map_smul, hgen x]

/--
Any quotient comultiplication with the primitive generator formula has the same
comultiplication map as `OGPrimitiveComul`.
-/
theorem stableQuotientComultiplication_comul_eq_OGPrimitive_of_generator_formula
    (Δ : StableQuotientComultiplication)
    (hcomul : ∀ x : PTree,
      Δ.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
        TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen x)) :
    Δ.comul = OGPrimitiveComul.comul := by
  apply PreLieDifferenceStableQuotient_linearMap_ext_treeGen
  intro x
  rw [hcomul x, OGPrimitiveComul_comul_treeGen]

/--
Any quotient comultiplication with zero generator counit has the same counit
map as `OGPrimitiveComul`.
-/
theorem stableQuotientComultiplication_counit_eq_OGPrimitive_of_generator_formula
    (Δ : StableQuotientComultiplication)
    (hcounit : ∀ x : PTree,
      Δ.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0) :
    Δ.counit = OGPrimitiveComul.counit := by
  apply PreLieDifferenceStableQuotient_linearMap_ext_treeGen
  intro x
  rw [hcounit x, OGPrimitiveComul_counit_treeGen]

/--
The OG primitive quotient comultiplication is canonical: any quotient
comultiplication with the expected primitive generator formula and zero
generator counit agrees with it on both structure maps.
-/
theorem stableQuotientComultiplication_eq_OGPrimitive_of_generator_formula
    (Δ : StableQuotientComultiplication)
    (hcomul : ∀ x : PTree,
      Δ.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
        TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen x))
    (hcounit : ∀ x : PTree,
      Δ.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0) :
    Δ.comul = OGPrimitiveComul.comul ∧
      Δ.counit = OGPrimitiveComul.counit := by
  exact
    ⟨stableQuotientComultiplication_comul_eq_OGPrimitive_of_generator_formula
        Δ hcomul,
      stableQuotientComultiplication_counit_eq_OGPrimitive_of_generator_formula
        Δ hcounit⟩

/--
Any packaged quotient comultiplication data agrees with the OG primitive
quotient comultiplication on both structure maps.
-/
theorem StableQuotientComultiplicationData_eq_OGPrimitive
    (D : StableQuotientComultiplicationData) :
    D.comul = OGPrimitiveComul.comul ∧
      D.counit = OGPrimitiveComul.counit := by
  exact
    stableQuotientComultiplication_eq_OGPrimitive_of_generator_formula
      D.Δ D.comul_on_generators D.counit_on_generators

/--
Likewise, any quotient comultiplication pack with the generator axioms agrees
with the OG primitive pack on both structure maps.
-/
theorem StableQuotientComultiplicationPack_eq_OGPrimitive
    (D : StableQuotientComultiplicationPack) :
    D.comul = OGPrimitiveComulPack.comul ∧
      D.counit = OGPrimitiveComulPack.counit := by
  constructor
  · apply PreLieDifferenceStableQuotient_linearMap_ext_treeGen
    intro x
    rw [D.comul_on_treeGen, OGPrimitiveComulPack.comul_on_treeGen]
  · apply PreLieDifferenceStableQuotient_linearMap_ext_treeGen
    intro x
    rw [D.counit_on_treeGen, OGPrimitiveComulPack.counit_on_treeGen]

/--
Any quotient comultiplication satisfying the primitive generator formula already
obeys the full primitive formula on arbitrary raw linear combinations.
-/
theorem stableQuotientComultiplication_comul_mk_eq_primitive_formula_of_generator_formula
    (Δ : StableQuotientComultiplication)
    (hcomul : ∀ x : PTree,
      Δ.comul (mkPreLieDifferenceStableQuotient (treeGen x)) =
        TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen x))
    (a : linearProofTreeCarrier) :
    Δ.comul (mkPreLieDifferenceStableQuotient a) =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  rw [stableQuotientComultiplication_comul_eq_OGPrimitive_of_generator_formula
    Δ hcomul]
  exact OGPrimitiveComul_comul_mk a

/--
Likewise, any quotient comultiplication with zero generator counit has
identically zero counit on arbitrary raw linear combinations.
-/
theorem stableQuotientComultiplication_counit_mk_eq_zero_of_generator_formula
    (Δ : StableQuotientComultiplication)
    (hcounit : ∀ x : PTree,
      Δ.counit (mkPreLieDifferenceStableQuotient (treeGen x)) = 0)
    (a : linearProofTreeCarrier) :
    Δ.counit (mkPreLieDifferenceStableQuotient a) = 0 := by
  rw [stableQuotientComultiplication_counit_eq_OGPrimitive_of_generator_formula
    Δ hcounit]
  exact OGPrimitiveComul_counit_mk a

/--
Packaged quotient comultiplication data already satisfies the full primitive
formula on arbitrary raw linear combinations.
-/
theorem StableQuotientComultiplicationData_comul_mk_eq_primitive_formula
    (D : StableQuotientComultiplicationData)
    (a : linearProofTreeCarrier) :
    D.comul (mkPreLieDifferenceStableQuotient a) =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  exact
    stableQuotientComultiplication_comul_mk_eq_primitive_formula_of_generator_formula
      D.Δ D.comul_on_generators a

/--
Packaged quotient comultiplication data has identically zero counit on
arbitrary raw linear combinations.
-/
theorem StableQuotientComultiplicationData_counit_mk_eq_zero
    (D : StableQuotientComultiplicationData)
    (a : linearProofTreeCarrier) :
    D.counit (mkPreLieDifferenceStableQuotient a) = 0 := by
  exact
    stableQuotientComultiplication_counit_mk_eq_zero_of_generator_formula
      D.Δ D.counit_on_generators a

/--
Likewise for quotient comultiplication packs: the primitive generator law
forces the full primitive formula on arbitrary raw linear combinations.
-/
theorem StableQuotientComultiplicationPack_comul_mk_eq_primitive_formula
    (D : StableQuotientComultiplicationPack)
    (a : linearProofTreeCarrier) :
    D.comul (mkPreLieDifferenceStableQuotient a) =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  exact
    stableQuotientComultiplication_comul_mk_eq_primitive_formula_of_generator_formula
      D.Δ D.comul_on_treeGen a

/--
Likewise, every quotient comultiplication pack with the generator axioms has
identically zero counit.
-/
theorem StableQuotientComultiplicationPack_counit_mk_eq_zero
    (D : StableQuotientComultiplicationPack)
    (a : linearProofTreeCarrier) :
    D.counit (mkPreLieDifferenceStableQuotient a) = 0 := by
  exact
    stableQuotientComultiplication_counit_mk_eq_zero_of_generator_formula
      D.Δ D.counit_on_treeGen a

/-!
### Conditional UEA lifts of the primitive OG formulas

When the tensor square of the stable UEA carries the expected algebra
structure, the primitive quotient formulas upgrade to honest algebra
morphisms out of the stable UEA by the universal property of
`UniversalEnvelopingAlgebra`.

This is the algebra-side half of the expected bialgebra package: the target
coalgebra axioms are still tracked separately, but the multiplicative lifts are
now canonical rather than only informally described.
-/

section OGPrimitiveUEALifts

variable [Ring stableUEATensor] [Algebra ℤ stableUEATensor]

noncomputable local instance (priority := 1000) :
    LieRing PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientLieRing

local instance (priority := 1000) : LieRing stableUEATensor :=
  LieRing.ofAssociativeRing

local instance (priority := 1000) : LieAlgebra ℤ stableUEATensor :=
  LieAlgebra.ofAssociativeAlgebra

/--
The tensor-square multiplication has the expected elementary-tensor law.
This is the algebraic hypothesis that turns the primitive formula
`x ↦ x ⊗ 1 + 1 ⊗ x` into a Lie morphism.
-/
def StableUEATensorHasTensorMul : Prop :=
  ∀ a b c d : preLieDifferenceStableQuotientUEA,
    TensorProduct.tmul ℤ a b * TensorProduct.tmul ℤ c d =
      TensorProduct.tmul ℤ (a * c) (b * d)

/--
The primitive OG comultiplication is compatible with the Lie bracket.
This is the exact algebraic condition needed before the universal property of
the UEA can turn the primitive formula into a multiplicative comultiplication.
-/
def StableUEATensorPrimitiveBracketCompatible : Prop :=
  ∀ q r : PreLieDifferenceStableQuotient,
    OGPrimitiveComul.comul ⁅q, r⁆ =
      ⁅OGPrimitiveComul.comul q, OGPrimitiveComul.comul r⁆

/--
Two algebra homomorphisms out of the stable UEA are equal as soon as they agree
on the canonical Lie insertion `ι`.
-/
theorem stableUEA_algHom_ext_ι
    (Φ Ψ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor)
    (hι : ∀ q : PreLieDifferenceStableQuotient,
      Φ (preLieDifferenceStableQuotientUEA_ι q) =
        Ψ (preLieDifferenceStableQuotientUEA_ι q)) :
    Φ = Ψ := by
  apply UniversalEnvelopingAlgebra.hom_ext (R := ℤ)
  ext q
  exact hι q

/--
Likewise for algebra homomorphisms from the stable UEA to `ℤ`.
-/
theorem stableUEA_counitAlgHom_ext_ι
    (ε₁ ε₂ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] ℤ)
    (hι : ∀ q : PreLieDifferenceStableQuotient,
      ε₁ (preLieDifferenceStableQuotientUEA_ι q) =
        ε₂ (preLieDifferenceStableQuotientUEA_ι q)) :
    ε₁ = ε₂ := by
  apply UniversalEnvelopingAlgebra.hom_ext (R := ℤ)
  ext q
  exact hι q

/--
Any two multiplicative comultiplication candidates whose restrictions to the
Lie generators agree with `OGPrimitiveComul.comul` must coincide.
-/
theorem stableUEA_comulAlgHom_unique_of_ι_formula
    (Φ Ψ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor)
    (hΦ : ∀ q : PreLieDifferenceStableQuotient,
      Φ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.comul q)
    (hΨ : ∀ q : PreLieDifferenceStableQuotient,
      Ψ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.comul q) :
    Φ = Ψ := by
  apply stableUEA_algHom_ext_ι
  intro q
  rw [hΦ q, hΨ q]

/--
Likewise, any two multiplicative counit candidates whose restrictions to the
Lie generators agree with `OGPrimitiveComul.counit` must coincide.
-/
theorem stableUEA_counitAlgHom_unique_of_ι_formula
    (ε₁ ε₂ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] ℤ)
    (hε₁ : ∀ q : PreLieDifferenceStableQuotient,
      ε₁ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.counit q)
    (hε₂ : ∀ q : PreLieDifferenceStableQuotient,
      ε₂ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.counit q) :
    ε₁ = ε₂ := by
  apply stableUEA_counitAlgHom_ext_ι
  intro q
  rw [hε₁ q, hε₂ q]

/--
Any algebra hom out of the stable UEA with the OG primitive formula on `ι`
automatically satisfies the corresponding tree-generator formula.
-/
theorem stableUEA_comulAlgHom_treeGen_formula_of_ι_formula
    (Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor)
    (hΦ : ∀ q : PreLieDifferenceStableQuotient,
      Φ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.comul q) :
    ∀ x : PTree,
      Φ (stableUEA_treeGen x) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  intro x
  simpa [stableUEA_treeGen_eq_ι] using
    congrArg id (hΦ (mkPreLieDifferenceStableQuotient (treeGen x)))

/--
Likewise, the OG counit formula on `ι` implies the expected tree-generator
vanishing formula.
-/
theorem stableUEA_counitAlgHom_treeGen_formula_of_ι_formula
    (ε : preLieDifferenceStableQuotientUEA →ₐ[ℤ] ℤ)
    (hε : ∀ q : PreLieDifferenceStableQuotient,
      ε (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.counit q) :
    ∀ x : PTree, ε (stableUEA_treeGen x) = 0 := by
  intro x
  simpa [stableUEA_treeGen_eq_ι] using
    congrArg id (hε (mkPreLieDifferenceStableQuotient (treeGen x)))

/--
The canonical UEA counit is the unique algebra homomorphism out of the stable
UEA that kills every inserted stable quotient class.
-/
theorem stableUEA_counitAlgHom_unique_of_ι_zero
    (ε : preLieDifferenceStableQuotientUEA →ₐ[ℤ] ℤ)
    (hε : ∀ q : PreLieDifferenceStableQuotient,
      ε (preLieDifferenceStableQuotientUEA_ι q) = 0) :
    ε = stableUEA_counitAlgHom := by
  apply stableUEA_counitAlgHom_ext_ι
  intro q
  rw [hε q, stableUEA_counitAlgHom_ι q]

/--
The genuine algebraic condition needed for the OG comultiplication to extend
multiplicatively to the UEA: the primitive quotient map must be a Lie
morphism into the tensor-square algebra.
-/
def OGPrimitiveComulLieLiftable : Prop :=
  ∃ Φ : PreLieDifferenceStableQuotient →ₗ⁅ℤ⁆ stableUEATensor,
    ∀ q : PreLieDifferenceStableQuotient, Φ q = OGPrimitiveComul.comul q

/--
Any genuine Lie lift of the descended primitive comultiplication forces the
primitive bracket-compatibility equation.
-/
theorem primitiveBracketCompatible_of_OGPrimitiveComulLieLiftable
    (h : OGPrimitiveComulLieLiftable) :
    StableUEATensorPrimitiveBracketCompatible := by
  rcases h with ⟨Φ, hΦ⟩
  intro q r
  rw [← hΦ (⁅q, r⁆), ← hΦ q, ← hΦ r]
  exact LieHom.map_lie Φ q r

/--
If the primitive OG comultiplication is a Lie morphism, then the universal
property of the stable UEA gives the multiplicative OG comultiplication
algebra homomorphism.
-/
noncomputable def stableUEA_OGPrimitiveComulAlgHom
    (h : OGPrimitiveComulLieLiftable) :
    preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor :=
  preLieDifferenceStableQuotientUEA_lift h.choose

/--
The UEA algebra homomorphism obtained from a Lie-liftable primitive
comultiplication has exactly the OG primitive formula on Lie generators.
-/
theorem stableUEA_OGPrimitiveComulAlgHom_ι_formula
    (h : OGPrimitiveComulLieLiftable) :
    ∀ q : PreLieDifferenceStableQuotient,
      stableUEA_OGPrimitiveComulAlgHom h
          (preLieDifferenceStableQuotientUEA_ι q) =
        OGPrimitiveComul.comul q := by
  intro q
  have hlift :=
    congrFun
      (preLieDifferenceStableQuotientUEA_ι_comp_lift h.choose) q
  exact (by
    simpa [stableUEA_OGPrimitiveComulAlgHom] using
      hlift.trans (h.choose_spec q))

/--
Consequently, the multiplicative OG comultiplication has the primitive formula
on proof-tree generators.
-/
theorem stableUEA_OGPrimitiveComulAlgHom_treeGen_formula
    (h : OGPrimitiveComulLieLiftable) :
    ∀ x : PTree,
      stableUEA_OGPrimitiveComulAlgHom h (stableUEA_treeGen x) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  stableUEA_comulAlgHom_treeGen_formula_of_ι_formula
    (stableUEA_OGPrimitiveComulAlgHom h)
    (stableUEA_OGPrimitiveComulAlgHom_ι_formula h)

/--
The multiplicative OG comultiplication, if it exists via the Lie condition, is
unique.
-/
theorem stableUEA_OGPrimitiveComulAlgHom_unique
    (h : OGPrimitiveComulLieLiftable)
    (Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor)
    (hΦ : ∀ q : PreLieDifferenceStableQuotient,
      Φ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.comul q) :
    Φ = stableUEA_OGPrimitiveComulAlgHom h := by
  apply stableUEA_comulAlgHom_unique_of_ι_formula
  · exact hΦ
  · exact stableUEA_OGPrimitiveComulAlgHom_ι_formula h

/--
The universal property of the stable UEA gives an exact equivalence:
to give a multiplicative OG comultiplication algebra homomorphism with the
primitive formula on Lie generators is the same thing as giving a Lie lift of
the descended primitive comultiplication.
-/
theorem OGPrimitiveComulLieLiftable_iff_exists_UEA_algHom :
    OGPrimitiveComulLieLiftable ↔
      ∃ Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor,
        ∀ q : PreLieDifferenceStableQuotient,
          Φ (preLieDifferenceStableQuotientUEA_ι q) =
            OGPrimitiveComul.comul q := by
  constructor
  · intro h
    exact ⟨stableUEA_OGPrimitiveComulAlgHom h,
      stableUEA_OGPrimitiveComulAlgHom_ι_formula h⟩
  · rintro ⟨Φ, hΦ⟩
    refine
      ⟨(AlgHom.toLieHom Φ).comp
          preLieDifferenceStableQuotientUEA_ι, ?_⟩
    intro q
    exact hΦ q

/--
In fact the OG primitive Lie data determines a unique multiplicative
comultiplication on the stable UEA.
-/
theorem OGPrimitiveComulLieLiftable_iff_existsUnique_UEA_algHom :
    OGPrimitiveComulLieLiftable ↔
      ∃! Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor,
        ∀ q : PreLieDifferenceStableQuotient,
          Φ (preLieDifferenceStableQuotientUEA_ι q) =
            OGPrimitiveComul.comul q := by
  constructor
  · intro h
    refine
      ⟨stableUEA_OGPrimitiveComulAlgHom h,
        stableUEA_OGPrimitiveComulAlgHom_ι_formula h, ?_⟩
    intro Ψ hΨ
    exact stableUEA_OGPrimitiveComulAlgHom_unique h Ψ hΨ
  · intro h
    rcases h with ⟨Φ, hΦ, _uniq⟩
    exact
      (OGPrimitiveComulLieLiftable_iff_exists_UEA_algHom).2
        ⟨Φ, hΦ⟩

/--
The multiplicative OG comultiplication is equivalently a unique UEA algebra
map with primitive generator formula; whenever it exists, the primitive
formula also satisfies the grafting commutator bracket equation.
-/
theorem OGPrimitiveComulLieLiftable_iff_existsUnique_UEA_algHom_and_bracketCompatible :
    OGPrimitiveComulLieLiftable ↔
      (∃! Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor,
        ∀ q : PreLieDifferenceStableQuotient,
          Φ (preLieDifferenceStableQuotientUEA_ι q) =
            OGPrimitiveComul.comul q) ∧
        StableUEATensorPrimitiveBracketCompatible := by
  constructor
  · intro h
    exact
      ⟨(OGPrimitiveComulLieLiftable_iff_existsUnique_UEA_algHom).1 h,
        primitiveBracketCompatible_of_OGPrimitiveComulLieLiftable h⟩
  · intro h
    exact (OGPrimitiveComulLieLiftable_iff_existsUnique_UEA_algHom).2 h.1

end OGPrimitiveUEALifts

/-!
### Canonical tensor algebra structure for the OG primitive coproduct

The preceding section deliberately stated the UEA lifting theorem for an
abstract algebra structure on `stableUEATensor`.  Here we install the actual
mathlib tensor-product algebra structure.  This is the algebraic point at which
the primitive formula

`q ↦ ι q ⊗ 1 + 1 ⊗ ι q`

becomes a genuine Lie morphism, hence gives a multiplicative UEA
comultiplication by the universal property of the enveloping algebra.
-/

section OGPrimitiveCanonicalTensorAlgebra

instance stableUEATensor_smulCommClass :
    SMulCommClass ℤ preLieDifferenceStableQuotientUEA
      preLieDifferenceStableQuotientUEA :=
  Algebra.to_smulCommClass
    (R := ℤ) (A := preLieDifferenceStableQuotientUEA)

instance stableUEATensor_isScalarTower :
    IsScalarTower ℤ preLieDifferenceStableQuotientUEA
      preLieDifferenceStableQuotientUEA :=
  IsScalarTower.right
    (R := ℤ) (A := preLieDifferenceStableQuotientUEA)

noncomputable instance stableUEATensor_ring : Ring stableUEATensor :=
  Algebra.TensorProduct.instRing
    (R := ℤ)
    (A := preLieDifferenceStableQuotientUEA)
    (B := preLieDifferenceStableQuotientUEA)

noncomputable instance stableUEATensor_algebra :
    Algebra ℤ stableUEATensor :=
  Algebra.TensorProduct.instAlgebra
    (R := ℤ)
    (A := preLieDifferenceStableQuotientUEA)
    (B := preLieDifferenceStableQuotientUEA)

noncomputable instance stableUEATensor_rightDistribClass :
    RightDistribClass stableUEATensor where
  right_distrib := by
    intro a b c
    exact Distrib.right_distrib a b c

noncomputable instance stableUEATensor_leftDistribClass :
    LeftDistribClass stableUEATensor where
  left_distrib := by
    intro a b c
    exact Distrib.left_distrib a b c

noncomputable local instance (priority := 1000) :
    LieRing PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientLieRing

noncomputable local instance (priority := 1000) : LieRing stableUEATensor :=
  LieRing.ofAssociativeRing

noncomputable local instance (priority := 1000) :
    LieAlgebra ℤ stableUEATensor :=
  LieAlgebra.ofAssociativeAlgebra

/--
The canonical tensor-product algebra structure has the expected multiplication
law on elementary tensors.  This discharges the earlier ad hoc
`StableUEATensorHasTensorMul` hypothesis for the actual OG tensor square.
-/
theorem stableUEATensor_canonical_tmul_mul_tmul
    (a b c d : preLieDifferenceStableQuotientUEA) :
    TensorProduct.tmul ℤ a b * TensorProduct.tmul ℤ c d =
      TensorProduct.tmul ℤ (a * c) (b * d) := by
  exact @Algebra.TensorProduct.tmul_mul_tmul
    ℤ preLieDifferenceStableQuotientUEA preLieDifferenceStableQuotientUEA
    inferInstance inferInstance inferInstance
    stableUEATensor_smulCommClass stableUEATensor_isScalarTower
    inferInstance inferInstance
    stableUEATensor_smulCommClass stableUEATensor_isScalarTower
    a c b d

/-- The actual tensor-product algebra satisfies the elementary tensor law. -/
theorem stableUEATensor_canonical_hasTensorMul :
    StableUEATensorHasTensorMul := by
  intro a b c d
  exact stableUEATensor_canonical_tmul_mul_tmul a b c d

/--
The descended OG primitive comultiplication has the primitive tensor formula
on every stable quotient class.
-/
theorem OGPrimitiveComul_comul_eq_primitive_formula
    (q : PreLieDifferenceStableQuotient) :
    OGPrimitiveComul.comul q =
      TensorProduct.tmul ℤ (preLieDifferenceStableQuotientUEA_ι q) 1 +
        TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientUEA_ι q) := by
  induction q using Submodule.Quotient.induction_on with
  | H a =>
      simpa [preLieDifferenceStableQuotientToUEA] using
        OGPrimitiveComul_comul_mk a

/--
Primitive elements are closed under the commutator bracket in the canonical
tensor square.  Algebraically, this is the calculation that turns the formula
`x ↦ x ⊗ 1 + 1 ⊗ x` into a Lie morphism.
-/
theorem stableUEATensor_canonical_primitive_bracket
    (x y : preLieDifferenceStableQuotientUEA) :
    Bracket.bracket
      (TensorProduct.tmul ℤ x (1 : preLieDifferenceStableQuotientUEA) +
        TensorProduct.tmul ℤ (1 : preLieDifferenceStableQuotientUEA) x)
      (TensorProduct.tmul ℤ y (1 : preLieDifferenceStableQuotientUEA) +
        TensorProduct.tmul ℤ (1 : preLieDifferenceStableQuotientUEA) y) =
      TensorProduct.tmul ℤ (Bracket.bracket x y)
        (1 : preLieDifferenceStableQuotientUEA) +
        TensorProduct.tmul ℤ (1 : preLieDifferenceStableQuotientUEA)
          (Bracket.bracket x y) := by
  rw [LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket]
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add]
  rw [stableUEATensor_canonical_tmul_mul_tmul x 1 y 1,
    stableUEATensor_canonical_tmul_mul_tmul x 1 1 y,
    stableUEATensor_canonical_tmul_mul_tmul 1 x y 1,
    stableUEATensor_canonical_tmul_mul_tmul 1 x 1 y,
    stableUEATensor_canonical_tmul_mul_tmul y 1 x 1,
    stableUEATensor_canonical_tmul_mul_tmul y 1 1 x,
    stableUEATensor_canonical_tmul_mul_tmul 1 y x 1,
    stableUEATensor_canonical_tmul_mul_tmul 1 y 1 x]
  simp only [one_mul, mul_one, sub_eq_add_neg]
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  simp only [TensorProduct.neg_tmul, TensorProduct.tmul_neg]
  abel

/--
The actual OG primitive comultiplication is compatible with the Lie bracket in
the canonical tensor-product algebra.
-/
theorem OGPrimitiveComul_canonical_bracketCompatible :
    StableUEATensorPrimitiveBracketCompatible := by
  intro q r
  rw [OGPrimitiveComul_comul_eq_primitive_formula (⁅q, r⁆),
    OGPrimitiveComul_comul_eq_primitive_formula q,
    OGPrimitiveComul_comul_eq_primitive_formula r]
  rw [LieHom.map_lie preLieDifferenceStableQuotientUEA_ι q r]
  exact (stableUEATensor_canonical_primitive_bracket
    (preLieDifferenceStableQuotientUEA_ι q)
    (preLieDifferenceStableQuotientUEA_ι r)).symm

/--
The primitive OG comultiplication, with the canonical tensor-product algebra
on the target, is a Lie morphism.
-/
noncomputable def OGPrimitiveComulCanonicalLieHom :
    PreLieDifferenceStableQuotient →ₗ⁅ℤ⁆ stableUEATensor :=
  { OGPrimitiveComul.comul with
    map_lie' := by
      intro q r
      exact OGPrimitiveComul_canonical_bracketCompatible q r }

/-- The canonical tensor algebra makes the OG primitive map Lie-liftable. -/
theorem OGPrimitiveComul_canonical_lieLiftable :
    OGPrimitiveComulLieLiftable := by
  exact ⟨OGPrimitiveComulCanonicalLieHom, by intro q; rfl⟩

/--
The multiplicative OG comultiplication on the stable UEA obtained from the
canonical primitive Lie morphism.
-/
noncomputable def stableUEA_OGPrimitiveCanonicalComulAlgHom :
    preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor :=
  stableUEA_OGPrimitiveComulAlgHom
    OGPrimitiveComul_canonical_lieLiftable

/--
The canonical UEA comultiplication restricts to the primitive OG formula on
the canonical Lie insertion.
-/
theorem stableUEA_OGPrimitiveCanonicalComulAlgHom_ι_formula :
    ∀ q : PreLieDifferenceStableQuotient,
      stableUEA_OGPrimitiveCanonicalComulAlgHom
          (preLieDifferenceStableQuotientUEA_ι q) =
        OGPrimitiveComul.comul q :=
  stableUEA_OGPrimitiveComulAlgHom_ι_formula
    OGPrimitiveComul_canonical_lieLiftable

/-- The canonical UEA comultiplication has the primitive formula on tree generators. -/
theorem stableUEA_OGPrimitiveCanonicalComulAlgHom_treeGen_formula :
    ∀ x : PTree,
      stableUEA_OGPrimitiveCanonicalComulAlgHom (stableUEA_treeGen x) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) :=
  stableUEA_OGPrimitiveComulAlgHom_treeGen_formula
    OGPrimitiveComul_canonical_lieLiftable

/--
The canonical multiplicative OG comultiplication is the unique UEA algebra map
with the primitive formula on Lie generators.
-/
theorem stableUEA_OGPrimitiveCanonicalComulAlgHom_unique
    (Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor)
    (hΦ : ∀ q : PreLieDifferenceStableQuotient,
      Φ (preLieDifferenceStableQuotientUEA_ι q) = OGPrimitiveComul.comul q) :
    Φ = stableUEA_OGPrimitiveCanonicalComulAlgHom := by
  exact stableUEA_OGPrimitiveComulAlgHom_unique
    OGPrimitiveComul_canonical_lieLiftable Φ hΦ

/--
Existence and uniqueness of the multiplicative OG comultiplication is now a
theorem for the canonical tensor-product algebra, not an extra assumption.
-/
theorem OGPrimitiveComul_canonical_existsUnique_UEA_algHom :
    ∃! Φ : preLieDifferenceStableQuotientUEA →ₐ[ℤ] stableUEATensor,
      ∀ q : PreLieDifferenceStableQuotient,
        Φ (preLieDifferenceStableQuotientUEA_ι q) =
          OGPrimitiveComul.comul q :=
  (OGPrimitiveComulLieLiftable_iff_existsUnique_UEA_algHom).1
    OGPrimitiveComul_canonical_lieLiftable

end OGPrimitiveCanonicalTensorAlgebra

section OGPrimitiveUEABialgebraRigidity

variable [Ring stableUEATensor] [Algebra ℤ stableUEATensor]

/--
Bundled stable-UEA bialgebra data has the OG primitive comultiplication formula
on the canonical Lie insertion `ι`.
-/
def StableUEABialgebraData.OGPrimitiveComulOnIota
    (D : StableUEABialgebraData) : Prop :=
  ∀ q : PreLieDifferenceStableQuotient,
    D.comulAlgHom (preLieDifferenceStableQuotientUEA_ι q) =
      OGPrimitiveComul.comul q

/--
Bundled stable-UEA bialgebra data has the OG primitive counit formula on the
canonical Lie insertion `ι`.
-/
def StableUEABialgebraData.OGPrimitiveCounitOnIota
    (D : StableUEABialgebraData) : Prop :=
  ∀ q : PreLieDifferenceStableQuotient,
    D.counitAlgHom (preLieDifferenceStableQuotientUEA_ι q) =
      OGPrimitiveComul.counit q

/--
Combined OG primitive `ι`-formula for bundled stable-UEA bialgebra data.
-/
def StableUEABialgebraData.OGPrimitiveOnIota
    (D : StableUEABialgebraData) : Prop :=
  StableUEABialgebraData.OGPrimitiveComulOnIota D ∧
    StableUEABialgebraData.OGPrimitiveCounitOnIota D

/--
Any two packaged stable-UEA bialgebra candidates with the same OG primitive
formula on `ι` have the same multiplicative comultiplication map.
-/
theorem StableUEABialgebraData_comulAlgHom_eq_of_ι_formula
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveComulOnIota E) :
    D.comulAlgHom = E.comulAlgHom := by
  exact stableUEA_comulAlgHom_unique_of_ι_formula D.comulAlgHom E.comulAlgHom hD hE

/--
Likewise for the multiplicative counit maps in bundled stable-UEA bialgebra
data.
-/
theorem StableUEABialgebraData_counitAlgHom_eq_of_ι_formula
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveCounitOnIota E) :
    D.counitAlgHom = E.counitAlgHom := by
  exact
    stableUEA_counitAlgHom_unique_of_ι_formula
      D.counitAlgHom E.counitAlgHom hD hE

/--
Any two bundled stable-UEA bialgebra candidates with the OG primitive
behavior on `ι` also agree on their underlying UEA-level comultiplication maps.
-/
theorem StableUEABialgebraData_comul_eq_of_ι_formula
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveComulOnIota E) :
    D.comul = E.comul := by
  have hAlg :
      D.comulAlgHom = E.comulAlgHom :=
    StableUEABialgebraData_comulAlgHom_eq_of_ι_formula D E hD hE
  ext x
  rw [← D.comulAlgHom_apply_simp, ← E.comulAlgHom_apply_simp, hAlg]

/--
Likewise for the underlying UEA-level counit maps.
-/
theorem StableUEABialgebraData_counit_eq_of_ι_formula
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveCounitOnIota E) :
    D.counit = E.counit := by
  have hAlg :
      D.counitAlgHom = E.counitAlgHom :=
    StableUEABialgebraData_counitAlgHom_eq_of_ι_formula D E hD hE
  ext x
  rw [← D.counitAlgHom_apply_simp, ← E.counitAlgHom_apply_simp, hAlg]

/--
Hence any two bundled stable-UEA bialgebra candidates with the OG primitive
behavior on `ι` agree on both multiplicative maps and on the induced UEA-level
coalgebra structure maps.
-/
theorem StableUEABialgebraData_eq_on_structure_maps_of_ι_formula
    (D E : StableUEABialgebraData)
    (hDcomul : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hEcomul : StableUEABialgebraData.OGPrimitiveComulOnIota E)
    (hDcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hEcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota E) :
    D.comulAlgHom = E.comulAlgHom ∧
      D.counitAlgHom = E.counitAlgHom ∧
      D.comul = E.comul ∧
      D.counit = E.counit := by
  have hAlgComul :
      D.comulAlgHom = E.comulAlgHom :=
    StableUEABialgebraData_comulAlgHom_eq_of_ι_formula D E hDcomul hEcomul
  have hAlgCounit :
      D.counitAlgHom = E.counitAlgHom :=
    StableUEABialgebraData_counitAlgHom_eq_of_ι_formula D E hDcounit hEcounit
  have hComul :
      D.comul = E.comul := by
    exact StableUEABialgebraData_comul_eq_of_ι_formula D E hDcomul hEcomul
  have hCounit :
      D.counit = E.counit := by
    exact StableUEABialgebraData_counit_eq_of_ι_formula D E hDcounit hEcounit
  exact ⟨hAlgComul, hAlgCounit, hComul, hCounit⟩

/--
Under the OG primitive `ι`-formula, two bundled stable-UEA bialgebra
candidates agree pointwise on the Lie-generator image.
-/
theorem StableUEABialgebraData_eq_on_ι_of_ι_formula
    (D E : StableUEABialgebraData)
    (hDcomul : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hEcomul : StableUEABialgebraData.OGPrimitiveComulOnIota E)
    (hDcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hEcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota E) :
    (∀ q : PreLieDifferenceStableQuotient,
      D.comul (preLieDifferenceStableQuotientUEA_ι q) =
        E.comul (preLieDifferenceStableQuotientUEA_ι q)) ∧
    (∀ q : PreLieDifferenceStableQuotient,
      D.counit (preLieDifferenceStableQuotientUEA_ι q) =
        E.counit (preLieDifferenceStableQuotientUEA_ι q)) := by
  have hMaps :=
    StableUEABialgebraData_eq_on_structure_maps_of_ι_formula
      D E hDcomul hEcomul hDcounit hEcounit
  rcases hMaps with ⟨_, _, hComul, hCounit⟩
  constructor
  · intro q
    rw [hComul]
  · intro q
    rw [hCounit]

/--
In particular, the same rigidity holds on the UEA images of tree generators.
-/
theorem StableUEABialgebraData_eq_on_treeGen_of_ι_formula
    (D E : StableUEABialgebraData)
    (hDcomul : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hEcomul : StableUEABialgebraData.OGPrimitiveComulOnIota E)
    (hDcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hEcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota E) :
    (∀ x : PTree, D.comul (stableUEA_treeGen x) = E.comul (stableUEA_treeGen x)) ∧
    (∀ x : PTree, D.counit (stableUEA_treeGen x) = E.counit (stableUEA_treeGen x)) := by
  have hι :=
    StableUEABialgebraData_eq_on_ι_of_ι_formula
      D E hDcomul hEcomul hDcounit hEcounit
  rcases hι with ⟨hComul, hCounit⟩
  constructor
  · intro x
    simpa [stableUEA_treeGen_eq_ι] using
      hComul (mkPreLieDifferenceStableQuotient (treeGen x))
  · intro x
    simpa [stableUEA_treeGen_eq_ι] using
      hCounit (mkPreLieDifferenceStableQuotient (treeGen x))

/--
A bundled stable-UEA bialgebra candidate with the OG primitive formula on `ι`
already has the expected primitive tree-generator comultiplication formula.
-/
theorem StableUEABialgebraData_comul_on_treeGen_of_ι_formula
    (D : StableUEABialgebraData)
    (hDcomul : StableUEABialgebraData.OGPrimitiveComulOnIota D) :
    ∀ x : PTree,
      D.comul (stableUEA_treeGen x) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x) := by
  intro x
  rw [← D.comulAlgHom_apply_simp]
  exact stableUEA_comulAlgHom_treeGen_formula_of_ι_formula D.comulAlgHom hDcomul x

/--
Likewise, the OG counit formula on `ι` implies the expected vanishing on tree
generators for bundled stable-UEA bialgebra data.
-/
theorem StableUEABialgebraData_counit_on_treeGen_of_ι_formula
    (D : StableUEABialgebraData)
    (hDcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota D) :
    ∀ x : PTree, D.counit (stableUEA_treeGen x) = 0 := by
  intro x
  rw [← D.counitAlgHom_apply_simp]
  exact stableUEA_counitAlgHom_treeGen_formula_of_ι_formula D.counitAlgHom hDcounit x

/--
The combined OG primitive `ι`-formula immediately yields the standard
tree-generator formulas for bundled stable-UEA bialgebra data.
-/
theorem StableUEABialgebraData_on_treeGen_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D) :
    (∀ x : PTree,
      D.comul (stableUEA_treeGen x) =
        TensorProduct.tmul ℤ (stableUEA_treeGen x) 1 +
          TensorProduct.tmul ℤ 1 (stableUEA_treeGen x)) ∧
    (∀ x : PTree, D.counit (stableUEA_treeGen x) = 0) := by
  exact
    ⟨StableUEABialgebraData_comul_on_treeGen_of_ι_formula D hD.1,
      StableUEABialgebraData_counit_on_treeGen_of_ι_formula D hD.2⟩

/--
The OG primitive `ι`-formula for a bundled stable-UEA bialgebra candidate
forces the full primitive comultiplication formula on arbitrary raw linear
combinations.
-/
theorem StableUEABialgebraData_comul_mk_eq_primitive_formula_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (a : linearProofTreeCarrier) :
    D.comul (preLieDifferenceStableQuotientToUEA a) =
      TensorProduct.tmul ℤ (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientToUEA a) := by
  rw [← D.comulAlgHom_apply_simp]
  simpa [preLieDifferenceStableQuotientToUEA] using
    (hD (mkPreLieDifferenceStableQuotient a)).trans (OGPrimitiveComul_comul_mk a)

/--
Likewise, the OG primitive `ι`-formula forces identically zero counit on
arbitrary raw linear combinations.
-/
theorem StableUEABialgebraData_counit_mk_eq_zero_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (a : linearProofTreeCarrier) :
    D.counit (preLieDifferenceStableQuotientToUEA a) = 0 := by
  rw [← D.counitAlgHom_apply_simp]
  simpa [preLieDifferenceStableQuotientToUEA] using
    (hD (mkPreLieDifferenceStableQuotient a)).trans (OGPrimitiveComul_counit_mk a)

/--
Forest-level form of the bundled UEA-side primitive comultiplication formula.
-/
theorem StableUEABialgebraData_comul_forestGen_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      TensorProduct.tmul ℤ (preLieDifferenceStableQuotientToUEA (forestGen f)) 1 +
        TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
  simpa using
    StableUEABialgebraData_comul_mk_eq_primitive_formula_of_ι_formula
      D hD (forestGen f)

/--
Forest-level form of the bundled UEA-side primitive counit formula.
-/
theorem StableUEABialgebraData_counit_forestGen_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (f : Forest) :
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) = 0 := by
  exact
    StableUEABialgebraData_counit_mk_eq_zero_of_ι_formula
      D hD (forestGen f)

/--
Combined forest-level OG primitive formula for bundled stable-UEA bialgebra
data.
-/
theorem StableUEABialgebraData_on_forestGen_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      TensorProduct.tmul ℤ (preLieDifferenceStableQuotientToUEA (forestGen f)) 1 +
        TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientToUEA (forestGen f)) ∧
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) = 0 := by
  exact
    ⟨StableUEABialgebraData_comul_forestGen_of_ι_formula D hD.1 f,
      StableUEABialgebraData_counit_forestGen_of_ι_formula D hD.2 f⟩

/--
If a bundled stable-UEA bialgebra candidate is OG primitive on `ι`, then its
UEA-level comultiplication agrees with `OGPrimitiveComul.comul` on every raw
linear combination.
-/
theorem StableUEABialgebraData_comul_mk_eq_OGPrimitive_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (a : linearProofTreeCarrier) :
    D.comul (preLieDifferenceStableQuotientToUEA a) =
      OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient a) := by
  rw [← D.comulAlgHom_apply_simp]
  simpa [preLieDifferenceStableQuotientToUEA] using
    hD (mkPreLieDifferenceStableQuotient a)

/--
Likewise for the counit.
-/
theorem StableUEABialgebraData_counit_mk_eq_OGPrimitive_of_ι_formula
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (a : linearProofTreeCarrier) :
    D.counit (preLieDifferenceStableQuotientToUEA a) =
      OGPrimitiveComul.counit (mkPreLieDifferenceStableQuotient a) := by
  rw [← D.counitAlgHom_apply_simp]
  simpa [preLieDifferenceStableQuotientToUEA] using
    hD (mkPreLieDifferenceStableQuotient a)

/--
Combined raw-combination comparison with `OGPrimitiveComul`.
-/
theorem StableUEABialgebraData_on_mk_eq_OGPrimitive_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (a : linearProofTreeCarrier) :
    D.comul (preLieDifferenceStableQuotientToUEA a) =
      OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient a) ∧
    D.counit (preLieDifferenceStableQuotientToUEA a) =
      OGPrimitiveComul.counit (mkPreLieDifferenceStableQuotient a) := by
  exact
    ⟨StableUEABialgebraData_comul_mk_eq_OGPrimitive_of_ι_formula D hD.1 a,
      StableUEABialgebraData_counit_mk_eq_OGPrimitive_of_ι_formula D hD.2 a⟩

/--
Combined raw primitive formula for a bundled stable-UEA bialgebra candidate
that is OG primitive on `ι`.
-/
theorem StableUEABialgebraData_on_mk_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (a : linearProofTreeCarrier) :
    D.comul (preLieDifferenceStableQuotientToUEA a) =
      TensorProduct.tmul ℤ (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul ℤ 1 (preLieDifferenceStableQuotientToUEA a) ∧
    D.counit (preLieDifferenceStableQuotientToUEA a) = 0 := by
  exact
    ⟨StableUEABialgebraData_comul_mk_eq_primitive_formula_of_ι_formula D hD.1 a,
      StableUEABialgebraData_counit_mk_eq_zero_of_ι_formula D hD.2 a⟩

/--
Tree-generator specialization of the UEA-vs-OG primitive comparison.
-/
theorem StableUEABialgebraData_on_treeGen_eq_OGPrimitive_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (x : PTree) :
    D.comul (stableUEA_treeGen x) =
      OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient (treeGen x)) ∧
    D.counit (stableUEA_treeGen x) =
      OGPrimitiveComul.counit (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simpa [stableUEA_treeGen_eq_ι, preLieDifferenceStableQuotientToUEA] using
    StableUEABialgebraData_on_mk_eq_OGPrimitive_of_OGPrimitiveOnIota
      D hD (treeGen x)

/--
Forest specialization of the UEA-vs-OG primitive comparison.
-/
theorem StableUEABialgebraData_on_forestGen_eq_OGPrimitive_of_OGPrimitiveOnIota
    (D : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      OGPrimitiveComul.comul (mkPreLieDifferenceStableQuotient (forestGen f)) ∧
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      OGPrimitiveComul.counit (mkPreLieDifferenceStableQuotient (forestGen f)) := by
  exact
    StableUEABialgebraData_on_mk_eq_OGPrimitive_of_OGPrimitiveOnIota
      D hD (forestGen f)

/--
Any two bundled stable-UEA bialgebra candidates that are OG primitive on `ι`
agree on arbitrary raw linear combinations in the stable UEA.
-/
theorem StableUEABialgebraData_eq_on_mk_of_OGPrimitiveOnIota
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveOnIota E)
    (a : linearProofTreeCarrier) :
    D.comul (preLieDifferenceStableQuotientToUEA a) =
      E.comul (preLieDifferenceStableQuotientToUEA a) ∧
    D.counit (preLieDifferenceStableQuotientToUEA a) =
      E.counit (preLieDifferenceStableQuotientToUEA a) := by
  have hD' := StableUEABialgebraData_on_mk_eq_OGPrimitive_of_OGPrimitiveOnIota D hD a
  have hE' := StableUEABialgebraData_on_mk_eq_OGPrimitive_of_OGPrimitiveOnIota E hE a
  exact ⟨by rw [hD'.1, hE'.1], by rw [hD'.2, hE'.2]⟩

/--
Any two bundled stable-UEA bialgebra candidates with the OG primitive
`ι`-formula agree on every forest input in the stable UEA.
-/
theorem StableUEABialgebraData_eq_on_forestGen_of_ι_formula
    (D E : StableUEABialgebraData)
    (hDcomul : StableUEABialgebraData.OGPrimitiveComulOnIota D)
    (hEcomul : StableUEABialgebraData.OGPrimitiveComulOnIota E)
    (hDcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota D)
    (hEcounit : StableUEABialgebraData.OGPrimitiveCounitOnIota E)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) ∧
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
  have hMaps :=
    StableUEABialgebraData_eq_on_structure_maps_of_ι_formula
      D E hDcomul hEcomul hDcounit hEcounit
  rcases hMaps with ⟨_, _, hComul, hCounit⟩
  exact ⟨by rw [hComul], by rw [hCounit]⟩

/--
Combined-predicate form of forest-level agreement for bundled stable-UEA
bialgebra candidates.
-/
theorem StableUEABialgebraData_eq_on_forestGen_of_OGPrimitiveOnIota
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveOnIota E)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) ∧
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
  exact
    StableUEABialgebraData_eq_on_forestGen_of_ι_formula
      D E hD.1 hE.1 hD.2 hE.2 f

/--
If two bundled stable-UEA bialgebra candidates are both OG primitive on `ι`,
then they agree on the UEA images of all tree generators.
-/
theorem StableUEABialgebraData_eq_on_treeGen_of_OGPrimitiveOnIota
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveOnIota E) :
    (∀ x : PTree, D.comul (stableUEA_treeGen x) = E.comul (stableUEA_treeGen x)) ∧
    (∀ x : PTree, D.counit (stableUEA_treeGen x) = E.counit (stableUEA_treeGen x)) := by
  exact
    StableUEABialgebraData_eq_on_treeGen_of_ι_formula
      D E hD.1 hE.1 hD.2 hE.2

/--
The OG primitive `ι`-formula determines the forest-level comultiplication of a
bundled stable-UEA bialgebra candidate uniquely.
-/
theorem StableUEABialgebraData_comul_forestGen_eq_of_OGPrimitiveOnIota
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveOnIota E)
    (f : Forest) :
    D.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.comul (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
  exact
    (StableUEABialgebraData_eq_on_forestGen_of_OGPrimitiveOnIota
      D E hD hE f).1

/--
Likewise for the forest-level counit.
-/
theorem StableUEABialgebraData_counit_forestGen_eq_of_OGPrimitiveOnIota
    (D E : StableUEABialgebraData)
    (hD : StableUEABialgebraData.OGPrimitiveOnIota D)
    (hE : StableUEABialgebraData.OGPrimitiveOnIota E)
    (f : Forest) :
    D.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) =
      E.counit (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
  exact
    (StableUEABialgebraData_eq_on_forestGen_of_OGPrimitiveOnIota
      D E hD hE f).2

end OGPrimitiveUEABialgebraRigidity

/--
On a sum of two tree generators, the OG primitive comultiplication is the sum
of the two primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_two
    (x y : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  simpa [OGPrimitiveComul] using
    (stableUEA_comul_descend_treeGen_sum_two
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom x y)

/--
The OG primitive counit vanishes on a sum of two tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_two
    (x y : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) = 0 := by
  simpa [OGPrimitiveComul] using
    (stableUEA_counit_descend_treeGen_sum_two
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom x y)

/--
On a sum of three tree generators, the OG primitive comultiplication expands as
the sum of the three primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_three
    (x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [OGPrimitiveComul] using
    (stableUEA_comul_descend_treeGen_sum_three_expanded
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom x y z)

/--
The OG primitive counit vanishes on a sum of three tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_three
    (x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) = 0 := by
  simpa [OGPrimitiveComul] using
    (stableUEA_counit_descend_treeGen_sum_three
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom x y z)

/--
On a sum of four tree generators, the OG primitive comultiplication expands as
the sum of the four primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_four
    (w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [OGPrimitiveComul] using
    (stableUEA_comul_descend_treeGen_sum_four_expanded
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom w x y z)

/--
The OG primitive counit vanishes on a sum of four tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_four
    (w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  simpa [OGPrimitiveComul] using
    (stableUEA_counit_descend_treeGen_sum_four
      stableUEA_OGPrimitiveGeneratorComulData
      stableUEA_OGPrimitive_respectsStableQuotient_axiom w x y z)

/--
On a sum of five tree generators, the OG primitive comultiplication expands as
the sum of the five primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_five
    (v w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, add_assoc, OGPrimitiveComul_comul_treeGen_sum_four,
    OGPrimitiveComul_comul_treeGen] using
    (OGPrimitiveComul.comul.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The OG primitive counit vanishes on a sum of five tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_five
    (v w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, OGPrimitiveComul_counit_treeGen_sum_four,
    OGPrimitiveComul_counit_treeGen] using
    (OGPrimitiveComul.counit.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
On a sum of six tree generators, the OG primitive comultiplication expands as
the sum of the six primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_six
    (u v w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, add_assoc, OGPrimitiveComul_comul_treeGen_sum_five,
    OGPrimitiveComul_comul_treeGen] using
    (OGPrimitiveComul.comul.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The OG primitive counit vanishes on a sum of six tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_six
    (u v w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, OGPrimitiveComul_counit_treeGen_sum_five,
    OGPrimitiveComul_counit_treeGen] using
    (OGPrimitiveComul.counit.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
On a sum of seven tree generators, the OG primitive comultiplication expands as
the sum of the seven primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_seven
    (t u v w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, add_assoc, OGPrimitiveComul_comul_treeGen_sum_six,
    OGPrimitiveComul_comul_treeGen] using
    (OGPrimitiveComul.comul.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The OG primitive counit vanishes on a sum of seven tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_seven
    (t u v w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z)) = 0 := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, OGPrimitiveComul_counit_treeGen_sum_six,
    OGPrimitiveComul_counit_treeGen] using
    (OGPrimitiveComul.counit.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
On a sum of eight tree generators, the OG primitive comultiplication expands as
the sum of the eight primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, add_assoc, OGPrimitiveComul_comul_treeGen_sum_seven,
    OGPrimitiveComul_comul_treeGen] using
    (OGPrimitiveComul.comul.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The OG primitive counit vanishes on a sum of eight tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hmk :
      mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z) =
        mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) +
        mkPreLieDifferenceStableQuotient (treeGen z) := by
    simpa using
      (mkPreLieDifferenceStableQuotient.map_add
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, OGPrimitiveComul_counit_treeGen_sum_seven,
    OGPrimitiveComul_counit_treeGen] using
    (OGPrimitiveComul.counit.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
On a sum of nine tree generators, the OG primitive comultiplication expands as
the sum of the nine primitive generator formulas.
-/
theorem OGPrimitiveComul_comul_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
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
          treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, add_assoc, OGPrimitiveComul_comul_treeGen_sum_eight,
    OGPrimitiveComul_comul_treeGen] using
    (OGPrimitiveComul.comul.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The OG primitive counit vanishes on a sum of nine tree generators.
-/
theorem OGPrimitiveComul_counit_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
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
          treeGen w + treeGen x + treeGen y)
        (treeGen z))
  simpa [hmk, OGPrimitiveComul_counit_treeGen_sum_eight,
    OGPrimitiveComul_counit_treeGen] using
    (OGPrimitiveComul.counit.map_add
      (mkPreLieDifferenceStableQuotient
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y))
      (mkPreLieDifferenceStableQuotient (treeGen z)))

/--
The canonical-lift version of the primitive formula is just the tree-generator
formula rewritten through `stableUEA_canonicalLiftData`.
-/
theorem OGPrimitiveComul_comul_treeGen_via_canonicalLift
    (x : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int
        (stableUEA_canonicalLiftData.lift
          (mkPreLieDifferenceStableQuotient (treeGen x))) 1 +
        TensorProduct.tmul Int 1
          (stableUEA_canonicalLiftData.lift
            (mkPreLieDifferenceStableQuotient (treeGen x))) := by
  simpa using
    (OGPrimitiveComulPack_comul_on_treeGen_via_canonicalLift x)

/--
The concrete GL comultiplication on a forest sum is obtained by evaluating the
descended quotient comultiplication on `mk(forestGen f)`.
-/
theorem instance_comul_forestGen
    (f : Forest) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (forestGen f)) := by
  simpa using
    (coproductSupportQuotientCoalgebraInst.comul_mk (forestGen f))

/-!
### Relationship between GL and OG comultiplications

The GL comultiplication on `PreLieDifferenceStableQuotient` (via
`coproductSupportSummary_comul_quot h_respects`) and the OG primitive
comultiplication (via `OGPrimitiveComul.comul`) are related by the Oudom-Guin
theorem: the UEA comultiplication on generators coincides with the primitive
formula `x ⊗ 1 + 1 ⊗ x`.  A formal proof requires the isomorphism between the
GL Hopf algebra on forests and the UEA of the free pre-Lie algebra.

Until that transport is formalized, we record side-by-side comparison lemmas:
the GL comultiplication on small sums of generators, and the corresponding OG
primitive comultiplication on the same sums.
-/

/--
General side-by-side comparison on an arbitrary raw linear combination, before
passing to special finite sums of generators.
-/
theorem GL_OG_comul_compare_mk
    (a : linearProofTreeCarrier) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient a) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear a) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient a) =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  exact ⟨coproductSupportQuotientCoalgebraInst.comul_mk a,
    OGPrimitiveComul_comul_mk a⟩

/--
General side-by-side comparison of the GL and OG counits on an arbitrary raw
linear combination.
-/
theorem GL_OG_counit_compare_mk
    (a : linearProofTreeCarrier) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient a) =
      coproductSupportSummary_counit_linear a ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient a) = 0 := by
  exact ⟨coproductSupportQuotientCoalgebraInst.counit_mk a,
    OGPrimitiveComul_counit_mk a⟩

/--
Side-by-side comparison on a single tree generator.
-/
theorem GL_OG_comul_compare_treeGen
    (x : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  exact ⟨instance_comul_treeGen x, OGPrimitiveComul_comul_treeGen x⟩

/--
Side-by-side comparison on a sum of two tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_two
    (x y : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_two_tensor x y,
      OGPrimitiveComul_comul_treeGen_sum_two x y⟩

/--
Side-by-side comparison on a sum of three tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_three
    (x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_three_tensor x y z,
      OGPrimitiveComul_comul_treeGen_sum_three x y z⟩

/--
Side-by-side comparison on a sum of four tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_four
    (w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen w)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen x)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen y)) +
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_four_tensor w x y z,
      OGPrimitiveComul_comul_treeGen_sum_four w x y z⟩

/--
Side-by-side comparison on a sum of five tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_five
    (v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
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
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_five_tensor v w x y z,
      OGPrimitiveComul_comul_treeGen_sum_five v w x y z⟩

/--
Side-by-side comparison on a sum of six tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_six
    (u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
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
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_six_tensor u v w x y z,
      OGPrimitiveComul_comul_treeGen_sum_six u v w x y z⟩

/--
Side-by-side comparison on a sum of seven tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_seven
    (t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
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
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_seven_tensor t u v w x y z,
      OGPrimitiveComul_comul_treeGen_sum_seven t u v w x y z⟩

/--
Side-by-side comparison on a sum of eight tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
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
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_eight_tensor s t u v w x y z,
      OGPrimitiveComul_comul_treeGen_sum_eight s t u v w x y z⟩

/--
Side-by-side comparison on a sum of nine tree generators.
-/
theorem GL_OG_comul_compare_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient
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
        (coproductSupportSummary_comul_linear (treeGen z)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact
    ⟨coproductSupportQuotientCoalgebraInst.comul_treeGen_sum_nine_tensor r s t u v w x y z,
      OGPrimitiveComul_comul_treeGen_sum_nine r s t u v w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a single tree generator.
-/
theorem GL_OG_counit_compare_treeGen
    (x : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 := by
  exact ⟨instance_counit_treeGen_zero x, OGPrimitiveComul_counit_treeGen x⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of two tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_two
    (x y : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk (treeGen x) (treeGen y))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_two x y⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of three tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_three
    (x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen x + treeGen y) (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_three x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of four tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_four
    (w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen w + treeGen x + treeGen y) (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_four w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of five tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_five
    (v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_five v w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of six tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_six
    (u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y) (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_six u v w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of seven tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_seven
    (t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w +
            treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen t + treeGen u + treeGen v + treeGen w +
              treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_seven t u v w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of eight tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen s + treeGen t + treeGen u + treeGen v +
              treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen s + treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y)
        (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_eight s t u v w x y z⟩

/--
Side-by-side comparison of the GL and OG counits on a sum of nine tree generators.
-/
theorem GL_OG_counit_compare_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 ∧
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
  have hGL :
      coproductSupportQuotientCoalgebraInst.counit
          (mkPreLieDifferenceStableQuotient
            (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
              treeGen w + treeGen x + treeGen y + treeGen z)) = 0 := by
    simpa using
      (coproductSupportQuotientCoalgebraInst.counit_add_mk
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y)
        (treeGen z))
  exact ⟨hGL, OGPrimitiveComul_counit_treeGen_sum_nine r s t u v w x y z⟩

/-!
### GL support formulas valued directly in the stable UEA tensor

Because the canonical lift has only been packaged functionally so far, the
full tensor-level transport from quotient tensor to UEA tensor still needs a
separate linear packaging step.  What we can already do cleanly is evaluate
the same cut-support data directly in the stable UEA tensor.
-/

noncomputable def stableUEA_forestGen : Forest -> preLieDifferenceStableQuotientUEA
  | [] => 0
  | t :: ts => stableUEA_treeGen t + stableUEA_forestGen ts

@[simp] theorem stableUEA_forestGen_nil :
    stableUEA_forestGen ([] : Forest) = 0 := by
  rfl

@[simp] theorem stableUEA_forestGen_cons (t : PTree) (ts : Forest) :
    stableUEA_forestGen (t :: ts) =
      stableUEA_treeGen t + stableUEA_forestGen ts := by
  rfl

theorem stableUEA_forestGen_append (xs ys : Forest) :
    stableUEA_forestGen (xs ++ ys) =
      stableUEA_forestGen xs + stableUEA_forestGen ys := by
  induction xs with
  | nil =>
      simp [stableUEA_forestGen]
  | cons t ts ih =>
      simp [stableUEA_forestGen, ih, add_assoc, add_left_comm, add_comm]

noncomputable def stableUEA_coproductSupportSummary_tensorGen
    (p : Prod Forest PTree) : stableUEATensor :=
  TensorProduct.tmul Int (stableUEA_forestGen p.1) (stableUEA_treeGen p.2)

noncomputable def stableUEA_coproductSupportSummary_comul_linear :
    LinearMap (RingHom.id Int) linearProofTreeCarrier stableUEATensor :=
  coproductSupportSummary_sum_linear
    (alpha := stableUEATensor)
    stableUEA_coproductSupportSummary_tensorGen

noncomputable def stableUEA_expectedPrimitiveComulLinear :
    LinearMap (RingHom.id Int) linearProofTreeCarrier stableUEATensor :=
  Finsupp.lsum Int (fun x : PTree =>
    (LinearMap.id : LinearMap (RingHom.id Int) Int Int).smulRight
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)))

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_treeGen
    (x : PTree) :
    stableUEA_expectedPrimitiveComulLinear (treeGen x) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  classical
  simp only [stableUEA_expectedPrimitiveComulLinear, treeGen, Finsupp.lsum_single,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  exact one_smul Int _

theorem stableUEA_expectedPrimitiveComulLinear_apply
    (a : linearProofTreeCarrier) :
    stableUEA_expectedPrimitiveComulLinear a =
      a.sum (fun x c =>
        c • (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen x))) := by
  simp [stableUEA_expectedPrimitiveComulLinear, Finsupp.lsum_apply]
  rfl

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_add
    (a b : linearProofTreeCarrier) :
    stableUEA_expectedPrimitiveComulLinear (a + b) =
      stableUEA_expectedPrimitiveComulLinear a +
        stableUEA_expectedPrimitiveComulLinear b := by
  simpa using (stableUEA_expectedPrimitiveComulLinear.map_add a b)

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_smul
    (z : Int) (a : linearProofTreeCarrier) :
    stableUEA_expectedPrimitiveComulLinear (z • a) =
      z • stableUEA_expectedPrimitiveComulLinear a := by
  simpa using (stableUEA_expectedPrimitiveComulLinear.map_smul z a)

/--
The primitive comultiplication formula, accumulated over a whole forest.

This is the finite-list version of repeatedly adding the primitive terms
`x ⊗ 1 + 1 ⊗ x`.
-/
noncomputable def stableUEA_expectedPrimitiveComulForest : Forest -> stableUEATensor
  | [] => 0
  | t :: ts =>
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      stableUEA_expectedPrimitiveComulForest ts

@[simp] theorem stableUEA_expectedPrimitiveComulForest_nil :
    stableUEA_expectedPrimitiveComulForest ([] : Forest) = 0 := by
  rfl

@[simp] theorem stableUEA_expectedPrimitiveComulForest_cons
    (t : PTree) (ts : Forest) :
    stableUEA_expectedPrimitiveComulForest (t :: ts) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      stableUEA_expectedPrimitiveComulForest ts := by
  rfl

theorem stableUEA_expectedPrimitiveComulForest_append
    (xs ys : Forest) :
    stableUEA_expectedPrimitiveComulForest (xs ++ ys) =
      stableUEA_expectedPrimitiveComulForest xs +
        stableUEA_expectedPrimitiveComulForest ys := by
  induction xs with
  | nil =>
      simp [stableUEA_expectedPrimitiveComulForest]
  | cons t ts ih =>
      simp [stableUEA_expectedPrimitiveComulForest, ih, add_assoc,
        add_left_comm, add_comm]

/--
The raw-to-UEA linear map sends `forestGen` to the corresponding stable UEA
sum of tree generators.
-/
theorem stableUEA_rawToUEALinear_forestGen
    (f : Forest) :
    stableUEA_rawToUEALinear (forestGen f) = stableUEA_forestGen f := by
  induction f with
  | nil =>
      simp
  | cons t ts ih =>
      simp [forestGen_cons, stableUEA_forestGen_cons, ih,
        stableUEA_rawToUEALinear_add, stableUEA_rawToUEALinear_treeGen]

/--
Likewise, the older quotient-then-UEA map sends `forestGen` to the same stable
UEA forest sum.
-/
theorem preLieDifferenceStableQuotientToUEA_forestGen
    (f : Forest) :
    preLieDifferenceStableQuotientToUEA (forestGen f) = stableUEA_forestGen f := by
  rw [← stableUEA_rawToUEALinear_eq_preLieDifferenceStableQuotientToUEA]
  exact stableUEA_rawToUEALinear_forestGen f

/--
The recursive forest primitive formula is equivalent to the compact primitive
formula on the forest sum itself.
-/
theorem stableUEA_expectedPrimitiveComulForest_eq_formula
    (f : Forest) :
    stableUEA_expectedPrimitiveComulForest f =
      TensorProduct.tmul Int (stableUEA_forestGen f) 1 +
        TensorProduct.tmul Int 1 (stableUEA_forestGen f) := by
  induction f with
  | nil =>
      simp [stableUEA_expectedPrimitiveComulForest, stableUEA_forestGen]
  | cons t ts ih =>
      simp [stableUEA_expectedPrimitiveComulForest, stableUEA_forestGen, ih,
        TensorProduct.tmul_add, TensorProduct.add_tmul, add_assoc,
        add_left_comm, add_comm]

/--
Applying the expected primitive linear comultiplication to `forestGen f`
produces the recursive forest primitive formula.
-/
theorem stableUEA_expectedPrimitiveComulLinear_forestGen
    (f : Forest) :
    stableUEA_expectedPrimitiveComulLinear (forestGen f) =
      stableUEA_expectedPrimitiveComulForest f := by
  induction f with
  | nil =>
      simp [forestGen, stableUEA_expectedPrimitiveComulForest]
  | cons t ts ih =>
      simp [forestGen_cons, stableUEA_expectedPrimitiveComulForest, ih,
        stableUEA_expectedPrimitiveComulLinear_add,
        stableUEA_expectedPrimitiveComulLinear_treeGen]

/--
The OG primitive raw linear comultiplication on `forestGen f` is exactly the
recursive forest primitive formula.
-/
theorem stableUEA_OGPrimitive_comul_linear_forestGen
    (f : Forest) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen f) =
      stableUEA_expectedPrimitiveComulForest f := by
  calc
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen f)
        = TensorProduct.tmul Int (stableUEA_rawToUEALinear (forestGen f)) 1 +
            TensorProduct.tmul Int 1 (stableUEA_rawToUEALinear (forestGen f)) := by
              exact stableUEA_OGPrimitive_comul_linear_formula (forestGen f)
    _ = TensorProduct.tmul Int (stableUEA_forestGen f) 1 +
          TensorProduct.tmul Int 1 (stableUEA_forestGen f) := by
            simp [stableUEA_rawToUEALinear_forestGen]
    _ = stableUEA_expectedPrimitiveComulForest f := by
          symm
          exact stableUEA_expectedPrimitiveComulForest_eq_formula f

/--
The OG primitive raw linear counit vanishes on every forest sum.
-/
theorem stableUEA_OGPrimitive_counit_linear_forestGen
    (f : Forest) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen f) = 0 := by
  induction f with
  | nil =>
      simp [forestGen]
  | cons t ts ih =>
      simp [forestGen_cons, ih, stableUEA_counit_linear_add,
        stableUEA_counit_linear_treeGen]

/--
The cut-support comultiplication, evaluated in the stable UEA tensor, also
admits a recursive forest formula.
-/
noncomputable def stableUEA_coproductSupportSummary_comulForest : Forest -> stableUEATensor
  | [] => 0
  | t :: ts =>
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        stableUEA_coproductSupportSummary_comulForest ts

@[simp] theorem stableUEA_coproductSupportSummary_comulForest_nil :
    stableUEA_coproductSupportSummary_comulForest ([] : Forest) = 0 := by
  rfl

@[simp] theorem stableUEA_coproductSupportSummary_comulForest_cons
    (t : PTree) (ts : Forest) :
    stableUEA_coproductSupportSummary_comulForest (t :: ts) =
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        stableUEA_coproductSupportSummary_comulForest ts := by
  rfl

theorem stableUEA_coproductSupportSummary_comulForest_append
    (xs ys : Forest) :
    stableUEA_coproductSupportSummary_comulForest (xs ++ ys) =
      stableUEA_coproductSupportSummary_comulForest xs +
        stableUEA_coproductSupportSummary_comulForest ys := by
  induction xs with
  | nil =>
      simp [stableUEA_coproductSupportSummary_comulForest]
  | cons t ts ih =>
      simp [stableUEA_coproductSupportSummary_comulForest, ih, add_assoc,
        add_left_comm, add_comm]

/--
Evaluating the cut-support linear map on `forestGen f` gives the recursive
forest sum of the one-tree cut-support contributions.
-/
theorem stableUEA_coproductSupportSummary_comul_linear_forestGen
    (f : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen f) =
      stableUEA_coproductSupportSummary_comulForest f := by
  induction f with
  | nil =>
      simp [forestGen, stableUEA_coproductSupportSummary_comulForest]
  | cons t ts ih =>
      rw [forestGen_cons, stableUEA_coproductSupportSummary_comulForest_cons]
      change
        (coproductSupportSummary_sum_linear
            stableUEA_coproductSupportSummary_tensorGen) (treeGen t + forestGen ts) =
          coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
            stableUEA_coproductSupportSummary_comulForest ts
      rw [coproductSupportSummary_sum_linear_add,
        coproductSupportSummary_sum_linear_treeGen]
      simpa [stableUEA_coproductSupportSummary_comul_linear] using ih

/--
The cut-support linear counit vanishes on every forest sum, since it already
vanishes on each tree generator.
-/
theorem coproductSupportSummary_counit_linear_forestGen
    (f : Forest) :
    coproductSupportSummary_counit_linear (forestGen f) = 0 := by
  induction f with
  | nil =>
      simp [forestGen]
  | cons t ts ih =>
      simp [forestGen_cons, ih, coproductSupportSummary_counit_linear_add,
        coproductSupportSummary_counit_linear_treeGen]

/--
The concrete GL counit vanishes on every forest sum.
-/
theorem instance_counit_forestGen_zero
    (f : Forest) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 := by
  simpa [coproductSupportSummary_counit_linear_forestGen] using
    (coproductSupportQuotientCoalgebraInst.counit_mk (forestGen f))

/--
The descended OG primitive comultiplication on a forest sum is the recursive
forest primitive formula.
-/
theorem OGPrimitiveComul_comul_forestGen
    (f : Forest) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      stableUEA_expectedPrimitiveComulForest f := by
  calc
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen f))
        =
      TensorProduct.tmul Int
        (preLieDifferenceStableQuotientToUEA (forestGen f)) 1 +
      TensorProduct.tmul Int 1
        (preLieDifferenceStableQuotientToUEA (forestGen f)) := by
          exact OGPrimitiveComul_comul_mk (forestGen f)
    _ =
      TensorProduct.tmul Int (stableUEA_forestGen f) 1 +
        TensorProduct.tmul Int 1 (stableUEA_forestGen f) := by
          simp [preLieDifferenceStableQuotientToUEA_forestGen]
    _ = stableUEA_expectedPrimitiveComulForest f := by
          symm
          exact stableUEA_expectedPrimitiveComulForest_eq_formula f

/--
The descended OG primitive counit vanishes on every forest sum.
-/
theorem OGPrimitiveComul_counit_forestGen
    (f : Forest) :
    OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 := by
  exact OGPrimitiveComul_counit_mk (forestGen f)

/--
Forest-level side-by-side comparison of the GL and OG comultiplications.
-/
theorem GL_OG_comul_compare_forestGen
    (f : Forest) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      mkPreLieDifferenceStableQuotient_tensor
        (coproductSupportSummary_comul_linear (forestGen f)) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen f)) =
      stableUEA_expectedPrimitiveComulForest f := by
  exact ⟨instance_comul_forestGen f, OGPrimitiveComul_comul_forestGen f⟩

/--
Forest-level side-by-side comparison of the GL and OG counits.
-/
theorem GL_OG_counit_compare_forestGen
    (f : Forest) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 ∧
      OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 := by
  exact ⟨instance_counit_forestGen_zero f, OGPrimitiveComul_counit_forestGen f⟩

/--
Raw same-codomain comparison on a forest generator sum: the GL support-side
linear map and the OG primitive linear map both admit explicit forest formulas.
-/
theorem GLSupport_OGRaw_compare_forestGen
    (f : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen f) =
        stableUEA_coproductSupportSummary_comulForest f ∧
      stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen f) =
        stableUEA_expectedPrimitiveComulForest f := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_forestGen f,
    stableUEA_OGPrimitive_comul_linear_forestGen f⟩

/--
Forest-level comparison between the raw GL support-side comultiplication and
the descended OG primitive comultiplication.
-/
theorem GLSupport_OG_comul_compare_forestGen
    (f : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen f) =
        stableUEA_coproductSupportSummary_comulForest f ∧
      OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen f)) =
        stableUEA_expectedPrimitiveComulForest f := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_forestGen f,
    OGPrimitiveComul_comul_forestGen f⟩

/--
Forest-level comparison between the raw GL support-side comultiplication and
the expected primitive comultiplication formula.
-/
theorem GLSupport_expectedPrimitive_compare_forestGen
    (f : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen f) =
        stableUEA_coproductSupportSummary_comulForest f ∧
      stableUEA_expectedPrimitiveComulLinear (forestGen f) =
        stableUEA_expectedPrimitiveComulForest f := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_forestGen f,
    stableUEA_expectedPrimitiveComulLinear_forestGen f⟩

/--
Raw same-codomain counit comparison on a forest generator sum: both the GL
support-side counit and the OG primitive counit vanish.
-/
theorem GLSupport_OGRaw_counit_compare_forestGen
    (f : Forest) :
    coproductSupportSummary_counit_linear (forestGen f) = 0 ∧
      stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen f) = 0 := by
  exact ⟨coproductSupportSummary_counit_linear_forestGen f,
    stableUEA_OGPrimitive_counit_linear_forestGen f⟩

/--
The expected primitive comultiplication of an appended forest is the sum of the
expected primitive comultiplications of the two parts.
-/
theorem stableUEA_expectedPrimitiveComulLinear_forestGen_append
    (xs ys : Forest) :
    stableUEA_expectedPrimitiveComulLinear (forestGen (xs ++ ys)) =
      stableUEA_expectedPrimitiveComulLinear (forestGen xs) +
        stableUEA_expectedPrimitiveComulLinear (forestGen ys) := by
  rw [stableUEA_expectedPrimitiveComulLinear_forestGen,
    stableUEA_expectedPrimitiveComulLinear_forestGen,
    stableUEA_expectedPrimitiveComulLinear_forestGen,
    stableUEA_expectedPrimitiveComulForest_append]

/--
The raw OG primitive comultiplication of an appended forest is the sum of the
raw OG primitive comultiplications of the two parts.
-/
theorem stableUEA_OGPrimitive_comul_linear_forestGen_append
    (xs ys : Forest) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (forestGen (xs ++ ys)) =
      stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen xs) +
        stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen ys) := by
  rw [stableUEA_OGPrimitive_comul_linear_forestGen,
    stableUEA_OGPrimitive_comul_linear_forestGen,
    stableUEA_OGPrimitive_comul_linear_forestGen,
    stableUEA_expectedPrimitiveComulForest_append]

/--
The raw GL support-side comultiplication of an appended forest is the sum of the
raw GL support-side comultiplications of the two parts.
-/
theorem stableUEA_coproductSupportSummary_comul_linear_forestGen_append
    (xs ys : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen (xs ++ ys)) =
      stableUEA_coproductSupportSummary_comul_linear (forestGen xs) +
        stableUEA_coproductSupportSummary_comul_linear (forestGen ys) := by
  rw [stableUEA_coproductSupportSummary_comul_linear_forestGen,
    stableUEA_coproductSupportSummary_comul_linear_forestGen,
    stableUEA_coproductSupportSummary_comul_linear_forestGen,
    stableUEA_coproductSupportSummary_comulForest_append]

/--
The descended OG primitive comultiplication of an appended forest is the sum of
the descended OG primitive comultiplications of the two parts.
-/
theorem OGPrimitiveComul_comul_forestGen_append
    (xs ys : Forest) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  rw [OGPrimitiveComul_comul_forestGen, OGPrimitiveComul_comul_forestGen,
    OGPrimitiveComul_comul_forestGen, stableUEA_expectedPrimitiveComulForest_append]

/--
Any packaged quotient comultiplication data agrees with the OG primitive forest
formula on arbitrary forest sums.
-/
theorem StableQuotientComultiplicationData_comul_forestGen
    (D : StableQuotientComultiplicationData)
    (f : Forest) :
    D.comul (mkPreLieDifferenceStableQuotient (forestGen f)) =
      stableUEA_expectedPrimitiveComulForest f := by
  have hD := StableQuotientComultiplicationData_eq_OGPrimitive D
  rw [hD.1]
  exact OGPrimitiveComul_comul_forestGen f

/--
Any packaged quotient comultiplication data has zero counit on arbitrary forest
sums.
-/
theorem StableQuotientComultiplicationData_counit_forestGen
    (D : StableQuotientComultiplicationData)
    (f : Forest) :
    D.counit (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 := by
  have hD := StableQuotientComultiplicationData_eq_OGPrimitive D
  rw [hD.2]
  exact OGPrimitiveComul_counit_forestGen f

/--
Any quotient comultiplication pack agrees with the OG primitive forest formula
on arbitrary forest sums.
-/
theorem StableQuotientComultiplicationPack_comul_forestGen
    (D : StableQuotientComultiplicationPack)
    (f : Forest) :
    D.comul (mkPreLieDifferenceStableQuotient (forestGen f)) =
      stableUEA_expectedPrimitiveComulForest f := by
  have hD := StableQuotientComultiplicationPack_eq_OGPrimitive D
  rw [hD.1]
  exact OGPrimitiveComul_comul_forestGen f

/--
Any quotient comultiplication pack has zero counit on arbitrary forest sums.
-/
theorem StableQuotientComultiplicationPack_counit_forestGen
    (D : StableQuotientComultiplicationPack)
    (f : Forest) :
    D.counit (mkPreLieDifferenceStableQuotient (forestGen f)) = 0 := by
  have hD := StableQuotientComultiplicationPack_eq_OGPrimitive D
  rw [hD.2]
  exact OGPrimitiveComul_counit_forestGen f

/--
Any packaged quotient comultiplication data is additive with respect to forest
concatenation.
-/
theorem StableQuotientComultiplicationData_comul_forestGen_append
    (D : StableQuotientComultiplicationData)
    (xs ys : Forest) :
    D.comul (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      D.comul (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        D.comul (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  have hD := StableQuotientComultiplicationData_eq_OGPrimitive D
  rw [hD.1]
  exact OGPrimitiveComul_comul_forestGen_append xs ys

/--
Likewise, any quotient comultiplication pack is additive with respect to forest
concatenation.
-/
theorem StableQuotientComultiplicationPack_comul_forestGen_append
    (D : StableQuotientComultiplicationPack)
    (xs ys : Forest) :
    D.comul (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      D.comul (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        D.comul (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  have hD := StableQuotientComultiplicationPack_eq_OGPrimitive D
  rw [hD.1]
  exact OGPrimitiveComul_comul_forestGen_append xs ys

/--
The descended GL support-side comultiplication of an appended forest is the sum
of the descended GL support-side comultiplications of the two parts.
-/
theorem instance_comul_forestGen_append
    (xs ys : Forest) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      coproductSupportQuotientCoalgebraInst.comul
          (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        coproductSupportQuotientCoalgebraInst.comul
          (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  rw [instance_comul_forestGen, instance_comul_forestGen, instance_comul_forestGen]
  rw [forestGen_append, coproductSupportSummary_comul_linear_add,
    mkPreLieDifferenceStableQuotient_tensor_add]

/--
The descended GL/OG comultiplication comparison is additive with respect to
forest concatenation.
-/
theorem GL_OG_comul_compare_forestGen_append
    (xs ys : Forest) :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      coproductSupportQuotientCoalgebraInst.comul
          (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        coproductSupportQuotientCoalgebraInst.comul
          (mkPreLieDifferenceStableQuotient (forestGen ys)) ∧
      OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  exact ⟨instance_comul_forestGen_append xs ys,
    OGPrimitiveComul_comul_forestGen_append xs ys⟩

/--
The raw GL support-side and descended OG primitive forest comultiplications are
both additive with respect to forest concatenation.
-/
theorem GLSupport_OG_comul_compare_forestGen_append
    (xs ys : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen (xs ++ ys)) =
      stableUEA_coproductSupportSummary_comul_linear (forestGen xs) +
        stableUEA_coproductSupportSummary_comul_linear (forestGen ys) ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) =
      OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen xs)) +
        OGPrimitiveComul.comul
          (mkPreLieDifferenceStableQuotient (forestGen ys)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_forestGen_append xs ys,
    OGPrimitiveComul_comul_forestGen_append xs ys⟩

/--
The raw GL support-side and expected primitive forest comultiplications are
both additive with respect to forest concatenation.
-/
theorem GLSupport_expectedPrimitive_compare_forestGen_append
    (xs ys : Forest) :
    stableUEA_coproductSupportSummary_comul_linear (forestGen (xs ++ ys)) =
      stableUEA_coproductSupportSummary_comul_linear (forestGen xs) +
        stableUEA_coproductSupportSummary_comul_linear (forestGen ys) ∧
    stableUEA_expectedPrimitiveComulLinear (forestGen (xs ++ ys)) =
      stableUEA_expectedPrimitiveComulLinear (forestGen xs) +
        stableUEA_expectedPrimitiveComulLinear (forestGen ys) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_forestGen_append xs ys,
    stableUEA_expectedPrimitiveComulLinear_forestGen_append xs ys⟩

/--
Both descended counits vanish on appended forest sums.
-/
theorem GL_OG_counit_compare_forestGen_append
    (xs ys : Forest) :
    coproductSupportQuotientCoalgebraInst.counit
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) = 0 ∧
      OGPrimitiveComul.counit
        (mkPreLieDifferenceStableQuotient (forestGen (xs ++ ys))) = 0 := by
  exact GL_OG_counit_compare_forestGen (xs ++ ys)

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_forestGen_nil :
    stableUEA_expectedPrimitiveComulLinear (forestGen ([] : Forest)) = 0 := by
  simpa using stableUEA_expectedPrimitiveComulLinear_forestGen ([] : Forest)

@[simp] theorem stableUEA_OGPrimitive_comul_linear_forestGen_nil :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (forestGen ([] : Forest)) = 0 := by
  simpa using stableUEA_OGPrimitive_comul_linear_forestGen ([] : Forest)

@[simp] theorem stableUEA_coproductSupportSummary_comul_linear_forestGen_nil :
    stableUEA_coproductSupportSummary_comul_linear (forestGen ([] : Forest)) = 0 := by
  simpa using stableUEA_coproductSupportSummary_comul_linear_forestGen ([] : Forest)

@[simp] theorem OGPrimitiveComul_comul_forestGen_nil :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen ([] : Forest))) = 0 := by
  simpa [stableUEA_expectedPrimitiveComulForest_nil] using
    OGPrimitiveComul_comul_forestGen ([] : Forest)

@[simp] theorem instance_comul_forestGen_nil :
    coproductSupportQuotientCoalgebraInst.comul
        (mkPreLieDifferenceStableQuotient (forestGen ([] : Forest))) = 0 := by
  simpa [stableUEA_coproductSupportSummary_comulForest_nil] using
    instance_comul_forestGen ([] : Forest)

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_forestGen_singleton
    (t : PTree) :
    stableUEA_expectedPrimitiveComulLinear (forestGen [t]) =
      TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    stableUEA_expectedPrimitiveComulLinear_forestGen [t]

@[simp] theorem stableUEA_OGPrimitive_comul_linear_forestGen_singleton
    (t : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen [t]) =
      TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    stableUEA_OGPrimitive_comul_linear_forestGen [t]

@[simp] theorem OGPrimitiveComul_comul_forestGen_singleton
    (t : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen [t])) =
      TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    OGPrimitiveComul_comul_forestGen [t]

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_forestGen_pair
    (s t : PTree) :
    stableUEA_expectedPrimitiveComulLinear (forestGen [s, t]) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    stableUEA_expectedPrimitiveComulLinear_forestGen [s, t]

@[simp] theorem stableUEA_OGPrimitive_comul_linear_forestGen_pair
    (s t : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen [s, t]) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    stableUEA_OGPrimitive_comul_linear_forestGen [s, t]

@[simp] theorem OGPrimitiveComul_comul_forestGen_pair
    (s t : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen [s, t])) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) := by
  simpa [stableUEA_expectedPrimitiveComulForest] using
    OGPrimitiveComul_comul_forestGen [s, t]

@[simp] theorem stableUEA_expectedPrimitiveComulLinear_forestGen_triple
    (r s t : PTree) :
    stableUEA_expectedPrimitiveComulLinear (forestGen [r, s, t]) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      ((TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
        (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen t))) := by
  simpa [stableUEA_expectedPrimitiveComulForest, add_assoc] using
    stableUEA_expectedPrimitiveComulLinear_forestGen [r, s, t]

@[simp] theorem stableUEA_OGPrimitive_comul_linear_forestGen_triple
    (r s t : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (forestGen [r, s, t]) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      ((TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
        (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen t))) := by
  simpa [stableUEA_expectedPrimitiveComulForest, add_assoc] using
    stableUEA_OGPrimitive_comul_linear_forestGen [r, s, t]

@[simp] theorem OGPrimitiveComul_comul_forestGen_triple
    (r s t : PTree) :
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (forestGen [r, s, t])) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      ((TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
        (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
          TensorProduct.tmul Int 1 (stableUEA_treeGen t))) := by
  simpa [stableUEA_expectedPrimitiveComulForest, add_assoc] using
    OGPrimitiveComul_comul_forestGen [r, s, t]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_two
    (x y : PTree) :
    stableUEA_expectedPrimitiveComulLinear (treeGen x + treeGen y) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear (treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

theorem stableUEA_expectedPrimitiveComulLinear_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_expectedPrimitiveComulLinear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simp [stableUEA_expectedPrimitiveComulLinear_add, add_assoc]

@[simp] theorem stableUEA_OGPrimitive_comul_linear_eq_expected :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData =
      stableUEA_expectedPrimitiveComulLinear := by
  apply LinearMap.ext
  intro a
  induction a using Finsupp.induction_linear with
  | zero =>
      simp [stableUEA_comul_linear, stableUEA_expectedPrimitiveComulLinear]
  | add f g hf hg =>
      simp [hf, hg]
  | single x n =>
      simp [stableUEA_comul_linear, stableUEA_expectedPrimitiveComulLinear,
        stableUEA_OGPrimitiveGeneratorComulData, Finsupp.lsum_single,
        LinearMap.smulRight_apply, LinearMap.id_apply]



theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_two
    (x y : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_two x y)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_three x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_four w x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_five v w x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_six u v w x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_seven t u v w x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_eight s t u v w x y z)

theorem stableUEA_OGPrimitive_comul_linear_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen r + treeGen s + treeGen t + treeGen u +
          treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  simpa [stableUEA_OGPrimitive_comul_linear_eq_expected] using
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_nine r s t u v w x y z)
@[simp] theorem stableUEA_coproductSupportSummary_comul_linear_treeGen
    (x : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear,
    coproductSupportSummary_sum_linear_treeGen]

theorem stableUEA_coproductSupportSummary_comul_linear_apply
    (a : linearProofTreeCarrier) :
    stableUEA_coproductSupportSummary_comul_linear a =
      a.sum (fun x c =>
        c • coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen) := by
  simp [stableUEA_coproductSupportSummary_comul_linear,
    coproductSupportSummary_sum_linear_apply]
  rfl

@[simp] theorem stableUEA_coproductSupportSummary_comul_linear_add
    (a b : linearProofTreeCarrier) :
    stableUEA_coproductSupportSummary_comul_linear (a + b) =
      stableUEA_coproductSupportSummary_comul_linear a +
        stableUEA_coproductSupportSummary_comul_linear b := by
  simpa using (stableUEA_coproductSupportSummary_comul_linear.map_add a b)

@[simp] theorem stableUEA_coproductSupportSummary_comul_linear_smul
    (z : Int) (a : linearProofTreeCarrier) :
    stableUEA_coproductSupportSummary_comul_linear (z • a) =
      z • stableUEA_coproductSupportSummary_comul_linear a := by
  simpa using (stableUEA_coproductSupportSummary_comul_linear.map_smul z a)

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_two
    (x y : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x + treeGen y) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum r stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen := by
  simp [stableUEA_coproductSupportSummary_comul_linear_add, add_assoc]

theorem GLSupport_OG_comul_compare_treeGen
    (x : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen x,
    OGPrimitiveComul_comul_treeGen x⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_two
    (x y : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x + treeGen y) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_two x y,
    OGPrimitiveComul_comul_treeGen_sum_two x y⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient (treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_three x y z,
    OGPrimitiveComul_comul_treeGen_sum_three x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_four w x y z,
    OGPrimitiveComul_comul_treeGen_sum_four w x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_five v w x y z,
    OGPrimitiveComul_comul_treeGen_sum_five v w x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_six u v w x y z,
    OGPrimitiveComul_comul_treeGen_sum_six u v w x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_seven t u v w x y z,
    OGPrimitiveComul_comul_treeGen_sum_seven t u v w x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_eight s t u v w x y z,
    OGPrimitiveComul_comul_treeGen_sum_eight s t u v w x y z⟩

theorem GLSupport_OG_comul_compare_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum r stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen ∧
    OGPrimitiveComul.comul
        (mkPreLieDifferenceStableQuotient
          (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
            treeGen w + treeGen x + treeGen y + treeGen z)) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_nine r s t u v w x y z,
    OGPrimitiveComul_comul_treeGen_sum_nine r s t u v w x y z⟩

theorem GLSupport_expectedPrimitive_compare_treeGen
    (x : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear (treeGen x) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen x)
    (stableUEA_expectedPrimitiveComulLinear_treeGen x)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_two
    (x y : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x + treeGen y) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear (treeGen x + treeGen y) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_two x y)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_two x y)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear (treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_three x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_three x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_four w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_four w x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_five v w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_five v w x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_six u v w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_six u v w x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_seven t u v w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_seven t u v w x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_eight s t u v w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_eight s t u v w x y z)

theorem GLSupport_expectedPrimitive_compare_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum r stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_expectedPrimitiveComulLinear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) := by
  exact And.intro
    (stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_nine r s t u v w x y z)
    (stableUEA_expectedPrimitiveComulLinear_treeGen_sum_nine r s t u v w x y z)

@[simp] theorem stableUEA_OGPrimitive_counit_linear_apply_zero
    (a : linearProofTreeCarrier) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  simpa using
    congrFun
      (congrArg DFunLike.coe stableUEA_OGPrimitive_counit_linear_eq_zero) a

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_two
    (x y : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero (treeGen x + treeGen y))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen w + treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen s + treeGen t + treeGen u + treeGen v +
        treeGen w + treeGen x + treeGen y + treeGen z))

theorem stableUEA_OGPrimitive_counit_linear_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen r + treeGen s + treeGen t + treeGen u +
          treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  simpa using
    (stableUEA_OGPrimitive_counit_linear_apply_zero
      (treeGen r + treeGen s + treeGen t + treeGen u +
        treeGen v + treeGen w + treeGen x + treeGen y + treeGen z))

theorem GLSupport_OGRaw_compare_treeGen
    (x : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData (treeGen x) =
      TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData (treeGen x) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen x,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen x,
      stableUEA_OGPrimitive_counit_linear_treeGen x⟩⟩

theorem GLSupport_OGRaw_compare_apply
    (a : linearProofTreeCarrier) :
    stableUEA_coproductSupportSummary_comul_linear a =
      a.sum (fun x c =>
        c • coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen) /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      TensorProduct.tmul Int (stableUEA_rawToUEALinear a) 1 +
        TensorProduct.tmul Int 1 (stableUEA_rawToUEALinear a) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData a = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_apply a,
    ⟨stableUEA_OGPrimitive_comul_linear_formula a,
      stableUEA_OGPrimitive_counit_linear_apply_zero a⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_two
    (x y : PTree) :
    stableUEA_coproductSupportSummary_comul_linear (treeGen x + treeGen y) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_two x y,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_two x y,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_two x y⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_three
    (x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_three x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_three x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_three x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_four
    (w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_four w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_four w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_four w x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_five
    (v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_five v w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_five v w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_five v w x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_six
    (u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_six u v w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_six u v w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_six u v w x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_seven
    (t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen t + treeGen u + treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_seven t u v w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_seven t u v w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_seven t u v w x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_eight
    (s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_eight s t u v w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_eight s t u v w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_eight s t u v w x y z⟩⟩

theorem GLSupport_OGRaw_compare_treeGen_sum_nine
    (r s t u v w x y z : PTree) :
    stableUEA_coproductSupportSummary_comul_linear
        (treeGen r + treeGen s + treeGen t + treeGen u + treeGen v +
          treeGen w + treeGen x + treeGen y + treeGen z) =
      coproductSupportSummary_sum r stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum s stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum t stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum u stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum v stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum w stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum x stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum y stableUEA_coproductSupportSummary_tensorGen +
        coproductSupportSummary_sum z stableUEA_coproductSupportSummary_tensorGen /\
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen r + treeGen s + treeGen t + treeGen u +
          treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) =
      (TensorProduct.tmul Int (stableUEA_treeGen r) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen r)) +
      (TensorProduct.tmul Int (stableUEA_treeGen s) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen s)) +
      (TensorProduct.tmul Int (stableUEA_treeGen t) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen t)) +
      (TensorProduct.tmul Int (stableUEA_treeGen u) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen u)) +
      (TensorProduct.tmul Int (stableUEA_treeGen v) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen v)) +
      (TensorProduct.tmul Int (stableUEA_treeGen w) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen w)) +
      (TensorProduct.tmul Int (stableUEA_treeGen x) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen x)) +
      (TensorProduct.tmul Int (stableUEA_treeGen y) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen y)) +
      (TensorProduct.tmul Int (stableUEA_treeGen z) 1 +
        TensorProduct.tmul Int 1 (stableUEA_treeGen z)) /\
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData
        (treeGen r + treeGen s + treeGen t + treeGen u +
          treeGen v + treeGen w + treeGen x + treeGen y + treeGen z) = 0 := by
  exact ⟨stableUEA_coproductSupportSummary_comul_linear_treeGen_sum_nine r s t u v w x y z,
    ⟨stableUEA_OGPrimitive_comul_linear_treeGen_sum_nine r s t u v w x y z,
      stableUEA_OGPrimitive_counit_linear_treeGen_sum_nine r s t u v w x y z⟩⟩

/--
The counit on the stable quotient induced by the OG primitive data is
the zero map on generators, consistent with the augmentation ideal structure.
-/
theorem OGPrimitiveComul_counit_eq_zero_on_generators :
    ∀ (x : PTree),
      OGPrimitiveComul.counit
          (mkPreLieDifferenceStableQuotient (treeGen x)) = 0 :=
  OGPrimitiveComul_counit_treeGen

end OudomGuinScaffolding

/-! ## 18. Coalgebra summary and live sorry ledger

All non-trivial theorems that remain `sorry`'d, with their mathematical status:

### Sorry'd combinatorial theorems (core bottlenecks)

1. `coproductSupportSummary_comul_linear_preLieDifferenceGenerators` (Section 2a):
   The GL coproduct kills every pre-Lie difference generator.
   *Status*: Requires a bijection on admissible-cut addresses.

2. `comul_linear_ker_stable_left/right` (Section 2b):
   The kernel is stable under graftPreLie by tree generators.
   *Status*: Requires the coaction formula Δ(u ▷ a) in terms of Δ(a).

3. `comul_quot_coassoc_tensor` (Section 5):
   Pointwise cut-tensor coassociativity for the descended comultiplication.
   *Status*: Requires a two-level cut bijection.  The higher tree-level and
   global coassociativity theorems are now reduced to this pointwise theorem.

### Sorry'd counit theorems (structural issue in main file)

4. `coproductSupportSummary_rTensor_counit_comp_comul` (Section 8):
   Right counit law with the zero counit.  *False as stated.*
   *Status*: The counit definition in the main file needs `then 1` not `then 0`.

5. `coproductSupportSummary_lTensor_counit_comp_comul` (Section 8):
   Left counit law.  *False as stated.*  Same fix needed.

### Sorry'd corrected-counit theorems (Section 14–15)

6. `correctedCounit_linear_preLieDifferenceGenerators`:
   The corrected counit kills generators.
   *Status*: Follows from the leaf-count symmetry `[(b+c-1)+a-(a+c-1)-b] = 0`.
   *Needs*: Formal leaf-count lemmas for `PTree.graftPreLieTree`.

7. `correctedCounit_linear_graft_preLieDifferenceGenerators`:
   Corrected counit kills graftings of generators.
   *Status*: Same leaf-count identity propagates to all grafting depths.

8. `correctedCounit_linear_kills_stableSubmodule`:
   Descent of corrected counit.
   *Status*: Follows from (6) and (7) by induction on stable closure.

9. `correctedCounit_rTensor_comp_comul` / `correctedCounit_lTensor_comp_comul`:
   The naive corrected-counit laws are false as stated.
   *Status*: Obstructed already on `nodeLeaf`; see
   `correctedCounit_rTensor_comp_comul_obstructed` and
   `correctedCounit_lTensor_comp_comul_obstructed`.

### Completed since the original ledger

The theorem

`stableUEA_OGPrimitive_respectsStableQuotient_axiom`

is now proved in Section 17, so it is no longer part of the live blocker list.

At the theorem level, the file still contains 9 explicit `sorry`s; the list
below groups those into the main mathematical bottlenecks rather than counting
every wrapper lemma separately.
-/

section SorryLedger

/-- Summary: the live blocker list above has 9 grouped items, while the file
still contains 9 explicit theorem-level `sorry`s.  The mathematical content is
fully specified; the remaining `sorry`s mark combinatorial or UEA-theoretic
gaps rather than missing architectural structure. -/
theorem sorry_ledger_count : True := trivial

end SorryLedger

end QuotientConnected.CoproductSupport
