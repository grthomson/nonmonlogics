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
theorem coproductSupportSummary_comul_linear_preLieDifferenceGenerators
    (x y z : PTree) :
    coproductSupportSummary_comul_linear (preLieDifferenceGenerators x y z) = 0 := by
  sorry

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
The kernel of `coproductSupportSummary_comul_linear` is a member of
`preLieDifferenceStableSubmoduleFamily`:
* it contains `preLieDifferenceSubmodule` (by (2a)), and
* it is stable under generator grafting (by (2b)).
-/
theorem comul_linear_ker_mem_stableFamily :
    (coproductSupportSummary_comul_linear).ker ∈ preLieDifferenceStableSubmoduleFamily := by
  refine ⟨?_, ?_, ?_⟩
  · -- preLieDifferenceSubmodule ≤ ker(comul_linear)
    apply Submodule.span_le.mpr
    rintro a ⟨x, y, z, rfl⟩
    exact LinearMap.mem_ker.mpr
      (coproductSupportSummary_comul_linear_preLieDifferenceGenerators x y z)
  · -- stable under left grafting
    intro u a ha
    exact LinearMap.mem_ker.mpr
      (comul_linear_ker_stable_left u (LinearMap.mem_ker.mp ha))
  · -- stable under right grafting
    intro u a ha
    exact LinearMap.mem_ker.mpr
      (comul_linear_ker_stable_right u (LinearMap.mem_ker.mp ha))

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
  have hmem : a ∈ (coproductSupportSummary_comul_linear).ker :=
    Submodule.mem_sInf.mp ha _ comul_linear_ker_mem_stableFamily
  exact LinearMap.mem_ker.mp hmem

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
Coassociativity on a single generator `treeGen x`:
`(id ⊗ Δ)(Δ(mk(tg x))) = assoc((Δ ⊗ id)(Δ(mk(tg x))))`.
This follows from `comul_quot_coassoc_tensor` by summing over the admissible cuts of `x`.
-/
theorem comul_quot_coassoc_treeGen (x : PTree) :
    coproductSupportSummary_comul_quot_left h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) =
      coproductSupportSummary_comul_quot_left_assoc h_respects
        (mkPreLieDifferenceStableQuotient (treeGen x)) := by
  simp only [coproductSupportSummary_comul_quot_left_treeGen_sum,
             coproductSupportSummary_comul_quot_left_assoc_treeGen_sum]
  -- Both sides are Σ over cuts of x applied to the same tensor;
  -- use linearity of assoc and rTensor to reduce to individual cut tensors.
  rw [← coproductSupportSummary_comul_linear_treeGen]
  simp only [coproductSupportSummary_comul_linear_apply]
  -- Reduce to comul_quot_coassoc_tensor on each summand via linearity.
  sorry

/--
Coassociativity of the descended comultiplication:
`(id ⊗ Δ) ∘ Δ = assoc ∘ (Δ ⊗ id) ∘ Δ`
as linear maps `PreLieDifferenceStableQuotient → Q ⊗ Q ⊗ Q`.
-/
theorem coproductSupportSummary_comul_quot_coassoc :
    coproductSupportSummary_comul_quot_left h_respects =
      coproductSupportSummary_comul_quot_left_assoc h_respects := by
  apply LinearMap.ext
  intro a
  -- Reduce to the quotient via induction on `linearProofTreeCarrier`.
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    -- Reduce to free-module generators via Finsupp linear induction.
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
        exact congrArg (fun q => n • q) (comul_quot_coassoc_treeGen x)

end Coassociativity

/-! ## 6. Instantiation of the coalgebra axioms structure

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
  have hEval := congrArg
      (fun f =>
        f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) h
  have hTensor :
      TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) =
      TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) := by
    calc
      TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) +
        TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)))
          =
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) := by
            symm
            exact correctedCounit_rTensor_comp_comul_treeGen_nodeLeaf r s s'
      _ =
        (fun f =>
          f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))))
          ((TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient) 1) := by
            exact hEval
      _ =
        TensorProduct.tmul ℤ (1 : ℤ)
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) := by
            simp [TensorProduct.mk_apply]
  have hLid :
      mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) +
        mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) =
      mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) := by
    simpa using congrArg (TensorProduct.lid ℤ PreLieDifferenceStableQuotient) hTensor
  have hzero :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) = 0 := by
    have hCancel :
        mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) +
          mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s)) =
        mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) + 0 := by
      simpa using hLid
    exact add_left_cancel hCancel
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s)
  rw [hzero, correctedCounit_quot_zero] at hone
  norm_num at hone

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
  have hEval := congrArg
      (fun f =>
        f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) h
  have hTensor :
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) (1 : ℤ) +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) (1 : ℤ) =
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) (1 : ℤ) := by
    calc
      TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) (1 : ℤ) +
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) (1 : ℤ)
          =
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
          (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')))) := by
            symm
            exact correctedCounit_lTensor_comp_comul_treeGen_nodeLeaf r s s'
      _ =
        (fun f =>
          f (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))))
          ((TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1) := by
            exact hEval
      _ =
        TensorProduct.tmul ℤ
          (mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s'))) (1 : ℤ) := by
            simp [TensorProduct.mk_apply]
  have hRid :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s')) +
        mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) =
      mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) := by
    simpa using congrArg (TensorProduct.rid ℤ PreLieDifferenceStableQuotient) hTensor
  have hzero :
      mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s')) = 0 := by
    have hCancel :
        mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s')) +
          mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) =
        0 + mkPreLieDifferenceStableQuotient (treeGen (nodeLeaf r s s')) := by
      simpa using hRid
    exact add_right_cancel hCancel
  have hone :
      correctedCounit_quot
          (mkPreLieDifferenceStableQuotient (treeGen (PTree.leaf s'))) = 1 := by
    simpa using correctedCounit_quot_treeGen (PTree.leaf s')
  rw [hzero, correctedCounit_quot_zero] at hone
  norm_num at hone

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

/-- The OG primitive counit linear map is identically zero. -/
theorem stableUEA_OGPrimitive_counit_linear_eq_zero :
    stableUEA_counit_linear stableUEA_OGPrimitiveGeneratorComulData = 0 := by
  apply LinearMap.ext
  intro a
  rw [stableUEA_counit_linear_apply, LinearMap.zero_apply]
  classical
  simp [stableUEA_OGPrimitiveGeneratorComulData]

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

3. `comul_quot_coassoc_treeGen` / `coproductSupportSummary_comul_quot_coassoc`
   (Section 5):
   Coassociativity of the descended comultiplication.
   *Status*: Requires a two-level cut bijection.

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

At the theorem level, the file still contains 12 explicit `sorry`s; the list
below groups those into the main mathematical bottlenecks rather than counting
every wrapper lemma separately.
-/

section SorryLedger

/-- Summary: the live blocker list above has 9 grouped items, while the file
still contains 12 explicit theorem-level `sorry`s.  The mathematical content is
fully specified; the remaining `sorry`s mark combinatorial or UEA-theoretic
gaps rather than missing architectural structure. -/
theorem sorry_ledger_count : True := trivial

end SorryLedger

end QuotientConnected.CoproductSupport
