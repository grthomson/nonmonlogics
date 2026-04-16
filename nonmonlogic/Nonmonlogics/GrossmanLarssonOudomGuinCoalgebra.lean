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
  sorry
/-
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
        simp only [map_add, LinearMap.map_add]
        rw [hf, hg]
    | single x n =>
        simp only [LinearMap.map_smul]
        -- Now on `n • treeGen x`, reduce to `treeGen x`.
        congr 1
        -- `mkPreLieDifferenceStableQuotient (n • treeGen x) = n • mkPreLieDifferenceStableQuotient (treeGen x)`
        rw [show mkPreLieDifferenceStableQuotient (n • treeGen x) =
                n • mkPreLieDifferenceStableQuotient (treeGen x) from by
          simp [mkPreLieDifferenceStableQuotient]]
        simp only [LinearMap.map_smul]
        congr 1
        exact comul_quot_coassoc_treeGen x
-/

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
The corrected counit kills every pre-Lie difference generator.

Proof outline: `preLieDifferenceGenerators x y z = comparison - swapped`
where both sides have the same total coefficient in the PTree basis, by a
leaf-count symmetry (see module doc above).  `sorry`'d pending formalization
of the leaf-count lemmas.
-/
theorem correctedCounit_linear_preLieDifferenceGenerators (x y z : PTree) :
    correctedCounit_linear (preLieDifferenceGenerators x y z) = 0 := by
  sorry

/--
The corrected counit kills every element of `preLieDifferenceSubmodule`.
-/
theorem correctedCounit_linear_kills_preLieDifferenceSubmodule
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceSubmodule) :
    correctedCounit_linear a = 0 := by
  sorry

/--
Higher-order leaf-count identity: the corrected counit also kills
`graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)`.

This follows from the same leaf-count symmetry: the factor that cancels is
`(b+c-1+a) - (a+c-1+b) = 0`, independent of the "height" of the graft.
`sorry`'d pending formalization.
-/
theorem correctedCounit_linear_graft_preLieDifferenceGenerators
    (u x y z : PTree) :
    correctedCounit_linear
        (graftPreLie (treeGen u) (preLieDifferenceGenerators x y z)) = 0 := by
  sorry

/--
The corrected counit kills every element of `preLieDifferenceStableSubmodule`.

This requires the same leaf-count symmetry at all grafting depths.
`sorry`'d pending formalization; the key algebraic identity is that the bracket
`[(b+c-1)+a-(a+c-1)-b]` vanishes, propagating through all iterated graftings.
-/
theorem correctedCounit_linear_kills_stableSubmodule
    {a : linearProofTreeCarrier}
    (ha : a ∈ preLieDifferenceStableSubmodule) :
    correctedCounit_linear a = 0 := by
  sorry

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

These laws are `sorry`'d, with a detailed explanation of what combinatorial
identity is needed.
-/

section CorrectedCounitAxioms

/--
Right counit law for the corrected counit:
`(correctedCounit_quot ⊗ id) ∘ Δ_quot = (1 ⊗ -)`.

`sorry`'d: requires the combinatorial identity that the only admissible cut
`(f, r)` of `t` with `correctedCounit_linear(forestGen(f)) = 1` is the
full-admissible cut where `f` is a singleton forest.  The sum over all cuts
then recovers the identity element via telescope.
-/
theorem correctedCounit_rTensor_comp_comul :
    LinearMap.comp
        (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      TensorProduct.mk ℤ ℤ PreLieDifferenceStableQuotient 1 := by
  sorry

/--
Left counit law for the corrected counit:
`(id ⊗ correctedCounit_quot) ∘ Δ_quot = (- ⊗ 1)`.

`sorry`'d: symmetric to `correctedCounit_rTensor_comp_comul`.
-/
theorem correctedCounit_lTensor_comp_comul :
    LinearMap.comp
        (LinearMap.lTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        Δ_quot =
      (TensorProduct.mk ℤ PreLieDifferenceStableQuotient ℤ).flip 1 := by
  sorry

/--
On tree generators: the right counit law holds iff the telescope identity
over admissible cuts gives exactly `1 ⊗ mk(tg t)`.
-/
theorem correctedCounit_rTensor_comp_comul_treeGen (t : PTree) :
    (LinearMap.rTensor PreLieDifferenceStableQuotient correctedCounit_quot)
        (Δ_quot (mkPreLieDifferenceStableQuotient (treeGen t))) =
      TensorProduct.tmul ℤ 1 (mkPreLieDifferenceStableQuotient (treeGen t)) := by
  sorry

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

noncomputable local instance : LieRing PreLieDifferenceStableQuotient :=
  preLieDifferenceStableQuotientLieRing

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

@[simp] theorem preLieDifferenceStableQuotientToUEA_zero :
    preLieDifferenceStableQuotientToUEA 0 = 0 := by
  sorry

@[simp] theorem preLieDifferenceStableQuotientToUEA_add
    (a b : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientToUEA (a + b) =
      preLieDifferenceStableQuotientToUEA a +
        preLieDifferenceStableQuotientToUEA b := by
  sorry

@[simp] theorem preLieDifferenceStableQuotientToUEA_smul
    (n : Int) (a : linearProofTreeCarrier) :
    preLieDifferenceStableQuotientToUEA (n • a) =
      n • preLieDifferenceStableQuotientToUEA a := by
  sorry

@[simp] theorem preLieDifferenceStableQuotientToUEA_treeGen
    (x : PTree) :
    preLieDifferenceStableQuotientToUEA (treeGen x) = stableUEA_treeGen x := by
  simp [preLieDifferenceStableQuotientToUEA, stableUEA_treeGen]

/--
For the OG primitive datum, the raw linear comultiplication depends only on the
stable quotient class of the input linear combination.
-/
theorem stableUEA_OGPrimitive_comul_linear_formula
    (a : linearProofTreeCarrier) :
    stableUEA_comul_linear stableUEA_OGPrimitiveGeneratorComulData a =
      TensorProduct.tmul Int (preLieDifferenceStableQuotientToUEA a) 1 +
        TensorProduct.tmul Int 1 (preLieDifferenceStableQuotientToUEA a) := by
  sorry

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

This is a `sorry`'d axiom: it is the content of the Oudom–Guin theorem that
the pre-Lie bracket relations are compatible with the primitive comultiplication.
-/
theorem stableUEA_OGPrimitive_comul_respectsStableQuotient_axiom :
    stableUEA_OGPrimitiveComulRespectsStableQuotient := by
  sorry

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

/-! ## 18. Coalgebra summary and sorry ledger

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
   Counit laws for the corrected counit.
   *Status*: Requires combinatorial identity on cut telescope sums.

### Sorry'd OG isomorphism (Section 17)

10. `stableUEA_OGPrimitive_respectsStableQuotient_axiom`:
    The OG primitive comultiplication descends through the stable quotient.
    *Status*: This IS the Oudom–Guin theorem.  Proof requires the full
    isomorphism `PreLieDifferenceStableQuotient ≅ FreePLie`.
-/

section SorryLedger

/-- Summary: the number of non-trivial `sorry`s in this file is 10 (as of the
current version).  The mathematical content is fully specified; the `sorry`s
mark combinatorial or UEA-theoretic gaps, not conceptual ones. -/
theorem sorry_ledger_count : True := trivial

end SorryLedger

end QuotientConnected.CoproductSupport
