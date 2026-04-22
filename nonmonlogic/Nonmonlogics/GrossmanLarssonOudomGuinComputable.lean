import Nonmonlogics.GrossmanLarssonOudomGuin

/-!
Computable layer for the Oudom-Guin / Grossman-Larson coproduct.

This file stays on raw `PTree` data and avoids quotient-level definitions.
The core idea: use the explicit list of coproduct data and compute sums
directly over that list (via `toFinset` when needed).

## Sections

1. Basic coproduct evaluation wrappers
2. Explicit coproduct on leaf trees
3. Explicit matching-leaf graftings on leaf trees
4. Explicit pre-Lie product on leaves
5. Tree grading and weight utilities
6. Canonical representative framework
7. Forest normal form utilities
8. Explicit GL comultiplication for leaf trees
9. Explicit `coproductEvalSum` for leaves
10. Stump trees (nodes with no children)
11. One-leaf-child trees
-/

namespace QuotientConnected.CoproductSupport

open Syntax PTree

/-! ## 1. Basic coproduct evaluation -/

def coproductEval (t : PTree) : List (Prod Forest PTree) :=
  (coproductSupportSummary t).supportList

@[simp] theorem coproductEval_eq_supportList (t : PTree) :
    coproductEval t = (coproductSupportSummary t).supportList := rfl

@[simp] theorem coproductEval_eq_coproductData (t : PTree) :
    coproductEval t = PTree.coproductData t := by
  simp [coproductEval]

@[simp] theorem coproductEval_eq_supportList_data (t : PTree) :
    coproductEval t = coproductSupportList t := by
  simp [coproductEval, coproductSupportList]

def coproductEvalSum
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) (f : Prod Forest PTree -> alpha) : alpha :=
  (coproductEval t).toFinset.sum f

@[simp] theorem coproductEvalSum_eq
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductEvalSum t f = (coproductEval t).toFinset.sum f := rfl

theorem coproductEvalSum_eq_supportSummary_sum
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductEvalSum t f = coproductSupportSummary_sum t f := by
  rw [coproductEvalSum_eq, coproductEval_eq_supportList, coproductSupportSummary_sum_eq_supportFinset]
  have hs : (PTree.coproductData t).toFinset = coproductSupportFinset t := by
    ext p
    simp [coproductSupportFinset]
  exact congrArg (fun s => s.sum f) hs

@[simp] theorem coproductEvalSum_one_eq_card (t : PTree) :
    coproductEvalSum t (fun _ => (1 : Nat)) =
      (coproductEval t).toFinset.card := by
  classical
  simp [coproductEvalSum]

theorem coproductEvalSum_zero
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) :
    coproductEvalSum t (fun _ => (0 : alpha)) = 0 := by
  classical
  simp [coproductEvalSum]

/-! ## 2. Explicit coproduct on leaf trees

A leaf `PTree.leaf s` has exactly two admissible cuts:
- The **empty cut** `([], leaf s)`: no subtrees removed.
- The **full cut** `([leaf s], leaf s)`: the leaf itself is pruned; by
  `remainderGo`'s leaf case the remainder is still `leaf s`.
-/

section ExplicitCoproductLeaf

/-- A leaf has exactly one address: the root. -/
theorem allAddresses_leaf (s : MultiSequent) :
    allAddresses (PTree.leaf s) = [[]] := by
  simp [allAddresses, allAddressesGo, PTree.size]

/-- The two sublists of a singleton: empty and the singleton itself. -/
theorem sublists_singleton {α : Type*} (x : α) :
    sublists [x] = [[], [x]] := by simp [sublists]

/-- The root address is always valid for any tree. -/
@[simp] theorem validAddress_leaf_root (s : MultiSequent) :
    validAddress (PTree.leaf s) [] = true :=
  validAddress_root (PTree.leaf s)

/-- The empty cut and root cut are the only admissible cuts of a leaf. -/
theorem allAdmissibleCuts_leaf (s : MultiSequent) :
    allAdmissibleCuts (PTree.leaf s) = [[], [[]]] := by
  unfold allAdmissibleCuts
  rw [allAddresses_leaf, sublists_singleton]
  simp [isAntichainBool, comparableBool, isPrefixOf, validAddress_root]

/-- Empty cut of a leaf: forest is empty, remainder is the leaf. -/
@[simp] theorem coproductTerm_leaf_empty (s : MultiSequent) :
    coproductTerm (PTree.leaf s) [] = ([], PTree.leaf s) := by
  simp [coproductTerm, remainderGo]

/-- Full cut of a leaf: pruned forest is `[leaf s]`, remainder is `leaf s`. -/
@[simp] theorem coproductTerm_leaf_root (s : MultiSequent) :
    coproductTerm (PTree.leaf s) [[]] = ([PTree.leaf s], PTree.leaf s) := by
  simp [coproductTerm, subtreeAt, remainderGo]

/-- The coproduct data of a leaf has exactly two cuts. -/
theorem coproductData_leaf (s : MultiSequent) :
    PTree.coproductData (PTree.leaf s) =
      [([], PTree.leaf s), ([PTree.leaf s], PTree.leaf s)] := by
  simp [PTree.coproductData, allAdmissibleCuts_leaf,
        coproductTerm_leaf_empty, coproductTerm_leaf_root]

/-- Every leaf has exactly 2 admissible cuts. -/
theorem coproductData_leaf_length (s : MultiSequent) :
    (PTree.coproductData (PTree.leaf s)).length = 2 := by
  simp [coproductData_leaf]

/-- The `coproductEval` list for a leaf. -/
theorem coproductEval_leaf (s : MultiSequent) :
    coproductEval (PTree.leaf s) =
      [([], PTree.leaf s), ([PTree.leaf s], PTree.leaf s)] := by
  simp [coproductEval, coproductData_leaf]

/-- The forest part of the leaf coproduct. -/
theorem coproductForestsList_leaf (s : MultiSequent) :
    coproductForestsList (PTree.leaf s) = [[], [PTree.leaf s]] := by
  simp [coproductForestsList, coproductData_leaf]

/-- The remainder part of the leaf coproduct: both cuts give `leaf s`. -/
theorem coproductRemaindersList_leaf (s : MultiSequent) :
    coproductRemaindersList (PTree.leaf s) = [PTree.leaf s, PTree.leaf s] := by
  simp [coproductRemaindersList, coproductData_leaf]

end ExplicitCoproductLeaf

/-! ## 3. Explicit matching-leaf graftings on leaves

Grafting `u` into `PTree.leaf s` either replaces the single leaf (when
`u.conclusion = s`) or produces the empty list (otherwise).
-/

section ExplicitMatchingLeafGraftingsLeaf

/-- `matchingLeafGraftings u (leaf s) = [u]` when `u.conclusion = s`. -/
theorem matchingLeafGraftings_leaf_match
    (u : PTree) (s : MultiSequent) (h : u.conclusion = s) :
    matchingLeafGraftings u (PTree.leaf s) = [u] := by
  simp [matchingLeafGraftings, allAddresses_leaf, graftMatchingLeafAt_root_of_match u s h]

/-- `matchingLeafGraftings u (leaf s) = []` when `u.conclusion ≠ s`. -/
theorem matchingLeafGraftings_leaf_mismatch
    (u : PTree) (s : MultiSequent) (h : u.conclusion ≠ s) :
    matchingLeafGraftings u (PTree.leaf s) = [] := by
  simp [matchingLeafGraftings, allAddresses_leaf, graftMatchingLeafAt_root_of_mismatch u s h]

/-- The clean if-then-else form of `matchingLeafGraftings` on a leaf. -/
theorem matchingLeafGraftings_leaf
    (u : PTree) (s : MultiSequent) :
    matchingLeafGraftings u (PTree.leaf s) =
      if u.conclusion = s then [u] else [] := by
  split_ifs with h
  · exact matchingLeafGraftings_leaf_match u s h
  · exact matchingLeafGraftings_leaf_mismatch u s h

/-- The length of `matchingLeafGraftings u (leaf s)`. -/
theorem matchingLeafGraftings_leaf_length
    (u : PTree) (s : MultiSequent) :
    (matchingLeafGraftings u (PTree.leaf s)).length =
      if u.conclusion = s then 1 else 0 := by
  simp [matchingLeafGraftings_leaf]
  split_ifs <;> simp

/-- When grafting a leaf into another leaf of the same type: self-loop. -/
theorem matchingLeafGraftings_leaf_self (s : MultiSequent) :
    matchingLeafGraftings (PTree.leaf s) (PTree.leaf s) = [PTree.leaf s] :=
  matchingLeafGraftings_leaf_match (PTree.leaf s) s rfl

/-- No self-graftings when sequents differ. -/
theorem matchingLeafGraftings_leaf_leaf_ne
    (s t : MultiSequent) (h : s ≠ t) :
    matchingLeafGraftings (PTree.leaf s) (PTree.leaf t) = [] :=
  matchingLeafGraftings_leaf_mismatch (PTree.leaf s) t (by simpa using h)

end ExplicitMatchingLeafGraftingsLeaf

/-! ## 4. Explicit pre-Lie product on leaves

`graftPreLieTree u (leaf s)` equals `treeGen u` when `u.conclusion = s`, and
`0` otherwise.  This follows directly from the `matchingLeafGraftings` results.
-/

section ExplicitPreLieLeaf

/-- `graftPreLieTree u (leaf s) = treeGen u` when `u.conclusion = s`. -/
theorem graftPreLieTree_leaf_match
    (u : PTree) (s : MultiSequent) (h : u.conclusion = s) :
    graftPreLieTree u (PTree.leaf s) = treeGen u := by
  simp [graftPreLieTree, matchingLeafGraftings_leaf_match u s h]

/-- `graftPreLieTree u (leaf s) = 0` when `u.conclusion ≠ s`. -/
theorem graftPreLieTree_leaf_mismatch
    (u : PTree) (s : MultiSequent) (h : u.conclusion ≠ s) :
    graftPreLieTree u (PTree.leaf s) = 0 := by
  simp [graftPreLieTree, matchingLeafGraftings_leaf_mismatch u s h]

/-- The clean if-then-else form of `graftPreLieTree` on a leaf target. -/
theorem graftPreLieTree_leaf
    (u : PTree) (s : MultiSequent) :
    graftPreLieTree u (PTree.leaf s) =
      if u.conclusion = s then treeGen u else 0 := by
  split_ifs with h
  · exact graftPreLieTree_leaf_match u s h
  · exact graftPreLieTree_leaf_mismatch u s h

/-- Leaf-into-leaf: `graftPreLieTree (leaf s) (leaf t) = treeGen (leaf s)` iff `s = t`. -/
theorem graftPreLieTree_leaf_leaf
    (s t : MultiSequent) :
    graftPreLieTree (PTree.leaf s) (PTree.leaf t) =
      if s = t then treeGen (PTree.leaf s) else 0 := by
  simp [graftPreLieTree_leaf, PTree.conclusion]

/-- Self-grafting a leaf gives that tree generator. -/
@[simp] theorem graftPreLieTree_leaf_self (s : MultiSequent) :
    graftPreLieTree (PTree.leaf s) (PTree.leaf s) = treeGen (PTree.leaf s) :=
  graftPreLieTree_leaf_match (PTree.leaf s) s rfl

/-- The linear pre-Lie product on leaf generators. -/
theorem graftPreLie_treeGen_leaf_leaf
    (s t : MultiSequent) :
    graftPreLie (treeGen (PTree.leaf s)) (treeGen (PTree.leaf t)) =
      if s = t then treeGen (PTree.leaf s) else 0 := by
  rw [graftPreLie_on_generators, graftPreLieTree_leaf_leaf]

/-- Self-grafting of leaf generators. -/
@[simp] theorem graftPreLie_treeGen_leaf_self (s : MultiSequent) :
    graftPreLie (treeGen (PTree.leaf s)) (treeGen (PTree.leaf s)) =
      treeGen (PTree.leaf s) := by
  simp [graftPreLie_treeGen_leaf_leaf]

end ExplicitPreLieLeaf

/-! ## 5. Tree grading and weight utilities -/

section TreeGrading

/-- The weight of a tree (alias for `PTree.size`). -/
abbrev treeWeight (t : PTree) : Nat := t.size

/-- The weight of a forest is the sum of sizes. -/
def forestWeight : Forest → Nat
  | [] => 0
  | t :: ts => t.size + forestWeight ts

@[simp] theorem forestWeight_nil : forestWeight [] = 0 := rfl

@[simp] theorem forestWeight_cons (t : PTree) (ts : Forest) :
    forestWeight (t :: ts) = t.size + forestWeight ts := rfl

@[simp] theorem forestWeight_append (xs ys : Forest) :
    forestWeight (xs ++ ys) = forestWeight xs + forestWeight ys := by
  induction xs with
  | nil => simp
  | cons t ts ih => simp [ih, Nat.add_assoc]

@[simp] theorem treeWeight_leaf (s : MultiSequent) :
    treeWeight (PTree.leaf s) = 1 := by simp [treeWeight, PTree.size]

/-- The coproduct data maps for leaf forest weights. -/
theorem coproductData_leaf_forest_weights (s : MultiSequent) :
    (PTree.coproductData (PTree.leaf s)).map (fun p => forestWeight p.1) = [0, 1] := by
  simp [coproductData_leaf, forestWeight]

/-- A tree has at least one admissible cut (the empty cut). -/
theorem coproductData_nonempty (t : PTree) :
    (PTree.coproductData t).length > 0 :=
  coproductSupportList_nonempty t

/-- The number of cuts of a leaf is 2. -/
theorem coproductData_leaf_card (s : MultiSequent) :
    (PTree.coproductData (PTree.leaf s)).length = 2 := by
  simp [coproductData_leaf]

/-- Property: a linear combination is supported only on weight-`n` trees. -/
def isWeightN (n : Nat) (a : linearProofTreeCarrier) : Prop :=
  ∀ t ∈ a.support, treeWeight t = n

theorem isWeightN_treeGen (t : PTree) :
    isWeightN (treeWeight t) (treeGen t) := by
  intro u hu
  simp [treeGen, Finsupp.support_single_ne_zero] at hu
  simp [treeWeight, ← hu]

@[simp] theorem isWeightN_zero_iff_trivial (a : linearProofTreeCarrier) :
    isWeightN 0 a ↔ ∀ t ∈ a.support, False := by
  constructor
  · intro h t ht
    have ht0 := h t ht
    cases t with
    | leaf s => simp [isWeightN, treeWeight, PTree.size] at ht0
    | node r s cs => simp [isWeightN, treeWeight, PTree.size, Nat.succ_ne_zero] at ht0
  · intro h t ht
    exact False.elim (h t ht)

end TreeGrading

/-! ## 6. Canonical representative framework

Every element of `PreLieDifferenceStableQuotient` has a lift to
`linearProofTreeCarrier`.  The **canonical representative** is one such lift
chosen consistently (e.g., via `Quotient.out`).
-/

section CanonicalRepresentative

/-- The tree coefficient: the coefficient of `treeGen t` in a linear combination. -/
def treeCoefficient (a : linearProofTreeCarrier) (t : PTree) : ℤ := a t

@[simp] theorem treeCoefficient_treeGen (t u : PTree) :
    treeCoefficient (treeGen t) u = if t = u then 1 else 0 := by
  simp [treeCoefficient, treeGen, Finsupp.single_apply]

@[simp] theorem treeCoefficient_zero (t : PTree) :
    treeCoefficient 0 t = 0 := rfl

@[simp] theorem treeCoefficient_add (a b : linearProofTreeCarrier) (t : PTree) :
    treeCoefficient (a + b) t = treeCoefficient a t + treeCoefficient b t := rfl

@[simp] theorem treeCoefficient_smul (n : ℤ) (a : linearProofTreeCarrier) (t : PTree) :
    treeCoefficient (n • a) t = n * treeCoefficient a t := by
  simp [treeCoefficient, Finsupp.smul_apply, smul_eq_mul]

/-- The support of a linear combination. -/
def linearCombinationSupport (a : linearProofTreeCarrier) : Finset PTree := a.support

@[simp] theorem mem_linearCombinationSupport (a : linearProofTreeCarrier) (t : PTree) :
    t ∈ linearCombinationSupport a ↔ treeCoefficient a t ≠ 0 := by
  simp [linearCombinationSupport, treeCoefficient, Finsupp.mem_support_iff]

/-- A linear combination is a sum of its basis components. -/
theorem linearCombination_eq_finsupp_sum (a : linearProofTreeCarrier) :
    a = a.support.sum (fun t => treeCoefficient a t • treeGen t) := by
  simp only [treeCoefficient, treeGen]
  conv_lhs => rw [← Finsupp.sum_single a]
  simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Two elements represent the same equivalence class iff their difference is in the submodule. -/
theorem eq_in_quotient_iff (a b : linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient a = mkPreLieDifferenceStableQuotient b ↔
      a - b ∈ preLieDifferenceStableSubmodule := by
  simpa [mkPreLieDifferenceStableQuotient] using
    (Submodule.Quotient.eq (p := preLieDifferenceStableSubmodule) (x := a) (y := b))

/-- A canonical representative of an equivalence class via `Quotient.out`. -/
noncomputable def canonicalRep (q : PreLieDifferenceStableQuotient) :
    linearProofTreeCarrier :=
  q.out

/-- The canonical rep maps back to its equivalence class. -/
theorem canonicalRep_class (q : PreLieDifferenceStableQuotient) :
    mkPreLieDifferenceStableQuotient (canonicalRep q) = q := by
  simp [canonicalRep, mkPreLieDifferenceStableQuotient]
  exact Quotient.out_eq q

/-- Canonical representatives of distinct classes are distinct. -/
theorem canonicalRep_injective
    (q₁ q₂ : PreLieDifferenceStableQuotient)
    (h : canonicalRep q₁ = canonicalRep q₂) :
    q₁ = q₂ := by
  have := congr_arg mkPreLieDifferenceStableQuotient h
  rwa [canonicalRep_class, canonicalRep_class] at this

/-- Two elements are equivalent iff they have the same canonical representative. -/
theorem eq_iff_canonicalRep_eq (a b : linearProofTreeCarrier) :
    mkPreLieDifferenceStableQuotient a = mkPreLieDifferenceStableQuotient b ↔
      canonicalRep (mkPreLieDifferenceStableQuotient a) =
        canonicalRep (mkPreLieDifferenceStableQuotient b) := by
  constructor
  · intro h; exact congr_arg canonicalRep h
  · intro h; exact canonicalRep_injective _ _ h

end CanonicalRepresentative

/-! ## 7. Forest normal form utilities -/

section ForestNormalForm

/-- Count trees in a forest with a given conclusion. -/
def forestConclusionCount (f : Forest) (s : MultiSequent) : Nat :=
  f.countP (fun t => decide (t.conclusion = s))

@[simp] theorem forestConclusionCount_nil (s : MultiSequent) :
    forestConclusionCount [] s = 0 := rfl

theorem forestConclusionCount_cons_match
    (t : PTree) (ts : Forest) (s : MultiSequent) (h : t.conclusion = s) :
    forestConclusionCount (t :: ts) s = 1 + forestConclusionCount ts s := by
  simpa [forestConclusionCount, List.countP_cons, h, Nat.add_comm]

theorem forestConclusionCount_cons_mismatch
    (t : PTree) (ts : Forest) (s : MultiSequent) (h : t.conclusion ≠ s) :
    forestConclusionCount (t :: ts) s = forestConclusionCount ts s := by
  simp [forestConclusionCount, List.countP_cons, h]

/-- All trees obtained by `matchingLeafGraftings u t` have conclusion `t.conclusion`. -/
theorem matchingLeafGraftings_conclusion
    (u t t' : PTree)
    (hmem : t' ∈ matchingLeafGraftings u t) :
    t'.conclusion = t.conclusion := by
  unfold matchingLeafGraftings at hmem
  rcases List.mem_filterMap.1 hmem with ⟨a, _, ha⟩
  exact graftMatchingLeafAt_preserves_conclusion u t t' a ha

/-- Tautological length witness (used for structural induction stubs). -/
theorem forestGen_length_eq
    (f g : Forest) (h : f.length = g.length) :
    ∃ (σ : f.length = g.length), σ = h := ⟨h, rfl⟩

end ForestNormalForm

/-! ## 8. Explicit GL comultiplication for leaf trees

The GL comultiplication on `treeGen (leaf s)` is `treeGen(leaf s) ⊗ treeGen(leaf s)`.
The empty cut contributes 0, and the full cut contributes the diagonal term.
-/

section ExplicitCoproductLinearLeaf

/-- The GL coproduct on a leaf generator equals the diagonal tensor. -/
theorem coproductSupportSummary_comul_linear_leaf (s : MultiSequent) :
    coproductSupportSummary_comul_linear (treeGen (PTree.leaf s)) =
      TensorProduct.tmul ℤ (treeGen (PTree.leaf s)) (treeGen (PTree.leaf s)) := by
  rw [coproductSupportSummary_comul_linear_treeGen,
      coproductSupportSummary_sum_eq_supportList,
      coproductSupportSummary_supportList, coproductData_leaf]
  simp [coproductSupportSummary_tensorGen, forestGen_cons, forestGen_nil]

end ExplicitCoproductLinearLeaf

/-! ## 9. Explicit `coproductEvalSum` for leaves -/

section LeafEvalSum

/-- On a leaf, the `coproductEvalSum` is a sum over the two explicit cuts. -/
theorem coproductEvalSum_leaf
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (s : MultiSequent) (f : Forest × PTree → alpha) :
    coproductEvalSum (PTree.leaf s) f =
      f ([], PTree.leaf s) + f ([PTree.leaf s], PTree.leaf s) := by
  classical
  simp only [coproductEvalSum, coproductEval_leaf]
  simp [List.toFinset_cons, Finset.sum_insert, List.toFinset_nil]

/-- The empty cut is always in `coproductData t`. -/
theorem empty_cut_mem_coproductData (t : PTree) :
    ([], t) ∈ PTree.coproductData t := by
  unfold PTree.coproductData
  refine List.mem_map.2 ⟨[], empty_cut_mem_allAdmissibleCuts t, ?_⟩
  simp [coproductTerm, remainderGo_nil]

/-- When all non-trivial cuts contribute zero, the sum equals `f([], t)`. -/
theorem coproductEvalSum_trivial_cut
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) (f : Forest × PTree → alpha)
    (h : ∀ p ∈ (coproductEval t).toFinset, p ≠ ([], t) → f p = 0) :
    coproductEvalSum t f = f ([], t) := by
  classical
  simp only [coproductEvalSum]
  rw [Finset.sum_eq_single ([], t)]
  · intro p hp hpne
    exact h p hp hpne
  · intro hne
    exfalso
    apply hne
    rw [List.mem_toFinset, coproductEval_eq_coproductData]
    exact empty_cut_mem_coproductData t

end LeafEvalSum

/-! ## 10. Stump trees (nodes with no children)

A **stump** is `PTree.node r s []` — a rule application with no subproofs.
Like a leaf it has exactly one address (the root), so its admissible cuts are
the empty cut and the root cut.  Unlike a leaf, the root-cut remainder is
`PTree.leaf s` rather than the stump itself.
-/

section StumpTrees

/-- A stump is a rule node with no children. -/
@[reducible] def stump (r : RuleTag) (s : MultiSequent) : PTree :=
  PTree.node r s []

@[simp] theorem stump_size (r : RuleTag) (s : MultiSequent) :
    (stump r s).size = 1 := by simp [stump, PTree.size]

@[simp] theorem stump_conclusion (r : RuleTag) (s : MultiSequent) :
    (stump r s).conclusion = s := rfl

@[simp] theorem stump_children (r : RuleTag) (s : MultiSequent) :
    (stump r s).children = [] := rfl

/-- A stump has exactly one address: the root. -/
theorem allAddresses_stump (r : RuleTag) (s : MultiSequent) :
    allAddresses (stump r s) = [[]] := by
  simp [allAddresses, allAddressesGo, stump, PTree.size]

/-- Admissible cuts of a stump: empty cut and root cut. -/
theorem allAdmissibleCuts_stump (r : RuleTag) (s : MultiSequent) :
    allAdmissibleCuts (stump r s) = [[], [[]]] := by
  unfold allAdmissibleCuts
  rw [allAddresses_stump, sublists_singleton]
  simp [validAddress_root, isAntichainBool, comparableBool, isPrefixOf,
        List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
        List.filter_cons, List.filter_nil, Bool.true_and, Bool.and_true]

@[simp] theorem coproductTerm_stump_empty (r : RuleTag) (s : MultiSequent) :
    coproductTerm (stump r s) [] = ([], stump r s) := by
  simp [coproductTerm, remainderGo, stump]

/-- Root cut of a stump: the stump is pruned; the remainder is the leaf stub. -/
@[simp] theorem coproductTerm_stump_root (r : RuleTag) (s : MultiSequent) :
    coproductTerm (stump r s) [[]] = ([stump r s], PTree.leaf s) := by
  simp [coproductTerm, subtreeAt, remainderGo, stump]

theorem coproductData_stump (r : RuleTag) (s : MultiSequent) :
    PTree.coproductData (stump r s) =
      [([], stump r s), ([stump r s], PTree.leaf s)] := by
  simp [PTree.coproductData, allAdmissibleCuts_stump,
        coproductTerm_stump_empty, coproductTerm_stump_root]

theorem coproductEval_stump (r : RuleTag) (s : MultiSequent) :
    coproductEval (stump r s) = [([], stump r s), ([stump r s], PTree.leaf s)] := by
  simp [coproductEval, coproductData_stump]

/-- GL comultiplication on a stump generator: `tg(stump r s) ⊗ tg(leaf s)`. -/
theorem coproductSupportSummary_comul_linear_stump (r : RuleTag) (s : MultiSequent) :
    coproductSupportSummary_comul_linear (treeGen (stump r s)) =
      TensorProduct.tmul ℤ (treeGen (stump r s)) (treeGen (PTree.leaf s)) := by
  rw [coproductSupportSummary_comul_linear_treeGen,
      coproductSupportSummary_sum_eq_supportList,
      coproductSupportSummary_supportList, coproductData_stump]
  simp [coproductSupportSummary_tensorGen, forestGen_cons, forestGen_nil]

/-- Stumps have no leaf nodes, so grafting into one always returns nothing. -/
theorem matchingLeafGraftings_stump (u : PTree) (r : RuleTag) (s : MultiSequent) :
    matchingLeafGraftings u (stump r s) = [] := by
  simp only [matchingLeafGraftings, allAddresses_stump, List.filterMap_cons, List.filterMap_nil]
  rw [graftMatchingLeafAt_eq_none_of_subtreeAt_node u (stump r s) [] r s []
        (by simp [stump, subtreeAt])]

/-- Grafting into a stump always gives 0. -/
theorem graftPreLieTree_stump (u : PTree) (r : RuleTag) (s : MultiSequent) :
    graftPreLieTree u (stump r s) = 0 := by
  simp [graftPreLieTree, matchingLeafGraftings_stump]

/-- The linear pre-Lie product on a stump target is always 0. -/
theorem graftPreLie_treeGen_stump (x : PTree) (r : RuleTag) (s : MultiSequent) :
    graftPreLie (treeGen x) (treeGen (stump r s)) = 0 := by
  rw [graftPreLie_on_generators, graftPreLieTree_stump]

/-- Stump eval sum: explicit sum over two cuts. -/
theorem coproductEvalSum_stump
    {alpha : Type*} [AddCommMonoid alpha] [DecidableEq (Prod Forest PTree)]
    (r : RuleTag) (s : MultiSequent) (f : Forest × PTree → alpha) :
    coproductEvalSum (stump r s) f =
      f ([], stump r s) + f ([stump r s], PTree.leaf s) := by
  classical
  simp only [coproductEvalSum, coproductEval_stump]
  simp [List.toFinset_cons, Finset.sum_insert, List.toFinset_nil]

end StumpTrees

/-! ## 11. One-leaf-child trees

The tree `PTree.node r s [PTree.leaf s']` has two addresses (`[]` and `[0]`)
and three admissible cuts: empty, root, and child-leaf.  The child-leaf cut
yields the same remainder as the empty cut (since a leaf stub is unchanged by
`remainderGo`).  The GL comultiplication therefore has two non-zero summands.
-/

section OneLChild

/-- A node whose sole child is a leaf. -/
@[reducible] def nodeLeaf (r : RuleTag) (s s' : MultiSequent) : PTree :=
  PTree.node r s [PTree.leaf s']

@[simp] theorem nodeLeaf_size (r : RuleTag) (s s' : MultiSequent) :
    (nodeLeaf r s s').size = 2 := by simp [nodeLeaf, PTree.size]

@[simp] theorem nodeLeaf_conclusion (r : RuleTag) (s s' : MultiSequent) :
    (nodeLeaf r s s').conclusion = s := rfl

/-- The two addresses of a one-leaf-child node. -/
theorem allAddresses_nodeLeaf (r : RuleTag) (s s' : MultiSequent) :
    allAddresses (nodeLeaf r s s') = [[], [0]] := by
  simp [allAddresses, allAddressesGo, nodeLeaf, PTree.size,
        List.mapIdx_cons, List.mapIdx_nil]

/-- Address `[0]` is valid in a one-leaf-child node. -/
@[simp] theorem validAddress_nodeLeaf_child (r : RuleTag) (s s' : MultiSequent) :
    validAddress (nodeLeaf r s s') [0] = true := by
  simp [validAddress, subtreeAt, nodeLeaf]

/-- The three admissible cuts of a one-leaf-child node. -/
theorem allAdmissibleCuts_nodeLeaf (r : RuleTag) (s s' : MultiSequent) :
    allAdmissibleCuts (nodeLeaf r s s') = [[], [[0]], [[]]] := by
  unfold allAdmissibleCuts
  rw [allAddresses_nodeLeaf]
  simp [sublists, validAddress_root, validAddress_nodeLeaf_child,
        isAntichainBool, comparableBool, isPrefixOf,
        List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
        List.filter_cons, List.filter_nil, Bool.true_and, Bool.and_true,
        Bool.false_and, Bool.and_false]

@[simp] theorem coproductTerm_nodeLeaf_empty (r : RuleTag) (s s' : MultiSequent) :
    coproductTerm (nodeLeaf r s s') [] = ([], nodeLeaf r s s') := by
  simp [coproductTerm, remainderGo, nodeLeaf]

/-- Child-leaf cut: prune the leaf child; the remainder retains the leaf stub. -/
@[simp] theorem coproductTerm_nodeLeaf_child (r : RuleTag) (s s' : MultiSequent) :
    coproductTerm (nodeLeaf r s s') [[0]] =
      ([PTree.leaf s'], nodeLeaf r s s') := by
  simp [coproductTerm, nodeLeaf, subtreeAt, remainderGo,
    List.mapIdx_cons, List.mapIdx_nil, List.attach, List.attachWith]

/-- Root cut: prune the entire tree; the remainder is the leaf stub. -/
@[simp] theorem coproductTerm_nodeLeaf_root (r : RuleTag) (s s' : MultiSequent) :
    coproductTerm (nodeLeaf r s s') [[]] = ([nodeLeaf r s s'], PTree.leaf s) := by
  simp [coproductTerm, subtreeAt, remainderGo, nodeLeaf]

/-- The coproduct data of a one-leaf-child node has three terms. -/
theorem coproductData_nodeLeaf (r : RuleTag) (s s' : MultiSequent) :
    PTree.coproductData (nodeLeaf r s s') =
      [([], nodeLeaf r s s'),
       ([PTree.leaf s'], nodeLeaf r s s'),
       ([nodeLeaf r s s'], PTree.leaf s)] := by
  simp [PTree.coproductData, allAdmissibleCuts_nodeLeaf,
        coproductTerm_nodeLeaf_empty, coproductTerm_nodeLeaf_child,
        coproductTerm_nodeLeaf_root]

theorem coproductEval_nodeLeaf (r : RuleTag) (s s' : MultiSequent) :
    coproductEval (nodeLeaf r s s') =
      [([], nodeLeaf r s s'),
       ([PTree.leaf s'], nodeLeaf r s s'),
       ([nodeLeaf r s s'], PTree.leaf s)] := by
  simp [coproductEval, coproductData_nodeLeaf]

/-- GL comultiplication on a one-leaf-child node generator. -/
theorem coproductSupportSummary_comul_linear_nodeLeaf (r : RuleTag) (s s' : MultiSequent) :
    coproductSupportSummary_comul_linear (treeGen (nodeLeaf r s s')) =
      TensorProduct.tmul ℤ (treeGen (PTree.leaf s')) (treeGen (nodeLeaf r s s')) +
      TensorProduct.tmul ℤ (treeGen (nodeLeaf r s s')) (treeGen (PTree.leaf s)) := by
  rw [coproductSupportSummary_comul_linear_treeGen,
      coproductSupportSummary_sum_eq_supportList,
      coproductSupportSummary_supportList, coproductData_nodeLeaf]
  simp [coproductSupportSummary_tensorGen, forestGen_cons, forestGen_nil]

/-- Grafting `u` into `nodeLeaf r s s'` replaces the leaf child with `u`. -/
theorem matchingLeafGraftings_nodeLeaf
    (u : PTree) (r : RuleTag) (s s' : MultiSequent) :
    matchingLeafGraftings u (nodeLeaf r s s') =
      if u.conclusion = s' then [PTree.node r s [u]] else [] := by
  simp only [matchingLeafGraftings, allAddresses_nodeLeaf, List.filterMap_cons, List.filterMap_nil]
  have h0 : graftMatchingLeafAt u (nodeLeaf r s s') [] = none :=
    graftMatchingLeafAt_eq_none_of_subtreeAt_node u (nodeLeaf r s s') [] r s [PTree.leaf s']
      (by simp [nodeLeaf, subtreeAt])
  rw [h0]
  by_cases h : u.conclusion = s'
  · simp [graftMatchingLeafAt, nodeLeaf, subtreeAt, h, modifyAt, PTree.replaceNth]
  · simp [graftMatchingLeafAt, nodeLeaf, subtreeAt, h]

/-- `graftPreLieTree` on a one-leaf-child node: grafting `u` gives `node r s [u]`. -/
theorem graftPreLieTree_nodeLeaf
    (u : PTree) (r : RuleTag) (s s' : MultiSequent) :
    graftPreLieTree u (nodeLeaf r s s') =
      if u.conclusion = s' then treeGen (PTree.node r s [u]) else 0 := by
  unfold graftPreLieTree
  rw [matchingLeafGraftings_nodeLeaf]
  split_ifs with h <;> simp

/-- The linearized pre-Lie product on a `nodeLeaf` target. -/
theorem graftPreLie_treeGen_nodeLeaf
    (x : PTree) (r : RuleTag) (s s' : MultiSequent) :
    graftPreLie (treeGen x) (treeGen (nodeLeaf r s s')) =
      if x.conclusion = s' then treeGen (PTree.node r s [x]) else 0 := by
  rw [graftPreLie_on_generators, graftPreLieTree_nodeLeaf]

/-- EvalSum for a one-leaf-child node over three explicit cuts. -/
theorem coproductEvalSum_nodeLeaf
    {alpha : Type*} [AddCommMonoid alpha] [DecidableEq (Prod Forest PTree)]
    (r : RuleTag) (s s' : MultiSequent) (f : Forest × PTree → alpha) :
    coproductEvalSum (nodeLeaf r s s') f =
      f ([], nodeLeaf r s s') +
      f ([PTree.leaf s'], nodeLeaf r s s') +
      f ([nodeLeaf r s s'], PTree.leaf s) := by
  classical
  simp only [coproductEvalSum, coproductEval_nodeLeaf]
  simp [List.toFinset_cons, Finset.sum_insert, List.toFinset_nil, add_assoc]

end OneLChild

/-! ## 12. Node with one stump child (`nodeStump`)

`PTree.node r s [stump r' s']` has the same address/cut structure as
`nodeLeaf r s s'`, but cutting at the child position `[0]` replaces the
stump with `leaf s'` in the remainder, yielding `nodeLeaf r s s'`.
This illustrates how pruning a non-leaf node reduces depth.
-/

section NodeStumpChild

/-- A node whose sole child is a stump. -/
@[reducible] def nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) : PTree :=
  PTree.node r s [stump r' s']

@[simp] theorem nodeStump_size
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (nodeStump r s r' s').size = 2 := by simp [nodeStump, stump, PTree.size]

@[simp] theorem nodeStump_conclusion
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    (nodeStump r s r' s').conclusion = s := rfl

/-- Same two addresses as `nodeLeaf`: root and the sole child. -/
theorem allAddresses_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    allAddresses (nodeStump r s r' s') = [[], [0]] := by
  simp [allAddresses, allAddressesGo, nodeStump, stump, PTree.size,
        List.mapIdx_cons, List.mapIdx_nil]

@[simp] theorem validAddress_nodeStump_child
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    validAddress (nodeStump r s r' s') [0] = true := by
  simp [validAddress, subtreeAt, nodeStump, stump]

/-- Same three admissible cuts as `nodeLeaf`. -/
theorem allAdmissibleCuts_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    allAdmissibleCuts (nodeStump r s r' s') = [[], [[0]], [[]]] := by
  unfold allAdmissibleCuts
  rw [allAddresses_nodeStump]
  simp [sublists, validAddress_root, validAddress_nodeStump_child,
        isAntichainBool, comparableBool, isPrefixOf,
        List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
        List.filter_cons, List.filter_nil, Bool.true_and, Bool.and_true,
        Bool.false_and, Bool.and_false]

@[simp] theorem coproductTerm_nodeStump_empty
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    coproductTerm (nodeStump r s r' s') [] = ([], nodeStump r s r' s') := by
  simp [coproductTerm, remainderGo, nodeStump]

/-- Cutting at `[0]` replaces the stump with `leaf s'`; the remainder is `nodeLeaf r s s'`. -/
@[simp] theorem coproductTerm_nodeStump_child
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    coproductTerm (nodeStump r s r' s') [[0]] =
      ([stump r' s'], nodeLeaf r s s') := by
  simp [coproductTerm, nodeStump, stump, nodeLeaf, subtreeAt, remainderGo,
    List.mapIdx_cons, List.mapIdx_nil, List.attach, List.attachWith]

@[simp] theorem coproductTerm_nodeStump_root
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    coproductTerm (nodeStump r s r' s') [[]] =
      ([nodeStump r s r' s'], PTree.leaf s) := by
  simp [coproductTerm, subtreeAt, remainderGo, nodeStump]

theorem coproductData_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    PTree.coproductData (nodeStump r s r' s') =
      [([], nodeStump r s r' s'),
       ([stump r' s'], nodeLeaf r s s'),
       ([nodeStump r s r' s'], PTree.leaf s)] := by
  simp [PTree.coproductData, allAdmissibleCuts_nodeStump,
        coproductTerm_nodeStump_empty, coproductTerm_nodeStump_child,
        coproductTerm_nodeStump_root]

theorem coproductEval_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    coproductEval (nodeStump r s r' s') =
      [([], nodeStump r s r' s'),
       ([stump r' s'], nodeLeaf r s s'),
       ([nodeStump r s r' s'], PTree.leaf s)] := by
  simp [coproductEval, coproductData_nodeStump]

/-- GL comultiplication: `tg(stump r' s') ⊗ tg(nodeLeaf r s s') + tg(nodeStump) ⊗ tg(leaf s)`. -/
theorem coproductSupportSummary_comul_linear_nodeStump
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    coproductSupportSummary_comul_linear (treeGen (nodeStump r s r' s')) =
      TensorProduct.tmul ℤ (treeGen (stump r' s')) (treeGen (nodeLeaf r s s')) +
      TensorProduct.tmul ℤ (treeGen (nodeStump r s r' s')) (treeGen (PTree.leaf s)) := by
  rw [coproductSupportSummary_comul_linear_treeGen,
      coproductSupportSummary_sum_eq_supportList,
      coproductSupportSummary_supportList, coproductData_nodeStump]
  simp [coproductSupportSummary_tensorGen, forestGen_cons, forestGen_nil]

/-- `nodeStump` has no leaf positions — grafting always returns nothing. -/
theorem matchingLeafGraftings_nodeStump
    (u : PTree) (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    matchingLeafGraftings u (nodeStump r s r' s') = [] := by
  simp only [matchingLeafGraftings, allAddresses_nodeStump,
             List.filterMap_cons, List.filterMap_nil]
  have h0 : graftMatchingLeafAt u (nodeStump r s r' s') [] = none :=
    graftMatchingLeafAt_eq_none_of_subtreeAt_node u (nodeStump r s r' s') []
      r s [stump r' s'] (by simp [nodeStump, subtreeAt])
  have h1 : graftMatchingLeafAt u (nodeStump r s r' s') [0] = none :=
    graftMatchingLeafAt_eq_none_of_subtreeAt_node u (nodeStump r s r' s') [0]
      r' s' [] (by simp [nodeStump, stump, subtreeAt])
  simp [h0, h1]

theorem graftPreLieTree_nodeStump
    (u : PTree) (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    graftPreLieTree u (nodeStump r s r' s') = 0 := by
  simp [graftPreLieTree, matchingLeafGraftings_nodeStump]

theorem graftPreLie_treeGen_nodeStump
    (x : PTree) (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent) :
    graftPreLie (treeGen x) (treeGen (nodeStump r s r' s')) = 0 := by
  rw [graftPreLie_on_generators, graftPreLieTree_nodeStump]

theorem coproductEvalSum_nodeStump
    {alpha : Type*} [AddCommMonoid alpha] [DecidableEq (Prod Forest PTree)]
    (r : RuleTag) (s : MultiSequent) (r' : RuleTag) (s' : MultiSequent)
    (f : Forest × PTree → alpha) :
    coproductEvalSum (nodeStump r s r' s') f =
      f ([], nodeStump r s r' s') +
      f ([stump r' s'], nodeLeaf r s s') +
      f ([nodeStump r s r' s'], PTree.leaf s) := by
  classical
  simp only [coproductEvalSum, coproductEval_nodeStump]
  simp [List.toFinset_cons, Finset.sum_insert, List.toFinset_nil, add_assoc]

end NodeStumpChild

/-! ## 13. Node with a `nodeLeaf` child (`nodeNodeLeaf`)

`PTree.node r s [nodeLeaf r₁ s₁ s₂]` has three addresses (`[]`, `[0]`,
`[0,0]`) and four admissible cuts.  Pruning the grandchild leaf at `[0,0]`
leaves the tree unchanged (leaf is a stub); pruning the child node at `[0]`
reduces the remainder to `nodeLeaf r s s₁`.
-/

section NodeNodeLeafChild

/-- A node whose sole child is a `nodeLeaf`. -/
@[reducible] def nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) : PTree :=
  PTree.node r s [nodeLeaf r₁ s₁ s₂]

@[simp] theorem nodeNodeLeaf_size
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (nodeNodeLeaf r s r₁ s₁ s₂).size = 3 := by simp [nodeNodeLeaf, nodeLeaf, PTree.size]

@[simp] theorem nodeNodeLeaf_conclusion
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    (nodeNodeLeaf r s r₁ s₁ s₂).conclusion = s := rfl

/-- Three addresses: root, child node, and grandchild leaf. -/
theorem allAddresses_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    allAddresses (nodeNodeLeaf r s r₁ s₁ s₂) = [[], [0], [0, 0]] := by
  simp [allAddresses, allAddressesGo, nodeNodeLeaf, nodeLeaf, PTree.size,
        List.mapIdx_cons, List.mapIdx_nil]

@[simp] theorem validAddress_nodeNodeLeaf_child
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    validAddress (nodeNodeLeaf r s r₁ s₁ s₂) [0] = true := by
  simp [validAddress, subtreeAt, nodeNodeLeaf, nodeLeaf]

@[simp] theorem validAddress_nodeNodeLeaf_grandchild
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    validAddress (nodeNodeLeaf r s r₁ s₁ s₂) [0, 0] = true := by
  simp [validAddress, subtreeAt, nodeNodeLeaf, nodeLeaf]

/-- Four admissible cuts: empty, grandchild, child, root. -/
theorem allAdmissibleCuts_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    allAdmissibleCuts (nodeNodeLeaf r s r₁ s₁ s₂) = [[], [[0, 0]], [[0]], [[]]] := by
  unfold allAdmissibleCuts
  rw [allAddresses_nodeNodeLeaf]
  simp [sublists, validAddress_root, validAddress_nodeNodeLeaf_child,
        validAddress_nodeNodeLeaf_grandchild,
        isAntichainBool, comparableBool, isPrefixOf,
        List.mapIdx_cons, List.mapIdx_nil, List.all_cons, List.all_nil,
        List.filter_cons, List.filter_nil, Bool.true_and, Bool.and_true,
        Bool.false_and, Bool.and_false]

@[simp] theorem coproductTerm_nodeNodeLeaf_empty
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductTerm (nodeNodeLeaf r s r₁ s₁ s₂) [] =
      ([], nodeNodeLeaf r s r₁ s₁ s₂) := by
  simp [coproductTerm, remainderGo, nodeNodeLeaf]

/-- Cutting the grandchild leaf at `[0,0]` leaves the tree unchanged as remainder. -/
@[simp] theorem coproductTerm_nodeNodeLeaf_grandchild
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductTerm (nodeNodeLeaf r s r₁ s₁ s₂) [[0, 0]] =
      ([PTree.leaf s₂], nodeNodeLeaf r s r₁ s₁ s₂) := by
  simp [coproductTerm, nodeNodeLeaf, nodeLeaf, subtreeAt, remainderGo,
    List.mapIdx_cons, List.mapIdx_nil, List.attach, List.attachWith]

/-- Cutting the child node at `[0]` reduces the remainder to `nodeLeaf r s s₁`. -/
@[simp] theorem coproductTerm_nodeNodeLeaf_child
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductTerm (nodeNodeLeaf r s r₁ s₁ s₂) [[0]] =
      ([nodeLeaf r₁ s₁ s₂], nodeLeaf r s s₁) := by
  simp [coproductTerm, nodeNodeLeaf, nodeLeaf, subtreeAt, remainderGo,
    List.mapIdx_cons, List.mapIdx_nil, List.attach, List.attachWith]

@[simp] theorem coproductTerm_nodeNodeLeaf_root
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductTerm (nodeNodeLeaf r s r₁ s₁ s₂) [[]] =
      ([nodeNodeLeaf r s r₁ s₁ s₂], PTree.leaf s) := by
  simp [coproductTerm, subtreeAt, remainderGo, nodeNodeLeaf, nodeLeaf]

theorem coproductData_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    PTree.coproductData (nodeNodeLeaf r s r₁ s₁ s₂) =
      [([], nodeNodeLeaf r s r₁ s₁ s₂),
       ([PTree.leaf s₂], nodeNodeLeaf r s r₁ s₁ s₂),
       ([nodeLeaf r₁ s₁ s₂], nodeLeaf r s s₁),
       ([nodeNodeLeaf r s r₁ s₁ s₂], PTree.leaf s)] := by
  simp [PTree.coproductData, allAdmissibleCuts_nodeNodeLeaf,
        coproductTerm_nodeNodeLeaf_empty, coproductTerm_nodeNodeLeaf_grandchild,
        coproductTerm_nodeNodeLeaf_child, coproductTerm_nodeNodeLeaf_root]

theorem coproductEval_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductEval (nodeNodeLeaf r s r₁ s₁ s₂) =
      [([], nodeNodeLeaf r s r₁ s₁ s₂),
       ([PTree.leaf s₂], nodeNodeLeaf r s r₁ s₁ s₂),
       ([nodeLeaf r₁ s₁ s₂], nodeLeaf r s s₁),
       ([nodeNodeLeaf r s r₁ s₁ s₂], PTree.leaf s)] := by
  simp [coproductEval, coproductData_nodeNodeLeaf]

/-- GL comultiplication on a depth-2 tree. -/
theorem coproductSupportSummary_comul_linear_nodeNodeLeaf
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    coproductSupportSummary_comul_linear (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) =
      TensorProduct.tmul ℤ (treeGen (PTree.leaf s₂)) (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) +
      TensorProduct.tmul ℤ (treeGen (nodeLeaf r₁ s₁ s₂)) (treeGen (nodeLeaf r s s₁)) +
      TensorProduct.tmul ℤ (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) (treeGen (PTree.leaf s)) := by
  rw [coproductSupportSummary_comul_linear_treeGen,
      coproductSupportSummary_sum_eq_supportList,
      coproductSupportSummary_supportList, coproductData_nodeNodeLeaf]
  simp [coproductSupportSummary_tensorGen, forestGen_cons, forestGen_nil, add_assoc]

/-- `nodeNodeLeaf` has exactly one leaf position: the grandchild at `[0,0]`. -/
theorem matchingLeafGraftings_nodeNodeLeaf
    (u : PTree) (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    matchingLeafGraftings u (nodeNodeLeaf r s r₁ s₁ s₂) =
      if u.conclusion = s₂ then [PTree.node r s [PTree.node r₁ s₁ [u]]] else [] := by
  simp only [matchingLeafGraftings, allAddresses_nodeNodeLeaf,
             List.filterMap_cons, List.filterMap_nil]
  have h0 : graftMatchingLeafAt u (nodeNodeLeaf r s r₁ s₁ s₂) [] = none :=
    graftMatchingLeafAt_eq_none_of_subtreeAt_node u (nodeNodeLeaf r s r₁ s₁ s₂) []
      r s [nodeLeaf r₁ s₁ s₂] (by simp [nodeNodeLeaf, subtreeAt])
  have h1 : graftMatchingLeafAt u (nodeNodeLeaf r s r₁ s₁ s₂) [0] = none :=
    graftMatchingLeafAt_eq_none_of_subtreeAt_node u (nodeNodeLeaf r s r₁ s₁ s₂) [0]
      r₁ s₁ [PTree.leaf s₂] (by simp [nodeNodeLeaf, nodeLeaf, subtreeAt])
  rw [h0, h1]
  by_cases h : u.conclusion = s₂
  · simp [graftMatchingLeafAt, nodeNodeLeaf, nodeLeaf, subtreeAt, h,
      modifyAt, PTree.replaceNth]
  · simp [graftMatchingLeafAt, nodeNodeLeaf, nodeLeaf, subtreeAt, h]

/-- `graftPreLieTree` on a depth-2 tree: grafts `u` at the grandchild leaf. -/
theorem graftPreLieTree_nodeNodeLeaf
    (u : PTree) (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    graftPreLieTree u (nodeNodeLeaf r s r₁ s₁ s₂) =
      if u.conclusion = s₂ then treeGen (PTree.node r s [PTree.node r₁ s₁ [u]]) else 0 := by
  unfold graftPreLieTree
  rw [matchingLeafGraftings_nodeNodeLeaf]
  split_ifs with h <;> simp

/-- The linearized pre-Lie product on a depth-2 target. -/
theorem graftPreLie_treeGen_nodeNodeLeaf
    (x : PTree) (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent) :
    graftPreLie (treeGen x) (treeGen (nodeNodeLeaf r s r₁ s₁ s₂)) =
      if x.conclusion = s₂ then treeGen (PTree.node r s [PTree.node r₁ s₁ [x]]) else 0 := by
  rw [graftPreLie_on_generators, graftPreLieTree_nodeNodeLeaf]

theorem coproductEvalSum_nodeNodeLeaf
    {alpha : Type*} [AddCommMonoid alpha] [DecidableEq (Prod Forest PTree)]
    (r : RuleTag) (s : MultiSequent) (r₁ : RuleTag) (s₁ s₂ : MultiSequent)
    (f : Forest × PTree → alpha) :
    coproductEvalSum (nodeNodeLeaf r s r₁ s₁ s₂) f =
      f ([], nodeNodeLeaf r s r₁ s₁ s₂) +
      f ([PTree.leaf s₂], nodeNodeLeaf r s r₁ s₁ s₂) +
      f ([nodeLeaf r₁ s₁ s₂], nodeLeaf r s s₁) +
      f ([nodeNodeLeaf r s r₁ s₁ s₂], PTree.leaf s) := by
  classical
  simp only [coproductEvalSum, coproductEval_nodeNodeLeaf]
  simp [List.toFinset_cons, Finset.sum_insert, List.toFinset_nil, add_assoc]

end NodeNodeLeafChild

end QuotientConnected.CoproductSupport
