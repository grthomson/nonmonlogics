# Current choices (on the maths side)

- Objects: proof trees `PTree` representing derivations in a (nonmonotonic) sequent calculus.

- Forests: lists of trees interpreted as commutative multisets (via coercion to `Multiset PTree`).

- Hopf algebra carrier:
  H := ℤ[Multiset PTree]
  implemented as `AddMonoidAlgebra ℤ (Multiset PTree)`.

- Generators:
  treeGen : PTree → H
  forestMon : Forest → H
  embedding trees and forests as basis elements.

- Unit:
  oneForest := forestMon []

- Product:
  induced by multiset addition (disjoint union of forests)
  i.e. commutative concatenation of proof trees.

- Coproduct (core idea):
  deltaTree t :=
    ∑_{cut ∈ admissibleCuts(t)}
      forestMon(forestBelowCut) ⊗ treeGen(remainder)

  where each cut decomposes a proof tree into:
    - a forest of extracted subtrees
    - a residual tree with holes removed

- Implementation mechanism:
  coproductTerm t cut : Forest × PTree
  computes the pair (extracted forest, remainder tree).

- Recursion:
  remainderGo : PTree → List Address → ...
  performs cut-based traversal and decomposition.

- Counit:
  ε(forestMon f) = 1 if f = [] else 0

- Intended laws:
  - coassociativity via compatibility of nested cuts
  - counit laws via trivial/empty cut behaviour
  - algebra/coalgebra compatibility (bialgebra → Hopf via antipode later)

- Conceptual picture:
  trees = proofs,
  coproduct = all ways of extracting subproofs,
  product = juxtaposition of independent proofs.

# Lean-specific issues

## 1. Nested inductives forced away from structural induction

Because I defined:

```lean
inductive PTree : Type where
| leaf : MultiSequent → PTree
| node : RuleTag → MultiSequent → List PTree → PTree
```

the recursive occurrence sits inside `List PTree`. Lean therefore does not support straightforward structural induction of the form:

```lean
induction t
```

In practice, I had to replace this with strong induction on size:

```lean
let P : Nat → Prop := ...
have hP : ∀ n, (∀ m < n, P m) → P n := ...
have hstrong : ∀ n, P n := ...
exact hstrong t.size t rfl
```

This pattern appears repeatedly (e.g. in `remainderGo_nil`, `remainderGo_remainderGo_eq`, `remainderGo_append_self`). Conceptually simple tree recursion had to be recast as size-based induction.

---

## 2. `mapIdx` introduced a large amount of infra

Because the recursion over children is indexed I naturally used:

```lean
cs.attach.mapIdx (fun i ⟨child, hmem⟩ => ...)
```

but Lean does not treat `mapIdx` as transparent enough to simplify compositions automatically. Therefore had to to prove a LOT of helper lemmas:

- `mapIdx_congr'`
- `mapIdx_attach_eq_mapIdx`
- `mapIdx_attach_eq_mapIdx_from`
- `mapIdx_mapIdx`
- `mapIdx_mapIdx_from`

and frequently normalize expressions manually:

```lean
rw [mapIdx_attach_eq_mapIdx]
rw [mapIdx_mapIdx]
rw [mapIdx_attach_eq_mapIdx]
```

In ordinary mathematics just “iterate over children with indices”. In Lean a nontrivial amount of bookkeeping.

---

## 3. `attach` introduced persistent subtype noise

Using `cs.attach` gives elements of type:

```lean
{x // x ∈ cs}
```

so every element must be accessed via `.1`, with `.2` carrying the membership proof.

This led to expressions like:

```lean
fun i (x : {x // x ∈ cs}) => ...
```

and required repeated coercion handling. Also had to prove glue lemmas such as:

```lean
map_attach_val :
  cs.attach.map (fun x => x.1) = cs
```

The maths does not care about these subtypes but Lean does! this significantly increased verbosity.

---

## 4. Equality of trees required explicit lifting

When proving equalities of trees often ended up with equalities of child lists:

```lean
hchildren :
  List.mapIdx ... cs.attach = List.mapIdx ... cs.attach
```

Lean does not automatically lift this to equality of nodes so had to write:

```lean
congrArg (PTree.node r s) hchildren
```

or use `congr 2`.

Mathematically this step should be trivial but Lean required it be made explicit.

---

## 5. `simp` only solved part of the problem

For many proofs `simp` handled the outer structure (especially `if` in `remainderGo`) but left behind nontrivial goals involving:

- `mapIdx`
- `attach`
- lambda expressions
- index arithmetic

So typical pattern was:

1. simplify with `simp`
2. resolve the remaining structure manually using custom lemmas

This happens repeatedly in the `remainderGo` proofs.

---

## 6. Equality orientation mattered constantly

I often have a lemma in the form:

```lean
A = B
```

but need:

```lean
B = A
```

Lean will not automatically flip equalities so had to insert:

```lean
symm
```

or use `.symm` or rewrite in the correct direction.

This showed up frequently in `mapIdx` normalization and in `calc` blocks.

---

## 7. Elaborator behaviour sometimes looked like failure

At several points even trivial definitions like:

```lean
def iteratedCoproductData (t : PTree) :
  List ((Forest × Forest) × PTree) := []
```

appear to hang or leave goals open.

Not sure what is going on here -- may be nothing.

---

## 8. Tensor-product expressions were syntactically heavy

Even simple algebraic facts (e.g. counit identities) involved expressions like:

```lean
(TensorProduct.lid ℤ HopfCarrier)
((LinearMap.rTensor HopfCarrier epsilon) (deltaTree t))
```

To manage these had to introduce auxiliary lemmas (e.g. `htail_aux`) and carefully control `foldr` expansions.

Underlying algebra is simple but the encoding is verbose.

---

## 9. I had to build small “glue” lemmas for lists

Several simple facts were not available in the exact form needed, so I proved local lemmas such as:

- `nil_mem_sublists`
- `attach_mapIdx_val_eq`
- `mapIdx_attach_singleton`
- `mapIdx_attach_pair`

These are mathematically trivial but necessary for Lean to align definitions.

---

## 10. Induction hypotheses often needed generalisation

Many proofs initially failed because the induction hypothesis was too weak. I had to generalise over additional parameters before induction, for example:

```lean
induction xs generalizing n
```

or:

```lean
induction a generalizing d s u
```

This was especially important in the `mapIdx` lemmas and the `remainderGo` recursion.

---

## 11. Namespace structure became fragile

At one point I have opened:

```lean
namespace Syntax
...
namespace Syntax
namespace PTree
```

inside an already open namespace which Lean tolerates but leads to names like:

```lean
Syntax.Syntax.PTree...
```

This is not strictly a logical error but will make later refactoring and reuse more difficult.

---

## 12. “Too many variables / too many arguments”

Lean frequently complained about:

- too many variables in `rename_i`
- too many arguments in lambdas
- mismatched function arities

This typically arose in:

- deeply nested `mapIdx` expressions  
- strong induction proofs with many parameters  
- lemmas involving both indexed and non-indexed forms of functions  

E.g. in `decreasing_by` blocks or induction steps Lean would infer more variables than expected leading to errors like:

```text
too many variables at rename_i
```

or mismatches between expected and inferred function types.

These issues require careful control of:

- argument order  
- explicit type annotations  
- simplifying lambdas to match Lean’s expectations  

---

## 13. Current state of play

The main difficulty in this development has not been mathematical. The combinatorics of cuts and trees is conceptually straightforward.

The difficulty comes from expressing that combinatorics in Lean in a way that:

- tracks indices explicitly (`mapIdx`)
- handles subtypes (`attach`)
- respects strict typing of functions and lambdas
- provides sufficiently strong induction hypotheses

In summary:

> the mathematics is simple tree combinatorics but Lean requires it to be expressed as precise index-aware list transformations. Most of the effort has gone into making those transformations visible and usable to the elaborator.