just some wip notes and code for nonmonotonic logics

Hopf Algebra of Proof Trees (Nonmonotonic Sequent Calculus)
Overview

We aim to construct an algebraic structure on proof trees arising from a nonmonotonic sequent calculus where derivations are constrained by a base consequence relation encoding primitive entailments and incompatibilities.

Our guiding idea is that the algebraic structure should reflect genuine proof-theoretic behaviour. Proof objects are not freely composable: admissibility, incompatibility and the directed structure of inference all play a role in determining which operations are meaningful.

```
                          ┌─────────────────────────────────┐
                          │  Nonmonotonic Sequent Calculus  │
                          │  + base consequence relation    │
                          │  + incompatibility detector     │
                          └─────────────────────────────────┘
                                          │
                                          ▼
                          ┌─────────────────────────────────┐
                          │  Proof objects: PTree           │
                          │  - rooted, n-ary trees          │
                          │  - nodes = (rule, sequent)      │
                          │  - leaves = sequents            │
                          └─────────────────────────────────┘
                                          │
                                          ▼
                          ┌─────────────────────────────────┐
                          │  Goal: Hopf algebra of proofs   │
                          └─────────────────────────────────┘
                                          │
        ┌─────────────────────────────────┼──────────────────────────────┐
        │                                 │                              │
        ▼                                 ▼                              ▼

┌──────────────────────┐     ┌──────────────────────────┐     ┌──────────────────────────┐
│  Loday–Ronco         │     │  Connes–Kreimer          │     │  Grossman–Larson         │
│  (binary trees)      │     │  (cut decomposition)     │     │  (insertion algebra)     │
└──────────────────────┘     └──────────────────────────┘     └──────────────────────────┘
        │                                 │                                 │
        ▼                                 ▼                                 ▼
   ❌ Abandoned                  🟢 Coproduct works              🟡 Natural product
   - forces binary              - admissible cuts                - grafting/insertion
   - unnatural for proofs       - forest ⊗ remainder            - matches proof comp
                                                                            │
                                                                    ┌───────┼
                                                                    |         
                                                                    ▼
                                                ┌──────────────────────────────┐
                                                │  Pre-Lie / OG construction   │
                                                │  product = sum over grafts   │
                                                └──────────────────────────────┘
                                                                 │
                                                                 ▼
                                                ┌──────────────────────────────┐
                                                │  Problem: counting failure   │
                                                │  - addresses overcount       │
                                                │  - order/bureaucracy         │
                                                └──────────────────────────────┘
                                                                 │
                        ┌────────────────────────────────────────┼────────────────────────────────────────┐
                        │                                        │                                        │
                        ▼                                        ▼                                        ▼
        ┌──────────────────────────────┐        ┌──────────────────────────────┐        ┌────────────────────────────┐
        │  Quotient / Normalisation    │        │  Witness-level bijection     |        | Coproduct-first approach   │
        │  (proof identity)            │        │  (address pairing)           │        │  (coalgebra → algebra)     │
        │    (Lambek, Dosen)           │        │                              │        │                            │
        │  - remove order effects      │        │  - explicit (a,b) ↔ (a',b')  │        │  - prove coassociativity   │
        │  - keep rule structure       │        │  - test invertibility        │        │  - define product later    │
        │                              │        │                              │        │                            │
        │      MOST PROMISING          │        │     TESTABLE NOW             │        | BACKUP STRATEGY            │
        └──────────────────────────────┘        └──────────────────────────────┘        └────────────────────────────┘
```

```
                     Our intended construction proceeds as follows:

                             proof trees / witness classes
                                        ↓
                                   (quotienting)
                                        ↓
                                   pre-Lie algebra V
                                        ↓
                                   symmetric algebra S(V)
                                        ↓
                                Oudom–Guin Hopf algebra
```

We begin with proof trees together with witness data describing admissible graftings. 
After quotienting to remove irrelevant combinatorial artefacts such as ordering or duplication of witnesses, 
we aim to obtain a well-defined pre-Lie algebra V. The symmetric algebra S(V) then carries a Hopf algebra structure via the Oudom–Guin theorem.

The coproduct in the final Hopf algebra is the standard cocommutative coproduct on S(V) rather than a novel coproduct derived from proof decomposition.

Conceptual Background

Our objects are proof trees:
```

                                         Γ ⊢ Δ
                                        /     \
                                  Γ₁ ⊢ Δ₁     Γ₂ ⊢ Δ₂
                                          ...
                                          ...
                                          ...
```
These are vertically structured objects encoding derivations. 
Unlike generic combinatorial trees, they are constrained by admissibility conditions coming from the 
underlying nonmonotonic logic. In particular, weakening is not freely available and incompatibilities may block extensions of a derivation.

This makes it natural to focus on two kinds of structure: composition of proofs by insertion of one derivation into another, and decomposition of proofs by splitting a derivation into subderivations.

Why We Do Not Use the Connes–Kreimer Product

In the Connes–Kreimer Hopf algebra the product is given by forming forests, that is by placing trees side by side:

```
T₁ · T₂ = [ T₁   T₂ ]
```

This operation is associative and combinatorially natural, but it does not correspond to proof composition. Two derivations written side by side do not form a new derivation.

From a proof-theoretic perspective this product is therefore not appropriate. What we want instead is a notion of composition in which one proof is inserted into another at a suitable point.

```Connes–Kreimer:
    trees side by side
    = forest product
    = juxtaposition
```
```
Current approach:
    one proof inserted into another
    = composition / grapfting of trees
    = directed proof extension
```

Composition via Grafting

The fundamental operation we consider is grafting or insertion of one proof tree into another:

```
Before:             Insert:              After:

    y                  x                  y[x]
   / \                 |                 /   \
  ...                 ...              ...
                                       ...
                                       ...
```

This operation is directed, position-sensitive, and constrained by admissibility. 
One proof is inserted into another at a specific address or leaf, and only certain insertions are allowed.

At the level of individual grafts with fixed addresses, this behaves like a partial composition operation. When we sum over all admissible grafting sites we expect to obtain a pre-Lie structure after suitable quotienting to remove witness-level artefacts.
That is the route we now regard as primary.

Decomposition of Proofs

Independently of composition there is a natural notion of decomposing a proof into subderivations together with their surrounding context. This is reminiscent of the Connes–Kreimer coproduct:
```
        T
       / \
      A   B
Δ(T) ≈  A ⊗ (T with A removed) + B ⊗ (T with B removed) + ...
```

This kind of structure captures extraction of subproofs, the remainder of a derivation after removal and the internal organisation of a proof.

We regard this as proof-theoretically meaningful in its own right but it is not the coproduct of the final Hopf algebra obtained via Oudom–Guin.

Split in the Project

The project now separates cleanly into two interacting strands.

Route A: (current main route)
```
                                          
                                          quotient-corrected grafting
                                                  ↓
                                             pre-Lie algebra
                                                  ↓
                                             symmetric algebra S(V)
                                                  ↓
                                          Oudom–Guin Hopf algebra
```
Here the essential work is on the product side. We correct the grafting operation by quotienting witness data appropriately, prove the pre-Lie identity and then use Oudom–Guin to obtain the Hopf algebra.

This is the insertion-first route. It is closer in spirit to Grossman–Larson and other pre-Lie-based constructions than to Connes–Kreimer.

Route B: (earlier decomposition-first route)
```

                                                grafting product
                                                        +
                                               cut-based coproduct
                                                        ↓
                                        try to force bialgebra compatibility
```
This route was more fragile. It required us to make a witness-sensitive grafting operation compatible with a hand-built coproduct, and the bookkeeping became delicate very quickly.

Route C: (still viable)

We do not throw away the cut-based coproduct. Instead we keep it as a potentially valuable secondary structure:
```
                                                   proof trees
                                                       ↓
                                         decomposition into subderivations
                                                       ↓
                                     comparison with the Oudom–Guin Hopf algebra
```
So the decomposition side may still matter later, either as a comparison object or as part of a second construction more aligned with semantics of proofs.

From the current state of development our next steps are as follows.

First finish packaging the quotient structure on witnesses, ensuring that two-step graftings are represented canonically and that permutation or counting artefacts are eliminated.

Second, we prove that the associator
```
(x▹y)▹z−x▹(y▹z)
```
is symmetric in x and y at the quotient level.

Third we define the pre-Lie carrier V consisting of proof objects modulo the chosen equivalence.

Fourth, we prove the pre-Lie identity on V.

Fifth we construct the symmetric algebra S(V).

Finally we apply the Oudom–Guin construction and Bob's yer uncle, a Hopf algebra.

In compressed form the roadmap is:
```
proof trees / witnesses
        ↓
   quotient layer
        ↓
   pre-Lie identity
        ↓
   pre-Lie algebra V
        ↓
   symmetric algebra S(V)
        ↓
Oudom–Guin Hopf algebra
```