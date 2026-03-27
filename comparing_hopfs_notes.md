# On Loday–Ronco vs GL/CK for Proof Trees

I do **not** think you should regret moving away from the initial Loday–Ronco idea.

Reading that excerpt, my view is:

> **CK fits the “cut/extract/remainder” side of your project best.**  
> **GL fits the “directed proof insertion/grafting” side best.**  
> **Loday–Ronco fits only if you force the trees into a binary-workspace model.**

For your actual proof trees, **GL/CK is a better fit than Loday–Ronco**.

---

## Why the Chomsky/Berwick/Marcolli Setup is Different

That excerpt is built around a very particular linguistic architecture:

- binary rooted trees  
- workspaces as forests  
- accessible terms  
- admissible cuts  
- quotients  
- a *Merge* operation expressed via:
  - coproduct  
  - grafting  
  - reassembly  

This is elegant, but it is tailored to:

- binary merge syntax  
- workspace dynamics  
- extraction/reinsertion of subtrees  

Your proof trees are not naturally like that in two key ways.

---

## 1. Your Trees Are Not Intrinsically Binary

Your `PTree` allows arbitrary child lists:

```lean
| leaf : MultiSequent → PTree
| node : RuleTag → MultiSequent → List PTree → PTree
```

- In practice, rules are often unary or binary  
- But the **datatype itself is not planar-binary** (in the Loday–Ronco sense)

More importantly:

- The **binary shape is not the main invariant**
- The **rule-labelled derivational interface is**

So forcing everything into binary trees would be artificial unless you had a strong proof-theoretic reason.

---

## 2. Your Primary Operation Is Not “Merge”

Their *Merge* does:

- find two accessible terms  
- delete them  
- attach them under a new root  
- reassemble the workspace  

Your operation is different:

> **Find a matching leaf and replace it with a derivation tree with the same conclusion.**

This is much closer to:

- substitution  
- cut-like insertion  
- directed grafting  

rather than symmetric binary merge.

So the **asymmetry** of your project points away from Loday–Ronco and toward GL.

---

## Where Each Hopf Algebra Family Fits

### Loday–Ronco

Best when:

- binary trees are fundamental  
- associativity / parenthesisation matter  
- merge-like composition is central  

➡️ Fits the Berwick/Marcolli *workspace* picture  
➡️ Less aligned with your proof-theoretic setting  

---

### Connes–Kreimer (CK)

Best when:

- decomposition via admissible cuts is central  
- extracted subforests + remainder drive the coalgebra  
- quotient/remainder structure matters  

➡️ Matches:
- `remainderGo`  
- `coproductTerm`  
- admissible cuts  
- subderivation structure  

**Conclusion:** CK fits one half of your project *very naturally*.

---

### Grossman–Larson / Oudom–Guin (GL)

Best when:

- insertion/grafting is primitive  
- a pre-Lie structure is present  
- Hopf algebra arises from symmetric algebra over trees  

➡️ Matches your theorem:

```
graftMatchingLeafAt_toTree_is_toTree
```

**Conclusion:** GL fits the *other half* of your project *very naturally*.

---

## Recommendation

The right picture is:

> Your proof trees are best modeled by a **GL primitive product**, together with either:
>
> - the standard symmetric/Oudom–Guin coproduct, or  
> - a CK-style proof-theoretic coproduct  

I would **not** go back to Loday–Ronco unless you decide that:

- binary branching is essential  
- workspaces + merge are the true core  
- proof insertion was a red herring  

From your description, that does **not** seem to be your project.

---

## The Strongest Reason *Against* Loday–Ronco

Your key operation is:

> A derivation whose conclusion matches a leaf may be inserted at that leaf.

This is not naturally Loday–Ronco.

It *is* naturally:

- GL grafting  
- pre-Lie insertion  
- substitution-like proof composition  

That is the decisive point.

---

## What the Excerpt *Does* Validate

It supports your earlier instinct that:

> **cuts, extraction, and remainders are essential.**

Their framework:

- extracts accessible terms  
- quotients by them  
- reassembles  

This closely mirrors your **CK-style cut/remainder machinery**.

So your earlier CK work was **not a mistake** — it captures a genuinely important decomposition story.

---

## Final Verdict

- ❌ Not Loday–Ronco as the main framework  
- ✅ GL as the main product-side framework  
- ✅ CK retained as decomposition-side structure  

---

## One-Sentence Summary

> Your proof trees are not binary syntactic workspaces; they are typed derivation trees with a directed insertion operation.  
> Therefore, **GL is the right primary structure**, while **CK captures admissible-cut decomposition**.

---

## Clean Conceptual Split

A very natural architecture emerges:

- **Primitive algebraic structure:**  
  GL / pre-Lie grafting on proof trees  

- **Auxiliary decomposition theory:**  
  CK-style admissible cuts and remainders  

- **Hopf lift:**  
  Oudom–Guin symmetric algebra on the pre-Lie space  

---

This is a much more natural fit for your objects than returning to Loday–Ronco.