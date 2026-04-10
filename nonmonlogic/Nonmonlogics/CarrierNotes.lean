

/-!
## Bundled recovery forms
-/

theorem canonicalRightNeighborOfLeftNeighbor_recovers_target_bundled
    (x y z w : PTree)
    (t : RightContributionClasses x y z w)
    (s : leftContributionNeighborClasses x y z w t) :
    (canonicalRightNeighborOfLeftNeighbor x y z w t s).1 = t := by
  cases t
  cases canonicalRightNeighborOfLeftNeighbor x y z w t s
  simp at *
  aesop

theorem canonicalLeftNeighborOfRightNeighbor_recovers_target_bundled
    (x y z w : PTree)
    (s : LeftContributionClasses x y z w)
    (t : rightContributionNeighborClasses x y z w s) :
    (canonicalLeftNeighborOfRightNeighbor x y z w s t).1 = s := by
  cases s
  cases canonicalLeftNeighborOfRightNeighbor x y z w s t
  simp at *
  aesop




/-- Placeholder: local counting theorem.
Likely target: the neighbour sets on the two sides are equinumerous, or both
are controlled by the same witness/support data.
-/
theorem swappedNeighbors_cardinal_balance
    (x y z w : PTree)
    (qL : TwoStepQuotient x y z w)
    (qR : TwoStepQuotient y x z w) :
    True := by
  /-
  Replace `True` with the correct statement once you decide whether the right
  theorem is:
  - equality of cardinalities,
  - existence of a surjection each way,
  - or equivalence with previously-defined witness-support fibres.
  -/
  trivial




/--
Inner reassociation is already canonical up to swapping `x` and `y`.

This is the quotient-level inner contribution to pre-Lie symmetry:
the nested case on the left with parameters `(x,y,z,w)` is literally the
nested case on the right with parameters `(y,x,z,w)`.
-/
theorem inner_symmetry_on_classes
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    classOfLeftInner a b y' hay hbw =
      classOfRightInner (x := x) (y := y) a b y' hay hbw := by
  rfl





/--
Inner reassociation is already canonical up to swapping `x` and `y`.

This is the quotient-level inner contribution to pre-Lie symmetry:
the nested case on the left with parameters `(x,y,z,w)` is literally the
nested case on the right with parameters `(y,x,z,w)`.
-/
theorem inner_symmetry_on_classes
    (x y z w : PTree)
    (a b : Address) (y' : PTree)
    (hay : (a, y') ∈ matchingLeafGraftWitnesses y x)
    (hbw : (b, w) ∈ matchingLeafGraftWitnesses y' z) :
    classOfLeftInner a b y' hay hbw =
      classOfRightInner (x := x) (y := y) a b y' hay hbw := by
  rfl

/-!
## Canonicalisation maps

These maps send raw two-step witness codes to the more invariant
canonical two-step data. The intended meaning is that a raw derivation
history presents a canonical proof-composition pattern.
-/




/--
Canonicalisation of a raw left witness.

A witness for the left-bracketed two-step grafting
`x ▷ (y ▷ z)` determines canonical two-step data for the associator.
-/
def canonOfLeftWitness
    {x y z w : PTree} :
    TwoStepWitnessLeft x y z w → TwoStepCanonical x y z w
  | TwoStepWitnessLeft.outer a b z' haz hbw =>
      TwoStepCanonical.outer z'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)
  | TwoStepWitnessLeft.inner a b y' hay hbw =>
      TwoStepCanonical.inner y'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)

/--
Canonicalisation of a raw right witness.

A witness for the right-bracketed two-step grafting
`y ▷ (x ▷ z)` determines canonical two-step data for the associator,
with `x` and `y` swapped. This reflects symmetry of the associator,
not commutativity of grafting.
-/
def canonOfRightWitness
    {x y z w : PTree} :
    TwoStepWitnessRight x y z w → TwoStepCanonical y x z w
  | TwoStepWitnessRight.outer a b z' haz hbw =>
      TwoStepCanonical.outer z'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, z'), haz, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)
  | TwoStepWitnessRight.inner a b y' hay hbw =>
      TwoStepCanonical.inner y'
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(a, y'), hay, rfl⟩)
        (by
          rw [← map_snd_matchingLeafGraftWitnesses]
          exact List.mem_map.2 ⟨(b, w), hbw, rfl⟩)

/-!
## Completeness back to witnesses

Canonical two-step data should also be realisable by raw witnesses.
These are the converse directions to the canonicalisation maps.
-/

/--
Canonical two-step data gives rise to a raw left witness presentation.
-/
theorem canonical_gives_left_witness
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical x y z w) →
    Nonempty (TwoStepWitnessLeft x y z w) := by
  intro h
  rcases h with ⟨hcanon⟩
  cases hcanon with
  | outer z₃ hxz hyw =>
      rw [twoStepWitnessLeft_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨z₃, hxz, hyw⟩
  | inner y' hxy hyw =>
      rw [twoStepWitnessLeft_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨y', hxy, hyw⟩

/--
Canonical two-step data gives rise to a raw right witness presentation,
with `x` and `y` swapped as appropriate for associator symmetry.
-/
theorem canonical_gives_right_witness
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical y x z w) →
    Nonempty (TwoStepWitnessRight x y z w) := by
  intro h
  rcases h with ⟨hcanon⟩
  cases hcanon with
  | outer z' hyz hxw =>
      rw [twoStepWitnessRight_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨z', hyz, hxw⟩
  | inner y' hyx hyw =>
      rw [twoStepWitnessRight_iff]
      simp [List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨y', hyx, hyw⟩

/-!
## Support characterisation

These theorems express that raw witness support and canonical support
present the same underlying two-step proof-composition data.
-/

/--
A left raw witness exists iff canonical two-step data exists.
-/
theorem left_witness_iff_canonical
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessLeft x y z w) ↔
    Nonempty (TwoStepCanonical x y z w) := by
  constructor
  · intro h
    exact ⟨canonOfLeftWitness h.some⟩
  · intro h
    exact canonical_gives_left_witness x y z w h

/--
A right raw witness exists iff canonical two-step data exists,
with the canonical side written in the associator-symmetric order.
-/
theorem right_witness_iff_canonical
    (x y z w : PTree) :
    Nonempty (TwoStepWitnessRight x y z w) ↔
    Nonempty (TwoStepCanonical y x z w) := by
  constructor
  · intro h
    exact ⟨canonOfRightWitness h.some⟩
  · intro h
    exact canonical_gives_right_witness x y z w h

/-!
## Symmetry at the canonical level

This is the first real pre-Lie-style target: once bureaucratic witness
history is forgotten, the associator should become symmetric in `x` and `y`.
-/

/--
Canonical symmetry of two-step proof-composition data.

This is the intended first “pre-Lie modulo proof identity” theorem:
the associator should be symmetric once raw address bookkeeping has been
collapsed to canonical two-step data.
-/
theorem canonical_symm
    (x y z w : PTree) :
    Nonempty (TwoStepCanonical x y z w) ↔
    Nonempty (TwoStepCanonical y x z w) := by
  sorry

/-!
## 2. Bureaucratic equivalences
-/

/-! Placeholder: equivalence generated by commuting independent grafts
and identifying inner reassociation presentations. -/
-- inductive TwoStepWitnessEq : ... → ... → Prop
-- | ...

/-!
## 3. Left/right comparison
-/

/-! Placeholder: canonical left witnesses. -/
-- def canonicalLeftWitnesses ... := ...

/-! Placeholder: canonical right witnesses. -/
-- def canonicalRightWitnesses ... := ...

/-! Main target: left and right canonical witnesses agree. -/
-- theorem canonical_two_step_balance ... := by
--   ...

/-!
## 4. Corrected pre-Lie product
-/

/-- Placeholder: pre-Lie product built from canonical witness classes
rather than raw address multiplicities. -/
-- noncomputable def graftPreLieCanonical ... := ...

/-!
## 5. Toward the symmetric algebra / Hopf algebra
-/

-- Placeholder theorems here.
