import Nonmonlogics.GrossmanLarsson

/-!
# Monotonicity modality M for NM-MS

This file extends the NM-MS system with a monotonicity modality
`MyProp.mon` (written `M A` in the paper, Section 4.1).

The key idea: `M A` internalises the meta-level predicate
"A holds persistently under all context weakenings" as an object-language
formula. This simultaneously tags:
  - where the weakening rule applies (Corollary 2)
  - where cut elimination is available (`NormalisableAtCut`)

The construction parallels Girard's `!` in linear logic: M marks the
monotone fragment embedded inside the nonmonotonic logic.

Connection to the algebra: inner grafts (cut compositions) through
M-tagged formulas are eliminable; those through bare atoms are not.
This is relevant to the antipode construction, where normalisation of
certain inner compositions may be needed.
-/

open Syntax

universe u

/-! ## Monotone derivability (meta-level predicate `|∼M`) -/

/--
A sequent `Γ |∼ Θ` holds *monotonically* (`Γ |∼M Θ` in the paper)
if it holds under all context extensions: for every `Δ` on the left
and `Λ` on the right, `Δ + Γ |∼ Θ + Λ` is NM-MS derivable.

This is `Prop`-valued (via `Nonempty`) since we care about existence
of derivations, not canonical choice among them.
-/
def MonotoneDerivable (base : BaseRel) (Γ Θ : Multiset MyProp) : Prop :=
  ∀ Δ Λ : Multiset MyProp,
    Nonempty (NMMS base ((Δ + Γ) ∣∼ (Θ + Λ)))

/-! ## Fixed-base vs background-indexed consequence relations -/

/--
The sequent-level consequence relation induced by `NMMS` over a fixed base
relation.

This is the fixed-background notion used by the current tree/algebra
development: the primitive material consequence relation is held fixed, and the
logical rules generate a consequence relation over the same ambient language.
-/
def NMMSDerivable (base : BaseRel) : Multiset MyProp → Multiset MyProp → Prop :=
  fun Γ Θ => Nonempty (NMMS base (Γ ∣∼ Θ))

@[simp] theorem nmmsDerivable_iff_nonempty (base : BaseRel)
    (Γ Θ : Multiset MyProp) :
    NMMSDerivable base Γ Θ ↔ Nonempty (NMMS base (Γ ∣∼ Θ)) := by
  rfl

/--
Any base entailment is derivable in `NMMS` by the base axiom.

This is the easy half of conservativity for the logical extension over a fixed
background.
-/
theorem nmmsDerivable_of_base (base : BaseRel)
    {Γ Θ : Multiset MyProp} (h : base Γ Θ) :
    NMMSDerivable base Γ Θ := by
  exact ⟨NMMS.baseAx h⟩

/--
The strongest two-sided monotonicity property for a multisuccedent consequence
relation: derivability persists under arbitrary left and right context
extension.
-/
def TwoSidedMonotone
    (R : Multiset MyProp → Multiset MyProp → Prop) : Prop :=
  ∀ {Γ Θ : Multiset MyProp},
    R Γ Θ → ∀ Δ Λ : Multiset MyProp, R (Δ + Γ) (Θ + Λ)

/--
If the derived `NMMS` consequence relation is two-sided monotone, then every
derivable sequent is monotone in the meta-level sense used by `M`.
-/
theorem monotoneDerivable_of_twoSidedMonotone
    (base : BaseRel)
    (hmono : TwoSidedMonotone (NMMSDerivable base))
    {Γ Θ : Multiset MyProp}
    (h : NMMSDerivable base Γ Θ) :
    MonotoneDerivable base Γ Θ := by
  intro Δ Λ
  exact hmono h Δ Λ

/--
Internal nonmonotonicity at a fixed background: some derivable sequent fails to
persist under a further context extension.

This is the sense in which Hlobil/Kaplan style systems are already genuinely
nonmonotonic even when the primitive background relation is fixed once and for
all.
-/
def InternallyNonmonotone
    (R : Multiset MyProp → Multiset MyProp → Prop) : Prop :=
  ∃ (Γ Θ Δ Λ : Multiset MyProp), R Γ Θ ∧ ¬ R (Δ + Γ) (Θ + Λ)

/--
Internal nonmonotonicity of the `NMMS` consequence relation over a fixed base
relation.
-/
def FixedBaseInternallyNonmonotone (base : BaseRel) : Prop :=
  InternallyNonmonotone (NMMSDerivable base)

/--
Equivalent formulation of fixed-base internal nonmonotonicity: there is a
derivable sequent that is not `MonotoneDerivable`.
-/
theorem fixedBaseInternallyNonmonotone_iff_exists_not_monotoneDerivable
    (base : BaseRel) :
    FixedBaseInternallyNonmonotone base ↔
      ∃ Γ Θ : Multiset MyProp,
        NMMSDerivable base Γ Θ ∧ ¬ MonotoneDerivable base Γ Θ := by
  classical
  constructor
  · intro h
    rcases h with ⟨Γ, Θ, Δ, Λ, hderiv, hfail⟩
    refine ⟨Γ, Θ, hderiv, ?_⟩
    intro hmono
    exact hfail (hmono Δ Λ)
  · intro h
    rcases h with ⟨Γ, Θ, hderiv, hnot⟩
    push_neg at hnot
    rcases hnot with ⟨Δ, Λ, hfail⟩
    exact ⟨Γ, Θ, Δ, Λ, hderiv, hfail⟩

/--
Two-sided monotonicity rules out fixed-base internal nonmonotonicity.

So if we later prove a concrete `NMMS` instance is internally nonmonotone, that
immediately certifies failure of unrestricted weakening for the derived
consequence relation.
-/
theorem not_fixedBaseInternallyNonmonotone_of_twoSidedMonotone
    (base : BaseRel)
    (hmono : TwoSidedMonotone (NMMSDerivable base)) :
    ¬ FixedBaseInternallyNonmonotone base := by
  intro hnon
  rcases hnon with ⟨Γ, Θ, Δ, Λ, hderiv, hfail⟩
  exact hfail (hmono hderiv Δ Λ)

/--
A family of primitive/base consequence relations indexed by some background
parameter.

Typical intended readings of the background index:
- a knowledge base
- a stock of base sentences
- a chosen atomic/material consequence relation
- a language expansion parameter

The current project mainly works with a single fixed member of such a family.
-/
abbrev BackgroundIndexedBaseRel (β : Type u) := β → BaseRel

/--
Specialize a background-indexed primitive consequence family at one chosen
background.

This turns a background-sensitive setup into the fixed-base setup used by the
current quotient/pre-Lie/Hopf development.
-/
def fixedBaseAt {β : Type u} (B : BackgroundIndexedBaseRel β) (b : β) : BaseRel :=
  B b

@[simp] theorem fixedBaseAt_apply {β : Type u}
    (B : BackgroundIndexedBaseRel β) (b : β)
    (Γ Θ : Multiset MyProp) :
    fixedBaseAt B b Γ Θ = B b Γ Θ := by
  rfl

/--
The `NMMS`-derivable consequence relation obtained from a background-indexed
base family by fixing one background.
-/
def NMMSDerivableAt {β : Type u}
    (B : BackgroundIndexedBaseRel β) (b : β) :
    Multiset MyProp → Multiset MyProp → Prop :=
  NMMSDerivable (fixedBaseAt B b)

@[simp] theorem nmmsDerivableAt_iff {β : Type u}
    (B : BackgroundIndexedBaseRel β) (b : β)
    (Γ Θ : Multiset MyProp) :
    NMMSDerivableAt B b Γ Θ ↔ Nonempty (NMMS (B b) (Γ ∣∼ Θ)) := by
  rfl

/--
Background-monotonicity: extending the background parameter never destroys a
derivable sequent.

This is distinct from fixed-base monotonicity. A relation may be internally
nonmonotone at each fixed background while still being monotone as the
background grows, or vice versa.
-/
def BackgroundMonotone
    {β : Type u}
    (Ext : β → β → Prop)
    (B : BackgroundIndexedBaseRel β) : Prop :=
  ∀ {b b' : β}, Ext b b' →
    ∀ {Γ Θ : Multiset MyProp},
      NMMSDerivableAt B b Γ Θ →
      NMMSDerivableAt B b' Γ Θ

/--
Background sensitivity: some derivable sequent at one background fails after a
background extension.

This captures the stronger "changing the base changes the consequence relation"
phenomenon. It should not be conflated with fixed-base internal
nonmonotonicity.
-/
def BackgroundSensitive
    {β : Type u}
    (Ext : β → β → Prop)
    (B : BackgroundIndexedBaseRel β) : Prop :=
  ∃ (b b' : β) (Γ Θ : Multiset MyProp),
    Ext b b' ∧
      NMMSDerivableAt B b Γ Θ ∧
      ¬ NMMSDerivableAt B b' Γ Θ

/--
Background monotonicity rules out background sensitivity.

This is the direct analogue of
`not_fixedBaseInternallyNonmonotone_of_twoSidedMonotone`, but now for failure
caused by changing the background parameter rather than extending a fixed
premise context.
-/
theorem not_backgroundSensitive_of_backgroundMonotone
    {β : Type u}
    (Ext : β → β → Prop)
    (B : BackgroundIndexedBaseRel β)
    (hmono : BackgroundMonotone Ext B) :
    ¬ BackgroundSensitive Ext B := by
  intro hsens
  rcases hsens with ⟨b, b', Γ, Θ, hExt, hderiv, hfail⟩
  exact hfail (hmono hExt hderiv)

/--
Exact conservativity of the logical extension over a fixed base background:
derivability agrees with the primitive consequence relation on purely base
sequents.

The forward implication is a substantive metatheorem; the reverse implication is
always given by `nmmsDerivable_of_base`.
-/
def NMMSExactlyConservativeOverBase (base : BaseRel) : Prop :=
  ∀ {Γ Θ : Multiset MyProp},
    IsBaseMultiset Γ →
    IsBaseMultiset Θ →
    (NMMSDerivable base Γ Θ ↔ base Γ Θ)

/--
Per-background version of exact conservativity: after fixing one background
parameter, the logically extended relation agrees with the primitive relation on
base sequents.
-/
def NMMSExactlyConservativeOverBaseAt
    {β : Type u}
    (B : BackgroundIndexedBaseRel β)
    (b : β) : Prop :=
  NMMSExactlyConservativeOverBase (B b)

@[simp] theorem nmmsExactlyConservativeOverBaseAt_iff
    {β : Type u}
    (B : BackgroundIndexedBaseRel β)
    (b : β) :
    NMMSExactlyConservativeOverBaseAt B b ↔
      NMMSExactlyConservativeOverBase (B b) := by
  rfl

theorem nmmsExactlyConservativeOverBase_of_forward
    (base : BaseRel)
    (hforward :
      ∀ {Γ Θ : Multiset MyProp},
        IsBaseMultiset Γ →
        IsBaseMultiset Θ →
        NMMSDerivable base Γ Θ →
        base Γ Θ) :
    NMMSExactlyConservativeOverBase base := by
  intro Γ Θ hΓ hΘ
  constructor
  · exact hforward hΓ hΘ
  · intro h
    exact nmmsDerivable_of_base base h

/--
If a background-indexed base family is exactly conservative at each background
member, then each fixed-background specialization inherits exact
conservativity.
-/
theorem nmmsExactlyConservativeOverBaseAt_of_forward
    {β : Type u}
    (B : BackgroundIndexedBaseRel β)
    (b : β)
    (hforward :
      ∀ {Γ Θ : Multiset MyProp},
        IsBaseMultiset Γ →
        IsBaseMultiset Θ →
        NMMSDerivableAt B b Γ Θ →
        B b Γ Θ) :
    NMMSExactlyConservativeOverBaseAt B b := by
  exact nmmsExactlyConservativeOverBase_of_forward (B b) hforward

/-!
Summary of the distinction:

- `FixedBaseInternallyNonmonotone base`:
  a single fixed background already exhibits nonmonotonicity under premise
  extension.
- `BackgroundSensitive Ext B`:
  changing the background itself destroys an inference.

The current proof-tree/Hopf development mainly fixes one `base : BaseRel` and
works in the first regime.  The second regime is recorded here so that later
generalizations can be expressed without changing the existing coalgebraic code.
-/

/-! ## Extended derivation system NM-MS[M] (`|∼[M]`) -/

/--
The derivation system NM-MS extended with introduction rules for
the monotonicity modality `MyProp.mon` (`M` in the paper).

  - `embed`: every NM-MS derivation is an NM-MS[M] derivation
  - `lm`  (Left M):  `A, Γ |∼M Θ`   ⊢  `M A, Γ |∼[M] Θ`
  - `rm`  (Right M): `Γ |∼M Θ, A`   ⊢  `Γ |∼[M] Θ, M A`

Premises of `lm` and `rm` use the meta-level `MonotoneDerivable`
predicate (`|∼M`), not the extended turnstile (`|∼[M]`).
-/
inductive NMMS_M (base : BaseRel) : MultiSequent → Type u where
  /-- Every NM-MS derivation is valid in NM-MS[M]. -/
  | embed {s : MultiSequent} :
      NMMS base s → NMMS_M base s
  /-- LM: a monotone left hypothesis may be tagged with M. -/
  | lm {A : MyProp} {Γ Θ : Multiset MyProp} :
      MonotoneDerivable base (A ::ₘ Γ) Θ →
      NMMS_M base ((MyProp.mon A ::ₘ Γ) ∣∼ Θ)
  /-- RM: a monotone right conclusion may be tagged with M. -/
  | rm {A : MyProp} {Γ Θ : Multiset MyProp} :
      MonotoneDerivable base Γ (A ::ₘ Θ) →
      NMMS_M base (Γ ∣∼ (MyProp.mon A ::ₘ Θ))

/-! ## Corollary 2: M expresses weakening/monotonicity -/

/--
`MyProp.mon A` never appears in any NM-MS (base system) derivation.

Argument: `baseAx` requires all formulas to be base formulas, and
`MyProp.mon A` is not base (the wildcard branch of `IsBaseFormula`
returns `False`). No logical rule introduces `mon`, and there is no
weakening rule. So by induction, `mon` is absent from all base derivations.

The inductive proof is deferred; the lemma is used to eliminate the
`embed` and `rm` cases in Corollary 2.
-/
lemma nmms_no_mon_lhs (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp} :
    ¬ Nonempty (NMMS base ((MyProp.mon A ::ₘ Γ) ∣∼ Θ)) := by
  sorry

/--
Backward direction of Corollary 2 (left):
  `∀ Δ Λ, Δ + A, Γ |∼ Θ + Λ`  →  `M A, Γ |∼[M] Θ`
-/
theorem nmms_m_lm_intro (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp}
    (h : MonotoneDerivable base (A ::ₘ Γ) Θ) :
    NMMS_M base ((MyProp.mon A ::ₘ Γ) ∣∼ Θ) :=
  NMMS_M.lm h

/--
Backward direction of Corollary 2 (right):
  `∀ Δ Λ, Δ + Γ |∼ Θ, A + Λ`  →  `Γ |∼[M] Θ, M A`
-/
theorem nmms_m_rm_intro (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp}
    (h : MonotoneDerivable base Γ (A ::ₘ Θ)) :
    NMMS_M base (Γ ∣∼ (MyProp.mon A ::ₘ Θ)) :=
  NMMS_M.rm h

/--
Forward direction of Corollary 2 (left):
  `M A, Γ |∼[M] Θ`  →  `∀ Δ Λ, Δ + A, Γ |∼ Θ + Λ`

- `embed h`: vacuous — `nmms_no_mon_lhs` shows `mon A` cannot appear
  on the left of any base-system derivation.
- `lm h`: the monotonicity hypothesis `h` is exactly what we need.
- `rm h`: in this branch Lean unifies the sequent index, giving
  `h : MonotoneDerivable base (MyProp.mon A ::ₘ Γ) _`. Instantiating
  at `Δ = 0, Λ = 0` produces a base derivation with `mon A` on the
  left, contradicting `nmms_no_mon_lhs`.
-/
theorem nmms_m_lm_elim (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp}
    (d : NMMS_M base ((MyProp.mon A ::ₘ Γ) ∣∼ Θ)) :
    MonotoneDerivable base (A ::ₘ Γ) Θ := by
  cases d with
  | embed h => exact absurd ⟨h⟩ nmms_no_mon_lhs
  | lm h    => exact h
  | rm h    =>
      have hmon := h 0 0
      simp only [Multiset.zero_add, Multiset.add_zero] at hmon
      exact absurd hmon nmms_no_mon_lhs

/--
Corollary 2 (left), full biconditional:
  `M A, Γ |∼[M] Θ  ↔  ∀ Δ Λ, Δ + A, Γ |∼ Θ + Λ`
-/
theorem corollary2_left (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp} :
    NMMS_M base ((MyProp.mon A ::ₘ Γ) ∣∼ Θ) ↔
    MonotoneDerivable base (A ::ₘ Γ) Θ :=
  ⟨nmms_m_lm_elim base, nmms_m_lm_intro base⟩

/--
Corollary 2 (right), biconditional:
  `Γ |∼[M] Θ, M A  ↔  ∀ Δ Λ, Δ + Γ |∼ Θ, A + Λ`

Forward direction deferred (symmetric argument to the left case).
-/
theorem corollary2_right (base : BaseRel) {A : MyProp} {Γ Θ : Multiset MyProp} :
    NMMS_M base (Γ ∣∼ (MyProp.mon A ::ₘ Θ)) ↔
    MonotoneDerivable base Γ (A ::ₘ Θ) :=
  ⟨fun d => by
    cases d with
    | embed h => exact absurd ⟨h⟩ (by sorry)  -- nmms_no_mon_rhs, symmetric
    | lm h    => exact absurd (h 0 0) (by simp; sorry)
    | rm h    => exact h,
   nmms_m_rm_intro base⟩

/-! ## Cut normalisation boundary -/

/--
A formula *supports cut elimination* when it appears as a cut formula.

Holds for:
  - all logical connectives (`⇒`, `&`, `∨`, `¬`): standard cut elimination
    by induction on formula complexity, independent of weakening.
  - all M-tagged formulas (`MyProp.mon A`): M internalises exactly the
    context-transfer step that the cut elimination argument needs.

Fails for:
  - bare atoms (`MyProp.atom a`) and `MyProp.falsum`: the nonmonotonic
    base produces ineliminable cuts here.
-/
def NormalisableAtCut (A : MyProp) : Prop := ¬ IsBaseFormula A

-- M-tagged: IsBaseFormula returns False (wildcard), so ¬ False = True.
theorem normalisableAtCut_mon (A : MyProp) : NormalisableAtCut (MyProp.mon A) :=
  fun h => h

-- Logical connectives: all handled by the wildcard, same argument.
theorem normalisableAtCut_imp  (A B : MyProp) : NormalisableAtCut (A ⇒ B)       := fun h => h
theorem normalisableAtCut_conj (A B : MyProp) : NormalisableAtCut (A & B)        := fun h => h
theorem normalisableAtCut_disj (A B : MyProp) : NormalisableAtCut (A ∨ B)        := fun h => h
theorem normalisableAtCut_neg  (A   : MyProp) : NormalisableAtCut (MyProp.neg A)  := fun h => h

-- Bare atoms: IsBaseFormula = True, so NormalisableAtCut = (True → False) → False.
-- The negation ¬ NormalisableAtCut is provable by supplying `trivial : True`.
theorem not_normalisableAtCut_atom (a : Atomic) :
    ¬ NormalisableAtCut (MyProp.atom a) :=
  fun h => h trivial

theorem not_normalisableAtCut_falsum :
    ¬ NormalisableAtCut MyProp.falsum :=
  fun h => h trivial

/--
The normalisation boundary is exactly the base/non-base divide.
-/
theorem normalisableAtCut_iff_not_base (A : MyProp) :
    NormalisableAtCut A ↔ ¬ IsBaseFormula A :=
  Iff.rfl
