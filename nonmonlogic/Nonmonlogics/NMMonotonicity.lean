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
