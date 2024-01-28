import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists

namespace Syntax

universe u

-- Define the Atom datatype with constructors Int and String
inductive Atomic : Type
| Int : Atomic
| String : Atomic

inductive MyProp : Type u
| El : Atomic → MyProp
| imp : MyProp → MyProp → MyProp
infixr: 6 "⇒" => MyProp.imp

-- Define the Sequent datatype
inductive Sequent : Type u
| Proof : List MyProp → MyProp → Sequent
infixr: 6 "⊢" => Sequent.Proof

variable {A B C: MyProp}
variable {Γ Γ' : List MyProp}
variable {S : Sequent}

-- Define the ND_ datatype for Minimal Prop Logic

inductive ND_ : Sequent → Type
| ax : A ∈ Γ → ND_ (Γ ⊢ A)
| imp_i : ND_ (A :: Γ ⊢ B) → ND_ (Γ ⊢ A ⇒ B)
| imp_e : ND_ (Γ ⊢ A ⇒ B) → ND_ (Γ ⊢ A) → ND_ (Γ ⊢ B)

#check ND_

-- Declare the precedence for the ND_ operator
infix: 3 "ND_" => ND_

inductive SC_ : Sequent → Type u
| ax : A ∈ Γ → SC_ (Γ ⊢ A)
| cut : SC_ (Γ ⊢ A) → SC_ (A :: Γ ⊢ B) → SC_ (Γ ⊢ B)
| imp_l : SC_ (Γ ⊢ A) → SC_ (B :: Γ ⊢ C) → SC_ ((A ⇒ B) :: Γ ⊢ C)
| imp_r : SC_ (A :: Γ ⊢ B) → SC_ (Γ ⊢ A ⇒ B)

-- Declare the precedence for the SC_ operator
infix: 3 "SC_" => SC_

end Syntax


namespace HeteroProperties



-- Assuming `A` and `B` are defined appropriately
variable {A B : Type}
-- Assuming `R` is defined appropriately
variable {R : A → B → Prop}

-- Define the ++ˡ function in Lean
def concat_lists {α : Type} : List α → List α → List α
| [], ys => ys
| (x :: xs), ys => x :: concat_lists xs ys



-- Define the ++⁺ˡ function in Lean
--def concat_sublist {as bs cs : List A} (h : List.Sublist as bs) : List.Sublist as (concat_lists cs bs) :=
--  List.Sublist.trans h (sublist_concat_right cs bs)



end HeteroProperties


/-
-- Define the ++ˡ function
def concat_lists {α : Type} : List α → List α → List α
| [], ys => ys
| (x :: xs), ys => x :: concat_lists xs ys

-- Define the ++⁺ˡ function in Lean
def concat_subset {as bs cs : List A} (h : as ⊆ bs) : as ⊆ (concat_lists cs bs) :=
  h


-- Define the function w'
--def w' : Syntax.ND_ Γ ⊢ B → Syntax.ND_ (list.cons A Γ) ⊢ B :=
 -- λ f struct (++⁺ˡ _ ⊆-refl) f

  /-import data.list

  def concatenateLists {α : Type} : list α → list α → list α :=
    list.append

  -- Example usage
  #eval concatenateLists [1, 2, 3] [4, 5, 6] -- Result: [1, 2, 3, 4, 5, 6]
-/


end Syntax
