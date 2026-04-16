import Nonmonlogics.GrossmanLarssonOudomGuin

/-!
Computable layer for the Oudom-Guin / Grossman-Larson coproduct.

This file stays on raw `PTree` data and avoids quotient-level definitions.
The core idea: use the explicit list of coproduct data and compute sums
directly over that list (via `toFinset` when needed).
-/

namespace QuotientConnected.CoproductSupport

def coproductEval (t : PTree) : List (Prod Forest PTree) :=
  (coproductSupportSummary t).supportList

@[simp] theorem coproductEval_eq_supportList (t : PTree) :
    coproductEval t = (coproductSupportSummary t).supportList := by
  rfl

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
    coproductEvalSum t f = (coproductEval t).toFinset.sum f := by
  rfl

theorem coproductEvalSum_eq_supportSummary_sum
    {alpha : Type*} [AddCommMonoid alpha]
    [DecidableEq (Prod Forest PTree)]
    (t : PTree) (f : Prod Forest PTree -> alpha) :
    coproductEvalSum t f = coproductSupportSummary_sum t f := by
  simp [coproductEvalSum, coproductEval, coproductSupportSummary_sum_eq_supportList]

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

end QuotientConnected.CoproductSupport
