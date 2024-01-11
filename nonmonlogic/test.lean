import Mathlib.Topology.Basic
--import Mathlib.group

#check TopologicalSpace


-- FILEPATH: /path/to/file.lean
-- BEGIN

inductive nat : Type
| zero : nat
| succ : nat → nat

-- END

-- FILEPATH: /path/to/file.lean
-- BEGIN


/- variables {G : Type} [group G]

theorem unique_identity (e₁ e₂ : G) (h₁ : ∀ g : G, e₁ * g = g) (h₂ : ∀ g : G, e₂ * g = g) : e₁ = e₂ :=
begin
  rw ←h₂ e₁,
  rw ←h₁ e₂,
  rw ←mul_one e₁,
  rw ←mul_one e₂,
  rw mul_assoc,
  rw mul_inv_self,
  rw mul_one,
end
-- END -/
