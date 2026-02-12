import Mathlib

notation "T" => Tropical (WithTop ℝ)

noncomputable instance : CommSemiring T :=  by
  exact Tropical.instCommSemiring

open Tropical
open WithTop
open LinearOrderedAddCommGroup

example (a : T) : a + a = a:= by
  exact add_self a

example : (1 : T) + (0 : T) = (1 : T) := by
  rw [← untrop_inj_iff]
  rw [untrop_add]
  rw [untrop_zero]
  exact rfl


example (a : T) : a*(1:T) = a := by
  rw [← untrop_inj_iff]
  rw [untrop_mul]
  rw [untrop_one]
  rw [add_zero]



example : IsField T := by
  refine {
    exists_pair_ne := by exact exists_pair_ne T,
    mul_comm := by exact fun x y ↦ CommMonoid.mul_comm x y ,
    mul_inv_cancel := by
      intro a ha
      use trop (-(untrop a))
      rw [← untrop_inj_iff]
      rw [untrop_one]
      rw [untrop_mul]
      rw [untrop_trop]
      rw [LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top]
      have aux : untrop a ≠ ⊤ := by
        intro hb
        rw [← trop_inj_iff] at hb
        rw [trop_untrop] at hb
        rw [trop_top] at hb
        exact ha hb
      assumption
     }
