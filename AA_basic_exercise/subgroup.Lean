import Mathlib

open Set
open Subgroup MonoidHom

example {G : Type*} [CommGroup G] (H : Subgroup G) : H.Normal where
  conj_mem := by
    intro a ha b
    have : b * a * b⁻¹ = a := by simp only [mul_comm, mul_inv_cancel_right]
    rw [this]
    exact ha
