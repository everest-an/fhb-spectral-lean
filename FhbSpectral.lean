import Mathlib

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

/-!
  FHB · the spectral core of the Fuxi Hypercube Benchmark.

  `AwareLiquid/The-Fuxi-Hypercube-Math` derives its exact mixing result from the
  spectrum of the hypercube walk.  This module supplies that spectrum.

  Vertices are `(Z/2)^n` (`n = 6` gives the 64 Fuxi hexagrams).  The walk
  Hamiltonian is the hypercube adjacency

      H ψ x = Σ_j ψ (flip_j x) ,

  and it is diagonalised by the characters

      χ_S x = ∏_{j ∈ S} (if x_j = 0 then 1 else -1) ,   S ⊆ Fin n ,

  with eigenvalue `n - 2·|S|`:

      H (χ_S) x = (n - 2·|S|) · χ_S x .

  Those eigenvalues are exactly what makes the walk uniformly mixing at
  `t = π/4` (Moore–Russell, arXiv:quant-ph/0104137, Thm 2; FHB Thm 3).
-/

namespace FHBSpectral

/-- Vertices of the hypercube `Q_n`: the `n`-hexagram states `(Z/2)^n`. -/
abbrev V (n : ℕ) := Fin n → ZMod 2

/-- Flip coordinate `j` (one single-line change). -/
def flip {n : ℕ} (j : Fin n) (x : V n) : V n := Function.update x j (x j + 1)

/-- The walk Hamiltonian: the hypercube adjacency `H = Σ_j X_j`. -/
noncomputable def H {n : ℕ} (ψ : V n → ℂ) : V n → ℂ := fun x => ∑ j, ψ (flip j x)

/-- The character `χ_S`. -/
noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (x : V n) : ℂ :=
  ∏ j ∈ S, (if x j = 0 then (1 : ℂ) else -1)

lemma eq_zero_or_eq_one (y : ZMod 2) : y = 0 ∨ y = 1 := by
  have : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  exact this y

lemma flip_apply_self {n : ℕ} (j : Fin n) (x : V n) : flip j x j = x j + 1 := by
  simp [flip]

lemma flip_apply_of_ne {n : ℕ} {j i : Fin n} (h : i ≠ j) (x : V n) :
    flip j x i = x i := by
  simp only [flip]
  exact Function.update_of_ne h _ _

/-- The factor at `j` is negated by flipping `j`. -/
lemma factor_flip {n : ℕ} (j : Fin n) (x : V n) :
    (if flip j x j = 0 then (1 : ℂ) else -1) =
      -1 * (if x j = 0 then (1 : ℂ) else -1) := by
  rw [flip_apply_self]
  rcases eq_zero_or_eq_one (x j) with hx | hx
  · rw [if_neg (by rw [hx]; decide : ¬ (x j + 1 = 0)), if_pos hx]
    ring
  · rw [if_pos (by rw [hx]; decide : x j + 1 = 0),
        if_neg (by rw [hx]; decide : ¬ (x j = 0))]
    ring

/-- Flipping coordinate `j` negates the factor of `χ_S` at `j` and leaves every
other factor alone. -/
lemma chi_flip {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (x : V n) :
    chi S (flip j x) = (if j ∈ S then (-1 : ℂ) else 1) * chi S x := by
  classical
  unfold chi
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    conv_lhs => rw [← Finset.insert_erase hj]
    conv_rhs => rw [← Finset.insert_erase hj]
    rw [Finset.prod_insert (Finset.notMem_erase j S),
      Finset.prod_insert (Finset.notMem_erase j S), factor_flip]
    have hprod : (∏ i ∈ S.erase j, (if flip j x i = 0 then (1 : ℂ) else -1))
        = ∏ i ∈ S.erase j, (if x i = 0 then (1 : ℂ) else -1) :=
      Finset.prod_congr (M := ℂ) rfl
        (fun i hi => by rw [flip_apply_of_ne (Finset.mem_erase.mp hi).1])
    rw [hprod]
    ring
  · rw [if_neg hj, one_mul]
    exact Finset.prod_congr (M := ℂ) rfl
      (fun i hi => by
        have hij : i ≠ j := by
          intro h
          exact hj (h ▸ hi)
        rw [flip_apply_of_ne hij])

/-- The eigenvalue sum: `Σ_j (if j ∈ S then -1 else 1) = n - 2·|S|`. -/
lemma sum_ite_mem {n : ℕ} (S : Finset (Fin n)) :
    (∑ j : Fin n, (if j ∈ S then (-1 : ℂ) else 1)) = n - 2 * S.card := by
  classical
  have hpt : ∀ j : Fin n,
      (if j ∈ S then (-1 : ℂ) else 1) = 1 - 2 * (if j ∈ S then (1 : ℂ) else 0) := by
    intro j
    by_cases h : j ∈ S
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp only [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  have hcount : (∑ j : Fin n, (if j ∈ S then (1 : ℂ) else 0)) = S.card := by
    rw [Finset.sum_ite_mem]
    simp
  rw [hcount]
  ring

/-- **The spectral theorem.**  Every character is an eigenvector of the walk
Hamiltonian with eigenvalue `n - 2·|S|`. -/
theorem H_chi {n : ℕ} (S : Finset (Fin n)) (x : V n) :
    H (chi S) x = (n - 2 * S.card) * chi S x := by
  classical
  unfold H
  simp only [chi_flip]
  rw [← Finset.sum_mul, sum_ite_mem]

end FHBSpectral
