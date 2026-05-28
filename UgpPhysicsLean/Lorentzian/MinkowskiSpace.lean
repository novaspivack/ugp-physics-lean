import Mathlib

/-!
# Minkowski Space and Lorentz Group

Minkowski metric η = diag(-1,+1,+1,+1) on ℝ⁴.
The Lorentz group SO(1,3) = {M : Mat₄ℝ | Mᵀ η M = η, det M = 1}.
-/

namespace Lorentzian

open Matrix

/-- The Minkowski metric matrix η = diag(-1,1,1,1) -/
def η : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal (![(-1 : ℝ), 1, 1, 1])

/-- The Minkowski inner product ⟨u,v⟩_η = uᵀ η v -/
def minkowskiInner (u v : Fin 4 → ℝ) : ℝ :=
  u ⬝ᵥ (η *ᵥ v)

/-- A vector is timelike if ⟨v,v⟩ < 0 -/
def Timelike (v : Fin 4 → ℝ) : Prop := minkowskiInner v v < 0

/-- A vector is spacelike if ⟨v,v⟩ > 0 -/
def Spacelike (v : Fin 4 → ℝ) : Prop := minkowskiInner v v > 0

/-- A vector is null (lightlike) if ⟨v,v⟩ = 0 -/
def Null (v : Fin 4 → ℝ) : Prop := minkowskiInner v v = 0

/-- A matrix preserves the Minkowski metric. -/
def isLorentzMatrix (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Mᵀ * η * M = η

theorem lorentz_identity : isLorentzMatrix (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  simp [isLorentzMatrix, η]

private lemma minkowski_mul_reassoc (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    N.transpose * M.transpose * η * (M * N) = N.transpose * (M.transpose * η * M) * N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, η, diagonal, Fin.sum_univ_four]
  all_goals ring_nf

theorem lorentz_closed_mul (M N : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : isLorentzMatrix M) (hN : isLorentzMatrix N) :
    isLorentzMatrix (M * N) := by
  simp only [isLorentzMatrix, Matrix.transpose_mul]
  calc
    N.transpose * M.transpose * η * (M * N) =
        N.transpose * (M.transpose * η * M) * N := minkowski_mul_reassoc M N
    _ = η := by rw [hM, hN]

theorem lorentz_inv_of_mul (M Minv : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : isLorentzMatrix M) (hMMinv : M * Minv = 1) : isLorentzMatrix Minv := by
  simp only [isLorentzMatrix]
  have hη : M.transpose * η * M = η := hM
  have hmid : Minv.transpose * η = η * M := by
    have step1 : Minv.transpose * η = Minv.transpose * (M.transpose * η * M) := by
      rw [hη]
    calc
      Minv.transpose * η = Minv.transpose * (M.transpose * η * M) := step1
      _ = Minv.transpose * M.transpose * η * M := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = (M * Minv).transpose * η * M := by simp [Matrix.transpose_mul]
      _ = η * M := by simp [hMMinv, Matrix.transpose_one]
  calc
    Minv.transpose * η * Minv = (Minv.transpose * η) * Minv := by rw [Matrix.mul_assoc]
    _ = (η * M) * Minv := by rw [hmid]
    _ = η * (M * Minv) := by rw [Matrix.mul_assoc]
    _ = η := by simp [hMMinv]

/-- The Lorentz group: matrices preserving the Minkowski metric -/
def LorentzGroup : Subgroup (GL (Fin 4) ℝ) where
  carrier := {M | isLorentzMatrix M.val}
  one_mem' := by
    simpa using lorentz_identity
  mul_mem' := by
    intro M N hM hN
    simp only [Set.mem_setOf_eq, isLorentzMatrix] at hM hN ⊢
    have hval : (M * N).val = M.val * N.val := Units.val_mul M N
    rw [hval]
    exact lorentz_closed_mul M.val N.val hM hN
  inv_mem' := by
    intro M hM
    simp only [Set.mem_setOf_eq, isLorentzMatrix]
    exact lorentz_inv_of_mul M.val (M⁻¹).val hM (Units.mul_inv M)

theorem eta_symmetric : η = ηᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [η, diagonal, transpose]

theorem minkowski_inner_symm (u v : Fin 4 → ℝ) :
    minkowskiInner u v = minkowskiInner v u := by
  simp [minkowskiInner, dotProduct, mulVec, η, diagonal]
  congr 1
  ext i
  ring

/-- Standard basis vector e₀ is timelike. -/
def e0 : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0

/-- Standard basis vector e₁ is spacelike. -/
def e1 : Fin 4 → ℝ := fun i => if i = 1 then 1 else 0

theorem basis_e0_timelike : Timelike e0 := by
  simp [Timelike, minkowskiInner, e0, dotProduct, mulVec, η, diagonal]

theorem basis_e1_spacelike : Spacelike e1 := by
  simp [Spacelike, minkowskiInner, e1, dotProduct, mulVec, η, diagonal]

end Lorentzian
