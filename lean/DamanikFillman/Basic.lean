/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, Graduate Studies in Mathematics 221, AMS 2022.

# Basic objects shared by all chapters  (book §2.2, eqs. (2.2.1), (2.2.2), (2.2.4))

* `DF.schr V` — the discrete Schrödinger operator `[Hφ](n) = φ(n+1) + φ(n-1) + V(n) φ(n)`
  on `ℓ²(ℤ)` with bounded real potential `V` (2.2.1);
* `DF.BddPot V` — boundedness of the potential;
* `DF.transfer z v`, `DF.transferProd` — one-step transfer matrices
  `T_z(n) = [[z - V(n), -1], [1, 0]]` and their products `A_z(n) = T_z(n) ⋯ T_z(1)` (2.2.4).

`ℓ²(ℤ)` is the space `L2 ℤ` of `AnalyticPerturbationsAMO.Operators`.
-/
import AnalyticPerturbationsAMO.Operators

noncomputable section

open L2

namespace DF

/-- Bounded operators on `ℓ²(ℤ)`. -/
abbrev Op := L2 ℤ →L[ℂ] L2 ℤ

/-- The potential `V : ℤ → ℝ` is bounded. -/
def BddPot (V : ℤ → ℝ) : Prop := ∃ M, ∀ n, |V n| ≤ M

lemma bdd_of_bddPot {V : ℤ → ℝ} (hV : BddPot V) : Bdd (fun n : ℤ => ((V n : ℝ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hV
  exact ⟨M, fun n => by simpa [Complex.norm_real] using hM n⟩

lemma bdd_one : Bdd (fun _ : ℤ => (1 : ℂ)) := ⟨1, fun _ => by simp⟩

/-- The discrete Schrödinger operator (2.2.1): `[Hφ](n) = φ(n+1) + φ(n-1) + V(n) φ(n)`. -/
def schr (V : ℤ → ℝ) : Op :=
  weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight 1) +
  weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (-1)) +
  weightedShift (fun n : ℤ => ((V n : ℝ) : ℂ)) (Equiv.refl ℤ)

/-- Matrix elements of `schr V`. -/
lemma schr_apply {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) (n : ℤ) :
    schr V φ n = φ (n + 1) + φ (n - 1) + (V n : ℂ) * φ n := by
  simp only [schr, add_apply, lp.coeFn_add, Pi.add_apply]
  rw [weightedShift_apply bdd_one, weightedShift_apply bdd_one,
    weightedShift_apply (bdd_of_bddPot hV)]
  simp [sub_eq_add_neg]

/-- The one-step transfer matrix `T_z(n) = [[z - V(n), -1], [1, 0]]` (2.2.4), here as a
function of the value `v = V(n)`. -/
def transfer (z : ℂ) (v : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![z - v, -1; 1, 0]

/-- `A_z(n) = T_z(n) T_z(n-1) ⋯ T_z(1)` for `n ≥ 0` (2.2.4); `A_z(0) = I`. -/
def transferProd (V : ℤ → ℝ) (z : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | n + 1 => transfer z (V (n + 1)) * transferProd V z n

lemma det_transfer (z : ℂ) (v : ℝ) : (transfer z v).det = 1 := by
  simp [transfer, Matrix.det_fin_two]

lemma det_transferProd (V : ℤ → ℝ) (z : ℂ) (n : ℕ) : (transferProd V z n).det = 1 := by
  induction n with
  | zero => simp [transferProd]
  | succ n ih => simp [transferProd, Matrix.det_mul, det_transfer, ih]

/-- A sequence `u : ℤ → ℂ` solves the difference equation (2.2.2) at energy `z`. -/
def IsSolution (V : ℤ → ℝ) (z : ℂ) (u : ℤ → ℂ) : Prop :=
  ∀ n, u (n - 1) + u (n + 1) + (V n : ℂ) * u n = z * u n

/-- Transfer matrices propagate solutions: `(u(n+1), u(n)) = T_z(n) (u(n), u(n-1))`. -/
lemma transfer_step {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (n : ℤ) :
    Matrix.mulVec (transfer z (V n)) ![u n, u (n - 1)] = ![u (n + 1), u n] := by
  have h := hu n
  ext i; fin_cases i
  · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination -h
  · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end DF
