/-
# Jacobi operators, transfer matrices and Lyapunov exponents  (paper §1.1, §2)

* The prepared Jacobi operator `J = a(x+nα) U + conj(a(x+(n-1)α)) U^{-1} + b(x+nα)` on `ℓ²(ℤ)`,
  its explicit action, and its self-adjointness for real `b` (proved).
* The prepared transfer matrix `C = [[-b/c, -1/c], [c, 0]]`: `det C = 1` (proved), and the
  transfer identity `C(x_n) (u_n, c_{n-1}u_{n-1}) = (u_{n+1}, c_n u_n)` for solutions of
  `c_n u_{n+1} + c_{n-1} u_{n-1} + b_n u_n = 0` (proved).
* The cocycle iterates `A_n(x) = A(x+(n-1)α) ⋯ A(x)` and the **Lyapunov exponent**
  `L(α, A) = lim (1/n) ∫_𝕋 log ‖A_n(x)‖ dx`.  For a continuous `1`-periodic cocycle with
  `det A ≡ 1` we prove (Fekete) that the limit exists, equals the infimum, and is `≥ 0`.

We use the `ℓ^∞` operator norm on `2 × 2` matrices; `LyapunovNorm.lean` proves that the
Euclidean operator norm used in the paper gives the same exponent.
-/
import AnalyticPerturbationsAMO.Spectrum

noncomputable section

open scoped ComplexConjugate Matrix.Norms.Operator
open Matrix Filter Topology L2

namespace AMO

/-! ### The prepared Jacobi operator -/

/-- `J_x = a(x+nα) U + conj(a(x+(n-1)α)) U^{-1} + b(x+nα)` on `ℓ²(ℤ)`; here `a, b : ℂ → ℂ`
are evaluated on the real axis. -/
def jacobi (α : ℝ) (a b : ℂ → ℂ) (x : ℝ) : L2 ℤ →L[ℂ] L2 ℤ :=
  weightedShift (fun n : ℤ => a (x + n * α : ℝ)) (Equiv.addRight 1) +
    weightedShift (fun n : ℤ => conj (a (x + (n - 1) * α : ℝ))) (Equiv.addRight (-1)) +
    weightedShift (fun n : ℤ => b (x + n * α : ℝ)) (Equiv.refl ℤ)

/-- The weights of a Jacobi operator along an orbit are bounded. -/
def JacobiBdd (α : ℝ) (a b : ℂ → ℂ) (x : ℝ) : Prop :=
  Bdd (fun n : ℤ => a (x + n * α : ℝ)) ∧ Bdd (fun n : ℤ => b (x + n * α : ℝ))

lemma jacobi_apply {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (h : JacobiBdd α a b x) (u : L2 ℤ) (n : ℤ) :
    jacobi α a b x u n =
      a (x + n * α : ℝ) * u (n + 1) + conj (a (x + (n - 1) * α : ℝ)) * u (n - 1)
        + b (x + n * α : ℝ) * u n := by
  have h2 : Bdd (fun n : ℤ => conj (a (x + (n - 1) * α : ℝ))) := by
    have := (h.1.comp (Equiv.addRight (-1))).conj
    convert this using 3 with n
    simp [sub_eq_add_neg]
  simp only [jacobi, _root_.add_apply, lp.coeFn_add, Pi.add_apply,
    weightedShift_apply h.1, weightedShift_apply h2, weightedShift_apply h.2]
  simp [sub_eq_add_neg]

/-- The prepared Jacobi operator is self-adjoint when `b` is real on the real axis. -/
theorem isSelfAdjoint_jacobi {α : ℝ} {a b : ℂ → ℂ} {x : ℝ} (h : JacobiBdd α a b x)
    (hb : ∀ t : ℝ, conj (b t) = b t) : IsSelfAdjoint (jacobi α a b x) := by
  have h2 : Bdd (fun n : ℤ => conj (a (x + (n - 1) * α : ℝ))) := by
    have := (h.1.comp (Equiv.addRight (-1))).conj
    convert this using 3 with n
    simp [sub_eq_add_neg]
  unfold IsSelfAdjoint jacobi
  set X := weightedShift (fun n : ℤ => a (x + n * α : ℝ)) (Equiv.addRight 1)
  set Y := weightedShift (fun n : ℤ => conj (a (x + (n - 1) * α : ℝ))) (Equiv.addRight (-1))
  set Z := weightedShift (fun n : ℤ => b (x + n * α : ℝ)) (Equiv.refl ℤ)
  have hsum : star (X + Y + Z) = star X + star Y + star Z :=
    (star_add (X + Y) Z).trans (congrArg (· + star Z) (star_add X Y))
  rw [hsum, star_weightedShift h.1, star_weightedShift h2, star_weightedShift h.2]
  have e1 : weightedShift (fun j : ℤ => conj (a (x + ((Equiv.addRight (1 : ℤ)).symm j) * α : ℝ)))
      (Equiv.addRight (1 : ℤ)).symm =
      weightedShift (fun n : ℤ => conj (a (x + (n - 1) * α : ℝ))) (Equiv.addRight (-1)) := by
    apply weightedShift_congr
    · intro n; simp; ring_nf
    · intro n; simp [sub_eq_add_neg]
  have e2 : weightedShift
      (fun j : ℤ => conj (conj (a (x + (((Equiv.addRight (-1 : ℤ)).symm j : ℤ) - 1) * α : ℝ))))
      (Equiv.addRight (-1 : ℤ)).symm =
      weightedShift (fun n : ℤ => a (x + n * α : ℝ)) (Equiv.addRight 1) := by
    apply weightedShift_congr
    · intro n; simp
    · intro n; simp
  have e3 : weightedShift (fun j : ℤ => conj (b (x + ((Equiv.refl ℤ).symm j) * α : ℝ)))
      (Equiv.refl ℤ).symm = weightedShift (fun n : ℤ => b (x + n * α : ℝ)) (Equiv.refl ℤ) := by
    apply weightedShift_congr
    · intro n; simpa using hb (x + n * α)
    · intro n; simp
  rw [e1, e2, e3]
  abel

/-! ### Transfer matrices -/

/-- `2 × 2` complex matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The prepared transfer matrix `C = [[-b/c, -1/c], [c, 0]]`. -/
def transferMatrix (b c : ℂ) : M2 := !![-b / c, -1 / c; c, 0]

theorem det_transferMatrix (b : ℂ) {c : ℂ} (hc : c ≠ 0) : (transferMatrix b c).det = 1 := by
  simp [transferMatrix, Matrix.det_fin_two]
  field_simp

/-- For real `b` and `c ≠ 0` the transfer matrix lies in `SL(2, ℝ)`. -/
def transferMatrixSL (b c : ℝ) (hc : c ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![-b / c, -1 / c; c, 0], by simp [Matrix.det_fin_two]; field_simp⟩

/-- **Transfer identity.** If `c_n u_{n+1} + c_{n-1} u_{n-1} + b_n u_n = 0`, then
`C(b_n, c_n) (u_n, c_{n-1} u_{n-1}) = (u_{n+1}, c_n u_n)`. -/
theorem transferMatrix_mulVec {b c u : ℤ → ℂ} (hc : ∀ n, c n ≠ 0)
    (heq : ∀ n, c n * u (n + 1) + c (n - 1) * u (n - 1) + b n * u n = 0) (n : ℤ) :
    transferMatrix (b n) (c n) *ᵥ ![u n, c (n - 1) * u (n - 1)] = ![u (n + 1), c n * u n] := by
  have h := heq n
  have hcn := hc n
  ext i
  fin_cases i
  · simp [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    linear_combination -h
  · simp [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Cocycles and the Lyapunov exponent -/

/-- Rows of a `2 × 2` matrix are bounded by the `ℓ^∞` operator norm. -/
lemma row_sum_le_norm (M : M2) (i : Fin 2) : ‖M i 0‖ + ‖M i 1‖ ≤ ‖M‖ := by
  have h := Finset.le_sup (f := fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) (Finset.mem_univ i)
  rw [← linfty_opNNNorm_def] at h
  have h' : ((∑ j : Fin 2, ‖M i j‖₊ : NNReal) : ℝ) ≤ (‖M‖₊ : ℝ) := by exact_mod_cast h
  simpa [Fin.sum_univ_two] using h'

/-- `|det M| ≤ ‖M‖²` for `2 × 2` matrices. -/
theorem norm_det_le_sq (M : M2) : ‖M.det‖ ≤ ‖M‖ ^ 2 := by
  have h0 := row_sum_le_norm M 0
  have h1 := row_sum_le_norm M 1
  rw [Matrix.det_fin_two]
  calc ‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖
      ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ (‖M 0 0‖ + ‖M 0 1‖) * (‖M 1 0‖ + ‖M 1 1‖) := by
        nlinarith [norm_nonneg (M 0 0), norm_nonneg (M 0 1), norm_nonneg (M 1 0),
          norm_nonneg (M 1 1)]
    _ ≤ ‖M‖ * ‖M‖ := by
        apply mul_le_mul h0 h1 (by positivity) (norm_nonneg _)
    _ = ‖M‖ ^ 2 := by ring

lemma one_le_norm_of_det_eq_one {M : M2} (h : M.det = 1) : 1 ≤ ‖M‖ := by
  have := norm_det_le_sq M
  rw [h, norm_one] at this
  nlinarith [norm_nonneg M]

/-- The cocycle iterates `A_n(x) = A(x+(n-1)α) ⋯ A(x+α) A(x)`. -/
def iter (α : ℝ) (A : ℝ → M2) : ℕ → ℝ → M2
  | 0, _ => 1
  | n + 1, x => A (x + n * α) * iter α A n x

variable {α : ℝ} {A : ℝ → M2}

lemma iter_add (m n : ℕ) (x : ℝ) : iter α A (n + m) x = iter α A m (x + n * α) * iter α A n x := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [← add_assoc, iter, ih, iter, mul_assoc]
    congr 2
    push_cast
    ring

lemma det_iter (hdet : ∀ x, (A x).det = 1) (n : ℕ) (x : ℝ) : (iter α A n x).det = 1 := by
  induction n with
  | zero => simp [iter]
  | succ n ih => rw [iter, Matrix.det_mul, hdet, ih, one_mul]

lemma continuous_iter (hA : Continuous A) (n : ℕ) : Continuous (iter α A n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous fun x => A (x + n * α) * iter α A n x
    exact (hA.comp (continuous_id.add continuous_const)).mul ih

lemma iter_periodic (hper : Function.Periodic A 1) (n : ℕ) :
    Function.Periodic (iter α A n) 1 := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    change A (x + 1 + n * α) * iter α A n (x + 1) = A (x + n * α) * iter α A n x
    rw [ih x, add_right_comm, hper]

/-- `u_n = ∫_𝕋 log ‖A_n(x)‖ dx`. -/
def lyapSeq (α : ℝ) (A : ℝ → M2) (n : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, Real.log ‖iter α A n x‖

/-- The Lyapunov exponent `L(α, A) = lim_n (1/n) ∫_𝕋 log ‖A_n(x)‖ dx`. -/
def lyapunov (α : ℝ) (A : ℝ → M2) : ℝ := limUnder atTop fun n : ℕ => lyapSeq α A n / n

/-- Standing hypotheses on a cocycle: continuous, `1`-periodic, determinant one. -/
structure IsSLCocycle (A : ℝ → M2) : Prop where
  continuous : Continuous A
  periodic : Function.Periodic A 1
  det_eq_one : ∀ x, (A x).det = 1

namespace IsSLCocycle

variable (hA : IsSLCocycle A)
include hA

lemma one_le_norm_iter (n : ℕ) (x : ℝ) : 1 ≤ ‖iter α A n x‖ :=
  one_le_norm_of_det_eq_one (det_iter hA.det_eq_one n x)

lemma continuous_log_norm_iter (n : ℕ) : Continuous fun x => Real.log ‖iter α A n x‖ :=
  (continuous_iter hA.continuous n).norm.log
    (fun x => (zero_lt_one.trans_le (hA.one_le_norm_iter n x)).ne')

lemma lyapSeq_nonneg (n : ℕ) : 0 ≤ lyapSeq α A n :=
  intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => Real.log_nonneg (hA.one_le_norm_iter n x))

lemma integral_shift (n m : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.log ‖iter α A m (x + n * α)‖ = lyapSeq α A m := by
  rw [intervalIntegral.integral_comp_add_right (fun x => Real.log ‖iter α A m x‖), zero_add,
    add_comm (1 : ℝ)]
  have hp : Function.Periodic (fun x => Real.log ‖iter α A m x‖) 1 := fun x => by
    simp only [iter_periodic (α := α) hA.periodic m x]
  have := hp.intervalIntegral_add_eq (n * α) 0
  rw [zero_add] at this
  rw [this]
  rfl

/-- The sequence `n ↦ ∫ log ‖A_n‖` is subadditive. -/
theorem subadditive : Subadditive (lyapSeq α A) := by
  intro n m
  have hc := hA.continuous_log_norm_iter (α := α)
  have hcs : Continuous fun x => Real.log ‖iter α A m (x + n * α)‖ :=
    (hc m).comp (continuous_id.add continuous_const)
  calc lyapSeq α A (n + m)
      ≤ ∫ x in (0 : ℝ)..1, (Real.log ‖iter α A m (x + n * α)‖ + Real.log ‖iter α A n x‖) := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((hc _).intervalIntegrable _ _) ((hcs.add (hc n)).intervalIntegrable _ _)
          (fun x _ => ?_)
        have h1 := hA.one_le_norm_iter (α := α) m (x + n * α)
        have h2 := hA.one_le_norm_iter (α := α) n x
        have h3 := hA.one_le_norm_iter (α := α) (n + m) x
        rw [iter_add] at h3 ⊢
        rw [← Real.log_mul (by linarith) (by linarith)]
        exact Real.log_le_log (by linarith) (norm_mul_le _ _)
    _ = lyapSeq α A n + lyapSeq α A m := by
        rw [intervalIntegral.integral_add (hcs.intervalIntegrable _ _)
          ((hc n).intervalIntegrable _ _), hA.integral_shift, add_comm]
        rfl

/-- **Existence of the Lyapunov exponent** (Fekete): `(1/n) ∫ log ‖A_n‖ → L(α, A)`. -/
theorem tendsto_lyapunov :
    Tendsto (fun n : ℕ => lyapSeq α A n / n) atTop (𝓝 (lyapunov α A)) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => lyapSeq α A n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (hA.lyapSeq_nonneg n) (Nat.cast_nonneg n)⟩
  have h := hA.subadditive.tendsto_lim hbdd
  rwa [lyapunov, h.limUnder_eq]

/-- `L(α, A)` is the infimum of `(1/n) ∫ log ‖A_n‖` over `n ≥ 1`. -/
theorem lyapunov_eq_lim : lyapunov α A = (hA.subadditive (α := α)).lim :=
  tendsto_nhds_unique hA.tendsto_lyapunov
    (hA.subadditive.tendsto_lim ⟨0, by
      rintro _ ⟨n, rfl⟩; exact div_nonneg (hA.lyapSeq_nonneg n) (Nat.cast_nonneg n)⟩)

theorem lyapunov_le (n : ℕ) (hn : n ≠ 0) : lyapunov α A ≤ lyapSeq α A n / n := by
  rw [hA.lyapunov_eq_lim]
  exact (hA.subadditive (α := α)).lim_le_div ⟨0, by
      rintro _ ⟨n, rfl⟩; exact div_nonneg (hA.lyapSeq_nonneg n) (Nat.cast_nonneg n)⟩ hn

/-- `L(α, A) ≥ 0` for an `SL(2)` cocycle. -/
theorem lyapunov_nonneg : 0 ≤ lyapunov α A :=
  ge_of_tendsto' hA.tendsto_lyapunov
    (fun n => div_nonneg (hA.lyapSeq_nonneg n) (Nat.cast_nonneg n))

end IsSLCocycle

/-- A constant rotation-free example: the identity cocycle has exponent `0`. -/
example : lyapunov α (fun _ => 1) = 0 := by
  have hA : IsSLCocycle (fun _ : ℝ => (1 : M2)) := ⟨continuous_const, fun _ => rfl, fun _ => by simp⟩
  have hiter : ∀ n x, iter α (fun _ => (1 : M2)) n x = 1 := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih => simp [iter, ih]
  have h := hA.tendsto_lyapunov (α := α)
  simp only [lyapSeq, hiter, norm_one, Real.log_one, intervalIntegral.integral_zero,
    zero_div] at h
  exact tendsto_nhds_unique h tendsto_const_nhds |>.symm ▸ rfl

end AMO
