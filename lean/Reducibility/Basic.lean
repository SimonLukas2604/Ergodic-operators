/-
# Rotations reducibility and degree normalization

Formalization of the elementary (non-KAM) parts of

* §"Rotations reducibility for every irrational frequency", Lemma `t-lem:reducibility`:
  a conjugacy `Z(x+α)⁻¹ A(x) Z(x) = R_{φ(x)}` to a (possibly non-constant) rotation cocycle
  gives the uniform bound `t-eq:all-irr-bounded` on the cocycle products and their inverses
  (by telescoping), and hence a zero Lyapunov exponent;
* the degree normalization in the proof of Lemma `t-lem:arithmetic-reducibility`:
  if `B(x+α)⁻¹ A(x) B(x) = R_r` then `Z(x) = B(x) R_{-d x}` conjugates `A` to `R_{r + d α}`,
  and `Z` is `1`-periodic when `d ∈ ℤ` and `B` is periodic, or when `d ∈ ½ + ℤ` and `B` is
  antiperiodic (the lift of a `PSL(2,ℝ)` conjugacy).

The analytic reducibility theorems themselves (Avila, Avila–Fayad–Krikorian, Ge–Jitomirskaya)
are not formalized here.  We use the `ℓ^∞` operator norm on `2 × 2` matrices
(`open scoped Matrix.Norms.Operator`), as in `AnalyticPerturbationsAMO.Cocycle`.

Conjugacies are stated without inverses: `Conj α A B Z` means `A(x) Z(x) = Z(x+α) B(x)`.
-/
import AnalyticPerturbationsAMO.Cocycle

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Real AMO

namespace Red

/-! ### Entrywise bounds for the `ℓ^∞` operator norm -/

lemma norm_entry_le (M : M2) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  have h1 : ‖M i j‖₊ ≤ ∑ k, ‖M i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖M i k‖₊) (fun k _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ k, ‖M i k‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ k, ‖M i k‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

lemma norm_le_of_rows {M : M2} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖M i 0‖ + ‖M i 1‖ ≤ c) :
    ‖M‖ ≤ c := by
  have : ‖M‖₊ ≤ ⟨c, hc⟩ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    rw [Fin.sum_univ_two]
    refine NNReal.coe_le_coe.mp ?_
    simp only [NNReal.coe_add, coe_nnnorm]
    exact h i
  exact NNReal.coe_le_coe.mpr this

/-- For `det M = 1`, the adjugate formula gives `‖M⁻¹‖ ≤ 2 ‖M‖`. -/
theorem norm_inv_le_of_det_eq_one {M : M2} (h : M.det = 1) : ‖M⁻¹‖ ≤ 2 * ‖M‖ := by
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]
  rw [hinv, Matrix.adjugate_fin_two]
  refine norm_le_of_rows (by positivity) fun i => ?_
  fin_cases i <;> simp <;> linarith [norm_entry_le M 0 0, norm_entry_le M 0 1,
    norm_entry_le M 1 0, norm_entry_le M 1 1]

/-! ### Rotation matrices -/

/-- The rotation `R_θ` through angle `2πθ`, as a complex matrix with real entries. -/
def rot (θ : ℝ) : M2 :=
  !![(Real.cos (2 * π * θ) : ℂ), -(Real.sin (2 * π * θ) : ℂ);
     (Real.sin (2 * π * θ) : ℂ), (Real.cos (2 * π * θ) : ℂ)]

/-- `R_a R_b = R_{a+b}`. -/
theorem rot_add (a b : ℝ) : rot a * rot b = rot (a + b) := by
  have hc : Real.cos (2 * π * (a + b)) = Real.cos (2 * π * a) * Real.cos (2 * π * b)
      - Real.sin (2 * π * a) * Real.sin (2 * π * b) := by
    rw [mul_add, Real.cos_add]
  have hs : Real.sin (2 * π * (a + b)) = Real.sin (2 * π * a) * Real.cos (2 * π * b)
      + Real.cos (2 * π * a) * Real.sin (2 * π * b) := by
    rw [mul_add, Real.sin_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, hc, hs] <;> ring

theorem rot_zero : rot 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot]

theorem rot_int (k : ℤ) : rot (k : ℝ) = 1 := by
  have hc : Real.cos (2 * π * k) = 1 := by
    rw [show 2 * π * (k : ℝ) = (k : ℝ) * (2 * π) by ring]; exact Real.cos_int_mul_two_pi k
  have hs : Real.sin (2 * π * k) = 0 := by
    rw [show 2 * π * (k : ℝ) = ((2 * k : ℤ) : ℝ) * π by push_cast; ring]
    exact Real.sin_int_mul_pi _
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, hc, hs]

theorem rot_half : rot (1 / 2) = -1 := by
  have h : 2 * π * (1 / 2 : ℝ) = π := by ring
  rw [rot, h, Real.cos_pi, Real.sin_pi]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem rot_comm (a b : ℝ) : rot a * rot b = rot b * rot a := by
  rw [rot_add, rot_add, add_comm]

theorem rot_mul_rot_neg (a : ℝ) : rot a * rot (-a) = 1 := by
  rw [rot_add, add_neg_cancel, rot_zero]

theorem rot_inv (a : ℝ) : (rot a)⁻¹ = rot (-a) :=
  Matrix.inv_eq_right_inv (rot_mul_rot_neg a)

theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  have h : (Real.cos (2 * π * θ) : ℂ) ^ 2 + (Real.sin (2 * π * θ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (2 * π * θ)
  rw [rot, Matrix.det_fin_two_of]
  linear_combination h

/-- `‖R_θ‖ ≤ 2` in the `ℓ^∞` operator norm. -/
theorem norm_rot_le (θ : ℝ) : ‖rot θ‖ ≤ 2 := by
  have key : ∀ c s : ℝ, |c| ≤ 1 → |s| ≤ 1 →
      ‖(!![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)] : M2)‖ ≤ 2 := by
    intro c s hc hs
    refine norm_le_of_rows (by norm_num) fun i => ?_
    fin_cases i <;> simp [Complex.norm_real] <;> linarith
  exact key _ _ (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)

/-! ### Conjugacies -/

/-- `Conj α A B Z`: `A(x) Z(x) = Z(x+α) B(x)`, i.e. `Z(x+α)⁻¹ A(x) Z(x) = B(x)`. -/
def Conj (α : ℝ) (A B Z : ℝ → M2) : Prop := ∀ x, A x * Z x = Z (x + α) * B x

variable {α : ℝ}

theorem Conj.refl (A : ℝ → M2) : Conj α A A (fun _ => 1) := fun x => by simp

/-- Composition of conjugacies. -/
theorem Conj.trans {A B C Z W : ℝ → M2} (h₁ : Conj α A B Z) (h₂ : Conj α B C W) :
    Conj α A C (fun x => Z x * W x) := fun x => by
  rw [← mul_assoc, h₁ x, mul_assoc, h₂ x, mul_assoc]

/-- Conjugation by a constant invertible matrix. -/
theorem conj_const (A : ℝ → M2) {P : M2} (hP : IsUnit P.det) :
    Conj α A (fun x => P⁻¹ * A x * P) (fun _ => P) := fun x => by
  rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hP, one_mul]

/-- Telescoping: `A_n(x) Z(x) = Z(x+nα) B_n(x)`. -/
theorem Conj.iter {A B Z : ℝ → M2} (h : Conj α A B Z) (n : ℕ) (x : ℝ) :
    AMO.iter α A n x * Z x = Z (x + n * α) * AMO.iter α B n x := by
  induction n with
  | zero => simp [AMO.iter]
  | succ n ih =>
    simp only [AMO.iter]
    rw [mul_assoc, ih, ← mul_assoc, h, mul_assoc]
    congr 2
    push_cast; ring

/-- The products of a rotation cocycle: `R_{φ(x+(n-1)α)} ⋯ R_{φ(x)} = R_{∑_{j<n} φ(x+jα)}`. -/
theorem iter_rot (φ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    AMO.iter α (fun y => rot (φ y)) n x = rot (∑ j ∈ Finset.range n, φ (x + j * α)) := by
  induction n with
  | zero => simp [AMO.iter, rot_zero]
  | succ n ih =>
    simp only [AMO.iter]
    rw [ih, rot_add, Finset.sum_range_succ, add_comm]

/-- If `A` is conjugate to `B` by `Z` with `det Z = 1`, then `A_n(x) = Z(x+nα) B_n(x) Z(x)⁻¹`. -/
theorem Conj.iter_eq {A B Z : ℝ → M2} (h : Conj α A B Z) (hdet : ∀ x, (Z x).det = 1)
    (n : ℕ) (x : ℝ) :
    AMO.iter α A n x = Z (x + n * α) * AMO.iter α B n x * (Z x)⁻¹ := by
  rw [← h.iter, Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [hdet]; exact isUnit_one)]

/-- General transfer of bounds through a conjugacy:
if `‖Z‖ ≤ K`, `‖Z⁻¹‖ ≤ K'` and `‖B_n‖ ≤ c`, then `‖A_n‖ ≤ c K K'`. -/
theorem Conj.norm_iter_le {A B Z : ℝ → M2} (h : Conj α A B Z) (hdet : ∀ x, (Z x).det = 1)
    {K K' c : ℝ} (hK : ∀ x, ‖Z x‖ ≤ K) (hK' : ∀ x, ‖(Z x)⁻¹‖ ≤ K')
    (hc : ∀ n x, ‖AMO.iter α B n x‖ ≤ c) (n : ℕ) (x : ℝ) :
    ‖AMO.iter α A n x‖ ≤ c * K * K' := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0)
  rw [h.iter_eq hdet]
  calc ‖Z (x + n * α) * AMO.iter α B n x * (Z x)⁻¹‖
      ≤ ‖Z (x + n * α)‖ * ‖AMO.iter α B n x‖ * ‖(Z x)⁻¹‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ K * c * K' := by gcongr <;> simp [hK, hc, hK']
    _ = c * K * K' := by ring

/-- **Rotations reducibility ⇒ bounded products** (paper `t-eq:all-irr-bounded`):
if `Z(x+α)⁻¹ A(x) Z(x) = R_{φ(x)}` with `det Z ≡ 1`, `‖Z‖ ≤ K` and `‖Z⁻¹‖ ≤ K'`, then
`‖A_n(x)‖ ≤ 2 K K'` for all `n, x`. -/
theorem norm_iter_le_of_rotReducible {A Z : ℝ → M2} {φ : ℝ → ℝ}
    (h : Conj α A (fun x => rot (φ x)) Z) (hdet : ∀ x, (Z x).det = 1)
    {K K' : ℝ} (hK : ∀ x, ‖Z x‖ ≤ K) (hK' : ∀ x, ‖(Z x)⁻¹‖ ≤ K') (n : ℕ) (x : ℝ) :
    ‖AMO.iter α A n x‖ ≤ 2 * K * K' :=
  h.norm_iter_le hdet hK hK' (fun n x => by rw [iter_rot]; exact norm_rot_le _) n x

/-- Same bound using only `‖Z‖ ≤ K` (via `‖Z⁻¹‖ ≤ 2‖Z‖`): `‖A_n(x)‖ ≤ 4 K²`. -/
theorem norm_iter_le_of_rotReducible' {A Z : ℝ → M2} {φ : ℝ → ℝ}
    (h : Conj α A (fun x => rot (φ x)) Z) (hdet : ∀ x, (Z x).det = 1)
    {K : ℝ} (hK : ∀ x, ‖Z x‖ ≤ K) (n : ℕ) (x : ℝ) :
    ‖AMO.iter α A n x‖ ≤ 4 * K ^ 2 := by
  have := norm_iter_le_of_rotReducible h hdet hK (K' := 2 * K)
    (fun x => (norm_inv_le_of_det_eq_one (hdet x)).trans (by linarith [hK x])) n x
  linarith

/-- The inverse products are bounded too (paper `t-eq:all-irr-bounded` for negative times):
`‖A_n(x)⁻¹‖ ≤ 2 K K'`. -/
theorem norm_inv_iter_le_of_rotReducible {A Z : ℝ → M2} {φ : ℝ → ℝ}
    (h : Conj α A (fun x => rot (φ x)) Z) (hdet : ∀ x, (Z x).det = 1)
    {K K' : ℝ} (hK : ∀ x, ‖Z x‖ ≤ K) (hK' : ∀ x, ‖(Z x)⁻¹‖ ≤ K') (n : ℕ) (x : ℝ) :
    ‖(AMO.iter α A n x)⁻¹‖ ≤ 2 * K * K' := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [h.iter_eq hdet, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (by rw [hdet]; exact isUnit_one), iter_rot, rot_inv]
  calc ‖Z x * ((rot (-∑ j ∈ Finset.range n, φ (x + j * α))) * (Z (x + n * α))⁻¹)‖
      ≤ ‖Z x‖ * (‖rot (-∑ j ∈ Finset.range n, φ (x + j * α))‖ * ‖(Z (x + n * α))⁻¹‖) := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ K * (2 * K') := by gcongr <;> simp [hK, hK', norm_rot_le]
    _ = 2 * K * K' := by ring

/-! ### Zero Lyapunov exponent -/

/-- A continuous `1`-periodic matrix function is bounded. -/
theorem exists_bound_of_periodic {Z : ℝ → M2} (hc : Continuous Z) (hp : Function.Periodic Z 1) :
    ∃ K, ∀ x, ‖Z x‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨K, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]
  exact hK y (Set.Ico_subset_Icc_self hy)

/-- An `SL(2)` cocycle with uniformly bounded products has zero Lyapunov exponent. -/
theorem lyapunov_eq_zero_of_bounded {A : ℝ → M2} (hA : AMO.IsSLCocycle A) {C : ℝ}
    (hC : ∀ n x, ‖AMO.iter α A n x‖ ≤ C) : AMO.lyapunov α A = 0 := by
  have hC1 : 1 ≤ C := (hA.one_le_norm_iter 0 0).trans (hC 0 0)
  have hseq : ∀ n, AMO.lyapSeq α A n ≤ Real.log C := fun n => by
    have hint := intervalIntegral.integral_mono_on (a := 0) (b := 1)
      (f := fun x => Real.log ‖AMO.iter α A n x‖) (g := fun _ => Real.log C) zero_le_one
      ((hA.continuous_log_norm_iter (α := α) n).intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
      (fun x _ => Real.log_le_log (zero_lt_one.trans_le (hA.one_le_norm_iter n x)) (hC n x))
    simpa [AMO.lyapSeq] using hint
  have hlim : Tendsto (fun n : ℕ => AMO.lyapSeq α A n / n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
      (fun n => div_nonneg (hA.lyapSeq_nonneg n) (Nat.cast_nonneg n))
      (fun n => div_le_div_of_nonneg_right (hseq n) (Nat.cast_nonneg n))
  exact tendsto_nhds_unique hA.tendsto_lyapunov hlim

/-- **Rotations reducible cocycles have zero Lyapunov exponent**: if a continuous periodic
`SL(2)` cocycle `A` satisfies `Z(x+α)⁻¹ A(x) Z(x) = R_{φ(x)}` with `Z` continuous,
`1`-periodic and of determinant one, then `L(α, A) = 0`. -/
theorem lyapunov_eq_zero_of_rotReducible {A Z : ℝ → M2} {φ : ℝ → ℝ} (hA : AMO.IsSLCocycle A)
    (h : Conj α A (fun x => rot (φ x)) Z) (hZc : Continuous Z) (hZp : Function.Periodic Z 1)
    (hdet : ∀ x, (Z x).det = 1) : AMO.lyapunov α A = 0 := by
  obtain ⟨K, hK⟩ := exists_bound_of_periodic hZc hZp
  exact lyapunov_eq_zero_of_bounded hA (norm_iter_le_of_rotReducible' h hdet hK)

/-! ### Degree normalization (proof of `t-lem:arithmetic-reducibility`) -/

/-- If `B(x+α)⁻¹ A(x) B(x) = R_r`, then `Z(x) = B(x) R_{-d x}` satisfies
`Z(x+α)⁻¹ A(x) Z(x) = R_{r + d α}` (for any real `d`). -/
theorem conj_degree_shift {A B : ℝ → M2} {r : ℝ} (h : Conj α A (fun _ => rot r) B) (d : ℝ) :
    Conj α A (fun _ => rot (r + d * α)) (fun x => B x * rot (-(d * x))) := fun x => by
  simp only
  rw [← mul_assoc, h x, mul_assoc, mul_assoc, rot_add, rot_add]
  congr 2
  ring

/-- For an integer winding `d` and periodic `B`, `Z(x) = B(x) R_{-d x}` is `1`-periodic. -/
theorem periodic_degree_shift {B : ℝ → M2} (hB : Function.Periodic B 1) (d : ℤ) :
    Function.Periodic (fun x => B x * rot (-((d : ℝ) * x))) 1 := fun x => by
  simp only
  rw [hB x, show -((d : ℝ) * (x + 1)) = -((d : ℝ) * x) + ((-d : ℤ) : ℝ) by push_cast; ring,
    ← rot_add, rot_int, mul_one]

/-- For a half-integer winding `d = m + ½` and antiperiodic `B` (`B(x+1) = -B(x)`, the lift of a
`PSL(2,ℝ)` map), `Z(x) = B(x) R_{-d x}` is `1`-periodic. -/
theorem periodic_degree_shift_half {B : ℝ → M2} (hB : ∀ x, B (x + 1) = -B x) (m : ℤ) :
    Function.Periodic (fun x => B x * rot (-(((m : ℝ) + 1 / 2) * x))) 1 := fun x => by
  simp only
  rw [hB x, show -(((m : ℝ) + 1 / 2) * (x + 1)) =
      -(((m : ℝ) + 1 / 2) * x) + (((-m - 1 : ℤ) : ℝ) + 1 / 2) by push_cast; ring,
    ← rot_add, ← rot_add, rot_int, rot_half]
  simp only [mul_one, mul_neg, neg_mul, neg_neg]

end Red
